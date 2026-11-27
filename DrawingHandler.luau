-- Discord: ibunnybee | Roblox: iBunnyBee8

-- architecture decision notes: 
-- the server validates and applies every op before sending it to both players so both clients follow the same order and stay in sync
-- one pairKey is used to identify the pair and access their drawing data and retrieve their canvas for spectating
-- canvases are saved as strings so they stay independent from later changes to the live buffer
-- DrawOp handles drawing history, undo/redo and catch-up while DrawStroke sends live pixel changes
-- DrawingService sends the full canvas if more than 40% changes, otherwise it sends smaller packed 7-byte pixel patches
-- DrawStore uses sequence numbers to prevent duplicate ops, keeps layer IDs consistent when reordering and uses groupVisited to stop overlapping transparent strokes from getting darker
-- the stabilizer uses a lazy brush dead zone while the partner cursor uses lerp and hides after 0.4 seconds
-- alpha is normalized on the final canvas so saved canvases stay fully opaque when used for spectating or voting 

local Players: Players = game:GetService("Players") -- gets the players service so the handler can track players joining and leaving
local ReplicatedStorage: ReplicatedStorage = game:GetService("ReplicatedStorage") -- gets shared storage where the remotes and modules are kept

local Remotes: Folder = ReplicatedStorage:WaitForChild("Remotes"):: Folder -- gets the folder that contains the drawing remotes
local DrawStroke: RemoteEvent = Remotes:WaitForChild("DrawStroke") :: RemoteEvent -- remote used for sending pixel buffer updates
local FullCanvas: RemoteEvent = Remotes:WaitForChild("FullCanvas") :: RemoteEvent -- remote used to send a complete saved canvas to a client
local RequestUndo: RemoteEvent = Remotes:WaitForChild("RequestUndo"):: RemoteEvent -- remote used when a player requests an undo
local RequestRedo: RemoteEvent = Remotes:WaitForChild("RequestRedo"):: RemoteEvent -- remote used when a player requests a redo
local RoundCanvas: RemoteEvent = Remotes:WaitForChild("RoundCanvas") :: RemoteEvent -- remote used to send the final canvas at the end of a round
local RequestCanvas: RemoteFunction = Remotes.Spectate:WaitForChild("RequestCanvas") :: RemoteFunction -- lets spectators load a saved pair canvas
local RequestPairs: RemoteFunction = Remotes.Spectate:WaitForChild("RequestPairs") :: RemoteFunction -- lets spectators request the list of active drawing pairs

local RoundManager = require(game:GetService("ServerScriptService").Modules.RoundManager) -- roundManager owns the round pairing and each players round data used by this handler
local DrawStore = require(ReplicatedStorage.Modules.DrawStore) -- drawStore is the server side operation log and pixel/layer state for each pair
local DrawOp: RemoteEvent = Remotes:WaitForChild("DrawOp") :: RemoteEvent -- has structured drawing operations such as strokes, fills and layer changes

type RequestLimit = {
	start: number,
	count: number
}
type DrawStoreInstance = typeof(DrawStore.new())


-- tracking which player in the pair has authority over the drawing of their team
local authorityPlayer: {[Player]: Player} = {} -- maps both players to the same drawing authority
local canvasSnapshots: {[string]: string} = {} -- this keeps the latest saved canvas so it can be loaded or spectated later
local pendingCanvases: {[string]: buffer} = {} -- table for canvases waiting to be processed
local serverCanvases: {[string]: buffer} = {} -- keeps the current pixel buffer for each pair on the server
local pairStores: {[string]: DrawStoreInstance} = {} -- each pair gets their own DrawStore so their drawing history stays separate
local pairRedo: {[string]: {{any}}} = {} -- keeps undone ops so redo can restore them
local practicePartners: {[Player]: Player} = {} -- keeps practice partners separate from the normal RoundManager pairs cause there is a practice functionality in the full game i made originally 
local requestLimits: {[string]: RequestLimit} = {} -- keeps a separate request count for each player and remote


-- making a key for each pair
local function pairKey(a: Player, b: Player): string -- sorts ids so both players get the same key
	local ua: number, ub: number = a.UserId, b.UserId  -- uses Userids because display names can change or be the same
	if ua > ub then ua, ub = ub, ua end -- puts the smaller id first so both players create the same key
	return tostring(ua) .. "_" .. tostring(ub) -- combines both ids into one key for the pair
end

local DrawingHandler: {[string]: any} = {} -- table that holds the functions used by the other modules

-- getting the user paired with this player and using it also for practice partner since a practice mechanic was also coded with this mechanic 
local function getPartner(player: Player): Player? -- checks practice pairing before normal rounds
	local practicePartner: Player? = practicePartners[player]  -- practice pairing takes priority when this player is using the practice mode

	if practicePartner and practicePartner.Parent then -- checks that the practice partner still exists in the game
		return practicePartner -- practice partner
	end
	return RoundManager.getPartner(player) -- otherwise use the normal round pairing maintained by RoundManager
end

local function isByte(value: any): boolean -- keeps color channels within 0-255
	return type(value) == "number" and value % 1 == 0 and value >= 0 and value <= 255  -- one color channel range 
end
local function isInteger(value: any, min: number, max: number): boolean -- integer check
	return type(value) == "number" and value % 1 == 0 and value >= min and value <= max -- checks that the value is a whole number inside the allowed range
end
local function isOffset(value: any): boolean -- pixel offset check
	return isInteger(value, 0, 512 * 512 * 4 - 4) and value % 4 == 0 -- each RGBA pixel uses 4 bytes so the offset has to start at the beginning of a pixel and not inside one of its channels
end

-- limiting how often each players can send remote requests since they are used very often this ends up getting used a lot 
local function rateLimit(player: Player, action: string, limit: number): boolean -- request limit
	local key: string = player.UserId .. "_" .. action -- adds the remote name so each action has its own limit for this player
	local now: number = os.clock() -- gets the current time for the one second request window
	local data: RequestLimit? = requestLimits[key] -- gets counter

	if not data or now - data.start >= 1 then -- starts a new request window if this is the first request or the old one expired
		data = {start = now, count = 0} -- resets the counter for this player and action
		requestLimits[key] = data -- stores the new request window
	end
	if data.count >= limit then return false end -- stops a client from spamming this remote after reaching its limit
	data.count += 1 -- counts this request against the limit
	return true -- allows the request when it is still under the limit
end

-- Initializing the shared draw state for the paired players 
function DrawingHandler.onPairFormed(playerA: Player, playerB: Player): () -- sets up pair
	authorityPlayer[playerA] = playerA -- sets playerA as the authority for the pairs drawing
	authorityPlayer[playerB] = playerA -- both players point to the same authority so the server can check either one

	practicePartners[playerA] = playerB -- storing both sides of the practice pair so either player can find the other
	practicePartners[playerB] = playerA -- also letting the other player find their partner when they trigger an event
	pairStores[pairKey(playerA, playerB)] = DrawStore.new() -- creates a fresh drawing store for the new pair
end

-- Clearing the drawing data of each pair thats dissolved 
function DrawingHandler.onPairDissolved(playerA: Player, playerB: Player): () -- clears pair
	authorityPlayer[playerA] = nil -- clears playerA drawing authority when the pair ends
	authorityPlayer[playerB] = nil -- clears playerB drawing authority when the pair ends

	practicePartners[playerA] = nil -- removes playerA practice pairing
	practicePartners[playerB] = nil -- removes playerB practice pairing

	local key: string = pairKey(playerA, playerB) -- uses the same key to clear this pairs data

	canvasSnapshots[key] = nil -- removes the saved canvas for this pair
	serverCanvases[key] = nil -- removes the live pixel buffer for this pair
	pairStores[key] = nil -- removes the pair drawing history
	pairRedo[key] = nil -- removes redo history when the pair is dissolved
end


-- Used to return the drawstore for a pair and makes it if there is none 
local function getPairStore(key: string): DrawStoreInstance -- gets pair store
	local s: DrawStoreInstance? = pairStores[key] -- checks whether this pair already has a drawing store
	if not s then -- creates store
		s = DrawStore.new() -- creates a store if this pair does not have one yet
		pairStores[key] = s -- keeps the new store so later requests reuse it
	end
	return s -- returns the same store for every event from this pair
end

-- starts storage in the beggining of each round
function DrawingHandler.onRoundStart(playerA: Player, playerB: Player): () -- resets round history
	pairStores[pairKey(playerA, playerB)] = DrawStore.new() -- resets the pair drawing history for the new round
end


-- Main core event, it recieves an operation, validates, stores and sends it back to the client 
DrawOp.OnServerEvent:Connect(function(sender: Player, msg: any) -- drawing op remote
	if not rateLimit(sender, "DrawOp", 60) then return end  -- limits this to 60 ops per second. strokes and layer changes can send often but this still stops someone from spamming the remote
	-- then a bunch of checks to make sure partner is there who has authority ect ect 
	if type(msg) ~= "table" then return end -- rejects anything that is not a structured operation request
	local partner: Player? = getPartner(sender) -- finds who should receive the drawing
	if not partner then return end -- stops if the player does not currently have a partner
	local authority: Player? = authorityPlayer[sender] -- checks who is allowed to draw for the pair
	if not authority then return end -- also stopping players from drawing before their pair has been set up

	-- requesting all the stored data 
	local key: string = pairKey(sender, partner) -- makes both sides use the same pair data
	local store: DrawStoreInstance = getPairStore(key) -- reuses this pairs drawing history

	-- client can request operations newer than its last known sequence number to catch up so there is no gaps in the drawing 
	if msg.since ~= nil then -- checks whether the client is asking for operations it has missed
		if type(msg.since) ~= "number" then return end -- makes sure the sequence number is valid before using it
		DrawOp:FireClient(sender, {ops = store:opsSince(msg.since)}) -- sends only the operations newer than the clients last known sequence
		return -- ends request
	end

	-- Takes the requested operation before checking if its data is valid
	local op: any = msg.op -- gets the operation to validate and apply
	if type(op) ~= "table" or type(op.op) ~= "string" then return end -- rejects operations that do not have a valid operation type
	if op.op == "stroke" then -- runs extra validation when the requested operation is a stroke
		if type(op.pts) ~= "table" or #op.pts > 8000 then return end -- limits the number of points so one request cannot create excessive work
		if not isInteger(op.size, 1, 50) then return end  -- keeps brush size between 1 and 50 so a fake huge brush cannot make the server do pixel work and crash everything
		for _, pt in ipairs(op.pts) do -- checks every point in the stroke before applying it
			if type(pt) ~= "table" or not isInteger(pt[1], 1, 512) or not isInteger(pt[2], 1, 512) then return end -- rejects points outside the canvas or with invalid coordinates
		end
	end
	if op.op == "addLayer" then -- handles layer creation separately so the server controls its id
		op.id = store:allocLayerId()  -- the server creates the layer id instead of trusting the client so both players use the same id for that layer
	end

	-- Applies the operation to the servers drawstore (another module in the place) and saves it in the operation history
	store:apply(op) -- updates the server drawing state and adds the operation to its history
	pairRedo[key] = nil -- clears redo history because a new operation changes the drawing timeline

	DrawOp:FireClient(sender, {op = op}) -- sends the accepted op back to the sender so their client DrawStore stays in sync with the server

	if partner ~= sender then -- avoids sending the same update twice when the sender is their own partner
		DrawOp:FireClient(partner, {op = op}) -- sends the same op to the partner so both clients apply the same change
	end
end)

-- Receives pixel buffer updates seperate from drawing operations and sends them to other player
DrawStroke.OnServerEvent:Connect(function(sender: Player, strokeData: any) -- pixel update remote
	if not rateLimit(sender, "DrawStroke", 120) then return end  -- allows 120 patches per second because live drawing sends small pixel batches pretty often
	if type(strokeData) ~= "table" then return end -- rejects pixel updates that are not sent in the expected format

	local partner: Player? = getPartner(sender) -- finds who should receive the pixel update
	if not partner then return end -- stops if the player does not currently have a partner

	local authority: Player? = authorityPlayer[sender] -- gets the player who controls the drawing
	if not authority then return end -- stops players without drawing permission

	local key: string = pairKey(sender, partner) -- keeps pixel updates under the same pair key

	-- full update replaces the saved canvas snapshot for this pair
	if strokeData.full then -- full canvas update
		if typeof(strokeData.data) ~= "buffer" then return end -- makes sure a full canvas update contains a buffer
		if buffer.len(strokeData.data) ~= 512 * 512 * 4 then return end -- checks that the buffer has exactly enough bytes for the canvas

		local str: string = buffer.tostring(strokeData.data) -- buffer to string

		serverCanvases[key] = buffer.fromstring(str) -- keeps a separate live buffer for future pixel patches
		canvasSnapshots[key] = str -- stores a copy of the full canvas for later loading or spectating
		RoundManager.saveBuffer(sender, str) -- saves the full canvas to the sender round data
		RoundManager.saveBuffer(partner, str) -- saves the same canvas to the partner round data
	elseif strokeData.full == false then -- partial update
		-- partial update changes only the pixel offsets included in the incoming patch
		if type(strokeData.count) ~= "number" then return end -- checks that the patch count is a number
		if strokeData.count % 1 ~= 0 or strokeData.count < 0 or strokeData.count > 512 * 512 then return end -- keeps the patch count within the maximum number of canvas pixels
		if type(strokeData.data) ~= "table" then return end -- makes sure the pixel patch data is a table
		if not serverCanvases[key] then -- creates a starting buffer if this pair has not sent a full canvas yet
			local buf = buffer.create(512 * 512 * 4)-- creates enough space for all 512x512 RGBA pixels
			buffer.fill(buf, 0, 255) -- fills the starting canvas with opaque white
			serverCanvases[key] = buf -- stores the new buffer so later patches update the same canvas
		end

		local buf: buffer = serverCanvases[key]  -- gets the server buffer that these pixel changes will be written into

		for i = 1, math.min(strokeData.count, #strokeData.data) do-- uses the smaller count so it never tries to read entries that were not sent
			local px: any = strokeData.data[i] -- gets pixel
			if type(px) == "table" and isOffset(px[1]) and isByte(px[2]) and isByte(px[3])and isByte(px[4]) then  -- checks the pixel offset and RGB values before writing so bad data cannot write outside the buffer or into the wrong channel
				buffer.writeu8(buf, px[1], px[2])-- writing the red value into the first byte of this pixel
				buffer.writeu8(buf, px[1]+1, px[3]) -- writing the green value into the second byte
				buffer.writeu8(buf, px[1]+2, px[4])-- writes the blue value into the third byte, alpha is not changed by this patch
			end
		end

		canvasSnapshots[key] = buffer.tostring(buf) -- updates the saved snapshot after applying the pixel changes
	else
		return -- rejects invalid update
	end

	-- copies the update before adding metadata that identifies if it came from the authority player
	local data: {[string]: any} = table.clone(strokeData) -- keeps the original request unchanged when adding sender info
	data.fromAuthority = sender == authority -- marks whether this update came from the player with drawing authority
	if sender == authority then -- sends the update to the correct side based on authority
		if partner ~= sender then -- avoids sending the same update twice when the sender is their own partner
			DrawStroke:FireClient(partner, data) -- sends the pixel update to the other player
		end
	else
		DrawStroke:FireClient(authority, data) -- sends non-authority pixel updates to the authority player
	end
end)


-- This handles undo requests on the server so both players stay in sync
RequestUndo.OnServerEvent:Connect(function(sender: Player) -- undo request remote
	if not rateLimit(sender, "RequestUndo", 5) then return end -- undo limit
	local partner: Player? = getPartner(sender) -- finds who shares this drawing history
	if not partner then return end -- stops if the player does not currently have a partner
	if not authorityPlayer[sender] then return end -- only allows undo when the player belongs to an active drawing pair
	local key: string = pairKey(sender, partner) -- keeps undo tied to the correct pair
	local store: DrawStoreInstance = getPairStore(key) -- gets the history that needs to be undone
	local n: number = #store.ops -- gets the number of operations currently in the drawing history

	-- Here it removes the most recent operation or every operation belonging to its stroke group
	if n > 0 then -- only continues if there is something to undo
		local group: string? = store.ops[n].group -- one stroke can be sent in multiple chunks, but they all share the same group id
		local removed: {any} = {} -- holds the operations removed by this undo so they can be restored

		if group then -- checks stroke group
			for i = n, 1, -1 do -- starts from the newest op and finds every chunk that belongs to the same stroke
				if store.ops[i].group == group then -- checks whether this operation belongs to the same stroke group
					table.insert(removed, 1, table.remove(store.ops, i)) -- removes each chunk and keeps their original order so redo can put them back correctly
				end
			end
		else
			removed[1] = table.remove(store.ops)  -- removes the latest operation when it is not part of a group
		end
		pairRedo[key] = pairRedo[key] or {} -- creates redo storage if this pair does not have it yet
		table.insert(pairRedo[key], removed) -- saves the removed ops together so redo can restore the whole stroke
		store:rebuildFrom(store.ops) -- rebuilds the drawing from the remaining ops so the pixels and layers match the updated history

		DrawOp:FireClient(sender, {undo = true}) -- tells the sender to undo the same operation

		if partner ~= sender then -- avoids sending the same update twice when the sender is their own partner
			DrawOp:FireClient(partner, {undo = true}) -- keeps the partner drawing in sync with the undo
		end
	end
end)

-- Here I reapply the most recently undone operation group and sends it to both clients
RequestRedo.OnServerEvent:Connect(function(sender: Player) -- redo request remote
	if not rateLimit(sender, "RequestRedo", 5) then return end -- redo limit
	local partner: Player? = getPartner(sender) -- finds who shares this drawing history
	if not partner then return end -- stops if the player does not currently have a partner
	if not authorityPlayer[sender] then return end -- only allows redo requests from an active drawing pair
	local key: string = pairKey(sender, partner) -- keeps redo tied to the correct pair
	local store: DrawStoreInstance = getPairStore(key) -- gets the history to restore the operation into
	local redo: {{any}}? = pairRedo[key] -- gets the saved undo groups that can be restored
	local group: {any}? = redo and table.remove(redo) -- takes the latest undone group first, so redo follows the correct order

	if group then -- checks redo group
		for _, op in ipairs(group) do -- reapplies every operation in the undone group
			store:apply(op) -- updates the server drawing state and adds the operation to its history
		end
		DrawOp:FireClient(sender, {redo = group}) -- tells the sender to restore the group on their client
		if partner ~= sender then -- avoids sending the same update twice when the sender is their own partner
			DrawOp:FireClient(partner, {redo = group}) -- sends the same redo to the partner
		end
	end
end)

-- Here it recieves the complete final round canvas normalizes its alpha channel and saves a snapshot for both players
RoundCanvas.OnServerEvent:Connect(function(player: Player, buf: buffer) -- final canvas remote
	-- again a bunch of checks here the communication is complex so need to be sure about every stroke and its purpose 
	if not rateLimit(player, "RoundCanvas", 2) then return end -- request limit
	if typeof(buf) ~= "buffer" then return end -- rejects the final canvas if it is not a buffer
	if buffer.len(buf) ~= 512 * 512 * 4 then return end -- checks the final canvas has the expected size
	local partner: Player? = getPartner(player) -- finds who should receive the final canvas
	if not partner then return end -- stops if the player does not currently have a partner

	local key: string = pairKey(player, partner) -- saves the canvas under the pair's shared key
	local fixedBuf: buffer = buffer.create(512 * 512 * 4) -- creates a separate buffer for the normalized final canvas

	for i = 0, 512 * 512 - 1 do -- goes through every pixel in the canvas
		local o: number = i * 4-- moves to the start of the next RGBA pixel
		-- then i coppy the channels into the new buffer
		buffer.writeu8(fixedBuf, o, buffer.readu8(buf, o)) -- copies the red channel into the new buffer
		buffer.writeu8(fixedBuf, o+1, buffer.readu8(buf, o+1)) -- copies the green channel into the new buffer
		buffer.writeu8(fixedBuf, o+2, buffer.readu8(buf, o+2)) -- copies the blue channel into the new buffer
		buffer.writeu8(fixedBuf, o+3, 255) -- sets alpha to 255 for every pixel so the final saved canvas is fully opaque
	end

	local bufStr: string = buffer.tostring(fixedBuf) -- converts the normalized buffer into a string for saving and sending

	serverCanvases[key] = fixedBuf -- keeps the normalized buffer on the server for any later pixel updates.
	canvasSnapshots[key] = bufStr -- saves the final canvas so it can be loaded later or shown to spectators the extended version of this system has cinematic shots for voting in the end of each round
	RoundManager.saveBuffer(player, bufStr) -- saves the final canvas to this players round data
	RoundManager.saveBuffer(partner, bufStr) -- saves the same final canvas to the partners round data
end)

-- Here removing cached pair data and rate limit records when a player leaves
Players.PlayerRemoving:Connect(function(player: Player) -- player cleanup
	authorityPlayer[player] = nil -- clears the authority reference for the player who left
	for key in pairs(canvasSnapshots) do -- checks saved pair snapshots to find any that belong to this player
		local idA: string?, idB: string? = key:match("(%d+)_(%d+)") -- gets user ids
		if idA == tostring(player.UserId) or idB == tostring(player.UserId) then -- checks whether either id in the pair key belongs to the player who left
			canvasSnapshots[key] = nil -- removes the saved canvas for this pair
			serverCanvases[key] = nil -- removes the live pixel buffer for this pair
			pairStores[key] = nil -- removes the pair drawing history
			pairRedo[key] = nil -- removes redo history for pairs involving the player who left
		end
	end
	for key in pairs(requestLimits) do -- checks the stored request counters for this player
		if key:match("^" .. player.UserId .. "_") then -- finds rate limit entries that start with this players user id
			requestLimits[key] = nil -- removes old limits so departed players leave no entries
		end
	end
end) -- ends cleanup

-- sending the latest saved canvas snapshot to both players when they need to load it
function DrawingHandler.pushCanvasToPlayers(playerA: Player, playerB: Player): () -- sends canvas
	local key: string = pairKey(playerA, playerB) -- finds the saved canvas for this pair
	local snap: string? = canvasSnapshots[key] -- gets snapshot
	if snap then -- avoids sending an empty snapshot
		FullCanvas:FireClient(playerA, snap) -- sends the saved canvas to the first player
		FullCanvas:FireClient(playerB, snap) -- sends the same saved canvas to the second player
	end
end

-- Making a list of active drawing pairs for the spectating interface
RequestPairs.OnServerInvoke = function(spectator: Player): {{pairKey: string, nameA: string, nameB: string}} -- pair list remote
	local pairsList: {{pairKey: string, nameA: string, nameB: string}} = {} -- stores pair list
	for key, snap in pairs(canvasSnapshots) do -- goes through saved canvases to build the spectator list
		local idA: string?, idB: string? = key:match("(%d+)_(%d+)") -- gets user ids
		if idA and idB then -- continues only when the pair key contains both user ids
			local playerA: Player? = Players:GetPlayerByUserId(tonumber(idA) :: number) -- gets the first player currently in the server
			local playerB: Player? = Players:GetPlayerByUserId(tonumber(idB) :: number) -- gets the second player currently in the server
			if playerA and playerB then -- only lists pairs when both players are still online
				table.insert(pairsList, {pairKey = key, nameA = playerA.DisplayName, nameB = playerB.DisplayName,}) -- includes the pair once both players are online
			end
		end
	end
	for player, partner in pairs(authorityPlayer) do -- checks active authority entries for pairs without a saved snapshot yet
		if player == partner then -- uses the authority player entry once so each pair is only checked once
			local key: string = pairKey(player, partner and RoundManager.getPartner(player) or player) -- gets the normal partner when building the pair key
			local alreadyAdded: boolean = false -- prevents the same pair appearing twice
			for _, entry in ipairs(pairsList) do -- checks whether this pair is already in the spectator list
				if entry.pairKey == key then alreadyAdded = true break end -- marks the pair as already listed and stops searching
			end
			if not alreadyAdded then -- only adds the pair if it was not included from saved snapshots
				local actualPartner: Player? = RoundManager.getPartner(player) -- gets the normal round partner for this active player
				if actualPartner then -- only adds the pair when a partner exists
					table.insert(pairsList, { -- adds the active pair and their display names to the spectator list
						pairKey = pairKey(player, actualPartner), nameA = player.DisplayName,nameB = actualPartner.DisplayName}) -- includes this active pair in the spectator list
				end
			end
		end
	end
	return pairsList -- returns the finished list of pairs to the spectator
end

-- Returning the saved canvas snapshot for a pair selected by a spectator
RequestCanvas.OnServerInvoke = function(spectator: Player, requestedKey: any): string? -- lets spectators request the canvas for a pair
	if type(requestedKey) ~= "string" then return nil end -- rejects invalid pair keys sent by the spectator
	return canvasSnapshots[requestedKey] -- returns the saved canvas belonging to the selected pair
end

return DrawingHandler -- makes these handler functions available to the other server modules

