local addonName, FL = ...

-------------------------------------------------------------------------------
-- AuctionScan.lua
-- Auction house scanning for ForeverLedger: throttled request queue with
-- in-flight tracking, full ReplicateItems scans processed in time slices,
-- per-item commodity/item ladders with paging, browse paging, owned-auction
-- queries and the hardware-event purchase flows (via FL.Secure).
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- Cached globals
-------------------------------------------------------------------------------
local pairs, type, tonumber, tostring, pcall = pairs, type, tonumber, tostring, pcall
local math_floor, math_max = math.floor, math.max
local string_format = string.format
local table_remove = table.remove
local wipe = wipe
local GetTime, time, debugprofilestop, GetFramerate = GetTime, time, debugprofilestop, GetFramerate
local CreateFrame, InCombatLockdown = CreateFrame, InCombatLockdown
local C_AuctionHouse, C_Item, C_Timer, Enum = C_AuctionHouse, C_Item, C_Timer, Enum

-- Auction house API functions (existence-checked at use; nil when missing)
local AH = C_AuctionHouse or {}
local ReplicateItems = AH.ReplicateItems
local GetNumReplicateItems = AH.GetNumReplicateItems
local GetReplicateItemInfo = AH.GetReplicateItemInfo
local GetReplicateItemLink = AH.GetReplicateItemLink
local GetReplicateItemTimeLeft = AH.GetReplicateItemTimeLeft
local SendSearchQuery = AH.SendSearchQuery
local MakeItemKey = AH.MakeItemKey
local GetItemKeyInfo = AH.GetItemKeyInfo
local GetNumCommoditySearchResults = AH.GetNumCommoditySearchResults
local GetCommoditySearchResultInfo = AH.GetCommoditySearchResultInfo
local HasFullCommoditySearchResults = AH.HasFullCommoditySearchResults
local RequestMoreCommoditySearchResults = AH.RequestMoreCommoditySearchResults
local GetNumItemSearchResults = AH.GetNumItemSearchResults
local GetItemSearchResultInfo = AH.GetItemSearchResultInfo
local HasFullItemSearchResults = AH.HasFullItemSearchResults
local RequestMoreItemSearchResults = AH.RequestMoreItemSearchResults
local SendBrowseQuery = AH.SendBrowseQuery
local GetBrowseResults = AH.GetBrowseResults
local HasFullBrowseResults = AH.HasFullBrowseResults
local RequestMoreBrowseResults = AH.RequestMoreBrowseResults
local QueryOwnedAuctions = AH.QueryOwnedAuctions
local GetOwnedAuctions = AH.GetOwnedAuctions
local IsThrottledMessageSystemReady = AH.IsThrottledMessageSystemReady
local StartCommoditiesPurchase = AH.StartCommoditiesPurchase
local ConfirmCommoditiesPurchase = AH.ConfirmCommoditiesPurchase
local CancelCommoditiesPurchase = AH.CancelCommoditiesPurchase
local PlaceBid = AH.PlaceBid

-------------------------------------------------------------------------------
-- Constants
-------------------------------------------------------------------------------
local FULL_SCAN_COOLDOWN = 900          -- seconds; account-wide ReplicateItems cooldown
local EMPTY_SCAN_RETRY = 60             -- seconds before retrying after an empty replicate list
local REQUEST_TIMEOUT = 10              -- seconds a throttled request may await its event
local REPLICATE_TIMEOUT = 60            -- seconds a ReplicateItems request may await its event
local MAX_RETRIES = 3                   -- retries before a request is dropped
local MAX_PAGES = 200                   -- hard cap on RequestMore* paging per request
local PURCHASE_TIMEOUT = 15             -- seconds a purchase step may await its event
local KEYINFO_TIMEOUT = 5               -- seconds to wait for ITEM_KEY_ITEM_INFO_RECEIVED
local LADDER_POOL_MAX = 512             -- pooled ladder tables kept after a full scan
local SUFFIX_KEY_BASE = 100000
local SUFFIX_KEY_OFFSET = 50000
local FPS_SKIP_LIMIT = 20               -- consecutive low-FPS skips before sending anyway
local ROWS_PER_CLOCK_CHECK = 8          -- replicate rows processed between debugprofilestop checks

local SORT_PRICE = (Enum and Enum.AuctionHouseSortOrder and Enum.AuctionHouseSortOrder.Price) or 0
local SORTS_PRICE = { { sortOrder = SORT_PRICE, reverseSort = false } }
local BROWSE_EMPTY_FILTERS = {}
local EMPTY = {}

-------------------------------------------------------------------------------
-- Module table
-------------------------------------------------------------------------------
local AuctionScan = {
	isOpen = false,
	state = "idle",
	lastFullScanAt = 0,
	nextFullScanAt = 0,
	progress = 0,
	progressText = "",
	ownedByItem = {},
	pendingItemLoads = {},
}
FL.AuctionScan = AuctionScan

-------------------------------------------------------------------------------
-- Settings access (tolerant of being called before hydration)
-------------------------------------------------------------------------------
local DEFAULT_SCAN = { fullScanOnOpen = false, chunkMs = 8, requestIntervalSec = 0.35, minFPS = 15, keepRawAuctions = false, historyDays = 30 }

local function Settings()
	return FL.Settings or (FL.RuntimeDB and FL.RuntimeDB.settings) or FL.DefaultSettings
end

local function ScanSetting(key)
	local s = Settings()
	local scan = s and s.scan
	local v = scan and scan[key]
	if v == nil then
		local d = FL.DefaultSettings
		local ds = d and d.scan
		v = ds and ds[key]
	end
	if v == nil then v = DEFAULT_SCAN[key] end
	return v
end

local function PriceTolerance()
	local s = Settings()
	local v = s and s.sniper and s.sniper.priceTolerance
	if v == nil then v = s and s.scan and s.scan.priceTolerance end
	v = tonumber(v) or 0
	if v < 0 then v = 0 end
	return v
end

-------------------------------------------------------------------------------
-- Small utilities
-------------------------------------------------------------------------------
local function SafeCall(fn, ...)
	if not fn then return true end
	local ok, err = pcall(fn, ...)
	if not ok then
		FL:Warn("AuctionScan callback error: %s", tostring(err))
	end
	return ok, err
end

local function After(sec, fn)
	if FL.Timer and FL.Timer.After then
		FL.Timer.After(sec, fn)
	elseif C_Timer and C_Timer.After then
		C_Timer.After(sec, function()
			local ok, err = pcall(fn)
			if not ok then FL:Warn("AuctionScan timer error: %s", tostring(err)) end
		end)
	end
end

local function InCombat()
	return InCombatLockdown and InCombatLockdown() or false
end

local function ItemLabel(itemID)
	local s = FL.GetItemLinkCached and FL.GetItemLinkCached(itemID)
	if not s then s = FL.GetItemName and FL.GetItemName(itemID) end
	if not s then s = "item:" .. tostring(itemID) end
	return s
end

local function ItemPlainName(itemID)
	local s = FL.GetItemName and FL.GetItemName(itemID)
	if not s then s = "item:" .. tostring(itemID) end
	return s
end

-------------------------------------------------------------------------------
-- Ladder tables (per-item price ladders, pooled and reused)
-- { n, unitPrices, quantities, auctionIDs, own, timeLefts, suffixes,
--   isCommodity, ts, itemID, suffix, totalQuantity, marketValue, minBuyout }
-------------------------------------------------------------------------------
local ladderPool = {}
local ladderPoolN = 0
local lastResults = {}      -- itemID -> ladder of the last per-item scan

local function AcquireLadder()
	local l
	if ladderPoolN > 0 then
		l = ladderPool[ladderPoolN]
		ladderPool[ladderPoolN] = nil
		ladderPoolN = ladderPoolN - 1
	else
		l = { unitPrices = {}, quantities = {}, auctionIDs = {}, own = {}, timeLefts = {}, suffixes = {} }
	end
	l.n = 0
	l.prevN = 0
	l.isCommodity = false
	l.ts = 0
	l.itemID = 0
	l.suffix = 0
	l.hasSuffix = false
	l.totalQuantity = 0
	l.marketValue = nil
	l.minBuyout = nil
	l.pages = 0
	return l
end

local function LadderTrim(l, fromN)
	local n = l.n
	if fromN > n then
		local up, q, a, o, t, s = l.unitPrices, l.quantities, l.auctionIDs, l.own, l.timeLefts, l.suffixes
		for i = fromN, n + 1, -1 do
			up[i] = nil
			q[i] = nil
			a[i] = nil
			o[i] = nil
			t[i] = nil
			s[i] = nil
		end
	end
	l.prevN = n
end

local function ReleaseLadder(l)
	if ladderPoolN >= LADDER_POOL_MAX then return end
	local filled = math_max(l.n or 0, l.prevN or 0)
	l.n = 0
	LadderTrim(l, filled)
	ladderPoolN = ladderPoolN + 1
	ladderPool[ladderPoolN] = l
end

local function LadderBegin(l)
	l.prevN = math_max(l.prevN or 0, l.n or 0)
	l.n = 0
	l.totalQuantity = 0
	l.hasSuffix = false
	l.marketValue = nil
	l.minBuyout = nil
end

local function LadderAdd(l, unitPrice, quantity, auctionID, own, timeLeft, suffix)
	local n = l.n + 1
	l.n = n
	l.unitPrices[n] = unitPrice
	l.quantities[n] = quantity
	l.auctionIDs[n] = auctionID or 0
	l.own[n] = own and true or false
	l.timeLefts[n] = timeLeft or 0
	suffix = suffix or 0
	l.suffixes[n] = suffix
	if suffix ~= 0 then l.hasSuffix = true end
	l.totalQuantity = l.totalQuantity + quantity
end

local function LadderEnd(l)
	LadderTrim(l, l.prevN or 0)
end

-------------------------------------------------------------------------------
-- Market recording helpers
-------------------------------------------------------------------------------
local scratchPrices, scratchQty, scratchSuffixes = {}, {}, {}

-- Computes market stats for parallel arrays and records them; returns marketValue, minBuyout, totalQty.
local function RecordStats(itemID, suffix, isCommodity, prices, qtys, n, now)
	if n <= 0 then return nil end
	local Market = FL.Market
	if not Market or not Market.ComputeMarketValue or not Market.Record then return nil end
	local mv, minBuyout, totalQty = Market.ComputeMarketValue(prices, qtys, n)
	local prevQty, prevTs
	if Market.Get then
		prevQty = Market.Get(itemID, "lastSeenQty", suffix)
		prevTs = Market.Get(itemID, "lastSeenTs", suffix)
	end
	Market.Record(itemID, suffix, isCommodity and true or false, mv or 0, minBuyout or 0, n, totalQty or 0, now)
	if Market.ApplySaleEstimate and prevTs and prevTs > 0 and prevQty and prevQty > 0 then
		local dt = now - prevTs
		-- Only apply when Record left the lastSeen bookkeeping untouched (avoids double EMA updates).
		local seenTs = Market.Get and Market.Get(itemID, "lastSeenTs", suffix)
		if dt > 0 and seenTs == prevTs then
			Market.ApplySaleEstimate(itemID, suffix, prevQty, totalQty or 0, dt)
		end
	end
	return mv, minBuyout, totalQty
end

-- Records a per-item ladder; groups by suffix when the ladder mixes suffixed variants.
local function RecordLadder(l, now)
	if l.n == 0 then return end
	if not l.hasSuffix then
		local mv, mb = RecordStats(l.itemID, 0, l.isCommodity, l.unitPrices, l.quantities, l.n, now)
		l.marketValue, l.minBuyout = mv, mb
		return
	end
	local suf, prices, qtys = l.suffixes, l.unitPrices, l.quantities
	local distinct = 0
	for i = 1, l.n do
		local s = suf[i]
		local seen = false
		for j = 1, distinct do
			if scratchSuffixes[j] == s then seen = true break end
		end
		if not seen then
			distinct = distinct + 1
			scratchSuffixes[distinct] = s
		end
	end
	local bestMV, bestMin
	for j = 1, distinct do
		local s = scratchSuffixes[j]
		local m = 0
		for i = 1, l.n do
			if suf[i] == s then
				m = m + 1
				scratchPrices[m] = prices[i]
				scratchQty[m] = qtys[i]
			end
		end
		for i = #scratchPrices, m + 1, -1 do
			scratchPrices[i] = nil
			scratchQty[i] = nil
		end
		local mv, mb = RecordStats(l.itemID, s, l.isCommodity, scratchPrices, scratchQty, m, now)
		if mb and (not bestMin or mb < bestMin) then bestMin = mb end
		if mv and (not bestMV or mv < bestMV) then bestMV = mv end
	end
	for j = distinct, 1, -1 do scratchSuffixes[j] = nil end
	l.marketValue, l.minBuyout = bestMV, bestMin
end

-------------------------------------------------------------------------------
-- Commodity detection cache
-------------------------------------------------------------------------------
local commodityCache = {}   -- itemID -> boolean

local function IsCommodityItem(itemID, observedCount, allowKeyInfo)
	local c = commodityCache[itemID]
	if c ~= nil then return c end
	if C_Item and C_Item.GetItemInfo then
		local _, _, _, _, _, _, _, stackCount = C_Item.GetItemInfo(itemID)
		if stackCount then
			c = stackCount > 1
			commodityCache[itemID] = c
			return c
		end
	end
	if allowKeyInfo and GetItemKeyInfo and MakeItemKey then
		local ok, info = pcall(GetItemKeyInfo, MakeItemKey(itemID))
		if ok and info and info.isCommodity ~= nil then
			c = info.isCommodity and true or false
			commodityCache[itemID] = c
			return c
		end
	end
	if observedCount and observedCount > 1 then return true end
	return false
end

-------------------------------------------------------------------------------
-- Request queue (FIFO with O(1) pop) and request pool
-- request = { kind="search"|"browse"|"replicate"|"owned", itemID, itemKey,
--             isCommodity, query, onPage, cb, quiet, serial, retries, pages,
--             sentAt, needMore, startedMs }
-------------------------------------------------------------------------------
local queue, qHead, qTail = {}, 1, 0
local requestPool = {}
local inflight = nil
local requestSerial = 0

local function AcquireRequest(kind)
	local n = #requestPool
	local r
	if n > 0 then
		r = requestPool[n]
		requestPool[n] = nil
	else
		r = {}
	end
	requestSerial = requestSerial + 1
	r.kind = kind
	r.serial = requestSerial
	r.retries = 0
	r.pages = 0
	r.sentAt = 0
	r.needMore = false
	r.startedMs = debugprofilestop()
	return r
end

local function ReleaseRequest(r)
	wipe(r)
	requestPool[#requestPool + 1] = r
end

local function QueuePush(r)
	qTail = qTail + 1
	queue[qTail] = r
end

local function QueuePushFront(r)
	qHead = qHead - 1
	queue[qHead] = r
end

local function QueuePop()
	if qHead > qTail then return nil end
	local r = queue[qHead]
	queue[qHead] = nil
	qHead = qHead + 1
	if qHead > qTail then
		qHead, qTail = 1, 0
	end
	return r
end

local function QueueLength()
	return qTail - qHead + 1
end

local function HasRequestOfKind(kind)
	if inflight and inflight.kind == kind then return true end
	for i = qHead, qTail do
		local r = queue[i]
		if r and r.kind == kind then return true end
	end
	return false
end

-- Invokes a request's completion callback with a failure reason.
local function FailRequest(r, reason)
	local kind, cb = r.kind, r.cb
	if kind == "search" then
		if cb then SafeCall(cb, r.itemID, nil, reason) end
	elseif kind == "browse" then
		if cb then SafeCall(cb, nil, reason) end
	elseif kind == "owned" then
		if cb then SafeCall(cb, nil, reason) end
	elseif kind == "replicate" then
		AuctionScan.progress = 0
		AuctionScan.progressText = "Full scan failed: " .. tostring(reason)
	end
end

-------------------------------------------------------------------------------
-- Full-scan processing state and public state bookkeeping
-------------------------------------------------------------------------------
local full = {
	active = false,
	phase = "",
	cursor = 0,
	num = 0,
	startedMs = 0,
	numAuctions = 0,
	numSkipped = 0,
	list = {},
	listN = 0,
	map = {},
	finalizeCursor = 0,
	keepRaw = false,
	rawDB = nil,
}

local function UpdateState()
	local s
	if full.active then
		s = "full"
	elseif inflight then
		local kind = inflight.kind
		if kind == "replicate" then
			s = "full"
		elseif kind == "browse" then
			local sn = FL.Sniper
			if sn and sn.IsRunning and sn:IsRunning() then
				s = "sniper"
			else
				s = "browse"
			end
		else
			s = "search"
		end
	else
		s = "idle"
	end
	AuctionScan.state = s
end

-------------------------------------------------------------------------------
-- Throttle engine: sending, paging, timeouts, ticker
-------------------------------------------------------------------------------
local ticker = nil
local fpsSkips = 0
local lastTickErrorAt = 0
local Tick -- forward declaration (defined below)
local HandleCommodityResults, HandleItemResults, HandleBrowseResults -- forward declarations

local function ThrottleReady()
	if IsThrottledMessageSystemReady then
		return IsThrottledMessageSystemReady() and true or false
	end
	return true
end

-- Sends a queued request to the server; returns true when it became in-flight.
local function SendRequest(r)
	local kind = r.kind
	local ok = false
	if kind == "replicate" then
		if ReplicateItems then
			ok = pcall(ReplicateItems)
			if ok then
				local now = time()
				AuctionScan.lastFullScanAt = now
				AuctionScan.nextFullScanAt = now + FULL_SCAN_COOLDOWN
				AuctionScan.progress = 0
				AuctionScan.progressText = "Waiting for auction house data..."
				full.startedMs = r.startedMs or debugprofilestop()
			end
		end
	elseif kind == "search" then
		if SendSearchQuery then
			if not r.itemKey and MakeItemKey then
				r.itemKey = MakeItemKey(r.itemID)
			end
			if r.itemKey then
				ok = pcall(SendSearchQuery, r.itemKey, SORTS_PRICE, false)
			end
		end
	elseif kind == "browse" then
		if SendBrowseQuery and r.query then
			ok = pcall(SendBrowseQuery, r.query)
		end
	elseif kind == "owned" then
		if QueryOwnedAuctions then
			ok = pcall(QueryOwnedAuctions, SORTS_PRICE)
		end
	end
	if not ok then
		FL:Debug("AuctionScan: could not send %s request", tostring(kind))
		FailRequest(r, "unsupported")
		ReleaseRequest(r)
		UpdateState()
		return false
	end
	r.sentAt = GetTime()
	r.needMore = false
	inflight = r
	UpdateState()
	FL:Debug("AuctionScan: sent %s request%s", kind, r.itemID and (" for item " .. tostring(r.itemID)) or "")
	return true
end

-- Requests the next page for an in-flight search/browse request.
local function RequestMore(r)
	local alreadyFull = nil
	local ok = true
	if r.kind == "search" then
		if r.isCommodity then
			if RequestMoreCommoditySearchResults then
				ok, alreadyFull = pcall(RequestMoreCommoditySearchResults, r.itemID)
			end
		elseif r.itemKey then
			if RequestMoreItemSearchResults then
				ok, alreadyFull = pcall(RequestMoreItemSearchResults, r.itemKey)
			end
		end
	elseif r.kind == "browse" then
		if RequestMoreBrowseResults then
			ok, alreadyFull = pcall(RequestMoreBrowseResults)
		end
	end
	r.needMore = false
	r.sentAt = GetTime()
	r.pages = r.pages + 1
	if not ok then
		FL:Debug("AuctionScan: RequestMore failed for %s", tostring(r.kind))
		return
	end
	if alreadyFull == true then
		-- The API reports the client already holds the complete result set; verify with
		-- HasFull* before processing so a "request sent" return can never recurse.
		if r.kind == "search" then
			if r.isCommodity then
				if HasFullCommoditySearchResults and HasFullCommoditySearchResults(r.itemID) then
					HandleCommodityResults(r.itemID)
				end
			elseif r.itemKey then
				if HasFullItemSearchResults and HasFullItemSearchResults(r.itemKey) then
					HandleItemResults(r.itemKey)
				end
			end
		elseif r.kind == "browse" then
			if HasFullBrowseResults and HasFullBrowseResults() then
				HandleBrowseResults(nil)
			end
		end
	end
end

-- Attempts to page immediately; otherwise the ticker pages when the throttle is ready.
local function TryRequestMore(r)
	r.needMore = true
	if ThrottleReady() then
		RequestMore(r)
	end
end

-- Handles an in-flight request that received no response in time.
local function RetryOrDrop(r, why)
	inflight = nil
	r.retries = r.retries + 1
	local maxRetries = (r.kind == "replicate") and 1 or MAX_RETRIES
	if r.retries > maxRetries then
		FL:Warn("Auction request (%s%s) %s after %d attempts; dropped.", tostring(r.kind), r.itemID and (" item " .. tostring(r.itemID)) or "", why, maxRetries)
		FailRequest(r, why)
		ReleaseRequest(r)
	else
		FL:Debug("AuctionScan: %s request %s, retry %d", tostring(r.kind), why, r.retries)
		r.needMore = false
		r.pages = 0
		QueuePushFront(r)
	end
	UpdateState()
end

Tick = function()
	if not AuctionScan.isOpen then return end
	local now = GetTime()
	if inflight then
		local limit = (inflight.kind == "replicate") and REPLICATE_TIMEOUT or REQUEST_TIMEOUT
		if now - inflight.sentAt > limit then
			RetryOrDrop(inflight, "timeout")
		else
			if inflight.needMore and ThrottleReady() then
				RequestMore(inflight)
			end
			return
		end
	end
	if inflight then return end
	if QueueLength() <= 0 then return end
	local minFPS = tonumber(ScanSetting("minFPS")) or 15
	if GetFramerate and minFPS > 0 and GetFramerate() < minFPS then
		fpsSkips = fpsSkips + 1
		if fpsSkips < FPS_SKIP_LIMIT then return end
	end
	fpsSkips = 0
	if not ThrottleReady() then return end
	local r = QueuePop()
	if not r then return end
	SendRequest(r)
end

local function SafeTick()
	local ok, err = pcall(Tick)
	if not ok then
		local now = GetTime()
		if now - lastTickErrorAt > 10 then
			lastTickErrorAt = now
			FL:Warn("AuctionScan tick error: %s", tostring(err))
		end
	end
end

local function StopTicker()
	if ticker then
		if ticker.Cancel then ticker:Cancel() end
		ticker = nil
	end
end

local function StartTicker()
	StopTicker()
	local interval = tonumber(ScanSetting("requestIntervalSec")) or 0.35
	if interval < 0.1 then interval = 0.1 end
	if C_Timer and C_Timer.NewTicker then
		ticker = C_Timer.NewTicker(interval, SafeTick)
	end
end

-- Queues a prepared request and kicks the throttle engine.
local function Submit(r)
	QueuePush(r)
	UpdateState()
	SafeTick()
	return true
end

-------------------------------------------------------------------------------
-- Full scan (ReplicateItems) — time-sliced processing on a hidden OnUpdate frame
-------------------------------------------------------------------------------
local driver = CreateFrame("Frame")
driver:Hide()

local rawRow = { itemID = 0, suffix = 0, unitPrice = 0, quantity = 0, auctionID = 0, timeLeft = 0, isCommodity = false, own = false }

local function OnPendingItemLoaded(itemID)
	AuctionScan.pendingItemLoads[itemID] = nil
end

local function ReleaseFullLadders()
	local list = full.list
	for i = full.listN, 1, -1 do
		ReleaseLadder(list[i])
		list[i] = nil
	end
	full.listN = 0
	wipe(full.map)
end

local function AbortFullScan(reason)
	if not full.active then return end
	ReleaseFullLadders()
	full.active = false
	full.phase = ""
	full.cursor = 0
	full.num = 0
	full.startedMs = 0
	full.rawDB = nil
	driver:Hide()
	AuctionScan.progress = 0
	AuctionScan.progressText = reason and ("Full scan aborted: " .. tostring(reason)) or ""
	UpdateState()
end

local function BeginFullProcessing(num)
	if full.active then
		ReleaseFullLadders()
	end
	full.active = true
	full.phase = "collect"
	full.cursor = 0
	full.num = num
	full.numAuctions = 0
	full.numSkipped = 0
	full.finalizeCursor = 0
	if full.startedMs <= 0 then full.startedMs = debugprofilestop() end
	full.keepRaw = ScanSetting("keepRawAuctions") and true or false
	full.rawDB = nil
	if full.keepRaw and FL.DB and FL.DB.auctions then
		full.rawDB = FL.DB.auctions
		if full.rawDB.Truncate then full.rawDB:Truncate() end
	end
	AuctionScan.progress = 0
	AuctionScan.progressText = string_format("Scanning 0 / %d auctions", num)
	UpdateState()
	driver:Show()
end

-- Processes one replicate row (0-based index) into the per-item ladders.
local function ProcessReplicateRow(i)
	local _, _, count, _, _, _, _, _, _, buyout, _, _, _, _, _, _, itemID, hasAllInfo = GetReplicateItemInfo(i)
	if not itemID or not buyout or buyout <= 0 or not count or count <= 0 then
		full.numSkipped = full.numSkipped + 1
		return
	end
	local unitPrice = math_floor(buyout / count)
	if unitPrice <= 0 then
		full.numSkipped = full.numSkipped + 1
		return
	end
	local suffix = 0
	if GetReplicateItemLink then
		local link = GetReplicateItemLink(i)
		if link then
			suffix = FL.ItemSuffixFromLink(link) or 0
		end
	end
	local key
	if suffix == 0 then
		key = itemID
	else
		key = -(itemID * SUFFIX_KEY_BASE + suffix + SUFFIX_KEY_OFFSET)
	end
	local l = full.map[key]
	if not l then
		l = AcquireLadder()
		l.itemID = itemID
		l.suffix = suffix
		l.isCommodity = IsCommodityItem(itemID, count, false)
		full.map[key] = l
		full.listN = full.listN + 1
		full.list[full.listN] = l
	elseif not l.isCommodity and count > 1 and commodityCache[itemID] == nil then
		l.isCommodity = true
	end
	local timeLeft = 0
	if GetReplicateItemTimeLeft then
		timeLeft = GetReplicateItemTimeLeft(i) or 0
	end
	LadderAdd(l, unitPrice, count, 0, false, timeLeft, suffix)
	full.numAuctions = full.numAuctions + 1
	if hasAllInfo == false and not AuctionScan.pendingItemLoads[itemID] then
		AuctionScan.pendingItemLoads[itemID] = true
		if FL.RequestItem then
			FL.RequestItem(itemID, OnPendingItemLoaded)
		end
	end
end

local function InsertRawRows(db, l)
	local n = l.n
	local up, q, a, t = l.unitPrices, l.quantities, l.auctionIDs, l.timeLefts
	rawRow.itemID = l.itemID
	rawRow.suffix = l.suffix or 0
	rawRow.isCommodity = l.isCommodity and true or false
	rawRow.own = false
	for i = 1, n do
		rawRow.unitPrice = up[i]
		rawRow.quantity = q[i]
		rawRow.auctionID = a[i] or 0
		rawRow.timeLeft = t[i] or 0
		local ok, err = pcall(db.Insert, db, rawRow)
		if not ok then
			FL:Debug("AuctionScan: raw auction insert failed: %s", tostring(err))
			return
		end
	end
end

-- Records finalized ladders within the frame budget; returns true when all are done.
local function FinalizeStep(budgetEnd)
	local now = time()
	local rawDB = full.rawDB
	local list = full.list
	local listN = full.listN
	local cursor = full.finalizeCursor
	while cursor < listN do
		if debugprofilestop() >= budgetEnd then
			full.finalizeCursor = cursor
			return false
		end
		cursor = cursor + 1
		local l = list[cursor]
		LadderEnd(l)
		local ok, err = pcall(RecordStats, l.itemID, l.suffix, l.isCommodity, l.unitPrices, l.quantities, l.n, now)
		if not ok then
			FL:Debug("AuctionScan: record failed for item %s: %s", tostring(l.itemID), tostring(err))
		end
		if rawDB then
			InsertRawRows(rawDB, l)
		end
	end
	full.finalizeCursor = cursor
	return true
end

local function FinishFullScan()
	local elapsedMs = debugprofilestop() - full.startedMs
	if elapsedMs < 0 then elapsedMs = 0 end
	local numItems, numAuctions = full.listN, full.numAuctions
	ReleaseFullLadders()
	full.active = false
	full.phase = ""
	full.cursor = 0
	full.num = 0
	full.startedMs = 0
	full.rawDB = nil
	driver:Hide()
	AuctionScan.progress = 1
	AuctionScan.progressText = string_format("Full scan complete: %d items", numItems)
	UpdateState()
	FL.Fire("FL_SCAN_FINISHED", "full", numItems, numAuctions, elapsedMs)
	FL.Fire("FL_MARKET_UPDATED")
	FL:Print("Full scan complete: %d auctions, %d items in %.1fs.", numAuctions, numItems, elapsedMs / 1000)
end

local function OnUpdateDriver()
	if not full.active then
		driver:Hide()
		return
	end
	if not GetReplicateItemInfo then
		AbortFullScan("GetReplicateItemInfo unavailable")
		return
	end
	local budget = tonumber(ScanSetting("chunkMs")) or 8
	if budget < 1 then budget = 1 end
	local budgetEnd = debugprofilestop() + budget
	if full.phase == "collect" then
		local num = full.num
		local cursor = full.cursor
		local sinceCheck = 0
		while cursor < num do
			ProcessReplicateRow(cursor)
			cursor = cursor + 1
			sinceCheck = sinceCheck + 1
			if sinceCheck >= ROWS_PER_CLOCK_CHECK then
				sinceCheck = 0
				if debugprofilestop() >= budgetEnd then break end
			end
		end
		full.cursor = cursor
		if num > 0 then
			AuctionScan.progress = (cursor / num) * 0.9
		end
		AuctionScan.progressText = string_format("Scanning %d / %d auctions", cursor, num)
		if cursor >= num then
			full.phase = "finalize"
			full.finalizeCursor = 0
		end
		return
	end
	if full.phase == "finalize" then
		if FinalizeStep(budgetEnd) then
			FinishFullScan()
		else
			local listN = math_max(1, full.listN)
			AuctionScan.progress = 0.9 + 0.1 * (full.finalizeCursor / listN)
			AuctionScan.progressText = string_format("Recording %d / %d items", full.finalizeCursor, full.listN)
		end
		return
	end
	AbortFullScan("unknown phase")
end

driver:SetScript("OnUpdate", function()
	local ok, err = pcall(OnUpdateDriver)
	if not ok then
		AbortFullScan("error")
		FL:Warn("Full scan processing error: %s", tostring(err))
	end
end)

local function OnReplicateListUpdate()
	local ours = false
	if inflight and inflight.kind == "replicate" then
		local r = inflight
		inflight = nil
		ours = true
		ReleaseRequest(r)
		UpdateState()
	end
	if not AuctionScan.isOpen then return end
	local num = 0
	if GetNumReplicateItems then
		num = GetNumReplicateItems() or 0
	end
	if num <= 0 then
		if ours then
			AuctionScan.nextFullScanAt = time() + EMPTY_SCAN_RETRY
			AuctionScan.progress = 0
			AuctionScan.progressText = "Full scan returned no data"
			full.startedMs = 0
			UpdateState()
			FL:Warn("Full scan returned an empty list (the server throttled the request). Try again in a minute.")
			FL.Fire("FL_SCAN_FINISHED", "full", 0, 0, 0)
		end
		SafeTick()
		return
	end
	local now = time()
	if AuctionScan.lastFullScanAt <= 0 or now - AuctionScan.lastFullScanAt > FULL_SCAN_COOLDOWN then
		-- Data produced by another addon's ReplicateItems call: the cooldown is shared.
		AuctionScan.lastFullScanAt = now
		AuctionScan.nextFullScanAt = now + FULL_SCAN_COOLDOWN
	end
	BeginFullProcessing(num)
	SafeTick()
end

-------------------------------------------------------------------------------
-- Per-item searches (commodities and items) with paging
-------------------------------------------------------------------------------
local function GetOrCreateResults(itemID)
	local l = lastResults[itemID]
	if not l then
		l = AcquireLadder()
		l.itemID = itemID
		lastResults[itemID] = l
	end
	return l
end

local function PrintItemSummary(itemID, l)
	local label = ItemLabel(itemID)
	if l.n == 0 then
		FL:Print("%s: no buyout auctions found.", label)
		return
	end
	FL:Print("%s: %d auctions, %d units, min buyout %s, market value %s.", label, l.n, l.totalQuantity,
		FL.FormatMoney(l.minBuyout or 0), FL.FormatMoney(l.marketValue or 0))
end

-- Finalizes a search request: records market data, stores the ladder, notifies.
local function CompleteSearch(r, l)
	LadderEnd(l)
	local now = time()
	l.ts = now
	l.pages = r.pages
	local itemID = r.itemID
	commodityCache[itemID] = l.isCommodity and true or false
	local ok, err = pcall(RecordLadder, l, now)
	if not ok then
		FL:Debug("AuctionScan: record failed for item %s: %s", tostring(itemID), tostring(err))
	end
	local elapsedMs = debugprofilestop() - (r.startedMs or debugprofilestop())
	local cb, quiet = r.cb, r.quiet
	if inflight == r then inflight = nil end
	ReleaseRequest(r)
	AuctionScan.progressText = ""
	UpdateState()
	FL.Fire("FL_SCAN_FINISHED", "item", 1, l.n, elapsedMs)
	FL.Fire("FL_MARKET_UPDATED", itemID)
	if cb then
		SafeCall(cb, itemID, l)
	elseif not quiet then
		PrintItemSummary(itemID, l)
	end
	SafeTick()
end

HandleCommodityResults = function(itemID)
	local r = inflight
	if not r or r.kind ~= "search" or r.itemID ~= itemID then return end
	r.isCommodity = true
	local num = 0
	if GetNumCommoditySearchResults then
		num = GetNumCommoditySearchResults(itemID) or 0
	end
	local l = GetOrCreateResults(itemID)
	LadderBegin(l)
	l.isCommodity = true
	if GetCommoditySearchResultInfo then
		for i = 1, num do
			local info = GetCommoditySearchResultInfo(itemID, i)
			if info then
				local unit, qty = info.unitPrice, info.quantity
				if unit and unit > 0 and qty and qty > 0 then
					LadderAdd(l, unit, qty, info.auctionID or 0, info.containsOwnerItem, info.timeLeftSeconds or 0, 0)
				end
			end
		end
	end
	r.sentAt = GetTime()
	local hasFull = true
	if HasFullCommoditySearchResults then
		hasFull = HasFullCommoditySearchResults(itemID) and true or false
	end
	if not hasFull and r.pages < MAX_PAGES then
		AuctionScan.progressText = string_format("Scanning %s (page %d)", ItemPlainName(itemID), r.pages + 2)
		TryRequestMore(r)
		return
	end
	CompleteSearch(r, l)
end

HandleItemResults = function(itemKey)
	local r = inflight
	if not r or r.kind ~= "search" then return end
	local keyID = itemKey and itemKey.itemID
	if keyID ~= r.itemID then return end
	r.isCommodity = false
	r.itemKey = itemKey
	local num = 0
	if GetNumItemSearchResults then
		num = GetNumItemSearchResults(itemKey) or 0
	end
	local l = GetOrCreateResults(r.itemID)
	LadderBegin(l)
	l.isCommodity = false
	if GetItemSearchResultInfo then
		for i = 1, num do
			local info = GetItemSearchResultInfo(itemKey, i)
			if info then
				local buyout = info.buyoutAmount
				local qty = info.quantity or 1
				if buyout and buyout > 0 and qty > 0 then
					local suffix = 0
					local ik = info.itemKey
					if ik and ik.itemSuffix and ik.itemSuffix ~= 0 then
						suffix = ik.itemSuffix
					elseif info.itemLink then
						suffix = FL.ItemSuffixFromLink(info.itemLink) or 0
					end
					LadderAdd(l, math_floor(buyout / qty), qty, info.auctionID or 0, info.containsOwnerItem, info.timeLeftSeconds or info.timeLeft or 0, suffix)
				end
			end
		end
	end
	r.sentAt = GetTime()
	local hasFull = true
	if HasFullItemSearchResults then
		hasFull = HasFullItemSearchResults(itemKey) and true or false
	end
	if not hasFull and r.pages < MAX_PAGES then
		AuctionScan.progressText = string_format("Scanning %s (page %d)", ItemPlainName(r.itemID), r.pages + 2)
		TryRequestMore(r)
		return
	end
	CompleteSearch(r, l)
end

-------------------------------------------------------------------------------
-- Browse scans with paging
-------------------------------------------------------------------------------
local function CompleteBrowse(r, ok, reason)
	local cb = r.cb
	if inflight == r then inflight = nil end
	ReleaseRequest(r)
	AuctionScan.progressText = ""
	UpdateState()
	if cb then
		if ok then
			local results = GetBrowseResults and GetBrowseResults() or EMPTY
			SafeCall(cb, results)
		else
			SafeCall(cb, nil, reason)
		end
	end
	SafeTick()
end

HandleBrowseResults = function(added)
	local r = inflight
	if not r or r.kind ~= "browse" then return end
	local results = added
	if not results then
		results = GetBrowseResults and GetBrowseResults() or EMPTY
	end
	local hasFull = true
	if HasFullBrowseResults then
		hasFull = HasFullBrowseResults() and true or false
	end
	r.sentAt = GetTime()
	local stop = false
	if r.onPage then
		local ok, ret = pcall(r.onPage, results, hasFull)
		if not ok then
			FL:Warn("AuctionScan browse page callback error: %s", tostring(ret))
			stop = true
		elseif ret == true then
			stop = true
		end
	end
	if inflight ~= r then return end
	if not hasFull and not stop and r.pages < MAX_PAGES then
		AuctionScan.progressText = string_format("Browsing (page %d)", r.pages + 2)
		TryRequestMore(r)
		return
	end
	CompleteBrowse(r, true)
end

local function OnBrowseFailure()
	local r = inflight
	if not r or r.kind ~= "browse" then return end
	FL:Debug("AuctionScan: browse query failed")
	CompleteBrowse(r, false, "failure")
end

-------------------------------------------------------------------------------
-- Owned auctions
-------------------------------------------------------------------------------
local ownedEntryPool = {}

local function RefreshOwnedByItem(owned)
	local map = AuctionScan.ownedByItem
	for k, v in pairs(map) do
		map[k] = nil
		ownedEntryPool[#ownedEntryPool + 1] = v
	end
	for i = 1, #owned do
		local a = owned[i]
		local itemID = a and a.itemKey and a.itemKey.itemID
		if itemID and (a.status == nil or a.status == 0) then
			local e = map[itemID]
			if not e then
				e = table_remove(ownedEntryPool)
				if not e then e = {} end
				e.count = 0
				e.numAuctions = 0
				e.minBuyoutUnit = nil
				map[itemID] = e
			end
			local qty = a.quantity or 1
			if qty <= 0 then qty = 1 end
			e.count = e.count + qty
			e.numAuctions = e.numAuctions + 1
			local buyout = a.buyoutAmount
			if buyout and buyout > 0 then
				local unit = math_floor(buyout / qty)
				if not e.minBuyoutUnit or unit < e.minBuyoutUnit then
					e.minBuyoutUnit = unit
				end
			end
		end
	end
end

local function OnOwnedAuctionsUpdated()
	local owned = GetOwnedAuctions and GetOwnedAuctions() or EMPTY
	RefreshOwnedByItem(owned)
	if FL.Inventory and FL.Inventory.UpdateAuctions then
		SafeCall(FL.Inventory.UpdateAuctions, owned)
	end
	local r = inflight
	if r and r.kind == "owned" then
		local cb = r.cb
		inflight = nil
		ReleaseRequest(r)
		UpdateState()
		if cb then SafeCall(cb, owned) end
		SafeTick()
	end
end

-------------------------------------------------------------------------------
-- Purchase flows (hardware events run inside FL.Secure "buy" actions)
-- purchase = { kind="commodity"|"item", serial, itemID, quantity, expectedUnitPrice,
--              auctionID, buyoutAmount, onDone, state, unitPrice, totalPrice }
-- commodity states: armed -> awaitPrice -> awaitConfirm -> awaitResult
-- item states:      armed -> awaitResult
-------------------------------------------------------------------------------
local purchase = nil
local purchaseSerial = 0
local deferredDisarm = false

local function DisarmBuy()
	local Secure = FL.Secure
	if not Secure or not Secure.Disarm then return end
	if InCombat() then
		deferredDisarm = true
		return
	end
	deferredDisarm = false
	pcall(Secure.Disarm, "buy")
end

local function ArmBuy(label, fn, onFail)
	local Secure = FL.Secure
	if not Secure or not Secure.Arm then return false end
	if InCombat() then return false end
	local ok, res = pcall(Secure.Arm, "buy", { label = label, fn = fn, onFail = onFail })
	if not ok then
		FL:Warn("AuctionScan: could not arm the buy button: %s", tostring(res))
		return false
	end
	return res ~= false
end

local function FinishPurchase(ok, reason, extra)
	local p = purchase
	if not p then return end
	purchase = nil
	DisarmBuy()
	if p.onDone then
		SafeCall(p.onDone, ok, reason, extra)
	end
end

local function CancelServerPurchase(p)
	if p.kind == "commodity" and CancelCommoditiesPurchase and (p.state == "awaitPrice" or p.state == "awaitConfirm") then
		pcall(CancelCommoditiesPurchase)
	end
end

local function SchedulePurchaseTimeout(p, seconds, expectedState)
	local serial = p.serial
	After(seconds, function()
		local cur = purchase
		if cur and cur.serial == serial and cur.state == expectedState then
			CancelServerPurchase(cur)
			FinishPurchase(false, "timeout")
		end
	end)
end

local function LedgerPurchase(p, total, quantity, note)
	if FL.Ledger and FL.Ledger.Add then
		local ok, err = pcall(FL.Ledger.Add, "purchase", p.itemID, quantity, total, "", "ah", note, time())
		if not ok then
			FL:Debug("AuctionScan: ledger add failed: %s", tostring(err))
		end
	end
end

local function OnCommodityPriceUpdated(unit, total)
	local p = purchase
	if not p or p.kind ~= "commodity" or p.state ~= "awaitPrice" then return end
	unit = tonumber(unit) or 0
	total = tonumber(total) or (unit * p.quantity)
	p.unitPrice, p.totalPrice = unit, total
	local limit = p.expectedUnitPrice * (1 + PriceTolerance())
	if unit > 0 and unit <= limit then
		p.state = "awaitConfirm"
		local armed = ArmBuy(string_format("CONFIRM %s", FL.FormatMoney(total)), function()
			local cur = purchase
			if cur ~= p or p.state ~= "awaitConfirm" then return end
			p.state = "awaitResult"
			ConfirmCommoditiesPurchase(p.itemID, p.quantity)
			SchedulePurchaseTimeout(p, PURCHASE_TIMEOUT, "awaitResult")
		end, function(err)
			if purchase == p then
				CancelServerPurchase(p)
				FinishPurchase(false, "error", err)
			end
		end)
		if not armed then
			CancelServerPurchase(p)
			FinishPurchase(false, "combat")
		end
	else
		CancelServerPurchase(p)
		FinishPurchase(false, "price_changed", unit)
	end
end

local function OnCommodityPriceUnavailable()
	local p = purchase
	if not p or p.kind ~= "commodity" then return end
	if p.state ~= "awaitPrice" and p.state ~= "awaitConfirm" then return end
	FinishPurchase(false, "unavailable")
end

local function OnCommodityPurchaseSucceeded()
	local p = purchase
	if not p or p.kind ~= "commodity" then return end
	if p.state ~= "awaitResult" and p.state ~= "awaitConfirm" then return end
	local qty = p.purchasedQuantity or p.quantity
	local total = p.totalPrice or ((p.unitPrice or p.expectedUnitPrice or 0) * qty)
	LedgerPurchase(p, total, qty, "commodity")
	FinishPurchase(true, "ok", total)
end

local function OnCommodityPurchaseFailed()
	local p = purchase
	if not p or p.kind ~= "commodity" then return end
	if p.state == "armed" then return end
	FinishPurchase(false, "failed")
end

local function OnCommodityPurchased(itemID, quantity)
	local p = purchase
	if not p or p.kind ~= "commodity" or p.itemID ~= itemID then return end
	p.purchasedQuantity = tonumber(quantity) or p.quantity
end

local function OnAuctionPurchaseCompleted(auctionID)
	local p = purchase
	if not p or p.kind ~= "item" then return end
	if auctionID ~= nil and p.auctionID ~= nil and auctionID ~= p.auctionID then return end
	if p.state ~= "awaitResult" then return end
	LedgerPurchase(p, p.buyoutAmount or 0, p.quantity or 1, "buyout")
	FinishPurchase(true, "ok", p.buyoutAmount)
end

local function OnAuctionHouseShowError(err)
	local p = purchase
	if not p or p.state == "armed" then return end
	CancelServerPurchase(p)
	if err == nil then err = "error" end
	FinishPurchase(false, err)
end

-- Starts a commodity purchase: arms the buy button, then confirms after the price update.
function AuctionScan:BeginCommodityPurchase(itemID, quantity, expectedUnitPrice, onDone)
	itemID = tonumber(itemID)
	quantity = math_floor(tonumber(quantity) or 0)
	expectedUnitPrice = tonumber(expectedUnitPrice) or 0
	if not itemID or itemID <= 0 or quantity <= 0 then
		if onDone then SafeCall(onDone, false, "invalid") end
		return false, "invalid"
	end
	if not self.isOpen then
		if onDone then SafeCall(onDone, false, "closed") end
		return false, "closed"
	end
	if not StartCommoditiesPurchase or not ConfirmCommoditiesPurchase then
		if onDone then SafeCall(onDone, false, "unsupported") end
		return false, "unsupported"
	end
	if purchase then self:CancelPurchase() end
	purchaseSerial = purchaseSerial + 1
	local p = {
		kind = "commodity", serial = purchaseSerial, itemID = itemID, quantity = quantity,
		expectedUnitPrice = expectedUnitPrice, onDone = onDone, state = "armed",
	}
	purchase = p
	local label = string_format("BUY %dx %s ≤ %s", quantity, ItemPlainName(itemID), FL.FormatMoney(expectedUnitPrice))
	local armed = ArmBuy(label, function()
		local cur = purchase
		if cur ~= p or p.state ~= "armed" then return end
		p.state = "awaitPrice"
		StartCommoditiesPurchase(itemID, quantity)
		SchedulePurchaseTimeout(p, PURCHASE_TIMEOUT, "awaitPrice")
	end, function(err)
		if purchase == p then
			CancelServerPurchase(p)
			FinishPurchase(false, "error", err)
		end
	end)
	if not armed then
		purchase = nil
		if onDone then SafeCall(onDone, false, "combat") end
		return false, "combat"
	end
	return true
end

-- Starts an item buyout: arms the buy button with PlaceBid(auctionID, buyoutAmount).
function AuctionScan:BeginItemBuyout(auctionID, buyoutAmount, itemID, onDone)
	auctionID = tonumber(auctionID)
	buyoutAmount = tonumber(buyoutAmount) or 0
	itemID = tonumber(itemID) or 0
	if not auctionID or buyoutAmount <= 0 then
		if onDone then SafeCall(onDone, false, "invalid") end
		return false, "invalid"
	end
	if not self.isOpen then
		if onDone then SafeCall(onDone, false, "closed") end
		return false, "closed"
	end
	if not PlaceBid then
		if onDone then SafeCall(onDone, false, "unsupported") end
		return false, "unsupported"
	end
	if purchase then self:CancelPurchase() end
	purchaseSerial = purchaseSerial + 1
	local p = {
		kind = "item", serial = purchaseSerial, itemID = itemID, quantity = 1,
		auctionID = auctionID, buyoutAmount = buyoutAmount, onDone = onDone, state = "armed",
	}
	purchase = p
	local label = string_format("BUY %s %s", ItemPlainName(itemID), FL.FormatMoney(buyoutAmount))
	local armed = ArmBuy(label, function()
		local cur = purchase
		if cur ~= p or p.state ~= "armed" then return end
		p.state = "awaitResult"
		PlaceBid(auctionID, buyoutAmount)
		SchedulePurchaseTimeout(p, PURCHASE_TIMEOUT, "awaitResult")
	end, function(err)
		if purchase == p then
			FinishPurchase(false, "error", err)
		end
	end)
	if not armed then
		purchase = nil
		if onDone then SafeCall(onDone, false, "combat") end
		return false, "combat"
	end
	return true
end

-- Aborts the pending purchase (server-side commodity purchase included) and disarms the button.
function AuctionScan:CancelPurchase()
	local p = purchase
	if not p then return false end
	CancelServerPurchase(p)
	FinishPurchase(false, "cancelled")
	return true
end

-------------------------------------------------------------------------------
-- Public scan API
-------------------------------------------------------------------------------
local keyInfoWaiters = {}   -- itemID -> array of callbacks (false = none)

local function FailSearchCallback(callback, itemID, reason)
	if callback then SafeCall(callback, itemID, nil, reason) end
end

local function EnqueueSearch(self, itemID, callback, isCommodity)
	itemID = tonumber(itemID)
	if not itemID or itemID <= 0 then
		FailSearchCallback(callback, itemID, "invalid")
		return false, "Invalid item."
	end
	if not self.isOpen then
		FailSearchCallback(callback, itemID, "closed")
		return false, "The Auction House is not open."
	end
	if not SendSearchQuery or not MakeItemKey then
		FailSearchCallback(callback, itemID, "unsupported")
		return false, "Item searches are not available on this client."
	end
	local r = AcquireRequest("search")
	r.itemID = itemID
	r.isCommodity = isCommodity
	r.cb = callback
	r.quiet = false
	r.itemKey = MakeItemKey(itemID)
	Submit(r)
	return true
end

-- Runs a full ReplicateItems scan (respects the 15-minute cooldown); returns ok, reason.
function AuctionScan:RunFullScan()
	if not self.isOpen then
		return false, "The Auction House is not open."
	end
	if not ReplicateItems or not GetNumReplicateItems or not GetReplicateItemInfo then
		return false, "ReplicateItems is not available on this client."
	end
	if full.active or HasRequestOfKind("replicate") then
		return false, "A full scan is already in progress."
	end
	local now = time()
	if now < self.nextFullScanAt then
		local remain = self.nextFullScanAt - now
		return false, string_format("Full scan on cooldown: %dm %02ds remaining.", math_floor(remain / 60), remain - math_floor(remain / 60) * 60)
	end
	local r = AcquireRequest("replicate")
	self.progress = 0
	self.progressText = "Full scan queued"
	Submit(r)
	return true
end

-- Scans one commodity's price ladder with paging; callback(itemID, resultTable).
function AuctionScan:RunCommodityScan(itemID, callback)
	return EnqueueSearch(self, itemID, callback, true)
end

-- Scans one non-commodity item's auctions with paging; callback(itemID, resultTable).
function AuctionScan:RunItemScan(itemID, callback)
	return EnqueueSearch(self, itemID, callback, false)
end

local function ResolveKeyInfo(itemID, timedOut)
	local list = keyInfoWaiters[itemID]
	if not list then return end
	keyInfoWaiters[itemID] = nil
	if commodityCache[itemID] == nil then
		if timedOut then
			commodityCache[itemID] = IsCommodityItem(itemID, nil, true)
		else
			return
		end
	end
	for i = 1, #list do
		local cb = list[i]
		if cb == false then cb = nil end
		AuctionScan:ScanItem(itemID, cb)
	end
end

local function OnItemKeyInfoReceived(itemID)
	if not keyInfoWaiters[itemID] then return end
	if commodityCache[itemID] == nil and GetItemKeyInfo and MakeItemKey then
		local ok, info = pcall(GetItemKeyInfo, MakeItemKey(itemID))
		if ok and info and info.isCommodity ~= nil then
			commodityCache[itemID] = info.isCommodity and true or false
		end
	end
	if commodityCache[itemID] ~= nil then
		ResolveKeyInfo(itemID, false)
	end
end

-- Scans an item, choosing the commodity or item path via GetItemKeyInfo (retries when info is pending).
function AuctionScan:ScanItem(itemID, callback)
	itemID = tonumber(itemID)
	if not itemID or itemID <= 0 then
		FailSearchCallback(callback, itemID, "invalid")
		return false, "Invalid item."
	end
	if not self.isOpen then
		FailSearchCallback(callback, itemID, "closed")
		return false, "The Auction House is not open."
	end
	local isCommodity = commodityCache[itemID]
	if isCommodity == nil and GetItemKeyInfo and MakeItemKey then
		local ok, info = pcall(GetItemKeyInfo, MakeItemKey(itemID))
		if ok and info and info.isCommodity ~= nil then
			isCommodity = info.isCommodity and true or false
			commodityCache[itemID] = isCommodity
		end
	elseif isCommodity == nil then
		isCommodity = IsCommodityItem(itemID, nil, false)
		commodityCache[itemID] = isCommodity
	end
	if isCommodity == nil then
		local list = keyInfoWaiters[itemID]
		if not list then
			list = {}
			keyInfoWaiters[itemID] = list
			After(KEYINFO_TIMEOUT, function() ResolveKeyInfo(itemID, true) end)
		end
		list[#list + 1] = callback or false
		return true, "pending"
	end
	if isCommodity then
		return self:RunCommodityScan(itemID, callback)
	end
	return self:RunItemScan(itemID, callback)
end

-- Runs a browse query with paging; onPage(resultsArray, isFull) per page (return true to stop), onDone(results|nil, reason).
function AuctionScan:RunBrowseScan(query, onPage, onDone)
	if not self.isOpen then
		if onDone then SafeCall(onDone, nil, "closed") end
		return false, "The Auction House is not open."
	end
	if not SendBrowseQuery then
		if onDone then SafeCall(onDone, nil, "unsupported") end
		return false, "Browse queries are not available on this client."
	end
	if type(query) ~= "table" then
		query = {}
	end
	if query.searchString == nil then query.searchString = "" end
	if query.sorts == nil then query.sorts = SORTS_PRICE end
	if query.filters == nil then query.filters = BROWSE_EMPTY_FILTERS end
	if query.minLevel == nil then query.minLevel = 0 end
	if query.maxLevel == nil then query.maxLevel = 0 end
	local r = AcquireRequest("browse")
	r.query = query
	r.onPage = onPage
	r.cb = onDone
	Submit(r)
	return true
end

-- Queues a raw request { kind="search"|"browse"|"replicate"|"owned", itemID=, query=, cb= }.
function AuctionScan:Enqueue(request)
	if type(request) ~= "table" then
		return false, "Invalid request."
	end
	local kind = request.kind
	if kind == "search" then
		local itemID = tonumber(request.itemID)
		if not itemID or itemID <= 0 then
			return false, "Invalid item."
		end
		if not self.isOpen then
			FailSearchCallback(request.cb, itemID, "closed")
			return false, "The Auction House is not open."
		end
		if not SendSearchQuery or not MakeItemKey then
			FailSearchCallback(request.cb, itemID, "unsupported")
			return false, "Item searches are not available on this client."
		end
		local r = AcquireRequest("search")
		r.itemID = itemID
		r.isCommodity = request.isCommodity
		if r.isCommodity == nil then
			r.isCommodity = IsCommodityItem(itemID, nil, true)
		end
		r.cb = request.cb
		r.quiet = request.quiet and true or false
		r.itemKey = request.itemKey or MakeItemKey(itemID)
		return Submit(r)
	elseif kind == "browse" then
		return self:RunBrowseScan(request.query, request.onPage, request.cb)
	elseif kind == "replicate" then
		return self:RunFullScan()
	elseif kind == "owned" then
		return self:QueryOwned(request.cb)
	end
	return false, "Unknown request kind."
end

-- Cancels queued and in-flight requests, full-scan processing and any pending purchase.
function AuctionScan:CancelAll()
	while true do
		local r = QueuePop()
		if not r then break end
		FailRequest(r, "cancelled")
		ReleaseRequest(r)
	end
	if inflight then
		local r = inflight
		inflight = nil
		FailRequest(r, "cancelled")
		ReleaseRequest(r)
	end
	if full.active then
		AbortFullScan("cancelled")
	end
	full.startedMs = 0
	for itemID, list in pairs(keyInfoWaiters) do
		keyInfoWaiters[itemID] = nil
		for i = 1, #list do
			if list[i] then
				SafeCall(list[i], itemID, nil, "cancelled")
			end
		end
	end
	self:CancelPurchase()
	self.progress = 0
	self.progressText = ""
	UpdateState()
end

-- Returns the last per-item ladder { n, unitPrices, quantities, auctionIDs, own, isCommodity, ts } or nil.
function AuctionScan.GetLastResults(a, b)
	local itemID = a
	if a == AuctionScan then itemID = b end
	itemID = tonumber(itemID)
	if not itemID then return nil end
	return lastResults[itemID]
end

-- Queries this character's auctions; callback(ownedArray) after OWNED_AUCTIONS_UPDATED.
function AuctionScan:QueryOwned(callback)
	if not self.isOpen then
		if callback then SafeCall(callback, nil, "closed") end
		return false, "The Auction House is not open."
	end
	if not QueryOwnedAuctions or not GetOwnedAuctions then
		if callback then SafeCall(callback, nil, "unsupported") end
		return false, "Owned auction queries are not available on this client."
	end
	local r = AcquireRequest("owned")
	r.cb = callback
	Submit(r)
	return true
end

-------------------------------------------------------------------------------
-- Auction house open/close and event wiring
-------------------------------------------------------------------------------
local function OnAuctionHouseShow()
	AuctionScan.isOpen = true
	fpsSkips = 0
	StartTicker()
	UpdateState()
	After(1.0, function()
		if AuctionScan.isOpen then
			AuctionScan:QueryOwned(nil)
		end
	end)
	if ScanSetting("fullScanOnOpen") then
		After(1.5, function()
			if AuctionScan.isOpen then
				local ok, reason = AuctionScan:RunFullScan()
				if not ok then
					FL:Debug("AuctionScan: automatic full scan skipped: %s", tostring(reason))
				end
			end
		end)
	end
end

local function OnAuctionHouseClosed()
	AuctionScan.isOpen = false
	StopTicker()
	AuctionScan:CancelAll()
	UpdateState()
end

local function OnThrottleDropped()
	local r = inflight
	if not r then return end
	RetryOrDrop(r, "dropped")
	SafeTick()
end

local function OnThrottleResponseReceived()
	if inflight then
		inflight.sentAt = GetTime()
	end
end

local function OnRegenEnabled()
	if deferredDisarm then
		deferredDisarm = false
		if not purchase and FL.Secure and FL.Secure.Disarm then
			pcall(FL.Secure.Disarm, "buy")
		end
	end
end

local eventHandlers = {
	AUCTION_HOUSE_SHOW = function() OnAuctionHouseShow() end,
	AUCTION_HOUSE_CLOSED = function() OnAuctionHouseClosed() end,
	AUCTION_HOUSE_THROTTLED_SYSTEM_READY = function() SafeTick() end,
	AUCTION_HOUSE_THROTTLED_MESSAGE_SENT = function() FL:Debug("AuctionScan: throttled message sent") end,
	AUCTION_HOUSE_THROTTLED_MESSAGE_QUEUED = function() FL:Debug("AuctionScan: throttled message queued") end,
	AUCTION_HOUSE_THROTTLED_MESSAGE_RESPONSE_RECEIVED = function() OnThrottleResponseReceived() end,
	AUCTION_HOUSE_THROTTLED_MESSAGE_DROPPED = function() OnThrottleDropped() end,
	REPLICATE_ITEM_LIST_UPDATE = function() OnReplicateListUpdate() end,
	COMMODITY_SEARCH_RESULTS_UPDATED = function(_, itemID) HandleCommodityResults(itemID) end,
	ITEM_SEARCH_RESULTS_UPDATED = function(_, itemKey) HandleItemResults(itemKey) end,
	AUCTION_HOUSE_BROWSE_RESULTS_UPDATED = function() HandleBrowseResults(nil) end,
	AUCTION_HOUSE_BROWSE_RESULTS_ADDED = function(_, added) HandleBrowseResults(added) end,
	AUCTION_HOUSE_BROWSE_FAILURE = function() OnBrowseFailure() end,
	ITEM_KEY_ITEM_INFO_RECEIVED = function(_, itemID) OnItemKeyInfoReceived(itemID) end,
	OWNED_AUCTIONS_UPDATED = function() OnOwnedAuctionsUpdated() end,
	COMMODITY_PRICE_UPDATED = function(_, unit, total) OnCommodityPriceUpdated(unit, total) end,
	COMMODITY_PRICE_UNAVAILABLE = function() OnCommodityPriceUnavailable() end,
	COMMODITY_PURCHASE_SUCCEEDED = function() OnCommodityPurchaseSucceeded() end,
	COMMODITY_PURCHASE_FAILED = function() OnCommodityPurchaseFailed() end,
	COMMODITY_PURCHASED = function(_, itemID, quantity) OnCommodityPurchased(itemID, quantity) end,
	AUCTION_HOUSE_PURCHASE_COMPLETED = function(_, auctionID) OnAuctionPurchaseCompleted(auctionID) end,
	AUCTION_HOUSE_SHOW_ERROR = function(_, err) OnAuctionHouseShowError(err) end,
	ITEM_PURCHASED = function(_, itemID) FL:Debug("AuctionScan: item purchased %s", tostring(itemID)) end,
	PLAYER_REGEN_ENABLED = function() OnRegenEnabled() end,
}

for eventName, handler in pairs(eventHandlers) do
	local ok, err = pcall(FL.RegisterEvent, eventName, handler)
	if not ok then
		FL:Debug("AuctionScan: could not register %s: %s", eventName, tostring(err))
	end
end

if FL.On then
	FL.On("FL_SETTINGS_CHANGED", function()
		if AuctionScan.isOpen then
			StartTicker()
		end
	end)
end
