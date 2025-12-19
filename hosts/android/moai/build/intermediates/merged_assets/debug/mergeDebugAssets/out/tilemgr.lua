local debugging = false
local isDesktop = Application:isDesktop()
--isDesktop = false
local concurrentLoadingThreads = 4
local delayBetweenTiles = 0 --2000

local tilemgr = { VERSION = "0.0.1" }

local tileScale = 1
local tileSize = 256*tileScale

local lfs = require("lfs")
local socket = require("socket")
local http = require("socket.http")
local toast = require("toast");
local LatLon = require("latlon")

local function prequire(m) 
  local ok, err = pcall(require, m) 
  if not ok then return nil, err end
  return err
end

-- If we don't have struct, then we must be running a vanilla moai.  Disable metaTile support in osmMetaTileURL.
local struct, err = prequire("struct")
if not struct and err then
	print('struct not found, disabling metaTile support')
end

local luadate = require("luadate")

local function convertHttpTimestamp(d)
	local luathen = luadate(d)
	local luaint = (luathen-luadate.epoch()):spanseconds()
	return luaint
end

local function GetScaledRGColor(Current, RedValue, GreenValue)
	local Percent = (Current - RedValue) / (GreenValue - RedValue) * 100.0;

	if (Percent <= 50.0) then
		if (Percent < 0.0) then Percent = 0.0 end
		return 1.0,Percent/50,0.0
	else
		if (Percent > 100.0) then Percent = 100.0 end
		return (100.0-Percent)/50,1.0,0.0
	end
end

local IPFSLoaded = 0		-- Count of meta tiles from IPFS
local metaLoaded = 0		-- Count of loaded meta tiles
local tilesLoaded = 0		-- Count of loaded tiles
local tilesFailed = 0		-- Count of failed tiles
local extraTilesLoaded = 0	-- Count of "extra" non-requested tiles in metatiles

function tilemgr:getTilesLoaded()
	return tilesLoaded, extraTilesLoaded, tilesFailed
end

function tilemgr:validLatLon(lat_deg, lon_deg)	-- returns true or false
	if lat_deg < -85.0511 or lat_deg > 85.0511 or lon_deg < -180 or lon_deg > 180 then
		print(string.format("tilemgr:validLatLon:Invalid lat(%f) or lon(%f)", lat_deg, lon_deg))
		return false
	end
	return true
end

local function validTileNum(x, y, z)
	if z < 0 or z > 20 then return false end
	local pow2 = 2^z - 1
	if x < 0 or x > pow2 then return false end
	if y < 0 or y > pow2 then return false end
	return true
end

function tilemgr:validTileNum(x,y,z)
	return validTileNum(x,y,z)
end

local bit = bit
if type(bit) ~= 'table' then
	if type(bit32) == 'table' then
		print('otp:using internal bit32 module')
		bit = bit32
	else
		print('otp:using mybits type(bit)='..type(bit))
		bit = require("mybits")
		bit.lshift = bit.blshift
		bit.rshift = bit.blogic_rshift
	end
else print('otp:using internal bit module!')
end
-- bit.bxor band bor lshift rshift

function tilemgr:osmMetaTile(x, y)	-- Returns MetaTile path and index within meta file
	x = math.floor(x) y = math.floor(y)
--<base dir>/<style>/<zoom>/<16*A+a>/<16*B+b>/<16*C+c>/<16*D+d>/<8*(16*E+e)>.meta
--x = AAAABBBBCCCCDDDDEMMM
--y = aaaabbbbccccddddemmm
--The index of the tile within the metatile file is 8*M+m. The <style> directory allows generating different map appearances on the same server.
	local M = bit.band(x,0x7)
	local E = bit.band(bit.rshift(x,3),0x1)
	local D = bit.band(bit.rshift(x,4),0xf)
	local C = bit.band(bit.rshift(x,8),0xf)
	local B = bit.band(bit.rshift(x,12),0xf)
	local A = bit.band(bit.rshift(x,16),0xf)
	local m = bit.band(y,0x7)
	local e = bit.band(bit.rshift(y,3),0x1)
	local d = bit.band(bit.rshift(y,4),0xf)
	local c = bit.band(bit.rshift(y,8),0xf)
	local b = bit.band(bit.rshift(y,12),0xf)
	local a = bit.band(bit.rshift(y,16),0xf)
	local mTile = tostring(16*A+a)..'/'..tostring(16*B+b)..'/'..tostring(16*C+c)..'/'..tostring(16*D+d)..'/'..tostring(8*(16*E+e))..'.meta'
	local i = 8*M+m
	return mTile, i
end

function tilemgr:tileFromMetaID(metaID)	-- Returns (top left) x, y from MetaTile ID
	local z, Aa, Bb, Cc, Dd, Ee = metaID:match("(%d+)/(%d+)/(%d+)/(%d+)/(%d+)/(%d+)%.meta")
	if not Aa or not Bb or not Cc or not Dd or not Ee then return nil end
	local A = bit.rshift(Aa,4)
	local B = bit.rshift(Bb,4)
	local C = bit.rshift(Cc,4)
	local D = bit.rshift(Dd,4)
	local E = bit.rshift(Ee/8,4)
	local a = bit.band(Aa,0xf)
	local b = bit.band(Bb,0xf)
	local c = bit.band(Cc,0xf)
	local d = bit.band(Dd,0xf)
	local e = bit.band(Ee/8,0xf)
	local x = bit.lshift(A,16) + bit.lshift(B,12) + bit.lshift(C,8) + bit.lshift(D,4) + bit.lshift(E,3)
	local y = bit.lshift(a,16) + bit.lshift(b,12) + bit.lshift(c,8) + bit.lshift(d,4) + bit.lshift(e,3)
	
	--local test = tonumber(z).."/"..tilemgr:osmMetaTile(x,y)
	--if test ~= metaID then
	--	print(string.format("checkTile:tileFromMeta(%s) %d %d NOT %s", metaID, x, y, test))
	----else print(string.format("checkTile:tileFromMeta(%s) %d %d IS %s", metaID, x, y, test))
	--end
	return x, y, tonumber(z)
end

function tilemgr:osmTileNum(lat_deg, lon_deg, zoom)	-- lat/lon in degrees gives xTile, yTile
	--if not lat_deg or not lon_deg then return nil end
	if not tilemgr:validLatLon(lat_deg, lon_deg) then
		print(string.format("osmTileNum:Invalid lat(%f) or lon(%f)", lat_deg, lon_deg))
		return nil
	end
	local n = 2 ^ zoom
	local xtile = n * ((lon_deg + 180) / 360)

--	1 = n * ((0.017971305190311+180)/360)
--	1 = n * 0.5000499202921953
--	n = 1.999800338765513 (0.000199661234487)
--	1 = n * 0.4999500797078047
--	n = 2.000199701107056 (0.0001997011070564653)
--	1/0.017971305190311 = 20031.93402970472 or approx 20032 or 78.25 256pixel tiles
	
	local lat_rad = math.rad(lat_deg)
	local ytile = n * (1 - (math.log(math.tan(lat_rad) + (1/math.cos(lat_rad))) / math.pi)) / 2
	if xtile < 0 or xtile >= 2^zoom or ytile < 0 or ytile >= 2^zoom then
		print(string.format("osmTileNum:%f %f gave %f %f zoom %i", lat_deg, lon_deg, xtile, ytile, zoom))
		local foo = nil
		foo.x = 5
	end
	-- print(string.format("osmTileNum(%f %f %d) gives Tile %d %d", lat_deg, lon_deg, zoom, xtile, ytile))
	return xtile, ytile
end
-- This returns the NW-corner of the square. Use the function with xtile+1 and/or ytile+1
-- to get the other corners. With xtile+0.5 & ytile+0.5 it will return the center of the tile. 
function tilemgr:osmTileLatLon(xTile, yTile, zTile)	-- xTile, yTile, zoom -> lat, lon
	local n = 2^zTile
	local lon_deg = xTile / n * 360.0 - 180.0
	local lat_deg = 180.0 / math.pi * math.atan(math.sinh(math.pi * (1 - 2 * yTile / n)))
	return lat_deg, lon_deg
end

-- returns E/W and N/S size along with diagonal size of tile at zoom in km
function tilemgr:osmTileSizeKM(lat, lon, z)
	local tx, ty = self:osmTileNum(lat,lon,z)
	tx, ty = math.floor(tx), math.floor(ty)
	local nwlat, nwlon = self:osmTileLatLon(tx,ty,z)
	local selat, selon = self:osmTileLatLon(tx+1,ty+1,z)
	local nwPoint = LatLon.new(nwlat, nwlon)
	local nePoint = LatLon.new(nwlat, selon)
	local swPoint = LatLon.new(selat, nwlon)
	local sePoint = LatLon.new(selat, selon)
	local ndist = nwPoint.distanceTo(nePoint)
	local wdist = nwPoint.distanceTo(swPoint)
	local edist = nePoint.distanceTo(sePoint)
	local sdist = sePoint.distanceTo(swPoint)
	local d1dist = nwPoint.distanceTo(sePoint)
	local d2dist = nePoint.distanceTo(swPoint)
--	print(string.format("osmTileSizeKM:zoom %d lat %f lon %f tile is n:%f s:%f e:%f w:%f d1:%f d2:%f", z, lat, lon, ndist, sdist, edist, wdist, d1dist, d2dist))
	return (edist+wdist)/2, (ndist+sdist)/2, (d1dist+d2dist)/2
end

-- returns N/S (lat) and E/W (lon) size of tile at zoom in degrees
function tilemgr:osmTileSizeDegrees(lat, lon, z)
	local tx, ty = self:osmTileNum(lat,lon,z)
	tx, ty = math.floor(tx), math.floor(ty)
	local nwlat, nwlon = self:osmTileLatLon(tx,ty,z)
	local selat, selon = self:osmTileLatLon(tx+1,ty+1,z)
	local dlat = math.abs(nwlat-selat)
	local dlon = math.abs(nwlon-selon)
--	print(string.format("osmTileSizeDegrees:zoom %d lat %f lon %f tile is lat:%f lon:%f", z, lat, lon, dlat, dlon))
	return dlon, dlat
end

local function makeRequiredDirectory(file, dir)
	if file == '' then return nil end
	local path = string.match(file, "(.+)/.+")
	local fullpath = dir..'/'..path
	MOAIFileSystem.affirmPath(fullpath)
	return fullpath
end

local TileSets = {
	OSMTiles = { Name="OSMTiles", URLFormat="https://tile.openstreetmap.org/%z/%x/%y.png" },
	LynnsTiles = { Name="LynnsTiles", URLFormat="http://ldeffenb.dnsalias.net:6360/osm/%z/%x/%y.png" },
	LocalTiles = { Name="LynnsTiles", URLFormat="http://192.168.10.8:6360/osm/%z/%x/%y.png" },
	CTNPS = {Name='CT-NPS', URLFormat='http://s3-us-west-1.amazonaws.com/ctvisitor/nps/%z/%x/%y.png' },
	CTVisitor = {Name='CT-Visitor', URLFormat='http://s3-us-west-1.amazonaws.com/ctfun/visitor/%z/%x/%y.png' },
	CTTopo1545 = {Name='CT-Topo15-45', URLFormat='http://s3-us-west-1.amazonaws.com/ctfun/1930/%z/%x/%y.png' },
	}

local TileSet = TileSets.LynnsTiles --TileSets.CTNPS
--TileSet = TileSets.LocalTiles
--TileSet = TileSets.OSMTiles

local function osmTileDir()
	if config.Dir.Tiles ~= '' then return config.Dir.Tiles end
	config.Dir.Tiles = MOAIEnvironment.externalFilesDirectory or MOAIEnvironment.externalCacheDirectory or MOAIEnvironment.cacheDirectory or MOAIEnvironment.documentDirectory or "Cache/";
	return config.Dir.Tiles
end

local function recurseDirCountSize(dir)
	local tCount, tSize = 0,0
	for file in lfs.dir(dir) do
		local mode = lfs.attributes(dir..'/'..file,"mode")
		if mode == 'directory' then
			if file ~= '.' and file ~= '..' then
				local count, size = recurseDirCountSize(dir..'/'..file)
				tCount = tCount + count
				tSize = tSize + size
			end
		elseif mode == 'file' then
			tCount = tCount + 1
			tSize = tSize + lfs.attributes(dir..'/'..file,"size")
		end
	end
	return tCount, tSize
end

local function summarizeTileSetUsage(root)
	local start = MOAISim.getDeviceTime()
	print("summarizeTileSetUsage("..tostring(root)..')')
	local count, size = recurseDirCountSize(root)
	local text = string.format('%i/%.1fMB (%ims)', count, size/1024/1024, (MOAISim.getDeviceTime()-start)*1000)
	print("summarizeTileSetUsage("..tostring(root)..') gives '..tostring(text))
	return text
end

local directoryInformed = false
local function summarizeTileUsage()
	dir = osmTileDir()..'/MapTiles'
	local tileSets = {}
	print('summaraizeTileUsage('..tostring(dir)..')')
	for file in lfs.dir(dir) do
		print('Checking '..file)
		local mode = lfs.attributes(dir..'/'..file,"mode")
		if mode == 'directory' then
			if file ~= '.' and file ~= '..' then
				tileSets[file] = file..':'..summarizeTileSetUsage(dir..'/'..file)
			end
		else print(tostring(file)..' mode is '..tostring(mode))
		end
	end

	local text = 'Tiles Stored In '..tostring(dir)
	for k,v in pairs(tileSets) do
		text = text..'\n'..v
	end
	toast.new(text)
end



local List = {}
function List.new ()
  return {first = 0, last = -1, count = 0, maxcount = 0, pushcount = 0, popcount = 0}
end

function List.getCount (list)
	return list.count
end

function List.pushleft (list, value)
  local first = list.first - 1
  list.first = first
  list[first] = value
  list.count = list.count + 1
  list.pushcount = list.pushcount + 1
  if list.count == 1 then list.maxcount = 1; list.pushcount = 1; list.popcount = 0 end
  if list.count > list.maxcount then list.maxcount = list.count end
end

function List.pushright (list, value)
  local last = list.last + 1
  list.last = last
  list[last] = value
  list.count = list.count + 1
  list.pushcount = list.pushcount + 1
  if list.count == 1 then list.maxcount = 1; list.pushcount = 1; list.popcount = 0 end
  if list.count > list.maxcount then list.maxcount = list.count end
end

function List.popleft (list)
  local first = list.first
  if first > list.last then error("list is empty") end
  local value = list[first]
  list[first] = nil        -- to allow garbage collection
  list.first = first + 1
  list.count = list.count - 1
  if list.count == 0 then list.maxcount = 0 end
  list.popcount = list.popcount + 1
  return value
end

function List.popright (list)
  local last = list.last
  if list.first > last then error("list is empty") end
  local value = list[last]
  list[last] = nil         -- to allow garbage collection
  list.last = last - 1
  list.count = list.count - 1
  if list.count == 0 then list.maxcount = 0 end
  list.popcount = list.popcount + 1
  return value
end

--MBTile = require("mbtile")
MBTile = require("mbtile3")
if not MBTile then
	MBTile = require("mbtilelua")
	print(string.format("mbtilelua:type(MBTile) = %s(%s)", type(MBTile), tostring(MBTile)))
else 	print(string.format("mbtile3:type(MBTile) = %s(%s)", type(MBTile), tostring(MBTile)))
end

function getMBTilesDirectory()

	if config.Dir.Tiles ~= '' then return config.Dir.Tiles..'/MBTiles/' end
	return (MOAIEnvironment.externalFilesDirectory or MOAIEnvironment.externalCacheDirectory or MOAIEnvironment.cacheDirectory or MOAIEnvironment.documentDirectory or "Cache").."/MBTiles/";
--	return (MOAIEnvironment.externalFilesDirectory or MOAIEnvironment.documentDirectory or '/sdcard/'..MOAIEnvironment.appDisplayName)..'/MBTiles/'
end

local function EnsureMBTiles(MBTiles)
	local dir = getMBTilesDirectory()
	local fullpath = MOAIFileSystem.getAbsoluteFilePath(dir.."/"..MBTiles)
	if MOAIFileSystem.checkFileExists(fullpath) then
		print("sqlite:"..fullpath.." ALSO EXISTS!")
		MBTiles = fullpath
	elseif MOAIFileSystem.checkFileExists(MOAIFileSystem.getAbsoluteFilePath(MBTiles)) then
		print("sqlite:"..MOAIFileSystem.getAbsoluteFilePath(MBTiles).." EXISTS!")
		print("sqlite:"..fullpath.." NOT FOUND, attempting copy")
		if MOAIFileSystem.copy(MOAIFileSystem.getAbsoluteFilePath(MBTiles), fullpath) then
			print("sqlite:Copy succeeded!")
			MBTiles = fullpath
		else
			print("sqlite:Copy FAILED")
		end
	else print("sqlite:"..MBTiles.." NOT FOUND!")
	end
	return MBTiles
end

local function EnsureAllMBTiles()
	local files = MOAIFileSystem.listFiles(dir)
	if not files then files = {} end
	table.sort(files)
	for i, f in pairs(files) do
		if f:match("^.+%.mbtiles$") then
			EnsureMBTiles(f)
		end
	end
end

--local env,conn = opendb("World0-8.mbtiles")
--local MBTiles = ("./LynnsTiles.mbtiles")
--local MBTiles = ("./OpenStreetMaps.mbtiles")
--local MBTiles = ("./ArcGISWoldImagery.mbtiles")
local MBTiles = nil
local TopTiles = nil
local TopTiles2, TopTiles3, TopTiles4
local MBinited = false
--local env,conn = nil, nil
--local trans = 0
--local contents = nil

function tilemgr:getMBTilesCounts()
	if TopTiles and TopTiles.contents then
		return TopTiles.contents
	elseif MBTiles and MBTiles.contents then
		return MBTiles.contents
	else return nil
	end
end

local primeMBTiles -- forward function reference

local function initMBTiles(force)

	if not force and MBinited then return end
	MBinited = true
	
	EnsureAllMBTiles()
	
	config.Map.MBTiles = config.Map.MBTiles or "./LynnsTiles.mbtiles"
	if MOAIFileSystem.getAbsoluteFilePath(config.Map.MBTiles) ~= config.Map.MBTiles then
		config.Map.MBTiles = EnsureMBTiles(config.Map.MBTiles)
	end
	config.Map.TopTiles = config.Map.TopTiles or "./LynnsTiles.mbtiles"
	if config.Map.TopTiles ~= '' and MOAIFileSystem.getAbsoluteFilePath(config.Map.TopTiles) ~= config.Map.TopTiles then
		print("Verifying TopTiles="..tostring(config.Map.TopTiles))
		config.Map.TopTiles = EnsureMBTiles(config.Map.TopTiles)
	end

	MBTiles = MBTile(config.Map.MBTiles, force)--("./LynnsTiles.mbtiles")
	if not MBTiles then
		MBTiles = MBTile(EnsureMBTiles("./LynnsTiles.mbtiles"))
	end

	primeMBTiles(MBTiles)

	if config.Map.TopTiles and config.Map.TopTiles ~= '' then
		TopTiles = MBTile(config.Map.TopTiles, force)
	else TopTiles = nil
	end
--	TopTiles2 = MBTile(EnsureMBTiles("CatalinaMtns_SAHC.mbtiles"))
--	TopTiles3 = MBTile(EnsureMBTiles("RinconMtnsTI.mbtiles"))
--	TopTiles4 = MBTile(EnsureMBTiles("TortolitaMtns_USA.mbtiles"))
--[[
	performWithDelay(force and 10 or 5000, function() toast.new(tostring(MBTiles.name).."\n"..tostring(MBTiles.URLFormat).."\n"..MBTiles.db, 10000) end)
	if TopTiles and TopTiles ~= MBTiles then
		performWithDelay(force and 10 or 5000, function() toast.new(tostring(TopTiles.name).."\n"..tostring(TopTiles.URLFormat).."\n"..TopTiles.db, 10000) end)
	else TopTiles = nil	-- Don't carry both if they are the same!
	end
]]
end

function tilemgr:deleteAllTiles()
	return MBTiles:deleteAllTiles()
end

local function human(c)
	if c < 1000 then
		return tostring(c)
	elseif c < 10*1000 then
		return string.format("%.2fK", c/1000)
	elseif c < 100*1000 then
		return string.format("%.1fK", c/1000)
	elseif c < 1000*1000 then
		return string.format("%.0fK", c/1000)

	elseif c < 10*1000*1000 then
		return string.format("%.2fM", c/1000/1000)
	elseif c < 100*1000*1000 then
		return string.format("%.1fM", c/1000/1000)
	elseif c < 1000*1000*1000 then
		return string.format("%.0fM", c/1000/1000)
		
	elseif c < 10*1000*1000*1000 then
		return string.format("%.2fB", c/1000/1000/1000)
	elseif c < 100*1000*1000*1000 then
		return string.format("%.1fB", c/1000/1000/1000)
	elseif c < 1000*1000*1000*1000 then
		return string.format("%.0fB", c/1000/1000/1000)
		
	elseif c < 10*1000*1000*1000*1000 then
		return string.format("%.2fT", c/1000/1000/1000/1000)
	elseif c < 100*1000*1000*1000*1000 then
		return string.format("%.1fT", c/1000/1000/1000/1000)
	elseif c < 1000*1000*1000*1000*1000 then
		return string.format("%.0fT", c/1000/1000/1000/1000)
		
	else return string.format("%.0fT", c/1000/1000/1000/1000)
	end
end

function tilemgr:getContentImage2(xIn, yIn, zoom, label)

	label:setText("Loading")
	local worldImage = MOAIImageTexture.new ()
	print("getContentImage2:texture="..tostring(worldImage))
	worldImage:init ( 256, 256 )
	
	for x = 0, 255 do
		for _, y in ipairs({0, 255}) do
			worldImage:setRGBA(x,y,0,1,0,1)
		end
	end
	for y = 0, 255 do
		for _, x in ipairs({0, 255}) do
			worldImage:setRGBA(x,y,0,1,0,1)
		end
	end

	MOAICoroutine.new ():run ( function()

		local imgsize = 256
		local t = imgsize
		local zmax = 0
		while t > 1 do
			t = math.floor(t/2)
			zmax = zmax + 1
		end
		zmax = zoom>8 and zoom or 8
		
		local maxTime = MOAISim.getStep() * 1.9 -- / 4	-- Max loop time is 1/4 step (25%)
		local counts, maxCount, totalCount = MBTiles:getPixelCounts2(xIn, yIn, zoom, imgsize, zmax, maxTime)

		label:setText(label:getText().."...")

		local function overlayPixel(x,y,c)
	--[[
			local a = 0.5
			local r, g, b = worldImage:getRGBA(x,y)
			r = r*(1-a) + 1.0*a
			g = g*(1-a) + c*a
			b = b*(1-a) + c*a
			worldImage:setRGBA(x,y,r,g,b,1.0)
	]]
			--c = c * 100 / 256
			--worldImage:setRGBA(x,y,1.0,c,c,1.0)
			r, g, b = GetScaledRGColor(c, 0.0, 1.0)
			worldImage:setRGBA(x,y,r,g,b,1.0)
		end
		

		local start = MOAISim.getDeviceTime()
		local pSize = 2^(zmax - zoom)
		for y = 0, 255 do
			if counts[y] then
				local didOne = false
				for x = 0, 255 do
					if counts[y][x] then
						local c = 1-counts[y][x]/maxCount
						if pSize > 1 then
							for xp=x, x+pSize-1 do
								for yp=y, y+pSize-1 do
									overlayPixel(xp,yp,c)
								end
							end
--print("getContentImage2:invalidating:"..tostring(worldImage))
							worldImage:invalidate(x,y,x+pSize-1+1,y+pSize-1+1)
						else
							overlayPixel(x,y,c)
--print("getContentImage2:invalidating:"..tostring(worldImage))
							worldImage:invalidate(x,y,x+1,y+1)
						end
						didOne = true
						local elapsed = (MOAISim.getDeviceTime()-start)
						if elapsed > maxTime then	-- 1/4 (25%) of frame rate
							--print("getContentImage:Summary set yield after "..tostring(elapsed*1000).."msec")
							label:setText(label:getText()..".")
							coroutine.yield()
							start = MOAISim.getDeviceTime()
						end
					end
				end
			end
		end
		
		print(string.format("Zoom %d for size %d, Have %d tiles Max %d in cell, pSize=%f zoom %d", zmax, imgsize, totalCount, maxCount, pSize, zoom))

--print("getContentImage2:Final invalidate:"..tostring(worldImage))
		worldImage:invalidate()
		
		local text = string.format("Zoom %d %s tile%s", zoom, human(totalCount), totalCount==1 and "" or "s")
		if maxCount > 1 then
			text = text..string.format(", up to %s/cell", human(maxCount))
		else
			local z = zoom>8 and 8 or zoom
			local pow2 = 2^z
			local zoomTiles = pow2*pow2
			local percent = totalCount / zoomTiles
			text = text..string.format(" %d%%", percent*100)
		end
		label:setText(text)
	
	end)
	
	return worldImage
end


function tilemgr:getContentImage(zoom, label)

	label:setText("Loading")
	local worldImage = MOAIImageTexture.new ()
print("getContentImage:worldImage:"..tostring(worldImage))
	worldImage:init ( 256, 256 )
	
	for x = 0, 255 do
		for _, y in ipairs({0, 255}) do
			worldImage:setRGBA(x,y,0,1,0,1)
		end
	end
	for y = 0, 255 do
		for _, x in ipairs({0, 255}) do
			worldImage:setRGBA(x,y,0,1,0,1)
		end
	end

	MOAICoroutine.new ():run ( function()

		local imgsize = 256
		local t = imgsize
		local zmax = 0
		while t > 1 do
			t = math.floor(t/2)
			zmax = zmax + 1
		end

		local maxTime = MOAISim.getStep() * 1.9 -- / 4	-- Max loop time is 1/4 step (25%)
		local counts, maxCount, totalCount = MBTiles:getPixelCounts(zoom, imgsize, zmax, maxTime)

		label:setText(label:getText().."...")

		local function overlayPixel(x,y,c)
	--[[
			local a = 0.5
			local r, g, b = worldImage:getRGBA(x,y)
			r = r*(1-a) + 1.0*a
			g = g*(1-a) + c*a
			b = b*(1-a) + c*a
			worldImage:setRGBA(x,y,r,g,b,1.0)
	]]
			--c = c * 100 / 256
			--worldImage:setRGBA(x,y,1.0,c,c,1.0)
			r, g, b = GetScaledRGColor(c, 0.0, 1.0)
			worldImage:setRGBA(x,y,r,g,b,1.0)
		end
		

		local start = MOAISim.getDeviceTime()
		local pSize = 2^(zmax - zoom)
		for y = 0, 255 do
			if counts[y] then
				local didOne = false
				for x = 0, 255 do
					if counts[y][x] then
						local c = 1-counts[y][x]/maxCount
						if pSize > 1 then
							for xp=x, x+pSize-1 do
								for yp=y, y+pSize-1 do
									overlayPixel(xp,yp,c)
								end
							end
--print("getContentImage:invalidating:"..tostring(worldImage))
							worldImage:invalidate(x,y,x+pSize-1+1,y+pSize-1+1)
						else
							overlayPixel(x,y,c)
							worldImage:invalidate(x,y,x+1,y+1)
--print("getContentImage:invalidating:"..tostring(worldImage))
						end
						didOne = true
						local elapsed = (MOAISim.getDeviceTime()-start)
						if elapsed > maxTime then	-- 1/4 (25%) of frame rate
							--print("getContentImage:Summary set yield after "..tostring(elapsed*1000).."msec")
							label:setText(label:getText()..".")
							coroutine.yield()
							start = MOAISim.getDeviceTime()
						end
					end
				end
			end
		end
		
		print(string.format("Zoom %d for size %d, Have %d tiles Max %d in cell, pSize=%f zoom %d", zmax, imgsize, totalCount, maxCount, pSize, zoom))

print("getContentImage:final invalidate:"..tostring(worldImage))
		worldImage:invalidate()

		local text = string.format("Zoom %d %s tile%s", zoom, human(totalCount), totalCount==1 and "" or "s")
		if maxCount > 1 then
			text = text..string.format(", up to %s/cell", human(maxCount))
		else
			local pow2 = 2^zoom
			local zoomTiles = pow2*pow2
			local percent = totalCount / zoomTiles
			text = text..string.format(" %d%%", percent*100)
		end
		label:setText(text)
	
	end)
	
	return worldImage
end


function tilemgr:newMBTiles()
	print("tilemgr::newMBTiles("..tostring(config.Map.MBTiles)..")")
	initMBTiles(true)
end


function tilemgr:osmMetaTileURL(x,y,z,MBTiles)
	local URL = ''
	local m, idx = tilemgr:osmMetaTile(x, y)

	if struct and MBTiles.MetaFormat and MBTiles.MetaFormat ~= "" then
		local f = MBTiles.MetaFormat
		local DidOne = false;
		
		while f ~= "" do
			if f:sub(1,1) == '%' then
				local invert = false
				f = f:sub(2)
				if f:sub(1,1) == '!' then	-- %!X or %!Y inverts via (2^Z-n-1)
					invert = true
					f = f:sub(2)
				end
				if f:sub(1,1) == '%' then	-- %% is a single %
					URL = URL.."%"
					DidOne = true
				elseif f:sub(1,1) == 'z' then	-- %z is zoom
					URL = URL..tostring(z)
					DidOne = true
				elseif f:sub(1,1) == 'y' then	-- %y is y, but may be inverted
					URL = URL..tostring(invert and (2^z-y-1) or y)
					DidOne = true
				elseif f:sub(1,1) == 'x' then	-- %x is x but may be inverted
					URL = URL..tostring(invert and (2^z-x-1) or x)
					DidOne = true
				elseif f:sub(1,1) == 'm' then	-- %m is meta bits including .meta
					URL = URL..tostring(m)
					DidOne = true
				else							-- %<unknown> emits the original text
					URL = URL.."%"
					if invert then URL = URL.."!" end
					URL = URL..f:sub(1,1)
				end
			else URL = URL..f:sub(1,1)			-- Non-% copies right through
			end
			f = f:sub(2)
		end
		if not DidOne then
			if URL:sub(-1) ~= '\\' and URL:sub(-1) ~= '/' then URL = URL..'/' end
			URL = URL..string.format("%i/%i/%i.png", z, x, y)
		end
	end

	return URL, idx, tostring(z).."/"..m
end



local function osmTileKey(x,y,z,MBTiles)
	return string.format('%s/%i/%i/%i.png', MBTiles.name, z, x, y)
end

local function osmTileURL(x,y,z,MBTiles)
	local URL = ''

	if MBTiles.URLFormat then
		local f = MBTiles.URLFormat
		local DidOne = false;
		
		while f ~= "" do
			if f:sub(1,1) == '%' then
				local invert = false
				f = f:sub(2)
				if f:sub(1,1) == '!' then	-- %!X or %!Y inverts via (2^Z-n-1)
					invert = true
					f = f:sub(2)
				end
				if f:sub(1,1) == '%' then	-- %% is a single %
					URL = URL.."%"
					DidOne = true
				elseif f:sub(1,1) == 'z' then	-- %z is zoom
					URL = URL..tostring(z)
					DidOne = true
				elseif f:sub(1,1) == 'y' then	-- %y is y, but may be inverted
					URL = URL..tostring(invert and (2^z-y-1) or y)
					DidOne = true
				elseif f:sub(1,1) == 'x' then	-- %x is x but may be inverted
					URL = URL..tostring(invert and (2^z-x-1) or x)
					DidOne = true
				else							-- %<unknown> emits the original text
					URL = URL.."%"
					if invert then URL = URL.."!" end
					URL = URL..f:sub(1,1)
				end
			else URL = URL..f:sub(1,1)			-- Non-% copies right through
			end
			f = f:sub(2)
		end
		if not DidOne then
			if URL:sub(-1) ~= '\\' and URL:sub(-1) ~= '/' then URL = URL..'/' end
			URL = URL..string.format("%i/%i/%i.png", z, x, y)
		end
	end

	return URL
end

local loadingList = List:new()
local loadRunning = 0
local loadedCount, skippedCount, errorCount, lateCount, soonCount
local queuedFiles = {}
local downloadingFiles = {}
local metaTilesPending = {}
local osmReallyLoadRemoteTile

local pendingPrevious = {}
local pendingPrefetch = {}
local pendingExpired = {}
pendingPrevious[0] = 0
pendingPrefetch[0] = 0
pendingExpired[0] = 0

local loadingCircle
local getTileGroup

function tilemgr:setGetTileGroup(getCallback)
	getTileGroup = getCallback
end

function tilemgr:getQueueStats()	-- returns count, maxcount, pushcount, popcount
	local loadingActive = loadingList.count + loadRunning + #pendingPrevious + #pendingPrefetch + #pendingExpired
	local loadingMax = loadingList.maxcount + concurrentLoadingThreads + pendingPrevious[0] + pendingPrefetch[0] + pendingExpired[0]
	return loadingActive, loadingMax, loadingList.pushcount, loadingList.popcount
end

local function updateLoadingCount(what)
	local loadingActive = loadingList.count + loadRunning + #pendingPrevious + #pendingPrefetch + #pendingExpired
	local loadingMax = loadingList.maxcount + concurrentLoadingThreads + pendingPrevious[0] + pendingPrefetch[0] + pendingExpired[0]
	if true or debugging then
		local info = debug.getinfo( 2, "Sl" )
		local where = info.source..':'..info.currentline
		if where:sub(1,1) == '@' then where = where:sub(2) end
		print("updateLoadingCount:"..what.." "..tostring(loadingActive)..'/'..tostring(loadingMax).." from "..tostring(where))
	end
	if stilltext then
print(string.format("metaLoaded:%s IPFSLoaded:%s Middle:'%s' Whole:'%s'",
					tostring(metaLoaded), tostring(IPFSLoaded),
					(IPFSLoaded>0 and "("..tostring(IPFSLoaded)..")" or ""),
metaLoaded>0 and (tostring(metaLoaded)..(IPFSLoaded>0 and "("..tostring(IPFSLoaded)..")" or "").."+") or ""))
					
		local new = string.format("%d(%d)+%d+%d+%d/%d(%d)+%d+%d+%d\n%s%d%s%s",
									loadingList.count, loadRunning, #pendingPrevious, #pendingPrefetch, #pendingExpired,
									loadingList.maxcount, concurrentLoadingThreads, pendingPrevious[0], pendingPrefetch[0], pendingExpired[0],
metaLoaded>0 and (tostring(metaLoaded)..(IPFSLoaded>0 and "("..tostring(IPFSLoaded)..")" or "").."+") or "",
									tilesLoaded, extraTilesLoaded>0 and "+"..tostring(extraTilesLoaded) or "",
									tilesFailed>0 and "-"..tostring(tilesFailed) or "")
print("newmetaLoaded:"..new)
		local x,y = stilltext:getLoc()
		stilltext:setString ( new );
		stilltext:fitSize()
		if getTileGroup then
			local tileGroup = getTileGroup()
			local height = tileGroup.height;
			stilltext:setLoc(stilltext:getWidth()/2+config.Screen.scale, height-stilltext:getHeight()/2)		--0*config.Screen.scale)
		else
			stilltext:setLoc(x,y)
		end
		
		if getTileGroup then
			local tileGroup = getTileGroup()
			--print("updateLoadingCount:Tile group is "..tostring(tileGroup))

			if loadingCircle then
				tileGroup:removeChild(loadingCircle)
				loadingCircle = nil
			end
			if loadingActive > 0 and loadingMax > 0 then
				local w, h = tileGroup.width, tileGroup.height
				local rScreen = math.min(w, h)/2
				local r = math.max(0.05,(1.0-(loadingActive)/(loadingMax)))*rScreen
				--print("updateLoadingGroup:r="..tostring(r))
				if r > 0 then
					local dpi = MOAIEnvironment.screenDpi
					loadingCircle = Graphics {width = r*2-2, height = r*2-2, left = w/2-r, top = h/2-r}
					loadingCircle:setPenWidth(2):drawCircle()
					loadingCircle:setColor(255/255, 69/255, 0/255, 0.5)
					loadingCircle:setPriority(2000000019)
					tileGroup:addChild(loadingCircle)
				end
			end
		end

	--else print("updateLoadingCount:No stilltext to update")
	
	end
	
end

local function checkMetaQueue(client)
	local queued = false
	local metaURL, idx, metaID = tilemgr:osmMetaTileURL(client.x, client.y, client.z, client.MBTiles)
	if metaURL ~= "" then
		if not metaTilesPending[metaID] then
			metaTilesPending[metaID] = { }
			metaTilesPending[metaID][0] = 0
			--print(string.format("Initialized metaTilesPending[%s] to zero for %s", metaID, client.key))
		end
		if not metaTilesPending[metaID][client.key] then
			metaTilesPending[metaID][client.key] = client
			metaTilesPending[metaID][0] = metaTilesPending[metaID][0] + 1
			queued = (metaTilesPending[metaID][0] > 1)
			--print(string.format("Incremented metaTilesPending[%s] to %d queued:%s for %s", metaID, metaTilesPending[metaID][0], tostring(queued), client.key))
		else
			queued = true
			--print(string.format("metaTilesPending[%s] has %d IS QUEUED %s", metaID, metaTilesPending[metaID][0], client.key))
		end
		if debugging then print(string.format("metaTilesPending[%s] has %d %s %s", metaID, metaTilesPending[metaID][0], queued and "queued" or "NEW", client.key)) end
	end
	return queued
end

local function clearDownloadedTile(key)
	local function removeKey(list)
		if list[key] then
			local removes
			for i, t in ipairs(list) do
				if t.key == key then
					if not removes then removes = {} end
					table.insert(removes, 1, i)
				end
			end
			for _, i in ipairs(removes) do
				if table.remove(list, i) ~= list[key] then
					print("Oh NO!  Didn't remove "..key.." from list!")
				end
			end
			list[key] = nil
		end
	end
	removeKey(pendingPrevious)
	removeKey(pendingPrefetch)
	removeKey(pendingExpired)
end

local function OLD_startQueueServer(client)
--	MOAICoroutine.new ():run ( function()
	if debugging then print(string.format('startQueueServer:running %i/%i/%i key:%s', client.z, client.x, client.y, client.key)) end
	if loadRunning == 0 then
		loadedCount, skippedCount, errorCount, lateCount, soonCount = 0, 0, 0, 0, 0
	end
	loadRunning = loadRunning + 1
	loadedCount = loadedCount + 1
	updateLoadingCount("loadRunning now has "..tostring(loadRunning))
	-- osmReallyLoadRemoteTile(0,x,y,z,MBTiles,callback, LastDate)
	if not osmReallyLoadRemoteTile(0,client.x,client.y,client.z,client.MBTiles,client.callback, client.LastDate, "Priority") then
		print("osmReallyLoadRemoteTile failed!  "..printableTable(tostring(client),client))
		loadRunning = loadRunning - 1
		loadedCount = loadedCount - 1
		updateLoadingCount("osmReallyLoadRemoteFile failed.  loadRunning now has "..tostring(loadRunning))
	end
end

local function OLD_queueTile(list, x, y, z, MBTiles, callback, LastDate)
	local listname = "Unknown"
	if list == pendingPrevious then listname = "Previous"
	elseif list == pendingPrefetch then listname = "Prefetch"
	elseif list == pendingExpired then listname = "Expired"
	else listname = tostring(list)
	end
	local queued = false
	local key = osmTileKey(x,y,z,MBTiles)
	local client = {n=0, x=x, y=y, z=z, key=key, MBTiles=MBTiles, callback=callback, LastDate=LastDate}
	local queued = checkMetaQueue(client)
	if not queued then
		if not list[key] then
			if loadRunning == 0 then
				startQueueServer(client)
			else
				table.insert(list, client)
				list[key] = client
				if #list > list[0] then list[0] = #list end
				updateLoadingCount("added to queue "..tostring(client).."="..tostring(client.key))
			end
		else
		local function TraceBack(start,stop)
			local result = ""
			for s=start, stop, 1 do
				local info = debug.getinfo( s, "Sl" )
				if not info then break end
				local where = info.source..':'..info.currentline
				if where:sub(1,1) == '@' then where = where:sub(2) end
				if #result > 0 then result = result.."<-"..where
				else result = where
				end
			end
			return result
		end
		local where = TraceBack(2,8)
		print("Key "..key.." Already in "..listname.." list!  from "..tostring(where))
		end
	end
end

local function OLD_osmRemoteLoadTile(n, x, y, z, MBTiles, callback)
	local now = MOAISim.getDeviceTime()*1000
	local key = osmTileKey(x,y,z,MBTiles)
--local info = debug.getinfo( 2, "Sl" )
--local where = info.source..':'..info.currentline
--if where:sub(1,1) == '@' then where = where:sub(2) end
--print(where..">osmRemoteLoadTile:tile("..key..") queued:"..tostring(queuedFiles[key]).." download:"..tostring(downloadingFiles[key]))
	if queuedFiles[key] then
		if debugging then print(string.format('osmRemoteLoadTile['..n..']:NOT queueing %s queued %ims', key, (now-queuedFiles[key]))) end
	else
		queuedFiles[key] = now
		local client = {n=n, x=x, y=y, z=z, key=key, MBTiles=MBTiles, callback=callback}
		local queued = checkMetaQueue(client)
		if not queued then
			if loadRunning >= concurrentLoadingThreads then
				if true or debugging then print(string.format('osmRemoteLoadTile[%i] queueing %i/%i/%i key:%s', n, z, x, y, key)) end
				List.pushright(loadingList, client)
				updateLoadingCount("loadingList now has "..tostring(loadingList.count))
			else
				startQueueServer(client)
			end
		end
	end
end


local queueServer	-- forward reference

local function startQueueServer()
	if debugging then print(string.format('startQueueServer:running %i/%i/%i key:%s', client.z, client.x, client.y, client.key)) end
	if loadRunning == 0 then
		loadedCount, skippedCount, errorCount, lateCount, soonCount = 0, 0, 0, 0, 0
	end
	loadRunning = loadRunning + 1
	updateLoadingCount("loadRunning now has "..tostring(loadRunning))
	runServiceCoroutine ( queueServer, loadRunning )
end

local function queueTile(list, x, y, z, MBTiles, callback, LastDate)
	local listname = "Unknown"
	if list == pendingPrevious then listname = "Previous"
	elseif list == pendingPrefetch then listname = "Prefetch"
	elseif list == pendingExpired then listname = "Expired"
	else listname = tostring(list)
	end
	local queued, key, client = false
	if type(x) == "table" then	-- Requeueing from somewhere
		key = x.key
		client = x
		queued = false	-- If we're requeueing, it's not queued!
	else
		key = osmTileKey(x,y,z,MBTiles)
		client = {n=0, x=x, y=y, z=z, key=key, MBTiles=MBTiles, callback=callback, LastDate=LastDate}
		queued = checkMetaQueue(client)
	end
	if not queued then
		if not list[key] then
			table.insert(list, client)
			list[key] = client
			if #list > list[0] then list[0] = #list end
			updateLoadingCount("added to queue "..tostring(client).."="..tostring(client.key))
			if loadRunning == 0 then
				startQueueServer()
			end
		else
		local function TraceBack(start,stop)
			local result = ""
			for s=start, stop, 1 do
				local info = debug.getinfo( s, "Sl" )
				if not info then break end
				local where = info.source..':'..info.currentline
				if where:sub(1,1) == '@' then where = where:sub(2) end
				if #result > 0 then result = result.."<-"..where
				else result = where
				end
			end
			return result
		end
		local where = TraceBack(2,8)
		print("Key "..key.." Already in "..listname.." list!  from "..tostring(where))
		end
	end
	return not queued	-- true means we queued it (it wasn't previously queued)
end

local function osmRemoteLoadTile(n, x, y, z, MBTiles, callback)
	local now = MOAISim.getDeviceTime()*1000
	local key = osmTileKey(x,y,z,MBTiles)
--local info = debug.getinfo( 2, "Sl" )
--local where = info.source..':'..info.currentline
--if where:sub(1,1) == '@' then where = where:sub(2) end
--print(where..">osmRemoteLoadTile:tile("..key..") queued:"..tostring(queuedFiles[key]).." download:"..tostring(downloadingFiles[key]))
	if queuedFiles[key] then
		if debugging then print(string.format('osmRemoteLoadTile['..n..']:NOT queueing %s queued %ims', key, (now-queuedFiles[key]))) end
	elseif not HasInternet() then
		if (callback) then callback(nil) end
	else
		queuedFiles[key] = now
		local client = {n=n, x=x, y=y, z=z, key=key, MBTiles=MBTiles, callback=callback}
		local queued = checkMetaQueue(client)
		if not queued then
			if true or debugging then print(string.format('osmRemoteLoadTile[%i] queueing %i/%i/%i key:%s', n, z, x, y, key)) end
			List.pushright(loadingList, client)
			updateLoadingCount("loadingList now has "..tostring(loadingList.count))
			if loadRunning < concurrentLoadingThreads then
				startQueueServer()
			end
		end
	end
end

--[[
function tilemgr:osmGetTileImage(n,x,y,z)
	if not MBTiles then initMBTiles() end
	local image = MBTiles:getTileImage(n, x,y,z)
	return image
end
]]

-- Preloads all tiles from z to 0 from lat,lon out to range (km) away with a
-- callback(x,y,z,status) as each tile is loaded, but not if already present
function tilemgr:buildSpiralTileList(lat,lon,range,z)
	local result = {}
	range = tonumber(range) or 50
	local maxChord = 0.5
	local b = maxChord/(2*math.pi)	-- This gives maxChord distance between spirals
	local a = math.pi
	local sPoint = LatLon.new(lat,lon)
	local sx, sy = self:osmTileNum(lat,lon,z)
	if not sx or not sy then return result end
	sx, sy = math.floor(sx)+0.5, math.floor(sy)+0.5	-- Relocate to the center of the tile
	--print(string.format("Spiral:titles ,a,r,x,y,z,d,"))
	--print(string.format("Spiral:checking ,0,0,%f,%f,%f,0,", sx,sy,z))
	repeat
		local r = a * b
		local x, y = r * math.cos(a) + sx, r * math.sin(a) + sy
		local tlat, tlon = self:osmTileLatLon(math.floor(x)+0.5, math.floor(y)+0.5, z)
		local tPoint = LatLon.new(tlat, tlon)
		local dist = sPoint.distanceTo(tPoint)
		--print(string.format("Spiral:checking ,%f,%f,%f,%f,%f,%f,", a,r,x,y,z,dist))
		x, y = math.floor(x), math.floor(y)
		local key = string.format("%d/%d/%d", z, x, y)
		if not result[key] then
			table.insert(result, { x=x, y=y, z=z })
			result[key] = 1
		else result[key] = result[key] + 1
		end
		local da = 2*math.asin(math.min(maxChord,r)/2/r)
		a = a + da
	until (dist > range)
	return result
end

function tilemgr:estimateSpiralTileCount(lat,lon,range,z)
	range = tonumber(range) or 50
	local ewdist, nsdist, ddist = self:osmTileSizeKM(lat, lon, z)
	local ewcount, nscount = range/ewdist*2, range/nsdist*2	-- range is radius and rectangle is twice that size
	local area = ewcount*nscount
	local circle = math.pi/4*area
	local actual = -1
	if circle <= 10000 then
		actual = #self:buildSpiralTileList(lat,lon,range,z)
	end
	
	print(string.format("Spiral:estimated %d or %d actual %d for %fx%f(%f) tiles over %f range", area, circle, actual, ewdist, nsdist, ddist, range))

	return circle
end

-- Preloads all tiles from z to 0 from lat,lon out to range (km) away with a
-- callback(x,y,z,status) as each tile is loaded, but not if already present
function tilemgr:spiralPreloadTiles(lat,lon,range,z,callback)
	range = tonumber(range) or 50
	local estimated = self:estimateSpiralTileCount(lat,lon,range,z)
	local maxAllowed = 10000
	if estimated > maxAllowed then
		return nil, string.format("Too Many Estimated Tiles, %d > %d", estimated, maxAllowed)
	end
	local list = self:buildSpiralTileList(lat,lon,range,z)
	local vmin, vmax = nil, nil
	for k,v in pairs(list) do
		if type(k) == 'string' and type(v) == 'number' then
			if not vmin or v < vmin then vmin = v end
			if not vmax or v > vmax then vmax = v end
		end
	end
	print(string.format("Spiral:%d elements with visits:min:%s max:%s", #list, tostring(vmin), tostring(vmax)))
	
	if type(callback) == 'function' then
		local failed, fetched, updated, OK = 0,0,0,0
		--MOAICoroutine.new():run(function()
		runServiceCoroutine(function()
			local sx, sy = self:osmTileNum(lat,lon,z)
			local abort = callback(sx,sy,z,string.format("start checking %d tiles", #list))
			for k,v in ipairs(list) do
				if callback(v.x, v.y, v.z, "move") then
					abort = true
					break
				end
				local function checkTile(x,y,z)
					local abort
					local wasOK = false
					local haveIt, LastDate = MBTiles:checkTile(0, x, y, z)
					if not haveIt then
						queueTile(pendingPrefetch, x, y, z, MBTiles, function(sprite) if sprite then fetched = fetched + 1 else failed = failed + 1 end abort = callback(x,y,z,sprite and "prefetch" or nil) end)
					elseif LastDate then
						queueTile(pendingExpired, x, y, z, MBTiles, function(sprite) if sprite then updated = updated + 1 else failed = failed + 1 end abort = callback(x,y,z,sprite and "expired" or nil) end, LastDate)
					else
						wasOK = true
						OK = OK + 1
						abort = callback(x,y,z,"OK")
					end

					repeat
						coroutine.yield()
					until self:getQueueStats() == 0 or abort
					
					if not abort and z > 0 and not wasOK then
						return checkTile(math.floor(x/2), math.floor(y/2), z-1)
					end
					print("checkTile returning "..tostring(abort))
					return abort
				end
				
				if checkTile(v.x,v.y,v.z) then
					abort = true
					print("checkTile returned ABORT("..tostring(abort)..")")
					break
				else 
					print("checkTile returned ABORT("..tostring(abort)..")")
				end
			end
			print("End of loop abort="..tostring(abort).." or "..((abort and "aborted" or "done")))
			callback(sx,sy,z,"move")
			callback(sx,sy,z,string.format("%s checking %d tiles\n%d failed\n%d fetched\n%d expired\n%d OK", (abort and "aborted" or "done"), #list, failed, fetched, updated, OK))
		end)
	end
	return #list, vmin, vmax
end



function tilemgr:osmGetTileTexture(n,x,y,z,ignoreExpired)
	if not MBTiles then initMBTiles() end
	local texture, LastDate = MBTiles:getTileTexture(n, x,y,z)
	if LastDate then
		if not ignoreExpired then
			-- print(string.format("osmGetTileTexture:queueing Expired %d/%d/%d since %s", z, x, y, os.date("!%Y-%m-%d %H:%M:%S", LastDate)))
			queueTile(pendingExpired, x, y, z, MBTiles, function(sprite) print(string.format("(Re)Loaded %d/%d/%d since %s", z, x, y, os.date("!%Y-%m-%d %H:%M:%S", LastDate))) end, LastDate)
		else
			print(string.format("Ignored Expired %d/%d/%d since %s", z, x, y, os.date("!%Y-%m-%d %H:%M:%S", LastDate)))
		end
	end
	return texture
end

function tilemgr:getTileImageOrStretch(x,y,z, callback)
	local tstart = MOAISim.getDeviceTime()
	local texture = self:osmGetTileTexture(0,x,y,z,false)
	if texture then
print(string.format("getTileTextureOrStretch:got %d/%d/%d as %s", z, x, y, tostring(texture)))
		return Sprite { texture = texture }
	end

	if callback then
		osmRemoteLoadTile(0, x,y,z, MBTiles, callback)
	end

	if z > 0 then
		local szoom, sx, sy = z, x, y
		local stretch = 0
		repeat
			szoom = szoom - 1
			stretch = stretch + 1
			sx = math.floor(sx/2) sy = math.floor(sy/2)
			local source = tilemgr:osmGetTileTexture(0,sx,sy,szoom,true)
			if source then
print(string.format("getTileTextureOrStretch:stretching %d/%d/%d from %d/%d/%d", z, x, y, szoom, sx, sy))
				local pow2 = bit.lshift(1,stretch)
				local size = 256 / pow2
				local xoffset = (x%pow2)*size
				local yoffset = (y%pow2)*size

				local image = MapSprite { texture=source }
				image:setMapSize(pow2, pow2, size, size)
				image:setMapSheets(size, size, pow2, pow2)
				image:setTile(1,1,(y%pow2)*pow2+(x%pow2)+1)
				image:setScl(pow2,pow2)
				return image, szoom

			end
		until szoom <= 0 or stretch > 5
	end
	local telapsed = (MOAISim.getDeviceTime()-tstart)*1000
print(string.format("getTileTextureOrStretch:FAILED %d/%d/%d in %dmsec", z, x, y, telapsed))
	return nil
end

function tilemgr:flushPriorityQueue(why)
	if loadingList.count > 0 then
		updateLoadingCount(tostring(why).." Flushing "..tostring(loadingList.count).." Priority to Previous")
		while loadingList.count > 0 do
			local client = List.popleft(loadingList)
			queueTile(pendingPrevious, client)
		end
	end
end

function tilemgr:osmCheckTiles(x,y,z, callback)
	local xt, yt, zt = math.floor(x), math.floor(y), z
	local checked, queued = 0, 0
	for zt = z, 0, -1 do
		local haveIt, LastDate = MBTiles:checkTile(0, xt, yt, zt)
		if not haveIt then
			local xt2, yt2, zt2 = xt, yt, zt
			if queueTile(pendingPrefetch, xt, yt, zt, MBTiles, function(sprite) if callback then callback(xt2,yt2,zt2,sprite and "prefetch" or "failed") end end) then
				queued = queued + 1
			elseif callback then
				callback(x,y,z,"pending")
			end
		elseif LastDate then
			local xt2, yt2, zt2 = xt, yt, zt
			if queueTile(pendingExpired, xt, yt, zt, MBTiles, function(sprite) if callback then callback(xt2,yt2,zt2,sprite and "expired" or "failed") end end, LastDate) then
				queued = queued + 1
			elseif callback then
				callback(x,y,z,"pending")
			end
		else
			if callback then callback(xt,yt,zt,"OK") end
			break	-- Once we get a good one, quit zooming uot the check
		end
		checked = checked + 1
		xt, yt = math.floor(xt/2), math.floor(yt/2)
	end
	print(string.format("osmCheckTiles:%d/%d/%d checked %d queued %d", z, x, y, checked, queued))
end

function tilemgr:osmLoadTile(n,x,y,z,force,callback)
	x = math.floor(x)
	y = math.floor(y)
if debugging then print(string.format("osmLoadTile:[%d]<-%d/%d/%d", n, z, x, y)) end
	if not MBTiles then initMBTiles() end
	local tryImage, opaque = nil, false
	local key = osmTileKey(x,y,z,MBTiles)
	if debugging then print('osmLoadTile['..n..'] is '..key..' in '..tostring(dir)) end
	if false and dir == MOAIEnvironment.resourceDirectory then
		--tryImage = display.newImage( file, dir, 0, 0 )
--print("Loading3 "..file)
		tryImage = Sprite { texture = file, left=0, top=0 }
	elseif downloadingFiles[key] then
		local now = MOAISim.getDeviceTime()*1000
		print(string.format('osmLoadTile['..n..']:ALREADY downloading %s for %ims', key, (now-downloadingFiles[key])))
	else
--[[
		local function isOpaque(image)
			if type(image.isOpaque) == 'function' then return image:isOpaque() end
			if type(image.getRGBA) ~= 'function' then
				print("type(image)="..type(image))
				return false
			end
			local width, height = image:getSize()
			for x=0,width-1 do
				for y=0,height-1 do
					local r,g,b,a = image:getRGBA(x,y)
					if a < 1 then return false end
				end
			end
			return true
		end
		local function isTransparent(image)
			if type(image.getRGBA) ~= 'function' then
				print("type(image)="..type(image))
				return false
			end
			local width, height = image:getSize()
			for x=0,width-1 do
				for y=0,height-1 do
					local r,g,b,a = image:getRGBA(x,y)
					if a > 0 then return false end
				end
			end
			return true
		end
]]
--		tryImage = osmLoadMBTile(n, x,y,z)
		local function addImage(image,priority)
			if image then
--				if isOpaque(image) then opaque = true end
				image = Sprite { texture = image, left=0, top=0 }
--				return image
				if not tryImage then
					tryImage = Group({width=256, height=256, left=1, top=1})	-- Need non-zero left/top to work
					tryImage:setPos(0,0)	-- Don't ask me why this is necessary
				end
				tryImage:addChild(image)
				if priority then image:setPriority(priority) end
			end
			return tryImage
		end
		
		local function addOrLoadImage(n,x,y,z,MBTiles,priority)
			local image, LastDate = MBTiles:getTileTexture(n, x,y,z)
			if image then
				if LastDate then
					-- print(string.format("osmLoadTile:queueing Expired %d/%d/%d since %s", z, x, y, os.date("!%Y-%m-%d %H:%M:%S", LastDate)))
					queueTile(pendingExpired, x, y, z, MBTiles, function(sprite) print(string.format("(Re)Loaded %d/%d/%d since %s", z, x, y, os.date("!%Y-%m-%d %H:%M:%S", LastDate))) end, LastDate)
				end
				tryImage = addImage(image,priority)
if debugging then print("osmLoadTile["..n..'] for '..z..'/'..x..'/'..y..' Loaded from '..MBTiles.name) end
			else
if debugging then print("osmLoadTile["..n..'] for '..z..'/'..x..'/'..y..' Not Found In '..MBTiles.name) end
				osmRemoteLoadTile(n, x,y,z, MBTiles, callback)
			end
			return tryImage
		end

		if TopTiles and TopTiles ~= MBTiles and not opaque then tryImage = addImage(TopTiles:getTileTexture(n, x,y,z),100) end
		if TopTiles2 and not opaque then tryImage = addImage(TopTiles2:getTileTexture(n, x,y,z),90) end
		if TopTiles3 and not opaque then tryImage = addImage(TopTiles3:getTileTexture(n, x,y,z),80) end
		if TopTiles4 and not opaque then tryImage = addImage(TopTiles4:getTileTexture(n, x,y,z),70) end
		if MBTiles and not opaque then tryImage = addOrLoadImage(n, x,y,z, MBTiles, 0) end

	end
	
	if not tryImage then
		osmRemoteLoadTile(n, x,y,z, MBTiles, callback)
	end
	return tryImage
end

local function getNextTileFromQueue()
	if loadingList.count > 0 then
		while loadingList.count > 0 do
			local client = List.popleft(loadingList)
			updateLoadingCount("Popping Leaves "..tostring(loadingList.count))
			loadedCount = loadedCount + 1
			return client, "Priority"	-- This word must not change!  It is used later.
		end
	end

	--if loadRunning == 1 then	-- Only if this is the last running queuer
	if loadRunning <= 2 then	-- Allow 2 prefetch threads
	--if loadRunning < concurrentLoadingThreads then	-- Keep at least 1 available
		local function dequeueTile(list, why)
			local client = table.remove(list)
			if not client then return nil end
			list[client.key] = nil
			updateLoadingCount("dequeueing item "..tostring(client).." "..tostring(client.key))
			return client, why
		end
		local client, why = dequeueTile(pendingPrevious, "Previous")
		if not client then client, why = dequeueTile(pendingPrefetch, "Prefetch") end
		if not client then client, why = dequeueTile(pendingExpired, "Expired") end
		if client then return client, why end
	end
	return nil	-- Nothing to do, trust the co-routine to exit now
end

function queueServer(which)
	print(string.format("queueuServer %d/%d Running...", which, loadRunning))
	local client, why = getNextTileFromQueue()
	while client ~= nil do
		if HasInternet() then
			local co = coroutine.create( osmReallyLoadRemoteTile )
			repeat
				local ok, msg = coroutine.resume( co, 0,client.x,client.y,client.z,client.MBTiles,client.callback, client.LastDate, why )
				if not ok then
					local full_tb = debug.traceback( co )
								 .. "\n" .. debug.traceback( ) -- with 'stack traceback:' line
								 -- .. debug.traceback( ):sub( 17 ) -- drop 'stack traceback:' line
					print("osmReallyLoadRemoteTile2 failed with\n"..tostring(msg).."\n"..full_tb)
					toast.new(msg)
				else coroutine.yield()
				end
			until coroutine.status(co) ~= "suspended"
		else print("queueServer:Dumping tile request due to No Internet")
		end
		client, why = getNextTileFromQueue()
	end
	loadRunning = loadRunning - 1
	updateLoadingCount("queue empty.  loadRunning now has "..tostring(loadRunning))
	print(string.format("queueuServer %d Terminating!  %d still running.", which, loadRunning))
	if loadRunning == 0 then
		saveIPFSGateways(MBTiles)
	end
end

local function OLD_propagateLoadingList()
	if debugging then print('propagateLoadingList:loadingList:'..loadingList.count.." loadRunning:"..loadRunning); end
	local didOne = false
	if loadingList.count > 0 then
		while loadingList.count > 0 do
			local client = List.popleft(loadingList)
			updateLoadingCount("Popping Leaves "..tostring(loadingList.count))
			loadedCount = loadedCount + 1
			--osmReallyLoadRemoteTile(client.n, client.x, client.y, client.z, client.MBTiles, client.callback)
			if not osmReallyLoadRemoteTile(client.n, client.x, client.y, client.z, client.MBTiles, client.callback, nil, "Priority") then
				print("osmReallyLoadRemoteTile failed!  "..tostring(printableTable(tostring(client),client)))
				loadRunning = loadRunning - 1
				loadedCount = loadedCount - 1
				updateLoadingCount("osmReallyLoadRemoteFile failed.  loadRunning now has "..tostring(loadRunning))
			end
			didOne = true
			break
		end
	end
	if loadingList.count <= 0 and not didOne then
		if loadRunning == 1 then
			local function dequeueTile(list, why)
				local client = table.remove(list)
				if not client then return false end
				list[client.key] = nil
				updateLoadingCount("dequeueing item "..tostring(client).." "..tostring(client.key))
				--osmReallyLoadRemoteTile(client.n, client.x, client.y, client.z, client.MBTiles, client.callback, client.LastDate)
				if not osmReallyLoadRemoteTile(client.n, client.x, client.y, client.z, client.MBTiles, client.callback, client.LastDate, why) then
					print("osmReallyLoadRemoteTile failed!  "..tostring(printableTable(tostring(client),client)))
					loadRunning = loadRunning - 1
					loadedCount = loadedCount - 1
					updateLoadingCount("osmReallyLoadRemoteFile failed.  loadRunning now has "..tostring(loadRunning))
				end
				didOne = true
				return true
			end
			if not dequeueTile(pendingPrevious, "Previous") then
				if not dequeueTile(pendingPrefetch, "Prefetch") then
					if not dequeueTile(pendingExpired, "Expired") then
						pendingPrevious[0] = 0
						pendingPrefetch[0] = 0
						pendingExpired[0] = 0
						didOne = false
					end
				end
			end
		end
		if not didOne then
			local now = MOAISim.getDeviceTime()*1000
			--print(string.format("propagateLoadingList:Remote Loading ran for %ims, max %i", now-loadRunning, loadingList.maxcount))
			loadRunning = loadRunning - 1
			updateLoadingCount("loadRunning gone leaves "..tostring(loadRunning))
		end
	end
	if debugging then print('propagateLoadingList:Done'); end
end

local recentFailures = {}

local function purgeRecentFailures()
	local now = MOAISim.getDeviceTime()*1000
	local delCount, keepCount = 0, 0
	for k,v in pairs(recentFailures) do
		if now-v > 60000 then
			--print("Removing failure "..tostring(now-v).."ms "..tostring(k))
			recentFailures[k] = nil
			delCount = delCount + 1
		else	keepCount = keepCount + 1
		end
	end
--[[
	if delCount > 0 or keepCount > 0 then
		print(string.format("purgeRecentFailures deleted %i, retained %i", delCount, keepCount))
	end
	local queCount = 0
	for k,v in pairs(queuedFiles) do
		queCount = queCount + 1
	end
	if queCount > 0 then
		print(string.format('purgeRecentFailures:%d in queue', queCount))
	end
]]
end

local function getDateExpires(task, URL)
-- Expires: Tue, 25 Sep 2018 09:31:51 GMT
-- CacheControl: max-age=115134, stale-while-revalidate=604800, stale-if-error=604800
	local LastModified = task:getResponseHeader("Last-Modified")
	local CacheControl = task:getResponseHeader("Cache-Control")
	local Expires = task:getResponseHeader("Expires")
	local Date = task:getResponseHeader("Date")

	if LastModified then print("getDateExpires:"..URL.." Date:"..tostring(Date).." Expires:"..tostring(Expires).." Last-Modified:"..tostring(LastModified)) end
	--print("getDateExpires:"..URL.." Date:"..tostring(Date).." Expires:"..tostring(Expires).." CacheControl:"..tostring(CacheControl))

	if LastModified then LastModified = convertHttpTimestamp(LastModified) end
	if Expires then Expires = convertHttpTimestamp(Expires) end
	if Date then Date = convertHttpTimestamp(Date) end

	if CacheControl then
		local maxAge = CacheControl:match('max%-age=(%d+)')
		if maxAge then
			--print(string.format("getDateExpires:%s gave %s or %s", CacheControl, maxAge, tostring(tonumber(maxAge))))
			maxAge = tonumber(maxAge)
			if type(Date) == 'number' and type(maxAge) == 'number' then
				if Expires ~= (Date+maxAge) then
					print(string.format("Trumping Expires(%s) with maxAge:%d or %s", tostring(task:getResponseHeader("Expires")), maxAge, os.date("!%Y-%m-%d %H:%M:%S",Date+maxAge)))
				end
				Expires = Date + maxAge
			end
		else print("No max-age= found in "..tostring(CacheControl))
		end
	end

	if LastModified then print("getDateExpires:"..URL.." Date:"..tostring(Date).." Expires:"..os.date("!%Y-%m-%d %H:%M:%S",Expires).." Last-Modified:"..os.date("!%Y-%m-%d %H:%M:%S",LastModified)) end
	if (false or debugging) and type(Date) == 'number' then
		local now = os.time()
		if Date ~= now then
			print(string.format("Date %d Now %d Diff %d", Date, now, now-Date))
		end
		if type(Expires) == 'number' then
			print(string.format("%s Expires +%d seconds or %.2f hours or %.2f days",URL, Expires-Date, (Expires-Date)/3600, (Expires-Date)/3600/24))
		end
	end
	return Date, Expires
end

local function getURL(URL, stream, why)
	local task = MOAIHttpTask.new ()
	if debugging then task:setVerbose(true) end
	task:setVerb ( MOAIHttpTask.HTTP_GET )
	task:setUrl ( URL )
	task:setStream ( stream )
	task:setTimeout ( 30 )
	--task:setCallback ( metaListener )
--[[
	if LastDate and LastDate ~= 0 then
		local luathen = luadate(LastDate)
		local sthen = luathen:fmt("${http}")
		print(string.format("%s If-Modified-Since: %s", metaURL, sthen))
		task:setHeader("If-Modified-Since", sthen)
	end
]]
	task:setUserAgent ( string.format('%s %s from %s %s', tostring(why),
										tostring(config.StationID),
										MOAIEnvironment.appDisplayName,
										tostring(config.About.Version)) )
	task:performAsync ()
	while task:isBusy() do
		coroutine.yield()
	end
	local sl = stream:getString()
	if sl then sl = #sl else sl = 0 end
	print(string.format("%s Read %d, cl %s, gs %d, status %d", URL, task:getSize(), tostring(task:getResponseHeader("Content-Length")), sl, task:getResponseCode()))
	return task

end

local function getURLContent(URL, why)
	local stream = MOAIMemStream.new ()
	stream:open ( )
	local task = getURL(URL, stream, why)
	local responseCode = task:getResponseCode()
	if type(task.getResultCode) == "function" and task:getResultCode() ~= 0 then
		local resultCode = task:getResultCode()
		if resultCode == 22 then	-- CURLE_HTTP_RETURNED_ERROR
			resultCode = responseCode	-- switch to actual HTTP error code
			print ( "getURLContent:HTTP error:"..resultCode.." from "..URL)
		elseif resultCode == 28 then	-- CURLE_OPERATION_TIMEDOUT
			if resultCode == 200 then	-- But HTTP looked ok
				local length = task:getResponseHeader("Content-Length")
				if length then length = tonumber(length) end
				if length then
					stream:seek(0)
					local content, readbytes = stream:read()
					local text = string.format("%s Content-Length %s read %s content %s TO=200", URL, tostring(length), tostring(readbytes), tostring(#content))
					print(text)
					toast.new(text)
				end
			end
		else print ( "getURLContent:CURL error:"..resultCode.." from "..URL)
		end
		stream:close()
		return nil, tostring(resultCode)
	elseif responseCode ~= 200 then
		print ( "getURLContent:Network error:"..responseCode.." from "..URL)
		stream:close()
		return nil, tostring(responseCode)
	else
		stream:seek(0)
		local content, readbytes = stream:read()
		local test = stream:getString()
		if test then test = #test else test = 0 end
		stream:close()
		print(string.format("%s Read %d content is %d test is %d", URL, readbytes, #content, test))
		
		local length = task:getResponseHeader("Content-Length")
		if length then
			length = tonumber(length)
			if length then
				if length ~= readbytes then
					local text = string.format("%s Content-Length %s read %s", URL, tostring(length), tostring(readbytes))
					print(text)
					toast.new(text)
					return nil, -1
				elseif content and length ~= #content then
					local text = string.format("%s Content-Length %s #content %s", URL, tostring(length), tostring(#content))
					print(text)
					toast.new(text)
					return nil, -1
				end
			else
				local text = string.format("%s non-numeric Content-Length %s", URL, tostring(task:getResponseHeader("Content-Length")))
				print(text)
				toast.new(text)
			end
		end

		return content, task
	end
end

local probeContentCount, primeGatewayCount = 0, 0
local IPFSGateways, IPFSHomeGateway, IPFSLocalGateway, IPFSPriorityGateway, IPFSGatewayGateway, IPFSHasNotGateway, IPFSHasGateway
local IPFSPrioritySkipped, IPFSFailures, IPFSHasNot, IPFSGatewayHits, IPFSLocalHits = 0, 0, 0, 0, 0
local IPFSRevision
local usedChoices = {}

function formatChoices()
		local a = {}
		for k in pairs(usedChoices) do
			table.insert(a,k)
		end

		table.sort(a, function(l,r)
			if type(l)=="number" and type(r)=="number" then
				return l<r
			elseif type(l)~="number" and type(r)=="number" then
				return true
			elseif type(l)=="number" and type(r)~="number" then
				return false
			else
				return tostring(l) < tostring(r)
			end end)
		local result = ""
		for i, c in ipairs(a) do
			if result ~= "" then result = result.."\n" end
			result = result..string.format("[%d] %d", c, usedChoices[c])
		end
		return result
end

local function getGatewayAverage(gateway, newElapsed)
	if not gateway.avgRecent or not gateway.recentTimed or not gateway.recentElapsed then return "" end
	local avg = gateway.avgRecent
	local timed = gateway.recentTimed
	local elapsed = gateway.recentElapsed
	if new then
		if timed >= 20 then
			timed = timed - 1
			elapsed = elapsed - avg
		end
		timed = timed + 1
		elapsed = elapsed + newElapsed
		avg = elapsed / timed
	end
	return string.format("%.0fms/%d", avg, timed)
end

local function updateGatewayAverage(gateway, elapsed)
	if not gateway.totalTimed then gateway.totalTimed = 0 end
	if not gateway.totalElapsed then gateway.totalElapsed = 0 end
	gateway.totalTimed = gateway.totalTimed + 1
	gateway.totalElapsed = gateway.totalElapsed + elapsed
	gateway.avgTimed = gateway.totalElapsed / gateway.totalTimed
	if not gateway.recentTimed then gateway.recentTimed = 0 end
	if not gateway.recentElapsed then gateway.recentElapsed = 0 end
	if gateway.recentTimed >= 20 then
		gateway.recentTimed = gateway.recentTimed - 1
		gateway.recentElapsed = gateway.recentElapsed - gateway.avgRecent
	end
	gateway.recentTimed = gateway.recentTimed + 1
	gateway.recentElapsed = gateway.recentElapsed + elapsed
	gateway.avgRecent = gateway.recentElapsed / gateway.recentTimed
	gateway.dirty = true
	return getGatewayAverage(gateway)
end

local function prettyPrintURI(URI)
	if URI:match("^https://") then
		URI = URI:sub(9)
	end
	if URI:match("^http://") then
		URI = URI:sub(8)
	end
	if URI:match("^ipfs%.") and URI ~= "ipfs.io/" then
		URI = URI:sub(6)
	end
	if URI:match("^gateway%.") and URI ~= "gateway.ipfs.io/" then
		URI = URI:sub(9)
	end
	if URI:sub(-1) == "/" then
		URI = URI:sub(1,-2)
	end
	local domains = { ".com", ".org", ".net", 
						".io", ".at", ".co", ".id", ".lc", ".se",  
						".cloud", ".link", ".network", ".ninja", ".ovh" }
	for _, d in ipairs(domains) do
		if URI:match("%"..d.."$") then
			URI = URI:sub(1,-#d-1)
			break
		end
	end
	return URI
end

local function formatGatewayStats(g, narrow)
	local result = prettyPrintURI(tostring(g.URI))
	if g.gotZoom then

		local a = {}
		for k in pairs(g.gotZoom) do
			table.insert(a,k)
		end
		table.sort(a, function(l,r)
			local which = string.format("%s(%s) %s(%s) => ", type(l), tostring(l), type(r), tostring(r))
			if type(l)=="number" and type(r)=="number" then
				--print(which..tostring(l<r))
				return l<r
			elseif type(l)~="number" and type(r)=="number" then
				--print(which.."true")
				return true
			elseif type(l)=="number" and type(r)~="number" then
				--print(which.."false")
				return false
			else
				--print(which..tostring(tostring(l)<tostring(r)))
				return tostring(l) < tostring(r)
			end end)

		local has = ""

		if true or not narrow then
			local p = {}
			for i, k in ipairs(a) do
				local v = g.gotZoom[k]
				if #p == 0 or not tonumber(p[#p].last) or not tonumber(k) or p[#p].last+1 ~= k then
					p[#p+1] = { first=k, last=k }
				else p[#p].last = k
				end
			end
			local ranges = ""
			local gotNumber = false
			for i, t in ipairs(p) do
				if ranges ~= "" and gotNumber then ranges = ranges.."," end
				if tonumber(t.first) then
					gotNumber = true	-- Need commas after numbers
					ranges = ranges..tostring(t.first)
				else
					ranges = ranges..t.first:sub(1,1)	-- Only first characters
				end
				if t.first ~= t.last then
					gotNumber = true
					ranges = ranges.."-"..tostring(t.last)
				end
			end
			if ranges == "ar0-20" then ranges = "ar*"
			elseif ranges == "r0-20" then ranges = "r*"
			elseif ranges == "0-20" then ranges = "*"
			end
			if ranges ~= "" then result = result.." z:"..ranges end
		end
		
		if not narrow then
			for i, k in ipairs(a) do
				local v = g.gotZoom[k]
				if v > 0 then
					if has ~="" then has = has.." " end
					has = has..tostring(k)
					has = has..":"..tostring(v)
				end
			end
			if has ~= "" then result = result.." g:"..has end
		end
	end
	if g.good and g.good > 0 then result = result.." G:"..tostring(g.good) end
	if isDesktop and g.avgTimed then result = result..string.format(" %.0fms/%d", g.avgTimed, g.totalTimed or 0) end
	if g.avgRecent then result = result..string.format(" %.0fms/%d", g.avgRecent, g.recentTimed or 0) end
	if g.timeout and g.timeout > 0 then result = result.." TO:"..tostring(g.timeout) end
	if g.bad then
		local bad = ""
		for k,c in pairs(g.bad) do
			bad = bad.." "..tostring(k)..":"..tostring(c)
		end
		if bad ~= "" then
			result = result..bad
		end
	end
	return result
end

local function fastestGatewaySort(l,r)
	if (l.avgRecent or 0) < (r.avgRecent or 0) then return true end
	if (l.avgRecent or 0) > (r.avgRecent or 0) then return false end
	if (l.avgTimed or 0) < (r.avgTimed or 0) then return true end
	if (l.avgTimed or 0) > (r.avgTimed or 0) then return false end
	if (l.timeout or 0) < (r.timeout or 0) then return true end
	if (l.timeout or 0) > (r.timeout or 0) then return false end
	if (l.good or 0) > (r.good or 0) then return true end
	if (l.good or 0) < (r.good or 0) then return false end
	return l.URI < r.URI
end

local function displayGatewaySort(l,r)
	if type(l) ~= "number" or type(r) ~= "number" or l < 1 or l > #IPFSGateways or r < 1 or r > #IPFSGateways then
		print(string.format("l=%s(%s) r=%s(%s) c=%d", type(l), tostring(l), type(r), tostring(r), #IPFSGateways))
	end
	local lt, rt = IPFSGateways[l], IPFSGateways[r]
	
	if lt.gotZoom and rt.gotZoom then
		return fastestGatewaySort(lt, rt)
	end
	if lt.gotZoom and not rt.gotZoom then return true end
	if not lt.gotZoom and rt.gotZoom then return false end
	
	local function badTotal(t)
		local res = t.timeout
		for k, c in pairs(t.bad) do
			res = res + c
		end
		return res
	end
	local lb, rb = badTotal(lt), badTotal(rt)
	if lt.good > rt.good then return true end
	if lt.good < rt.good then return false end
	if lt.good > 0 and lt.good == rt.good then
		if lb < rb then return true end
		if lb > rb then return false end
		return lt.URI < rt.URI
	end
	if lt.good > 0 and rt.good <= 0 then return true end
	if lt.good <= 0 and rt.good > 0 then return false end
	if lb < rb then return true end
	if lb > rb then return false end
	return lt.URI < rt.URI
end

function formatIPFSSummary()
	local text = ""
--print(string.format("LG:%s probe:%d IPG:%s prime:%d/%s",
--					tostring(IPFSLocalGateway), probeContentCount,
--					tostring(IPFSGateways), primeGatewayCount, IPFSGateways and #IPFSGateways or 0))
	if probeContentCount < 20 then
		text = text..string.format(" Probe:%d/%d", probeContentCount, 20)
	end
	if IPFSGateways and primeGatewayCount < #IPFSGateways then
		text = text..string.format(" Prime:%d/%d", primeGatewayCount, #IPFSGateways)
	end
	if IPFSPrioritySkipped > 0 then
		text = text.." Priority:"..tostring(IPFSPrioritySkipped)
	end
	if IPFSGatewayHits > 0 then
		text = text.." Gateway:"..tostring(IPFSGatewayHits)
	end
	if IPFSLocalHits > 0 then
		text = text.." Local:"..tostring(IPFSLocalHits)
	end
	if IPFSHasNot > 0 then
		text = text.." HasNot:"..tostring(IPFSHasNot)
	end
	if IPFSFailures > 0 then
		text = text.." Failed:"..tostring(IPFSFailures)
	end
	return text
end

function formatIPFSContents()
	if not IPFSGateways or #IPFSGateways <= 0 then return "No IPFS Gateways" end
	local result
	if isDesktop then
		result = os.date().."\n"
	else result = ""
	end
	
	local text = "IPFS"
	if IPFSRevision then
		text = text.." Revision:"..tostring(IPFSRevision)
	end
	result = result..text.."\n"

	local summary = formatIPFSSummary()
	if summary ~= "" then
		result = result..summary
		if isDesktop then
			result = result.."\n"
		end
	end

	local got = {}
	local function summarize(g)
		if g and g.gotZoom then
			for z, c in pairs(g.gotZoom) do
				if not got[z] then got[z] = 0 end
				got[z] = got[z] + c
			end
		end
	end
	summarize(IPFSGatewayGateway)
	summarize(IPFSHomeGateway)
	summarize(IPFSLocalGateway)

	local has = ""
	if IPFSHasGateway.gotZoom then
		local a = {}
--print(printableTable("IPFSHasGateway.gotZoom", IPFSHasGateway.gotZoom))
		for z in pairs(IPFSHasGateway.gotZoom) do
			if tonumber(z) then
--print("formatIPFSContents:Inserting "..tostring(z))
				table.insert(a,z)
			else print(string.format("non-number in IPFSHasGateway %s(%s)", type(z), tostring(z)))
			end
		end
		table.sort(a, function(l,r)
			if type(l)=="number" and type(r)=="number" then
				return l<r
			else
				return tostring(l) < tostring(r)
			end end)
		has = "zz local %rng/%all IPFS  %all nnnn:G"
		local counts = tilemgr:getMBTilesCounts()
		for i, z in ipairs(a) do
			local v = IPFSHasGateway.gotZoom[z]
			if v > 0 or (counts and counts[z] and counts[z] > 0) then
				if has ~="" then has = has.."\n" end
				local z2 = 2^z
				local ztotal = z2*z2
				local tc = math.max(z2*z2/64,1)
				local p = v / tc * 100

				local c = counts and counts[z] or {count=0, min_x=0, max_x=0, min_y=0, max_y=0}
				local ctotal = (c.max_y-c.min_y+1)*(c.max_x-c.min_x+1)

				has = has.. string.format("%-2d %5s %3d%%/%3d%% %5s %3d%%",
								z, human(c.count), c.count/ctotal*100, ctotal/ztotal*100,
								human(math.min(v*64,z2*z2)), p)

				-- has = has..string.format("%2d %5s %3d%%", z, human(v), p)
				if got[z] and got[z] > 0 then
					has = has..string.format(" %4d:G", got[z])
				else has = has.."     :G"
				end
			end
		end
		if has == "" then has = "IPFS Has Nothing?" end
	else has = "IPFS Contents Not Known (yet?)"
	end

	if result ~= "" then result = result.."\n" end
	result = result..has
	return result
end

function formatGatewayCounts(which)	-- 0=all, 1=good, -1=bad
	if not IPFSGateways or #IPFSGateways <= 0 then return "No IPFS Gateways" end
	local result
	if isDesktop then
		result = os.date().."\n"
	else result = ""
	end
	
	do	-- Hide local text
		local text = formatIPFSSummary()
		if text ~= "" then
			result = result.."IPFS"..text
			if isDesktop then
				result = result.."\n"
			end
		end
	end
	local narrow = not isDesktop
	local a = {}
	for n, g in ipairs(IPFSGateways) do
		if which==0
		or (which==1 and g.good > 0)
		or (which==-1 and g.good == 0) then
			table.insert(a, n)
		end
	end
	table.sort(a, displayGatewaySort)
	for i, k in ipairs(a) do
		local g = IPFSGateways[k]
		if result ~= "" then result = result.."\n" end
		result = result..formatGatewayStats(g, narrow)
	end
	
	local didDouble = which ~= 1
	if not isDesktop then didDouble = true end
	if which ~= -1 and IPFSPriorityGateway then
		local text = formatGatewayStats(IPFSPriorityGateway, narrow)
		if text ~= IPFSPriorityGateway.URI then
			if result ~= "" then result = result.."\n" end
			if result ~= "" and not didDouble then result = result.."\n" didDouble = true end
			result = result..text
		end
	end
	if which ~= -1 and IPFSGatewayGateway then
		local text = formatGatewayStats(IPFSGatewayGateway, narrow)
		if text ~= IPFSGatewayGateway.URI then
			if result ~= "" then result = result.."\n" end
			if result ~= "" and not didDouble then result = result.."\n" didDouble = true end
			result = result..text
		end
	end
	if which ~= -1 and IPFSHasNotGateway then
		local text = formatGatewayStats(IPFSHasNotGateway, narrow)
		if text ~= IPFSHasNotGateway.URI then
			if result ~= "" then result = result.."\n" end
			if result ~= "" and not didDouble then result = result.."\n" didDouble = true end
			result = result..text
		end
	end
	if which ~= -1 and IPFSHomeGateway then
		if result ~= "" then result = result.."\n" end
		if result ~= "" and not didDouble then result = result.."\n" didDouble = true end
		result = result..formatGatewayStats(IPFSHomeGateway, narrow)
	end
	if which ~= -1 and IPFSLocalGateway then
		if result ~= "" then result = result.."\n" end
		if result ~= "" and not didDouble then result = result.."\n" didDouble = true end
		result = result..formatGatewayStats(IPFSLocalGateway, narrow)
	end

	return result
end

local IPFSScroll = {}
local function updateIPFS(text)
	if #IPFSScroll > 4 then table.remove(IPFSScroll,1) end
	IPFSScroll[#IPFSScroll+1] = os.date("%H:%M:%S ")..text
	IPFSUpdate = ""
	for i, t in ipairs(IPFSScroll) do
		if IPFSUpdate ~= "" then IPFSUpdate = IPFSUpdate.."\n" end
		IPFSUpdate = IPFSUpdate..t
	end
	print("updateIPFS:"..text)
end

local function getFromIPFSGateway(gateway, MBTiles, metaID, why)
	if MBTiles.IPFSBase and gateway.URI then
		if not HasInternet() then
			return nil, "getFromIPFSGateway: No Internet"
		end
		local URI = gateway.URI
		local ipfsURL = URI..MBTiles.IPFSBase.."/"..metaID
		updateIPFS("Get:"..URI.." "..metaID)
		local start = MOAISim.getDeviceTime()
		local content, task = getURLContent(ipfsURL, why)
		local elapsed = (MOAISim.getDeviceTime() - start) * 1000
		local avg = getGatewayAverage(gateway, elapsed)
		if not content then print ( "getFromIPFSGateway:Network status:"..tostring(task)..' from '..tostring(ipfsURL)) end
		if content then
			if not gateway.good then gateway.good = 0 end
			gateway.good = gateway.good + 1
			updateIPFS(string.format("%s   G+ %dms %s", URI, elapsed, avg))
			return content, task, ipfsURL
		elseif tonumber(task) and tonumber(task) == 0 then
			if not gateway.timeout then gateway.timeout = 0 end
			gateway.timeout = gateway.timeout + 1
			updateIPFS(string.format("%s   TO+ %dms %s", URI, elapsed, avg))
		else
			local rp = tostring(task)
			if not gateway.bad then gateway.bad = {} end
			if not gateway.bad[rp] then gateway.bad[rp] = 0 end
			gateway.bad[rp] = gateway.bad[rp] + 1
			updateIPFS(string.format("%s   %s %dms %s", URI, rp, elapsed, avg))
		end
		return nil, task
	end
	return nil, "getFromIPFSGateway Not Available "..tostring(MBTiles.IPFSBase).." "..tostring(gateway.URI)
end	

--local MBTtiles_IPFShas

local function parseDirectoryList(z, list, MBTiles)

	local lineCount, dirCount, goodCount, yieldCount = 0, 0, 0, 0
	local maxTime = MOAISim.getStep() / 2	-- Max loop time is 1/2 step (50%)
	local start = MOAISim.getDeviceTime()
	local dir = ""
	for line in string.gmatch(list, "(%C+)%c") do
		--print("Line="..tostring(line))
		lineCount = lineCount + 1
		if line:sub(-1) == ":" then
			dir = line:sub(1,-2).."/"
			dirCount = dirCount + 1
		elseif line:sub(-5) == ".meta" then
			local words = {}
			for w in string.gmatch(line, "(%S+)%s*") do words[#words+1] = w end
			if #words == 9 then
				local metaID = dir..words[9]
				--print(string.format("metaID:%s Date:%s %s or %s", metaID, words[6], words[7], tostring(modified)))
				if words[8] == "+0000" then
					local modified = convertHttpTimestamp(words[6].." "..words[7])
					if not MBTiles.IPFShas then
						MBTiles.IPFShas = {}
						MBTiles.IPFShasCount = 0
						print(string.format("MBTiles(%s).new IPFShas(%s)", tostring(MBTiles), tostring(MBTiles.IPFShas)))
					end
					MBTiles.IPFShas[metaID] = modified
					MBTiles.IPFShasCount = MBTiles.IPFShasCount + 1
					goodCount = goodCount + 1
					local mz = tonumber(metaID:match("^(%d+)/"))
					if mz then
						if mz ~= z then print(string.format("MBTiles(%s) IPFShas(%s) mz(%d) ~= z(%d)",
											tostring(MBTiles), tostring(MBTiles.IPFShas), mz, z)) end
						if not IPFSHasGateway.gotZoom then IPFSHasGateway.gotZoom = {} end
						if not IPFSHasGateway.gotZoom[mz] then
							IPFSHasGateway.gotZoom[mz] = 0
							print(string.format("MBTiles(%s) IPFShas(%s) new IPFSHasGateway.gotZoom[%d]=%s",
											tostring(MBTiles), tostring(MBTiles.IPFShas),
											mz, tostring(IPFSHasGateway.gotZoom[mz])))
						end
						IPFSHasGateway.gotZoom[mz] = IPFSHasGateway.gotZoom[mz] + 1
					else print(string.format("IPFShas(%s) invalid metaID=%s or '%s'",
								tostring(MBTiles.IPFShas), tostring(metaID), tostring(metaID:match("^(%d+)/"))))
					end
				else
					print(string.format("metaID:%s NOT UTC (+0000) but %s", metaID, words[8]))
				end
			else
				print(string.format(".meta has %d words, expected 9 in:%s", #words, line))
				for i, w in ipairs(words) do
					print(string.format("[%d]=%s", i, w))
				end
			end
		else
			print("Unrecognized line:"..tostring(line))
		end
		local elapsed = (MOAISim.getDeviceTime()-start)
		if elapsed > maxTime then
			yieldCount = yieldCount + 1
			coroutine.yield()
			start = MOAISim.getDeviceTime()
		end
	end
	print(string.format("MBTiles(%s) IPFShas(%s) done IPFSHasGateway.gotZoom[%d]=%s",
					tostring(MBTiles), tostring(MBTiles.IPFShas),
					z, tostring(IPFSHasGateway.gotZoom[z])))
	print(printableTable("IPFSHasGateway.gotZoom", IPFSHasGateway.gotZoom))
	print(string.format("MBTiles(%s).IPFShas(%s) parseDirectory(%d) had %d lines, %d dir, %d good over %d yields",
						tostring(MBTiles), tostring(MBTiles.IPFShas), z, lineCount, dirCount, goodCount, yieldCount))
	updateIPFS(string.format("parseDirectory(%d) had %d lines, %d dir, %d good over %d yields",
						z, lineCount, dirCount, goodCount, yieldCount))
	if (dirCount+goodCount ~= lineCount) then
		print(string.format("parseDirectory(%d) had %d BAD lines!", z, lineCount-dirCount-goodCount))
	end
end

local function refreshZoomAvailability(MBTiles)
	local function tryGateway(gateway, MBTiles, metaID, why, z, failures)
		local URI = gateway.URI
		local ipfsURL = URI..MBTiles.IPFSBase.."/"..metaID
		--updateIPFS("Get:"..ipfsURL)	-- getFromIPFSGateway logs this
		local start = MOAISim.getDeviceTime()
		local content, task = getFromIPFSGateway(gateway, MBTiles, metaID, why)
		if not content then print ( "tryGateway:Network status:"..tostring(task)..' from '..tostring(ipfsURL)) end
		if content then
			local elapsed = (MOAISim.getDeviceTime() - start) * 1000
			return content, task, ipfsURL
		elseif tonumber(task) and tonumber(task) == 0 then
			local elapsed = (MOAISim.getDeviceTime() - start) * 1000
		else
			local rp = tostring(task)
		end
		return nil, task
	end

	local function getFromIPFS(MBTiles, metaID, why, z)
		if not IPFSGateways and not IPFSHomeGateway and not IPFSLocalGateway then return nil, "No IPFSGateways defined" end

		local failures = {}

		if true and IPFSLocalGateway then	-- Prefer the local gateway if we have one!
			local gateway = IPFSLocalGateway
			local URI = gateway.URI
			local ipfsURL = URI..MBTiles.IPFSBase.."/"..metaID
			print(string.format("getFromIPFS from LOCAL %s", ipfsURL))
			local content, task, actualURL = tryGateway(gateway, MBTiles, metaID, why, z, failures)
			if content then
				return content, task, actualURL
			end
		end

		local choices = {}
		if IPFSGateways then
			for i, g in ipairs(IPFSGateways) do
				if g.gotZoom and g.gotZoom["root"] then
					choices[#choices+1] = g
				end
			end
		end
		if #choices == 0 and IPFSHomeGateway then
			choices[#choices+1] = IPFSHomeGateway
		end
		if #choices == 0 and IPFSLocalGateway then
			choices[#choices+1] = IPFSLocalGateway
		end
		if #choices == 0 then
			return nil, string.format("Zoom %d Not Available via IPFS", z)
		end
		local choiceCount = #choices
		table.sort(choices, fastestGatewaySort)

		while #choices > 0 do
			local choice = math.random(#choices)
			choice = 1	-- Always use 1st choice for priming
			local gateway = choices[choice]
			local URI = gateway.URI
			local ipfsURL = URI..MBTiles.IPFSBase.."/"..metaID
			print(string.format("getFromIPFS choice %d/%d from %s", choice, #choices, ipfsURL))
			table.remove(choices, choice)
			local content, task, actualURL = tryGateway(gateway, MBTiles, metaID, why, z, failures)
			if content then
				return content, task, actualURL
			end
		end
		if IPFSHomeGateway then
			local gateway = IPFSHomeGateway
			local URI = gateway.URI
			local ipfsURL = URI..MBTiles.IPFSBase.."/"..metaID
			print(string.format("getFromIPFS from HOME %s", ipfsURL))
			local content, task, actualURL = tryGateway(gateway, MBTiles, metaID, why, z, failures)
			if content then
				return content, task, actualURL
			end
		end
		if IPFSLocalGateway then	-- This is redundant based on preferring it above
			local gateway = IPFSLocalGateway
			local URI = gateway.URI
			local ipfsURL = URI..MBTiles.IPFSBase.."/"..metaID
			print(string.format("getFromIPFS from LOCAL %s", ipfsURL))
			local content, task, actualURL = tryGateway(gateway, MBTiles, metaID, why, z, failures)
			if content then
				return content, task, actualURL
			end
		end
		
		local text = ""
		for k,v in pairs(failures) do
			if text ~= "" then text = text.." " end
			text = text..tostring(k)..":"..tostring(v)
		end
		print("getFromIPFS:IPFS completely failed("..text..") to get "..metaID)
		updateIPFS("IPFS Failed("..text.."):"..metaID)
		return nil, string.format("IPFS Failed %d Gateways", choiceCount)
	end	

	local function refreshZoom(MBTiles, z)
		local fileID = string.format("%d.txt", z)
		while true do
			local content, task, actualURL = getFromIPFS(MBTiles, fileID, "Zoom Availability", z)
			if content then
				print(string.format("refreshZoomAvailability:got %d bytes of %s from %s", #content, fileID, tostring(actualURL)))
				parseDirectoryList(z, content, MBTiles)
				break
			end
			print(string.format("refreshZoomAvailability(%s) Failed with %s", fileID, tostring(task)))
			local restart = os.time() + 5
			while os.time() < restart do
				coroutine.yield()
			end
			print(string.format("refreshZoomAvailability(%s) Retrying...", fileID))
		end
	end
	
	print("Refreshing zoom availability MBTiles="..tostring(MBTiles))

	if MBTiles.IPFSBase then
		while true do
			local content, task, actualURL = getFromIPFS(MBTiles, "revision.txt", "Revision", 0)
			if content then IPFSRevision = content:match("(%C+)") break end
			print(string.format("refreshZoomAvailability(revision.txt) Failed with %s", tostring(task)))
			local restart = os.time() + 5
			while os.time() < restart do
				coroutine.yield()
			end
			print(string.format("refreshZoomAvailability(revision.txt) Retrying..."))
		end
		local destroyToast = nil
		for z=0, 20 do
			print(string.format("checkTile:Refreshing zoom %d", z))
			if destroyToast then toast.destroy(destroyToast, true) end
			destroyToast = toast.new(string.format("Refreshing zoom %d", z))
			refreshZoom(MBTiles, z)
			probeContentCount = z
			coroutine.yield()
		end
		if destroyToast then toast.destroy(destroyToast, true) end

		if IPFSHasGateway and IPFSHasGateway.gotZoom then
			for z=0, 20 do
				print(string.format("IPFSHasGateway[%d]=%s", z, tostring(IPFSHasGateway.gotZoom[z])))
			end
		end

--[[
25	ZOOM_LEVEL_AGES = [
26	        86400 * 28 * 6, # Zoom 0        6 Months
27	        86400 * 28 * 6, # Zoom 1        6 Months
28	        86400 * 28 * 5, # Zoom 2        5 Months
29	        86400 * 28 * 4, # Zoom 3        4 Months
30	        86400 * 28 * 3, # Zoom 4        3 Months
31	        86400 * 28 * 2, # Zoom 5        2 Months
32	        86400 * 28,     # Zoom 6        1 Month
33	        86400 * 14,     # Zoom 7        2 Weeks
34	        86400 * 7,      # Zoom 8        1 Week
35	        86400 * 3,      # Zoom 9        3 Days
36	        86400 * 3,      # Zoom 10       3 Days
37	        86400,          # Zoom 11       1 Day
38	        7200,           # Zoom 12       2 Hours
39	        3600,           # Zoom 13       1 Hour
40	]
]]

		if false then	-- Only do the analysis if necessary
			local zBase, minZ, maxZ = 0, 0, 20
			local maxTime = math.min(45,MOAISim.getStep() * 1.9) -- / 4	-- Max loop time is 1/4 step (25%)
			local nextBreak = MOAISim.getDeviceTime() + maxTime
			local hasTiles = {}
			local nodeCount = 0
			local hasCount = 0
			
			local function getNode(x,y,z)
				local node = hasTiles
				if not node[z] then node[z] = {} end
				node = node[z]
				if not node[x] then node[x] = {} end
				node = node[x]
				if not node[y] then
					node[y] = {}
					--if z == 12 then print(string.format("checkTile:Added %d %d to %d", x, y, z)) end
					nodeCount = nodeCount + 1
				end
				node = node[y]
				return node
			end
			
			local function addChild(x,y,z,node)
				if z == 0 then return nil end
				local x2, y2, z1 = math.floor(x/2), math.floor(y/2), z-1
				local x8, y8 = math.floor(x2/8)*8, math.floor(y2/8)*8
				local xo, yo = (x2==x8) and 0 or 1, (y2==y8) and 0 or 1
				local cn = xo*2+yo
				local parent = getNode(x8,y8,z1)
				if not parent[cn] then
					parent[cn] = node
					addChild(x8,y8,z1,parent)
				elseif parent[cn] ~= node then
					print(string.format("checkTile:parent[%d] is %s NOT %s", cn, tostring(parent[cn]), tostring(node)))
				end
				return parent
			end

			local destroyToast = toast.new(string.format("Accumulating %d Tiles", MBTiles.IPFShasCount))
			local nextToast = 0
			for k, v in pairs(MBTiles.IPFShas) do
				local x, y, z = tilemgr:tileFromMetaID(k)

				local node = getNode(x,y,z)
				if not node.modified then
					--print(string.format("checkTile:%s is %d %d %d", k, x, y, z))
					node.modified = v
					node.parent = addChild(x,y,z,node)
					hasCount = hasCount + 1
				else print(string.format("checkTile:%s ALREADY %d %d %d at %d vs ", k, x, y, z, node.modified, v))
				end

				if MOAISim.getDeviceTime() > nextBreak then
					if MOAISim.getDeviceTime() > nextToast then
						if destroyToast then toast.destroy(destroyToast,true) end
						print(string.format("checkTile:Accumulating %d/%d across %d nodes", hasCount, MBTiles.IPFShasCount, nodeCount))
						destroyToast = toast.new(string.format("Accumulating %d/%d across %d nodes", hasCount, MBTiles.IPFShasCount, nodeCount))
						nextToast = MOAISim.getDeviceTime() + 2
					end
					coroutine.yield()
					nextBreak = MOAISim.getDeviceTime() + maxTime
				end
			end
			print(string.format("checkTile:Accumulated %d/%d tiles across %d nodes", hasCount, MBTiles.IPFShasCount, nodeCount))
			if destroyToast then toast.destroy(destroyToast,true) end
			destroyToast = toast.new(string.format("Accumulated %d/%d tiles across %d nodes", hasCount, MBTiles.IPFShasCount, nodeCount))
		
			local nextToast = 0
			local hasFile = io.open ("HaveTiles.txt", "w")
			local function checkTile(x,y,z,node)
				if node and node.modified then
					--print(string.format("checkTile:Has %d %d %d modified %d", x, y, z, node.modified))
					if z>= minZ and z <= maxZ then hasFile:write(string.format("%d %d %d\n", x, y, z)) end
				end
				if MOAISim.getDeviceTime() > nextBreak then
					coroutine.yield()
					nextBreak = MOAISim.getDeviceTime() + maxTime
				end
			end
			local function recurseCheck(x,y,z,node)
				if z < 20 then
					local x2, y2, z1 = x*2, y*2, z+1
					if node[0] then recurseCheck(x2, y2, z1, node[0]) end
					if node[2] then recurseCheck(x2+8, y2, z1, node[2]) end
					if node[3] then recurseCheck(x2+8, y2+8, z1, node[3]) end
					if node[1] then recurseCheck(x2, y2+8, z1, node[1]) end
				end
				if MOAISim.getDeviceTime() > nextToast then
					if destroyToast then toast.destroy(destroyToast,true) end
					print(string.format("checkTile:Checking %d %d in zoom %d", x, y, z))
					destroyToast = toast.new(string.format("Checking %d %d in zoom %d", x, y, z))
					nextToast = MOAISim.getDeviceTime() + 1
				end
				checkTile(x,y,z,node)
			end
			
    local function pairsByKeys (t, f)
      local a = {}
      for n in pairs(t) do table.insert(a, n) end
      table.sort(a, f)
      local i = 0      -- iterator variable
      local iter = function ()   -- iterator function
        i = i + 1
        if a[i] == nil then return nil
        else return a[i], t[a[i]]
        end
      end
      return iter
    end			

			if hasTiles[zBase] then
				--print(printableTable("hasTiles[12]", hasTiles[zBase]))
				for x, tx in pairsByKeys(hasTiles[zBase]) do
					for y, node in pairsByKeys(tx) do
						recurseCheck(x,y,zBase,node)
					end
				end
				if destroyToast then toast.destroy(destroyToast,true) end
				destroyToast = toast.new("Done emitting HaveTiles.txt")
			else
				if destroyToast then toast.destroy(destroyToast,true) end
				toast.new(string.format("No Tiles In Zoom %d", zBase))
			end
			print("checkTile:Done emitting HaveTiles.txt")
			hasFile:close()
		end
	end
--[[
	for k,v in pairs(MBTiles.IPFShas) do
		print(string.format("MBTiles.IPFShas[%s]=%s", tostring(k), tostring(v)))
	end
]]
end

local function isValidIndex(URL, content)
--         <div class="ipfs-hash">
--          QmUo39WPW1xahxTFkA2HPmKrxE8vcoGYubG8g8AzEPETPw
--        </div>
	-- Magic characters require quoting: ^$()%.[]*+-?
	local CID = content:match('<div class="ipfs%-hash"(.-)</div>')
	if CID then
		CID = (CID:gsub("^[%c%s]*(.-)[%c%s]*$", "%1"))
		print("isValidIndex:URL:"..URL.." gives CID="..tostring(CID))
	else
		local first = URL:match("^(.+):")
		local second = URL:match("^(.+)://")
		local third = URL:match("^.+://(.-)/")
		local what = URL:match("^.+://.-(/.+)$")
		print(string.format("isValidIndex:Got %s %s %s %s from %s", tostring(first), tostring(second), tostring(third), tostring(what), tostring(URL)))
		print(string.format("isValidIndex:Extracted %s from %s", tostring(what), tostring(URL)))
		local index = content:match("Index of "..what)
		if index then
			print(string.format("isValidIndex:Found %s from %s", what, URL))
		else
			print(string.format("isValidIndex:ipfs-hash not found (nor %s) from %s", what, URL))
			print(content)
			return false
		end
	end
	return true
end

local function OLDprimeIPFSGateway(gateway, MBTiles)	-- A free-running coroutine

	local function delay(ms)
		if ms > 0 then
			local timer = MOAITimer.new()
			timer:setSpan(ms/1000)
			MOAICoroutine.blockOnAction(timer:start())
		end
	end

	if not gateway.gotZoom then gateway.gotZoom = {} end
	if not gateway.gotZoom["priming"] then gateway.gotZoom["priming"] = 0 end
	local startTotal = MOAISim.getDeviceTime()
	local start = MOAISim.getDeviceTime()
	local content, task, ipfsURL = getFromIPFSGateway(gateway, MBTiles, "", "ipns root")	-- Start with just the root
	if content then
		local elapsed = (MOAISim.getDeviceTime() - start) * 1000
		if isValidIndex(ipfsURL, content) then
			updateGatewayAverage(gateway, elapsed)
			if not gateway.gotZoom then gateway.gotZoom = {} end
			if not gateway.gotZoom["root"] then gateway.gotZoom["root"] = 0 end
			updateIPFS(string.format("%s   root+ %dms", gateway.URI, elapsed))
		else
			if gateway.good then gateway.good = gateway.good - 1 end
			if not gateway.bad["INDEX"] then gateway.bad["INDEX"] = 0 end
			gateway.bad["INDEX"] = gateway.bad["INDEX"] + 1
			print("Invalid index received from "..ipfsURL)
			updateIPFS(string.format("%s   INDEX+ %dms", gateway.URI, elapsed))
		end
	else
		if tonumber(task) and tonumber(task) == 0 then
			local elapsed = (MOAISim.getDeviceTime() - start) * 1000
			updateGatewayAverage(gateway, elapsed)
		end
		print("primeIPFSGateway:Root failed from "..tostring(gateway.URI).." with "..tostring(task))
	end
	delay(500-(MOAISim.getDeviceTime()-start)*1000)
	for z = 0, 20 do
		local start = MOAISim.getDeviceTime()
		local content, task, ipfsURL = getFromIPFSGateway(gateway, MBTiles, tostring(z), "Zoom check")
		local elapsed = (MOAISim.getDeviceTime() - start) * 1000
		if content then
			if isValidIndex(ipfsURL, content) then
				updateGatewayAverage(gateway, elapsed)
				if not gateway.gotZoom then gateway.gotZoom = {} end
				if not gateway.gotZoom[z] then gateway.gotZoom[z] = 0 end
				updateIPFS(string.format("%s   %s+ %dms", gateway.URI, tostring(z), elapsed))
			else
				if gateway.good then gateway.good = gateway.good - 1 end
				if not gateway.bad["INDEX"] then gateway.bad["INDEX"] = 0 end
				gateway.bad["INDEX"] = gateway.bad["INDEX"] + 1
				print("Invalid index received from "..ipfsURL)
				updateIPFS(string.format("%s   INDEX+ %dms", gateway.URI, elapsed))
			end
		else
			if tonumber(task) and tonumber(task) == 0 then
				updateGatewayAverage(gateway, elapsed)
			end
			print("primeIPFSGateway:Zoom "..tostring(z).." failed from "..tostring(gateway.URI).." with "..tostring(task))
		end
		delay(500-(MOAISim.getDeviceTime()-start)*1000)
	end
	gateway.gotZoom["priming"] = nil
	local c = 0
	for k,v in pairs(gateway.gotZoom) do
		c = c + 1
	end
	if c == 0 then gateway.gotZoom = nil end
	updateIPFS(formatGatewayStats(gateway).."   Primed!")	-- Final stats
	primeGatewayCount = primeGatewayCount + 1
	local has = ""
	if gateway.gotZoom then
		for k,v in pairs(gateway.gotZoom) do
			if has ~="" then has = has.." " end
			has = has..tostring(k)
			if v > 1 then
				has = has..":"..tostring(v)
			end
		end
	end
	print(string.format("primeIPFSGateway:Completed in %dms %s has %s",
							(MOAISim.getDeviceTime() - startTotal)*1000,
							tostring(gateway.URI), has))
end

local function resolveAndReplaceIpnsRoot(gateway, MBTiles)
	if MBTiles.IPFSBase:sub(1,5) == "ipns/" then
		local URI = gateway.URI
		local name = MBTiles.IPFSBase:sub(6)
--{"Path":"/ipfs/QmUn2A8jUe4YJZbkYdJvRa2mpzUYVsiq22p8vA7jy8ta61"}
		local ipnsURL = URI.."api/v0/name/resolve?arg="..name
		updateIPFS("Resolve:"..URI.." "..name)
		local start = MOAISim.getDeviceTime()
		local content, task = getURLContent(ipnsURL, "IPNS Resolve")
		local elapsed = (MOAISim.getDeviceTime() - start) * 1000
		if not content then print ( "resolveAndReplaceIpnsRoot:Network status:"..tostring(task)..' from '..tostring(ipnsURL)) end
		if content then
			local json = require("json")
			local success, values = pcall(json.decode, json, content)
			if not success then
				--print('resolveAndReplaceIpnsRoot:json.decode('..tostring(values)..') on:'..content)
				local rp = "API"
				if not gateway.bad then gateway.bad = {} end
				if not gateway.bad[rp] then gateway.bad[rp] = 0 end
				gateway.bad[rp] = gateway.bad[rp] + 1
				updateIPFS(string.format("%s   %s %dms", URI, rp, elapsed))
			elseif type(values) == 'table' then
				print(printableTable('resolveAndReplaceIpnsRoot:json', values, "\n"))
				if values.Path and values.Path:sub(1,1) == "/" then values.Path = values.Path:sub(2) end
				if values.Path and values.Path:sub(1,5) == "ipfs/" then
					MBTiles.IPFSBaseOriginal = MBTiles.IPFSBase
					MBTiles.IPFSBase = values.Path
					print(string.format("resolveAndReplaceIpnsRoot:Resolved(%s) to (%s)", MBTiles.IPFSBaseOriginal, MBTiles.IPFSBase))
					if not gateway.good then gateway.good = 0 end
					gateway.good = gateway.good + 1
					updateIPFS(string.format("%s   IPNS+ %dms", URI, elapsed))
				else
					local rp = "IPNS"
					if not gateway.bad then gateway.bad = {} end
					if not gateway.bad[rp] then gateway.bad[rp] = 0 end
					gateway.bad[rp] = gateway.bad[rp] + 1
					updateIPFS(string.format("%s   %s %dms", URI, rp, elapsed))
				end
			end
		elseif tonumber(task) and tonumber(task) == 0 then
			if not gateway.timeout then gateway.timeout = 0 end
			gateway.timeout = gateway.timeout + 1
			updateIPFS(string.format("%s   TO+ %dms", URI, elapsed))
		else
			local rp = tostring(task)
			if not gateway.bad then gateway.bad = {} end
			if not gateway.bad[rp] then gateway.bad[rp] = 0 end
			gateway.bad[rp] = gateway.bad[rp] + 1
			updateIPFS(string.format("%s   %s %dms", URI, rp, elapsed))
		end
	end
end

local function checkAPI(gateway, MBTiles)
--http://ldeffenb.dnsalias.net:5000/api/v0/object/stat?arg=QmUn2A8jUe4YJZbkYdJvRa2mpzUYVsiq22p8vA7jy8ta61
--{"Hash":"QmUn2A8jUe4YJZbkYdJvRa2mpzUYVsiq22p8vA7jy8ta61","NumLinks":45,"BlockSize":2180,"LinksSize":2178,"DataSize":2,"CumulativeSize":16566907820}

	if MBTiles.IPFSBase:sub(1,5) == "ipfs/" then
		local URI = gateway.URI
		local CID = MBTiles.IPFSBase:sub(6)
		local URL = URI.."api/v0/object/stat?arg="..CID
		updateIPFS("APIstat:"..URI.." "..CID)
		local start = MOAISim.getDeviceTime()
		local content, task = getURLContent(URL, "API stat")
		local elapsed = (MOAISim.getDeviceTime() - start) * 1000
		if not content then print ( "checkAPI:Network status:"..tostring(task)..' from '..tostring(URL)) end
		if content then
			local json = require("json")
			local success, values = pcall(json.decode, json, content)
			if not success then
				--print('checkAPI:json.decode('..tostring(values)..') on:'..content)
				local rp = "API"
				if not gateway.bad then gateway.bad = {} end
				if not gateway.bad[rp] then gateway.bad[rp] = 0 end
				gateway.bad[rp] = gateway.bad[rp] + 1
				updateIPFS(string.format("%s   %s %dms", URI, rp, elapsed))
			elseif type(values) == 'table' then
				print(printableTable('checkAPI:json', values, "\n"))
				if values.Hash and values.Hash == CID then
					print(string.format("checkAPI:Object(%s) CumulativeSize:%s", CID, tostring(values.CumulativeSize)))
					if not gateway.good then gateway.good = 0 end
					gateway.good = gateway.good + 1
					if not gateway.gotZoom then gateway.gotZoom = {} end
					if not gateway.gotZoom["api"] then gateway.gotZoom["api"] = 0 end
					updateIPFS(string.format("%s   API+ %dms", URI, elapsed))
				else
					local rp = "API"
					if not gateway.bad then gateway.bad = {} end
					if not gateway.bad[rp] then gateway.bad[rp] = 0 end
					gateway.bad[rp] = gateway.bad[rp] + 1
					updateIPFS(string.format("%s   %s %dms", URI, rp, elapsed))
				end
			end
		elseif tonumber(task) and tonumber(task) == 0 then
			if not gateway.timeout then gateway.timeout = 0 end
			gateway.timeout = gateway.timeout + 1
			updateIPFS(string.format("%s   TO+ %dms", URI, elapsed))
		else
			local rp = tostring(task)
			if not gateway.bad then gateway.bad = {} end
			if not gateway.bad[rp] then gateway.bad[rp] = 0 end
			gateway.bad[rp] = gateway.bad[rp] + 1
			updateIPFS(string.format("%s   %s %dms", URI, rp, elapsed))
		end
	end
end

local function invokeAPI(gateway, MBTiles, api)
	local URI = gateway.URI
	local URL = URI..api
	local start = MOAISim.getDeviceTime()
	local content, task = getURLContent(URL, "API stat")
	local elapsed = (MOAISim.getDeviceTime() - start) * 1000
	if not content then print ( "invokeAPI:Network status:"..tostring(task)..' from '..tostring(URL)) end
	if content then
		local json = require("json")
		local success, values = pcall(json.decode, json, content)
		if not success then
			print('invokeAPI:json.decode('..tostring(values)..') on:'..content)
		elseif type(values) == 'table' then
			--print("invokeAPI:"..printableTable(api, values, "\n"))
			return values
		end
	end
end


local function primeIPFSGatewayStep(gateway, MBTiles)	-- Returns as each step is completed

	local function delay(ms)
		if ms > 0 then
			local timer = MOAITimer.new()
			timer:setSpan(ms/1000)
			MOAICoroutine.blockOnAction(timer:start())
		end
	end

	if not gateway.gotZoom then gateway.gotZoom = {} end
	
print("Priming "..tostring(gateway.URI).." response "..tostring(gateway.avgRecent))
	
	if gateway.primeFirst or not gateway.gotZoom or not gateway.gotZoom["priming"] then
		gateway.primeFirst = nil
		if not gateway.gotZoom then gateway.gotZoom = {} end
		if not gateway.gotZoom["priming"] then gateway.gotZoom["priming"] = 0 end
		
print("Priming "..tostring(gateway.URI).." API")
		checkAPI(gateway, MBTiles)

print("Priming "..tostring(gateway.URI).." root")
		local start = MOAISim.getDeviceTime()
		local content, task, ipfsURL = getFromIPFSGateway(gateway, MBTiles, "", "root")	-- Start with just the root
		local elapsed = (MOAISim.getDeviceTime() - start) * 1000
		local avg = updateGatewayAverage(gateway, elapsed)
		if content then
			if isValidIndex(ipfsURL, content) then
				if not gateway.gotZoom then gateway.gotZoom = {} end
				if not gateway.gotZoom["root"] then gateway.gotZoom["root"] = 0 end
				updateIPFS(string.format("%s   root+ %dms %s", gateway.URI, elapsed, avg))
			else
				if gateway.good then gateway.good = gateway.good - 1 end
				if not gateway.bad["INDEX"] then gateway.bad["INDEX"] = 0 end
				gateway.bad["INDEX"] = gateway.bad["INDEX"] + 1
				print("Invalid index received from "..ipfsURL)
				updateIPFS(string.format("%s   INDEX+ %dms %s", gateway.URI, elapsed, avg))
			end
		else
			if tonumber(task) and tonumber(task) == 0 then	-- Timeout vs other failure

			end
			print("primeIPFSGateway:Root failed from "..tostring(gateway.URI).." with "..tostring(task))
		end
		return false	-- Not done yet, call me again
	else
		local z = gateway.gotZoom["priming"] or 0	-- Next zoom level to do
print("Priming "..tostring(gateway.URI).." Zoom:"..tostring(z))
		local start = MOAISim.getDeviceTime()
		local content, task, ipfsURL = getFromIPFSGateway(gateway, MBTiles, tostring(z), "Zoom check")
		local elapsed = (MOAISim.getDeviceTime() - start) * 1000
		local avg = updateGatewayAverage(gateway, elapsed)
		if content then
			if isValidIndex(ipfsURL, content) then
				if not gateway.gotZoom then gateway.gotZoom = {} end
				if not gateway.gotZoom[z] then gateway.gotZoom[z] = 0 end
				updateIPFS(string.format("%s   %s+ %dms %s", gateway.URI, tostring(z), elapsed, avg))
			else
				if gateway.good then gateway.good = gateway.good - 1 end
				if not gateway.bad["INDEX"] then gateway.bad["INDEX"] = 0 end
				gateway.bad["INDEX"] = gateway.bad["INDEX"] + 1
				print("Invalid index received from "..ipfsURL)
				updateIPFS(string.format("%s   INDEX+ %dms %s", gateway.URI, elapsed, avg))
			end
		else
			if tonumber(task) and tonumber(task) == 0 then	-- Timeout vs other failure

			end
			print("primeIPFSGateway:Zoom "..tostring(z).." failed from "..tostring(gateway.URI).." with "..tostring(task))
		end
		
		z = z + 1	-- Next zoom
		if z <= 20 then
			gateway.gotZoom["priming"] = z	-- remember it for next pass
			return false	-- Not done yet, call me again
		end

		gateway.gotZoom["priming"] = nil	-- Done priming this one!
		local c = 0
		for k,v in pairs(gateway.gotZoom) do
			c = c + 1
		end
		if c == 0 then gateway.gotZoom = nil end
		updateIPFS(formatGatewayStats(gateway).."   Primed!")	-- Final stats
		local has = ""
		if gateway.gotZoom then
			for k,v in pairs(gateway.gotZoom) do
				if has ~="" then has = has.." " end
				has = has..tostring(k)
				if v > 1 then
					has = has..":"..tostring(v)
				end
			end
		end
		print(string.format("primeIPFSGateway:Completed priming %s which has %s",
								tostring(gateway.URI), has))
		if has == "" then
			MBTiles:dropGateway(gateway.URI)
		elseif not IPFSHomeGateway or IPFSHomeGateway.URI ~= gateway.URI then
			MBTiles:saveGateway(gateway.URI, gateway.gotZoom["api"], gateway.avgRecent, gateway.good or 0)
			gateway.dirty = nil
		end
		return true
	end
	print("Huh?  Not supposed to get here!")
	return true		-- So tell him we're done (but confused)
end

local function primeIPFSGatewaysThread(MBTiles)
	local startTotal = MOAISim.getDeviceTime()
	local choices = {}
	for i, g in ipairs(IPFSGateways) do
		g.totalTimed = 0
		g.totalElapsed = 0
		if not g.avgTimed then
			g.avgTimed = math.random(5000,6000)
		end
		if not g.avgRecent then	-- Preserve recalled avgRecent
			g.avgRecent = g.avgTimed
		end
		g.primeFirst = true
		if not g.gotZoom then g.gotZoom = {} end
		g.gotZoom["priming"] = 0	-- So display sort works better (only on time)
		choices[#choices+1] = g
	end
	local choiceCount = #choices

	print(string.format("Priming %d gateways", choiceCount))
	while #choices > 0 do
		table.sort(choices, fastestGatewaySort)
		local choice = math.random(#choices)
		choice = 1	-- Always prime the fastest first
		local gateway = choices[choice]
		if primeIPFSGatewayStep(gateway, MBTiles) then
			primeGatewayCount = primeGatewayCount + 1
			table.remove(choices, choice)
		end
	end
	print(string.format("Priming all %d gateways took %d seconds!",
						choiceCount, (MOAISim.getDeviceTime()-startTotal)))
end

local function OLDprimeIPFSGatewaysThread(MBTiles)
	local choices = {}
	for i, g in ipairs(IPFSGateways) do
		choices[#choices+1] = g
	end
	while #choices > 0 do
		local choice = math.random(#choices)
		local g = choices[choice]
		--MOAICoroutine.new ():run ( function() primeIPFSGateway(g, MBTiles) end )
		primeIPFSGateway(g, MBTiles)
		table.remove(choices,choice)
	end
end

local function setupSpecialGatewaysThread(MBTiles)
	IPFSPriorityGateway = { URI = "Priority", good=0, timeout=0, bad={} }
	IPFSGatewayGateway = { URI = "Total Gateways", good=0, timeout=0, bad={} }
	IPFSHasNotGateway = { URI = "IPFS Has Not", good=0, timeout=0, bad={} }
	IPFSHasGateway = { URI = "IPFS Has", good=0, timeout=0, bad={} }

	if MBTiles.IPFSHomeGateway then
		if MBTiles.IPFSHomeGateway:sub(-1) ~= "/" then
			MBTiles.IPFSHomeGateway = MBTiles.IPFSHomeGateway.."/"
		end
		local URI = MBTiles.IPFSHomeGateway
		IPFSHomeGateway = { URI = URI, good=0, timeout=0, bad={} }

		print("Priming IPFSHomeGateway from "..URI)

		if MBTiles.IPFSBase:sub(1,5) == "ipns/" then
print("Priming "..tostring(IPFSHomeGateway.URI).." IPNS")
			resolveAndReplaceIpnsRoot(IPFSHomeGateway, MBTiles)
		end

		while not primeIPFSGatewayStep(IPFSHomeGateway, MBTiles) do
			coroutine.yield()
		end
	else print("No IPFSHomeGateway in MBTiles:"..tostring(config.Map.MBTiles))
	end
	
	if true and isDesktop then	-- Only set this up to avoid hitting the IPFS network
		local URI = "http://192.168.10.13:5000/"	-- Should come from config
		IPFSLocalGateway = { URI = URI, good=0, timeout=0, bad={} }
		while not primeIPFSGatewayStep(IPFSLocalGateway, MBTiles) do
			coroutine.yield()
		end
	end
	
	refreshZoomAvailability(MBTiles)	-- This should wait for another gateway or three
end

function saveIPFSGateways(MBTiles)
	if MBTiles and MBTiles.IPFSBase and MBTiles.IPFSGateways and IPFSGateways and #IPFSGateways > 0 then
		local saveCount = 0
		for i, g in ipairs(IPFSGateways) do
			if g.dirty and g.gotZoom and g.good and g.good > 0 then
				MBTiles:saveGateway(g.URI, g.gotZoom["api"], g.avgRecent, g.good)
				saveCount = saveCount + 1
				g.dirty = nil
			end
		end
		if saveCount > 0 then print("saveIPFSGateways:Saved "..tostring(saveCount).." dirty gateways") end
	elseif not MBTiles then
		print(string.format("saveIPFSGateways:MBTiles is %s", tostring(MBTiles)))
	else
		print(string.format("saveIPFSGateways:MBTiles:%s IPFSBase:%s IPFSGateways:%s IPFSGateways:%s",
				tostring(MBTiles), tostring(MBTiles.IPFSBase),
				tostring(MBTiles.IPFSGateways), tostring(IPFSGateways)))
	end
end

local function refreshIPFSGateways(MBTiles)
	if MBTiles.IPFSBase and MBTiles.IPFSGateways and (not IPFSGateways or #IPFSGateways <= 0) then
	
		runServiceCoroutine(setupSpecialGatewaysThread, MBTiles)
	
		if not IPFSGateways then IPFSGateways = {} end
		
		local gwys = MBTiles:recallGateways()
		if gwys then
			for u, g in pairs(gwys) do
				if not IPFSGateways[g.URI] then
					IPFSGateways[#IPFSGateways+1] = { URI=g.URI, good=0, timeout=0, bad={},
													avgRecent=g.response, avgTimed=g.response }
					IPFSGateways[g.URI] = #IPFSGateways
					print(printableTable("Recall:"..g.URI,IPFSGateways[#IPFSGateways]))
				else print("Huh?  Redefined Recalled gateway:"..tostring(g.URI))
				end
			end
		end

		updateIPFS("Gateways:"..MBTiles.IPFSGateways)
		local content, err = getURLContent(MBTiles.IPFSGateways, "Gateways")
		if not content then
			print ( "refreshIPFSGateways:Network error:"..tostring(err).." from "..MBTiles.IPFSGateways)
			--IPFSGateways = nil
		else
			local json = require("json")
			local success, values = pcall(json.decode, json, content)
			if not success then
				print('refreshIPFSGateways:json.decode('..tostring(values)..') on:'..content)
			elseif type(values) == 'table' then
				--print(printableTable('refreshIPFSGateways:json', values, "\n"))
				--if not IPFSGateways or #IPFSGateways <= 0 then
					for i, v in ipairs(values) do
						if v:sub(-10) == "ipfs/:hash" then
							if not IPFSGateways then IPFSGateways = {} end
							local URI = v:sub(1,-11)
							if not IPFSGateways[URI] then
								local gateway = { URI = URI, good=0, timeout=0, bad={} }
								IPFSGateways[#IPFSGateways+1] = gateway
								IPFSGateways[URI] = #IPFSGateways
							end
							local gwy = MBTiles:getGateway(URI)
							if gwy then
								local gateway = IPFSGateways[IPFSGateways[URI]]
								print(string.format("gwy[%s]=%s(%s)", tostring(URI), type(gwy), tostring(gwy)))
								print(printableTable(URI, gwy))
								gateway.avgRecent = gwy.response
								gateway.avgTimed = gwy.response
								print(printableTable(URI, gateway))
							end
						else
							print("Can't use non-ipfs/:hash gateway:"..tostring(v))
						end
					end
					if IPFSGateways and #IPFSGateways > 0 then
						runServiceCoroutine(primeIPFSGatewaysThread, MBTiles)
					end
				--else print("Avoided doubling IPFSGateways!")
				--end
			else
				print(string.format("refreshIPFSGateways:Gateways:%s(%s)", type(values), tostring(values)))
				IPFSGateways = nil
			end
		end
	end
end

primeMBTiles = function(MBTiles)	-- was locally declared earlier
	if MBTiles and MBTiles.IPFSBase then
		if not MBTiles.IPFSPrimed then
			print("Priming IPFS MBTiles IPFSHomeGateway="..tostring(MBTiles.IPFSHomeGateway))
			MBTiles.IPFSPrimed = true
			MOAICoroutine.new ():run ( function() refreshIPFSGateways(MBTiles) end )
		end
	end
	local x, y, z = 0, 0, 0	-- highest level tile gets checked and loaded every time
	local haveIt, LastDate = MBTiles:checkTile(0, x, y, z)
	if not haveIt then
		queueTile(pendingPrefetch, x, y, z, MBTiles)
	elseif LastDate then
		queueTile(pendingExpired, x, y, z, MBTiles, nil, LastDate)
	end
end

local function tryGateway(gateway, MBTiles, metaID, why, z, failures)
	local URI = gateway.URI
	local ipfsURL = URI..MBTiles.IPFSBase.."/"..metaID
	--updateIPFS("Get:"..ipfsURL)	-- getFromIPFSGateway logs this
	local start = MOAISim.getDeviceTime()
	local content, task = getFromIPFSGateway(gateway, MBTiles, metaID, why)
	if not content then print ( "tryGateway:Network status:"..tostring(task)..' from '..tostring(ipfsURL)) end
	if content then
		local magic = struct.unpack('<c4', content)
		if magic ~= "META" then
			if gateway.good then gateway.good = gateway.good - 1 end	-- Not really a good retrieve!
			if not gateway.bad then gateway.bad = {} end
			if not gateway.bad["META"] then gateway.bad["META"] = 0 end
			gateway.bad["META"] = gateway.bad["META"] + 1
			print("META Read "..tostring(readBytes).."/"..tostring(streamSize).." of:"..content)
			if not failures["META"] then failures["META"] = 0 end
			failures["META"] = failures["META"] + 1
			updateIPFS(gateway.URI.."   META+1")
		else
			local elapsed = (MOAISim.getDeviceTime() - start) * 1000
			updateGatewayAverage(gateway, elapsed)
			if not gateway.gotZoom then gateway.gotZoom = {} end
			if not gateway.gotZoom[z] then gateway.gotZoom[z] = 0 end
			gateway.gotZoom[z] = gateway.gotZoom[z] + 1
			if gateway ~= IPFSLocalGateway then
				if not IPFSGatewayGateway.gotZoom then IPFSGatewayGateway.gotZoom = {} end
				if not IPFSGatewayGateway.gotZoom[z] then IPFSGatewayGateway.gotZoom[z] = 0 end
				IPFSGatewayGateway.gotZoom[z] = IPFSGatewayGateway.gotZoom[z] + 1
			end
			return content, task, ipfsURL
		end
	elseif tonumber(task) and tonumber(task) == 0 then
		local elapsed = (MOAISim.getDeviceTime() - start) * 1000
		updateGatewayAverage(gateway, elapsed>15000 and elapsed or 15000)	-- "timeouts" cost 15sec or actual time
		if not failures["to"] then failures["to"] = 0 end
		failures["to"] = failures["to"] + 1
	else
		local elapsed = (MOAISim.getDeviceTime() - start) * 1000
		updateGatewayAverage(gateway, elapsed>15000 and elapsed or 15000)	-- errors cost 15sec or actual time
		local rp = tostring(task)
		if not failures[rp] then failures[rp] = 0 end
		failures[rp] = failures[rp] + 1
	end
	return nil, task
end

local function getFromIPFS(MBTiles, metaID, why, z)
	if MBTiles.IPFSBase and IPFSGateways and #IPFSGateways > 0 then
		if MBTiles.IPFShas and not MBTiles.IPFShas[metaID] then
			if not IPFSHasNotGateway.gotZoom then IPFSHasNotGateway.gotZoom = {} end
			if not IPFSHasNotGateway.gotZoom[z] then IPFSHasNotGateway.gotZoom[z] = 0 end
			IPFSHasNotGateway.gotZoom[z] = IPFSHasNotGateway.gotZoom[z] + 1
			IPFSHasNot = IPFSHasNot + 1
			return nil, string.format("%s Not Available via IPFS", metaID)
		end
		
		local failures = {}

		if true and IPFSLocalGateway then	-- Always prefer to hit local for speed
			local gateway = IPFSLocalGateway
			local URI = gateway.URI
			local ipfsURL = URI..MBTiles.IPFSBase.."/"..metaID
			print(string.format("getFromIPFS holding %d from LOCAL %s", metaTilesPending[metaID][0], ipfsURL))
			local content, task, actualURL = tryGateway(IPFSLocalGateway, MBTiles, metaID, why, z, failures)
			if content then
				IPFSLocalHits = IPFSLocalHits + 1
				return content, task, actualURL
			end
		end
		
		local choices = {}
		for i, g in ipairs(IPFSGateways) do
			if g.gotZoom and g.gotZoom[z] then
				choices[#choices+1] = g
			end
		end
		if #choices == 0 then
			return nil, string.format("Zoom %d Not Available via IPFS", z)
		end
		local choiceCount = #choices
--		local choices = { unpack(IPFSGateways) }

		table.sort(choices, fastestGatewaySort)
--[[
		for k,g in pairs(choices) do
			print(string.format("choice[%d]=%s", k, formatGatewayStats(g)))
		end
]]

		while #choices > 0 do
			local choice
			--choice = math.random(math.min(#choices,math.max(1,math.floor(#choices/3))))	-- This uses fastest 1/3
			local power = 4	-- 4 is a nice steep curve, 2 puts more to the slower ones, 10 (or higher) really focusses on fastest
			local r = math.random()	-- From 0 up to, but NOT including 1
			choice = math.floor((r ^ power) * #choices) + 1
			if why == "Priority" then choice = 1 end	-- Priority always uses the fastest
			if choice < 1 or choice > #choices then
				local text = string.format("getFromIPFS OOR %d/%d from %f", choice, #choices, r)
				print(text)
				toast.new(text)
				choice = 1
			end
			if not usedChoices then usedChoices = {} end
			if not usedChoices[choice] then usedChoices[choice] = 0 end
			usedChoices[choice] = usedChoices[choice] + 1
			local gateway = IPFSGateways[IPFSGateways[choices[choice].URI]]
			local URI = gateway.URI
			local ipfsURL = URI..MBTiles.IPFSBase.."/"..metaID
			print(string.format("getFromIPFS choice %d/%d holding %d from %s", choice, #choices, metaTilesPending[metaID][0], ipfsURL))
			table.remove(choices, choice)
			local content, task, actualURL = tryGateway(gateway, MBTiles, metaID, why, z, failures)
			if content then
				IPFSGatewayHits = IPFSGatewayHits + 1
				if MBTiles.IPFSBase:sub(1,5) == "ipfs/" then
					local links = invokeAPI(IPFSHomeGateway, MBTiles, "api/v0/object/links?arg="..MBTiles.IPFSBase:sub(6).."/"..metaID)
					if links and type(links) == "table" and links.Hash then
						print(string.format("invokeAPI:Got CID %s from %s for %s",
											tostring(links.Hash), gateway.URI, metaID))
						if links.Links and type(links.Links) == "table" then
							for _, l in ipairs(links.Links) do
								print(string.format("invokeAPI:Body CID %s length %s from %s for %s",
													tostring(l.Hash), tostring(l.Size), gateway.URI, metaID))
							end
						end
					end
				else print("invokeAPI:IPFSBase not ipfs/ but "..tostring(MBTiles.IPFSBase))
				end
				return content, task, actualURL
			end
		end
		if IPFSLocalGateway then
			local gateway = IPFSLocalGateway
			local URI = gateway.URI
			local ipfsURL = URI..MBTiles.IPFSBase.."/"..metaID
			print(string.format("getFromIPFS holding %d from LOCAL %s", metaTilesPending[metaID][0], ipfsURL))
			local content, task, actualURL = tryGateway(IPFSLocalGateway, MBTiles, metaID, why, z, failures)
			if content then
				IPFSLocalHits = IPFSLocalHits + 1
				return content, task, actualURL
			end
		end
		
		IPFSFailures = IPFSFailures + 1
		local text = ""
		for k,v in pairs(failures) do
			if text ~= "" then text = text.." " end
			text = text..tostring(k)..":"..tostring(v)
		end
		print("getFromIPFS:IPFS completely failed("..text..") to get "..metaID)
		updateIPFS("IPFS Failed("..text.."):"..metaID)
		return nil, string.format("IPFS Failed %d Gateways", choiceCount)
	end
	return nil, "getFromIPFS Not Available "..tostring(MBTiles.IPFSBase).." "..tostring(IPFSGateways).." "..(type(IPFSGateways)=="table" and tostring(#IPFSGateways) or "")
end	

local function reallyLoadRemoteMetaTile(x, y, z, MBTiles, LastDate, why)

	local metaURL, idx, metaID = tilemgr:osmMetaTileURL(x, y, z, MBTiles)
	if metaURL == "" then
		return
	end
	
	local start = MOAISim.getDeviceTime()
	local content, task

	if MBTiles.IPFSBase then
		--refreshIPFSGateways(MBTiles)
		if IPFSGateways and #IPFSGateways > 0 then
			if why == "xPriority" then
				print(string.format("reallyLoadRemoteMetaTile:IPFS NOT Loading %s %s", why, metaID))
				if not IPFSPriorityGateway.gotZoom then IPFSPriorityGateway.gotZoom = {} end
				if not IPFSPriorityGateway.gotZoom[z] then IPFSPriorityGateway.gotZoom[z] = 0 end
				IPFSPriorityGateway.gotZoom[z] = IPFSPriorityGateway.gotZoom[z] + 1
				IPFSPrioritySkipped = IPFSPrioritySkipped + 1
			else
				local actualURL
				content, task, actualURL = getFromIPFS(MBTiles, metaID, why, z)
				if content then metaURL = actualURL IPFSLoaded = IPFSLoaded + 1
				else print(string.format("reallyLoadRemoteMetaTile:IPFS Failed %s %s because %s", why, metaID, tostring(task)))
				end
			end
		end
	end

	if not content then	-- Didn't get it from IPFS
		print(string.format("reallyLoadRemoteMetaTile metaTilesPending[%s] at %d from %s", metaID, metaTilesPending[metaID][0], metaURL))
		content, task = getURLContent(metaURL, why)
		if not content then print ( "reallyLoadRemoteMetaTile:Network error:"..tostring(task)..' from '..tostring(metaURL)) end
	end
	
--[[
		if task:getResponseCode() == 304 then	-- Not Modified, from If-Modified-Since
			print ( "reallyLoadRemoteMetaTile:NotModified:304 from '..tostring(metaURL))
			local LastModified = task:getResponseHeader("Last-Modified")
			local Expires = task:getResponseHeader("Expires")
			local Date = task:getResponseHeader("Date")
			print("reallyLoadRemoteMetaTile:304:"..metaURL.." Date:"..tostring(Date).." Expires:"..tostring(Expires).." Last-Modified:"..tostring(LastModified))
		end
]]
	if content then
		local Date, Expires = getDateExpires(task, metaURL)

		metaLoaded = metaLoaded + 1
		print(string.format("reallyLoadRemoteMetaTile:Received metaTilesPending[%s] at %d from %s", metaID, metaTilesPending[metaID][0], metaURL))
		local expectedMin = 4+4*4+64*(4+4)
		if #content < expectedMin then
			local text = string.format("%s got %d bytes, minimum %d", metaURL, #content, expectedMin)
			print(text)
			toast.new(text)
		else
			local magic, count, xFirst, yFirst, zoom = struct.unpack('<c4IIII', content)
			local sq = math.sqrt(count)
			print(string.format("magic:%s count:%d (%dx%d) x,y:%d,%d z:%d", magic, count, sq, sq, xFirst, yFirst, zoom))
			if magic ~= "META" then
				print(content)
				toast.new(string.format("%s META = %s", metaURL, meta))
			elseif count ~= 64 then
				local text = string.format("%s count %d ~= 64", metaURL, count)
				print(text)
				toast.new(text)
			else
				local buffer = MOAIDataBuffer.new()
				for i=0,count-1 do
					local offset, size = struct.unpack('<II', content:sub(20+i*8+1))
					if (size > 0) then
						if offset+size < 0 or offset+size > #content then
							local text = string.format("%s off %d size %d > %d content", metaURL, offset, size, #content)
							print(text)
							toast.new(text)
							break;
						end
						local xt, yt = xFirst+math.floor(i/sq), yFirst+(i%sq)
						buffer:setString(content:sub(offset+1,offset+1+size))
						local tryImage = MOAITexture.new()
						tryImage:load(buffer, "MetaTile "..tostring(z).."/"..tostring(xt).."/"..tostring(yt))
						local width, height = tryImage:getSize()
						--print(string.format("Tile@%d %d %d offset:%d size:%d wxh:%dx%d", i, xt, yt, offset, size, width, height))
						if width == 256 and height == 256 then
							--print("reallyLoadRemoteMetaTile:Saving "..tostring(size).." bytes from "..tostring(metaURL))
							MBTiles:saveTile(n,xt,yt,z,buffer,Date,Expires)
							clearDownloadedTile(osmTileKey(xt,yt,z,MBTiles))
						else
							print('reallyLoadRemoteMetaTile:Failed To Load '..xt..','..yt..' size:'..tostring(width)..'x'..tostring(height))
							tryImage = nil
						end
						local removes = {}
						for it, t in pairs(metaTilesPending[metaID]) do
							if type(t) == 'table' then
								if t.x == xt and t.y == yt and t.z == z then
									if debugging then print(string.format("reallyLoadRemoteMetaTile:Satisfied %i's %i/%i/%i callback %s key %s", t.n, t.z, t.x, t.y, tostring(t.callback), tostring(t.key))) end
									queuedFiles[t.key] = nil
									tilesLoaded = tilesLoaded + 1
									if t.callback then
										t.callback(Sprite { texture = tryImage, left=0, top=0 })
									end
									table.insert(removes,it)
								else extraTilesLoaded = extraTilesLoaded + 1
								end
							end
						end
						for _, it in pairs(removes) do
							metaTilesPending[metaID][it] = nil
							metaTilesPending[metaID][0] = metaTilesPending[metaID][0] - 1
							--print(string.format("reallyLoadRemoteMetaTile:Removed %s from metaTilesPending[%s] now %d", it, metaID, metaTilesPending[metaID][0]))
						end
						if debugging then
							if #removes == 0 then
								local key = osmTileKey(xt,yt,z,MBTiles)
								if queuedFiles[key] then
									print(string.format("reallyLoadRemoteMetaTile:Unused %i/%i/%i key:%s queuedFiles:%s", z, xt, yt, key, tostring(queuedFiles[key])))
								else print(string.format("reallyLoadRemoteMetaTile:Unused %i/%i/%i key:%s", z, xt, yt, key))
								end
							end
						end
					end
				end
			end
		end

		local function checkPrefetch(x2,y2,z2)
			if validTileNum(x2,y2,z2) then
				if not MBTiles:checkTile(0, x2,y2,z2) then
					--local file2, dir2 = osmTileKey(x2,y2,z2,MBTiles)
					--print("Prefetch "..file2.." or z="..tostring(z2).." x="..tostring(x2).." y="..tostring(y2))
					queueTile(pendingPrefetch, x2, y2, z2, MBTiles, function(sprite) print(string.format("Prefetched %d/%d/%d", z2, x2, y2, tostring(Expired))) end)
				end
			end
		end
		if z>0 then
			checkPrefetch(math.floor(x/2), math.floor(y/2), z-1)
		end
--[[
		if n >= 1 and n <= 9 and z<15 then		-- Prefetch below center 3x3 square
			checkPrefetch(x*2, y*2, z+1)
			checkPrefetch(x*2+1, y*2, z+1)
			checkPrefetch(x*2, y*2+1, z+1)
			checkPrefetch(x*2+1, y*2+1, z+1)
		end
]]
		
--[[
Offset (hex)	Size	Meaning
000	4	Magic string "META"
004	4	Number of tiles in this metatile (64)
008	4	X index of first metatile (0 .. 2zoom-1)
00C	4	Y index of first metatile (0 .. 2zoom-1)
010	4	Zoom level
014	64 * 2 * 4	Offsets (from start of file) and sizes of tile data for each tile in column-major order
214		Tile data in PNG format at offsets given in header]]
	end

	for it, t in pairs(metaTilesPending[metaID]) do
		if type(t) == 'table' then
			if debugging then print(string.format("reallyLoadRemoteMetaTile:Clearing %i's %i/%i/%i callback %s key %s", t.n, t.z, t.x, t.y, tostring(t.callback), tostring(t.key))) end
			queuedFiles[t.key] = nil
			if t.callback then
				print(string.format("reallyLoadRemoteMetaTile:Clearing %i's %i/%i/%i callback %s key %s", t.n, t.z, t.x, t.y, tostring(t.callback), tostring(t.key)))
				tilesFailed = tilesFailed + 1
				t.callback(nil)	-- Callback with a failure
			end
		end
	end
	print(string.format("reallyLoadRemoteMetaTile:NILLING metaTilesPending[%s] from %d", metaID, metaTilesPending[metaID][0]))
	metaTilesPending[metaID] = nil
	
	local elapsed = (MOAISim.getDeviceTime()-start)
	print(string.format("reallyLoadRemoteMetaTile:%s(%s) Took %.0fmsec", tostring(why), metaURL, elapsed*1000))

end

function osmReallyLoadRemoteTile(n, x, y, z, MBTiles, callback, LastDate, why)

	local key = osmTileKey(x, y, z, MBTiles)
	local URL = osmTileURL(x, y, z, MBTiles)

	local haveIt, newLastDate = MBTiles:checkTile(n, x, y, z)
	if haveIt and not newLastDate then
		print(string.format('osmReallyLoadRemoteTile[%i] already HAVE %i/%i/%i key:%s newLastDate:%s', n, z, x, y, key, tostring(newLastDate)))
		if callback then callback(Sprite{texture = MBTiles:getTileTexture(n, x, y, z), left=0, top=0}) end
		queuedFiles[key] = nil
		return
	end

	local metaURL, idx, metaID = tilemgr:osmMetaTileURL(x, y, z, MBTiles)
	if metaURL ~= "" then
		if debugging then print(string.format('osmReallyLoadRemoteTile[%i] Loading meta %s [+%d] from %s for %s', n, metaID, metaTilesPending[metaID][0], metaURL, key)) end
		return reallyLoadRemoteMetaTile(x,y,z,MBTiles, LastDate, why)
	end

if debugging then print(string.format('[%i] loading %i/%i/%i key:%s', n, z, x, y, key)) end
--print("osmReallyLoadRemoteTile:tile("..key..") queued:"..tostring(queuedFiles[key]).." download:"..tostring(downloadingFiles[key]))

	if false and not makeRequiredDirectory(key, dir) then
		print("makeRequiredDirectory("..file..','..dir..') FAILED!')
		--displayTileFailed(n,"DIR\nFAIL")
		if callback then callback(nil) end
		queuedFiles[key] = nil
		errorCount = errorCount + 1
		tilesFailed = tilesFailed + 1
		return
	end

	local now = MOAISim.getDeviceTime()*1000
		
--[[
http://ldeffenb.dnsalias.net:6360/osm/%z/%x/%y.png
		local server = URL:match("http://(.-)[:/].+")
		print("dns server "..tostring(server).." from "..tostring(URL))
		if server then
			local homeIP, text = socket.dns.toip(server)
			if not homeIP then
				print("dns.toip("..server..") returned "..tostring(text))
			else
				print(server..'=dns='..tostring(homeIP))
				--URL = URL:gsub(server,homeIP,1)
				print("dns URL:"..tostring(URL))
			end
		end
]]

		if not URL or URL == '' then
			local text = tostring(z)..'\n'..tostring(x)..'\n'..tostring(y)
			--displayTileFailed(n,text)--"NO\nURL")
			if callback then callback(nil) end
			queuedFiles[key] = nil
			--soonCount = soonCount + 1
			tilesFailed = tilesFailed + 1
			return
		end

		if (recentFailures[URL]) and (now-recentFailures[URL] < 60000) then
			--print("Too Soon("..tostring(now-recentFailures[URL])..'ms) for '..URL)
			local elapsed = now-recentFailures[URL]
			local percent = elapsed / 60000 * 100
			--displayTileFailed(n,string.format('%.1f%%',100-percent).."\nTOO\nSOON")
			if callback then callback(nil) end
			queuedFiles[key] = nil
			soonCount = soonCount + 1
		end

		if downloadingFiles[key] then
			print(string.format('osmReallyLoadRemoteTile['..n..']:ALREADY downloading %s for %ims', key, (now-downloadingFiles[key])))
		else
			downloadingFiles[key] = now
		end
		
		local stream = MOAIMemStream.new ()
		stream:open ( )

--		print("osmReallyLoadRemoteTile["..tostring(n).."]:Prepping for "..tostring(URL))

--		local startedLoading = MOAISim.getDeviceTime()*1000

	local start = MOAISim.getDeviceTime()
	
	local task = getURL(URL, stream, why)
	local responseCode = task:getResponseCode()
	
	local now = MOAISim.getDeviceTime()*1000
	local itWorked = false
	local tryImage

	local startedLoading = nil

local streamSize = stream:getLength()
if debugging then print('osmPlanetListener['..tostring(n)..'] completed with '..tostring(responseCode)..' got '..tostring(streamSize)..' bytes') end

	if responseCode == 304 then	-- Not Modified, from If-Modified-Since
		print ( "osmReallyLoadRemoteTile:NotModified:"..responseCode..' from '..tostring(metaURL))
		local LastModified = task:getResponseHeader("Last-Modified")
		local Expires = task:getResponseHeader("Expires")
		local Date = task:getResponseHeader("Date")
		
		print("osmPlanetListener:"..metaURL.." Date:"..tostring(Date).." Expires:"..tostring(Expires).." Last-Modified:"..tostring(LastModified))
	elseif responseCode ~= 200 then
		print ( "osmPlanetListener["..tostring(n).."]:Network error:"..responseCode..' from '..tostring(URL).." after "..tostring(now-(startedLoading or 0)).."ms")
		if responseCode ~= 404 and responseCode ~= 0 then
			if not config or not config.Debug or config.Debug.TileFailure then
				toast.new(file..'\nFailure Response:'..tostring(responseCode)..' Bytes:'..tostring(streamSize))
			end
		end
	elseif streamSize == 4294967295 then
		print ( "osmPlanetListener["..tostring(n).."]:Size:"..streamSize..' from '..tostring(URL).." after "..tostring(now-(startedLoading or 0)).."ms")
	else
if debugging then print("osmPlanetListener["..n.."]:Loading1 "..key) end

--	Tue, 25 Sep 2018 09:31:51 GMT
		local Date, Expires = getDateExpires(task, URL)

		if debugging then print("osmPlanetListener["..tostring(n).."]:Checking "..tostring(streamSize).." bytes from "..tostring(URL).." after "..tostring(now-(startedLoading or 0)).."ms") end

		local buffer = MOAIDataBuffer.new()
		stream:seek(0)
		local content, readbytes = stream:read()
		buffer:setString(content)
if debugging then print("osmPlanetListener["..tostring(n).."]:read "..tostring(readbytes).."/"..tostring(streamSize).." bytes to buffer giving "..tostring(buffer:getSize())) end

--[[
		local fstream = MOAIFileStream.new ()
		fstream:open ( dir..'/'..file, MOAIFileStream.READ_WRITE_NEW )
		stream:seek(0)
		local wrote = fstream:writeStream(stream)
if debugging then print("osmPlanetListener["..tostring(n).."]:Wrote "..tostring(wrote).."/"..tostring(streamSize).." bytes to "..dir.."/"..file) end
		fstream:close()
if debugging then print("osmPlanetListener["..tostring(n).."]:"..file.." size:"..tostring(streamSize))	end
]]

		tryImage = MOAITexture.new()
		tryImage:load(buffer, key)
		tryImage = Sprite { texture = tryImage, left=0, top=0 }
if debugging then print("osmPlanetListener["..n.."]:Loading1.25 "..key) end
		local width, height = tryImage:getSize()
if debugging then print("osmPlanetListener["..n.."]:Loading1.5 "..key..' is '..tostring(width)..'x'..tostring(height)) end

		if width == 256 and height == 256 then
			itWorked = true
--			osmSaveMBTileBuffer(n,x,y,z,buffer)
			if debugging then print("osmPlanetListener["..tostring(n).."]:Saving "..tostring(streamSize).." bytes from "..tostring(URL)) end
			MBTiles:saveTile(n,x,y,z,buffer,Date,Expires)
			clearDownloadedTile(osmTileKey(x,y,z,MBTiles))

			-- I think this is left over from the original Meta implementation 
			-- Originally it only went for a MetaTile if a single tile succeeded
			--reallyLoadRemoteMetaTile(x, y, z, MBTiles)

			local function checkPrefetch(x2,y2,z2)
				if validTileNum(x2,y2,z2) then
					if not MBTiles:checkTile(0, x2,y2,z2) then
						--local key2 = osmTileKey(x2,y2,z2,MBTiles)
	--					print("Prefetch "..key2.." or z="..tostring(z2).." x="..tostring(x2).." y="..tostring(y2))
						queueTile(pendingPrefetch, x2, y2, z2, MBTiles, function(sprite) print(string.format("Prefetched %d/%d/%d", z2, x2, y2, tostring(Expired))) end)
					end
				end
			end
			if z>0 then
				checkPrefetch(math.floor(x/2), math.floor(y/2), z-1)
			end
			if n ~= 0 then	-- NOT for prefetches or expirations
				checkPrefetch(x+1,y,z)	-- Go outwards in just a + shape
				checkPrefetch(x,y+1,z)
				checkPrefetch(x-1,y,z)
				checkPrefetch(x,y-1,z)
			end
			if n >= 1 and n <= 9 and z<=16 then		-- Prefetch below center 3x3 square
				checkPrefetch(x*2, y*2, z+1)
				checkPrefetch(x*2+1, y*2, z+1)
				checkPrefetch(x*2, y*2+1, z+1)
				checkPrefetch(x*2+1, y*2+1, z+1)
			end
		
		else
			tryImage = nil
			print('osmPlanetListener["..tostring(n).."]:Failed To Load '..key..' size:'..tostring(width)..'x'..tostring(height))
			toast.new(key..'\nFailure Size:'..tostring(width)..'x'..tostring(height)..' Bytes:'..tostring(streamSize), 5000)
		end
	end
	stream:close()

--print("osmPlanetListener:tile("..key..") queued:"..tostring(queuedFiles[key]).." download:"..tostring(downloadingFiles[key]))
	queuedFiles[key] = nil
	downloadingFiles[key] = nil
	if callback then callback(tryImage) end
	if itWorked then
		--print (string.format("Loaded in %ims", now-(startedLoading or 0)))
		tilesLoaded = tilesLoaded + 1
	else
		errorCount = errorCount + 1
		tilesFailed = tilesFailed + 1
		print("planetListener["..tostring(n).."]:Marking failure for "..tostring(URL))
		recentFailures[URL] = now
		print (string.format("planetListener[%d]:Loading FAILED in %ims", n, now-(startedLoading or 0)))
	end

	local elapsed = (MOAISim.getDeviceTime()-start)
	print(string.format("osmReallyLoadRemoteTile2:%s(%s) Took %.0fmsec", tostring(why), URL, elapsed*1000))

	return
end



local function OLD_reallyLoadRemoteMetaTile(x, y, z, MBTiles, LastDate, why)

	local metaURL, idx, metaID = tilemgr:osmMetaTileURL(x, y, z, MBTiles)
	if metaURL == "" then
		return
	end
	print(string.format("reallyLoadRemoteMetaTile metaTilesPending[%s] at %d from %s", metaID, metaTilesPending[metaID][0], metaURL))
	local stream = MOAIMemStream.new ()
	stream:open ( )

	local start = MOAISim.getDeviceTime()
	
local function metaListener( task, responseCode )
	local itWorked = false

	local streamSize = stream:getLength()
--	print('reallyLoadRemoteMetaTile completed with '..tostring(responseCode)..' got '..tostring(streamSize)..' bytes')

	if responseCode == 304 then	-- Not Modified, from If-Modified-Since
		print ( "reallyLoadRemoteMetaTile:NotModified:"..responseCode..' from '..tostring(metaURL))
		local LastModified = task:getResponseHeader("Last-Modified")
		local Expires = task:getResponseHeader("Expires")
		local Date = task:getResponseHeader("Date")
		
		print("metaListener:"..metaURL.." Date:"..tostring(Date).." Expires:"..tostring(Expires).." Last-Modified:"..tostring(LastModified))
	elseif responseCode ~= 200 then
		print ( "reallyLoadRemoteMetaTile:Network error:"..responseCode..' from '..tostring(metaURL))
	elseif streamSize == 4294967295 then
		print ( "reallyLoadRemoteMetaTile:Size:"..streamSize..' from '..tostring(metaURL))
	else

		local Date, Expires = getDateExpires(task, metaURL)

		local buffer = MOAIDataBuffer.new()
		stream:seek(0)
		local content, readbytes = stream:read()
		
		print(string.format("reallyLoadRemoteMetaTile:Received metaTilesPending[%s] at %d from %s", metaID, metaTilesPending[metaID][0], metaURL))
		local magic, count, xFirst, yFirst, zoom = struct.unpack('<c4IIII', content)
		local sq = math.sqrt(count)
		print(string.format("magic:%s count:%d (%dx%d) x,y:%d,%d z:%d", magic, count, sq, sq, xFirst, yFirst, zoom))
		for i=0,count-1 do
			local offset, size = struct.unpack('<II', content:sub(20+i*8+1))
			if (size > 0) then
				local xt, yt = xFirst+math.floor(i/sq), yFirst+(i%sq)
				buffer:setString(content:sub(offset+1,offset+1+size))
				local tryImage = MOAITexture.new()
				tryImage:load(buffer, "MetaTile "..tostring(z).."/"..tostring(xt).."/"..tostring(yt))
				local width, height = tryImage:getSize()
				--print(string.format("Tile@%d %d %d offset:%d size:%d wxh:%dx%d", i, xt, yt, offset, size, width, height))
				if width == 256 and height == 256 then
					--print("reallyLoadRemoteMetaTile:Saving "..tostring(size).." bytes from "..tostring(metaURL))
					MBTiles:saveTile(n,xt,yt,z,buffer,Date,Expires)
					clearDownloadedTile(osmTileKey(xt,yt,z,MBTiles))
				else
					print('reallyLoadRemoteMetaTile:Failed To Load '..xt..','..yt..' size:'..tostring(width)..'x'..tostring(height))
					tryImage = nil
				end
				local removes = {}
				for it, t in pairs(metaTilesPending[metaID]) do
					if type(t) == 'table' then
						if t.x == xt and t.y == yt and t.z == z then
							if debugging then print(string.format("reallyLoadRemoteMetaTile:Satisfied %i's %i/%i/%i callback %s key %s", t.n, t.z, t.x, t.y, tostring(t.callback), tostring(t.key))) end
							queuedFiles[t.key] = nil
							tilesLoaded = tilesLoaded + 1
							if t.callback then
								t.callback(Sprite { texture = tryImage, left=0, top=0 })
							end
							table.insert(removes,it)
						else extraTilesLoaded = extraTilesLoaded + 1
						end
					end
				end
				for _, it in pairs(removes) do
					metaTilesPending[metaID][it] = nil
					metaTilesPending[metaID][0] = metaTilesPending[metaID][0] - 1
					print(string.format("reallyLoadRemoteMetaTile:Removed %s from metaTilesPending[%s] now %d", it, metaID, metaTilesPending[metaID][0]))
				end
				if debugging then
					if #removes == 0 then
						local key = osmTileKey(xt,yt,z,MBTiles)
						if queuedFiles[key] then
							print(string.format("reallyLoadRemoteMetaTile:Unused %i/%i/%i key:%s queuedFiles:%s", z, xt, yt, key, tostring(queuedFiles[key])))
						else print(string.format("reallyLoadRemoteMetaTile:Unused %i/%i/%i key:%s", z, xt, yt, key))
						end
					end
				end
			end
		end

		local function checkPrefetch(x2,y2,z2)
			if validTileNum(x2,y2,z2) then
				if not MBTiles:checkTile(0, x2,y2,z2) then
					--local file2, dir2 = osmTileKey(x2,y2,z2,MBTiles)
					--print("Prefetch "..file2.." or z="..tostring(z2).." x="..tostring(x2).." y="..tostring(y2))
					queueTile(pendingPrefetch, x2, y2, z2, MBTiles, function(sprite) print(string.format("Prefetched %d/%d/%d", z2, x2, y2, tostring(Expired))) end)
				end
			end
		end
		if z>1 then
			checkPrefetch(math.floor(x/2), math.floor(y/2), z-1)
		end
--[[
		if n >= 1 and n <= 9 and z<15 then		-- Prefetch below center 3x3 square
			checkPrefetch(x*2, y*2, z+1)
			checkPrefetch(x*2+1, y*2, z+1)
			checkPrefetch(x*2, y*2+1, z+1)
			checkPrefetch(x*2+1, y*2+1, z+1)
		end
]]
		
--[[
Offset (hex)	Size	Meaning
000	4	Magic string "META"
004	4	Number of tiles in this metatile (64)
008	4	X index of first metatile (0 .. 2zoom-1)
00C	4	Y index of first metatile (0 .. 2zoom-1)
010	4	Zoom level
014	64 * 2 * 4	Offsets (from start of file) and sizes of tile data for each tile in column-major order
214		Tile data in PNG format at offsets given in header]]
	end

	for it, t in pairs(metaTilesPending[metaID]) do
		if type(t) == 'table' then
			if debugging then print(string.format("reallyLoadRemoteMetaTile:Clearing %i's %i/%i/%i callback %s key %s", t.n, t.z, t.x, t.y, tostring(t.callback), tostring(t.key))) end
			queuedFiles[t.key] = nil
			if t.callback then
				print(string.format("reallyLoadRemoteMetaTile:Clearing %i's %i/%i/%i callback %s key %s", t.n, t.z, t.x, t.y, tostring(t.callback), tostring(t.key)))
				t.callback(nil)	-- Callback with a failure
			end
		end
	end
	print(string.format("reallyLoadRemoteMetaTile:NILLING metaTilesPending[%s] from %d", metaID, metaTilesPending[metaID][0]))
	metaTilesPending[metaID] = nil
	
	stream:close()

	local elapsed = (MOAISim.getDeviceTime()-start)
	print(string.format("reallyLoadRemoteMetaTile:%s(%s) Took %.0fmsec", tostring(why), metaURL, elapsed*1000))

	propagateLoadingList()

end	-- testListener

	local task = MOAIHttpTask.new ()
	if debugging then task:setVerbose(true) end
	task:setVerb ( MOAIHttpTask.HTTP_GET )
	task:setUrl ( metaURL )
	task:setStream ( stream )
	task:setTimeout ( 30 )
	task:setCallback ( metaListener )
--[[
	if LastDate and LastDate ~= 0 then
		local luathen = luadate(LastDate)
		local sthen = luathen:fmt("${http}")
		print(string.format("%s If-Modified-Since: %s", metaURL, sthen))
		task:setHeader("If-Modified-Since", sthen)
	end
]]
	task:setUserAgent ( string.format('%s %s from %s %s', tostring(why),
										tostring(config.StationID),
										MOAIEnvironment.appDisplayName,
										tostring(config.About.Version)) )
	task:performAsync ()
end


function OLD_osmReallyLoadRemoteTile(n, x, y, z, MBTiles, callback, LastDate, why)	-- Wrapper to capture stack dump
	local co = coroutine.create( osmReallyLoadRemoteTile2 )
	local ok, msg = coroutine.resume( co, n, x, y, z, MBTiles, callback, LastDate, why )
	if not ok then
		local full_tb = debug.traceback( co )
					 .. "\n" .. debug.traceback( ) -- with 'stack traceback:' line
					 -- .. debug.traceback( ):sub( 17 ) -- drop 'stack traceback:' line
		print("osmReallyLoadRemoteTile2 failed with\n"..tostring(msg).."\n"..full_tb)
		toast.new(msg)
		return false
	end
	return true
end
			 
function OLD_osmReallyLoadRemoteTile2(n, x, y, z, MBTiles, callback, LastDate, why)

	local key = osmTileKey(x, y, z, MBTiles)
	local URL = osmTileURL(x, y, z, MBTiles)

	local haveIt, newLastDate = MBTiles:checkTile(n, x, y, z)
	if haveIt and not newLastDate then
		print(string.format('osmReallyLoadRemoteTile[%i] already HAVE %i/%i/%i key:%s newLastDate:%s', n, z, x, y, key, tostring(newLastDate)))
		if callback then callback(Sprite{texture = MBTiles:getTileTexture(n, x, y, z), left=0, top=0}) end
		queuedFiles[key] = nil
		propagateLoadingList()
		return
	end

	local metaURL, idx, metaID = tilemgr:osmMetaTileURL(x, y, z, MBTiles)
	if metaURL ~= "" then
		if debugging then print(string.format('osmReallyLoadRemoteTile[%i] Loading meta %s [+%d] from %s for %s', n, metaID, metaTilesPending[metaID][0], metaURL, key)) end
		reallyLoadRemoteMetaTile(x,y,z,MBTiles, LastDate, why)
		return
	end

if debugging then print(string.format('[%i] loading %i/%i/%i key:%s', n, z, x, y, key)) end
--print("osmReallyLoadRemoteTile:tile("..key..") queued:"..tostring(queuedFiles[key]).." download:"..tostring(downloadingFiles[key]))
	if true or makeRequiredDirectory(key, dir) then
		local now = MOAISim.getDeviceTime()*1000
		
--[[
http://ldeffenb.dnsalias.net:6360/osm/%z/%x/%y.png
		local server = URL:match("http://(.-)[:/].+")
		print("dns server "..tostring(server).." from "..tostring(URL))
		if server then
			local homeIP, text = socket.dns.toip(server)
			if not homeIP then
				print("dns.toip("..server..") returned "..tostring(text))
			else
				print(server..'=dns='..tostring(homeIP))
				--URL = URL:gsub(server,homeIP,1)
				print("dns URL:"..tostring(URL))
			end
		end
]]

		if URL and URL ~= '' then
		if (not recentFailures[URL]) or (now-recentFailures[URL] >= 60000) then
		
		if downloadingFiles[key] then
			print(string.format('osmReallyLoadRemoteTile['..n..']:ALREADY downloading %s for %ims', key, (now-downloadingFiles[key])))
		else
			downloadingFiles[key] = now
		end
		
		local stream = MOAIMemStream.new ()
		stream:open ( )

--		print("osmReallyLoadRemoteTile["..tostring(n).."]:Prepping for "..tostring(URL))

--		local startedLoading = MOAISim.getDeviceTime()*1000

	local start = MOAISim.getDeviceTime()

local function osmPlanetListener( task, responseCode )
	local now = MOAISim.getDeviceTime()*1000
	local itWorked = false
	local tryImage

	local startedLoading = nil

local streamSize = stream:getLength()
if debugging then print('osmPlanetListener['..tostring(n)..'] completed with '..tostring(responseCode)..' got '..tostring(streamSize)..' bytes') end

	if responseCode == 304 then	-- Not Modified, from If-Modified-Since
		print ( "osmReallyLoadRemoteTile:NotModified:"..responseCode..' from '..tostring(metaURL))
		local LastModified = task:getResponseHeader("Last-Modified")
		local Expires = task:getResponseHeader("Expires")
		local Date = task:getResponseHeader("Date")
		
		print("osmPlanetListener:"..metaURL.." Date:"..tostring(Date).." Expires:"..tostring(Expires).." Last-Modified:"..tostring(LastModified))
	elseif responseCode ~= 200 then
		print ( "osmPlanetListener["..tostring(n).."]:Network error:"..responseCode..' from '..tostring(URL).." after "..tostring(now-(startedLoading or 0)).."ms")
		if responseCode ~= 404 and responseCode ~= 0 then
			if not config or not config.Debug or config.Debug.TileFailure then
				toast.new(file..'\nFailure Response:'..tostring(responseCode)..' Bytes:'..tostring(streamSize))
			end
		end
	elseif streamSize == 4294967295 then
		print ( "osmPlanetListener["..tostring(n).."]:Size:"..streamSize..' from '..tostring(URL).." after "..tostring(now-(startedLoading or 0)).."ms")
	else
if debugging then print("osmPlanetListener["..n.."]:Loading1 "..key) end

--	Tue, 25 Sep 2018 09:31:51 GMT
		local Date, Expires = getDateExpires(task, URL)

		if debugging then print("osmPlanetListener["..tostring(n).."]:Checking "..tostring(streamSize).." bytes from "..tostring(URL).." after "..tostring(now-(startedLoading or 0)).."ms") end

		local buffer = MOAIDataBuffer.new()
		stream:seek(0)
		local content, readbytes = stream:read()
		buffer:setString(content)
if debugging then print("osmPlanetListener["..tostring(n).."]:read "..tostring(readbytes).."/"..tostring(streamSize).." bytes to buffer giving "..tostring(buffer:getSize())) end

--[[
		local fstream = MOAIFileStream.new ()
		fstream:open ( dir..'/'..file, MOAIFileStream.READ_WRITE_NEW )
		stream:seek(0)
		local wrote = fstream:writeStream(stream)
if debugging then print("osmPlanetListener["..tostring(n).."]:Wrote "..tostring(wrote).."/"..tostring(streamSize).." bytes to "..dir.."/"..file) end
		fstream:close()
if debugging then print("osmPlanetListener["..tostring(n).."]:"..file.." size:"..tostring(streamSize))	end
]]

		tryImage = MOAITexture.new()
		tryImage:load(buffer, key)
		tryImage = Sprite { texture = tryImage, left=0, top=0 }
if debugging then print("osmPlanetListener["..n.."]:Loading1.25 "..key) end
		local width, height = tryImage:getSize()
if debugging then print("osmPlanetListener["..n.."]:Loading1.5 "..key..' is '..tostring(width)..'x'..tostring(height)) end

		if width == 256 and height == 256 then
			itWorked = true
--			osmSaveMBTileBuffer(n,x,y,z,buffer)
			if debuggin then print("osmPlanetListener["..tostring(n).."]:Saving "..tostring(streamSize).." bytes from "..tostring(URL)) end
			MBTiles:saveTile(n,x,y,z,buffer,Date,Expires)
			clearDownloadedTile(osmTileKey(x,y,z,MBTiles))

			-- I think this is left over from the original Meta implementation 
			-- Originally it only went for a MetaTile if a single tile succeeded
			--reallyLoadRemoteMetaTile(x, y, z, MBTiles)

			local function checkPrefetch(x2,y2,z2)
				if validTileNum(x2,y2,z2) then
					if not MBTiles:checkTile(0, x2,y2,z2) then
						--local key2 = osmTileKey(x2,y2,z2,MBTiles)
	--					print("Prefetch "..key2.." or z="..tostring(z2).." x="..tostring(x2).." y="..tostring(y2))
						queueTile(pendingPrefetch, x2, y2, z2, MBTiles, function(sprite) print(string.format("Prefetched %d/%d/%d", z2, x2, y2, tostring(Expired))) end)
					end
				end
			end
			if z>1 then
				checkPrefetch(math.floor(x/2), math.floor(y/2), z-1)
			end
			if n ~= 0 then	-- NOT for prefetches or expirations
				checkPrefetch(x+1,y,z)	-- Go outwards in just a + shape
				checkPrefetch(x,y+1,z)
				checkPrefetch(x-1,y,z)
				checkPrefetch(x,y-1,z)
			end
			if n >= 1 and n <= 9 and z<=16 then		-- Prefetch below center 3x3 square
				checkPrefetch(x*2, y*2, z+1)
				checkPrefetch(x*2+1, y*2, z+1)
				checkPrefetch(x*2, y*2+1, z+1)
				checkPrefetch(x*2+1, y*2+1, z+1)
			end
		
		else
			tryImage = nil
			print('osmPlanetListener["..tostring(n).."]:Failed To Load '..key..' size:'..tostring(width)..'x'..tostring(height))
			toast.new(key..'\nFailure Size:'..tostring(width)..'x'..tostring(height)..' Bytes:'..tostring(streamSize), 5000)
		end
	end
	stream:close()

--print("osmPlanetListener:tile("..key..") queued:"..tostring(queuedFiles[key]).." download:"..tostring(downloadingFiles[key]))
	queuedFiles[key] = nil
	downloadingFiles[key] = nil
	if callback then callback(tryImage) end
	if itWorked then
		--print (string.format("Loaded in %ims", now-(startedLoading or 0)))
		tilesLoaded = tilesLoaded + 1
	else
		errorCount = errorCount + 1
		print("planetListener["..tostring(n).."]:Marking failure for "..tostring(URL))
		recentFailures[URL] = now
		tilesFailed = tilesFailed + 1
		print (string.format("planetListener[%d]:Loading FAILED in %ims", n, now-(startedLoading or 0)))
	end

	local elapsed = (MOAISim.getDeviceTime()-start)
	print(string.format("osmReallyLoadRemoteTile2:%s(%s) Took %.0fmsec", tostring(why), URL, elapsed*1000))

	if delayBetweenTiles <= 0 then
		propagateLoadingList()
	else performWithDelay(delayBetweenTiles, propagateLoadingList)
	end
end	-- osmPlanetListener


		local task = MOAIHttpTask.new ()
		if debugging then task:setVerbose(true) end
		task:setVerb ( MOAIHttpTask.HTTP_GET )
		task:setUrl ( URL )
		task:setStream ( stream )
		task:setTimeout ( 30 )
		task:setCallback ( osmPlanetListener )
--[[
		if LastDate and LastDate ~= 0 then
			local luathen = luadate(LastDate)
			local sthen = luathen:fmt("${http}")
			print(string.format("%s If-Modified-Since: %s", URL, sthen))
			task:setHeader("If-Modified-Since", sthen)
		end
]]
		task:setUserAgent ( string.format('%s %s from %s %s', tostring(why),
													tostring(config.StationID),
													MOAIEnvironment.appDisplayName,
													tostring(config.About.Version)) )
		--task:setHeader ( "Foo", "foo" )
		task:performAsync ()

		--if busyImage then busyImage:removeSelf(); busyImage = nil end
		--[[if not busyImage and tileGroup then
			busyImage = display.newText("Loading...", 0, 0, native.systemFont, 32)
			tileGroup:insert(2,busyImage)
			busyImage:setTextColor( 255,255,0,192)
			busyImage.x = tileGroup.contentWidth/2
			busyImage.y = tileGroup.contentHeight - busyImage.contentHeight/2
		end]]
		else
			--print("Too Soon("..tostring(now-recentFailures[URL])..'ms) for '..URL)
			local elapsed = now-recentFailures[URL]
			local percent = elapsed / 60000 * 100
			--displayTileFailed(n,string.format('%.1f%%',100-percent).."\nTOO\nSOON")
			if callback then callback(nil) end
			queuedFiles[key] = nil
			soonCount = soonCount + 1
			propagateLoadingList()
		end
		else
			local text = tostring(z)..'\n'..tostring(x)..'\n'..tostring(y)
			--displayTileFailed(n,text)--"NO\nURL")
			if callback then callback(nil) end
			queuedFiles[key] = nil
			--soonCount = soonCount + 1
			propagateLoadingList()
		end
	else
		print("makeRequiredDirectory("..file..','..dir..') FAILED!')
		--displayTileFailed(n,"DIR\nFAIL")
		if callback then callback(nil) end
		queuedFiles[key] = nil
		errorCount = errorCount + 1
		propagateLoadingList()
	end
end

function tilemgr:start()

print("tilemgr:start")

performWithDelay(30000, purgeRecentFailures, 0)	-- do this forever

end

return tilemgr
