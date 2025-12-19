local debugging = false
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

require "struct"

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

local tilesLoaded = 0		-- Count of loaded tiles
local extraTilesLoaded = 0	-- Count of "extra" non-requested tiles in metatiles

function tilemgr:getTilesLoaded()
	return tilesLoaded, extraTilesLoaded
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

function getMBTilesDirectory()

	if config.Dir.Tiles ~= '' then return config.Dir.Tiles..'/MBTiles/' end
	return (MOAIEnvironment.externalFilesDirectory or MOAIEnvironment.externalCacheDirectory or MOAIEnvironment.cacheDirectory or MOAIEnvironment.documentDirectory or "Cache/").."/MBTiles/";
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

local function initMBTiles(force)

	if not force and MBinited then return end
	MBinited = true
	
	EnsureAllMBTiles()
	
	config.Map.MBTiles = config.Map.MBTiles or "./LynnsTiles.mbtiles"
	if MOAIFileSystem.getAbsoluteFilePath(config.Map.MBTiles) ~= config.Map.MBTiles then
		config.Map.MBTiles = EnsureMBTiles(config.Map.MBTiles)
	end
	config.Map.TopTiles = config.Map.TopTiles or "./LynnsTiles.mbtiles"
	if MOAIFileSystem.getAbsoluteFilePath(config.Map.TopTiles) ~= config.Map.TopTiles then
		config.Map.TopTiles = EnsureMBTiles(config.Map.TopTiles)
	end

	MBTiles = MBTile(config.Map.MBTiles, force)--("./LynnsTiles.mbtiles")
	if not MBTiles then
		MBTiles = MBTile(EnsureMBTiles("./LynnsTiles.mbtiles"))
	end

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

	if MBTiles.MetaFormat and MBTiles.MetaFormat ~= "" then
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
				elseif f:sub(1,1) == 'm' then	-- %m is meta bits
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

local pendingPrefetch = {}
local pendingExpired = {}
pendingPrefetch[0] = 0
pendingExpired[0] = 0

local loadingCircle
local getTileGroup

function tilemgr:setGetTileGroup(getCallback)
	getTileGroup = getCallback
end

function tilemgr:getQueueStats()	-- returns count, maxcount, pushcount, popcount
	local loadingActive = loadingList.count + loadRunning + #pendingPrefetch + #pendingExpired
	local loadingMax = loadingList.maxcount + concurrentLoadingThreads + pendingPrefetch[0] + pendingExpired[0]
	return loadingActive, loadingMax, loadingList.pushcount, loadingList.popcount
end

local function updateLoadingCount(what)
	local loadingActive = loadingList.count + loadRunning + #pendingPrefetch + #pendingExpired
	local loadingMax = loadingList.maxcount + concurrentLoadingThreads + pendingPrefetch[0] + pendingExpired[0]
	if true or debugging then
		local info = debug.getinfo( 2, "Sl" )
		local where = info.source..':'..info.currentline
		if where:sub(1,1) == '@' then where = where:sub(2) end
		print("updateLoadingCount:"..what.." "..tostring(loadingActive)..'/'..tostring(loadingMax).." from "..tostring(where))
	end
	if stilltext then
		local new = string.format("%d(%d)+%d+%d/%d(%d)+%d+%d\n%d%s",
									loadingList.count, loadRunning, #pendingPrefetch, #pendingExpired,
									loadingList.maxcount, concurrentLoadingThreads, pendingPrefetch[0], pendingExpired[0],
									tilesLoaded, extraTilesLoaded>0 and "+"..tostring(extraTilesLoaded) or "")
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
			print(string.format("Initialized metaTilesPending[%s] to zero for %s", metaID, client.key))
		end
		if not metaTilesPending[metaID][client.key] then
			metaTilesPending[metaID][client.key] = client
			metaTilesPending[metaID][0] = metaTilesPending[metaID][0] + 1
			queued = (metaTilesPending[metaID][0] > 1)
			print(string.format("Incremented metaTilesPending[%s] to %d queued:%s for %s", metaID, metaTilesPending[metaID][0], tostring(queued), client.key))
		else
			queued = true
			print(string.format("metaTilesPending[%s] has %d IS QUEUED %s", metaID, metaTilesPending[metaID][0], client.key))
		end
		if true or debugging then print(string.format("metaTilesPending[%s] has %d %s %s", metaID, metaTilesPending[metaID][0], queued and "queued" or "NEW", client.key)) end
	end
	return queued
end

local function startQueueServer(client)
--	MOAICoroutine.new ():run ( function()
	if debugging then print(string.format('startQueueServer:running %i/%i/%i key:%s', client.z, client.x, client.y, client.key)) end
	loadedCount, skippedCount, errorCount, lateCount, soonCount = 0, 0, 0, 0, 0
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

local function queueTile(list, x, y, z, MBTiles, callback, LastDate)
	local listname = "Unknown"
	if list == pendingPrefetch then listname = "Prefetch"
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
				StartQueueServer(client)
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
	removeKey(pendingPrefetch)
	removeKey(pendingExpired)
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
		MOAICoroutine.new():run(function()
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
				
				--local timer = MOAITimer.new()
				--timer:setSpan(0.1)
				--MOAICoroutine.blockOnAction(timer:start())
				--coroutine.yield()
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
			return client
		end
	end
	if loadRunning == 1 then	-- Only if this is the last running queuer
		local function dequeueTile(list, why)
			local client = table.remove(list)
			if not client then return nil end
			list[client.key] = nil
			updateLoadingCount("dequeueing item "..tostring(client).." "..tostring(client.key))
			return client
		end
		local client = dequeueTile(pendingPrefetch, "Prefetch")
		if not client then client = dequeueTile(pendingExpired, "Expired") end
		if client then return client end
	end
	return nil	-- Nothing to do, trust the co-routine to exit now
end

local function propagateLoadingList()
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
			if not dequeueTile(pendingPrefetch, "Prefetch") then
				if not dequeueTile(pendingExpired, "Expired") then
					pendingPrefetch[0] = 0
					pendingExpired[0] = 0
					didOne = false
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

local function reallyLoadRemoteMetaTile(x, y, z, MBTiles, LastDate, why)

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

function osmReallyLoadRemoteTile(n, x, y, z, MBTiles, callback, LastDate, why)	-- Wrapper to capture stack dump
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
			 
function osmReallyLoadRemoteTile2(n, x, y, z, MBTiles, callback, LastDate, why)

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
			toast.new(key..'\nFailure Size:'..tostring(width)..'x'..tostring(height)..' Bytes:'..tostring(streamSize))
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
