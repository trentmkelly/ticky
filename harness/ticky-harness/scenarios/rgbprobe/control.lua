-- Probe: lamps in packed-RGB colour mode. What colour does a lamp show for a given value
-- (including 0, negatives and values past 0xFFFFFF), with and without an enable condition,
-- and with a quality signal as the colour signal? Writes ticky/rgb.txt (results and the
-- blueprint string of the lamps).
local s, f
local x = 0
local tests = {}
local log = {}
local W = defines.wire_connector_id
local function konst(sig, v)
  local c = s.create_entity{name = "constant-combinator", position = {x, 0}, force = f}
  c.get_control_behavior().get_section(1).set_slot(1, {value = sig, min = v})
  return c
end
local function lamp(sig, v, cond, label)
  x = x + 3
  local k = konst(sig, v)
  local l = s.create_entity{name = "small-lamp", position = {x + 1, 0}, force = f}
  local cb = l.get_or_create_control_behavior()
  local ok, err = pcall(function()
    cb.use_colors = true
    cb.color_mode = defines.control_behavior.lamp.color_mode.packed_rgb
    cb.rgb_signal = sig
    if cond then
      cb.circuit_enable_disable = true
      cb.circuit_condition = {first_signal = sig, comparator = "≠", constant = 0}
    end
  end)
  if not ok then log[#log + 1] = label .. ": setup error " .. tostring(err) end
  k.get_wire_connector(W.circuit_red, true).connect_to(l.get_wire_connector(W.circuit_red, true))
  tests[#tests + 1] = {label, l}
end
script.on_event(defines.events.on_tick, function(e)
  if e.tick == 1 then
    s = game.surfaces[1]
    f = game.forces.player
    s.create_entity{name = "electric-energy-interface", position = {-6, 6}, force = f}
    for px = -2, 300, 14 do s.create_entity{name = "substation", position = {px, 4}, force = f} end
    local A = {type = "virtual", name = "signal-A", quality = "normal"}
    local Aq = {type = "virtual", name = "signal-A", quality = "uncommon"}
    for _, v in ipairs({0, 255, 65280, 16711680, 16746496, 16777215, 16777216, 16777471, -1, -16777216}) do
      lamp(A, v, false, "plain v=" .. v)
      lamp(A, v, true, "cond v=" .. v)
    end
    lamp(Aq, 16746496, true, "quality v=16746496")
    local inv = game.create_inventory(1)
    inv.insert{name = "blueprint"}
    local bp = inv[1]
    bp.create_blueprint{surface = s, force = f, area = {{2, -1}, {6, 1}}}
    log[#log + 1] = "BP " .. bp.export_stack()
  elseif e.tick == 10 then
    for _, t in ipairs(tests) do
      local l = t[2]
      local cb = l.get_control_behavior()
      local ok, c = pcall(function() return cb.color end)
      local col = ok and c and string.format("r=%.3f g=%.3f b=%.3f", c.r or -1, c.g or -1, c.b or -1) or ("color err " .. tostring(c))
      local ok2, dis = pcall(function() return cb.disabled end)
      log[#log + 1] = t[1] .. ": " .. col .. " disabled=" .. tostring(ok2 and dis) .. " status=" .. tostring(l.status)
    end
    helpers.write_file("ticky/rgb.txt", table.concat(log, "\n"))
    helpers.write_file("ticky/done.txt", "ok")
  end
end)
