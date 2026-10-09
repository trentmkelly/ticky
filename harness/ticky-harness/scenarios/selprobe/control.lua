-- Probe: selector `select` with an index signal. Does the index signal take part in the
-- sort? Writes ticky/sel.txt.
local s, f
local x = 0
local tests = {}
local function konst(vals)
  x = x + 3
  local c = s.create_entity{name = "constant-combinator", position = {x, 0}, force = f}
  local sec = c.get_control_behavior().get_section(1)
  for i, v in ipairs(vals) do sec.set_slot(i, {value = {type = v[1], name = v[2], quality = "normal"}, min = v[3]}) end
  return c
end
local W = defines.wire_connector_id
local function sel(params, red, green, label)
  x = x + 3
  local c = s.create_entity{name = "selector-combinator", position = {x, 0}, force = f}
  c.get_control_behavior().parameters = params
  if red then konst(red).get_wire_connector(W.circuit_red, true).connect_to(c.get_wire_connector(W.combinator_input_red, true)) end
  if green then konst(green).get_wire_connector(W.circuit_green, true).connect_to(c.get_wire_connector(W.combinator_input_green, true)) end
  tests[#tests + 1] = {label, c}
end
script.on_event(defines.events.on_tick, function(e)
  if e.tick == 1 then
    s = game.surfaces[1]
    f = game.forces.player
    s.create_entity{name = "electric-energy-interface", position = {-6, 6}, force = f}
    for px = -2, 300, 14 do s.create_entity{name = "substation", position = {px, 4}, force = f} end
    local b = {{"item", "iron-plate", 100}, {"item", "copper-plate", 50}, {"item", "coal", 10}}
    local I = {type = "virtual", name = "signal-I"}
    for _, iv in ipairs({0, 1, 2, 3, 4}) do
      sel({operation = "select", select_max = true, index_signal = I}, b, {{"virtual", "signal-I", iv}}, "max I=" .. iv)
      sel({operation = "select", select_max = false, index_signal = I}, b, {{"virtual", "signal-I", iv}}, "min I=" .. iv)
    end
    sel({operation = "select", select_max = true, index_signal = I}, b, nil, "max no I")
  elseif e.tick == 10 then
    local out = {}
    for _, t in ipairs(tests) do
      local parts = {}
      for _, sg in pairs(t[2].get_control_behavior().signals_last_tick or {}) do
        parts[#parts + 1] = sg.signal.name .. "=" .. sg.count
      end
      out[#out + 1] = t[1] .. ": " .. table.concat(parts, ",")
    end
    helpers.write_file("ticky/sel.txt", table.concat(out, "\n") .. "\n")
    helpers.write_file("ticky/done.txt", "ok")
  end
end)
