-- Probe: the selector combinator's order among equal values. For each set of signals (all
-- with the same value) and each index k, records which signal `select` outputs (max and min).
-- Writes ticky/ties.txt: "<set> <max|min> <k> <type>/<name>/<quality>".
local s, f
local x = 0
local tests = {}
local function konst(vals)
  x = x + 3
  local c = s.create_entity{name = "constant-combinator", position = {x, 0}, force = f}
  local sec = c.get_control_behavior().get_section(1)
  for i, v in ipairs(vals) do sec.set_slot(i, {value = {type = v[1], name = v[2], quality = v[3] or "normal"}, min = v[4] or 5}) end
  return c
end
local function sel(src, max, k, label)
  x = x + 3
  local c = s.create_entity{name = "selector-combinator", position = {x, 0}, force = f}
  c.get_control_behavior().parameters = {operation = "select", select_max = max, index_constant = k}
  src.get_wire_connector(defines.wire_connector_id.circuit_red, true).connect_to(c.get_wire_connector(defines.wire_connector_id.combinator_input_red, true))
  tests[#tests + 1] = {label, c}
end
local sets = {
  items = {{"item", "wood"}, {"item", "iron-plate"}, {"item", "coal"}, {"item", "copper-plate"}, {"item", "stone"}, {"item", "iron-ore"}},
  items_rev = {{"item", "iron-ore"}, {"item", "stone"}, {"item", "copper-plate"}, {"item", "coal"}, {"item", "iron-plate"}, {"item", "wood"}},
  virtual = {{"virtual", "signal-Z"}, {"virtual", "signal-A"}, {"virtual", "signal-0"}, {"virtual", "signal-red"}, {"virtual", "signal-check"}, {"virtual", "signal-B"}},
  mixed = {{"fluid", "water"}, {"item", "coal"}, {"virtual", "signal-A"}, {"item", "iron-plate"}, {"fluid", "crude-oil"}, {"virtual", "signal-dot"}},
  quality = {{"virtual", "signal-A", "rare"}, {"virtual", "signal-A", "normal"}, {"virtual", "signal-B", "uncommon"}, {"virtual", "signal-A", "legendary"}, {"virtual", "signal-A", "uncommon"}, {"item", "coal", "epic"}},
  partial = {{"item", "coal", nil, 5}, {"item", "iron-plate", nil, 9}, {"item", "wood", nil, 5}, {"virtual", "signal-A", nil, 9}, {"item", "stone", nil, 5}, {"virtual", "signal-B", nil, -1}},
}
script.on_event(defines.events.on_tick, function(e)
  if e.tick == 1 then
    s = game.surfaces[1]
    f = game.forces.player
    s.create_entity{name = "electric-energy-interface", position = {-6, 6}, force = f}
    for px = -2, 600, 14 do s.create_entity{name = "substation", position = {px, 4}, force = f} end
    local names = {}
    for n in pairs(sets) do names[#names + 1] = n end
    table.sort(names)
    for _, n in ipairs(names) do
      for k = 0, #sets[n] - 1 do
        sel(konst(sets[n]), true, k, n .. " max " .. k)
        sel(konst(sets[n]), false, k, n .. " min " .. k)
      end
    end
  elseif e.tick == 10 then
    local out = {}
    for _, t in ipairs(tests) do
      local sigs = t[2].get_control_behavior().signals_last_tick or {}
      local parts = {}
      for _, sg in pairs(sigs) do
        parts[#parts + 1] = (sg.signal.type or "item") .. "/" .. sg.signal.name .. "/" .. (sg.signal.quality or "normal") .. "=" .. sg.count
      end
      out[#out + 1] = t[1] .. " " .. table.concat(parts, ",")
    end
    helpers.write_file("ticky/ties.txt", table.concat(out, "\n") .. "\n")
    helpers.write_file("ticky/done.txt", "ok")
  end
end)
