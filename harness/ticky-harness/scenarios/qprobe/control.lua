-- Probe: the selector modes Ticky does not use yet (quality transfer/filter, random, stack
-- size, rocket capacity). Run with TICKY_QUALITY=1 TICKY_SCENARIO=qprobe. Writes ticky/q.txt.
local s, f
local x = 0
local tests = {}
local W = defines.wire_connector_id
local function konst(vals)
  x = x + 3
  local c = s.create_entity{name = "constant-combinator", position = {x, 0}, force = f}
  local sec = c.get_control_behavior().get_section(1)
  for i, v in ipairs(vals) do sec.set_slot(i, {value = {type = v[1], name = v[2], quality = v[4] or "normal"}, min = v[3]}) end
  return c
end
local function sel(params, red, green, label)
  x = x + 3
  local c = s.create_entity{name = "selector-combinator", position = {x, 0}, force = f}
  local ok, err = pcall(function() c.get_control_behavior().parameters = params end)
  if red then konst(red).get_wire_connector(W.circuit_red, true).connect_to(c.get_wire_connector(W.combinator_input_red, true)) end
  if green then konst(green).get_wire_connector(W.circuit_green, true).connect_to(c.get_wire_connector(W.combinator_input_green, true)) end
  tests[#tests + 1] = {label .. (ok and "" or (" [ERR " .. tostring(err) .. "]")), c}
end
local function dump(c)
  local parts = {}
  for _, sg in pairs(c.get_control_behavior().signals_last_tick or {}) do
    parts[#parts + 1] = sg.signal.name .. "@" .. (sg.signal.quality or "normal") .. "=" .. sg.count
  end
  table.sort(parts)
  return table.concat(parts, ",")
end
local rnd = {}
script.on_event(defines.events.on_tick, function(e)
  if e.tick == 1 then
    s = game.surfaces[1]
    f = game.forces.player
    s.create_entity{name = "electric-energy-interface", position = {-6, 6}, force = f}
    for px = -2, 400, 14 do s.create_entity{name = "substation", position = {px, 4}, force = f} end
    local b = {{"item", "iron-plate", 100}, {"item", "copper-plate", 50}, {"virtual", "signal-A", 7}, {"fluid", "water", 9}}
    local mixed = {{"item", "iron-plate", 100}, {"item", "iron-plate", 3, "rare"}, {"item", "iron-plate", 5, "epic"},
      {"virtual", "signal-A", 7, "uncommon"}, {"virtual", "signal-B", 11, "legendary"}}
    local EACH = {type = "virtual", name = "signal-each"}
    local B = {type = "virtual", name = "signal-B"}
    for _, form in ipairs({"str", "tbl"}) do
      local q = function(n) if form == "str" then return n else return {name = n} end end
      sel({operation = "quality-transfer", quality_source_static = q("legendary"), quality_destination_signal = EACH}, b, nil, form .. " QT each->legendary")
      sel({operation = "quality-transfer", quality_source_static = q("rare"), quality_destination_signal = EACH}, mixed, nil, form .. " QT mixed each->rare")
      sel({operation = "quality-transfer", quality_source_static = q("rare"), quality_destination_signal = {type = "item", name = "iron-plate"}}, mixed, nil, form .. " QT iron->rare mixed")
      sel({operation = "quality-transfer", quality_source_static = q("rare"), quality_destination_signal = {type = "item", name = "iron-plate", quality = "epic"}}, mixed, nil, form .. " QT iron@epic->rare mixed")
    end
    sel({operation = "quality-transfer", select_quality_from_signal = true, quality_source_signal = {type = "virtual", name = "signal-Q"}, quality_destination_signal = EACH}, mixed, {{"virtual", "signal-Q", 1, "uncommon"}}, "QT src Q(uncommon) each mixed")
    sel({operation = "quality-transfer", select_quality_from_signal = true, quality_source_signal = {type = "virtual", name = "signal-Q"}, quality_destination_signal = EACH}, b, nil, "QT src Q absent")
    sel({operation = "quality-transfer", select_quality_from_signal = true, quality_source_signal = {type = "virtual", name = "signal-Q"}, quality_destination_signal = EACH}, b, {{"virtual", "signal-Q", 1, "uncommon"}, {"virtual", "signal-Q", 1, "epic"}}, "QT src Q two qualities")
    sel({operation = "quality-transfer", select_quality_from_signal = true, quality_source_signal = {type = "virtual", name = "signal-Q"}, quality_destination_signal = {type = "virtual", name = "signal-Q"}}, b, {{"virtual", "signal-Q", 4, "rare"}}, "QT src Q dest Q")
    for _, cmp in ipairs({"=", ">", "<", "≥", "≠"}) do
      sel({operation = "quality-filter", quality_filter = {quality = "rare", comparator = cmp}}, mixed, b, "QF " .. cmp .. " rare")
    end
    sel({operation = "stack-size"}, {{"item", "iron-plate", 1}, {"item", "iron-gear-wheel", -5, "rare"}, {"item", "nuclear-reactor", 1}, {"fluid", "water", 3}, {"virtual", "signal-A", 1}, {"item", "iron-plate", 2, "epic"}}, nil, "stack-size")
    sel({operation = "rocket-capacity"}, {{"item", "iron-plate", 1}, {"item", "iron-gear-wheel", 5}, {"item", "nuclear-reactor", 1}, {"item", "rocket-silo", 1}}, nil, "rocket-capacity")
    local eight = {}
    for k = 1, 8 do eight[k] = {"virtual", "signal-" .. k, k} end
    sel({operation = "random"}, eight, nil, "random interval 0")
    sel({operation = "random", random_update_interval = 1}, eight, nil, "random interval 1")
    sel({operation = "random", random_update_interval = 10}, eight, nil, "random interval 10")
    sel({operation = "random"}, {{"virtual", "signal-A", 5}}, nil, "random single")
    rnd = {#tests - 3, #tests - 2, #tests - 1, #tests}
  elseif e.tick > 5 and e.tick <= 205 then
    for _, i in ipairs(rnd) do
      local t = tests[i]
      t.seq = t.seq or {}
      local v = 0
      for _, sg in pairs(t[2].get_control_behavior().signals_last_tick or {}) do v = v * 100 + sg.count end
      t.seq[#t.seq + 1] = v
    end
  elseif e.tick == 206 then
    local out = {}
    for _, t in ipairs(tests) do
      out[#out + 1] = t[1] .. ": " .. dump(t[2])
      if t.seq then out[#out + 1] = "  seq: " .. table.concat(t.seq, " ", 1, 60) end
    end
    -- How blueprints store these modes: the selector entities exported as JSON.
    local inv = game.create_inventory(1)
    inv.insert{name = "blueprint"}
    local bp = inv[1]
    bp.create_blueprint{surface = s, force = f, area = {{0, -2}, {x + 2, 2}}}
    local seen = {}
    for _, ent in ipairs(bp.get_blueprint_entities() or {}) do
      if ent.name == "selector-combinator" and ent.control_behavior then
        local j = helpers.table_to_json(ent.control_behavior)
        if not seen[j] then seen[j] = true; out[#out + 1] = "bp: " .. j end
      end
    end
    helpers.write_file("ticky/q.txt", table.concat(out, "\n") .. "\n")
    helpers.write_file("ticky/done.txt", "ok")
  end
end)
