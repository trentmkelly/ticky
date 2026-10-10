-- Probe: programmable speakers. Instruments and notes, the blueprint format, and whether
-- anything readable (entity status) follows the circuit condition. Writes ticky/speaker.txt.
local s, f, k, sp, log = nil, nil, nil, {}, {}
local W = defines.wire_connector_id
local V = {type = "virtual", name = "signal-V"}
script.on_event(defines.events.on_tick, function(e)
  if e.tick == 1 then
    s = game.surfaces[1]
    f = game.forces.player
    s.create_entity{name = "electric-energy-interface", position = {-6, 6}, force = f}
    s.create_entity{name = "substation", position = {0, 4}, force = f}
    local proto = prototypes.entity["programmable-speaker"]
    for i, ins in ipairs(proto.instruments) do
      local notes = {}
      for j, n in ipairs(ins.notes) do notes[#notes + 1] = j .. ":" .. n end
      log[#log + 1] = "instrument " .. i .. " " .. ins.name .. " (" .. #ins.notes .. "): " .. table.concat(notes, " ")
    end
    k = s.create_entity{name = "constant-combinator", position = {-3, 0}, force = f}
    -- A speaker as built: its default instrument and note (ids are 0-based if alarms = 0).
    local d = s.create_entity{name = "programmable-speaker", position = {6, 0}, force = f}
    k.get_wire_connector(W.circuit_red, true).connect_to(d.get_wire_connector(W.circuit_red, true))
    log[#log + 1] = "default: " .. helpers.table_to_json(d.get_control_behavior().circuit_parameters)
    local ok = pcall(function() d.get_control_behavior().circuit_parameters = {signal_value_is_pitch = false, instrument_id = 11, note_id = 0} end)
    log[#log + 1] = "set instrument 11: " .. tostring(ok) .. " " .. helpers.table_to_json(d.get_control_behavior().circuit_parameters)
    ok = pcall(function() d.get_control_behavior().circuit_parameters = {signal_value_is_pitch = false, instrument_id = 12, note_id = 0} end)
    log[#log + 1] = "set instrument 12: " .. tostring(ok) .. " " .. helpers.table_to_json(d.get_control_behavior().circuit_parameters)
    -- 1: an alarm (condition V > 0, alert with message); 2: notes, pitch from V.
    local a = s.create_entity{name = "programmable-speaker", position = {0, 0}, force = f}
    k.get_wire_connector(W.circuit_red, true).connect_to(a.get_wire_connector(W.circuit_red, true))
    a.parameters = {playback_volume = 1, playback_mode = "global", allow_polyphony = false}
    a.alert_parameters = {show_alert = true, show_on_map = true, icon_signal_id = {type = "virtual", name = "signal-fire"}, alert_message = "Too hot"}
    a.get_control_behavior().circuit_condition = {first_signal = V, comparator = ">", constant = 0}
    a.get_control_behavior().circuit_parameters = {signal_value_is_pitch = false, instrument_id = 1, note_id = 1}
    local b = s.create_entity{name = "programmable-speaker", position = {2, 0}, force = f}
    k.get_wire_connector(W.circuit_red, true).connect_to(b.get_wire_connector(W.circuit_red, true))
    b.get_control_behavior().circuit_condition = {first_signal = V, comparator = ">", constant = 0}
    b.get_control_behavior().circuit_parameters = {signal_value_is_pitch = true, instrument_id = 4, note_id = 1}
    sp = {a, b}
  elseif e.tick >= 2 and e.tick <= 10 then
    local v = ({[2] = 0, [3] = 0, [4] = 5, [5] = 5, [6] = 5, [7] = 0, [8] = 0, [9] = 3, [10] = 3})[e.tick]
    k.get_control_behavior().get_section(1).set_slot(1, {value = {type = "virtual", name = "signal-V", quality = "normal"}, min = v})
    local row = {"tick " .. e.tick .. " V=" .. v .. ":"}
    for i, x in ipairs(sp) do
      local st = x.status
      local name = "?"
      for n, c in pairs(defines.entity_status) do if c == st then name = n end end
      row[#row + 1] = i .. "=" .. name
    end
    log[#log + 1] = table.concat(row, " ")
  elseif e.tick == 11 then
    local inv = game.create_inventory(1)
    inv.insert{name = "blueprint"}
    local bp = inv[1]
    bp.create_blueprint{surface = s, force = f, area = {{-1, -2}, {4, 2}}}
    for _, ent in ipairs(bp.get_blueprint_entities() or {}) do
      if ent.name == "programmable-speaker" then log[#log + 1] = "bp: " .. helpers.table_to_json(ent) end
    end
    helpers.write_file("ticky/speaker.txt", table.concat(log, "\n") .. "\n")
    helpers.write_file("ticky/done.txt", "ok")
  end
end)
