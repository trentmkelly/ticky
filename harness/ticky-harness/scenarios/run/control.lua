-- "@quality" for a signal of a quality other than normal, else "".
local function qname(sig)
  local q = sig.quality
  if q and type(q) ~= "string" then q = q.name end
  return (q and q ~= "normal") and ("@" .. q) or ""
end

-- Ticky in-game harness. Builds the blueprint from job.lua on a lab-tile surface, powers it,
-- then on each tick applies scheduled input changes and records every output port, writing
-- script-output/ticky/trace.txt (one line per tick: "<tick> <out1> <out2> ...").
local job = require("job")

local SETTLE = 30 -- ticks between building and turning RUN on

local function log(msg)
  helpers.write_file("ticky/log.txt", msg .. "\n", true)
end

local function fail(msg)
  log("FAIL " .. msg)
  helpers.write_file("ticky/done.txt", "fail")
  error(msg)
end

local function setup()
  local s = game.create_surface("ticky", {width = 256, height = 256})
  s.generate_with_lab_tiles = true
  s.always_day = true
  s.request_to_generate_chunks({0, 0}, 3)
  s.force_generate_chunk_requests()
  local f = game.forces.player

  local inv = game.create_inventory(1)
  local stack = inv[1]
  stack.set_stack{name = "blueprint"}
  if stack.import_stack(job.bp) ~= 0 then fail("blueprint import failed") end
  local bp_ents = stack.get_blueprint_entities()
  local ghosts = stack.build_blueprint{surface = s, force = f, position = {0, 0}, build_mode = defines.build_mode.forced}
  if #ghosts ~= #bp_ents then fail("built " .. #ghosts .. " ghosts for " .. #bp_ents .. " entities") end

  -- Match ghosts to blueprint entities by a common position offset.
  local by_pos = {}
  for _, g in pairs(ghosts) do by_pos[string.format("%.1f,%.1f", g.position.x, g.position.y)] = g end
  local offset
  for _, g in pairs(ghosts) do
    if g.ghost_name == bp_ents[1].name then
      local dx, dy = g.position.x - bp_ents[1].position.x, g.position.y - bp_ents[1].position.y
      local ok = true
      for _, e in pairs(bp_ents) do
        local m = by_pos[string.format("%.1f,%.1f", e.position.x + dx, e.position.y + dy)]
        if not m or m.ghost_name ~= e.name then ok = false break end
      end
      if ok then offset = {dx, dy} break end
    end
  end
  if not offset then fail("could not match ghosts to blueprint entities") end

  local ents = {}
  for _, e in pairs(bp_ents) do
    local g = by_pos[string.format("%.1f,%.1f", e.position.x + offset[1], e.position.y + offset[2])]
    local _, built = g.revive()
    if not built then fail("could not revive " .. e.name) end
    ents[e.entity_number] = built
  end

  -- Infinite power next to the left-most power pole (wire relays have no copper wires).
  local left
  local function powered(e)
    return e.get_wire_connector(defines.wire_connector_id.pole_copper, true).connection_count > 0
  end
  for _, e in pairs(ents) do
    if e.name == "medium-electric-pole" and (not left or (powered(e) and not powered(left))
        or (powered(e) == powered(left) and e.position.x < left.position.x)) then
      left = e
    end
  end
  local eei = s.create_entity{name = "electric-energy-interface", position = {left.position.x - 2, left.position.y + 0.5}, force = f}
  if not eei then fail("could not place power source") end

  -- A constant combinator feeding each input port, standing in for the player's wires.
  local injectors = {}
  for i, p in ipairs(job.ports) do
    if p.dir == "in" then
      local port = ents[p.entity]
      -- West of the port, or north of it for ports in a row (facing south).
      local pos = {port.position.x - 6.5, port.position.y}
      if port.direction == defines.direction.south then pos = {port.position.x, port.position.y - 3.5} end
      local inj = s.create_entity{name = "constant-combinator", position = pos, force = f}
      if not inj then fail("could not place injector for " .. p.name) end
      inj.get_wire_connector(defines.wire_connector_id.circuit_red, true)
        .connect_to(port.get_wire_connector(defines.wire_connector_id.combinator_input_red, true))
      injectors[i] = inj
    end
  end
  storage.ents = ents
  storage.injectors = injectors
  storage.start = game.tick + SETTLE
  storage.lines = {}
  log("built " .. #bp_ents .. " entities; offset " .. offset[1] .. "," .. offset[2])
end

script.on_event(defines.events.on_tick, function(e)
  if e.tick == 1 then setup() return end
  if not storage.start or e.tick < storage.start then return end
  local i = e.tick - storage.start
  if i == 0 then
    local run = storage.ents[job.run].get_control_behavior()
    if run.enabled then fail("RUN switch was already on") end
    run.enabled = true
  end
  for _, st in ipairs(job.sets) do
    if st.t == i and st.port == 0 then
      storage.ents[job.run].get_control_behavior().enabled = st.value ~= 0
    elseif st.t == i and st.values then
      -- A bundle input: replace every slot.
      local section = storage.injectors[st.port].get_control_behavior().get_section(1)
      for k = 1, section.filters_count do section.clear_slot(k) end
      for k, v in ipairs(st.values) do
        section.set_slot(k, {value = {type = v.type, name = v.name, quality = v.quality or "normal"}, min = v.value})
      end
    elseif st.t == i and job.ports[st.port].control then
      -- A control: switch its constant combinator, or edit its value, as a player would.
      local p = job.ports[st.port]
      local cb = storage.ents[p.control].get_control_behavior()
      if p.switch then
        cb.enabled = st.value ~= 0
      else
        cb.get_section(1).set_slot(1, {value = {type = p.signal.type, name = p.signal.name, quality = "normal"}, min = st.value})
      end
    elseif st.t == i then
      local p = job.ports[st.port]
      local section = storage.injectors[st.port].get_control_behavior().get_section(1)
      section.set_slot(1, {value = {type = p.signal.type, name = p.signal.name, quality = "normal"}, min = st.value})
    end
  end
  local row = {tostring(i)}
  for _, p in ipairs(job.ports) do
    -- An output read at the end of its return line: the red network there.
    local signals
    if p.dir == "out" and p.pole then
      local n = storage.ents[p.entity].get_circuit_network(defines.wire_connector_id.circuit_red)
      signals = n and n.signals or {}
    elseif p.dir == "out" and p.bundle then
      signals = storage.ents[p.entity].get_control_behavior().signals_last_tick or {}
    end
    if p.dir == "out" and p.pole and not p.bundle then
      local v = 0
      for _, sg in pairs(signals) do
        if sg.signal.name == p.signal.name and qname(sg.signal) == "" then v = v + sg.count end
      end
      row[#row + 1] = tostring(v)
    elseif p.dir == "out" and p.bundle then
      -- Every signal the port outputs, as {name=value,...} sorted by name.
      local parts = {}
      for _, sg in pairs(signals) do
        if sg.count ~= 0 then parts[#parts + 1] = {n = sg.signal.name .. qname(sg.signal), v = sg.count} end
      end
      table.sort(parts, function(a, b) return a.n < b.n end)
      local strs = {}
      for _, x in ipairs(parts) do strs[#strs + 1] = x.n .. "=" .. x.v end
      row[#row + 1] = "{" .. table.concat(strs, ",") .. "}"
    elseif p.dir == "out" and not p.pole then
      local v = storage.ents[p.entity].get_control_behavior().get_signal_last_tick(p.signal)
      row[#row + 1] = tostring(v or 0)
    end
  end
  -- Screens: each pixel's colour as shown (0xRRGGBB as a number, 0 while off).
  for _, lamps in ipairs(job.screens or {}) do
    local px = {}
    local first = storage.ents[lamps[1]]
    if first and first.name == "display-panel" then
      -- A panel: which message it shows (1-based; 0 for none), by text and icon.
      local shown, ic = 0, first.display_panel_icon
      for k, m in ipairs(first.get_control_behavior().messages) do
        if (m.text or "") == (first.display_panel_text or "") and ((m.icon and m.icon.name) == (ic and ic.name)) then
          shown = k
          break
        end
      end
      px[1] = tostring(shown)
      lamps = {}
    elseif first and first.name == "programmable-speaker" then
      -- A speaker: the value of its condition's signal while the condition holds (it plays),
      -- else 0.
      local cond = first.get_control_behavior().circuit_condition
      local net = first.get_circuit_network(defines.wire_connector_id.circuit_red)
      px[1] = tostring(cond.fulfilled and net and net.get_signal(cond.first_signal) or 0)
      lamps = {}
    end
    for k, id in ipairs(lamps) do
      local cb = storage.ents[id].get_control_behavior()
      local c = (not cb.disabled) and cb.color
      if c then
        local function b(x) return math.floor(x * 255 + 0.5) end
        px[k] = tostring(b(c.r) * 65536 + b(c.g) * 256 + b(c.b))
      else
        px[k] = "0"
      end
    end
    row[#row + 1] = table.concat(px, ",")
  end
  storage.lines[#storage.lines + 1] = table.concat(row, " ")
  if i == job.ticks - 1 then
    if job.screenshot then
      local x0, y0, x1, y1 = math.huge, math.huge, -math.huge, -math.huge
      for _, ent in pairs(storage.ents) do
        x0, y0 = math.min(x0, ent.position.x), math.min(y0, ent.position.y)
        x1, y1 = math.max(x1, ent.position.x), math.max(y1, ent.position.y)
      end
      local w, h = x1 - x0 + 16, y1 - y0 + 8
      local zoom = math.min(1280 / (w * 32), 800 / (h * 32)) * 1.0
      game.take_screenshot{surface = "ticky", position = {(x0 + x1) / 2 - 3, (y0 + y1) / 2}, resolution = {1280, 800},
        zoom = zoom, path = "ticky/shot.png", show_entity_info = true, daytime = 0}
      game.take_screenshot{surface = "ticky", position = {x0 + 1, y0 + 4}, resolution = {1280, 800},
        zoom = 1.6, path = "ticky/shot-ports.png", show_entity_info = true, daytime = 0}
    end
    helpers.write_file("ticky/trace.txt", table.concat(storage.lines, "\n") .. "\n")
    -- Lamps (the --checks error lamp): lit or not at the end.
    local lamps = {}
    for _, ent in pairs(storage.ents) do
      if ent.valid and ent.name == "small-lamp" then
        lamps[#lamps + 1] = ent.get_control_behavior().disabled and "off" or "lit"
      end
    end
    helpers.write_file("ticky/lamps.txt", table.concat(lamps, " ") .. "\n")
    -- Speakers and panels as built from the blueprint: their settings.
    local per = {}
    for _, ent in pairs(storage.ents) do
      if ent.valid and ent.name == "programmable-speaker" then
        per[#per + 1] = "speaker " .. helpers.table_to_json({ent.parameters, ent.alert_parameters, ent.get_control_behavior().circuit_parameters, ent.get_control_behavior().circuit_condition})
      elseif ent.valid and ent.name == "display-panel" then
        per[#per + 1] = "panel " .. helpers.table_to_json({ent.display_panel_always_show, ent.display_panel_show_in_chart, ent.get_control_behavior().messages})
      end
    end
    helpers.write_file("ticky/peripherals.txt", table.concat(per, "\n") .. "\n")
    helpers.write_file("ticky/done.txt", "ok")
  end
end)
