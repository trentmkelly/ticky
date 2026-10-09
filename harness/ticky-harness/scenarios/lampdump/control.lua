-- Builds a lamp with a circuit condition and writes its blueprint string (ticky/lamp.txt).
script.on_event(defines.events.on_tick, function(e)
  if e.tick ~= 1 then return end
  local s = game.surfaces[1]
  local f = game.forces.player
  local lamp = s.create_entity{name = "small-lamp", position = {0.5, 0.5}, force = f}
  local cb = lamp.get_or_create_control_behavior()
  cb.circuit_enable_disable = true
  cb.circuit_condition = {first_signal = {type = "virtual", name = "signal-E"}, comparator = ">", constant = 0}
  local ok, err = pcall(function() lamp.color = {r = 1, g = 0, b = 0} end)
  local log = {"color set: " .. tostring(ok) .. " " .. tostring(err)}
  for k, v in pairs({use_colors = cb.use_colors, color_mode = cb.color_mode}) do log[#log + 1] = k .. "=" .. tostring(v) end
  local inv = game.create_inventory(1)
  inv.insert{name = "blueprint"}
  local bp = inv[1]
  bp.create_blueprint{surface = s, force = f, area = {{-2, -2}, {3, 3}}}
  log[#log + 1] = bp.export_stack()
  helpers.write_file("ticky/lamp.txt", table.concat(log, "\n"))
  helpers.write_file("ticky/done.txt", "ok")
end)
