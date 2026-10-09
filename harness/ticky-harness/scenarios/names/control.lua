-- Writes ticky/names.txt: the localised-name structure of every item, fluid and recipe whose
-- name starts with "nt-" (one per line: type, name, serpent of localised_name). Resolved to
-- text against the mod's locale file outside the game.
script.on_event(defines.events.on_tick, function(e)
  if e.tick ~= 1 then return end
  local rows = {}
  for _, kind in ipairs({"item", "fluid", "recipe"}) do
    for name, proto in pairs(prototypes[kind]) do
      if name:sub(1, 3) == "nt-" then
        rows[#rows + 1] = kind .. "\t" .. name .. "\t" .. helpers.table_to_json({proto.localised_name})
      end
    end
  end
  helpers.write_file("ticky/names.txt", table.concat(rows, "\n") .. "\n")
  helpers.write_file("ticky/done.txt", "ok")
end)
