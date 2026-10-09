#!/usr/bin/env bash
# usage: run.sh [JOB.lua]  — runs the harness scenario on a headless server in a sandbox
# (/tmp/ticky-harness; never touches ~/.factorio). Results in /tmp/ticky-harness/script-output/ticky/
set -u
H=$(cd "$(dirname "$0")" && pwd)
F=~/.local/share/Steam/steamapps/common/Factorio
T=/tmp/ticky-harness
mkdir -p "$T/config" "$T/mods"
cat > "$T/config/config.ini" <<'INI'
[path]
read-data=__PATH__executable__/../../data
write-data=/tmp/ticky-harness
INI
[ -n "${TICKY_SCREENSHOT:-}" ] && printf '[graphics]\nfull-screen=false\n' >> "$T/config/config.ini"
echo '{"mods": [{"name": "base", "enabled": true}, {"name": "space-age", "enabled": false},
 {"name": "quality", "enabled": false}, {"name": "elevated-rails", "enabled": false},
 {"name": "ticky-harness", "enabled": true}]}' > "$T/mods/mod-list.json"
rm -rf "$T/mods/ticky-harness"; cp -r "$H/ticky-harness" "$T/mods/ticky-harness"
[ -n "${1:-}" ] && cp "$1" "$T/mods/ticky-harness/scenarios/run/job.lua"
python3 -c "
import json; s=json.load(open('$F/data/server-settings.example.json'))
s.update(visibility={'public': False, 'lan': False}, auto_pause=False, require_user_verification=False, autosave_interval=0)
json.dump(s, open('$T/server-settings.json', 'w'))"
rm -rf "$T/script-output" "$T/factorio-current.log"
cd "$T" || exit 1
# The server quits on stdin EOF; hold a FIFO open for as long as this script runs.
rm -f "$T/stdin"; mkfifo "$T/stdin"; exec 3<>"$T/stdin"
if [ -n "${TICKY_SCREENSHOT:-}" ]; then
  # Windowed single-player so the game can render screenshots.
  SteamAppId=427520 SteamGameId=427520 timeout 600 "$F/bin/x64/factorio" --config "$T/config/config.ini" \
    --mod-directory "$T/mods" --load-scenario ticky-harness/run --disable-audio --window-size 1280x800 \
    < "$T/stdin" > "$T/run.log" 2>&1 &
else
  SteamAppId=427520 SteamGameId=427520 timeout 600 "$F/bin/x64/factorio" --config "$T/config/config.ini" \
    --mod-directory "$T/mods" --start-server-load-scenario ticky-harness/run \
    --server-settings "$T/server-settings.json" --port 34297 < "$T/stdin" > "$T/run.log" 2>&1 &
fi
PID=$!
for _ in $(seq 590); do
  sleep 0.5
  [ -f "$T/script-output/ticky/done.txt" ] && break
  kill -0 $PID 2>/dev/null || break
  grep -qE "Error while running|Failed to load mods|Error ServerMultiplayer" "$T/run.log" && break
  grep -qE "Error AppManager|Error while running" "$T/factorio-current.log" 2>/dev/null && break
done
kill $PID 2>/dev/null; wait $PID 2>/dev/null
# The windowed client can sit on an error dialog; make sure nothing from this sandbox survives.
pkill -9 -f "factorio --config $T/config" 2>/dev/null
cat "$T/run.log" "$T/factorio-current.log" 2>/dev/null | grep -E "Error|error" | grep -viE "steam|primary display" | sort -u | head -20
[ -f "$T/script-output/ticky/done.txt" ] || { echo "NO RESULT (see $T/run.log)"; exit 1; }
