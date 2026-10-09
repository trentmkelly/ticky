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
# TICKY_SPACE_AGE=1 also loads the Space Age expansion (used to dump its signals).
# TICKY_QUALITY=1 loads just the Quality mod (blueprints whose internal signals use quality).
SA=$([ -n "${TICKY_SPACE_AGE:-}" ] && echo true || echo false)
Q=$([ -n "${TICKY_SPACE_AGE:-}${TICKY_QUALITY:-}" ] && echo true || echo false)
echo '{"mods": [{"name": "base", "enabled": true}, {"name": "space-age", "enabled": '$SA'},
 {"name": "quality", "enabled": '$Q'}, {"name": "elevated-rails", "enabled": '$SA'},
 {"name": "ticky-harness", "enabled": true}]}' > "$T/mods/mod-list.json"
# Only the harness (and TICKY_EXTRA_MODS) are loaded: mod folders left from earlier runs go.
find "$T/mods" -mindepth 1 -maxdepth 1 -type d -exec rm -rf {} +
cp -r "$H/ticky-harness" "$T/mods/ticky-harness"
# TICKY_EXTRA_MODS="name=path ...": extra mod folders to load (copied in under their names).
for m in ${TICKY_EXTRA_MODS:-}; do
  rm -rf "$T/mods/${m%%=*}"; cp -r "${m#*=}" "$T/mods/${m%%=*}"
  python3 -c "import json,sys; f='$T/mods/mod-list.json'; d=json.load(open(f)); d['mods'].append({'name': sys.argv[1], 'enabled': True}); json.dump(d, open(f,'w'))" "${m%%=*}"
done
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
    --mod-directory "$T/mods" --load-scenario ticky-harness/${TICKY_SCENARIO:-run} --disable-audio --window-size 1280x800 \
    < "$T/stdin" > "$T/run.log" 2>&1 &
else
  SteamAppId=427520 SteamGameId=427520 timeout 600 "$F/bin/x64/factorio" --config "$T/config/config.ini" \
    --mod-directory "$T/mods" --start-server-load-scenario ticky-harness/${TICKY_SCENARIO:-run} \
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
