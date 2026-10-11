#!/usr/bin/env bash
# Full check of a compiler change: release build, `cargo test --release`, the bench, and
# every fuzzer, all against one frozen copy of the release binary (so a rebuild elsewhere
# mid-run can't change what is tested, and no fuzzer falls back to a stale debug build).
# usage: tools/verify.sh            (run from anywhere; exits non-zero on any failure)
#   FUZZ_N=200 FUZZ_SEED=7 tools/verify.sh   fuzzer size (COUNT/ROUNDS, default 20) and seed (default 1)
#   BENCH_OUT=after.txt tools/verify.sh      also save the bench table there
set -u
cd "$(dirname "$0")/.."
N=${FUZZ_N:-20}
SEED=${FUZZ_SEED:-1}
DIR=$(mktemp -d /tmp/ticky-verify-XXXXXX)
trap 'rm -rf "$DIR"' EXIT
fail=()

echo "== cargo build --release"
cargo build --release || { echo "verify: build failed"; exit 1; }
cp target/release/ticky "$DIR/ticky"
export TICKY="$DIR/ticky"
export FUZZ_KEEP="${FUZZ_KEEP:-/tmp/ticky-verify-$$-programs}"  # failing fuzz_level2 programs

echo "== cargo test --release"
cargo test --release || fail+=("cargo test")

echo "== tools/bench.sh"
tools/bench.sh > "$DIR/bench.txt"
cat "$DIR/bench.txt"
grep -q ' error$' "$DIR/bench.txt" && fail+=("bench (an example failed to compile)")
[ -n "${BENCH_OUT:-}" ] && cp "$DIR/bench.txt" "$BENCH_OUT"

for f in tools/fuzz_*.py; do
  echo "== $f $N $SEED"
  python3 "$f" "$N" "$SEED" > "$DIR/fuzz.log" 2>&1
  rc=$?
  tail -n 3 "$DIR/fuzz.log"
  if [ $rc -ne 0 ]; then
    fail+=("$f")
    cp "$DIR/fuzz.log" "/tmp/ticky-verify-$$-$(basename "$f" .py).log"
    echo "   (full log: /tmp/ticky-verify-$$-$(basename "$f" .py).log)"
  fi
done

echo
if [ ${#fail[@]} -ne 0 ]; then
  echo "verify: FAILED: ${fail[*]}"
  exit 1
fi
echo "verify: all passed (fuzz size $N, seed $SEED)"
