#!/usr/bin/env python3
"""fuzz_programs.py and fuzz_procs.py with profile-guided builds (PGO=1): each random program
is profiled with `ticky test --profile` (on its own inputs or, half the time, on others) and
the circuit compared with Python is the one `build --profile` makes. COUNT programs of each.

usage: tools/fuzz_pgo.py [COUNT] [SEED]
"""
import os
import sys

os.environ["PGO"] = "1"
# Their loops are short: count a jump taken once as hot, so the profile changes something.
os.environ.setdefault("TICKY_PGO_HOT", "1")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fuzz_procs  # noqa: E402  pylint: disable=wrong-import-position
import fuzz_programs  # noqa: E402  pylint: disable=wrong-import-position


def main():
    """Runs both fuzzers; fails if either does."""
    codes = []
    for fuzzer in (fuzz_programs, fuzz_procs):
        try:
            fuzzer.main()
            codes.append(0)
        except SystemExit as e:
            codes.append(e.code or 0)
    sys.exit(1 if any(codes) else 0)


if __name__ == "__main__":
    main()
