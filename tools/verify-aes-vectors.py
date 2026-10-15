#!/usr/bin/env python3
"""Recheck the AES circuit's committed test answers using the OpenSSL CLI.

Run from any directory: python3 tools/verify-aes-vectors.py
Then exercise the compiled circuits (both optimization modes, with/without checks):
    cargo test --release --locked -p ticky-compiler --test aes128
No Python crypto package is required. OpenSSL must be on PATH.
"""
import json
import shutil
import subprocess
from pathlib import Path


def main():
    if not shutil.which("openssl"):
        raise SystemExit("openssl is required to verify the independent AES answers")
    root = Path(__file__).resolve().parents[1]
    fixtures = json.loads((root / "crates/ticky-compiler/tests/fixtures/aes128-vectors.json").read_text())
    verified = 0
    for case in fixtures:
        key = bytes.fromhex(case["key"])
        assert len(key) == 16
        plaintext = [bytes.fromhex(v["plaintext"]) for v in case["vectors"]]
        expected = [bytes.fromhex(v["ciphertext"]) for v in case["vectors"]]
        assert all(len(v) == 16 for v in plaintext + expected)
        actual = subprocess.run(
            ["openssl", "enc", "-aes-128-ecb", "-K", key.hex(), "-nopad", "-nosalt"],
            input=b"".join(plaintext), stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True,
        ).stdout
        assert actual == b"".join(expected), f"AES answers differ for key {key.hex()}"
        verified += len(plaintext)
    print(f"OpenSSL agrees with all {verified} AES-128 vectors across {len(fixtures)} keys.")


if __name__ == "__main__":
    main()
