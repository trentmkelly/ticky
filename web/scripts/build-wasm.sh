#!/usr/bin/env bash
# Builds the compiler for the browser into web/src/pkg (wasm-bindgen glue + optimised wasm).
# Needs: rustup target wasm32-unknown-unknown and wasm-bindgen-cli 0.2.100 (cargo install
# wasm-bindgen-cli --version 0.2.100). No wasm-opt: it saves only ~3% gzipped, and older
# binaryen releases break the reference-types table wasm-bindgen sets up.
set -euo pipefail
cd "$(dirname "$0")/../.."
cargo build -p ticky-web --target wasm32-unknown-unknown --release
wasm-bindgen --target web --out-dir web/src/pkg target/wasm32-unknown-unknown/release/ticky_web.wasm
ls -l web/src/pkg/ticky_web_bg.wasm
