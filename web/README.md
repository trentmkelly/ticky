# Ticky playground

The compiler and test runner in the browser: an editor with Ticky highlighting, compile-as-you-type
diagnostics, test runs in the simulator, the build summary, a drawing of the placed circuit, and a
button that copies the blueprint string. Published to GitHub Pages by
`.github/workflows/pages.yml` on every push to `main`.

```bash
rustup target add wasm32-unknown-unknown
cargo install wasm-bindgen-cli --version 0.2.100
cd web
npm install
npm run wasm      # crates/ticky-web → src/pkg (wasm + glue)
npm run dev       # http://localhost:5173
npm run build     # dist/
```

- `crates/ticky-web`: `compile(src, options)` and `test(src, options)`, JSON in and out.
- `src/worker.ts`: the compiler runs in a Web Worker (restarted after a panic or a 60 s build).
- `src/ticky-lang.ts`: syntax highlighting; `src/circuit.ts`: the circuit drawing, with the
  game's graphics from `public/sprites/` (checked in). `scripts/build-sprites.py [DATA_DIR]`
  remakes them from a Factorio install (needs Pillow): it slices the frames used and reads
  sprite offsets, display symbols and wire terminals from the game's prototype files.
  Graphics © Wube Software.
- The examples menu reads `../examples/*.ticky` at build time (the list is in `src/main.ts`).
