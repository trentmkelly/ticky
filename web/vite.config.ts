import { defineConfig } from "vite";

export default defineConfig({
  // Relative URLs, so the site works under GitHub Pages' /ticky/ path.
  base: "./",
  // The examples are read from ../examples at build time.
  server: { fs: { allow: [".."] } },
  worker: { format: "es" },
  build: { target: "es2022" },
});
