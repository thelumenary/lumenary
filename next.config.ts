import type { NextConfig } from "next";

// The Lumenary is deployed as a fully static site (no application server),
// so it can be hosted cheaply on any static host or CDN without vendor lock-in.
// Learner code never runs on a server: Python runs in a sandboxed Web Worker
// in the learner's own browser (Pyodide/WebAssembly).
const nextConfig: NextConfig = {
  output: "export",
  trailingSlash: true,
  images: { unoptimized: true },
  reactStrictMode: true,
};

export default nextConfig;
