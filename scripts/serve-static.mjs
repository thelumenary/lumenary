// Minimal static file server for the exported site (out/). No dependencies.
import http from "node:http";
import fs from "node:fs";
import path from "node:path";

const TYPES = { ".html": "text/html; charset=utf-8", ".js": "text/javascript", ".css": "text/css", ".json": "application/json", ".svg": "image/svg+xml", ".png": "image/png", ".woff2": "font/woff2", ".txt": "text/plain", ".ico": "image/x-icon" };

export function serve(root, port = 4173) {
  const server = http.createServer((req, res) => {
    const url = decodeURIComponent((req.url ?? "/").split("?")[0]);
    let file = path.join(root, url);
    if (!file.startsWith(root)) return res.writeHead(403).end();
    if (fs.existsSync(file) && fs.statSync(file).isDirectory()) file = path.join(file, "index.html");
    if (!fs.existsSync(file)) {
      res.writeHead(404, { "content-type": TYPES[".html"] });
      return res.end(fs.existsSync(path.join(root, "404.html")) ? fs.readFileSync(path.join(root, "404.html")) : "Not found");
    }
    res.writeHead(200, { "content-type": TYPES[path.extname(file)] ?? "application/octet-stream" });
    fs.createReadStream(file).pipe(res);
  });
  return new Promise((resolve) => server.listen(port, () => resolve(server)));
}

if (import.meta.url === `file://${process.argv[1]}`) {
  const root = path.resolve(process.argv[2] ?? "out");
  const port = Number(process.argv[3] ?? 4173);
  await serve(root, port);
  console.log(`Serving ${root} at http://localhost:${port}/`);
}
