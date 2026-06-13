// Regenerates standalone.html (the no-build, double-click version) from the
// Vite source of truth (src/main.jsx + src/index.css). Run: npm run build:standalone
import { readFileSync, writeFileSync } from "node:fs";

const css = readFileSync("src/index.css", "utf8")
  .replace(/^@tailwind[^\n]*\n/gm, "")   // drop Tailwind directives (CDN handles them)
  .replace(/^\s+/, "");

let js = readFileSync("src/main.jsx", "utf8")
  .replace(/^import .*\n/gm, "")          // strip ES imports (UMD globals used instead)
  .replace(/\n?createRoot\(document\.getElementById\("root"\)\)\.render\(<App \/>\);\s*$/, "")
  .trim();

const html = `<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8" />
<meta name="viewport" content="width=device-width, initial-scale=1.0" />
<title>STL → Ladder Diagram Converter | S7 PLC</title>
<script src="https://unpkg.com/react@18/umd/react.production.min.js"></script>
<script src="https://unpkg.com/react-dom@18/umd/react-dom.production.min.js"></script>
<script src="https://unpkg.com/@babel/standalone/babel.min.js"></script>
<script src="https://cdn.tailwindcss.com"></script>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=JetBrains+Mono:wght@400;600;700&family=Inter:wght@400;500;600;700&display=swap" rel="stylesheet">
<style>
${css}
</style>
</head>
<body>
<div id="root"></div>
<script type="text/babel" data-presets="react">
const { useState, useEffect, useMemo, useRef, useCallback } = React;

${js}

ReactDOM.createRoot(document.getElementById("root")).render(<App />);
<\/script>
</body>
</html>
`;

writeFileSync("standalone.html", html);
console.log("standalone.html regenerated (" + html.length + " bytes)");
