// Sets the app password by writing its SHA-256 hash into src/main.jsx.
// Usage:  npm run set-password -- "yourPassword"
//   then: npm run build  (and git push to redeploy on Render)
import { readFileSync, writeFileSync } from "node:fs";
import { createHash } from "node:crypto";

const pw = process.argv[2];
if (!pw) {
  console.error('Provide a password, e.g.:  npm run set-password -- "myPass123"');
  process.exit(1);
}
const hash = createHash("sha256").update(pw).digest("hex");

const path = "src/main.jsx";
let src = readFileSync(path, "utf8");
if (!/const PASSWORD_HASH = "[a-f0-9]*";/.test(src)) {
  console.error("Could not find PASSWORD_HASH in src/main.jsx");
  process.exit(1);
}
src = src.replace(/const PASSWORD_HASH = "[a-f0-9]*";.*$/m, `const PASSWORD_HASH = "${hash}"; // (set via set-password)`);
writeFileSync(path, src);
console.log("Password updated. Next:  npm run build  &&  git add -A && git commit -m \"set password\" && git push");
