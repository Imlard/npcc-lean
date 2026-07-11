#!/usr/bin/env node
// PIPELINE v1 runner — C1 I/O + C3 compiler verdict + C4 router (C2/C5 drive via packets).
// Contract per formalization/PIPELINE-SPEC.md. The compiler is the only truth.
// Commands:
//   node pipeline/runner.mjs status
//   node pipeline/runner.mjs next                 -> emits pipeline/packets/<id>.md (work packet)
//   node pipeline/runner.mjs state  <id> <file>   -> register statement file (claim block; sorry body OK)
//   node pipeline/runner.mjs signoff <id>         -> mark signed (ONLY after Simon's explicit yes)
//   node pipeline/runner.mjs submit <id> <file>   -> proof submission: Claim-Check + build + axiom gate + route
// Ledger: obligations.json (single source of truth; runner is its only writer).

import fs from "node:fs";
import path from "node:path";
import { execFileSync } from "node:child_process";

const ROOT = path.resolve(path.dirname(new URL(import.meta.url).pathname.replace(/^\/([A-Za-z]:)/, "$1")), "..");
const LEDGER = path.join(ROOT, "obligations.json");
const CONFIG = JSON.parse(fs.readFileSync(path.join(ROOT, "pipeline", "config.json"), "utf8"));
const CLAIMS = path.join(ROOT, "claims");
const PACKETS = path.join(ROOT, "pipeline", "packets");
const TMP = path.join(ROOT, "pipeline", "tmp");
for (const d of [CLAIMS, PACKETS, TMP]) fs.mkdirSync(d, { recursive: true });

const CLOSED = new Set(["proved", "axiom"]);
const SIGNOFF_KINDS = new Set(["def", "lemma", "bridge", "port-check"]); // aux-lemma: judge-only (v1 interpretation, see README)

function loadLedger() { return JSON.parse(fs.readFileSync(LEDGER, "utf8")); }
function saveLedger(L) {
  const tmp = LEDGER + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(L, null, 1) + "\n");
  fs.renameSync(tmp, LEDGER);
}
function byId(L, id) {
  const o = L.obligations.find(x => x.id === id);
  if (!o) die(`unknown obligation id: ${id}`);
  return o;
}
function die(msg) { console.error("FATAL: " + msg); process.exit(1); }

function depsClosed(L, o) {
  return o.deps.every(d => CLOSED.has(byId(L, d).status));
}
function needsSignoff(o) { return SIGNOFF_KINDS.has(o.kind); }
function claimPath(id) { return path.join(CLAIMS, id.replace(/[:/]/g, "_") + ".txt"); }

// ---------- claim blocks ----------
const BEGIN = id => `-- CLAIM-BEGIN ${id}`;
const END = id => `-- CLAIM-END ${id}`;
function canonicalClaim(text) {
  return text.replace(/\r\n/g, "\n").replace(/\n$/, "");
}
function extractClaim(text, id) {
  const begin = BEGIN(id);
  const end = END(id);
  const escape = value => value.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const starts = [...text.matchAll(new RegExp(`^${escape(begin)}\\r?$`, "gm"))];
  const ends = [...text.matchAll(new RegExp(`^${escape(end)}\\r?$`, "gm"))];
  if (starts.length !== 1 || ends.length !== 1 || ends[0].index <= starts[0].index) return null;
  return text.slice(starts[0].index, ends[0].index + end.length);
}
// Any write to a file must preserve, byte-identically, EVERY already-registered claim
// living in that file (not just the obligation being worked on).
function verifyRegisteredClaims(L, file, text, exceptId) {
  for (const o of L.obligations) {
    if (o.file !== file || o.id === exceptId) continue;
    const reg = claimPath(o.id);
    if (!fs.existsSync(reg)) continue;
    if (canonicalClaim(extractClaim(text, o.id) || "") !==
        canonicalClaim(fs.readFileSync(reg, "utf8"))) return o.id;
  }
  return null;
}

// ---------- compiler verdict (C3) ----------
function lakeBuild() {
  try {
    const out = execFileSync("lake", ["build", "NPCC"], { cwd: ROOT, encoding: "utf8", stdio: ["ignore", "pipe", "pipe"], timeout: 15 * 60 * 1000 });
    return { ok: true, out };
  } catch (err) {
    const out = (err.stdout || "") + "\n" + (err.stderr || "");
    return { ok: false, out };
  }
}
function errHead(out) {
  return out.split("\n").filter(l => /error/.test(l)).slice(0, 12).join("\n");
}
function regenerateRoot() {
  // NPCC.lean imports every NPCC/*.lean module that exists (recursive).
  const mods = [];
  (function walk(dir, prefix) {
    if (!fs.existsSync(dir)) return;
    for (const f of fs.readdirSync(dir, { withFileTypes: true })) {
      if (f.isDirectory()) walk(path.join(dir, f.name), prefix + f.name + ".");
      else if (f.name.endsWith(".lean")) mods.push("import " + prefix + f.name.slice(0, -5));
    }
  })(path.join(ROOT, "NPCC"), "NPCC.");
  fs.writeFileSync(path.join(ROOT, "NPCC.lean"), mods.sort().join("\n") + "\n");
}
function axiomCheck(leanName) {
  const f = path.join(TMP, "AxCheck.lean");
  fs.writeFileSync(f, `import NPCC\n#print axioms ${leanName}\n`);
  let out;
  try {
    out = execFileSync("lake", ["env", "lean", f], { cwd: ROOT, encoding: "utf8", stdio: ["ignore", "pipe", "pipe"], timeout: 10 * 60 * 1000 });
  } catch (err) {
    return { ok: false, axioms: null, out: (err.stdout || "") + (err.stderr || "") };
  }
  const m = out.match(/depends on axioms: \[([^\]]*)\]/);
  if (!m) {
    if (/does not depend on any axioms/.test(out)) return { ok: true, axioms: [], out };
    return { ok: false, axioms: null, out };
  }
  const axioms = m[1].split(",").map(s => s.trim()).filter(Boolean);
  const bad = axioms.filter(a => !CONFIG.allowedAxioms.includes(a));
  return { ok: bad.length === 0, axioms, bad, out };
}
function usesSorry(text) {
  return /(^|[^A-Za-z0-9_])sorry([^A-Za-z0-9_]|$)/m.test(text);
}

// ---------- C4 router ----------
function route(L, o, failureNote) {
  o.attempts.push({ ts: new Date().toISOString(), note: failureNote.slice(0, 800) });
  const lanes = CONFIG.lanes.length;
  const budget = CONFIG.attemptsPerLane * lanes;
  if (o.attempts.length >= budget) {
    o.status = "parked";
    o.route = "parked: budgets exhausted -> decompose or escalate-human (Simon)";
  } else {
    const lane = CONFIG.lanes[Math.floor(o.attempts.length / CONFIG.attemptsPerLane)];
    o.route = `retry on lane '${lane}' (attempt ${o.attempts.length + 1}/${budget})`;
  }
}

// ---------- packets (C2/C5 interface) ----------
function emitPacket(L, o) {
  const phase = o.status === "open" ? "STATE" : "PROVE";
  const lines = [];
  lines.push(`# WORK PACKET — ${o.id} [${phase}]`, "");
  lines.push(`lean_name: ${o.lean_name}`, `file: ${o.file}`, `kind: ${o.kind}`, `deps: ${o.deps.join(", ") || "none"}`, "");
  if (o.statement_tex) lines.push("## Statement (VERBATIM from frozen arXiv v4 — the ONLY authority)", "", "```latex", o.statement_tex, "```", "");
  if (o.spec) lines.push("## Spec / intent", "", o.spec, "");
  if (phase === "STATE") {
    lines.push("## Contract (STATE phase)",
      "- Author the Lean STATEMENT only (defs: the definition; lemmas: `theorem ... := by sorry`).",
      `- Wrap the statement in claim markers:`,
      "```", BEGIN(o.id), "<statement lines>", END(o.id), "```",
      "- General and faithful to the tex; no problem-specific tailoring beyond the paper.",
      "- Submit with: node pipeline/runner.mjs state " + o.id + " <file-containing-full-new-lean-file>",
      needsSignoff(o) ? "- SIGN-OFF REQUIRED (Simon) before proving starts." : "- aux-lemma: judge-only, no Simon sign-off (v1).");
  } else {
    lines.push("## Contract (PROVE phase)",
      "- The claim block is FROZEN (byte-identical check against claims/" + o.id.replace(/[:/]/g, "_") + ".txt). Touch only the proof body / add private helpers BELOW the claim block.",
      "- Claim blocks of OTHER obligations in the same file are frozen too.",
      "- No new axioms. No sorry for status=proved.",
      "- Submit with: node pipeline/runner.mjs submit " + o.id + " <file-containing-full-new-lean-file>");
  }
  lines.push("", "## Available context",
    "- Reuse layer: Workspace.* (artifact, verified; see formalization/reference-lean/REUSE-INVENTORY.md)",
    "- Existing NPCC modules in this repo: see NPCC/ directory",
    `- Prior attempts: ${o.attempts.length}${o.attempts.length ? " — " + o.attempts.map(a => a.note.split("\n")[0]).join(" | ").slice(0, 400) : ""}`);
  const p = path.join(PACKETS, o.id.replace(/[:/]/g, "_") + ".md");
  fs.writeFileSync(p, lines.join("\n") + "\n");
  return p;
}

// ---------- commands ----------
const [, , cmd, arg1, arg2] = process.argv;
const L = loadLedger();

if (cmd === "status") {
  const counts = {};
  for (const o of L.obligations) counts[o.status] = (counts[o.status] || 0) + 1;
  const attempts = L.obligations.reduce((s, o) => s + o.attempts.length, 0);
  const closed = L.obligations.filter(o => CLOSED.has(o.status)).length;
  const completion = L.obligations.length
    ? (closed / L.obligations.length * 100).toFixed(0) + "%"
    : "n/a";
  console.log(`target=${L.target} frozen=${L.dag_frozen} obligations=${L.obligations.length}`);
  console.log("counts:", JSON.stringify(counts));
  console.log(`proof attempts=${attempts}  obligations closed=${closed}/${L.obligations.length}  completion=${completion}`);
  for (const o of L.obligations)
    console.log(` ${o.status.padEnd(7)} ${String(o.attempts.length).padStart(2)}att ${o.signed_off ? "S" : (needsSignoff(o) ? "-" : "·")} ${o.id}${o.route ? "  [" + o.route + "]" : ""}`);
} else if (cmd === "next") {
  const o = L.obligations.find(x =>
    (x.status === "open" && depsClosed(L, x)) ||
    (x.status === "stated" && (!needsSignoff(x) || x.signed_off) && depsClosed(L, x)));
  if (!o) { console.log("no actionable obligation (check sign-offs / parked items)"); process.exit(0); }
  console.log("next:", o.id, "phase:", o.status === "open" ? "STATE" : "PROVE");
  console.log("packet:", emitPacket(L, o));
} else if (cmd === "state") {
  if (!arg1 || !arg2) die("usage: state <id> <file>");
  const o = byId(L, arg1);
  if (o.status !== "open") die(`state: ${o.id} is '${o.status}', expected 'open'`);
  const text = fs.readFileSync(arg2, "utf8");
  const claim = extractClaim(text, o.id);
  if (!claim) die("no claim block found for " + o.id);
  const clash = verifyRegisteredClaims(L, o.file, text, o.id);
  if (clash) die(`file write would alter registered claim of ${clash} — rejected`);
  const prev = fs.existsSync(path.join(ROOT, o.file)) ? fs.readFileSync(path.join(ROOT, o.file), "utf8") : null;
  fs.writeFileSync(path.join(ROOT, o.file), text);
  regenerateRoot();
  const v = lakeBuild();
  if (!v.ok) {
    if (prev !== null) fs.writeFileSync(path.join(ROOT, o.file), prev); else fs.rmSync(path.join(ROOT, o.file));
    regenerateRoot();
    route(L, o, "STATE compile failed:\n" + errHead(v.out));
    saveLedger(L);
    die("statement does not compile; file reverted; routed. Errors:\n" + errHead(v.out));
  }
  fs.writeFileSync(claimPath(o.id), claim);
  o.status = "stated";
  o.route = needsSignoff(o) && !o.signed_off ? "awaiting Simon sign-off (+ C5 judge)" : "ready to prove";
  saveLedger(L);
  console.log(`STATED ${o.id}; claim registered (${claim.length} bytes). ${o.route}`);
} else if (cmd === "signoff") {
  const o = byId(L, arg1 || die("usage: signoff <id>"));
  o.signed_off = true;
  if (o.route && o.route.startsWith("awaiting")) o.route = "ready to prove";
  saveLedger(L);
  console.log(`SIGNED ${o.id} (recorded; only do this after Simon's explicit yes)`);
} else if (cmd === "submit") {
  if (!arg1 || !arg2) die("usage: submit <id> <file>");
  const o = byId(L, arg1);
  if (o.status !== "stated") die(`submit: ${o.id} is '${o.status}', expected 'stated'`);
  if (needsSignoff(o) && !o.signed_off) die(`submit: ${o.id} awaits Simon sign-off`);
  const text = fs.readFileSync(arg2, "utf8");
  const claim = extractClaim(text, o.id);
  const registered = fs.readFileSync(claimPath(o.id), "utf8");
  if (canonicalClaim(claim) !== canonicalClaim(registered)) { // C3 gate (a): Claim Check
    route(L, o, "CLAIM-CHECK FAILED: statement block differs from registered claim");
    saveLedger(L);
    die("Claim Check failed: statement block was modified. Rejected.");
  }
  const clash = verifyRegisteredClaims(L, o.file, text, o.id);
  if (clash) {
    route(L, o, `CLAIM-CHECK FAILED: would alter registered claim of ${clash}`);
    saveLedger(L);
    die(`Claim Check failed: submission alters registered claim of ${clash}. Rejected.`);
  }
  const prev = fs.existsSync(path.join(ROOT, o.file)) ? fs.readFileSync(path.join(ROOT, o.file), "utf8") : null;
  fs.writeFileSync(path.join(ROOT, o.file), text);
  regenerateRoot();
  const v = lakeBuild();
  if (!v.ok) {
    if (prev !== null) fs.writeFileSync(path.join(ROOT, o.file), prev);
    regenerateRoot();
    route(L, o, "compile failed:\n" + errHead(v.out));
    saveLedger(L);
    die("compile failed; file reverted; routed:\n" + errHead(v.out));
  }
  if (usesSorry(text)) {
    route(L, o, "compiles but contains sorry");
    saveLedger(L);
    die("compiles but still contains sorry — not accepted as proved; routed.");
  }
  if (o.kind !== "def") { // C3 gate (b): axiom gate
    const ax = axiomCheck(o.lean_name);
    if (!ax.ok) {
      if (prev !== null) fs.writeFileSync(path.join(ROOT, o.file), prev);
      regenerateRoot();
      route(L, o, "AXIOM GATE FAILED: " + (ax.bad ? ax.bad.join(",") : ax.out.slice(0, 300)));
      saveLedger(L);
      die("axiom gate failed: " + (ax.bad ? "disallowed axioms " + ax.bad.join(", ") : "could not verify axioms"));
    }
    o.axioms = ax.axioms;
  }
  o.status = "proved";
  o.route = null;
  saveLedger(L);
  console.log(`PROVED ${o.id}${o.axioms ? "  axioms=[" + o.axioms.join(", ") + "]" : ""}`);
} else {
  die("usage: runner.mjs status|next|state <id> <file>|signoff <id>|submit <id> <file>");
}
