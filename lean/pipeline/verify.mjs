#!/usr/bin/env node

import fs from "node:fs";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const SITE = path.resolve(ROOT, "..");
const WITH_LEAN = process.argv.includes("--lean");
const failures = [];

function fail(message) {
  failures.push(message);
}

function check(condition, message) {
  if (!condition) fail(message);
}

function read(file) {
  return fs.readFileSync(file, "utf8");
}

function walk(dir) {
  if (!fs.existsSync(dir)) return [];
  return fs.readdirSync(dir, { withFileTypes: true }).flatMap((entry) => {
    const full = path.join(dir, entry.name);
    return entry.isDirectory() ? walk(full) : [full];
  });
}

function canonicalClaim(text) {
  return text.replace(/\r\n/g, "\n").replace(/\n$/, "");
}

function extractClaim(text, id) {
  const begin = `-- CLAIM-BEGIN ${id}`;
  const end = `-- CLAIM-END ${id}`;
  const escape = (value) => value.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const starts = [...text.matchAll(new RegExp(`^${escape(begin)}\\r?$`, "gm"))];
  const ends = [...text.matchAll(new RegExp(`^${escape(end)}\\r?$`, "gm"))];
  if (starts.length !== 1 || ends.length !== 1 || ends[0].index <= starts[0].index) return null;
  return text.slice(starts[0].index, ends[0].index + end.length);
}

function stripLeanNoise(text) {
  let out = "";
  let state = "code";
  let depth = 0;
  let escaped = false;
  for (let i = 0; i < text.length; i += 1) {
    const c = text[i];
    const n = text[i + 1];
    if (state === "line") {
      if (c === "\n") {
        state = "code";
        out += "\n";
      } else out += " ";
      continue;
    }
    if (state === "block") {
      if (c === "/" && n === "-") {
        depth += 1;
        out += "  ";
        i += 1;
      } else if (c === "-" && n === "/") {
        depth -= 1;
        out += "  ";
        i += 1;
        if (depth === 0) state = "code";
      } else out += c === "\n" ? "\n" : " ";
      continue;
    }
    if (state === "string") {
      if (escaped) escaped = false;
      else if (c === "\\") escaped = true;
      else if (c === '"') state = "code";
      out += c === "\n" ? "\n" : " ";
      continue;
    }
    if (c === "-" && n === "-") {
      state = "line";
      out += "  ";
      i += 1;
    } else if (c === "/" && n === "-") {
      state = "block";
      depth = 1;
      out += "  ";
      i += 1;
    } else if (c === '"') {
      state = "string";
      escaped = false;
      out += " ";
    } else out += c;
  }
  return out;
}

function moduleName(base, file) {
  const rel = path.relative(ROOT, file).replace(/\\/g, "/").replace(/\.lean$/, "");
  return rel.split("/").join(".");
}

function importedModules(rootFile) {
  return new Set(
    [...read(path.join(ROOT, rootFile)).matchAll(/^import\s+(\S+)/gm)].map((m) => m[1]),
  );
}

function verifyImportCoverage(dir, rootFile) {
  const files = walk(path.join(ROOT, dir)).filter((file) => file.endsWith(".lean"));
  const imports = importedModules(rootFile);
  const missing = files.map((file) => moduleName(dir, file)).filter((name) => !imports.has(name));
  check(missing.length === 0, `${rootFile} misses modules: ${missing.join(", ")}`);
}

function extractJsonScript(html, id) {
  const marker = `<script id="${id}" type="application/json">`;
  const start = html.indexOf(marker);
  const end = html.indexOf("</script>", start + marker.length);
  if (start < 0 || end < 0) throw new Error(`missing JSON script ${id}`);
  return html.slice(start + marker.length, end);
}

function proofMapTargets(html) {
  const nav = html.match(/<nav class="proofmap"[\s\S]*?<\/nav>/);
  if (!nav) return [];
  return [...nav[0].matchAll(/data-target="([^"]+)"/g)].map((match) => match[1]);
}

function run(command, args) {
  const result = spawnSync(command, args, {
    cwd: ROOT,
    encoding: "utf8",
    shell: false,
    maxBuffer: 64 * 1024 * 1024,
  });
  if (result.status !== 0) {
    fail(`${command} ${args.join(" ")} failed:\n${result.stdout || ""}${result.stderr || ""}`);
  }
  return `${result.stdout || ""}${result.stderr || ""}`;
}

function findPython() {
  const candidates = process.platform === "win32"
    ? [["python", []], ["py", ["-3"]], ["python3", []]]
    : [["python3", []], ["python", []]];
  for (const [command, prefix] of candidates) {
    const probe = spawnSync(command, [...prefix, "--version"], {
      cwd: ROOT,
      encoding: "utf8",
      shell: false,
    });
    if (probe.status === 0) return { command, prefix };
  }
  return null;
}

// Ledger and frozen claim blocks.
const ledger = JSON.parse(read(path.join(ROOT, "obligations.json")));
check(Array.isArray(ledger.obligations), "obligations.json has no obligations array");
if (Array.isArray(ledger.obligations)) {
  check(ledger.obligations.length === 126, `expected 126 obligations, found ${ledger.obligations.length}`);
  const ids = new Set();
  for (const obligation of ledger.obligations) {
    check(!ids.has(obligation.id), `duplicate obligation id ${obligation.id}`);
    ids.add(obligation.id);
    check(obligation.status === "proved", `${obligation.id} has status ${obligation.status}`);
    const sourcePath = path.join(ROOT, obligation.file);
    const claimPath = path.join(ROOT, "claims", obligation.id.replace(/[:/]/g, "_") + ".txt");
    if (!fs.existsSync(sourcePath)) {
      fail(`${obligation.id} source is missing: ${obligation.file}`);
      continue;
    }
    if (!fs.existsSync(claimPath)) {
      fail(`${obligation.id} registered claim is missing`);
      continue;
    }
    const block = extractClaim(read(sourcePath), obligation.id);
    if (block === null) fail(`${obligation.id} has missing or duplicate claim markers`);
    else if (canonicalClaim(block) !== canonicalClaim(read(claimPath))) {
      fail(`${obligation.id} source block differs from its registered claim`);
    }
  }
}

// Source-level trust checks.
const leanFiles = ["NPCC", "Workspace", "Tests"]
  .flatMap((dir) => walk(path.join(ROOT, dir)))
  .filter((file) => file.endsWith(".lean"));
const directAxioms = [];
for (const file of leanFiles) {
  const stripped = stripLeanNoise(read(file));
  if (/\b(sorry|admit)\b/.test(stripped)) fail(`executable sorry/admit in ${path.relative(ROOT, file)}`);
  if (/^\s*unsafe\s+(?:def|theorem|abbrev|opaque)\b/m.test(stripped)) {
    fail(`source unsafe declaration in ${path.relative(ROOT, file)}`);
  }
  for (const match of stripped.matchAll(/^\s*axiom\s+([A-Za-z0-9_'.]+)/gm)) {
    directAxioms.push(match[1]);
  }
}
check(
  directAxioms.length === 1 && directAxioms[0] === "finite_alphabet_balanced_family_exists",
  `direct project axioms are [${directAxioms.join(", ")}]`,
);

verifyImportCoverage("NPCC", "NPCC.lean");
verifyImportCoverage("Workspace", "Workspace.lean");
verifyImportCoverage("Tests", "Tests.lean");

const lakefile = read(path.join(ROOT, "lakefile.toml"));
check(
  /defaultTargets\s*=\s*\["NPCC",\s*"Workspace",\s*"Tests"\]/.test(lakefile),
  "default Lake targets do not cover NPCC, Workspace, and Tests",
);
check(!/name\s*=\s*"Npcc"/.test(lakefile), "stale case-sensitive Npcc library remains");

const tracked = spawnSync("git", ["ls-files", "lean"], { cwd: SITE, encoding: "utf8" });
if (tracked.status === 0) {
  check(!/(?:^|\n)lean\/Npcc(?:\/|\.lean)/.test(tracked.stdout), "tracked Npcc path breaks Linux imports");
  check(tracked.stdout.includes("lean/NPCC.lean"), "tracked root module is not lean/NPCC.lean");
} else fail("could not inspect tracked path casing with git ls-files");

const workflow = read(path.join(SITE, ".github", "workflows", "lean.yml"));
check(/os:\s*\[ubuntu-latest,\s*windows-latest\]/.test(workflow), "CI is not cross-platform");
check(/build-args:\s*NPCC Workspace Tests/.test(workflow), "CI does not build all Lean libraries");
check(/leanchecker:\s*true/.test(workflow), "CI does not run Lean's environment checker");
check(/node pipeline\/verify\.mjs --lean/.test(workflow), "CI does not run the full integrity verifier");

const python = findPython();
if (!python) fail("Python 3 is required to verify the downloadable release archive");
else run(python.command, [...python.prefix, "pipeline/package-release.py", "--check"]);

// Explorer/source synchronization.
const graphHtml = read(path.join(SITE, "index.html"));
const inspectorHtml = read(path.join(SITE, "inspector", "index.html"));
for (const [name, html] of [["graph", graphHtml], ["inspector", inspectorHtml]]) {
  check(html.includes("Lean-checked core · Lean 4"), `${name} has a stale verification headline`);
  check(!html.includes("Machine-verified · Lean 4"), `${name} retains the overbroad headline`);
  check(
    html.includes("choice-based threshold-gap equivalence, explicit and fixed-degree carrier/truth-table bounds in |V|+|E|+1, and square power-of-two padding preserving D"),
    `${name} does not display the audited scope boundary`,
  );
  check(html.includes("one balanced-family citation axiom"), `${name} states the wrong project-axiom count`);
  check(html.includes("BALANCED-FAMILY-CITATION.md"), `${name} does not link the citation boundary`);
}
const graphDataRaw = extractJsonScript(graphHtml, "data");
const inspectorDataRaw = extractJsonScript(inspectorHtml, "data");
check(graphDataRaw === inspectorDataRaw, "the two explorers contain different graph data");
const graphProofMap = proofMapTargets(graphHtml);
const inspectorProofMap = proofMapTargets(inspectorHtml);
check(graphProofMap.length >= 6, `graph proof map has only ${graphProofMap.length} steps`);
check(
  JSON.stringify(graphProofMap) === JSON.stringify(inspectorProofMap),
  "the two explorers contain different proof maps",
);
check(graphProofMap.at(-1) === "thm:padded-gap", "proof map does not end at the padded gap theorem");

let graphData;
try {
  graphData = JSON.parse(graphDataRaw);
} catch (error) {
  fail(`graph data is invalid JSON: ${error.message}`);
}
if (graphData) {
  check(graphData.nodes.length === graphData.meta.nodes, "graph node count differs from metadata");
  check(graphData.meta.counts?.axioms === 1, "graph metadata states the wrong axiom count");
  const graphIds = new Set(graphData.nodes.map((node) => node.id));
  for (const target of graphProofMap) {
    check(graphIds.has(target), `proof map target ${target} is not a graph node`);
  }
  for (const node of graphData.nodes) {
    const sourcePath = path.join(ROOT, node.file);
    if (!fs.existsSync(sourcePath)) {
      fail(`${node.id} records missing source ${node.file}`);
      continue;
    }
    const source = read(sourcePath).replace(/\r\n/g, "\n");
    const statement = String(node.leanStmt || "").replace(/\r\n/g, "\n");
    check(statement.length > 0 && source.includes(statement), `${node.id} embedded statement is stale`);
    check(
      !statement.includes("-- CLAIM-BEGIN") && !statement.includes("-- CLAIM-END"),
      `${node.id} exposes internal claim sentinels in the reader-facing statement`,
    );
  }
}

let explainers;
try {
  explainers = JSON.parse(extractJsonScript(inspectorHtml, "explainers"));
} catch (error) {
  fail(`inspector explainers are invalid JSON: ${error.message}`);
}
if (graphData && explainers) {
  const nodesById = Object.fromEntries(graphData.nodes.map((node) => [node.id, node]));
  for (const [id, items] of Object.entries(explainers)) {
    const node = nodesById[id];
    check(Boolean(node), `explainer set ${id} has no graph node`);
    if (!node) continue;
    const lineCount = String(node.leanStmt || "").split("\n").length;
    let previousLine = -1;
    for (const item of items) {
      check(
        Number.isInteger(item.line) && item.line >= 0 && item.line < lineCount,
        `${id}/${item.label || "unnamed"} has an out-of-range line anchor`,
      );
      check(item.line >= previousLine, `${id} explainer anchors are not sorted`);
      check(Boolean(item.label && item.concept), `${id} has an incomplete explainer`);
      previousLine = item.line;
    }
  }

  const auditPath = path.join(ROOT, "pipeline", "explainer-audit.json");
  let audit;
  try {
    audit = JSON.parse(read(auditPath));
  } catch (error) {
    fail(`explainer audit manifest is invalid: ${error.message}`);
  }
  if (audit) {
    check(audit.schema === 1, `unsupported explainer audit schema ${audit.schema}`);
    check(
      audit.corrections?.length === audit.audit?.changedExplainers,
      "explainer audit correction count differs from its metadata",
    );
    const changedNodes = new Set();
    const fieldChanges = { line: 0, concept: 0, label: 0 };
    for (const correction of audit.corrections || []) {
      changedNodes.add(correction.node);
      const node = nodesById[correction.node];
      const finalLabel = correction.label || correction.matchLabel;
      const item = (explainers[correction.node] || [])
        .find((entry) => entry.label === finalLabel);
      check(Boolean(node), `audited explainer has no graph node ${correction.node}`);
      check(Boolean(item), `audited explainer is missing ${correction.node}/${finalLabel}`);
      if (!node || !item) continue;
      if (correction.anchor) {
        fieldChanges.line += 1;
        const positions = String(node.leanStmt || "")
          .split("\n")
          .flatMap((line, index) => line.trim() === correction.anchor ? [index] : []);
        const expected = positions[(correction.occurrence || 1) - 1];
        check(
          item.line === expected,
          `${correction.node}/${finalLabel} is not on its audited source line`,
        );
      }
      if (correction.concept) {
        fieldChanges.concept += 1;
        check(
          item.concept === correction.concept,
          `${correction.node}/${finalLabel} lost its audited explanation`,
        );
      }
      if (correction.label) {
        fieldChanges.label += 1;
        check(item.label === correction.label, `${correction.node} lost its audited label`);
      }
      if (correction.concept || correction.label) {
        check(
          item.audit === audit.audit?.date,
          `${correction.node}/${finalLabel} lost its audit marker`,
        );
      }
    }
    check(
      changedNodes.size === audit.audit?.changedNodes,
      `explainer audit covers ${changedNodes.size} nodes, expected ${audit.audit?.changedNodes}`,
    );
    for (const field of Object.keys(fieldChanges)) {
      check(
        fieldChanges[field] === audit.audit?.fieldChanges?.[field],
        `explainer audit ${field} count is ${fieldChanges[field]}, expected ` +
          `${audit.audit?.fieldChanges?.[field]}`,
      );
    }
    check(
      inspectorHtml.includes(
        "if(block && !block.audit && Object.prototype.hasOwnProperty.call(overrides, block.label)){",
      ),
      "runtime clarity overrides can replace audited explanations",
    );
  }
}

let glossary;
try {
  glossary = JSON.parse(extractJsonScript(inspectorHtml, "gloss"));
} catch (error) {
  fail(`inspector glossary is invalid JSON: ${error.message}`);
}
if (glossary) {
  let localCards = 0;
  let exactCards = 0;
  for (const [name, declaration] of Object.entries(glossary.decls || {})) {
    const sourcePath = path.join(ROOT, declaration.file || "");
    if (!declaration.code || !fs.existsSync(sourcePath)) continue;
    localCards += 1;
    if (read(sourcePath).replace(/\r\n/g, "\n").includes(declaration.code.replace(/\r\n/g, "\n"))) {
      exactCards += 1;
    } else fail(`glossary code for ${name} is not an exact source substring`);
  }
  check(localCards > 1000, `unexpectedly few local glossary cards: ${localCards}`);
  check(exactCards === localCards, `only ${exactCards}/${localCards} local glossary cards match source`);
}

// Kernel-level checks are intentionally optional for fast static runs.
if (WITH_LEAN) {
  const axiomOutput = run("lake", ["env", "lean", "AxiomReport.lean"]);
  const wrapperOutput = run("lake", ["env", "lean", "wrapper_check.lean"]);
  const allOutput = `${axiomOutput}\n${wrapperOutput}`;
  check(!allOutput.includes("sorryAx"), "axiom reports contain sorryAx");
  const allowed = new Set([
    "propext",
    "Classical.choice",
    "NPCC.finite_alphabet_balanced_family_exists",
    "Quot.sound",
  ]);
  const reports = new Map(
    [...allOutput.matchAll(/'([^']+)' depends on axioms:\s*\[([^\]]*)\]/g)].map((m) => [
      m[1],
      m[2].split(",").map((item) => item.trim()).filter(Boolean),
    ]),
  );
  check(reports.size >= 12, `expected at least 12 named axiom reports, found ${reports.size}`);
  for (const footprint of reports.values()) {
    const unexpected = footprint.filter((axiom) => !allowed.has(axiom));
    check(unexpected.length === 0, `unexpected transitive axioms: ${unexpected.join(", ")}`);
  }
  const normalized = (items) => [...items].sort().join("|");
  const expectedMain = normalized(allowed);
  const expectedClassical = normalized(["propext", "Classical.choice", "Quot.sound"]);
  const exactFootprint = (name, expected) => {
    const actual = reports.get(name);
    check(Boolean(actual), `missing axiom report for ${name}`);
    if (actual) check(normalized(actual) === expected, `${name} has the wrong axiom footprint`);
  };
  for (const name of [
    "NPCC.main_np_hardness",
    "NPCC.fourColorable_iff_gapMatrix_cost_le",
    "NPCC.not_fourColorable_iff_gapMatrix_cost_at_least_one_more",
    "NPCC.fourColorable_iff_gapTruthTable_cost_le",
    "NPCC.not_fourColorable_iff_gapTruthTable_cost_at_least_one_more",
    "NPCC.gapTruthTable_cost",
    "NPCC.reduction_gap",
    "NPCC.output_size_bounds",
  ]) exactFootprint(name, expectedMain);
  exactFootprint("NPCC.vbp_np_hard", expectedClassical);
  for (const name of [
    "Workspace.MainTheorem.refutation_of_direct_sum_conjecture",
    "Workspace.MainTheorem.multiplicative_consequence",
    "Workspace.MainTheorem.complexity_invariant_to_transposition",
    "Workspace.MainTheorem.subgames_are_easier",
  ]) exactFootprint(name, expectedClassical);

  if (graphData) {
    const names = [...new Set(graphData.nodes.map((node) => node.lean).filter(Boolean))];
    const checkFile = path.join(ROOT, "pipeline", "tmp", "AuditGraphNames.lean");
    fs.mkdirSync(path.dirname(checkFile), { recursive: true });
    fs.writeFileSync(checkFile, `import NPCC\nimport Workspace\n${names.map((name) => `#check ${name}`).join("\n")}\n`);
    run("lake", ["env", "lean", checkFile]);
    fs.rmSync(checkFile, { force: true });
  }
}

if (failures.length) {
  console.error(`INTEGRITY CHECK FAILED (${failures.length})`);
  for (const message of failures) console.error(`- ${message}`);
  process.exit(1);
}

console.log(`Integrity check passed: ${ledger.obligations.length} claims, ${leanFiles.length} Lean modules, ${graphData?.nodes.length || 0} graph nodes.`);
if (!WITH_LEAN) console.log("Kernel checks skipped; rerun with --lean for axiom and identifier verification.");
