#!/usr/bin/env node

import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const SITE = path.resolve(ROOT, "..");
const graphPath = path.join(SITE, "index.html");
const inspectorPath = path.join(SITE, "inspector", "index.html");
const explainerAuditPath = path.join(ROOT, "pipeline", "explainer-audit.json");

function read(file) {
  return fs.readFileSync(file, "utf8");
}

function jsonScript(html, id) {
  const marker = `<script id="${id}" type="application/json">`;
  const start = html.indexOf(marker);
  const end = html.indexOf("</script>", start + marker.length);
  if (start < 0 || end < 0) throw new Error(`missing JSON script ${id}`);
  return {
    value: JSON.parse(html.slice(start + marker.length, end)),
    replace(value) {
      return html.slice(0, start + marker.length) + JSON.stringify(value) + html.slice(end);
    },
  };
}

function replaceJsonScript(html, id, value) {
  const marker = `<script id="${id}" type="application/json">`;
  const start = html.indexOf(marker);
  const end = html.indexOf("</script>", start + marker.length);
  if (start < 0 || end < 0) throw new Error(`missing JSON script ${id}`);
  return html.slice(0, start + marker.length) + JSON.stringify(value) + html.slice(end);
}

function extractClaim(text, id) {
  const begin = `-- CLAIM-BEGIN ${id}`;
  const end = `-- CLAIM-END ${id}`;
  const escape = (value) => value.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const starts = [...text.matchAll(new RegExp(`^${escape(begin)}\\r?$`, "gm"))];
  const ends = [...text.matchAll(new RegExp(`^${escape(end)}\\r?$`, "gm"))];
  if (starts.length !== 1 || ends.length !== 1 || ends[0].index <= starts[0].index) {
    return null;
  }
  // Claim sentinels belong to the pipeline, not to the Lean statement shown to
  // readers. Explainer line coordinates are zero-based within this body.
  return text
    .slice(starts[0].index + starts[0][0].length, ends[0].index)
    .replace(/^\r?\n/, "")
    .replace(/\r?\n$/, "");
}

function maskUnicode(text) {
  return text.replace(/[^\x00-\x7f]/g, "?");
}

function sourcePath(recorded) {
  return path.join(ROOT, String(recorded || "").replace(/^Npcc\//, "NPCC/"));
}

function lineAt(text, offset) {
  return text.slice(0, offset).split("\n").length;
}

function lineContaining(text, needle) {
  const index = text.indexOf(needle);
  if (index < 0) throw new Error(`could not find displayed line containing ${needle}`);
  return lineAt(text, index) - 1;
}

function stripClaimSentinels(text) {
  const lines = String(text || "").replace(/\r\n/g, "\n").split("\n");
  if (/^-- CLAIM-BEGIN\s+/.test(lines[0] || "")) lines.shift();
  if (/^-- CLAIM-END\s+/.test(lines.at(-1) || "")) lines.pop();
  return lines.join("\n");
}

function remapExplainerLines(items, previousText, nextText) {
  if (!items?.length) return;
  const oldLines = stripClaimSentinels(previousText).split("\n");
  const newLines = stripClaimSentinels(nextText).split("\n");
  if (oldLines.join("\n") === newLines.join("\n")) return;

  const key = (line) => line.trim();
  const newPositions = new Map();
  newLines.forEach((line, index) => {
    const value = key(line);
    const positions = newPositions.get(value) || [];
    positions.push(index);
    newPositions.set(value, positions);
  });
  const exactAnchors = [];
  oldLines.forEach((line, index) => {
    const positions = newPositions.get(key(line)) || [];
    if (positions.length === 1) exactAnchors.push([index, positions[0]]);
  });

  function estimatedPosition(oldIndex) {
    let before = null;
    let after = null;
    for (const anchor of exactAnchors) {
      if (anchor[0] <= oldIndex) before = anchor;
      if (anchor[0] >= oldIndex) {
        after = anchor;
        break;
      }
    }
    if (before && after && before[0] !== after[0]) {
      const fraction = (oldIndex - before[0]) / (after[0] - before[0]);
      return before[1] + fraction * (after[1] - before[1]);
    }
    if (before) return before[1] + oldIndex - before[0];
    if (after) return after[1] - (after[0] - oldIndex);
    return oldIndex * newLines.length / Math.max(1, oldLines.length);
  }

  for (const item of items) {
    if (!Number.isInteger(item.line) || item.line < 0 || item.line >= oldLines.length) continue;
    const estimate = estimatedPosition(item.line);
    const positions = newPositions.get(key(oldLines[item.line])) || [];
    const mapped = positions.length
      ? positions.reduce((best, position) =>
          Math.abs(position - estimate) < Math.abs(best - estimate) ? position : best)
      : Math.round(estimate);
    item.line = Math.max(0, Math.min(newLines.length - 1, mapped));
  }
}

function escapeRegExp(text) {
  return text.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

function currentDeclarationSnippet(source, fullName) {
  const shortName = fullName.split(".").at(-1);
  const declaration = new RegExp(
    `^(?:(?:private|protected|noncomputable|local)\\s+)*(?:theorem|lemma|def|abbrev|structure|class|inductive|opaque)\\s+(?:[A-Za-z0-9_'.]+\\.)*${escapeRegExp(shortName)}(?=[\\s.{])`,
    "m",
  );
  const match = declaration.exec(source);
  if (!match) return null;
  const start = match.index;
  const kind = match[0].match(/(?:theorem|lemma|def|abbrev|structure|class|inductive|opaque)/)?.[0];
  const rest = source.slice(start + match[0].length);
  const nextMatch = /\n(?=(?:(?:private|protected|noncomputable|local)\s+)*(?:theorem|lemma|def|abbrev|structure|class|inductive|opaque)\s+)/.exec(rest);
  const next = nextMatch ? start + match[0].length + nextMatch.index + 1 : source.length;
  if (["structure", "class", "inductive"].includes(kind)) {
    return { start, code: source.slice(start, next).trimEnd() };
  }
  const assignment = source.indexOf(":=", start + match[0].length);
  if (assignment >= 0 && assignment < next) {
    return { start, code: source.slice(start, assignment).trimEnd() };
  }
  return { start, code: source.slice(start, next).trimEnd() };
}

function ensureGlossaryDeclaration(glossary, name, file, kind, plain, how) {
  if (glossary.decls[name]) return;
  const source = read(sourcePath(file)).replace(/\r\n/g, "\n");
  const current = currentDeclarationSnippet(source, name);
  if (!current) throw new Error(`could not add glossary declaration ${name}`);
  glossary.decls[name] = {
    kind,
    file,
    line: lineAt(source, current.start),
    doc: "",
    code: current.code,
    plain,
    how,
  };
}

function setConcept(explainers, id, label, concept) {
  const item = (explainers[id] || []).find((entry) => entry.label === label);
  if (!item) throw new Error(`missing explainer ${id}/${label}`);
  item.concept = concept;
}

function upsertConcept(explainers, id, label, line, concept) {
  const items = explainers[id] || (explainers[id] = []);
  const item = items.find((entry) => entry.label === label);
  if (item) Object.assign(item, { line, concept });
  else items.push({ line, label, concept });
  items.sort((left, right) => left.line - right.line);
}

function auditedAnchorLine(statement, anchor, occurrence) {
  const positions = String(statement || "")
    .split("\n")
    .flatMap((line, index) => line.trim() === anchor ? [index] : []);
  const target = positions[occurrence - 1];
  if (!Number.isInteger(target)) {
    throw new Error(
      `audited explainer anchor ${JSON.stringify(anchor)} occurrence ${occurrence} ` +
      `was not found`,
    );
  }
  return target;
}

function applyExplainerAudit(explainers, nodesById, audit) {
  if (audit.schema !== 1 || !Array.isArray(audit.corrections)) {
    throw new Error("invalid explainer audit manifest");
  }
  if (audit.corrections.length !== audit.audit?.changedExplainers) {
    throw new Error("explainer audit correction count differs from its metadata");
  }

  const touched = new Set();
  for (const correction of audit.corrections) {
    const node = nodesById[correction.node];
    if (!node) throw new Error(`audited explainer has no node ${correction.node}`);
    const items = explainers[correction.node] || [];
    const finalLabel = correction.label || correction.matchLabel;
    const item = items.find((entry) => entry.label === correction.matchLabel) ||
      items.find((entry) => entry.label === finalLabel);
    if (!item) {
      throw new Error(
        `missing audited explainer ${correction.node}/${correction.matchLabel}`,
      );
    }
    if (correction.anchor) {
      item.line = auditedAnchorLine(
        node.leanStmt,
        correction.anchor,
        correction.occurrence || 1,
      );
    }
    if (correction.label) item.label = correction.label;
    if (correction.concept) item.concept = correction.concept;
    if (correction.label || correction.concept) {
      item.audit = audit.audit?.date || true;
    }
    touched.add(correction.node);
  }
  for (const id of touched) {
    explainers[id].sort((left, right) => left.line - right.line);
  }
}

let graphHtml = read(graphPath);
let inspectorHtml = read(inspectorPath);
const data = jsonScript(graphHtml, "data").value;
const explainers = jsonScript(inspectorHtml, "explainers").value;

const paddedGapId = "thm:padded-gap";
const fixedSizeId = "thm:fixed-degree-size";
const claimIdAliases = {
  "def:equipartition": "def:equipartition-ge",
  "def:bracket": "def:bracket-ge",
};
const paddedGapSource = read(path.join(ROOT, "NPCC", "Public.lean")).replace(/\r\n/g, "\n");
const paddedGapClaim = extractClaim(paddedGapSource, paddedGapId);
if (!paddedGapClaim) throw new Error(`missing claim ${paddedGapId}`);
let paddedGapNode = data.nodes.find((node) => node.id === paddedGapId);
if (!paddedGapNode) {
  paddedGapNode = {
    id: paddedGapId,
    kind: "lemma",
    status: "proved",
    lean: "NPCC.fourColorable_iff_gapTruthTable_cost_le",
    file: "NPCC/Public.lean",
    deps: ["thm:main-nphard-intro"],
    tex: null,
    texLine: null,
    leanStmt: paddedGapClaim,
    paper: null,
    title: "Square Truth-Table Gap",
    summary: "Pads the typed rectangular reduction matrix to a square Boolean truth table with power-of-two side length. Lean proves that the padding only duplicates rows and columns, preserves deterministic communication complexity exactly, and therefore preserves both directions of the one-bit threshold gap.",
    spine: true,
    paperDeps: [],
    dependents: [],
    paperDependents: [],
    x: 7016,
    y: 46,
    level: 24,
    sx: 7476,
    sy: 46,
  };
  data.nodes.push(paddedGapNode);
  data.meta.nodes += 1;
  data.meta.edges_full += 1;
  data.meta.edges_spine += 1;
  data.meta.spine_nodes += 1;
  data.meta.counts.proved += 1;
  const main = data.nodes.find((node) => node.id === "thm:main-nphard-intro");
  if (main && !main.dependents.includes(paddedGapId)) main.dependents.push(paddedGapId);
}
paddedGapNode.leanStmt = paddedGapClaim;

const fixedSizeSource = read(path.join(ROOT, "NPCC", "Wrapper.lean")).replace(/\r\n/g, "\n");
const fixedSizeClaim = extractClaim(fixedSizeSource, fixedSizeId);
if (!fixedSizeClaim) throw new Error(`missing claim ${fixedSizeId}`);
const fixedSizeDeps = ["lem:polytime", "aux:ctor-full", "axiom:vbp-np-hard"];
let fixedSizeNode = data.nodes.find((node) => node.id === fixedSizeId);
if (!fixedSizeNode) {
  fixedSizeNode = {
    id: fixedSizeId,
    kind: "lemma",
    status: "proved",
    lean: "NPCC.main_output_size_fixed_degree",
    file: "NPCC/Wrapper.lean",
    deps: fixedSizeDeps,
    tex: null,
    texLine: null,
    leanStmt: fixedSizeClaim,
    paper: null,
    title: "Fixed-Degree Output Bound",
    summary: "Proves that one explicit polynomial with an absolute exponent bounds both typed carriers in |V|+|E|+1. NPCC.Public then derives a fixed-degree bound for the number of bits in the final square truth table.",
    spine: true,
    paperDeps: [],
    dependents: [],
    paperDependents: [],
    x: 7016,
    y: 100,
    level: 24,
    sx: 7476,
    sy: 100,
  };
  data.nodes.push(fixedSizeNode);
  data.meta.nodes += 1;
  data.meta.edges_full += fixedSizeDeps.length;
  data.meta.edges_spine += 2;
  data.meta.spine_nodes += 1;
  data.meta.counts.proved += 1;
}
Object.assign(fixedSizeNode, {
  lean: "NPCC.main_output_size_fixed_degree",
  file: "NPCC/Wrapper.lean",
  deps: fixedSizeDeps,
  leanStmt: fixedSizeClaim,
  title: "Fixed-Degree Output Bound",
  summary: "Proves that one explicit polynomial with an absolute exponent bounds both typed carriers in |V|+|E|+1. NPCC.Public then derives a fixed-degree bound for the number of bits in the final square truth table.",
});
for (const dependencyId of fixedSizeDeps) {
  const dependency = data.nodes.find((node) => node.id === dependencyId);
  if (dependency && !dependency.dependents.includes(fixedSizeId)) {
    dependency.dependents.push(fixedSizeId);
  }
}

for (const node of data.nodes) {
  node.file = String(node.file).replace(/^Npcc\//, "NPCC/");
  const file = sourcePath(node.file);
  if (!fs.existsSync(file)) throw new Error(`${node.id}: missing ${node.file}`);
  const source = read(file).replace(/\r\n/g, "\n");
  const claim = extractClaim(source, claimIdAliases[node.id] || node.id);
  if (claim) {
    remapExplainerLines(explainers[node.id], node.leanStmt, claim);
    node.leanStmt = claim;
  }
}

const nodeById = Object.fromEntries(data.nodes.map((node) => [node.id, node]));
nodeById["lem:lambda-row-step"].lean = "Workspace.Appendix.lemma_A3_row_ladder_step";
nodeById["lem:one-step-partition"].lean = "NPCC.one_step_partition";
nodeById["def:scaffold-params"].lean = "NPCC.Params.q1";
nodeById["def:stage-matrices"].lean = "NPCC.M0";

nodeById["thm:main-nphard-intro"].title = "Checked Communication-Gap Construction";
nodeById["thm:main-nphard-intro"].summary =
  "For every loopless edge-list graph G, Lean constructs the typed matrix M4, proves the VBP promise, explicit source and scale bounds, one fixed-degree carrier polynomial in |V|+|E|+1, and G.IsYes iff D(M4) <= B_yes. NPCC.Public square-pads M4 without changing D and proves a fixed-degree truth-table bit bound. Serialized-language encodings, executable construction time, target NP membership, and source NP-hardness remain external.";
nodeById["axiom:aghp"].summary =
  "The sole project citation axiom. It supplies the arbitrary-finite-alphabet, relative-error indexed family and explicit cardinality bound consumed by Lean. AGHP is the historical binary source; the exact finite-alphabet corollary is sourced through Bshouty's derandomized Chernoff sampler and arbitrary-alphabet extension. The parameter translation is documented explicitly; executable generation and runtime remain external.";
nodeById[paddedGapId].summary =
  "Pads the typed rectangular reduction matrix to a square Boolean truth table with power-of-two side length. Lean proves that the padding only duplicates rows and columns, preserves deterministic communication complexity exactly, and therefore preserves both directions of the one-bit threshold gap.";
nodeById["axiom:vbp-np-hard"].summary =
  "A proved source correctness map, not a live axiom: one vector per vertex and one coordinate per edge. Lean proves the promise, 4-colourable iff packable, and elementary item/dimension/presentation-size bounds. A bit encoding, polynomial-time machine, and the known NP-hardness of 4-Colouring remain external.";
nodeById["lem:polytime"].summary =
  "Proves the exact carrier bounds |R4| <= n + rowPoly(d) and |C4| <= colPoly(d). The companion theorem main_output_size_fixed_degree proves that one absolute exponent bounds both carriers in |V|+|E|+1. Executable construction time and the bridge to serialized source and target languages remain external.";
nodeById["thm:Extension"].summary =
  "The quantitative transfer theorem. Start with a matrix whose hardness survives column loss and a hard classical interlace seed. Balanced projections then force every sufficiently row-spread, column-dense extraction of the relaxed interlace to retain complexity at least D(M) + log q. This is how the proof amplifies a seed lower bound into the stage matrices used by the reduction.";
nodeById["thm:SeparationTheorem"].summary =
  "The rigidity companion to Extension. Under robustness and the same transfer hypotheses, any protocol that meets the tight depth budget must spend its first log q bits on Alice's outer-block information along every surviving input-realizable branch. The induced transcript partition has one dominant block per part. Later stages use this forced prefix structure, not merely the numerical lower bound.";
nodeById["lem:scaffold-completeness"].summary =
  "The YES direction of the reduction. A canonical feasible four-bin packing gives an explicit three-phase protocol: Alice identifies the bin in 2 bits, Bob identifies the dimension block in ceil(log q2) bits, and the remaining capacity gadget costs at most Bcap. Hence D(M4) <= Byes. The zero anchors ensure the witness is canonical, while feasibility is the load-bearing hypothesis for this upper bound.";
nodeById["lem:MFourNoWasteLift"].summary =
  "The structural heart of the NO direction. Assuming a protocol of cost at most Byes, it reconstructs four transcript bins, proves that the first two bits are Alice bits, identifies Bob's dimension prefix, and exposes a residual local branch with budget at most Bcap. The zero-anchor overload then forces that branch to need at least Bcap + 1, yielding the contradiction used by reduction_gap.";
nodeById["thm:reduction-gap"].summary =
  "The exact promised-instance gap. If the vector-bin-packing instance is feasible, scaffold_completeness gives D(M4) <= Byes. If it is infeasible, the no-waste lift and local threshold theorem give Byes < D(M4), equivalently Byes + 1 <= D(M4) because D is natural-valued. Thus both directions of the one-bit threshold equivalence are present, not just a YES upper bound or a NO lower bound in isolation.";
nodeById["lem:relaxed-to-classical"].summary =
  "The combinatorial bridge behind both black boxes. Balancedness limits how many family indices share one projection, so a dense set of relaxed columns must contain many distinct classical column patterns. Choosing one realizing index per pattern transfers rows, columns, and protocol subtrees to a classical bracket while losing only the factor 1 + eps in column density.";
if (nodeById["aux:ctor-full"]) {
  nodeById["aux:ctor-full"].summary =
    "Selects a sufficiently large power-of-two construction scale and packages the numerical gates used by the reduction. Its linear bound in the preprocessed dimension feeds the checked fixed-degree output theorem. The certificate is choice-based; it does not by itself provide executable construction code or a running-time proof.";
}

graphHtml = replaceJsonScript(graphHtml, "data", data);
inspectorHtml = replaceJsonScript(inspectorHtml, "data", data);

upsertConcept(
  explainers,
  paddedGapId,
  "square padded target",
  lineContaining(nodeById[paddedGapId].leanStmt, "fourColorable_iff_gapTruthTable_cost_le"),
  "This is the conventional decision-problem target: a square Boolean table indexed by equally long binary inputs. The padding map is proved surjective and only duplicates existing rows and columns.",
);
upsertConcept(
  explainers,
  paddedGapId,
  "YES threshold direction",
  lineContaining(nodeById[paddedGapId].leanStmt, "G.IsYes <->"),
  "A graph is 4-colourable exactly when the padded truth table has deterministic communication complexity at most the displayed budget. This is an iff, not merely completeness.",
);
upsertConcept(
  explainers,
  fixedSizeId,
  "the theorem signature",
  lineContaining(nodeById[fixedSizeId].leanStmt, "theorem main_output_size_fixed_degree"),
  "This is the checked asymptotic statement: the degree and coefficients are absolute constants, independent of the graph. The input yardstick here is the explicit combinatorial size |V|+|E|+1.",
);
upsertConcept(
  explainers,
  fixedSizeId,
  "Alice carrier bound",
  lineContaining(nodeById[fixedSizeId].leanStmt, "Fintype.card\n        (R4"),
  "The row carrier of the final typed matrix is bounded by sourceCarrierPolynomial. The proof combines the exact row formula with the cancellation a(d)*t2(d) <= 24*log2(d), so the exponent no longer depends on the instance.",
);
upsertConcept(
  explainers,
  fixedSizeId,
  "Bob carrier bound",
  lineContaining(nodeById[fixedSizeId].leanStmt, "Fintype.card (C4"),
  "The same explicit polynomial bounds the column carrier. A later theorem in NPCC.Public uses these two bounds and power-of-two padding to bound the complete square truth-table bit count.",
);
upsertConcept(
  explainers,
  paddedGapId,
  "NO one-more-bit direction",
  lineContaining(nodeById[paddedGapId].leanStmt, "Not G.IsYes"),
  "Because costs are natural numbers, failure of the YES threshold is equivalent to needing at least one additional bit. The theorem is a lower bound, not an assertion that every NO instance has exactly that cost.",
);
setConcept(
  explainers,
  "thm:reduction-gap",
  "YES side of the gap",
  "For every promised vector-bin-packing input, a feasible packing constructs a protocol whose cost is at most Byes. This is the completeness half of the threshold gap.",
);
setConcept(
  explainers,
  "thm:reduction-gap",
  "NO side of the gap",
  "For the same promised input, infeasibility forces Byes < D(M4). Since D is a natural number, this is exactly the at-least-one-more-bit statement Byes + 1 <= D(M4).",
);
{
  const statement = nodeById["thm:reduction-gap"].leanStmt;
  const byLabel = Object.fromEntries(
    explainers["thm:reduction-gap"].map((item) => [item.label, item]),
  );
  byLabel["the theorem signature"].line = lineContaining(statement, "theorem reduction_gap");
  byLabel["YES side of the gap"].line = lineContaining(statement, "(I.IsYes →");
  byLabel["YES upper bound"].line = lineContaining(statement, "D (M4 (ctorScaleFull I)");
  byLabel["NO side of the gap"].line = lineContaining(statement, "(¬ I.IsYes →");
  byLabel["NO lower bound"].line = lineContaining(statement, "Byes (ctorScaleFull I) < D");
  explainers["thm:reduction-gap"].sort((left, right) => left.line - right.line);
}
setConcept(
  explainers,
  "lem:coord-projection",
  "row equipartition hypothesis",
  "Assumes that every selected block q in Q contributes at least T rows. No equality or even spreading between blocks is required.",
);
setConcept(
  explainers,
  "lem:new-partition",
  "base density hypothesis",
  "Assumes the minimum deterministic communication complexity Dfamily of the indicated bracket family is at least 1. Dfamily is a complexity minimum, not a density measure.",
);
setConcept(
  explainers,
  "lem:new-partition",
  "scalar conclusion",
  "Compares the three-rung family-complexity quantity LambdaGE before and after amplification. The parameters are densities; LambdaGE itself is a communication-complexity lower bound.",
);
setConcept(
  explainers,
  "lem:mono",
  "the conclusion",
  "Concludes that the minimum family communication complexity DSet at the weaker parameters is at most the value at the stronger parameters. This is monotonicity of a complexity minimum, not a density statistic.",
);
setConcept(
  explainers,
  "lem:M1LowColumnStage2",
  "row equipartition hypothesis",
  "The selected set Q has the required cardinality, and every block indexed by Q contributes at least one row. The condition does not say that row counts are equal across Q.",
);
setConcept(
  explainers,
  "thm:Extension",
  "submatrix conditions and conclusion",
  "Choose any relaxed-interlace extraction whose selected rows cover exactly r*pseed outer blocks at the required per-block threshold and whose selected columns retain at least an h fraction of the family. The transfer argument converts this density into a classical hard seed, yielding D(extraction) >= D(f) + log q. This is a universal hardness statement about all such extractions.",
);
setConcept(
  explainers,
  "thm:SeparationTheorem",
  "theorem signature",
  "States a rigidity theorem for protocols on a dense-column restriction of the full-row relaxed interlace. It uses the same transfer data as Extension, plus robustness and strict numerical gates that make the lower bound tight enough to control the protocol's shape.",
);
upsertConcept(
  explainers,
  "thm:SeparationTheorem",
  "rigidity conclusion",
  lineContaining(nodeById["thm:SeparationTheorem"].leanStmt, "∀ P : Protocol"),
  "For every computing protocol within the budget D(f)+log q, the first log q queries are Alice queries on every nonempty current rectangle. Their transcript labels partition the rows so that each part has one dominant outer block, losing at most (q-1)*ceil(2^(1-b)*m) rows. Dead, input-unrealizable subtrees are intentionally unconstrained.",
);
setConcept(
  explainers,
  "thm:main-nphard-intro",
  "theorem signature",
  "Declares the checked communication-gap construction for every loopless edge-list 4-Colouring instance. The historical Lean name says NP-hardness, but the theorem type does not encode an effective many-one reduction.",
);
setConcept(
  explainers,
  "thm:main-nphard-intro",
  "promise and size bounds",
  "Proves the VBP promise and bounds item and dimension counts by sourceSize. Here sourceSize is the combinatorial proxy |V|+|E|+1, not a formal bit-level encoding length.",
);
setConcept(
  explainers,
  "thm:main-nphard-intro",
  "row count bound",
  "Bounds the row carrier by the exact formula n + rowPoly(scale). The checked theorem main_output_size_fixed_degree separately dominates this by one fixed-exponent polynomial in |V|+|E|+1.",
);
setConcept(
  explainers,
  "thm:main-nphard-intro",
  "column count bound",
  "Bounds the column carrier by the exact formula colPoly(scale). The checked fixed-degree theorem dominates it in |V|+|E|+1; only the formal bridge to a chosen serialized input language remains external.",
);
setConcept(
  explainers,
  "axiom:aghp",
  "the axiom's name",
  "Declares the sole project axiom. AGHP supplies the historical binary construction; Bshouty's derandomized Chernoff sampler explicitly extends to arbitrary alphabets. The repository records the cylinder-event parameter translation to this exact interface.",
);
setConcept(
  explainers,
  "axiom:vbp-np-hard",
  "the package declaration",
  "Defines a proved correctness-and-size package from loopless edge-list 4-Colouring to promised Vector Bin Packing. It is not an axiom and does not contain an encoded polynomial-time machine or the external NP-hardness of 4-Colouring.",
);
setConcept(
  explainers,
  "axiom:vbp-np-hard",
  "matrix-size bound",
  "Bounds the simple VBP presentation footprint by sourceSize squared. This is a combinatorial cardinality statement, not a formal running-time theorem.",
);
setConcept(
  explainers,
  "lem:polytime",
  "row-count bound",
  "Concludes the exact row-carrier bound |R4| <= n + rowPoly(d). NPCC.PolynomialSize proves the separate fixed-degree domination consumed by main_output_size_fixed_degree.",
);
setConcept(
  explainers,
  "lem:polytime",
  "column-count bound",
  "Concludes the exact column-carrier bound |C4| <= colPoly(d). Fixed-degree domination and square truth-table size are checked separately; executable construction time remains outside this theorem.",
);

for (const id of ["axiom:aghp", "thm:main-nphard-intro"]) {
  const statement = nodeById[id].leanStmt;
  const byLabel = Object.fromEntries((explainers[id] || []).map((item) => [item.label, item]));
  if (id === "axiom:aghp") {
    byLabel["the axiom's name"].line = lineContaining(statement, "axiom finite_alphabet_balanced_family_exists");
    byLabel["one universal constant"].line = lineContaining(statement, "∃ C : ℕ");
    byLabel["the parameters"].line = lineContaining(statement, "∀ (q t : ℕ)");
    byLabel["side conditions"].line = lineContaining(statement, "1 ≤ t →");
    byLabel["the family exists"].line = lineContaining(statement, "∃ (L : ℕ)");
    byLabel["nonempty family"].line = lineContaining(statement, "0 < L ∧");
    byLabel["size bound"].line = lineContaining(statement, "(L : ℝ) ≤");
    byLabel["the balance guarantee"].line = lineContaining(statement, "∀ J : Finset");
  } else {
    byLabel["theorem signature"].line = lineContaining(statement, "theorem main_np_hardness");
    byLabel["promise and size bounds"].line = lineContaining(statement, ").Promise ∧");
    byLabel["scale bound"].line = lineContaining(statement, "ctorScaleFull");
    byLabel["row count bound"].line = lineContaining(statement, "Fintype.card (R4");
    byLabel["column count bound"].line = lineContaining(statement, "Fintype.card (C4");
    byLabel["the hardness equivalence"].line = lineContaining(statement, "(G.IsYes ↔");
  }
}
applyExplainerAudit(explainers, nodeById, JSON.parse(read(explainerAuditPath)));
inspectorHtml = replaceJsonScript(inspectorHtml, "explainers", explainers);

const glossary = jsonScript(inspectorHtml, "gloss").value;
ensureGlossaryDeclaration(
  glossary,
  "NPCC.fixedStructuralDegree",
  "NPCC/PolynomialSize.lean",
  "def",
  "One absolute natural-number exponent chosen to dominate both carrier-size formulas.",
  "It is the maximum of explicit row and column exponents built from the single balanced-family constant.",
);
ensureGlossaryDeclaration(
  glossary,
  "NPCC.sourceCarrierPolynomial",
  "NPCC/Wrapper.lean",
  "def",
  "The explicit fixed-degree polynomial used to bound both final typed carriers.",
  "It combines a linear source-size term with sourceScalePolynomial raised to fixedStructuralDegree.",
);
ensureGlossaryDeclaration(
  glossary,
  "NPCC.main_output_size_fixed_degree",
  "NPCC/Wrapper.lean",
  "theorem",
  "The checked fixed-degree size theorem for the complete graph-to-matrix construction.",
  "It transports the normalized-dimension power bounds to the combinatorial graph size |V|+|E|+1.",
);
ensureGlossaryDeclaration(
  glossary,
  "NPCC.gapTruthTableBitCount_le_fixed_polynomial",
  "NPCC/Public.lean",
  "theorem",
  "The checked fixed-degree bound on the number of entries in the final square Boolean truth table.",
  "It combines the two carrier bounds with the factor-two power-of-two padding estimate and then squares the side length.",
);
const unmatched = [];
const fallback = [];
for (const [name, declaration] of Object.entries(glossary.decls || {})) {
  declaration.file = String(declaration.file || "").replace(/^Npcc\//, "NPCC/");
  const file = sourcePath(declaration.file);
  if (!declaration.code || !fs.existsSync(file)) continue;
  const source = read(file).replace(/\r\n/g, "\n");
  const code = String(declaration.code).replace(/\r\n/g, "\n");
  const maskedSource = maskUnicode(source);
  const maskedCode = maskUnicode(code);
  const start = maskedSource.indexOf(maskedCode);
  if (start < 0) {
    const current = currentDeclarationSnippet(source, name);
    if (!current) {
      unmatched.push(name);
      continue;
    }
    declaration.code = current.code;
    declaration.line = lineAt(source, current.start);
    fallback.push(name);
  } else {
    declaration.code = source.slice(start, start + code.length);
    declaration.line = lineAt(source, start);
  }
  if (declaration.doc) {
    const doc = String(declaration.doc).replace(/\r\n/g, "\n");
    const maskedDoc = maskUnicode(doc);
    const declarationStart = declaration.line > 0
      ? source.split("\n").slice(0, declaration.line - 1).join("\n").length
      : source.length;
    let docStart = maskedSource.lastIndexOf(maskedDoc, declarationStart);
    if (docStart < 0) docStart = maskedSource.indexOf(maskedDoc);
    if (docStart >= 0) declaration.doc = source.slice(docStart, docStart + doc.length);
  }
}
if (unmatched.length) {
  throw new Error(`could not repair ${unmatched.length} glossary snippets: ${unmatched.slice(0, 12).join(", ")}`);
}

glossary.summaries["thm:main-nphard-intro"] = nodeById["thm:main-nphard-intro"].summary;
glossary.summaries["axiom:aghp"] = nodeById["axiom:aghp"].summary;
glossary.summaries["axiom:vbp-np-hard"] = nodeById["axiom:vbp-np-hard"].summary;
glossary.summaries["lem:polytime"] = nodeById["lem:polytime"].summary;
glossary.summaries["thm:Extension"] = nodeById["thm:Extension"].summary;
glossary.summaries["thm:SeparationTheorem"] = nodeById["thm:SeparationTheorem"].summary;
glossary.summaries["lem:scaffold-completeness"] = nodeById["lem:scaffold-completeness"].summary;
glossary.summaries["lem:MFourNoWasteLift"] = nodeById["lem:MFourNoWasteLift"].summary;
glossary.summaries["thm:reduction-gap"] = nodeById["thm:reduction-gap"].summary;
glossary.summaries["lem:relaxed-to-classical"] = nodeById["lem:relaxed-to-classical"].summary;
glossary.summaries[paddedGapId] = nodeById[paddedGapId].summary;
glossary.summaries[fixedSizeId] = nodeById[fixedSizeId].summary;

const mainTrust = glossary.trust["thm:main-nphard-intro"] || [];
for (const item of mainTrust) {
  if (item.term === "NPCC.FourColorInstance.sourceSize") {
    item.why = "The combinatorial proxy |V|+|E|+1. It is not a formal bit-level encoding length.";
  } else if (item.term === "NPCC.vbp_np_hard") {
    item.why = "The proved 4-Colouring to promised-VBP correctness map. Its runtime and source NP-hardness are external.";
  } else if (item.term === "NPCC.R4") {
    item.why = "M4's row carrier. Lean proves both the exact rowPoly formula and a fixed-degree bound in |V|+|E|+1.";
  } else if (item.term === "NPCC.C4") {
    item.why = "M4's column carrier. Lean proves both the exact colPoly formula and a fixed-degree bound; NPCC.Public then square-pads both carriers while preserving D exactly.";
  } else if (item.term === "NPCC.rowPoly") {
    item.why = "The exact row-bound expression. NPCC.PolynomialSize proves its fixed-degree domination in the normalized constructor regime.";
  }
}
if (!mainTrust.some((item) => item.term === "NPCC.finite_alphabet_balanced_family_exists")) {
  mainTrust.push({
    term: "NPCC.finite_alphabet_balanced_family_exists",
    why: "The sole project axiom in the theorem's transitive footprint. Its exact finite-alphabet cylinder-event derivation and source chain are documented in BALANCED-FAMILY-CITATION.md.",
  });
}
glossary.trust["thm:main-nphard-intro"] = mainTrust;
if (glossary.trust["axiom:aghp"]?.[0]) {
  glossary.trust["axiom:aghp"][0].why =
    "The property consumed downstream. The citation note identifies the binary AGHP result, Bshouty's arbitrary-alphabet sampler, and the exact parameter translation to this interface.";
}

if (glossary.decls["NPCC.finite_alphabet_balanced_family_exists"]) {
  glossary.decls["NPCC.finite_alphabet_balanced_family_exists"].plain =
    "The sole project axiom: an exact existence-and-cardinality interface for balanced finite-alphabet column families.";
  glossary.decls["NPCC.finite_alphabet_balanced_family_exists"].how =
    "It supplies a nonempty indexed family with the displayed relative projection error and size bound. The source-to-interface translation is documented; executable generation and runtime are not proved in Lean.";
}
if (glossary.decls["NPCC.FourColorInstance.sourceSize"]) {
  glossary.decls["NPCC.FourColorInstance.sourceSize"].plain =
    "The combinatorial proxy |V|+|E|+1; not a bit-level encoding length.";
}
inspectorHtml = replaceJsonScript(inspectorHtml, "gloss", glossary);

const rootScope = '<b>Scope of the machine check:</b> Lean proves the <b>choice-based threshold-gap equivalence, explicit and fixed-degree carrier/truth-table bounds in |V|+|E|+1, and square power-of-two padding preserving D</b>, conditional on one balanced-family citation axiom. <b>External:</b> the bridge to chosen serialized source and target languages, executable construction/runtime, NP membership, and 4-Colouring hardness. <a href="lean/AUDIT.md">Full audit</a> · <a href="lean/docs/BALANCED-FAMILY-CITATION.md">Citation boundary</a>.';
const inspectorScope = '<b>Scope of the machine check:</b> Lean proves the <b>choice-based threshold-gap equivalence, explicit and fixed-degree carrier/truth-table bounds in |V|+|E|+1, and square power-of-two padding preserving D</b>, conditional on one balanced-family citation axiom. <b>External:</b> the bridge to chosen serialized source and target languages, executable construction/runtime, NP membership, and 4-Colouring hardness. <a href="../lean/AUDIT.md">Full audit</a> · <a href="../lean/docs/BALANCED-FAMILY-CITATION.md">Citation boundary</a>.';
graphHtml = graphHtml.replace(/<b>Scope of the machine check:<\/b>[\s\S]*?<\/div>/, `${rootScope}</div>`);
inspectorHtml = inspectorHtml.replace(/<b>Scope of the machine check:<\/b>[\s\S]*?<\/div>/, `${inspectorScope}</div>`);
graphHtml = graphHtml.replaceAll("Npcc/ (this work)", "NPCC/ (this work)");
inspectorHtml = inspectorHtml.replaceAll("Npcc/ (this work)", "NPCC/ (this work)");
graphHtml = graphHtml.replaceAll("Machine-verified · Lean 4", "Lean-checked core · Lean 4");
inspectorHtml = inspectorHtml.replaceAll("Machine-verified · Lean 4", "Lean-checked core · Lean 4");
graphHtml = graphHtml.replaceAll(
  "Builds with 0 sorries via `lake build NPCC`.",
  "Builds with 0 sorries via `lake build NPCC Workspace Tests`.",
);
inspectorHtml = inspectorHtml.replaceAll(
  "Builds with 0 sorries via `lake build NPCC`.",
  "Builds with 0 sorries via `lake build NPCC Workspace Tests`.",
);
graphHtml = graphHtml.replace("the 50 formalized statements are highlighted", "all mapped formalized statements are highlighted");
inspectorHtml = inspectorHtml.replace("the 50 formalized statements are highlighted", "all mapped formalized statements are highlighted");
inspectorHtml = inspectorHtml.replace(
  "The proof below this line is machine-checked by Lean’s kernel. To believe the theorem says what the paper claims, a reader only needs to check that these definitions mean what the paper means — click each one:",
  "The proof term below is checked by Lean’s kernel relative to its axiom footprint. To assess faithfulness to the paper, inspect these definitions, imported assumptions, and the external scope boundary — click each one:",
);
inspectorHtml = inspectorHtml.replace(
  /if\(block && (?:!block\.audit && )?Object\.prototype\.hasOwnProperty\.call\(overrides, block\.label\)\)\{/,
  "if(block && !block.audit && Object.prototype.hasOwnProperty.call(overrides, block.label)){",
);
const fixedSizeProofStep = '<button data-target="thm:fixed-degree-size" title="Checked fixed-degree carrier and truth-table size bounds"><span class="pm-num">5</span><span class="pm-copy"><b>Size bound</b><small>one absolute exponent</small></span></button>';
graphHtml = graphHtml.replace(/<button data-target="(?:lem:polytime|thm:fixed-degree-size)" title="[^"]*"><span class="pm-num">5<\/span><span class="pm-copy"><b>Size bounds?<\/b><small>[^<]*<\/small><\/span><\/button>/, fixedSizeProofStep);
inspectorHtml = inspectorHtml.replace(/<button data-target="(?:lem:polytime|thm:fixed-degree-size)" title="[^"]*"><span class="pm-num">5<\/span><span class="pm-copy"><b>Size bounds?<\/b><small>[^<]*<\/small><\/span><\/button>/, fixedSizeProofStep);

fs.writeFileSync(graphPath, graphHtml);
fs.writeFileSync(inspectorPath, inspectorHtml);
console.log(`Synchronized ${data.nodes.length} graph nodes and ${Object.keys(glossary.decls).length} glossary declarations.`);
if (fallback.length) console.log(`Refreshed ${fallback.length} stale glossary signatures from current declarations.`);
