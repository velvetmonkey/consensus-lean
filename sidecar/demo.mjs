// Consensus Seal sidecar — live demo + conformance harness.
//
// Runs the runtime checker on the SAME five-agent scenario as Consensus/Demo.lean and
// asserts the verdicts match the Lean proof's verdicts. If the port ever drifts from the
// proven spec, this exits non-zero.
//
//   run:  node sidecar/demo.mjs

import { gate, check, overlapWitness } from "./consensus-seal.mjs";

// ── Trusted, pinned policy: the roster and the recorded votes (3–2 split for "ship"). ──
const policy = {
  config: { members: [0, 1, 2, 3, 4] },
  votes: { 0: "ship", 1: "ship", 2: "ship", 3: "hold", 4: "hold" },
};

// Build a tools/call carrying a consensus certificate.
const call = (value, voters) => ({
  method: "tools/call",
  params: { name: "deploy", arguments: { release: value }, _consensusCert: { value, voters } },
});

const scenarios = [
  { label: 'honest majority  ship  (agents 0,1,2)', req: call("ship", [0, 1, 2]), expect: "allow" },
  { label: 'minority         hold  (agents 3,4)  ', req: call("hold", [3, 4]),    expect: "deny" },
  { label: 'forged           hold  (agents 0,1,3)', req: call("hold", [0, 1, 3]), expect: "deny" },
  { label: 'no certificate   (bare tools/call)   ', req: { method: "tools/call", params: { name: "deploy" } }, expect: "deny" },
  { label: 'malformed        (voters not a list) ', req: { method: "tools/call", params: { name: "deploy", _consensusCert: { value: "ship", voters: "0,1,2" } } }, expect: "deny" },
];

console.log("── Consensus Seal · sidecar enforcing on live tools/call ──");
let failures = 0;
for (const s of scenarios) {
  const { decision, reason } = gate(s.req, policy);
  const mark = decision === "allow" ? "ACCEPT ✓ discharged" : "REJECT ✗ blocked  ";
  const ok = decision === s.expect ? "    [conforms]" : "    [!! MISMATCH vs Lean spec]";
  if (decision !== s.expect) failures++;
  console.log(`  ${s.label}   ${mark}${ok}   (${reason})`);
}

// ── Reconfiguration: roster shrinks to {0,1,2,3}; the old and new "ship" certs agree. ──
const policy2 = { config: { members: [0, 1, 2, 3] }, votes: policy.votes };
const certShip = { value: "ship", voters: [0, 1, 2] };
const cross = overlapWitness(policy, certShip, policy2, certShip);
const crossOk = cross === true ? "    [conforms]" : "    [!! MISMATCH]";
if (!cross) failures++;
console.log(`  after reconfig   ship  (agents 0,1,2)   ${check(policy2, certShip) ? "ACCEPT ✓ discharged" : "REJECT ✗ blocked  "}` +
  `${crossOk}   (overlap witness ${cross ? "holds" : "fails"}: agreement preserved)`);

console.log("── Verdicts match Consensus/Demo.lean (proof: cert_agreement, no_conflicting_certs). ──");

if (failures > 0) {
  console.error(`\nCONFORMANCE FAILED: ${failures} verdict(s) diverged from the Lean spec.`);
  process.exit(1);
} else {
  console.log("\nCONFORMANCE OK: every runtime verdict matches the machine-checked spec.");
}
