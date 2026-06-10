// Demo: the gate decided by the EXTRACTED Lean binary, on the 5-agent scenario.
// Asserts the binary's verdicts match the spec; exits non-zero on any divergence.
//   build first:  lake build checker
//   run:          node sidecar/extracted-demo.mjs

import { gateExtracted } from "./extracted-gate.mjs";

const policy = {
  config: { members: [0, 1, 2, 3, 4] },
  votes: { 0: "ship", 1: "ship", 2: "ship", 3: "hold", 4: "hold" },
};

const call = (value, voters) => ({
  method: "tools/call",
  params: { name: "deploy", arguments: { release: value }, _consensusCert: { value, voters } },
});

const scenarios = [
  { label: 'honest majority  ship  (agents 0,1,2)', req: call("ship", [0, 1, 2]), expect: "allow" },
  { label: 'minority         hold  (agents 3,4)  ', req: call("hold", [3, 4]),    expect: "deny" },
  { label: 'forged           hold  (agents 0,1,3)', req: call("hold", [0, 1, 3]), expect: "deny" },
  { label: 'no certificate   (bare tools/call)   ', req: { method: "tools/call", params: { name: "deploy" } }, expect: "deny" },
];

console.log("── Consensus Seal · gate decided by the EXTRACTED Lean binary ──");
let failures = 0;
for (const s of scenarios) {
  const { decision, reason } = gateExtracted(s.req, policy);
  const mark = decision === "allow" ? "ACCEPT ✓ discharged" : "REJECT ✗ blocked  ";
  const ok = decision === s.expect ? "    [conforms]" : "    [!! MISMATCH]";
  if (decision !== s.expect) failures++;
  console.log(`  ${s.label}   ${mark}${ok}   (${reason})`);
}
console.log("── The decision above is proved Lean code (Consensus.Checker.agreement, 0 sorry). ──");

if (failures > 0) {
  console.error(`\nFAILED: ${failures} verdict(s) diverged.`);
  process.exit(1);
} else {
  console.log("\nOK: the extracted Lean checker gated every action correctly.");
}
