// Consensus Seal — runtime enforcement sidecar.
//
// consensus-lean (the Lean 4 library) PROVES the safety property: any certificate
// the checker accepts cannot conflict with another (`Consensus.Bridge.cert_agreement`,
// machine-checked, 0 sorry). This file ENFORCES that property at runtime on a real MCP
// `tools/call`. It implements exactly the decidable predicate `Consensus.Bridge.Valid`:
//
//     Valid cfg vote c  :=  c.voters ⊆ cfg.members
//                          ∧ 2 * |c.voters| > |cfg.members|
//                          ∧ ∀ a ∈ c.voters, vote a = some c.value
//
// The roster (`members`) and recorded `votes` are TRUSTED, PINNED POLICY held by the
// sidecar — never read from the agent's certificate (the gate brings its own guest list).
// The action carries only the claim: a value and the voters who back it.
//
// Trust boundary: the predicate below is a direct transcription of the Lean `Valid`
// definition (simple enough to read off by eye). The NON-obvious fact — that accepting
// implies agreement — is what Lean proves. `conformance` (see demo.mjs) pins this port to
// the proof's verdicts on the same scenarios.

/** @typedef {{ members: number[] }} Config */
/** @typedef {{ value: string, voters: number[] }} Cert */
/** @typedef {{ config: Config, votes: Record<number, string> }} Policy  trusted, pinned */

/** Strict-majority quorum check, faithful to Lean `Valid`.
 *  Total + fail-closed: any malformed input DENIES (returns false), never throws. */
export function isValid(/** @type {Policy} */ policy, /** @type {Cert} */ cert) {
  // Shape guards — a malformed certificate or policy is denied, not an exception.
  if (cert == null || typeof cert !== "object") return false;
  if (typeof cert.value !== "string") return false;
  if (!Array.isArray(cert.voters)) return false;
  if (policy?.config == null || !Array.isArray(policy.config.members)) return false;
  if (policy.votes == null || typeof policy.votes !== "object") return false;
  const members = new Set(policy.config.members);
  const voters = cert.voters;
  // 1. voters ⊆ members
  if (!voters.every((a) => members.has(a))) return false;
  // 2. strict majority: 2 * |voters| > |members|   (voters assumed duplicate-free)
  const distinct = new Set(voters);
  if (distinct.size !== voters.length) return false; // reject malformed (duplicate) voter lists
  if (2 * distinct.size <= members.size) return false;
  // 3. every voter's recorded vote matches the claimed value
  if (!voters.every((a) => policy.votes[a] === cert.value)) return false;
  return true;
}

/** Runnable Bool check — mirrors `Consensus.Bridge.check`. */
export function check(policy, cert) {
  return isValid(policy, cert);
}

/**
 * Gate an MCP `tools/call`. Fail-closed: an action is admitted only if it carries a
 * certificate that the checker accepts against the trusted policy. No certificate, or an
 * invalid one, is DENIED (default-deny, same discipline as mcp-seal's Safety Seal).
 *
 * @param {{ method: string, params: { name: string, arguments?: any, _consensusCert?: Cert } }} request
 * @param {Policy} policy  trusted, pinned configuration
 * @returns {{ decision: "allow" | "deny", reason: string }}
 */
export function gate(request, policy) {
  if (request?.method !== "tools/call") {
    return { decision: "deny", reason: "not a tools/call (default-deny)" };
  }
  const cert = request.params?._consensusCert;
  if (!cert) {
    return { decision: "deny", reason: "no consensus certificate attached (default-deny)" };
  }
  if (!check(policy, cert)) {
    return { decision: "deny", reason: "certificate rejected: not a matching majority quorum" };
  }
  return { decision: "allow", reason: `discharged: majority chose "${cert.value}"` };
}

/**
 * Cross-configuration (reconfiguration) check — mirrors `cert_agreement_cross`. Two
 * certificates valid against different rosters agree IF the per-instance overlap witness
 * holds: |voters_a| + |voters_b| > |members_a ∪ members_b|.
 */
export function overlapWitness(policyA, certA, policyB, certB) {
  const union = new Set([...policyA.config.members, ...policyB.config.members]);
  return certA.voters.length + certB.voters.length > union.size;
}
