# Consensus Seal — runtime enforcement sidecar

This is the **bridge to a running agent**: a small, dependency-free Node sidecar that gates
an MCP `tools/call` using the consensus check that [`consensus-lean`](../) proves sound.

```bash
node demo.mjs        # or: npm run demo
```

```
── Consensus Seal · sidecar enforcing on live tools/call ──
  honest majority  ship  (agents 0,1,2)   ACCEPT ✓ discharged    [conforms]   (discharged: majority chose "ship")
  minority         hold  (agents 3,4)     REJECT ✗ blocked       [conforms]   (certificate rejected: not a matching majority quorum)
  forged           hold  (agents 0,1,3)   REJECT ✗ blocked       [conforms]   (certificate rejected: not a matching majority quorum)
  no certificate   (bare tools/call)      REJECT ✗ blocked       [conforms]   (no consensus certificate attached (default-deny))
  after reconfig   ship  (agents 0,1,2)   ACCEPT ✓ discharged    [conforms]   (overlap witness holds: agreement preserved)
── Verdicts match Consensus/Demo.lean ──
CONFORMANCE OK: every runtime verdict matches the machine-checked spec.
```

## How it works

- The sidecar holds a **trusted, pinned policy**: the member `roster` and the recorded
  `votes`. These are *never* read from the agent's request (the gate brings its own guest
  list — see the reconfiguration / membership-as-trusted-config design).
- An action is an MCP `tools/call` carrying a **certificate** in `params._consensusCert`:
  a claimed `value` and the `voters` who back it.
- `gate` is **fail-closed**: it admits the action only if the certificate passes `check`
  against the pinned policy. No certificate, a non-majority, duplicate voters, or votes
  that do not match the claim → **deny**. Same default-deny discipline as the Safety Seal
  ([mcp-seal](https://github.com/velvetmonkey/mcp-seal)).

## The trust boundary (stated plainly)

`consensus-lean` is the **specification and the proof**. `isValid` here is a direct
transcription of the Lean predicate `Consensus.Bridge.Valid` (short enough to read off by
eye). The *non-obvious* claim — that any two accepted certificates must agree — is what
Lean machine-checks (`cert_agreement`, `no_conflicting_certs`, 0 sorry). This sidecar is
the **enforcement layer**; it does not re-prove anything.

`demo.mjs` is a **conformance harness**: it runs the same scenarios as
[`Consensus/Demo.lean`](../Consensus/Demo.lean) and exits non-zero if any runtime verdict
diverges from the proof's verdict. That pins the port to the spec. (A future step can
replace the transcription with code extracted directly from Lean, closing the boundary
entirely.)

## What this is and is not

- **Is**: a working reject-or-discharge gate over a real MCP `tools/call` shape, backed by
  a machine-checked safety theorem, fail-closed, with reconfiguration support.
- **Is not**: a full consensus *protocol* (no ballots / rounds / leader election /
  termination), and not yet wired into a live MCP transport — it gates request objects.
  Both are deliberate, honest boundaries.
