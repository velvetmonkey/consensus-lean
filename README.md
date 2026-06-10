# consensus-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](Consensus)

**consensus-lean: Formal Proofs of Quorum-based Consensus Safety in Lean 4**

Lean 4 formal proofs of the **safety core of distributed consensus**: under any quorum
system whose quorums pairwise intersect, **at most one value is ever chosen**. This is the
agreement guarantee at the heart of Paxos and Raft, reduced to its load-bearing fact —
quorum intersection — and proved for strict-majority quorums over a finite acceptor set.

**Zero sorry statements.** Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

## Why it matters

Consensus (the CP problem) and convergence (the AP property of CRDTs) are different
guarantees, and conflating them is a classic error. CRDTs converge precisely by *avoiding*
consensus: no quorum, no total order, accept everything and merge. Consensus does the
opposite — it forces a single agreed value even under failures — and the price is quorum
intersection. This library certifies that price is sufficient: intersection alone gives
agreement.

It is the **CP sibling** of [crdt-lean](https://github.com/velvetmonkey/crdt-lean) (AP
convergence) and [kuramoto-lean](https://github.com/velvetmonkey/kuramoto-lean)
(continuous control consensus), under the verified-agent-kernel line.

## Setting

A `QuorumSystem α` is a predicate `IsQuorum : Finset α → Prop` together with its single
defining axiom: any two quorums share an acceptor (`inter`). A run is a vote assignment
`vote : α → Option V` — each acceptor votes for at most one value because it is a
function. A value `v` is **chosen** when some quorum has *every* member voting `v`. The
abstraction is deliberate: agreement needs only intersection, so it holds for majority,
weighted, or grid quorums alike; `Consensus.Majority` supplies the canonical
strict-majority instance.

## Theorem inventory

| # | Name | Statement |
|---|------|-----------|
| 1 | `QuorumSystem` | A quorum family with the single axiom that any two quorums intersect |
| 2 | `Chosen` | A value is chosen when some quorum unanimously votes it |
| 3 | `quorum_nonempty` | Every quorum is nonempty (falls out of self-intersection) |
| 4 | `agreement` | **If two values are both chosen, they are equal** — the consensus safety core |
| 5 | `validity` | A chosen value was actually voted by some acceptor |
| 6 | `IsMajority` | A set is a strict-majority quorum when `2·|Q| > |acceptors|` |
| 7 | `majority_inter` | Any two strict-majority sets intersect (counting argument) |
| 8 | `majorityQuorums` | The majority quorum system over a finite acceptor population |
| 9 | `majority_agreement` | Under majority quorums, at most one value is ever chosen |
| 10 | `majority_validity` | Under majority quorums, a chosen value was voted by someone |
| 11 | `Compatible` | Two configurations whose quorums all pairwise intersect — the safe-reconfiguration condition |
| 12 | `agreement_cross` | **Agreement across a reconfiguration**: values chosen under two compatible configurations must be equal |
| 13 | `Transition` / `Transition.agreement_preserved` | A membership change bundled with its overlap witness; the change preserves agreement |
| 14 | `agreement_history` | Agreement across an entire timeline of pairwise-compatible configurations — reconfigure freely, never disagree |
| 15 | `Bridge.Valid` (+ `Decidable` instance) | **Executable** acceptance: voters are members, form a strict majority, and each one's recorded vote matches the certificate — a runtime check, not an abstract `∀` |
| 16 | `Bridge.cert_agreement` | **Bridge soundness**: two certificates valid against the same configuration have equal values — the checker can never discharge two conflicting actions |
| 17 | `Bridge.no_conflicting_certs` | `check` (the runnable `Bool`) never accepts a conflicting pair |
| 18 | `Bridge.cert_agreement_cross` | Soundness across a reconfiguration, given a decidable per-instance overlap witness — the runtime-checkable form of `Compatible` |

## The honest boundary

This is **safety**, not liveness or a full protocol. It proves that *no two different
values can both be chosen* — the property a consensus protocol must never violate. It does
**not** model ballots, rounds, leader election, proposal phases, or termination; those are
the Paxos/Raft machinery that *achieves* a chosen value while preserving this invariant.
The `vote` function also abstracts the per-acceptor single-vote discipline that a real
protocol enforces over time (an acceptor may only ever vote once per decree). What is
certified here is the invariant every correct protocol rests on: intersection ⇒ agreement.

`Consensus.Reconfig` extends this through **membership change**: agreement is preserved
across a reconfiguration exactly when the old and new configurations are *compatible*
(their quorums pairwise intersect), and across an arbitrarily long timeline when the
configurations are pairwise compatible. The single-vote discipline is still assumed across
epochs; transitive safety over a long history via per-step value carry-forward (Vertical
Paxos / Raft joint-consensus) is the protocol layer, deliberately left unmodelled. The
certified heart is: *compatible configurations cannot disagree.*

`Consensus.Certificate` is the **bridge** from proof to runtime. The abstract `agreement`
is a `∀` over all quorum subsets — a proof obligation no runtime can evaluate. The bridge
recasts it over concrete data: a `Config` is an explicit member roster, a `Cert` is a
chosen value plus the voters who carried it, and `Valid` is a **decidable** check (run it
as the `Bool` `check`). The soundness theorem `cert_agreement` proves that *any two
certificates the checker accepts against the same configuration must carry the same value*,
so an MCP Consensus-Seal sidecar can run `check` on every gated action and is guaranteed
never to discharge two conflicting ones. `cert_agreement_cross` carries the guarantee
across a reconfiguration given a decidable overlap witness. This is the reject-or-discharge
core. A working enforcement sidecar lives in [`sidecar/`](sidecar/): a dependency-free
Node gate that admits an MCP `tools/call` only if its certificate passes `check` against a
trusted pinned roster (fail-closed, like [mcp-seal](https://github.com/velvetmonkey/mcp-seal)),
with a conformance harness that pins the runtime verdicts to the Lean proof. Full MCP
transport wiring is the remaining integration, not new mathematics.

## Project structure

```
Consensus/
├── Quorum.lean    — QuorumSystem, Chosen, quorum_nonempty, agreement, validity
├── Majority.lean  — IsMajority, majority_inter, majorityQuorums, majority_agreement, majority_validity
├── Reconfig.lean  — Compatible, agreement_cross, Transition, agreement_history (safe reconfiguration)
├── Certificate.lean — Config, Cert, Valid (decidable), check, cert_agreement, no_conflicting_certs (the executable bridge)
└── Demo.lean      — the checker run live on a 5-agent scenario: accept honest majority, reject minority + forged, survive reconfiguration
```

## Running the demo

`Consensus.Demo` executes the verified checker on a concrete five-agent scenario and
*proves* every verdict (`by decide`, axiom-free). Run it through the Lean interpreter (no
native build needed):

```bash
lake env lean Consensus/Demo.lean
```

```
── Consensus Seal · certificate checker (verified, running live) ──
  honest majority  ship  (agents 0,1,2)   ACCEPT  ✓ discharged
  minority         hold  (agents 3,4)     REJECT  ✗ blocked
  forged           hold  (agents 0,1,3)   REJECT  ✗ blocked
  after reconfig   ship  (agents 0,1,2)   ACCEPT  ✓ discharged
── Theorem (machine-checked): any accepted certificate carries "ship".
   A conflicting decision can never be discharged. ──
```

The forged certificate lists a real majority but claims a value two of its voters never
cast; the checker rejects it. The minority certificate is a genuine vote but not a quorum;
rejected. And `no_conflicting_certs` proves, on this concrete data, that no `"hold"`
certificate can ever be accepted once `"ship"` is.

## Building

```bash
lake exe cache get   # fetch Mathlib build cache
lake build
```

Requires the Lean toolchain pinned in `lean-toolchain` (v4.28.0) and Mathlib v4.28.0.

## Related

Part of the [velvetmonkey Lean 4 proof corpus](https://velvetmonkey.github.io/lean/).
CP sibling to [crdt-lean](https://github.com/velvetmonkey/crdt-lean) (AP convergence) and
part of the [mcp-seal](https://github.com/velvetmonkey/mcp-seal) verified-agent-kernel
line.
