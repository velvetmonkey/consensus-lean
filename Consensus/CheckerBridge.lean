/-
Copyright (c) 2026 Ben Cassie. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ben Cassie
-/
import Mathlib
import Consensus.Certificate
import Consensus.Majority
import Consensus.Checker

set_option linter.unusedSectionVars false

/-!
# Checker ↔ Bridge refinement — the prose link made machine-checked

`Consensus.Checker.agreement`'s docstring claims the `List`-level checker "is
`Consensus.Bridge.cert_agreement` re-established for the compilable `List`
checker" — until this file, that link was a COMMENT, not a lemma. This module
is the refinement proof: every certificate the running `Bool` gate accepts is
`Bridge.Valid` under the evident maps, so the `List`-level agreement is a
corollary of the abstract `Finset`-level soundness theorem, not an independent
re-proof that merely resembles it.

## FROZEN STATEMENTS (Day-1 freeze; proofs follow the review)

* `configOf (members : List Nat) : Bridge.Config Nat` — the roster as a
  `Finset` (`List.toFinset`). `Bridge.Config` carries no quorum field: its
  majority rule is baked into `Bridge.Valid` (`2 * voters.card >
  members.card`), which is exactly the `majorityQuorums` rule bounded to an
  explicit roster (`Bridge.majority_inter_in` is the bounded
  `majority_inter`) — so "majority-quorum config" is definitional, with
  nothing further to plug in.
* `voteOf (votes : Votes) : Nat → Option String` — `Checker.lookup votes`,
  the checker's own first-match vote lookup, unchanged.
* `certOf (c : Checker.Cert) : Bridge.Cert Nat String` — same value, voters
  `List → Finset`.
* `validB_refines` — **the refinement**: `validB members votes c = true →
  Bridge.Valid (configOf members) (voteOf votes) (certOf c)`. The crux is the
  cardinality step: `voters.Nodup` gives `voters.toFinset.card =
  voters.length`, while the possibly-duplicated roster only needs
  `members.toFinset.card ≤ members.length`, so the strict-majority inequality
  survives the transport in the required direction.
* `agreement_via_bridge` — `Checker.agreement`'s exact statement DERIVED as a
  corollary of `Bridge.cert_agreement` through `validB_refines` (both
  accepted certs refine to `Bridge.Valid` over the same config and votes;
  `(certOf c).value = c.value` is definitional).

## Why `Checker.agreement`'s original proof stays

`Checker.lean` is deliberately Mathlib-free — that is its entire reason to
exist (a small native binary, seconds to compile). Re-pointing its proof at
this module would (a) import Mathlib into the extracted checker, destroying
the extraction property, and (b) create an import cycle (this file imports
`Checker`). So the original `List`-level proof stands as the compilable
artifact, this module proves it is subsumed by the abstract theory, and the
`Checker.agreement` docstring is re-pointed at `validB_refines` /
`agreement_via_bridge` so the prose claim is true.

Axiom footprint target for both results: ⊆ {propext, Classical.choice,
Quot.sound} (probed and recorded at proof time; consensus-lean has no axiom
gate yet — adding one is separate work, D4).
-/

namespace Consensus.CheckerBridge

open Consensus.Checker (Votes lookup validB)

/-- The `List` roster as a `Bridge` configuration: members as a `Finset`.
The majority-quorum rule is `Bridge.Valid`'s own card condition — see the
module docstring. -/
def configOf (members : List Nat) : Bridge.Config Nat :=
  ⟨members.toFinset⟩

/-- The checker's vote table as the abstract vote assignment: the checker's
own first-match `lookup`, unchanged. -/
def voteOf (votes : Votes) : Nat → Option String :=
  fun a => lookup votes a

/-- A `List`-level certificate as a `Bridge` certificate: same value, voters
as a `Finset`. -/
def certOf (c : Checker.Cert) : Bridge.Cert Nat String :=
  ⟨c.value, c.voters.toFinset⟩

/-- **The refinement (frozen).** Every certificate the running `Bool` checker
accepts is `Bridge.Valid` under the evident maps: acceptance at the `List`
level lands inside the abstract `Finset`-level acceptance predicate. -/
theorem validB_refines (members : List Nat) (votes : Votes) (c : Checker.Cert)
    (h : validB members votes c = true) :
    Bridge.Valid (configOf members) (voteOf votes) (certOf c) := by
  sorry

/-- **Agreement as a corollary (frozen).** `Checker.agreement`'s exact
statement, derived from `Bridge.cert_agreement` through `validB_refines` —
the `List`-level agreement is BACKED BY the abstract quorum-intersection
theorem, not an independent re-proof. -/
theorem agreement_via_bridge (members : List Nat) (votes : Votes)
    (c c' : Checker.Cert)
    (h : validB members votes c = true) (h' : validB members votes c' = true) :
    c.value = c'.value := by
  sorry

end Consensus.CheckerBridge
