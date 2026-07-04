/-
Copyright (c) 2026 Ben Cassie. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ben Cassie
-/
import Consensus.Quorum
import Consensus.Majority
import Consensus.Reconfig
import Consensus.Certificate
import Consensus.Checker
import Consensus.CheckerBridge

/-!
# Axiom-footprint gate for consensus-lean

Every load-bearing public soundness theorem must sit on the standard axiom set
only — `{propext, Quot.sound}` for the Mathlib-free checker, plus
`Classical.choice` for the `Finset`/`Fintype` theory — with no `sorryAx` and no
`Lean.ofReduceBool`. Each expected footprint is pinned with `#guard_msgs`, so any
axiom drift (a stray `sorry`, a `native_decide`, an unexpected classical
dependency) fails the build itself, at compile time.

Footprints observed via `#print axioms` on 2026-07-04.
-/

-- Quorum safety (Consensus/Quorum.lean): abstract single-decree agreement.

/-- info: 'Consensus.agreement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Consensus.agreement

/-- info: 'Consensus.validity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Consensus.validity

-- Majority quorums (Consensus/Majority.lean): the concrete majority instance.

/--
info: 'Consensus.majority_agreement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Consensus.majority_agreement

/--
info: 'Consensus.majority_validity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Consensus.majority_validity

-- Certificate bridge (Consensus/Certificate.lean): decidable checker soundness.

/--
info: 'Consensus.Bridge.cert_agreement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Consensus.Bridge.cert_agreement

/--
info: 'Consensus.Bridge.no_conflicting_certs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Consensus.Bridge.no_conflicting_certs

/--
info: 'Consensus.Bridge.cert_agreement_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Consensus.Bridge.cert_agreement_cross

-- Reconfiguration safety (Consensus/Reconfig.lean): agreement across epochs.

/-- info: 'Consensus.agreement_cross' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Consensus.agreement_cross

/-- info: 'Consensus.Transition.agreement_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Transition.agreement_preserved

/-- info: 'Consensus.agreement_history' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Consensus.agreement_history

-- Extracted runtime checker (Consensus/Checker.lean): Mathlib-free, its own proof.

/-- info: 'Consensus.Checker.agreement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Checker.agreement

-- Checker ↔ Bridge refinement (Consensus/CheckerBridge.lean): the running gate
-- is backed by the abstract quorum-intersection theory.

/--
info: 'Consensus.CheckerBridge.validB_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Consensus.CheckerBridge.validB_refines

/--
info: 'Consensus.CheckerBridge.agreement_via_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Consensus.CheckerBridge.agreement_via_bridge

def main : IO Unit :=
  IO.println "axiom gate passed: all checks pinned by #guard_msgs at compile time"
