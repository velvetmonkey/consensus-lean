/-
Copyright (c) 2026 Ben Cassie. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Ben Cassie
-/
import Mathlib
import Consensus.Quorum

set_option linter.unusedSectionVars false

/-!
# The certificate bridge — executable consensus checking with proved soundness

`Consensus.Quorum` proves agreement as an *abstract* property (`∀` over all quorum
subsets) — a proof obligation, not something a runtime can evaluate. This file builds the
**bridge** the design calls for: a **decidable, executable** certificate checker over
concrete data, together with a machine-checked theorem that *acceptance implies the
abstract agreement guarantee*. This is the "reject-or-discharge a real run" artifact —
the verified core that an MCP Consensus-Seal sidecar calls on every gated action.

## The objects

* `Config` — a concrete configuration: an explicit `Finset` roster of members. The quorum
  rule is strict majority of the roster (decidable, no abstract `∀`).
* `Cert` — a per-action certificate: a chosen `value` and the `Finset` of members who
  voted for it (the evidence the agent action carries).
* `Valid cfg vote c` — the decidable acceptance predicate: the voters are members, they
  form a strict majority, and each one's recorded vote matches the certificate's value.
* `check` — the same thing as a runnable `Bool`; `check_iff` ties it to `Valid`.

## What is proved (the bridge)

* `Valid` is `Decidable` — the checker is executable; the seal can actually run it.
* `cert_agreement` — **soundness**: if two certificates are both valid against the same
  configuration, their values are equal. So the checker can never discharge two
  conflicting actions.
* `no_conflicting_certs` — the same, stated as "`check` never accepts a conflicting pair."
* `cert_agreement_cross` — **soundness across a reconfiguration**: two valid certificates
  against *different* configurations agree, given a decidable per-instance overlap witness
  (their voter counts exceed the combined roster). This is the runtime-checkable form of
  `Reconfig.Compatible`, fused into the bridge.

Everything here is `Finset`-level and computable: feed it concrete rosters, votes, and a
certificate and it returns accept/reject, with the guarantee that an accepted pair can
never disagree. Zero sorry, standard axioms only.
-/

namespace Consensus.Bridge

variable {α V : Type*} [DecidableEq α] [DecidableEq V]

/-- Two majority subsets of the same roster `M` intersect. The bounded form of
`majority_inter`, over an explicit `Finset` rather than a `Fintype`. -/
theorem majority_inter_in (M Q Q' : Finset α) (hQ : Q ⊆ M) (hQ' : Q' ⊆ M)
    (hc : 2 * Q.card > M.card) (hc' : 2 * Q'.card > M.card) : ∃ a, a ∈ Q ∧ a ∈ Q' := by
  by_contra hno
  push_neg at hno
  have hdisj : Disjoint Q Q' := Finset.disjoint_left.mpr (fun a ha ha' => hno a ha ha')
  have hle : (Q ∪ Q').card ≤ M.card := Finset.card_le_card (Finset.union_subset hQ hQ')
  rw [Finset.card_union_of_disjoint hdisj] at hle
  omega

/-- Subsets of two rosters whose sizes exceed the combined roster must intersect. The
runtime-checkable overlap condition for safe reconfiguration. -/
theorem inter_of_card_gt_union (M N Q Q' : Finset α) (hQ : Q ⊆ M) (hQ' : Q' ⊆ N)
    (h : Q.card + Q'.card > (M ∪ N).card) : ∃ a, a ∈ Q ∧ a ∈ Q' := by
  by_contra hno
  push_neg at hno
  have hdisj : Disjoint Q Q' := Finset.disjoint_left.mpr (fun a ha ha' => hno a ha ha')
  have hle : (Q ∪ Q').card ≤ (M ∪ N).card :=
    Finset.card_le_card (Finset.union_subset_union hQ hQ')
  rw [Finset.card_union_of_disjoint hdisj] at hle
  omega

/-- A concrete configuration: an explicit roster of members. Quorum = strict majority. -/
structure Config (α : Type*) where
  /-- The authorised member roster. -/
  members : Finset α

/-- A per-action certificate: the chosen value and the members who voted for it. -/
structure Cert (α V : Type*) where
  /-- The value the certificate claims was chosen. -/
  value : V
  /-- The members who voted for it (the carried evidence). -/
  voters : Finset α

/-- The decidable acceptance predicate: the voters are members, form a strict majority of
the roster, and each one's recorded vote matches the certificate's value. -/
def Valid (cfg : Config α) (vote : α → Option V) (c : Cert α V) : Prop :=
  c.voters ⊆ cfg.members ∧
  2 * c.voters.card > cfg.members.card ∧
  ∀ a ∈ c.voters, vote a = some c.value

instance (cfg : Config α) (vote : α → Option V) (c : Cert α V) :
    Decidable (Valid cfg vote c) := by
  unfold Valid; infer_instance

/-- The checker as a runnable `Bool`. -/
def check (cfg : Config α) (vote : α → Option V) (c : Cert α V) : Bool :=
  decide (Valid cfg vote c)

theorem check_iff (cfg : Config α) (vote : α → Option V) (c : Cert α V) :
    check cfg vote c = true ↔ Valid cfg vote c := by
  unfold check; exact decide_eq_true_iff

/-- **Bridge soundness.** Two certificates both valid against the same configuration have
equal values. The checker can never discharge two conflicting actions. -/
theorem cert_agreement (cfg : Config α) (vote : α → Option V) (c c' : Cert α V)
    (h : Valid cfg vote c) (h' : Valid cfg vote c') : c.value = c'.value := by
  obtain ⟨hsub, hmaj, hvotes⟩ := h
  obtain ⟨hsub', hmaj', hvotes'⟩ := h'
  obtain ⟨a, ha, ha'⟩ := majority_inter_in cfg.members c.voters c'.voters hsub hsub' hmaj hmaj'
  have e1 := hvotes a ha
  have e2 := hvotes' a ha'
  rw [e1] at e2
  exact Option.some.inj e2

/-- **No conflicting pair is ever accepted.** If `check` accepts two certificates against
the same configuration, they cannot carry different values. -/
theorem no_conflicting_certs (cfg : Config α) (vote : α → Option V) (c c' : Cert α V)
    (h : check cfg vote c = true) (h' : check cfg vote c' = true) :
    c.value = c'.value :=
  cert_agreement cfg vote c c' ((check_iff cfg vote c).mp h) ((check_iff cfg vote c').mp h')

/-- **Bridge soundness across a reconfiguration.** Two certificates valid against
*different* configurations agree, given a decidable per-instance overlap witness: their
voter counts exceed the combined roster. The runtime-checkable form of
`Reconfig.Compatible`. -/
theorem cert_agreement_cross (cfg cfg' : Config α) (vote : α → Option V) (c c' : Cert α V)
    (h : Valid cfg vote c) (h' : Valid cfg' vote c')
    (hoverlap : c.voters.card + c'.voters.card > (cfg.members ∪ cfg'.members).card) :
    c.value = c'.value := by
  obtain ⟨hsub, _, hvotes⟩ := h
  obtain ⟨hsub', _, hvotes'⟩ := h'
  obtain ⟨a, ha, ha'⟩ :=
    inter_of_card_gt_union cfg.members cfg'.members c.voters c'.voters hsub hsub' hoverlap
  have e1 := hvotes a ha
  have e2 := hvotes' a ha'
  rw [e1] at e2
  exact Option.some.inj e2

end Consensus.Bridge
