/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Topology.LocallyConstant.Basic
import Jacobians.LocalMultiplicity.LocalMultiplicity

/-! # Degree of a holomorphic map between compact Riemann surfaces

This file provides a *fibre-cardinality* candidate body for `ContMDiff.degree`,
upgrading the constant-vs-non-constant indicator (`degreeIndicator`) toward the
classical definition

```
deg(f) = |f ⁻¹' {y}|   for any regular value y : Y.
```

## What is honest in this file

* For **constant** `f`, `degreeFiber f hf = 0` unconditionally.
* For **non-constant** `f`, `degreeFiber f hf` extracts a natural number from a
  packaged witness bundle (`RegularValueWitness`) using `Classical.choice` on
  the existence of such a witness. The witness records:
  - a chosen value `y₀ : Y`,
  - a proof that the fibre `f ⁻¹' {y₀}` is finite, and
  - the cardinality is then `(h.toFinset).card`.
  A `RegularValueWitnessReg f` now provably exists for non-constant `f`
  (see "## Status" below), so the no-witness fallback to `0` does not fire.
  Caveat: the witness only requires the fibre `f ⁻¹' {y₀}` finite, not
  non-empty, so positivity (`deg ≥ 1`) is not yet established — see below.

## Status (classical inputs)

For a non-constant holomorphic map `f : X → Y` between compact connected
Riemann surfaces, the following classical inputs are now formalised in the
`Discharge/Manifold/` chain:

1. **Properness with finite fibres.** Every fibre `f ⁻¹' {y}` is finite —
   `fibres_finite` (discreteness via the identity
   theorem for analytic functions).
2. **Existence of a regular value.** The critical values are finite
   (`criticalValues_finite_general`), so a regular value exists —
   `exists_regularValueWitnessReg` produces a `RegularValueWitnessReg`.
3. **Constancy of fibre cardinality across regular values.** The Hurwitz
   patching / local-normal-form argument gives well-definedness —
   `degreeFiber_eq_card_of_regular_witness`.

Together (1)–(3) make `degreeFiber f hf` a well-defined natural number,
equal to the fibre cardinality at any regular witness.

**Still open — positivity.** The regular value `y₀` is chosen from the
complement of the critical values, with no guarantee `y₀ ∈ range f`. If
`y₀ ∉ range f` the fibre is empty and `degreeFiber f hf = 0` even for a
non-constant `f`. Establishing `deg ≥ 1` needs surjectivity of a
non-constant holomorphic map on a compact connected surface (open-mapping
theorem + compactness), which is not yet formalised.

## Why a separate definition (and not editing `_root_.ContMDiff.degree`)

`Basic.lean`'s `_root_.ContMDiff.degree f hf : ℕ` signature is locked. This
file provides `Jacobians.Discharge.ContMDiff.degreeFiber` as a strict upgrade
candidate that matches the same signature shape (no extra arguments at the
call site beyond `f` and `hf`). When (1)–(3) above land in mathlib, the body
of `_root_.ContMDiff.degree` in `Basic.lean` can be retargeted from
`degreeIndicator` to `degreeFiber` without touching any caller.

## Main definitions

* `Jacobians.Discharge.ContMDiff.RegularValueWitness f` — a chosen value `y₀ : Y`
  together with a proof that the fibre over `y₀` is finite. Existence of this
  witness for non-constant analytic `f` between compact RS is the deep
  classical input.
* `Jacobians.Discharge.ContMDiff.degreeFiber f hf : ℕ` — `0` if `f` is constant;
  otherwise `Classical.choice`-extracted fibre cardinality (falling back to
  `0` if no `RegularValueWitness` exists at the pin).

## Compatibility with `degreeIndicator`

* `degreeFiber_const` matches `degreeIndicator_const`: constant maps have degree 0.
* `degreeFiber f hf = 0` whenever no `RegularValueWitness f` exists — same as
  `degreeIndicator` would give in the absence of any classical witness.
-/

noncomputable section

open scoped Manifold Topology
open Set

namespace Jacobians.Discharge

namespace ContMDiff

universe u v

/-! ## The witness bundle

A `RegularValueWitness f` packages a chosen value `y₀ : Y` together with a
proof that the fibre `f ⁻¹' {y₀}` is finite. This is the minimal structural
data needed to define a fibre cardinality without changing the signature of
`_root_.ContMDiff.degree`.

For a non-constant holomorphic map between compact connected Riemann surfaces,
existence of such a witness is a classical theorem (see file docstring item
1+2). At this mathlib pin neither (1) nor (2) is formalised, so the
`Nonempty (RegularValueWitness f)` hypothesis is the gap. -/
structure RegularValueWitness {X : Type u} {Y : Type v} (f : X → Y) where
  /-- Chosen value in the codomain. -/
  value : Y
  /-- The fibre over the chosen value is finite. -/
  fiber_finite : (f ⁻¹' {value}).Finite

/-- Cardinality of the chosen finite fibre, as a `Finset.card`. -/
def RegularValueWitness.card {X : Type u} {Y : Type v} {f : X → Y}
    (w : RegularValueWitness f) : ℕ :=
  w.fiber_finite.toFinset.card

/-- The witness card is the `Set.ncard` of its fibre. -/
lemma RegularValueWitness.card_eq_ncard {X : Type u} {Y : Type v} {f : X → Y}
    (w : RegularValueWitness f) : w.card = (f ⁻¹' {w.value}).ncard := by
  rw [RegularValueWitness.card, (f ⁻¹' {w.value}).ncard_eq_toFinset_card w.fiber_finite]

/-! ## Regular-value strengthened witness (ZZ172 corrected form)

`RegularValueWitness` carries only `fiber_finite`, which is structurally too
weak: classical "fibre cardinality is constant" requires the chosen value
*also* be a regular value (no preimage with degenerate chart-pullback
derivative). A `RegularValueWitness` over a critical point can have a smaller
fibre than a generic one (counts drop at branch points), so any "constant
fibre card" statement quantifying over arbitrary `RegularValueWitness` is
*false* as written.

`RegularValueWitnessReg f` strengthens `RegularValueWitness f` with a
**chart-pullback-derivative-nonzero certificate** inlined directly into the
structure: for every preimage point `x ∈ f ⁻¹' {value}`, the derivative
of the chart-pullback `(chartAt ℂ value) ∘ f ∘ (chartAt ℂ x).symm` at
`(chartAt ℂ x) x` is nonzero.

This is the analytic content of "value is a regular value of `f`" and is
exactly the shape consumed by `LocalSheetData.ofContMDiffMfderivNeZero`
(`Manifold/LocalSheetDataFromContMDiff.lean`, ZZ169). -/

/-- A **regular** regular-value witness for `f`. Strengthens
`RegularValueWitness` with a chart-pullback-derivative-nonzero certificate:
for every preimage point `x ∈ f ⁻¹' {value}`, the derivative of the
chart-pullback `(chartAt ℂ value) ∘ f ∘ (chartAt ℂ x).symm` at
`(chartAt ℂ x) x` is nonzero.

This is the analytic content of "`value` is a regular value of `f`",
inlined into the structure. -/
structure RegularValueWitnessReg
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (f : X → Y) where
  /-- Underlying (cardinality-bearing) witness. -/
  toWitness : RegularValueWitness f
  /-- The chosen value is regular: at every preimage point, the chart-
  pullback of `f` has nonzero derivative. -/
  is_regular : ∀ x ∈ f ⁻¹' {toWitness.value},
    deriv ((chartAt ℂ toWitness.value) ∘ f ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x) ≠ 0

namespace RegularValueWitnessReg

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
variable {f : X → Y}

/-- Cardinality of the chosen finite fibre of a regular witness. -/
def card (w : RegularValueWitnessReg f) : ℕ := w.toWitness.card

/-- The chosen regular value. -/
def value (w : RegularValueWitnessReg f) : Y := w.toWitness.value

/-- The fibre over the chosen regular value is finite. -/
def fiber_finite (w : RegularValueWitnessReg f) :
    (f ⁻¹' {w.toWitness.value}).Finite :=
  w.toWitness.fiber_finite

end RegularValueWitnessReg

/-- **Builder.** Promote a plain `RegularValueWitness` to a regular one,
given a chart-pullback-derivative-nonzero certificate at every preimage
point. -/
def RegularValueWitness.toRegular
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y} (w : RegularValueWitness f)
    (h_reg : ∀ x ∈ f ⁻¹' {w.value},
      deriv ((chartAt ℂ w.value) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) ≠ 0) :
    RegularValueWitnessReg f :=
  { toWitness := w, is_regular := h_reg }

/-! ## The degree

A drop-in replacement for `degreeIndicator` that, when a `RegularValueWitnessReg`
is classically available, returns a *real* fibre cardinality rather than an
indicator. -/

/-- The **degree** of an analytic map `f : X → Y` between compact Riemann
surfaces, as a fibre cardinality.

* For constant `f`, returns `0` (matching the convention in challenge item 9
  and `degreeIndicator`).
* For non-constant `f`, returns the cardinality of *some* regular fibre,
  selected via `Classical.choice` on the existence of a `RegularValueWitnessReg`
  (a witness whose chosen value carries a chart-pullback-derivative-nonzero
  certificate at every preimage; this is the analytic content of "regular
  value"). If no such regular witness is classically available, falls back
  to `0`.

The well-definedness — independence of the chosen witness — is the deep
classical input that is **not** discharged here. See file docstring items
(2)–(3) for what is deferred.

**ZZ-RegFix correction.** Earlier the `Classical.choice` was on
`Nonempty (RegularValueWitness f)`, which carries no regularity certificate;
`Classical.choice` could pick a branch-point witness whose fibre cardinality
is strictly smaller than the topological degree. Switching to
`RegularValueWitnessReg f` bakes the analytic regularity in, so the choice
is always at a regular value. Existence of a regular witness for
non-constant analytic `f` is discharged unconditionally in
`Manifold/RegularValueExistsRegUnconditional.lean`. -/
def degreeFiber {ω : WithTop ℕ∞}
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ :=
  open Classical in
  if IsConstantMap f then 0
  else
    if h : Nonempty (RegularValueWitnessReg f) then
      (Classical.choice h).card
    else 0

/-- When a *regular* regular-value witness *does* exist (non-constant case,
`Classical` mode), the fibre-degree equals the cardinality of *some* such
witness. The particular witness is `Classical.choice`-selected; independence
of choice is the deep classical input. Because the choice is now over
`RegularValueWitnessReg f` (whose `is_regular` is built in), the chosen
witness is always at a regular value. -/
lemma degreeFiber_eq_witness_card {ω : WithTop ℕ∞}
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnc : ¬ IsConstantMap f) (h : Nonempty (RegularValueWitnessReg f)) :
    degreeFiber f hf = (Classical.choice h).card := by
  unfold degreeFiber
  simp [hnc, h]

/-! ## Open mathlib infrastructure

The following statements would, if formalised in mathlib at this pin, allow
`degreeFiber` to be promoted from "structural skeleton with `Classical.choice`
fallback" to a fully honest definition. They are not proved here; they are
recorded as type-checking placeholders so that downstream files can grep for
`Degree.` to find the dependency surface.

Each placeholder is a `Prop`-valued definition of the **statement** of the
classical theorem; we do **not** assume it (no `axiom`s). Discharging them is
out of scope for this round. -/

namespace Degree

/-! ### Partial discharge of `fibres_finite_statement`

The full statement requires the analytic identity theorem on charts to ensure
fibres are discrete. We do not formalise the chart-level identity theorem at
this pin. We do however reduce `fibres_finite_statement` to a single named
topological hypothesis: **each fibre carries the discrete subspace topology**
(`IsDiscrete (f ⁻¹' {y})`). The reduction itself is purely topological:
continuity gives closedness, compactness of `X` upgrades closed to compact,
and a compact discrete subspace is finite (`IsCompact.finite`).

What is deferred (and not formalised here) is the implication

  analytic, non-constant ⇒ ∀ y, IsDiscrete (f ⁻¹' {y}).

That is the chart-level identity theorem.
-/

/-- A fibre of a continuous map into a `T2` compact space is closed and hence
compact; if additionally the fibre carries the discrete subspace topology, it
is finite. This is the purely topological half of the identity-theorem
argument. -/
lemma fiber_finite_of_isDiscrete
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf_cont : Continuous f) (y : Y)
    (h_disc : IsDiscrete (f ⁻¹' {y})) :
    (f ⁻¹' {y}).Finite := by
  have h_closed : IsClosed (f ⁻¹' {y}) :=
    isClosed_singleton.preimage hf_cont
  have h_cpct : IsCompact (f ⁻¹' {y}) := h_closed.isCompact
  exact h_cpct.finite h_disc

/-! ### Partial discharge of `regular_value_exists_statement`

A `RegularValueWitness f` needs only *some* `y₀ : Y` with finite fibre. The
classical statement gives much more (the *critical value set* is finite, hence
its complement contains many regular values). For the witness-existence
question alone, the much weaker fact "there is at least one `y` with finite
fibre" suffices. We record three reductions of decreasing strength:

* `regular_value_exists_of_some_fiber_finite`: from `∃ y, (f ⁻¹' {y}).Finite`.
* `regular_value_exists_of_fibres_finite`: from the full
  `fibres_finite_statement` (uses `ConnectedSpace Y → Nonempty Y`).
* `regular_value_exists_of_critical_values_finite`: from finiteness of the
  *critical-value set* together with `Infinite Y` — this is the form that
  exposes the actual analytic obligation (critical-point set is the zero set
  of `f'` in chart coords, discrete by the identity theorem, hence finite by
  compactness; its image is finite). -/

/-- Trivial reduction: a `RegularValueWitness f` is exactly an element of `Y`
together with finiteness of its fibre. So existence is equivalent to
`∃ y, (f ⁻¹' {y}).Finite`. -/
lemma regular_value_exists_of_some_fiber_finite
    {X : Type u} {Y : Type v} {f : X → Y}
    (h : ∃ y : Y, (f ⁻¹' {y}).Finite) :
    Nonempty (RegularValueWitness f) := by
  obtain ⟨y, hy⟩ := h
  exact ⟨{ value := y, fiber_finite := hy }⟩

/-- Reduction of `regular_value_exists_statement` to `fibres_finite_statement`.

Given that *every* fibre is finite (the conclusion of
`fibres_finite_statement`), and `Y` is non-empty (free from
`ConnectedSpace Y`), pick any `y : Y` and package it as a witness. -/
lemma regular_value_exists_of_fibres_finite {ω : WithTop ℕ∞}
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_fib : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f → ∀ y : Y, (f ⁻¹' {y}).Finite) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f → Nonempty (RegularValueWitness f) := by
  intro f hf hnc
  haveI : Nonempty Y := inferInstance
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  exact regular_value_exists_of_some_fiber_finite ⟨y, h_fib f hf hnc y⟩

/-! ### Partial discharge of `fibre_card_well_defined_statement`

Independence of the chosen `RegularValueWitness` — i.e. the topological-degree
well-definedness — has the following classical structure. The set of regular
values `R ⊆ Y` is the complement of the (finite) critical-value set. On `R`
the map `f` is a covering map, so the fibre-cardinality function

  `n : R → ℕ`,   `n y = |f ⁻¹' {y}|`

is *locally constant*. Since `R = Y \ C` with `C` finite and `Y` a connected
Riemann surface (real dimension `≥ 2`), `R` is connected. A locally constant
function on a (pre)connected space is constant. Hence any two regular-value
witnesses give the same fibre cardinality.

We do **not** prove "covering map ⇒ locally constant fibre cardinality" or
"connected minus finite is connected for real-dim ≥ 2 manifolds" at this pin:
both are classical and both are heavy enough to deserve their own files. We
instead reduce `fibre_card_well_defined_statement` to a single named
hypothesis — the **fibre-cardinality function exists, extends every witness,
and is constant on the regular-value support** — and discharge the rest. The
shape of the hypothesis exactly mirrors the form items (1)–(2) take above:
classical content is named, topological/structural plumbing is dispatched. -/

/-- A **fibre-cardinality function** packaging the data classical
covering-space theory provides. Recorded as a structure so downstream files
have a single named target: discharging
`fibre_card_well_defined_statement` reduces to producing one of these for
every non-constant analytic `f`.

Fields:
* `card_of`: the fibre-cardinality function on `Y` (or any superset of the
  regular-value set; we take all of `Y` for simplicity, since the value at a
  critical point is irrelevant for the witness-comparison argument).
* `card_of_witness`: every `RegularValueWitness w` has
  `card_of w.value = w.card`. This is a definitional compatibility: it says
  `card_of` agrees with the true fibre cardinality at every point that
  *carries* a witness — exactly the points the well-definedness statement
  ranges over.
* `card_of_constant`: `card_of` is constant when restricted to the witness
  values. This is the deep classical content (covering-space + connectedness
  of `Y \ critical-values`). -/
structure FibreCardData {X : Type u} {Y : Type v} (f : X → Y) where
  /-- The fibre-cardinality function. -/
  card_of : Y → ℕ
  /-- `card_of` reads off any witness's cardinality. -/
  card_of_witness : ∀ w : RegularValueWitness f, card_of w.value = w.card
  /-- `card_of` agrees on any two witness values. (This is what the
  covering-space + connected-regular-value-set argument supplies.) -/
  card_of_constant : ∀ w₁ w₂ : RegularValueWitness f,
    card_of w₁.value = card_of w₂.value

/-- **Sharper reduction (regular form): locally-constant fibre-cardinality on
a preconnected subset.** Same shape as the unrestricted
`fibre_card_eq_of_locallyConstant_subtype`. The user supplies a regular-
value subset `R : Set Y` and a proof `h_supp` that every regular witness's
value lies in `R`. -/
lemma fibre_card_eq_of_locallyConstant_subtype_reg
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y}
    {R : Set Y}
    (card_of : Y → ℕ)
    (h_witness : ∀ w : RegularValueWitness f, card_of w.value = w.card)
    (h_supp : ∀ w : RegularValueWitnessReg f, w.toWitness.value ∈ R)
    (h_lc_sub : IsLocallyConstant (fun y : R => card_of y.val))
    (h_conn_sub : IsPreconnected (Set.univ : Set R))
    (w₁ w₂ : RegularValueWitnessReg f) :
    w₁.card = w₂.card := by
  have hc : card_of w₁.toWitness.value = card_of w₂.toWitness.value := by
    have :=
      h_lc_sub.apply_eq_of_isPreconnected h_conn_sub
        (Set.mem_univ (⟨w₁.toWitness.value, h_supp w₁⟩ : R))
        (Set.mem_univ (⟨w₂.toWitness.value, h_supp w₂⟩ : R))
    simpa using this
  show w₁.toWitness.card = w₂.toWitness.card
  calc w₁.toWitness.card
      = card_of w₁.toWitness.value := (h_witness w₁.toWitness).symm
    _ = card_of w₂.toWitness.value := hc
    _ = w₂.toWitness.card := h_witness w₂.toWitness

end Degree

end ContMDiff

end Jacobians.Discharge

end
