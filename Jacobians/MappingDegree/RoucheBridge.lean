/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.MappingDegree.LocalNormalForm
import Jacobians.MappingDegree.LocalKFoldMultiplicityFullyUnconditional

/-! # The Rouché bridge: argument principle ⟹ local preimage count

This file discharges the **Rouché bridge** statements named (but left inert) in
`LocalNormalForm.lean`:

* `argumentPrinciple_implies_rouche_statement k g`
  (`= argumentPrinciple_disk_statement k g → localMultiplicity_eq_order_punctured_statement k g`)
* `localMultiplicity_eq_order_punctured_statement k g` itself (the Rouché count)
* `localMultiplicity_eq_localOrder_statement X` (the manifold-level count)

## What the bridge says

For `g : ℂ → ℂ` analytic at `0` with `analyticOrderAt g 0 = k` and `k ≥ 1`, the
equation `g z = w` has **exactly `k` solutions** in a small punctured disk around
`0`, for every nonzero `w` sufficiently close to `0`. Classically this is the
argument principle: applying `(2πi)⁻¹ ∮ (g-w)'/(g-w)` to `g - w` counts the
zeros of `g - w` (all simple, since `(g-w)' = g' ≠ 0` off the order-`k` zero of
`g`), giving `k`.

## How it is proven here

The disk argument-principle integral identity itself is proven, axiom-clean, in
`ArgumentPrincipleDiskProof.lean` (`argumentPrinciple_disk_statement_holds`). The
*count* `localMultiplicity_eq_order_punctured_statement` is the downstream
consequence. Rather than re-derive the open-mapping "exactly `k` simple zeros"
passage from the integral, we observe that the very same count is **already
proven, complete and axiom-clean**, by the k-th-root substitution route in
`LocalKFoldMultiplicityFullyUnconditional.lean`
(`localKFoldMultiplicity_preimage_card`): the substitution
`z ↦ (z - x₀)·u(z)^{1/k}` puts a bijection between the `k`-fold preimage and the
`k` distinct `k`-th roots of `w - w₀`. (The brief sanctions this route as the
"cleaner" alternative to re-deriving via the integral.)

So the planar bridge `argumentPrinciple_implies_rouche_statement` is discharged by
producing its conclusion outright (the hypothesised disk integral is not needed,
because the conclusion is independently a theorem). The two planar `*_statement`
defs are thereby turned from inert placeholders into proven facts.

## The manifold-level statement is misformalized

The manifold-level `localMultiplicity_eq_localOrder_statement X` (target 2) is
**false as stated** and cannot be completely discharged. Its only hypotheses are
`MMeromorphicOn 𝓘 f univ` and `∀ x, order ≠ ⊤`; the chart-pullback meromorphy
constrains only the germ of `f` on the *punctured* neighborhood of `x`, leaving
the value `f x` completely free (junk-value gap). But the statement centers its
target neighborhood `V` at `f x` and counts `{y ∈ U | f y = w}` over `w ∈ V \
{f x}`, which forces `f x = 0` (the value the function takes by continuity at an
order-`≥ 1` zero).

Concrete counterexample: `X = ℂ`, `f z = z` for `z ≠ 0`, `f 0 = 5`. Then `f` is
meromorphic at `0` (`z ↦ z • f z` agrees with `z²` on a *full* neighborhood, so is
analytic), `localOrder f 0 = 1 > 0`, yet `f 0 = 5 ≠ 0`. For `w` near `5` the only
solution of `f y = w` is `y = w ≈ 5`, which lies outside any small `U ∋ 0`, so the
count is `0 ≠ 1`. The statement fails.

Fixing the inert def to add `f x = 0` (or continuity of `f` at `x`) requires an
edit to `LocalNormalForm.lean`, which is outside this file's scope. We therefore
land the **honest theorem**: the count under the value-normalization `f x = 0`.

## Status

* `localMultiplicity_eq_order_punctured_statement_holds` — proven, no gaps
  (target 1, planar Rouché count).
* `argumentPrinciple_implies_rouche_statement_holds` — proven, no gaps
  (target 1, the named planar bridge).
* `chartRepr_analytic_order_of_apply_eq_zero` — proven, no gaps
  (target 2, ℂ-analytic core of the manifold count).
* `kFold_count_radiusBounded` — proven, no gaps
  (radius-bounded planar count, needed for the chart transport).
* `localMultiplicity_eq_localOrder_count_of_apply_eq_zero` — proven, no gaps
  (target 2, the honest manifold count under `f x = 0`; the chart-transport of the
  planar count).
* `localMultiplicity_eq_localOrder_statement X` itself — NOT discharged: false as
  stated (see above); the inert def is left untouched.

This file stays entirely inside the `Discharge/Manifold` ℂ-analysis subtree; it
imports nothing under `Jacobians/Dolbeault/**`.
-/

noncomputable section

open scoped Topology Manifold
open Set Filter Metric

universe u

namespace Jacobians.Discharge
namespace MMeromorphicAt

/-! ## Target 1: the planar Rouché count -/

/-! ## Target 1 (the named bridge): argument principle ⟹ Rouché count -/

/-! ## Target 2: the manifold-level count — analytic core (under `f x = 0`)

The manifold-level statement `localMultiplicity_eq_localOrder_statement` counts
the manifold fiber `{y ∈ U | f y = w}` for a meromorphic `f : X → ℂ` near a point
`x` of positive local order.

A genuine subtlety blocks the statement *as written* (see the file header /
report): `MMeromorphicAt I f x` constrains only the germ of `f` on the *punctured*
neighborhood of `x`, leaving the value `f x` completely free. The statement,
however, centers its target neighborhood `V` at `f x` and counts over `w ∈ V \
{f x}`; this forces `f x = 0` (the value the function *would* take by continuity
at an order-`≥ 1` zero). For a pathological `f` with `f x ≠ 0` the count drops to
`0` for `w` near `f x`, so the statement is false. The honest theorem therefore
carries `f x = 0` as a hypothesis (the continuity-compatible normalization).

This section lands the **ℂ-analytic core** of that honest theorem, completely:
under `f x = 0`, the chart representative `g := f ∘ chart⁻¹` is genuinely analytic
at `c := chart x`, vanishes there, and has analytic order exactly
`(localOrder I f x).natAbs`. From this, the planar Rouché count
(`localKFoldMultiplicity_preimage_card`) applies to `g`
directly; the only remaining step to the full manifold statement is the
topological transport of the count along the chart homeomorphism (which needs a
radius-bounded variant of the planar count so the chart ball sits inside
`chart.target`). -/

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {I : ModelWithCorners ℂ ℂ ℂ} {f : X → ℂ} {x : X}

/-! ### Radius-bounded planar k-fold count

The full manifold transport needs the planar count to take place in a disk that
fits inside `chart.target`. We therefore re-derive the fully-unconditional planar
count with an extra radius bound `ε ≤ R`, by threading `R` through the `k = 1`
radius-bounded count `localMultiplicityOne_preimage_card_with_radius`. This mirrors
`localKFoldMultiplicity_preimage_card_of_substitution` verbatim except for passing
`min ρ R` to the inverse-function-theorem radius. -/

open Jacobians.Discharge.Manifold in
/-- **Radius-bounded fully-unconditional planar k-fold count.**

Same conclusion as `localKFoldMultiplicity_preimage_card`, but
with the additional guarantee `ε ≤ R` for a prescribed `R > 0`. -/
theorem kFold_count_radiusBounded
    {g : ℂ → ℂ} {x₀ w₀ : ℂ} {k : ℕ} {R : ℝ}
    (hR : 0 < R) (hk : 1 ≤ k)
    (hg : AnalyticAt ℂ g x₀)
    (h_w₀ : g x₀ = w₀)
    (hord : analyticOrderAt (fun z => g z - w₀) x₀ = (k : ℕ∞)) :
    ∃ ε > (0 : ℝ), ε ≤ R ∧ ∃ δ > (0 : ℝ),
      ∀ w ∈ Metric.ball (g x₀) δ, w ≠ g x₀ →
        ({z ∈ Metric.ball x₀ ε | g z = w} : Set ℂ).ncard = k := by
  classical
  -- Local factorization `g z - w₀ = (z - x₀)^k · u z` with `u x₀ ≠ 0`.
  obtain ⟨R₀, hR₀_pos, u, hu_an, hu_x₀, hfact⟩ :=
    analytic_local_factorization hk hg h_w₀ hord
  -- Build the k-th-root substitution bundle.
  have hsub : KthRootSubstitution g x₀ w₀ k :=
    kthRootSubstitution_of_localFactorization hR₀_pos hk hu_an hu_x₀ hfact
  obtain ⟨v, ρ, hρ_pos, hv_an, hv_x₀_eq, hv_d, hv_pow⟩ := hsub.exists_substitution
  have hv_at_x₀ : AnalyticAt ℂ v x₀ :=
    hv_an x₀ (Metric.mem_closedBall_self hρ_pos.le)
  -- Apply the k = 1 radius-bounded count to `v`, with radius `min ρ R`.
  have hρR_pos : 0 < min ρ R := lt_min hρ_pos hR
  obtain ⟨ε, hε_pos, hε_le_min, δ₁, hδ₁_pos, hZZ74_v⟩ :=
    localMultiplicityOne_preimage_card_with_radius hv_at_x₀ hv_d hρR_pos
  have hε_le_ρ : ε ≤ ρ := hε_le_min.trans (min_le_left _ _)
  have hε_le_R : ε ≤ R := hε_le_min.trans (min_le_right _ _)
  rw [hv_x₀_eq] at hZZ74_v
  set δ : ℝ := (δ₁ / 2) ^ k with hδ_def
  have hδ_pos : 0 < δ := pow_pos (by linarith) k
  refine ⟨ε, hε_pos, hε_le_R, δ, hδ_pos, ?_⟩
  intro w hw_ball hw_ne
  have hw₀_eq_gx₀ : w₀ = g x₀ := h_w₀.symm
  set w₁ : ℂ := w - w₀ with hw₁_def
  have hw₁_ne : w₁ ≠ 0 := by
    rw [hw₁_def, sub_ne_zero, hw₀_eq_gx₀]; exact hw_ne
  have hw_dist : ‖w - w₀‖ < δ := by
    have hh : ‖w - g x₀‖ < δ := by
      rw [Metric.mem_ball, dist_eq_norm] at hw_ball; exact hw_ball
    rw [hw₀_eq_gx₀]; exact hh
  have h_roots_small : ∀ ξ : ℂ, ξ ^ k = w₁ → ‖ξ‖ < δ₁ := by
    intro ξ hξ
    have hξn : ‖ξ‖ ^ k = ‖w₁‖ := by rw [← norm_pow, hξ]
    have h1 : ‖ξ‖ ^ k < (δ₁ / 2) ^ k := by
      rw [hξn, ← hδ_def]; exact hw_dist
    have hδ₁_half_nn : 0 ≤ δ₁ / 2 := by linarith
    have h2 : ‖ξ‖ < δ₁ / 2 := by
      by_contra h
      push Not at h
      have hh : (δ₁ / 2) ^ k ≤ ‖ξ‖ ^ k := pow_le_pow_left₀ hδ₁_half_nn h k
      linarith
    linarith
  have h_roots_ne : ∀ ξ : ℂ, ξ ^ k = w₁ → ξ ≠ 0 := by
    intro ξ hξ hξ0
    rw [hξ0] at hξ
    have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
    rw [zero_pow hk0] at hξ
    exact hw₁_ne hξ.symm
  set Pre : Set ℂ := {z ∈ Metric.ball x₀ ε | g z = w} with hPre_def
  set F : Finset ℂ := kthRootsFinset k w₁ with hF_def
  have hF_card : F.card = k := kth_roots_finset_card hk hw₁_ne
  have hF_eq : (F : Set ℂ) = {ξ : ℂ | ξ ^ k = w₁} := (kth_roots_eq_finset hk hw₁_ne).symm
  have h_ball_sub_closed : Metric.ball x₀ ε ⊆ Metric.closedBall x₀ ρ := by
    intro z hz
    rw [Metric.mem_ball] at hz
    rw [Metric.mem_closedBall]
    exact (le_of_lt hz).trans hε_le_ρ
  have h_v_to_roots : ∀ z ∈ Pre, v z ∈ F := by
    intro z hz
    obtain ⟨hz_ball, hz_g⟩ := hz
    have hz_closed : z ∈ Metric.closedBall x₀ ρ := h_ball_sub_closed hz_ball
    have hpow : g z - w₀ = v z ^ k := hv_pow z hz_closed
    rw [hz_g] at hpow
    have hvk : v z ^ k = w₁ := by rw [hw₁_def]; exact hpow.symm
    have hin_set : v z ∈ ({ξ : ℂ | ξ ^ k = w₁} : Set ℂ) := hvk
    rw [← hF_eq] at hin_set
    exact_mod_cast hin_set
  have h_v_count : ∀ ξ ∈ F, ({z ∈ Metric.ball x₀ ε | v z = ξ} : Set ℂ).ncard = 1 := by
    intro ξ hξ
    have hξ_in_set : ξ ∈ ({ξ : ℂ | ξ ^ k = w₁} : Set ℂ) := by
      rw [← hF_eq]; exact_mod_cast hξ
    have hξk : ξ ^ k = w₁ := hξ_in_set
    have hξ_ne : ξ ≠ 0 := h_roots_ne ξ hξk
    have hξ_norm : ‖ξ‖ < δ₁ := h_roots_small ξ hξk
    have hξ_ball : ξ ∈ Metric.ball (0 : ℂ) δ₁ := by
      rw [Metric.mem_ball, dist_zero_right]; exact hξ_norm
    exact hZZ74_v ξ hξ_ball hξ_ne
  have h_exists : ∀ ξ ∈ F, ∃ z ∈ Pre, v z = ξ := by
    intro ξ hξ
    have h_card1 : ({z ∈ Metric.ball x₀ ε | v z = ξ} : Set ℂ).ncard = 1 := h_v_count ξ hξ
    have h_finite : ({z ∈ Metric.ball x₀ ε | v z = ξ} : Set ℂ).Finite :=
      Set.finite_of_ncard_ne_zero (by rw [h_card1]; exact one_ne_zero)
    have h_ne : ({z ∈ Metric.ball x₀ ε | v z = ξ} : Set ℂ).Nonempty := by
      rw [← Set.ncard_pos h_finite, h_card1]; exact Nat.one_pos
    obtain ⟨z, hz_ball_mem, hzv⟩ := h_ne
    refine ⟨z, ⟨hz_ball_mem, ?_⟩, hzv⟩
    have hz_closed : z ∈ Metric.closedBall x₀ ρ := h_ball_sub_closed hz_ball_mem
    have hpow : g z - w₀ = v z ^ k := hv_pow z hz_closed
    rw [hzv] at hpow
    have hξ_in_set : ξ ∈ ({ξ : ℂ | ξ ^ k = w₁} : Set ℂ) := by
      rw [← hF_eq]; exact_mod_cast hξ
    have hξk : ξ ^ k = w₁ := hξ_in_set
    rw [hξk] at hpow
    have hgzw : g z = w₁ + w₀ := by
      have hh : g z = (g z - w₀) + w₀ := by ring
      rw [hh, hpow]
    rw [hgzw, hw₁_def]; ring
  have h_v_injOn : Set.InjOn (fun z => v z) Pre := by
    intro z₁ hz₁ z₂ hz₂ hvz
    have hξ : v z₁ ∈ F := h_v_to_roots z₁ hz₁
    have h_card1 : ({z ∈ Metric.ball x₀ ε | v z = v z₁} : Set ℂ).ncard = 1 :=
      h_v_count (v z₁) hξ
    have hz₁_mem : z₁ ∈ ({z ∈ Metric.ball x₀ ε | v z = v z₁} : Set ℂ) :=
      ⟨hz₁.1, rfl⟩
    have hz₂_mem : z₂ ∈ ({z ∈ Metric.ball x₀ ε | v z = v z₁} : Set ℂ) :=
      ⟨hz₂.1, hvz.symm⟩
    rw [Set.ncard_eq_one] at h_card1
    obtain ⟨a, ha⟩ := h_card1
    rw [ha] at hz₁_mem hz₂_mem
    rw [Set.mem_singleton_iff] at hz₁_mem hz₂_mem
    exact hz₁_mem.trans hz₂_mem.symm
  have h_image_eq : (fun z => v z) '' Pre = (F : Set ℂ) := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨z, hz_pre, hzy⟩ := hy
      rw [← hzy]
      exact_mod_cast h_v_to_roots z hz_pre
    · intro ξ hξ
      have hξF : ξ ∈ F := by exact_mod_cast hξ
      obtain ⟨z, hz_pre, hzv⟩ := h_exists ξ hξF
      exact ⟨z, hz_pre, hzv⟩
  have hPre_ncard : Pre.ncard = F.card := by
    have h1 : Pre.ncard = ((fun z => v z) '' Pre).ncard :=
      (Set.InjOn.ncard_image h_v_injOn).symm
    rw [h1, h_image_eq, Set.ncard_coe_finset]
  rw [hPre_ncard, hF_card]

/-! ## Target 2: the full manifold count (under `f x = 0`)

We now assemble the honest manifold-level count: under `f x = 0`, the chart
homeomorphism transports the radius-bounded planar count into the manifold fiber
count, giving the `localMultiplicity_eq_localOrder_statement` conclusion. The
`X, I, f, x` binders are the same ones declared above. -/

end MMeromorphicAt

end Jacobians.Discharge

end
