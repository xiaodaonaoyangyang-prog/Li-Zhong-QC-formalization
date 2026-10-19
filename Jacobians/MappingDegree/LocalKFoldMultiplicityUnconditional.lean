/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Jacobians.MappingDegree.AnalyticKthRoot
import Mathlib.Analysis.Complex.Polynomial.Basic


/-! # k-fold local multiplicity from a local factorization

Composes the analytic k-th root (`AnalyticKthRoot.lean`), the substitution
bundle (`KthRootSubstitution`), and the multiplicity-one preimage count
(re-implemented inline with a radius bound) to give: under a local
analytic factorization `g(z) - w₀ = (z - x₀)^k · u(z)` with `u(x₀) ≠ 0`,
the equation `g z = w` has exactly `k` solutions in a small ball around
`x₀` for `w` near (but not equal to) `w₀`.

Bijection: `z ↦ v z` between
`{z ∈ ball x₀ ε | g z = w}` and `{ξ : ℂ | ξ^k = w - w₀}`. -/

noncomputable section

open scoped Topology
open Set Filter Metric

namespace Jacobians.Discharge
namespace Manifold

/-- **Bundle construction from a local factorization.** -/
theorem kthRootSubstitution_of_localFactorization
    {g u : ℂ → ℂ} {x₀ w₀ : ℂ} {R : ℝ} {k : ℕ}
    (hR : 0 < R) (hk : 1 ≤ k)
    (hu_an : AnalyticOnNhd ℂ u (Metric.closedBall x₀ R))
    (hu_x₀ : u x₀ ≠ 0)
    (hfact : ∀ z ∈ Metric.closedBall x₀ R,
        g z - w₀ = (z - x₀) ^ k * u z) :
    KthRootSubstitution g x₀ w₀ k := by
  obtain ⟨r, ρ', hρ'_pos, hρ'_le, hr_an, hr_pow⟩ :=
    analytic_kth_root_of_nonvanishing hR hu_an hu_x₀ hk
  refine ⟨⟨fun z => (z - x₀) * r z, ρ', hρ'_pos, ?_, ?_, ?_, ?_⟩⟩
  · intro z hz
    have h1 : AnalyticAt ℂ (fun ζ : ℂ => ζ - x₀) z :=
      analyticAt_id.sub analyticAt_const
    have h2 : AnalyticAt ℂ r z := hr_an z hz
    exact h1.mul h2
  · change (x₀ - x₀) * r x₀ = 0
    simp
  · have hx₀_in : x₀ ∈ Metric.closedBall x₀ ρ' := Metric.mem_closedBall_self hρ'_pos.le
    have hr_x₀_pow : r x₀ ^ k = u x₀ := hr_pow x₀ hx₀_in
    have hr_x₀_ne : r x₀ ≠ 0 := by
      intro h
      have hpow : (0 : ℂ) ^ k = u x₀ := by rw [← h]; exact hr_x₀_pow
      have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
      rw [zero_pow hk0] at hpow
      exact hu_x₀ hpow.symm
    have hr_diff : DifferentiableAt ℂ r x₀ := (hr_an x₀ hx₀_in).differentiableAt
    have hsub_diff : DifferentiableAt ℂ (fun ζ : ℂ => ζ - x₀) x₀ :=
      (differentiableAt_id).sub (differentiableAt_const x₀)
    have hderiv :
        deriv (fun z => (z - x₀) * r z) x₀ =
          deriv (fun ζ : ℂ => ζ - x₀) x₀ * r x₀ +
          (x₀ - x₀) * deriv r x₀ := by
      simpa using deriv_fun_mul hsub_diff hr_diff
    have hderiv_sub : deriv (fun ζ : ℂ => ζ - x₀) x₀ = 1 := by
      have hh : deriv (fun ζ : ℂ => ζ - x₀) x₀
            = deriv (id : ℂ → ℂ) x₀ - deriv (fun _ : ℂ => x₀) x₀ :=
        deriv_sub differentiableAt_id (differentiableAt_const x₀)
      rw [hh]; simp
    rw [hderiv, hderiv_sub, sub_self, zero_mul, add_zero, one_mul]
    exact hr_x₀_ne
  · intro z hz
    have hz_in_R : z ∈ Metric.closedBall x₀ R :=
      (Metric.closedBall_subset_closedBall hρ'_le) hz
    have h1 : g z - w₀ = (z - x₀) ^ k * u z := hfact z hz_in_R
    have h2 : r z ^ k = u z := hr_pow z hz
    rw [h1, ← h2, mul_pow]

/-- `localMultiplicityOne_preimage_card` with an extra radius bound `ε ≤ R`. -/
theorem localMultiplicityOne_preimage_card_with_radius
    {g : ℂ → ℂ} {x₀ : ℂ}
    (h_an : AnalyticAt ℂ g x₀) (hd : deriv g x₀ ≠ 0)
    {R : ℝ} (hR : 0 < R) :
    ∃ ε > (0 : ℝ), ε ≤ R ∧ ∃ δ > (0 : ℝ),
      ∀ w ∈ Metric.ball (g x₀) δ, w ≠ g x₀ →
        ({z ∈ Metric.ball x₀ ε | g z = w} : Set ℂ).ncard = 1 := by
  have hsd : HasStrictDerivAt g (deriv g x₀) x₀ := h_an.hasStrictDerivAt
  have hsfd :
      HasStrictFDerivAt g
        (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv g x₀) hd) :
          ℂ →L[ℂ] ℂ) x₀ :=
    hsd.hasStrictFDerivAt_equiv hd
  set φ : OpenPartialHomeomorph ℂ ℂ := hsfd.toOpenPartialHomeomorph g with hφ
  have h_x0_src : x₀ ∈ φ.source := hsfd.mem_toOpenPartialHomeomorph_source
  have h_w0_tgt : g x₀ ∈ φ.target := hsfd.image_mem_toOpenPartialHomeomorph_target
  have h_coe : (φ : ℂ → ℂ) = g := hsfd.toOpenPartialHomeomorph_coe
  have h_src_nhds : φ.source ∈ 𝓝 x₀ := φ.open_source.mem_nhds h_x0_src
  obtain ⟨ε₀, hε₀_pos, hε₀_sub⟩ := Metric.mem_nhds_iff.mp h_src_nhds
  set ε : ℝ := min ε₀ R with hε_def
  have hε_pos : 0 < ε := lt_min hε₀_pos hR
  have hε_le_R : ε ≤ R := min_le_right _ _
  have hε_le_ε₀ : ε ≤ ε₀ := min_le_left _ _
  have hε_sub : Metric.ball x₀ ε ⊆ φ.source := fun z hz =>
    hε₀_sub (Metric.ball_subset_ball hε_le_ε₀ hz)
  have h_symm_cont : ContinuousAt φ.symm (g x₀) :=
    (φ.continuousOn_symm).continuousAt (φ.open_target.mem_nhds h_w0_tgt)
  have h_symm_w0 : φ.symm (g x₀) = x₀ := by
    have hpre := φ.left_inv h_x0_src
    have hφx₀ : (φ : ℂ → ℂ) x₀ = g x₀ := by rw [h_coe]
    rw [hφx₀] at hpre
    exact hpre
  have h_ball_x0_nhds : Metric.ball x₀ ε ∈ 𝓝 x₀ :=
    Metric.ball_mem_nhds x₀ hε_pos
  have h_preimage_nhds : φ.symm ⁻¹' (Metric.ball x₀ ε) ∈ 𝓝 (g x₀) := by
    have ht := h_symm_cont.tendsto
    rw [h_symm_w0] at ht
    exact ht h_ball_x0_nhds
  have h_combo_nhds :
      φ.target ∩ φ.symm ⁻¹' (Metric.ball x₀ ε) ∈ 𝓝 (g x₀) :=
    Filter.inter_mem (φ.open_target.mem_nhds h_w0_tgt) h_preimage_nhds
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.mem_nhds_iff.mp h_combo_nhds
  refine ⟨ε, hε_pos, hε_le_R, δ, hδ_pos, ?_⟩
  intro w hw_ball hw_ne
  have hw_target : w ∈ φ.target := (hδ_sub hw_ball).1
  have hw_pre_in_ball : φ.symm w ∈ Metric.ball x₀ ε := (hδ_sub hw_ball).2
  have h_symm_w_src : φ.symm w ∈ φ.source := φ.map_target hw_target
  have h_g_symm : g (φ.symm w) = w := by
    have hr : (φ : ℂ → ℂ) (φ.symm w) = w := φ.right_inv hw_target
    rw [h_coe] at hr
    exact hr
  have h_preimage_eq :
      {z ∈ Metric.ball x₀ ε | g z = w} = {φ.symm w} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨⟨hw_pre_in_ball, h_g_symm⟩, ?_⟩
    intro z hz
    obtain ⟨hz_ball, hz_g⟩ := hz
    have hz_src : z ∈ φ.source := hε_sub hz_ball
    have hφz : (φ : ℂ → ℂ) z = w := by rw [h_coe]; exact hz_g
    have hφ_symm_w : (φ : ℂ → ℂ) (φ.symm w) = w := by
      rw [h_coe]; exact h_g_symm
    exact φ.injOn hz_src h_symm_w_src (hφz.trans hφ_symm_w.symm)
  rw [h_preimage_eq]
  exact Set.ncard_singleton _

/-! ## Cardinality of k-th roots of a nonzero complex number -/

/-- The k-th roots of a nonzero complex number, viewed as a `Finset`. -/
noncomputable def kthRootsFinset (k : ℕ) (a : ℂ) : Finset ℂ :=
  (Polynomial.X ^ k - Polynomial.C a : Polynomial ℂ).roots.toFinset

/-- The set of k-th roots of `a` equals `(kthRootsFinset k a : Set ℂ)`,
when `a ≠ 0` and `k ≥ 1`. -/
lemma kth_roots_eq_finset {k : ℕ} (hk : 1 ≤ k) {a : ℂ} (_ha : a ≠ 0) :
    {ξ : ℂ | ξ ^ k = a} = (kthRootsFinset k a : Set ℂ) := by
  set p : Polynomial ℂ := Polynomial.X ^ k - Polynomial.C a with hp_def
  have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  have hp_deg : p.natDegree = k := by
    rw [hp_def]; exact Polynomial.natDegree_X_pow_sub_C
  have hp_ne : p ≠ 0 := fun h => by
    rw [h] at hp_deg
    simp at hp_deg
    exact hk0 hp_deg.symm
  ext ξ
  simp only [Set.mem_setOf_eq, kthRootsFinset, Finset.mem_coe,
             Multiset.mem_toFinset]
  rw [Polynomial.mem_roots hp_ne]
  show ξ ^ k = a ↔ p.IsRoot ξ
  unfold Polynomial.IsRoot
  rw [hp_def]
  simp [sub_eq_zero, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C, eq_comm]

/-- The Finset of k-th roots has cardinality `k`. -/
lemma kth_roots_finset_card {k : ℕ} (hk : 1 ≤ k) {a : ℂ} (ha : a ≠ 0) :
    (kthRootsFinset k a).card = k := by
  classical
  set p : Polynomial ℂ := Polynomial.X ^ k - Polynomial.C a with hp_def
  have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  have hp_deg : p.natDegree = k := by
    rw [hp_def]; exact Polynomial.natDegree_X_pow_sub_C
  have h_separable : p.Separable := by
    rw [hp_def]
    exact Polynomial.separable_X_pow_sub_C a (by exact_mod_cast hk0) ha
  have h_splits : p.Splits := IsAlgClosed.splits p
  have h_card_roots : p.roots.card = p.natDegree :=
    Polynomial.splits_iff_card_roots.mp h_splits
  have h_nodup : p.roots.Nodup := Polynomial.nodup_roots h_separable
  unfold kthRootsFinset
  rw [show (Polynomial.X ^ k - Polynomial.C a : Polynomial ℂ) = p from rfl]
  rw [Multiset.toFinset_card_of_nodup h_nodup, h_card_roots, hp_deg]

/-! ## Main count from the bundle -/

end Manifold
end Jacobians.Discharge

end
