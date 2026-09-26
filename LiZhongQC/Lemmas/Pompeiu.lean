import LiZhongQC.Lemmas.GreenPolar
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Pompeiu's formula on a disc

This file proves the *two-Green identity* behind Pompeiu's formula (11.11):
for `f ∈ C¹(closedBall c R)`, `z ∈ ball c R` and `closedBall z ε ⊆ ball c R`,
```
∮_{C(c,R)} f ζ/(ζ - z) dζ = ∮_{C(z,ε)} f ζ/(ζ - z) dζ
    + 2i ∬_{ball c R \ ball z ε} (∂_z̄ f ζ)/(ζ - z) dA.
```

The textbook derivation applies Green's formula to `ζ ↦ f ζ/(ζ - z)` on the non-concentric
annulus `ball c R \ closedBall z ε`, which needs a Stokes formula that Mathlib does not have.
The trick used here avoids it: multiply the kernel by a smooth cutoff `χ` vanishing near `z`,
so that `g = χ · f/(· - z)` is `C¹` on the whole closed disc, and then apply the **concentric**
disc Green formula `green_disc_dzbar_closedBall` twice — once on `ball c R`, once on `ball z ε`.
The cutoff contributes a term `∬ (∂_z̄ χ) · f/(· - z)` supported in `ball z ε`, which is
identical in the two applications and therefore cancels when they are subtracted.  No limit in
the cutoff is needed, and `χ` disappears from the statement.

## Main results

* `dz_mul`, `dzbar_mul` — the Wirtinger product rules.
* `dzbar_inv_sub` — `∂_z̄ (ζ - z)⁻¹ = 0` away from `z`.
* `exists_kernel_cutoff` — a smooth `χ` vanishing on `ball z (ε/2)` and equal to `1` where
  `ε ≤ ‖· - z‖`, with `ζ ↦ χ ζ * (ζ - z)⁻¹` globally `C¹`.
* `circleIntegral_sub_circleIntegral_eq` — the two-Green identity.
* `exists_bound_dzbar` — `∂_z̄ f` is bounded on the open disc.
-/

open Complex Set MeasureTheory intervalIntegral Filter
open scoped Interval Real ComplexConjugate Topology ENNReal

noncomputable section
namespace LiZhongQC

/-! ## The Wirtinger product rules -/

/-- Product rule for `∂_z`. -/
theorem dz_mul {u v : ℂ → ℂ} {z : ℂ} (hu : DifferentiableAt ℝ u z)
    (hv : DifferentiableAt ℝ v z) :
    dz (fun w => u w * v w) z = u z * dz v z + v z * dz u z := by
  simp only [dz, fderiv_fun_mul hu hv, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  ring

/-- Product rule for `∂_z̄`. -/
theorem dzbar_mul {u v : ℂ → ℂ} {z : ℂ} (hu : DifferentiableAt ℝ u z)
    (hv : DifferentiableAt ℝ v z) :
    dzbar (fun w => u w * v w) z = u z * dzbar v z + v z * dzbar u z := by
  simp only [dzbar, fderiv_fun_mul hu hv, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  ring

/-- The Cauchy kernel is holomorphic away from its pole, so its `∂_z̄` vanishes there. -/
theorem dzbar_inv_sub {z w : ℂ} (hw : w ≠ z) :
    dzbar (fun ζ : ℂ => (ζ - z)⁻¹) w = 0 :=
  (cauchyRiemann_iff.1 ((differentiableAt_id.sub_const z).inv (sub_ne_zero.2 hw))).2

/-- The Cauchy kernel is `ℝ`-differentiable away from its pole. -/
theorem differentiableAt_inv_sub {z w : ℂ} (hw : w ≠ z) :
    DifferentiableAt ℝ (fun ζ : ℂ => (ζ - z)⁻¹) w := by
  have h : DifferentiableAt ℂ (fun ζ : ℂ => (ζ - z)⁻¹) w :=
    (differentiableAt_id.sub_const z).inv (sub_ne_zero.2 hw)
  exact h.restrictScalars ℝ

/-! ## A cutoff that smooths the Cauchy kernel -/

/-- A smooth cutoff `χ` for the pole at `z`: it vanishes on `ball z (ε/2)`, equals `1` wherever
`ε ≤ ‖· - z‖`, and `ζ ↦ χ ζ * (ζ - z)⁻¹` is globally `C¹` — the cutoff removes the pole. -/
theorem exists_kernel_cutoff (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ χ : ℂ → ℂ, ContDiff ℝ 1 χ ∧ (∀ w ∈ Metric.ball z (ε / 2), χ w = 0) ∧
      (∀ w : ℂ, ε ≤ ‖w - z‖ → χ w = 1) ∧
      ContDiff ℝ 1 (fun ζ : ℂ => χ ζ * (ζ - z)⁻¹) := by
  set b : ContDiffBump z := ⟨ε / 2, ε, by positivity, by linarith⟩ with hb
  refine ⟨fun w => 1 - ((b w : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · exact contDiff_const.sub (Complex.ofRealCLM.contDiff.comp b.contDiff)
  · intro w hw
    have h1 : b w = 1 :=
      b.one_of_mem_closedBall (by
        simp only [hb, Metric.mem_closedBall]
        exact le_of_lt (Metric.mem_ball.1 hw))
    simp [h1]
  · intro w hw
    have h0 : b w = 0 := by
      refine b.zero_of_le_dist ?_
      simpa only [hb, dist_eq_norm] using hw
    simp [h0]
  · rw [contDiff_iff_contDiffAt]
    intro x
    rcases eq_or_ne x z with rfl | hx
    · -- near `z` the cutoff is `0`, so the product vanishes identically
      have hev : (fun ζ : ℂ => (1 - ((b ζ : ℝ) : ℂ)) * (ζ - x)⁻¹) =ᶠ[nhds x]
          fun _ => (0 : ℂ) := by
        filter_upwards [Metric.ball_mem_nhds x (by positivity : (0 : ℝ) < ε / 2)] with w hw
        have h1 : b w = 1 :=
          b.one_of_mem_closedBall (by
            simp only [hb, Metric.mem_closedBall]
            exact le_of_lt (Metric.mem_ball.1 hw))
        simp [h1]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · exact (contDiff_const.sub
        (Complex.ofRealCLM.contDiff.comp b.contDiff)).contDiffAt.mul
        ((contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.2 hx))

/-- `∂_z̄` only depends on the germ. -/
theorem dzbar_congr_of_eventuallyEq {u v : ℂ → ℂ} {w : ℂ} (h : u =ᶠ[nhds w] v) :
    dzbar u w = dzbar v w := by
  simp only [dzbar, h.fderiv_eq]

/-! ## The two-Green identity -/

/-- **The two-Green identity.**  For `f ∈ C¹(closedBall c R)` and `closedBall z ε ⊆ ball c R`,
```
∮_{C(c,R)} f ζ/(ζ - z) dζ - ∮_{C(z,ε)} f ζ/(ζ - z) dζ
  = 2i ∬_{ball c R \ ball z ε} (∂_z̄ f ζ)/(ζ - z) dA.
```
Both circle integrals are produced by the *same* cutoff function `g = χ · f/(· - z)`, via the
concentric disc Green formula on `ball c R` and on `ball z ε`; the contribution of `∂_z̄ χ` is
therefore the same on both sides and cancels. -/
theorem circleIntegral_sub_circleIntegral_eq {f : ℂ → ℂ} {c z : ℂ} {R ε : ℝ} (hR : 0 < R)
    (hε : 0 < ε) (hf : ContDiffOn ℝ 1 f (Metric.closedBall c R))
    (hsub : Metric.closedBall z ε ⊆ Metric.ball c R) :
    (∮ ζ in C(c, R), f ζ / (ζ - z)) - (∮ ζ in C(z, ε), f ζ / (ζ - z))
      = 2 * I * ∫ ζ in Metric.ball c R \ Metric.ball z ε, dzbar f ζ / (ζ - z) := by
  obtain ⟨χ, hχ, hχ0, hχ1, hu⟩ := exists_kernel_cutoff z hε
  obtain ⟨g, hgdef⟩ : ∃ g : ℂ → ℂ, g = fun ζ => (χ ζ * (ζ - z)⁻¹) * f ζ := ⟨_, rfl⟩
  have hsub' : Metric.ball z ε ⊆ Metric.ball c R :=
    Metric.ball_subset_closedBall.trans hsub
  have hcbz : Metric.closedBall z ε ⊆ Metric.closedBall c R :=
    hsub.trans Metric.ball_subset_closedBall
  have hgR : ContDiffOn ℝ 1 g (Metric.closedBall c R) := by
    rw [hgdef]; exact hu.contDiffOn.mul hf
  have hgz : ContDiffOn ℝ 1 g (Metric.closedBall z ε) := by
    rw [hgdef]; exact hu.contDiffOn.mul (hf.mono hcbz)
  -- Green's formula on the two concentric discs
  have hG1 := green_disc_dzbar_closedBall hR hgR
  have hG2 := green_disc_dzbar_closedBall hε hgz
  -- on either circle the cutoff is `1`, so `g` is the Cauchy kernel there
  have hc1 : (∮ ζ in C(c, R), g ζ) = ∮ ζ in C(c, R), f ζ / (ζ - z) := by
    refine circleIntegral.integral_congr hR.le fun w hw => ?_
    have hwz : ε ≤ ‖w - z‖ := by
      by_contra hlt
      have hb : w ∈ Metric.ball c R := hsub (by
        simp only [Metric.mem_closedBall, dist_eq_norm]
        exact (not_le.1 hlt).le)
      rw [Metric.mem_ball, dist_eq_norm] at hb
      rw [Metric.mem_sphere, dist_eq_norm] at hw
      rw [hw] at hb
      exact lt_irrefl R hb
    simp only [hgdef]
    rw [hχ1 w hwz, one_mul, div_eq_mul_inv, mul_comm]
  have hc2 : (∮ ζ in C(z, ε), g ζ) = ∮ ζ in C(z, ε), f ζ / (ζ - z) := by
    refine circleIntegral.integral_congr hε.le fun w hw => ?_
    have hwz : ε ≤ ‖w - z‖ := by
      rw [Metric.mem_sphere, dist_eq_norm] at hw
      exact hw.ge
    simp only [hgdef]
    rw [hχ1 w hwz, one_mul, div_eq_mul_inv, mul_comm]
  -- split the area integral at the small disc
  have hint : IntegrableOn (dzbar g) (Metric.ball c R) := integrableOn_dzbar_ball hR hgR
  have hdisj : Disjoint (Metric.ball z ε) (Metric.ball c R \ Metric.ball z ε) :=
    Set.disjoint_left.2 fun a ha hb => hb.2 ha
  have hsplit : (∫ ζ in Metric.ball c R, dzbar g ζ)
      = (∫ ζ in Metric.ball z ε, dzbar g ζ)
        + ∫ ζ in Metric.ball c R \ Metric.ball z ε, dzbar g ζ := by
    rw [← MeasureTheory.setIntegral_union hdisj
      (measurableSet_ball.diff measurableSet_ball) (hint.mono_set hsub')
      (hint.mono_set Set.diff_subset), Set.union_diff_cancel hsub']
  -- outside the small disc the cutoff is `1`, so `∂_z̄ g = (∂_z̄ f)/(· - z)`
  have hdiff : (∫ ζ in Metric.ball c R \ Metric.ball z ε, dzbar g ζ)
      = ∫ ζ in Metric.ball c R \ Metric.ball z ε, dzbar f ζ / (ζ - z) := by
    refine MeasureTheory.setIntegral_congr_ae
      (measurableSet_ball.diff measurableSet_ball) ?_
    have h0 : ∀ᵐ ζ : ℂ, ζ ∉ Metric.sphere z ε := by
      rw [MeasureTheory.ae_iff]
      have hs : {a : ℂ | ¬ a ∉ Metric.sphere z ε} = Metric.sphere z ε := by
        ext a; simp
      rw [hs]
      exact MeasureTheory.Measure.addHaar_sphere (volume : Measure ℂ) z ε
    filter_upwards [h0] with ζ hζ hmem
    have hge : ε ≤ ‖ζ - z‖ := by
      have h2 := hmem.2
      simp only [Metric.mem_ball, dist_eq_norm, not_lt] at h2
      exact h2
    have hgt : ε < ‖ζ - z‖ := by
      rcases hge.lt_or_eq with h | h
      · exact h
      · exact absurd (by
          simp only [Metric.mem_sphere, dist_eq_norm]
          exact h.symm) hζ
    have hne : ζ ≠ z := by
      intro h
      rw [h, sub_self, norm_zero] at hgt
      exact absurd hgt (not_lt.2 hε.le)
    have hev : g =ᶠ[nhds ζ] fun w => (w - z)⁻¹ * f w := by
      have hopen : IsOpen {w : ℂ | ε < ‖w - z‖} :=
        isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
      filter_upwards [hopen.mem_nhds hgt] with w hw
      simp only [hgdef]
      rw [hχ1 w (le_of_lt hw), one_mul]
    have hfd : DifferentiableAt ℝ f ζ :=
      (hf.differentiableOn one_ne_zero).differentiableAt
        (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hmem.1)
          Metric.ball_subset_closedBall)
    rw [dzbar_congr_of_eventuallyEq hev,
      dzbar_mul (differentiableAt_inv_sub hne) hfd, dzbar_inv_sub hne, mul_zero, add_zero,
      div_eq_mul_inv, mul_comm]
  rw [← hc1, ← hc2, hG1, hG2, hsplit, hdiff]
  ring

/-! ## Boundedness of the formal derivative -/

/-- `∂_z̄ f` is bounded on the open disc when `f` is `C¹` on the closed disc: the `fderivWithin`
extends continuously to the compact closed disc, and agrees with `fderiv` in the interior.
This is the bound extracted from the proof of `integrableOn_dzbar_ball`. -/
theorem exists_bound_dzbar {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContDiffOn ℝ 1 f (Metric.closedBall c R)) :
    ∃ M : ℝ, ∀ ζ ∈ Metric.ball c R, ‖dzbar f ζ‖ ≤ M := by
  have hud : UniqueDiffOn ℝ (Metric.closedBall c R) :=
    uniqueDiffOn_convex (convex_closedBall c R)
      (by rw [interior_closedBall c hR.ne']; exact ⟨c, Metric.mem_ball_self hR⟩)
  have hcw : ContinuousOn (fderivWithin ℝ f (Metric.closedBall c R)) (Metric.closedBall c R) :=
    hf.continuousOn_fderivWithin hud le_rfl
  obtain ⟨M, hM⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hcw
  refine ⟨M, fun ζ hζ => ?_⟩
  have hζ' : ζ ∈ Metric.closedBall c R := Metric.ball_subset_closedBall hζ
  have hdiffAt : DifferentiableAt ℝ f ζ :=
    (hf.contDiffAt (Metric.closedBall_mem_nhds_of_mem hζ)).differentiableAt one_ne_zero
  have heq : fderiv ℝ f ζ = fderivWithin ℝ f (Metric.closedBall c R) ζ :=
    (fderivWithin_eq_fderiv (hud ζ hζ') hdiffAt).symm
  have hop := hM ζ hζ'
  have h1 : ‖fderiv ℝ f ζ 1‖ ≤ M := by
    rw [heq]
    have := (fderivWithin ℝ f (Metric.closedBall c R) ζ).le_opNorm (1 : ℂ)
    simpa using this.trans (by simpa using hop)
  have hI : ‖fderiv ℝ f ζ I‖ ≤ M := by
    rw [heq]
    have := (fderivWithin ℝ f (Metric.closedBall c R) ζ).le_opNorm I
    simpa using this.trans (by simpa using hop)
  have hb : ‖dzbar f ζ‖ ≤ (‖fderiv ℝ f ζ 1‖ + ‖fderiv ℝ f ζ I‖) / 2 := by
    simp only [dzbar, norm_div]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
    gcongr
    calc ‖fderiv ℝ f ζ 1 + I * fderiv ℝ f ζ I‖
        ≤ ‖fderiv ℝ f ζ 1‖ + ‖I * fderiv ℝ f ζ I‖ := norm_add_le _ _
      _ = ‖fderiv ℝ f ζ 1‖ + ‖fderiv ℝ f ζ I‖ := by simp
  linarith

end LiZhongQC
