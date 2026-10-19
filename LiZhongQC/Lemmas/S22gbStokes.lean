import LiZhongQC.Lemmas.CurvatureDegreeBoundary

open Complex Set Filter Topology MeasureTheory
open scoped Real

noncomputable section
namespace LiZhongQC

/-- The real-linear identification `ℝ × ℝ → ℂ`. -/
abbrev s22gb_toC (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * I

theorem s22gb_toC_eq (p : ℝ × ℝ) : s22gb_toC p = Complex.equivRealProdCLM.symm p := by
  apply Complex.ext <;> simp [s22gb_toC]

/-- The product `u * f` composed with the identification has the expected derivative. -/
theorem s22gb_fderiv_toC {f : ℂ → ℝ} {p : ℝ × ℝ} (hf : DifferentiableAt ℝ f (s22gb_toC p))
    (v : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => f (s22gb_toC q)) p v = fderiv ℝ f (s22gb_toC p) (s22gb_toC v) := by
  have hι : HasFDerivAt (fun q : ℝ × ℝ => s22gb_toC q)
      (Complex.equivRealProdCLM.symm.toContinuousLinearMap) p := by
    have h := Complex.equivRealProdCLM.symm.hasFDerivAt (x := p)
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
    exact (s22gb_toC_eq q)
  have hcomp := HasFDerivAt.comp p hf.hasFDerivAt hι
  have h2 := hcomp.fderiv
  change fderiv ℝ (fun q : ℝ × ℝ => f (s22gb_toC q)) p = _ at h2
  rw [h2]
  simp [s22gb_toC_eq]

/-- Rectangle Stokes in the plane, for a function `u` and a real one-form family `α`:
`∫_K (u dα + du ∧ α)(1, I) = ∮_{∂K} u α`. -/
theorem s22gb_rect_stokes (u : ℂ → ℝ) (α : ℂ → ℂ → ℝ) (a b : ℂ) (hre : a.re ≤ b.re)
    (him : a.im ≤ b.im)
    (hu : ∀ z ∈ wv_rectK a b, ContDiffAt ℝ 1 u z)
    (hα1 : ∀ z ∈ wv_rectK a b, ContDiffAt ℝ 1 (fun w => α w 1) z)
    (hαI : ∀ z ∈ wv_rectK a b, ContDiffAt ℝ 1 (fun w => α w I) z) :
    (∫ z in wv_rectK a b,
      (u z * (fderiv ℝ (fun w => α w I) z 1 - fderiv ℝ (fun w => α w 1) z I) +
        (fderiv ℝ u z 1 * α z I - fderiv ℝ u z I * α z 1))) =
      s22cd_rectBoundary (fun ζ v => u ζ * α ζ v) a b := by
  classical
  set a' : ℝ × ℝ := (a.re, a.im) with ha'
  set b' : ℝ × ℝ := (b.re, b.im) with hb'
  have hab : a' ≤ b' := ⟨hre, him⟩
  have hmem : ∀ p ∈ Icc a' b', s22gb_toC p ∈ wv_rectK a b := by
    intro p hp
    rw [wv_rectK, Complex.mem_reProdIm, uIcc_of_le hre, uIcc_of_le him]
    exact ⟨by simpa [s22gb_toC] using And.intro hp.1.1 hp.2.1,
      by simpa [s22gb_toC] using And.intro hp.1.2 hp.2.2⟩
  have hK : wv_rectK a b = Complex.measurableEquivRealProd ⁻¹' Icc a' b' := by
    ext z
    rw [wv_rectK, Complex.mem_reProdIm, uIcc_of_le hre, uIcc_of_le him]
    simp only [mem_preimage, mem_Icc, Prod.le_def]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h1, h3⟩, h2, h4⟩
    · rintro ⟨⟨h1, h3⟩, h2, h4⟩
      exact ⟨⟨h1, h2⟩, h3, h4⟩
  let P : ℝ × ℝ → ℝ := fun q => u (s22gb_toC q) * α (s22gb_toC q) 1
  let Q : ℝ × ℝ → ℝ := fun q => u (s22gb_toC q) * α (s22gb_toC q) I
  have htoC : ContDiff ℝ 1 (fun q : ℝ × ℝ => s22gb_toC q) := by
    have hfun : (fun q : ℝ × ℝ => s22gb_toC q) = Complex.equivRealProdCLM.symm :=
      funext s22gb_toC_eq
    rw [hfun]
    exact Complex.equivRealProdCLM.symm.contDiff
  have hcd : ∀ (f : ℂ → ℝ), (∀ z ∈ wv_rectK a b, ContDiffAt ℝ 1 f z) →
      ∀ q ∈ Icc a' b', ContDiffAt ℝ 1 (fun q : ℝ × ℝ => f (s22gb_toC q)) q :=
    fun f hf q hq => (hf _ (hmem q hq)).comp q htoC.contDiffAt
  have hPd : ∀ q ∈ Icc a' b', ContDiffAt ℝ 1 P q := fun q hq =>
    (hcd u hu q hq).mul (hcd _ hα1 q hq)
  have hQd : ∀ q ∈ Icc a' b', ContDiffAt ℝ 1 Q q := fun q hq =>
    (hcd u hu q hq).mul (hcd _ hαI q hq)
  have hc : ContinuousOn (fun x => fderiv ℝ Q x (1, 0) - fderiv ℝ P x (0, 1)) (Icc a' b') := by
    intro q hq
    have h1 : ContinuousAt (fderiv ℝ Q) q := ((hQd q hq).fderiv_right (m := 0) (by simp)).continuousAt
    have h2 : ContinuousAt (fderiv ℝ P) q := ((hPd q hq).fderiv_right (m := 0) (by simp)).continuousAt
    exact ((h1.clm_apply continuousAt_const).sub (h2.clm_apply continuousAt_const)).continuousWithinAt
  have hbox : ∀ q : ℝ × ℝ, q ∈ Ioo a'.1 b'.1 ×ˢ Ioo a'.2 b'.2 → q ∈ Icc a' b' :=
    fun q hq => ⟨⟨hq.1.1.le, hq.2.1.le⟩, ⟨hq.1.2.le, hq.2.2.le⟩⟩
  have hst := s22cd_rectangle_stokes P Q (fun x => fderiv ℝ P x) (fun x => fderiv ℝ Q x) a' b' hab
    (fun q hq => (hPd q hq).continuousAt.continuousWithinAt)
    (fun q hq => (hQd q hq).continuousAt.continuousWithinAt)
    (fun q hq => ((hPd q (hbox q hq)).differentiableAt one_ne_zero).hasFDerivAt)
    (fun q hq => ((hQd q (hbox q hq)).differentiableAt one_ne_zero).hasFDerivAt) hc
  have hLR : (∫ z in wv_rectK a b,
      (u z * (fderiv ℝ (fun w => α w I) z 1 - fderiv ℝ (fun w => α w 1) z I) +
        (fderiv ℝ u z 1 * α z I - fderiv ℝ u z I * α z 1))) =
      ∫ x in Icc a' b', fderiv ℝ Q x (1, 0) - fderiv ℝ P x (0, 1) := by
    have hm := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding
      (fun x => fderiv ℝ Q x (1, 0) - fderiv ℝ P x (0, 1)) (Icc a' b')
    rw [← hm, hK]
    refine setIntegral_congr_fun
      (measurableSet_Icc.preimage Complex.measurableEquivRealProd.measurable) fun z hz => ?_
    have hzK : z ∈ wv_rectK a b := by rw [hK]; exact hz
    have hz' : s22gb_toC (z.re, z.im) = z := by simp [s22gb_toC]
    have hDu : DifferentiableAt ℝ u z := (hu z hzK).differentiableAt one_ne_zero
    have hD1 : DifferentiableAt ℝ (fun w => α w 1) z := (hα1 z hzK).differentiableAt one_ne_zero
    have hDI : DifferentiableAt ℝ (fun w => α w I) z := (hαI z hzK).differentiableAt one_ne_zero
    have e1 := s22gb_fderiv_toC (f := fun w => u w * α w I) (p := (z.re, z.im))
      (by rw [hz']; exact hDu.mul hDI) (1, 0)
    have e2 := s22gb_fderiv_toC (f := fun w => u w * α w 1) (p := (z.re, z.im))
      (by rw [hz']; exact hDu.mul hD1) (0, 1)
    rw [hz'] at e1 e2
    have h10 : s22gb_toC ((1 : ℝ), (0 : ℝ)) = 1 := by simp [s22gb_toC]
    have h01 : s22gb_toC ((0 : ℝ), (1 : ℝ)) = I := by simp [s22gb_toC]
    rw [h10, fderiv_fun_mul hDu hDI] at e1
    rw [h01, fderiv_fun_mul hDu hD1] at e2
    change _ = fderiv ℝ Q (z.re, z.im) (1, 0) - fderiv ℝ P (z.re, z.im) (0, 1)
    rw [show fderiv ℝ Q (z.re, z.im) (1, 0) = _ from e1,
      show fderiv ℝ P (z.re, z.im) (0, 1) = _ from e2]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hLR, hst]
  rfl

end LiZhongQC
