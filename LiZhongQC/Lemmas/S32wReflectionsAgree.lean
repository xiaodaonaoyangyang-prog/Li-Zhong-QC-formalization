import LiZhongQC.Lemmas.S32wSeamElement

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace LiZhongQC

/-- `-g` and `g` act in the same way on `ℍ`. -/
theorem s32w_neg_smul (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : UpperHalfPlane) : (-g) • w = g • w := by
  apply UpperHalfPlane.ext
  rw [h36t_coe_smul, h36t_coe_smul]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
  push_cast
  have hden : ((g 1 0 : ℂ) * w + g 1 1) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) w
    simpa [UpperHalfPlane.denom] using this
  have hden' : (-(g 1 0 : ℂ)) * w + -(g 1 1 : ℂ) ≠ 0 := by
    intro h
    apply hden
    linear_combination -h
  rw [div_eq_div_iff hden' hden]
  ring

/-- A conjugator `N` carrying one diagonal hyperbolic matrix to another is diagonal or anti-diagonal. -/
theorem s32w_diag_conj (N Mv Mh : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h : N * Mv = Mh * N) (hv01 : Mv 0 1 = 0) (hv10 : Mv 1 0 = 0) (hv : |Mv 0 0| ≠ 1)
    (hh01 : Mh 0 1 = 0) (hh10 : Mh 1 0 = 0) (hh : |Mh 0 0| ≠ 1) :
    (N 0 1 = 0 ∧ N 1 0 = 0) ∨ (N 0 0 = 0 ∧ N 1 1 = 0) := by
  have key : ∀ i j, (N * Mv) i j = (Mh * N) i j := fun i j => by rw [h]
  have k00 := key 0 0
  have k01 := key 0 1
  have k10 := key 1 0
  have k11 := key 1 1
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hv01, hv10, hh01, hh10,
    mul_zero, zero_mul, add_zero, zero_add] at k00 k01 k10 k11
  have dv : Mv 0 0 * Mv 1 1 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe Mv
    rw [Matrix.det_fin_two, hv01, hv10] at this
    linarith
  have dh : Mh 0 0 * Mh 1 1 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe Mh
    rw [Matrix.det_fin_two, hh01, hh10] at this
    linarith
  have dN : N 0 0 * N 1 1 - N 0 1 * N 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe N
    rwa [Matrix.det_fin_two] at this
  set l := Mv 0 0 with hl
  set m := Mh 0 0 with hm
  have hl0 : l ≠ 0 := by intro h0; rw [h0, zero_mul] at dv; exact zero_ne_one dv
  have hm0 : m ≠ 0 := by intro h0; rw [h0, zero_mul] at dh; exact zero_ne_one dh
  have hli : Mv 1 1 = l⁻¹ := eq_inv_of_mul_eq_one_right dv
  have hmi : Mh 1 1 = m⁻¹ := eq_inv_of_mul_eq_one_right dh
  rw [hli] at k01
  rw [hmi] at k10
  rw [hli, hmi] at k11
  have hl1 : l ^ 2 ≠ 1 := by
    intro h2
    apply hv
    have : |l| ^ 2 = 1 := by rw [sq_abs]; exact h2
    nlinarith [abs_nonneg l]
  have hm1 : m ^ 2 ≠ 1 := by
    intro h2
    apply hh
    have : |m| ^ 2 = 1 := by rw [sq_abs]; exact h2
    nlinarith [abs_nonneg m]
  by_cases hlm : m = l
  · left
    rw [hlm] at k00 k01 k10 k11
    have e1 : N 0 1 * (l⁻¹ - l) = 0 := by linarith
    have e2 : N 1 0 * (l - l⁻¹) = 0 := by linarith
    have hne : l⁻¹ - l ≠ 0 := by
      intro h0
      apply hl1
      have h1 : l * l⁻¹ = 1 := mul_inv_cancel₀ hl0
      have hh : l⁻¹ = l := by linarith
      rw [hh] at h1
      nlinarith
    refine ⟨?_, ?_⟩
    · rcases mul_eq_zero.mp e1 with h0 | h0
      · exact h0
      · exact absurd h0 hne
    · rcases mul_eq_zero.mp e2 with h0 | h0
      · exact h0
      · exact absurd h0 (fun h' => hne (by linarith))
  · by_cases hlm' : m = l⁻¹
    · right
      have e1 : N 0 0 * (l - m) = 0 := by linarith
      have e2 : N 1 1 * (l⁻¹ - m⁻¹) = 0 := by linarith
      have hne1 : l - m ≠ 0 := fun h0 => hlm (by linarith)
      have hne2 : l⁻¹ - m⁻¹ ≠ 0 := by
        intro h0
        apply hlm
        have : l⁻¹ = m⁻¹ := by linarith
        exact (inv_injective this).symm
      refine ⟨?_, ?_⟩
      · rcases mul_eq_zero.mp e1 with h0 | h0
        · exact h0
        · exact absurd h0 hne1
      · rcases mul_eq_zero.mp e2 with h0 | h0
        · exact h0
        · exact absurd h0 hne2
    · exfalso
      have e00 : N 0 0 * (l - m) = 0 := by linarith
      have e01 : N 0 1 * (l⁻¹ - m) = 0 := by linarith
      have n00 : N 0 0 = 0 := by
        rcases mul_eq_zero.mp e00 with h0 | h0
        · exact h0
        · exact absurd (by linarith : m = l) hlm
      have n01 : N 0 1 = 0 := by
        rcases mul_eq_zero.mp e01 with h0 | h0
        · exact h0
        · exact absurd (by linarith : m = l⁻¹) hlm'
      rw [n00, n01] at dN
      norm_num at dN

/-- **L3.**  Two anti-holomorphic reflections `R_v = a_v⁻¹ c a_v`, `R_h = a_h⁻¹ c a_h` of `ℍ`, both commuting
with the same non-trivial element `δ` of a freely acting group, coincide. -/
theorem s32w_reflections_agree (Rv Rh : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hfree : ∀ τ : UpperHalfPlane, δ • τ = τ → δ = 1 ∨ δ = -1)
    (hnt : ¬ ∀ τ : UpperHalfPlane, δ • τ = τ)
    (hcv : ∀ τ, Rv (δ • τ) = δ • Rv τ) (hch : ∀ τ, Rh (δ • τ) = δ • Rh τ)
    (av ah : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hav : ∀ τ : UpperHalfPlane, ((av • Rv τ : UpperHalfPlane) : ℂ) = -conj ((av • τ : UpperHalfPlane) : ℂ))
    (hah : ∀ τ : UpperHalfPlane, ((ah • Rh τ : UpperHalfPlane) : ℂ) = -conj ((ah • τ : UpperHalfPlane) : ℂ)) :
    ∀ τ, Rv τ = Rh τ := by
  obtain ⟨c, hc⟩ := s32w_refl_exists
  obtain ⟨σ, hσ⟩ := s32w_sigma_exists
  obtain ⟨v1, v2, v3⟩ := s32w_commute_diag Rv av δ hav hcv hfree hnt
  obtain ⟨h1, h2, h3⟩ := s32w_commute_diag Rh ah δ hah hch hfree hnt
  have hNN : (ah * av⁻¹) * (av * δ * av⁻¹) = (ah * δ * ah⁻¹) * (ah * av⁻¹) := by group
  have hcases := s32w_diag_conj _ _ _ hNN v1 v2 v3 h1 h2 h3
  set N := ah * av⁻¹ with hN
  -- `N` commutes with the reflection `c`
  have hNc : ∀ w, N • c w = c (N • w) := by
    intro w
    rw [s32w_refl_smul c hc σ hσ]
    rcases hcases with ⟨n1, n2⟩ | ⟨n1, n2⟩
    · have : σ N = N := by
        obtain ⟨s00, s01, s10, s11⟩ := hσ N
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [s00, s01, s10, s11, n1, n2]
      rw [this]
    · have : σ N = -N := by
        obtain ⟨s00, s01, s10, s11⟩ := hσ N
        apply Matrix.SpecialLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_neg, s00, s01, s10, s11, n1, n2]
      rw [this, s32w_neg_smul]
  have hRc : ∀ (R : UpperHalfPlane ≃ₜ UpperHalfPlane) (a : Matrix.SpecialLinearGroup (Fin 2) ℝ),
      (∀ τ : UpperHalfPlane, ((a • R τ : UpperHalfPlane) : ℂ) = -conj ((a • τ : UpperHalfPlane) : ℂ)) →
      ∀ τ, R τ = a⁻¹ • c (a • τ) := by
    intro R a ha τ
    have : a • R τ = c (a • τ) := by
      apply UpperHalfPlane.ext
      rw [ha, hc]
    rw [← this, inv_smul_smul]
  intro τ
  rw [hRc Rv av hav, hRc Rh ah hah]
  have hah' : ah = N * av := by rw [hN]; group
  rw [hah', mul_smul, ← hNc, ← mul_smul, mul_smul]
  simp [mul_smul]

end LiZhongQC
