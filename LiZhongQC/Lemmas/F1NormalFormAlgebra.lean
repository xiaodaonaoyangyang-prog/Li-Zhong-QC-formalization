import LiZhongQC.Lemmas.FoundationQuotient

/-! Small algebraic steps for the approved ft1fas_end_normal_form contract.
Source-only, uncompiled. No collar topology is repeated and no primitive
generator assumption is introduced. -/
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Inverting a generator preserves its signed cyclic subgroup literally. -/
theorem ft1fn_signed_cyclic_inv (h β : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (∃ k : ℤ, β = h ^ k ∨ β = -h ^ k) ↔
      (∃ k : ℤ, β = (h⁻¹) ^ k ∨ β = -(h⁻¹) ^ k) := by
  constructor
  · rintro ⟨k, hk | hk⟩
    · refine ⟨-k, Or.inl ?_⟩
      simpa only [inv_zpow, zpow_neg, inv_inv] using hk
    · refine ⟨-k, Or.inr ?_⟩
      simpa only [inv_zpow, zpow_neg, inv_inv] using hk
  · rintro ⟨k, hk | hk⟩
    · refine ⟨-k, Or.inl ?_⟩
      simpa only [inv_zpow, zpow_neg, inv_inv] using hk
    · refine ⟨-k, Or.inr ?_⟩
      simpa only [inv_zpow, zpow_neg, inv_inv] using hk

/-- Reverse the curve parameter when replacing the actual generator by its inverse. -/
theorem ft1fn_reverse_period (ρ : ℝ → UpperHalfPlane)
    (h : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hp : ∀ t : ℝ, ρ (t + 1) = h • ρ t) :
    ∀ t : ℝ, ρ (-(t + 1)) = h⁻¹ • ρ (-t) := by
  intro t
  have he : ρ (-t) = h • ρ (-(t + 1)) := by
    convert hp (-(t + 1)) using 1 <;> congr 1 <;> ring
  rw [he, inv_smul_smul]

/-- Set invariance under the actual period also gives invariance under its inverse. -/
theorem ft1fn_inverse_invariant (h : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (W : Set UpperHalfPlane) (hW : (fun τ : UpperHalfPlane => h • τ) '' W = W) :
    (fun τ : UpperHalfPlane => h⁻¹ • τ) '' W = W := by
  have he := congrArg (fun T : Set UpperHalfPlane => (fun τ => h⁻¹ • τ) '' T) hW
  simpa only [Set.image_image, Function.comp_def, inv_smul_smul, Set.image_id'] using he.symm

/-- Installed hyperbolic normalization, expressed in the exact coordinate direction
used by the end contract. The generator itself is retained. -/
theorem ft1fn_hyperbolic_coordinate {h : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hh : IsHyperbolic h) :
    ∃ (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (lam : ℝ), 1 < lam ∧
      ∀ τ : UpperHalfPlane, ((B⁻¹ • (h • (B • τ)) : UpperHalfPlane) : ℂ) =
        (lam : ℂ) * (τ : ℂ) := by
  obtain ⟨A, l, hl, -, hA⟩ := s30w_conj_dilation hh
  refine ⟨A⁻¹, l ^ 2, ?_, ?_⟩
  · nlinarith
  · intro τ
    simpa only [inv_inv, mul_smul] using hA τ

/-- A normalized high cusp inside a precisely invariant exterior detects the full
infinity stabilizer. The cyclic conclusion is derived from actual intersection,
not assumed as a primitivity input. -/
theorem ft1fn_high_cusp_stabilizer
    (W : Set UpperHalfPlane) (A h : Matrix.SpecialLinearGroup (Fin 2) ℝ) (Y : ℝ)
    (hhigh : {τ : UpperHalfPlane | Y < τ.im} ⊆ (fun τ => A • τ) ⁻¹' W)
    (hprec : ∀ β ∈ Γ, ((fun τ : UpperHalfPlane => β • τ) '' W ∩ W).Nonempty →
      ∃ k : ℤ, β = h ^ k ∨ β = -h ^ k) :
    ∀ β ∈ Γ, (A⁻¹ * β * A) 1 0 = 0 → ∃ k : ℤ, β = h ^ k ∨ β = -h ^ k := by
  intro β hβ hc
  let g : Matrix.SpecialLinearGroup (Fin 2) ℝ := A⁻¹ * β * A
  have hgc : g 1 0 = 0 := hc
  have hd : g 1 1 ≠ 0 := by
    intro he
    have ht := hnf_sl2_det g
    simp only [hgc, he, mul_zero, zero_mul, sub_zero] at ht
    norm_num at ht
  have hd2 : 0 < (g 1 1) ^ 2 := sq_pos_of_ne_zero hd
  let y : ℝ := (|Y| + 1) * ((g 1 1) ^ 2 + 1)
  have hy : 0 < y := by dsimp only [y]; positivity
  have hYy : Y < y := by
    have hp := mul_nonneg (show 0 ≤ |Y| + 1 by positivity) (sq_nonneg (g 1 1))
    dsimp only [y]
    nlinarith [le_abs_self Y]
  have hYgy : Y < y / (g 1 1) ^ 2 := by
    rw [lt_div_iff₀ hd2]
    have hp := mul_nonneg (sub_nonneg.mpr (le_abs_self Y)) (sq_nonneg (g 1 1))
    dsimp only [y]
    nlinarith [abs_nonneg Y]
  let τ : UpperHalfPlane := ⟨⟨0, y⟩, hy⟩
  have him : (g • τ).im = y / (g 1 1) ^ 2 := by
    change (((g • τ : UpperHalfPlane) : ℂ).im) = _
    rw [h36t_coe_smul, utm_im_mobius (hnf_sl2_det g)]
    simp only [hgc, Complex.ofReal_zero, zero_mul, zero_add, Complex.normSq_apply,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero]
    change y / (g 1 1 * g 1 1) = y / (g 1 1) ^ 2
    rw [pow_two]
  have hτW : A • τ ∈ W := hhigh hYy
  have hgτW : A • (g • τ) ∈ W := hhigh (by change Y < (g • τ).im; rw [him]; exact hYgy)
  have he : A • (g • τ) = β • (A • τ) := by
    simp only [g, mul_smul, smul_inv_smul]
  rw [he] at hgτW
  exact hprec β hβ ⟨β • (A • τ), ⟨A • τ, hτW, rfl⟩, hgτW⟩

end LiZhongQC
