import LiZhongQC.Ch07.S27_TeichmullerExistence

/-!
# Standard generators for a closed surface group (R83): algebra and monodromy

`s83sg_normalize` (matrix algebra: diagonalize a hyperbolic `δ`, normalize `γ(1) = 1`, `bc > 0` from
`tr[γ, δ] < 2`) and `s83sg_deck_pi1` (the monodromy `Γ₀ → π₁(S₀, p₀ τ₀)` of a uniformization, via Mathlib's
`IsQuotientCoveringMap.fundamentalGroupEquiv`; Mathlib's `π₁` multiplication is reversed, hence the `γ⁻¹`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold UpperHalfPlane

noncomputable section
namespace LiZhongQC

universe u

theorem s83sg_conj_entries (A M : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (A * M * A⁻¹) 0 0 = (A 0 0 * M 0 0 + A 0 1 * M 1 0) * A 1 1 - (A 0 0 * M 0 1 + A 0 1 * M 1 1) * A 1 0 ∧
    (A * M * A⁻¹) 0 1 = -(A 0 1) * (A 0 0 * M 0 0 + A 0 1 * M 1 0) + A 0 0 * (A 0 0 * M 0 1 + A 0 1 * M 1 1) ∧
    (A * M * A⁻¹) 1 0 = (A 1 0 * M 0 0 + A 1 1 * M 1 0) * A 1 1 - (A 1 0 * M 0 1 + A 1 1 * M 1 1) * A 1 0 ∧
    (A * M * A⁻¹) 1 1 = -(A 0 1) * (A 1 0 * M 0 0 + A 1 1 * M 1 0) + A 0 0 * (A 1 0 * M 0 1 + A 1 1 * M 1 1) := by
  have hinv : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.adjugate (A : Matrix (Fin 2) (Fin 2) ℝ) := Matrix.SpecialLinearGroup.coe_inv A
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hinv,
      Matrix.adjugate_fin_two]
    simp
    ring

theorem s83sg_det (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
  have hd := Matrix.SpecialLinearGroup.det_coe M
  rwa [Matrix.det_fin_two] at hd

theorem s83sg_trace_conj (A M : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (A * M * A⁻¹) 0 0 + (A * M * A⁻¹) 1 1 = M 0 0 + M 1 1 := by
  obtain ⟨h00, h01, h10, h11⟩ := s83sg_conj_entries A M
  rw [h00, h11]
  have hd := s83sg_det A
  linear_combination (M 0 0 + M 1 1) * hd

theorem s83sg_diag_of_eigen (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (p q r s ν₁ ν₂ : ℝ)
    (e1 : δ 0 0 * p + δ 0 1 * q = ν₁ * p) (e2 : δ 1 0 * p + δ 1 1 * q = ν₁ * q)
    (e3 : δ 0 0 * r + δ 0 1 * s = ν₂ * r) (e4 : δ 1 0 * r + δ 1 1 * s = ν₂ * s)
    (hD : p * s - q * r ≠ 0) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, (A * δ * A⁻¹) 0 0 = ν₁ ∧ (A * δ * A⁻¹) 0 1 = 0 ∧
      (A * δ * A⁻¹) 1 0 = 0 ∧ (A * δ * A⁻¹) 1 1 = ν₂ := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t * (p * s - q * r) = 1 := ⟨(p * s - q * r)⁻¹, inv_mul_cancel₀ hD⟩
  let A : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    ⟨!![s * t, -r * t; -q, p], by rw [Matrix.det_fin_two_of]; linear_combination ht⟩
  refine ⟨A, ?_⟩
  obtain ⟨h00, h01, h10, h11⟩ := s83sg_conj_entries A δ
  have a00 : A 0 0 = s * t := rfl
  have a01 : A 0 1 = -r * t := rfl
  have a10 : A 1 0 = -q := rfl
  have a11 : A 1 1 = p := rfl
  rw [h00, h01, h10, h11, a00, a01, a10, a11]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (t * s) * e1 - (t * r) * e2 + ν₁ * ht
  · linear_combination (t ^ 2 * s) * e3 - (t ^ 2 * r) * e4
  · linear_combination p * e2 - q * e1
  · linear_combination (-q * t) * e3 + (p * t) * e4 + ν₂ * ht

theorem s83sg_eigen_exists (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hδ : 4 < (δ 0 0 + δ 1 1) ^ 2) :
    ∃ p q r s ν₁ ν₂ : ℝ, δ 0 0 * p + δ 0 1 * q = ν₁ * p ∧ δ 1 0 * p + δ 1 1 * q = ν₁ * q ∧
      δ 0 0 * r + δ 0 1 * s = ν₂ * r ∧ δ 1 0 * r + δ 1 1 * s = ν₂ * s ∧ p * s - q * r ≠ 0 := by
  have hdet := s83sg_det δ
  obtain ⟨μ, μ', hsum, hprod, hne⟩ : ∃ μ μ' : ℝ, μ + μ' = δ 0 0 + δ 1 1 ∧ μ * μ' = 1 ∧ μ - μ' ≠ 0 := by
    have hsqpos : 0 < (δ 0 0 + δ 1 1) ^ 2 - 4 := by linarith
    have hsq : Real.sqrt ((δ 0 0 + δ 1 1) ^ 2 - 4) ^ 2 = (δ 0 0 + δ 1 1) ^ 2 - 4 := Real.sq_sqrt hsqpos.le
    have hsqp : 0 < Real.sqrt ((δ 0 0 + δ 1 1) ^ 2 - 4) := Real.sqrt_pos.2 hsqpos
    refine ⟨((δ 0 0 + δ 1 1) + Real.sqrt ((δ 0 0 + δ 1 1) ^ 2 - 4)) / 2,
      ((δ 0 0 + δ 1 1) - Real.sqrt ((δ 0 0 + δ 1 1) ^ 2 - 4)) / 2, by ring, ?_, ?_⟩
    · linear_combination (-1 / 4) * hsq
    · intro h; linarith
  have hne' : μ' - μ ≠ 0 := by intro h; apply hne; linarith
  by_cases h10 : δ 1 0 = 0
  · by_cases h01 : δ 0 1 = 0
    · refine ⟨1, 0, 0, 1, δ 0 0, δ 1 1, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [h10, h01]
    · have hd : δ 0 0 * δ 1 1 = 1 := by rw [h10] at hdet; linarith
      refine ⟨δ 0 1, δ 1 1 - μ', δ 0 1, δ 1 1 - μ, μ, μ', ?_, ?_, ?_, ?_, ?_⟩
      · linear_combination (-(δ 0 1)) * hsum
      · rw [h10]
        linear_combination (-(δ 1 1)) * hsum + hprod - hd
      · linear_combination (-(δ 0 1)) * hsum
      · rw [h10]
        linear_combination (-(δ 1 1)) * hsum + hprod - hd
      · intro h
        have : δ 0 1 * (μ' - μ) = 0 := by linear_combination h
        rcases mul_eq_zero.1 this with h1 | h1
        · exact h01 h1
        · exact hne' h1
  · refine ⟨δ 0 0 - μ', δ 1 0, δ 0 0 - μ, δ 1 0, μ, μ', ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination (-(δ 0 0)) * hsum + hprod - hdet
    · linear_combination (-(δ 1 0)) * hsum
    · linear_combination (-(δ 0 0)) * hsum + hprod - hdet
    · linear_combination (-(δ 1 0)) * hsum
    · intro h
      have : δ 1 0 * (μ - μ') = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h1 | h1
      · exact h10 h1
      · exact hne h1

theorem s83sg_diagonalize (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hδ : 4 < (δ 0 0 + δ 1 1) ^ 2) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, (A * δ * A⁻¹) 0 1 = 0 ∧ (A * δ * A⁻¹) 1 0 = 0 ∧
      1 < (A * δ * A⁻¹) 0 0 ^ 2 := by
  obtain ⟨p, q, r, s, ν₁, ν₂, e1, e2, e3, e4, hD⟩ := s83sg_eigen_exists δ hδ
  obtain ⟨A, a00, a01, a10, a11⟩ := s83sg_diag_of_eigen δ p q r s ν₁ ν₂ e1 e2 e3 e4 hD
  have hdet := s83sg_det (A * δ * A⁻¹)
  have htr := s83sg_trace_conj A δ
  rw [a00, a01, a10, a11] at hdet
  rw [a00, a11] at htr
  have hprod : ν₁ * ν₂ = 1 := by linarith
  have hsum : (ν₁ + ν₂) ^ 2 > 4 := by rw [htr]; exact hδ
  by_cases h : 1 < ν₁ ^ 2
  · exact ⟨A, a01, a10, by rw [a00]; exact h⟩
  · have hD' : r * q - s * p ≠ 0 := by
      intro h0; apply hD; linarith
    obtain ⟨A', b00, b01, b10, b11⟩ := s83sg_diag_of_eigen δ r s p q ν₂ ν₁ e3 e4 e1 e2 hD'
    refine ⟨A', b01, b10, ?_⟩
    rw [b00]
    nlinarith

theorem s83sg_comm_trace_diag (γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (h01 : δ 0 1 = 0)
    (h10 : δ 1 0 = 0) :
    (commutatorSL γ δ) 0 0 + (commutatorSL γ δ) 1 1 = 2 - γ 0 1 * γ 1 0 * (δ 0 0 - δ 1 1) ^ 2 := by
  have hdγ := s83sg_det γ
  have hdδ := s83sg_det δ
  rw [h01, h10] at hdδ
  have hi : ∀ M : Matrix.SpecialLinearGroup (Fin 2) ℝ, ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = Matrix.adjugate (M : Matrix (Fin 2) (Fin 2) ℝ) :=
    fun M => Matrix.SpecialLinearGroup.coe_inv M
  simp only [commutatorSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hi,
    Matrix.adjugate_fin_two]
  simp [h01, h10]
  linear_combination (2 * δ 0 0 * δ 1 1) * hdγ + 2 * hdδ

theorem s83sg_pos_root (a b c d : ℝ) (hbc : 0 < b * c) :
    ∃ u : ℝ, 0 < u ∧ b * u ^ 2 + (a - d) * u - c = 0 := by
  have hb : b ≠ 0 := by rintro rfl; simp at hbc
  have hΔ : 0 < (a - d) ^ 2 + 4 * (b * c) := by positivity
  set r := Real.sqrt ((a - d) ^ 2 + 4 * (b * c)) with hr
  have hr2 : r ^ 2 = (a - d) ^ 2 + 4 * (b * c) := Real.sq_sqrt hΔ.le
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hlt : |d - a| < r := by
    apply abs_lt_of_sq_lt_sq _ hr0
    nlinarith
  have h1 : d - a < r := (abs_lt.1 hlt).2
  have h2 : -r < d - a := (abs_lt.1 hlt).1
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · refine ⟨((d - a) - r) / (2 * b), ?_, ?_⟩
    · apply div_pos_of_neg_of_neg <;> linarith
    · field_simp
      linear_combination hr2
  · refine ⟨((d - a) + r) / (2 * b), ?_, ?_⟩
    · apply div_pos <;> linarith
    · field_simp
      linear_combination hr2

theorem s83sg_normalize (γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hδ : 4 < (δ 0 0 + δ 1 1) ^ 2)
    (hc : (commutatorSL γ δ) 0 0 + (commutatorSL γ δ) 1 1 < 2) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (A * δ * A⁻¹) 0 1 = 0 ∧ (A * δ * A⁻¹) 1 0 = 0 ∧ 1 < (A * δ * A⁻¹) 0 0 ^ 2 ∧
      (A * γ * A⁻¹) 0 0 + (A * γ * A⁻¹) 0 1 = (A * γ * A⁻¹) 1 0 + (A * γ * A⁻¹) 1 1 ∧
      0 < (A * γ * A⁻¹) 0 1 * (A * γ * A⁻¹) 1 0 := by
  obtain ⟨A₀, h01, h10, hl⟩ := s83sg_diagonalize δ hδ
  have hcomm : commutatorSL (A₀ * γ * A₀⁻¹) (A₀ * δ * A₀⁻¹) = A₀ * commutatorSL γ δ * A₀⁻¹ := by
    simp only [commutatorSL]
    group
  have htr : (commutatorSL (A₀ * γ * A₀⁻¹) (A₀ * δ * A₀⁻¹)) 0 0 +
      (commutatorSL (A₀ * γ * A₀⁻¹) (A₀ * δ * A₀⁻¹)) 1 1 < 2 := by
    rw [hcomm, s83sg_trace_conj]; exact hc
  rw [s83sg_comm_trace_diag _ _ h01 h10] at htr
  have hxy := s83sg_det (A₀ * δ * A₀⁻¹)
  rw [h01, h10] at hxy
  obtain ⟨γ₁, hγ₁⟩ : ∃ γ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ, γ₁ = A₀ * γ * A₀⁻¹ := ⟨_, rfl⟩
  obtain ⟨δ₁, hδ₁⟩ : ∃ δ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ, δ₁ = A₀ * δ * A₀⁻¹ := ⟨_, rfl⟩
  rw [← hγ₁, ← hδ₁] at htr
  rw [← hδ₁] at hxy hl h01 h10
  have hne : δ₁ 0 0 - δ₁ 1 1 ≠ 0 := by
    intro h
    have : δ₁ 0 0 = δ₁ 1 1 := by linarith
    rw [← this] at hxy
    nlinarith
  have hdiff : 0 < (δ₁ 0 0 - δ₁ 1 1) ^ 2 := by positivity
  have hbc : 0 < γ₁ 0 1 * γ₁ 1 0 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg (neg_nonneg.2 h) hdiff.le]
  obtain ⟨u, hu0, hu⟩ := s83sg_pos_root (γ₁ 0 0) (γ₁ 0 1) (γ₁ 1 0) (γ₁ 1 1) hbc
  have hs0 : 0 < Real.sqrt u := Real.sqrt_pos.2 hu0
  have hs2 : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
  set s := Real.sqrt u with hsdef
  let S : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    ⟨!![s, 0; 0, s⁻¹], by rw [Matrix.det_fin_two_of]; field_simp; ring⟩
  have hconj : ∀ M : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      S * A₀ * M * (S * A₀)⁻¹ = S * (A₀ * M * A₀⁻¹) * S⁻¹ := by
    intro M
    group
  refine ⟨S * A₀, ?_⟩
  rw [hconj, hconj, ← hγ₁, ← hδ₁]
  obtain ⟨d00, d01, d10, d11⟩ := s83sg_conj_entries S δ₁
  obtain ⟨g00, g01, g10, g11⟩ := s83sg_conj_entries S γ₁
  have S00 : S 0 0 = s := rfl
  have S01 : S 0 1 = 0 := rfl
  have S10 : S 1 0 = 0 := rfl
  have S11 : S 1 1 = s⁻¹ := rfl
  simp only [S00, S01, S10, S11] at d00 d01 d10 d11 g00 g01 g10 g11
  have hsne : s ≠ 0 := hs0.ne'
  have hu' : u ≠ 0 := hu0.ne'
  have hg00 : (S * γ₁ * S⁻¹) 0 0 = γ₁ 0 0 := by rw [g00]; field_simp; ring
  have hg01 : (S * γ₁ * S⁻¹) 0 1 = u * γ₁ 0 1 := by rw [g01, ← hs2]; ring
  have hg10 : (S * γ₁ * S⁻¹) 1 0 = γ₁ 1 0 / u := by rw [g10, ← hs2]; field_simp; ring
  have hg11 : (S * γ₁ * S⁻¹) 1 1 = γ₁ 1 1 := by rw [g11]; field_simp; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [d01, h01]; ring
  · rw [d10, h10]; ring
  · have : (S * δ₁ * S⁻¹) 0 0 = δ₁ 0 0 := by rw [d00, h10, h01]; field_simp; ring
    rw [this]; exact hl
  · rw [hg00, hg01, hg10, hg11]
    field_simp
    linear_combination hu
  · rw [hg01, hg10]
    have : u * γ₁ 0 1 * (γ₁ 1 0 / u) = γ₁ 0 1 * γ₁ 1 0 := by field_simp
    rw [this]; exact hbc


variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]

theorem s83sg_deck_pi1 [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) (τ₀ : UpperHalfPlane) :
    ∃ ρ : Γ₀ →* FundamentalGroup S₀ (p₀ τ₀), Function.Surjective ρ ∧
      (∀ γ : Γ₀, ρ γ = 1 ↔ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) = 1 ∨
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) = -1) ∧
      ∀ (γ : Γ₀) (c : Path τ₀ ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ • τ₀))
        (L : Path (p₀ τ₀) (p₀ τ₀)), (∀ t, L t = p₀ (c t)) →
        ρ γ = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L) := by
  have hfree : ActsFreely Γ₀ := s27g_actsFreely hp₀
  obtain ⟨hcov, hhol, hsurj, hfib⟩ := hp₀
  have hneg : ∀ τ : UpperHalfPlane, (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ = τ := fun τ => by
    ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    have hz : (τ : ℂ) ≠ 0 := τ.ne_zero
    simp
  let φ : Γ₀ →* Equiv.Perm UpperHalfPlane := MulAction.toPermHom Γ₀ UpperHalfPlane
  have hφ : ∀ (γ : Γ₀) (τ : UpperHalfPlane), φ γ τ = (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ :=
    fun γ τ => rfl
  have hφ1 : ∀ γ : Γ₀, φ γ = 1 ↔ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) = 1 ∨
      (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) = -1 := by
    intro γ
    constructor
    · intro h
      apply s27g_eq_one_of_smul_eq
      intro τ
      have := hφ γ τ
      rw [h] at this
      exact this.symm
    · rintro (h | h)
      · ext τ
        rw [hφ, h]
        simp
      · ext τ
        rw [hφ, h]
        simpa using hneg τ
  let G : Subgroup (Equiv.Perm UpperHalfPlane) := φ.range
  have : ContinuousConstSMul G UpperHalfPlane := by
    refine ⟨?_⟩
    rintro ⟨g, γ, rfl⟩
    exact (s27t_mdifferentiable_smul (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)).continuous
  have hcancel : IsCancelSMul G UpperHalfPlane := by
    refine { left_cancel' := fun a b c h => a.1.injective h, right_cancel' := ?_ }
    rintro ⟨a, γ1, rfl⟩ ⟨b, γ2, rfl⟩ c h
    change φ γ1 c = φ γ2 c at h
    rw [hφ, hφ] at h
    have hfix : ((γ2⁻¹ * γ1 : Γ₀) : Matrix.SpecialLinearGroup (Fin 2) ℝ) • c = c := by
      have e : ((γ2⁻¹ * γ1 : Γ₀) : Matrix.SpecialLinearGroup (Fin 2) ℝ) =
          (γ2 : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ * γ1 := rfl
      rw [e, mul_smul, h, inv_smul_smul]
    have h1 := (hφ1 (γ2⁻¹ * γ1)).2 (hfree _ (γ2⁻¹ * γ1).2 c hfix)
    apply Subtype.ext
    show φ γ1 = φ γ2
    have : φ (γ2⁻¹ * γ1) = 1 := h1
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this.symm
  have horbit : ∀ {e₁ e₂ : UpperHalfPlane}, p₀ e₁ = p₀ e₂ ↔ e₁ ∈ MulAction.orbit G e₂ := by
    intro e₁ e₂
    constructor
    · intro h
      obtain ⟨γ, hγ, h'⟩ := (hfib e₂ e₁).1 h.symm
      exact ⟨⟨φ ⟨γ, hγ⟩, ⟨_, rfl⟩⟩, h'⟩
    · rintro ⟨⟨g, γ, rfl⟩, h⟩
      exact ((hfib e₂ e₁).2 ⟨γ, γ.2, h⟩).symm
  have hq : IsQuotientCoveringMap p₀ G :=
    (isQuotientCoveringMap_iff_isCoveringMap_and ..).2 ⟨hcov, hsurj, inferInstance, hcancel, horbit⟩
  let e : p₀ ⁻¹' {p₀ τ₀} := ⟨τ₀, rfl⟩
  let eqv : FundamentalGroup S₀ (p₀ τ₀) ≃* Gᵐᵒᵖ := hq.fundamentalGroupEquiv e
  let ρ : Γ₀ →* FundamentalGroup S₀ (p₀ τ₀) :=
    (eqv.symm.toMonoidHom.comp (MulEquiv.inv' G).toMonoidHom).comp φ.rangeRestrict
  have hρ : ∀ γ : Γ₀, eqv (ρ γ) = MulOpposite.op ((φ.rangeRestrict γ)⁻¹) := by
    intro γ
    show eqv (eqv.symm (MulEquiv.inv' G (φ.rangeRestrict γ))) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  refine ⟨ρ, ?_, ?_, ?_⟩
  · exact eqv.symm.surjective.comp ((MulEquiv.inv' G).surjective.comp φ.rangeRestrict_surjective)
  · intro γ
    rw [← hφ1]
    constructor
    · intro h
      have h2 := hρ γ
      rw [h, map_one] at h2
      have h3 : (φ.rangeRestrict γ)⁻¹ = 1 := MulOpposite.op_injective h2.symm
      have h4 : φ.rangeRestrict γ = 1 := inv_eq_one.1 h3
      exact congrArg Subtype.val h4
    · intro h
      have h4 : φ.rangeRestrict γ = 1 := Subtype.ext h
      have h2 := hρ γ
      rw [h4, inv_one] at h2
      exact eqv.injective (by rw [h2, map_one, MulOpposite.op_one])
  · intro γ c L hL
    apply eqv.injective
    rw [hρ γ]
    show _ = hq.fundamentalGroupToMulOpposite e _
    symm
    rw [hq.fundamentalGroupToMulOpposite_apply_eq_Iff]
    have hey : p₀ ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ • τ₀) = p₀ τ₀ :=
      (hfib _ _).2 ⟨γ, γ.2, smul_inv_smul _ _⟩
    have eq : (Path.Homotopic.Quotient.mk c).map ⟨p₀, hcov.continuous⟩ =
        (Path.Homotopic.Quotient.mk L).cast (show p₀ (e : UpperHalfPlane) = p₀ τ₀ from rfl) hey := by
      rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
      congr 1
      ext t
      exact (hL t).symm
    have hm := hcov.monodromy_eq_of_map_eq (ex := e) (ey := ⟨_, hey⟩)
      (Path.Homotopic.Quotient.mk c) eq
    rw [hm]
    show (φ γ)⁻¹ τ₀ = _
    rw [← map_inv]
    rfl


end LiZhongQC
