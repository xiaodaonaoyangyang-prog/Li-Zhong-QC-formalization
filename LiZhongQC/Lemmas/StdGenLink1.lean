import LiZhongQC.Lemmas.StdGenAlg
import LiZhongQC.Ch08.S30_ModularGroupDiscontinuity

/-!
# Standard generators of a closed surface group (R83): fixed points, linking algebra, line ends
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold UpperHalfPlane

noncomputable section
namespace LiZhongQC

universe u



/-- For `c ≠ 0` and hyperbolic `γ`: the two finite fixed points have `c(σ + τ) = a - d`, `c σ τ = -b`. -/
theorem s83sg_vieta {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : 2 < |γ 0 0 + γ 1 1|)
    (hc : γ 1 0 ≠ 0) {σ τ : ℝ} (hσ : attractingFixedPoint γ = ((σ : ℂ) : ExtPlane))
    (hτ : repellingFixedPoint γ = ((τ : ℂ) : ExtPlane)) :
    γ 1 0 * (σ + τ) = γ 0 0 - γ 1 1 ∧ γ 1 0 * σ * τ = -γ 0 1 := by
  have hdet := hnf_sl2_det γ
  obtain ⟨-, hε2, -, -, hs2⟩ := hnf_sign_sqrt hγ
  have e1 := hnf_attr_eq hc hσ
  have e2 := hnf_rep_eq hc hτ
  set X : ℝ := Real.sign (γ 0 0 + γ 1 1) * Real.sqrt ((γ 0 0 + γ 1 1) ^ 2 - 4) with hX
  have hX2 : X ^ 2 = (γ 0 0 + γ 1 1) ^ 2 - 4 := by rw [hX, mul_pow, hε2, one_mul, hs2]
  refine ⟨?_, ?_⟩
  · linear_combination (e1 + e2) / 2
  · have h4 : 4 * γ 1 0 * (γ 1 0 * σ * τ + γ 0 1) = 0 := by
      linear_combination (2 * γ 1 0 * τ) * e1 + (γ 0 0 - γ 1 1 + X) * e2 - hX2 - 4 * hdet
    have h5 : γ 1 0 * σ * τ + γ 0 1 = 0 := by
      rcases mul_eq_zero.1 h4 with h | h
      · exact absurd h (mul_ne_zero four_ne_zero hc)
      · exact h
    linarith

/-- For hyperbolic `γ`, the fixed points of the Möbius map on `ℂ̄` are exactly `attractingFixedPoint γ` and
`repellingFixedPoint γ`. -/
theorem s83sg_fix_iff {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : 2 < |γ 0 0 + γ 1 1|) (x : ExtPlane) :
    x ∈ ({attractingFixedPoint γ, repellingFixedPoint γ} : Set ExtPlane) ↔
      x ∈ mobiusFixedPoints (γ 0 0 : ℂ) (γ 0 1) (γ 1 0) (γ 1 1) := by
  have hdet := k24_det_real γ
  by_cases hc : γ 1 0 = 0
  · obtain ⟨h1, h2⟩ := hnf_fixed_of_eq_zero hc
    have had : γ 0 0 * γ 1 1 = 1 := by
      have := hnf_sl2_det γ
      rw [hc] at this
      linarith
    have hda : γ 1 1 - γ 0 0 ≠ 0 := (hnf_core_eq had hγ).1
    have hc' : ((γ 1 0 : ℝ) : ℂ) = 0 := by rw [hc]; simp
    have hmem : ∀ z : ℂ, (z : ExtPlane) ∈ mobiusFixedPoints (γ 0 0 : ℂ) (γ 0 1) (γ 1 0) (γ 1 1) ↔
        z = ((γ 0 1 / (γ 1 1 - γ 0 0) : ℝ) : ℂ) := by
      intro z
      rw [mem_mobiusFixedPoints_coe_iff hdet, hc']
      have hda' : ((γ 1 1 : ℝ) : ℂ) - γ 0 0 ≠ 0 := by exact_mod_cast hda
      push_cast
      constructor
      · intro h
        field_simp
        linear_combination h
      · intro h
        rw [h]
        field_simp
        ring
    have hinf : extInf ∈ mobiusFixedPoints (γ 0 0 : ℂ) (γ 0 1) (γ 1 0) (γ 1 1) :=
      (mem_mobiusFixedPoints_infty_iff _ _ _ _).2 hc'
    have hset : ({attractingFixedPoint γ, repellingFixedPoint γ} : Set ExtPlane) =
        {extInf, (((γ 0 1 / (γ 1 1 - γ 0 0) : ℝ) : ℂ) : ExtPlane)} := by
      by_cases ha : 1 < |γ 0 0|
      · rw [(h1 ha).1, (h1 ha).2]
      · rw [(h2 ha).1, (h2 ha).2]
        exact Set.pair_comm _ _
    rw [hset]
    induction x using OnePoint.rec with
    | infty => simp [hinf]
    | coe z =>
      rw [hmem z]
      simp [OnePoint.coe_ne_infty]
  · obtain ⟨σ, hσ⟩ := hnf_attr_exists hc
    obtain ⟨τ, hτ⟩ := hnf_rep_exists hc
    obtain ⟨hv1, hv2⟩ := s83sg_vieta hγ hc hσ hτ
    rw [hσ, hτ]
    induction x using OnePoint.rec with
    | infty =>
      constructor
      · rintro (h | h)
        · exact absurd h.symm (OnePoint.coe_ne_infty _)
        · exact absurd h.symm (OnePoint.coe_ne_infty _)
      · intro h
        have := (mem_mobiusFixedPoints_infty_iff _ _ _ _).1 h
        exact absurd (by exact_mod_cast this) hc
    | coe z =>
      rw [mem_mobiusFixedPoints_coe_iff hdet]
      have hc' : ((γ 1 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
      have hv1' : (γ 1 0 : ℂ) * ((σ : ℂ) + τ) = (γ 0 0 : ℂ) - γ 1 1 := by exact_mod_cast hv1
      have hv2' : (γ 1 0 : ℂ) * σ * τ = -(γ 0 1 : ℂ) := by exact_mod_cast hv2
      have hfac : (γ 1 0 : ℂ) * z ^ 2 + ((γ 1 1 : ℂ) - γ 0 0) * z - γ 0 1 =
          (γ 1 0 : ℂ) * ((z - σ) * (z - τ)) := by
        linear_combination z * hv1' - hv2'
      rw [hfac]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, OnePoint.coe_eq_coe, mul_eq_zero, hc',
        false_or]
      constructor
      · rintro (h | h)
        · rw [h]; simp
        · rw [h]; simp
      · rintro (h | h)
        · left; exact sub_eq_zero.1 h
        · right; exact sub_eq_zero.1 h




theorem s83sg_slc_mul (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    slRealToComplex (A * B) = slRealToComplex A * slRealToComplex B :=
  map_mul (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)) A B

theorem s83sg_slc_inv (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    slRealToComplex A⁻¹ = (slRealToComplex A)⁻¹ :=
  map_inv (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)) A

theorem s83sg_fixset_eq (Y : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    mobiusFixedPoints (Y 0 0 : ℂ) (Y 0 1) (Y 1 0) (Y 1 1) =
      {p | mobiusSL (slRealToComplex Y) p = p} := by
  ext p
  simp only [mobiusFixedPoints, Set.mem_setOf_eq, k24_mobiusSL_real]

/-- Fixed points of a conjugate. -/
theorem s83sg_fix_conj (A X : Matrix.SpecialLinearGroup (Fin 2) ℝ) (p : ExtPlane) :
    p ∈ mobiusFixedPoints ((A * X * A⁻¹) 0 0 : ℂ) ((A * X * A⁻¹) 0 1) ((A * X * A⁻¹) 1 0)
        ((A * X * A⁻¹) 1 1) ↔
      mobiusSL (slRealToComplex A⁻¹) p ∈ mobiusFixedPoints (X 0 0 : ℂ) (X 0 1) (X 1 0) (X 1 1) := by
  rw [s83sg_fixset_eq, s83sg_fixset_eq]
  simp only [Set.mem_setOf_eq]
  rw [s83sg_slc_mul, s83sg_slc_mul, k24_mobiusSL_mul, k24_mobiusSL_mul, s83sg_slc_inv]
  constructor
  · intro h
    have := congrArg (mobiusSL (slRealToComplex A)⁻¹) h
    rwa [k24_mobiusSL_inv_apply] at this
  · intro h
    rw [h, k24_mobiusSL_apply_inv]

/-- `∞` is a limit of points of an unbounded set of reals. -/
theorem s83sg_infty_mem_closure (S : Set ℝ) (hS : ∀ R : ℝ, ∃ x ∈ S, R < |x|) :
    extInf ∈ closure (toExt (Complex.ofReal '' S)) := by
  choose f hfS hf using hS
  have h1 : Tendsto (fun n : ℕ => ((f n : ℝ) : ℂ)) atTop (cocompact ℂ) := by
    refine tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℂ) ?_
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    have := hf n
    rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact this.le
  have h2 : Tendsto (fun n : ℕ => (((f n : ℝ) : ℂ) : ExtPlane)) atTop (𝓝 extInf) :=
    OnePoint.tendsto_coe_infty.comp (by rw [coclosedCompact_eq_cocompact]; exact h1)
  exact mem_closure_of_tendsto h2 (Eventually.of_forall fun n => ⟨_, ⟨f n, hfS n, rfl⟩, rfl⟩)

theorem s83sg_halfline_conn (s : Set ℝ) (hs : IsPreconnected s) (hS : ∀ R : ℝ, ∃ x ∈ s, R < |x|) :
    IsConnected (toExt (Complex.ofReal '' s) ∪ {extInf}) := by
  have hA : IsPreconnected (toExt (Complex.ofReal '' s)) :=
    k24_toExt_isPreconnected (hs.image _ Complex.continuous_ofReal.continuousOn)
  have hcl := s83sg_infty_mem_closure s hS
  have hne : (toExt (Complex.ofReal '' s)).Nonempty := by
    obtain ⟨x, hx, -⟩ := hS 0
    exact ⟨_, _, ⟨x, hx, rfl⟩, rfl⟩
  refine ⟨hne.mono subset_union_left, hA.subset_closure subset_union_left ?_⟩
  intro p hp
  rcases hp with hp | hp
  · exact subset_closure hp
  · rw [mem_singleton_iff.1 hp]
    exact hcl

/-- Fixed points of a diagonal element with `a² ≠ 1`: `0` and `∞`. -/
theorem s83sg_fix_diag (D : Matrix.SpecialLinearGroup (Fin 2) ℝ) (h01 : D 0 1 = 0) (h10 : D 1 0 = 0)
    (hl : 1 < D 0 0 ^ 2) (p : ExtPlane) :
    p ∈ mobiusFixedPoints (D 0 0 : ℂ) (D 0 1) (D 1 0) (D 1 1) ↔ p = extInf ∨ p = ((0 : ℂ) : ExtPlane) := by
  have hdet := k24_det_real D
  have hd : D 0 0 * D 1 1 = 1 := by
    have := hnf_sl2_det D
    rw [h01, h10] at this
    linarith
  have hda : D 1 1 - D 0 0 ≠ 0 := (hnf_core_eq hd (by
    have : 2 < |D 0 0 + D 1 1| := by
      have h1 : (D 0 0 + D 1 1) ^ 2 = D 0 0 ^ 2 + D 1 1 ^ 2 + 2 := by linear_combination 2 * hd
      have h2 : D 0 0 ^ 2 * D 1 1 ^ 2 = 1 := by rw [← mul_pow, hd]; norm_num
      have h3 : 4 < (D 0 0 + D 1 1) ^ 2 := by nlinarith [sq_nonneg (D 0 0 ^ 2 - D 1 1 ^ 2), sq_nonneg (D 0 0 - D 1 1)]
      nlinarith [sq_abs (D 0 0 + D 1 1), abs_nonneg (D 0 0 + D 1 1)]
    exact this)).1
  have hc' : ((D 1 0 : ℝ) : ℂ) = 0 := by rw [h10]; simp
  have hb' : ((D 0 1 : ℝ) : ℂ) = 0 := by rw [h01]; simp
  induction p using OnePoint.rec with
  | infty =>
    simp only [true_or, iff_true]
    exact (mem_mobiusFixedPoints_infty_iff _ _ _ _).2 hc'
  | coe z =>
    rw [mem_mobiusFixedPoints_coe_iff hdet, hc', hb']
    have hda' : ((D 1 1 : ℝ) : ℂ) - D 0 0 ≠ 0 := by exact_mod_cast hda
    constructor
    · intro h
      right
      have : ((D 1 1 : ℝ) : ℂ) - D 0 0 = 0 ∨ z = 0 := by
        apply mul_eq_zero.1
        linear_combination h
      rcases this with h' | h'
      · exact absurd h' hda'
      · rw [h']
    · rintro (h | h)
      · exact absurd h (OnePoint.coe_ne_infty _)
      · have : z = 0 := OnePoint.coe_injective h
        rw [this]; ring




/-- **[L5, algebra]** Interleaved, pairwise distinct fixed points of two hyperbolic matrices give `tr[γ, δ] < 2`. -/
theorem s83sg_sep_trace {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : IsHyperbolic γ) (hδ : IsHyperbolic δ)
    (hdisj : ∀ x ∈ ({attractingFixedPoint γ, repellingFixedPoint γ} : Set ExtPlane),
      x ∉ ({attractingFixedPoint δ, repellingFixedPoint δ} : Set ExtPlane))
    (hsep : ∀ C : Set ExtPlane, C ⊆ extRealLine → IsConnected C → attractingFixedPoint δ ∈ C →
      repellingFixedPoint δ ∈ C → attractingFixedPoint γ ∈ C ∨ repellingFixedPoint γ ∈ C) :
    (commutatorSL γ δ) 0 0 + (commutatorSL γ δ) 1 1 < 2 := by
  by_contra hlt
  push Not at hlt
  have hγ' : 2 < |γ 0 0 + γ 1 1| := hγ
  have hδ' : 2 < |δ 0 0 + δ 1 1| := hδ
  have hδ4 : 4 < (δ 0 0 + δ 1 1) ^ 2 := by
    nlinarith [sq_abs (δ 0 0 + δ 1 1), abs_nonneg (δ 0 0 + δ 1 1)]
  obtain ⟨A, h01, h10, hl⟩ := s83sg_diagonalize δ hδ4
  obtain ⟨γ₁, hγ₁⟩ : ∃ γ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ, γ₁ = A * γ * A⁻¹ := ⟨_, rfl⟩
  obtain ⟨δ₁, hδ₁⟩ : ∃ δ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ, δ₁ = A * δ * A⁻¹ := ⟨_, rfl⟩
  have hcomm : commutatorSL γ₁ δ₁ = A * commutatorSL γ δ * A⁻¹ := by
    rw [hγ₁, hδ₁]
    simp only [commutatorSL]
    group
  have htr : 2 ≤ (commutatorSL γ₁ δ₁) 0 0 + (commutatorSL γ₁ δ₁) 1 1 := by
    rw [hcomm, s83sg_trace_conj]
    exact hlt
  rw [← hδ₁] at h01 h10 hl
  rw [s83sg_comm_trace_diag _ _ h01 h10] at htr
  have hxy := s83sg_det δ₁
  rw [h01, h10] at hxy
  have hne : δ₁ 0 0 - δ₁ 1 1 ≠ 0 := by
    intro h
    have : δ₁ 0 0 = δ₁ 1 1 := by linarith
    rw [← this] at hxy
    nlinarith
  have hdiff : 0 < (δ₁ 0 0 - δ₁ 1 1) ^ 2 := by positivity
  have hbc : γ₁ 0 1 * γ₁ 1 0 ≤ 0 := by
    by_contra h
    push Not at h
    nlinarith [mul_pos h hdiff]
  have hγ1 : 2 < |γ₁ 0 0 + γ₁ 1 1| := by
    rw [hγ₁, s83sg_trace_conj]
    exact hγ'
  -- fixed point sets
  have hFγ : ∀ p, p ∈ mobiusFixedPoints (γ 0 0 : ℂ) (γ 0 1) (γ 1 0) (γ 1 1) ↔
      p ∈ ({attractingFixedPoint γ, repellingFixedPoint γ} : Set ExtPlane) :=
    fun p => (s83sg_fix_iff hγ' p).symm
  have hFδ : ∀ p, p ∈ mobiusFixedPoints (δ 0 0 : ℂ) (δ 0 1) (δ 1 0) (δ 1 1) ↔
      p ∈ ({attractingFixedPoint δ, repellingFixedPoint δ} : Set ExtPlane) :=
    fun p => (s83sg_fix_iff hδ' p).symm
  have hdisj' : ∀ p, p ∈ mobiusFixedPoints (γ₁ 0 0 : ℂ) (γ₁ 0 1) (γ₁ 1 0) (γ₁ 1 1) →
      p ∉ mobiusFixedPoints (δ₁ 0 0 : ℂ) (δ₁ 0 1) (δ₁ 1 0) (δ₁ 1 1) := by
    intro p hp1 hp2
    rw [hγ₁, s83sg_fix_conj, hFγ] at hp1
    rw [hδ₁, s83sg_fix_conj, hFδ] at hp2
    exact hdisj _ hp1 hp2
  have hb0 : γ₁ 0 1 ≠ 0 := by
    intro hb
    apply hdisj' ((0 : ℂ) : ExtPlane)
    · rw [mem_mobiusFixedPoints_coe_iff (k24_det_real γ₁)]
      rw [hb]
      simp
    · exact (s83sg_fix_diag δ₁ h01 h10 hl _).2 (Or.inr rfl)
  have hc0 : γ₁ 1 0 ≠ 0 := by
    intro hc
    apply hdisj' extInf
    · exact (mem_mobiusFixedPoints_infty_iff _ _ _ _).2 (by rw [hc]; simp)
    · exact (s83sg_fix_diag δ₁ h01 h10 hl _).2 (Or.inl rfl)
  have hbc' : γ₁ 0 1 * γ₁ 1 0 < 0 :=
    lt_of_le_of_ne hbc (mul_ne_zero hb0 hc0)
  obtain ⟨σ, hσ⟩ := hnf_attr_exists hc0
  obtain ⟨τ, hτ⟩ := hnf_rep_exists hc0
  obtain ⟨hv1, hv2⟩ := s83sg_vieta hγ1 hc0 hσ hτ
  have hστ : 0 < σ * τ := by
    have h1 : γ₁ 1 0 ^ 2 * (σ * τ) = -(γ₁ 0 1 * γ₁ 1 0) := by linear_combination γ₁ 1 0 * hv2
    have h2 : 0 < γ₁ 1 0 ^ 2 := by positivity
    have h3 : 0 < γ₁ 1 0 ^ 2 * (σ * τ) := by rw [h1]; linarith
    exact pos_of_mul_pos_right h3 h2.le
  obtain ⟨s, hs0, hsσ, hsτ, hsconn, hsunb⟩ : ∃ s : Set ℝ, (0 : ℝ) ∈ s ∧ σ ∉ s ∧ τ ∉ s ∧
      IsPreconnected s ∧ ∀ R : ℝ, ∃ x ∈ s, R < |x| := by
    have hσ0 : σ ≠ 0 := fun h => by rw [h, zero_mul] at hστ; exact lt_irrefl _ hστ
    rcases lt_or_gt_of_ne hσ0 with hneg | hpos
    · have hτneg : τ < 0 := by nlinarith
      refine ⟨Ici 0, by simp, by simpa using hneg, by simpa using hτneg, isPreconnected_Ici, fun R => ?_⟩
      refine ⟨|R| + 1, by simp only [mem_Ici]; positivity, ?_⟩
      rw [abs_of_pos (by positivity)]
      linarith [le_abs_self R]
    · have hτpos : 0 < τ := by nlinarith
      refine ⟨Iic 0, by simp, by simpa using hpos, by simpa using hτpos, isPreconnected_Iic, fun R => ?_⟩
      refine ⟨-(|R| + 1), by simp only [mem_Iic]; linarith [abs_nonneg R], ?_⟩
      rw [abs_neg, abs_of_pos (by positivity)]
      linarith [le_abs_self R]
  have hC'conn := s83sg_halfline_conn s hsconn hsunb
  have hC'sub : toExt (Complex.ofReal '' s) ∪ {extInf} ⊆ extRealLine := by
    rintro p (⟨z, ⟨x, hx, rfl⟩, rfl⟩ | hp)
    · exact Or.inl ⟨(x : ℂ), by simp [realLine], rfl⟩
    · exact Or.inr hp
  have hcont : Continuous (mobiusSL (slRealToComplex A⁻¹)) := (k24_mobiusSLHomeo _).continuous
  have hC_sub : mobiusSL (slRealToComplex A⁻¹) '' (toExt (Complex.ofReal '' s) ∪ {extInf}) ⊆
      extRealLine := by
    rintro _ ⟨p, hp, rfl⟩
    exact k24_real_mapsTo_extRealLine A⁻¹ (hC'sub hp)
  have hC_conn := hC'conn.image _ hcont.continuousOn
  have hδC : ∀ q ∈ ({attractingFixedPoint δ, repellingFixedPoint δ} : Set ExtPlane),
      q ∈ mobiusSL (slRealToComplex A⁻¹) '' (toExt (Complex.ofReal '' s) ∪ {extInf}) := by
    intro q hq
    have hqF := (hFδ q).2 hq
    have e : mobiusSL (slRealToComplex A⁻¹) (mobiusSL (slRealToComplex A) q) = q := by
      rw [s83sg_slc_inv]
      exact k24_mobiusSL_inv_apply _ q
    have hmq : mobiusSL (slRealToComplex A) q ∈
        mobiusFixedPoints (δ₁ 0 0 : ℂ) (δ₁ 0 1) (δ₁ 1 0) (δ₁ 1 1) := by
      rw [hδ₁, s83sg_fix_conj, e]
      exact hqF
    refine ⟨mobiusSL (slRealToComplex A) q, ?_, e⟩
    rcases (s83sg_fix_diag δ₁ h01 h10 hl _).1 hmq with h | h
    · exact Or.inr h
    · left
      rw [h]
      exact ⟨_, ⟨0, hs0, rfl⟩, by simp⟩
  have key : ∀ r ∈ ({attractingFixedPoint γ, repellingFixedPoint γ} : Set ExtPlane),
      r ∈ mobiusSL (slRealToComplex A⁻¹) '' (toExt (Complex.ofReal '' s) ∪ {extInf}) → False := by
    intro r hr hrC
    obtain ⟨c', hc'C, hc'e⟩ := hrC
    have hrF := (hFγ r).2 hr
    have e : mobiusSL (slRealToComplex A⁻¹) (mobiusSL (slRealToComplex A) r) = r := by
      rw [s83sg_slc_inv]
      exact k24_mobiusSL_inv_apply _ r
    have hmq : mobiusSL (slRealToComplex A) r ∈
        mobiusFixedPoints (γ₁ 0 0 : ℂ) (γ₁ 0 1) (γ₁ 1 0) (γ₁ 1 1) := by
      rw [hγ₁, s83sg_fix_conj, e]
      exact hrF
    have hce : mobiusSL (slRealToComplex A) r = c' := by
      rw [← hc'e, s83sg_slc_inv, k24_mobiusSL_apply_inv]
    rw [hce] at hmq
    have hmem := (s83sg_fix_iff hγ1 c').2 hmq
    rw [hσ, hτ] at hmem
    rcases hc'C with ⟨z, ⟨x, hx, rfl⟩, hz⟩ | hinf
    · rw [← hz] at hmem
      rcases hmem with h | h
      · have := Complex.ofReal_injective (OnePoint.coe_injective h)
        exact hsσ (this ▸ hx)
      · have := Complex.ofReal_injective (OnePoint.coe_injective h)
        exact hsτ (this ▸ hx)
    · rw [mem_singleton_iff.1 hinf] at hmem
      rcases hmem with h | h
      · exact OnePoint.coe_ne_infty _ h.symm
      · exact OnePoint.coe_ne_infty _ h.symm
  rcases hsep _ hC_sub hC_conn (hδC _ (Or.inl rfl)) (hδC _ (Or.inr rfl)) with hr | hr
  · exact key _ (Or.inl rfl) hr
  · exact key _ (Or.inr rfl) hr




/-- The commutator of two upper triangular matrices has trace `2`. -/
theorem s83sg_comm_tr_upper (γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hγ : γ 1 0 = 0) (hδ : δ 1 0 = 0) :
    (commutatorSL γ δ) 0 0 + (commutatorSL γ δ) 1 1 = 2 := by
  have hdγ := s83sg_det γ
  have hdδ := s83sg_det δ
  rw [hγ, mul_zero, sub_zero] at hdγ
  rw [hδ, mul_zero, sub_zero] at hdδ
  have hi : ∀ M : Matrix.SpecialLinearGroup (Fin 2) ℝ, ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = Matrix.adjugate (M : Matrix (Fin 2) (Fin 2) ℝ) :=
    fun M => Matrix.SpecialLinearGroup.coe_inv M
  simp only [commutatorSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hi,
    Matrix.adjugate_fin_two]
  simp [hγ, hδ]
  linear_combination (2 * δ 0 0 * δ 1 1) * hdγ + 2 * hdδ

/-- Every fixed point of a hyperbolic element is `∞` or a real point. -/
theorem s83sg_fixpt_cases {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : 2 < |γ 0 0 + γ 1 1|)
    {x : ExtPlane} (hx : x ∈ ({attractingFixedPoint γ, repellingFixedPoint γ} : Set ExtPlane)) :
    x = extInf ∨ ∃ r : ℝ, x = ((r : ℂ) : ExtPlane) := by
  by_cases hc : γ 1 0 = 0
  · obtain ⟨h1, h2⟩ := hnf_fixed_of_eq_zero hc
    by_cases ha : 1 < |γ 0 0|
    · rw [(h1 ha).1, (h1 ha).2] at hx
      rcases hx with h | h
      · exact Or.inl h
      · exact Or.inr ⟨_, h⟩
    · rw [(h2 ha).1, (h2 ha).2] at hx
      rcases hx with h | h
      · exact Or.inr ⟨_, h⟩
      · exact Or.inl h
  · obtain ⟨σ, hσ⟩ := hnf_attr_exists hc
    obtain ⟨τ, hτ⟩ := hnf_rep_exists hc
    rw [hσ, hτ] at hx
    rcases hx with h | h
    · exact Or.inr ⟨σ, h⟩
    · exact Or.inr ⟨τ, h⟩

/-- Two hyperbolic elements with a common fixed point have `tr[γ, δ] = 2`. -/
theorem s83sg_common_fix_tr {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : 2 < |γ 0 0 + γ 1 1|)
    (hδ : 2 < |δ 0 0 + δ 1 1|) {x : ExtPlane}
    (hxγ : x ∈ ({attractingFixedPoint γ, repellingFixedPoint γ} : Set ExtPlane))
    (hxδ : x ∈ ({attractingFixedPoint δ, repellingFixedPoint δ} : Set ExtPlane)) :
    (commutatorSL γ δ) 0 0 + (commutatorSL γ δ) 1 1 = 2 := by
  rcases s83sg_fixpt_cases hγ hxγ with rfl | ⟨r, rfl⟩
  · have h1 := (s83sg_fix_iff hγ _).1 hxγ
    have h2 := (s83sg_fix_iff hδ _).1 hxδ
    rw [mem_mobiusFixedPoints_infty_iff] at h1 h2
    exact s83sg_comm_tr_upper γ δ (by exact_mod_cast h1) (by exact_mod_cast h2)
  · let Q : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
      ⟨!![0, -1; 1, -r], by rw [Matrix.det_fin_two_of]; ring⟩
    have hQ : ∀ M : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        ((M 1 0 : ℂ) * (r : ℂ) ^ 2 + ((M 1 1 : ℂ) - M 0 0) * r - M 0 1 = 0) → (Q * M * Q⁻¹) 1 0 = 0 := by
      intro M hM
      have hM' : M 1 0 * r ^ 2 + (M 1 1 - M 0 0) * r - M 0 1 = 0 := by exact_mod_cast hM
      obtain ⟨-, -, h10, -⟩ := s83sg_conj_entries Q M
      have q00 : Q 0 0 = 0 := rfl
      have q01 : Q 0 1 = -1 := rfl
      have q10 : Q 1 0 = 1 := rfl
      have q11 : Q 1 1 = -r := rfl
      rw [h10, q10, q11]
      linear_combination hM'
    have hγ1 := hQ γ (by
      have := (s83sg_fix_iff hγ _).1 hxγ
      rwa [mem_mobiusFixedPoints_coe_iff (k24_det_real γ)] at this)
    have hδ1 := hQ δ (by
      have := (s83sg_fix_iff hδ _).1 hxδ
      rwa [mem_mobiusFixedPoints_coe_iff (k24_det_real δ)] at this)
    have hup := s83sg_comm_tr_upper _ _ hγ1 hδ1
    have hcomm : commutatorSL (Q * γ * Q⁻¹) (Q * δ * Q⁻¹) = Q * commutatorSL γ δ * Q⁻¹ := by
      simp only [commutatorSL]
      group
    rw [hcomm, s83sg_trace_conj] at hup
    exact hup

/-- **[D, discreteness]** Two non-commuting hyperbolic elements of a cocompact Fuchsian group have no common fixed
point (a common fixed point makes `[γ, δ]` unipotent, hence parabolic or `1`: `s30e1_no_parabolic`). -/
theorem s83sg_disjoint_fixed {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hc : IsCocompact Γ) {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) (hδ : δ ∈ Γ)
    (hγh : IsHyperbolic γ) (hδh : IsHyperbolic δ) (hnc : γ * δ ≠ δ * γ) :
    ∀ x ∈ ({attractingFixedPoint γ, repellingFixedPoint γ} : Set ExtPlane),
      x ∉ ({attractingFixedPoint δ, repellingFixedPoint δ} : Set ExtPlane) := by
  intro x hxγ hxδ
  have htr := s83sg_common_fix_tr hγh hδh hxγ hxδ
  have hmem : commutatorSL γ δ ∈ Γ :=
    Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hγ hδ) (Γ.inv_mem hγ)) (Γ.inv_mem hδ)
  by_cases h1 : commutatorSL γ δ = 1
  · apply hnc
    have h2 : γ * δ * γ⁻¹ = δ := mul_inv_eq_one.1 h1
    calc γ * δ = γ * δ * γ⁻¹ * γ := by group
      _ = δ * γ := by rw [h2]
  · refine s30e1_no_parabolic hΓ hc hmem ⟨?_, h1, ?_⟩
    · show |(commutatorSL γ δ) 0 0 + (commutatorSL γ δ) 1 1| = 2
      rw [htr]; norm_num
    · intro hm
      have := s83sg_trace_conj 1 (commutatorSL γ δ)
      rw [hm] at htr
      simp at htr
      norm_num at htr




/-- Inversion swaps the attracting and the repelling fixed point. -/
theorem s83sg_attr_inv {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : 2 < |γ 0 0 + γ 1 1|) :
    attractingFixedPoint γ⁻¹ = repellingFixedPoint γ := by
  obtain ⟨i00, i01, i10, i11⟩ := s27t_inv_apply γ
  by_cases hc : γ 1 0 = 0
  · have hc' : γ⁻¹ 1 0 = 0 := by rw [i10, hc, neg_zero]
    have had : γ 0 0 * γ 1 1 = 1 := by
      have := hnf_sl2_det γ
      rw [hc] at this
      linarith
    obtain ⟨hda, hA, hD⟩ := hnf_core_eq had hγ
    rw [attractingFixedPoint, if_pos hc', repellingFixedPoint, if_pos hc, i00, i01, i11]
    by_cases ha : 1 < |γ 0 0|
    · have hd : ¬ 1 < |γ 1 1| := by
        intro hd
        have h1 : |γ 0 0| * |γ 1 1| = 1 := by rw [← abs_mul, had, abs_one]
        nlinarith [abs_nonneg (γ 0 0), abs_nonneg (γ 1 1)]
      rw [if_neg hd, if_pos ha]
      congr 2
      have : γ 0 0 - γ 1 1 ≠ 0 := fun h => hda (by linarith)
      field_simp
      ring
    · have hd : 1 < |γ 1 1| := by
        have h1 : |γ 0 0| * |γ 1 1| = 1 := by rw [← abs_mul, had, abs_one]
        have h2 : |γ 0 0| < 1 := by
          refine lt_of_le_of_ne (not_lt.1 ha) fun h => ?_
          have := abs_add_le (γ 0 0) (γ 1 1)
          rw [h, one_mul] at h1
          linarith
        nlinarith [abs_nonneg (γ 0 0), abs_nonneg (γ 1 1)]
      rw [if_pos hd, if_neg ha]
  · have hc' : γ⁻¹ 1 0 ≠ 0 := by rw [i10]; exact neg_ne_zero.2 hc
    rw [attractingFixedPoint, if_neg hc', repellingFixedPoint, if_neg hc, i00, i10, i11]
    congr 2
    have : (2 : ℝ) * -γ 1 0 ≠ 0 := by
      have : (2 : ℝ) * γ 1 0 ≠ 0 := mul_ne_zero two_ne_zero hc
      intro h; apply this; linarith
    rw [add_comm (γ 1 1) (γ 0 0)]
    field_simp
    ring




/-- **Uniform attraction, `c ≠ 0`**: along `u k ∈ K` (compact) and `n k → ∞`, `γ ^ n k • u k → σ`. -/
theorem s83sg_attr_seq_ne {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : 2 < |γ 0 0 + γ 1 1|)
    (hc : γ 1 0 ≠ 0) {K : Set UpperHalfPlane} (hK : IsCompact K) {u : ℕ → UpperHalfPlane}
    (hu : ∀ k, u k ∈ K) {nn : ℕ → ℕ} (hn : Tendsto nn atTop atTop) :
    Tendsto (fun k => (((γ ^ nn k • u k : UpperHalfPlane) : ℂ) : ExtPlane)) atTop
      (𝓝 (attractingFixedPoint γ)) := by
  obtain ⟨hL1, hne, hcross, hinfA, hinfR, -⟩ := hyperbolic_normal_form hγ
  have hL0 : 0 < multiplier γ := lt_trans one_pos hL1
  have hLc : (multiplier γ : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
  have hsmul : ∀ u : UpperHalfPlane,
      ((γ • u : UpperHalfPlane) : ℂ) = mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) u := by
    intro u
    rw [h36t_coe_smul]
    rfl
  have hpow : Tendsto (fun n : ℕ => ((multiplier γ : ℂ)⁻¹) ^ n) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 hL0.le) (inv_lt_one_of_one_lt₀ hL1)
    have h' := (Complex.continuous_ofReal.tendsto 0).comp h
    rw [Complex.ofReal_zero] at h'
    refine h'.congr fun n => ?_
    simp [Function.comp]
  obtain ⟨σ, hσ⟩ := hnf_attr_exists hc
  obtain ⟨τ, hτ⟩ := hnf_rep_exists hc
  have hdet := hnf_sl2_det γ
  obtain ⟨-, hε2, hεt, hs, hs2⟩ := hnf_sign_sqrt hγ
  obtain ⟨fσ, fτ, -, -⟩ := hnf_core_ne hdet hc hε2 hεt hs hs2 (hnf_attr_eq hc hσ) (hnf_rep_eq hc hτ)
  have hστ : σ ≠ τ := by
    intro h
    apply hne
    rw [hσ, hτ, h]
  have hστc : (σ : ℂ) ≠ (τ : ℂ) := by exact_mod_cast hστ
  set Φ : UpperHalfPlane → ℂ := fun u => ((u : ℂ) - σ) / ((u : ℂ) - τ) with hΦdef
  have hΦ : ∀ u : UpperHalfPlane, Φ u = (multiplier γ : ℂ) * Φ (γ • u) := by
    intro u
    have h := hcross σ τ hσ hτ (u : ℂ) (h36t_den_ne γ u) (s27t_ne_real u τ)
      (by rw [← hsmul]; exact s27t_ne_real _ τ)
    simp only [hΦdef]
    rw [hsmul]
    exact h
  have hΦ1 : ∀ u : UpperHalfPlane, Φ u ≠ 1 := by
    intro u h
    simp only [hΦdef] at h
    rw [div_eq_one_iff_eq (sub_ne_zero.2 (s27t_ne_real u τ))] at h
    exact hστc (by linear_combination -h)
  have hsolve : ∀ u : UpperHalfPlane, (u : ℂ) = (σ - Φ u * τ) / (1 - Φ u) := by
    intro u
    rw [eq_div_iff (sub_ne_zero.2 (Ne.symm (hΦ1 u)))]
    simp only [hΦdef]
    field_simp [sub_ne_zero.2 (s27t_ne_real u τ)]
    ring
  have hiter : ∀ (n : ℕ) (w : UpperHalfPlane),
      Φ (γ ^ n • w) = Φ w * ((multiplier γ : ℂ)⁻¹) ^ n := by
    intro n w
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_smul]
      have h := hΦ (γ ^ n • w)
      rw [ih] at h
      rw [pow_succ]
      field_simp
      linear_combination -h
  have hΦc : Continuous Φ :=
    (UpperHalfPlane.continuous_coe.sub continuous_const).div
      (UpperHalfPlane.continuous_coe.sub continuous_const) fun u => sub_ne_zero.2 (s27t_ne_real u τ)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ u ∈ K, ‖Φ u‖ ≤ M := by
    obtain ⟨M, hM⟩ := (hK.image hΦc.norm).bddAbove
    exact ⟨M, fun u hu => hM ⟨u, hu, rfl⟩⟩
  have ht : Tendsto (fun k => Φ (γ ^ nn k • u k)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => M * ‖((multiplier γ : ℂ)⁻¹) ^ nn k‖) atTop (𝓝 (M * ‖(0 : ℂ)‖)) :=
      ((hpow.comp hn).norm).const_mul M
    rw [norm_zero, mul_zero] at h1
    refine squeeze_zero_norm (fun k => ?_) h1
    rw [hiter, norm_mul]
    exact mul_le_mul_of_nonneg_right (hM _ (hu k)) (norm_nonneg _)
  have h2 : Tendsto (fun k => (((γ ^ nn k • u k : UpperHalfPlane) : ℂ))) atTop (𝓝 (σ : ℂ)) :=
    (s27t_tendsto_frac (A := (σ : ℂ)) (B := (τ : ℂ)) ht).congr fun k => (hsolve _).symm
  rw [hσ]
  exact (OnePoint.continuous_coe.tendsto _).comp h2

/-- **Uniform attraction, `c = 0`**. -/
theorem s83sg_attr_seq_eq {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : 2 < |γ 0 0 + γ 1 1|)
    (hc : γ 1 0 = 0) {K : Set UpperHalfPlane} (hK : IsCompact K) {u : ℕ → UpperHalfPlane}
    (hu : ∀ k, u k ∈ K) {nn : ℕ → ℕ} (hn : Tendsto nn atTop atTop) :
    Tendsto (fun k => (((γ ^ nn k • u k : UpperHalfPlane) : ℂ) : ExtPlane)) atTop
      (𝓝 (attractingFixedPoint γ)) := by
  have had : γ 0 0 * γ 1 1 = 1 := by
    have := hnf_sl2_det γ
    rw [hc] at this
    linarith
  obtain ⟨hda, -, -⟩ := hnf_core_eq had hγ
  obtain ⟨h1, h2⟩ := hnf_fixed_of_eq_zero hc
  set x : ℝ := γ 0 1 / (γ 1 1 - γ 0 0) with hx
  have hxfix : (x : ℂ) * (1 - (γ 0 0 : ℂ) ^ 2) = (γ 0 0 : ℂ) * (γ 0 1 : ℂ) := by
    have hda' : ((γ 1 1 : ℝ) : ℂ) - γ 0 0 ≠ 0 := by exact_mod_cast hda
    have had' : (γ 0 0 : ℂ) * γ 1 1 = 1 := by exact_mod_cast had
    rw [hx]
    push_cast
    field_simp
    linear_combination (-(γ 0 1 : ℂ)) * had'
  have hc' : ((γ 1 0 : ℝ) : ℂ) = 0 := by rw [hc]; simp
  have hstep : ∀ w : UpperHalfPlane,
      ((γ • w : UpperHalfPlane) : ℂ) - x = (γ 0 0 : ℂ) ^ 2 * ((w : ℂ) - x) := by
    intro w
    have had' : (γ 0 0 : ℂ) * γ 1 1 = 1 := by exact_mod_cast had
    rw [h36t_coe_smul]
    show mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) w - x = _
    rw [hc', hnf_mobiusFn_of_c_zero had']
    linear_combination (-1 : ℂ) * hxfix
  have hiter : ∀ (n : ℕ) (w : UpperHalfPlane),
      ((γ ^ n • w : UpperHalfPlane) : ℂ) - x = ((γ 0 0 : ℂ) ^ 2) ^ n * ((w : ℂ) - x) := by
    intro n w
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_smul, hstep, ih, pow_succ]
      ring
  have hcont : Continuous fun w : UpperHalfPlane => ‖(w : ℂ) - x‖ :=
    (UpperHalfPlane.continuous_coe.sub continuous_const).norm
  by_cases ha : 1 < |γ 0 0|
  · rw [(h1 ha).1]
    -- expansion: `‖γⁿ u - x‖ = |a|^(2n) ‖u - x‖ ≥ |a|^(2n) m`
    have hinv : Continuous fun w : UpperHalfPlane => ‖(w : ℂ) - x‖⁻¹ :=
      hcont.inv₀ fun w => by
        simpa using sub_ne_zero.2 (s27t_ne_real w x)
    obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ w ∈ K, ‖(w : ℂ) - x‖⁻¹ ≤ B := by
      obtain ⟨B, hB⟩ := (hK.image hinv).bddAbove
      exact ⟨B, fun w hw => hB ⟨w, hw, rfl⟩⟩
    have hpos : ∀ w : UpperHalfPlane, 0 < ‖(w : ℂ) - x‖ := fun w => by
      simpa using sub_ne_zero.2 (s27t_ne_real w x)
    have hlow : ∀ w ∈ K, 1 / (max B 1) ≤ ‖(w : ℂ) - x‖ := by
      intro w hw
      have h := hB w hw
      have hm : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
      rw [div_le_iff₀ hm]
      have : 1 ≤ ‖(w : ℂ) - x‖ * max B 1 := by
        have := mul_le_mul_of_nonneg_left (h.trans (le_max_left B 1)) (hpos w).le
        rwa [mul_inv_cancel₀ (hpos w).ne'] at this
      linarith
    have hq : 1 < (|γ 0 0|) ^ 2 := by nlinarith [abs_nonneg (γ 0 0)]
    have hgrow : Tendsto (fun k => ((|γ 0 0|) ^ 2) ^ nn k) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt hq).comp hn
    have hbig : Tendsto (fun k => (1 / (max B 1)) * ((|γ 0 0|) ^ 2) ^ nn k) atTop atTop :=
      hgrow.const_mul_atTop (by positivity)
    have hdist : Tendsto (fun k => ((γ ^ nn k • u k : UpperHalfPlane) : ℂ)) atTop (cocompact ℂ) := by
      refine tendsto_cocompact_of_tendsto_dist_comp_atTop (x : ℂ) ?_
      refine tendsto_atTop_mono (fun k => ?_) hbig
      rw [dist_eq_norm, hiter, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        mul_comm]
      exact mul_le_mul_of_nonneg_left (hlow _ (hu k)) (by positivity)
    exact OnePoint.tendsto_coe_infty.comp (by rw [coclosedCompact_eq_cocompact]; exact hdist)
  · rw [(h2 ha).1]
    have hlt : |γ 0 0| < 1 := by
      refine lt_of_le_of_ne (not_lt.1 ha) fun h => ?_
      have h1' : |γ 0 0| * |γ 1 1| = 1 := by rw [← abs_mul, had, abs_one]
      have := abs_add_le (γ 0 0) (γ 1 1)
      rw [h, one_mul] at h1'
      linarith
    obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ w ∈ K, ‖(w : ℂ) - x‖ ≤ M := by
      obtain ⟨M, hM⟩ := (hK.image hcont).bddAbove
      exact ⟨M, fun w hw => hM ⟨w, hw, rfl⟩⟩
    have hq0 : 0 ≤ (|γ 0 0|) ^ 2 := by positivity
    have hq1 : (|γ 0 0|) ^ 2 < 1 := by nlinarith [abs_nonneg (γ 0 0)]
    have hdec : Tendsto (fun k => M * ((|γ 0 0|) ^ 2) ^ nn k) atTop (𝓝 (M * 0)) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp hn).const_mul M
    rw [mul_zero] at hdec
    have h3 : Tendsto (fun k => ((γ ^ nn k • u k : UpperHalfPlane) : ℂ) - x) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => ?_) hdec
      rw [hiter, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hM _ (hu k)) (by positivity)
    have h4 : Tendsto (fun k => ((γ ^ nn k • u k : UpperHalfPlane) : ℂ)) atTop (𝓝 (x : ℂ)) := by
      have := h3.add_const (x : ℂ)
      simp only [zero_add, sub_add_cancel] at this
      exact this
    exact (OnePoint.continuous_coe.tendsto _).comp h4

/-- **Uniform attraction** for every hyperbolic `γ`. -/
theorem s83sg_attr_seq {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : 2 < |γ 0 0 + γ 1 1|)
    {K : Set UpperHalfPlane} (hK : IsCompact K) {u : ℕ → UpperHalfPlane}
    (hu : ∀ k, u k ∈ K) {nn : ℕ → ℕ} (hn : Tendsto nn atTop atTop) :
    Tendsto (fun k => (((γ ^ nn k • u k : UpperHalfPlane) : ℂ) : ExtPlane)) atTop
      (𝓝 (attractingFixedPoint γ)) := by
  by_cases hc : γ 1 0 = 0
  · exact s83sg_attr_seq_eq hγ hc hK hu hn
  · exact s83sg_attr_seq_ne hγ hc hK hu hn

/-- Image of a point of `ℍ` in the Riemann sphere. -/
abbrev s83sg_pt (τ : UpperHalfPlane) : ExtPlane := ((τ : ℂ) : ExtPlane)

theorem s83sg_line_atTop {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : 2 < |γ 0 0 + γ 1 1|)
    {a : ℝ → UpperHalfPlane} (ha : Continuous a) (hper : ∀ t, a (t + 1) = γ • a t) :
    Tendsto (fun t => s83sg_pt (a t)) atTop (𝓝 (attractingFixedPoint γ)) := by
  have hpow : ∀ (n : ℕ) (s : ℝ), a (s + n) = γ ^ n • a s := by
    intro n s
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_smul, ← ih, ← hper]
      congr 1
      push_cast
      ring
  have hK : IsCompact (a '' Icc (0 : ℝ) 1) := isCompact_Icc.image ha
  rw [Filter.tendsto_iff_seq_tendsto]
  intro tk htk
  have hev : ∀ᶠ k in atTop, 0 ≤ tk k := htk.eventually_ge_atTop 0
  have hn : Tendsto (fun k => ⌊tk k⌋₊) atTop atTop := tendsto_nat_floor_atTop.comp htk
  have hmain := s83sg_attr_seq hγ hK (u := fun k => a (Int.fract (tk k)))
    (fun k => ⟨Int.fract (tk k), ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, rfl⟩) hn
  refine hmain.congr' ?_
  filter_upwards [hev] with k hk
  show _ = s83sg_pt (a (tk k))
  rw [← hpow]
  congr 3
  have h1 := Int.fract_add_floor (tk k)
  have h2 : ((⌊tk k⌋₊ : ℕ) : ℝ) = ((⌊tk k⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.natCast_floor_eq_floor hk
  rw [h2]
  exact h1

/-- **[L1]** An equivariant continuous line `a (t + 1) = γ • a t` of a hyperbolic `γ` runs from the repelling to the
attracting fixed point of `γ`. -/
theorem s83sg_line_ends {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : IsHyperbolic γ)
    {a : ℝ → UpperHalfPlane} (ha : Continuous a) (hper : ∀ t, a (t + 1) = γ • a t) :
    Tendsto (fun t => s83sg_pt (a t)) atTop (𝓝 (attractingFixedPoint γ)) ∧
      Tendsto (fun t => s83sg_pt (a t)) atBot (𝓝 (repellingFixedPoint γ)) := by
  have hγ' : 2 < |γ 0 0 + γ 1 1| := hγ
  refine ⟨s83sg_line_atTop hγ' ha hper, ?_⟩
  obtain ⟨i00, i01, i10, i11⟩ := s27t_inv_apply γ
  have hinv : 2 < |γ⁻¹ 0 0 + γ⁻¹ 1 1| := by
    rw [i00, i11, add_comm]
    exact hγ'
  have hper' : ∀ t, (fun t : ℝ => a (-t)) (t + 1) = γ⁻¹ • (fun t : ℝ => a (-t)) t := by
    intro t
    have h := hper (-t - 1)
    simp only [sub_add_cancel] at h
    show a (-(t + 1)) = γ⁻¹ • a (-t)
    rw [show -(t + 1) = -t - 1 by ring, h, inv_smul_smul]
  have h := s83sg_line_atTop hinv (ha.comp continuous_neg) hper'
  rw [s83sg_attr_inv hγ'] at h
  have h2 := h.comp tendsto_neg_atBot_atTop
  refine h2.congr fun t => ?_
  simp


end LiZhongQC
