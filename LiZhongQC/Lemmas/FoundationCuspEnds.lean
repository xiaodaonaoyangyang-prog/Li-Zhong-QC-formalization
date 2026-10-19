import LiZhongQC.Lemmas.FoundationSmallSupport

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC
universe u
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- The parabolic `π₀` (acting as `τ ↦ τ + 1` in the coordinate `A`) is `±(1 1; 0 1)` in that coordinate. -/
theorem ft2c_conj_T {A π₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hπ : ∀ τ : UpperHalfPlane, π₀ • (A • τ) = A • ((1 : ℝ) +ᵥ τ)) :
    ∃ T : Matrix.SpecialLinearGroup (Fin 2) ℝ, (T 0 0 = 1 ∧ T 0 1 = 1 ∧ T 1 0 = 0 ∧ T 1 1 = 1) ∧
      (A⁻¹ * π₀ * A = T ∨ A⁻¹ * π₀ * A = -T) := by
  let T : Matrix.SpecialLinearGroup (Fin 2) ℝ := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hT : T 0 0 = 1 ∧ T 0 1 = 1 ∧ T 1 0 = 0 ∧ T 1 1 = 1 := by simp [T]
  refine ⟨T, hT, ?_⟩
  have hδ : ∀ τ : UpperHalfPlane, (A⁻¹ * π₀ * A) • τ = (1 : ℝ) +ᵥ τ := by
    intro τ
    rw [mul_smul, mul_smul, hπ, inv_smul_smul]
  obtain ⟨hc, hd, hb⟩ := ft1e_translation_entries (k := 1) (by simpa using hδ)
  have hdet := k24_det_realR (A⁻¹ * π₀ * A)
  rw [hc, hd, hb] at hdet
  have hsq : ((A⁻¹ * π₀ * A) 0 0 - 1) * ((A⁻¹ * π₀ * A) 0 0 + 1) = 0 := by linear_combination hdet
  rcases mul_eq_zero.1 hsq with h | h
  · left
    exact s30l_eq_of_entries (by rw [hT.1]; linarith) (by rw [hT.2.1, hb]; linarith) (by rw [hT.2.2.1, hc])
      (by rw [hT.2.2.2, hd]; linarith)
  · right
    refine s30l_eq_of_entries ?_ ?_ ?_ ?_ <;>
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, hT.1, hT.2.1, hT.2.2.1, hT.2.2.2]
    · linarith
    · rw [hb]; linarith
    · rw [hc]; simp
    · rw [hd]; linarith

/-- **The cusp in its coordinate** (from `s30l_cusp` for the conjugate group `A⁻¹ Γ A`): `p ∘ A` is invariant under
integer translations; two points of `{Im > 1}` with the same image differ by an integer; and a point `τ` of `{Im > 1}`
with `p (A τ) = p κ` has `Im τ ≤ max (Im A⁻¹κ) (1 / Im A⁻¹κ)`. -/
theorem ft2c_cusp_normal {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) (hΓ : IsFuchsian Γ) {A π₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hπΓ : π₀ ∈ Γ)
    (hπ : ∀ τ : UpperHalfPlane, π₀ • (A • τ) = A • ((1 : ℝ) +ᵥ τ))
    (hpc : ∀ γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, 1 < τ.im → 1 < (A⁻¹ • (γ • (A • τ))).im →
        ∃ k : ℤ, γ = π₀ ^ k ∨ γ = -π₀ ^ k) :
    (∀ (n : ℤ) (x : UpperHalfPlane), p (A • ((n : ℝ) +ᵥ x)) = p (A • x)) ∧
    (∀ τ τ' : UpperHalfPlane, 1 < τ.im → 1 < τ'.im → p (A • τ) = p (A • τ') → ∃ n : ℤ, (τ' : ℂ) = τ + n) ∧
    (∀ (κ τ : UpperHalfPlane), 1 < τ.im → p (A • τ) = p κ → τ.im ≤ max (A⁻¹ • κ).im (1 / (A⁻¹ • κ).im)) := by
  obtain ⟨T, hT, hπT⟩ := ft2c_conj_T hπ
  have hp' := adjustProjection_isUniformization hp A⁻¹
  have hΓ' := s30l_isFuchsian_conj hΓ A⁻¹
  have hadj : ∀ τ, adjustProjection p A⁻¹ τ = p (A • τ) := fun τ => by
    show p (A⁻¹⁻¹ • τ) = _
    rw [inv_inv]
  have hmem : ∀ γ ∈ Γ, A⁻¹ * γ * A ∈ conjGroup Γ A⁻¹ := fun γ hγ =>
    s30l_mem_conjGroup.2 ⟨γ, hγ, by rw [inv_inv]⟩
  have hTmem : T ∈ conjGroup Γ A⁻¹ ∨ -T ∈ conjGroup Γ A⁻¹ := by
    rcases hπT with h | h
    · exact Or.inl (h ▸ hmem π₀ hπΓ)
    · right
      have := hmem π₀ hπΓ
      rw [h] at this
      exact this
  -- the stabilizer of `∞` in `A⁻¹ Γ A` is `±⟨T⟩`
  have hstab : ∀ β ∈ conjGroup Γ A⁻¹, β 1 0 = 0 → ∃ n : ℤ, β = T ^ n ∨ β = -T ^ n := by
    intro β hβ hc
    obtain ⟨γ, hγ, rfl⟩ := s30l_mem_conjGroup.1 hβ
    rw [inv_inv] at hc ⊢
    set β := A⁻¹ * γ * A with hβdef
    have hdet := k24_det_realR β
    rw [hc, mul_zero, sub_zero] at hdet
    have ha0 : β 0 0 ≠ 0 := fun h => by rw [h, zero_mul] at hdet; exact zero_ne_one hdet
    -- a point of `{Im > 1}` sent into `{Im > 1}`
    set t : ℝ := 2 + 1 / β 0 0 ^ 2 with ht
    have htpos : 1 < t := by
      have hnonneg : 0 ≤ 1 / β 0 0 ^ 2 := div_nonneg zero_le_one (sq_nonneg _)
      rw [ht]
      linarith
    let τ : UpperHalfPlane := ⟨(t : ℂ) * I, by simp; linarith⟩
    have himβ : (β • τ).im = β 0 0 ^ 2 * t := by
      have hcoe := h36t_coe_smul β τ
      rw [hc] at hcoe
      have hd : β 1 1 = 1 / β 0 0 := by field_simp; linarith
      have : (β • τ).im = ((β • τ : UpperHalfPlane) : ℂ).im := rfl
      rw [this, hcoe, hd]
      simp [τ, Complex.div_im]
      field_simp
    have h1 : 1 < (A⁻¹ • (γ • (A • τ))).im := by
      have : A⁻¹ • (γ • (A • τ)) = β • τ := by rw [hβdef, mul_smul, mul_smul]
      rw [this, himβ, ht]
      have hb2 : 0 < β 0 0 ^ 2 := by positivity
      field_simp
      nlinarith
    obtain ⟨k, hk⟩ := hpc γ hγ τ (by change 1 < ((t : ℂ) * I).im; simpa using htpos) h1
    have hconj : A⁻¹ * π₀ ^ k * A = (A⁻¹ * π₀ * A) ^ k := by
      have := map_zpow (MulAut.conj A⁻¹).toMonoidHom π₀ k
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using this
    have hnegT : ∀ m : ℤ, (-T) ^ m = T ^ m ∨ (-T) ^ m = -T ^ m := by
      intro m
      rcases Int.even_or_odd m with he | ho
      · exact Or.inl (he.neg_zpow T)
      · exact Or.inr (ho.neg_zpow T)
    rcases hk with rfl | rfl
    · rw [hβdef, hconj]
      rcases hπT with h | h
      · exact ⟨k, Or.inl (by rw [h])⟩
      · rw [h]
        exact ⟨k, hnegT k⟩
    · rw [hβdef, mul_neg, neg_mul, hconj]
      rcases hπT with h | h
      · exact ⟨k, Or.inr (by rw [h])⟩
      · rw [h]
        rcases hnegT k with h2 | h2
        · exact ⟨k, Or.inr (by rw [h2])⟩
        · exact ⟨k, Or.inl (by rw [h2, neg_neg])⟩
  obtain ⟨ha, hb, hc⟩ := s30l_cusp hp' hΓ' hT hTmem hstab
  refine ⟨fun n x => ?_, fun τ τ' h1 h2 he => ?_, fun κ τ h1 he => ?_⟩
  · have hx : (n : ℝ) +ᵥ x = T ^ n • x := UpperHalfPlane.ext (by rw [s30l_transl_coe hT, UpperHalfPlane.coe_vadd]; push_cast; ring)
    rw [hx, ← hadj, ← hadj, ha]
  · exact hb τ τ' h1 h2 (by rw [hadj, hadj, he])
  · refine hc (A⁻¹ • κ) τ h1 ?_
    rw [hadj, hadj, smul_inv_smul, he]

/-- The coordinate `w = e^{2π} e^{2πiτ}` of the cusp: for `0 < |w|`, `τ_w = log w / 2πi + i` has `e^{2πi(τ_w - i)} = w`
and `Im τ_w = 1 - log |w| / 2π`. -/
theorem ft2c_tau {w : ℂ} (hw : w ≠ 0) :
    exp (2 * π * I * ((Complex.log w / (2 * π * I) + I) - I)) = w ∧
      (Complex.log w / (2 * π * I) + I).im = 1 - Real.log ‖w‖ / (2 * π) := by
  have h2π : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  constructor
  · rw [add_sub_cancel_right, mul_div_cancel₀ _ h2π, Complex.exp_log hw]
  · have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    simp only [add_im, I_im, Complex.div_im, Complex.log_re, Complex.log_im, mul_re, mul_im, ofReal_re,
      ofReal_im, I_re, Complex.normSq_apply]
    norm_num <;> field_simp <;> ring

/-- Two cusp coordinates of the same `w` differ by an integer, so `p ∘ A` takes the same value. -/
theorem ft2c_shift {S : Type*} {p : UpperHalfPlane → S} {A : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (ha : ∀ (n : ℤ) (x : UpperHalfPlane), p (A • ((n : ℝ) +ᵥ x)) = p (A • x)) {σ τ : UpperHalfPlane}
    (h : exp (2 * π * I * ((σ : ℂ) - I)) = exp (2 * π * I * ((τ : ℂ) - I))) : p (A • σ) = p (A • τ) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have h2π : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hστ : σ = (n : ℝ) +ᵥ τ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_vadd]
    have := mul_left_cancel₀ h2π (by linear_combination hn : 2 * π * I * ((σ : ℂ) - I) =
      2 * π * I * ((τ : ℂ) - I + n))
    push_cast
    linear_combination this
  rw [hστ, ha]

/-- **F2c (cusp ends of `ℍ/Γ`).**  If every point of `ℍ` has a `Γ`-translate in a compact set or in one of the
horoballs `A i • {Im > 1}`, precisely invariant under `⟨π₀ i⟩` and pairwise disjoint modulo `Γ`, then `S = ℍ/Γ` has
the cusp end data: holomorphic, injective, open punctured-disc charts `φ i` with pairwise disjoint images, a compact
core `K` with `S = K ∪ ⋃ φ i (0 < |w| ≤ r)`, and ends leaving every compact set (`|w| → 0`). -/
theorem ft2_cusp_ends {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) (hΓ : IsFuchsian Γ)
    (hfree : ActsFreely Γ) {n : ℕ} (C : Set UpperHalfPlane) (A π₀ : Fin n → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hC : IsCompact C)
    (hcusp : ∀ i, π₀ i ∈ Γ ∧ ∀ τ : UpperHalfPlane, π₀ i • (A i • τ) = A i • ((1 : ℝ) +ᵥ τ))
    (hpc : ∀ i i' γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, 1 < τ.im → 1 < ((A i')⁻¹ • (γ • (A i • τ))).im →
        i = i' ∧ ∃ k : ℤ, γ = π₀ i ^ k ∨ γ = -π₀ i ^ k)
    (hcover : ∀ τ : UpperHalfPlane, ∃ γ ∈ Γ, γ • τ ∈ C ∨ ∃ i, 1 < ((A i)⁻¹ • (γ • τ)).im) :
    ∃ (φ : Fin n → ℂ → S) (K : Set S) (r : ℝ), IsCompact K ∧ r < 1 ∧
      (∀ i, InjOn (φ i) {w | w ≠ 0 ∧ ‖w‖ < 1} ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (φ i) {w | w ≠ 0 ∧ ‖w‖ < 1} ∧
        ∀ V : Set ℂ, IsOpen V → V ⊆ {w | w ≠ 0 ∧ ‖w‖ < 1} → IsOpen (φ i '' V)) ∧
      (∀ i i', i ≠ i' → Disjoint (φ i '' {w | w ≠ 0 ∧ ‖w‖ < 1}) (φ i' '' {w | w ≠ 0 ∧ ‖w‖ < 1})) ∧
      (∀ x : S, x ∈ K ∨ ∃ i w, w ≠ 0 ∧ ‖w‖ ≤ r ∧ φ i w = x) ∧
      (∀ x : S, ∃ N ∈ 𝓝 x, ∃ δ > (0 : ℝ), ∀ i w, w ≠ 0 → ‖w‖ < 1 → φ i w ∈ N → δ ≤ ‖w‖) := by
  classical
  -- `_hfree` is not needed: the decomposition already encodes the freeness of the action on the horoballs
  have _hfree := hfree
  obtain ⟨hcov, hpd, hps, hfib⟩ := hp
  have hnorm : ∀ i, (∀ (m : ℤ) (x : UpperHalfPlane), p (A i • ((m : ℝ) +ᵥ x)) = p (A i • x)) ∧
      (∀ τ τ' : UpperHalfPlane, 1 < τ.im → 1 < τ'.im → p (A i • τ) = p (A i • τ') →
        ∃ m : ℤ, (τ' : ℂ) = τ + m) ∧
      (∀ (κ τ : UpperHalfPlane), 1 < τ.im → p (A i • τ) = p κ →
        τ.im ≤ max ((A i)⁻¹ • κ).im (1 / ((A i)⁻¹ • κ).im)) := fun i =>
    ft2c_cusp_normal ⟨hcov, hpd, hps, hfib⟩ hΓ (hcusp i).1 (hcusp i).2
      fun γ hγ τ h1 h2 => (hpc i i γ hγ τ h1 h2).2
  -- the coordinate `τ_w` as a point of `ℍ`
  have hτpos : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → 1 < (Complex.log w / (2 * π * I) + I).im := by
    intro w hw0 hw1
    rw [(ft2c_tau hw0).2]
    have : Real.log ‖w‖ < 0 := Real.log_neg (norm_pos_iff.2 hw0) hw1
    have hπ : 0 < π := Real.pi_pos
    have : Real.log ‖w‖ / (2 * π) < 0 := div_neg_of_neg_of_pos this (by positivity)
    linarith
  let tw : ℂ → UpperHalfPlane := fun w => UpperHalfPlane.ofComplex (Complex.log w / (2 * π * I) + I)
  have htw : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → ((tw w : UpperHalfPlane) : ℂ) = Complex.log w / (2 * π * I) + I := by
    intro w hw0 hw1
    show ((UpperHalfPlane.ofComplex _ : UpperHalfPlane) : ℂ) = _
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by linarith [hτpos w hw0 hw1])]
  have htwim : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → 1 < (tw w).im := fun w hw0 hw1 => by
    have : (tw w).im = ((tw w : UpperHalfPlane) : ℂ).im := rfl
    rw [this, htw w hw0 hw1]
    exact hτpos w hw0 hw1
  have htwexp : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → exp (2 * π * I * (((tw w : UpperHalfPlane) : ℂ) - I)) = w :=
    fun w hw0 hw1 => by rw [htw w hw0 hw1]; exact (ft2c_tau hw0).1
  let φ : Fin n → ℂ → S := fun i w => p (A i • tw w)
  -- `φ i w = p (A i σ)` for every coordinate `σ` of `w`
  have hφσ : ∀ i (w : ℂ) (σ : UpperHalfPlane), w ≠ 0 → ‖w‖ < 1 → exp (2 * π * I * ((σ : ℂ) - I)) = w →
      φ i w = p (A i • σ) := by
    intro i w σ hw0 hw1 hσ
    exact (ft2c_shift (hnorm i).1 (by rw [hσ, htwexp w hw0 hw1])).symm
  have hnormexp : ∀ σ : UpperHalfPlane, ‖exp (2 * π * I * ((σ : ℂ) - I))‖ = Real.exp (-(2 * π) * (σ.im - 1)) := by
    intro σ
    rw [Complex.norm_exp]
    congr 1
    have : σ.im = (σ : ℂ).im := rfl
    rw [this]
    simp
  refine ⟨φ, p '' (C ∪ ⋃ i, (fun τ => A i • τ) '' (UpperHalfPlane.ofComplex ''
      {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 ≤ z.im ∧ z.im ≤ 2})), Real.exp (-(2 * π)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the core is compact
    refine (hC.union (isCompact_iUnion fun i => ?_)).image hcov.continuous
    have hR : IsCompact {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 ≤ z.im ∧ z.im ≤ 2} := by
      refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
      · exact (isClosed_le continuous_const continuous_re).inter
          ((isClosed_le continuous_re continuous_const).inter
            ((isClosed_le continuous_const continuous_im).inter (isClosed_le continuous_im continuous_const)))
      · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 3)).subset ?_
        rintro z ⟨h1, h2, h3, h4⟩
        rw [Metric.mem_closedBall, dist_zero_right]
        calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
          _ ≤ 3 := by rw [abs_of_nonneg h1, abs_of_nonneg (by linarith)]; linarith
    refine (hR.image_of_continuousOn ?_).image (continuous_const_smul (A i))
    intro z hz
    have hzpos : 0 < z.im := lt_of_lt_of_le zero_lt_one hz.2.2.1
    exact (UpperHalfPlane.mdifferentiableAt_ofComplex hzpos).continuousAt.continuousWithinAt
  · -- `r < 1`
    rw [Real.exp_lt_one_iff]
    have := Real.pi_pos
    linarith
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · -- injectivity
      rintro w₁ ⟨hw₁0, hw₁1⟩ w₂ ⟨hw₂0, hw₂1⟩ he
      obtain ⟨m, hm⟩ := (hnorm i).2.1 (tw w₁) (tw w₂) (htwim w₁ hw₁0 hw₁1) (htwim w₂ hw₂0 hw₂1) he
      rw [← htwexp w₁ hw₁0 hw₁1, ← htwexp w₂ hw₂0 hw₂1, hm,
        show 2 * π * I * (((tw w₁ : UpperHalfPlane) : ℂ) + m - I) =
          2 * π * I * (((tw w₁ : UpperHalfPlane) : ℂ) - I) + m * (2 * π * I) by ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    · -- holomorphy, through a local branch of the logarithm
      rintro w₀ ⟨hw0, hw1⟩
      refine MDifferentiableAt.mdifferentiableWithinAt ?_
      obtain ⟨L, hLd, hL⟩ : ∃ L : ℂ → ℂ, DifferentiableAt ℂ L w₀ ∧
          ∀ᶠ w in 𝓝 w₀, exp (L w) = w ∧ (L w).re = Real.log ‖w‖ := by
        by_cases hs : w₀ ∈ slitPlane
        · refine ⟨Complex.log, Complex.differentiableAt_log hs, ?_⟩
          filter_upwards [isOpen_ne.mem_nhds hw0] with w hw
          exact ⟨Complex.exp_log hw, Complex.log_re w⟩
        · have hs' : -w₀ ∈ slitPlane := by
            rw [Complex.mem_slitPlane_iff] at hs ⊢
            push Not at hs
            obtain ⟨hre, him⟩ := hs
            left
            have hne : w₀.re ≠ 0 := fun h => hw0 (Complex.ext h him)
            simp only [neg_re]
            exact neg_pos.2 (lt_of_le_of_ne hre hne)
          refine ⟨fun w => Complex.log (-w) + π * I,
            ((Complex.differentiableAt_log hs').comp w₀ differentiableAt_id.neg).add_const _, ?_⟩
          filter_upwards [isOpen_ne.mem_nhds hw0] with w hw
          refine ⟨?_, ?_⟩
          · rw [Complex.exp_add, Complex.exp_log (neg_ne_zero.2 hw), Complex.exp_pi_mul_I]
            ring
          · simp [Complex.log_re]
      -- near `w₀`, `φ i = p ∘ A i ∘ (L / 2πi + i)`
      have hτL : ∀ᶠ w in 𝓝 w₀, w ≠ 0 ∧ ‖w‖ < 1 ∧ exp (L w) = w ∧ (L w).re = Real.log ‖w‖ := by
        filter_upwards [isOpen_ne.mem_nhds hw0, (isOpen_lt continuous_norm continuous_const).mem_nhds hw1, hL]
          with w h1 h2 h3
        exact ⟨h1, h2, h3⟩
      have hLim : ∀ w, w ≠ 0 → ‖w‖ < 1 → (L w).re = Real.log ‖w‖ → 1 < (L w / (2 * π * I) + I).im := by
        intro w hw0 hw1 hre
        have h1 := hτpos w hw0 hw1
        have e1 := (ft2c_tau hw0).2
        have : (L w / (2 * π * I) + I).im = 1 - Real.log ‖w‖ / (2 * π) := by
          have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
          simp only [add_im, I_im, Complex.div_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re,
            Complex.normSq_apply, hre]
          norm_num <;> field_simp <;> ring
        linarith
      have heq : (fun w => p (A i • UpperHalfPlane.ofComplex (L w / (2 * π * I) + I))) =ᶠ[𝓝 w₀] φ i := by
        filter_upwards [hτL] with w hw
        obtain ⟨hw0', hw1', hexp, hre⟩ := hw
        have him := hLim w hw0' hw1' hre
        refine (hφσ i w _ hw0' hw1' ?_).symm
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by linarith)]
        show exp (2 * π * I * (L w / (2 * π * I) + I - I)) = w
        have h2π : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
        rw [add_sub_cancel_right, mul_div_cancel₀ _ h2π, hexp]
      refine MDifferentiableAt.congr_of_eventuallyEq ?_ heq.symm
      have him0 : 0 < (L w₀ / (2 * π * I) + I).im := by
        obtain ⟨h1, h2, -, h4⟩ := hτL.self_of_nhds
        linarith [hLim w₀ h1 h2 h4]
      have hz : DifferentiableAt ℂ (fun w => L w / (2 * π * I) + I) w₀ := (hLd.div_const _).add_const _
      exact ((hpd _).comp _ ((s27t_mdifferentiable_smul (A i)) _)).comp w₀
        ((UpperHalfPlane.mdifferentiableAt_ofComplex him0).comp w₀ hz.mdifferentiableAt)
    · -- open images
      intro V hV hVsub
      have himg : φ i '' V = p '' ((fun τ => A i • τ) ''
          {σ : UpperHalfPlane | exp (2 * π * I * ((σ : ℂ) - I)) ∈ V}) := by
        ext x
        constructor
        · rintro ⟨w, hw, rfl⟩
          obtain ⟨hw0, hw1⟩ := hVsub hw
          exact ⟨A i • tw w, ⟨tw w, by rw [mem_setOf_eq, htwexp w hw0 hw1]; exact hw, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
          obtain ⟨hw0, hw1⟩ := hVsub hσ
          exact ⟨_, hσ, hφσ i _ σ hw0 hw1 rfl⟩
      rw [himg]
      refine hcov.isLocalHomeomorph.isOpenMap _ ((Homeomorph.smul (A i)).isOpenMap _ ?_)
      exact hV.preimage (by fun_prop)
  · -- disjointness of different cusps
    intro i i' hii'
    rw [Set.disjoint_left]
    rintro _ ⟨w, ⟨hw0, hw1⟩, rfl⟩ ⟨w', ⟨hw0', hw1'⟩, he⟩
    obtain ⟨γ, hγ, hγe⟩ := (hfib (A i' • tw w') (A i • tw w)).1 he
    refine hii' ((hpc i' i γ hγ (tw w') (htwim w' hw0' hw1') ?_).1.symm)
    rw [hγe, inv_smul_smul]
    exact htwim w hw0 hw1
  · -- the cover
    intro x
    obtain ⟨τ, rfl⟩ := hps x
    obtain ⟨γ, hγ, hτ⟩ := hcover τ
    have hpγ : p (γ • τ) = p τ := ((hfib _ _).2 ⟨γ, hγ, rfl⟩).symm
    rcases hτ with hτ | ⟨i, hi⟩
    · exact Or.inl ⟨γ • τ, Or.inl hτ, hpγ⟩
    set σ := (A i)⁻¹ • (γ • τ) with hσ
    have hpσ : p (A i • σ) = p τ := by rw [hσ, smul_inv_smul, hpγ]
    by_cases h2 : σ.im ≤ 2
    · left
      set m : ℤ := ⌊σ.re⌋ with hm
      set σ' : UpperHalfPlane := ((-m : ℤ) : ℝ) +ᵥ σ with hσ'
      have hσ're : σ'.re = σ.re - m := by
        rw [hσ']
        simp [UpperHalfPlane.vadd_re]
        ring
      have hσ'im : σ'.im = σ.im := by rw [hσ', UpperHalfPlane.vadd_im]
      refine ⟨A i • σ', Or.inr (mem_iUnion.2 ⟨i, ⟨σ', ⟨(σ' : ℂ), ?_, UpperHalfPlane.ofComplex_apply σ'⟩, rfl⟩⟩), ?_⟩
      · have hre0 : 0 ≤ σ'.re := by rw [hσ're, hm]; linarith [Int.floor_le σ.re]
        have hre1 : σ'.re ≤ 1 := by rw [hσ're, hm]; linarith [Int.lt_floor_add_one σ.re]
        exact ⟨hre0, hre1, by rw [show (σ' : ℂ).im = σ'.im from rfl, hσ'im]; linarith, by
          rw [show (σ' : ℂ).im = σ'.im from rfl, hσ'im]; exact h2⟩
      · rw [hσ', (hnorm i).1, hpσ]
    · right
      push Not at h2
      refine ⟨i, exp (2 * π * I * ((σ : ℂ) - I)), Complex.exp_ne_zero _, ?_, ?_⟩
      · rw [hnormexp, Real.exp_le_exp]
        have := Real.pi_pos
        nlinarith
      · have hlt : ‖exp (2 * π * I * ((σ : ℂ) - I))‖ < 1 := by
          rw [hnormexp, Real.exp_lt_one_iff]
          have := Real.pi_pos
          nlinarith
        rw [hφσ i _ σ (Complex.exp_ne_zero _) hlt rfl, hpσ]
  · -- the ends leave every compact set
    intro x
    obtain ⟨τx, rfl⟩ := hps x
    refine ⟨p '' Metric.ball τx 1, hcov.isLocalHomeomorph.isOpenMap _ Metric.isOpen_ball |>.mem_nhds
      ⟨τx, Metric.mem_ball_self one_pos, rfl⟩, ?_⟩
    have hB : IsCompact (Metric.closedBall τx 1) := isCompact_closedBall τx 1
    -- a bound for `max (Im A⁻¹ y) (1 / Im A⁻¹ y)` on the ball
    have hbd : ∀ i, ∃ M : ℝ, ∀ y ∈ Metric.closedBall τx 1,
        max ((A i)⁻¹ • y).im (1 / ((A i)⁻¹ • y).im) ≤ M := by
      intro i
      have hcont : Continuous fun y : UpperHalfPlane => max ((A i)⁻¹ • y).im (1 / ((A i)⁻¹ • y).im) := by
        have h1 : Continuous fun y : UpperHalfPlane => ((A i)⁻¹ • y).im :=
          UpperHalfPlane.continuous_im.comp (continuous_const_smul _)
        exact h1.max (continuous_const.div h1 fun y => ((A i)⁻¹ • y).im_ne_zero)
      obtain ⟨M, hM⟩ := (hB.image hcont).isBounded.bddAbove
      exact ⟨M, fun y hy => hM ⟨y, hy, rfl⟩⟩
    choose M hM using hbd
    set Mt : ℝ := 1 + ∑ i, |M i| with hMt
    have hMt : ∀ i, M i ≤ Mt := fun i => by
      rw [hMt]
      have := Finset.single_le_sum (f := fun j => |M j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      linarith [le_abs_self (M i)]
    refine ⟨Real.exp (-(2 * π) * Mt), Real.exp_pos _, fun i w hw0 hw1 hwN => ?_⟩
    obtain ⟨y, hy, hye⟩ := hwN
    have h1 := (hnorm i).2.2 y (tw w) (htwim w hw0 hw1) hye.symm
    have h2 : (tw w).im ≤ Mt := (h1.trans (hM i y (Metric.ball_subset_closedBall hy))).trans (hMt i)
    have h3 : (tw w).im = 1 - Real.log ‖w‖ / (2 * π) := by
      have : (tw w).im = ((tw w : UpperHalfPlane) : ℂ).im := rfl
      rw [this, htw w hw0 hw1, (ft2c_tau hw0).2]
    have hπ : 0 < π := Real.pi_pos
    have hlog : -(2 * π) * Mt ≤ Real.log ‖w‖ := by
      have : Real.log ‖w‖ / (2 * π) ≥ 1 - Mt := by linarith
      rw [ge_iff_le, le_div_iff₀ (by positivity)] at this
      nlinarith
    calc Real.exp (-(2 * π) * Mt) ≤ Real.exp (Real.log ‖w‖) := Real.exp_le_exp.2 hlog
      _ = ‖w‖ := Real.exp_log (norm_pos_iff.2 hw0)

end LiZhongQC
