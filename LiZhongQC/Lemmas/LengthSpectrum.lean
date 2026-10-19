import LiZhongQC.Ch08.S30_ModularGroupDiscontinuity

/-!
# Finite length spectrum

Proof support for finite length-spectrum rigidity.

* Theorem 30.2 (finite lengths determine the marked surface) —
  `thm30_2_length_spectrum_determines`.

Source-only combined interface: 11 contracts remain open. No proof acceptance is asserted.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC
universe u

open scoped UpperHalfPlane

/-- Every deck matrix covers a loop constructed by projecting a path from a prescribed lift point.
The loop and its Covers witness use the same prescribed lift point. -/
theorem s30ls_b1_covers_of_mem {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) (τ : UpperHalfPlane)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) :
    ∃ β : Loop S, β.1 = p τ ∧ Covers p γ β := by
  let L : Path τ (γ • τ) := PathConnectedSpace.somePath τ (γ • τ)
  have he : p τ = p (γ • τ) :=
    (hp.2.2.2 τ (γ • τ)).2 ⟨γ, hγ, rfl⟩
  let b : Path (p τ) (p τ) := (L.map hp.1.continuous).cast rfl he
  refine ⟨⟨p τ, b⟩, rfl, ?_⟩
  refine ⟨L.extend, L.continuous_extend.continuousOn, ?_, ?_⟩
  · intro t ht
    rw [L.extend_apply ht, b.extend_apply ht]
    rfl
  · rw [L.extend_one, L.extend_zero]

/-- Arbitrarily many, but finitely many, matrices generate the actual SL subgroup exactly.
The compact/Hausdorff uniformization hypotheses are weaker than the frozen S30 target. -/
theorem s30ls_b1_finite_generators {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [CompactSpace S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) (τ : UpperHalfPlane) :
    ∃ (m : ℕ) (C : Fin m → Matrix.SpecialLinearGroup (Fin 2) ℝ) (β : Fin m → Loop S),
      (∀ i, C i ∈ Γ ∧ (β i).1 = p τ ∧ Covers p (C i) (β i)) ∧
      Subgroup.closure (Set.range C) = Γ := by
  classical
  have hΓ : IsFuchsian Γ := utm_x2_isFuchsian hp
  obtain ⟨K, hK, hcov⟩ := utm_exists_compact_translate hp
  let T : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    {γ ∈ Γ | ((fun z => γ • z) '' K ∩ K).Nonempty}
  have hT : T.Finite := hΓ K hK
  letI : Fintype T := hT.fintype
  let m : ℕ := Fintype.card T
  let e : Fin m ≃ T := (Fintype.equivFin T).symm
  let C : Fin m → Matrix.SpecialLinearGroup (Fin 2) ℝ := fun i => (e i).1
  have hC : ∀ i, C i ∈ Γ := fun i => (e i).2.1
  have hCT : Set.range C = T := by
    ext γ
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hγ
      refine ⟨e.symm ⟨γ, hγ⟩, ?_⟩
      change (e (e.symm ⟨γ, hγ⟩)).1 = γ
      rw [e.apply_symm_apply]
  have hgen : Subgroup.closure (Set.range C) = Γ := by
    rw [hCT]
    exact Subgroup.closure_eq_of_le Γ (fun γ hγ => hγ.1) (s30b_generate hΓ hK hcov)
  choose β hβbase hβcover using fun i => s30ls_b1_covers_of_mem hp τ (hC i)
  exact ⟨m, C, β, fun i => ⟨hC i, hβbase i, hβcover i⟩, hgen⟩

/-- B2 M1: an expanding dilation action forces the literal diagonal entry conditions.
Use the existing identity-action uniqueness up to sign; do not replace the given group
element by an unsigned diagonal representative. -/
theorem s30ls_b2_dilation_entries
    {B : Matrix.SpecialLinearGroup (Fin 2) ℝ} {lam : ℝ} (hlam : 1 < lam)
    (hact : ∀ z : UpperHalfPlane,
      ((B • z : UpperHalfPlane) : ℂ) = ((lam ^ 2 : ℝ) : ℂ) * (z : ℂ)) :
    B 0 1 = 0 ∧ B 1 0 = 0 ∧ 1 < B 0 0 ^ 2 := by
  have hlam0 : lam ≠ 0 := (lt_trans zero_lt_one hlam).ne'
  have hlamc : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam0
  have hlam2 : 1 < lam ^ 2 := by nlinarith [sq_nonneg (lam - 1)]
  let T : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    ⟨!![lam, 0; 0, lam⁻¹], by simp [Matrix.det_fin_two, hlam0]⟩
  have hTact : ∀ z : UpperHalfPlane,
      ((T • z : UpperHalfPlane) : ℂ) = ((lam ^ 2 : ℝ) : ℂ) * (z : ℂ) := by
    intro z
    rw [h23l_b_coe_smul]
    change ((lam : ℂ) * (z : ℂ) + 0) / (0 * (z : ℂ) + ((lam⁻¹ : ℝ) : ℂ)) =
      ((lam ^ 2 : ℝ) : ℂ) * (z : ℂ)
    push_cast
    field_simp [hlamc]
    ring
  have hsame : ∀ z : UpperHalfPlane, T • z = B • z := by
    intro z
    apply UpperHalfPlane.ext
    exact (hTact z).trans (hact z).symm
  have hid : ∀ z : UpperHalfPlane, (T⁻¹ * B) • z = z := by
    intro z
    rw [mul_smul, ← hsame z, inv_smul_smul]
  have hBT : B = T ∨ B = -T := by
    rcases s27g_eq_one_of_smul_eq hid with h | h
    · left
      calc B = T * (T⁻¹ * B) := by group
        _ = T := by rw [h, mul_one]
    · right
      calc B = T * (T⁻¹ * B) := by group
        _ = -T := by rw [h, mul_neg_one]
  have hTdiag : T 0 1 = 0 ∧ T 1 0 = 0 ∧ 1 < T 0 0 ^ 2 :=
    ⟨rfl, rfl, hlam2⟩
  rcases hBT with h | h
  · simpa only [h] using hTdiag
  · simpa only [h, s27t_neg_apply, neg_zero, neg_eq_zero, neg_sq] using hTdiag

/-- B2 M2: a hyperbolic deck element fixing a nonzero finite point is off both axes
of an expanding diagonal deck element. Use the existing trace-2 commutator formulas
and compact-uniformization hyperbolicity, without a surface-group relator. -/
theorem s30ls_b2_off_axes
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [CompactSpace S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) {C B : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hC : C ∈ Γ) (hBmem : B ∈ Γ)
    (hB : B 0 1 = 0 ∧ B 1 0 = 0 ∧ 1 < B 0 0 ^ 2)
    (hCh : 2 < |slTrace C|) {x : ℝ} (hx : x ≠ 0)
    (hfix : C 1 0 * x ^ 2 + (C 1 1 - C 0 0) * x - C 0 1 = 0) :
    C 0 1 ≠ 0 ∧ C 1 0 ≠ 0 := by
  have hbad : C 0 1 = 0 ∨ C 1 0 = 0 → False := by
    intro haxis
    let Q : Matrix.SpecialLinearGroup (Fin 2) ℝ := C * B * C⁻¹ * B⁻¹
    have hQmem : Q ∈ Γ :=
      Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hC hBmem) (Γ.inv_mem hC)) (Γ.inv_mem hBmem)
    have hQtr : slTrace Q = 2 := by
      rcases haxis with h01 | h10
      · exact s30e1_comm_tr_lower hB.1 hB.2.1 h01
      · exact s30e1_comm_tr_upper hB.1 hB.2.1 h10
    have hQm : Q ≠ -1 := by
      intro h
      rw [h] at hQtr
      norm_num [slTrace, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one] at hQtr
    have hQone : Q = 1 := by
      by_contra h
      have hh : 2 < |slTrace Q| := s27f_hyp hp hQmem h hQm
      rw [hQtr] at hh
      norm_num at hh
    have hcomm : C * B = B * C := by
      calc C * B = Q * (B * C) := by dsimp only [Q]; group
        _ = B * C := by rw [hQone, one_mul]
    have hBne : B 0 0 ≠ B 1 1 := (s27t_diag_facts hB).2.2
    have hC01 : C 0 1 = 0 := by
      have e := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) ℝ => X 0 1) hcomm
      simp only [s27t_mul_apply, hB.1] at e
      have hz : C 0 1 * (B 1 1 - B 0 0) = 0 := by linear_combination e
      exact (mul_eq_zero.1 hz).resolve_right (sub_ne_zero.2 hBne.symm)
    have hC10 : C 1 0 = 0 := by
      have e := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) ℝ => X 1 0) hcomm
      simp only [s27t_mul_apply, hB.2.1] at e
      have hz : C 1 0 * (B 0 0 - B 1 1) = 0 := by linear_combination e
      exact (mul_eq_zero.1 hz).resolve_right (sub_ne_zero.2 hBne)
    have hz : (C 1 1 - C 0 0) * x = 0 := by
      simpa only [hC01, hC10, zero_mul, zero_add, sub_zero] using hfix
    have hdiag : C 1 1 = C 0 0 :=
      sub_eq_zero.1 ((mul_eq_zero.1 hz).resolve_right hx)
    have hd := hnf_sl2_det C
    rw [hC01, hC10, hdiag, zero_mul, sub_zero] at hd
    have hsq : slTrace C ^ 2 = 4 := by
      change (C 0 0 + C 1 1) ^ 2 = 4
      rw [hdiag]
      nlinarith [hd]
    have habs : |slTrace C| ^ 2 = 4 := by rw [sq_abs, hsq]
    nlinarith [abs_nonneg (slTrace C)]
  constructor
  · intro h
    exact hbad (Or.inl h)
  · intro h
    exact hbad (Or.inr h)

/-- B2 helper: a nonzero lower-left entry and the signed-root equation identify
the finite attracting point. This is the converse algebraic use of hnf_attr_eq. -/
theorem s30ls_b2_attracting_of_eq
    {E : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hc : E 1 0 ≠ 0) {x : ℝ}
    (h : 2 * E 1 0 * x = E 0 0 - E 1 1 +
      Real.sign (E 0 0 + E 1 1) * Real.sqrt ((E 0 0 + E 1 1) ^ 2 - 4)) :
    attractingFixedPoint E = ((x : ℂ) : ExtPlane) := by
  have hden : 2 * E 1 0 ≠ 0 := mul_ne_zero (by norm_num) hc
  have hf : (E 0 0 - E 1 1 +
      Real.sign (E 0 0 + E 1 1) * Real.sqrt ((E 0 0 + E 1 1) ^ 2 - 4)) /
      (2 * E 1 0) = x := by
    apply (div_eq_iff hden).2
    linear_combination -h
  rw [attractingFixedPoint, if_neg hc, hf]

/-- B2 M3: select the direction in which the given finite fixed point is attracting.
The signed-root formula selects C or its inverse; fixing x alone is not the conclusion. -/
theorem s30ls_b2_choose_attracting
    {C : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hCh : 2 < |slTrace C|)
    (hC01 : C 0 1 ≠ 0) (hC10 : C 1 0 ≠ 0) {x : ℝ}
    (hfix : C 1 0 * x ^ 2 + (C 1 1 - C 0 0) * x - C 0 1 = 0) :
    ∃ E : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (E = C ∨ E = C⁻¹) ∧ E 0 1 ≠ 0 ∧ E 1 0 ≠ 0 ∧ 2 < |slTrace E| ∧
      E 1 0 * x ^ 2 + (E 1 1 - E 0 0) * x - E 0 1 = 0 ∧
      attractingFixedPoint E = ((x : ℂ) : ExtPlane) := by
  have ht : 2 < |C 0 0 + C 1 1| := hCh
  obtain ⟨_, hsgn, _, _, hsqrt⟩ := hnf_sign_sqrt ht
  have hd := hnf_sl2_det C
  have hsigned :
      (Real.sign (C 0 0 + C 1 1) * Real.sqrt ((C 0 0 + C 1 1) ^ 2 - 4)) ^ 2 =
      (C 0 0 + C 1 1) ^ 2 - 4 := by
    rw [mul_pow, hsgn, one_mul, hsqrt]
  have hquad : (2 * C 1 0 * x - (C 0 0 - C 1 1)) ^ 2 =
      (Real.sign (C 0 0 + C 1 1) * Real.sqrt ((C 0 0 + C 1 1) ^ 2 - 4)) ^ 2 := by
    rw [hsigned]
    linear_combination 4 * C 1 0 * hfix - 4 * hd
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hquad with h | h
  · refine ⟨C, Or.inl rfl, hC01, hC10, hCh, hfix, ?_⟩
    apply s30ls_b2_attracting_of_eq hC10
    linear_combination h
  · obtain ⟨i00, i01, i10, i11⟩ := s27t_inv_apply C
    have hI01 : C⁻¹ 0 1 ≠ 0 := by
      rw [i01]
      exact neg_ne_zero.2 hC01
    have hI10 : C⁻¹ 1 0 ≠ 0 := by
      rw [i10]
      exact neg_ne_zero.2 hC10
    have hItrace : C⁻¹ 0 0 + C⁻¹ 1 1 = C 0 0 + C 1 1 := by
      rw [i00, i11]
      ring
    have hIh : 2 < |slTrace C⁻¹| := by
      change 2 < |C⁻¹ 0 0 + C⁻¹ 1 1|
      rw [hItrace]
      exact ht
    have hIfix :
        C⁻¹ 1 0 * x ^ 2 + (C⁻¹ 1 1 - C⁻¹ 0 0) * x - C⁻¹ 0 1 = 0 := by
      rw [i00, i01, i10, i11]
      linear_combination -hfix
    refine ⟨C⁻¹, Or.inr rfl, hI01, hI10, hIh, hIfix, ?_⟩
    apply s30ls_b2_attracting_of_eq hI10
    rw [i00, i10, i11, add_comm (C 1 1) (C 0 0)]
    linear_combination -h

/-- B2 M4: positive diagonal scaling sends the selected attractor to 1 while retaining
the expanding diagonal base element. Construct D from the positive square root of x;
use s30l_conj_diag and the explicit attracting-point formula, not general boundary dynamics. -/
theorem s30ls_b2_positive_normalize
    {E B : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hB : B 0 1 = 0 ∧ B 1 0 = 0 ∧ 1 < B 0 0 ^ 2)
    {x : ℝ} (hx : 0 < x) (hE01 : E 0 1 ≠ 0) (hE10 : E 1 0 ≠ 0)
    (hEh : 2 < |slTrace E|)
    (hfix : E 1 0 * x ^ 2 + (E 1 1 - E 0 0) * x - E 0 1 = 0)
    (hatt : attractingFixedPoint E = ((x : ℂ) : ExtPlane)) :
    ∃ D A B' : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      A = D * E * D⁻¹ ∧ B' = D * B * D⁻¹ ∧
      (B' 0 1 = 0 ∧ B' 1 0 = 0 ∧ 1 < B' 0 0 ^ 2) ∧
      A 0 1 ≠ 0 ∧ A 1 0 ≠ 0 ∧ 2 < |slTrace A| ∧
      A 0 0 + A 0 1 = A 1 0 + A 1 1 ∧
      attractingFixedPoint A = ((1 : ℂ) : ExtPlane) := by
  have hr : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hr0 : Real.sqrt x ≠ 0 := hr.ne'
  have hx0 : x ≠ 0 := hx.ne'
  -- Reciprocal first entry sends x to 1; the opposite scaling sends x to x^2.
  let D : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    ⟨!![(Real.sqrt x)⁻¹, 0; 0, Real.sqrt x],
      by simp [Matrix.det_fin_two, hr0]⟩
  let A : Matrix.SpecialLinearGroup (Fin 2) ℝ := D * E * D⁻¹
  let B' : Matrix.SpecialLinearGroup (Fin 2) ℝ := D * B * D⁻¹
  have d11 : D 1 1 = ((Real.sqrt x)⁻¹)⁻¹ := by
    change Real.sqrt x = ((Real.sqrt x)⁻¹)⁻¹
    rw [inv_inv]
  obtain ⟨e00, e01, e10, e11⟩ :=
    s30l_conj_diag (D := D) (g := E) (s := (Real.sqrt x)⁻¹)
      (inv_ne_zero hr0) rfl rfl rfl d11
  obtain ⟨b00, b01, b10, b11⟩ :=
    s30l_conj_diag (D := D) (g := B) (s := (Real.sqrt x)⁻¹)
      (inv_ne_zero hr0) rfl rfl rfl d11
  have hinvsq : ((Real.sqrt x)⁻¹) ^ 2 = x⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hx.le]
  have a00 : A 0 0 = E 0 0 := e00
  have a01 : A 0 1 = x⁻¹ * E 0 1 := by simpa only [hinvsq] using e01
  have a10 : A 1 0 = x * E 1 0 := by
    simpa only [inv_inv, Real.sq_sqrt hx.le] using e10
  have a11 : A 1 1 = E 1 1 := e11
  have hB' : B' 0 1 = 0 ∧ B' 1 0 = 0 ∧ 1 < B' 0 0 ^ 2 := by
    refine ⟨?_, ?_, ?_⟩
    · change (D * B * D⁻¹) 0 1 = 0
      rw [b01, hB.1, mul_zero]
    · change (D * B * D⁻¹) 1 0 = 0
      rw [b10, hB.2.1, mul_zero]
    · change 1 < (D * B * D⁻¹) 0 0 ^ 2
      rw [b00]
      exact hB.2.2
  have hA01 : A 0 1 ≠ 0 := by
    rw [a01]
    exact mul_ne_zero (inv_ne_zero hx0) hE01
  have hA10 : A 1 0 ≠ 0 := by
    rw [a10]
    exact mul_ne_zero hx0 hE10
  have hAh : 2 < |slTrace A| := by
    change 2 < |A 0 0 + A 1 1|
    rw [a00, a11]
    exact hEh
  have hscale : x⁻¹ * E 0 1 = x * E 1 0 + E 1 1 - E 0 0 := by
    calc x⁻¹ * E 0 1 = E 0 1 / x := by rw [div_eq_mul_inv]; ring
      _ = x * E 1 0 + E 1 1 - E 0 0 := by
        apply (div_eq_iff hx0).2
        nlinarith [hfix]
  have hrow : A 0 0 + A 0 1 = A 1 0 + A 1 1 := by
    rw [a00, a01, a10, a11, hscale]
    ring
  have hEeq := hnf_attr_eq hE10 hatt
  have hAatt : attractingFixedPoint A = ((1 : ℂ) : ExtPlane) := by
    apply s30ls_b2_attracting_of_eq hA10
    rw [a00, a10, a11]
    linear_combination hEeq
  exact ⟨D, A, B', rfl, rfl, hB', hA01, hA10, hAh, hrow, hAatt⟩

/-- B2: a compact uniformized Riemann surface admits a conjugated expanding diagonal
base element B and a hyperbolic element A off both axes, with 1 as its attracting fixed
point and equal row sums. No canonical generators or coherent SL section are required. -/
theorem s30ls_b2_normalized_base_pair
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    [CompactSpace S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) :
    ∃ H A B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      IsUniformization (conjGroup Γ H) (adjustProjection p H) ∧
      A ∈ conjGroup Γ H ∧ B ∈ conjGroup Γ H ∧
      (B 0 1 = 0 ∧ B 1 0 = 0 ∧ 1 < B 0 0 ^ 2) ∧
      A 0 1 ≠ 0 ∧ A 1 0 ≠ 0 ∧ 2 < |slTrace A| ∧
      A 0 0 + A 0 1 = A 1 0 + A 1 1 ∧
      attractingFixedPoint A = ((1 : ℂ) : ExtPlane) := by
  classical
  obtain ⟨β, hβ, hβ1, hβm⟩ := s27g_exists_ne_one hp
  have hβh : IsHyperbolic β := s27f_hyp hp hβ hβ1 hβm
  obtain ⟨H₀, lam, hlam, _hlog, hact⟩ := s30w_conj_dilation hβh
  let B₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ := H₀ * β * H₀⁻¹
  have hp₀ : IsUniformization (conjGroup Γ H₀) (adjustProjection p H₀) :=
    adjustProjection_isUniformization hp H₀
  have hB₀mem : B₀ ∈ conjGroup Γ H₀ :=
    s30l_mem_conjGroup.mpr ⟨β, hβ, rfl⟩
  have hB₀ : B₀ 0 1 = 0 ∧ B₀ 1 0 = 0 ∧ 1 < B₀ 0 0 ^ 2 :=
    s30ls_b2_dilation_entries hlam hact
  obtain ⟨x, hxball, hxfixed⟩ :=
    (Metric.dense_iff.mp (fuchsianFixedPoints_dense hp₀)) 1 (1 / 2) (by norm_num)
  have hx : 0 < x := by
    rw [mem_ball, Real.dist_eq] at hxball
    have hleft := (abs_lt.mp hxball).1
    linarith
  change ∃ C ∈ conjGroup Γ H₀, C ≠ 1 ∧ C ≠ -1 ∧
    C 1 0 * x ^ 2 + (C 1 1 - C 0 0) * x - C 0 1 = 0 at hxfixed
  obtain ⟨C, hC, hC1, hCm, hfix⟩ := hxfixed
  have hCh : 2 < |slTrace C| := s27f_hyp hp₀ hC hC1 hCm
  obtain ⟨hC01, hC10⟩ := s30ls_b2_off_axes hp₀ hC hB₀mem hB₀ hCh hx.ne' hfix
  obtain ⟨E, hchoice, hE01, hE10, hEh, hEfix, hEatt⟩ :=
    s30ls_b2_choose_attracting hCh hC01 hC10 hfix
  have hEmem : E ∈ conjGroup Γ H₀ := by
    rcases hchoice with h | h
    · rw [h]
      exact hC
    · rw [h]
      exact (conjGroup Γ H₀).inv_mem hC
  obtain ⟨D, A, B, hAeq, hBeq, hB, hA01, hA10, hAh, hArow, hAatt⟩ :=
    s30ls_b2_positive_normalize hB₀ hx hE01 hE10 hEh hEfix hEatt
  refine ⟨D * H₀, A, B, adjustProjection_isUniformization hp (D * H₀),
    ?_, ?_, hB, hA01, hA10, hAh, hArow, hAatt⟩
  · obtain ⟨a, ha, hEa⟩ := s30l_mem_conjGroup.mp hEmem
    apply s30l_mem_conjGroup.mpr
    refine ⟨a, ha, ?_⟩
    rw [hAeq, hEa]
    group
  · apply s30l_mem_conjGroup.mpr
    refine ⟨β, hβ, ?_⟩
    rw [hBeq]
    dsimp only [B₀]
    group

/-- The forward orbit of a hyperbolic matrix with nonzero lower-left entry tends
to its attracting point. This retains the direction omitted by the existential
statement of `s27t_hyperbolic_dynamics`. -/
theorem s30ls_b3_forward_attractor
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : 2 < |γ 0 0 + γ 1 1|) (hc : γ 1 0 ≠ 0) (w : UpperHalfPlane) :
    Tendsto (fun n : ℕ => (((γ ^ n • w : UpperHalfPlane) : ℂ) : ExtPlane))
      atTop (𝓝 (attractingFixedPoint γ)) := by
  obtain ⟨σ, hσ⟩ := hnf_attr_exists hc
  obtain ⟨τ, hτ⟩ := hnf_rep_exists hc
  obtain ⟨hL, hne, hcross, -, -, -⟩ := hyperbolic_normal_form hγ
  have hL0 : 0 < multiplier γ := lt_trans one_pos hL
  have hLc : (multiplier γ : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
  have hστc : (σ : ℂ) ≠ (τ : ℂ) := by
    intro h
    apply hne
    rw [hσ, hτ, h]
  have hsmul : ∀ u : UpperHalfPlane,
      ((γ • u : UpperHalfPlane) : ℂ) = mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) u := by
    intro u
    rw [h36t_coe_smul]
    rfl
  have hpow : Tendsto (fun n : ℕ => ((multiplier γ : ℂ)⁻¹) ^ n) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 hL0.le)
      (inv_lt_one_of_one_lt₀ hL)
    have h' := (Complex.continuous_ofReal.tendsto 0).comp h
    rw [Complex.ofReal_zero] at h'
    refine h'.congr fun n => ?_
    simp [Function.comp]
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
  have hiter : ∀ n : ℕ, Φ (γ ^ n • w) = Φ w * ((multiplier γ : ℂ)⁻¹) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_smul]
      have h := hΦ (γ ^ n • w)
      rw [ih] at h
      rw [pow_succ]
      field_simp
      linear_combination -h
  have ht : Tendsto (fun n : ℕ => Φ (γ ^ n • w)) atTop (𝓝 0) := by
    have h := hpow.const_mul (Φ w)
    rw [mul_zero] at h
    exact h.congr fun n => (hiter n).symm
  have hlim : Tendsto (fun n : ℕ => ((γ ^ n • w : UpperHalfPlane) : ℂ))
      atTop (𝓝 (σ : ℂ)) :=
    (s27t_tendsto_frac (A := (σ : ℂ)) (B := (τ : ℂ)) ht).congr fun n => (hsolve _).symm
  rw [hσ]
  exact (OnePoint.continuous_coe.tendsto _).comp hlim

/-- Forward attraction at `1` is preserved by a boundary extension of a conjugating
homeomorphism. Both matrices are hyperbolic with finite attracting points. -/
theorem s30ls_b3_attracting_one_transport
    {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {Gb : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension (liftToC F) upperHalf upperHalf Gb)
    (hG1 : Gb ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane))
    {A A' : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hR : RepresentsConj F A A')
    (hAh : 2 < |A 0 0 + A 1 1|) (hA'h : 2 < |A' 0 0 + A' 1 1|)
    (hcA : A 1 0 ≠ 0) (hcA' : A' 1 0 ≠ 0)
    (hAatt : attractingFixedPoint A = ((1 : ℂ) : ExtPlane)) :
    attractingFixedPoint A' = ((1 : ℂ) : ExtPlane) := by
  have hSource := s30ls_b3_forward_attractor hAh hcA UpperHalfPlane.I
  rw [hAatt] at hSource
  have hSeq : Tendsto
      (fun n : ℕ => Gb (((A ^ n • UpperHalfPlane.I : UpperHalfPlane) : ℂ) : ExtPlane))
      atTop (𝓝 (Gb ((1 : ℂ) : ExtPlane))) :=
    (hG.2.1 _ (s27t_mem_closure_real 1)).tendsto.comp (s27l_tendsto_within hSource)
  rw [hG1] at hSeq
  have hstep : ∀ w : UpperHalfPlane, F (A • w) = A' • F w := by
    intro w
    have h := hR (F w)
    rw [F.symm_apply_apply] at h
    exact h.symm
  have hConj : ∀ n : ℕ, F (A ^ n • UpperHalfPlane.I) = A' ^ n • F UpperHalfPlane.I := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp only [pow_succ', mul_smul, hstep, ih]
  have hFromSource : Tendsto
      (fun n : ℕ => (((A' ^ n • F UpperHalfPlane.I : UpperHalfPlane) : ℂ) : ExtPlane))
      atTop (𝓝 ((1 : ℂ) : ExtPlane)) := by
    refine hSeq.congr fun n => ?_
    rw [h36t_ext_coe hG, hConj n]
  exact tendsto_nhds_unique
    (s30ls_b3_forward_attractor hA'h hcA' (F UpperHalfPlane.I)) hFromSource

/-- Finite trace data force a normalized lift to commute with every deck action.
The finite test set is chosen on the source; no faithful surface-group representation
or assumption that the SL deck action is effective is used. -/
theorem s30ls_b5_commutes_of_tests
    {S₁ S₂ : Type u} [TopologicalSpace S₁] [ChartedSpace ℂ S₁] [CompactSpace S₁]
    [TopologicalSpace S₂] [ChartedSpace ℂ S₂]
    {Γ₁ Γ₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₁ : UpperHalfPlane → S₁} {p₂ : UpperHalfPlane → S₂}
    (hp₁ : IsUniformization Γ₁ p₁) (hp₂ : IsUniformization Γ₂ p₂)
    {f : S₁ ≃ₜ S₂} {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {Gb : ExtPlane → ExtPlane}
    (hF : IsNormalizedLift p₁ p₂ f F Gb)
    {A B : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hAmem : A ∈ Γ₁) (hBmem : B ∈ Γ₁)
    (hB : B 0 1 = 0 ∧ B 1 0 = 0 ∧ 1 < B 0 0 ^ 2)
    (hA01 : A 0 1 ≠ 0) (hA10 : A 1 0 ≠ 0) (hAh : 2 < |slTrace A|)
    (hArow : A 0 0 + A 0 1 = A 1 0 + A 1 1)
    (hAatt : attractingFixedPoint A = ((1 : ℂ) : ExtPlane))
    {m : ℕ} {C : Fin m → Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hCmem : ∀ i, C i ∈ Γ₁) (hgen : Subgroup.closure (Set.range C) = Γ₁)
    {T : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hbase : {A, B, A * B, A * B⁻¹} ⊆ T)
    (hwords : ∀ i, ∀ D ∈ ({1, A, A⁻¹, B, B⁻¹, A * B, (A * B)⁻¹,
      A * B⁻¹, (A * B⁻¹)⁻¹} : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)), C i * D ∈ T)
    (htrace : ∀ γ ∈ T, ∀ δ ∈ Γ₂, RepresentsConj F γ δ → |slTrace δ| = |slTrace γ|) :
    ∀ γ ∈ Γ₁, ∀ τ, F (γ • F.symm τ) = γ • τ := by
  classical
  obtain ⟨A₂, hA₂mem, hRA⟩ := s27g_rep_exists hp₁ hp₂ hF.1 hAmem
  obtain ⟨B₂, hB₂mem, hRB⟩ := s27g_rep_exists hp₁ hp₂ hF.1 hBmem
  rcases hF with ⟨hLift, hG, hG0, hG1, hGinf⟩
  obtain ⟨g, hg, hmono, hg0, hg1⟩ := s27g_bdry_real hG hG0 hG1 hGinf
  have hB₂ := s27g_diag hG hG0 hGinf hg hmono hg1 hB hRB
  have hA₂row := s27g_fixes_one hG hG1 hRA hArow
  have hA₂10 : A₂ 1 0 ≠ 0 := by
    intro hzero
    exact hA10 ((s27f_fix_infty hG hGinf hRA).2 hzero)
  have hAt : |slTrace A₂| = |slTrace A| :=
    htrace A (hbase (by simp)) A₂ hA₂mem hRA
  have hBt : |slTrace B₂| = |slTrace B| :=
    htrace B (hbase (by simp)) B₂ hB₂mem hRB
  have hA₂h : 2 < |slTrace A₂| := by
    rw [hAt]
    exact hAh
  have hA₂att := s30ls_b3_attracting_one_transport hG hG1 hRA hAh hA₂h hA10 hA₂10 hAatt
  have hABt : |slTrace (A₂ * B₂)| = |slTrace (A * B)| :=
    htrace (A * B) (hbase (by simp)) (A₂ * B₂)
      (Γ₂.mul_mem hA₂mem hB₂mem) (s27g_rep_mul hRA hRB)
  have hABit : |slTrace (A₂ * B₂⁻¹)| = |slTrace (A * B⁻¹)| :=
    htrace (A * B⁻¹) (hbase (by simp)) (A₂ * B₂⁻¹)
      (Γ₂.mul_mem hA₂mem (Γ₂.inv_mem hB₂mem)) (s27g_rep_mul hRA (s27g_rep_inv hRB))
  obtain ⟨hpmA, hpmB⟩ := s30e1_base_determined hB hB₂ hArow hA₂row hAatt hA₂att
    hAh hA₂h hA01 hA10 hA₂10 hAt hBt hABt hABit
  have hgenerators : ∀ i τ, F (C i • F.symm τ) = C i • τ := by
    intro i
    -- Scalar SL matrices act identically, so they need no hyperbolic reconstruction.
    by_cases hi : C i = 1
    · intro τ
      simp only [hi, one_smul, F.apply_symm_apply]
    by_cases hmi : C i = -1
    · intro τ
      simp only [hmi, s27g_neg_one_smul, F.apply_symm_apply]
    have hCi : 2 < |slTrace (C i)| := s27f_hyp hp₁ (hCmem i) hi hmi
    obtain ⟨C₂, hC₂mem, hRC⟩ := s27g_rep_exists hp₁ hp₂ hLift (hCmem i)
    have hCtest : C i ∈ T := by
      simpa only [mul_one] using hwords i 1 (by simp)
    have hCt : |slTrace C₂| = |slTrace (C i)| := htrace (C i) hCtest C₂ hC₂mem hRC
    have hword : ∀ (D D₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ),
        D ∈ ({1, A, A⁻¹, B, B⁻¹, A * B, (A * B)⁻¹,
          A * B⁻¹, (A * B⁻¹)⁻¹} : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)) →
        D₂ ∈ Γ₂ → RepresentsConj F D D₂ → (D₂ = D ∨ D₂ = -D) →
        |slTrace (C₂ * D)| = |slTrace (C i * D)| := by
      intro D D₂ hD hD₂ hRD hpm
      exact (s30e1_abs_tr_pm (X := C₂) hpm).symm.trans
        (htrace (C i * D) (hwords i D hD) (C₂ * D₂)
          (Γ₂.mul_mem hC₂mem hD₂) (s27g_rep_mul hRC hRD))
    have hAB₂mem := Γ₂.mul_mem hA₂mem hB₂mem
    have hABi₂mem := Γ₂.mul_mem hA₂mem (Γ₂.inv_mem hB₂mem)
    have hRAB := s27g_rep_mul hRA hRB
    have hRABi := s27g_rep_mul hRA (s27g_rep_inv hRB)
    have hpmAB := s30e1_pm_mul hpmA hpmB
    have hpmABi := s30e1_pm_mul hpmA (s30e1_pm_inv hpmB)
    have hpmC := s30e1_gen_determined hB hA01 hA10 hAh hCi hCt
      (hword A A₂ (by simp) hA₂mem hRA hpmA)
      (hword A⁻¹ A₂⁻¹ (by simp) (Γ₂.inv_mem hA₂mem)
        (s27g_rep_inv hRA) (s30e1_pm_inv hpmA))
      (hword B B₂ (by simp) hB₂mem hRB hpmB)
      (hword B⁻¹ B₂⁻¹ (by simp) (Γ₂.inv_mem hB₂mem)
        (s27g_rep_inv hRB) (s30e1_pm_inv hpmB))
      (hword (A * B) (A₂ * B₂) (by simp) hAB₂mem hRAB hpmAB)
      (hword (A * B)⁻¹ (A₂ * B₂)⁻¹ (by simp) (Γ₂.inv_mem hAB₂mem)
        (s27g_rep_inv hRAB) (s30e1_pm_inv hpmAB))
      (hword (A * B⁻¹) (A₂ * B₂⁻¹) (by simp) hABi₂mem hRABi hpmABi)
      (hword (A * B⁻¹)⁻¹ (A₂ * B₂⁻¹)⁻¹ (by simp) (Γ₂.inv_mem hABi₂mem)
        (s27g_rep_inv hRABi) (s30e1_pm_inv hpmABi))
    have hId : RepresentsConj (Homeomorph.refl UpperHalfPlane) (C i) (C i) := fun _ => rfl
    exact s27f_agree_of_pm hRC hId hpmC
  have hagree : ∀ x ∈ Set.range C, ∀ τ, F (x • F.symm τ) =
      (Homeomorph.refl UpperHalfPlane) (x • (Homeomorph.refl UpperHalfPlane).symm τ) := by
    rintro x ⟨i, rfl⟩ τ
    exact hgenerators i τ
  intro γ hγ
  have hcl : γ ∈ Subgroup.closure (Set.range C) := by rwa [hgen]
  exact s30b_agree_closure hagree γ hcl

/-- A lift commuting with the source deck actions has a biholomorphic representative
in its homotopy class. The two projection fibres agree; the descended identity and
the existing homotopy criterion supply the conclusion. -/
theorem s30ls_b5_descend_commuting
    {S₁ S₂ : Type u} [TopologicalSpace S₁] [ChartedSpace ℂ S₁]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁]
    [TopologicalSpace S₂] [ChartedSpace ℂ S₂]
    [T2Space S₂] [ConnectedSpace S₂] [IsManifold 𝓘(ℂ) ω S₂]
    {Γ₁ Γ₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₁ : UpperHalfPlane → S₁} {p₂ : UpperHalfPlane → S₂}
    (hp₁ : IsUniformization Γ₁ p₁) (hp₂ : IsUniformization Γ₂ p₂)
    {f : S₁ ≃ₜ S₂} {F : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hF : IsLift p₁ p₂ f F)
    (hcomm : ∀ γ ∈ Γ₁, ∀ τ, F (γ • F.symm τ) = γ • τ) :
    ∃ φ : S₁ ≃ₜ S₂, IsBiholomorphic φ ∧
      ContinuousMap.Homotopic (f : C(S₁, S₂)) (φ : C(S₁, S₂)) := by
  have hId : IsLift p₁ p₁ (Homeomorph.refl S₁) (Homeomorph.refl UpperHalfPlane) := fun _ => rfl
  have hag : ∀ γ ∈ Γ₁, ∀ τ, F (γ • F.symm τ) =
      (Homeomorph.refl UpperHalfPlane) (γ • (Homeomorph.refl UpperHalfPlane).symm τ) := by
    simpa using hcomm
  obtain ⟨φ, hφ, hlift⟩ := s27l_descend_homeomorph hp₁ hp₂
    (s27l_fiber_transfer hp₁ hp₁ hId hF fun γ hγ τ => (hag γ hγ τ).symm)
    (s27l_fiber_transfer hp₁ hp₂ hF hId hag)
  have hid : IsLift p₁ p₂ φ (Homeomorph.refl UpperHalfPlane) := fun τ => (hlift τ).symm
  refine ⟨φ, hφ, (thm23_1_homotopy_iff hp₁ hp₂ f φ hF hid).2 ?_⟩
  refine ⟨1, Γ₂.one_mem, ?_⟩
  intro γ hγ τ
  simpa using hcomm γ hγ τ

-- B4 reuses the existing deck-loop, free-homotopy, and Mobius invariance APIs.
-- These six proof bodies require no additional helper declarations.

/-- B4.1: the literal finite test set required by Root's B5 endpoint.
The four base tests are joined with range(C) times the nine-factor set.
The factor 1 includes C itself. No signs or relators need to be chosen.
Proof route: finite range, finite insert sets, finite image2 and union;
subgroup multiplication/inversion gives membership of every test.
This contract exposes the B5 membership premises without matrix reconstruction. -/
theorem s30ls_b4_finite_tests
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {A B : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hA : A ∈ Γ) (hB : B ∈ Γ) {m : ℕ}
    (C : Fin m → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hC : ∀ i, C i ∈ Γ)
    (D T : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hD : D = {1, A, A⁻¹, B, B⁻¹, A * B, (A * B)⁻¹, A * B⁻¹, (A * B⁻¹)⁻¹})
    (hT : T = {A, B, A * B, A * B⁻¹} ∪
      Set.image2 (fun x y => x * y) (Set.range C) D) :
    T.Finite ∧ T ⊆ Γ ∧ {A, B, A * B, A * B⁻¹} ⊆ T ∧
      (∀ i, ∀ d ∈ D, C i * d ∈ T) := by
  classical
  have hDfin : D.Finite := by
    rw [hD]
    simp
  have hbasefin : ({A, B, A * B, A * B⁻¹} :
      Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)).Finite := by
    simp
  have hfin : T.Finite := by
    rw [hT]
    exact hbasefin.union
      (Set.Finite.image2 (fun x y => x * y) (Set.finite_range C) hDfin)
  have hDmem : D ⊆ Γ := by
    intro d hd
    rw [hD] at hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Γ.one_mem
    · exact hA
    · exact Γ.inv_mem hA
    · exact hB
    · exact Γ.inv_mem hB
    · exact Γ.mul_mem hA hB
    · exact Γ.inv_mem (Γ.mul_mem hA hB)
    · exact Γ.mul_mem hA (Γ.inv_mem hB)
    · exact Γ.inv_mem (Γ.mul_mem hA (Γ.inv_mem hB))
  have hmem : T ⊆ Γ := by
    intro x hx
    rw [hT] at hx
    rcases hx with hx | hx
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hA
      · exact hB
      · exact Γ.mul_mem hA hB
      · exact Γ.mul_mem hA (Γ.inv_mem hB)
    · obtain ⟨a, ha, d, hd, had⟩ := hx
      obtain ⟨i, rfl⟩ := ha
      rw [← had]
      exact Γ.mul_mem (hC i) (hDmem hd)
  refine ⟨hfin, hmem, ?_, ?_⟩
  · rw [hT]
    exact Set.subset_union_left
  · intro i d hd
    rw [hT]
    exact Or.inr ⟨C i, ⟨i, rfl⟩, d, hd, rfl⟩

/-- B4.2: choose one source loop for every prescribed test matrix.
There is no concatenation of loop words or monodromy convention to reconcile.
Each test is already a literal matrix product. Project a path from tau to gamma*tau.
Covers records that matrix, rather than an arbitrary conjugate chosen afterwards.
The prescribed basepoint is retained for transparency, although B4 uses only Covers.
This general family-selection statement needs no finiteness or compactness. -/
theorem s30ls_b4_family_covers
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    (τ : UpperHalfPlane) (T : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hTmem : T ⊆ Γ) :
    ∃ β : T → Loop S, ∀ γ : T, (β γ).1 = p τ ∧ Covers p γ.1 (β γ) := by
  classical
  let β : T → Loop S := fun γ =>
    Classical.choose (s30ls_b1_covers_of_mem hp τ (hTmem γ.2))
  refine ⟨β, ?_⟩
  intro γ
  exact Classical.choose_spec (s30ls_b1_covers_of_mem hp τ (hTmem γ.2))

/-- B4.3: source enumeration indices and their explicit finite maximum.
Use hrep independently for each chosen loop, then Finset.le_sup at univ membership.
Repeated enumeration indices or repeated loops are permitted.
For an empty indexing type the supremum is 0, and the bound is vacuous.
This contract is selected before target choices; it contains no target surface,
target projection, homeomorphism, normalized lift, or target deck representative. -/
theorem s30ls_b4_enumeration_max
    {S : Type u} [TopologicalSpace S]
    (α : ℕ → Loop S) (hrep : ∀ b : Loop S, ∃ n, FreelyHomotopic b (α n))
    {ι : Type} [Fintype ι] (β : ι → Loop S) :
    ∃ k : ι → ℕ,
      (∀ i, FreelyHomotopic (β i) (α (k i))) ∧
      (∀ i, k i ≤ Finset.univ.sup k) := by
  classical
  let k : ι → ℕ := fun i => Classical.choose (hrep (β i))
  refine ⟨k, ?_, ?_⟩
  · intro i
    exact Classical.choose_spec (hrep (β i))
  · intro i
    exact Finset.le_sup (s := Finset.univ) (f := k) (Finset.mem_univ i)

/-- B4.4: adjusting a covering projection by a real Mobius map preserves free length.
Use s30b_fhl_eq_of_mob with the identity surface homeomorphism and H.
Its projection identity is p(H^-1*(H*tau)) = p(tau).
If the identity-mapped loop is not definitionally identical, identify it by
s30b_fh_of_eq and s30b_fhl_congr; no external definition is unfolded by simp.
This uses length equality directly in ENNReal, with no toReal or finiteness step. -/
theorem s30ls_b4_adjust_length
    {S : Type u} [TopologicalSpace S]
    (p : UpperHalfPlane → S) (H : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (β : Loop S) :
    freeHomotopyLength (adjustProjection p H) β = freeHomotopyLength p β := by
  have hproj : ∀ τ, adjustProjection p H (H • τ) = (Homeomorph.refl S) (p τ) := by
    intro τ
    change p (H⁻¹ • (H • τ)) = p τ
    rw [inv_smul_smul]
  have hmob := s30b_fhl_eq_of_mob (pX := p) (pY := adjustProjection p H)
    (Homeomorph.refl S) H hproj β
  have hloop : FreelyHomotopic
      ⟨(Homeomorph.refl S) β.1, β.2.map (Homeomorph.refl S).continuous⟩ β :=
    s30b_fh_of_eq (fun t => rfl)
  have hsame := s30b_fhl_congr (adjustProjection p H) hloop
  exact hsame.symm.trans hmob

/-- B4.5: the original finite-prefix premise reaches a selected test loop.
First change source coordinates using B4.4, then use its free-homotopy index.
On the target, homotopy from f to q and the mapped free homotopy give
q(beta) freely homotopic to f(alpha(k)). Finally change target coordinates.
The input equality is still for the original p1, p2 and f, exactly as in the book.
q needs only a homotopy to f here; QC is used later to obtain a normalized lift. -/
theorem s30ls_b4_selected_length
    {S₁ S₂ : Type u} [TopologicalSpace S₁] [TopologicalSpace S₂]
    {p₁ : UpperHalfPlane → S₁} {p₂ : UpperHalfPlane → S₂}
    (H₁ H₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (α : ℕ → Loop S₁) {N k : ℕ} (hk : k ≤ N)
    {β : Loop S₁} (hβ : FreelyHomotopic β (α k))
    (f q : S₁ ≃ₜ S₂)
    (hhom : ContinuousMap.Homotopic (f : C(S₁, S₂)) (q : C(S₁, S₂)))
    (hlen : ∀ n ≤ N,
      freeHomotopyLength p₁ (α n) =
        freeHomotopyLength p₂ ⟨f (α n).1, (α n).2.map f.continuous⟩) :
    freeHomotopyLength (adjustProjection p₁ H₁) β =
      freeHomotopyLength (adjustProjection p₂ H₂) ⟨q β.1, β.2.map q.continuous⟩ := by
  have hqf : FreelyHomotopic ⟨q β.1, β.2.map q.continuous⟩
      ⟨f β.1, β.2.map f.continuous⟩ :=
    s30b_fh_symm (s30b_fh_of_homotopic hhom β)
  have hmap : FreelyHomotopic ⟨f β.1, β.2.map f.continuous⟩
      ⟨f (α k).1, (α k).2.map f.continuous⟩ :=
    s30b_fh_map f.continuous hβ
  have htarget : FreelyHomotopic ⟨q β.1, β.2.map q.continuous⟩
      ⟨f (α k).1, (α k).2.map f.continuous⟩ := s30b_fh_trans hqf hmap
  calc
    freeHomotopyLength (adjustProjection p₁ H₁) β = freeHomotopyLength p₁ β :=
      s30ls_b4_adjust_length p₁ H₁ β
    _ = freeHomotopyLength p₁ (α k) := s30b_fhl_congr p₁ hβ
    _ = freeHomotopyLength p₂ ⟨f (α k).1, (α k).2.map f.continuous⟩ := hlen k hk
    _ = freeHomotopyLength p₂ ⟨q β.1, β.2.map q.continuous⟩ :=
      (s30b_fhl_congr p₂ htarget).symm
    _ = freeHomotopyLength (adjustProjection p₂ H₂) ⟨q β.1, β.2.map q.continuous⟩ :=
      (s30ls_b4_adjust_length p₂ H₂ ⟨q β.1, β.2.map q.continuous⟩).symm

/-- B4.6: lift conjugacy transports the literal covering matrix of a chosen loop.
Take F composed with the Covers witness c; IsLift gives its projected loop.
At the endpoints, RepresentsConj at F(c(0)) gives
delta * F(c(0)) = F(gamma * c(0)) = F(c(1)).
No arbitrary choice of a covering element for the image loop is made here.
No injectivity of the SL action or sign-coherent representative system is needed. -/
theorem s30ls_b4_covers_map
    {S₁ S₂ : Type u} [TopologicalSpace S₁] [ChartedSpace ℂ S₁]
    [TopologicalSpace S₂] [ChartedSpace ℂ S₂]
    {p₁ : UpperHalfPlane → S₁} {p₂ : UpperHalfPlane → S₂}
    {q : S₁ ≃ₜ S₂} {F : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hF : IsLift p₁ p₂ q F)
    {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hR : RepresentsConj F γ δ) {β : Loop S₁} (hβ : Covers p₁ γ β) :
    Covers p₂ δ ⟨q β.1, β.2.map q.continuous⟩ := by
  obtain ⟨c, hcc, hcp, hc1⟩ := hβ
  refine ⟨fun t => F (c t), F.continuous.comp_continuousOn hcc, ?_, ?_⟩
  · intro t ht
    rw [hF, hcp t ht]
    show q (β.2.extend t) = (β.2.map q.continuous).extend t
    rw [Path.extend_apply _ ht, Path.extend_apply _ ht]
    rfl
  · show F (c 1) = δ • F (c 0)
    have he : δ • F (c 0) = F (γ • c 0) := by
      have h := hR (F (c 0))
      rw [F.symm_apply_apply] at h
      exact h
    exact (congrArg F hc1).trans he.symm

/-- B4 consumer: finite source test loops select one N that controls every target
representative of every selected test action. This is the complete transfer draft.
Both target projections and the QC replacement remain universally quantified
after N; the replacement only needs its surface homotopy in this contract.
The normalized-lift boundary fields are unnecessary for the transfer itself.
eq30_2_trace_of_length supplies squared traces; sq_eq_sq_iff_abs_eq_abs supplies
absolute traces, including the scalar cases gamma = +1 or -1.
No new absolute-trace classification lemma is assumed. -/
theorem s30ls_b4_prefix_trace_control
    {S₁ : Type u} [TopologicalSpace S₁] [ChartedSpace ℂ S₁]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁]
    {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₁ : UpperHalfPlane → S₁} (hp₁ : IsUniformization Γ₁ p₁)
    (H₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (T : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (hT : T.Finite)
    (hTmem : T ⊆ conjGroup Γ₁ H₁)
    (α : ℕ → Loop S₁) (hrep : ∀ b : Loop S₁, ∃ n, FreelyHomotopic b (α n)) :
    ∃ N : ℕ, ∀ (S₂ : Type u) [TopologicalSpace S₂] [ChartedSpace ℂ S₂]
      [T2Space S₂] [ConnectedSpace S₂] [IsManifold 𝓘(ℂ) ω S₂]
      (Γ₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
      (p₂ : UpperHalfPlane → S₂) (hp₂ : IsUniformization Γ₂ p₂)
      (f q : S₁ ≃ₜ S₂)
      (hhom : ContinuousMap.Homotopic (f : C(S₁, S₂)) (q : C(S₁, S₂)))
      (H₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
      (F : UpperHalfPlane ≃ₜ UpperHalfPlane)
      (hF : IsLift (adjustProjection p₁ H₁) (adjustProjection p₂ H₂) q F),
      (∀ n ≤ N, freeHomotopyLength p₁ (α n) =
        freeHomotopyLength p₂ ⟨f (α n).1, (α n).2.map f.continuous⟩) →
      ∀ γ ∈ T, ∀ δ ∈ conjGroup Γ₂ H₂,
        RepresentsConj F γ δ → |slTrace δ| = |slTrace γ| := by
  classical
  have hpS : IsUniformization (conjGroup Γ₁ H₁) (adjustProjection p₁ H₁) :=
    adjustProjection_isUniformization hp₁ H₁
  obtain ⟨β, hβ⟩ := s30ls_b4_family_covers hpS UpperHalfPlane.I T hTmem
  letI : Fintype T := hT.fintype
  obtain ⟨k, hkrep, hkbound⟩ := s30ls_b4_enumeration_max α hrep β
  let N : ℕ := Finset.univ.sup k
  -- This existential is committed before any target surface is introduced.
  refine ⟨N, ?_⟩
  intro S₂ _ _ _ _ _ Γ₂ p₂ hp₂ f q hhom H₂ F hF hlen
  have hpT : IsUniformization (conjGroup Γ₂ H₂) (adjustProjection p₂ H₂) :=
    adjustProjection_isUniformization hp₂ H₂
  have hΓS : IsFuchsian (conjGroup Γ₁ H₁) := utm_x2_isFuchsian hpS
  have hΓT : IsFuchsian (conjGroup Γ₂ H₂) := utm_x2_isFuchsian hpT
  have hfreeS : ActsFreely (conjGroup Γ₁ H₁) := s27g_actsFreely hpS
  have hfreeT : ActsFreely (conjGroup Γ₂ H₂) := s27g_actsFreely hpT
  intro γ hγ δ hδ hR
  let j : T := ⟨γ, hγ⟩
  have hcovS : Covers (adjustProjection p₁ H₁) γ (β j) := (hβ j).2
  have hcovT : Covers (adjustProjection p₂ H₂) δ
      ⟨q (β j).1, (β j).2.map q.continuous⟩ :=
    s30ls_b4_covers_map hF hR hcovS
  have hlenβ : freeHomotopyLength (adjustProjection p₁ H₁) (β j) =
      freeHomotopyLength (adjustProjection p₂ H₂)
        ⟨q (β j).1, (β j).2.map q.continuous⟩ :=
    s30ls_b4_selected_length H₁ H₂ α (hkbound j) (hkrep j) f q hhom hlen
  have hsq : slTrace γ ^ 2 = slTrace δ ^ 2 :=
    eq30_2_trace_of_length hpS hpT hΓS hΓT hfreeS hfreeT
      (hTmem hγ) hδ hcovS hcovT hlenβ
  exact (sq_eq_sq_iff_abs_eq_abs (slTrace δ) (slTrace γ)).1 hsq.symm

/-- **Theorem 30.2** (由长度谱确定 Riemann 曲面).  Let `S₁`, `S₂` be compact Riemann surfaces of genus
`g > 1`, `f : S₁ → S₂` an orientation preserving homeomorphism, `{αₙ}` a sequence of closed curves
in `S₁` representing all elements of `π₁(S₁)`, `βₙ = f(αₙ)`.  There is `N`, depending only on
`{αₙ}` and `g`, such that `l[αₙ] = l[βₙ]` for `n = 1, …, N` implies that the homotopy class of `f`
contains a conformal map. -/
theorem thm30_2_length_spectrum_determines {S₁ : Type u} [TopologicalSpace S₁] [ChartedSpace ℂ S₁]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g) (h₁ : HasGenus S₁ g)
    {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₁ : UpperHalfPlane → S₁} (hp₁ : IsUniformization Γ₁ p₁)
    (α : ℕ → Loop S₁) (hrep : ∀ β : Loop S₁, ∃ n, FreelyHomotopic β (α n)) :
    ∃ N : ℕ, ∀ (S₂ : Type u) [TopologicalSpace S₂] [ChartedSpace ℂ S₂] [T2Space S₂] [ConnectedSpace S₂]
      [IsManifold 𝓘(ℂ) ω S₂] (h₂ : HasGenus S₂ g) (Γ₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
      (p₂ : UpperHalfPlane → S₂) (hp₂ : IsUniformization Γ₂ p₂) (f : S₁ ≃ₜ S₂) (hf : IsOrientationPreservingRS f),
      (∀ n ≤ N, freeHomotopyLength p₁ (α n) = freeHomotopyLength p₂ ⟨f (α n).1, (α n).2.map f.continuous⟩) →
      ∃ φ : S₁ ≃ₜ S₂, IsBiholomorphic φ ∧ ContinuousMap.Homotopic (f : C(S₁, S₂)) (φ : C(S₁, S₂)) := by
  classical
  have _hg := hg
  -- The frozen genus inequality is retained. B4 itself needs no genus bound.
  letI : CompactSpace S₁ := h₁.1
  -- Every choice in this block depends only on the given source data.
  obtain ⟨H₁, A, B, hpS, hAmem, hBmem, hB, hA01, hA10, hAh, hArow, hAatt⟩ :=
    s30ls_b2_normalized_base_pair hp₁
  obtain ⟨m, C, βgen, hC, hgen⟩ := s30ls_b1_finite_generators hpS UpperHalfPlane.I
  let D : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    {1, A, A⁻¹, B, B⁻¹, A * B, (A * B)⁻¹, A * B⁻¹, (A * B⁻¹)⁻¹}
  let T : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    {A, B, A * B, A * B⁻¹} ∪ Set.image2 (fun x y => x * y) (Set.range C) D
  have hCmem : ∀ i, C i ∈ conjGroup Γ₁ H₁ := fun i => (hC i).1
  have htests : T.Finite ∧ T ⊆ conjGroup Γ₁ H₁ ∧
      {A, B, A * B, A * B⁻¹} ⊆ T ∧ (∀ i, ∀ d ∈ D, C i * d ∈ T) :=
    s30ls_b4_finite_tests hAmem hBmem C hCmem D T rfl rfl
  obtain ⟨hTfinite, hTmem, hbase, hwords⟩ := htests
  obtain ⟨N, hN⟩ := s30ls_b4_prefix_trace_control hp₁ H₁ T hTfinite hTmem α hrep
  -- N is now fixed; only here do target data enter the consumer.
  refine ⟨N, ?_⟩
  intro S₂ _ _ _ _ _ h₂ Γ₂ p₂ hp₂ f hf hlen
  -- This target compactness instance is not involved in the source choices.
  letI : CompactSpace S₂ := h₂.1
  obtain ⟨q, hq, hfq⟩ := exists_qc_in_homotopy_class h₁ h₂ f hf
  -- The source is already normalized by B2; normalize only the target projection.
  obtain ⟨H₂, F, Gb, hnorm⟩ := exists_normalizedLift hpS hp₂ q hq
  have hpT : IsUniformization (conjGroup Γ₂ H₂) (adjustProjection p₂ H₂) :=
    adjustProjection_isUniformization hp₂ H₂
  have htrace : ∀ γ ∈ T, ∀ δ ∈ conjGroup Γ₂ H₂,
      RepresentsConj F γ δ → |slTrace δ| = |slTrace γ| :=
    hN S₂ Γ₂ p₂ hp₂ f q hfq H₂ F hnorm.1 hlen
  -- B5 is exactly Root's open endpoint; no reconstruction is implemented here.
  have hcomm : ∀ γ ∈ conjGroup Γ₁ H₁, ∀ τ, F (γ • F.symm τ) = γ • τ :=
    s30ls_b5_commutes_of_tests hpS hpT hnorm hAmem hBmem hB
      hA01 hA10 hAh hArow hAatt hCmem hgen hbase hwords htrace
  obtain ⟨φ, hφ, hqφ⟩ := s30ls_b5_descend_commuting hpS hpT hnorm.1 hcomm
  exact ⟨φ, hφ, hfq.trans hqφ⟩

/-- A finite family of source tests fixes one prefix before either marked target is chosen.
The conclusion compares the two target traces, without comparing either with the source trace. -/
theorem s30ml_prefix_two_trace
    {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
    [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀)
    (T : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (hT : T.Finite) (hTmem : T ⊆ Γ₀)
    (α : ℕ → Loop S₀) (hrep : ∀ β : Loop S₀, ∃ n, FreelyHomotopic β (α n)) :
    ∃ N : ℕ, ∀ (m₁ m₂ : MarkedRS S₀)
      (Γ₁ Γ₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
      (p₁ : UpperHalfPlane → m₁.X.carrier) (p₂ : UpperHalfPlane → m₂.X.carrier)
      (hp₁ : IsUniformization Γ₁ p₁) (hp₂ : IsUniformization Γ₂ p₂)
      (H₁ H₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
      (F₁ F₂ : UpperHalfPlane ≃ₜ UpperHalfPlane)
      (hF₁ : IsLift p₀ (adjustProjection p₁ H₁) m₁.marking F₁)
      (hF₂ : IsLift p₀ (adjustProjection p₂ H₂) m₂.marking F₂),
      (∀ n ≤ N,
        freeHomotopyLength p₁ ⟨m₁.marking (α n).1, (α n).2.map m₁.marking.continuous⟩ =
        freeHomotopyLength p₂ ⟨m₂.marking (α n).1, (α n).2.map m₂.marking.continuous⟩) →
      ∀ γ ∈ T, ∀ δ₁ ∈ conjGroup Γ₁ H₁, ∀ δ₂ ∈ conjGroup Γ₂ H₂,
        RepresentsConj F₁ γ δ₁ → RepresentsConj F₂ γ δ₂ → |slTrace δ₁| = |slTrace δ₂| := by
  classical
  obtain ⟨β, hβ⟩ := s30ls_b4_family_covers hp₀ UpperHalfPlane.I T hTmem
  letI : Fintype T := hT.fintype
  obtain ⟨k, hkrep, hkbound⟩ := s30ls_b4_enumeration_max α hrep β
  -- Commit the prefix using only the source family, before either target enters.
  refine ⟨Finset.univ.sup k, ?_⟩
  intro m₁ m₂ Γ₁ Γ₂ p₁ p₂ hp₁ hp₂ H₁ H₂ F₁ F₂ hF₁ hF₂ hlen
  have hpT₁ : IsUniformization (conjGroup Γ₁ H₁) (adjustProjection p₁ H₁) :=
    adjustProjection_isUniformization hp₁ H₁
  have hpT₂ : IsUniformization (conjGroup Γ₂ H₂) (adjustProjection p₂ H₂) :=
    adjustProjection_isUniformization hp₂ H₂
  intro γ hγ δ₁ hδ₁ δ₂ hδ₂ hR₁ hR₂
  let j : T := ⟨γ, hγ⟩
  have hcov : Covers p₀ γ (β j) := (hβ j).2
  have hcov₁ : Covers (adjustProjection p₁ H₁) δ₁
      ⟨m₁.marking (β j).1, (β j).2.map m₁.marking.continuous⟩ :=
    s30ls_b4_covers_map hF₁ hR₁ hcov
  have hcov₂ : Covers (adjustProjection p₂ H₂) δ₂
      ⟨m₂.marking (β j).1, (β j).2.map m₂.marking.continuous⟩ :=
    s30ls_b4_covers_map hF₂ hR₂ hcov
  have hlen₁ := s30b_fhl_congr p₁
    (s30b_fh_map m₁.marking.continuous (hkrep j))
  have hlen₂ := s30b_fhl_congr p₂
    (s30b_fh_map m₂.marking.continuous (hkrep j))
  have hlenβ : freeHomotopyLength (adjustProjection p₁ H₁)
        ⟨m₁.marking (β j).1, (β j).2.map m₁.marking.continuous⟩ =
      freeHomotopyLength (adjustProjection p₂ H₂)
        ⟨m₂.marking (β j).1, (β j).2.map m₂.marking.continuous⟩ := by
    calc
      _ = freeHomotopyLength p₁
          ⟨m₁.marking (β j).1, (β j).2.map m₁.marking.continuous⟩ :=
        s30ls_b4_adjust_length p₁ H₁ _
      _ = freeHomotopyLength p₁
          ⟨m₁.marking (α (k j)).1, (α (k j)).2.map m₁.marking.continuous⟩ := hlen₁
      _ = freeHomotopyLength p₂
          ⟨m₂.marking (α (k j)).1, (α (k j)).2.map m₂.marking.continuous⟩ :=
        hlen (k j) (hkbound j)
      _ = freeHomotopyLength p₂
          ⟨m₂.marking (β j).1, (β j).2.map m₂.marking.continuous⟩ := hlen₂.symm
      _ = _ := (s30ls_b4_adjust_length p₂ H₂ _).symm
  have hsq : slTrace δ₁ ^ 2 = slTrace δ₂ ^ 2 :=
    eq30_2_trace_of_length hpT₁ hpT₂
      (utm_x2_isFuchsian hpT₁) (utm_x2_isFuchsian hpT₂)
      (s27g_actsFreely hpT₁) (s27g_actsFreely hpT₂)
      hδ₁ hδ₂ hcov₁ hcov₂ hlenβ
  exact (sq_eq_sq_iff_abs_eq_abs (slTrace δ₁) (slTrace δ₂)).1 hsq

/-- Two normalized lifts with matching finite source-word traces induce the same deck action.
This is the two-target bridge absent from the installed source-versus-target B5 contract.
Its implementation must reuse the existing base/generator matrix determination theorems. -/
theorem s30ml_two_lifts_agree
    {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
    [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {Γ₀ Γ₁ Γ₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀)
    {m₁ m₂ : MarkedRS S₀} {p₁ : UpperHalfPlane → m₁.X.carrier}
    {p₂ : UpperHalfPlane → m₂.X.carrier}
    (hp₁ : IsUniformization Γ₁ p₁) (hp₂ : IsUniformization Γ₂ p₂)
    {F₁ F₂ : UpperHalfPlane ≃ₜ UpperHalfPlane} {Gb₁ Gb₂ : ExtPlane → ExtPlane}
    (hF₁ : IsNormalizedLift p₀ p₁ m₁.marking F₁ Gb₁)
    (hF₂ : IsNormalizedLift p₀ p₂ m₂.marking F₂ Gb₂)
    {A B : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hAmem : A ∈ Γ₀) (hBmem : B ∈ Γ₀)
    (hB : B 0 1 = 0 ∧ B 1 0 = 0 ∧ 1 < B 0 0 ^ 2)
    (hA01 : A 0 1 ≠ 0) (hA10 : A 1 0 ≠ 0) (hAh : 2 < |slTrace A|)
    (hArow : A 0 0 + A 0 1 = A 1 0 + A 1 1)
    (hAatt : attractingFixedPoint A = ((1 : ℂ) : ExtPlane))
    {m : ℕ} {C : Fin m → Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hCmem : ∀ i, C i ∈ Γ₀) (hgen : Subgroup.closure (Set.range C) = Γ₀)
    {T : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hbase : {A, B, A * B, A * B⁻¹} ⊆ T)
    (hwords : ∀ i, ∀ D ∈ ({1, A, A⁻¹, B, B⁻¹, A * B, (A * B)⁻¹,
      A * B⁻¹, (A * B⁻¹)⁻¹} : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)), C i * D ∈ T)
    (htrace : ∀ γ ∈ T, ∀ δ₁ ∈ Γ₁, ∀ δ₂ ∈ Γ₂,
      RepresentsConj F₁ γ δ₁ → RepresentsConj F₂ γ δ₂ → |slTrace δ₁| = |slTrace δ₂|) :
    ∀ γ ∈ Γ₀, ∀ τ, F₁ (γ • F₁.symm τ) = F₂ (γ • F₂.symm τ) := by
  classical
  obtain ⟨A₁, hA₁mem, hRA₁⟩ := s27g_rep_exists hp₀ hp₁ hF₁.1 hAmem
  obtain ⟨B₁, hB₁mem, hRB₁⟩ := s27g_rep_exists hp₀ hp₁ hF₁.1 hBmem
  obtain ⟨A₂, hA₂mem, hRA₂⟩ := s27g_rep_exists hp₀ hp₂ hF₂.1 hAmem
  obtain ⟨B₂, hB₂mem, hRB₂⟩ := s27g_rep_exists hp₀ hp₂ hF₂.1 hBmem
  rcases hF₁ with ⟨hLift₁, hG₁, hG₁0, hG₁1, hG₁inf⟩
  rcases hF₂ with ⟨hLift₂, hG₂, hG₂0, hG₂1, hG₂inf⟩
  obtain ⟨g₁, hg₁, hmono₁, _hg₁0, hg₁1⟩ :=
    s27g_bdry_real hG₁ hG₁0 hG₁1 hG₁inf
  obtain ⟨g₂, hg₂, hmono₂, _hg₂0, hg₂1⟩ :=
    s27g_bdry_real hG₂ hG₂0 hG₂1 hG₂inf
  have hB₁ := s27g_diag hG₁ hG₁0 hG₁inf hg₁ hmono₁ hg₁1 hB hRB₁
  have hB₂ := s27g_diag hG₂ hG₂0 hG₂inf hg₂ hmono₂ hg₂1 hB hRB₂
  have hA₁row := s27g_fixes_one hG₁ hG₁1 hRA₁ hArow
  have hA₂row := s27g_fixes_one hG₂ hG₂1 hRA₂ hArow
  have hA₁01 : A₁ 0 1 ≠ 0 := by
    intro hz
    exact hA01 ((s27f_fix_zero hG₁ hG₁0 hRA₁).2 hz)
  have hA₁10 : A₁ 1 0 ≠ 0 := by
    intro hz
    exact hA10 ((s27f_fix_infty hG₁ hG₁inf hRA₁).2 hz)
  have hA₂10 : A₂ 1 0 ≠ 0 := by
    intro hz
    exact hA10 ((s27f_fix_infty hG₂ hG₂inf hRA₂).2 hz)
  -- Each target A is hyperbolic by its own compact uniformization.
  have hA₁h : 2 < |slTrace A₁| := by
    apply s27f_hyp hp₁ hA₁mem
    · intro he
      apply hA₁10
      rw [he]
      norm_num
    · intro he
      apply hA₁10
      rw [he]
      norm_num [Matrix.SpecialLinearGroup.coe_neg]
  have hA₂h : 2 < |slTrace A₂| := by
    apply s27f_hyp hp₂ hA₂mem
    · intro he
      apply hA₂10
      rw [he]
      norm_num
    · intro he
      apply hA₂10
      rw [he]
      norm_num [Matrix.SpecialLinearGroup.coe_neg]
  have hA₁att := s30ls_b3_attracting_one_transport
    hG₁ hG₁1 hRA₁ hAh hA₁h hA10 hA₁10 hAatt
  have hA₂att := s30ls_b3_attracting_one_transport
    hG₂ hG₂1 hRA₂ hAh hA₂h hA10 hA₂10 hAatt
  have hAt : |slTrace A₂| = |slTrace A₁| :=
    (htrace A (hbase (by simp)) A₁ hA₁mem A₂ hA₂mem hRA₁ hRA₂).symm
  have hBt : |slTrace B₂| = |slTrace B₁| :=
    (htrace B (hbase (by simp)) B₁ hB₁mem B₂ hB₂mem hRB₁ hRB₂).symm
  have hAB₁mem := Γ₁.mul_mem hA₁mem hB₁mem
  have hAB₂mem := Γ₂.mul_mem hA₂mem hB₂mem
  have hABi₁mem := Γ₁.mul_mem hA₁mem (Γ₁.inv_mem hB₁mem)
  have hABi₂mem := Γ₂.mul_mem hA₂mem (Γ₂.inv_mem hB₂mem)
  have hRAB₁ := s27g_rep_mul hRA₁ hRB₁
  have hRAB₂ := s27g_rep_mul hRA₂ hRB₂
  have hRABi₁ := s27g_rep_mul hRA₁ (s27g_rep_inv hRB₁)
  have hRABi₂ := s27g_rep_mul hRA₂ (s27g_rep_inv hRB₂)
  have hABt : |slTrace (A₂ * B₂)| = |slTrace (A₁ * B₁)| :=
    (htrace (A * B) (hbase (by simp)) (A₁ * B₁) hAB₁mem
      (A₂ * B₂) hAB₂mem hRAB₁ hRAB₂).symm
  have hABit : |slTrace (A₂ * B₂⁻¹)| = |slTrace (A₁ * B₁⁻¹)| :=
    (htrace (A * B⁻¹) (hbase (by simp)) (A₁ * B₁⁻¹) hABi₁mem
      (A₂ * B₂⁻¹) hABi₂mem hRABi₁ hRABi₂).symm
  -- Use the first target as the comparison frame, not the original source.
  obtain ⟨hpmA, hpmB⟩ := s30e1_base_determined
    hB₁ hB₂ hA₁row hA₂row hA₁att hA₂att
    hA₁h hA₂h hA₁01 hA₁10 hA₂10 hAt hBt hABt hABit
  have hpmAB := s30e1_pm_mul hpmA hpmB
  have hpmABi := s30e1_pm_mul hpmA (s30e1_pm_inv hpmB)
  have hgenerators : ∀ i τ,
      F₁ (C i • F₁.symm τ) = F₂ (C i • F₂.symm τ) := by
    intro i
    -- Scalar source generators have identity action on both targets.
    by_cases hi : C i = 1
    · intro τ
      simp only [hi, one_smul, F₁.apply_symm_apply, F₂.apply_symm_apply]
    by_cases hmi : C i = -1
    · intro τ
      simp only [hmi, s27g_neg_one_smul, F₁.apply_symm_apply, F₂.apply_symm_apply]
    obtain ⟨C₁, hC₁mem, hRC₁⟩ := s27g_rep_exists hp₀ hp₁ hLift₁ (hCmem i)
    obtain ⟨C₂, hC₂mem, hRC₂⟩ := s27g_rep_exists hp₀ hp₂ hLift₂ (hCmem i)
    have hnscalar : C₁ = 1 ∨ C₁ = -1 → False := by
      intro hs
      have hid : ∀ τ : UpperHalfPlane, C i • τ = τ := by
        intro τ
        apply F₁.injective
        have hh := hRC₁ (F₁ τ)
        rw [F₁.symm_apply_apply] at hh
        rcases hs with hs | hs
        · simpa only [hs, one_smul] using hh.symm
        · simpa only [hs, s27g_neg_one_smul] using hh.symm
      rcases s27g_eq_one_of_smul_eq hid with he | he
      · exact hi he
      · exact hmi he
    have hC₁h : 2 < |slTrace C₁| :=
      s27f_hyp hp₁ hC₁mem (fun he => hnscalar (Or.inl he))
        (fun he => hnscalar (Or.inr he))
    have hCtest : C i ∈ T := by
      simpa only [mul_one] using hwords i 1 (by simp)
    have hCt : |slTrace C₂| = |slTrace C₁| :=
      (htrace (C i) hCtest C₁ hC₁mem C₂ hC₂mem hRC₁ hRC₂).symm
    have hword : ∀ (D D₁ D₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ),
        D ∈ ({1, A, A⁻¹, B, B⁻¹, A * B, (A * B)⁻¹,
          A * B⁻¹, (A * B⁻¹)⁻¹} : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)) →
        D₁ ∈ Γ₁ → D₂ ∈ Γ₂ →
        RepresentsConj F₁ D D₁ → RepresentsConj F₂ D D₂ →
        (D₂ = D₁ ∨ D₂ = -D₁) →
        |slTrace (C₂ * D₁)| = |slTrace (C₁ * D₁)| := by
      intro D D₁ D₂ hD hD₁ hD₂ hRD₁ hRD₂ hpm
      exact (s30e1_abs_tr_pm (X := C₂) hpm).symm.trans
        (htrace (C i * D) (hwords i D hD)
          (C₁ * D₁) (Γ₁.mul_mem hC₁mem hD₁)
          (C₂ * D₂) (Γ₂.mul_mem hC₂mem hD₂)
          (s27g_rep_mul hRC₁ hRD₁) (s27g_rep_mul hRC₂ hRD₂)).symm
    have hpmC := s30e1_gen_determined hB₁ hA₁01 hA₁10 hA₁h hC₁h hCt
      (hword A A₁ A₂ (by simp) hA₁mem hA₂mem hRA₁ hRA₂ hpmA)
      (hword A⁻¹ A₁⁻¹ A₂⁻¹ (by simp) (Γ₁.inv_mem hA₁mem) (Γ₂.inv_mem hA₂mem)
        (s27g_rep_inv hRA₁) (s27g_rep_inv hRA₂) (s30e1_pm_inv hpmA))
      (hword B B₁ B₂ (by simp) hB₁mem hB₂mem hRB₁ hRB₂ hpmB)
      (hword B⁻¹ B₁⁻¹ B₂⁻¹ (by simp) (Γ₁.inv_mem hB₁mem) (Γ₂.inv_mem hB₂mem)
        (s27g_rep_inv hRB₁) (s27g_rep_inv hRB₂) (s30e1_pm_inv hpmB))
      (hword (A * B) (A₁ * B₁) (A₂ * B₂) (by simp)
        hAB₁mem hAB₂mem hRAB₁ hRAB₂ hpmAB)
      (hword (A * B)⁻¹ (A₁ * B₁)⁻¹ (A₂ * B₂)⁻¹ (by simp)
        (Γ₁.inv_mem hAB₁mem) (Γ₂.inv_mem hAB₂mem)
        (s27g_rep_inv hRAB₁) (s27g_rep_inv hRAB₂) (s30e1_pm_inv hpmAB))
      (hword (A * B⁻¹) (A₁ * B₁⁻¹) (A₂ * B₂⁻¹) (by simp)
        hABi₁mem hABi₂mem hRABi₁ hRABi₂ hpmABi)
      (hword (A * B⁻¹)⁻¹ (A₁ * B₁⁻¹)⁻¹ (A₂ * B₂⁻¹)⁻¹ (by simp)
        (Γ₁.inv_mem hABi₁mem) (Γ₂.inv_mem hABi₂mem)
        (s27g_rep_inv hRABi₁) (s27g_rep_inv hRABi₂) (s30e1_pm_inv hpmABi))
    intro τ
    exact (s27f_agree_of_pm hRC₂ hRC₁ hpmC τ).symm
  have hagree : ∀ x ∈ Set.range C, ∀ τ,
      F₁ (x • F₁.symm τ) = F₂ (x • F₂.symm τ) := by
    rintro x ⟨i, rfl⟩ τ
    exact hgenerators i τ
  intro γ hγ
  have hcl : γ ∈ Subgroup.closure (Set.range C) := by rwa [hgen]
  exact s30b_agree_closure hagree γ hcl

/-- Equivalent markings have equal free lengths for every source loop and arbitrary
uniformizing projections, via the Mobius lift of the biholomorphic equivalence. -/
theorem s30ml_equiv_lengths
    {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
    {m₁ m₂ : MarkedRS S₀}
    {Γ₁ Γ₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₁ : UpperHalfPlane → m₁.X.carrier} {p₂ : UpperHalfPlane → m₂.X.carrier}
    (hp₁ : IsUniformization Γ₁ p₁) (hp₂ : IsUniformization Γ₂ p₂)
    (heq : m₁.Equiv m₂) (β : Loop S₀) :
    freeHomotopyLength p₁ ⟨m₁.marking β.1, β.2.map m₁.marking.continuous⟩ =
      freeHomotopyLength p₂ ⟨m₂.marking β.1, β.2.map m₂.marking.continuous⟩ := by
  obtain ⟨c, hc, hhom⟩ := heq
  obtain ⟨τ₂, hτ₂⟩ := hp₂.2.2.1 (c (p₁ UpperHalfPlane.I))
  obtain ⟨F, hF, -⟩ := exists_lift hp₁ hp₂ c UpperHalfPlane.I τ₂ hτ₂
  obtain ⟨A, hA⟩ := utm_eq_smul_of_isKQC_one F
    (h23l_lift_isKQC hp₁ hp₂ ((isKQCRS_one_iff c).2 hc) hF)
  have hmob : ∀ τ, p₂ (A • τ) = c (p₁ τ) := by
    intro τ
    rw [← hA τ]
    exact hF τ
  rw [← s30b_fhl_eq_of_mob c A hmob]
  apply s30b_fhl_congr
  have hloops := s30b_fh_of_homotopic hhom β
  refine s30b_fh_trans ?_ (s30b_fh_trans hloops ?_)
  · exact s30b_fh_of_eq fun t => rfl
  · exact s30b_fh_of_eq fun t => rfl

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]

/-- §30.5: the length spectrum of a marked surface `(S, f)`: `{l[f(αₙ)]}`; it depends only on the
class `[S, f] ∈ T(S₀)`, and (Theorem 30.2) two points of `T(S₀)` with the same first `N` terms
coincide. -/
theorem markedLengthSpectrum_wellDefined {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (α : ℕ → Loop S₀)
    (hrep : ∀ β : Loop S₀, ∃ n, FreelyHomotopic β (α n)) :
    ∃ N : ℕ, ∀ (m₁ m₂ : MarkedRS S₀) (Γ₁ Γ₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
      (p₁ : UpperHalfPlane → m₁.X.carrier) (p₂ : UpperHalfPlane → m₂.X.carrier),
      IsUniformization Γ₁ p₁ → IsUniformization Γ₂ p₂ →
      ((m₁.Equiv m₂) ↔ ∀ n ≤ N, freeHomotopyLength p₁ ⟨m₁.marking (α n).1, (α n).2.map m₁.marking.continuous⟩ =
        freeHomotopyLength p₂ ⟨m₂.marking (α n).1, (α n).2.map m₂.marking.continuous⟩) := by
  classical
  obtain ⟨Γ₀, p₀, _hΓ₀, _hfree₀, hp₀⟩ := s22hg_exists_fuchsian_uniformization hg hS
  obtain ⟨H₀, A, B, hpS, hAmem, hBmem, hB, hA01, hA10, hAh, hArow, hAatt⟩ :=
    s30ls_b2_normalized_base_pair hp₀
  obtain ⟨m, C, _βgen, hC, hgen⟩ := s30ls_b1_finite_generators hpS UpperHalfPlane.I
  let D : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    {1, A, A⁻¹, B, B⁻¹, A * B, (A * B)⁻¹, A * B⁻¹, (A * B⁻¹)⁻¹}
  let T : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    {A, B, A * B, A * B⁻¹} ∪ Set.image2 (fun x y => x * y) (Set.range C) D
  have hCmem : ∀ i, C i ∈ conjGroup Γ₀ H₀ := fun i => (hC i).1
  obtain ⟨hTfinite, hTmem, hbase, hwords⟩ :=
    s30ls_b4_finite_tests hAmem hBmem C hCmem D T rfl rfl
  obtain ⟨N, hN⟩ := s30ml_prefix_two_trace hpS T hTfinite hTmem α hrep
  -- The single source-only prefix is fixed before both targets and projections.
  refine ⟨N, ?_⟩
  intro m₁ m₂ Γ₁ Γ₂ p₁ p₂ hp₁ hp₂
  constructor
  · intro heq n _hn
    exact s30ml_equiv_lengths hp₁ hp₂ heq (α n)
  · intro hlen
    obtain ⟨H₁, F₁, Gb₁, hnorm₁⟩ := exists_normalizedLift hpS hp₁ m₁.marking m₁.qc
    obtain ⟨H₂, F₂, Gb₂, hnorm₂⟩ := exists_normalizedLift hpS hp₂ m₂.marking m₂.qc
    have hpT₁ := adjustProjection_isUniformization hp₁ H₁
    have hpT₂ := adjustProjection_isUniformization hp₂ H₂
    have htrace : ∀ γ ∈ T, ∀ δ₁ ∈ conjGroup Γ₁ H₁, ∀ δ₂ ∈ conjGroup Γ₂ H₂,
        RepresentsConj F₁ γ δ₁ → RepresentsConj F₂ γ δ₂ → |slTrace δ₁| = |slTrace δ₂| :=
      hN m₁ m₂ Γ₁ Γ₂ p₁ p₂ hp₁ hp₂ H₁ H₂ F₁ F₂ hnorm₁.1 hnorm₂.1 hlen
    have hag := s30ml_two_lifts_agree hpS hpT₁ hpT₂ hnorm₁ hnorm₂
      hAmem hBmem hB hA01 hA10 hAh hArow hAatt hCmem hgen hbase hwords htrace
    exact s27f_equiv_of_agree hpS hpT₁ hpT₂ hnorm₁.1 hnorm₂.1 hag

end LiZhongQC
