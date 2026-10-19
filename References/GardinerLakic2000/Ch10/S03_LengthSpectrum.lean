import References.GardinerLakic2000.Ch10.S02_ModuliSets

/-!
# Gardiner–Lakic 2000, Ch. 10 §10.3 The length spectrum

Source `teichmuller.txt`, lines 8080–8169 (Chapter 10, §10.3).

* Definition 3 (the length spectrum `LS(Γ)`, the numbers `log λ` of the hyperbolic elements, l. 8081) — exists:
  `LiZhongQC.lengthSpectrum`
* Theorem 3 (l. 8085; cited in §10.4) — `thm10_3`
* Remark (the stronger statement: finitely many conjugacy classes with `ℓ(A) ≤ M`, l. 8087; this is what is proved) —
  `thm10_3_classes`
* Lemma 1 (Shimizu [Shi59], l. 8101) — `lemma10_1_a`, `lemma10_1_b`

Not items: "`LS(Γ)` is the set of lengths of closed geodesics" (l. 8083, U−); the (modified) Nielsen kernel (l. 8089,
a device of the proof); the Remark on better results (l. 8168). Modelling: "finitely generated" is `Group.FG`; a
discrete subset of `ℝ` with all elements positive is read as "only finitely many elements `≤ M` for every `M`" (the
book's proof proves this); near miss `LiZhongQC.lengthSpectrum_discrete` (cocompact torsion-free groups only). In
Lemma 1, `A(z) = z + 1` is the matrix `(1 1; 0 1)`; "`A` is not a power of an element of `Γ`" is read modulo `±1`, and
the strip `D` is `{y ≥ 1, 0 ≤ x < 1}`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (IsFuchsian lengthSpectrum IsHyperbolic translationLength h36p_m)

/-- Helper for `lemma10_1_a`: in a Fuchsian group, only finitely many elements have entries with
`|a| + |b| + |c| + |d| ≤ B` (they all move `i` into one closed ball, by `dist_smul_eq_arsinh`). -/
theorem gl10_finite_bounded {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (B : ℝ) :
    {g ∈ Γ | |g 0 0| + |g 0 1| + |g 1 0| + |g 1 1| ≤ B}.Finite := by
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 * Real.arsinh (max B 0 / 2) := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by
    rw [hRdef]
    exact mul_nonneg (by norm_num) (Real.arsinh_nonneg_iff.2 (div_nonneg (le_max_right _ _) (by norm_num)))
  refine (hΓ _ (isCompact_closedBall UpperHalfPlane.I R)).subset ?_
  rintro g ⟨hg, hgB⟩
  refine ⟨hg, g • UpperHalfPlane.I, ⟨UpperHalfPlane.I, mem_closedBall_self hR0, rfl⟩,
    mem_closedBall.2 ?_⟩
  rw [dist_comm, (LiZhongQC.dist_smul_eq_arsinh g UpperHalfPlane.I).1, hRdef, UpperHalfPlane.coe_I,
    UpperHalfPlane.I_im, mul_one]
  refine mul_le_mul_of_nonneg_left (Real.arsinh_le_arsinh.2 ?_) (by norm_num)
  refine div_le_div_of_nonneg_right ?_ (by norm_num)
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, mul_one,
    ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  have := abs_sub (g 1 1) (g 0 0)
  have := le_max_left B 0
  linarith

/-- Helper for `lemma10_1_b`: the entries of `g⁻¹ = (d, -b; -c, a)`. -/
theorem gl10_inv_entries (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    g⁻¹ 0 0 = g 1 1 ∧ g⁻¹ 0 1 = -g 0 1 ∧ g⁻¹ 1 0 = -g 1 0 ∧ g⁻¹ 1 1 = g 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

/-- Helper for `lemma10_1_b`: the powers of `g = (s, su; 0, s)` are `gᵏ = (sᵏ, sᵏ k u; 0, sᵏ)`. -/
theorem gl10_pow_entries (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) {s u : ℝ} (h10 : g 1 0 = 0)
    (h00 : g 0 0 = s) (h11 : g 1 1 = s) (h01 : g 0 1 = s * u) (k : ℕ) :
    (g ^ k) 1 0 = 0 ∧ (g ^ k) 0 0 = s ^ k ∧ (g ^ k) 1 1 = s ^ k ∧ (g ^ k) 0 1 = s ^ k * (k * u) := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨e10, e00, e11, e01⟩ := ih
    rw [pow_succ]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, e10, e00, e11, e01,
      h10, h00, h11, h01]
    push_cast
    refine ⟨by ring, by ring, by ring, by ring⟩

/-- Helper for `lemma10_1_b`: the integer powers of `A : z ↦ z + 1` are `Aʲ = (1, j; 0, 1)`. -/
theorem gl10_zpow_entries {A : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hA1 : A 0 0 = 1 ∧ A 0 1 = 1 ∧ A 1 0 = 0 ∧ A 1 1 = 1) (j : ℤ) :
    (A ^ j) 0 0 = 1 ∧ (A ^ j) 0 1 = j ∧ (A ^ j) 1 0 = 0 ∧ (A ^ j) 1 1 = 1 := by
  obtain ⟨e00, e01, e10, e11⟩ := hA1
  obtain ⟨i00, i01, i10, i11⟩ := gl10_inv_entries A
  refine Int.induction_on j (by simp) (fun n ih => ?_) (fun n ih => ?_)
  · obtain ⟨f00, f01, f10, f11⟩ := ih
    rw [zpow_add_one]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e10, e11,
      f00, f01, f10, f11]
    push_cast
    refine ⟨by ring, by ring, by ring, by ring⟩
  · obtain ⟨f00, f01, f10, f11⟩ := ih
    rw [zpow_sub_one]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, i00, i01, i10, i11,
      e00, e01, e10, e11, f00, f01, f10, f11]
    push_cast
    refine ⟨by ring, by ring, by ring, by ring⟩

/-- Helper for `lemma10_1_b`: if the Fuchsian group `Γ` contains `A : z ↦ z + 1` and `A` is not a power `γᵏ`
(`k ≥ 2`) of an element, up to sign, then every element `(a, b; 0, a)` of `Γ` is a translation `z ↦ z + ab` by an
integer. (The amounts `ab` form an additive subgroup of `ℝ`, discrete by `IsFuchsian`, hence cyclic `ℤ t₀`;
`1 = k t₀` and primitivity force `k = 1`.) -/
theorem gl10_transl_int {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hA : A ∈ Γ) (hA1 : A 0 0 = 1 ∧ A 0 1 = 1 ∧ A 1 0 = 0 ∧ A 1 1 = 1)
    (hprim : ∀ γ ∈ Γ, ∀ k : ℕ, 2 ≤ k → γ ^ k ≠ A ∧ γ ^ k ≠ -A)
    {g : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hg : g ∈ Γ) (h10 : g 1 0 = 0) (h11 : g 0 0 = g 1 1) :
    ∃ n : ℤ, g 0 1 * g 0 0 = n := by
  have hsq : ∀ h : Matrix.SpecialLinearGroup (Fin 2) ℝ, h 1 0 = 0 → h 0 0 = h 1 1 → h 0 0 ^ 2 = 1 := by
    intro h e10 e11
    have hd := h.det_coe
    rw [Matrix.det_fin_two, e10, ← e11, mul_zero, sub_zero] at hd
    rw [sq]
    exact hd
  let S : AddSubgroup ℝ :=
    { carrier := {t | ∃ h ∈ Γ, h 1 0 = 0 ∧ h 0 0 = h 1 1 ∧ h 0 1 * h 0 0 = t}
      add_mem' := by
        rintro _ _ ⟨g₁, hg₁, a10, a11, rfl⟩ ⟨g₂, hg₂, b10, b11, rfl⟩
        have sa := hsq g₁ a10 a11
        have sb := hsq g₂ b10 b11
        refine ⟨g₁ * g₂, Γ.mul_mem hg₁ hg₂, ?_, ?_, ?_⟩ <;>
          simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, a10, b10]
        · ring
        · rw [← a11, ← b11]; ring
        · rw [← b11]
          linear_combination (g₂ 0 1 * g₂ 0 0) * sa + (g₁ 0 1 * g₁ 0 0) * sb
      zero_mem' := ⟨1, Γ.one_mem, by simp, by simp, by simp⟩
      neg_mem' := by
        rintro _ ⟨h, hh, e10, e11, rfl⟩
        obtain ⟨i00, i01, i10, i11⟩ := gl10_inv_entries h
        refine ⟨h⁻¹, Γ.inv_mem hh, by rw [i10, e10, neg_zero], by rw [i00, i11, e11], ?_⟩
        rw [i01, i00, ← e11]
        ring }
  have hmemS : ∀ t : ℝ, t ∈ S ↔ ∃ h ∈ Γ, h 1 0 = 0 ∧ h 0 0 = h 1 1 ∧ h 0 1 * h 0 0 = t := fun _ => Iff.rfl
  -- discreteness: finitely many amounts in `(0, 1)`
  have hfin : (S ∩ Ioo (0 : ℝ) 1 : Set ℝ).Finite := by
    refine ((gl10_finite_bounded hΓ 3).image fun h => h 0 1 * h 0 0).subset ?_
    rintro t ⟨ht, ht0, ht1⟩
    obtain ⟨h, hh, e10, e11, rfl⟩ := (hmemS _).1 ht
    have s2 := hsq h e10 e11
    have a00 : |h 0 0| = 1 :=
      (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).1 (by rw [sq_abs, s2])
    have a01 : |h 0 1| < 1 := by
      have : |h 0 1 * h 0 0| < 1 := abs_lt.2 ⟨by linarith, ht1⟩
      rwa [abs_mul, a00, mul_one] at this
    refine ⟨h, ⟨hh, ?_⟩, rfl⟩
    rw [e10, abs_zero, ← e11, a00]
    linarith
  have hnd : ¬ Dense (S : Set ℝ) := by
    intro hD
    have hne : (S ∩ Ioo (0 : ℝ) 1 : Set ℝ).Nonempty := by
      obtain ⟨t, ht1, ht2⟩ := hD.inter_open_nonempty (Ioo 0 1) isOpen_Ioo ⟨1 / 2, by norm_num, by norm_num⟩
      exact ⟨t, ht2, ht1⟩
    obtain ⟨m, ⟨hmS, hm0, hm1⟩, hmin⟩ := Set.exists_min_image _ id hfin hne
    obtain ⟨t, ht1, ht2⟩ := hD.inter_open_nonempty (Ioo 0 m) isOpen_Ioo ⟨m / 2, by linarith, by linarith⟩
    exact absurd (hmin t ⟨ht2, ht1.1, ht1.2.trans hm1⟩) (not_le.2 ht1.2)
  obtain ⟨a0, ha0⟩ := S.dense_or_cyclic.resolve_left hnd
  rw [← AddSubgroup.zmultiples_eq_closure] at ha0
  have h1S : (1 : ℝ) ∈ S := (hmemS 1).2 ⟨A, hA, hA1.2.2.1, by rw [hA1.1, hA1.2.2.2], by rw [hA1.1, hA1.2.1, one_mul]⟩
  rw [ha0, AddSubgroup.mem_zmultiples_iff] at h1S
  obtain ⟨n, hn⟩ := h1S
  rw [zsmul_eq_mul] at hn
  -- `|a0| ∈ S`
  have habsS : |a0| ∈ S := by
    have h0 : a0 ∈ S := by rw [ha0]; exact AddSubgroup.mem_zmultiples a0
    rcases abs_choice a0 with h | h <;> rw [h]
    · exact h0
    · exact S.neg_mem h0
  obtain ⟨g0, hg0, f10, f11, f01⟩ := (hmemS _).1 habsS
  have s0 := hsq g0 f10 f11
  have hk : (n.natAbs : ℝ) * |a0| = 1 := by
    rw [Nat.cast_natAbs, Int.cast_abs, ← abs_mul, hn, abs_one]
  have hpow := gl10_pow_entries g0 (s := g0 0 0) (u := |a0|) f10 rfl f11.symm (by
    rw [← f01]
    linear_combination (-(g0 0 1)) * s0) n.natAbs
  rw [hk] at hpow
  obtain ⟨p10, p00, p11, p01⟩ := hpow
  have hsk : g0 0 0 ^ n.natAbs * g0 0 0 ^ n.natAbs = 1 := by rw [← mul_pow, ← sq, s0, one_pow]
  have hk1 : n.natAbs = 1 := by
    by_contra hne
    have hk0 : n.natAbs ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero, zero_mul] at hk
      exact zero_ne_one hk
    have h2 : 2 ≤ n.natAbs := by omega
    rcases mul_self_eq_one_iff.1 hsk with hs | hs
    · refine (hprim g0 hg0 _ h2).1 (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)
      fin_cases i <;> fin_cases j <;> simp [p00, p01, p10, p11, hs, hA1.1, hA1.2.1, hA1.2.2.1, hA1.2.2.2]
    · refine (hprim g0 hg0 _ h2).2 (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.coe_neg, p00, p01, p10, p11, hs, hA1.1, hA1.2.1, hA1.2.2.1, hA1.2.2.2]
  rw [hk1, Nat.cast_one, one_mul] at hk
  have hgS : g 0 1 * g 0 0 ∈ S := (hmemS _).2 ⟨g, hg, h10, h11, rfl⟩
  rw [ha0, AddSubgroup.mem_zmultiples_iff] at hgS
  obtain ⟨m, hm⟩ := hgS
  rw [zsmul_eq_mul] at hm
  rcases abs_choice a0 with h | h
  · exact ⟨m, by rw [← hm, ← h, hk, mul_one]⟩
  · refine ⟨-m, ?_⟩
    rw [← hm, show a0 = -1 by linarith]
    push_cast
    ring

/-- **Theorem 3** (§10.3, l. 8085). For a finitely generated Fuchsian group `Γ`, `LS(Γ)` is a discrete subset of `ℝ`:
only finitely many of its elements are `≤ M`, for every `M`. -/
theorem thm10_3 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfg : Group.FG Γ)
    (M : ℝ) : {ℓ ∈ lengthSpectrum Γ | ℓ ≤ M}.Finite := by
  sorry

/-- **Remark** (§10.3, l. 8087). For every `M > 0`, the set of conjugacy classes `[A]` of hyperbolic `A ∈ Γ` with
`ℓ(A) ≤ M` is finite. -/
theorem thm10_3_classes {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfg : Group.FG Γ)
    (M : ℝ) :
    (ConjClasses.mk '' {γ : Γ | IsHyperbolic (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∧
      translationLength (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) ≤ M}).Finite := by
  sorry

/-- **Lemma 1** (Shimizu, §10.3, l. 8101), first part. If the Fuchsian group `Γ` contains `A(z) = z + 1`, every element
`(a b; c d)` of `Γ` with `c ≠ 0` has `|c| ≥ 1`. -/
theorem lemma10_1_a {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hA : A ∈ Γ) (hA1 : A 0 0 = 1 ∧ A 0 1 = 1 ∧ A 1 0 = 0 ∧ A 1 1 = 1) :
    ∀ B ∈ Γ, B 1 0 ≠ 0 → 1 ≤ |B 1 0| := by
  -- Shimizu's argument, as in `LiZhongQC.parabolic_horoball_disjoint` (whose `hstab` only serves to get `c ≠ 0`)
  intro β hβ hc0
  by_contra hlt
  rw [not_le] at hlt
  have hcpos : 0 < |β 1 0| := abs_pos.2 hc0
  obtain ⟨seq, hseq0, hseqS⟩ : ∃ seq : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ,
      seq 0 = β ∧ ∀ n, seq (n + 1) = seq n * A * (seq n)⁻¹ :=
    ⟨fun n => Nat.rec β (fun _ g => g * A * g⁻¹) n, rfl, fun _ => rfl⟩
  have hmem : ∀ n, seq n ∈ Γ := by
    intro n
    induction n with
    | zero => rw [hseq0]; exact hβ
    | succ n ih => rw [hseqS]; exact Γ.mul_mem (Γ.mul_mem ih hA) (Γ.inv_mem ih)
  have hcabs : ∀ n, |seq n 1 0| = |β 1 0| ^ (2 ^ n) := by
    intro n
    induction n with
    | zero => rw [hseq0, pow_zero, pow_one]
    | succ n ih =>
      rw [hseqS, (LiZhongQC.conj_translation_entries hA1 (seq n)).2.2.1, abs_neg, abs_pow, ih, ← pow_mul,
        pow_succ]
  have hcle : ∀ n, |seq n 1 0| ≤ |β 1 0| := fun n => by
    rw [hcabs]
    exact pow_le_of_le_one (abs_nonneg _) hlt.le (pow_ne_zero n two_ne_zero)
  -- the top-left entries stay bounded
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = max |β 0 0| (1 / (1 - |β 1 0|)) := ⟨_, rfl⟩
  have hM1 : 1 + M * |β 1 0| ≤ M := by
    have h1 : 1 / (1 - |β 1 0|) ≤ M := hMdef ▸ le_max_right _ _
    rw [div_le_iff₀ (by linarith)] at h1
    linarith
  have hM0 : 0 ≤ M := hMdef ▸ (abs_nonneg _).trans (le_max_left _ _)
  have habound : ∀ n, |seq n 0 0| ≤ M := by
    intro n
    induction n with
    | zero => rw [hseq0, hMdef]; exact le_max_left _ _
    | succ n ih =>
      rw [hseqS, (LiZhongQC.conj_translation_entries hA1 (seq n)).1]
      calc |1 - seq n 0 0 * seq n 1 0| ≤ 1 + |seq n 0 0| * |seq n 1 0| := by
            rw [← abs_mul]
            exact (abs_sub _ _).trans (by rw [abs_one])
        _ ≤ 1 + M * |β 1 0| :=
            add_le_add le_rfl (mul_le_mul ih (hcle n) (abs_nonneg _) hM0)
        _ ≤ M := hM1
  -- all entries stay bounded
  obtain ⟨Bd, hBdef⟩ : ∃ Bd : ℝ, Bd = M + (|β 0 1| + M ^ 2) + 1 + (|β 1 1| + (1 + M)) := ⟨_, rfl⟩
  have hBbound : ∀ n, |seq n 0 0| + |seq n 0 1| + |seq n 1 0| + |seq n 1 1| ≤ Bd := by
    intro n
    cases n with
    | zero =>
      rw [hseq0, hBdef]
      have ha := habound 0
      rw [hseq0] at ha
      nlinarith [abs_nonneg (β 0 1), abs_nonneg (β 1 1), sq_nonneg M]
    | succ n =>
      obtain ⟨e00, e01, e10, e11⟩ := LiZhongQC.conj_translation_entries hA1 (seq n)
      have ha := habound (n + 1)
      have hc := hcle (n + 1)
      rw [hseqS] at ha hc ⊢
      rw [e01, e11, hBdef]
      have h01 : |seq n 0 0 ^ 2| ≤ M ^ 2 := by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (habound n) 2
      have h11 : |1 + seq n 0 0 * seq n 1 0| ≤ 1 + M := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_one, abs_mul]
        have := habound n
        have := hcle n
        nlinarith [abs_nonneg (seq n 0 0), abs_nonneg (seq n 1 0)]
      nlinarith [abs_nonneg (β 0 1), abs_nonneg (β 1 1)]
  have hrange : range seq ⊆ {g ∈ Γ | |g 0 0| + |g 0 1| + |g 1 0| + |g 1 1| ≤ Bd} := by
    rintro _ ⟨n, rfl⟩
    exact ⟨hmem n, hBbound n⟩
  have hanti : StrictAnti fun n : ℕ => |β 1 0| ^ (2 ^ n) :=
    (pow_right_strictAnti₀ hcpos hlt).comp_strictMono
      (fun m n h => Nat.pow_lt_pow_right (by norm_num) h)
  have hinj : Function.Injective seq := by
    intro m n hmn
    have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) ℝ => |g 1 0|) hmn
    simp only [hcabs] at h
    exact hanti.injective h
  exact Set.infinite_range_of_injective hinj ((gl10_finite_bounded hΓ Bd).subset hrange)

/-- **Lemma 1** (Shimizu, §10.3, l. 8101), second part. If moreover `A` is not a power of any element of `Γ`, no two
points of `D = {z : y ≥ 1, 0 ≤ x < 1}` are identified by an element of `Γ`. -/
theorem lemma10_1_b {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hA : A ∈ Γ) (hA1 : A 0 0 = 1 ∧ A 0 1 = 1 ∧ A 1 0 = 0 ∧ A 1 1 = 1)
    (hprim : ∀ γ ∈ Γ, ∀ k : ℕ, 2 ≤ k → γ ^ k ≠ A ∧ γ ^ k ≠ -A) :
    ∀ z w : ℂ, 1 ≤ z.im → 0 ≤ z.re → z.re < 1 → 1 ≤ w.im → 0 ≤ w.re → w.re < 1 →
      ∀ γ ∈ Γ, h36p_m γ z = w → z = w := by
  intro z w hz1 hz0 hz2 hw1 hw0 hw2 γ hγ hzw
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  -- two points of the strip differing by an integer translation coincide
  have hfin : ∀ n : ℤ, w = z + n → z = w := by
    intro n hn
    have hre : w.re = z.re + n := by rw [hn]; simp
    have h1 : (n : ℝ) < 1 := by linarith
    have h2 : (-1 : ℝ) < n := by linarith
    have h1' : n < 1 := by exact_mod_cast h1
    have h2' : -1 < n := by exact_mod_cast h2
    have hn0 : n = 0 := by omega
    rw [hn, hn0, Int.cast_zero, add_zero]
  by_cases hc : γ 1 0 = 0
  · -- `c = 0`: `γ A γ⁻¹ = (1, a²; 0, 1)` and `γ⁻¹ A γ = (1, d²; 0, 1)` give `a², d² ∈ ℤ`, so `a² = 1`
    have had : γ 0 0 * γ 1 1 = 1 := by rw [hc, mul_zero, sub_zero] at hdet; exact hdet
    obtain ⟨c00, c01, c10, c11⟩ := LiZhongQC.conj_translation_entries hA1 γ
    obtain ⟨d00, d01, d10, d11⟩ := LiZhongQC.conj_translation_entries hA1 γ⁻¹
    obtain ⟨i00, i01, i10, i11⟩ := gl10_inv_entries γ
    rw [hc, mul_zero, sub_zero] at c00
    rw [hc, mul_zero, add_zero] at c11
    rw [hc, sq, mul_zero, neg_zero] at c10
    rw [i10, hc, neg_zero, mul_zero, sub_zero] at d00
    rw [i10, hc, neg_zero, mul_zero, add_zero] at d11
    rw [i10, hc, neg_zero, sq, mul_zero, neg_zero] at d10
    rw [i00] at d01
    obtain ⟨p, hp⟩ := gl10_transl_int hΓ hA hA1 hprim (Γ.mul_mem (Γ.mul_mem hγ hA) (Γ.inv_mem hγ)) c10
      (by rw [c00, c11])
    obtain ⟨q, hq⟩ := gl10_transl_int hΓ hA hA1 hprim
      (Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) hA) (Γ.inv_mem (Γ.inv_mem hγ))) d10 (by rw [d00, d11])
    rw [c01, c00, mul_one] at hp
    rw [d01, d00, mul_one] at hq
    have hpq : (p : ℝ) * q = 1 := by rw [← hp, ← hq, ← mul_pow, had, one_pow]
    have hpq' : p * q = 1 := by exact_mod_cast hpq
    have hp0 : 0 ≤ (p : ℝ) := by rw [← hp]; positivity
    have hp1 : p = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hpq' with h | h
      · exact h
      · have : (p : ℝ) = -1 := by exact_mod_cast h
        linarith
    have ha2 : γ 0 0 ^ 2 = 1 := by rw [hp, hp1, Int.cast_one]
    have hda : γ 1 1 = γ 0 0 := by linear_combination (γ 0 0) * had - (γ 1 1) * ha2
    obtain ⟨r, hr⟩ := gl10_transl_int hΓ hA hA1 hprim hγ hc hda.symm
    refine hfin r ?_
    have ha0 : (γ 0 0 : ℂ) ≠ 0 := by
      intro h0
      have : γ 0 0 = 0 := by exact_mod_cast h0
      rw [this] at ha2
      norm_num at ha2
    have ha2C : (γ 0 0 : ℂ) ^ 2 = 1 := by exact_mod_cast ha2
    have hrC : ((r : ℤ) : ℂ) = (γ 0 1 : ℂ) * γ 0 0 := by exact_mod_cast hr.symm
    rw [← hzw, LiZhongQC.h36p_m, hc, hda, Complex.ofReal_zero, zero_mul, zero_add, div_eq_iff ha0, hrC]
    linear_combination (-(γ 0 1 : ℂ)) * ha2C
  · -- `c ≠ 0`: `|c| ≥ 1` (Shimizu) and `Im w = Im z/|cz + d|² ≤ 1`, with equality only for `Im z = 1`, `c² = 1`,
    -- `cx + d = 0`; then `Re w - Re z = c(a + d)`, and `a + d ∈ ℤ` (else `(γ Aʲ)²` has `0 < |c| < 1`).
    have hc1 := lemma10_1_a hΓ hA hA1 γ hγ hc
    have hc2 : 1 ≤ γ 1 0 ^ 2 := by rw [← sq_abs]; nlinarith
    have hy : 0 < z.im := by linarith
    set D : ℂ := (γ 1 0 : ℂ) * z + γ 1 1 with hDdef
    have hDre : D.re = γ 1 0 * z.re + γ 1 1 := by simp [hDdef]
    have hDim : D.im = γ 1 0 * z.im := by simp [hDdef]
    have hD : D ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      rw [hDim, Complex.zero_im] at this
      rcases mul_eq_zero.1 this with h | h
      · exact hc h
      · linarith
    have hmul : w * D = (γ 0 0 : ℂ) * z + γ 0 1 := by
      rw [← hzw, LiZhongQC.h36p_m, div_mul_cancel₀ _ hD]
    have hre := congrArg Complex.re hmul
    have him := congrArg Complex.im hmul
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero, hDre, hDim] at hre him
    -- `Im w · |D|² = Im z`
    have hwim : w.im * ((γ 1 0 * z.re + γ 1 1) ^ 2 + (γ 1 0 * z.im) ^ 2) = z.im := by
      linear_combination (-(γ 1 0 * z.im)) * hre + (γ 1 0 * z.re + γ 1 1) * him + z.im * hdet
    have hN : (γ 1 0 * z.im) ^ 2 ≥ z.im ^ 2 := by
      rw [mul_pow]
      nlinarith [sq_nonneg z.im]
    have hNle : (γ 1 0 * z.re + γ 1 1) ^ 2 + (γ 1 0 * z.im) ^ 2 ≤ z.im := by
      nlinarith [mul_nonneg (sub_nonneg.2 hw1) (add_nonneg (sq_nonneg (γ 1 0 * z.re + γ 1 1))
        (sq_nonneg (γ 1 0 * z.im)))]
    have hyle : z.im ≤ 1 := by nlinarith [sq_nonneg (γ 1 0 * z.re + γ 1 1)]
    have hy1 : z.im = 1 := le_antisymm hyle hz1
    rw [hy1] at hwim him hNle
    have hc2' : γ 1 0 ^ 2 = 1 := by
      nlinarith [sq_nonneg (γ 1 0 * z.re + γ 1 1)]
    have hx : γ 1 0 * z.re + γ 1 1 = 0 := by
      have : (γ 1 0 * z.re + γ 1 1) ^ 2 = 0 := by
        nlinarith [sq_nonneg (γ 1 0 * z.re + γ 1 1)]
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    have hwim1 : w.im = 1 := by
      rw [hx, mul_one, hc2'] at hwim
      linear_combination hwim
    -- `c` is an integer `±1`
    obtain ⟨ci, hci⟩ : ∃ ci : ℤ, (ci : ℝ) = γ 1 0 := by
      rcases mul_self_eq_one_iff.1 (by rw [← sq]; exact hc2' : γ 1 0 * γ 1 0 = 1) with h | h
      · exact ⟨1, by rw [h, Int.cast_one]⟩
      · exact ⟨-1, by rw [h, Int.cast_neg, Int.cast_one]⟩
    -- the trace is an integer
    have htr : ∃ n : ℤ, γ 0 0 + γ 1 1 = n := by
      by_contra hno
      push Not at hno
      set t := γ 0 0 + γ 1 1 with htdef
      have hfr0 : 0 < Int.fract t := by
        rw [Int.fract_pos]
        exact hno ⌊t⌋
      have hfr1 : Int.fract t < 1 := Int.fract_lt_one t
      obtain ⟨z00, z01, z10, z11⟩ := gl10_zpow_entries hA1 (-⌊t⌋ * ci)
      set E := γ * A ^ (-⌊t⌋ * ci) with hE
      have hEΓ : E ∈ Γ := Γ.mul_mem hγ (Γ.zpow_mem hA _)
      have hE10 : E 1 0 = γ 1 0 := by
        simp only [hE, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, z00, z10]
        ring
      have hE00 : E 0 0 = γ 0 0 := by
        simp only [hE, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, z00, z10]
        ring
      have hE11 : E 1 1 = γ 1 0 * ((-⌊t⌋ * ci : ℤ) : ℝ) + γ 1 1 := by
        simp only [hE, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, z01, z11]
        ring
      have hE2 : (E * E) 1 0 = γ 1 0 * Int.fract t := by
        simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hE10, hE00, hE11]
        unfold Int.fract
        push_cast
        rw [hci]
        linear_combination (-(γ 1 0 * (⌊t⌋ : ℝ))) * hc2' - (γ 1 0) * htdef
      have h2 := lemma10_1_a hΓ hA hA1 (E * E) (Γ.mul_mem hEΓ hEΓ) (by
        rw [hE2]; exact mul_ne_zero hc hfr0.ne')
      have habs : |γ 1 0| = 1 := by
        have h := sq_abs (γ 1 0)
        rw [hc2'] at h
        exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).1 h
      rw [hE2, abs_mul, habs, one_mul, abs_of_pos hfr0] at h2
      linarith
    obtain ⟨n, hn⟩ := htr
    refine hfin (ci * n) (Complex.ext ?_ ?_)
    · -- `c · Re w = a` and `c · Re z = -d`
      have hwre : γ 1 0 * w.re = γ 0 0 := by
        rw [hx] at him
        linear_combination him
      simp only [Complex.add_re, Complex.intCast_re]
      push_cast
      rw [hci]
      linear_combination (γ 1 0) * hwre - (γ 1 0) * hx - (w.re - z.re) * hc2' + (γ 1 0) * hn
    · simp only [Complex.add_im, Complex.intCast_im, add_zero]
      rw [hwim1, hy1]

end GardinerLakic2000
