import References.GardinerLakic2000.Ch02.S07_FuchsianGroups

/-!
# Gardiner–Lakic 2000, Ch. 2 §2.8 Types of elements of PSL(2,ℝ)

Source `teichmuller.txt`, lines 1795–1834 (Chapter 2, §2.8).

* Definition (hyperbolic, `(tr A)² > 4`, l. 1805) — exists: `LiZhongQC.IsHyperbolic` (the absolute trace exceeds 2)
* Definition (parabolic, `(tr A)² = 4`, `A ≠ id`, l. 1806) — exists: `LiZhongQC.IsParabolic`
* Definition (elliptic, `(tr A)² < 4`, l. 1807) — exists: `Katok1992.IsElliptic` (applied to the image in
  PSL(2,ℝ); the project has no SL(2,ℝ) version)
* Definition (the multiplier `λ > 1`, l. 1823; used in Ch. 10) — exists: `LiZhongQC.multiplier` (the square of the
  larger eigenvalue in absolute value, which is λ of the normal form λz)
* Unlabelled (normal forms: hyperbolic `λz`, parabolic `z + b`, elliptic a rotation `e^{iθ}` in the disc coordinate
  `(z − z₁)/(z − z̄₁)`; l. 1816–1833; used in Ch. 8, 10) — `para2_8_normal_form_hyp`, `para2_8_normal_form_par`,
  `para2_8_normal_form_ell`
* Unlabelled (`(λ^{1/2} + λ^{−1/2})² = tr(A)²`, the multiplier depends only on the conjugacy class, l. 1823) —
  `para2_8_multiplier_trace`

Modelling: elements are matrices of SL(2,ℝ) (leader ruling A0.2); the hyperbolic and parabolic normal forms are
reached by conjugation inside SL(2,ℝ) (the book allows swapping the fixed points to get `λ > 1`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (IsHyperbolic IsParabolic multiplier h36p_m)

/-- Auxiliary (§2.8, l. 1823). For a hyperbolic trace `|t| > 2`, the larger eigenvalue modulus
`λ = (|t| + √(t² − 4))/2` exceeds `1` and `λ + λ⁻¹ = |t|`. -/
theorem gl28_lam {t : ℝ} (ht : 2 < |t|) :
    1 < (|t| + Real.sqrt (t ^ 2 - 4)) / 2 ∧
      (|t| + Real.sqrt (t ^ 2 - 4)) / 2 + ((|t| + Real.sqrt (t ^ 2 - 4)) / 2)⁻¹ = |t| := by
  have h4 : 0 < t ^ 2 - 4 := by nlinarith [sq_abs t, abs_nonneg t]
  have hs0 : 0 ≤ Real.sqrt (t ^ 2 - 4) := Real.sqrt_nonneg _
  have hs : Real.sqrt (t ^ 2 - 4) ^ 2 = t ^ 2 - 4 := Real.sq_sqrt h4.le
  have hinv : ((|t| + Real.sqrt (t ^ 2 - 4)) / 2)⁻¹ = (|t| - Real.sqrt (t ^ 2 - 4)) / 2 := by
    refine (eq_inv_of_mul_eq_one_right ?_).symm
    linear_combination (-(1 / 4 : ℝ)) * hs + (1 / 4 : ℝ) * sq_abs t
  refine ⟨by linarith, ?_⟩
  rw [hinv]
  ring

/-- Auxiliary (§2.8). A matrix of `SL(2,ℝ)` whose conjugate is `diag(n, n⁻¹)` acts by the conjugate as
`z ↦ n² z`. -/
theorem gl28_diag_act {A B : Matrix.SpecialLinearGroup (Fin 2) ℝ} {n : ℝ}
    (hB : ((B * A * B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![n, 0; 0, n⁻¹])
    (z : ℂ) : h36p_m (B * A * B⁻¹) z = (n ^ 2 : ℝ) * z := by
  unfold h36p_m
  simp only [hB, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  simp only [zero_mul, zero_add, add_zero, div_eq_mul_inv, inv_inv]
  ring

/-- **Unlabelled** (§2.8, l. 1816–1823), hyperbolic normal form. A hyperbolic `A` is conjugate in SL(2,ℝ) to
`z ↦ λz`, `λ > 1` its multiplier. -/
theorem para2_8_normal_form_hyp {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hA : IsHyperbolic A) :
    1 < multiplier A ∧ ∃ B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ z : ℂ, 0 < z.im → h36p_m (B * A * B⁻¹) z = multiplier A * z := by
  have ht : 2 < |A 0 0 + A 1 1| := hA
  obtain ⟨hr1, hr2⟩ := gl28_lam ht
  set t := A 0 0 + A 1 1 with htdef
  set r := (|t| + Real.sqrt (t ^ 2 - 4)) / 2 with hrdef
  have hm : multiplier A = r ^ 2 := rfl
  refine ⟨by rw [hm]; nlinarith, ?_⟩
  -- the diagonal form `P A P⁻¹ = diag(l, l⁻¹)` (Katok, Ch. 2 §2.1)
  have hhyp : (A : Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic := by
    show 0 < (A : Matrix (Fin 2) (Fin 2) ℝ).discr
    rw [Katok1992.k92n_discr]
    nlinarith [sq_abs t, abs_nonneg t]
  obtain ⟨l, -, -, P, hP⟩ := (Katok1992.hyperbolic_conj_diag A).1 hhyp
  have hd := (P * A * P⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ).2
  rw [hP, Matrix.det_fin_two_of] at hd
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hd
  have htr : l + l⁻¹ = t := by
    have := Katok1992.k92_trace_conj P A
    rw [hP, Matrix.trace_fin_two_of, Matrix.trace_fin_two] at this
    exact this
  -- `l² = λ²` or `l⁻² = λ²`
  have hr0 : r ≠ 0 := by linarith
  clear_value r t
  have e1 : r ^ 4 + 1 = (t ^ 2 - 2) * r ^ 2 := by
    have e : r ^ 2 + 1 = |t| * r := by
      field_simp at hr2
      linear_combination hr2
    linear_combination (r ^ 2 + 1 + |t| * r) * e + r ^ 2 * sq_abs t
  have key : (l ^ 2 - r ^ 2) * (l⁻¹ ^ 2 - r ^ 2) = 0 := by
    have e2 : l ^ 2 + l⁻¹ ^ 2 = t ^ 2 - 2 := by
      rw [← htr]
      field_simp
      ring
    have e3 : l ^ 2 * l⁻¹ ^ 2 = 1 := by
      field_simp
    linear_combination e3 - r ^ 2 * e2 + e1
  rcases mul_eq_zero.1 key with h | h
  · refine ⟨P, fun z _ => ?_⟩
    rw [gl28_diag_act hP, hm, sub_eq_zero.1 h]
  · -- swap the eigenvalues with `S = [[0, −1], [1, 0]]`
    set S : Matrix.SpecialLinearGroup (Fin 2) ℝ := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩
    have hS : ((S * P * A * (S * P)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![l⁻¹, 0; 0, l⁻¹⁻¹] := by
      have e : S * P * A * (S * P)⁻¹ = S * (P * A * P⁻¹) * S⁻¹ := by group
      rw [e, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hP,
        Matrix.SpecialLinearGroup.coe_inv, inv_inv]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [S, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
    refine ⟨S * P, fun z _ => ?_⟩
    rw [gl28_diag_act hS, hm, sub_eq_zero.1 h]

/-- **Unlabelled** (§2.8, l. 1825), parabolic normal form. A parabolic `A` is conjugate to a translation `z ↦ z + b`
(`b ≠ 0`, real). -/
theorem para2_8_normal_form_par {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hA : IsParabolic A) :
    ∃ (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (b : ℝ), b ≠ 0 ∧
      ∀ z : ℂ, 0 < z.im → h36p_m (B * A * B⁻¹) z = z + b := by
  obtain ⟨ht, hA1, hA2⟩ := hA
  have ht' : |A 0 0 + A 1 1| = 2 := ht
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := A.2
    rwa [Matrix.det_fin_two] at this
  have ht4 : (A 0 0 + A 1 1) ^ 2 = 4 := by
    rw [← sq_abs, ht']
    norm_num
  set ε := (A 0 0 + A 1 1) / 2 with hεdef
  have hε : ε ^ 2 = 1 := by
    rw [hεdef]
    linear_combination ht4 / 4
  have hε0 : ε ≠ 0 := by
    rintro h0
    rw [h0] at hε
    norm_num at hε
  rcases eq_or_ne (A 1 0) 0 with hc | hc
  · -- `c = 0`: `a = d = ±1` and `b ≠ 0`, so `A` itself is `z ↦ z + b/a`
    have had : A 0 0 = A 1 1 := by
      have : (A 0 0 - A 1 1) ^ 2 = 0 := by
        rw [hc, mul_zero, sub_zero] at hdet
        linear_combination ht4 - 4 * hdet
      linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.1 this]
    have ha0 : A 0 0 ≠ 0 := by
      intro h0
      rw [h0, zero_mul, hc, mul_zero, sub_zero] at hdet
      exact zero_ne_one hdet
    have hb : A 0 1 ≠ 0 := by
      -- `b = 0` would make `A = ±1`
      intro hb
      have ha2 : (A 0 0 - 1) * (A 0 0 + 1) = 0 := by
        rw [hb, hc, ← had] at hdet
        linear_combination hdet
      rcases mul_eq_zero.1 ha2 with h1 | h1
      · apply hA1
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hb, hc, ← had] <;> linarith
      · apply hA2
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hb, hc, ← had] <;> linarith
    refine ⟨1, A 0 1 / A 0 0, div_ne_zero hb ha0, fun z _ => ?_⟩
    rw [one_mul, inv_one, mul_one]
    unfold h36p_m
    rw [hc, ← had]
    have : (A 0 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha0
    push_cast
    rw [zero_mul, zero_add, add_div, mul_div_cancel_left₀ _ this]
  · -- `c ≠ 0`: `B(z) = −1/(z − x)` moves the double fixed point `x = (a − d)/(2c)` to `∞`
    set x := (A 0 0 - A 1 1) / (2 * A 1 0) with hxdef
    have hx : 2 * A 1 0 * x = A 0 0 - A 1 1 := by
      rw [hxdef]
      field_simp
    clear_value x
    set B : Matrix.SpecialLinearGroup (Fin 2) ℝ := ⟨!![0, -1; 1, -x], by simp [Matrix.det_fin_two_of]⟩
    have hBA : ((B * A * B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![ε, -A 1 0; 0, ε] := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [B, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, Matrix.vecMul, dotProduct]
      · linear_combination (1 / 2 : ℝ) * hx - hεdef
      · -- the double root: `c x² + (d − a) x − b = −((a + d)² − 4)/(4c) = 0`
        apply mul_left_cancel₀ (mul_ne_zero (four_ne_zero (α := ℝ)) hc)
        linear_combination (2 * A 1 0 * x - (A 0 0 - A 1 1)) * hx - ht4 + 4 * hdet
      · linear_combination (-1 / 2 : ℝ) * hx - hεdef
    refine ⟨B, -(A 1 0 * ε), neg_ne_zero.2 (mul_ne_zero hc hε0), fun z _ => ?_⟩
    unfold h36p_m
    simp only [hBA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    have : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hε0
    have hεC : (ε : ℂ) ^ 2 = 1 := by exact_mod_cast hε
    push_cast
    rw [zero_mul, zero_add, div_eq_iff this]
    linear_combination (A 1 0 : ℂ) * hεC

/-- Auxiliary (§2.8). The denominator `cw + d` of `A ∈ SL(2,ℝ)` does not vanish off the real axis. -/
theorem gl28_den_ne (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    (A 1 0 : ℂ) * w + A 1 1 ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.zero_im, Complex.add_re, Complex.mul_re, Complex.zero_re, sub_zero] at him hre
  have hc : A 1 0 = 0 := (mul_eq_zero.1 him).resolve_right hw
  rw [hc, zero_mul, zero_add] at hre
  have hd := A.2
  rw [Matrix.det_fin_two, hc, hre] at hd
  simp at hd

/-- Auxiliary (§2.8). `Az − Aw = (z − w)/((cz + d)(cw + d))` for `A ∈ SL(2,ℝ)`. -/
theorem gl28_m_sub (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z w : ℂ}
    (hz : (A 1 0 : ℂ) * z + A 1 1 ≠ 0) (hw : (A 1 0 : ℂ) * w + A 1 1 ≠ 0) :
    h36p_m A z - h36p_m A w = (z - w) / (((A 1 0 : ℂ) * z + A 1 1) * ((A 1 0 : ℂ) * w + A 1 1)) := by
  have hdet : ((A 0 0 : ℂ) * A 1 1 - A 0 1 * A 1 0) = 1 := by
    have := A.2
    rw [Matrix.det_fin_two] at this
    exact_mod_cast this
  unfold h36p_m
  rw [div_sub_div _ _ hz hw]
  congr 1
  linear_combination (z - w) * hdet

/-- Auxiliary (§2.8). `A` has real coefficients: `A(w̄) = conj (A w)`. -/
theorem gl28_m_conj (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : ℂ) :
    h36p_m A (conj w) = conj (h36p_m A w) := by
  unfold h36p_m
  simp [map_div₀]

/-- Auxiliary (§2.8). `(p/(D D₁)) / (q/(D D₂)) = (D₂/D₁)(p/q)` for nonzero `D, D₁, D₂, q`. -/
theorem gl28_ratio (p q D D₁ D₂ : ℂ) (hD : D ≠ 0) (h₁ : D₁ ≠ 0) (h₂ : D₂ ≠ 0) (hq : q ≠ 0) :
    p / (D * D₁) / (q / (D * D₂)) = D₂ / D₁ * (p / q) := by
  field_simp

/-- **Unlabelled** (§2.8, l. 1827–1833), elliptic normal form. An elliptic `A ≠ ±1` has a fixed point `z₁ ∈ ℍ`, and in
the coordinate `(z − z₁)/(z − z̄₁)` it is a rotation `e^{iθ}`. -/
theorem para2_8_normal_form_ell {A : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hA : Katok1992.IsElliptic (QuotientGroup.mk A)) (hA1 : A ≠ 1) (hA2 : A ≠ -1) :
    ∃ (z₁ : ℂ) (θ : ℝ), 0 < z₁.im ∧ h36p_m A z₁ = z₁ ∧ ∀ z : ℂ, 0 < z.im →
      (h36p_m A z - z₁) / (h36p_m A z - conj z₁) = exp (θ * I) * ((z - z₁) / (z - conj z₁)) := by
  -- `A ≠ ±1` is implied by `Tr < 2` and is not needed
  have _ := hA1
  have _ := hA2
  have ht : |A 0 0 + A 1 1| < 2 := by
    have h := hA
    unfold Katok1992.IsElliptic at h
    rwa [Katok1992.k92_Tr_mk, Matrix.trace_fin_two] at h
  obtain ⟨τ, hτ⟩ := LiZhongQC.s27g_elliptic_fixed ht
  set z₁ : ℂ := (τ : ℂ) with hz₁
  have him : 0 < z₁.im := τ.im_pos
  have hfix : h36p_m A z₁ = z₁ := by rw [hz₁, LiZhongQC.h36p_m_coe, hτ]
  have hfixc : h36p_m A (conj z₁) = conj z₁ := by rw [gl28_m_conj, hfix]
  have hd1 := gl28_den_ne A (w := z₁) him.ne'
  have hd2 := gl28_den_ne A (w := conj z₁) (by rw [Complex.conj_im]; exact neg_ne_zero.2 him.ne')
  -- the rotation factor `k = (c z̄₁ + d)/(c z₁ + d)`, of modulus `1`
  set k := ((A 1 0 : ℂ) * conj z₁ + A 1 1) / ((A 1 0 : ℂ) * z₁ + A 1 1) with hkdef
  have hconj : (A 1 0 : ℂ) * conj z₁ + A 1 1 = conj ((A 1 0 : ℂ) * z₁ + A 1 1) := by simp
  have hk : ‖k‖ = 1 := by
    rw [hkdef, norm_div, hconj, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hd1)]
  have hexp : exp (Complex.arg k * I) = k := by
    have := Complex.norm_mul_exp_arg_mul_I k
    rwa [hk, Complex.ofReal_one, one_mul] at this
  refine ⟨z₁, Complex.arg k, him, hfix, fun z hz => ?_⟩
  rw [hexp]
  have hdz := gl28_den_ne A (w := z) hz.ne'
  have hzc : z - conj z₁ ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  -- `Az − z₁ = Az − Az₁` and `Az − z̄₁ = Az − Az̄₁`
  have e1 := gl28_m_sub A hdz hd1
  have e2 := gl28_m_sub A hdz hd2
  rw [hfix] at e1
  rw [hfixc] at e2
  rw [e1, e2, hkdef]
  exact gl28_ratio _ _ _ _ _ hdz hd1 hd2 hzc

/-- **Unlabelled** (§2.8, l. 1823). For hyperbolic `A` with multiplier `λ`, `(λ^{1/2} + λ^{−1/2})² = tr(A)²`; hence
`λ` depends only on the conjugacy class of `A`. -/
theorem para2_8_multiplier_trace {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hA : IsHyperbolic A) :
    (Real.sqrt (multiplier A) + (Real.sqrt (multiplier A))⁻¹) ^ 2 = (A 0 0 + A 1 1) ^ 2 ∧
      ∀ B : Matrix.SpecialLinearGroup (Fin 2) ℝ, multiplier (B * A * B⁻¹) = multiplier A := by
  have ht : 2 < |A 0 0 + A 1 1| := hA
  obtain ⟨hr1, hr2⟩ := gl28_lam ht
  refine ⟨?_, fun B => ?_⟩
  · have hm : Real.sqrt (multiplier A) = (|A 0 0 + A 1 1| + Real.sqrt ((A 0 0 + A 1 1) ^ 2 - 4)) / 2 :=
      Real.sqrt_sq (by linarith)
    rw [hm, hr2, sq_abs]
  · -- `multiplier` depends only on the trace, which is a conjugation invariant
    have h := LiZhongQC.slTrace_conj B A
    unfold LiZhongQC.slTrace at h
    unfold multiplier
    rw [h]

end GardinerLakic2000
