import LiZhongQC.Ch04.S18_BoundedTurning

/-!
# Quasicircles of Hausdorff dimension close to `2` (the remark of §16.1)

`quasicircle_hausdorff_dim_near_two` (§16.1, book p. 108): for every `ε > 0` some quasicircle has Hausdorff
dimension greater than `2 - ε`.  The statement is moved here unchanged from `Ch04/S16_Quasicircles.lean` (user
decision, 2026-09-27) because the proof uses Ahlfors' criterion `thm18_1_quasicircle_of_boundedTurning`
(`Ch04/S18_BoundedTurning.lean`), which §16 cannot import.

The quasicircle is a generalized Koch curve.  For `c = cos θ ∈ (0, 1/2]` the four similarities `φᵢ` of ratio
`r = 1/(2 + 2c)` map `[0, 1]` onto the sides of the polygon `0, r, r + r e^{iθ}, 1 - r, 1`, and the arc `γ` is the
fixed point of the Read operator `f ↦ φᵢ ∘ f (4 · - i)`.  The pieces `φᵢ T` of the triangle
`T = conv {0, 1, (1 + i)/2}` stay in `T` and meet only at common vertices, at angles proportional to `c`; this makes
`γ` of bounded turning, with the co-Hölder exponent `d = log 4 / log (2 + 2c)`.  Closing `γ` by the tent
`t ↦ t - i min(t, 1 - t)` gives a Jordan curve of bounded turning, hence a quasicircle, of Hausdorff dimension at
least `d`, and `d > 2 - ε` for `c = min(ε, 1) log 2 / 2`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-! ### The generalized Koch arc (`koch_`) -/

/-- `s = √(1 - c²)`, i.e. `sin θ` for `cos θ = c`. -/
def koch_s (c : ℝ) : ℝ := Real.sqrt (1 - c ^ 2)

/-- The similarity ratio `r = 1/(2 + 2c)` of the generalized Koch arc (`c = cos θ`). -/
def koch_r (c : ℝ) : ℝ := 1 / (2 + 2 * c)

/-- The similarity dimension `d = log 4 / log (2 + 2c)` of the arc: `r ^ d = 1/4`. -/
def koch_d (c : ℝ) : ℝ := Real.log 4 / Real.log (2 + 2 * c)

/-- The translation parts of the four similarities: `0`, `r`, the apex `1/2 + i r s`, and `1 - r`. -/
def koch_A (c : ℝ) : Fin 4 → ℂ :=
  ![0, (koch_r c : ℂ), 1 / 2 + ((koch_r c * koch_s c : ℝ) : ℂ) * I, 1 - (koch_r c : ℂ)]

/-- The linear parts of the four similarities: `r`, `r e^{iθ}`, `r e^{-iθ}` and `r`. -/
def koch_B (c : ℝ) : Fin 4 → ℂ :=
  ![(koch_r c : ℂ), (koch_r c : ℂ) * ((c : ℂ) + (koch_s c : ℂ) * I),
    (koch_r c : ℂ) * ((c : ℂ) - (koch_s c : ℂ) * I), (koch_r c : ℂ)]

/-- The similarity `φᵢ z = Aᵢ + Bᵢ z` onto the `i`-th segment of the generator `0, r, r + r e^{iθ}, 1 - r, 1`. -/
def koch_φ (c : ℝ) (i : Fin 4) (z : ℂ) : ℂ := koch_A c i + koch_B c i * z

/-- The closed triangle `T = conv {0, 1, (1 + i)/2}`. -/
def koch_T : Set ℂ := {z | 0 ≤ z.im ∧ z.im ≤ z.re ∧ z.im ≤ 1 - z.re}

/-- `γ` is a generalized Koch arc for `c`: continuous on `[0, 1]`, from `0` to `1`, self-similar
(`γ ((i + t)/4) = φᵢ (γ t)`), and inside the triangle `T`. -/
def koch_IsArc (c : ℝ) (γ : ℝ → ℂ) : Prop :=
  ContinuousOn γ (Icc 0 1) ∧ γ 0 = 0 ∧ γ 1 = 1 ∧
    (∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, γ (((i : ℕ) + t) / 4) = koch_φ c i (γ t)) ∧
    ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ koch_T

/-- K1. The ratio for `0 < c ≤ 1/2`: `1/3 ≤ r < 1/2` and `r (1 + c) = 1/2`.
Truth: `r = 1/(2 + 2c)` with `2 < 2 + 2c ≤ 3`. -/
theorem koch_r_facts {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) :
    1 / 3 ≤ koch_r c ∧ koch_r c < 1 / 2 ∧ koch_r c * (1 + c) = 1 / 2 := by
  have h2 : 0 < 2 + 2 * c := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [koch_r]
    exact one_div_le_one_div_of_le h2 (by linarith)
  · rw [koch_r]
    exact one_div_lt_one_div_of_lt (by norm_num) (by linarith)
  · rw [koch_r, div_mul_eq_mul_div, one_mul, div_eq_div_iff h2.ne' two_ne_zero]
    ring

/-- K1. `s = √(1 - c²)` for `0 < c ≤ 1/2`: `c < s ≤ 1` and `s² = 1 - c²`.
Truth: `1 - c² ≥ 3/4 > c²` and `Real.sq_sqrt`. -/
theorem koch_s_facts {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) :
    c < koch_s c ∧ koch_s c ≤ 1 ∧ koch_s c ^ 2 = 1 - c ^ 2 := by
  have h1 : 0 ≤ 1 - c ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [koch_s, Real.lt_sqrt hc0.le]
    nlinarith
  · rw [koch_s, Real.sqrt_le_one]
    nlinarith
  · rw [koch_s, Real.sq_sqrt h1]

/-- K1. The dimension exceeds `1`: `1 < d` for `0 < c ≤ 1/2`.
Truth: `0 < log (2 + 2c) ≤ log 3 < log 4`. -/
theorem koch_d_gt_one {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) : 1 < koch_d c := by
  have hl : 0 < Real.log (2 + 2 * c) := Real.log_pos (by linarith)
  rw [koch_d, one_lt_div hl]
  exact Real.log_lt_log (by linarith) (by linarith)

/-- K1. Every `φᵢ` is a similarity of ratio `r`: `‖φᵢ z - φᵢ w‖ = r ‖z - w‖`.
Truth: `‖Bᵢ‖ = r`, since `|c ± i s| = 1`. -/
theorem koch_φ_dist {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) (i : Fin 4) (z w : ℂ) :
    ‖koch_φ c i z - koch_φ c i w‖ = koch_r c * ‖z - w‖ := by
  obtain ⟨hr3, -, -⟩ := koch_r_facts hc0 hc1
  obtain ⟨-, -, hs2⟩ := koch_s_facts hc0 hc1
  have hr0 : 0 ≤ koch_r c := by linarith
  have hu1 : ‖(c : ℂ) + (koch_s c : ℂ) * I‖ = 1 := by
    rw [Complex.norm_add_mul_I, show c ^ 2 + koch_s c ^ 2 = 1 by linarith, Real.sqrt_one]
  have hu2 : ‖(c : ℂ) - (koch_s c : ℂ) * I‖ = 1 := by
    rw [show (c : ℂ) - (koch_s c : ℂ) * I = (c : ℂ) + ((-koch_s c : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_add_mul_I, show c ^ 2 + (-koch_s c) ^ 2 = 1 by rw [neg_sq]; linarith, Real.sqrt_one]
  have hB : ‖koch_B c i‖ = koch_r c := by
    fin_cases i <;> simp [koch_B, abs_of_nonneg hr0, hu1, hu2]
  rw [koch_φ, koch_φ, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, hB]

/-- K1. The generator is a polygon from `0` to `1`: `φ₀ 0 = 0`, `φ₃ 1 = 1` and `φᵢ 1 = φᵢ₊₁ 0`.
Truth: `r + r (c + i s) = 1/2 + i r s` and `1/2 + i r s + r (c - i s) = 1 - r`, by `r (1 + c) = 1/2`. -/
theorem koch_φ_ends {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) :
    koch_φ c 0 0 = 0 ∧ koch_φ c 3 1 = 1 ∧ ∀ i : Fin 3, koch_φ c i.castSucc 1 = koch_φ c i.succ 0 := by
  obtain ⟨-, -, hr⟩ := koch_r_facts hc0 hc1
  have hr' : koch_r c + koch_r c * c = 1 / 2 := by rw [← hr]; ring
  refine ⟨by simp [koch_φ, koch_A, koch_B], by simp [koch_φ, koch_A, koch_B], fun i => ?_⟩
  fin_cases i
  · simp [koch_φ, koch_A, koch_B]
  · apply Complex.ext
    · simp [koch_φ, koch_A, koch_B]
      linarith
    · simp [koch_φ, koch_A, koch_B]
  · apply Complex.ext
    · simp [koch_φ, koch_A, koch_B]
      linarith
    · simp [koch_φ, koch_A, koch_B]

/-- The coordinates of `φᵢ z` in terms of `x = Re z` and `y = Im z`. -/
theorem koch_φ_re_im (c : ℝ) (z : ℂ) :
    (koch_φ c 0 z).re = koch_r c * z.re ∧ (koch_φ c 0 z).im = koch_r c * z.im ∧
      (koch_φ c 1 z).re = koch_r c + koch_r c * (c * z.re - koch_s c * z.im) ∧
      (koch_φ c 1 z).im = koch_r c * (koch_s c * z.re + c * z.im) ∧
      (koch_φ c 2 z).re = 1 / 2 + koch_r c * (c * z.re + koch_s c * z.im) ∧
      (koch_φ c 2 z).im = koch_r c * koch_s c + koch_r c * (c * z.im - koch_s c * z.re) ∧
      (koch_φ c 3 z).re = 1 - koch_r c + koch_r c * z.re ∧ (koch_φ c 3 z).im = koch_r c * z.im := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [koch_φ, koch_A, koch_B] <;> ring

/-- K1. Every `φᵢ` maps the triangle `T` into itself.
Truth: each defining inequality of `T` at `φᵢ z` is a nonnegative combination of those at `z` (coefficients in
`c`, `s`, `r`). -/
theorem koch_mapsTo_T {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) (i : Fin 4) :
    MapsTo (koch_φ c i) koch_T koch_T := by
  obtain ⟨hr3, hr2, hr⟩ := koch_r_facts hc0 hc1
  obtain ⟨hcs, hs1, -⟩ := koch_s_facts hc0 hc1
  intro z hz
  obtain ⟨hy0, hyx, hyx1⟩ := hz
  obtain ⟨e0r, e0i, e1r, e1i, e2r, e2i, e3r, e3i⟩ := koch_φ_re_im c z
  have hr0 : 0 ≤ koch_r c := by linarith
  have hr' : koch_r c + koch_r c * c = 1 / 2 := by rw [← hr]; ring
  have hs0 : 0 ≤ koch_s c := by linarith
  have hx0 : 0 ≤ z.re := by linarith
  have hx1 : 0 ≤ 1 - z.re := by linarith
  have hxy : 0 ≤ z.re - z.im := by linarith
  have hxy1 : 0 ≤ 1 - z.re - z.im := by linarith
  fin_cases i
  · show 0 ≤ (koch_φ c 0 z).im ∧ (koch_φ c 0 z).im ≤ (koch_φ c 0 z).re ∧
      (koch_φ c 0 z).im ≤ 1 - (koch_φ c 0 z).re
    rw [e0r, e0i]
    exact ⟨mul_nonneg hr0 hy0, mul_le_mul_of_nonneg_left hyx hr0, by linarith [mul_nonneg hr0 hxy1]⟩
  · show 0 ≤ (koch_φ c 1 z).im ∧ (koch_φ c 1 z).im ≤ (koch_φ c 1 z).re ∧
      (koch_φ c 1 z).im ≤ 1 - (koch_φ c 1 z).re
    rw [e1r, e1i]
    refine ⟨mul_nonneg hr0 (add_nonneg (mul_nonneg hs0 hx0) (mul_nonneg hc0.le hy0)), ?_, ?_⟩
    · linarith [mul_nonneg hr0 hxy1, mul_nonneg hr0 (mul_nonneg (sub_nonneg.2 hs1) hxy),
        mul_nonneg hr0 (mul_nonneg hc0.le hxy), mul_nonneg hr0 (mul_nonneg (sub_nonneg.2 hs1) hy0)]
    · linarith [mul_nonneg hr0 (mul_nonneg hs0 hy0), mul_nonneg hr0 (mul_nonneg (add_nonneg hc0.le hs0) hxy1),
        mul_nonneg hr0 (show 0 ≤ 1 + c - koch_s c by linarith)]
  · show 0 ≤ (koch_φ c 2 z).im ∧ (koch_φ c 2 z).im ≤ (koch_φ c 2 z).re ∧
      (koch_φ c 2 z).im ≤ 1 - (koch_φ c 2 z).re
    rw [e2r, e2i]
    refine ⟨?_, ?_, ?_⟩
    · linarith [mul_nonneg hr0 (mul_nonneg hs0 hx1), mul_nonneg hr0 (mul_nonneg hc0.le hy0)]
    · linarith [mul_nonneg hr0 (show 0 ≤ 1 + c - koch_s c by linarith),
        mul_nonneg hr0 (mul_nonneg (add_nonneg hc0.le hs0) hx0),
        mul_nonneg hr0 (mul_nonneg (show 0 ≤ koch_s c - c by linarith) hy0)]
    · linarith [mul_nonneg hr0 (mul_nonneg hs0 hxy), mul_nonneg hr0 (mul_nonneg hc0.le hxy1),
        mul_nonneg hr0 (show 0 ≤ 1 - koch_s c by linarith)]
  · show 0 ≤ (koch_φ c 3 z).im ∧ (koch_φ c 3 z).im ≤ (koch_φ c 3 z).re ∧
      (koch_φ c 3 z).im ≤ 1 - (koch_φ c 3 z).re
    rw [e3r, e3i]
    exact ⟨mul_nonneg hr0 hy0, by linarith [mul_nonneg hr0 hxy], by linarith [mul_nonneg hr0 hxy1]⟩

/-- Every `φᵢ` is continuous. -/
theorem koch_φ_continuous (c : ℝ) (i : Fin 4) : Continuous (koch_φ c i) := by
  unfold koch_φ
  fun_prop

/-- The triangle `T` is closed. -/
theorem koch_T_isClosed : IsClosed koch_T :=
  (isClosed_le continuous_const continuous_im).inter
    ((isClosed_le continuous_im continuous_re).inter (isClosed_le continuous_im (continuous_const.sub continuous_re)))

/-- Points of the triangle `T` have norm at most `1`. -/
theorem koch_T_norm_le {z : ℂ} (hz : z ∈ koch_T) : ‖z‖ ≤ 1 := by
  obtain ⟨h0, h1, h2⟩ := hz
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ = z.re + z.im := by rw [abs_of_nonneg (by linarith), abs_of_nonneg h0]
    _ ≤ 1 := by linarith

/-- The Read operator `f ↦ φᵢ ∘ f (4 · - i)` on the `i`-th quarter of `[0, 1]`. -/
def koch_read (c : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  if t ≤ 1 / 4 then koch_φ c 0 (f (4 * t)) else if t ≤ 1 / 2 then koch_φ c 1 (f (4 * t - 1))
    else if t ≤ 3 / 4 then koch_φ c 2 (f (4 * t - 2)) else koch_φ c 3 (f (4 * t - 3))

/-- The Read operator on the `i`-th quarter: `R f ((i + t)/4) = φᵢ (f t)` when `f 0 = 0` and `f 1 = 1`. -/
theorem koch_read_quarter {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) {f : ℝ → ℂ} (hf0 : f 0 = 0)
    (hf1 : f 1 = 1) (i : Fin 4) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    koch_read c f (((i : ℕ) + t) / 4) = koch_φ c i (f t) := by
  obtain ⟨-, -, hj⟩ := koch_φ_ends hc0 hc1
  obtain ⟨ht0, ht1⟩ := ht
  have j0 : koch_φ c 0 (f 1) = koch_φ c 1 (f 0) := by rw [hf0, hf1]; exact hj 0
  have j1 : koch_φ c 1 (f 1) = koch_φ c 2 (f 0) := by rw [hf0, hf1]; exact hj 1
  have j2 : koch_φ c 2 (f 1) = koch_φ c 3 (f 0) := by rw [hf0, hf1]; exact hj 2
  fin_cases i
  · show koch_read c f (((0 : ℕ) + t) / 4) = koch_φ c 0 (f t)
    simp only [koch_read]
    push_cast
    split_ifs <;> first | (exfalso; linarith) | (congr 2; ring)
  · show koch_read c f (((1 : ℕ) + t) / 4) = koch_φ c 1 (f t)
    simp only [koch_read]
    push_cast
    split_ifs
    · obtain rfl : t = 0 := by linarith
      rw [show (4 : ℝ) * ((1 + 0) / 4) = 1 by norm_num]
      exact j0
    · congr 2; ring
    all_goals exfalso; linarith
  · show koch_read c f (((2 : ℕ) + t) / 4) = koch_φ c 2 (f t)
    simp only [koch_read]
    push_cast
    split_ifs
    · exfalso; linarith
    · obtain rfl : t = 0 := by linarith
      rw [show (4 : ℝ) * ((2 + 0) / 4) - 1 = 1 by norm_num]
      exact j1
    · congr 2; ring
    · exfalso; linarith
  · show koch_read c f (((3 : ℕ) + t) / 4) = koch_φ c 3 (f t)
    simp only [koch_read]
    push_cast
    split_ifs
    · exfalso; linarith
    · exfalso; linarith
    · obtain rfl : t = 0 := by linarith
      rw [show (4 : ℝ) * ((3 + 0) / 4) - 2 = 1 by norm_num]
      exact j2
    · congr 2; ring

/-- The Read operator preserves continuity on `[0, 1]` when `f 0 = 0` and `f 1 = 1` (the junctions match). -/
theorem koch_read_continuousOn {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc 0 1)) (hf0 : f 0 = 0) (hf1 : f 1 = 1) :
    ContinuousOn (koch_read c f) (Icc 0 1) := by
  have hq : ∀ (i : Fin 4) (a b : ℝ), a = (i : ℕ) / 4 → b = ((i : ℕ) + 1) / 4 →
      ContinuousOn (koch_read c f) (Icc a b) := by
    intro i a b ha hb
    subst ha hb
    have hmaps : MapsTo (fun t : ℝ => 4 * t - (i : ℕ)) (Icc ((i : ℕ) / 4 : ℝ) (((i : ℕ) + 1) / 4)) (Icc 0 1) :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hcont : ContinuousOn (fun t : ℝ => koch_φ c i (f (4 * t - (i : ℕ))))
        (Icc ((i : ℕ) / 4 : ℝ) (((i : ℕ) + 1) / 4)) :=
      (koch_φ_continuous c i).comp_continuousOn (f := fun t : ℝ => f (4 * t - (i : ℕ)))
        (hf.comp (f := fun t : ℝ => 4 * t - (i : ℕ)) (by fun_prop) hmaps)
    refine hcont.congr fun t ht => ?_
    have h := koch_read_quarter hc0 hc1 hf0 hf1 i (t := 4 * t - (i : ℕ)) (hmaps ht)
    rwa [show ((i : ℕ) + (4 * t - (i : ℕ))) / 4 = t by ring] at h
  have e : Icc (0 : ℝ) 1 = (Icc 0 (1 / 4) ∪ Icc (1 / 4) (1 / 2)) ∪ (Icc (1 / 2) (3 / 4) ∪ Icc (3 / 4) 1) := by
    rw [Icc_union_Icc_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2),
      Icc_union_Icc_eq_Icc (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) ≤ 1),
      Icc_union_Icc_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  rw [e]
  exact ((hq 0 _ _ (by norm_num) (by norm_num)).union_of_isClosed (hq 1 _ _ (by norm_num) (by norm_num))
    isClosed_Icc isClosed_Icc).union_of_isClosed
    ((hq 2 _ _ (by norm_num) (by norm_num)).union_of_isClosed (hq 3 _ _ (by norm_num) (by norm_num))
      isClosed_Icc isClosed_Icc) (isClosed_Icc.union isClosed_Icc) (isClosed_Icc.union isClosed_Icc)

/-- The Read operator is a contraction of ratio `r` for the sup distance on `[0, 1]`. -/
theorem koch_read_dist {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) {f g : ℝ → ℂ} {M : ℝ}
    (hM : ∀ s ∈ Icc (0 : ℝ) 1, ‖f s - g s‖ ≤ M) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖koch_read c f t - koch_read c g t‖ ≤ koch_r c * M := by
  obtain ⟨hr3, -, -⟩ := koch_r_facts hc0 hc1
  have hr0 : 0 ≤ koch_r c := by linarith
  obtain ⟨ht0, ht1⟩ := ht
  simp only [koch_read]
  split_ifs <;>
    (rw [koch_φ_dist hc0 hc1]; exact mul_le_mul_of_nonneg_left (hM _ ⟨by linarith, by linarith⟩) hr0)

/-- The Read operator keeps maps of `[0, 1]` into `T` inside `T`. -/
theorem koch_read_mapsTo {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) {f : ℝ → ℂ}
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, f s ∈ koch_T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : koch_read c f t ∈ koch_T := by
  obtain ⟨ht0, ht1⟩ := ht
  simp only [koch_read]
  split_ifs <;> exact koch_mapsTo_T hc0 hc1 _ (hf _ ⟨by linarith, by linarith⟩)

/-- The Read operator keeps the endpoints: `R f 0 = 0` and `R f 1 = 1` when `f 0 = 0` and `f 1 = 1`. -/
theorem koch_read_ends {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) {f : ℝ → ℂ} (hf0 : f 0 = 0) (hf1 : f 1 = 1) :
    koch_read c f 0 = 0 ∧ koch_read c f 1 = 1 := by
  obtain ⟨h0, h3, -⟩ := koch_φ_ends hc0 hc1
  refine ⟨?_, ?_⟩
  · simp only [koch_read]
    norm_num [hf0, h0]
  · simp only [koch_read]
    norm_num [hf1, h3]

/-- K1. The generalized Koch arc exists.
Truth: the fixed point of the Read operator `f ↦ φᵢ ∘ f (4 · - i)` on `{f ∈ C([0, 1], ℂ) | f 0 = 0, f 1 = 1}`, a
contraction of ratio `r` (continuous at `i/4` by `φᵢ 1 = φᵢ₊₁ 0`); the maps into `T` form a closed invariant set. -/
theorem koch_exists_arc {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) : ∃ γ : ℝ → ℂ, koch_IsArc c γ := by
  obtain ⟨hr3, hr2, -⟩ := koch_r_facts hc0 hc1
  have hr0 : 0 ≤ koch_r c := by linarith
  have hr1 : koch_r c < 1 := by linarith
  obtain ⟨F, hF0, hFs⟩ : ∃ F : ℕ → ℝ → ℂ, F 0 = (fun t : ℝ => (t : ℂ)) ∧ ∀ n, F (n + 1) = koch_read c (F n) :=
    ⟨fun n => (koch_read c)^[n] (fun t : ℝ => (t : ℂ)), rfl, fun n => Function.iterate_succ_apply' _ _ _⟩
  have hinv : ∀ n, ContinuousOn (F n) (Icc 0 1) ∧ F n 0 = 0 ∧ F n 1 = 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, F n t ∈ koch_T := by
    intro n
    induction n with
    | zero =>
      rw [hF0]
      refine ⟨Complex.continuous_ofReal.continuousOn, by simp, by simp, fun t ht => ?_⟩
      show 0 ≤ (t : ℂ).im ∧ (t : ℂ).im ≤ (t : ℂ).re ∧ (t : ℂ).im ≤ 1 - (t : ℂ).re
      simp only [Complex.ofReal_im, Complex.ofReal_re]
      exact ⟨le_rfl, ht.1, by linarith [ht.2]⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      rw [hFs]
      obtain ⟨e0, e1⟩ := koch_read_ends hc0 hc1 h2 h3
      exact ⟨koch_read_continuousOn hc0 hc1 h1 h2 h3, e0, e1, fun t ht => koch_read_mapsTo hc0 hc1 h4 ht⟩
  have hgeo : ∀ n, ∀ t ∈ Icc (0 : ℝ) 1, ‖F (n + 1) t - F n t‖ ≤ 2 * koch_r c ^ n := by
    intro n
    induction n with
    | zero =>
      intro t ht
      calc ‖F (0 + 1) t - F 0 t‖ ≤ ‖F (0 + 1) t‖ + ‖F 0 t‖ := norm_sub_le _ _
        _ ≤ 1 + 1 :=
          add_le_add (koch_T_norm_le ((hinv _).2.2.2 t ht)) (koch_T_norm_le ((hinv 0).2.2.2 t ht))
        _ = 2 * koch_r c ^ 0 := by norm_num
    | succ n ih =>
      intro t ht
      rw [hFs (n + 1), hFs n]
      calc ‖koch_read c (koch_read c (F n)) t - koch_read c (F n) t‖ ≤ koch_r c * (2 * koch_r c ^ n) := by
            refine koch_read_dist hc0 hc1 (fun s hs => ?_) ht
            rw [← hFs n]
            exact ih s hs
        _ = 2 * koch_r c ^ (n + 1) := by ring
  have hcau : ∀ t ∈ Icc (0 : ℝ) 1, ∀ n, dist (F n t) (F (n + 1) t) ≤ 2 * koch_r c ^ n := fun t ht n => by
    rw [dist_eq_norm, norm_sub_rev]
    exact hgeo n t ht
  have hlim : ∀ t ∈ Icc (0 : ℝ) 1, ∃ z, Tendsto (fun n => F n t) atTop (𝓝 z) := fun t ht =>
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric (koch_r c) 2 hr1 (hcau t ht))
  choose! γ hγ using hlim
  have hbd : ∀ n, ∀ t ∈ Icc (0 : ℝ) 1, dist (F n t) (γ t) ≤ 2 * koch_r c ^ n / (1 - koch_r c) :=
    fun n t ht => dist_le_of_le_geometric_of_tendsto (koch_r c) 2 hr1 (hcau t ht) (hγ t ht) n
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  refine ⟨γ, ?_, ?_, ?_, ?_, ?_⟩
  · refine TendstoUniformlyOn.continuousOn (F := F) (p := atTop) (Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_)
      (Filter.Frequently.of_forall fun n => (hinv n).1)
    have h2 : 0 < 1 - koch_r c := by linarith
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos (mul_pos hε h2) two_pos) hr1
    refine Filter.eventually_atTop.2 ⟨N, fun n hn t ht => ?_⟩
    rw [dist_comm]
    have h1 : koch_r c ^ n ≤ koch_r c ^ N := pow_le_pow_of_le_one hr0 hr1.le hn
    calc dist (F n t) (γ t) ≤ 2 * koch_r c ^ n / (1 - koch_r c) := hbd n t ht
      _ ≤ 2 * koch_r c ^ N / (1 - koch_r c) := (div_le_div_iff_of_pos_right h2).2 (by linarith)
      _ < ε := by
        rw [div_lt_iff₀ h2]
        linarith
  · exact tendsto_nhds_unique (hγ 0 h01) (tendsto_const_nhds.congr fun n => ((hinv n).2.1).symm)
  · exact tendsto_nhds_unique (hγ 1 h11) (tendsto_const_nhds.congr fun n => ((hinv n).2.2.1).symm)
  · intro i t ht
    have hi3 : (i : ℕ) ≤ 3 := by
      have := i.isLt
      omega
    have hi3' : ((i : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hi3
    have hq : (((i : ℕ) : ℝ) + t) / 4 ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (add_nonneg (Nat.cast_nonneg _) ht.1) (by norm_num), by linarith [ht.2]⟩
    have h1 := (hγ _ hq).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n => F (n + 1) ((((i : ℕ) : ℝ) + t) / 4)) atTop (𝓝 (koch_φ c i (γ t))) := by
      have e : (fun n => F (n + 1) ((((i : ℕ) : ℝ) + t) / 4)) = fun n => koch_φ c i (F n t) := by
        funext n
        rw [hFs]
        exact koch_read_quarter hc0 hc1 (hinv n).2.1 (hinv n).2.2.1 i ht
      rw [e]
      exact ((koch_φ_continuous c i).tendsto _).comp (hγ t ht)
    exact tendsto_nhds_unique h1 h2
  · intro t ht
    exact koch_T_isClosed.mem_of_tendsto (hγ t ht) (Filter.Eventually.of_forall fun n => (hinv n).2.2.2 t ht)

/-- K2. The triangle `T` has diameter `1`.
Truth: the vertex distances are `1`, `√2/2`, `√2/2`, and a convex polygon's diameter is attained at vertices. -/
theorem koch_T_dist {z w : ℂ} (hz : z ∈ koch_T) (hw : w ∈ koch_T) : ‖z - w‖ ≤ 1 := by
  obtain ⟨hz0, hz1, hz2⟩ := hz
  obtain ⟨hw0, hw1, hw2⟩ := hw
  rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sqrt_le_one]
  simp only [Complex.sub_re, Complex.sub_im]
  nlinarith [mul_nonneg (show 0 ≤ 1 - ((z.re - z.im) - (w.re - w.im)) by linarith)
      (show 0 ≤ 1 + ((z.re - z.im) - (w.re - w.im)) by linarith),
    mul_nonneg (show 0 ≤ 1 - ((z.re + z.im) - (w.re + w.im)) by linarith)
      (show 0 ≤ 1 + ((z.re + z.im) - (w.re + w.im)) by linarith)]

/-- K2. Non-adjacent pieces are `r c` apart.
Truth: `Re (φ₀ T) ≤ r`, `Re (φ₁ T) ≤ 1/2 ≤ Re (φ₂ T)`, `Re (φ₃ T) ≥ 1 - r`, and `1/2 - r = r c`. -/
theorem koch_sep_far {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) {i j : Fin 4} (hij : (i : ℕ) + 2 ≤ j)
    {z w : ℂ} (hz : z ∈ koch_T) (hw : w ∈ koch_T) : koch_r c * c ≤ ‖koch_φ c i z - koch_φ c j w‖ := by
  obtain ⟨hr3, hr2, hr⟩ := koch_r_facts hc0 hc1
  obtain ⟨hcs, hs1, -⟩ := koch_s_facts hc0 hc1
  obtain ⟨hz0, hz1, hz2⟩ := hz
  obtain ⟨hw0, hw1, hw2⟩ := hw
  obtain ⟨z0r, -, z1r, -, -, -, -, -⟩ := koch_φ_re_im c z
  obtain ⟨-, -, -, -, w2r, -, w3r, -⟩ := koch_φ_re_im c w
  have hr0 : 0 ≤ koch_r c := by linarith
  have hr' : koch_r c + koch_r c * c = 1 / 2 := by rw [← hr]; ring
  have hs0 : 0 ≤ koch_s c := by linarith
  have hrc : 0 ≤ koch_r c * c := mul_nonneg hr0 hc0.le
  have a0 : (koch_φ c 0 z).re ≤ koch_r c := by
    rw [z0r]
    exact mul_le_of_le_one_right hr0 (by linarith)
  have a1 : (koch_φ c 1 z).re ≤ 1 / 2 := by
    rw [z1r]
    linarith [mul_nonneg hr0 (mul_nonneg hs0 hz0), mul_nonneg hr0 (mul_nonneg hc0.le (show 0 ≤ 1 - z.re by linarith))]
  have b2 : 1 / 2 ≤ (koch_φ c 2 w).re := by
    rw [w2r]
    linarith [mul_nonneg hr0 (mul_nonneg hc0.le (show 0 ≤ w.re by linarith)), mul_nonneg hr0 (mul_nonneg hs0 hw0)]
  have b3 : 1 - koch_r c ≤ (koch_φ c 3 w).re := by
    rw [w3r]
    linarith [mul_nonneg hr0 (show 0 ≤ w.re by linarith)]
  have hnorm : (koch_φ c j w).re - (koch_φ c i z).re ≤ ‖koch_φ c i z - koch_φ c j w‖ := by
    rw [norm_sub_rev, ← Complex.sub_re]
    exact Complex.re_le_norm _
  refine le_trans ?_ hnorm
  fin_cases i <;> fin_cases j <;> (try simp at hij)
  · show koch_r c * c ≤ (koch_φ c 2 w).re - (koch_φ c 0 z).re
    linarith
  · show koch_r c * c ≤ (koch_φ c 3 w).re - (koch_φ c 0 z).re
    linarith
  · show koch_r c * c ≤ (koch_φ c 3 w).re - (koch_φ c 1 z).re
    linarith

/-- K2. The first three pieces stay `1/8` away from `1`.
Truth: their real parts are at most `7/8` (for `φ₂`: `1/2 + r (c x + s y) ≤ 1/2 + 3/8`). -/
theorem koch_sep_one {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) {i : Fin 4} (hi : (i : ℕ) ≤ 2) {z : ℂ}
    (hz : z ∈ koch_T) : 1 / 8 ≤ ‖koch_φ c i z - 1‖ := by
  obtain ⟨hr3, hr2, hr⟩ := koch_r_facts hc0 hc1
  obtain ⟨hcs, hs1, -⟩ := koch_s_facts hc0 hc1
  obtain ⟨hz0, hz1, hz2⟩ := hz
  obtain ⟨z0r, -, z1r, -, z2r, -, -, -⟩ := koch_φ_re_im c z
  have hr0 : 0 ≤ koch_r c := by linarith
  have hr' : koch_r c + koch_r c * c = 1 / 2 := by rw [← hr]; ring
  have hs0 : 0 ≤ koch_s c := by linarith
  have hnorm : 1 - (koch_φ c i z).re ≤ ‖koch_φ c i z - 1‖ := by
    rw [norm_sub_rev]
    have h := Complex.re_le_norm (1 - koch_φ c i z)
    rwa [Complex.sub_re, Complex.one_re] at h
  refine le_trans ?_ hnorm
  fin_cases i <;> (try simp at hi)
  · show 1 / 8 ≤ 1 - (koch_φ c 0 z).re
    rw [z0r]
    linarith [mul_le_of_le_one_right hr0 (show z.re ≤ 1 by linarith)]
  · show 1 / 8 ≤ 1 - (koch_φ c 1 z).re
    rw [z1r]
    linarith [mul_nonneg hr0 (mul_nonneg hs0 hz0), mul_nonneg hr0 (mul_nonneg hc0.le (show 0 ≤ 1 - z.re by linarith))]
  · show 1 / 8 ≤ 1 - (koch_φ c 2 z).re
    rw [z2r]
    linarith [mul_nonneg hr0 (mul_nonneg (sub_nonneg.2 hs1) hz0),
      mul_nonneg hr0 (mul_nonneg (show 0 ≤ 1 - c by linarith) (show 0 ≤ z.re - z.im by linarith)),
      mul_nonneg hr0 (mul_nonneg (show 0 ≤ 1 + c by linarith) (show 0 ≤ 1 - z.re - z.im by linarith))]

/-- K2. The last three pieces stay `1/8` away from `0`.
Truth: their real parts are at least `1/8` (for `φ₁`: `r (1 + c x - s y) ≥ r/2`, as `y ≤ 1/2`). -/
theorem koch_sep_zero {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) {i : Fin 4} (hi : 1 ≤ (i : ℕ)) {z : ℂ}
    (hz : z ∈ koch_T) : 1 / 8 ≤ ‖koch_φ c i z‖ := by
  obtain ⟨hr3, hr2, hr⟩ := koch_r_facts hc0 hc1
  obtain ⟨hcs, hs1, -⟩ := koch_s_facts hc0 hc1
  obtain ⟨hz0, hz1, hz2⟩ := hz
  obtain ⟨-, -, z1r, -, z2r, -, z3r, -⟩ := koch_φ_re_im c z
  have hr0 : 0 ≤ koch_r c := by linarith
  have hs0 : 0 ≤ koch_s c := by linarith
  refine le_trans ?_ (Complex.re_le_norm _)
  fin_cases i <;> (try simp at hi)
  · show 1 / 8 ≤ (koch_φ c 1 z).re
    rw [z1r]
    linarith [mul_nonneg hr0 (mul_nonneg hc0.le (show 0 ≤ z.re by linarith)),
      mul_nonneg hr0 (mul_nonneg (sub_nonneg.2 hs1) hz0), mul_nonneg hr0 (show 0 ≤ 1 - 2 * z.im by linarith)]
  · show 1 / 8 ≤ (koch_φ c 2 z).re
    rw [z2r]
    linarith [mul_nonneg hr0 (mul_nonneg hc0.le (show 0 ≤ z.re by linarith)), mul_nonneg hr0 (mul_nonneg hs0 hz0)]
  · show 1 / 8 ≤ (koch_φ c 3 z).re
    rw [z3r]
    linarith [mul_nonneg hr0 (show 0 ≤ z.re by linarith)]

/-- A real-linear functional `a Re + b Im` with `|a|, |b| ≤ 1` is at most `2 ‖·‖`. -/
theorem koch_lin_le (v : ℂ) {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) : a * v.re + b * v.im ≤ 2 * ‖v‖ := by
  have h1 : a * v.re ≤ ‖v‖ := by
    calc a * v.re ≤ |a * v.re| := le_abs_self _
      _ = |a| * |v.re| := abs_mul _ _
      _ ≤ 1 * ‖v‖ := mul_le_mul ha (Complex.abs_re_le_norm v) (abs_nonneg _) zero_le_one
      _ = ‖v‖ := one_mul _
  have h2 : b * v.im ≤ ‖v‖ := by
    calc b * v.im ≤ |b * v.im| := le_abs_self _
      _ = |b| * |v.im| := abs_mul _ _
      _ ≤ 1 * ‖v‖ := mul_le_mul hb (Complex.abs_im_le_norm v) (abs_nonneg _) zero_le_one
      _ = ‖v‖ := one_mul _
  linarith

/-- K2. Adjacent pieces meet at their common vertex `P = φᵢ 1` at a positive angle:
`(c/8) (‖φᵢ z - P‖ + ‖φᵢ₊₁ w - P‖) ≤ ‖φᵢ z - φᵢ₊₁ w‖`.
Truth: a linear functional `L` with `|L v| ≤ 2 |v|` is `≤ -(c/4) |·|` on `φᵢ T - P` and `≥ (c/4) |·|` on `φᵢ₊₁ T - P`
(`L = Re + (1 - c) Im`, `Re`, `Re - (1 - c) Im` at the three junctions). -/
theorem koch_sep_adj {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) (i : Fin 3) {z w : ℂ} (hz : z ∈ koch_T)
    (hw : w ∈ koch_T) :
    c / 8 * (‖koch_φ c i.castSucc z - koch_φ c i.castSucc 1‖ + ‖koch_φ c i.succ w - koch_φ c i.castSucc 1‖) ≤
      ‖koch_φ c i.castSucc z - koch_φ c i.succ w‖ := by
  obtain ⟨hr3, hr2, hr⟩ := koch_r_facts hc0 hc1
  obtain ⟨hcs, hs1, -⟩ := koch_s_facts hc0 hc1
  obtain ⟨-, -, hj⟩ := koch_φ_ends hc0 hc1
  obtain ⟨z0r, z0i, z1r, z1i, z2r, z2i, -, -⟩ := koch_φ_re_im c z
  obtain ⟨-, -, w1r, w1i, w2r, w2i, w3r, w3i⟩ := koch_φ_re_im c w
  obtain ⟨hz0, hz1, hz2⟩ := hz
  obtain ⟨hw0, hw1, hw2⟩ := hw
  have hr0 : 0 ≤ koch_r c := by linarith
  have hr' : koch_r c + koch_r c * c = 1 / 2 := by rw [← hr]; ring
  have hs0 : 0 ≤ koch_s c := by linarith
  have hx1 : 0 ≤ 1 - z.re := by linarith
  have hxy1 : 0 ≤ 1 - z.re - z.im := by linarith
  have hwx : 0 ≤ w.re := by linarith
  have hwxy : 0 ≤ w.re - w.im := by linarith
  have hsc : 0 ≤ koch_s c - c + c ^ 2 := add_nonneg (sub_nonneg.2 hcs.le) (sq_nonneg c)
  have hsc' : 0 ≤ 3 / 2 - koch_s c - c := by linarith
  have hzn : ‖z - 1‖ ≤ 2 * (1 - z.re) := by
    calc ‖z - 1‖ ≤ |(z - 1).re| + |(z - 1).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = (1 - z.re) + z.im := by
        rw [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero,
          abs_of_nonpos (by linarith), abs_of_nonneg hz0]
        ring
      _ ≤ 2 * (1 - z.re) := by linarith
  have hwn : ‖w‖ ≤ 2 * w.re := by
    calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im _
      _ = w.re + w.im := by rw [abs_of_nonneg hwx, abs_of_nonneg hw0]
      _ ≤ 2 * w.re := by linarith
  have hA : ∀ k : Fin 4, ‖koch_φ c k z - koch_φ c k 1‖ ≤ 2 * koch_r c * (1 - z.re) := fun k => by
    rw [koch_φ_dist hc0 hc1]
    linarith [mul_le_mul_of_nonneg_left hzn hr0]
  have hB : ∀ k : Fin 4, ‖koch_φ c k w - koch_φ c k 0‖ ≤ 2 * koch_r c * w.re := fun k => by
    rw [koch_φ_dist hc0 hc1, sub_zero]
    linarith [mul_le_mul_of_nonneg_left hwn hr0]
  have hfin : ∀ {A B D : ℝ}, A ≤ 2 * koch_r c * (1 - z.re) → B ≤ 2 * koch_r c * w.re →
      c / 2 * koch_r c * ((1 - z.re) + w.re) ≤ 2 * D → c / 8 * (A + B) ≤ D := fun hA' hB' hL => by
    linarith [mul_le_mul_of_nonneg_left hA' (show (0 : ℝ) ≤ c / 8 by positivity),
      mul_le_mul_of_nonneg_left hB' (show (0 : ℝ) ≤ c / 8 by positivity)]
  fin_cases i
  · show c / 8 * (‖koch_φ c 0 z - koch_φ c 0 1‖ + ‖koch_φ c 1 w - koch_φ c 0 1‖) ≤
      ‖koch_φ c 0 z - koch_φ c 1 w‖
    have hP : koch_φ c 0 1 = koch_φ c 1 0 := hj 0
    refine hfin (hA 0) (by rw [hP]; exact hB 1) ?_
    have hL := koch_lin_le (koch_φ c 1 w - koch_φ c 0 z) (a := 1) (b := 1 - c) (by rw [abs_one])
      (by rw [abs_le]; constructor <;> linarith)
    rw [Complex.sub_re, Complex.sub_im, w1r, w1i, z0r, z0i, norm_sub_rev] at hL
    linarith [mul_nonneg hr0 (mul_nonneg (show 0 ≤ 1 - c by linarith) hxy1), mul_nonneg hr0 (mul_nonneg hc0.le hx1),
      mul_nonneg hr0 (mul_nonneg hwxy hsc), mul_nonneg hr0 (mul_nonneg hc0.le (mul_nonneg hwx hsc'))]
  · show c / 8 * (‖koch_φ c 1 z - koch_φ c 1 1‖ + ‖koch_φ c 2 w - koch_φ c 1 1‖) ≤
      ‖koch_φ c 1 z - koch_φ c 2 w‖
    have hP : koch_φ c 1 1 = koch_φ c 2 0 := hj 1
    refine hfin (hA 1) (by rw [hP]; exact hB 2) ?_
    have hL := koch_lin_le (koch_φ c 2 w - koch_φ c 1 z) (a := 1) (b := 0) (by rw [abs_one])
      (by rw [abs_zero]; norm_num)
    rw [Complex.sub_re, Complex.sub_im, w2r, w2i, z1r, z1i, norm_sub_rev] at hL
    linarith [mul_nonneg hr0 (mul_nonneg hc0.le hx1), mul_nonneg hr0 (mul_nonneg hc0.le hwx),
      mul_nonneg hr0 (mul_nonneg hs0 hw0), mul_nonneg hr0 (mul_nonneg hs0 hz0)]
  · show c / 8 * (‖koch_φ c 2 z - koch_φ c 2 1‖ + ‖koch_φ c 3 w - koch_φ c 2 1‖) ≤
      ‖koch_φ c 2 z - koch_φ c 3 w‖
    have hP : koch_φ c 2 1 = koch_φ c 3 0 := hj 2
    refine hfin (hA 2) (by rw [hP]; exact hB 3) ?_
    have hL := koch_lin_le (koch_φ c 3 w - koch_φ c 2 z) (a := 1) (b := -(1 - c)) (by rw [abs_one])
      (by rw [abs_le]; constructor <;> linarith)
    rw [Complex.sub_re, Complex.sub_im, w3r, w3i, z2r, z2i, norm_sub_rev] at hL
    linarith [mul_nonneg hr0 (mul_nonneg hxy1 hsc), mul_nonneg hr0 (mul_nonneg hc0.le (mul_nonneg hx1 hsc')),
      mul_nonneg hr0 (mul_nonneg (show 0 ≤ 1 - c by linarith) hwxy), mul_nonneg hr0 (mul_nonneg hc0.le hwx)]

/-- K2. Sub-arcs of a piece are images of sub-arcs: `γ [(i + u)/4, (i + v)/4] = φᵢ (γ [u, v])`.
Truth: the self-similarity of `γ` on `[u, v] ⊆ [0, 1]`, and `t ↦ (i + t)/4` maps `[u, v]` onto the left side. -/
theorem koch_image_piece {c : ℝ} {γ : ℝ → ℂ} (hγ : koch_IsArc c γ) (i : Fin 4) {u v : ℝ} (hu : 0 ≤ u)
    (hv : v ≤ 1) : γ '' Icc (((i : ℕ) + u) / 4) (((i : ℕ) + v) / 4) = koch_φ c i '' (γ '' Icc u v) := by
  ext p
  constructor
  · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
    refine ⟨γ (4 * t - (i : ℕ)), ⟨4 * t - (i : ℕ), ⟨by linarith, by linarith⟩, rfl⟩, ?_⟩
    have h := hγ.2.2.2.1 i (4 * t - (i : ℕ)) ⟨by linarith, by linarith⟩
    rw [show ((i : ℕ) + (4 * t - (i : ℕ))) / 4 = t by ring] at h
    exact h.symm
  · rintro ⟨_, ⟨t, ⟨ht1, ht2⟩, rfl⟩, rfl⟩
    exact ⟨((i : ℕ) + t) / 4, ⟨by linarith, by linarith⟩, hγ.2.2.2.1 i t ⟨by linarith, by linarith⟩⟩

/-- The triangle `T` is bounded. -/
theorem koch_T_bounded : Bornology.IsBounded koch_T :=
  (isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset fun z hz => by
    rw [mem_closedBall, dist_zero_right]
    exact koch_T_norm_le hz

/-- Sub-arcs of a Koch arc lie in `T`. -/
theorem koch_image_T {c : ℝ} {γ : ℝ → ℂ} (hγ : koch_IsArc c γ) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    γ '' Icc a b ⊆ koch_T := by
  rintro _ ⟨t, ⟨ht1, ht2⟩, rfl⟩
  exact hγ.2.2.2.2 t ⟨by linarith, by linarith⟩

/-- Sub-arcs of a Koch arc have diameter at most `1`. -/
theorem koch_diam_le_one {c : ℝ} {γ : ℝ → ℂ} (hγ : koch_IsArc c γ) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    diam (γ '' Icc a b) ≤ 1 :=
  diam_le_of_forall_dist_le zero_le_one fun p hp q hq => by
    rw [dist_eq_norm]
    exact koch_T_dist (koch_image_T hγ ha hb hp) (koch_image_T hγ ha hb hq)

/-- `φᵢ` scales diameters of subsets of `T` by at most `r`. -/
theorem koch_diam_φ {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) (i : Fin 4) {S : Set ℂ} (hS : S ⊆ koch_T) :
    diam (koch_φ c i '' S) ≤ koch_r c * diam S := by
  obtain ⟨hr3, -, -⟩ := koch_r_facts hc0 hc1
  have hr0 : 0 ≤ koch_r c := by linarith
  refine diam_le_of_forall_dist_le (mul_nonneg hr0 diam_nonneg) ?_
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
  rw [dist_eq_norm, koch_φ_dist hc0 hc1, ← dist_eq_norm]
  exact mul_le_mul_of_nonneg_left (dist_le_diam_of_mem (koch_T_bounded.subset hS) hp hq) hr0

/-- A point of the `i`-th quarter: `γ u = φᵢ (γ (4 u - i))`, and `γ (4 u - i) ∈ T`. -/
theorem koch_piece {c : ℝ} {γ : ℝ → ℂ} (hγ : koch_IsArc c γ) (i : Fin 4) {u : ℝ} (h1 : ((i : ℕ) : ℝ) / 4 ≤ u)
    (h2 : u ≤ (((i : ℕ) : ℝ) + 1) / 4) : γ u = koch_φ c i (γ (4 * u - (i : ℕ))) ∧ γ (4 * u - (i : ℕ)) ∈ koch_T := by
  have ht : 4 * u - (i : ℕ) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have e := hγ.2.2.2.1 i _ ht
  rw [show ((i : ℕ) + (4 * u - (i : ℕ))) / 4 = u by ring] at e
  exact ⟨e, hγ.2.2.2.2 _ ht⟩

/-- K2. The endpoint estimate at `1`: `diam γ [u, 1] ≤ 8 ‖γ u - 1‖`.
Truth: induction on `1 - u ≥ 4⁻ⁿ`; for `u ≤ 3/4`, `γ u` is in a piece `φᵢ T` with `i ≤ 2` (`koch_sep_one`) and
`diam γ ≤ 1`; otherwise rescale by `φ₃`. -/
theorem koch_end_one {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) {γ : ℝ → ℂ} (hγ : koch_IsArc c γ) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) : diam (γ '' Icc u 1) ≤ 8 * ‖γ u - 1‖ := by
  obtain ⟨hr3, hr2, -⟩ := koch_r_facts hc0 hc1
  have hr0 : 0 ≤ koch_r c := by linarith
  obtain ⟨-, h3, -⟩ := koch_φ_ends hc0 hc1
  have key : ∀ n : ℕ, ∀ u ∈ Icc (0 : ℝ) 1, 4 ≤ 4 ^ n * (1 - u) → diam (γ '' Icc u 1) ≤ 8 * ‖γ u - 1‖ := by
    intro n
    induction n with
    | zero =>
      intro u hu h
      rw [pow_zero, one_mul] at h
      linarith [hu.1]
    | succ n ih =>
      intro u hu h
      by_cases hu3 : u ≤ 3 / 4
      · have hsep : 1 / 8 ≤ ‖γ u - 1‖ := by
          by_cases hq1 : u ≤ 1 / 4
          · obtain ⟨e, hT⟩ := koch_piece hγ 0 (by show ((0 : ℕ) : ℝ) / 4 ≤ u; simp [hu.1])
              (by show u ≤ (((0 : ℕ) : ℝ) + 1) / 4; simp; linarith)
            rw [e]
            exact koch_sep_one hc0 hc1 (by decide) hT
          by_cases hq2 : u ≤ 1 / 2
          · obtain ⟨e, hT⟩ := koch_piece hγ 1 (by show ((1 : ℕ) : ℝ) / 4 ≤ u; push_cast; linarith)
              (by show u ≤ (((1 : ℕ) : ℝ) + 1) / 4; push_cast; linarith)
            rw [e]
            exact koch_sep_one hc0 hc1 (by decide) hT
          · obtain ⟨e, hT⟩ := koch_piece hγ 2 (by show ((2 : ℕ) : ℝ) / 4 ≤ u; push_cast; linarith)
              (by show u ≤ (((2 : ℕ) : ℝ) + 1) / 4; push_cast; linarith)
            rw [e]
            exact koch_sep_one hc0 hc1 (by decide) hT
        linarith [koch_diam_le_one hγ hu.1 le_rfl]
      · rw [not_le] at hu3
        have htI : 4 * u - 3 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hu.2]⟩
        have h4 : 4 ≤ 4 ^ n * (1 - (4 * u - 3)) := by
          rw [pow_succ] at h
          linarith
        have himg : γ '' Icc u 1 = koch_φ c 3 '' (γ '' Icc (4 * u - 3) 1) := by
          have e : γ '' Icc ((((3 : ℕ) : ℝ) + (4 * u - 3)) / 4) ((((3 : ℕ) : ℝ) + 1) / 4) =
              koch_φ c 3 '' (γ '' Icc (4 * u - 3) 1) := koch_image_piece hγ 3 htI.1 le_rfl
          rwa [show (((3 : ℕ) : ℝ) + (4 * u - 3)) / 4 = u by push_cast; ring,
            show (((3 : ℕ) : ℝ) + 1) / 4 = 1 by norm_num] at e
        have hγu : γ u = koch_φ c 3 (γ (4 * u - 3)) := by
          have e : γ ((((3 : ℕ) : ℝ) + (4 * u - 3)) / 4) = koch_φ c 3 (γ (4 * u - 3)) := hγ.2.2.2.1 3 _ htI
          rwa [show (((3 : ℕ) : ℝ) + (4 * u - 3)) / 4 = u by push_cast; ring] at e
        have hd := koch_φ_dist hc0 hc1 3 (γ (4 * u - 3)) 1
        rw [h3] at hd
        rw [himg]
        calc diam (koch_φ c 3 '' (γ '' Icc (4 * u - 3) 1)) ≤ koch_r c * diam (γ '' Icc (4 * u - 3) 1) :=
              koch_diam_φ hc0 hc1 3 (koch_image_T hγ htI.1 le_rfl)
          _ ≤ koch_r c * (8 * ‖γ (4 * u - 3) - 1‖) := mul_le_mul_of_nonneg_left (ih _ htI h4) hr0
          _ = 8 * ‖γ u - 1‖ := by
            rw [hγu, hd]
            ring
  rcases eq_or_lt_of_le hu.2 with rfl | hlt
  · rw [Icc_self, image_singleton, diam_singleton]
    positivity
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (4 / (1 - u)) (by norm_num : (1 : ℝ) < 4)
    refine key n u hu ?_
    rw [div_lt_iff₀ (by linarith)] at hn
    linarith

/-- K2. The endpoint estimate at `0`: `diam γ [0, u] ≤ 8 ‖γ u‖`.
Truth: as `koch_end_one`, with `koch_sep_zero` and `φ₀`. -/
theorem koch_end_zero {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) {γ : ℝ → ℂ} (hγ : koch_IsArc c γ) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) : diam (γ '' Icc 0 u) ≤ 8 * ‖γ u‖ := by
  obtain ⟨hr3, hr2, -⟩ := koch_r_facts hc0 hc1
  have hr0 : 0 ≤ koch_r c := by linarith
  obtain ⟨h0, -, -⟩ := koch_φ_ends hc0 hc1
  have key : ∀ n : ℕ, ∀ u ∈ Icc (0 : ℝ) 1, 4 ≤ 4 ^ n * u → diam (γ '' Icc 0 u) ≤ 8 * ‖γ u‖ := by
    intro n
    induction n with
    | zero =>
      intro u hu h
      rw [pow_zero, one_mul] at h
      linarith [hu.2]
    | succ n ih =>
      intro u hu h
      by_cases hu1 : 1 / 4 ≤ u
      · have hsep : 1 / 8 ≤ ‖γ u‖ := by
          by_cases hq3 : 3 / 4 ≤ u
          · obtain ⟨e, hT⟩ := koch_piece hγ 3 (by show ((3 : ℕ) : ℝ) / 4 ≤ u; push_cast; linarith)
              (by show u ≤ (((3 : ℕ) : ℝ) + 1) / 4; push_cast; linarith [hu.2])
            rw [e]
            exact koch_sep_zero hc0 hc1 (by decide) hT
          by_cases hq2 : 1 / 2 ≤ u
          · obtain ⟨e, hT⟩ := koch_piece hγ 2 (by show ((2 : ℕ) : ℝ) / 4 ≤ u; push_cast; linarith)
              (by show u ≤ (((2 : ℕ) : ℝ) + 1) / 4; push_cast; linarith)
            rw [e]
            exact koch_sep_zero hc0 hc1 (by decide) hT
          · obtain ⟨e, hT⟩ := koch_piece hγ 1 (by show ((1 : ℕ) : ℝ) / 4 ≤ u; push_cast; linarith)
              (by show u ≤ (((1 : ℕ) : ℝ) + 1) / 4; push_cast; linarith)
            rw [e]
            exact koch_sep_zero hc0 hc1 (by decide) hT
        linarith [koch_diam_le_one hγ le_rfl hu.2]
      · rw [not_le] at hu1
        have htI : 4 * u ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.1], by linarith⟩
        have h4 : 4 ≤ 4 ^ n * (4 * u) := by
          rw [pow_succ] at h
          linarith
        have himg : γ '' Icc 0 u = koch_φ c 0 '' (γ '' Icc 0 (4 * u)) := by
          have e : γ '' Icc ((((0 : ℕ) : ℝ) + 0) / 4) ((((0 : ℕ) : ℝ) + 4 * u) / 4) =
              koch_φ c 0 '' (γ '' Icc 0 (4 * u)) := koch_image_piece hγ 0 le_rfl htI.2
          rwa [show (((0 : ℕ) : ℝ) + 0) / 4 = 0 by norm_num,
            show (((0 : ℕ) : ℝ) + 4 * u) / 4 = u by push_cast; ring] at e
        have hγu : γ u = koch_φ c 0 (γ (4 * u)) := by
          have e : γ ((((0 : ℕ) : ℝ) + 4 * u) / 4) = koch_φ c 0 (γ (4 * u)) := hγ.2.2.2.1 0 _ htI
          rwa [show (((0 : ℕ) : ℝ) + 4 * u) / 4 = u by push_cast; ring] at e
        have hd := koch_φ_dist hc0 hc1 0 (γ (4 * u)) 0
        rw [h0, sub_zero, sub_zero] at hd
        rw [himg]
        calc diam (koch_φ c 0 '' (γ '' Icc 0 (4 * u))) ≤ koch_r c * diam (γ '' Icc 0 (4 * u)) :=
              koch_diam_φ hc0 hc1 0 (koch_image_T hγ le_rfl htI.2)
          _ ≤ koch_r c * (8 * ‖γ (4 * u)‖) := mul_le_mul_of_nonneg_left (ih _ htI h4) hr0
          _ = 8 * ‖γ u‖ := by
            rw [hγu, hd]
            ring
  rcases eq_or_lt_of_le hu.1 with h | hlt
  · rw [← h, Icc_self, image_singleton, diam_singleton]
    positivity
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (4 / u) (by norm_num : (1 : ℝ) < 4)
    refine key n u hu ?_
    rw [div_lt_iff₀ hlt] at hn
    linarith

/-- K2. The arc is of bounded turning: `diam γ [s, t] ≤ (64/c) ‖γ s - γ t‖`.
Truth: induction on `t - s ≥ 4⁻ⁿ`: in one level-1 piece, rescale; non-adjacent pieces, `koch_sep_far`
(`1 ≤ (3/c) r c`); adjacent pieces, the endpoint estimates on both sides of the common vertex and `koch_sep_adj`. -/
theorem koch_arc_bt {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) {γ : ℝ → ℂ} (hγ : koch_IsArc c γ) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    diam (γ '' Icc s t) ≤ 64 / c * ‖γ s - γ t‖ := by
  obtain ⟨hr3, hr2, -⟩ := koch_r_facts hc0 hc1
  have hr0 : 0 ≤ koch_r c := by linarith
  obtain ⟨-, -, hj⟩ := koch_φ_ends hc0 hc1
  have hrep : ∀ x ∈ Icc (0 : ℝ) 1, ∃ i : Fin 4, ∃ x' ∈ Icc (0 : ℝ) 1, x = ((i : ℕ) + x') / 4 := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    by_cases h1 : x ≤ 1 / 4
    · exact ⟨0, 4 * x, ⟨by linarith, by linarith⟩, by show x = (((0 : ℕ) : ℝ) + 4 * x) / 4; push_cast; ring⟩
    by_cases h2 : x ≤ 1 / 2
    · exact ⟨1, 4 * x - 1, ⟨by linarith, by linarith⟩,
        by show x = (((1 : ℕ) : ℝ) + (4 * x - 1)) / 4; push_cast; ring⟩
    by_cases h3 : x ≤ 3 / 4
    · exact ⟨2, 4 * x - 2, ⟨by linarith, by linarith⟩,
        by show x = (((2 : ℕ) : ℝ) + (4 * x - 2)) / 4; push_cast; ring⟩
    · exact ⟨3, 4 * x - 3, ⟨by linarith, by linarith⟩,
        by show x = (((3 : ℕ) : ℝ) + (4 * x - 3)) / 4; push_cast; ring⟩
  have key : ∀ n : ℕ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, s ≤ t → 4 ≤ 4 ^ n * (t - s) →
      diam (γ '' Icc s t) ≤ 64 / c * ‖γ s - γ t‖ := by
    intro n
    induction n with
    | zero =>
      intro s hs t ht _ h
      rw [pow_zero, one_mul] at h
      linarith [hs.1, ht.2]
    | succ n ih =>
      intro s hs t ht hst h
      obtain ⟨i, s', hs', rfl⟩ := hrep s hs
      obtain ⟨j, t', ht', rfl⟩ := hrep t ht
      have hj3 : (j : ℕ) ≤ 3 := by
        have := j.isLt
        omega
      rcases lt_trichotomy (i : ℕ) (j : ℕ) with hij | hij | hij
      · by_cases hadj : (j : ℕ) = (i : ℕ) + 1
        · obtain ⟨k, hk1, hk2⟩ : ∃ k : Fin 3, k.castSucc = i ∧ k.succ = j :=
            ⟨⟨i, by omega⟩, Fin.ext rfl, Fin.ext (by simp [hadj])⟩
          have hjR : ((j : ℕ) : ℝ) = (i : ℕ) + 1 := by exact_mod_cast hadj
          have hPij : koch_φ c i 1 = koch_φ c j 0 := by
            rw [← hk1, ← hk2]
            exact hj k
          have hm1 : (((i : ℕ) : ℝ) + s') / 4 ≤ (((i : ℕ) : ℝ) + 1) / 4 := by linarith [hs'.2]
          have hm2 : (((i : ℕ) : ℝ) + 1) / 4 ≤ (((j : ℕ) : ℝ) + t') / 4 := by
            rw [hjR]
            linarith [ht'.1]
          have hsplit : Icc ((((i : ℕ) : ℝ) + s') / 4) ((((j : ℕ) : ℝ) + t') / 4) =
              Icc ((((i : ℕ) : ℝ) + s') / 4) ((((i : ℕ) : ℝ) + 1) / 4) ∪
                Icc ((((j : ℕ) : ℝ) + 0) / 4) ((((j : ℕ) : ℝ) + t') / 4) := by
            rw [show (((j : ℕ) : ℝ) + 0) / 4 = (((i : ℕ) : ℝ) + 1) / 4 by rw [hjR]; ring]
            exact (Icc_union_Icc_eq_Icc hm1 hm2).symm
          have hsep := koch_sep_adj hc0 hc1 k (hγ.2.2.2.2 s' hs') (hγ.2.2.2.2 t' ht')
          rw [hk1, hk2] at hsep
          have hdA : diam (koch_φ c i '' (γ '' Icc s' 1)) ≤ 8 * ‖koch_φ c i (γ s') - koch_φ c i 1‖ := by
            calc diam (koch_φ c i '' (γ '' Icc s' 1)) ≤ koch_r c * diam (γ '' Icc s' 1) :=
                  koch_diam_φ hc0 hc1 i (koch_image_T hγ hs'.1 le_rfl)
              _ ≤ koch_r c * (8 * ‖γ s' - 1‖) := mul_le_mul_of_nonneg_left (koch_end_one hc0 hc1 hγ hs') hr0
              _ = 8 * ‖koch_φ c i (γ s') - koch_φ c i 1‖ := by
                rw [koch_φ_dist hc0 hc1]
                ring
          have hdB : diam (koch_φ c j '' (γ '' Icc 0 t')) ≤ 8 * ‖koch_φ c j (γ t') - koch_φ c i 1‖ := by
            calc diam (koch_φ c j '' (γ '' Icc 0 t')) ≤ koch_r c * diam (γ '' Icc 0 t') :=
                  koch_diam_φ hc0 hc1 j (koch_image_T hγ le_rfl ht'.2)
              _ ≤ koch_r c * (8 * ‖γ t'‖) := mul_le_mul_of_nonneg_left (koch_end_zero hc0 hc1 hγ ht') hr0
              _ = 8 * ‖koch_φ c j (γ t') - koch_φ c i 1‖ := by
                rw [hPij, koch_φ_dist hc0 hc1, sub_zero]
                ring
          have hPA : koch_φ c i 1 ∈ koch_φ c i '' (γ '' Icc s' 1) :=
            ⟨γ 1, ⟨1, ⟨hs'.2, le_rfl⟩, rfl⟩, by rw [hγ.2.2.1]⟩
          have hPB : koch_φ c i 1 ∈ koch_φ c j '' (γ '' Icc 0 t') :=
            ⟨γ 0, ⟨0, ⟨le_rfl, ht'.1⟩, rfl⟩, by rw [hγ.2.1, hPij]⟩
          have hU := diam_union' (s := koch_φ c i '' (γ '' Icc s' 1)) ⟨_, hPA, hPB⟩
          rw [hsplit, image_union, koch_image_piece hγ i hs'.1 le_rfl, koch_image_piece hγ j le_rfl ht'.2,
            hγ.2.2.2.1 i s' hs', hγ.2.2.2.1 j t' ht', div_mul_eq_mul_div, le_div_iff₀ hc0]
          linarith [mul_le_mul_of_nonneg_right (hU.trans (add_le_add hdA hdB)) hc0.le]
        · have hfar : (i : ℕ) + 2 ≤ j := by omega
          have hD := koch_sep_far hc0 hc1 hfar (hγ.2.2.2.2 s' hs') (hγ.2.2.2.2 t' ht')
          rw [← hγ.2.2.2.1 i s' hs', ← hγ.2.2.2.1 j t' ht'] at hD
          have hj3' : ((j : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hj3
          have hdiam := koch_diam_le_one hγ (a := (((i : ℕ) : ℝ) + s') / 4) (b := (((j : ℕ) : ℝ) + t') / 4)
            (div_nonneg (add_nonneg (Nat.cast_nonneg _) hs'.1) (by norm_num)) (by linarith [ht'.2])
          rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
          linarith [mul_le_mul_of_nonneg_right hdiam hc0.le, mul_le_mul_of_nonneg_right hr3 hc0.le,
            mul_nonneg hr0 hc0.le]
      · have hij' : i = j := Fin.ext hij
        subst hij'
        have hst' : s' ≤ t' := by linarith
        have h' : 4 ≤ 4 ^ n * (t' - s') := by
          rw [pow_succ] at h
          linarith
        have hih := ih s' hs' t' ht' hst' h'
        rw [koch_image_piece hγ i hs'.1 ht'.2, hγ.2.2.2.1 i s' hs', hγ.2.2.2.1 i t' ht', koch_φ_dist hc0 hc1]
        calc diam (koch_φ c i '' (γ '' Icc s' t')) ≤ koch_r c * diam (γ '' Icc s' t') :=
              koch_diam_φ hc0 hc1 i (koch_image_T hγ hs'.1 ht'.2)
          _ ≤ koch_r c * (64 / c * ‖γ s' - γ t'‖) := mul_le_mul_of_nonneg_left hih hr0
          _ = 64 / c * (koch_r c * ‖γ s' - γ t'‖) := by ring
      · exfalso
        have hji : ((j : ℕ) : ℝ) + 1 ≤ (i : ℕ) := by exact_mod_cast hij
        nlinarith [pow_pos (show (0 : ℝ) < 4 by norm_num) (n + 1), hs'.1, ht'.2]
  rcases eq_or_lt_of_le hst with h | hlt
  · rw [h]
    simp
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (4 / (t - s)) (by norm_num : (1 : ℝ) < 4)
    refine key n s hs t ht hst ?_
    rw [div_lt_iff₀ (by linarith)] at hn
    linarith

/-- K2. The level-`m` pieces have endpoint distance `r ^ m`: `‖γ ((k + 1)/4^m) - γ (k/4^m)‖ = r ^ m`.
Truth: induction on `m`, writing `k = i 4^m + k'` with `i < 4`, `k' < 4^m`, and the self-similarity. -/
theorem koch_grid {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) {γ : ℝ → ℂ} (hγ : koch_IsArc c γ) (m k : ℕ)
    (hk : k < 4 ^ m) : ‖γ (((k : ℝ) + 1) / 4 ^ m) - γ ((k : ℝ) / 4 ^ m)‖ = koch_r c ^ m := by
  induction m generalizing k with
  | zero =>
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    simp [hγ.2.1, hγ.2.2.1]
  | succ m ih =>
    have hpos : (0 : ℝ) < 4 ^ m := by positivity
    have hq4 : k / 4 ^ m < 4 := Nat.div_lt_of_lt_mul (by rw [← pow_succ]; exact hk)
    have hk'lt : k % 4 ^ m < 4 ^ m := Nat.mod_lt _ (by positivity)
    have hkR : (k : ℝ) = 4 ^ m * ((k / 4 ^ m : ℕ) : ℝ) + ((k % 4 ^ m : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod k (4 ^ m)).symm
    have hk'R : ((k % 4 ^ m : ℕ) : ℝ) + 1 ≤ 4 ^ m := by exact_mod_cast hk'lt
    have hx0 : ((k % 4 ^ m : ℕ) : ℝ) / 4 ^ m ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, by rw [div_le_one hpos]; linarith⟩
    have hx1 : (((k % 4 ^ m : ℕ) : ℝ) + 1) / 4 ^ m ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, by rw [div_le_one hpos]; exact hk'R⟩
    have e0 : γ ((((k / 4 ^ m : ℕ) : ℝ) + ((k % 4 ^ m : ℕ) : ℝ) / 4 ^ m) / 4) =
        koch_φ c ⟨k / 4 ^ m, hq4⟩ (γ (((k % 4 ^ m : ℕ) : ℝ) / 4 ^ m)) := hγ.2.2.2.1 ⟨k / 4 ^ m, hq4⟩ _ hx0
    have e1 : γ ((((k / 4 ^ m : ℕ) : ℝ) + (((k % 4 ^ m : ℕ) : ℝ) + 1) / 4 ^ m) / 4) =
        koch_φ c ⟨k / 4 ^ m, hq4⟩ (γ ((((k % 4 ^ m : ℕ) : ℝ) + 1) / 4 ^ m)) :=
      hγ.2.2.2.1 ⟨k / 4 ^ m, hq4⟩ _ hx1
    have ha : (k : ℝ) / 4 ^ (m + 1) = (((k / 4 ^ m : ℕ) : ℝ) + ((k % 4 ^ m : ℕ) : ℝ) / 4 ^ m) / 4 := by
      rw [hkR, pow_succ]
      field_simp
    have hb : ((k : ℝ) + 1) / 4 ^ (m + 1) =
        (((k / 4 ^ m : ℕ) : ℝ) + (((k % 4 ^ m : ℕ) : ℝ) + 1) / 4 ^ m) / 4 := by
      rw [hkR, pow_succ]
      field_simp
      ring
    rw [ha, hb, e0, e1, koch_φ_dist hc0 hc1, ih _ hk'lt, pow_succ]
    ring

/-- K2. The co-Hölder estimate `|s - t| ≤ C ‖γ s - γ t‖ ^ d`, `d = log 4 / log (2 + 2c)`.
Truth: `[s, t]` contains a level-`m` grid interval with `t - s < 8 · 4⁻ᵐ`, so bounded turning and `koch_grid` give
`‖γ s - γ t‖ ≥ rᵐ c/64`, and `r ^ d = 1/4`; `C = 8 (64/c) ^ d`. -/
theorem koch_coHolder {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) {γ : ℝ → ℂ} (hγ : koch_IsArc c γ) :
    ∃ C : ℝ≥0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      edist s t ≤ (C : ℝ≥0∞) * edist (γ s) (γ t) ^ ((koch_d c).toNNReal : ℝ) := by
  obtain ⟨hr3, hr2, -⟩ := koch_r_facts hc0 hc1
  have hr0 : 0 < koch_r c := by linarith
  have hd0 : 0 ≤ koch_d c := by linarith [koch_d_gt_one hc0 hc1]
  have hl : 0 < Real.log (2 + 2 * c) := Real.log_pos (by linarith)
  have hrd : koch_r c ^ koch_d c = 1 / 4 := by
    have e : Real.log (koch_r c) * koch_d c = -Real.log 4 := by
      rw [koch_r, koch_d, one_div, Real.log_inv, neg_mul, mul_div_assoc', mul_comm (Real.log (2 + 2 * c)),
        mul_div_assoc, div_self hl.ne', mul_one]
    rw [Real.rpow_def_of_pos hr0, e, Real.exp_neg, Real.exp_log (by norm_num), one_div]
  have key : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, s < t →
      t - s ≤ 8 * (64 / c) ^ koch_d c * ‖γ s - γ t‖ ^ koch_d c := by
    intro s hs t ht hst
    have hts : 0 < t - s := by linarith
    obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near (show (1 : ℝ) ≤ 8 / (t - s) by
      rw [le_div_iff₀ hts]; linarith [hs.1, ht.2]) (by norm_num : (1 : ℝ) < 4)
    have h4m : (0 : ℝ) < 4 ^ m := by positivity
    rw [le_div_iff₀ hts] at hm1
    rw [div_lt_iff₀ hts, pow_succ] at hm2
    have hsm : 0 ≤ s * 4 ^ m := mul_nonneg hs.1 h4m.le
    have hk1 : s * 4 ^ m ≤ (⌈s * 4 ^ m⌉₊ : ℝ) := Nat.le_ceil _
    have hk2 : (⌈s * 4 ^ m⌉₊ : ℝ) < s * 4 ^ m + 1 := Nat.ceil_lt_add_one hsm
    set k := ⌈s * 4 ^ m⌉₊ with hk
    have hks : s ≤ (k : ℝ) / 4 ^ m := by
      rw [le_div_iff₀ h4m]
      linarith
    have hkt : ((k : ℝ) + 1) / 4 ^ m ≤ t := by
      rw [div_le_iff₀ h4m]
      linarith
    have hkm : k < 4 ^ m := by
      have h1 : (k : ℝ) + 1 ≤ t * 4 ^ m := by rwa [div_le_iff₀ h4m] at hkt
      have h2 : (k : ℝ) < 4 ^ m := by linarith [mul_le_mul_of_nonneg_right ht.2 h4m.le]
      exact_mod_cast h2
    have hg := koch_grid hc0 hc1 hγ m k hkm
    have hbt := koch_arc_bt hc0 hc1 hγ hs ht hst.le
    have hbd : Bornology.IsBounded (γ '' Icc s t) := koch_T_bounded.subset (koch_image_T hγ hs.1 ht.2)
    have hkk : (k : ℝ) / 4 ^ m ≤ ((k : ℝ) + 1) / 4 ^ m := (div_le_div_iff_of_pos_right h4m).2 (by linarith)
    have hmem1 : γ (((k : ℝ) + 1) / 4 ^ m) ∈ γ '' Icc s t := ⟨_, ⟨hks.trans hkk, hkt⟩, rfl⟩
    have hmem0 : γ ((k : ℝ) / 4 ^ m) ∈ γ '' Icc s t := ⟨_, ⟨hks, hkk.trans hkt⟩, rfl⟩
    have hdist := dist_le_diam_of_mem hbd hmem1 hmem0
    rw [dist_eq_norm, hg] at hdist
    have hA : c / 64 * koch_r c ^ m ≤ ‖γ s - γ t‖ := by
      have h := hdist.trans hbt
      rw [div_mul_eq_mul_div, le_div_iff₀ hc0] at h
      linarith
    have hB : (c / 64 * koch_r c ^ m) ^ koch_d c ≤ ‖γ s - γ t‖ ^ koch_d c :=
      Real.rpow_le_rpow (by positivity) hA hd0
    have hC : (c / 64 * koch_r c ^ m) ^ koch_d c = (c / 64) ^ koch_d c * (1 / 4) ^ m := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hr0.le,
        mul_comm (m : ℝ), Real.rpow_mul hr0.le, hrd, Real.rpow_natCast]
    have hE : (64 / c) ^ koch_d c * (c / 64) ^ koch_d c = 1 := by
      rw [← Real.mul_rpow (by positivity) (by positivity), div_mul_div_comm, mul_comm (64 : ℝ) c,
        div_self (by positivity), Real.one_rpow]
    calc t - s ≤ 8 / 4 ^ m := by
          rw [le_div_iff₀ h4m]
          linarith
      _ = 8 * (64 / c) ^ koch_d c * ((c / 64) ^ koch_d c * (1 / 4) ^ m) := by
        rw [show (8 : ℝ) * (64 / c) ^ koch_d c * ((c / 64) ^ koch_d c * (1 / 4) ^ m) =
          8 * ((64 / c) ^ koch_d c * (c / 64) ^ koch_d c) * (1 / 4) ^ m by ring, hE, one_div_pow]
        ring
      _ ≤ 8 * (64 / c) ^ koch_d c * ‖γ s - γ t‖ ^ koch_d c := by
        rw [← hC]
        exact mul_le_mul_of_nonneg_left hB (by positivity)
  refine ⟨(8 * (64 / c) ^ koch_d c).toNNReal, fun s hs t ht => ?_⟩
  rw [Real.coe_toNNReal _ hd0, edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg hd0]
  change ENNReal.ofReal (dist s t) ≤
    ENNReal.ofReal (8 * (64 / c) ^ koch_d c) * ENNReal.ofReal (dist (γ s) (γ t) ^ koch_d c)
  rw [← ENNReal.ofReal_mul (p := 8 * (64 / c) ^ koch_d c) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.dist_eq, dist_eq_norm]
  rcases lt_trichotomy s t with h | h | h
  · rw [abs_of_neg (by linarith), neg_sub]
    exact key s hs t ht h
  · rw [h, sub_self, abs_zero]
    positivity
  · rw [abs_of_pos (by linarith), norm_sub_rev]
    exact key t ht s hs h

/-- K2. The arc is injective on `[0, 1]`.
Truth: in the co-Hölder estimate, `γ s = γ t` gives `edist s t ≤ C · 0 ^ d = 0` (`d > 0`). -/
theorem koch_injOn {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) {γ : ℝ → ℂ} (hγ : koch_IsArc c γ) :
    InjOn γ (Icc 0 1) := by
  obtain ⟨C, hC⟩ := koch_coHolder hc0 hc1 hγ
  have hd1 := koch_d_gt_one hc0 hc1
  have hd : (0 : ℝ) < ((koch_d c).toNNReal : ℝ) := by
    rw [Real.coe_toNNReal _ (by linarith)]
    linarith
  intro s hs t ht hst
  have h0 := hC s hs t ht
  rw [hst, edist_self, ENNReal.zero_rpow_of_pos hd, mul_zero, nonpos_iff_eq_zero, edist_eq_zero] at h0
  exact h0

/-- The tent `t ↦ t - i min(t, 1 - t)`: from `0` down to `(1 - i)/2` and back up to `1`, below the real axis. -/
def koch_tent (t : ℝ) : ℂ := (t : ℂ) - ((min t (1 - t) : ℝ) : ℂ) * I

/-- The closed curve: the Koch arc above `[0, 1]` and the tent below it. -/
def koch_curve (γ : ℝ → ℂ) : Set ℂ := γ '' Icc 0 1 ∪ koch_tent '' Icc 0 1

/-- A loop through the curve: the Koch arc on `[0, 1/2]`, then the tent backwards on `[1/2, 1]`. -/
def koch_loop (γ : ℝ → ℂ) (t : ℝ) : ℂ := if t ≤ 1 / 2 then γ (2 * t) else koch_tent (2 - 2 * t)

/-- The tent is continuous, runs from `0` to `1`, and has `Re (tent t) = t`, `Im (tent t) = -min(t, 1 - t)`. -/
theorem koch_tent_facts : Continuous koch_tent ∧ koch_tent 0 = 0 ∧ koch_tent 1 = 1 ∧
    ∀ t : ℝ, (koch_tent t).re = t ∧ (koch_tent t).im = -min t (1 - t) := by
  refine ⟨?_, by simp [koch_tent], by simp [koch_tent], fun t => ⟨by simp [koch_tent], by simp [koch_tent]⟩⟩
  unfold koch_tent
  fun_prop

/-- K3. The tent is of bounded turning: `diam (tent [u, v]) ≤ 2 ‖tent u - tent v‖`.
Truth: `Re (tent t) = t` gives `‖tent u - tent v‖ ≥ v - u`, and the tent is `√2`-Lipschitz. -/
theorem koch_tent_bt {u v : ℝ} (huv : u ≤ v) :
    diam (koch_tent '' Icc u v) ≤ 2 * ‖koch_tent u - koch_tent v‖ := by
  have hri := koch_tent_facts.2.2.2
  have hre : ∀ a b : ℝ, (koch_tent a - koch_tent b).re = a - b := fun a b => by
    rw [Complex.sub_re, (hri a).1, (hri b).1]
  have him : ∀ a b : ℝ, (koch_tent a - koch_tent b).im = min b (1 - b) - min a (1 - a) := fun a b => by
    rw [Complex.sub_im, (hri a).2, (hri b).2]
    ring
  have hlow : v - u ≤ ‖koch_tent u - koch_tent v‖ := by
    rw [norm_sub_rev]
    have h := Complex.re_le_norm (koch_tent v - koch_tent u)
    rwa [hre] at h
  have hlip : ∀ a b : ℝ, ‖koch_tent a - koch_tent b‖ ≤ 2 * |a - b| := fun a b => by
    have hm : |min b (1 - b) - min a (1 - a)| ≤ |a - b| := by
      calc |min b (1 - b) - min a (1 - a)| ≤ max |b - a| |1 - b - (1 - a)| := abs_min_sub_min_le_max _ _ _ _
        _ = |a - b| := by rw [show 1 - b - (1 - a) = a - b by ring, abs_sub_comm, max_self]
    calc ‖koch_tent a - koch_tent b‖ ≤ |(koch_tent a - koch_tent b).re| + |(koch_tent a - koch_tent b).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ |a - b| + |a - b| := by
          rw [hre, him]
          linarith
      _ = 2 * |a - b| := by ring
  refine (diam_le_of_forall_dist_le (mul_nonneg zero_le_two (sub_nonneg.2 huv)) ?_).trans (by linarith)
  rintro _ ⟨a, ⟨ha1, ha2⟩, rfl⟩ _ ⟨b, ⟨hb1, hb2⟩, rfl⟩
  rw [dist_eq_norm]
  have hab : |a - b| ≤ v - u := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  linarith [hlip a b]

/-- K3. The tent is strictly below the real axis except at its ends: `Im (tent t) < 0` for `0 < t < 1`.
Truth: `Im (tent t) = -min(t, 1 - t)` and `min(t, 1 - t) > 0` on `(0, 1)`. -/
theorem koch_tent_im_neg {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : (koch_tent t).im < 0 := by
  rw [(koch_tent_facts.2.2.2 t).2, neg_lt_zero]
  exact lt_min ht0 (by linarith)

/-- K3. The Koch arc and the tent meet exactly in their common ends: `γ [0, 1] ∩ tent [0, 1] = {0, 1}`.
Truth: `γ ⊆ T ⊆ {Im ≥ 0}` (the arc does touch `ℝ`, e.g. at `r, r², 1 - r`), while `Im (tent t) < 0` on `(0, 1)`
(`koch_tent_im_neg`); `γ 0 = 0 = tent 0` and `γ 1 = 1 = tent 1`. -/
theorem koch_arc_inter_tent {c : ℝ} {γ : ℝ → ℂ} (hγ : koch_IsArc c γ) :
    γ '' Icc 0 1 ∩ koch_tent '' Icc 0 1 = {0, 1} := by
  obtain ⟨-, ht0, ht1, -⟩ := koch_tent_facts
  ext p
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, ⟨t, ht, htu⟩⟩
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0, ht0] at htu
      exact Or.inl htu.symm
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · rw [h1, ht1] at htu
      exact Or.inr htu.symm
    · have h := koch_tent_im_neg h0 h1
      rw [htu] at h
      exact absurd (hγ.2.2.2.2 u hu).1 (not_le.2 h)
  · rintro (rfl | rfl)
    · exact ⟨⟨0, ⟨le_rfl, zero_le_one⟩, hγ.2.1⟩, ⟨0, ⟨le_rfl, zero_le_one⟩, ht0⟩⟩
    · exact ⟨⟨1, ⟨zero_le_one, le_rfl⟩, hγ.2.2.1⟩, ⟨1, ⟨zero_le_one, le_rfl⟩, ht1⟩⟩

/-- K3. `koch_loop γ` is a Jordan loop through the curve.
Truth: the pieces meet at `γ 1 = 1 = tent 1` and `γ 0 = 0 = tent 0`; injective on `[0, 1)` since `γ` is injective
(`koch_injOn`), the tent is a graph, and the two meet only at `0, 1` (`koch_arc_inter_tent`). -/
theorem koch_loop_props {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) {γ : ℝ → ℂ} (hγ : koch_IsArc c γ) :
    ContinuousOn (koch_loop γ) (Icc 0 1) ∧ InjOn (koch_loop γ) (Ico 0 1) ∧ koch_loop γ 0 = koch_loop γ 1 ∧
      koch_loop γ '' Icc 0 1 = koch_curve γ := by
  obtain ⟨htc, ht0, ht1, hri⟩ := koch_tent_facts
  have hinj := koch_injOn hc0 hc1 hγ
  have hL : ∀ t : ℝ, t ≤ 1 / 2 → koch_loop γ t = γ (2 * t) := fun t ht => ite_eq_left ht
  have hR : ∀ t : ℝ, 1 / 2 < t → koch_loop γ t = koch_tent (2 - 2 * t) := fun t ht => ite_eq_right (not_le.2 ht)
  have hmid : koch_loop γ (1 / 2) = koch_tent (2 - 2 * (1 / 2)) := by
    rw [hL _ le_rfl, show (2 : ℝ) * (1 / 2) = 1 by norm_num, show (2 : ℝ) - 1 = 1 by norm_num, hγ.2.2.1, ht1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Icc_union_Icc_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · have h1 : ContinuousOn (fun t : ℝ => γ (2 * t)) (Icc 0 (1 / 2)) :=
        hγ.1.comp (f := fun t : ℝ => 2 * t) (by fun_prop) fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
      exact h1.congr fun t ht => hL t ht.2
    · have h2 : ContinuousOn (fun t : ℝ => koch_tent (2 - 2 * t)) (Icc (1 / 2) 1) :=
        (htc.comp (f := fun t : ℝ => 2 - 2 * t) (by fun_prop)).continuousOn
      refine h2.congr fun t ht => ?_
      rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h]
        exact hmid
      · exact hR t h
  · intro a ha b hb hab
    by_cases ha2 : a ≤ 1 / 2 <;> by_cases hb2 : b ≤ 1 / 2
    · rw [hL a ha2, hL b hb2] at hab
      have := hinj ⟨by linarith [ha.1], by linarith⟩ ⟨by linarith [hb.1], by linarith⟩ hab
      linarith
    · rw [hL a ha2, hR b (not_le.1 hb2)] at hab
      have h := koch_tent_im_neg (t := 2 - 2 * b) (by linarith [hb.2]) (by linarith [not_le.1 hb2])
      rw [← hab] at h
      exact absurd (hγ.2.2.2.2 (2 * a) ⟨by linarith [ha.1], by linarith⟩).1 (not_le.2 h)
    · rw [hR a (not_le.1 ha2), hL b hb2] at hab
      have h := koch_tent_im_neg (t := 2 - 2 * a) (by linarith [ha.2]) (by linarith [not_le.1 ha2])
      rw [hab] at h
      exact absurd (hγ.2.2.2.2 (2 * b) ⟨by linarith [hb.1], by linarith⟩).1 (not_le.2 h)
    · rw [hR a (not_le.1 ha2), hR b (not_le.1 hb2)] at hab
      have h := congrArg Complex.re hab
      rw [(hri _).1, (hri _).1] at h
      linarith
  · rw [hL 0 (by norm_num), hR 1 (by norm_num), mul_zero, hγ.2.1, show (2 : ℝ) - 2 * 1 = 0 by norm_num, ht0]
  · ext p
    constructor
    · rintro ⟨t, ht, rfl⟩
      by_cases h : t ≤ 1 / 2
      · exact Or.inl ⟨2 * t, ⟨by linarith [ht.1], by linarith⟩, (hL t h).symm⟩
      · exact Or.inr ⟨2 - 2 * t, ⟨by linarith [ht.2], by linarith [not_le.1 h]⟩, (hR t (not_le.1 h)).symm⟩
    · rintro (⟨u, hu, rfl⟩ | ⟨v, hv, rfl⟩)
      · refine ⟨u / 2, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
        rw [hL _ (by linarith [hu.2]), show 2 * (u / 2) = u by ring]
      · rcases eq_or_lt_of_le hv.2 with h | h
        · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
          rw [hmid, h]
          norm_num
        · refine ⟨1 - v / 2, ⟨by linarith, by linarith [hv.1]⟩, ?_⟩
          rw [hR _ (by linarith), show 2 - 2 * (1 - v / 2) = v by ring]

/-- K3. The curve is a Jordan curve.
Truth: `isJordanCurve_of_loop` applied to `koch_loop γ` (`koch_loop_props`). -/
theorem koch_isJordanCurve {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) {γ : ℝ → ℂ} (hγ : koch_IsArc c γ) :
    IsJordanCurve (toExt (koch_curve γ)) := by
  obtain ⟨h1, h2, h3, h4⟩ := koch_loop_props hc0 hc1 hγ
  rw [← h4]
  exact isJordanCurve_of_loop h1 h2 h3

/-- In a Jordan loop `F` (`0 ≤ a < b < 1`), a common point `F u = F v` of `F [a, b]` and `F ([0, a] ∪ [b, 1])` is
`F a` or `F b`. -/
theorem koch_loop_split {F : ℝ → ℂ} (hinj : InjOn F (Ico 0 1)) (h01 : F 0 = F 1) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < 1) {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc 0 a ∪ Icc b 1) (huv : F u = F v) :
    F u = F a ∨ F u = F b := by
  have hu' : u ∈ Ico (0 : ℝ) 1 := ⟨ha.trans hu.1, lt_of_le_of_lt hu.2 hb⟩
  rcases hv with hv | hv
  · have h := hinj hu' ⟨hv.1, by linarith [hv.2]⟩ huv
    left
    rw [show u = a by linarith [hu.1, hv.2]]
  · rcases eq_or_lt_of_le hv.2 with h1 | h1
    · rw [h1, ← h01] at huv
      have h := hinj hu' ⟨le_rfl, zero_lt_one⟩ huv
      left
      rw [show u = a by linarith [hu.1]]
    · have h := hinj hu' ⟨by linarith [hv.1], h1⟩ huv
      right
      rw [show u = b by linarith [hu.2, hv.1]]

/-- In a Jordan loop `F` (`0 ≤ a < b < 1`), every component of `F [0, 1] ∖ {F a, F b}` lies in `F [a, b]` or in
`F ([0, a] ∪ [b, 1])`: both are compact, they cover, and they meet only in `{F a, F b}`. -/
theorem koch_component_cases {F : ℝ → ℂ} (hF : ContinuousOn F (Icc 0 1)) (hinj : InjOn F (Ico 0 1))
    (h01 : F 0 = F 1) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) (q : ExtPlane) :
    connectedComponentIn (toExt (F '' Icc 0 1) \ {(F a : ExtPlane), (F b : ExtPlane)}) q ⊆ toExt (F '' Icc a b) ∨
      connectedComponentIn (toExt (F '' Icc 0 1) \ {(F a : ExtPlane), (F b : ExtPlane)}) q ⊆
        toExt (F '' (Icc 0 a ∪ Icc b 1)) := by
  have hAc : IsClosed (toExt (F '' Icc a b)) :=
    ((isCompact_Icc.image_of_continuousOn (hF.mono (Icc_subset_Icc ha hb.le))).image
      OnePoint.continuous_coe).isClosed
  have hBc : IsClosed (toExt (F '' (Icc 0 a ∪ Icc b 1))) :=
    (((isCompact_Icc.union isCompact_Icc).image_of_continuousOn
      (hF.mono (union_subset (Icc_subset_Icc le_rfl (by linarith)) (Icc_subset_Icc (by linarith) le_rfl)))).image
      OnePoint.continuous_coe).isClosed
  have hKX := connectedComponentIn_subset (toExt (F '' Icc 0 1) \ {(F a : ExtPlane), (F b : ExtPlane)}) q
  refine isPreconnected_iff_subset_of_disjoint_closed.1 isPreconnected_connectedComponentIn _ _ hAc hBc ?_ ?_
  · intro p hp
    obtain ⟨⟨x, ⟨u, hu, rfl⟩, rfl⟩, -⟩ := hKX hp
    by_cases h1 : u ∈ Icc a b
    · exact Or.inl (coe_mem_toExt_iff.2 (mem_image_of_mem F h1))
    · refine Or.inr (coe_mem_toExt_iff.2 (mem_image_of_mem F ?_))
      rcases not_and_or.1 h1 with h | h
      · exact Or.inl ⟨hu.1, by linarith [not_le.1 h]⟩
      · exact Or.inr ⟨by linarith [not_le.1 h], hu.2⟩
  · refine eq_empty_iff_forall_notMem.2 fun p hp => ?_
    obtain ⟨hpK, ⟨x, ⟨u, hu, rfl⟩, rfl⟩, ⟨y, ⟨v, hv, rfl⟩, hxy⟩⟩ := hp
    have hX := hKX hpK
    rcases koch_loop_split hinj h01 ha hab hb hu hv (OnePoint.coe_injective hxy).symm with h | h
    · exact hX.2 (Or.inl (show ((F u : ℂ) : ExtPlane) = (F a : ExtPlane) by rw [h]))
    · exact hX.2 (Or.inr (show ((F u : ℂ) : ExtPlane) = (F b : ExtPlane) by rw [h]))

/-- K3. In a Jordan loop `F`, the component of `C ∖ {F a, F b}` (`C = F [0, 1]`, `0 ≤ a < b < 1`) through a point
of `F (a, b)` stays in `F [a, b]`.
Truth: `F [a, b]` and `F ([0, a] ∪ [b, 1])` are compact, cover `C`, and meet only in `{F a, F b}` (injectivity on
`[0, 1)` and `F 0 = F 1`), so the component, preconnected in `C ∖ {F a, F b}`, lies in one of them. -/
theorem koch_component_inner {F : ℝ → ℂ} (hF : ContinuousOn F (Icc 0 1)) (hinj : InjOn F (Ico 0 1))
    (h01 : F 0 = F 1) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) {p : ExtPlane}
    (hp : p ∈ toExt (F '' Ioo a b)) :
    connectedComponentIn (toExt (F '' Icc 0 1) \ {(F a : ExtPlane), (F b : ExtPlane)}) p ⊆
      toExt (F '' Icc a b) := by
  obtain ⟨x, ⟨w, hw, rfl⟩, rfl⟩ := hp
  have hwI : w ∈ Ico (0 : ℝ) 1 := ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hpX : ((F w : ℂ) : ExtPlane) ∈ toExt (F '' Icc 0 1) \ {(F a : ExtPlane), (F b : ExtPlane)} := by
    refine ⟨coe_mem_toExt_iff.2 (mem_image_of_mem F ⟨hwI.1, hwI.2.le⟩), ?_⟩
    rintro (h | h)
    · have := hinj hwI ⟨ha, by linarith⟩ (OnePoint.coe_injective h)
      linarith [hw.1]
    · have := hinj hwI ⟨by linarith, hb⟩ (OnePoint.coe_injective h)
      linarith [hw.2]
  rcases koch_component_cases hF hinj h01 ha hab hb (F w : ExtPlane) with h | h
  · exact h
  · exfalso
    obtain ⟨y, ⟨v, hv, rfl⟩, hxy⟩ := h (mem_connectedComponentIn hpX)
    have hFvw := OnePoint.coe_injective hxy
    rcases koch_loop_split hinj h01 ha hab hb ⟨hw.1.le, hw.2.le⟩ hv hFvw.symm with h' | h'
    · exact hpX.2 (Or.inl (show ((F w : ℂ) : ExtPlane) = (F a : ExtPlane) by rw [h']))
    · exact hpX.2 (Or.inr (show ((F w : ℂ) : ExtPlane) = (F b : ExtPlane) by rw [h']))

/-- K3. In a Jordan loop `F`, the component of `C ∖ {F a, F b}` through a point of `F ([0, a) ∪ (b, 1))` stays in
`F ([0, a] ∪ [b, 1])`.
Truth: the same clopen decomposition as `koch_component_inner`. -/
theorem koch_component_outer {F : ℝ → ℂ} (hF : ContinuousOn F (Icc 0 1)) (hinj : InjOn F (Ico 0 1))
    (h01 : F 0 = F 1) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) {p : ExtPlane}
    (hp : p ∈ toExt (F '' (Ico 0 a ∪ Ioo b 1))) :
    connectedComponentIn (toExt (F '' Icc 0 1) \ {(F a : ExtPlane), (F b : ExtPlane)}) p ⊆
      toExt (F '' (Icc 0 a ∪ Icc b 1)) := by
  obtain ⟨x, ⟨w, hw, rfl⟩, rfl⟩ := hp
  have hwI : w ∈ Ico (0 : ℝ) 1 := by
    rcases hw with hw | hw
    · exact ⟨hw.1, by linarith [hw.2]⟩
    · exact ⟨by linarith [hw.1], hw.2⟩
  have hw' : w ∈ Icc 0 a ∪ Icc b 1 := by
    rcases hw with hw | hw
    · exact Or.inl ⟨hw.1, hw.2.le⟩
    · exact Or.inr ⟨hw.1.le, hw.2.le⟩
  have hpX : ((F w : ℂ) : ExtPlane) ∈ toExt (F '' Icc 0 1) \ {(F a : ExtPlane), (F b : ExtPlane)} := by
    refine ⟨coe_mem_toExt_iff.2 (mem_image_of_mem F ⟨hwI.1, hwI.2.le⟩), ?_⟩
    rintro (h | h)
    · have := hinj hwI ⟨ha, by linarith⟩ (OnePoint.coe_injective h)
      rcases hw with hw | hw <;> linarith [hw.1, hw.2]
    · have := hinj hwI ⟨by linarith, hb⟩ (OnePoint.coe_injective h)
      rcases hw with hw | hw <;> linarith [hw.1, hw.2]
  rcases koch_component_cases hF hinj h01 ha hab hb (F w : ExtPlane) with h | h
  · exfalso
    obtain ⟨y, ⟨v, hv, rfl⟩, hxy⟩ := h (mem_connectedComponentIn hpX)
    have hFvw := OnePoint.coe_injective hxy
    rcases koch_loop_split hinj h01 ha hab hb hv hw' hFvw with h' | h'
    · exact hpX.2 (Or.inl (show ((F w : ℂ) : ExtPlane) = (F a : ExtPlane) by rw [← hFvw, h']))
    · exact hpX.2 (Or.inr (show ((F w : ℂ) : ExtPlane) = (F b : ExtPlane) by rw [← hFvw, h']))
  · exact h

/-- K3. The triangle and the first half of the tent are separated by an angle at `0`, globally:
`(‖z‖ + ‖tent t‖)/8 ≤ ‖z - tent t‖` for EVERY `z ∈ T` and `t ∈ [0, 1/2]` (so also for `z` far from `0`).
Truth: the global linear functional `L = Im + Re/3` is `≥ |z|/6` on all of `T` and `≤ -(1/3) |tent t|` on the whole
first half of the tent, and `|L v| ≤ (4/3) |v|`. -/
theorem koch_mixed_zero {z : ℂ} (hz : z ∈ koch_T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    (‖z‖ + ‖koch_tent t‖) / 8 ≤ ‖z - koch_tent t‖ := by
  obtain ⟨hz0, hz1, hz2⟩ := hz
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨hre, him⟩ := koch_tent_facts.2.2.2 t
  rw [min_eq_left (by linarith)] at him
  have hzn : ‖z‖ ≤ 2 * z.re := by
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im _
      _ = z.re + z.im := by rw [abs_of_nonneg (by linarith), abs_of_nonneg hz0]
      _ ≤ 2 * z.re := by linarith
  have htn : ‖koch_tent t‖ ≤ 2 * t := by
    calc ‖koch_tent t‖ ≤ |(koch_tent t).re| + |(koch_tent t).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = 2 * t := by
        rw [hre, him, abs_neg, abs_of_nonneg ht0]
        ring
  have h1 := Complex.re_le_norm (z - koch_tent t)
  have h2 := Complex.im_le_norm (z - koch_tent t)
  rw [Complex.sub_re, hre] at h1
  rw [Complex.sub_im, him] at h2
  linarith

/-- K3. The triangle and the second half of the tent are separated by an angle at `1`, globally:
`(‖z - 1‖ + ‖tent t - 1‖)/8 ≤ ‖z - tent t‖` for EVERY `z ∈ T` and `t ∈ [1/2, 1]`.
Truth: the mirror image `w ↦ 1 - w̄` of `koch_mixed_zero` (it preserves `T` and maps the tent onto itself). -/
theorem koch_mixed_one {z : ℂ} (hz : z ∈ koch_T) {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    (‖z - 1‖ + ‖koch_tent t - 1‖) / 8 ≤ ‖z - koch_tent t‖ := by
  obtain ⟨hz0, hz1, hz2⟩ := hz
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨hre, him⟩ := koch_tent_facts.2.2.2 t
  rw [min_eq_right (by linarith)] at him
  have hzn : ‖z - 1‖ ≤ 2 * (1 - z.re) := by
    calc ‖z - 1‖ ≤ |(z - 1).re| + |(z - 1).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = (1 - z.re) + z.im := by
        rw [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero,
          abs_of_nonpos (by linarith), abs_of_nonneg hz0]
        ring
      _ ≤ 2 * (1 - z.re) := by linarith
  have htn : ‖koch_tent t - 1‖ ≤ 2 * (1 - t) := by
    calc ‖koch_tent t - 1‖ ≤ |(koch_tent t - 1).re| + |(koch_tent t - 1).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = 2 * (1 - t) := by
        rw [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero, hre, him, abs_neg,
          abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
        ring
  have h1 := neg_le_abs (z - koch_tent t).re
  have h1' := Complex.abs_re_le_norm (z - koch_tent t)
  have h2 := Complex.im_le_norm (z - koch_tent t)
  rw [Complex.sub_re, hre] at h1 h1'
  rw [Complex.sub_im, him] at h2
  linarith

/-- K3. The curve is of bounded turning with constant `64/c`.
Truth: write `z₁ = F a`, `z₂ = F b` (`F = koch_loop γ`, `0 ≤ a < b < 1`) and take the component through the interior
point `F ((a + b)/2)` (inner sub-arc) or `F ((b + 1)/2)` (outer sub-arc), bounded by `koch_component_inner`/`outer`.
Two arc points: `koch_arc_bt`.  Two tent points: `koch_tent_bt`.  An arc point `γ u` and a tent point `tent t`: the
sub-arc through the junction on the tent point's side (`0` if `t ≤ 1/2`, else `1`), of diameter
`≤ 8 ‖γ u - j‖ + 2 ‖tent t - j‖` (`koch_end_zero`/`koch_end_one`, `koch_tent_bt`), which the GLOBAL
`koch_mixed_zero`/`koch_mixed_one` bound by `64 ‖z₁ - z₂‖`; this covers the far and middle pairs too. -/
theorem koch_boundedTurning {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) {γ : ℝ → ℂ} (hγ : koch_IsArc c γ) :
    IsBoundedTurning (toExt (koch_curve γ)) (64 / c) := by
  obtain ⟨hFc, hFi, hF01, hFim⟩ := koch_loop_props hc0 hc1 hγ
  obtain ⟨htc, ht0, ht1, -⟩ := koch_tent_facts
  have hM1 : (1 : ℝ) ≤ 64 / c := by
    rw [le_div_iff₀ hc0]
    linarith
  have hM64 : (64 : ℝ) ≤ 64 / c := by
    rw [le_div_iff₀ hc0]
    nlinarith
  have hL : ∀ t : ℝ, t ≤ 1 / 2 → koch_loop γ t = γ (2 * t) := fun t ht => ite_eq_left ht
  have hR : ∀ t : ℝ, 1 / 2 ≤ t → koch_loop γ t = koch_tent (2 - 2 * t) := fun t ht => by
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, hL _ le_rfl, show (2 : ℝ) * (1 / 2) = 1 by norm_num, show (2 : ℝ) - 1 = 1 by norm_num,
        hγ.2.2.1, ht1]
    · exact ite_eq_right (not_le.2 h)
  have hbγ : ∀ x y : ℝ, 0 ≤ x → y ≤ 1 → Bornology.IsBounded (γ '' Icc x y) := fun x y hx hy =>
    koch_T_bounded.subset (koch_image_T hγ hx hy)
  have hbt : ∀ x y : ℝ, Bornology.IsBounded (koch_tent '' Icc x y) := fun x y =>
    (isCompact_Icc.image htc).isBounded
  have hfin : ∀ (a b : ℝ) (J : Set ℝ) (m : ℝ), 0 ≤ a → a < b → b < 1 → IsCompact J → J ⊆ Icc 0 1 →
      m ∈ J → m ∈ Ico (0 : ℝ) 1 → m ≠ a → m ≠ b →
      connectedComponentIn (toExt (koch_loop γ '' Icc 0 1) \
        {(koch_loop γ a : ExtPlane), (koch_loop γ b : ExtPlane)}) (koch_loop γ m : ExtPlane) ⊆
          toExt (koch_loop γ '' J) →
      diam (koch_loop γ '' J) ≤ 64 / c * ‖koch_loop γ a - koch_loop γ b‖ →
      ∃ p ∈ toExt (koch_loop γ '' Icc 0 1) \ {(koch_loop γ a : ExtPlane), (koch_loop γ b : ExtPlane)},
        extInf ∉ connectedComponentIn (toExt (koch_loop γ '' Icc 0 1) \
          {(koch_loop γ a : ExtPlane), (koch_loop γ b : ExtPlane)}) p ∧
        Metric.ediam {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt (koch_loop γ '' Icc 0 1) \
          {(koch_loop γ a : ExtPlane), (koch_loop γ b : ExtPlane)}) p} ≤
            ENNReal.ofReal (64 / c * ‖koch_loop γ a - koch_loop γ b‖) := by
    intro a b J m ha hab hb hJc hJ hmJ hmI hma hmb hK hD
    refine ⟨(koch_loop γ m : ExtPlane), ⟨coe_mem_toExt_iff.2 (mem_image_of_mem _ (hJ hmJ)), ?_⟩, ?_, ?_⟩
    · rintro (h | h)
      · exact hma (hFi hmI ⟨ha, by linarith⟩ (OnePoint.coe_injective h))
      · exact hmb (hFi hmI ⟨by linarith, hb⟩ (OnePoint.coe_injective h))
    · intro hinf
      obtain ⟨x, -, hx⟩ := hK hinf
      exact OnePoint.coe_ne_infty x hx
    · have hbdd : Bornology.IsBounded (koch_loop γ '' J) := (hJc.image_of_continuousOn (hFc.mono hJ)).isBounded
      exact (Metric.ediam_mono fun z hz => coe_mem_toExt_iff.1 (hK hz)).trans
        (Metric.ediam_le_of_forall_dist_le fun x hx y hy => (dist_le_diam_of_mem hbdd hx hy).trans hD)
  have core : ∀ a b : ℝ, 0 ≤ a → a < b → b < 1 →
      ∃ p ∈ toExt (koch_loop γ '' Icc 0 1) \ {(koch_loop γ a : ExtPlane), (koch_loop γ b : ExtPlane)},
        extInf ∉ connectedComponentIn (toExt (koch_loop γ '' Icc 0 1) \
          {(koch_loop γ a : ExtPlane), (koch_loop γ b : ExtPlane)}) p ∧
        Metric.ediam {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt (koch_loop γ '' Icc 0 1) \
          {(koch_loop γ a : ExtPlane), (koch_loop γ b : ExtPlane)}) p} ≤
            ENNReal.ofReal (64 / c * ‖koch_loop γ a - koch_loop γ b‖) := by
    intro a b ha hab hb
    have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
    have hend : (b + 1) / 2 ∈ Ioo b 1 := ⟨by linarith, by linarith⟩
    have hInner := hfin a b (Icc a b) ((a + b) / 2) ha hab hb isCompact_Icc (Icc_subset_Icc ha hb.le)
      ⟨hmid.1.le, hmid.2.le⟩ ⟨by linarith, by linarith⟩ (ne_of_gt hmid.1) (ne_of_lt hmid.2)
      (koch_component_inner hFc hFi hF01 ha hab hb (coe_mem_toExt_iff.2 (mem_image_of_mem _ hmid)))
    have hOuter := hfin a b (Icc 0 a ∪ Icc b 1) ((b + 1) / 2) ha hab hb (isCompact_Icc.union isCompact_Icc)
      (union_subset (Icc_subset_Icc le_rfl (by linarith)) (Icc_subset_Icc (by linarith) le_rfl))
      (Or.inr ⟨hend.1.le, hend.2.le⟩) ⟨by linarith, hend.2⟩ (ne_of_gt (show a < (b + 1) / 2 by linarith [hend.1]))
      (ne_of_gt hend.1)
      (koch_component_outer hFc hFi hF01 ha hab hb (coe_mem_toExt_iff.2 (mem_image_of_mem _ (Or.inr hend))))
    by_cases hb2 : b ≤ 1 / 2
    · apply hInner
      have hsub : koch_loop γ '' Icc a b ⊆ γ '' Icc (2 * a) (2 * b) := by
        rintro _ ⟨t, ht, rfl⟩
        exact ⟨2 * t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, (hL t (by linarith [ht.2])).symm⟩
      calc diam (koch_loop γ '' Icc a b) ≤ diam (γ '' Icc (2 * a) (2 * b)) :=
            diam_mono hsub (hbγ _ _ (by linarith) (by linarith))
        _ ≤ 64 / c * ‖γ (2 * a) - γ (2 * b)‖ :=
            koch_arc_bt hc0 hc1 hγ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
        _ = 64 / c * ‖koch_loop γ a - koch_loop γ b‖ := by rw [hL a (by linarith), hL b hb2]
    by_cases ha2 : 1 / 2 ≤ a
    · apply hInner
      have hsub : koch_loop γ '' Icc a b ⊆ koch_tent '' Icc (2 - 2 * b) (2 - 2 * a) := by
        rintro _ ⟨t, ht, rfl⟩
        exact ⟨2 - 2 * t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, (hR t (by linarith [ht.1])).symm⟩
      calc diam (koch_loop γ '' Icc a b) ≤ diam (koch_tent '' Icc (2 - 2 * b) (2 - 2 * a)) :=
            diam_mono hsub (hbt _ _)
        _ ≤ 2 * ‖koch_tent (2 - 2 * b) - koch_tent (2 - 2 * a)‖ := koch_tent_bt (by linarith)
        _ ≤ 64 / c * ‖koch_loop γ a - koch_loop γ b‖ := by
            rw [hR a ha2, hR b (by linarith), norm_sub_rev]
            linarith [mul_le_mul_of_nonneg_right hM64 (norm_nonneg (koch_tent (2 - 2 * a) - koch_tent (2 - 2 * b))),
              norm_nonneg (koch_tent (2 - 2 * a) - koch_tent (2 - 2 * b))]
    rw [not_le] at hb2 ha2
    have hFa : koch_loop γ a = γ (2 * a) := hL a ha2.le
    have hFb : koch_loop γ b = koch_tent (2 - 2 * b) := hR b hb2.le
    have hu : 2 * a ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hzT := hγ.2.2.2.2 (2 * a) hu
    by_cases hτ : 2 - 2 * b ≤ 1 / 2
    · apply hOuter
      have hsub : koch_loop γ '' (Icc 0 a ∪ Icc b 1) ⊆ γ '' Icc 0 (2 * a) ∪ koch_tent '' Icc 0 (2 - 2 * b) := by
        rintro _ ⟨t, ht | ht, rfl⟩
        · exact Or.inl ⟨2 * t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, (hL t (by linarith [ht.2])).symm⟩
        · exact Or.inr ⟨2 - 2 * t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, (hR t (by linarith [ht.1])).symm⟩
      have h0A : (0 : ℂ) ∈ γ '' Icc 0 (2 * a) := ⟨0, ⟨le_rfl, by linarith⟩, hγ.2.1⟩
      have h0B : (0 : ℂ) ∈ koch_tent '' Icc 0 (2 - 2 * b) := ⟨0, ⟨le_rfl, by linarith⟩, ht0⟩
      have hmix := koch_mixed_zero hzT (t := 2 - 2 * b) ⟨by linarith, hτ⟩
      calc diam (koch_loop γ '' (Icc 0 a ∪ Icc b 1)) ≤
            diam (γ '' Icc 0 (2 * a) ∪ koch_tent '' Icc 0 (2 - 2 * b)) :=
            diam_mono hsub ((hbγ _ _ le_rfl hu.2).union (hbt _ _))
        _ ≤ diam (γ '' Icc 0 (2 * a)) + diam (koch_tent '' Icc 0 (2 - 2 * b)) := diam_union' ⟨0, h0A, h0B⟩
        _ ≤ 8 * ‖γ (2 * a)‖ + 2 * ‖koch_tent 0 - koch_tent (2 - 2 * b)‖ :=
            add_le_add (koch_end_zero hc0 hc1 hγ hu) (koch_tent_bt (by linarith))
        _ ≤ 64 / c * ‖koch_loop γ a - koch_loop γ b‖ := by
            rw [ht0, zero_sub, norm_neg, hFa, hFb]
            linarith [mul_le_mul_of_nonneg_right hM64 (norm_nonneg (γ (2 * a) - koch_tent (2 - 2 * b))),
              norm_nonneg (koch_tent (2 - 2 * b))]
    · rw [not_le] at hτ
      apply hInner
      have hsub : koch_loop γ '' Icc a b ⊆ γ '' Icc (2 * a) 1 ∪ koch_tent '' Icc (2 - 2 * b) 1 := by
        rintro _ ⟨t, ht, rfl⟩
        by_cases h : t ≤ 1 / 2
        · exact Or.inl ⟨2 * t, ⟨by linarith [ht.1], by linarith⟩, (hL t h).symm⟩
        · exact Or.inr ⟨2 - 2 * t, ⟨by linarith [ht.2], by linarith [not_le.1 h]⟩,
            (hR t (not_le.1 h).le).symm⟩
      have h1A : (1 : ℂ) ∈ γ '' Icc (2 * a) 1 := ⟨1, ⟨hu.2, le_rfl⟩, hγ.2.2.1⟩
      have h1B : (1 : ℂ) ∈ koch_tent '' Icc (2 - 2 * b) 1 := ⟨1, ⟨by linarith, le_rfl⟩, ht1⟩
      have hmix := koch_mixed_one hzT (t := 2 - 2 * b) ⟨hτ.le, by linarith⟩
      calc diam (koch_loop γ '' Icc a b) ≤ diam (γ '' Icc (2 * a) 1 ∪ koch_tent '' Icc (2 - 2 * b) 1) :=
            diam_mono hsub ((hbγ _ _ hu.1 le_rfl).union (hbt _ _))
        _ ≤ diam (γ '' Icc (2 * a) 1) + diam (koch_tent '' Icc (2 - 2 * b) 1) := diam_union' ⟨1, h1A, h1B⟩
        _ ≤ 8 * ‖γ (2 * a) - 1‖ + 2 * ‖koch_tent (2 - 2 * b) - koch_tent 1‖ :=
            add_le_add (koch_end_one hc0 hc1 hγ hu) (koch_tent_bt (by linarith))
        _ ≤ 64 / c * ‖koch_loop γ a - koch_loop γ b‖ := by
            rw [ht1, hFa, hFb]
            linarith [mul_le_mul_of_nonneg_right hM64 (norm_nonneg (γ (2 * a) - koch_tent (2 - 2 * b))),
              norm_nonneg (koch_tent (2 - 2 * b) - 1)]
  refine ⟨koch_isJordanCurve hc0 hc1 hγ, hM1, ?_⟩
  intro z₁ z₂ hz₁ hz₂ hne
  rw [← hFim] at hz₁ hz₂ ⊢
  have hpar : ∀ z : ℂ, (z : ExtPlane) ∈ toExt (koch_loop γ '' Icc 0 1) →
      ∃ s ∈ Ico (0 : ℝ) 1, koch_loop γ s = z := by
    intro z hz
    obtain ⟨s, hs, hsz⟩ := coe_mem_toExt_iff.1 hz
    rcases eq_or_lt_of_le hs.2 with h | h
    · exact ⟨0, ⟨le_rfl, zero_lt_one⟩, by rw [hF01, ← h, hsz]⟩
    · exact ⟨s, ⟨hs.1, h⟩, hsz⟩
  obtain ⟨s₁, hs₁, rfl⟩ := hpar z₁ hz₁
  obtain ⟨s₂, hs₂, rfl⟩ := hpar z₂ hz₂
  rcases lt_trichotomy s₁ s₂ with h | h | h
  · exact core s₁ s₂ hs₁.1 h hs₂.2
  · exact absurd (congrArg (koch_loop γ) h) hne
  · obtain ⟨p, hp, h1, h2⟩ := core s₂ s₁ hs₂.1 h hs₁.2
    rw [pair_comm] at hp h1 h2
    rw [norm_sub_rev] at h2
    exact ⟨p, hp, h1, h2⟩

/-- K3. The curve is a quasicircle.
Truth: `thm18_1_quasicircle_of_boundedTurning` (Ahlfors) with `M = 64/c ≥ 1`. -/
theorem koch_quasicircle {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) {γ : ℝ → ℂ} (hγ : koch_IsArc c γ) :
    IsQuasicircle (toExt (koch_curve γ)) := by
  have hM : (1 : ℝ) ≤ 64 / c := by
    rw [le_div_iff₀ hc0]
    linarith
  obtain ⟨K, hK⟩ := thm18_1_quasicircle_of_boundedTurning hM
  exact ⟨K, hK _ (koch_boundedTurning hc0 hc1 hγ)⟩

/-- Co-Hölder parametrization ⇒ Hausdorff dimension lower bound (the s21r probe `h21r4_le_dimH_of_coHolder`). -/
theorem koch_le_dimH_of_coHolder {γ : ℝ → ℂ} {c d : ℝ≥0} (hd : 0 < d)
    (h : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      edist s t ≤ (c : ℝ≥0∞) * edist (γ s) (γ t) ^ (d : ℝ)) :
    (d : ℝ≥0∞) ≤ dimH (γ '' Icc (0 : ℝ) 1) := by
  have hinj : InjOn γ (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    have h0 := h s hs t ht
    rw [hst, edist_self, ENNReal.zero_rpow_of_pos (by exact_mod_cast hd), mul_zero,
      nonpos_iff_eq_zero, edist_eq_zero] at h0
    exact h0
  set g := Function.invFunOn γ (Icc (0 : ℝ) 1) with hg
  have hleft : LeftInvOn g γ (Icc (0 : ℝ) 1) := hinj.leftInvOn_invFunOn
  have hH : HolderOnWith c d g (γ '' Icc (0 : ℝ) 1) := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    rw [hleft hs, hleft ht]
    exact h s hs t ht
  have himg : g '' (γ '' Icc (0 : ℝ) 1) = Icc (0 : ℝ) 1 := hleft.image_image
  have hdim := hH.dimH_image_le hd
  rw [himg, Real.dimH_of_nonempty_interior (by simp), Module.finrank_self, Nat.cast_one,
    ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hd.ne')) (Or.inl ENNReal.coe_ne_top),
    one_mul] at hdim
  exact hdim

/-- Transfer of the co-Hölder bound to the statement's set `{z | ↑z ∈ C}` (the s21r probe
`h21r4_statement_of_coHolder`). -/
theorem koch_statement_of_coHolder {C : Set ExtPlane} (hC : IsQuasicircle C)
    {γ : ℝ → ℂ} {c d : ℝ≥0} (hd : 0 < d)
    (h : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      edist s t ≤ (c : ℝ≥0∞) * edist (γ s) (γ t) ^ (d : ℝ))
    (hsub : ∀ t ∈ Icc (0 : ℝ) 1, ((γ t : ℂ) : ExtPlane) ∈ C)
    {ε : ℝ} (hdε : (2 : ℝ≥0∞) - ENNReal.ofReal ε < d) :
    ∃ C : Set ExtPlane, IsQuasicircle C ∧
      (2 : ℝ≥0∞) - ENNReal.ofReal ε < dimH {z : ℂ | (z : ExtPlane) ∈ C} := by
  refine ⟨C, hC, hdε.trans_le ((koch_le_dimH_of_coHolder hd h).trans (dimH_mono ?_))⟩
  rintro _ ⟨t, ht, rfl⟩
  exact hsub t ht

/-- K3. The parameter: for `ε > 0`, `c = min ε 1 · log 2 / 2 ∈ (0, 1/2]` has `2 - ε < d`.
Truth: `log (2 + 2c) ≤ log 2 + c`, so `d ≥ 2/(1 + min ε 1 / 2) > 2 - min ε 1`; for `ε ≥ 2` the left side is `0`. -/
theorem koch_param {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ (2 : ℝ≥0∞) - ENNReal.ofReal ε < ((koch_d c).toNNReal : ℝ≥0∞) := by
  have hm0 : 0 < min ε 1 := lt_min hε one_pos
  have hm1 : min ε 1 ≤ 1 := min_le_right _ _
  have hmε : min ε 1 ≤ ε := min_le_left _ _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) (by norm_num)
    linarith
  have hc0 : 0 < min ε 1 * Real.log 2 / 2 := by positivity
  have hc1 : min ε 1 * Real.log 2 / 2 ≤ 1 / 2 := by
    nlinarith [mul_le_mul hm1 hl2'.le hl2.le zero_le_one]
  refine ⟨min ε 1 * Real.log 2 / 2, hc0, hc1, ?_⟩
  have hd1 := koch_d_gt_one hc0 hc1
  have hlpos : 0 < Real.log (2 + 2 * (min ε 1 * Real.log 2 / 2)) := Real.log_pos (by linarith)
  have hlog : Real.log (2 + 2 * (min ε 1 * Real.log 2 / 2)) ≤ Real.log 2 + min ε 1 * Real.log 2 / 2 := by
    rw [show (2 : ℝ) + 2 * (min ε 1 * Real.log 2 / 2) = 2 * (1 + min ε 1 * Real.log 2 / 2) by ring,
      Real.log_mul (by norm_num) (by linarith)]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + min ε 1 * Real.log 2 / 2 by linarith)
    linarith
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul two_ne_zero two_ne_zero]
    ring
  have hd : 2 - ε < koch_d (min ε 1 * Real.log 2 / 2) := by
    rw [koch_d, lt_div_iff₀ hlpos, h4]
    rcases le_or_gt 2 ε with h2 | h2
    · nlinarith [mul_le_mul_of_nonneg_right (show 2 - ε ≤ 0 by linarith) hlpos.le]
    · have h5 := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 - ε by linarith)
      nlinarith [mul_nonneg hl2.le (sub_nonneg.2 hmε), mul_pos (mul_pos hε hm0) hl2]
  have e : (2 : ℝ≥0∞) - ENNReal.ofReal ε = ENNReal.ofReal (2 - ε) := by
    rw [ENNReal.ofReal_sub _ hε.le, ENNReal.ofReal_ofNat]
  rw [e]
  exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hd, by linarith⟩

/-- §16.1: there are quasicircles whose Hausdorff dimension is arbitrarily close to `2` (in
particular quasicircles need not be locally rectifiable). -/
theorem quasicircle_hausdorff_dim_near_two {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Set ExtPlane, IsQuasicircle C ∧
      (2 : ℝ≥0∞) - ENNReal.ofReal ε < dimH {z : ℂ | (z : ExtPlane) ∈ C} := by
  obtain ⟨c, hc0, hc1, hdim⟩ := koch_param hε
  obtain ⟨γ, hγ⟩ := koch_exists_arc hc0 hc1
  obtain ⟨C₀, hC₀⟩ := koch_coHolder hc0 hc1 hγ
  exact koch_statement_of_coHolder (koch_quasicircle hc0 hc1 hγ)
    (Real.toNNReal_pos.2 (zero_lt_one.trans (koch_d_gt_one hc0 hc1))) hC₀
    (fun t ht => ⟨γ t, Or.inl ⟨t, ht, rfl⟩, rfl⟩) hdim

end LiZhongQC
