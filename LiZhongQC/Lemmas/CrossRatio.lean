import LiZhongQC.Lemmas.Mobius

/-!
# The cross ratio and the normal-form parameter `k`

§3.1–3.4 of the Theorem 1.1 writeup (`proof in LZ.txt`).  These are the parts of the reduction
to the normal form `ℍ(-1/k, -1, 1, 1/k)` that need no imported facts: the cross-ratio
computation for the normal points, its strict monotonicity in `k`, and the fact that four reals
in increasing order have cross ratio `> 1`.

* `crossRatio`, `crossRatioR`            — §3.1
* `crossRatioR_normalPoints`             — Lemma 3.2, the computation `X = (1+k)²/(4k)`
* `normalParam_strictAntiOn`,
  `one_lt_normalParam`,
  `exists_unique_normalParam`            — Lemma 3.2, the bijection `(0,1) → (1,∞)`
* `one_lt_crossRatioR`                   — Lemma 3.3

Together these give Step 3 of Proposition 3.5: a quadruple of reals in increasing order
determines a unique `k ∈ (0,1)` with the same cross ratio as `(-1/k, -1, 1, 1/k)`.
-/

open Set

noncomputable section

namespace LiZhongQC

/-- §3.1: the cross ratio `X(a,b,c,d) = ((a-c)(b-d))/((a-d)(b-c))`. -/
def crossRatio (a b c d : ℂ) : ℂ := ((a - c) * (b - d)) / ((a - d) * (b - c))

/-- The cross ratio of four real points. -/
def crossRatioR (a b c d : ℝ) : ℝ := ((a - c) * (b - d)) / ((a - d) * (b - c))

theorem crossRatio_ofReal (a b c d : ℝ) :
    crossRatio (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) = ((crossRatioR a b c d : ℝ) : ℂ) := by
  simp only [crossRatio, crossRatioR, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub]

/-- §3.2: the parameter function `k ↦ (1+k)²/(4k)`. -/
def normalParam (k : ℝ) : ℝ := (1 + k) ^ 2 / (4 * k)

/-- **Lemma 3.2** (the computation): `X(-1/k, -1, 1, 1/k) = (1+k)²/(4k)`. -/
theorem crossRatioR_normalPoints {k : ℝ} (hk : 0 < k) :
    crossRatioR (-1 / k) (-1) 1 (1 / k) = normalParam k := by
  have hk0 : k ≠ 0 := hk.ne'
  unfold crossRatioR normalParam
  field_simp
  ring

/-- **Lemma 3.2** (monotonicity): `k ↦ (1+k)²/(4k)` is strictly decreasing on `(0,1)`.
The identity behind it is `4(k₂-k₁)(1-k₁k₂) > 0`. -/
theorem normalParam_strictAntiOn : StrictAntiOn normalParam (Ioo 0 1) := by
  rintro k₁ ⟨h₁, h₁'⟩ k₂ ⟨h₂, h₂'⟩ h
  unfold normalParam
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos (sub_pos.2 h) (show (0 : ℝ) < 1 - k₁ * k₂ by nlinarith)]

/-- **Lemma 3.2** (range): `(1+k)²/(4k) > 1` for `0 < k < 1`, since `(1+k)² - 4k = (1-k)²`. -/
theorem one_lt_normalParam {k : ℝ} (hk : 0 < k) (hk1 : k < 1) : 1 < normalParam k := by
  unfold normalParam
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [mul_pos (sub_pos.2 hk1) (sub_pos.2 hk1)]

theorem normalParam_one : normalParam 1 = 1 := by norm_num [normalParam]

theorem continuousOn_normalParam : ContinuousOn normalParam {x : ℝ | x ≠ 0} := by
  refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
  intro x hx
  simpa using hx

/-- **Lemma 3.2** (bijection): every `X > 1` is `(1+k)²/(4k)` for exactly one `k ∈ (0,1)`.
This is Step 3 of Proposition 3.5. -/
theorem exists_unique_normalParam {X : ℝ} (hX : 1 < X) :
    ∃! k : ℝ, k ∈ Ioo (0 : ℝ) 1 ∧ normalParam k = X := by
  have hX0 : 0 < X := lt_trans one_pos hX
  -- a point where the function exceeds `X`
  set c : ℝ := 1 / (4 * X) with hc_def
  have hc0 : 0 < c := by positivity
  have hc1 : c < 1 := by
    rw [hc_def, div_lt_one (by positivity)]; linarith
  have hXc : X < normalParam c := by
    have h4c : 4 * c = 1 / X := by rw [hc_def]; field_simp
    unfold normalParam
    rw [h4c, lt_div_iff₀ (by positivity)]
    have : (1 : ℝ) < (1 + c) ^ 2 := by nlinarith
    calc X * (1 / X) = 1 := by field_simp
      _ < (1 + c) ^ 2 := this
  -- the intermediate value theorem on `[c, 1]`
  have hcont : ContinuousOn normalParam (Icc c 1) := by
    refine continuousOn_normalParam.mono ?_
    intro x hx
    exact ne_of_gt (lt_of_lt_of_le hc0 hx.1)
  have hmem : X ∈ Icc (normalParam 1) (normalParam c) := by
    rw [normalParam_one]
    exact ⟨hX.le, hXc.le⟩
  obtain ⟨k, hk_mem, hk⟩ := intermediate_value_Icc' hc1.le hcont hmem
  have hk0 : 0 < k := lt_of_lt_of_le hc0 hk_mem.1
  have hk1 : k < 1 := by
    rcases lt_or_eq_of_le hk_mem.2 with h | h
    · exact h
    · rw [h, normalParam_one] at hk; exact absurd hk.symm (ne_of_gt hX)
  refine ⟨k, ⟨⟨hk0, hk1⟩, hk⟩, ?_⟩
  rintro m ⟨hm_mem, hm⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hlt := normalParam_strictAntiOn hm_mem ⟨hk0, hk1⟩ h
    rw [hk, hm] at hlt
    exact lt_irrefl X hlt
  · have hlt := normalParam_strictAntiOn ⟨hk0, hk1⟩ hm_mem h
    rw [hk, hm] at hlt
    exact lt_irrefl X hlt

/-- **Lemma 3.3**: four reals in increasing order have cross ratio `> 1`.
The denominator `(x₁-x₄)(x₂-x₃)` is a product of two negatives, and
`(x₁-x₃)(x₂-x₄) - (x₁-x₄)(x₂-x₃) = (x₃-x₄)(x₁-x₂) > 0`. -/
theorem one_lt_crossRatioR {x₁ x₂ x₃ x₄ : ℝ} (h₁₂ : x₁ < x₂) (h₂₃ : x₂ < x₃) (h₃₄ : x₃ < x₄) :
    1 < crossRatioR x₁ x₂ x₃ x₄ := by
  have hden : 0 < (x₁ - x₄) * (x₂ - x₃) :=
    mul_pos_of_neg_of_neg (by linarith) (by linarith)
  rw [crossRatioR, lt_div_iff₀ hden]
  nlinarith [mul_pos (show (0 : ℝ) < x₄ - x₃ by linarith)
    (show (0 : ℝ) < x₂ - x₁ by linarith)]

end LiZhongQC
