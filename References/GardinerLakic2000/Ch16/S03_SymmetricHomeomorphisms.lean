import References.GardinerLakic2000.Ch16.S02_PartialTopologicalGroups

/-!
# Gardiner–Lakic 2000, Ch. 16 §16.3 Symmetric homeomorphisms

Source `teichmuller.txt`, lines 12010–12084 (Chapter 16, §16.3).

* Definition 3 (vanishing ratio distortion; symmetric homeomorphisms, the group `S`, l. 12013–12019) —
  `HasVanishingRatioDistortion`
* Definition (the lift `h̃` of `h` to `ℝ`, (i)–(iii), l. 12020–12024) — `IsCircleLift`
* Unlabelled ((16.1) iff (16.2) for the lift, and vanishing ratio distortion iff for the lift, l. 12025–12031; used in
  Lemmas 3–4 and §16.6) — `para16_3_lift`
* Theorem 2 (l. 12033) — `thm16_2`
* Corollary 2 (l. 12036) — `cor16_2_2`
* Corollary 3 (l. 12039) — `cor16_2_3_a`, `cor16_2_3_b`
* Lemma 3 (l. 12046) — `lemma16_3`
* Lemma 4 (l. 12058) — `lemma16_4`

Not items: (16.3) and the proofs of Lemmas 3–4; the Remark on other smoothness classes (l. 12083). Modelling (E0.3):
QS is not given a group instance; "conjugation by `h` is continuous at the identity in QS" is
`∀ ε > 0, ∃ δ > 0, h ∘ U(δ) ∘ h⁻¹ ⊆ U(ε)` for batch E's `qsNbhdU`, for `h` and for `h⁻¹`; the characteristic
topological subgroup of QS (Theorem 2) is the set of such `h`. Corollary 2's "closed topological subgroup" is:
closed under composition and inversion, and closed for the right neighbourhoods `U(ε) ∘ h`. Corollary 3's "QS is not
a topological group" is the existence of a quasisymmetric `h` for which conjugation is not continuous at the
identity (Lemma 16.1 (iii) fails). The lift uses the covering `x ↦ e^{2πix}`; (16.2) is `LiZhongQC.IsQuasisymmetric`
(an increasing homeomorphism of `ℝ`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

/-- **Definition 3** (vanishing ratio distortion, §16.3, l. 12013). There is `ε(t) → 0` as `t → 0` (independent of `x`)
with (16.1) holding with `M = 1 + ε(t)`. A quasisymmetric map with this property is symmetric. -/
def HasVanishingRatioDistortion (h : ℂ → ℂ) : Prop :=
  ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧ ∀ x t : ℝ, 0 < t → t < 2 * π →
    1 / (1 + ε t) ≤ ‖h (exp ((x + t) * I)) - h (exp (x * I))‖ / ‖h (exp (x * I)) - h (exp ((x - t) * I))‖ ∧
      ‖h (exp ((x + t) * I)) - h (exp (x * I))‖ / ‖h (exp (x * I)) - h (exp ((x - t) * I))‖ ≤ 1 + ε t

/-- **Definition** (the lift, §16.3, l. 12020–12024). `h̃` is the increasing lift of the orientation-preserving
circle homeomorphism `h` through `π(x) = e^{2πix}`: `0 ≤ h̃(0) < 1`, `h̃(x + 1) = h̃(x) + 1`, `π ∘ h̃ = h ∘ π`. -/
def IsCircleLift (h : ℂ → ℂ) (hl : ℝ → ℝ) : Prop :=
  Continuous hl ∧ StrictMono hl ∧ 0 ≤ hl 0 ∧ hl 0 < 1 ∧ (∀ x, hl (x + 1) = hl x + 1) ∧
    ∀ x : ℝ, exp (2 * π * I * hl x) = h (exp (2 * π * I * x))

/-- Helper for `cor16_2_3_b` (§16.3). The derivative of a lift (`h̃(x + 1) = h̃(x) + 1`) is `1`-periodic. -/
theorem gl16_deriv_periodic {hl : ℝ → ℝ} (hper : ∀ x, hl (x + 1) = hl x + 1) : Function.Periodic (deriv hl) 1 := by
  intro x
  rw [← deriv_comp_add_const hl 1 x]
  have h2 : (fun y => hl (y + 1)) = fun y => hl y + 1 := funext hper
  rw [h2, deriv_add_const]

/-- Helper for `cor16_2_3_b` (§16.3). A `C¹` lift with positive derivative has its derivative between two positive
constants (compactness of `[0, 1]` and periodicity). -/
theorem gl16_deriv_bounds {hl : ℝ → ℝ} (hC1 : ContDiff ℝ 1 hl) (hpos : ∀ x, 0 < deriv hl x)
    (hper : ∀ x, hl (x + 1) = hl x + 1) : ∃ m M : ℝ, 0 < m ∧ ∀ x, m ≤ deriv hl x ∧ deriv hl x ≤ M := by
  have hc : Continuous (deriv hl) := hC1.continuous_deriv le_rfl
  obtain ⟨a, -, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (zero_le_one' ℝ)) hc.continuousOn
  obtain ⟨b, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (zero_le_one' ℝ)) hc.continuousOn
  refine ⟨deriv hl a, deriv hl b, hpos a, fun x => ?_⟩
  have hx : deriv hl (Int.fract x) = deriv hl x := by
    have := (gl16_deriv_periodic hper).sub_int_mul_eq (x := x) ⌊x⌋
    rw [mul_one] at this
    exact this
  have hmem : Int.fract x ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  rw [← hx]
  exact ⟨hmin hmem, hmax hmem⟩

/-- Helper for `cor16_2_3_b` (§16.3). Increments of `h̃` from the bounds of its derivative (mean value theorem). -/
theorem gl16_incr {hl : ℝ → ℝ} (hC1 : ContDiff ℝ 1 hl) {m M : ℝ} (hb : ∀ x, m ≤ deriv hl x ∧ deriv hl x ≤ M)
    {a b : ℝ} (hab : a < b) : m * (b - a) ≤ hl b - hl a ∧ hl b - hl a ≤ M * (b - a) := by
  have hd : Differentiable ℝ hl := hC1.differentiable one_ne_zero
  obtain ⟨c, -, hc⟩ := exists_deriv_eq_slope hl hab hd.continuous.continuousOn hd.differentiableOn
  have hba : 0 < b - a := sub_pos.2 hab
  rw [eq_div_iff hba.ne'] at hc
  have h1 := hb c
  constructor <;> nlinarith

/-- Helper for `cor16_2_3_b` (§16.3). The derivative of a `C¹` lift is uniformly continuous on `ℝ` (Heine–Cantor
on `[−1, 2]` and periodicity). -/
theorem gl16_deriv_uc {hl : ℝ → ℝ} (hC1 : ContDiff ℝ 1 hl) (hper : ∀ x, hl (x + 1) = hl x + 1) {η : ℝ}
    (hη : 0 < η) : ∃ δ > 0, ∀ a b : ℝ, |a - b| < δ → |deriv hl a - deriv hl b| < η := by
  have hc : Continuous (deriv hl) := hC1.continuous_deriv le_rfl
  have huc := (isCompact_Icc (a := (-1 : ℝ)) (b := 2)).uniformContinuousOn_of_continuous hc.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc η hη
  refine ⟨min δ 1, lt_min hδ one_pos, fun a b hab => ?_⟩
  have hP := gl16_deriv_periodic hper
  have ha' := hP.sub_int_mul_eq (x := a) ⌊b⌋
  have hb' := hP.sub_int_mul_eq (x := b) ⌊b⌋
  rw [mul_one] at ha' hb'
  rw [← ha', ← hb']
  have hfl := Int.floor_le b
  have hfl' := Int.lt_floor_add_one b
  have hab1 : |a - b| < 1 := lt_of_lt_of_le hab (min_le_right _ _)
  rw [abs_lt] at hab1
  have hmb : b - ⌊b⌋ ∈ Icc (-1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have hma : a - ⌊b⌋ ∈ Icc (-1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have hd : dist (a - ⌊b⌋) (b - ⌊b⌋) < δ := by
    rw [Real.dist_eq, show a - (⌊b⌋ : ℝ) - (b - ⌊b⌋) = a - b by ring]
    exact lt_of_lt_of_le hab (min_le_left _ _)
  have := hδ' _ hma _ hmb hd
  rwa [Real.dist_eq] at this

/-- Helper for `cor16_2_3_b` (§16.3). `sin(πD) ≥ 2 min(D, 1 − D)` on `(0, 1)` (Jordan's inequality). -/
theorem gl16_sin_low {D : ℝ} (h0 : 0 < D) (h1 : D < 1) : 2 * min D (1 - D) ≤ Real.sin (π * D) := by
  have hπ := Real.pi_pos
  rcases le_total D (1 / 2) with hD | hD
  · have h := Real.mul_le_sin (show 0 ≤ π * D by positivity) (by nlinarith)
    have e : 2 / π * (π * D) = 2 * D := by field_simp
    rw [e] at h
    exact le_trans (by nlinarith [min_le_left D (1 - D)]) h
  · have h := Real.mul_le_sin (show 0 ≤ π * (1 - D) by nlinarith) (by nlinarith)
    have e : 2 / π * (π * (1 - D)) = 2 * (1 - D) := by field_simp
    rw [e, show π * (1 - D) = π - π * D by ring, Real.sin_pi_sub] at h
    exact le_trans (by nlinarith [min_le_right D (1 - D)]) h

/-- Helper for `cor16_2_3_b` (§16.3). If `D₊/D₋ ∈ [1 − η, 1 + η]` and `(πD±)² ≤ η ≤ 1/2`, the ratio of `sin(πD₊)` to
`sin(πD₋)` and its inverse are at most `1 + 8η`. -/
theorem gl16_sin_ratio {Dp Dm η : ℝ} (hp : 0 < Dp) (hm : 0 < Dm) (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hq1 : (1 - η) * Dm ≤ Dp) (hq2 : Dp ≤ (1 + η) * Dm) (hsp : (π * Dp) ^ 2 ≤ η) (hsm : (π * Dm) ^ 2 ≤ η) :
    max (Real.sin (π * Dp) / Real.sin (π * Dm)) (Real.sin (π * Dp) / Real.sin (π * Dm))⁻¹ - 1 ≤ 8 * η := by
  have hπ := Real.pi_pos
  have hup : 0 < π * Dp := by positivity
  have hum : 0 < π * Dm := by positivity
  have hsp1 : Real.sin (π * Dp) ≤ π * Dp := Real.sin_le hup.le
  have hsm1 : Real.sin (π * Dm) ≤ π * Dm := Real.sin_le hum.le
  have hsp2 : π * Dp * (1 - η) ≤ Real.sin (π * Dp) := by
    have h := Real.sin_gt_sub_cube hup
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) hup.le]
  have hsm2 : π * Dm * (1 - η) ≤ Real.sin (π * Dm) := by
    have h := Real.sin_gt_sub_cube hum
    nlinarith [mul_nonneg (sub_nonneg.2 hsm) hum.le]
  have hsmpos : 0 < Real.sin (π * Dm) := lt_of_lt_of_le (by nlinarith) hsm2
  have hsppos : 0 < Real.sin (π * Dp) := lt_of_lt_of_le (by nlinarith) hsp2
  have hr1 : Real.sin (π * Dp) / Real.sin (π * Dm) ≤ 1 + 8 * η := by
    rw [div_le_iff₀ hsmpos]
    have ha : π * Dp ≤ π * ((1 + η) * Dm) := mul_le_mul_of_nonneg_left hq2 hπ.le
    have hb : (1 + 8 * η) * (π * Dm * (1 - η)) ≤ (1 + 8 * η) * Real.sin (π * Dm) :=
      mul_le_mul_of_nonneg_left hsm2 (by linarith)
    have hc : (1 + η) * (π * Dm) ≤ (1 + 8 * η) * (1 - η) * (π * Dm) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hum.le
    nlinarith
  have hr2 : (Real.sin (π * Dp) / Real.sin (π * Dm))⁻¹ ≤ 1 + 8 * η := by
    rw [inv_div, div_le_iff₀ hsppos]
    have ha : π * ((1 - η) * Dm) ≤ π * Dp := mul_le_mul_of_nonneg_left hq1 hπ.le
    have hb : (1 + 8 * η) * (π * Dp * (1 - η)) ≤ (1 + 8 * η) * Real.sin (π * Dp) :=
      mul_le_mul_of_nonneg_left hsp2 (by linarith)
    have hc : π * Dm ≤ (1 + 8 * η) * (1 - η) * ((1 - η) * (π * Dm)) := by
      have hq8 : 0 ≤ 8 * η ^ 2 - 15 * η + 6 := by nlinarith [sq_nonneg (η - 1 / 2)]
      have h8 : 1 ≤ (1 + 8 * η) * (1 - η) * (1 - η) := by nlinarith [mul_nonneg hη.le hq8]
      nlinarith
    have hd : (1 + 8 * η) * (1 - η) * ((1 - η) * (π * Dm)) ≤ (1 + 8 * η) * (1 - η) * (π * Dp) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (mul_nonneg (by linarith) (by linarith))
    nlinarith
  have := max_le hr1 hr2
  linarith

/-- Helper for `cor16_2_3_b` (§16.3). The increments of the lift over `[y, y + s]`, `[y − s, y]` and their
complements in a period (`0 < s < 1`). -/
theorem gl16_incr2 {hl : ℝ → ℝ} (hC1 : ContDiff ℝ 1 hl) {m M : ℝ} (hb : ∀ x, m ≤ deriv hl x ∧ deriv hl x ≤ M)
    (hper : ∀ x, hl (x + 1) = hl x + 1) (y : ℝ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    m * s ≤ hl (y + s) - hl y ∧ hl (y + s) - hl y ≤ M * s ∧ m * (1 - s) ≤ 1 - (hl (y + s) - hl y) ∧
      m * s ≤ hl y - hl (y - s) ∧ hl y - hl (y - s) ≤ M * s ∧ m * (1 - s) ≤ 1 - (hl y - hl (y - s)) := by
  have i1 := gl16_incr hC1 hb (show y < y + s by linarith)
  have i2 := gl16_incr hC1 hb (show y - s < y by linarith)
  have i3 := gl16_incr hC1 hb (show y + s < y + 1 by linarith)
  have i4 := gl16_incr hC1 hb (show y < y - s + 1 by linarith)
  rw [show y + s - y = s by ring] at i1
  rw [show y - (y - s) = s by ring] at i2
  rw [show y + 1 - (y + s) = 1 - s by ring, hper] at i3
  rw [show y - s + 1 - y = 1 - s by ring, hper] at i4
  exact ⟨i1.1, i1.2, by linarith [i3.1], i2.1, i2.2, by linarith [i4.1]⟩

/-- Helper for `cor16_2_3_b` (§16.3). At a fixed scale `s ∈ (0, 1)` the two sines are positive and the sine ratio
and its inverse are bounded by `1/(2 m min(s, 1 − s))` (`gl16_sin_low`). -/
theorem gl16_ratio_bdd {Dp Dm m s : ℝ} (hm : 0 < m) (hs0 : 0 < s) (hs1 : s < 1)
    (h1 : m * s ≤ Dp) (h2 : m * (1 - s) ≤ 1 - Dp) (h3 : m * s ≤ Dm) (h4 : m * (1 - s) ≤ 1 - Dm) :
    0 < Real.sin (π * Dp) ∧ 0 < Real.sin (π * Dm) ∧
      max (Real.sin (π * Dp) / Real.sin (π * Dm)) (Real.sin (π * Dp) / Real.sin (π * Dm))⁻¹ - 1 ≤
        1 / (2 * (m * min s (1 - s))) := by
  have hmin0 : 0 < min s (1 - s) := lt_min hs0 (by linarith)
  have hL : 0 < 2 * (m * min s (1 - s)) := by positivity
  have hms : 0 < m * s := mul_pos hm hs0
  have hm1s : 0 < m * (1 - s) := mul_pos hm (by linarith)
  have hp0 : 0 < Dp := lt_of_lt_of_le hms h1
  have hp1 : Dp < 1 := by linarith
  have hm0 : 0 < Dm := lt_of_lt_of_le hms h3
  have hm1 : Dm < 1 := by linarith
  have hmin : ∀ D : ℝ, m * s ≤ D → m * (1 - s) ≤ 1 - D → m * min s (1 - s) ≤ min D (1 - D) := by
    intro D hD1 hD2
    refine le_min ?_ ?_
    · exact le_trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hm.le) hD1
    · exact le_trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hm.le) hD2
  have hsp : 2 * (m * min s (1 - s)) ≤ Real.sin (π * Dp) :=
    le_trans (by linarith [hmin Dp h1 h2]) (gl16_sin_low hp0 hp1)
  have hsm : 2 * (m * min s (1 - s)) ≤ Real.sin (π * Dm) :=
    le_trans (by linarith [hmin Dm h3 h4]) (gl16_sin_low hm0 hm1)
  have hspos : 0 < Real.sin (π * Dp) := lt_of_lt_of_le hL hsp
  have hsmpos : 0 < Real.sin (π * Dm) := lt_of_lt_of_le hL hsm
  refine ⟨hspos, hsmpos, ?_⟩
  have e1 : Real.sin (π * Dp) / Real.sin (π * Dm) ≤ 1 / (2 * (m * min s (1 - s))) :=
    le_trans (div_le_div_of_nonneg_right (Real.sin_le_one _) hsmpos.le) (one_div_le_one_div_of_le hL hsm)
  have e2 : (Real.sin (π * Dp) / Real.sin (π * Dm))⁻¹ ≤ 1 / (2 * (m * min s (1 - s))) := by
    rw [inv_div]
    exact le_trans (div_le_div_of_nonneg_right (Real.sin_le_one _) hspos.le) (one_div_le_one_div_of_le hL hsp)
  have := max_le e1 e2
  linarith

/-- Helper for `cor16_2_3_b` (§16.3). At small scales the sine ratio and its inverse are within `8η` of `1`: the mean
value theorem on `[y, y + s]` and `[y − s, y]`, the uniform continuity of `h̃′` and `gl16_sin_ratio`. -/
theorem gl16_ratio_small {hl : ℝ → ℝ} (hC1 : ContDiff ℝ 1 hl) {m M : ℝ} (hm : 0 < m)
    (hb : ∀ x, m ≤ deriv hl x ∧ deriv hl x ≤ M) {η δ : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hδ' : ∀ a b : ℝ, |a - b| < δ → |deriv hl a - deriv hl b| < η * m)
    (y : ℝ) {s : ℝ} (hs0 : 0 < s) (hsδ : 2 * s < δ) (hsM : s * (π * M) ≤ min 1 η) :
    max (Real.sin (π * (hl (y + s) - hl y)) / Real.sin (π * (hl y - hl (y - s))))
      (Real.sin (π * (hl (y + s) - hl y)) / Real.sin (π * (hl y - hl (y - s))))⁻¹ - 1 ≤ 8 * η := by
  have hd : Differentiable ℝ hl := hC1.differentiable one_ne_zero
  obtain ⟨ξp, hξp, hξp'⟩ := exists_deriv_eq_slope hl (show y < y + s by linarith) hd.continuous.continuousOn
    hd.differentiableOn
  obtain ⟨ξm, hξm, hξm'⟩ := exists_deriv_eq_slope hl (show y - s < y by linarith) hd.continuous.continuousOn
    hd.differentiableOn
  rw [show y + s - y = s by ring] at hξp'
  rw [show y - (y - s) = s by ring] at hξm'
  have hDp : hl (y + s) - hl y = s * deriv hl ξp := by
    rw [hξp']
    field_simp
  have hDm : hl y - hl (y - s) = s * deriv hl ξm := by
    rw [hξm']
    field_simp
  have hclose : |deriv hl ξp - deriv hl ξm| < η * m := by
    refine hδ' ξp ξm ?_
    rw [abs_lt]
    constructor <;> linarith [hξp.1, hξp.2, hξm.1, hξm.2]
  have hbm := hb ξm
  have hbp := hb ξp
  rw [hDp, hDm]
  generalize deriv hl ξp = a at hclose hbp
  generalize deriv hl ξm = b at hclose hbm
  rw [abs_lt] at hclose
  have hb0 : 0 < b := lt_of_lt_of_le hm hbm.1
  have ha0 : 0 < a := lt_of_lt_of_le hm hbp.1
  have hηm : η * m ≤ η * b := mul_le_mul_of_nonneg_left hbm.1 hη.le
  have hπs : 0 < π * s := mul_pos Real.pi_pos hs0
  have hsq : ∀ c : ℝ, 0 < c → c ≤ M → (π * (s * c)) ^ 2 ≤ η := by
    intro c hc0 hcM
    have hu1 : π * (s * c) ≤ s * (π * M) := by
      have := mul_le_mul_of_nonneg_left hcM hπs.le
      calc π * (s * c) = π * s * c := by ring
        _ ≤ π * s * M := this
        _ = s * (π * M) := by ring
    have hu : π * (s * c) ≤ min 1 η := hu1.trans hsM
    have h3 : min 1 η ≤ 1 := min_le_left _ _
    have h4 : min 1 η ≤ η := min_le_right _ _
    have h5 : 0 ≤ π * (s * c) := by positivity
    have h6 : π * (s * c) * (π * (s * c)) ≤ π * (s * c) * 1 := mul_le_mul_of_nonneg_left (hu.trans h3) h5
    nlinarith
  refine gl16_sin_ratio (mul_pos hs0 ha0) (mul_pos hs0 hb0) hη hη2 ?_ ?_ (hsq a ha0 hbp.2) (hsq b hb0 hbm.2)
  · have : (1 - η) * b ≤ a := by linarith
    calc (1 - η) * (s * b) = s * ((1 - η) * b) := by ring
      _ ≤ s * a := mul_le_mul_of_nonneg_left this hs0.le
  · have : a ≤ (1 + η) * b := by linarith
    calc s * a ≤ s * ((1 + η) * b) := mul_le_mul_of_nonneg_left this hs0.le
      _ = (1 + η) * (s * b) := by ring

/-- Helper for `cor16_2_3_b` (§16.3). The ratio of (16.1) through the lift: chords `|e^{2πiu} − e^{2πiv}| =
2|sin(π(u − v))|`. -/
theorem gl16_ratio_lift {h : ℂ → ℂ} {hl : ℝ → ℝ}
    (hlh : ∀ x : ℝ, exp (2 * π * I * hl x) = h (exp (2 * π * I * x))) (x t : ℝ) :
    ‖h (exp ((x + t) * I)) - h (exp (x * I))‖ / ‖h (exp (x * I)) - h (exp ((x - t) * I))‖ =
      |Real.sin (π * (hl (x / (2 * π) + t / (2 * π)) - hl (x / (2 * π))))| /
        |Real.sin (π * (hl (x / (2 * π)) - hl (x / (2 * π) - t / (2 * π))))| := by
  have hπc : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hlift' : ∀ θ : ℝ, h (exp (θ * I)) = exp (2 * π * I * (hl (θ / (2 * π)) : ℂ)) := by
    intro θ
    rw [hlh]
    congr 2
    push_cast
    field_simp
  have hchord : ∀ u v : ℝ, ‖exp (2 * π * I * (u : ℂ)) - exp (2 * π * I * (v : ℂ))‖ =
      2 * |Real.sin (π * (u - v))| := by
    intro u v
    have e : exp (2 * π * I * (u : ℂ)) - exp (2 * π * I * (v : ℂ)) =
        exp (((2 * π * v : ℝ) : ℂ) * I) * (exp (I * ((2 * π * (u - v) : ℝ) : ℂ)) - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 2 <;> push_cast <;> ring
    rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_two, show 2 * π * (u - v) / 2 = π * (u - v) by ring]
  have e1 : ((x : ℂ) + t) * I = ((x + t : ℝ) : ℂ) * I := by push_cast; ring
  have e2 : ((x : ℂ) - t) * I = ((x - t : ℝ) : ℂ) * I := by push_cast; ring
  rw [e1, e2, hlift' (x + t), hlift' x, hlift' (x - t), hchord, hchord, mul_div_mul_left _ _ two_ne_zero, add_div,
    sub_div]

/-- Helper for `para16_3_lift` (§16.3). `h̃(y + n) = h̃(y) + n` for integers `n`. -/
theorem gl16_lift_int {hl : ℝ → ℝ} (hper : ∀ x, hl (x + 1) = hl x + 1) (y : ℝ) (n : ℤ) :
    hl (y + n) = hl y + n := by
  have hP : Function.Periodic (fun x => hl x - x) 1 := fun x => by
    simp only
    rw [hper]
    ring
  have h1 := (hP.int_mul n) y
  simp only [mul_one] at h1
  linarith

/-- Helper for `para16_3_lift` (§16.3). The lift is uniformly continuous (`h̃ − id` is `1`-periodic; Heine–Cantor
on `[−1, 2]`). -/
theorem gl16_lift_uc {hl : ℝ → ℝ} (hc : Continuous hl) (hper : ∀ x, hl (x + 1) = hl x + 1) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ a b : ℝ, |a - b| < δ → |hl a - hl b| < ε := by
  obtain ⟨k, hk⟩ : ∃ k : ℝ → ℝ, ∀ x, k x = hl x - x := ⟨_, fun _ => rfl⟩
  have hkc : Continuous k := by
    have : k = fun x => hl x - x := funext hk
    rw [this]
    exact hc.sub continuous_id
  have hP : Function.Periodic k 1 := fun x => by rw [hk, hk, hper]; ring
  have huc := (isCompact_Icc (a := (-1 : ℝ)) (b := 2)).uniformContinuousOn_of_continuous hkc.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc (ε / 2) (half_pos hε)
  refine ⟨min δ (min 1 (ε / 2)), lt_min hδ (lt_min one_pos (half_pos hε)), fun a b hab => ?_⟩
  have ha' := hP.sub_int_mul_eq (x := a) ⌊b⌋
  have hb' := hP.sub_int_mul_eq (x := b) ⌊b⌋
  rw [mul_one] at ha' hb'
  have hfl := Int.floor_le b
  have hfl' := Int.lt_floor_add_one b
  have hab1 : |a - b| < 1 := lt_of_lt_of_le hab (le_trans (min_le_right _ _) (min_le_left _ _))
  have hab2 : |a - b| < ε / 2 := lt_of_lt_of_le hab (le_trans (min_le_right _ _) (min_le_right _ _))
  have hab1' := hab1
  rw [abs_lt] at hab1'
  have hmb : b - ⌊b⌋ ∈ Icc (-1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have hma : a - ⌊b⌋ ∈ Icc (-1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have hd : dist (a - ⌊b⌋) (b - ⌊b⌋) < δ := by
    rw [Real.dist_eq, show a - (⌊b⌋ : ℝ) - (b - ⌊b⌋) = a - b by ring]
    exact lt_of_lt_of_le hab (min_le_left _ _)
  have h1 := hδ' _ hma _ hmb hd
  rw [Real.dist_eq, ha', hb'] at h1
  have e : hl a - hl b = (k a - k b) + (a - b) := by rw [hk, hk]; ring
  rw [e]
  calc |k a - k b + (a - b)| ≤ |k a - k b| + |a - b| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 hab2
    _ = ε := by ring

/-- Helper for `para16_3_lift` (§16.3). The increments of the lift over intervals of a fixed length `c > 0` are bounded
below by a positive constant (compactness of `[0, 1]` and periodicity). -/
theorem gl16_lift_incr_pos {hl : ℝ → ℝ} (hc : Continuous hl) (hmono : StrictMono hl)
    (hper : ∀ x, hl (x + 1) = hl x + 1) {c : ℝ} (hc0 : 0 < c) : ∃ δ > 0, ∀ y, δ ≤ hl (y + c) - hl y := by
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, ∀ y, f y = hl (y + c) - hl y := ⟨_, fun _ => rfl⟩
  have hfc : Continuous f := by
    have : f = fun y => hl (y + c) - hl y := funext hf
    rw [this]
    exact (hc.comp (continuous_id.add continuous_const)).sub hc
  have hP : Function.Periodic f 1 := fun y => by
    rw [hf, hf, show y + 1 + c = y + c + 1 by ring, hper, hper]
    ring
  obtain ⟨a, -, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (zero_le_one' ℝ)) hfc.continuousOn
  refine ⟨f a, by rw [hf]; linarith [hmono (lt_add_of_pos_right a hc0)], fun y => ?_⟩
  have hy : f (Int.fract y) = f y := by
    have := hP.sub_int_mul_eq (x := y) ⌊y⌋
    rw [mul_one] at this
    exact this
  have hmem : Int.fract y ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg y, (Int.fract_lt_one y).le⟩
  have h1 : f a ≤ f (Int.fract y) := hmin hmem
  rw [hy, hf y] at h1
  exact h1

/-- Helper for `para16_3_lift` (§16.3). The increments of the lift over `[y, y + s]` lie between `⌊s⌋` and
`⌊s⌋ + 1`. -/
theorem gl16_lift_incr_floor {hl : ℝ → ℝ} (hmono : Monotone hl) (hper : ∀ x, hl (x + 1) = hl x + 1) (y s : ℝ) :
    (⌊s⌋ : ℝ) ≤ hl (y + s) - hl y ∧ hl (y + s) - hl y ≤ ⌊s⌋ + 1 := by
  have h1 := gl16_lift_int hper y ⌊s⌋
  have h2 := gl16_lift_int hper y (⌊s⌋ + 1)
  have hf1 := Int.floor_le s
  have hf2 := Int.lt_floor_add_one s
  have m1 : hl (y + ⌊s⌋) ≤ hl (y + s) := hmono (by linarith)
  have m2 : hl (y + s) ≤ hl (y + ((⌊s⌋ + 1 : ℤ) : ℝ)) := hmono (by push_cast; linarith)
  push_cast at h2 m2
  constructor <;> linarith

/-- Helper for `para16_3_lift` (§16.3). Two positive increments whose mutual ratios are at most `B` have their ratio
in `[B⁻¹, B]`. -/
theorem gl16_qs_bound {Dp Dm B : ℝ} (hp : 0 < Dp) (hm : 0 < Dm) (h1 : Dp ≤ B * Dm) (h2 : Dm ≤ B * Dp) :
    B⁻¹ ≤ Dp / Dm ∧ Dp / Dm ≤ B := by
  have hB : 0 < B := by
    by_contra hB
    have hB' : B ≤ 0 := le_of_not_gt hB
    nlinarith
  constructor
  · rw [inv_le_iff_one_le_mul₀ hB, div_mul_eq_mul_div, le_div_iff₀ hm]
    linarith
  · rw [div_le_iff₀ hm]
    exact h1

/-- Helper for `para16_3_lift` (§16.3). Converse of `gl16_sin_ratio`: if `sin(πD₊)/sin(πD₋) ∈ [1 − η, 1 + η]` and
`(πD±)² ≤ η ≤ 1/2`, then `D₊/D₋` and its inverse are at most `1 + 8η`. -/
theorem gl16_sin_ratio_conv {Dp Dm η : ℝ} (hp : 0 < Dp) (hm : 0 < Dm) (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (h1 : (1 - η) * Real.sin (π * Dm) ≤ Real.sin (π * Dp)) (h2 : Real.sin (π * Dp) ≤ (1 + η) * Real.sin (π * Dm))
    (hsp : (π * Dp) ^ 2 ≤ η) (hsm : (π * Dm) ^ 2 ≤ η) :
    max (Dp / Dm) (Dp / Dm)⁻¹ - 1 ≤ 8 * η := by
  have hπ := Real.pi_pos
  have hup : 0 < π * Dp := by positivity
  have hum : 0 < π * Dm := by positivity
  have hsp1 : Real.sin (π * Dp) ≤ π * Dp := Real.sin_le hup.le
  have hsm1 : Real.sin (π * Dm) ≤ π * Dm := Real.sin_le hum.le
  have hsp2 : π * Dp * (1 - η) ≤ Real.sin (π * Dp) := by
    have h := Real.sin_gt_sub_cube hup
    nlinarith [mul_nonneg (sub_nonneg.2 hsp) hup.le]
  have hsm2 : π * Dm * (1 - η) ≤ Real.sin (π * Dm) := by
    have h := Real.sin_gt_sub_cube hum
    nlinarith [mul_nonneg (sub_nonneg.2 hsm) hum.le]
  have hq8 : 0 ≤ 8 * η ^ 2 - 15 * η + 6 := by nlinarith [sq_nonneg (η - 1 / 2)]
  have hr1 : Dp / Dm ≤ 1 + 8 * η := by
    rw [div_le_iff₀ hm]
    -- `π D₊ (1 − η) ≤ sin₊ ≤ (1 + η) sin₋ ≤ (1 + η) π D₋`
    have ha : π * Dp * (1 - η) ≤ (1 + η) * (π * Dm) := by
      nlinarith [mul_le_mul_of_nonneg_left hsm1 (by linarith : (0 : ℝ) ≤ 1 + η)]
    have hb : (1 + η) ≤ (1 + 8 * η) * (1 - η) := by nlinarith
    have hc : (1 + η) * (π * Dm) ≤ (1 + 8 * η) * (1 - η) * (π * Dm) := mul_le_mul_of_nonneg_right hb hum.le
    nlinarith
  have hr2 : (Dp / Dm)⁻¹ ≤ 1 + 8 * η := by
    rw [inv_div, div_le_iff₀ hp]
    -- `π D₋ (1 − η)² ≤ sin₋ (1 − η) ≤ sin₊ ≤ π D₊`
    have ha : π * Dm * (1 - η) * (1 - η) ≤ π * Dp := by
      nlinarith [mul_le_mul_of_nonneg_right hsm2 (by linarith : (0 : ℝ) ≤ 1 - η)]
    have h8 : 1 ≤ (1 + 8 * η) * (1 - η) * (1 - η) := by nlinarith [mul_nonneg hη.le hq8]
    have hc : π * Dm ≤ (1 + 8 * η) * (π * Dm * (1 - η) * (1 - η)) := by nlinarith
    nlinarith
  have := max_le hr1 hr2
  linarith

/-- Helper for `para16_3_lift` (§16.3). The ratio (16.1) at `(2πy, 2πs)` through the lift. -/
theorem gl16_ratio_lift2 {h : ℂ → ℂ} {hl : ℝ → ℝ}
    (hlh : ∀ x : ℝ, exp (2 * π * I * hl x) = h (exp (2 * π * I * x))) (y s : ℝ) :
    ‖h (exp ((((2 * π * y : ℝ) : ℂ) + ((2 * π * s : ℝ) : ℂ)) * I)) - h (exp (((2 * π * y : ℝ) : ℂ) * I))‖ /
      ‖h (exp (((2 * π * y : ℝ) : ℂ) * I)) - h (exp ((((2 * π * y : ℝ) : ℂ) - ((2 * π * s : ℝ) : ℂ)) * I))‖ =
      |Real.sin (π * (hl (y + s) - hl y))| / |Real.sin (π * (hl y - hl (y - s)))| := by
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  rw [gl16_ratio_lift hlh, show 2 * π * y / (2 * π) = y by field_simp, show 2 * π * s / (2 * π) = s by field_simp]

/-- Helper for `para16_3_lift` (§16.3). For `0 < s < 1` the two increments of the lift at `y` lie in `(0, 1)`. -/
theorem gl16_incr_unit {hl : ℝ → ℝ} (hmono : StrictMono hl) (hper : ∀ x, hl (x + 1) = hl x + 1) (y : ℝ) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) :
    0 < hl (y + s) - hl y ∧ hl (y + s) - hl y < 1 ∧ 0 < hl y - hl (y - s) ∧ hl y - hl (y - s) < 1 := by
  have h1 := hmono (lt_add_of_pos_right y hs0)
  have h2 := hmono (show y + s < y + 1 by linarith)
  have h3 := hmono (show y - s < y by linarith)
  have h4 := hmono (show y < y - s + 1 by linarith)
  have e1 := hper y
  have e2 := hper (y - s)
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Helper for `para16_3_lift` (§16.3). `sin(πD) > 0` on `(0, 1)`. -/
theorem gl16_sin_pos {D : ℝ} (h0 : 0 < D) (h1 : D < 1) : 0 < Real.sin (π * D) :=
  Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos h0) (mul_lt_of_lt_one_right Real.pi_pos h1)

/-- Helper for `para16_3_lift` (§16.3). Chord and arc are comparable on short arcs: `2D ≤ sin(πD) ≤ πD` for
`0 < D ≤ 1/2`. -/
theorem gl16_sin_short {D : ℝ} (h0 : 0 < D) (h1 : D ≤ 1 / 2) : 2 * D ≤ Real.sin (π * D) ∧ Real.sin (π * D) ≤ π * D := by
  have hm := gl16_sin_low h0 (by linarith)
  rw [min_eq_left (by linarith : D ≤ 1 - D)] at hm
  exact ⟨hm, Real.sin_le (mul_pos Real.pi_pos h0).le⟩

/-- Helper for `para16_3_lift` (§16.3). The `M`-condition on the circle makes the lift quasisymmetric: short scales
(uniform continuity and `gl16_sin_short`), intermediate scales (`gl16_lift_incr_pos`) and scales `≥ 1`
(`gl16_lift_incr_floor`). -/
theorem gl16_qs_of_M {h : ℂ → ℂ} {hl : ℝ → ℝ} (hlift : IsCircleLift h hl) {M : ℝ} (hM : IsMCondition h M) :
    ∃ M₁, LiZhongQC.IsQuasisymmetric hl M₁ := by
  obtain ⟨hc, hmono, -, -, hper, hlh⟩ := hlift
  have hπ := Real.pi_pos
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  -- the circle `M`-condition at `(2πy, 2πs)`, `0 < s < 1/2`, as a ratio of positive sines
  have hMR : ∀ y s : ℝ, 0 < s → s < 1 / 2 →
      1 / M ≤ Real.sin (π * (hl (y + s) - hl y)) / Real.sin (π * (hl y - hl (y - s))) ∧
      Real.sin (π * (hl (y + s) - hl y)) / Real.sin (π * (hl y - hl (y - s))) ≤ M := by
    intro y s hs0 hs1
    obtain ⟨hp0, hp1, hm0, hm1⟩ := gl16_incr_unit hmono hper y hs0 (by linarith)
    have hnot : ∀ k : ℤ, 2 * π * s ≠ 2 * π * k := by
      intro k hk
      have hsk : s = k := mul_left_cancel₀ h2π hk
      have h0' : (0 : ℤ) < k := by exact_mod_cast (hsk ▸ hs0 : (0 : ℝ) < k)
      have h1' : k < (1 : ℤ) := by exact_mod_cast (show (k : ℝ) < 1 by linarith)
      omega
    have h := hM (2 * π * y) (2 * π * s) hnot
    rw [gl16_ratio_lift2 hlh y s, abs_of_pos (gl16_sin_pos hp0 hp1), abs_of_pos (gl16_sin_pos hm0 hm1)] at h
    exact h
  -- `M > 0`
  have hM0 : 0 < M := by
    obtain ⟨hp0, hp1, hm0, hm1⟩ := gl16_incr_unit hmono hper 0 (s := 1 / 4) (by norm_num) (by norm_num)
    have h := (hMR 0 (1 / 4) (by norm_num) (by norm_num)).2
    have := div_pos (gl16_sin_pos hp0 hp1) (gl16_sin_pos hm0 hm1)
    linarith
  -- the scales
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := gl16_lift_uc hc hper (by norm_num : (0 : ℝ) < 1 / 2)
  have hc₀pos : 0 < min δ₀ (1 / 2) := lt_min hδ₀ (by norm_num)
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := gl16_lift_incr_pos hc hmono hper hc₀pos
  have hB1 : 0 < π * M / 2 := by positivity
  have hB2 : 0 < 1 / δ₁ := by positivity
  set M₁ : ℝ := max (max (π * M / 2) (1 / δ₁)) 2 with hM₁
  have hup : ∀ B : ℝ, 0 < B → B ≤ M₁ → ∀ q : ℝ, B⁻¹ ≤ q ∧ q ≤ B → M₁⁻¹ ≤ q ∧ q ≤ M₁ := by
    intro B hB hBM q hq
    exact ⟨le_trans ((inv_le_inv₀ (lt_of_lt_of_le hB hBM) hB).2 hBM) hq.1, hq.2.trans hBM⟩
  refine ⟨M₁, hmono, hc, ?_, ?_, fun y s hs => ?_⟩
  · -- `h̃ → ∞` at `∞`
    refine tendsto_atTop_atTop.2 fun b => ⟨(⌈b - hl 0⌉ : ℝ), fun a ha => ?_⟩
    have h1 := gl16_lift_int hper 0 ⌈b - hl 0⌉
    rw [zero_add] at h1
    have h2 := hmono.monotone ha
    have h3 := Int.le_ceil (b - hl 0)
    linarith
  · -- `h̃ → −∞` at `−∞`
    refine tendsto_atBot_atBot.2 fun b => ⟨(⌊b - hl 0⌋ : ℝ), fun a ha => ?_⟩
    have h1 := gl16_lift_int hper 0 ⌊b - hl 0⌋
    rw [zero_add] at h1
    have h2 := hmono.monotone ha
    have h3 := Int.floor_le (b - hl 0)
    linarith
  · -- the ratio bounds
    unfold LiZhongQC.qsRatio
    rcases lt_or_ge s (min δ₀ (1 / 2)) with hs1 | hs1
    · -- short scales: chords and arcs are comparable
      have hsδ : s < δ₀ := lt_of_lt_of_le hs1 (min_le_left _ _)
      have hs12 : s < 1 / 2 := lt_of_lt_of_le hs1 (min_le_right _ _)
      obtain ⟨hp0, hp1, hm0, hm1⟩ := gl16_incr_unit hmono hper y hs (by linarith)
      have hp2 : hl (y + s) - hl y ≤ 1 / 2 := by
        have := hδ₀' (y + s) y (by rw [show y + s - y = s by ring, abs_of_pos hs]; exact hsδ)
        rw [abs_lt] at this
        linarith
      have hm2 : hl y - hl (y - s) ≤ 1 / 2 := by
        have := hδ₀' y (y - s) (by rw [show y - (y - s) = s by ring, abs_of_pos hs]; exact hsδ)
        rw [abs_lt] at this
        linarith
      obtain ⟨hpl, hpu⟩ := gl16_sin_short hp0 hp2
      obtain ⟨hml, hmu⟩ := gl16_sin_short hm0 hm2
      obtain ⟨h1, h2⟩ := hMR y s hs hs12
      have hsp := gl16_sin_pos hp0 hp1
      have hsm := gl16_sin_pos hm0 hm1
      rw [div_le_iff₀ hsm] at h2
      rw [div_le_div_iff₀ hM0 hsm, one_mul] at h1
      refine hup (π * M / 2) hB1 (le_trans (le_max_left _ _) (le_max_left _ _)) _ (gl16_qs_bound hp0 hm0 ?_ ?_)
      · nlinarith
      · nlinarith
    · rcases lt_or_ge s 1 with hs2 | hs2
      · -- intermediate scales: increments at least `δ₁`, at most `1`
        obtain ⟨hp0, hp1, hm0, hm1⟩ := gl16_incr_unit hmono hper y hs hs2
        have hp3 : δ₁ ≤ hl (y + s) - hl y := by
          have := hδ₁' y
          have := hmono.monotone (show y + min δ₀ (1 / 2) ≤ y + s by linarith)
          linarith
        have hm3 : δ₁ ≤ hl y - hl (y - s) := by
          have := hδ₁' (y - s)
          have := hmono.monotone (show y - s + min δ₀ (1 / 2) ≤ y by linarith)
          linarith
        refine hup (1 / δ₁) hB2 (le_trans (le_max_right _ _) (le_max_left _ _)) _ (gl16_qs_bound hp0 hm0 ?_ ?_)
        · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hδ₁]
          nlinarith
        · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hδ₁]
          nlinarith
      · -- scales `≥ 1`: increments between `⌊s⌋` and `⌊s⌋ + 1`
        obtain ⟨hp1, hp2⟩ := gl16_lift_incr_floor hmono.monotone hper y s
        obtain ⟨hm1, hm2⟩ := gl16_lift_incr_floor hmono.monotone hper (y - s) s
        rw [show y - s + s = y by ring] at hm1 hm2
        have hn : (1 : ℝ) ≤ ⌊s⌋ := by exact_mod_cast Int.le_floor.2 (by exact_mod_cast hs2)
        refine hup 2 (by norm_num) (le_max_right _ _) _ (gl16_qs_bound (by linarith) (by linarith) ?_ ?_)
        · linarith
        · linarith

/-- Helper for `para16_3_lift` (§16.3). The sine ratio through the lift is unchanged when the scale moves by an
integer (`gl16_lift_int`; `t ↦ t + 2πn` on the circle). -/
theorem gl16_sin_ratio_shift {hl : ℝ → ℝ} (hper : ∀ x, hl (x + 1) = hl x + 1) (y r : ℝ) (n : ℤ) :
    |Real.sin (π * (hl (y + (n + r)) - hl y))| / |Real.sin (π * (hl y - hl (y - (n + r))))| =
      |Real.sin (π * (hl (y + r) - hl y))| / |Real.sin (π * (hl y - hl (y - r)))| := by
  have h1 := gl16_lift_int hper (y + r) n
  have h2 := gl16_lift_int hper (y - (n + r)) n
  rw [show y + r + n = y + (n + r) by ring] at h1
  rw [show y - (n + r) + n = y - r by ring] at h2
  have e1 : π * (hl (y + (n + r)) - hl y) = π * (hl (y + r) - hl y) + n * π := by rw [h1]; ring
  have e2 : π * (hl y - hl (y - (n + r))) = π * (hl y - hl (y - r)) + n * π := by
    have : hl (y - (n + r)) = hl (y - r) - n := by linarith
    rw [this]
    ring
  rw [e1, e2, Real.sin_add_int_mul_pi, Real.sin_add_int_mul_pi, abs_mul, abs_mul,
    mul_div_mul_left _ _ (abs_pos.2 (zpow_ne_zero n (by norm_num))).ne']

/-- Helper for `para16_3_lift` (§16.3). The sine ratio through the lift is inverted under `r ↦ 1 − r` (the
increments become `1 − Δ∓`; `t ↦ 2π − t` on the circle). -/
theorem gl16_sin_ratio_refl {hl : ℝ → ℝ} (hper : ∀ x, hl (x + 1) = hl x + 1) (y r : ℝ) :
    |Real.sin (π * (hl (y + (1 - r)) - hl y))| / |Real.sin (π * (hl y - hl (y - (1 - r))))| =
      (|Real.sin (π * (hl (y + r) - hl y))| / |Real.sin (π * (hl y - hl (y - r)))|)⁻¹ := by
  have h1 : hl (y + (1 - r)) = hl (y - r) + 1 := by rw [show y + (1 - r) = y - r + 1 by ring, hper]
  have h2 : hl (y - (1 - r)) = hl (y + r) - 1 := by
    have := hper (y - (1 - r))
    rw [show y - (1 - r) + 1 = y + r by ring] at this
    linarith
  have e1 : π * (hl (y + (1 - r)) - hl y) = π - π * (hl y - hl (y - r)) := by rw [h1]; ring
  have e2 : π * (hl y - hl (y - (1 - r))) = π - π * (hl (y + r) - hl y) := by rw [h2]; ring
  rw [e1, e2, Real.sin_pi_sub, Real.sin_pi_sub, inv_div]

/-- Helper for `para16_3_lift` (§16.3). A quasisymmetric lift gives the `M`-condition on the circle: short scales
(uniform continuity and `gl16_sin_short`), intermediate scales (`gl16_lift_incr_pos`, `gl16_sin_low`), and the
reductions `t mod 2π` and `t ↦ 2π − t` (`gl16_sin_ratio_shift`, `gl16_sin_ratio_refl`). -/
theorem gl16_M_of_qs {h : ℂ → ℂ} {hl : ℝ → ℝ} (hlift : IsCircleLift h hl) {M₁ : ℝ}
    (hq : LiZhongQC.IsQuasisymmetric hl M₁) : ∃ M, IsMCondition h M := by
  obtain ⟨hc, hmono, -, -, hper, hlh⟩ := hlift
  obtain ⟨-, -, -, -, hqs⟩ := hq
  have hπ := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * π := by positivity
  -- `M₁ > 0`
  have hM₁ : 0 < M₁ := by
    obtain ⟨hp0, -, hm0, -⟩ := gl16_incr_unit hmono hper 0 (s := 1 / 2) (by norm_num) (by norm_num)
    have h := (hqs 0 (1 / 2) (by norm_num)).2
    unfold LiZhongQC.qsRatio at h
    have := div_pos hp0 hm0
    linarith
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := gl16_lift_uc hc hper (by norm_num : (0 : ℝ) < 1 / 2)
  have hc₀pos : 0 < min δ₀ (1 / 2) := lt_min hδ₀ (by norm_num)
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := gl16_lift_incr_pos hc hmono hper hc₀pos
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := gl16_lift_incr_pos hc hmono hper (by norm_num : (0 : ℝ) < 1 / 2)
  have hL : 0 < 2 * min δ₁ δ₂ := by have := lt_min hδ₁ hδ₂; positivity
  have hB1 : 0 < π * M₁ / 2 := by positivity
  have hB2 : 0 < 1 / (2 * min δ₁ δ₂) := by positivity
  set M : ℝ := max (π * M₁ / 2) (1 / (2 * min δ₁ δ₂)) with hM
  have hMpos : 0 < M := lt_of_lt_of_le hB1 (le_max_left _ _)
  have hup : ∀ B : ℝ, 0 < B → B ≤ M → ∀ q : ℝ, B⁻¹ ≤ q ∧ q ≤ B → 1 / M ≤ q ∧ q ≤ M := by
    intro B hB hBM q hq
    rw [one_div]
    exact ⟨le_trans ((inv_le_inv₀ (lt_of_lt_of_le hB hBM) hB).2 hBM) hq.1, hq.2.trans hBM⟩
  -- the bound in lift coordinates for `0 < r ≤ 1/2`
  have hbd : ∀ y r : ℝ, 0 < r → r ≤ 1 / 2 →
      1 / M ≤ |Real.sin (π * (hl (y + r) - hl y))| / |Real.sin (π * (hl y - hl (y - r)))| ∧
      |Real.sin (π * (hl (y + r) - hl y))| / |Real.sin (π * (hl y - hl (y - r)))| ≤ M := by
    intro y r hr0 hr1
    obtain ⟨hp0, hp1, hm0, hm1⟩ := gl16_incr_unit hmono hper y hr0 (by linarith)
    have hsp := gl16_sin_pos hp0 hp1
    have hsm := gl16_sin_pos hm0 hm1
    rw [abs_of_pos hsp, abs_of_pos hsm]
    rcases lt_or_ge r (min δ₀ (1 / 2)) with hrs | hrs
    · -- short scales: the lift's ratio bound transfers to the chords up to `π/2`
      have hrδ : r < δ₀ := lt_of_lt_of_le hrs (min_le_left _ _)
      have hp2 : hl (y + r) - hl y ≤ 1 / 2 := by
        have := hδ₀' (y + r) y (by rw [show y + r - y = r by ring, abs_of_pos hr0]; exact hrδ)
        rw [abs_lt] at this
        linarith
      have hm2 : hl y - hl (y - r) ≤ 1 / 2 := by
        have := hδ₀' y (y - r) (by rw [show y - (y - r) = r by ring, abs_of_pos hr0]; exact hrδ)
        rw [abs_lt] at this
        linarith
      obtain ⟨hpl, hpu⟩ := gl16_sin_short hp0 hp2
      obtain ⟨hml, hmu⟩ := gl16_sin_short hm0 hm2
      obtain ⟨h1, h2⟩ := hqs y r hr0
      unfold LiZhongQC.qsRatio at h1 h2
      rw [div_le_iff₀ hm0] at h2
      rw [inv_le_iff_one_le_mul₀ hM₁, div_mul_eq_mul_div, le_div_iff₀ hm0, one_mul] at h1
      refine hup (π * M₁ / 2) hB1 (le_max_left _ _) _ (gl16_qs_bound hsp hsm ?_ ?_)
      · nlinarith
      · nlinarith
    · -- intermediate scales: both sines at least `2 min(δ₁, δ₂)`
      have hp3 : δ₁ ≤ hl (y + r) - hl y := by
        have := hδ₁' y
        have := hmono.monotone (show y + min δ₀ (1 / 2) ≤ y + r by linarith)
        linarith
      have hm3 : δ₁ ≤ hl y - hl (y - r) := by
        have := hδ₁' (y - r)
        have := hmono.monotone (show y - r + min δ₀ (1 / 2) ≤ y by linarith)
        linarith
      have hp4 : δ₂ ≤ 1 - (hl (y + r) - hl y) := by
        have := hδ₂' (y + r)
        have := hmono.monotone (show y + r + 1 / 2 ≤ y + 1 by linarith)
        have := hper y
        linarith
      have hm4 : δ₂ ≤ 1 - (hl y - hl (y - r)) := by
        have := hδ₂' y
        have := hmono.monotone (show y + 1 / 2 ≤ y - r + 1 by linarith)
        have := hper (y - r)
        linarith
      have hspL : 2 * min δ₁ δ₂ ≤ Real.sin (π * (hl (y + r) - hl y)) :=
        le_trans (by have := le_min (le_trans (min_le_left δ₁ δ₂) hp3) (le_trans (min_le_right δ₁ δ₂) hp4)
                     linarith) (gl16_sin_low hp0 hp1)
      have hsmL : 2 * min δ₁ δ₂ ≤ Real.sin (π * (hl y - hl (y - r))) :=
        le_trans (by have := le_min (le_trans (min_le_left δ₁ δ₂) hm3) (le_trans (min_le_right δ₁ δ₂) hm4)
                     linarith) (gl16_sin_low hm0 hm1)
      refine hup (1 / (2 * min δ₁ δ₂)) hB2 (le_max_right _ _) _ (gl16_qs_bound hsp hsm ?_ ?_)
      · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hL]
        nlinarith [Real.sin_le_one (π * (hl (y + r) - hl y))]
      · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hL]
        nlinarith [Real.sin_le_one (π * (hl y - hl (y - r)))]
  refine ⟨M, fun x t ht => ?_⟩
  -- reduce `t/2π` to its fractional part `r ∈ (0, 1)`, and reflect when `r > 1/2`
  set y := x / (2 * π) with hy
  set n : ℤ := ⌊t / (2 * π)⌋ with hn
  set r : ℝ := Int.fract (t / (2 * π)) with hr
  have hr0' : 0 ≤ r := Int.fract_nonneg _
  have hr1 : r < 1 := Int.fract_lt_one _
  have hr0 : 0 < r := by
    rcases hr0'.lt_or_eq with h' | h'
    · exact h'
    · exfalso
      refine ht n ?_
      have := Int.floor_add_fract (t / (2 * π))
      rw [← hr, ← h', add_zero] at this
      field_simp at this ⊢
      linarith
  have htr : t / (2 * π) = n + r := (Int.floor_add_fract _).symm
  rw [gl16_ratio_lift hlh, ← hy, htr, gl16_sin_ratio_shift hper y r n]
  rcases le_or_gt r (1 / 2) with hr2 | hr2
  · exact hbd y r hr0 hr2
  · obtain ⟨h1, h2⟩ := hbd y (1 - r) (by linarith) (by linarith)
    rw [show r = 1 - (1 - r) by ring, gl16_sin_ratio_refl hper y (1 - r)]
    have hpos : 0 < |Real.sin (π * (hl (y + (1 - r)) - hl y))| / |Real.sin (π * (hl y - hl (y - (1 - r))))| :=
      lt_of_lt_of_le (by positivity) h1
    constructor
    · rw [one_div]
      exact (inv_le_inv₀ (lt_of_lt_of_le hpos h2) hpos).2 h2
    · rw [one_div] at h1
      exact (inv_le_comm₀ hpos hMpos).2 h1

/-- Helper for `para16_3_lift` (§16.3). `max q q⁻¹ ≥ 1` for `q > 0`. -/
theorem gl16_max_inv_ge_one {q : ℝ} (hq : 0 < q) : 1 ≤ max q q⁻¹ := by
  rcases le_total 1 q with h | h
  · exact le_trans h (le_max_left _ _)
  · exact le_trans ((one_le_inv₀ hq).2 h) (le_max_right _ _)

/-- Helper for `para16_3_lift` (§16.3). For a positive family `q` with `max (q z) (q z)⁻¹` bounded above, the
supremum `E = ⨆ z, (max (q z) (q z)⁻¹ − 1)` is nonnegative and `1/(1 + E) ≤ q y ≤ 1 + E`. -/
theorem gl16_sup_bounds {q : ℝ → ℝ} (hq : ∀ z, 0 < q z) {B : ℝ} (hB : ∀ z, max (q z) (q z)⁻¹ ≤ B) (y : ℝ) :
    0 ≤ ⨆ z, (max (q z) (q z)⁻¹ - 1) ∧ 1 / (1 + ⨆ z, (max (q z) (q z)⁻¹ - 1)) ≤ q y ∧
      q y ≤ 1 + ⨆ z, (max (q z) (q z)⁻¹ - 1) := by
  have hbdd : BddAbove (range fun z => max (q z) (q z)⁻¹ - 1) := by
    refine ⟨B - 1, ?_⟩
    rintro _ ⟨z, rfl⟩
    show max (q z) (q z)⁻¹ - 1 ≤ B - 1
    linarith [hB z]
  have hle : max (q y) (q y)⁻¹ - 1 ≤ ⨆ z, (max (q z) (q z)⁻¹ - 1) := le_ciSup hbdd y
  have h1 := gl16_max_inv_ge_one (hq y)
  have h2 : (q y)⁻¹ ≤ 1 + ⨆ z, (max (q z) (q z)⁻¹ - 1) := by linarith [le_max_right (q y) (q y)⁻¹]
  refine ⟨by linarith, ?_, by linarith [le_max_left (q y) (q y)⁻¹]⟩
  calc 1 / (1 + ⨆ z, (max (q z) (q z)⁻¹ - 1)) ≤ 1 / (q y)⁻¹ := one_div_le_one_div_of_le (inv_pos.2 (hq y)) h2
    _ = q y := by rw [one_div, inv_inv]

/-- Helper for `para16_3_lift` (§16.3). A vanishing-distortion function from uniform bounds. If at each admissible
scale `t` the ratios `R x t` are positive and bounded with their inverses uniformly in `x`, and
`max (R, R⁻¹) − 1 ≤ η` at small scales, then `ε(t) = ⨆ x, (max (R x t) (R x t)⁻¹ − 1)` tends to `0` at `0+` and
`1/(1 + ε(t)) ≤ R x t ≤ 1 + ε(t)`. -/
theorem gl16_vanishing_of_bounds {R : ℝ → ℝ → ℝ} {P : ℝ → Prop}
    (hbdd : ∀ t, 0 < t → P t → ∃ B, ∀ x, 0 < R x t ∧ max (R x t) (R x t)⁻¹ ≤ B)
    (hsmall : ∀ η > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ → P t ∧ ∀ x, max (R x t) (R x t)⁻¹ - 1 ≤ η) :
    ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧
      ∀ x t, 0 < t → P t → 1 / (1 + ε t) ≤ R x t ∧ R x t ≤ 1 + ε t := by
  refine ⟨fun t => ⨆ x, (max (R x t) (R x t)⁻¹ - 1), ?_, fun x t ht hP => ?_⟩
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hsmall (ε / 2) (half_pos hε)
    refine ⟨δ, hδ, fun t ht htδ => ?_⟩
    rw [mem_Ioi] at ht
    rw [Real.dist_eq, sub_zero, abs_of_pos ht] at htδ
    obtain ⟨hP, hle⟩ := hδ' t ht htδ
    obtain ⟨B, hB⟩ := hbdd t ht hP
    have h0 := (gl16_sup_bounds (fun x => (hB x).1) (fun x => (hB x).2) 0).1
    have h1 : (⨆ x, (max (R x t) (R x t)⁻¹ - 1)) ≤ ε / 2 := ciSup_le hle
    show dist (⨆ x, (max (R x t) (R x t)⁻¹ - 1)) 0 < ε
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
    linarith
  · obtain ⟨B, hB⟩ := hbdd t ht hP
    exact (gl16_sup_bounds (fun x => (hB x).1) (fun x => (hB x).2) x).2

/-- Helper for `para16_3_lift` (§16.3). At a fixed scale `s > 0` the quasisymmetry ratio of the lift is positive and
bounded with its inverse, uniformly in `y` (`gl16_lift_incr_pos` for `s < 1`, `gl16_lift_incr_floor` for `s ≥ 1`). -/
theorem gl16_lift_incr_cmp {hl : ℝ → ℝ} (hc : Continuous hl) (hmono : StrictMono hl)
    (hper : ∀ x, hl (x + 1) = hl x + 1) {s : ℝ} (hs : 0 < s) :
    ∃ B, ∀ y, 0 < LiZhongQC.qsRatio hl y s ∧ max (LiZhongQC.qsRatio hl y s) (LiZhongQC.qsRatio hl y s)⁻¹ ≤ B := by
  have key : ∃ B, ∀ y, 0 < hl (y + s) - hl y ∧ 0 < hl y - hl (y - s) ∧
      hl (y + s) - hl y ≤ B * (hl y - hl (y - s)) ∧ hl y - hl (y - s) ≤ B * (hl (y + s) - hl y) := by
    rcases lt_or_ge s 1 with hs1 | hs1
    · obtain ⟨δ, hδ, hδ'⟩ := gl16_lift_incr_pos hc hmono hper hs
      refine ⟨1 / δ, fun y => ?_⟩
      obtain ⟨hp0, hp1, hm0, hm1⟩ := gl16_incr_unit hmono hper y hs hs1
      have a1 := hδ' y
      have a2 := hδ' (y - s)
      rw [show y - s + s = y by ring] at a2
      refine ⟨hp0, hm0, ?_, ?_⟩
      · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hδ]
        nlinarith
      · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hδ]
        nlinarith
    · refine ⟨2, fun y => ?_⟩
      obtain ⟨hp1, hp2⟩ := gl16_lift_incr_floor hmono.monotone hper y s
      obtain ⟨hm1, hm2⟩ := gl16_lift_incr_floor hmono.monotone hper (y - s) s
      rw [show y - s + s = y by ring] at hm1 hm2
      have hn : (1 : ℝ) ≤ ⌊s⌋ := by exact_mod_cast Int.le_floor.2 (by exact_mod_cast hs1)
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨B, hB⟩ := key
  refine ⟨B, fun y => ?_⟩
  obtain ⟨hp0, hm0, h1, h2⟩ := hB y
  obtain ⟨b1, b2⟩ := gl16_qs_bound hp0 hm0 h1 h2
  have hB0 : 0 < B := by
    by_contra hB0
    have : B ≤ 0 := le_of_not_gt hB0
    nlinarith
  unfold LiZhongQC.qsRatio
  exact ⟨div_pos hp0 hm0, max_le b2 (inv_le_of_inv_le₀ hB0 b1)⟩

/-- Helper for `para16_3_lift` (§16.3). At a fixed scale `s ∈ (0, 1)` both sines through the lift are bounded below
by a positive constant, uniformly in `y` (`gl16_lift_incr_pos` at `s` and `1 − s`, `gl16_sin_low`). -/
theorem gl16_lift_sin_low {hl : ℝ → ℝ} (hc : Continuous hl) (hmono : StrictMono hl)
    (hper : ∀ x, hl (x + 1) = hl x + 1) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ L > 0, ∀ y, L ≤ Real.sin (π * (hl (y + s) - hl y)) ∧ L ≤ Real.sin (π * (hl y - hl (y - s))) := by
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := gl16_lift_incr_pos hc hmono hper hs0
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := gl16_lift_incr_pos hc hmono hper (show 0 < 1 - s by linarith)
  refine ⟨2 * min δ₁ δ₂, by have := lt_min hδ₁ hδ₂; positivity, fun y => ?_⟩
  obtain ⟨hp0, hp1, hm0, hm1⟩ := gl16_incr_unit hmono hper y hs0 hs1
  have a1 := hδ₁' y
  have a2 := hδ₁' (y - s)
  have a3 := hδ₂' (y + s)
  have a4 := hδ₂' y
  rw [show y - s + s = y by ring] at a2
  rw [show y + s + (1 - s) = y + 1 by ring, hper] at a3
  rw [show y + (1 - s) = y - s + 1 by ring, hper] at a4
  have m1 := min_le_left δ₁ δ₂
  have m2 := min_le_right δ₁ δ₂
  constructor
  · refine le_trans ?_ (gl16_sin_low hp0 hp1)
    have : min δ₁ δ₂ ≤ min (hl (y + s) - hl y) (1 - (hl (y + s) - hl y)) := le_min (by linarith) (by linarith)
    linarith
  · refine le_trans ?_ (gl16_sin_low hm0 hm1)
    have : min δ₁ δ₂ ≤ min (hl y - hl (y - s)) (1 - (hl y - hl (y - s))) := le_min (by linarith) (by linarith)
    linarith

/-- Helper for `para16_3_lift` (§16.3). If `0 < D` and `|D| < min(1, η)/π`, then `(πD)² ≤ η`. -/
theorem gl16_sq_le {D η : ℝ} (h0 : 0 < D) (h1 : |D| < min 1 η / π) : (π * D) ^ 2 ≤ η := by
  have hπ := Real.pi_pos
  rw [abs_of_pos h0, lt_div_iff₀ hπ] at h1
  have h5 : 0 < π * D := by positivity
  have h6 := min_le_left 1 η
  have h7 := min_le_right 1 η
  nlinarith

/-- Helper for `para16_3_lift` (§16.3). Vanishing ratio distortion on the circle gives it for the lift
(`gl16_vanishing_of_bounds` at the lift's ratio; small scales by `gl16_sin_ratio_conv` and uniform continuity). -/
theorem gl16_lift_vanishing {h : ℂ → ℂ} {hl : ℝ → ℝ} (hlift : IsCircleLift h hl)
    (hv : HasVanishingRatioDistortion h) :
    ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧ ∀ x t : ℝ, 0 < t →
      1 / (1 + ε t) ≤ LiZhongQC.qsRatio hl x t ∧ LiZhongQC.qsRatio hl x t ≤ 1 + ε t := by
  obtain ⟨hc, hmono, -, -, hper, hlh⟩ := hlift
  obtain ⟨εc, hεc, hεc'⟩ := hv
  have hπ := Real.pi_pos
  suffices hsmall : ∀ η > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ → True ∧
      ∀ x, max (LiZhongQC.qsRatio hl x t) (LiZhongQC.qsRatio hl x t)⁻¹ - 1 ≤ η by
    obtain ⟨ε, hε, hε'⟩ := gl16_vanishing_of_bounds (R := LiZhongQC.qsRatio hl) (P := fun _ => True)
      (fun t ht _ => gl16_lift_incr_cmp hc hmono hper ht) hsmall
    exact ⟨ε, hε, fun x t ht => hε' x t ht trivial⟩
  intro η hη
  set η' : ℝ := min (η / 8) (1 / 2) with hη'
  have hη0 : 0 < η' := lt_min (by positivity) (by norm_num)
  have hη2 : η' ≤ 1 / 2 := min_le_right _ _
  have hη8 : 8 * η' ≤ η := by have := min_le_left (η / 8) (1 / 2); linarith
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.tendsto_nhdsWithin_nhds.1 hεc η' hη0
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := gl16_lift_uc hc hper (show 0 < min 1 η' / π by positivity)
  refine ⟨min (min (δ₁ / (2 * π)) δ₂) (1 / 2), by positivity, fun s hs hsδ => ⟨trivial, fun y => ?_⟩⟩
  have hs1 : s < δ₁ / (2 * π) := lt_of_lt_of_le hsδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hs2 : s < δ₂ := lt_of_lt_of_le hsδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hs3 : s < 1 / 2 := lt_of_lt_of_le hsδ (min_le_right _ _)
  -- the circle's distortion at the scale `2πs`
  have hεs : |εc (2 * π * s)| < η' := by
    have h2s : 2 * π * s < δ₁ := by
      rw [lt_div_iff₀ (by positivity)] at hs1
      linarith
    have := hδ₁' (show 2 * π * s ∈ Ioi (0 : ℝ) from mem_Ioi.2 (by positivity))
      (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; exact h2s)
    rwa [Real.dist_eq, sub_zero] at this
  rw [abs_lt] at hεs
  obtain ⟨hp0, hp1, hm0, hm1⟩ := gl16_incr_unit hmono hper y hs (by linarith)
  have hsp := gl16_sin_pos hp0 hp1
  have hsm := gl16_sin_pos hm0 hm1
  obtain ⟨h1, h2⟩ := hεc' (2 * π * y) (2 * π * s) (by positivity) (by nlinarith)
  rw [gl16_ratio_lift2 hlh y s, abs_of_pos hsp, abs_of_pos hsm] at h1 h2
  have hR1 : (1 - η') * Real.sin (π * (hl y - hl (y - s))) ≤ Real.sin (π * (hl (y + s) - hl y)) := by
    rw [← le_div_iff₀ hsm]
    refine le_trans ?_ h1
    rw [le_div_iff₀ (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.2 hεs.2.le) (by linarith : (0 : ℝ) ≤ 1 - η')]
  have hR2 : Real.sin (π * (hl (y + s) - hl y)) ≤ (1 + η') * Real.sin (π * (hl y - hl (y - s))) := by
    rw [← div_le_iff₀ hsm]
    linarith
  have hp2 := gl16_sq_le hp0 (hδ₂' (y + s) y (by rw [show y + s - y = s by ring, abs_of_pos hs]; exact hs2))
  have hm2 := gl16_sq_le hm0 (hδ₂' y (y - s) (by rw [show y - (y - s) = s by ring, abs_of_pos hs]; exact hs2))
  have := gl16_sin_ratio_conv hp0 hm0 hη0 hη2 hR1 hR2 hp2 hm2
  unfold LiZhongQC.qsRatio
  linarith

/-- Helper for `para16_3_lift` (§16.3). Vanishing ratio distortion of the lift gives it on the circle
(`gl16_vanishing_of_bounds` at the circle's ratio, bounded by `gl16_lift_sin_low`; small scales by `gl16_sin_ratio`
and uniform continuity). -/
theorem gl16_circle_vanishing {h : ℂ → ℂ} {hl : ℝ → ℝ} (hlift : IsCircleLift h hl)
    (hv : ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧ ∀ x t : ℝ, 0 < t →
      1 / (1 + ε t) ≤ LiZhongQC.qsRatio hl x t ∧ LiZhongQC.qsRatio hl x t ≤ 1 + ε t) :
    HasVanishingRatioDistortion h := by
  obtain ⟨hc, hmono, -, -, hper, hlh⟩ := hlift
  obtain ⟨εl, hεl, hεl'⟩ := hv
  have hπ := Real.pi_pos
  unfold HasVanishingRatioDistortion
  refine gl16_vanishing_of_bounds (P := fun t => t < 2 * π) (fun t ht0 ht1 => ?_) (fun η hη => ?_)
  · -- `t ∈ (0, 2π)`: the sines are bounded below
    have hs0 : 0 < t / (2 * π) := by positivity
    have hs1 : t / (2 * π) < 1 := by
      rw [div_lt_one (by positivity)]
      exact ht1
    obtain ⟨L, hL, hL'⟩ := gl16_lift_sin_low hc hmono hper hs0 hs1
    refine ⟨1 / L, fun x => ?_⟩
    obtain ⟨a1, a2⟩ := hL' (x / (2 * π))
    have hsp := lt_of_lt_of_le hL a1
    have hsm := lt_of_lt_of_le hL a2
    rw [gl16_ratio_lift hlh, abs_of_pos hsp, abs_of_pos hsm]
    refine ⟨div_pos hsp hsm, max_le ?_ ?_⟩
    · exact le_trans (div_le_div_of_nonneg_right (Real.sin_le_one _) hsm.le) (one_div_le_one_div_of_le hL a2)
    · rw [inv_div]
      exact le_trans (div_le_div_of_nonneg_right (Real.sin_le_one _) hsp.le) (one_div_le_one_div_of_le hL a1)
  · -- small scales
    set η' : ℝ := min (η / 8) (1 / 2) with hη'
    have hη0 : 0 < η' := lt_min (by positivity) (by norm_num)
    have hη2 : η' ≤ 1 / 2 := min_le_right _ _
    have hη8 : 8 * η' ≤ η := by have := min_le_left (η / 8) (1 / 2); linarith
    obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.tendsto_nhdsWithin_nhds.1 hεl η' hη0
    obtain ⟨δ₂, hδ₂, hδ₂'⟩ := gl16_lift_uc hc hper (show 0 < min 1 η' / π by positivity)
    refine ⟨min (min (2 * π * δ₁) (2 * π * δ₂)) π, by positivity, fun t ht htδ => ⟨?_, fun x => ?_⟩⟩
    · show t < 2 * π
      have := lt_of_lt_of_le htδ (min_le_right _ _)
      linarith
    have hs0 : 0 < t / (2 * π) := by positivity
    have ht1 : t < 2 * π * δ₁ := lt_of_lt_of_le htδ (le_trans (min_le_left _ _) (min_le_left _ _))
    have ht2 : t < 2 * π * δ₂ := lt_of_lt_of_le htδ (le_trans (min_le_left _ _) (min_le_right _ _))
    have ht3 : t < π := lt_of_lt_of_le htδ (min_le_right _ _)
    have hs1 : t / (2 * π) < δ₁ := by
      rw [div_lt_iff₀ (by positivity)]
      linarith
    have hs2 : t / (2 * π) < δ₂ := by
      rw [div_lt_iff₀ (by positivity)]
      linarith
    have hs3 : t / (2 * π) < 1 / 2 := by
      rw [div_lt_iff₀ (by positivity)]
      linarith
    rw [gl16_ratio_lift hlh]
    generalize t / (2 * π) = s at hs0 hs1 hs2 hs3 ⊢
    generalize x / (2 * π) = y
    have hεs : |εl s| < η' := by
      have := hδ₁' (mem_Ioi.2 hs0) (by rw [Real.dist_eq, sub_zero, abs_of_pos hs0]; exact hs1)
      rwa [Real.dist_eq, sub_zero] at this
    rw [abs_lt] at hεs
    obtain ⟨hp0, hp1, hm0, hm1⟩ := gl16_incr_unit hmono hper y hs0 (by linarith)
    rw [abs_of_pos (gl16_sin_pos hp0 hp1), abs_of_pos (gl16_sin_pos hm0 hm1)]
    obtain ⟨h1, h2⟩ := hεl' y s hs0
    unfold LiZhongQC.qsRatio at h1 h2
    have hq1 : (1 - η') * (hl y - hl (y - s)) ≤ hl (y + s) - hl y := by
      rw [← le_div_iff₀ hm0]
      refine le_trans ?_ h1
      rw [le_div_iff₀ (by linarith)]
      nlinarith [mul_nonneg (sub_nonneg.2 hεs.2.le) (by linarith : (0 : ℝ) ≤ 1 - η')]
    have hq2 : hl (y + s) - hl y ≤ (1 + η') * (hl y - hl (y - s)) := by
      rw [← div_le_iff₀ hm0]
      linarith
    have hp2 := gl16_sq_le hp0 (hδ₂' (y + s) y (by rw [show y + s - y = s by ring, abs_of_pos hs0]; exact hs2))
    have hm2 := gl16_sq_le hm0 (hδ₂' y (y - s) (by rw [show y - (y - s) = s by ring, abs_of_pos hs0]; exact hs2))
    have := gl16_sin_ratio hp0 hm0 hη0 hη2 hq1 hq2 hp2 hm2
    linarith

/-- **Unlabelled** (§16.3, l. 12025–12031). `h` satisfies (16.1) for some `M` iff its lift satisfies (16.2) for some
`M₁`; `h` has vanishing ratio distortion iff the lift does. -/
theorem para16_3_lift {h : ℂ → ℂ} {hl : ℝ → ℝ} (hh : Pommerenke1992.IsSensePreservingCircleHomeo h)
    (hlift : IsCircleLift h hl) :
    ((∃ M, IsMCondition h M) ↔ ∃ M₁, LiZhongQC.IsQuasisymmetric hl M₁) ∧
      (HasVanishingRatioDistortion h ↔ ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧ ∀ x t : ℝ, 0 < t →
        1 / (1 + ε t) ≤ LiZhongQC.qsRatio hl x t ∧ LiZhongQC.qsRatio hl x t ≤ 1 + ε t) := by
  -- `hh` is not needed: the ratios only read `h` on the circle, where the lift `hlift` determines it
  have _hh := hh
  exact ⟨⟨fun ⟨_, hM⟩ => gl16_qs_of_M hlift hM, fun ⟨_, hq⟩ => gl16_M_of_qs hlift hq⟩,
    ⟨gl16_lift_vanishing hlift, gl16_circle_vanishing hlift⟩⟩

/-- Helper for the circle layer (§16.3): every point of the circle is `e^{2πia}` with `a = arg z/(2π)`. -/
theorem gl16_cl_exp_arg {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) :
    exp (2 * π * I * ((arg z / (2 * π) : ℝ) : ℂ)) = z := by
  have h1 : ‖z‖ = 1 := by simpa using hz
  have h2 : (2 * π * I * ((arg z / (2 * π) : ℝ) : ℂ)) = (arg z : ℂ) * I := by
    push_cast
    field_simp
  rw [h2]
  have h3 := norm_mul_exp_arg_mul_I z
  rw [h1, Complex.ofReal_one, one_mul] at h3
  exact h3

/-- Helper for the circle layer (§16.3): `e^{2πia} = e^{2πib}` iff `a − b` is an integer. -/
theorem gl16_cl_exp_eq {a b : ℝ} (h : exp (2 * π * I * (a : ℂ)) = exp (2 * π * I * (b : ℂ))) :
    ∃ n : ℤ, a = b + n := by
  have h1 : exp (2 * π * I * ((a - b : ℝ) : ℂ)) = 1 := by
    rw [Complex.ofReal_sub, mul_sub, Complex.exp_sub, h, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
  refine ⟨n, ?_⟩
  have h2 : ((a - b : ℝ) : ℂ) = n := by
    have hne : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    apply mul_left_cancel₀ hne
    rw [hn]
    ring
  have h3 : a - b = n := by exact_mod_cast h2
  linarith

/-- Helper for the circle layer (§16.3): a circle map with a lift is injective on the circle (`h̃` is strictly
increasing with `h̃(x + n) = h̃(x) + n`). -/
theorem gl16_cl_lift_injOn {h : ℂ → ℂ} {hl : ℝ → ℝ} (hlift : IsCircleLift h hl) : InjOn h (sphere 0 1) := by
  intro z₁ hz₁ z₂ hz₂ heq
  obtain ⟨-, hmono, -, -, hper, hlh⟩ := hlift
  rw [← gl16_cl_exp_arg hz₁, ← gl16_cl_exp_arg hz₂] at heq ⊢
  rw [← hlh, ← hlh] at heq
  obtain ⟨n, hn⟩ := gl16_cl_exp_eq heq
  rw [← gl16_lift_int hper] at hn
  have h1 := hmono.injective hn
  rw [h1]
  push_cast
  rw [mul_add, Complex.exp_add]
  have : exp (2 * π * I * (n : ℂ)) = 1 := by
    rw [show (2 * π * I * (n : ℂ)) = n * (2 * π * I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  rw [this, mul_one]

/-- Helper for the circle layer (§16.3): the triple `e^{i(x ± t)}, e^{ix}` has equal chords, and they are nonzero
when `t ∉ 2πℤ`. -/
theorem gl16_cl_chord (x t : ℝ) (ht : ∀ k : ℤ, t ≠ 2 * π * k) :
    ‖exp (((x : ℂ) + t) * I) - exp ((x : ℂ) * I)‖ = ‖exp ((x : ℂ) * I) - exp (((x : ℂ) - t) * I)‖ ∧
      0 < ‖exp ((x : ℂ) * I) - exp (((x : ℂ) - t) * I)‖ := by
  have e1 : exp (((x : ℂ) + t) * I) = exp ((x : ℂ) * I) * exp ((t : ℂ) * I) := by
    rw [add_mul, Complex.exp_add]
  have e3 : exp ((x : ℂ) * I) = exp (((x : ℂ) - t) * I) * exp ((t : ℂ) * I) := by
    rw [← Complex.exp_add]
    ring_nf
  have hne : exp ((t : ℂ) * I) ≠ 1 := by
    intro h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
    apply ht n
    have h2 : ((t : ℂ)) = (((2 * π * n : ℝ)) : ℂ) := by
      apply mul_right_cancel₀ I_ne_zero
      rw [hn]
      push_cast
      ring
    exact_mod_cast h2
  have hL : ‖exp (((x : ℂ) + t) * I) - exp ((x : ℂ) * I)‖ = ‖exp ((t : ℂ) * I) - 1‖ := by
    rw [e1, ← mul_sub_one, norm_mul, norm_exp_ofReal_mul_I, one_mul]
  have hR : ‖exp ((x : ℂ) * I) - exp (((x : ℂ) - t) * I)‖ = ‖exp ((t : ℂ) * I) - 1‖ := by
    rw [e3, ← mul_sub_one, norm_mul, show ((x : ℂ) - t) = ((x - t : ℝ) : ℂ) by push_cast; ring,
      norm_exp_ofReal_mul_I, one_mul]
  refine ⟨by rw [hL, hR], ?_⟩
  rw [hR]
  exact norm_pos_iff.2 (sub_ne_zero.2 hne)

/-- Helper for the circle layer (§16.3): the chord `|e^{iθ} − 1| = 2|sin(θ/2)|`. -/
theorem gl16_cl_norm_exp_sub_one (θ : ℝ) : ‖exp ((θ : ℂ) * I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  rw [mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]

/-- Helper for the circle layer (§16.3): `| |sin a| − |sin b| | ≤ |a − b|`. -/
theorem gl16_cl_abs_sin_lip (a b : ℝ) : |(|Real.sin a| - |Real.sin b|)| ≤ |a - b| :=
  (abs_abs_sub_abs_le_abs_sub _ _).trans (Real.abs_sin_sub_sin_le a b)

/-- Helper for `gl16_cl_affine3` (§16.3): a copy of S04's `gl16_bal_halves` (placement: S03
precedes S04; consolidation candidate). One subdivision step: for a symmetric triple `x − t, x, x + t` in
`[a, a + L]`, each half carries at most the fraction `(1 + δ)/(2 + δ)` of the increment over `[x − t, x + t]`. -/
theorem gl16_cl_halves {h : ℝ → ℝ} (hmono : StrictMono h) {a L δ : ℝ} (hδ : 0 ≤ δ)
    (hr : ∀ x t : ℝ, 0 < t → a ≤ x - t → x + t ≤ a + L →
      1 / (1 + δ) ≤ LiZhongQC.qsRatio h x t ∧ LiZhongQC.qsRatio h x t ≤ 1 + δ) {x t : ℝ} (ht : 0 < t) (hxl : a ≤ x - t)
    (hxr : x + t ≤ a + L) :
    h x - h (x - t) ≤ (1 + δ) / (2 + δ) * (h (x + t) - h (x - t)) ∧
      h (x + t) - h x ≤ (1 + δ) / (2 + δ) * (h (x + t) - h (x - t)) := by
  obtain ⟨h1, h2⟩ := hr x t ht hxl hxr
  have hLh : 0 < h x - h (x - t) := sub_pos.2 (hmono (by linarith))
  have hR : 0 < h (x + t) - h x := sub_pos.2 (hmono (by linarith))
  have hδ1 : 0 < 1 + δ := by linarith
  change 1 / (1 + δ) ≤ (h (x + t) - h x) / (h x - h (x - t)) at h1
  change (h (x + t) - h x) / (h x - h (x - t)) ≤ 1 + δ at h2
  rw [div_le_iff₀ hLh] at h2
  rw [div_le_div_iff₀ hδ1 hLh, one_mul] at h1
  have h2δ : 0 < 2 + δ := by linarith
  constructor
  · rw [div_mul_eq_mul_div, le_div_iff₀ h2δ]
    nlinarith
  · rw [div_mul_eq_mul_div, le_div_iff₀ h2δ]
    nlinarith

/-- Helper for `gl16_cl_affine3` (§16.3): a copy of S04's `gl16_bal_dyadic_inc` (placement: S03
precedes S04; consolidation candidate). The dyadic increments of `h` on `[a, a + L]`: if the ratios on all symmetric
triples in `[a, a + L]` lie in `[1/(1 + δ), 1 + δ]`, then every level-`n` dyadic interval carries at most the fraction
`ρⁿ`, `ρ = (1 + δ)/(2 + δ)`, of the total increment (each half gets at most `ρ` of its parent). -/
theorem gl16_cl_dyadic_inc {h : ℝ → ℝ} (hmono : StrictMono h) {a L δ : ℝ} (hL : 0 < L) (hδ : 0 ≤ δ)
    (hr : ∀ x t : ℝ, 0 < t → a ≤ x - t → x + t ≤ a + L →
      1 / (1 + δ) ≤ LiZhongQC.qsRatio h x t ∧ LiZhongQC.qsRatio h x t ≤ 1 + δ) (n k : ℕ) (hk : k < 2 ^ n) :
    h (a + (k + 1) * L / 2 ^ n) - h (a + k * L / 2 ^ n) ≤ ((1 + δ) / (2 + δ)) ^ n * (h (a + L) - h a) := by
  have hρ0 : 0 ≤ (1 + δ) / (2 + δ) := by positivity
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by
      rw [pow_zero] at hk
      omega
    subst hk0
    simp
  | succ n ih =>
    have h2 : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
    have hpow : (0 : ℝ) < 2 ^ n := by positivity
    have hkn : k < 2 * 2 ^ n := by rw [pow_succ] at hk; omega
    obtain ⟨j, hj⟩ := Nat.even_or_odd' k
    have hjn : j < 2 ^ n := by rcases hj with hj | hj <;> omega
    have hpar := ih j hjn
    set t : ℝ := L / 2 ^ (n + 1) with ht
    have htpos : 0 < t := by positivity
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjle : ((j : ℝ) + 1) ≤ 2 ^ n := by exact_mod_cast hjn
    have eA : a + (j : ℝ) * L / 2 ^ n = a + (2 * j + 1) * t - t := by
      rw [ht, h2]
      field_simp
      ring
    have eB : a + ((j : ℝ) + 1) * L / 2 ^ n = a + (2 * j + 1) * t + t := by
      rw [ht, h2]
      field_simp
      ring
    have hxl : a ≤ a + (2 * j + 1) * t - t := by nlinarith
    have hxr : a + (2 * j + 1) * t + t ≤ a + L := by
      rw [← eB]
      have : ((j : ℝ) + 1) * L / 2 ^ n ≤ L := by
        rw [div_le_iff₀ hpow]
        nlinarith
      linarith
    obtain ⟨hl, hr'⟩ := gl16_cl_halves hmono hδ hr htpos hxl hxr
    rw [eA, eB] at hpar
    have hstep : (1 + δ) / (2 + δ) * (h (a + (2 * j + 1) * t + t) - h (a + (2 * j + 1) * t - t)) ≤
        ((1 + δ) / (2 + δ)) ^ (n + 1) * (h (a + L) - h a) := by
      rw [pow_succ, mul_comm (((1 + δ) / (2 + δ)) ^ n), mul_assoc]
      exact mul_le_mul_of_nonneg_left hpar hρ0
    rcases hj with rfl | rfl
    · -- the left half of the parent
      have e1 : a + ((((2 * j : ℕ) : ℝ)) + 1) * L / 2 ^ (n + 1) = a + (2 * j + 1) * t := by
        rw [ht]
        push_cast
        ring
      have e2 : a + (((2 * j : ℕ) : ℝ)) * L / 2 ^ (n + 1) = a + (2 * j + 1) * t - t := by
        rw [ht]
        push_cast
        ring
      rw [e1, e2]
      exact hl.trans hstep
    · -- the right half of the parent
      have e1 : a + ((((2 * j + 1 : ℕ) : ℝ)) + 1) * L / 2 ^ (n + 1) = a + (2 * j + 1) * t + t := by
        rw [ht]
        push_cast
        ring
      have e2 : a + (((2 * j + 1 : ℕ) : ℝ)) * L / 2 ^ (n + 1) = a + (2 * j + 1) * t := by
        rw [ht]
        push_cast
        ring
      rw [e1, e2]
      exact hr'.trans hstep

/-- Helper for `gl16_cl_affine3` (§16.3): a copy of S04's `gl16_bal_near_affine` (placement: S03
precedes S04; consolidation candidate). Near-affinity: under the ratio condition of `gl16_cl_dyadic_inc`, `h`
differs from its chord on `[a, a + L]` by at most `D((2ρ)ⁿ − 1 + 2⁻ⁿ)`, `D = h(a + L) − h(a)` (telescoping the dyadic
bound at the level-`n` points, monotonicity between them). -/
theorem gl16_cl_near_affine {h : ℝ → ℝ} (hmono : StrictMono h) {a L δ : ℝ} (hL : 0 < L) (hδ : 0 ≤ δ)
    (hr : ∀ x t : ℝ, 0 < t → a ≤ x - t → x + t ≤ a + L →
      1 / (1 + δ) ≤ LiZhongQC.qsRatio h x t ∧ LiZhongQC.qsRatio h x t ≤ 1 + δ) (n : ℕ) :
    ∀ t ∈ Icc a (a + L), |h t - (h a + (t - a) / L * (h (a + L) - h a))| ≤
      (h (a + L) - h a) * ((2 * ((1 + δ) / (2 + δ))) ^ n - 1 + (1 / 2) ^ n) := by
  set ρ : ℝ := (1 + δ) / (2 + δ) with hρ
  set D : ℝ := h (a + L) - h a with hD
  have hD0 : 0 ≤ D := sub_nonneg.2 (hmono.monotone (by linarith))
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hρh : 1 / 2 ≤ ρ := by
    rw [hρ, div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith
  have hρn : (1 / 2 : ℝ) ^ n ≤ ρ ^ n := pow_le_pow_left₀ (by norm_num) hρh n
  have hhalf : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have h2ρ : (2 * ρ) ^ n = 2 ^ n * ρ ^ n := mul_pow 2 ρ n
  -- the dyadic points `P k = a + k L / 2ⁿ`
  have hinc : ∀ k : ℕ, k < 2 ^ n →
      h (a + ((k : ℝ) + 1) * L / 2 ^ n) - h (a + (k : ℝ) * L / 2 ^ n) ≤ ρ ^ n * D :=
    fun k hk => gl16_cl_dyadic_inc hmono hL hδ hr n k hk
  have hG : ∀ i j : ℕ, i ≤ j → j ≤ 2 ^ n →
      h (a + (j : ℝ) * L / 2 ^ n) - h (a + (i : ℝ) * L / 2 ^ n) ≤ ((j : ℝ) - i) * (ρ ^ n * D) := by
    intro i j hij hjN
    induction j, hij using Nat.le_induction with
    | base => simp
    | succ j hij ih =>
      have h1 := hinc j (by omega)
      have h2 := ih (by omega)
      push_cast
      linarith
  have hP0 : a + ((0 : ℕ) : ℝ) * L / 2 ^ n = a := by simp
  have hPN : a + (((2 ^ n : ℕ)) : ℝ) * L / 2 ^ n = a + L := by
    push_cast
    field_simp
  -- the chord at `P k` is `h a + (k / 2ⁿ) D`
  have hchord : ∀ k : ℕ, (a + (k : ℝ) * L / 2 ^ n - a) / L * D = (k : ℝ) * (1 / 2) ^ n * D := by
    intro k
    rw [one_div_pow]
    field_simp
    ring
  -- the deviation at the dyadic points
  have hdev : ∀ k : ℕ, k ≤ 2 ^ n →
      |h (a + (k : ℝ) * L / 2 ^ n) - (h a + (a + (k : ℝ) * L / 2 ^ n - a) / L * D)| ≤ D * ((2 * ρ) ^ n - 1) := by
    intro k hk
    have hkR : (k : ℝ) ≤ 2 ^ n := by exact_mod_cast hk
    have hup := hG 0 k (Nat.zero_le k) hk
    have hlo := hG k (2 ^ n) hk le_rfl
    rw [hP0] at hup
    rw [hPN] at hlo
    push_cast at hup hlo
    rw [hchord k, abs_le, h2ρ]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hd : 0 ≤ ρ ^ n - (1 / 2) ^ n := by linarith
    constructor
    · -- `h(P k) − chord ≥ −(2ⁿ − k)(ρⁿ − 2⁻ⁿ) D`
      have e : D = h (a + L) - h a := rfl
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hkR) hd) hD0, mul_nonneg hk0 hD0]
    · nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hkR) hd) hD0, mul_nonneg (mul_nonneg hk0 hd) hD0]
  intro t ht
  obtain ⟨ht1, ht2⟩ := ht
  have hR0 : 0 ≤ D * ((2 * ρ) ^ n - 1 + (1 / 2) ^ n) := by
    have : 1 ≤ (2 * ρ) ^ n := one_le_pow₀ (by linarith)
    have : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
    exact mul_nonneg hD0 (by linarith)
  rcases ht2.lt_or_eq with ht2 | rfl
  · -- `t ∈ [P k, P (k + 1)]` with `k = ⌊(t − a) 2ⁿ / L⌋`
    set s : ℝ := (t - a) * 2 ^ n / L with hs
    have hs0 : 0 ≤ s := by
      rw [hs]
      have : 0 ≤ t - a := by linarith
      positivity
    have hsN : s < 2 ^ n := by
      rw [hs, div_lt_iff₀ hL]
      nlinarith
    set k : ℕ := ⌊s⌋₊ with hk
    have hk1 : (k : ℝ) ≤ s := Nat.floor_le hs0
    have hk2 : s < (k : ℝ) + 1 := Nat.lt_floor_add_one s
    have hkN : k < 2 ^ n := by
      have : (k : ℝ) < 2 ^ n := lt_of_le_of_lt hk1 hsN
      exact_mod_cast this
    have hts : t = a + s * L / 2 ^ n := by
      rw [hs]
      field_simp
      ring
    have hPk : a + (k : ℝ) * L / 2 ^ n ≤ t := by
      rw [hts]
      have : (k : ℝ) * L / 2 ^ n ≤ s * L / 2 ^ n := by gcongr
      linarith
    have hPk1 : t ≤ a + ((k + 1 : ℕ) : ℝ) * L / 2 ^ n := by
      rw [hts]
      push_cast
      have : s * L / 2 ^ n ≤ ((k : ℝ) + 1) * L / 2 ^ n := by gcongr
      linarith
    have hd1 := hdev k hkN.le
    have hd2 := hdev (k + 1) hkN
    have hm1 : h (a + (k : ℝ) * L / 2 ^ n) ≤ h t := hmono.monotone hPk
    have hm2 : h t ≤ h (a + ((k + 1 : ℕ) : ℝ) * L / 2 ^ n) := hmono.monotone hPk1
    -- the chord moves by `D / 2ⁿ` between consecutive dyadic points
    have hc1 : (a + (k : ℝ) * L / 2 ^ n - a) / L * D ≤ (t - a) / L * D := by
      apply mul_le_mul_of_nonneg_right _ hD0
      exact div_le_div_of_nonneg_right (by linarith) hL.le
    have hc2 : (t - a) / L * D ≤ (a + ((k + 1 : ℕ) : ℝ) * L / 2 ^ n - a) / L * D := by
      apply mul_le_mul_of_nonneg_right _ hD0
      exact div_le_div_of_nonneg_right (by linarith) hL.le
    have hgap : (a + ((k + 1 : ℕ) : ℝ) * L / 2 ^ n - a) / L * D - (a + (k : ℝ) * L / 2 ^ n - a) / L * D =
        D * (1 / 2) ^ n := by
      rw [hchord, hchord]
      push_cast
      ring
    rw [abs_le] at hd1 hd2 ⊢
    constructor <;> nlinarith
  · -- `t = a + L`: the deviation is `0`
    have e : h (a + L) - (h a + (a + L - a) / L * D) = 0 := by
      field_simp
      rw [hD]
      ring
    rw [e, abs_zero]
    exact hR0

/-- Helper for `lemma16_4` and `cor16_2_3_a` (§16.3, circle layer). A sense-preserving circle homeomorphism has a lift:
from `h(e^{it}) = e^{iu(t)}` (`u(t + 2π) = u(t) + 2π`), `h̃(x) = (u(2πx) − 2πm)/(2π)` with `m = ⌊u(0)/(2π)⌋`. -/
theorem gl16_cl_lift {h : ℂ → ℂ} (hh : Pommerenke1992.IsSensePreservingCircleHomeo h) :
    ∃ hl : ℝ → ℝ, IsCircleLift h hl := by
  obtain ⟨u, huc, hum, hup, hu⟩ := hh
  have hπ := Real.pi_pos
  set m : ℤ := ⌊u 0 / (2 * π)⌋ with hm
  have hm1 : (m : ℝ) ≤ u 0 / (2 * π) := Int.floor_le _
  have hm2 : u 0 / (2 * π) < m + 1 := Int.lt_floor_add_one _
  refine ⟨fun x => (u (2 * π * x) - 2 * π * m) / (2 * π), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((huc.comp (continuous_const.mul continuous_id)).sub continuous_const).div_const _
  · intro a b hab
    show (u (2 * π * a) - 2 * π * m) / (2 * π) < (u (2 * π * b) - 2 * π * m) / (2 * π)
    have := hum (show 2 * π * a < 2 * π * b by nlinarith)
    apply div_lt_div_of_pos_right _ (by positivity)
    linarith
  · show 0 ≤ (u (2 * π * 0) - 2 * π * m) / (2 * π)
    rw [mul_zero]
    apply div_nonneg _ (by positivity)
    rw [le_div_iff₀ (by positivity)] at hm1
    linarith
  · show (u (2 * π * 0) - 2 * π * m) / (2 * π) < 1
    rw [mul_zero, div_lt_one (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hm2
    linarith
  · intro x
    show (u (2 * π * (x + 1)) - 2 * π * m) / (2 * π) = (u (2 * π * x) - 2 * π * m) / (2 * π) + 1
    rw [show 2 * π * (x + 1) = 2 * π * x + 2 * π by ring, hup]
    field_simp
    ring
  · intro x
    show exp (2 * π * I * (((u (2 * π * x) - 2 * π * m) / (2 * π) : ℝ) : ℂ)) = h (exp (2 * π * I * x))
    have e1 : (2 * π * I * (x : ℂ)) = ((2 * π * x : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [e1, hu (2 * π * x)]
    have e2 : (2 * π * I * (((u (2 * π * x) - 2 * π * m) / (2 * π) : ℝ) : ℂ)) =
        (u (2 * π * x) : ℂ) * I - m * (2 * π * I) := by
      push_cast
      field_simp
    rw [e2, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

/-- Helper for `lemma16_4` (§16.3, circle layer). The lift is an increasing homeomorphism of `ℝ` (continuous, strictly
increasing, `h̃(x + 1) = h̃(x) + 1`, hence onto); its inverse `h̃⁻¹` is continuous and strictly increasing. -/
theorem gl16_cl_lift_inv {h : ℂ → ℂ} {hl : ℝ → ℝ} (hlift : IsCircleLift h hl) :
    ∃ hi : ℝ → ℝ, Continuous hi ∧ StrictMono hi ∧ (∀ x, hl (hi x) = x) ∧ ∀ x, hi (hl x) = x := by
  obtain ⟨hc, hm, -, -, hper, -⟩ := hlift
  have hb : ∀ s, s - 1 + hl 0 ≤ hl s ∧ hl s ≤ s + 1 + hl 0 := fun s => by
    have h := gl16_lift_incr_floor hm.monotone hper 0 s
    rw [zero_add] at h
    have h1 := Int.floor_le s
    have h2 := Int.lt_floor_add_one s
    constructor <;> linarith [h.1, h.2]
  have htop : Tendsto hl atTop atTop :=
    tendsto_atTop_mono (fun s => (hb s).1) (tendsto_atTop_add_const_right _ _
      (tendsto_atTop_add_const_right _ _ tendsto_id))
  have hbot : Tendsto hl atBot atBot :=
    tendsto_atBot_mono (fun s => (hb s).2) (tendsto_atBot_add_const_right _ _
      (tendsto_atBot_add_const_right _ _ tendsto_id))
  set e := StrictMono.orderIsoOfSurjective hl hm (hc.surjective htop hbot) with he
  refine ⟨e.symm, e.symm.continuous, e.symm.strictMono, fun x => ?_, fun x => ?_⟩
  · exact StrictMono.orderIsoOfSurjective_self_symm_apply hl hm _ x
  · exact StrictMono.orderIsoOfSurjective_symm_apply_self hl hm _ x

/-- Helper for `lemma16_4` (§16.3, circle layer). Ahlfors' quasisymmetry (5.1.1) gives the `M`-condition (16.1): the
triple `e^{i(x ± t)}, e^{ix}` has equal chords, so both ratios are bounded by the Ahlfors constant (the denominators
are positive by injectivity). -/
theorem gl16_cl_M_of_qsA {h : ℂ → ℂ} (hq : Pommerenke1992.IsQuasisymmetricA h) : ∃ M : ℝ, IsMCondition h M := by
  obtain ⟨-, hinj, M, hM⟩ := hq
  refine ⟨M, fun x t ht => ?_⟩
  have hs : ∀ θ : ℝ, exp ((θ : ℂ) * I) ∈ sphere (0 : ℂ) 1 := fun θ => by
    rw [mem_sphere_zero_iff_norm]
    exact norm_exp_ofReal_mul_I θ
  have e1 : exp (((x : ℂ) + t) * I) = exp ((x : ℂ) * I) * exp ((t : ℂ) * I) := by
    rw [add_mul, Complex.exp_add]
  have e3 : exp ((x : ℂ) * I) = exp (((x : ℂ) - t) * I) * exp ((t : ℂ) * I) := by
    rw [← Complex.exp_add]
    ring_nf
  have hne : exp ((t : ℂ) * I) ≠ 1 := by
    intro h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
    apply ht n
    have h2 : ((t : ℂ)) = (((2 * π * n : ℝ)) : ℂ) := by
      have hI : (I : ℂ) ≠ 0 := I_ne_zero
      apply mul_right_cancel₀ hI
      rw [hn]
      push_cast
      ring
    exact_mod_cast h2
  have hL : ‖exp (((x : ℂ) + t) * I) - exp ((x : ℂ) * I)‖ = ‖exp ((t : ℂ) * I) - 1‖ := by
    rw [e1, ← mul_sub_one, norm_mul, norm_exp_ofReal_mul_I, one_mul]
  have hR : ‖exp ((x : ℂ) * I) - exp (((x : ℂ) - t) * I)‖ = ‖exp ((t : ℂ) * I) - 1‖ := by
    rw [e3, ← mul_sub_one, norm_mul, show ((x : ℂ) - t) = ((x - t : ℝ) : ℂ) by push_cast; ring,
      norm_exp_ofReal_mul_I, one_mul]
  have hch : ‖exp (((x : ℂ) + t) * I) - exp ((x : ℂ) * I)‖ = ‖exp ((x : ℂ) * I) - exp (((x : ℂ) - t) * I)‖ := by
    rw [hL, hR]
  have hx1 : exp ((x : ℂ) * I) ≠ exp (((x : ℂ) + t) * I) := by
    rw [e1]
    intro h0
    apply hne
    have := (mul_eq_left₀ (Complex.exp_ne_zero _)).1 h0.symm
    exact this
  have hx3 : exp (((x : ℂ) - t) * I) ≠ exp ((x : ℂ) * I) := by
    rw [e3]
    intro h0
    apply hne
    exact ((mul_eq_left₀ (Complex.exp_ne_zero _)).1 h0.symm)
  have hs1 : exp (((x : ℂ) + t) * I) ∈ sphere (0 : ℂ) 1 := by
    rw [show ((x : ℂ) + t) = ((x + t : ℝ) : ℂ) by push_cast; ring]; exact hs _
  have hs3 : exp (((x : ℂ) - t) * I) ∈ sphere (0 : ℂ) 1 := by
    rw [show ((x : ℂ) - t) = ((x - t : ℝ) : ℂ) by push_cast; ring]; exact hs _
  have hA : 0 < ‖h (exp (((x : ℂ) + t) * I)) - h (exp ((x : ℂ) * I))‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 fun h0 => hx1 (hinj (hs x) hs1 h0.symm))
  have hB : 0 < ‖h (exp ((x : ℂ) * I)) - h (exp (((x : ℂ) - t) * I))‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 fun h0 => hx3 (hinj hs3 (hs x) h0.symm))
  have h1 := hM _ hs1 _ (hs x) _ hs3 hch
  have h2 := hM _ hs3 _ (hs x) _ hs1 (by rw [norm_sub_rev, ← hch, norm_sub_rev])
  rw [norm_sub_rev (h (exp (((x : ℂ) - t) * I))) (h (exp ((x : ℂ) * I))),
    norm_sub_rev (h (exp ((x : ℂ) * I))) (h (exp (((x : ℂ) + t) * I)))] at h2
  have hMpos : 0 < M := by
    by_contra hM0
    have : M * ‖h (exp (((x : ℂ) + t) * I)) - h (exp ((x : ℂ) * I))‖ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hM0) hA.le
    linarith
  constructor
  · rw [div_le_div_iff₀ hMpos hB, one_mul]
    linarith
  · rw [div_le_iff₀ hB]
    exact h1

/-- Helper for `cor16_2_3_a` (§16.3, circle layer). Conversely, a continuous injective map of the circle with the
`M`-condition is quasisymmetric in Ahlfors' sense: two points at equal chordal distance from `z₂ = e^{ix}` are
`e^{i(x ± t)}` (equal chords `|e^{ia} − 1| = |e^{ib} − 1|` force `e^{ia} = e^{±ib}`). -/
theorem gl16_cl_qsA_of_M {h : ℂ → ℂ} (hc : ContinuousOn h (sphere 0 1)) (hi : InjOn h (sphere 0 1)) {M : ℝ}
    (hM : IsMCondition h M) : Pommerenke1992.IsQuasisymmetricA h := by
  refine ⟨hc, hi, max M 1, fun z₁ hz₁ z₂ hz₂ z₃ hz₃ hd => ?_⟩
  have hM0 : 0 ≤ max M 1 := le_trans zero_le_one (le_max_right _ _)
  have hpolar : ∀ z : ℂ, z ∈ sphere (0 : ℂ) 1 → exp ((arg z : ℂ) * I) = z := fun z hz => by
    have h1 : ‖z‖ = 1 := by simpa using hz
    have h3 := norm_mul_exp_arg_mul_I z
    rwa [h1, Complex.ofReal_one, one_mul] at h3
  have hper : ∀ (θ : ℝ) (k : ℤ), exp (((θ + 2 * π * k : ℝ) : ℂ) * I) = exp ((θ : ℂ) * I) := fun θ k => by
    push_cast
    rw [add_mul, Complex.exp_add, show (2 * π * (k : ℂ)) * I = k * (2 * π * I) by ring,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  set x := arg z₂ with hx
  set t := arg z₁ - x with ht
  set s := x - arg z₃ with hs
  have e1 : z₁ = exp (((x : ℂ) + t) * I) := by
    rw [← hpolar z₁ hz₁, ht]
    push_cast
    ring_nf
  have e2 : z₂ = exp ((x : ℂ) * I) := (hpolar z₂ hz₂).symm
  have e3 : z₃ = exp (((x : ℂ) - s) * I) := by
    rw [← hpolar z₃ hz₃, hs]
    push_cast
    ring_nf
  -- equal chords force `z₃ = z₁` or `z₃ = e^{i(x − t)}`
  have hchord : ∀ θ : ℝ, ‖exp ((θ : ℂ) * I) - 1‖ = 2 * |Real.sin (θ / 2)| := fun θ => by
    rw [mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_two]
  have hd' : |Real.sin (t / 2)| = |Real.sin (s / 2)| := by
    have h1 : ‖z₁ - z₂‖ = 2 * |Real.sin (t / 2)| := by
      rw [e1, e2, add_mul, Complex.exp_add, ← mul_sub_one, norm_mul, norm_exp_ofReal_mul_I, one_mul, hchord]
    have h2 : ‖z₂ - z₃‖ = 2 * |Real.sin (s / 2)| := by
      have : exp ((x : ℂ) * I) = exp (((x : ℂ) - s) * I) * exp ((s : ℂ) * I) := by
        rw [← Complex.exp_add]
        ring_nf
      rw [e2, e3, this, ← mul_sub_one, norm_mul,
        show ((x : ℂ) - s) = ((x - s : ℝ) : ℂ) by push_cast; ring, norm_exp_ofReal_mul_I, one_mul, hchord]
    linarith [hd]
  have hcos : Real.cos t = Real.cos s := by
    have h1 : Real.sin (t / 2) ^ 2 = Real.sin (s / 2) ^ 2 := by
      rw [← sq_abs, hd', sq_abs]
    have h2 : ∀ θ : ℝ, Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := fun θ => by
      have h3 := Real.cos_sq_add_sin_sq (θ / 2)
      have h4 := Real.cos_two_mul (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring] at h4
      linarith
    rw [h2 t, h2 s, h1]
  obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.1 hcos
  · -- `s = 2kπ + t`: `z₃ = e^{i(x − t)}`
    have e3' : z₃ = exp (((x : ℂ) - t) * I) := by
      rw [e3, hk, show ((x : ℂ) - ((2 * k * π + t : ℝ) : ℂ)) = (((x - t) + 2 * π * (-k : ℤ) : ℝ) : ℂ) by
        push_cast; ring, hper]
      push_cast
      ring_nf
    by_cases htk : ∀ k : ℤ, t ≠ 2 * π * k
    · obtain ⟨hch, hpos⟩ := gl16_cl_chord x t htk
      have hne : exp ((x : ℂ) * I) ≠ exp (((x : ℂ) - t) * I) := fun h0 => by
        rw [h0, sub_self, norm_zero] at hpos
        exact lt_irrefl _ hpos
      have hs3 : exp (((x : ℂ) - t) * I) ∈ sphere (0 : ℂ) 1 := e3' ▸ hz₃
      have hB : 0 < ‖h (exp ((x : ℂ) * I)) - h (exp (((x : ℂ) - t) * I))‖ :=
        norm_pos_iff.2 (sub_ne_zero.2 fun h0 => hne (hi (e2 ▸ hz₂) hs3 h0))
      have h1 := (hM x t htk).2
      rw [div_le_iff₀ hB] at h1
      rw [e1, e2, e3']
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · push Not at htk
      obtain ⟨m, hm⟩ := htk
      have h12 : z₁ = z₂ := by
        rw [e1, e2, show ((x : ℂ) + t) = ((x + 2 * π * m : ℝ) : ℂ) by rw [hm]; push_cast; ring, hper]
      rw [h12, sub_self, norm_zero]
      exact mul_nonneg hM0 (norm_nonneg _)
  · -- `s = 2kπ − t`: `z₃ = z₁`
    have e31 : z₃ = z₁ := by
      rw [e3, e1, hk, show ((x : ℂ) - ((2 * k * π - t : ℝ) : ℂ)) = (((x + t) + 2 * π * (-k : ℤ) : ℝ) : ℂ) by
        push_cast; ring, hper]
      push_cast
      ring_nf
    rw [e31, norm_sub_rev (h z₂)]
    exact le_mul_of_one_le_left (norm_nonneg _) (le_max_right _ _)

/-- Helper for `lemma16_4` (§16.3, circle layer). Small rotations are in every `U(δ)`: `z ↦ e^{2πiσ} z` is a
sense-preserving isometry of the circle (ratio `1`), its inverse is the rotation by `−σ`, and `|e^{2πiσ} − 1| < δ`
for `|σ|` small. -/
theorem gl16_cl_rot {δ : ℝ} (hδ : 0 < δ) :
    ∃ τ > 0, ∀ σ : ℝ, |σ| < τ → (fun z : ℂ => exp (2 * π * σ * I) * z) ∈ qsNbhdU δ := by
  have hcont : Continuous fun σ : ℝ => exp (2 * π * (σ : ℂ) * I) := by fun_prop
  obtain ⟨τ, hτ, hτ'⟩ := Metric.continuousAt_iff.1 hcont.continuousAt δ hδ
  refine ⟨τ, hτ, fun σ hσ => ?_⟩
  have hn : ∀ θ : ℝ, ‖exp ((θ : ℂ) * I)‖ = 1 := norm_exp_ofReal_mul_I
  set c : ℂ := exp (2 * π * (σ : ℂ) * I) with hc
  have hcr : c = exp (((2 * π * σ : ℝ) : ℂ) * I) := by
    rw [hc]
    push_cast
    ring_nf
  have hc1 : ‖c‖ = 1 := by rw [hcr]; exact hn _
  have hcδ : ‖c - 1‖ < δ := by
    have h := hτ' (show dist σ 0 < τ by rwa [Real.dist_0_eq_abs])
    rw [dist_eq_norm] at h
    simpa using h
  have hc0 : c ≠ 0 := Complex.exp_ne_zero _
  refine ⟨?_, ?_, fun z hz => ?_, fun x t ht => ?_⟩
  · -- sense-preserving: `u(t) = t + 2πσ`
    refine ⟨fun t => t + 2 * π * σ, by fun_prop, fun a b hab => by simp only; linarith, fun t => by ring,
      fun t => ?_⟩
    show c * exp ((t : ℂ) * I) = exp (((t + 2 * π * σ : ℝ) : ℂ) * I)
    rw [hcr, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · -- an isometry of the circle
    refine ⟨(continuous_const.mul continuous_id).continuousOn, fun z₁ _ z₂ _ h => mul_left_cancel₀ hc0 h, 1,
      fun z₁ _ z₂ _ z₃ _ h => ?_⟩
    show ‖c * z₁ - c * z₂‖ ≤ 1 * ‖c * z₂ - c * z₃‖
    rw [← mul_sub, ← mul_sub, norm_mul, norm_mul, hc1, h]
    simp
  · -- near the identity, and so is the inverse
    have hz1 : ‖z‖ = 1 := by simpa using hz
    have hR : ∀ w : ℂ, ‖w‖ = 1 → ‖c * w - w‖ < δ := fun w hw => by
      rw [show c * w - w = (c - 1) * w by ring, norm_mul, hw, mul_one]
      exact hcδ
    refine ⟨hR z hz1, ?_⟩
    have hmem : ∃ a ∈ sphere (0 : ℂ) 1, c * a = z := by
      refine ⟨c⁻¹ * z, ?_, by field_simp⟩
      rw [mem_sphere_zero_iff_norm, norm_mul, norm_inv, hc1, hz1, inv_one, one_mul]
    set w := Function.invFunOn (fun w : ℂ => c * w) (sphere 0 1) z with hwdef
    have hw : w ∈ sphere (0 : ℂ) 1 := Function.invFunOn_mem hmem
    have hw' : c * w = z := Function.invFunOn_eq hmem
    have hw1 : ‖w‖ = 1 := by simpa using hw
    calc ‖w - z‖ = ‖c * w - w‖ := by rw [← hw', norm_sub_rev]
      _ < δ := hR w hw1
  · -- the ratio is `1`
    show 1 / (1 + δ) ≤ ‖c * exp (((x : ℂ) + t) * I) - c * exp ((x : ℂ) * I)‖ /
        ‖c * exp ((x : ℂ) * I) - c * exp (((x : ℂ) - t) * I)‖ ∧
      ‖c * exp (((x : ℂ) + t) * I) - c * exp ((x : ℂ) * I)‖ /
        ‖c * exp ((x : ℂ) * I) - c * exp (((x : ℂ) - t) * I)‖ ≤ 1 + δ
    rw [← mul_sub, ← mul_sub, norm_mul, norm_mul, hc1, one_mul, one_mul]
    obtain ⟨hch, hpos⟩ := gl16_cl_chord x t ht
    rw [hch, div_self hpos.ne']
    constructor
    · rw [div_le_one (by linarith)]
      linarith
    · linarith

/-- Helper for `lemma16_4` (§16.3, circle layer). The lift of the conjugate `h ∘ R_σ ∘ h⁻¹` of the rotation by `2πσ` is
`y ↦ h̃(h̃⁻¹(y) + σ)` (`h⁻¹` is `invFunOn h` on the circle, where `h` is injective by its lift). -/
theorem gl16_cl_conj {h : ℂ → ℂ} {hl hi : ℝ → ℝ} (hlift : IsCircleLift h hl) (hli : ∀ x, hl (hi x) = x)
    (hil : ∀ x, hi (hl x) = x) (σ y : ℝ) :
    exp (2 * π * I * hl (hi y + σ)) =
      (h ∘ (fun z : ℂ => exp (2 * π * σ * I) * z) ∘ Function.invFunOn h (sphere 0 1)) (exp (2 * π * I * y)) := by
  have _hil := hil  -- not needed: only `h̃ ∘ h̃⁻¹ = id` is used
  have hinj := gl16_cl_lift_injOn hlift
  have hlh := hlift.2.2.2.2.2
  have hp : exp (2 * π * I * (hi y : ℂ)) ∈ sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, show (2 * π * I * (hi y : ℂ)) = ((2 * π * hi y : ℝ) : ℂ) * I by push_cast; ring]
    exact norm_exp_ofReal_mul_I _
  have hhp : h (exp (2 * π * I * (hi y : ℂ))) = exp (2 * π * I * (y : ℂ)) := by
    rw [← hlh, hli]
  have hinv : Function.invFunOn h (sphere 0 1) (exp (2 * π * I * (y : ℂ))) = exp (2 * π * I * (hi y : ℂ)) := by
    rw [← hhp]
    exact hinj.leftInvOn_invFunOn hp
  show exp (2 * π * I * (hl (hi y + σ) : ℂ)) =
    h (exp (2 * π * (σ : ℂ) * I) * Function.invFunOn h (sphere 0 1) (exp (2 * π * I * (y : ℂ))))
  rw [hinv, ← Complex.exp_add, hlh]
  congr 2
  push_cast
  ring

/-- Helper for `lemma16_4` (§16.3, circle layer). The `M`-condition `1 + ε` on the circle gives the ratio condition
`1 + 8 max(ε, (πζ)²)` for the lift at symmetric triples whose two increments are at most `ζ`
(`gl16_ratio_lift2` and `gl16_sin_ratio_conv`). -/
theorem gl16_cl_ratio {g : ℂ → ℂ} {gl : ℝ → ℝ} {ε ζ : ℝ} (hM : IsMCondition g (1 + ε)) (hε : 0 ≤ ε)
    (hlg : ∀ y : ℝ, exp (2 * π * I * gl y) = g (exp (2 * π * I * y))) (hη : max ε ((π * ζ) ^ 2) ≤ 1 / 2)
    {y s : ℝ} (hs : 0 < s) (hs1 : s < 1) (hp : 0 < gl (y + s) - gl y) (hp' : gl (y + s) - gl y ≤ ζ)
    (hm : 0 < gl y - gl (y - s)) (hm' : gl y - gl (y - s) ≤ ζ) :
    1 / (1 + 8 * max ε ((π * ζ) ^ 2)) ≤ LiZhongQC.qsRatio gl y s ∧
      LiZhongQC.qsRatio gl y s ≤ 1 + 8 * max ε ((π * ζ) ^ 2) := by
  set η : ℝ := max ε ((π * ζ) ^ 2) with hηdef
  have hπ := Real.pi_pos
  have hζ0 : 0 < ζ := lt_of_lt_of_le hp hp'
  have hη0 : 0 < η := lt_max_of_lt_right (by positivity)
  have hπζ : π * ζ < π := by
    have h1 : (π * ζ) ^ 2 ≤ 1 / 2 := le_trans (le_max_right _ _) hη
    have h2 : π * ζ < 1 := by nlinarith
    linarith [Real.pi_gt_three]
  -- the chord ratio at `(2πy, 2πs)`
  have hk : ∀ k : ℤ, 2 * π * s ≠ 2 * π * k := by
    intro k hk
    have h1 : s = k := by
      have := mul_left_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0) hk
      exact this
    rcases le_or_gt k 0 with hk0 | hk0
    · have : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
      linarith
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
      linarith
  obtain ⟨hr1, hr2⟩ := hM (2 * π * y) (2 * π * s) hk
  have hrl := gl16_ratio_lift2 hlg y s
  push_cast at hr1 hr2 hrl
  rw [hrl] at hr1 hr2
  -- the sines are positive
  have hsp : 0 < Real.sin (π * (gl (y + s) - gl y)) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  have hsm : 0 < Real.sin (π * (gl y - gl (y - s))) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  rw [abs_of_pos hsp, abs_of_pos hsm] at hr1 hr2
  have hεη : ε ≤ η := le_max_left _ _
  have h1 : (1 - η) * Real.sin (π * (gl y - gl (y - s))) ≤ Real.sin (π * (gl (y + s) - gl y)) := by
    have h3 := (le_div_iff₀ hsm).1 hr1
    have h4 : (1 - η) * (1 + ε) ≤ 1 := by nlinarith
    have h5 : 1 - η ≤ 1 / (1 + ε) := by rw [le_div_iff₀ (by linarith)]; exact h4
    nlinarith
  have h2 : Real.sin (π * (gl (y + s) - gl y)) ≤ (1 + η) * Real.sin (π * (gl y - gl (y - s))) := by
    have h3 := (div_le_iff₀ hsm).1 hr2
    nlinarith
  have hsq : ∀ D : ℝ, 0 < D → D ≤ ζ → (π * D) ^ 2 ≤ η := fun D hD hDζ =>
    le_trans (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hDζ hπ.le) 2) (le_max_right _ _)
  have hconv := gl16_sin_ratio_conv hp hm hη0 hη h1 h2 (hsq _ hp hp') (hsq _ hm hm')
  have hq : LiZhongQC.qsRatio gl y s = (gl (y + s) - gl y) / (gl y - gl (y - s)) := rfl
  rw [hq]
  have hqpos : 0 < (gl (y + s) - gl y) / (gl y - gl (y - s)) := div_pos hp hm
  constructor
  · have h6 : ((gl (y + s) - gl y) / (gl y - gl (y - s)))⁻¹ ≤ 1 + 8 * η := by
      linarith [le_max_right ((gl (y + s) - gl y) / (gl y - gl (y - s)))
        ((gl (y + s) - gl y) / (gl y - gl (y - s)))⁻¹]
    rw [one_div]
    exact (inv_le_comm₀ hqpos (by positivity)).1 h6
  · linarith [le_max_left ((gl (y + s) - gl y) / (gl y - gl (y - s)))
      ((gl (y + s) - gl y) / (gl y - gl (y - s)))⁻¹]

/-- Helper for `lemma16_4` (§16.3, circle layer). Uniform near-affinity: for every `η > 0` there is `δ > 0` such that
the ratio condition `1 + δ` on all symmetric triples of `[a, a + L]` puts `G` within `η (G(a + L) − G(a))` of its
chord on `[a, a + L]` (`gl16_bal_near_affine` with `n` large, then `δ` small). -/
theorem gl16_cl_affine3 : ∀ η > 0, ∃ δ > 0, ∀ G : ℝ → ℝ, StrictMono G → ∀ a L : ℝ, 0 < L →
    (∀ x t : ℝ, 0 < t → a ≤ x - t → x + t ≤ a + L →
      1 / (1 + δ) ≤ LiZhongQC.qsRatio G x t ∧ LiZhongQC.qsRatio G x t ≤ 1 + δ) →
    ∀ p ∈ Icc a (a + L), |G p - (G a + (p - a) / L * (G (a + L) - G a))| ≤ η * (G (a + L) - G a) := by
  intro η hη
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hη) (by norm_num : (1 / 2 : ℝ) < 1)
  have hcont : ContinuousAt (fun δ : ℝ => (2 * ((1 + δ) / (2 + δ))) ^ n) 0 :=
    (continuousAt_const.mul ((continuousAt_const.add continuousAt_id).div
      (continuousAt_const.add continuousAt_id) (by norm_num))).pow n
  have hval : (fun δ : ℝ => (2 * ((1 + δ) / (2 + δ))) ^ n) 0 = 1 := by norm_num
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
    (hcont.eventually (gt_mem_nhds (show (fun δ : ℝ => (2 * ((1 + δ) / (2 + δ))) ^ n) 0 < 1 + η / 2 by
      rw [hval]; linarith)))
  refine ⟨ε / 2, half_pos hε, fun G hG a L hL hr p hp => ?_⟩
  have hδ : (2 * ((1 + ε / 2) / (2 + ε / 2))) ^ n < 1 + η / 2 :=
    hball (by rw [Real.dist_0_eq_abs, abs_of_pos (half_pos hε)]; linarith)
  have h := gl16_cl_near_affine hG hL (half_pos hε).le hr n p hp
  have hD : 0 ≤ G (a + L) - G a := sub_nonneg.2 (hG.monotone (by linarith))
  calc |G p - (G a + (p - a) / L * (G (a + L) - G a))| ≤
        (G (a + L) - G a) * ((2 * ((1 + ε / 2) / (2 + ε / 2))) ^ n - 1 + (1 / 2) ^ n) := h
    _ ≤ (G (a + L) - G a) * η := mul_le_mul_of_nonneg_left (by linarith) hD
    _ = η * (G (a + L) - G a) := mul_comm _ _

/-- Helper for `lemma16_4` (§16.3, the chain of Lemma 4's proof). Let `H` be `M₁`-quasisymmetric and let the
fractions `Fₖ = λₖ/(λₖ + λₖ₊₁)`, `λₖ = H(x + kt) − H(x + (k − 1)t)`, move by at most `η` per step for `k < 2j`. If
`2jη ≤ κ(γ)` and `M₁ < (1 + γ/2)ʲ`, then `max(r, 1/r) ≤ 1 + γ` for `r = H`'s ratio at `(x, t)`. Otherwise
`F₀ = 1/(1 + r)` is off `1/2` by more than `κ(γ)`, so all `Fₖ` (`k ≤ 2j`) stay on that side, and the consecutive
increments grow (or shrink) geometrically by `1 + γ/2`. Then the ratio of `H` at `(x + jt, jt)` exceeds `M₁` (or is
below `1/M₁`). -/
theorem gl16_cl_chain {H : ℝ → ℝ} (hmono : StrictMono H) {M₁ : ℝ}
    (hq : ∀ x t : ℝ, 0 < t → M₁⁻¹ ≤ LiZhongQC.qsRatio H x t ∧ LiZhongQC.qsRatio H x t ≤ M₁) {x t γ η : ℝ} {j : ℕ}
    (ht : 0 < t) (hγ : 0 < γ) (hj : M₁ < (1 + γ / 2) ^ j)
    (hη : 2 * j * η ≤ γ / 2 / ((2 + γ / 2) * (2 + γ)))
    (hF : ∀ k : ℕ, k < 2 * j →
      |(H (x + ((k : ℝ) + 1) * t) - H (x + k * t)) / (H (x + ((k : ℝ) + 2) * t) - H (x + k * t)) -
        (H (x + k * t) - H (x + ((k : ℝ) - 1) * t)) / (H (x + ((k : ℝ) + 1) * t) - H (x + ((k : ℝ) - 1) * t))| ≤
        η) :
    max (LiZhongQC.qsRatio H x t) (LiZhongQC.qsRatio H x t)⁻¹ ≤ 1 + γ := by
  -- the increments `λₖ = H(x + kt) − H(x + (k − 1)t)`
  set lam : ℕ → ℝ := fun k => H (x + (k : ℝ) * t) - H (x + ((k : ℝ) - 1) * t) with hlam
  have hlam_pos : ∀ k, 0 < lam k := fun k => sub_pos.2 (hmono (by linarith))
  have hlam1 : ∀ k : ℕ, lam (k + 1) = H (x + ((k : ℝ) + 1) * t) - H (x + k * t) := fun k => by
    show H (x + ((k + 1 : ℕ) : ℝ) * t) - H (x + (((k + 1 : ℕ) : ℝ) - 1) * t) = _
    rw [Nat.cast_succ, add_sub_cancel_right]
  have hlam2 : ∀ k : ℕ, lam (k + 2) = H (x + ((k : ℝ) + 2) * t) - H (x + ((k : ℝ) + 1) * t) := fun k => by
    show H (x + ((k + 2 : ℕ) : ℝ) * t) - H (x + (((k + 2 : ℕ) : ℝ) - 1) * t) = _
    have e : ((k + 2 : ℕ) : ℝ) - 1 = (k : ℝ) + 1 := by push_cast; ring
    rw [e]
    push_cast
    ring_nf
  -- the fractions `Fₖ = λₖ/(λₖ + λₖ₊₁)` and their drift
  set F : ℕ → ℝ := fun k => lam k / (lam k + lam (k + 1)) with hFdef
  have hF' : ∀ k, k < 2 * j → |F (k + 1) - F k| ≤ η := by
    intro k hk
    have h := hF k hk
    have e1 : H (x + ((k : ℝ) + 1) * t) - H (x + ((k : ℝ) - 1) * t) = lam k + lam (k + 1) := by
      rw [hlam1]
      simp only [hlam]
      ring
    have e2 : H (x + ((k : ℝ) + 2) * t) - H (x + k * t) = lam (k + 1) + lam (k + 2) := by
      rw [hlam1, hlam2]
      ring
    rw [e1, e2, ← hlam1] at h
    exact h
  have hM1 : 1 ≤ M₁ := by
    have h0 := hq x t ht
    have hr0 : 0 < LiZhongQC.qsRatio H x t := div_pos (sub_pos.2 (hmono (by linarith)))
      (sub_pos.2 (hmono (by linarith)))
    have hM : 0 < M₁ := lt_of_lt_of_le hr0 h0.2
    have h2 : M₁⁻¹ ≤ M₁ := h0.1.trans h0.2
    by_contra hlt
    have : 1 < M₁⁻¹ := (one_lt_inv₀ hM).2 (lt_of_not_ge hlt)
    linarith
  have hj1 : 1 ≤ j := by
    by_contra h0
    have h0' : j = 0 := by omega
    rw [h0', pow_zero] at hj
    linarith
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hF' 0 (by omega))
  have hdrift : ∀ k, k ≤ 2 * j → |F k - F 0| ≤ k * η := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have h2 := hF' m (by omega)
      calc |F (m + 1) - F 0| ≤ |F (m + 1) - F m| + |F m - F 0| := abs_sub_le _ _ _
        _ ≤ η + m * η := add_le_add h2 h1
        _ = ((m + 1 : ℕ) : ℝ) * η := by push_cast; ring
  have hdrift' : ∀ k, k ≤ 2 * j → |F k - F 0| ≤ γ / 2 / ((2 + γ / 2) * (2 + γ)) := fun k hk => by
    have h1 := hdrift k hk
    have h2 : (k : ℝ) * η ≤ 2 * j * η := by
      apply mul_le_mul_of_nonneg_right _ hη0
      exact_mod_cast hk
    linarith
  -- `H`'s ratio at the base point, and at `(x + jt, jt)` through sums of increments
  have hl0 : lam 0 = H x - H (x - t) := by simp only [hlam]; push_cast; ring_nf
  have hl1 : lam 1 = H (x + t) - H x := by
    have := hlam1 0
    rw [this]
    push_cast
    ring_nf
  have hr : LiZhongQC.qsRatio H x t = lam 1 / lam 0 := by
    rw [hl0, hl1]
    rfl
  have hS : ∀ m n : ℕ, H (x + ((m + n : ℕ) : ℝ) * t) - H (x + (m : ℝ) * t) =
      ∑ i ∈ Finset.range n, lam (m + i + 1) := by
    intro m n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      simp only [hlam]
      push_cast
      ring_nf
  have hbig : LiZhongQC.qsRatio H (x + j * t) (j * t) =
      (∑ i ∈ Finset.range j, lam (j + i + 1)) / ∑ i ∈ Finset.range j, lam (0 + i + 1) := by
    rw [← hS, ← hS]
    show (H (x + j * t + j * t) - H (x + j * t)) / (H (x + j * t) - H (x + j * t - j * t)) = _
    push_cast
    ring_nf
  have hjt : 0 < (j : ℝ) * t := mul_pos (by exact_mod_cast hj1) ht
  have hθ : 1 < 1 + γ / 2 := by linarith
  have hSL : 0 < ∑ i ∈ Finset.range j, lam (0 + i + 1) :=
    Finset.sum_pos (fun i _ => hlam_pos _) (Finset.nonempty_range_iff.2 (by omega))
  have hSR : 0 < ∑ i ∈ Finset.range j, lam (j + i + 1) :=
    Finset.sum_pos (fun i _ => hlam_pos _) (Finset.nonempty_range_iff.2 (by omega))
  by_contra hcon
  rcases lt_max_iff.1 (not_le.1 hcon) with hA | hB
  · -- `r > 1 + γ`: the increments grow geometrically
    have hF0 : F 0 < 1 / (2 + γ) := by
      show lam 0 / (lam 0 + lam (0 + 1)) < 1 / (2 + γ)
      rw [hr, lt_div_iff₀ (hlam_pos 0)] at hA
      rw [div_lt_div_iff₀ (by linarith [hlam_pos 0, hlam_pos 1]) (by positivity)]
      linarith
    have hstep : ∀ k, k < 2 * j → (1 + γ / 2) * lam k < lam (k + 1) := by
      intro k hk
      have h1 := (abs_le.1 (hdrift' k hk.le)).2
      have hk' : F k < 1 / (2 + γ / 2) := by
        have : 1 / (2 + γ) + γ / 2 / ((2 + γ / 2) * (2 + γ)) = 1 / (2 + γ / 2) := by
          field_simp
          ring
        linarith
      have hk'' : lam k / (lam k + lam (k + 1)) < 1 / (2 + γ / 2) := hk'
      rw [div_lt_div_iff₀ (by linarith [hlam_pos k, hlam_pos (k + 1)]) (by positivity)] at hk''
      linarith
    have hgeo : ∀ i m : ℕ, i + m ≤ 2 * j → (1 + γ / 2) ^ m * lam i ≤ lam (i + m) := by
      intro i m
      induction m with
      | zero => intro _; simp
      | succ m ih =>
        intro hm
        have h1 := ih (by omega)
        have h2 := hstep (i + m) (by omega)
        calc (1 + γ / 2) ^ (m + 1) * lam i = (1 + γ / 2) * ((1 + γ / 2) ^ m * lam i) := by ring
          _ ≤ (1 + γ / 2) * lam (i + m) := mul_le_mul_of_nonneg_left h1 (by linarith)
          _ ≤ lam (i + (m + 1)) := by rw [← add_assoc]; exact h2.le
    have hsum : (1 + γ / 2) ^ j * ∑ i ∈ Finset.range j, lam (0 + i + 1) ≤
        ∑ i ∈ Finset.range j, lam (j + i + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      have := hgeo (0 + i + 1) j (by omega)
      rw [show 0 + i + 1 + j = j + i + 1 by ring] at this
      exact this
    have hq2 := (hq (x + j * t) (j * t) hjt).2
    rw [hbig] at hq2
    have h3 : (1 + γ / 2) ^ j ≤ (∑ i ∈ Finset.range j, lam (j + i + 1)) /
        ∑ i ∈ Finset.range j, lam (0 + i + 1) := by
      rw [le_div_iff₀ hSL]
      exact hsum
    linarith
  · -- `1/r > 1 + γ`: the increments shrink geometrically
    have hF0 : (1 + γ) / (2 + γ) < F 0 := by
      show (1 + γ) / (2 + γ) < lam 0 / (lam 0 + lam (0 + 1))
      have hr0 : 0 < lam 1 / lam 0 := div_pos (hlam_pos 1) (hlam_pos 0)
      rw [hr, inv_div, lt_div_iff₀ (hlam_pos 1)] at hB
      rw [div_lt_div_iff₀ (by positivity) (by linarith [hlam_pos 0, hlam_pos 1])]
      nlinarith
    have hstep : ∀ k, k < 2 * j → (1 + γ / 2) * lam (k + 1) < lam k := by
      intro k hk
      have h1 := (abs_le.1 (hdrift' k hk.le)).1
      have hk' : (1 + γ / 2) / (2 + γ / 2) < F k := by
        have : (1 + γ) / (2 + γ) - γ / 2 / ((2 + γ / 2) * (2 + γ)) = (1 + γ / 2) / (2 + γ / 2) := by
          field_simp
          ring
        linarith
      have hk'' : (1 + γ / 2) / (2 + γ / 2) < lam k / (lam k + lam (k + 1)) := hk'
      rw [div_lt_div_iff₀ (by positivity) (by linarith [hlam_pos k, hlam_pos (k + 1)])] at hk''
      nlinarith
    have hgeo : ∀ i m : ℕ, i + m ≤ 2 * j → (1 + γ / 2) ^ m * lam (i + m) ≤ lam i := by
      intro i m
      induction m with
      | zero => intro _; simp
      | succ m ih =>
        intro hm
        have h1 := ih (by omega)
        have h2 := hstep (i + m) (by omega)
        calc (1 + γ / 2) ^ (m + 1) * lam (i + (m + 1)) = (1 + γ / 2) ^ m * ((1 + γ / 2) * lam (i + m + 1)) := by
              rw [← add_assoc]; ring
          _ ≤ (1 + γ / 2) ^ m * lam (i + m) :=
              mul_le_mul_of_nonneg_left h2.le (pow_nonneg (by linarith) _)
          _ ≤ lam i := h1
    have hsum : (1 + γ / 2) ^ j * ∑ i ∈ Finset.range j, lam (j + i + 1) ≤
        ∑ i ∈ Finset.range j, lam (0 + i + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      have := hgeo (0 + i + 1) j (by omega)
      rw [show 0 + i + 1 + j = j + i + 1 by ring] at this
      exact this
    have hq1 := (hq (x + j * t) (j * t) hjt).1
    rw [hbig] at hq1
    have hpow : 0 < (1 + γ / 2) ^ j := pow_pos (by linarith) _
    have h3 : (∑ i ∈ Finset.range j, lam (j + i + 1)) / ∑ i ∈ Finset.range j, lam (0 + i + 1) ≤
        1 / (1 + γ / 2) ^ j := by
      rw [div_le_div_iff₀ hSL hpow, one_mul, mul_comm]
      exact hsum
    have h4 : 1 / (1 + γ / 2) ^ j < M₁⁻¹ := by
      rw [one_div]
      exact (inv_lt_inv₀ hpow (by linarith)).2 hj
    linarith

/-- Helper for `cor16_2_3_a` (§16.3, the example). The map `h₀(z) = z e^{i|z − 1|/2}` has the lift
`h̃₀(x) = x + |sin πx|/(2π)` (increasing: the perturbation is `1/2`-Lipschitz) and is a sense-preserving circle
homeomorphism (`h₀(e^{it}) = e^{i(t + |sin(t/2)|)}`, since `|e^{it} − 1| = 2|sin(t/2)|`). -/
theorem gl16_cl_corner_lift :
    IsCircleLift (fun z : ℂ => z * exp (I * ((‖z - 1‖ / 2 : ℝ) : ℂ))) (fun x : ℝ => x + |Real.sin (π * x)| / (2 * π)) ∧
      Pommerenke1992.IsSensePreservingCircleHomeo (fun z : ℂ => z * exp (I * ((‖z - 1‖ / 2 : ℝ) : ℂ))) := by
  have hπ := Real.pi_pos
  -- the increment bounds `(b − a)/2 ≤ h̃₀(b) − h̃₀(a)` for `a < b`
  have hinc : ∀ a b : ℝ, a < b →
      (b - a) / 2 ≤ (b + |Real.sin (π * b)| / (2 * π)) - (a + |Real.sin (π * a)| / (2 * π)) := by
    intro a b hab
    have hab' : |π * a - π * b| = π * (b - a) := by
      rw [← mul_sub, abs_mul, abs_of_pos hπ, abs_of_neg (by linarith), neg_sub]
    have h1 := (gl16_cl_abs_sin_lip (π * a) (π * b)).trans_eq hab'
    have h2 : |Real.sin (π * a)| - |Real.sin (π * b)| ≤ π * (b - a) := (le_abs_self _).trans h1
    have h3 : (|Real.sin (π * a)| - |Real.sin (π * b)|) / (2 * π) ≤ (b - a) / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have h4 : |Real.sin (π * a)| / (2 * π) - |Real.sin (π * b)| / (2 * π) ≤ (b - a) / 2 := by
      rw [← sub_div]
      exact h3
    linarith
  refine ⟨⟨?_, fun a b hab => ?_, ?_, ?_, fun x => ?_, fun x => ?_⟩, ?_⟩
  · exact continuous_id.add ((continuous_abs.comp (Real.continuous_sin.comp
      (continuous_const.mul continuous_id))).div_const _)
  · have := hinc a b hab
    show a + |Real.sin (π * a)| / (2 * π) < b + |Real.sin (π * b)| / (2 * π)
    linarith
  · show 0 ≤ (0 : ℝ) + |Real.sin (π * 0)| / (2 * π)
    simp
  · show (0 : ℝ) + |Real.sin (π * 0)| / (2 * π) < 1
    simp
  · show x + 1 + |Real.sin (π * (x + 1))| / (2 * π) = x + |Real.sin (π * x)| / (2 * π) + 1
    rw [mul_add, mul_one, Real.sin_add_pi, abs_neg]
    ring
  · show exp (2 * π * I * ((x + |Real.sin (π * x)| / (2 * π) : ℝ) : ℂ)) =
      exp (2 * π * I * (x : ℂ)) * exp (I * ((‖exp (2 * π * I * (x : ℂ)) - 1‖ / 2 : ℝ) : ℂ))
    rw [show (2 * π * I * (x : ℂ)) = ((2 * π * x : ℝ) : ℂ) * I by push_cast; ring, gl16_cl_norm_exp_sub_one,
      ← Complex.exp_add]
    congr 1
    rw [show 2 * π * x / 2 = π * x by ring]
    push_cast
    field_simp
  · -- sense-preserving: `u(t) = t + |sin(t/2)|`
    refine ⟨fun t => t + |Real.sin (t / 2)|, ?_, fun a b hab => ?_, fun t => ?_, fun t => ?_⟩
    · exact continuous_id.add (continuous_abs.comp (Real.continuous_sin.comp (continuous_id.div_const _)))
    · have hab' : |a / 2 - b / 2| = (b - a) / 2 := by
        rw [abs_of_neg (by linarith)]
        ring
      have h1 := (gl16_cl_abs_sin_lip (a / 2) (b / 2)).trans_eq hab'
      have h2 := (le_abs_self _).trans h1
      show a + |Real.sin (a / 2)| < b + |Real.sin (b / 2)|
      linarith
    · show t + 2 * π + |Real.sin ((t + 2 * π) / 2)| = t + |Real.sin (t / 2)| + 2 * π
      rw [show (t + 2 * π) / 2 = t / 2 + π by ring, Real.sin_add_pi, abs_neg]
      ring
    · show exp ((t : ℂ) * I) * exp (I * ((‖exp ((t : ℂ) * I) - 1‖ / 2 : ℝ) : ℂ)) =
        exp (((t + |Real.sin (t / 2)| : ℝ) : ℂ) * I)
      rw [gl16_cl_norm_exp_sub_one, ← Complex.exp_add]
      congr 1
      push_cast
      ring

/-- Helper for `cor16_2_3_a` (§16.3, the example). `h₀` is quasisymmetric: its lift is bi-Lipschitz (ratios in
`[1/3, 3]`), so `gl16_M_of_qs` gives the `M`-condition and `gl16_cl_qsA_of_M` Ahlfors' condition (`h₀` is continuous,
and injective on the circle by its lift). -/
theorem gl16_cl_corner_qs : Pommerenke1992.IsQuasisymmetricA (fun z : ℂ => z * exp (I * ((‖z - 1‖ / 2 : ℝ) : ℂ))) := by
  have hL := gl16_cl_corner_lift.1
  have hπ := Real.pi_pos
  -- the lift is bi-Lipschitz: increments in `[(b − a)/2, 3(b − a)/2]`
  have hinc : ∀ a b : ℝ, a < b →
      (b - a) / 2 ≤ (b + |Real.sin (π * b)| / (2 * π)) - (a + |Real.sin (π * a)| / (2 * π)) ∧
        (b + |Real.sin (π * b)| / (2 * π)) - (a + |Real.sin (π * a)| / (2 * π)) ≤ 3 * (b - a) / 2 := by
    intro a b hab
    have hab' : |π * a - π * b| = π * (b - a) := by
      rw [← mul_sub, abs_mul, abs_of_pos hπ, abs_of_neg (by linarith), neg_sub]
    have h2 := abs_le.1 ((gl16_cl_abs_sin_lip (π * a) (π * b)).trans_eq hab')
    have h3 : |Real.sin (π * a)| / (2 * π) - |Real.sin (π * b)| / (2 * π) ≤ (b - a) / 2 := by
      rw [← sub_div, div_le_iff₀ (by positivity)]
      nlinarith [h2.2]
    have h4 : -((b - a) / 2) ≤ |Real.sin (π * a)| / (2 * π) - |Real.sin (π * b)| / (2 * π) := by
      rw [← sub_div, le_div_iff₀ (by positivity)]
      nlinarith [h2.1]
    constructor <;> linarith
  have hqs : LiZhongQC.IsQuasisymmetric (fun x : ℝ => x + |Real.sin (π * x)| / (2 * π)) 3 := by
    refine ⟨hL.2.1, hL.1, ?_, ?_, fun x t ht => ?_⟩
    · exact tendsto_atTop_mono (fun x => le_add_of_nonneg_right (by positivity)) tendsto_id
    · refine tendsto_atBot_mono (fun x => ?_) (tendsto_atBot_add_const_right _ (1 / (2 * π)) tendsto_id)
      show x + |Real.sin (π * x)| / (2 * π) ≤ x + 1 / (2 * π)
      have : |Real.sin (π * x)| ≤ 1 := Real.abs_sin_le_one _
      have : |Real.sin (π * x)| / (2 * π) ≤ 1 / (2 * π) := div_le_div_of_nonneg_right this (by positivity)
      linarith
    · obtain ⟨r1, r2⟩ := hinc x (x + t) (by linarith)
      obtain ⟨l1, l2⟩ := hinc (x - t) x (by linarith)
      have hR : 0 < (x + t + |Real.sin (π * (x + t))| / (2 * π)) - (x + |Real.sin (π * x)| / (2 * π)) := by
        linarith
      have hLft : 0 < (x + |Real.sin (π * x)| / (2 * π)) - (x - t + |Real.sin (π * (x - t))| / (2 * π)) := by
        linarith
      show 3⁻¹ ≤ ((x + t + |Real.sin (π * (x + t))| / (2 * π)) - (x + |Real.sin (π * x)| / (2 * π))) /
          ((x + |Real.sin (π * x)| / (2 * π)) - (x - t + |Real.sin (π * (x - t))| / (2 * π))) ∧
        ((x + t + |Real.sin (π * (x + t))| / (2 * π)) - (x + |Real.sin (π * x)| / (2 * π))) /
          ((x + |Real.sin (π * x)| / (2 * π)) - (x - t + |Real.sin (π * (x - t))| / (2 * π))) ≤ 3
      constructor
      · rw [le_div_iff₀ hLft]
        nlinarith
      · rw [div_le_iff₀ hLft]
        nlinarith
  obtain ⟨M, hM⟩ := gl16_M_of_qs hL hqs
  have hc : Continuous fun z : ℂ => z * exp (I * ((‖z - 1‖ / 2 : ℝ) : ℂ)) := by fun_prop
  exact gl16_cl_qsA_of_M hc.continuousOn (gl16_cl_lift_injOn hL) hM

/-- Helper for `cor16_2_3_a` (§16.3, the example). `h₀` is not symmetric. At the corner `x = 0` the lift's ratio is
`(t + sin(πt)/(2π))/(t − sin(πt)/(2π)) ≥ (1 + 1/π)/(1 − 1/π)` for `0 < t ≤ 1/2` (`sin πt ≥ 2t`). This does not tend to
`1`, against `gl16_lift_vanishing`. -/
theorem gl16_cl_corner_not :
    ¬ HasVanishingRatioDistortion (fun z : ℂ => z * exp (I * ((‖z - 1‖ / 2 : ℝ) : ℂ))) := by
  intro hv
  obtain ⟨ε, hε, hb⟩ := gl16_lift_vanishing gl16_cl_corner_lift.1 hv
  obtain ⟨t, ht1, ht2⟩ := ((hε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 2 / 3))).and
    (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2))).exists
  have hπ := Real.pi_pos
  have h1 := (hb 0 t ht2.1).2
  obtain ⟨hs1, hs2⟩ := gl16_sin_short ht2.1 ht2.2.le
  have hsin : 0 < Real.sin (π * t) := by linarith [ht2.1]
  have hq : LiZhongQC.qsRatio (fun x : ℝ => x + |Real.sin (π * x)| / (2 * π)) 0 t =
      (t + Real.sin (π * t) / (2 * π)) / (t - Real.sin (π * t) / (2 * π)) := by
    show ((0 + t + |Real.sin (π * (0 + t))| / (2 * π)) - (0 + |Real.sin (π * 0)| / (2 * π))) /
      ((0 + |Real.sin (π * 0)| / (2 * π)) - (0 - t + |Real.sin (π * (0 - t))| / (2 * π))) = _
    rw [zero_add, zero_sub, mul_zero, Real.sin_zero, abs_zero, zero_div, add_zero, mul_neg, Real.sin_neg, abs_neg,
      abs_of_pos hsin]
    congr 1 <;> ring
  rw [hq] at h1
  -- the ratio is at least `(π + 1)/(π − 1) ≥ 5/3`
  have hs : t / π ≤ Real.sin (π * t) / (2 * π) := by
    rw [div_le_div_iff₀ hπ (by positivity)]
    nlinarith
  have hs' : Real.sin (π * t) / (2 * π) ≤ t / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hden : 0 < t - Real.sin (π * t) / (2 * π) := by linarith [ht2.1]
  have h5 : 5 / 3 ≤ (t + Real.sin (π * t) / (2 * π)) / (t - Real.sin (π * t) / (2 * π)) := by
    rw [le_div_iff₀ hden]
    have h4 := Real.pi_le_four
    have h6 : t / π ≥ t / 4 := div_le_div_of_nonneg_left ht2.1.le hπ h4
    nlinarith
  linarith

/-- Helper for `lemma16_4` (§16.3, one window of Lemma 4's chain). Let `G = h̃(h̃⁻¹(·) + t)` be the lift of the
conjugate `g` (M-condition `1 + e₀`). On `[h̃(x + (k − 1)t), h̃(x + (k + 1)t)]` the increments of `G` are `< ζ`
(uniform continuity of `h̃`, `3t < τ₂`). So `G` satisfies the ratio condition `1 + δ₁` there (`gl16_cl_ratio`), and
the near-affinity `haff` at `p = h̃(x + kt)`, divided by `h̃(x + (k + 2)t) − h̃(x + kt)`, moves the fraction by at most
`η`. -/
theorem gl16_cl_window {hl hi : ℝ → ℝ} (hlmono : StrictMono hl) (himono : StrictMono hi)
    (hil : ∀ x, hi (hl x) = x) {g : ℂ → ℂ} {e₀ ζ δ₁ η τ₂ t x : ℝ} (hgM : IsMCondition g (1 + e₀)) (he₀ : 0 ≤ e₀)
    (hGlift : ∀ y : ℝ, exp (2 * π * I * hl (hi y + t)) = g (exp (2 * π * I * y)))
    (hη2 : max e₀ ((π * ζ) ^ 2) ≤ 1 / 2) (h8 : 8 * max e₀ ((π * ζ) ^ 2) ≤ δ₁) (hζ1 : ζ < 1)
    (huc : ∀ a b : ℝ, |a - b| < τ₂ → |hl a - hl b| < ζ) (ht : 0 < t) (htτ : 3 * t < τ₂)
    (haff : ∀ a L : ℝ, 0 < L →
      (∀ y s : ℝ, 0 < s → a ≤ y - s → y + s ≤ a + L →
        1 / (1 + δ₁) ≤ LiZhongQC.qsRatio (fun u => hl (hi u + t)) y s ∧
          LiZhongQC.qsRatio (fun u => hl (hi u + t)) y s ≤ 1 + δ₁) →
      ∀ p ∈ Icc a (a + L), |hl (hi p + t) - (hl (hi a + t) + (p - a) / L * (hl (hi (a + L) + t) - hl (hi a + t)))| ≤
        η * (hl (hi (a + L) + t) - hl (hi a + t)))
    (k : ℝ) :
    |(hl (x + (k + 1) * t) - hl (x + k * t)) / (hl (x + (k + 2) * t) - hl (x + k * t)) -
      (hl (x + k * t) - hl (x + (k - 1) * t)) / (hl (x + (k + 1) * t) - hl (x + (k - 1) * t))| ≤ η := by
  have hGmono : StrictMono fun y => hl (hi y + t) := fun a b hab => hlmono (by linarith [himono hab])
  have hab : hl (x + (k - 1) * t) < hl (x + (k + 1) * t) := hlmono (by linarith)
  have hap : hl (x + (k - 1) * t) ≤ hl (x + k * t) := (hlmono (by linarith)).le
  have hpb : hl (x + k * t) ≤ hl (x + (k + 1) * t) := (hlmono (by linarith)).le
  have hL : 0 < hl (x + (k + 1) * t) - hl (x + (k - 1) * t) := sub_pos.2 hab
  -- the increments of `G` inside the window are small
  have hwin : ∀ u v : ℝ, hl (x + (k - 1) * t) ≤ u → u ≤ v → v ≤ hl (x + (k + 1) * t) →
      hl (hi v + t) - hl (hi u + t) < ζ := by
    intro u v hu huv hv
    have h1 : x + (k - 1) * t ≤ hi u := by have := himono.monotone hu; rwa [hil] at this
    have h2 : hi v ≤ x + (k + 1) * t := by have := himono.monotone hv; rwa [hil] at this
    have h3 : hi u ≤ hi v := himono.monotone huv
    have h4 := huc (hi v + t) (hi u + t) (by rw [abs_lt]; constructor <;> linarith)
    rw [abs_lt] at h4
    linarith [h4.2]
  have hbl : hl (x + (k + 1) * t) - hl (x + (k - 1) * t) < 1 := by
    have h5 := huc (x + (k + 1) * t) (x + (k - 1) * t) (by rw [abs_lt]; constructor <;> linarith)
    rw [abs_lt] at h5
    linarith [h5.2]
  have hratio : ∀ y s : ℝ, 0 < s → hl (x + (k - 1) * t) ≤ y - s →
      y + s ≤ hl (x + (k - 1) * t) + (hl (x + (k + 1) * t) - hl (x + (k - 1) * t)) →
      1 / (1 + δ₁) ≤ LiZhongQC.qsRatio (fun y => hl (hi y + t)) y s ∧
        LiZhongQC.qsRatio (fun y => hl (hi y + t)) y s ≤ 1 + δ₁ := by
    intro y s hs hys hys'
    rw [add_sub_cancel] at hys'
    have hw1 := hwin y (y + s) (by linarith) (by linarith) hys'
    have hw2 := hwin (y - s) y hys (by linarith) (by linarith)
    obtain ⟨r1, r2⟩ := gl16_cl_ratio hgM he₀ hGlift hη2 hs (by linarith)
      (sub_pos.2 (hGmono (by linarith))) hw1.le (sub_pos.2 (hGmono (by linarith))) hw2.le
    constructor
    · calc 1 / (1 + δ₁) ≤ 1 / (1 + 8 * max e₀ ((π * ζ) ^ 2)) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        _ ≤ _ := r1
    · linarith
  have hA := haff _ _ hL hratio (hl (x + k * t)) ⟨hap, by rw [add_sub_cancel]; exact hpb⟩
  rw [add_sub_cancel, hil, hil, hil] at hA
  have e1 : x + (k - 1) * t + t = x + k * t := by ring
  have e2 : x + k * t + t = x + (k + 1) * t := by ring
  have e3 : x + (k + 1) * t + t = x + (k + 2) * t := by ring
  rw [e1, e2, e3] at hA
  have hD : 0 < hl (x + (k + 2) * t) - hl (x + k * t) := sub_pos.2 (hlmono (by linarith))
  rw [abs_le] at hA ⊢
  obtain ⟨hA1, hA2⟩ := hA
  generalize (hl (x + k * t) - hl (x + (k - 1) * t)) / (hl (x + (k + 1) * t) - hl (x + (k - 1) * t)) = F
    at hA1 hA2 ⊢
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ hD]
    linarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hD]
    linarith

/-- Helper for `lemma16_4` and `cor16_2_3_a` (§16.3): the proof of Lemma 4, placed here because Corollary 3 (above
Lemma 4 in the file) uses it. If conjugation by `h` is continuous at the identity, then `h` has vanishing ratio
distortion.
- Test maps: the rotations `R_t` (`gl16_cl_rot`); the conjugate `h ∘ R_t ∘ h⁻¹` has the lift
  `G = h̃ ∘ (· + t) ∘ h̃⁻¹` (`gl16_cl_conj`).
- `G` sends `h̃(x + (k − 1)t)` to `h̃(x + kt)`. On each window `[h̃(x + (k − 1)t), h̃(x + (k + 1)t)]` it satisfies a
  ratio condition close to `1` (`gl16_cl_ratio`), hence it is near-affine (`gl16_cl_affine3`).
- The chain `gl16_cl_chain` with `h̃`'s quasisymmetry then bounds `h̃`'s ratios at all small scales, and
  `gl16_circle_vanishing` transfers this to the circle. -/
theorem gl16_cl_vanishing {h : ℂ → ℂ} (hh : Pommerenke1992.IsSensePreservingCircleHomeo h)
    (hq : Pommerenke1992.IsQuasisymmetricA h)
    (hc : ∀ ε > 0, ∃ δ > 0, ∀ f ∈ qsNbhdU δ, h ∘ f ∘ Function.invFunOn h (sphere 0 1) ∈ qsNbhdU ε) :
    HasVanishingRatioDistortion h := by
  obtain ⟨hl, hlift⟩ := gl16_cl_lift hh
  obtain ⟨hi, -, himono, hli, hil⟩ := gl16_cl_lift_inv hlift
  obtain ⟨M, hM⟩ := gl16_cl_M_of_qsA hq
  obtain ⟨M₁, hM₁⟩ := gl16_qs_of_M hlift hM
  have hlc : Continuous hl := hlift.1
  have hlmono : StrictMono hl := hlift.2.1
  have hper : ∀ x, hl (x + 1) = hl x + 1 := hlift.2.2.2.2.1
  have hqs : ∀ x t : ℝ, 0 < t → M₁⁻¹ ≤ LiZhongQC.qsRatio hl x t ∧ LiZhongQC.qsRatio hl x t ≤ M₁ :=
    hM₁.2.2.2.2
  have hpos : ∀ x t : ℝ, 0 < t → 0 < LiZhongQC.qsRatio hl x t := fun x t ht =>
    div_pos (sub_pos.2 (hlmono (by linarith))) (sub_pos.2 (hlmono (by linarith)))
  -- the core: small scales
  have hsmall : ∀ γ > 0, ∃ τ > 0, ∀ t : ℝ, 0 < t → t < τ → True ∧
      ∀ x, max (LiZhongQC.qsRatio hl x t) (LiZhongQC.qsRatio hl x t)⁻¹ - 1 ≤ γ := by
    intro γ hγ
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt M₁ (show (1 : ℝ) < 1 + γ / 2 by linarith)
    set κ : ℝ := γ / 2 / ((2 + γ / 2) * (2 + γ)) with hκ
    have hκ0 : 0 < κ := by positivity
    set η : ℝ := κ / (2 * j + 1) with hηdef
    have hη0 : 0 < η := by positivity
    have hη : 2 * j * η ≤ κ := by
      rw [hηdef, mul_div_assoc']
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    obtain ⟨δ₁, hδ₁, haff⟩ := gl16_cl_affine3 η hη0
    set e₀ : ℝ := min (δ₁ / 8) (1 / 2) with he₀
    have he₀0 : 0 < e₀ := lt_min (by positivity) (by norm_num)
    set ζ : ℝ := Real.sqrt e₀ / π with hζ
    have hζ0 : 0 < ζ := div_pos (Real.sqrt_pos.2 he₀0) Real.pi_pos
    have hπζ : (π * ζ) ^ 2 = e₀ := by
      rw [hζ, mul_div_cancel₀ _ Real.pi_ne_zero, Real.sq_sqrt he₀0.le]
    have hmax : max e₀ ((π * ζ) ^ 2) = e₀ := by rw [hπζ, max_self]
    have hζ1 : ζ < 1 := by
      have h1 : Real.sqrt e₀ ≤ Real.sqrt (1 / 2) := Real.sqrt_le_sqrt (min_le_right _ _)
      have h2 : Real.sqrt (1 / 2) < 1 := by
        rw [Real.sqrt_lt' one_pos]
        norm_num
      rw [hζ, div_lt_one Real.pi_pos]
      linarith [Real.pi_gt_three]
    obtain ⟨δ₀, hδ₀, hconj⟩ := hc e₀ he₀0
    obtain ⟨τ₁, hτ₁, hrot⟩ := gl16_cl_rot hδ₀
    obtain ⟨τ₂, hτ₂, huc⟩ := gl16_lift_uc hlc hper hζ0
    refine ⟨min τ₁ (τ₂ / 3), lt_min hτ₁ (by positivity), fun t ht htτ => ⟨trivial, fun x => ?_⟩⟩
    have htτ₁ : t < τ₁ := lt_of_lt_of_le htτ (min_le_left _ _)
    have htτ₂ : 3 * t < τ₂ := by linarith [min_le_right τ₁ (τ₂ / 3)]
    -- the conjugate of the rotation by `2πt` and its lift
    have hg := hconj _ (hrot t (by rw [abs_of_pos ht]; exact htτ₁))
    have hgM := hg.2.2.2
    have hGlift := gl16_cl_conj hlift hli hil t
    have hGmono : StrictMono fun y => hl (hi y + t) := fun a b hab => hlmono (by linarith [himono hab])
    -- near-affinity of `G` on the windows, hence the chain hypothesis
    have hF : ∀ k : ℕ, k < 2 * j →
        |(hl (x + ((k : ℝ) + 1) * t) - hl (x + k * t)) / (hl (x + ((k : ℝ) + 2) * t) - hl (x + k * t)) -
          (hl (x + k * t) - hl (x + ((k : ℝ) - 1) * t)) /
            (hl (x + ((k : ℝ) + 1) * t) - hl (x + ((k : ℝ) - 1) * t))| ≤ η := fun k _ =>
      gl16_cl_window (δ₁ := δ₁) hlmono himono hil hgM he₀0.le hGlift (by rw [hmax]; exact min_le_right _ _)
        (by rw [hmax]; linarith [min_le_left (δ₁ / 8) (1 / 2)]) hζ1 huc ht htτ₂ (haff _ hGmono) k
    have hfin := gl16_cl_chain hlmono hqs ht hγ hj (hη.trans le_rfl) hF
    show max (LiZhongQC.qsRatio hl x t) (LiZhongQC.qsRatio hl x t)⁻¹ - 1 ≤ γ
    linarith
  refine gl16_circle_vanishing hlift ?_
  obtain ⟨ε, hε, hb⟩ := gl16_vanishing_of_bounds (R := fun x t => LiZhongQC.qsRatio hl x t) (P := fun _ => True)
    (fun t ht _ => ⟨M₁, fun x => ⟨hpos x t ht, max_le (hqs x t ht).2
      ((inv_le_comm₀ (hpos x t ht) (lt_of_lt_of_le (hpos x t ht) (hqs x t ht).2)).2 (hqs x t ht).1)⟩⟩) hsmall
  exact ⟨ε, hε, fun x t ht => hb x t ht trivial⟩

/-- Helper for the lift calculus (§16.3): chords through the covering, `|e^{2πia} − e^{2πib}| = 2|sin π(a − b)|`. -/
theorem gl16_sy_chord_eq (a b : ℝ) :
    ‖exp (2 * π * I * (a : ℂ)) - exp (2 * π * I * (b : ℂ))‖ = 2 * |Real.sin (π * (a - b))| := by
  have e : exp (2 * π * I * (a : ℂ)) - exp (2 * π * I * (b : ℂ)) =
      exp (((2 * π * b : ℝ) : ℂ) * I) * (exp (I * ((2 * π * (a - b) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2 <;> push_cast <;> ring
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_two, show 2 * π * (a - b) / 2 = π * (a - b) by ring]

/-- Helper for the lift calculus (§16.3): Jordan's inequality in absolute value, `2|r| ≤ |sin πr|` for
`|r| ≤ 1/2`. -/
theorem gl16_sy_abs_sin_ge {r : ℝ} (hr : |r| ≤ 1 / 2) : 2 * |r| ≤ |Real.sin (π * r)| := by
  rcases lt_trichotomy r 0 with h | h | h
  · rw [abs_of_neg h] at hr ⊢
    have h1 := (gl16_sin_short (D := -r) (by linarith) hr).1
    rw [show π * -r = -(π * r) by ring, Real.sin_neg] at h1
    calc 2 * -r ≤ -Real.sin (π * r) := h1
      _ ≤ |Real.sin (π * r)| := neg_le_abs _
  · subst h
    simp
  · rw [abs_of_pos h] at hr ⊢
    exact (gl16_sin_short h hr).1.trans (le_abs_self _)

/-- Helper for the lift calculus (§16.3): `e^{2πix}` lies on the unit circle. -/
theorem gl16_sy_exp_mem (x : ℝ) : exp (2 * π * I * (x : ℂ)) ∈ sphere (0 : ℂ) 1 := by
  rw [mem_sphere_zero_iff_norm, show (2 * π * I * (x : ℂ)) = ((2 * π * x : ℝ) : ℂ) * I by push_cast; ring]
  exact norm_exp_ofReal_mul_I _

/-- Helper for the lift calculus (§16.3): a continuous increasing `F` with `F(x + 1) = F(x) + 1` and
`e^{2πiF(x)} = h(e^{2πix})`, normalized by `⌊F(0)⌋`, is a lift of `h`. -/
theorem gl16_sy_lift_of {h : ℂ → ℂ} {F : ℝ → ℝ} (hc : Continuous F) (hm : StrictMono F)
    (hper : ∀ x, F (x + 1) = F x + 1) (hF : ∀ x : ℝ, exp (2 * π * I * F x) = h (exp (2 * π * I * x))) :
    IsCircleLift h (fun x => F x - ⌊F 0⌋) := by
  refine ⟨hc.sub continuous_const, fun a b hab => sub_lt_sub_right (hm hab) _, ?_, ?_, fun x => ?_, fun x => ?_⟩
  · show 0 ≤ F 0 - ⌊F 0⌋
    exact sub_nonneg.2 (Int.floor_le _)
  · show F 0 - ⌊F 0⌋ < 1
    linarith [Int.lt_floor_add_one (F 0)]
  · show F (x + 1) - ⌊F 0⌋ = F x - ⌊F 0⌋ + 1
    rw [hper]
    ring
  · show exp (2 * π * I * ((F x - ⌊F 0⌋ : ℝ) : ℂ)) = h (exp (2 * π * I * x))
    rw [← hF x]
    push_cast
    rw [mul_sub, Complex.exp_sub, show 2 * π * I * (⌊F 0⌋ : ℂ) = ⌊F 0⌋ * (2 * π * I) by ring,
      Complex.exp_int_mul_two_pi_mul_I, div_one]

/-- Helper for the lift calculus (§16.3): through the lift, `h⁻¹(e^{2πiy}) = e^{2πih̃⁻¹(y)}` (`h` is injective on the
circle). -/
theorem gl16_sy_invFun_exp {h : ℂ → ℂ} {hl hi : ℝ → ℝ} (hlift : IsCircleLift h hl) (hli : ∀ x, hl (hi x) = x)
    (y : ℝ) : Function.invFunOn h (sphere 0 1) (exp (2 * π * I * y)) = exp (2 * π * I * hi y) := by
  have hhp : h (exp (2 * π * I * (hi y : ℂ))) = exp (2 * π * I * (y : ℂ)) := by
    rw [← hlift.2.2.2.2.2, hli]
  rw [← hhp]
  exact (gl16_cl_lift_injOn hlift).leftInvOn_invFunOn (gl16_sy_exp_mem _)

/-- Helper for the lift calculus (§16.3): a circle map with a lift maps the circle onto itself. -/
theorem gl16_sy_maps_surj {h : ℂ → ℂ} {hl : ℝ → ℝ} (hlift : IsCircleLift h hl) :
    (∀ z ∈ sphere (0 : ℂ) 1, h z ∈ sphere (0 : ℂ) 1) ∧ ∀ z ∈ sphere (0 : ℂ) 1, ∃ a ∈ sphere (0 : ℂ) 1, h a = z := by
  obtain ⟨hi, -, -, hli, -⟩ := gl16_cl_lift_inv hlift
  have hlh := hlift.2.2.2.2.2
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · rw [← gl16_cl_exp_arg hz, ← hlh]
    exact gl16_sy_exp_mem _
  · refine ⟨exp (2 * π * I * (hi (arg z / (2 * π)) : ℂ)), gl16_sy_exp_mem _, ?_⟩
    rw [← hlh, hli, gl16_cl_exp_arg hz]

/-- Helper for the lift calculus (§16.3): `invFunOn` on the circle only reads the values on the circle (for a map
injective there). -/
theorem gl16_sy_invFunOn_congr {g g' : ℂ → ℂ} (heq : EqOn g g' (sphere 0 1)) (hinj : InjOn g (sphere 0 1)) (z : ℂ) :
    Function.invFunOn g' (sphere 0 1) z = Function.invFunOn g (sphere 0 1) z := by
  by_cases h : ∃ a ∈ sphere (0 : ℂ) 1, g a = z
  · have h' : ∃ a ∈ sphere (0 : ℂ) 1, g' a = z := by
      obtain ⟨a, ha, hga⟩ := h
      exact ⟨a, ha, by rw [← heq ha]; exact hga⟩
    refine hinj (Function.invFunOn_mem h') (Function.invFunOn_mem h) ?_
    rw [heq (Function.invFunOn_mem h'), Function.invFunOn_eq h', Function.invFunOn_eq h]
  · have h' : ¬∃ a ∈ sphere (0 : ℂ) 1, g' a = z := by
      rintro ⟨a, ha, hga⟩
      exact h ⟨a, ha, (heq ha).trans hga⟩
    rw [Function.invFunOn_neg h, Function.invFunOn_neg h']

/-- Helper for the near-affinity calculus (§16.3): the ratio of a lift is unchanged by a constant shift of the
values. -/
theorem gl16_sy_qsRatio_sub (F : ℝ → ℝ) (c x t : ℝ) :
    LiZhongQC.qsRatio (fun y => F y - c) x t = LiZhongQC.qsRatio F x t := by
  show (F (x + t) - c - (F x - c)) / (F x - c - (F (x - t) - c)) = (F (x + t) - F x) / (F x - F (x - t))
  congr 1 <;> ring

/-- Helper for the near-affinity calculus (§16.3): one step of a ratio chain. If `R'` and `R` agree up to the factor
`1 + a` and `R ∈ [1/X, X]`, then `R' ∈ [1/((1 + a)X), (1 + a)X]`. -/
theorem gl16_sy_step {R R' a X : ℝ} (ha : 0 ≤ a) (hX : 0 < X) (h1 : R' ≤ (1 + a) * R)
    (h2 : R ≤ (1 + a) * R') (hx1 : 1 / X ≤ R) (hx2 : R ≤ X) :
    1 / ((1 + a) * X) ≤ R' ∧ R' ≤ (1 + a) * X := by
  have hX' : 0 < (1 + a) * X := by positivity
  refine ⟨?_, h1.trans (mul_le_mul_of_nonneg_left hx2 (by linarith))⟩
  rw [div_le_iff₀ hX']
  rw [div_le_iff₀ hX] at hx1
  have : R * X ≤ (1 + a) * R' * X := mul_le_mul_of_nonneg_right h2 hX.le
  linarith

/-- Helper for the near-affinity calculus (§16.3): `R ∈ [1/X, X]` gives `max(R, R⁻¹) ≤ X`. -/
theorem gl16_sy_max_of {R X : ℝ} (hX : 0 < X) (h1 : 1 / X ≤ R) (h2 : R ≤ X) : max R R⁻¹ ≤ X := by
  refine max_le h2 ?_
  rw [one_div] at h1
  exact inv_le_of_inv_le₀ hX h1

/-- Helper for `lemma16_3` (§16.3): the `M`-condition is monotone in `M`. -/
theorem gl16_sy_M_mono {g : ℂ → ℂ} {M M' : ℝ} (hM : IsMCondition g M) (hM0 : 0 < M) (hMM : M ≤ M') :
    IsMCondition g M' := by
  intro x t ht
  obtain ⟨h1, h2⟩ := hM x t ht
  exact ⟨le_trans (one_div_le_one_div_of_le hM0 hMM) h1, h2.trans hMM⟩

/-- Helper for `thm16_2`, `cor16_2_2` and `lemma16_3` (§16.3, lift calculus). A map with a lift is a sense-preserving
circle homeomorphism: `u(t) = 2π h̃(t/2π)`. -/
theorem gl16_sy_homeo_of_lift {h : ℂ → ℂ} {hl : ℝ → ℝ} (hlift : IsCircleLift h hl) :
    Pommerenke1992.IsSensePreservingCircleHomeo h := by
  obtain ⟨hc, hm, -, -, hper, hlh⟩ := hlift
  have hπ := Real.pi_pos
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  have hπc : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine ⟨fun t => 2 * π * hl (t / (2 * π)), ?_, ?_, fun t => ?_, fun t => ?_⟩
  · exact continuous_const.mul (hc.comp (continuous_id.div_const _))
  · intro a b hab
    show 2 * π * hl (a / (2 * π)) < 2 * π * hl (b / (2 * π))
    exact mul_lt_mul_of_pos_left (hm (div_lt_div_of_pos_right hab (by positivity))) (by positivity)
  · show 2 * π * hl ((t + 2 * π) / (2 * π)) = 2 * π * hl (t / (2 * π)) + 2 * π
    rw [show (t + 2 * π) / (2 * π) = t / (2 * π) + 1 by field_simp, hper]
    ring
  · show h (exp (t * I)) = exp (((2 * π * hl (t / (2 * π)) : ℝ) : ℂ) * I)
    have e1 : (t : ℂ) * I = 2 * π * I * ((t / (2 * π) : ℝ) : ℂ) := by
      push_cast
      field_simp
    rw [e1, ← hlh]
    congr 1
    push_cast
    ring

/-- Helper for `thm16_2` and `lemma16_3` (§16.3, lift calculus). A map with a lift is continuous on the circle: near
`z₀ = e^{2πix₀}`, `z = e^{2πi(x₀ + arg(z/z₀)/2π)}`, with `arg` continuous at `1`. -/
theorem gl16_sy_contOn_of_lift {h : ℂ → ℂ} {hl : ℝ → ℝ} (hlift : IsCircleLift h hl) :
    ContinuousOn h (sphere 0 1) := by
  obtain ⟨hc, -, -, -, -, hlh⟩ := hlift
  intro z₀ hz₀
  have hz₀1 : ‖z₀‖ = 1 := mem_sphere_zero_iff_norm.1 hz₀
  have hz₀' : z₀ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hz₀1
    exact zero_ne_one hz₀1
  -- on the circle, `h z = e^{2πi h̃(x₀ + arg(z/z₀)/2π)}` with `x₀ = arg z₀/2π`
  have hΦ : ∀ z ∈ sphere (0 : ℂ) 1,
      h z = exp (2 * π * I * (hl (arg z₀ / (2 * π) + arg (z / z₀) / (2 * π)) : ℂ)) := by
    intro z hz
    have hq : z / z₀ ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_div, mem_sphere_zero_iff_norm.1 hz, hz₀1, div_one]
    have e : exp (2 * π * I * ((arg z₀ / (2 * π) + arg (z / z₀) / (2 * π) : ℝ) : ℂ)) = z := by
      rw [Complex.ofReal_add, mul_add, Complex.exp_add, gl16_cl_exp_arg hz₀, gl16_cl_exp_arg hq]
      field_simp
    rw [hlh, e]
  have h1 : ContinuousAt (fun z : ℂ => arg (z / z₀)) z₀ := by
    have hs : z₀ / z₀ ∈ slitPlane := by
      rw [div_self hz₀']
      exact one_mem_slitPlane
    exact (continuousAt_arg hs).comp (f := fun z : ℂ => z / z₀) (continuousAt_id.div_const z₀)
  have h2 : ContinuousAt (fun z : ℂ => hl (arg z₀ / (2 * π) + arg (z / z₀) / (2 * π))) z₀ :=
    hc.continuousAt.comp (continuousAt_const.add (h1.div_const _))
  have h3 : ContinuousAt (fun z : ℂ => exp (2 * π * I * (hl (arg z₀ / (2 * π) + arg (z / z₀) / (2 * π)) : ℂ)))
      z₀ :=
    Complex.continuous_exp.continuousAt.comp
      (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp h2))
  exact h3.continuousWithinAt.congr (fun z hz => hΦ z hz) (hΦ z₀ hz₀)

/-- Helper for `cor16_2_2` and `lemma16_3` (§16.3, lift calculus). The lift of a composition is the composition of
the lifts, renormalized by an integer: `f̃(g̃(x)) − ⌊f̃(g̃(0))⌋`. -/
theorem gl16_sy_comp_lift {f g : ℂ → ℂ} {fl gl : ℝ → ℝ} (hf : IsCircleLift f fl) (hg : IsCircleLift g gl) :
    IsCircleLift (f ∘ g) (fun x => fl (gl x) - ⌊fl (gl 0)⌋) := by
  obtain ⟨hfc, hfm, -, -, hfp, hfh⟩ := hf
  obtain ⟨hgc, hgm, -, -, hgp, hgh⟩ := hg
  refine gl16_sy_lift_of (F := fun x => fl (gl x)) (hfc.comp hgc) (hfm.comp hgm) (fun x => ?_) fun x => ?_
  · show fl (gl (x + 1)) = fl (gl x) + 1
    rw [hgp, hfp]
  · show exp (2 * π * I * (fl (gl x) : ℂ)) = f (g (exp (2 * π * I * x)))
    rw [hfh, hgh]

/-- Helper for `thm16_2`, `cor16_2_2` and `lemma16_3` (§16.3, lift calculus). The inverse lift `h̃⁻¹`, renormalized by
an integer, is a lift of the inverse `invFunOn f` on the circle. -/
theorem gl16_sy_inv_lift {f : ℂ → ℂ} {fl hi : ℝ → ℝ} (hf : IsCircleLift f fl) (hic : Continuous hi)
    (him : StrictMono hi) (hli : ∀ x, fl (hi x) = x) (hil : ∀ x, hi (fl x) = x) :
    IsCircleLift (Function.invFunOn f (sphere 0 1)) (fun y => hi y - ⌊hi 0⌋) := by
  have hper := hf.2.2.2.2.1
  have hiper : ∀ y, hi (y + 1) = hi y + 1 := fun y => by
    rw [← hil (hi y + 1), hper, hli]
  exact gl16_sy_lift_of hic him hiper fun y => (gl16_sy_invFun_exp hf hli y).symm

/-- Helper for `lemma16_3` (§16.3, lift calculus). A map within `δ ≤ 1` of the identity on the circle has its lift
within `δ/4` of a translation by an integer. Here `2|sin π(f̃ − id)| < δ` and `sin πd ≥ 2d` for `d ≤ 1/2`; the integer
is constant by continuity. -/
theorem gl16_sy_near_lift {f : ℂ → ℂ} {fl : ℝ → ℝ} (hf : IsCircleLift f fl) {δ : ℝ} (hδ : δ ≤ 1)
    (hnear : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z - z‖ < δ) : ∃ k : ℤ, ∀ u : ℝ, |fl u - u - k| ≤ δ / 4 := by
  obtain ⟨hc, -, -, -, -, hlh⟩ := hf
  have hd : Continuous fun u => fl u - u := hc.sub continuous_id
  -- at each point, `f̃(u) − u` is within `δ/4` of an integer
  have hpt : ∀ u : ℝ, |fl u - u - round (fl u - u)| < δ / 4 := by
    intro u
    have h1 := hnear _ (gl16_sy_exp_mem u)
    rw [← hlh, gl16_sy_chord_eq] at h1
    have h3 := gl16_sy_abs_sin_ge (abs_sub_round (fl u - u))
    have e : π * (fl u - u) = π * (fl u - u - round (fl u - u)) + round (fl u - u) * π := by ring
    rw [e, Real.sin_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul] at h1
    linarith
  -- no value is at distance `1/2` from the integers
  have hj : ∀ j : ℤ, 1 / 2 ≤ |(j : ℝ) + 1 / 2| := fun j => by
    rcases le_or_gt 0 j with h | h
    · have : (0 : ℝ) ≤ j := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]
      linarith
    · have h' : j ≤ -1 := by omega
      have : (j : ℝ) ≤ -1 := by exact_mod_cast h'
      rw [abs_of_neg (by linarith)]
      linarith
  have hval : ∀ v : ℝ, ∀ m : ℤ, fl v - v ≠ m + 1 / 2 := by
    intro v m hv
    have h1 := hpt v
    rw [hv] at h1
    have h2 := hj (m - round ((m : ℝ) + 1 / 2))
    push_cast at h2
    rw [show (m : ℝ) - round ((m : ℝ) + 1 / 2) + 1 / 2 = m + 1 / 2 - round ((m : ℝ) + 1 / 2) by ring] at h2
    linarith
  refine ⟨round (fl 0 - 0), fun u => ?_⟩
  suffices hk : round (fl u - u) = round (fl 0 - 0) by
    have := hpt u
    rw [hk] at this
    exact this.le
  by_contra hne
  have h0 := abs_lt.1 (hpt 0)
  have hu := abs_lt.1 (hpt u)
  have hu1 := abs_lt.1 (hpt u)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `round(f̃u − u) ≤ k − 1`: the value `k − 1/2` is attained between `u` and `0`
    have hle : round (fl u - u) ≤ round (fl 0 - 0) - 1 := by omega
    have hle' : (round (fl u - u) : ℝ) ≤ round (fl 0 - 0) - 1 := by exact_mod_cast hle
    obtain ⟨v, hv⟩ := intermediate_value_univ u 0 hd
      (show ((round (fl 0 - 0) - 1 : ℤ) : ℝ) + 1 / 2 ∈ Icc (fl u - u) (fl 0 - 0) by
        push_cast
        constructor <;> linarith)
    exact hval v _ hv
  · have hle : round (fl 0 - 0) + 1 ≤ round (fl u - u) := by omega
    have hle' : (round (fl 0 - 0) : ℝ) + 1 ≤ round (fl u - u) := by exact_mod_cast hle
    obtain ⟨v, hv⟩ := intermediate_value_univ 0 u hd
      (show ((round (fl 0 - 0) : ℤ) : ℝ) + 1 / 2 ∈ Icc (fl 0 - 0) (fl u - u) by
        constructor <;> linarith)
    exact hval v _ hv

/-- Helper for `lemma16_3` (§16.3, lift calculus). Conversely, a lift within `r` of a translation by an integer gives
`‖f z − z‖ ≤ 2πr` on the circle. -/
theorem gl16_sy_chord_of_lift {f : ℂ → ℂ} {fl : ℝ → ℝ} (hf : IsCircleLift f fl) {k : ℤ} {r : ℝ}
    (hr : ∀ u : ℝ, |fl u - u - k| ≤ r) : ∀ z ∈ sphere (0 : ℂ) 1, ‖f z - z‖ ≤ 2 * π * r := by
  obtain ⟨-, -, -, -, -, hlh⟩ := hf
  intro z hz
  rw [← gl16_cl_exp_arg hz, ← hlh, gl16_sy_chord_eq]
  generalize arg z / (2 * π) = u
  have hπ := Real.pi_pos
  have e : π * (fl u - u) = π * (fl u - u - k) + k * π := by ring
  rw [e, Real.sin_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
  have h1 : |Real.sin (π * (fl u - u - k))| ≤ π * |fl u - u - k| := by
    refine Real.abs_sin_le_abs.trans_eq ?_
    rw [abs_mul, abs_of_pos hπ]
  have h2 := hr u
  nlinarith

/-- Helper for `gl16_sy_M_core` (§16.3): increments with mutual ratios at most `1 + η` differ by at most `η` times
either of them. -/
theorem gl16_sy_abs_diff {Dp Dm η : ℝ} (hp : 0 < Dp) (hm : 0 < Dm) (hη : 0 ≤ η) (a1 : Dp ≤ (1 + η) * Dm)
    (a2 : Dm ≤ (1 + η) * Dp) : |Dp - Dm| ≤ η * Dm ∧ |Dp - Dm| ≤ η * Dp := by
  rcases le_total Dp Dm with h | h
  · have e1 := mul_le_mul_of_nonneg_left h hη
    have e2 := mul_nonneg hη hp.le
    constructor <;> rw [abs_le] <;> constructor <;> linarith
  · have e1 := mul_le_mul_of_nonneg_left h hη
    have e2 := mul_nonneg hη hm.le
    constructor <;> rw [abs_le] <;> constructor <;> linarith

/-- Helper for `gl16_sy_M_of_lift` (§16.3): the core estimate at a reduced scale `0 < σ ≤ 1/2`. With
`D± = g̃(y ± σ) − g̃(y)` (signed so both are positive), `sin πD₊ ≤ M sin πD₋` and `sin πD₋ ≤ M sin πD₊`.
- `σ ≤ s₀`: `|D₊ − D₋| ≤ η min(D₊, D₋)` and `2D ≤ sin πD` (`gl16_sin_short`).
- `σ > s₀`: `|D₊ − D₋| ≤ 4ρ` and `sin πD± ≥ 15s₀/8` (`gl16_sin_low`). -/
theorem gl16_sy_M_core {gl : ℝ → ℝ} (hm : StrictMono gl) (hper : ∀ x, gl (x + 1) = gl x + 1) {k : ℤ}
    {ρ η s₀ : ℝ} (hs₀ : 0 < s₀) (hs₀' : s₀ ≤ 1 / 4) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ s₀ / 32) (hη : 0 ≤ η)
    (hnear : ∀ y : ℝ, |gl y - y - k| ≤ ρ)
    (hsmall : ∀ y s : ℝ, 0 < s → s ≤ s₀ →
      1 / (1 + η) ≤ LiZhongQC.qsRatio gl y s ∧ LiZhongQC.qsRatio gl y s ≤ 1 + η)
    (y : ℝ) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 2) :
    (1 + 4 * η + 32 * ρ / s₀)⁻¹ ≤
        |Real.sin (π * (gl (y + σ) - gl y))| / |Real.sin (π * (gl y - gl (y - σ)))| ∧
      |Real.sin (π * (gl (y + σ) - gl y))| / |Real.sin (π * (gl y - gl (y - σ)))| ≤ 1 + 4 * η + 32 * ρ / s₀ := by
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_le_four
  obtain ⟨hp0, hp1, hm0, hm1⟩ := gl16_incr_unit hm hper y hσ0 (by linarith)
  have n1 := abs_le.1 (hnear (y + σ))
  have n2 := abs_le.1 (hnear y)
  have n3 := abs_le.1 (hnear (y - σ))
  have hq' : LiZhongQC.qsRatio gl y σ = (gl (y + σ) - gl y) / (gl y - gl (y - σ)) := rfl
  generalize hDp : gl (y + σ) - gl y = Dp at hp0 hp1 hq' ⊢
  generalize hDm : gl y - gl (y - σ) = Dm at hm0 hm1 hq' ⊢
  have hsp := gl16_sin_pos hp0 hp1
  have hsm := gl16_sin_pos hm0 hm1
  rw [abs_of_pos hsp, abs_of_pos hsm]
  have hq : 0 ≤ 32 * ρ / s₀ := by positivity
  have hlip : |Real.sin (π * Dp) - Real.sin (π * Dm)| ≤ π * |Dp - Dm| := by
    have := Real.abs_sin_sub_sin_le (π * Dp) (π * Dm)
    rwa [← mul_sub, abs_mul, abs_of_pos hπ] at this
  have l := abs_le.1 hlip
  suffices key : Real.sin (π * Dp) ≤ (1 + 4 * η + 32 * ρ / s₀) * Real.sin (π * Dm) ∧
      Real.sin (π * Dm) ≤ (1 + 4 * η + 32 * ρ / s₀) * Real.sin (π * Dp) from
    gl16_qs_bound hsp hsm key.1 key.2
  have eM : ∀ w : ℝ, (1 + 4 * η + 32 * ρ / s₀) * w = w + 4 * η * w + 32 * ρ / s₀ * w := fun w => by ring
  rw [eM, eM]
  rcases le_or_gt σ s₀ with hσs | hσs
  · -- small scales: the lift's ratio is within `1 + η`
    obtain ⟨r1, r2⟩ := hsmall y σ hσ0 hσs
    rw [hq'] at r1 r2
    have a1 : Dp ≤ (1 + η) * Dm := (div_le_iff₀ hm0).1 r2
    have a2 : Dm ≤ (1 + η) * Dp := by
      rw [div_le_div_iff₀ (by linarith) hm0, one_mul] at r1
      linarith
    obtain ⟨sp1, -⟩ := gl16_sin_short hp0 (by linarith)
    obtain ⟨sm1, -⟩ := gl16_sin_short hm0 (by linarith)
    obtain ⟨hd1, hd2⟩ := gl16_sy_abs_diff hp0 hm0 hη a1 a2
    have b1 : π * |Dp - Dm| ≤ 2 * η * Real.sin (π * Dm) := by
      have h1 := mul_le_mul_of_nonneg_left hd1 hπ.le
      have h2 : π * (η * Dm) ≤ 4 * (η * Dm) := mul_le_mul_of_nonneg_right hπ4 (mul_nonneg hη hm0.le)
      have h3 := mul_le_mul_of_nonneg_left sm1 hη
      linarith
    have b2 : π * |Dp - Dm| ≤ 2 * η * Real.sin (π * Dp) := by
      have h1 := mul_le_mul_of_nonneg_left hd2 hπ.le
      have h2 : π * (η * Dp) ≤ 4 * (η * Dp) := mul_le_mul_of_nonneg_right hπ4 (mul_nonneg hη hp0.le)
      have h3 := mul_le_mul_of_nonneg_left sp1 hη
      linarith
    have c1 : 0 ≤ 2 * η * Real.sin (π * Dm) + 32 * ρ / s₀ * Real.sin (π * Dm) := by positivity
    have c2 : 0 ≤ 2 * η * Real.sin (π * Dp) + 32 * ρ / s₀ * Real.sin (π * Dp) := by positivity
    constructor <;> linarith
  · -- large scales: `D±` within `2ρ` of `σ`, sines at least `15 s₀/8`
    have hlo : ∀ D : ℝ, 0 < D → D < 1 → 15 * s₀ / 16 ≤ D → D ≤ 1 / 2 + s₀ / 16 →
        15 * s₀ / 8 ≤ Real.sin (π * D) := by
      intro D h0 h1 h2 h3
      refine le_trans ?_ (gl16_sin_low h0 h1)
      have : 15 * s₀ / 16 ≤ min D (1 - D) := le_min h2 (by linarith)
      linarith
    have sp := hlo Dp hp0 hp1 (by linarith) (by linarith)
    have sm := hlo Dm hm0 hm1 (by linarith) (by linarith)
    have hd : |Dp - Dm| ≤ 4 * ρ := by
      rw [abs_le]
      constructor <;> linarith
    have hπd : π * |Dp - Dm| ≤ 60 * ρ := by
      have h1 := mul_le_mul_of_nonneg_left hd hπ.le
      have h2 : π * (4 * ρ) ≤ 4 * (4 * ρ) := mul_le_mul_of_nonneg_right hπ4 (by positivity)
      linarith
    have e60 : 32 * ρ / s₀ * (15 * s₀ / 8) = 60 * ρ := by
      field_simp
      ring
    have hq1 : 60 * ρ ≤ 32 * ρ / s₀ * Real.sin (π * Dm) := by
      have := mul_le_mul_of_nonneg_left sm hq
      linarith
    have hq2 : 60 * ρ ≤ 32 * ρ / s₀ * Real.sin (π * Dp) := by
      have := mul_le_mul_of_nonneg_left sp hq
      linarith
    have c1 : 0 ≤ 4 * η * Real.sin (π * Dm) := by positivity
    have c2 : 0 ≤ 4 * η * Real.sin (π * Dp) := by positivity
    constructor <;> linarith

/-- Helper for `lemma16_3` (§16.3, lift calculus). The circle `M`-condition from lift data: a lift within `ρ` of an
integer translation, with ratios within `1 + η` at scales `≤ s₀`, gives the `M`-condition `1 + 4η + 32ρ/s₀`.
- The chord ratio at `(x, t)` only depends on `t/2π` mod `1`, up to inversion, so `0 < t/2π ≤ 1/2`.
- Scales `≤ s₀`: `|sin πa − sin πb| ≤ π|a − b|` and `sin πb ≥ 2b`.
- Scales in `(s₀, 1/2]`: both increments are within `2ρ` of the scale, and `sin πD ≥ 2 min(D, 1 − D)`. -/
theorem gl16_sy_M_of_lift {g : ℂ → ℂ} {gl : ℝ → ℝ} (hg : IsCircleLift g gl) {k : ℤ} {ρ η s₀ : ℝ} (hs₀ : 0 < s₀)
    (hs₀' : s₀ ≤ 1 / 4) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ s₀ / 32) (hη : 0 ≤ η) (hη' : η ≤ 1 / 4)
    (hnear : ∀ y : ℝ, |gl y - y - k| ≤ ρ)
    (hsmall : ∀ y s : ℝ, 0 < s → s ≤ s₀ →
      1 / (1 + η) ≤ LiZhongQC.qsRatio gl y s ∧ LiZhongQC.qsRatio gl y s ≤ 1 + η) :
    IsMCondition g (1 + 4 * η + 32 * ρ / s₀) := by
  obtain ⟨-, hm, -, -, hper, hlh⟩ := hg
  have _hη' := hη'  -- not needed: the bound `1 + 4η + 32ρ/s₀` holds for every `η ≥ 0`
  have hπ := Real.pi_pos
  intro x t ht
  rw [gl16_ratio_lift hlh x t]
  have hσ : ∀ n : ℤ, t / (2 * π) ≠ n := by
    intro n hn
    apply ht n
    rw [div_eq_iff (by positivity)] at hn
    rw [hn]
    ring
  generalize t / (2 * π) = σ at hσ ⊢
  generalize x / (2 * π) = y
  have hM0 : 0 < 1 + 4 * η + 32 * ρ / s₀ := by positivity
  have e : σ = (⌊σ⌋ : ℝ) + Int.fract σ := (Int.floor_add_fract σ).symm
  have hfr0 : 0 < Int.fract σ := by
    rcases (Int.fract_nonneg σ).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hσ ⌊σ⌋
      rw [← h, add_zero] at e
      exact e
  have hfr1 := Int.fract_lt_one σ
  rw [e, gl16_sin_ratio_shift hper y (Int.fract σ) ⌊σ⌋, one_div]
  generalize Int.fract σ = r at hfr0 hfr1 ⊢
  rcases le_or_gt r (1 / 2) with hr | hr
  · exact gl16_sy_M_core hm hper hs₀ hs₀' hρ hρ' hη hnear hsmall y hfr0 hr
  · rw [show r = 1 - (1 - r) by ring, gl16_sin_ratio_refl hper y (1 - r)]
    obtain ⟨a, b⟩ := gl16_sy_M_core hm hper hs₀ hs₀' hρ hρ' hη hnear hsmall y (σ := 1 - r) (by linarith)
      (by linarith)
    have hQ := lt_of_lt_of_le (inv_pos.2 hM0) a
    exact ⟨inv_anti₀ hQ b, inv_le_of_inv_le₀ hM0 a⟩

/-- Helper for `cor16_2_2` and `lemma16_3` (§16.3, near-affinity calculus). A near-affine map nearly preserves ratios:
- Let `F` be within `η (F b − F a)` of its chord at `p`, where `(p − a)/(b − a) ∈ [c, 1 − c]` and `η ≤ c/4`.
- Then the ratio `(F b − F p)/(F p − F a)` is within the factor `1 + 3η/c` of `(b − p)/(p − a)`. -/
theorem gl16_sy_transfer {F : ℝ → ℝ} (hF : StrictMono F) {a p b c η : ℝ} (hap : a < p) (hpb : p < b) (hc : 0 < c)
    (hc1 : c ≤ (p - a) / (b - a)) (hc2 : (p - a) / (b - a) ≤ 1 - c) (hη : 0 ≤ η) (hηc : η ≤ c / 4)
    (hna : |F p - (F a + (p - a) / (b - a) * (F b - F a))| ≤ η * (F b - F a)) :
    (F b - F p) / (F p - F a) ≤ (1 + 3 * η / c) * ((b - p) / (p - a)) ∧
      (b - p) / (p - a) ≤ (1 + 3 * η / c) * ((F b - F p) / (F p - F a)) := by
  have hpa : 0 < p - a := by linarith
  have hba : 0 < b - a := by linarith
  have hD0 : 0 < F b - F a := sub_pos.2 (hF (hap.trans hpb))
  have hr : (b - p) / (p - a) = (1 - (p - a) / (b - a)) / ((p - a) / (b - a)) := by
    field_simp
    ring
  rw [hr, show 3 * η / c = 3 * (η / c) by ring]
  generalize hl : (p - a) / (b - a) = l at hc1 hc2 hna ⊢
  have hA : F p - F a = l * (F b - F a) + (F p - (F a + l * (F b - F a))) := by ring
  have hB : F b - F p = (1 - l) * (F b - F a) - (F p - (F a + l * (F b - F a))) := by ring
  generalize he : F p - (F a + l * (F b - F a)) = e at hna hA hB
  generalize hD : F b - F a = D at hD0 hna hA hB
  generalize hA' : F p - F a = A at hA ⊢
  generalize hB' : F b - F p = B at hB ⊢
  obtain ⟨he1, he2⟩ := abs_le.1 hna
  have ha'0 : 0 ≤ η / c := div_nonneg hη hc.le
  have ha'1 : η / c ≤ 1 / 4 := by
    rw [div_le_iff₀ hc]
    linarith
  have hηc' : η / c * c = η := div_mul_cancel₀ _ hc.ne'
  generalize η / c = a' at ha'0 ha'1 hηc' ⊢
  have hl0 : 0 < l := by linarith
  have hl1 : 0 < 1 - l := by linarith
  have hηl : η ≤ a' * l := by
    rw [← hηc']
    exact mul_le_mul_of_nonneg_left hc1 ha'0
  have hηl' : η ≤ a' * (1 - l) := by
    rw [← hηc']
    exact mul_le_mul_of_nonneg_left (by linarith) ha'0
  have m1 := mul_le_mul_of_nonneg_right hηl hD0.le
  have m2 := mul_le_mul_of_nonneg_right hηl' hD0.le
  have hA1 : l * D * (1 - a') ≤ A := by nlinarith
  have hA2 : A ≤ l * D * (1 + a') := by nlinarith
  have hB1 : (1 - l) * D * (1 - a') ≤ B := by nlinarith
  have hB2 : B ≤ (1 - l) * D * (1 + a') := by nlinarith
  have hApos : 0 < A := lt_of_lt_of_le (mul_pos (mul_pos hl0 hD0) (by linarith)) hA1
  have hq : (1 - l) / l * l = 1 - l := div_mul_cancel₀ _ hl0.ne'
  have hq0 : 0 ≤ (1 - l) / l := div_nonneg hl1.le hl0.le
  have h13 : 1 + a' ≤ (1 + 3 * a') * (1 - a') := by
    nlinarith [mul_nonneg ha'0 (by linarith : (0 : ℝ) ≤ 1 / 4 - a')]
  constructor
  · rw [div_le_iff₀ hApos]
    calc B ≤ (1 - l) * D * (1 + a') := hB2
      _ ≤ (1 - l) * D * ((1 + 3 * a') * (1 - a')) :=
        mul_le_mul_of_nonneg_left h13 (mul_nonneg hl1.le hD0.le)
      _ = (1 + 3 * a') * ((1 - l) / l) * (l * D * (1 - a')) := by
        rw [show (1 + 3 * a') * ((1 - l) / l) * (l * D * (1 - a')) =
          (1 + 3 * a') * (1 - a') * ((1 - l) / l * l) * D by ring, hq]
        ring
      _ ≤ (1 + 3 * a') * ((1 - l) / l) * A := mul_le_mul_of_nonneg_left hA1 (by positivity)
  · rw [mul_div_assoc', le_div_iff₀ hApos]
    calc (1 - l) / l * A ≤ (1 - l) / l * (l * D * (1 + a')) := mul_le_mul_of_nonneg_left hA2 hq0
      _ = (1 - l) * D * (1 + a') := by
        rw [show (1 - l) / l * (l * D * (1 + a')) = (1 + a') * ((1 - l) / l * l) * D by ring, hq]
        ring
      _ ≤ (1 - l) * D * ((1 + 3 * a') * (1 - a')) :=
        mul_le_mul_of_nonneg_left h13 (mul_nonneg hl1.le hD0.le)
      _ = (1 + 3 * a') * ((1 - l) * D * (1 - a')) := by ring
      _ ≤ (1 + 3 * a') * B := mul_le_mul_of_nonneg_left hB1 (by positivity)

/-- Helper for the near-affinity calculus (§16.3): `gl16_sy_transfer` with the fraction read off the input ratio
`r = (b − p)/(p − a) ∈ [1/B, B]` (`c = 1/(1 + B)`). -/
theorem gl16_sy_trM {F : ℝ → ℝ} (hF : StrictMono F) {a p b η B : ℝ} (hap : a < p) (hpb : p < b) (hB : 0 < B)
    (hη : 0 ≤ η) (hη' : η ≤ 1 / (4 * (1 + B))) (hr1 : 1 / B ≤ (b - p) / (p - a)) (hr2 : (b - p) / (p - a) ≤ B)
    (hna : |F p - (F a + (p - a) / (b - a) * (F b - F a))| ≤ η * (F b - F a)) :
    (F b - F p) / (F p - F a) ≤ (1 + 3 * η * (1 + B)) * ((b - p) / (p - a)) ∧
      (b - p) / (p - a) ≤ (1 + 3 * η * (1 + B)) * ((F b - F p) / (F p - F a)) := by
  have hpa : 0 < p - a := by linarith
  have hba : 0 < b - a := by linarith
  have h2 := (div_le_iff₀ hpa).1 hr2
  have h1 : p - a ≤ B * (b - p) := by
    rw [div_le_div_iff₀ hB hpa, one_mul] at hr1
    linarith
  have hc1 : 1 / (1 + B) ≤ (p - a) / (b - a) := by
    rw [div_le_div_iff₀ (by linarith) hba, one_mul]
    linarith
  have hc2 : (p - a) / (b - a) ≤ 1 - 1 / (1 + B) := by
    rw [show 1 - 1 / (1 + B) = B / (1 + B) by field_simp; ring, div_le_div_iff₀ hba (by linarith)]
    linarith
  have hηc : η ≤ 1 / (1 + B) / 4 := by
    rw [div_div, mul_comm]
    exact hη'
  have h := gl16_sy_transfer hF hap hpb (by positivity) hc1 hc2 hη hηc hna
  rwa [show 3 * η / (1 / (1 + B)) = 3 * η * (1 + B) by field_simp] at h

/-- Helper for the near-affinity calculus (§16.3): `gl16_sy_trM` for input ratios in `[1/2, 2]`. -/
theorem gl16_sy_tr3 {F : ℝ → ℝ} (hF : StrictMono F) {a p b η : ℝ} (hap : a < p) (hpb : p < b) (hη : 0 ≤ η)
    (hη' : η ≤ 1 / 12) (hr1 : 1 / 2 ≤ (b - p) / (p - a)) (hr2 : (b - p) / (p - a) ≤ 2)
    (hna : |F p - (F a + (p - a) / (b - a) * (F b - F a))| ≤ η * (F b - F a)) :
    (F b - F p) / (F p - F a) ≤ (1 + 9 * η) * ((b - p) / (p - a)) ∧
      (b - p) / (p - a) ≤ (1 + 9 * η) * ((F b - F p) / (F p - F a)) := by
  have h := gl16_sy_trM hF hap hpb (by norm_num : (0 : ℝ) < 2) hη (by linarith) hr1 hr2 hna
  rwa [show 3 * η * (1 + 2) = 9 * η by ring] at h

/-- Helper for `cor16_2_2` (§16.3, near-affinity calculus). Near-affinity passes to the inverse with the same `η`: if
`P` is within `η (P b − P a)` of its chord on `[a, b]`, then each `p ∈ [a, b]` is within `η (b − a)` of the inverse
chord at `P p`. -/
theorem gl16_sy_inv_affine {P : ℝ → ℝ} (hP : StrictMono P) {a b η : ℝ} (hab : a < b)
    (hna : ∀ p ∈ Icc a b, |P p - (P a + (p - a) / (b - a) * (P b - P a))| ≤ η * (P b - P a)) :
    ∀ p ∈ Icc a b, |p - (a + (P p - P a) / (P b - P a) * (b - a))| ≤ η * (b - a) := by
  intro p hp
  have hD : 0 < P b - P a := sub_pos.2 (hP hab)
  have hL : 0 < b - a := sub_pos.2 hab
  have hD' := hD.ne'
  have hL' := hL.ne'
  have h := hna p hp
  have e : p - (a + (P p - P a) / (P b - P a) * (b - a)) =
      -((b - a) / (P b - P a)) * (P p - (P a + (p - a) / (b - a) * (P b - P a))) := by
    field_simp
    ring
  rw [e, abs_mul, abs_neg, abs_of_pos (div_pos hL hD)]
  calc (b - a) / (P b - P a) * |P p - (P a + (p - a) / (b - a) * (P b - P a))| ≤
      (b - a) / (P b - P a) * (η * (P b - P a)) := mul_le_mul_of_nonneg_left h (div_pos hL hD).le
    _ = η * (b - a) := by
      field_simp

/-- Helper for `cor16_2_2` and `lemma16_3` (§16.3, near-affinity calculus). Vanishing ratio distortion of a lift makes
it uniformly near-affine at small scales: `gl16_cl_affine3`, with `τ` where `ε(t) ≤ δ` (the ratio bounds force
`ε(t) ≥ 0`). -/
theorem gl16_sy_vanish_affine {F : ℝ → ℝ} (hF : StrictMono F)
    (hv : ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧ ∀ x t : ℝ, 0 < t →
      1 / (1 + ε t) ≤ LiZhongQC.qsRatio F x t ∧ LiZhongQC.qsRatio F x t ≤ 1 + ε t) :
    ∀ η > 0, ∃ τ > 0, ∀ a L : ℝ, 0 < L → L < τ →
      ∀ p ∈ Icc a (a + L), |F p - (F a + (p - a) / L * (F (a + L) - F a))| ≤ η * (F (a + L) - F a) := by
  obtain ⟨ε, hε, hε'⟩ := hv
  intro η hη
  obtain ⟨δ, hδ, hδ'⟩ := gl16_cl_affine3 η hη
  obtain ⟨τ, hτ, hτ'⟩ := Metric.tendsto_nhdsWithin_nhds.1 hε (min δ (1 / 2)) (lt_min hδ (by norm_num))
  refine ⟨τ, hτ, fun a L hL hLτ p hp => hδ' F hF a L hL (fun x t ht hxa hxb => ?_) p hp⟩
  have htτ : t < τ := by linarith
  have h1 := hτ' (mem_Ioi.2 ht) (by rw [Real.dist_eq, sub_zero, abs_of_pos ht]; exact htτ)
  rw [Real.dist_eq, sub_zero, abs_lt] at h1
  have m1 := min_le_left δ (1 / 2)
  have m2 := min_le_right δ (1 / 2)
  obtain ⟨r1, r2⟩ := hε' x t ht
  exact ⟨le_trans (one_div_le_one_div_of_le (by linarith) (by linarith)) r1, by linarith⟩

/-- Helper for `cor16_2_2` (§16.3, near-affinity calculus). Conversely, a continuous increasing lift
(`F(x + 1) = F(x) + 1`) that is uniformly near-affine at small scales has vanishing ratio distortion.
- Small scales: `gl16_sy_transfer` at the midpoint (`c = 1/2`).
- Each scale is bounded by `gl16_lift_incr_cmp`; then `gl16_vanishing_of_bounds`. -/
theorem gl16_sy_affine_vanish {F : ℝ → ℝ} (hF : StrictMono F) (hcF : Continuous F) (hper : ∀ x, F (x + 1) = F x + 1)
    (hna : ∀ η > 0, ∃ τ > 0, ∀ a L : ℝ, 0 < L → L < τ →
      ∀ p ∈ Icc a (a + L), |F p - (F a + (p - a) / L * (F (a + L) - F a))| ≤ η * (F (a + L) - F a)) :
    ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧ ∀ x t : ℝ, 0 < t →
      1 / (1 + ε t) ≤ LiZhongQC.qsRatio F x t ∧ LiZhongQC.qsRatio F x t ≤ 1 + ε t := by
  have key : ∀ η > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ → True ∧
      ∀ x, max (LiZhongQC.qsRatio F x t) (LiZhongQC.qsRatio F x t)⁻¹ - 1 ≤ η := by
    intro η hη
    have hη₀0 : 0 < min (η / 6) (1 / 8) := lt_min (by positivity) (by norm_num)
    have hη₀1 := min_le_left (η / 6) (1 / 8)
    have hη₀2 := min_le_right (η / 6) (1 / 8)
    generalize min (η / 6) (1 / 8) = η₀ at hη₀0 hη₀1 hη₀2
    obtain ⟨τ, hτ, hτ'⟩ := hna η₀ hη₀0
    refine ⟨τ / 2, half_pos hτ, fun t ht htτ => ⟨trivial, fun x => ?_⟩⟩
    have h := hτ' (x - t) (2 * t) (by linarith) (by linarith) x ⟨by linarith, by linarith⟩
    rw [show x - t + 2 * t = x + t by ring] at h
    have h' : |F x - (F (x - t) + (x - (x - t)) / (x + t - (x - t)) * (F (x + t) - F (x - t)))| ≤
        η₀ * (F (x + t) - F (x - t)) := by
      rw [show x + t - (x - t) = 2 * t by ring]
      exact h
    have hc1 : 1 / 2 ≤ (x - (x - t)) / (x + t - (x - t)) := by
      rw [show x - (x - t) = t by ring, show x + t - (x - t) = 2 * t by ring, le_div_iff₀ (by linarith)]
      linarith
    have hc2 : (x - (x - t)) / (x + t - (x - t)) ≤ 1 - 1 / 2 := by
      rw [show x - (x - t) = t by ring, show x + t - (x - t) = 2 * t by ring, div_le_iff₀ (by linarith)]
      linarith
    obtain ⟨c1, c2⟩ := gl16_sy_transfer hF (a := x - t) (p := x) (b := x + t) (by linarith) (by linarith)
      (by norm_num) hc1 hc2 hη₀0.le (by linarith) h'
    rw [show (x + t - x) / (x - (x - t)) = 1 by rw [show x + t - x = t by ring, show x - (x - t) = t by ring,
      div_self ht.ne'], show 3 * η₀ / (1 / 2) = 6 * η₀ by ring] at c1 c2
    rw [mul_one] at c1
    have hq : LiZhongQC.qsRatio F x t = (F (x + t) - F x) / (F x - F (x - t)) := rfl
    rw [hq]
    have hmax := gl16_sy_max_of (R := (F (x + t) - F x) / (F x - F (x - t))) (X := 1 + 6 * η₀) (by linarith)
      (by rw [div_le_iff₀ (by linarith)]; linarith) c1
    linarith
  obtain ⟨ε, hε, hε'⟩ := gl16_vanishing_of_bounds (R := LiZhongQC.qsRatio F) (P := fun _ => True)
    (fun t ht _ => gl16_lift_incr_cmp hcF hF hper ht) key
  exact ⟨ε, hε, fun x t ht => hε' x t ht trivial⟩

/-- Helper for `gl16_sy_closed` and `gl16_sy_conj` (§16.3, near-affinity calculus). A lift `K` of a map with the
`M`-condition `1 + ε`, within `θ` of a translation, is near-affine with error `η` on windows of length `≤ θ` once
`ε ≤ θ` (`gl16_cl_ratio` with increments `≤ ζ`, then `gl16_cl_affine3`). -/
theorem gl16_sy_na_of_M : ∀ η > 0, ∃ θ > 0, ∀ (k : ℂ → ℂ) (K : ℝ → ℝ), StrictMono K →
    (∀ y : ℝ, exp (2 * π * I * K y) = k (exp (2 * π * I * y))) → ∀ ε : ℝ, 0 ≤ ε → ε ≤ θ →
    IsMCondition k (1 + ε) → ∀ j : ℝ, (∀ u, |K u - u - j| ≤ θ) → ∀ a L : ℝ, 0 < L → L ≤ θ →
    ∀ p ∈ Icc a (a + L), |K p - (K a + (p - a) / L * (K (a + L) - K a))| ≤ η * (K (a + L) - K a) := by
  intro η hη
  obtain ⟨δ, hδ, hδ'⟩ := gl16_cl_affine3 η hη
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_le_four
  obtain ⟨d, hd0, hd1, hd2⟩ : ∃ d : ℝ, 0 < d ∧ d ≤ δ ∧ d ≤ 1 / 2 :=
    ⟨min δ (1 / 2), lt_min hδ (by norm_num), min_le_left _ _, min_le_right _ _⟩
  obtain ⟨ζ, hζ0, hζ1, hζ2⟩ : ∃ ζ : ℝ, 0 < ζ ∧ ζ ≤ 1 ∧ ζ ≤ d / 128 :=
    ⟨min 1 (d / 128), lt_min one_pos (by positivity), min_le_left _ _, min_le_right _ _⟩
  have hπζ : 8 * (π * ζ) ^ 2 ≤ d := by
    have h1 : π * ζ ≤ 4 * ζ := mul_le_mul_of_nonneg_right hπ4 hζ0.le
    have h2 : (π * ζ) ^ 2 ≤ (4 * ζ) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have h3 : ζ * ζ ≤ ζ := by nlinarith
    nlinarith
  refine ⟨min (ζ / 3) (d / 8), lt_min (by positivity) (by positivity),
    fun k K hK hlk ε hε0 hεθ hM j hj a L hL hLθ => ?_⟩
  have hθ1 := min_le_left (ζ / 3) (d / 8)
  have hθ2 := min_le_right (ζ / 3) (d / 8)
  have hmax : 8 * max ε ((π * ζ) ^ 2) ≤ d := by
    rcases le_total ε ((π * ζ) ^ 2) with h | h
    · rw [max_eq_right h]
      exact hπζ
    · rw [max_eq_left h]
      linarith
  have hmax' : max ε ((π * ζ) ^ 2) ≤ 1 / 2 := by linarith
  refine hδ' K hK a L hL (fun x t ht hxa hxb => ?_)
  -- the increments of `K` over the triple are at most `ζ`
  have i1 := abs_le.1 (hj (x + t))
  have i2 := abs_le.1 (hj x)
  have i3 := abs_le.1 (hj (x - t))
  have hp : 0 < K (x + t) - K x := sub_pos.2 (hK (by linarith))
  have hm : 0 < K x - K (x - t) := sub_pos.2 (hK (by linarith))
  obtain ⟨r1, r2⟩ := gl16_cl_ratio hM hε0 hlk hmax' ht (by linarith) hp (by linarith) hm (by linarith)
  have hpos : 0 < 1 + 8 * max ε ((π * ζ) ^ 2) := by positivity
  exact ⟨le_trans (one_div_le_one_div_of_le hpos (by linarith)) r1, by linarith⟩

/-- Helper for `gl16_sy_conj` (§16.3): membership in `U(ε)` from a lift. A lift within `ρ` of an integer translation
(`2πρ < ε`) and the `M`-condition `1 + ε` give all components of `U(ε)`: sense-preserving (`gl16_sy_homeo_of_lift`),
Ahlfors (`gl16_cl_qsA_of_M`), and near the identity with the inverse (`gl16_sy_chord_of_lift` for the lift and for
the inverse lift). -/
theorem gl16_sy_U_of_lift {g : ℂ → ℂ} {G : ℝ → ℝ} (hG : IsCircleLift g G) {k : ℤ} {ρ ε : ℝ}
    (hnear : ∀ y, |G y - y - k| ≤ ρ) (hρ : 2 * π * ρ < ε) (hM : IsMCondition g (1 + ε)) : g ∈ qsNbhdU ε := by
  obtain ⟨Gi, hGic, hGim, hGli, hGil⟩ := gl16_cl_lift_inv hG
  have hGi := gl16_sy_inv_lift hG hGic hGim hGli hGil
  have hnear' : ∀ y, |Gi y - ⌊Gi 0⌋ - y - ((-k - ⌊Gi 0⌋ : ℤ) : ℝ)| ≤ ρ := fun y => by
    have := hnear (Gi y)
    rw [hGli] at this
    rw [show Gi y - ⌊Gi 0⌋ - y - ((-k - ⌊Gi 0⌋ : ℤ) : ℝ) = -(y - Gi y - k) by push_cast; ring, abs_neg]
    exact this
  exact ⟨gl16_sy_homeo_of_lift hG, gl16_cl_qsA_of_M (gl16_sy_contOn_of_lift hG) (gl16_cl_lift_injOn hG) hM,
    fun z hz => ⟨(gl16_sy_chord_of_lift hG hnear z hz).trans_lt hρ,
      (gl16_sy_chord_of_lift hGi hnear' z hz).trans_lt hρ⟩, hM⟩

/-- Helper for `gl16_sy_conj` (§16.3): the ratio chain through three near-affine maps. If `Ψ`, `Φ` and `H` are within
`η ≤ 1/27` of their chords at the successive images of the symmetric triple `y − s, y, y + s`, then the ratio of
`H ∘ Φ ∘ Ψ` at `(y, s)` is within the factor `(1 + 9η)³` of `1` (`gl16_sy_tr3` three times). -/
theorem gl16_sy_chain3 {H Φ Ψ : ℝ → ℝ} (hH : StrictMono H) (hΦ : StrictMono Φ) (hΨ : StrictMono Ψ) {η y s : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 27) (hs : 0 < s)
    (h1 : |Ψ y - (Ψ (y - s) + (y - (y - s)) / (y + s - (y - s)) * (Ψ (y + s) - Ψ (y - s)))| ≤
      η * (Ψ (y + s) - Ψ (y - s)))
    (h2 : |Φ (Ψ y) - (Φ (Ψ (y - s)) + (Ψ y - Ψ (y - s)) / (Ψ (y + s) - Ψ (y - s)) *
      (Φ (Ψ (y + s)) - Φ (Ψ (y - s))))| ≤ η * (Φ (Ψ (y + s)) - Φ (Ψ (y - s))))
    (h3 : |H (Φ (Ψ y)) - (H (Φ (Ψ (y - s))) + (Φ (Ψ y) - Φ (Ψ (y - s))) / (Φ (Ψ (y + s)) - Φ (Ψ (y - s))) *
      (H (Φ (Ψ (y + s))) - H (Φ (Ψ (y - s)))))| ≤ η * (H (Φ (Ψ (y + s))) - H (Φ (Ψ (y - s))))) :
    1 / (1 + 9 * η) ^ 3 ≤ LiZhongQC.qsRatio (fun x => H (Φ (Ψ x))) y s ∧
      LiZhongQC.qsRatio (fun x => H (Φ (Ψ x))) y s ≤ (1 + 9 * η) ^ 3 := by
  have ha0 : 0 ≤ 9 * η := by positivity
  have ha1 : 9 * η ≤ 1 / 3 := by linarith
  have hab : y - s < y := by linarith
  have hbc : y < y + s := by linarith
  have hr0 : (y + s - y) / (y - (y - s)) = 1 := by
    rw [show y + s - y = s by ring, show y - (y - s) = s by ring, div_self hs.ne']
  -- through `Ψ`
  obtain ⟨c1, c2⟩ := gl16_sy_tr3 hΨ hab hbc hη (by linarith) (by rw [hr0]; norm_num) (by rw [hr0]; norm_num) h1
  rw [hr0] at c1 c2
  obtain ⟨s1, s2⟩ := gl16_sy_step (R := 1) (X := 1) ha0 one_pos c1 c2 (by norm_num) le_rfl
  have hX1 : 0 < (1 + 9 * η) * 1 := by positivity
  have hX1' : (1 + 9 * η) * 1 ≤ 2 := by linarith
  -- through `Φ`
  obtain ⟨d1, d2⟩ := gl16_sy_tr3 hΦ (hΨ hab) (hΨ hbc) hη (by linarith)
    (le_trans (one_div_le_one_div_of_le hX1 hX1') s1) (s2.trans hX1') h2
  obtain ⟨t1, t2⟩ := gl16_sy_step ha0 hX1 d1 d2 s1 s2
  have hX2 : 0 < (1 + 9 * η) * ((1 + 9 * η) * 1) := by positivity
  have hX2' : (1 + 9 * η) * ((1 + 9 * η) * 1) ≤ 2 := by nlinarith
  -- through `H`
  obtain ⟨e1, e2⟩ := gl16_sy_tr3 hH (hΦ (hΨ hab)) (hΦ (hΨ hbc)) hη (by linarith)
    (le_trans (one_div_le_one_div_of_le hX2 hX2') t1) (t2.trans hX2') h3
  obtain ⟨u1, u2⟩ := gl16_sy_step ha0 hX2 e1 e2 t1 t2
  have e3 : (1 + 9 * η) * ((1 + 9 * η) * ((1 + 9 * η) * 1)) = (1 + 9 * η) ^ 3 := by ring
  rw [e3] at u1 u2
  exact ⟨u1, u2⟩

/-- Helper for `gl16_sy_conj` (§16.3): `(1 + 9ε/300)³ ≤ 1 + ε/8` for `0 < ε ≤ 1`. -/
theorem gl16_sy_num {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) : (1 + 9 * (ε / 300)) ^ 3 ≤ 1 + ε / 8 := by
  have ha : 0 ≤ ε / 100 := by positivity
  have ha' : ε / 100 ≤ 1 / 100 := by linarith
  have e : 1 + 9 * (ε / 300) = 1 + 3 * (ε / 100) := by ring
  rw [e, show ε / 8 = 25 / 2 * (ε / 100) by ring]
  generalize ε / 100 = a at ha ha' ⊢
  have h2 : a * a ≤ 1 / 100 * a := mul_le_mul_of_nonneg_right ha' ha
  have h3 : a * a * a ≤ 1 / 100 * a * a := mul_le_mul_of_nonneg_right h2 ha
  nlinarith

/-- Helper for `cor16_2_2` (a) (§16.3). Symmetric maps are closed under composition: the lift of `f ∘ g` is
`f̃ ∘ g̃` up to an integer. `g̃` keeps small symmetric triples nearly symmetric, and `f̃` is near-affine on the small
windows they span (`gl16_sy_vanish_affine`, `gl16_sy_transfer`). -/
theorem gl16_sy_comp_vanishing {f g : ℂ → ℂ} (hf : Pommerenke1992.IsSensePreservingCircleHomeo f)
    (hg : Pommerenke1992.IsSensePreservingCircleHomeo g) (hvf : HasVanishingRatioDistortion f)
    (hvg : HasVanishingRatioDistortion g) : HasVanishingRatioDistortion (f ∘ g) := by
  obtain ⟨fl, hfl⟩ := gl16_cl_lift hf
  obtain ⟨gl, hgl⟩ := gl16_cl_lift hg
  have hlift := gl16_sy_comp_lift hfl hgl
  refine gl16_circle_vanishing hlift ?_
  obtain ⟨εg, hεg, hεg'⟩ := gl16_lift_vanishing hgl hvg
  have hna := gl16_sy_vanish_affine hfl.2.1 (gl16_lift_vanishing hfl hvf)
  have hgm := hgl.2.1
  have hfm := hfl.2.1
  obtain ⟨hc, hm, -, -, hper, -⟩ := hlift
  have key : ∀ η > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ → True ∧
      ∀ x, max (LiZhongQC.qsRatio (fun x => fl (gl x) - ⌊fl (gl 0)⌋) x t)
        (LiZhongQC.qsRatio (fun x => fl (gl x) - ⌊fl (gl 0)⌋) x t)⁻¹ - 1 ≤ η := by
    intro η hη
    obtain ⟨η', hη'0, hη'1, hη'2⟩ : ∃ η' : ℝ, 0 < η' ∧ η' ≤ η ∧ η' ≤ 1 :=
      ⟨min η 1, lt_min hη one_pos, min_le_left _ _, min_le_right _ _⟩
    obtain ⟨τ, hτ, hτ'⟩ := hna (η' / 27) (by positivity)
    obtain ⟨δu, hδu, hδu'⟩ := gl16_lift_uc hgl.1 hgl.2.2.2.2.1 hτ
    obtain ⟨δg, hδg, hδg'⟩ := Metric.tendsto_nhdsWithin_nhds.1 hεg (η' / 3) (by positivity)
    refine ⟨min (δu / 2) δg, lt_min (half_pos hδu) hδg, fun t ht htδ => ⟨trivial, fun x => ?_⟩⟩
    have ht1 : t < δu / 2 := lt_of_lt_of_le htδ (min_le_left _ _)
    have ht2 : t < δg := lt_of_lt_of_le htδ (min_le_right _ _)
    have hεt := hδg' (mem_Ioi.2 ht) (by rw [Real.dist_eq, sub_zero, abs_of_pos ht]; exact ht2)
    rw [Real.dist_eq, sub_zero, abs_lt] at hεt
    obtain ⟨r1, r2⟩ := hεg' x t ht
    have hq : LiZhongQC.qsRatio gl x t = (gl (x + t) - gl x) / (gl x - gl (x - t)) := rfl
    rw [hq] at r1 r2
    -- `g̃`'s ratio is within `1 + η'/3`
    have rg1 : 1 / (1 + η' / 3) ≤ (gl (x + t) - gl x) / (gl x - gl (x - t)) :=
      le_trans (one_div_le_one_div_of_le (by linarith) (by linarith)) r1
    have rg2 : (gl (x + t) - gl x) / (gl x - gl (x - t)) ≤ 1 + η' / 3 := by linarith
    -- the window spanned by the triple is short, so `f̃` is near-affine on it
    have hwin : gl (x + t) - gl (x - t) < τ := by
      have := hδu' (x + t) (x - t) (by rw [show x + t - (x - t) = 2 * t by ring, abs_of_pos (by linarith)]; linarith)
      rwa [abs_of_pos (sub_pos.2 (hgm (by linarith)))] at this
    have e : gl (x - t) + (gl (x + t) - gl (x - t)) = gl (x + t) := by ring
    have hNA := hτ' (gl (x - t)) (gl (x + t) - gl (x - t)) (sub_pos.2 (hgm (by linarith))) hwin (gl x)
      ⟨hgm.monotone (by linarith), by rw [e]; exact hgm.monotone (by linarith)⟩
    rw [e] at hNA
    have hr1 : 1 / 2 ≤ (gl (x + t) - gl x) / (gl x - gl (x - t)) :=
      le_trans (one_div_le_one_div_of_le (by positivity) (by linarith)) rg1
    obtain ⟨c1, c2⟩ := gl16_sy_tr3 hfm (hgm (show x - t < x by linarith)) (hgm (show x < x + t by linarith))
      (by positivity) (by linarith) hr1 (by linarith) hNA
    have hqH : LiZhongQC.qsRatio (fun x => fl (gl x) - ⌊fl (gl 0)⌋) x t =
        (fl (gl (x + t)) - fl (gl x)) / (fl (gl x) - fl (gl (x - t))) := by
      show (fl (gl (x + t)) - ⌊fl (gl 0)⌋ - (fl (gl x) - ⌊fl (gl 0)⌋)) /
        (fl (gl x) - ⌊fl (gl 0)⌋ - (fl (gl (x - t)) - ⌊fl (gl 0)⌋)) = _
      congr 1 <;> ring
    rw [hqH]
    obtain ⟨s1, s2⟩ := gl16_sy_step (by positivity) (by positivity) c1 c2 rg1 rg2
    have hX : (1 + 9 * (η' / 27)) * (1 + η' / 3) ≤ 1 + η := by
      nlinarith [mul_nonneg hη'0.le (by linarith : (0 : ℝ) ≤ 1 - η')]
    have hmax := gl16_sy_max_of (by positivity) s1 s2
    linarith
  obtain ⟨ε, hε, hε'⟩ := gl16_vanishing_of_bounds
    (R := LiZhongQC.qsRatio (fun x => fl (gl x) - ⌊fl (gl 0)⌋)) (P := fun _ => True)
    (fun t ht _ => gl16_lift_incr_cmp hc hm hper ht) key
  exact ⟨ε, hε, fun x t ht => hε' x t ht trivial⟩

/-- Helper for `thm16_2`, `cor16_2_2` (b) and `lemma16_3` (§16.3). The inverse of a symmetric map is symmetric:
`f̃` near-affine at small scales (`gl16_sy_vanish_affine`) passes to `f̃⁻¹` (`gl16_sy_inv_affine`), so `f̃⁻¹` is
near-affine at small scales and symmetric (`gl16_sy_affine_vanish`); `gl16_sy_inv_lift` transfers this to the
circle. -/
theorem gl16_sy_inv_vanishing {f : ℂ → ℂ} (hf : Pommerenke1992.IsSensePreservingCircleHomeo f)
    (hvf : HasVanishingRatioDistortion f) : HasVanishingRatioDistortion (Function.invFunOn f (sphere 0 1)) := by
  obtain ⟨fl, hfl⟩ := gl16_cl_lift hf
  obtain ⟨hi, hic, him, hli, hil⟩ := gl16_cl_lift_inv hfl
  have hlifti := gl16_sy_inv_lift hfl hic him hli hil
  refine gl16_circle_vanishing hlifti ?_
  have hna := gl16_sy_vanish_affine hfl.2.1 (gl16_lift_vanishing hfl hvf)
  have hper := hfl.2.2.2.2.1
  have hiper : ∀ y, hi (y + 1) = hi y + 1 := fun y => by
    rw [← hil (hi y + 1), hper, hli]
  -- `f̃⁻¹` is near-affine at small scales (`gl16_sy_inv_affine` on the image windows)
  have hnai : ∀ η > 0, ∃ τ > 0, ∀ a L : ℝ, 0 < L → L < τ →
      ∀ p ∈ Icc a (a + L), |hi p - (hi a + (p - a) / L * (hi (a + L) - hi a))| ≤ η * (hi (a + L) - hi a) := by
    intro η hη
    obtain ⟨τ, hτ, hτ'⟩ := hna η hη
    obtain ⟨δ, hδ, hδ'⟩ := gl16_lift_uc hic hiper hτ
    refine ⟨δ, hδ, fun a L hL hLδ p hp => ?_⟩
    have hab : hi a < hi (a + L) := him (by linarith)
    have hw : hi (a + L) - hi a < τ := by
      have := hδ' (a + L) a (by rw [show a + L - a = L by ring, abs_of_pos hL]; exact hLδ)
      rwa [abs_of_pos (by linarith)] at this
    have e : hi a + (hi (a + L) - hi a) = hi (a + L) := by ring
    have h1 := gl16_sy_inv_affine hfl.2.1 hab (fun q hq => by
      have := hτ' (hi a) (hi (a + L) - hi a) (by linarith) hw q (by rw [e]; exact hq)
      rwa [e] at this) (hi p) ⟨him.monotone hp.1, him.monotone hp.2⟩
    simp only [hli] at h1
    rwa [show a + L - a = L by ring] at h1
  obtain ⟨ε, hε, hε'⟩ := gl16_sy_affine_vanish him hic hiper hnai
  exact ⟨ε, hε, fun x t ht => by rw [gl16_sy_qsRatio_sub]; exact hε' x t ht⟩

/-- Helper for `cor16_2_2` (c) (§16.3). Closedness. If `s_ε ∘ h⁻¹ ∈ U(ε)` with `s_ε` symmetric, for every `ε`, then
`h̃ = k̃⁻¹ ∘ s̃_ε` up to an integer, with `k = s_ε ∘ h⁻¹`.
- `k̃` and hence `k̃⁻¹` are near-affine with an error `η(ε)` on small windows (`gl16_cl_ratio`, `gl16_cl_affine3`,
  `gl16_sy_inv_affine`).
- So `h̃`'s small-scale ratios are within `(1 + ε_s(t))(1 + O(η(ε)))`; let `ε → 0`. -/
theorem gl16_sy_closed {h : ℂ → ℂ} (hh : Pommerenke1992.IsSensePreservingCircleHomeo h)
    (hq : Pommerenke1992.IsQuasisymmetricA h)
    (hs : ∀ ε > 0, ∃ s : ℂ → ℂ, Pommerenke1992.IsSensePreservingCircleHomeo s ∧ HasVanishingRatioDistortion s ∧
      s ∘ Function.invFunOn h (sphere 0 1) ∈ qsNbhdU ε) : HasVanishingRatioDistortion h := by
  obtain ⟨hl, hlift⟩ := gl16_cl_lift hh
  obtain ⟨hi, hic, him, hli, hil⟩ := gl16_cl_lift_inv hlift
  obtain ⟨M₀, hM₀⟩ := gl16_cl_M_of_qsA hq
  obtain ⟨M₁, -, -, -, -, hqs⟩ := gl16_qs_of_M hlift hM₀
  have hlc := hlift.1
  have hlm := hlift.2.1
  have hlp := hlift.2.2.2.2.1
  have hiper : ∀ y, hi (y + 1) = hi y + 1 := fun y => by
    rw [← hil (hi y + 1), hlp, hli]
  have hM₁0 : 0 < M₁ := by
    have h1 := (hqs 0 1 one_pos).2
    have hpos : 0 < LiZhongQC.qsRatio hl 0 1 :=
      div_pos (sub_pos.2 (hlm (by norm_num))) (sub_pos.2 (hlm (by norm_num)))
    linarith
  refine gl16_circle_vanishing hlift ?_
  have key : ∀ γ > 0, ∃ δ > 0, ∀ t, 0 < t → t < δ → True ∧
      ∀ x, max (LiZhongQC.qsRatio hl x t) (LiZhongQC.qsRatio hl x t)⁻¹ - 1 ≤ γ := by
    intro γ hγ
    obtain ⟨γ', hγ'0, hγ'1, hγ'2⟩ : ∃ γ' : ℝ, 0 < γ' ∧ γ' ≤ γ ∧ γ' ≤ 1 :=
      ⟨min γ 1, lt_min hγ one_pos, min_le_left _ _, min_le_right _ _⟩
    -- the near-affinity error `η` of `k̃`, small against the fraction bound `1/(1 + M₁)`
    obtain ⟨η, hη0, hηe⟩ : ∃ η : ℝ, 0 < η ∧ 3 * η * (1 + M₁) = γ' / 3 :=
      ⟨γ' / (9 * (1 + M₁)), by positivity, by field_simp; ring⟩
    have hη1 : η ≤ 1 / (4 * (1 + M₁)) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    obtain ⟨θ, hθ, hθ'⟩ := gl16_sy_na_of_M η hη0
    obtain ⟨ε₀, hε₀0, hε₀1, hε₀2⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ θ ∧ ε₀ ≤ 1 :=
      ⟨min θ 1, lt_min hθ one_pos, min_le_left _ _, min_le_right _ _⟩
    obtain ⟨s, hs1, hs2, -, -, hk3, hk4⟩ := hs ε₀ hε₀0
    obtain ⟨sl, hsl⟩ := gl16_cl_lift hs1
    -- the lift `K = s̃ ∘ h̃⁻¹` of `k = s ∘ h⁻¹`
    have hlk : ∀ y : ℝ, exp (2 * π * I * sl (hi y)) =
        (s ∘ Function.invFunOn h (sphere 0 1)) (exp (2 * π * I * y)) := fun y => by
      show _ = s (Function.invFunOn h (sphere 0 1) (exp (2 * π * I * y)))
      rw [gl16_sy_invFun_exp hlift hli, ← hsl.2.2.2.2.2]
    have hKm : StrictMono fun y => sl (hi y) := hsl.2.1.comp him
    have hKl := gl16_sy_lift_of (F := fun y => sl (hi y)) (hsl.1.comp hic) hKm
      (fun y => by show sl (hi (y + 1)) = sl (hi y) + 1; rw [hiper, hsl.2.2.2.2.1]) hlk
    obtain ⟨j, hj⟩ := gl16_sy_near_lift hKl hε₀2 (fun z hz => (hk3 z hz).1)
    have hjθ : ∀ u, |sl (hi u) - u - ((j : ℝ) + ⌊sl (hi 0)⌋)| ≤ θ := fun u => by
      have := hj u
      rw [show sl (hi u) - u - ((j : ℝ) + ⌊sl (hi 0)⌋) = sl (hi u) - ⌊sl (hi 0)⌋ - u - j by ring]
      exact this.trans (by linarith)
    have hNA := hθ' _ _ hKm hlk ε₀ hε₀0.le hε₀1 hk4 _ hjθ
    -- `s` is symmetric; `h̃` is uniformly continuous
    obtain ⟨εs, hεs, hεs'⟩ := gl16_lift_vanishing hsl hs2
    obtain ⟨τs, hτs, hτs'⟩ := Metric.tendsto_nhdsWithin_nhds.1 hεs (γ' / 3) (by positivity)
    obtain ⟨δh, hδh, hδh'⟩ := gl16_lift_uc hlc hlp hθ
    refine ⟨min (δh / 2) τs, lt_min (half_pos hδh) hτs, fun t ht htδ => ⟨trivial, fun x => ?_⟩⟩
    have ht1 : t < δh / 2 := lt_of_lt_of_le htδ (min_le_left _ _)
    have ht2 : t < τs := lt_of_lt_of_le htδ (min_le_right _ _)
    have hεt := hτs' (mem_Ioi.2 ht) (by rw [Real.dist_eq, sub_zero, abs_of_pos ht]; exact ht2)
    rw [Real.dist_eq, sub_zero, abs_lt] at hεt
    have hab : hl (x - t) < hl x := hlm (by linarith)
    have hbc : hl x < hl (x + t) := hlm (by linarith)
    -- the window `[h̃(x − t), h̃(x + t)]` is shorter than `θ`
    have hwin : hl (x + t) - hl (x - t) ≤ θ := by
      have := hδh' (x + t) (x - t) (by rw [show x + t - (x - t) = 2 * t by ring, abs_of_pos (by linarith)]; linarith)
      rw [abs_of_pos (by linarith)] at this
      exact this.le
    have e : hl (x - t) + (hl (x + t) - hl (x - t)) = hl (x + t) := by ring
    have hNAx := hNA (hl (x - t)) (hl (x + t) - hl (x - t)) (by linarith) hwin (hl x)
      ⟨hab.le, by rw [e]; exact hbc.le⟩
    rw [e] at hNAx
    -- transfer through `K` at the triple `h̃(x − t), h̃(x), h̃(x + t)`
    obtain ⟨q1, q2⟩ := hqs x t ht
    have hq : LiZhongQC.qsRatio hl x t = (hl (x + t) - hl x) / (hl x - hl (x - t)) := rfl
    rw [hq] at q1 q2 ⊢
    obtain ⟨c1, c2⟩ := gl16_sy_trM (F := fun y => sl (hi y)) hKm hab hbc hM₁0 hη0.le hη1
      (by rw [one_div]; exact q1) q2 hNAx
    simp only [hil] at c1 c2
    rw [hηe] at c1 c2
    obtain ⟨r1, r2⟩ := hεs' x t ht
    have hqs' : LiZhongQC.qsRatio sl x t = (sl (x + t) - sl x) / (sl x - sl (x - t)) := rfl
    rw [hqs'] at r1 r2
    have rs1 : 1 / (1 + γ' / 3) ≤ (sl (x + t) - sl x) / (sl x - sl (x - t)) :=
      le_trans (one_div_le_one_div_of_le (by linarith) (by linarith)) r1
    have rs2 : (sl (x + t) - sl x) / (sl x - sl (x - t)) ≤ 1 + γ' / 3 := by linarith
    obtain ⟨u1, u2⟩ := gl16_sy_step (by positivity) (by positivity) c2 c1 rs1 rs2
    have hX : (1 + γ' / 3) * (1 + γ' / 3) ≤ 1 + γ := by
      nlinarith [mul_nonneg hγ'0.le (by linarith : (0 : ℝ) ≤ 1 - γ')]
    have hmax := gl16_sy_max_of (by positivity) u1 u2
    linarith
  obtain ⟨ε, hε, hε'⟩ := gl16_vanishing_of_bounds (R := LiZhongQC.qsRatio hl) (P := fun _ => True)
    (fun t ht _ => gl16_lift_incr_cmp hlc hlm hlp ht) key
  exact ⟨ε, hε, fun x t ht => hε' x t ht trivial⟩

/-- Helper for `thm16_2` and `lemma16_3` (§16.3, the core of Lemma 3). If the lift `h̃` and its inverse `h̃⁻¹` are
both uniformly near-affine at small scales, then conjugation by `h` is continuous at the identity. For
`f ∈ U(δ)` the conjugate `g = h ∘ f ∘ h⁻¹` has the lift `G = h̃ ∘ f̃ ∘ h̃⁻¹` up to an integer.
- `G` is within `ω_{h̃}(δ/4)` of an integer translation (`gl16_sy_near_lift`, uniform continuity).
- Small symmetric triples pass nearly symmetric through `h̃⁻¹`, `f̃` (M-condition `1 + δ`: `gl16_cl_ratio`,
  `gl16_cl_affine3`) and `h̃` (`gl16_sy_transfer` three times).
- `gl16_sy_M_of_lift` gives `G`'s M-condition. The sense-preserving, Ahlfors and inverse parts follow from the lifts
  (`gl16_sy_homeo_of_lift`, `gl16_cl_qsA_of_M`, `gl16_sy_inv_lift`, `gl16_sy_chord_of_lift`). -/
theorem gl16_sy_conj {h : ℂ → ℂ} {hl hi : ℝ → ℝ} (hlift : IsCircleLift h hl) (hic : Continuous hi)
    (him : StrictMono hi) (hli : ∀ x, hl (hi x) = x) (hil : ∀ x, hi (hl x) = x)
    (hna : ∀ η > 0, ∃ τ > 0, ∀ a L : ℝ, 0 < L → L < τ →
      ∀ p ∈ Icc a (a + L), |hl p - (hl a + (p - a) / L * (hl (a + L) - hl a))| ≤ η * (hl (a + L) - hl a))
    (hnai : ∀ η > 0, ∃ τ > 0, ∀ a L : ℝ, 0 < L → L < τ →
      ∀ p ∈ Icc a (a + L), |hi p - (hi a + (p - a) / L * (hi (a + L) - hi a))| ≤ η * (hi (a + L) - hi a)) :
    ∀ ε > 0, ∃ δ > 0, ∀ f ∈ qsNbhdU δ, h ∘ f ∘ Function.invFunOn h (sphere 0 1) ∈ qsNbhdU ε := by
  intro ε hε
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_le_four
  have hlc := hlift.1
  have hlm := hlift.2.1
  have hlp := hlift.2.2.2.2.1
  have hiper : ∀ y, hi (y + 1) = hi y + 1 := fun y => by
    rw [← hil (hi y + 1), hlp, hli]
  obtain ⟨ε', hε'0, hε'1, hε'2⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ 1 :=
    ⟨min ε 1, lt_min hε one_pos, min_le_left _ _, min_le_right _ _⟩
  -- the near-affinity error `η₀` of each of the three maps
  have hη₀0 : 0 < ε' / 300 := by positivity
  have hη₀1 : ε' / 300 ≤ 1 / 27 := by linarith
  have hX3 := gl16_sy_num hε'0 hε'2
  generalize ε' / 300 = η₀ at hη₀0 hη₀1 hX3
  obtain ⟨τi, hτi, hτi'⟩ := hnai η₀ hη₀0
  obtain ⟨τl, hτl, hτl'⟩ := hna η₀ hη₀0
  obtain ⟨θ, hθ, hθ'⟩ := gl16_sy_na_of_M η₀ hη₀0
  -- the scale `s₀`, the translation error `ρ₀`, and finally `δ`
  obtain ⟨δi, hδi, hδi'⟩ := gl16_lift_uc hic hiper (show 0 < min θ (τl / 2) from lt_min hθ (half_pos hτl))
  obtain ⟨s₀, hs₀0, hs₀1, hs₀2, hs₀3⟩ : ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 / 4 ∧ 2 * s₀ < τi ∧ 2 * s₀ < δi := by
    refine ⟨min (1 / 4) (min (τi / 4) (δi / 4)), lt_min (by norm_num) (lt_min (by positivity) (by positivity)),
      min_le_left _ _, ?_, ?_⟩
    · have := (min_le_right (1 / 4) (min (τi / 4) (δi / 4))).trans (min_le_left _ _)
      linarith
    · have := (min_le_right (1 / 4) (min (τi / 4) (δi / 4))).trans (min_le_right _ _)
      linarith
  obtain ⟨ρ₀, hρ₀0, hρ₀1, hρ₀2⟩ : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ ≤ s₀ / 32 ∧ ρ₀ ≤ ε' * s₀ / 64 :=
    ⟨min (s₀ / 32) (ε' * s₀ / 64), lt_min (by positivity) (by positivity), min_le_left _ _, min_le_right _ _⟩
  obtain ⟨δl, hδl, hδl'⟩ := gl16_lift_uc hlc hlp hρ₀0
  obtain ⟨δ, hδ0, hδ1, hδ2, hδ3, hδ4⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ δ ≤ θ ∧ δ ≤ δl ∧ δ ≤ τl := by
    refine ⟨min 1 (min θ (min δl τl)), lt_min one_pos (lt_min hθ (lt_min hδl hτl)), min_le_left _ _, ?_, ?_, ?_⟩
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ, hδ0, fun f hf => ?_⟩
  obtain ⟨hf1, -, hf3, hf4⟩ := hf
  obtain ⟨fl, hfl⟩ := gl16_cl_lift hf1
  have hfm := hfl.2.1
  obtain ⟨k, hk⟩ := gl16_sy_near_lift hfl hδ1 (fun z hz => (hf3 z hz).1)
  -- the conjugate `h ∘ f ∘ h⁻¹` has the lift `h̃ ∘ f̃ ∘ h̃⁻¹`, normalized
  have hF3 : ∀ y : ℝ, exp (2 * π * I * hl (fl (hi y))) =
      (h ∘ f ∘ Function.invFunOn h (sphere 0 1)) (exp (2 * π * I * y)) := fun y => by
    show _ = h (f (Function.invFunOn h (sphere 0 1) (exp (2 * π * I * y))))
    rw [gl16_sy_invFun_exp hlift hli, ← hfl.2.2.2.2.2, ← hlift.2.2.2.2.2]
  have hGl := gl16_sy_lift_of (F := fun y => hl (fl (hi y))) (hlc.comp (hfl.1.comp hic))
    (hlm.comp (hfm.comp him)) (fun y => by
      show hl (fl (hi (y + 1))) = hl (fl (hi y)) + 1
      rw [hiper, hfl.2.2.2.2.1, hlp]) hF3
  -- the lift is within `ρ₀` of an integer translation
  have hnear : ∀ y : ℝ, |hl (fl (hi y)) - ⌊hl (fl (hi 0))⌋ - y - ((k - ⌊hl (fl (hi 0))⌋ : ℤ) : ℝ)| ≤ ρ₀ := by
    intro y
    have e1 : hl (hi y + k) = y + k := by rw [gl16_lift_int hlp, hli]
    have h1 := hk (hi y)
    have h2 := hδl' (fl (hi y)) (hi y + k) (by
      rw [show fl (hi y) - (hi y + k) = fl (hi y) - hi y - k by ring]
      linarith)
    rw [e1] at h2
    rw [show hl (fl (hi y)) - ⌊hl (fl (hi 0))⌋ - y - ((k - ⌊hl (fl (hi 0))⌋ : ℤ) : ℝ) = hl (fl (hi y)) - (y + k) by
      push_cast
      ring]
    exact h2.le
  -- small scales: the chain through `h̃⁻¹`, `f̃` and `h̃`
  have hsmall : ∀ y s : ℝ, 0 < s → s ≤ s₀ →
      1 / (1 + ((1 + 9 * η₀) ^ 3 - 1)) ≤ LiZhongQC.qsRatio (fun y => hl (fl (hi y)) - ⌊hl (fl (hi 0))⌋) y s ∧
        LiZhongQC.qsRatio (fun y => hl (fl (hi y)) - ⌊hl (fl (hi 0))⌋) y s ≤ 1 + ((1 + 9 * η₀) ^ 3 - 1) := by
    intro y s hs hss
    rw [gl16_sy_qsRatio_sub, show 1 + ((1 + 9 * η₀) ^ 3 - 1) = (1 + 9 * η₀) ^ 3 by ring]
    have hab : hi (y - s) < hi (y + s) := him (by linarith)
    -- `h̃⁻¹` on `[y − s, y + s]`
    have h1 := hτi' (y - s) (2 * s) (by linarith) (by linarith) y ⟨by linarith, by linarith⟩
    rw [show y - s + 2 * s = y + s by ring] at h1
    have h1' : |hi y - (hi (y - s) + (y - (y - s)) / (y + s - (y - s)) * (hi (y + s) - hi (y - s)))| ≤
        η₀ * (hi (y + s) - hi (y - s)) := by
      rw [show y + s - (y - s) = 2 * s by ring]
      exact h1
    -- `f̃` on `[h̃⁻¹(y − s), h̃⁻¹(y + s)]`, a window shorter than `θ` and `τl/2`
    have hw2 := hδi' (y + s) (y - s) (by rw [show y + s - (y - s) = 2 * s by ring, abs_of_pos (by linarith)]; linarith)
    rw [abs_of_pos (by linarith)] at hw2
    have hw2a := hw2.trans_le (min_le_left _ _)
    have hw2b := hw2.trans_le (min_le_right _ _)
    have hkθ : ∀ u, |fl u - u - (k : ℝ)| ≤ θ := fun u => (hk u).trans (by linarith)
    have e2 : hi (y - s) + (hi (y + s) - hi (y - s)) = hi (y + s) := by ring
    have h2 := hθ' f fl hfm hfl.2.2.2.2.2 δ hδ0.le hδ2 hf4 k hkθ (hi (y - s)) (hi (y + s) - hi (y - s))
      (by linarith) hw2a.le (hi y) ⟨(him (by linarith : y - s < y)).le, by rw [e2]; exact (him (by linarith)).le⟩
    rw [e2] at h2
    -- `h̃` on `[f̃(h̃⁻¹(y − s)), f̃(h̃⁻¹(y + s))]`, a window shorter than `τl`
    have k1 := abs_le.1 (hk (hi (y + s)))
    have k2 := abs_le.1 (hk (hi (y - s)))
    have hw3 : fl (hi (y + s)) - fl (hi (y - s)) < τl := by linarith
    have e3 : fl (hi (y - s)) + (fl (hi (y + s)) - fl (hi (y - s))) = fl (hi (y + s)) := by ring
    have h3 := hτl' (fl (hi (y - s))) (fl (hi (y + s)) - fl (hi (y - s))) (sub_pos.2 (hfm hab)) hw3 (fl (hi y))
      ⟨(hfm (him (by linarith : y - s < y))).le, by rw [e3]; exact (hfm (him (by linarith))).le⟩
    rw [e3] at h3
    exact gl16_sy_chain3 hlm hfm him hη₀0.le hη₀1 hs h1' h2 h3
  -- the `M`-condition of the conjugate, and the other components of `U(ε)`
  have hη3 : 0 ≤ (1 + 9 * η₀) ^ 3 - 1 := by
    have : 1 ≤ (1 + 9 * η₀) ^ 3 := one_le_pow₀ (by linarith)
    linarith
  have hM := gl16_sy_M_of_lift hGl (k := k - ⌊hl (fl (hi 0))⌋) hs₀0 hs₀1 hρ₀0.le hρ₀1 hη3 (by linarith) hnear
    hsmall
  have hq32 : 0 ≤ 32 * ρ₀ / s₀ := by positivity
  have hbound : 1 + 4 * ((1 + 9 * η₀) ^ 3 - 1) + 32 * ρ₀ / s₀ ≤ 1 + ε := by
    have : 32 * ρ₀ / s₀ ≤ ε' / 2 := by
      rw [div_le_iff₀ hs₀0]
      linarith
    linarith
  have hM' := gl16_sy_M_mono hM (by linarith) hbound
  refine gl16_sy_U_of_lift hGl (k := k - ⌊hl (fl (hi 0))⌋) hnear ?_ hM'
  have h1 : 2 * π * ρ₀ ≤ 8 * ρ₀ := mul_le_mul_of_nonneg_right (by linarith) hρ₀0.le
  have h2 : ε' * s₀ ≤ ε' * (1 / 4) := mul_le_mul_of_nonneg_left hs₀1 hε'0.le
  linarith

/-- Helper for `thm16_2` (§16.3). Membership in `U(ε)` only depends on the values on the circle. -/
theorem gl16_sy_U_congr {g g' : ℂ → ℂ} {ε : ℝ} (heq : EqOn g g' (sphere 0 1)) (hg : g ∈ qsNbhdU ε) :
    g' ∈ qsNbhdU ε := by
  obtain ⟨⟨u, huc, hum, hup, hu⟩, ⟨hc, hinj, M, hM⟩, hnear, hMc⟩ := hg
  have hS : ∀ θ : ℝ, exp ((θ : ℂ) * I) ∈ sphere (0 : ℂ) 1 := fun θ => by
    rw [mem_sphere_zero_iff_norm]
    exact norm_exp_ofReal_mul_I θ
  have hS1 : ∀ x t : ℝ, exp (((x : ℂ) + t) * I) ∈ sphere (0 : ℂ) 1 := fun x t => by
    rw [← Complex.ofReal_add]
    exact hS _
  have hS2 : ∀ x t : ℝ, exp (((x : ℂ) - t) * I) ∈ sphere (0 : ℂ) 1 := fun x t => by
    rw [← Complex.ofReal_sub]
    exact hS _
  refine ⟨⟨u, huc, hum, hup, fun t => ?_⟩, ⟨hc.congr (fun z hz => (heq hz).symm), hinj.congr heq, M,
    fun z₁ h₁ z₂ h₂ z₃ h₃ hd => ?_⟩, fun z hz => ?_, fun x t ht => ?_⟩
  · rw [← heq (hS t)]
    exact hu t
  · rw [← heq h₁, ← heq h₂, ← heq h₃]
    exact hM z₁ h₁ z₂ h₂ z₃ h₃ hd
  · rw [← heq hz, gl16_sy_invFunOn_congr heq hinj]
    exact hnear z hz
  · rw [← heq (hS1 x t), ← heq (hS x), ← heq (hS2 x t)]
    exact hMc x t ht

/-- Helper for `thm16_2` (§16.3). For a circle map with a lift (a bijection of the circle), `(h⁻¹)⁻¹ = h` on the
circle (`invFunOn` twice). -/
theorem gl16_sy_inv_inv {h : ℂ → ℂ} {hl : ℝ → ℝ} (hlift : IsCircleLift h hl) :
    EqOn (Function.invFunOn (Function.invFunOn h (sphere 0 1)) (sphere 0 1)) h (sphere 0 1) := by
  have hinj := gl16_cl_lift_injOn hlift
  obtain ⟨hmaps, hsurj⟩ := gl16_sy_maps_surj hlift
  have hk1 : ∀ z ∈ sphere (0 : ℂ) 1, Function.invFunOn h (sphere 0 1) (h z) = z := fun z hz =>
    hinj.leftInvOn_invFunOn hz
  have hk2 : ∀ z ∈ sphere (0 : ℂ) 1, h (Function.invFunOn h (sphere 0 1) z) = z := fun z hz =>
    Function.invFunOn_eq (hsurj z hz)
  have hkinj : InjOn (Function.invFunOn h (sphere 0 1)) (sphere 0 1) := fun a ha b hb hab => by
    rw [← hk2 a ha, ← hk2 b hb, hab]
  intro z hz
  have hex : ∃ a ∈ sphere (0 : ℂ) 1, Function.invFunOn h (sphere 0 1) a = z := ⟨h z, hmaps z hz, hk1 z hz⟩
  exact hkinj (Function.invFunOn_mem hex) (hmaps z hz) ((Function.invFunOn_eq hex).trans (hk1 z hz).symm)

/-- Helper for `thm16_2` and `lemma16_3` (§16.3, near-affinity calculus). Uniform near-affinity at small scales is
invariant under translations of the variable and of the value (`G(x) = F(x + c) + d`). -/
theorem gl16_sy_na_shift {F G : ℝ → ℝ} {c d : ℝ} (hG : ∀ x, G x = F (x + c) + d)
    (hna : ∀ η > 0, ∃ τ > 0, ∀ a L : ℝ, 0 < L → L < τ →
      ∀ p ∈ Icc a (a + L), |F p - (F a + (p - a) / L * (F (a + L) - F a))| ≤ η * (F (a + L) - F a)) :
    ∀ η > 0, ∃ τ > 0, ∀ a L : ℝ, 0 < L → L < τ →
      ∀ p ∈ Icc a (a + L), |G p - (G a + (p - a) / L * (G (a + L) - G a))| ≤ η * (G (a + L) - G a) := by
  intro η hη
  obtain ⟨τ, hτ, hτ'⟩ := hna η hη
  refine ⟨τ, hτ, fun a L hL hLτ p hp => ?_⟩
  have h := hτ' (a + c) L hL hLτ (p + c) ⟨by linarith [hp.1], by linarith [hp.2]⟩
  rw [show p + c - (a + c) = p - a by ring] at h
  simp only [hG]
  rw [show a + L + c = a + c + L by ring]
  have e : F (p + c) + d - (F (a + c) + d + (p - a) / L * (F (a + c + L) + d - (F (a + c) + d))) =
      F (p + c) - (F (a + c) + (p - a) / L * (F (a + c + L) - F (a + c))) := by ring
  rw [e, show F (a + c + L) + d - (F (a + c) + d) = F (a + c + L) - F (a + c) by ring]
  exact h

/-- **Theorem 2** (§16.3, l. 12033). The characteristic topological subgroup `S` of the partial topological group QS
consists precisely of the maps with vanishing ratio distortion: for quasisymmetric `h`, conjugation by `h` and by `h⁻¹`
is continuous at the identity iff `h` has vanishing ratio distortion. -/
theorem thm16_2 {h : ℂ → ℂ} (hh : Pommerenke1992.IsSensePreservingCircleHomeo h)
    (hq : Pommerenke1992.IsQuasisymmetricA h) :
    ((∀ ε > 0, ∃ δ > 0, ∀ f ∈ qsNbhdU δ, h ∘ f ∘ Function.invFunOn h (sphere 0 1) ∈ qsNbhdU ε) ∧
      ∀ ε > 0, ∃ δ > 0, ∀ f ∈ qsNbhdU δ, Function.invFunOn h (sphere 0 1) ∘ f ∘ h ∈ qsNbhdU ε) ↔
      HasVanishingRatioDistortion h := by
  constructor
  · rintro ⟨h1, -⟩
    exact gl16_cl_vanishing hh hq h1
  · intro hv
    obtain ⟨hl, hlift⟩ := gl16_cl_lift hh
    obtain ⟨hi, hic, him, hli, hil⟩ := gl16_cl_lift_inv hlift
    have hna := gl16_sy_vanish_affine hlift.2.1 (gl16_lift_vanishing hlift hv)
    have hlifti := gl16_sy_inv_lift hlift hic him hli hil
    have hnai' := gl16_sy_vanish_affine hlifti.2.1 (gl16_lift_vanishing hlifti (gl16_sy_inv_vanishing hh hv))
    have hnai := gl16_sy_na_shift (F := fun y => hi y - ⌊hi 0⌋) (G := hi) (c := 0) (d := ⌊hi 0⌋)
      (fun x => by simp) hnai'
    refine ⟨gl16_sy_conj hlift hic him hli hil hna hnai, ?_⟩
    -- the inverse `h⁻¹`, with lift `h̃⁻¹ − n` and inverse lift `h̃(· + n)`
    have hc' := gl16_sy_conj (hl := fun y => hi y - ⌊hi 0⌋) (hi := fun x => hl (x + ⌊hi 0⌋)) hlifti
      (hlift.1.comp (continuous_id.add continuous_const)) (fun a b hab => hlift.2.1 (by linarith))
      (fun x => by simp [hil]) (fun x => by simp [hli])
      hnai' (gl16_sy_na_shift (F := hl) (G := fun x => hl (x + ⌊hi 0⌋)) (c := ⌊hi 0⌋) (d := 0) (fun x => by simp) hna)
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hc' ε hε
    refine ⟨δ, hδ, fun f hf => gl16_sy_U_congr (fun z hz => ?_) (hδ' f hf)⟩
    show Function.invFunOn h (sphere 0 1) (f (Function.invFunOn (Function.invFunOn h (sphere 0 1)) (sphere 0 1) z)) =
      Function.invFunOn h (sphere 0 1) (f (h z))
    rw [gl16_sy_inv_inv hlift hz]

/-- **Corollary 2** (§16.3, l. 12036). The symmetric homeomorphisms form a closed topological subgroup of QS: closed
under composition and inversion, and every quasisymmetric `h` all of whose right neighbourhoods `U(ε) ∘ h` contain a
symmetric map is symmetric. -/
theorem cor16_2_2 :
    (∀ f g : ℂ → ℂ, Pommerenke1992.IsSensePreservingCircleHomeo f → Pommerenke1992.IsSensePreservingCircleHomeo g →
      HasVanishingRatioDistortion f → HasVanishingRatioDistortion g → HasVanishingRatioDistortion (f ∘ g)) ∧
    (∀ f : ℂ → ℂ, Pommerenke1992.IsSensePreservingCircleHomeo f → HasVanishingRatioDistortion f →
      HasVanishingRatioDistortion (Function.invFunOn f (sphere 0 1))) ∧
    ∀ h : ℂ → ℂ, Pommerenke1992.IsSensePreservingCircleHomeo h → Pommerenke1992.IsQuasisymmetricA h →
      (∀ ε > 0, ∃ s : ℂ → ℂ, Pommerenke1992.IsSensePreservingCircleHomeo s ∧ HasVanishingRatioDistortion s ∧
        s ∘ Function.invFunOn h (sphere 0 1) ∈ qsNbhdU ε) → HasVanishingRatioDistortion h := by
  exact ⟨fun f g hf hg hvf hvg => gl16_sy_comp_vanishing hf hg hvf hvg, fun f hf hvf => gl16_sy_inv_vanishing hf hvf,
    fun h hh hq hs => gl16_sy_closed hh hq hs⟩

/-- **Corollary 3** (§16.3, l. 12039), first part. `S` is a proper subgroup of QS, and QS is not a topological group:
some quasisymmetric `h` is not symmetric, and conjugation by it is not continuous at the identity. -/
theorem cor16_2_3_a :
    ∃ h : ℂ → ℂ, Pommerenke1992.IsSensePreservingCircleHomeo h ∧ Pommerenke1992.IsQuasisymmetricA h ∧
      ¬ HasVanishingRatioDistortion h ∧
      ¬ ∀ ε > 0, ∃ δ > 0, ∀ f ∈ qsNbhdU δ, h ∘ f ∘ Function.invFunOn h (sphere 0 1) ∈ qsNbhdU ε := by
  refine ⟨fun z : ℂ => z * exp (I * ((‖z - 1‖ / 2 : ℝ) : ℂ)), gl16_cl_corner_lift.2, gl16_cl_corner_qs,
    gl16_cl_corner_not, fun hc => ?_⟩
  exact gl16_cl_corner_not (gl16_cl_vanishing gl16_cl_corner_lift.2 gl16_cl_corner_qs hc)

/-- **Corollary 3** (§16.3, l. 12039), second part. `S` contains the `C¹` diffeomorphisms of the circle: a circle
homeomorphism whose lift and its inverse are `C¹` has vanishing ratio distortion. -/
theorem cor16_2_3_b {h : ℂ → ℂ} {hl : ℝ → ℝ} (hh : Pommerenke1992.IsSensePreservingCircleHomeo h)
    (hlift : IsCircleLift h hl) (hC1 : ContDiff ℝ 1 hl) (hpos : ∀ x, 0 < deriv hl x) :
    HasVanishingRatioDistortion h := by
  -- `hh` is not needed: the lift determines `h` on the circle
  have _hh := hh
  obtain ⟨-, -, -, -, hper, hlh⟩ := hlift
  obtain ⟨m, M, hm, hb⟩ := gl16_deriv_bounds hC1 hpos hper
  have hMpos : 0 < M := lt_of_lt_of_le hm ((hb 0).1.trans (hb 0).2)
  have hπ := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ → ℝ, ∀ x t : ℝ, F x t = ‖h (exp ((x + t) * I)) - h (exp (x * I))‖ /
      ‖h (exp (x * I)) - h (exp ((x - t) * I))‖ := ⟨_, fun _ _ => rfl⟩
  -- for `0 < t < 2π`: the sine ratio, positive, with a bound uniform in `x`
  have hRB : ∀ x t : ℝ, 0 < t → t < 2 * π →
      F x t = Real.sin (π * (hl (x / (2 * π) + t / (2 * π)) - hl (x / (2 * π)))) /
        Real.sin (π * (hl (x / (2 * π)) - hl (x / (2 * π) - t / (2 * π)))) ∧
      0 < F x t ∧ max (F x t) (F x t)⁻¹ - 1 ≤ 1 / (2 * (m * min (t / (2 * π)) (1 - t / (2 * π)))) := by
    intro x t ht0 ht1
    have hs0 : 0 < t / (2 * π) := div_pos ht0 h2π
    have hs1 : t / (2 * π) < 1 := (div_lt_one h2π).2 ht1
    obtain ⟨i1, -, i3, i4, -, i6⟩ := gl16_incr2 hC1 hb hper (x / (2 * π)) hs0 hs1
    obtain ⟨hsp, hsm, hbd⟩ := gl16_ratio_bdd hm hs0 hs1 i1 i3 i4 i6
    have hFe : F x t = Real.sin (π * (hl (x / (2 * π) + t / (2 * π)) - hl (x / (2 * π)))) /
        Real.sin (π * (hl (x / (2 * π)) - hl (x / (2 * π) - t / (2 * π)))) := by
      rw [hF, gl16_ratio_lift hlh, abs_of_pos hsp, abs_of_pos hsm]
    exact ⟨hFe, by rw [hFe]; exact div_pos hsp hsm, by rw [hFe]; exact hbd⟩
  -- for small `t`, uniformly in `x`
  have hFsmall : ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ t₀ > 0, ∀ t, 0 < t → t < t₀ → t < 2 * π ∧ ∀ x,
      max (F x t) (F x t)⁻¹ - 1 ≤ 8 * η := by
    intro η hη hη2
    obtain ⟨δ, hδ, hδ'⟩ := gl16_deriv_uc hC1 hper (mul_pos hη hm)
    have hπM : 0 < π * M := by positivity
    have hs₀pos : 0 < min (min (δ / 4) (min 1 η / (π * M))) (1 / 2) :=
      lt_min (lt_min (by linarith) (div_pos (lt_min one_pos hη) hπM)) (by norm_num)
    refine ⟨2 * π * min (min (δ / 4) (min 1 η / (π * M))) (1 / 2), by positivity, fun t ht0 ht1 => ?_⟩
    have hs0 : 0 < t / (2 * π) := div_pos ht0 h2π
    have hss₀ : t / (2 * π) < min (min (δ / 4) (min 1 η / (π * M))) (1 / 2) := by
      rw [div_lt_iff₀ h2π]
      linarith
    have hsδ : t / (2 * π) < δ / 4 := lt_of_lt_of_le hss₀ (le_trans (min_le_left _ _) (min_le_left _ _))
    have hsM' : t / (2 * π) < min 1 η / (π * M) := lt_of_lt_of_le hss₀ (le_trans (min_le_left _ _) (min_le_right _ _))
    have hs12 : t / (2 * π) < 1 / 2 := lt_of_lt_of_le hss₀ (min_le_right _ _)
    have ht2 : t < 2 * π := by
      have : t / (2 * π) < 1 := by linarith
      rwa [div_lt_one h2π] at this
    refine ⟨ht2, fun x => ?_⟩
    rw [(hRB x t ht0 ht2).1]
    rw [lt_div_iff₀ hπM] at hsM'
    exact gl16_ratio_small hC1 hm hb hη hη2 hδ' (x / (2 * π)) hs0 (by linarith) hsM'.le
  -- the distortion function
  unfold HasVanishingRatioDistortion
  simp only [← hF]
  refine ⟨fun t => sSup (Set.range fun x : ℝ => max (F x t) (F x t)⁻¹ - 1), ?_, fun x t ht0 ht1 => ?_⟩
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro e he
    obtain ⟨t₀, ht₀, hsm⟩ := hFsmall (min (e / 16) (1 / 2)) (lt_min (by linarith) (by norm_num)) (min_le_right _ _)
    refine ⟨t₀, ht₀, fun t ht htd => ?_⟩
    have ht0 : 0 < t := ht
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0] at htd
    obtain ⟨ht2, hsmx⟩ := hsm t ht0 htd
    have hnn : ∀ y ∈ Set.range fun x : ℝ => max (F x t) (F x t)⁻¹ - 1, 0 ≤ y := by
      rintro y ⟨x, rfl⟩
      have hp := (hRB x t ht0 ht2).2.1
      rcases le_total 1 (F x t) with h1 | h1
      · linarith [le_max_left (F x t) (F x t)⁻¹]
      · have : 1 ≤ (F x t)⁻¹ := by rw [le_inv_comm₀ one_pos hp, inv_one]; exact h1
        linarith [le_max_right (F x t) (F x t)⁻¹]
    have h0 : 0 ≤ sSup (Set.range fun x : ℝ => max (F x t) (F x t)⁻¹ - 1) := Real.sSup_nonneg hnn
    have h1 : sSup (Set.range fun x : ℝ => max (F x t) (F x t)⁻¹ - 1) ≤ 8 * min (e / 16) (1 / 2) :=
      csSup_le (Set.range_nonempty _) (by rintro y ⟨x, rfl⟩; exact hsmx x)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
    have : 8 * min (e / 16) (1 / 2) ≤ e / 2 := by
      have := min_le_left (e / 16) (1 / 2)
      linarith
    linarith
  · obtain ⟨-, hp, -⟩ := hRB x t ht0 ht1
    have hbdd : BddAbove (Set.range fun x : ℝ => max (F x t) (F x t)⁻¹ - 1) :=
      ⟨_, by rintro y ⟨x', rfl⟩; exact (hRB x' t ht0 ht1).2.2⟩
    have hle : max (F x t) (F x t)⁻¹ - 1 ≤ sSup (Set.range fun x : ℝ => max (F x t) (F x t)⁻¹ - 1) :=
      le_csSup hbdd ⟨x, rfl⟩
    have hmax1 := le_max_left (F x t) (F x t)⁻¹
    have hmax2 := le_max_right (F x t) (F x t)⁻¹
    refine ⟨?_, by linarith⟩
    have hinv : (F x t)⁻¹ ≤ 1 + sSup (Set.range fun x : ℝ => max (F x t) (F x t)⁻¹ - 1) := by linarith
    have hpos1 : 0 < 1 + sSup (Set.range fun x : ℝ => max (F x t) (F x t)⁻¹ - 1) :=
      lt_of_lt_of_le (inv_pos.2 hp) hinv
    rw [div_le_iff₀ hpos1]
    calc (1 : ℝ) = F x t * (F x t)⁻¹ := (mul_inv_cancel₀ hp.ne').symm
      _ ≤ F x t * (1 + sSup (Set.range fun x : ℝ => max (F x t) (F x t)⁻¹ - 1)) :=
        mul_le_mul_of_nonneg_left hinv hp.le
      _ = _ := by ring

/-- **Lemma 3** (§16.3, l. 12046). If `h` has vanishing ratio distortion and `f` is quasisymmetric and near the
identity, then `h ∘ f ∘ h⁻¹` is near the identity. -/
theorem lemma16_3 {h : ℂ → ℂ} (hh : Pommerenke1992.IsSensePreservingCircleHomeo h)
    (hq : Pommerenke1992.IsQuasisymmetricA h) (hv : HasVanishingRatioDistortion h) :
    ∀ ε > 0, ∃ δ > 0, ∀ f ∈ qsNbhdU δ, h ∘ f ∘ Function.invFunOn h (sphere 0 1) ∈ qsNbhdU ε := by
  have _hq := hq  -- not needed: vanishing ratio distortion of `h` (and of `h⁻¹`) suffices
  obtain ⟨hl, hlift⟩ := gl16_cl_lift hh
  obtain ⟨hi, hic, him, hli, hil⟩ := gl16_cl_lift_inv hlift
  have hna := gl16_sy_vanish_affine hlift.2.1 (gl16_lift_vanishing hlift hv)
  have hlifti := gl16_sy_inv_lift hlift hic him hli hil
  have hnai' := gl16_sy_vanish_affine hlifti.2.1 (gl16_lift_vanishing hlifti (gl16_sy_inv_vanishing hh hv))
  have hnai := gl16_sy_na_shift (F := fun y => hi y - ⌊hi 0⌋) (G := hi) (c := 0) (d := ⌊hi 0⌋)
    (fun x => by simp) hnai'
  exact gl16_sy_conj hlift hic him hli hil hna hnai

/-- **Lemma 4** (§16.3, l. 12058). If conjugation by `h` is continuous at the identity in QS, then `h` has vanishing
ratio distortion. -/
theorem lemma16_4 {h : ℂ → ℂ} (hh : Pommerenke1992.IsSensePreservingCircleHomeo h)
    (hq : Pommerenke1992.IsQuasisymmetricA h)
    (hc : ∀ ε > 0, ∃ δ > 0, ∀ f ∈ qsNbhdU δ, h ∘ f ∘ Function.invFunOn h (sphere 0 1) ∈ qsNbhdU ε) :
    HasVanishingRatioDistortion h := by
  exact gl16_cl_vanishing hh hq hc

end GardinerLakic2000
