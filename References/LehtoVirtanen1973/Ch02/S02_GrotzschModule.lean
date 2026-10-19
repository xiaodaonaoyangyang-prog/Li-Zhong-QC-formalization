import References.LehtoVirtanen1973.Ch02.S01_ExtremalRingDomains
import LiZhongQC.Ch03.S14_PoincareMetric

/-!
# Lehto–Virtanen, Chapter II §2: Module of Grötzsch's extremal domain

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. II §2
(pp. 59–63; `full.md` P1:1714–1873).

`μ` is the module of Grötzsch's extremal domain (§1.1, `LiZhongQC.grotzschMu`), a real function used only on
`0 < r < 1`; every formula below is stated for arguments of `μ` in that interval. The quadrilateral of (2.1) is the
upper half-plane of `ℂ̄` with four vertices on the extended real axis (Ch. I §2.3); Q(∞, -r₁, 0, 1) is carried onto
Q(0, 1/(1 + r₁), 1, ∞) by x ↦ -1/(x - 1).

* Formula (2.1) (§2.1) — `eq2_2_1`
* Definition (the Legendre normal integral `K(r)`, §2.1) — `legendreK`
* Formula (2.2) (§2.1) — `eq2_2_2`
* Formula (2.3) (§2.2) — `eq2_2_3`
* Formula (2.4) (§2.2) — `eq2_2_4`
* Formula (2.5) (§2.2) — exists: `LiZhongQC.em_mu_landen` (the same equation for u = r with both sides doubled and
  exchanged: μ((1 - r)/(1 + r)) = 2 μ(√(1 - r²)) for 0 < r < 1)
* Formula (2.6) (§2.2) — exists: `LiZhongQC.eq5_19` (with ρ = r₁: μ(√(1/(1 + ρ))) μ(√(ρ/(1 + ρ))) = π²/4, i.e. (2.6)
  divided by 4, with the two factors in the other order; the middle term M(B₁) M(B₂) of the printed chain is
  Theorem 1.1 (ii), thm2_1_1_ii, for B₂ after z ↦ -z)
* Formula (2.7) (§2.2) — `eq2_2_7`
* Formula (2.8) (§2.2) — exists: `LiZhongQC.eq5_21` (the same equation μ(1/√2) = π/2)
* Formula (2.9) (§2.2) — omitted: a consequence of (2.5) and (2.7) that is not cited again in the book
* Unlabelled (§2.2, P1:1802): `μ` is continuous in `0 < r < 1` — exists: `LiZhongQC.s15_grotzschMu_continuousOn`
  (continuity on the open unit interval)
* Formula (2.10) (§2.3) — `eq2_2_10`
* Formula (2.11) (§2.3) — exists: `LiZhongQC.w15_a_tendsto_g` (the limit is taken as r tends to 0 from the right, μ
  being defined on the open unit interval; for r > 0, μ(r) - log(4/r) = (μ(r) + log r) - log 4, so the limit of
  μ(r) - log(4/r) is 0 exactly when μ(r) + log r tends to log 4, which is the project's statement)
* Formula (2.12) and the limiting relation `μ(r) = lim 2⁻ⁿ log(4/rₙ)` (§2.4) — `eq2_2_12`, `eq2_2_12_tendsto`
* Formula (2.13) (§2.4) — `eq2_2_13`
* Formula (2.14) (§2.4) — `eq2_2_14`
* Unlabelled (§2.4, P1:1872): `μ` has the limit `μ(1) = 0` as `r → 1` — `grotzschMu_tendsto_one`

The elliptic-integral mapping of `Q(∞, 0, r, 1/r)` onto the rectangle
`R(0, K(√(1 - r²)), K(√(1 - r²)) + iK(r), iK(r))` (P1:1726–1732) is a step towards (2.2) and is not stated; nor are
the steps of the derivations in §2.3–2.4 (the ellipse comparison, `rₙ → 0`, the case `n = 1` of (2.12)), nor the
explicit map through the Koebe function (P1:1752, a proof step). The claim of
§2.2 on the modules of the half-plane quadrilaterals `Q(∞, -r₁, 0, 1)` and `Q(-r₁, 0, 1, ∞)` (P1:1777–1779, used at
P1:2083, 2403 and cited "by 2.2 and 6.3" at P1:3171) is stated in §6.3 as `module_upperHalf_infty`.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve IsMobius grotzschMu)
open References (IsDomainExt IsJordanDomainExt finitePart)

/-! ## §2.1 Representation by means of elliptic integrals -/

/-- **Formula (2.1)** (Ch. II §2.1). For `0 < r < 1`, `μ(r) = (π/2) M(Q)`, where `Q = Q(∞, 0, r, 1/r)` is the
quadrilateral consisting of the upper half-plane with the vertices `∞, 0, r, 1/r`.
Modelling: stated for every quadrilateral `Q` with this domain and these vertices (they are in the positive order
with respect to the upper half-plane, so such a `Q` exists). -/
theorem eq2_2_1 {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) (Q : Quadrilateral)
    (hQ : Q.dom = toExt LiZhongQC.upperHalf)
    (hv : Q.vert = ![extInf, ((0 : ℂ) : ExtPlane), ((r : ℂ) : ExtPlane), (((1 / r : ℝ) : ℂ) : ExtPlane)]) :
    grotzschMu r = Real.pi / 2 * Q.module := by
  have hr2 : 0 < r ^ 2 := pow_pos hr₀ 2
  have hr1r : r < 1 / r := by
    rw [lt_div_iff₀ hr₀]
    nlinarith
  have hM := lv21_quadModulusOf_upperHalf_infty (x₁ := 0) hr₀ hr1r
  rw [Complex.ofReal_zero] at hM
  have hρ : 0 < (1 / r - r) / (r - 0) := div_pos (by linarith) (by linarith)
  rw [LiZhongQC.eq5_18 hρ] at hM
  have e : 1 / (1 + (1 / r - r) / (r - 0)) = r ^ 2 := by
    rw [sub_zero]
    field_simp
    ring
  rw [e, Real.sqrt_sq hr₀.le] at hM
  rw [Quadrilateral.module, hQ, hv,
    lv12_quadModule_toExt LiZhongQC.isOpen_upperHalf LiZhongQC.isConnected_upperHalf, hM]
  field_simp

/-- **Definition** (Legendre normal integral, Ch. II §2.1).
`K(r) = ∫₀¹ dx / √((1 - x²)(1 - r²x²))`, `0 < r < 1`.
Modelling: an interval integral; the integrand is integrable for `0 ≤ r < 1` (it is `O((1 - x)^{-1/2})` at `x = 1`).
Junk: `0` at `|r| = 1` (not integrable); for `|r| > 1` the value is `K(1/|r|)/|r|`, the integrand being `0` where the
radicand is negative; never used. -/
def legendreK (r : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, 1 / Real.sqrt ((1 - x ^ 2) * (1 - r ^ 2 * x ^ 2))

/-- **Formula (2.2)** (Ch. II §2.1). For `0 < r < 1`, `μ(r) = (π/2) K(√(1 - r²)) / K(r)`.
Modelling: multiplied out, `μ(r) K(r) = (π/2) K(√(1 - r²))` (`K(r) > 0`). -/
theorem eq2_2_2 {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    grotzschMu r * legendreK r = Real.pi / 2 * legendreK (Real.sqrt (1 - r ^ 2)) := by
  have hs2 : 0 < 1 - r ^ 2 := by nlinarith
  have hσ₀ : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.2 hs2
  have hσ₁ : Real.sqrt (1 - r ^ 2) < 1 := by
    rw [Real.sqrt_lt' one_pos]
    nlinarith
  have hK : ∀ c : ℝ, 0 < c → c < 1 → legendreK c = LiZhongQC.scSideB c / 2 := fun c h0 h1 => by
    rw [LiZhongQC.e57K_sideB_eq_two_mul h0 h1, legendreK]
    ring
  have hb := (LiZhongQC.scSide_pos hr₀ hr₁).2
  rw [LiZhongQC.gm_grotzschMu_eq hr₀ hr₁, LiZhongQC.e57_sideA_eq hr₀ hr₁, hK r hr₀ hr₁, hK _ hσ₀ hσ₁]
  field_simp

/-! ## §2.2 Functional equations -/

/-- **Formula (2.3)** (Ch. II §2.2). For `0 < r < 1`, `μ(r) = 2μ(2√r / (1 + r))`. -/
theorem eq2_2_3 {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    grotzschMu r = 2 * grotzschMu (2 * Real.sqrt r / (1 + r)) := by
  have hu₀ : 0 < (1 - r) / (1 + r) := div_pos (by linarith) (by linarith)
  have hu₁ : (1 - r) / (1 + r) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have h := LiZhongQC.em_mu_landen hu₀ hu₁
  have e1 : (1 - (1 - r) / (1 + r)) / (1 + (1 - r) / (1 + r)) = r := by
    have h1r : (1 + r) ≠ 0 := by linarith
    field_simp
    ring
  rw [e1, (LiZhongQC.e57_landen_param hr₀ hr₁).2] at h
  exact h

/-- **Formula (2.4)** (Ch. II §2.2). For `0 < r < 1`, `μ(r) = ½ μ(((1 - √(1 - r²))/r)²)`. -/
theorem eq2_2_4 {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    grotzschMu r = grotzschMu (((1 - Real.sqrt (1 - r ^ 2)) / r) ^ 2) / 2 := by
  have hs2 : 0 < 1 - r ^ 2 := by nlinarith
  set σ := Real.sqrt (1 - r ^ 2) with hσ
  have hσ₀ : 0 < σ := Real.sqrt_pos.2 hs2
  have hσsq : σ ^ 2 = 1 - r ^ 2 := Real.sq_sqrt hs2.le
  have hσ₁ : σ < 1 := by nlinarith
  have h := LiZhongQC.em_mu_landen hσ₀ hσ₁
  have e1 : Real.sqrt (1 - σ ^ 2) = r := by
    rw [hσsq, sub_sub_cancel, Real.sqrt_sq hr₀.le]
  have e2 : ((1 - σ) / r) ^ 2 = (1 - σ) / (1 + σ) := by
    rw [div_pow, div_eq_div_iff (pow_pos hr₀ 2).ne' (by linarith : (0 : ℝ) < 1 + σ).ne']
    have hr2 : r ^ 2 = 1 - σ ^ 2 := by linarith
    rw [hr2]
    ring
  rw [e2, h, e1]
  ring

/-- **Formula (2.7)** (Ch. II §2.2). For `0 < r < 1`, `μ(r) μ(√(1 - r²)) = π²/4`. -/
theorem eq2_2_7 {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    grotzschMu r * grotzschMu (Real.sqrt (1 - r ^ 2)) = Real.pi ^ 2 / 4 := by
  have hr2 : 0 < r ^ 2 := pow_pos hr₀ 2
  have hρ : 0 < (1 - r ^ 2) / r ^ 2 := div_pos (by nlinarith) hr2
  have h := LiZhongQC.eq5_19 hρ
  have e0 : 1 + (1 - r ^ 2) / r ^ 2 = 1 / r ^ 2 := by
    rw [eq_div_iff hr2.ne', add_mul, div_mul_cancel₀ _ hr2.ne']
    ring
  have e1 : 1 / (1 + (1 - r ^ 2) / r ^ 2) = r ^ 2 := by
    rw [e0, one_div_one_div]
  have e2 : (1 - r ^ 2) / r ^ 2 / (1 + (1 - r ^ 2) / r ^ 2) = 1 - r ^ 2 := by
    rw [e0]
    field_simp
  rw [e1, e2, Real.sqrt_sq hr₀.le] at h
  exact h

/-! ## §2.3 Asymptotic behaviour -/

/-- Landen step of §2.4 (from `rₙ` to `rₙ₊₁`): for `0 < t < 1`, `σ = √(1 - t²)` and `t' = ((1 - σ)/t)²`,
`0 < t' < t`, `½ log (4/t') = log (2(1 + σ)/t)` and `½ log ((1 + √(1 - t'²))²/t') = log ((1 + √σ)²/t)`. -/
theorem lv22_step {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) :
    0 < ((1 - Real.sqrt (1 - t ^ 2)) / t) ^ 2 ∧ ((1 - Real.sqrt (1 - t ^ 2)) / t) ^ 2 < t ∧
      Real.log (4 / ((1 - Real.sqrt (1 - t ^ 2)) / t) ^ 2) / 2 =
        Real.log (2 * (1 + Real.sqrt (1 - t ^ 2)) / t) ∧
      Real.log ((1 + Real.sqrt (1 - (((1 - Real.sqrt (1 - t ^ 2)) / t) ^ 2) ^ 2)) ^ 2 /
          ((1 - Real.sqrt (1 - t ^ 2)) / t) ^ 2) / 2 =
        Real.log ((1 + Real.sqrt (Real.sqrt (1 - t ^ 2))) ^ 2 / t) := by
  have ht2 : 0 < 1 - t ^ 2 := by nlinarith
  set σ := Real.sqrt (1 - t ^ 2) with hσ
  have hσ₀ : 0 < σ := Real.sqrt_pos.2 ht2
  have hσsq : σ ^ 2 = 1 - t ^ 2 := Real.sq_sqrt ht2.le
  have hσ₁ : σ < 1 := by nlinarith
  have htt : t ^ 2 = (1 - σ) * (1 + σ) := by
    rw [show (1 - σ) * (1 + σ) = 1 - σ ^ 2 by ring, hσsq]
    ring
  have e1 : ((1 - σ) / t) ^ 2 = (1 - σ) / (1 + σ) := by
    rw [div_pow, div_eq_div_iff (pow_pos ht₀ 2).ne' (by linarith : (0 : ℝ) < 1 + σ).ne', htt]
    ring
  rw [e1, (LiZhongQC.e57_landen_param hσ₀ hσ₁).2]
  refine ⟨div_pos (by linarith) (by linarith), ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ (by linarith)]
    nlinarith [mul_pos (sub_pos.2 hσ₁) hσ₀, mul_pos ht₀ (sub_pos.2 ht₁), mul_pos ht₀ hσ₀]
  · have e : 4 / ((1 - σ) / (1 + σ)) = (2 * (1 + σ) / t) ^ 2 := by
      rw [div_div_eq_mul_div, div_pow,
        div_eq_div_iff (by linarith : (0 : ℝ) < 1 - σ).ne' (pow_pos ht₀ 2).ne', htt]
      ring
    rw [e, Real.log_pow]
    push_cast
    ring
  · set q := Real.sqrt σ with hq
    have hq₀ : 0 < q := Real.sqrt_pos.2 hσ₀
    have hqsq : q ^ 2 = σ := Real.sq_sqrt hσ₀.le
    have e : (1 + 2 * q / (1 + σ)) ^ 2 / ((1 - σ) / (1 + σ)) = ((1 + q) ^ 2 / t) ^ 2 := by
      rw [div_pow ((1 + q) ^ 2) t 2, htt, ← hqsq]
      have h1 : (1 - q ^ 2) ≠ 0 := by
        rw [hqsq]
        exact (sub_pos.2 hσ₁).ne'
      have h2 : (1 + q ^ 2) ≠ 0 := by positivity
      field_simp
      ring
    rw [e, Real.log_pow]
    push_cast
    ring

/-- The sequence `rₙ` of §2.4: `0 < rₙ ≤ r` and `μ(rₙ) = 2ⁿ μ(r)` (by (2.4)). -/
theorem lv22_seq {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {s : ℕ → ℝ} (hs₀ : s 0 = r)
    (hs : ∀ n, s (n + 1) = ((1 - Real.sqrt (1 - s n ^ 2)) / s n) ^ 2) (n : ℕ) :
    0 < s n ∧ s n ≤ r ∧ grotzschMu (s n) = 2 ^ n * grotzschMu r := by
  induction n with
  | zero => exact ⟨by rw [hs₀]; exact hr₀, hs₀.le, by rw [hs₀, pow_zero, one_mul]⟩
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have hn₁ : s n < 1 := lt_of_le_of_lt h1 hr₁
    obtain ⟨hp, hlt, -, -⟩ := lv22_step h0 hn₁
    have h4 := eq2_2_4 h0 hn₁
    rw [hs n]
    refine ⟨hp, by linarith, ?_⟩
    rw [pow_succ (2 : ℝ) n]
    linear_combination (-2) * h4 + 2 * h2

/-- Upper half of (2.12) in the non-strict form: `2ⁿ μ(r) = μ(rₙ) ≤ log (4/rₙ)` (`LiZhongQC.em_upper`). -/
theorem lv22_le_upper {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {s : ℕ → ℝ} (hs₀ : s 0 = r)
    (hs : ∀ n, s (n + 1) = ((1 - Real.sqrt (1 - s n ^ 2)) / s n) ^ 2) (n : ℕ) :
    grotzschMu r ≤ Real.log (4 / s n) / 2 ^ n := by
  obtain ⟨h0, h1, h2⟩ := lv22_seq hr₀ hr₁ hs₀ hs n
  have h := LiZhongQC.em_upper h0 (lt_of_le_of_lt h1 hr₁)
  rw [h2] at h
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- The other side, from `LiZhongQC.em_lower`: `log (4/rₙ) ≤ 2ⁿ μ(r) - log √(1 - r²)`. -/
theorem lv22_upper_le {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {s : ℕ → ℝ} (hs₀ : s 0 = r)
    (hs : ∀ n, s (n + 1) = ((1 - Real.sqrt (1 - s n ^ 2)) / s n) ^ 2) (n : ℕ) :
    Real.log (4 / s n) ≤ 2 ^ n * grotzschMu r - Real.log (Real.sqrt (1 - r ^ 2)) := by
  obtain ⟨h0, h1, h2⟩ := lv22_seq hr₀ hr₁ hs₀ hs n
  have hn₁ : s n < 1 := lt_of_le_of_lt h1 hr₁
  have h := LiZhongQC.em_lower h0 hn₁
  have hσn : 0 < 1 - s n ^ 2 := by nlinarith
  have hσr : 0 < 1 - r ^ 2 := by nlinarith
  have hmono : Real.log (Real.sqrt (1 - r ^ 2)) ≤ Real.log (Real.sqrt (1 - s n ^ 2)) :=
    Real.log_le_log (Real.sqrt_pos.2 hσr) (Real.sqrt_le_sqrt (by nlinarith))
  have hsplit : Real.log (4 * Real.sqrt (1 - s n ^ 2) / s n) =
      Real.log (4 / s n) + Real.log (Real.sqrt (1 - s n ^ 2)) := by
    rw [mul_div_right_comm, Real.log_mul (by positivity) (Real.sqrt_pos.2 hσn).ne']
  rw [hsplit, h2] at h
  linarith

/-- The limiting relation of §2.4: `2⁻ⁿ log (4/rₙ) → μ(r)`. -/
theorem lv22_tendsto {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {s : ℕ → ℝ} (hs₀ : s 0 = r)
    (hs : ∀ n, s (n + 1) = ((1 - Real.sqrt (1 - s n ^ 2)) / s n) ^ 2) :
    Tendsto (fun n : ℕ => Real.log (4 / s n) / 2 ^ n) atTop (𝓝 (grotzschMu r)) := by
  have hup : Tendsto (fun n : ℕ => grotzschMu r + -Real.log (Real.sqrt (1 - r ^ 2)) / 2 ^ n) atTop
      (𝓝 (grotzschMu r)) := by
    have := (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => -Real.log (Real.sqrt (1 - r ^ 2))) atTop
          (𝓝 (-Real.log (Real.sqrt (1 - r ^ 2))))).div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : (1 : ℝ) < 2))
    simpa using this.const_add (grotzschMu r)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => lv22_le_upper hr₀ hr₁ hs₀ hs n) (fun n => ?_)
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have e : grotzschMu r + -Real.log (Real.sqrt (1 - r ^ 2)) / 2 ^ n =
      (2 ^ n * grotzschMu r + -Real.log (Real.sqrt (1 - r ^ 2))) / 2 ^ n := by
    rw [add_div, mul_div_cancel_left₀ _ h2n.ne']
  show Real.log (4 / s n) / 2 ^ n ≤ grotzschMu r + -Real.log (Real.sqrt (1 - r ^ 2)) / 2 ^ n
  rw [e]
  exact (div_le_div_iff_of_pos_right h2n).2 (by linarith [lv22_upper_le hr₀ hr₁ hs₀ hs n])

/-- One step of (2.12): the upper bounds decrease strictly and the lower bounds increase strictly. -/
theorem lv22_succ {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {s : ℕ → ℝ} (hs₀ : s 0 = r)
    (hs : ∀ n, s (n + 1) = ((1 - Real.sqrt (1 - s n ^ 2)) / s n) ^ 2) (n : ℕ) :
    Real.log (4 / s (n + 1)) / 2 ^ (n + 1) < Real.log (4 / s n) / 2 ^ n ∧
      Real.log ((1 + Real.sqrt (1 - s n ^ 2)) ^ 2 / s n) / 2 ^ n <
        Real.log ((1 + Real.sqrt (1 - s (n + 1) ^ 2)) ^ 2 / s (n + 1)) / 2 ^ (n + 1) := by
  obtain ⟨h0, h1, -⟩ := lv22_seq hr₀ hr₁ hs₀ hs n
  have hn₁ : s n < 1 := lt_of_le_of_lt h1 hr₁
  obtain ⟨-, -, e3, e4⟩ := lv22_step h0 hn₁
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hσn : 0 < 1 - s n ^ 2 := by nlinarith
  have hσ₀ : 0 < Real.sqrt (1 - s n ^ 2) := Real.sqrt_pos.2 hσn
  have hσ₁ : Real.sqrt (1 - s n ^ 2) < 1 := by
    rw [Real.sqrt_lt' one_pos]
    nlinarith
  rw [hs n, pow_succ' (2 : ℝ) n, ← div_div, ← div_div, e3, e4]
  constructor
  · refine div_lt_div_of_pos_right (Real.log_lt_log (by positivity) ?_) h2n
    exact div_lt_div_of_pos_right (by linarith) h0
  · refine div_lt_div_of_pos_right (Real.log_lt_log (by positivity) ?_) h2n
    refine div_lt_div_of_pos_right ?_ h0
    have hq : Real.sqrt (1 - s n ^ 2) < Real.sqrt (Real.sqrt (1 - s n ^ 2)) :=
      (Real.lt_sqrt hσ₀.le).2 (by nlinarith)
    exact pow_lt_pow_left₀ (by linarith) (by positivity) two_ne_zero

/-- The two bounds of (2.12) are ordered: `(1 + √(1 - rₙ²))² ≤ 4`. -/
theorem lv22_lower_le_upper {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {s : ℕ → ℝ} (hs₀ : s 0 = r)
    (hs : ∀ n, s (n + 1) = ((1 - Real.sqrt (1 - s n ^ 2)) / s n) ^ 2) (n : ℕ) :
    Real.log ((1 + Real.sqrt (1 - s n ^ 2)) ^ 2 / s n) / 2 ^ n ≤ Real.log (4 / s n) / 2 ^ n := by
  obtain ⟨h0, h1, -⟩ := lv22_seq hr₀ hr₁ hs₀ hs n
  have hn₁ : s n < 1 := lt_of_le_of_lt h1 hr₁
  have hσn : 0 < 1 - s n ^ 2 := by nlinarith
  have hσ₁ : Real.sqrt (1 - s n ^ 2) < 1 := by
    rw [Real.sqrt_lt' one_pos]
    nlinarith
  have hσ₀ := Real.sqrt_nonneg (1 - s n ^ 2)
  refine (div_le_div_iff_of_pos_right (by positivity)).2 (Real.log_le_log (by positivity) ?_)
  exact (div_le_div_iff_of_pos_right h0).2 (by nlinarith)

/-- (2.12) for every sequence `rₙ` of §2.4 (the content of `eq2_2_12`, used here for `n = 0` and `n = 1`). -/
theorem lv22_bounds {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {s : ℕ → ℝ} (hs₀ : s 0 = r)
    (hs : ∀ n, s (n + 1) = ((1 - Real.sqrt (1 - s n ^ 2)) / s n) ^ 2) (n : ℕ) :
    Real.log ((1 + Real.sqrt (1 - s n ^ 2)) ^ 2 / s n) / 2 ^ n < grotzschMu r ∧
      grotzschMu r < Real.log (4 / s n) / 2 ^ n := by
  have ha : StrictMono fun n : ℕ => Real.log ((1 + Real.sqrt (1 - s n ^ 2)) ^ 2 / s n) / 2 ^ n :=
    strictMono_nat_of_lt_succ fun n => (lv22_succ hr₀ hr₁ hs₀ hs n).2
  have hle : ∀ m, Real.log ((1 + Real.sqrt (1 - s m ^ 2)) ^ 2 / s m) / 2 ^ m ≤ grotzschMu r := by
    intro m
    refine ge_of_tendsto (lv22_tendsto hr₀ hr₁ hs₀ hs) (eventually_atTop.2 ⟨m, fun k hk => ?_⟩)
    exact (ha.monotone hk).trans (lv22_lower_le_upper hr₀ hr₁ hs₀ hs k)
  exact ⟨(ha (Nat.lt_succ_self n)).trans_le (hle (n + 1)),
    (lv22_le_upper hr₀ hr₁ hs₀ hs (n + 1)).trans_lt (lv22_succ hr₀ hr₁ hs₀ hs n).1⟩

/-- The sequence `rₙ` of §2.4, as an iterate. -/
theorem lv22_iterate (r : ℝ) (n : ℕ) :
    (fun t : ℝ => ((1 - Real.sqrt (1 - t ^ 2)) / t) ^ 2)^[n + 1] r =
      ((1 - Real.sqrt (1 - ((fun t : ℝ => ((1 - Real.sqrt (1 - t ^ 2)) / t) ^ 2)^[n] r) ^ 2)) /
        (fun t : ℝ => ((1 - Real.sqrt (1 - t ^ 2)) / t) ^ 2)^[n] r) ^ 2 :=
  Function.iterate_succ_apply' _ n r

/-- **Formula (2.10)** (Ch. II §2.3). For `0 < r < 1`, `log ((1 + √(1 - r²))² / r) < μ(r) < log (4/r)`. -/
theorem eq2_2_10 {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    Real.log ((1 + Real.sqrt (1 - r ^ 2)) ^ 2 / r) < grotzschMu r ∧ grotzschMu r < Real.log (4 / r) := by
  have h := lv22_bounds hr₀ hr₁ (s := fun n => (fun t : ℝ => ((1 - Real.sqrt (1 - t ^ 2)) / t) ^ 2)^[n] r)
    rfl (lv22_iterate r) 0
  simpa only [Function.iterate_zero, id, pow_zero, div_one] using h

/-! ## §2.4 Successive approximations -/

/-- **Formula (2.12)** (Ch. II §2.4). Let `0 < r < 1`, `r₀ = r` and `rₙ₊₁ = ((1 - √(1 - rₙ²))/rₙ)²`. Then for
every `n`, `2⁻ⁿ log ((1 + √(1 - rₙ²))² / rₙ) < μ(r) < 2⁻ⁿ log (4/rₙ)`.
Modelling: for every sequence `s` with `s 0 = r` and this recursion; all `sₙ` lie in `(0, 1)`. -/
theorem eq2_2_12 {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {s : ℕ → ℝ} (hs₀ : s 0 = r)
    (hs : ∀ n, s (n + 1) = ((1 - Real.sqrt (1 - s n ^ 2)) / s n) ^ 2) (n : ℕ) :
    Real.log ((1 + Real.sqrt (1 - s n ^ 2)) ^ 2 / s n) / 2 ^ n < grotzschMu r ∧
      grotzschMu r < Real.log (4 / s n) / 2 ^ n := by
  exact lv22_bounds hr₀ hr₁ hs₀ hs n

/-- **Formula (2.12), limiting relation** (Ch. II §2.4). With `rₙ` as in (2.12), `μ(r) = lim_{n → ∞} 2⁻ⁿ log (4/rₙ)`.
-/
theorem eq2_2_12_tendsto {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {s : ℕ → ℝ} (hs₀ : s 0 = r)
    (hs : ∀ n, s (n + 1) = ((1 - Real.sqrt (1 - s n ^ 2)) / s n) ^ 2) :
    Tendsto (fun n : ℕ => Real.log (4 / s n) / 2 ^ n) atTop (𝓝 (grotzschMu r)) := by
  exact lv22_tendsto hr₀ hr₁ hs₀ hs

/-- The case `n = 1` of (2.12) (§2.4), exponentiated:
`(1 + ⁴√(1 - r²))²/r < e^{μ(r)} < 2(1 + √(1 - r²))/r`. -/
theorem lv22_exp_bounds {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    (1 + Real.sqrt (Real.sqrt (1 - r ^ 2))) ^ 2 / r < Real.exp (grotzschMu r) ∧
      Real.exp (grotzschMu r) < 2 * (1 + Real.sqrt (1 - r ^ 2)) / r := by
  have h := lv22_bounds hr₀ hr₁ (s := fun n => (fun t : ℝ => ((1 - Real.sqrt (1 - t ^ 2)) / t) ^ 2)^[n] r)
    rfl (lv22_iterate r) 1
  simp only [lv22_iterate r 0, Function.iterate_zero, id, pow_one] at h
  obtain ⟨-, -, e3, e4⟩ := lv22_step hr₀ hr₁
  rw [e3, e4] at h
  have hs2 : 0 < 1 - r ^ 2 := by nlinarith
  have hσ₀ := Real.sqrt_nonneg (1 - r ^ 2)
  exact ⟨(Real.log_lt_iff_lt_exp (by positivity)).1 h.1, (Real.lt_log_iff_exp_lt (by positivity)).1 h.2⟩

/-- Elementary facts on `σ = √(1 - r²)` and `q = √σ = ⁴√(1 - r²)` used in (2.13) and (2.14). -/
theorem lv22_facts {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    ∃ σ q : ℝ, 0 < σ ∧ σ < 1 ∧ σ ^ 2 = 1 - r ^ 2 ∧ 0 < q ∧ q < 1 ∧ q ^ 2 = σ ∧ 1 - σ < r ^ 2 ∧
      1 - q < 1 - σ ∧ Real.sqrt (1 - r ^ 2) = σ ∧ Real.sqrt (Real.sqrt (1 - r ^ 2)) = q := by
  have hs2 : 0 < 1 - r ^ 2 := by nlinarith
  have hσ₀ : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.2 hs2
  have hσsq : Real.sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 := Real.sq_sqrt hs2.le
  have hσ₁ : Real.sqrt (1 - r ^ 2) < 1 := by nlinarith
  have hq₀ : 0 < Real.sqrt (Real.sqrt (1 - r ^ 2)) := Real.sqrt_pos.2 hσ₀
  have hqsq : Real.sqrt (Real.sqrt (1 - r ^ 2)) ^ 2 = Real.sqrt (1 - r ^ 2) := Real.sq_sqrt hσ₀.le
  have hq₁ : Real.sqrt (Real.sqrt (1 - r ^ 2)) < 1 := by nlinarith
  refine ⟨_, _, hσ₀, hσ₁, hσsq, hq₀, hq₁, hqsq, ?_, ?_, rfl, rfl⟩
  · nlinarith [mul_pos (sub_pos.2 hσ₁) hσ₀]
  · nlinarith [mul_pos hq₀ (sub_pos.2 hq₁)]

/-- **Formula (2.13)** (Ch. II §2.4). For `0 < r < 1`, `μ(r) = log (2(1 + √(1 - r²))/r - δ(r))` with
`0 < δ(r) < r³`.
Modelling: `δ(r)` is determined by the equation, `δ(r) = 2(1 + √(1 - r²))/r - e^{μ(r)}`, and the statement is
`0 < δ(r) < r³` for this value (equivalent, and no logarithm of a nonpositive number occurs). -/
theorem eq2_2_13 {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    0 < 2 * (1 + Real.sqrt (1 - r ^ 2)) / r - Real.exp (grotzschMu r) ∧
      2 * (1 + Real.sqrt (1 - r ^ 2)) / r - Real.exp (grotzschMu r) < r ^ 3 := by
  obtain ⟨h1, h2⟩ := lv22_exp_bounds hr₀ hr₁
  obtain ⟨σ, q, hσ₀, hσ₁, hσsq, hq₀, hq₁, hqsq, hA, hB, hσd, hqd⟩ := lv22_facts hr₀ hr₁
  rw [hqd] at h1
  rw [hσd] at h2 ⊢
  refine ⟨by linarith, ?_⟩
  have key : 2 * (1 + σ) / r - (1 + q) ^ 2 / r < r ^ 3 := by
    rw [← sub_div, div_lt_iff₀ hr₀]
    have : (1 - q) ^ 2 < (r ^ 2) ^ 2 := pow_lt_pow_left₀ (by linarith) (by linarith) two_ne_zero
    nlinarith
  linarith

/-- **Formula (2.14)** (Ch. II §2.4). For `0 < r < 1`, `μ(r) = log (4/r - r - δ₁(r))` with `r³/4 < δ₁(r) < 2r³`.
Modelling: as in (2.13), `δ₁(r) = 4/r - r - e^{μ(r)}`. -/
theorem eq2_2_14 {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    r ^ 3 / 4 < 4 / r - r - Real.exp (grotzschMu r) ∧ 4 / r - r - Real.exp (grotzschMu r) < 2 * r ^ 3 := by
  obtain ⟨h1, h2⟩ := lv22_exp_bounds hr₀ hr₁
  obtain ⟨σ, q, hσ₀, hσ₁, hσsq, hq₀, hq₁, hqsq, hA, hB, hσd, hqd⟩ := lv22_facts hr₀ hr₁
  rw [hqd] at h1
  rw [hσd] at h2
  set E := Real.exp (grotzschMu r)
  have h1' : (1 + q) ^ 2 < E * r := (div_lt_iff₀ hr₀).1 h1
  have h2' : E * r < 2 * (1 + σ) := (lt_div_iff₀ hr₀).1 h2
  have hmul : (4 / r - r - E) * r = 4 - r * r - E * r := by
    simp only [sub_mul, div_mul_cancel₀ _ hr₀.ne']
  have hr4 : r ^ 4 = ((1 - σ) * (1 + σ)) ^ 2 := by
    rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, show (1 - σ) * (1 + σ) = 1 - σ ^ 2 by ring, hσsq]
    ring
  have hσ4 : (1 - σ) ^ 2 < (r ^ 2) ^ 2 := pow_lt_pow_left₀ hA (by linarith) two_ne_zero
  have hq4 : (1 - q) ^ 2 < (r ^ 2) ^ 2 := pow_lt_pow_left₀ (by linarith) (by linarith) two_ne_zero
  constructor
  · refine lt_of_mul_lt_mul_right ?_ hr₀.le
    rw [hmul]
    nlinarith [mul_pos (pow_pos (sub_pos.2 hσ₁) 2) (by nlinarith : (0 : ℝ) < 4 - (1 + σ) ^ 2)]
  · refine lt_of_mul_lt_mul_right ?_ hr₀.le
    rw [hmul]
    nlinarith

/-- From (2.10): `-log t < μ(t)` for `0 < t < 1`, since `(1 + √(1 - t²))² ≥ 1`. -/
theorem lv22_neg_log_lt {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) : -Real.log t < grotzschMu t := by
  have h := (eq2_2_10 ht₀ ht₁).1
  have hσ := Real.sqrt_nonneg (1 - t ^ 2)
  have : -Real.log t ≤ Real.log ((1 + Real.sqrt (1 - t ^ 2)) ^ 2 / t) := by
    rw [← Real.log_inv, inv_eq_one_div]
    exact Real.log_le_log (by positivity) ((div_le_div_iff_of_pos_right ht₀).2 (by nlinarith))
  linarith

/-- **Unlabelled** (Ch. II §2.4, P1:1872). `μ` has the limit `μ(1) = 0`: `μ(r) → 0` as `r` increases to `1`. -/
theorem grotzschMu_tendsto_one : Tendsto grotzschMu (𝓝[<] 1) (𝓝 0) := by
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), r ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  have hσ : Tendsto (fun r : ℝ => Real.sqrt (1 - r ^ 2)) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hev.mono fun r hr => ?_⟩
    · have hc : Continuous fun r : ℝ => Real.sqrt (1 - r ^ 2) :=
        (continuous_const.sub (continuous_pow 2)).sqrt
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    · exact Real.sqrt_pos.2 (by nlinarith [hr.1, hr.2])
  have hlog : Tendsto (fun r : ℝ => -Real.log (Real.sqrt (1 - r ^ 2))) (𝓝[<] 1) atTop :=
    tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hσ)
  have hup : Tendsto (fun r : ℝ => Real.pi ^ 2 / 4 / -Real.log (Real.sqrt (1 - r ^ 2))) (𝓝[<] 1) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hpos : ∀ r ∈ Ioo (0 : ℝ) 1, 0 ≤ grotzschMu r := fun r hr => by
    have := lv22_neg_log_lt hr.1 hr.2
    have : 0 < -Real.log r := neg_pos.2 (Real.log_neg hr.1 hr.2)
    linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [hev] with r hr
    exact hpos r hr
  · filter_upwards [hev] with r hr
    have hs2 : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
    have hσ₀ : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.2 hs2
    have hσ₁ : Real.sqrt (1 - r ^ 2) < 1 := by
      rw [Real.sqrt_lt' one_pos]
      nlinarith [hr.1]
    have hL : 0 < -Real.log (Real.sqrt (1 - r ^ 2)) := neg_pos.2 (Real.log_neg hσ₀ hσ₁)
    have hm := lv22_neg_log_lt hσ₀ hσ₁
    rw [le_div_iff₀ hL, ← eq2_2_7 hr.1 hr.2]
    exact mul_le_mul_of_nonneg_left hm.le (hpos r hr)

end LehtoVirtanen1973
