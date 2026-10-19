import References.LehtoVirtanen1973.Ch02.S06_BoundaryValues

/-!
# Lehto–Virtanen, Chapter II §7: Quasisymmetric functions

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. II §7
(pp. 88–96; `full.md` P1:2670–2889).

The functions of this section are finite real functions `φ : ℝ → ℝ` on intervals `I` of the finite `x`-axis (an
order-connected set of reals, bounded or unbounded); "on the real axis" is `I = univ`. The double inequality (7.1)
is multiplied out: `φ` being strictly increasing, both differences in its quotient are positive. The upper and lower
half-planes are `H₁ = toExt LiZhongQC.upperHalf` and `H₂ = toExt LiZhongQC.lowerHalf`; boundary values on the real
axis are those of II.6 (`HasRealBoundaryValues`), resp. of the homeomorphic extension to the closed half-plane
(I.2.2).

* Definition (`k`-quasisymmetric and quasisymmetric function on an interval, §7.1, footnote 23) —
  `IsKQuasisymmetricOn`, `IsQuasisymmetricOn`
* Unlabelled (§7.1, P1:2680): a finite real function is quasisymmetric on the real axis if and only if it is the
  boundary function of a quasiconformal self-mapping of the upper half-plane — `quasisymmetric_iff_qcBoundaryValues`
* Unlabelled (§7.1, P1:2680): inverses and compositions of functions quasisymmetric on the real axis are
  quasisymmetric — `quasisymmetric_inv`, `quasisymmetric_comp`
* Unlabelled (§7.1, P1:2706, Remark): (7.1) for small and for large `t` gives quasisymmetry on the whole axis —
  `kQuasisymmetric_of_local_and_large`
* Lemma 7.1 (§7.2) — `lemma2_7_1`
* Formula (7.8) (§7.3) — `eq2_7_8`
* Formula (7.9) (§7.3) — `eq2_7_9`
* Formula (7.10) (§7.3) — `eq2_7_10`
* Definition (the Gauss integrals `φₙ` of a quasisymmetric function, §7.4) — `qsGaussApprox`
* Unlabelled (§7.4, P1:2798–2818): `φₙ` is an entire function (the integral converging uniformly in compact sets)
  with the properties 1°–3° — `qsGaussApprox_differentiable`, `qsGaussApprox_kQuasisymmetric`,
  `qsGaussApprox_deriv_pos`, `qsGaussApprox_tendstoUniformlyOn`
* Sewing theorem (§7.5, footnote 25) — `sewing_theorem`

Not stated (inventory U−: immediate, examples, or used only inside proofs): linear polynomials are the
`1`-quasisymmetric functions (P1:2682); invariance of `k`-quasisymmetry under linear changes of variable and value
(P1:2684, used in the proof of Lemma 7.1); the exponential function as an example (P1:2686); quasisymmetry on bounded
intervals from (7.1) for small `t` (P1:2688–2704, of which the cited form is the Remark; see its `[OCR?]` note); the
remarks P1:2760 and P1:2768 (U−, proof steps of the estimates (7.10) and (7.13));
footnote 24 (a quasisymmetric function need not be absolutely continuous); the proof steps (7.2)–(7.7), (7.11).
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve IsMobius upperHalf lowerHalf)
open References (IsDomainExt IsJordanDomainExt finitePart)

/-! ## §7.1 Definition of a quasisymmetric function -/

/-- **Definition** (`k`-quasisymmetric function, Ch. II §7.1). Let `φ` be a continuous, strictly increasing function
on the bounded or unbounded interval `I` of the finite `x`-axis. `φ` is `k`-quasisymmetric on `I` (`k` a positive
constant) if `1/k ≤ (φ(x + t) - φ(x))/(φ(x) - φ(x - t)) ≤ k` (7.1) for `x, x - t, x + t ∈ I` and `t > 0`.
Modelling: the interval is an order-connected set of reals; (7.1) is multiplied out (both differences are
positive, `φ` being strictly increasing). -/
def IsKQuasisymmetricOn (φ : ℝ → ℝ) (I : Set ℝ) (k : ℝ) : Prop :=
  I.OrdConnected ∧ ContinuousOn φ I ∧ StrictMonoOn φ I ∧ 0 < k ∧
    ∀ x t : ℝ, 0 < t → x ∈ I → x - t ∈ I → x + t ∈ I →
      φ x - φ (x - t) ≤ k * (φ (x + t) - φ x) ∧ φ (x + t) - φ x ≤ k * (φ x - φ (x - t))

/-- **Definition** (quasisymmetric function, Ch. II §7.1; the term is due to Kelingos, footnote 23). `φ` is
quasisymmetric on `I` if it is `k`-quasisymmetric on `I` for some `k`. -/
def IsQuasisymmetricOn (φ : ℝ → ℝ) (I : Set ℝ) : Prop := ∃ k : ℝ, IsKQuasisymmetricOn φ I k

/-- **Unlabelled** (Ch. II §7.1, P1:2680). By Theorems 6.2 and 6.3 a finite real function `φ` is quasisymmetric on
the real axis if and only if there exists a quasiconformal mapping of the upper half-plane onto itself with the
boundary values `φ` (cited in the proof of Theorem 8.5 and in V.1).
Modelling: the boundary values are those of II.6.3 (`HasRealBoundaryValues`; the mapping preserves `∞`, as it must
when its boundary values on the real axis are finite). -/
theorem quasisymmetric_iff_qcBoundaryValues (φ : ℝ → ℝ) :
    IsQuasisymmetricOn φ univ ↔
      ∃ w : ExtPlane → ExtPlane, IsQuasiconformalMap w (toExt upperHalf) ∧
        w '' toExt upperHalf = toExt upperHalf ∧ HasRealBoundaryValues w φ := by
  constructor
  · -- Theorem 6.3 (Beurling–Ahlfors)
    rintro ⟨k, -, hc, hm, -, hq⟩
    obtain ⟨K₀, hK₀⟩ := thm2_6_3 k
    obtain ⟨w, hw, hwH, hbv⟩ := hK₀ φ (continuousOn_univ.1 hc) (strictMonoOn_univ.1 hm)
      fun x t ht => hq x t ht (mem_univ _) (mem_univ _) (mem_univ _)
    exact ⟨w, ⟨hw.1, hw.2.1, lt_of_le_of_lt hw.2.2 ENNReal.ofReal_lt_top⟩, hwH, hbv⟩
  · -- Theorem 6.2, through Li Zhong's Theorem 17.1
    rintro ⟨w, hw, hwH, hbv⟩
    have hkw : IsKQuasiconformal w (toExt LiZhongQC.upperHalf) (maxDilatationK w (toExt LiZhongQC.upperHalf)).toReal :=
      ⟨hw.1, hw.2.1, (ENNReal.ofReal_toReal hw.2.2.ne).ge⟩
    obtain ⟨hmono, hcont, -, -, hratio⟩ := LiZhongQC.thm17_1_quasisymmetric (lv26_hasQCExtensionH_of hkw hwH hbv)
    set ρ := LiZhongQC.lambdaInv (maxDilatationK w (toExt LiZhongQC.upperHalf)).toReal with hρ
    have hρ0 : 0 < ρ := by
      obtain ⟨-, hhi⟩ := hratio 0 1 one_pos
      have hd1 : 0 < φ 0 - φ (0 - 1) := sub_pos.2 (hmono (by norm_num))
      have hd2 : 0 < φ (0 + 1) - φ 0 := sub_pos.2 (hmono (by norm_num))
      rw [LiZhongQC.qsRatio] at hhi
      exact (div_pos hd2 hd1).trans_le hhi
    refine ⟨ρ, ordConnected_univ, hcont.continuousOn, hmono.strictMonoOn _, hρ0, fun x t ht _ _ _ => ?_⟩
    obtain ⟨hlo, hhi⟩ := hratio x t ht
    have hd1 : 0 < φ x - φ (x - t) := sub_pos.2 (hmono (by linarith))
    rw [LiZhongQC.qsRatio] at hlo hhi
    constructor
    · have h := (le_div_iff₀ hd1).1 hlo
      have h' := mul_le_mul_of_nonneg_left h hρ0.le
      rwa [← mul_assoc, mul_inv_cancel₀ hρ0.ne', one_mul] at h'
    · exact (div_le_iff₀ hd1).1 hhi

/-- (7.1) on the real axis without the membership hypotheses: `φ` is strictly increasing, and `1 ≤ k` (the two
halves `A ≤ kB`, `B ≤ kA` with `A, B > 0` force `k² ≥ 1`). -/
theorem lv27_qs {φ : ℝ → ℝ} {k : ℝ} (h : IsKQuasisymmetricOn φ univ k) :
    StrictMono φ ∧ 1 ≤ k ∧ ∀ x t : ℝ, 0 < t →
      φ x - φ (x - t) ≤ k * (φ (x + t) - φ x) ∧ φ (x + t) - φ x ≤ k * (φ x - φ (x - t)) := by
  obtain ⟨-, -, hm, hk, hq⟩ := h
  have hm' : StrictMono φ := strictMonoOn_univ.1 hm
  have hq' : ∀ x t : ℝ, 0 < t →
      φ x - φ (x - t) ≤ k * (φ (x + t) - φ x) ∧ φ (x + t) - φ x ≤ k * (φ x - φ (x - t)) :=
    fun x t ht => hq x t ht (mem_univ _) (mem_univ _) (mem_univ _)
  refine ⟨hm', ?_, hq'⟩
  obtain ⟨h1, h2⟩ := hq' 0 1 one_pos
  have hA : 0 < φ 0 - φ (0 - 1) := sub_pos.2 (hm' (by norm_num))
  have hB : 0 < φ (0 + 1) - φ 0 := sub_pos.2 (hm' (by norm_num))
  by_contra hk1
  have hk1' : k < 1 := not_le.1 hk1
  nlinarith [mul_le_mul_of_nonneg_left h2 hk.le, mul_pos (mul_pos (sub_pos.2 hk1') (by linarith : (0 : ℝ) < 1 + k)) hA]

/-- Reflection: `x ↦ -φ(-x)` is `k`-quasisymmetric on the real axis with `φ` (the two halves of (7.1) swap). -/
theorem lv27_reflect {φ : ℝ → ℝ} {k : ℝ} (h : IsKQuasisymmetricOn φ univ k) :
    IsKQuasisymmetricOn (fun x => -φ (-x)) univ k := by
  obtain ⟨hm, hk1, hq⟩ := lv27_qs h
  have hc : Continuous φ := continuousOn_univ.1 h.2.1
  refine ⟨ordConnected_univ, (hc.comp continuous_neg).neg.continuousOn, ?_, by linarith, ?_⟩
  · exact strictMonoOn_univ.2 fun x y hxy => neg_lt_neg (hm (neg_lt_neg hxy))
  · intro x t ht _ _ _
    obtain ⟨h1, h2⟩ := hq (-x) t ht
    simp only
    rw [show -(x - t) = -x + t by ring, show -(x + t) = -x - t by ring]
    constructor <;> linarith

/-- Halving: `φ(x + t/2) - φ(x) ≤ k/(1 + k) · (φ(x + t) - φ(x))` (first half of (7.1) at the midpoint). -/
theorem lv27_half {φ : ℝ → ℝ} {k : ℝ} (h : IsKQuasisymmetricOn φ univ k) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    φ (x + t / 2) - φ x ≤ k / (1 + k) * (φ (x + t) - φ x) := by
  obtain ⟨-, hk, hq⟩ := lv27_qs h
  have h1 := (hq (x + t / 2) (t / 2) (by positivity)).1
  rw [show x + t / 2 - t / 2 = x by ring, show x + t / 2 + t / 2 = x + t by ring] at h1
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  linarith

/-- Iterated halving: `φ(x + t/2ⁿ) - φ(x) ≤ (k/(1 + k))ⁿ (φ(x + t) - φ(x))`. -/
theorem lv27_half_iter {φ : ℝ → ℝ} {k : ℝ} (h : IsKQuasisymmetricOn φ univ k) (x : ℝ) {t : ℝ} (ht : 0 < t)
    (n : ℕ) : φ (x + t / 2 ^ n) - φ x ≤ (k / (1 + k)) ^ n * (φ (x + t) - φ x) := by
  obtain ⟨-, hk, -⟩ := lv27_qs h
  have hk0 : 0 < k := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 := lv27_half h x (t := t / 2 ^ n) (by positivity)
    rw [show t / 2 ^ n / 2 = t / 2 ^ (n + 1) by rw [pow_succ, div_div]] at h2
    have hθ : 0 ≤ k / (1 + k) := by positivity
    calc φ (x + t / 2 ^ (n + 1)) - φ x ≤ k / (1 + k) * (φ (x + t / 2 ^ n) - φ x) := h2
      _ ≤ k / (1 + k) * ((k / (1 + k)) ^ n * (φ (x + t) - φ x)) := mul_le_mul_of_nonneg_left ih hθ
      _ = (k / (1 + k)) ^ (n + 1) * (φ (x + t) - φ x) := by ring

/-- `(k/(1 + k))ⁿ = (2⁻ⁿ)^{q₁}` for `q₁ = log₂((1 + k)/k)`. -/
theorem lv27_theta_pow {k : ℝ} (hk : 1 ≤ k) (n : ℕ) :
    (k / (1 + k)) ^ n = (1 / (2 : ℝ) ^ n) ^ Real.logb 2 ((1 + k) / k) := by
  have hk0 : 0 < k := by linarith
  have hb : (2 : ℝ) ^ Real.logb 2 ((1 + k) / k) = (1 + k) / k :=
    Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
  rw [Real.div_rpow zero_le_one (by positivity), Real.one_rpow, ← Real.rpow_natCast (2 : ℝ) n,
    ← Real.rpow_mul (by norm_num), mul_comm (n : ℝ), Real.rpow_mul (by norm_num), hb, Real.rpow_natCast,
    div_pow, div_pow, one_div_div]

/-- Doubling: `φ(2ⁿ t) - φ(0) ≤ (1 + k)ⁿ (φ(t) - φ(0))` (second half of (7.1) at `x = s`, `t = s`). -/
theorem lv27_double_iter {φ : ℝ → ℝ} {k : ℝ} (h : IsKQuasisymmetricOn φ univ k) (n : ℕ) {t : ℝ}
    (ht : 0 < t) : φ (2 ^ n * t) - φ 0 ≤ (1 + k) ^ n * (φ t - φ 0) := by
  obtain ⟨-, hk, hq⟩ := lv27_qs h
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : 0 < 2 ^ n * t := by positivity
    have h2 := (hq (2 ^ n * t) (2 ^ n * t) hs).2
    rw [show 2 ^ n * t + 2 ^ n * t = 2 ^ (n + 1) * t by ring, sub_self] at h2
    have hk0 : 0 ≤ 1 + k := by linarith
    calc φ (2 ^ (n + 1) * t) - φ 0 = (φ (2 ^ (n + 1) * t) - φ (2 ^ n * t)) + (φ (2 ^ n * t) - φ 0) := by ring
      _ ≤ (1 + k) * (φ (2 ^ n * t) - φ 0) := by linarith
      _ ≤ (1 + k) * ((1 + k) ^ n * (φ t - φ 0)) := mul_le_mul_of_nonneg_left ih hk0
      _ = (1 + k) ^ (n + 1) * (φ t - φ 0) := by ring

/-- Growth on the positive axis: for `r > 0` there is `E` with `|φ(x)|^{1/p} < E x` for `x > r`, where
`p = log₂(1 + k) ≥ 1`. -/
theorem lv27_growth {φ : ℝ → ℝ} {k : ℝ} (h : IsKQuasisymmetricOn φ univ k) {r : ℝ} (hr : 0 < r) :
    ∃ E : ℝ, ∀ x : ℝ, r < x → |φ x| ^ (Real.logb 2 (1 + k))⁻¹ < E * x := by
  obtain ⟨hm, hk, -⟩ := lv27_qs h
  set p := Real.logb 2 (1 + k) with hp
  have hp1 : 1 ≤ p := by
    rw [hp, Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_one]
    linarith
  have hp0 : 0 < p := by linarith
  have h2p : (2 : ℝ) ^ p = 1 + k := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
  have hD : 0 < φ r - φ 0 := sub_pos.2 (hm hr)
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = (|φ 0| + (1 + k) * (φ r - φ 0)) / r ^ p := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by
    rw [hG]
    have : 0 ≤ 1 + k := by linarith
    positivity
  refine ⟨G ^ p⁻¹ + 1, fun x hx => ?_⟩
  have hx0 : 0 < x := hr.trans hx
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near ((one_le_div hr).2 hx.le) (by norm_num : (1 : ℝ) < 2)
  have hxlt : x ≤ 2 ^ (n + 1) * r := by
    rw [div_lt_iff₀ hr] at hn2
    linarith
  have h1 : φ x - φ 0 ≤ (1 + k) ^ (n + 1) * (φ r - φ 0) := by
    have := lv27_double_iter h (n + 1) hr
    linarith [hm.monotone hxlt]
  have h2 : (1 + k) ^ n ≤ (x / r) ^ p := by
    rw [← h2p, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm p (n : ℝ),
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
    exact Real.rpow_le_rpow (by positivity) hn1 hp0.le
  have hxr1 : 1 ≤ (x / r) ^ p := Real.one_le_rpow ((one_le_div hr).2 hx.le) hp0.le
  have hpow : (1 + k) ^ (n + 1) * (φ r - φ 0) ≤ (1 + k) * (x / r) ^ p * (φ r - φ 0) := by
    rw [pow_succ']
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by linarith)) hD.le
  have habs : |φ 0| ≤ |φ 0| * (x / r) ^ p := le_mul_of_one_le_right (abs_nonneg _) hxr1
  have hnn : 0 ≤ (1 + k) * (x / r) ^ p * (φ r - φ 0) := by
    have : 0 ≤ 1 + k := by linarith
    positivity
  have h3 : |φ x| ≤ G * x ^ p := by
    have e : G * x ^ p = (|φ 0| + (1 + k) * (φ r - φ 0)) * (x / r) ^ p := by
      rw [hG, Real.div_rpow hx0.le hr.le]
      ring
    rw [e, abs_le]
    have hφx : φ 0 < φ x := hm hx0
    constructor
    · nlinarith [neg_abs_le (φ 0)]
    · nlinarith [le_abs_self (φ 0)]
  have h4 := Real.rpow_le_rpow (abs_nonneg _) h3 (inv_nonneg.2 hp0.le)
  rw [Real.mul_rpow hG0 (by positivity), Real.rpow_rpow_inv hx0.le hp0.ne'] at h4
  linarith

/-- Translation: `y ↦ φ(y + c)` is `k`-quasisymmetric on the real axis with `φ`. -/
theorem lv27_translate {φ : ℝ → ℝ} {k : ℝ} (h : IsKQuasisymmetricOn φ univ k) (c : ℝ) :
    IsKQuasisymmetricOn (fun y => φ (y + c)) univ k := by
  obtain ⟨hm, hk1, hq⟩ := lv27_qs h
  have hc : Continuous φ := continuousOn_univ.1 h.2.1
  refine ⟨ordConnected_univ, (hc.comp (continuous_id.add continuous_const)).continuousOn, ?_, by linarith, ?_⟩
  · exact strictMonoOn_univ.2 fun x y hxy => hm (by linarith)
  · intro x t ht _ _ _
    obtain ⟨h1, h2⟩ := hq (x + c) t ht
    simp only
    rw [show x - t + c = x + c - t by ring, show x + t + c = x + c + t by ring]
    exact ⟨h1, h2⟩

/-- Doubling from a base point `b`: `φ(b + 2ᵐ t) - φ(b) ≤ (1 + k)ᵐ (φ(b + t) - φ(b))` (`lv27_double_iter` for the
translate). -/
theorem lv27_double_at {φ : ℝ → ℝ} {k : ℝ} (h : IsKQuasisymmetricOn φ univ k) (b : ℝ) (m : ℕ) {t : ℝ}
    (ht : 0 < t) : φ (b + 2 ^ m * t) - φ b ≤ (1 + k) ^ m * (φ (b + t) - φ b) := by
  have := lv27_double_iter (lv27_translate h b) m ht
  simp only [zero_add] at this
  rwa [add_comm b, add_comm b]

/-- Lower doubling: `kᴺ (φ(x + 2ᴺ s) - φ(x)) ≥ (1 + k)ᴺ (φ(x + s) - φ(x))` (first half of (7.1) at `x + s`). -/
theorem lv27_double_lower {φ : ℝ → ℝ} {k : ℝ} (h : IsKQuasisymmetricOn φ univ k) (x : ℝ) (N : ℕ) {s : ℝ}
    (hs : 0 < s) : (1 + k) ^ N * (φ (x + s) - φ x) ≤ k ^ N * (φ (x + 2 ^ N * s) - φ x) := by
  obtain ⟨hm, hk1, hq⟩ := lv27_qs h
  induction N with
  | zero => simp
  | succ N ih =>
    have hs' : 0 < 2 ^ N * s := by positivity
    have h1 := (hq (x + 2 ^ N * s) (2 ^ N * s) hs').1
    rw [show x + 2 ^ N * s - 2 ^ N * s = x by ring,
      show x + 2 ^ N * s + 2 ^ N * s = x + 2 ^ (N + 1) * s by ring] at h1
    have hk0 : 0 < k := by linarith
    have hkN : 0 ≤ k ^ N := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 hkN
    calc (1 + k) ^ (N + 1) * (φ (x + s) - φ x) = (1 + k) * ((1 + k) ^ N * (φ (x + s) - φ x)) := by ring
      _ ≤ (1 + k) * (k ^ N * (φ (x + 2 ^ N * s) - φ x)) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
      _ ≤ k ^ (N + 1) * (φ (x + 2 ^ (N + 1) * s) - φ x) := by
          rw [pow_succ k N]
          nlinarith

/-- One side of the quasisymmetry of the inverse: if `u < v` and `φ(w) - φ(v) ≤ φ(v) - φ(u)`, then
`w - v ≤ 2ᴺ (v - u)` for every `N` with `k < ((1 + k)/k)ᴺ`. -/
theorem lv27_inv_side {φ : ℝ → ℝ} {k : ℝ} (h : IsKQuasisymmetricOn φ univ k) {N : ℕ}
    (hN : k < ((1 + k) / k) ^ N) {u v w : ℝ} (huv : u < v) (heq : φ w - φ v ≤ φ v - φ u) :
    w - v ≤ 2 ^ N * (v - u) := by
  obtain ⟨hm, hk1, hq⟩ := lv27_qs h
  have hk0 : 0 < k := by linarith
  by_contra hlt
  have hlt' : v + 2 ^ N * (v - u) < w := by linarith [not_le.1 hlt]
  have hh : 0 < v - u := sub_pos.2 huv
  have hD : 0 < φ v - φ u := sub_pos.2 (hm huv)
  have h1 := (hq v (v - u) hh).1
  rw [sub_sub_cancel] at h1
  have h2 := lv27_double_lower h v N hh
  have h3 : φ (v + 2 ^ N * (v - u)) - φ v < φ v - φ u := by linarith [hm hlt']
  have hQ : 0 < k ^ N := by positivity
  have hP : 0 < (1 + k) ^ N := by positivity
  rw [div_pow, lt_div_iff₀ hQ] at hN
  nlinarith [mul_lt_mul_of_pos_left h3 (mul_pos hk0 hQ), mul_le_mul_of_nonneg_left h2 hk0.le,
    mul_le_mul_of_nonneg_left h1 hP.le, mul_lt_mul_of_pos_right hN hD]

/-- **Unlabelled** (Ch. II §7.1, P1:2680). The inverse of a function quasisymmetric on the real axis is quasisymmetric
on the real axis (cited in §7.3).
Modelling: the inverse is any `ψ : ℝ → ℝ` with `ψ ∘ φ = id` and `φ ∘ ψ = id` (a function quasisymmetric on the real
axis maps it onto itself, so such a `ψ` exists). -/
theorem quasisymmetric_inv {φ ψ : ℝ → ℝ} (hφ : IsQuasisymmetricOn φ univ) (h₁ : Function.LeftInverse ψ φ)
    (h₂ : Function.RightInverse ψ φ) : IsQuasisymmetricOn ψ univ := by
  obtain ⟨k, hk⟩ := hφ
  obtain ⟨hm, hk1, -⟩ := lv27_qs hk
  have hk0 : 0 < k := by linarith
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt k (by rw [lt_div_iff₀ hk0]; linarith : (1 : ℝ) < (1 + k) / k)
  have hψ : StrictMono ψ := fun x y hxy => hm.lt_iff_lt.1 (by rwa [h₂ x, h₂ y])
  have hsurj : Function.Surjective ψ := fun x => ⟨φ x, h₁ x⟩
  refine ⟨2 ^ N, ordConnected_univ, (hψ.monotone.continuous_of_surjective hsurj).continuousOn,
    strictMonoOn_univ.2 hψ, by positivity, fun X T hT _ _ _ => ?_⟩
  have huv : ψ (X - T) < ψ X := hψ (by linarith)
  have hvw : ψ X < ψ (X + T) := hψ (by linarith)
  have e1 : φ (ψ (X + T)) - φ (ψ X) = T := by rw [h₂ (X + T), h₂ X]; ring
  have e2 : φ (ψ X) - φ (ψ (X - T)) = T := by rw [h₂ X, h₂ (X - T)]; ring
  constructor
  · -- the mirrored side, through the reflection `x ↦ -φ(-x)`
    have := lv27_inv_side (lv27_reflect hk) hN (w := -ψ (X - T)) (neg_lt_neg hvw)
      (by simp only [neg_neg]; linarith)
    linarith
  · exact lv27_inv_side hk hN huv (by linarith)

/-- Comparability of adjacent intervals: if `a < b` and `c - b ≤ 2ᵐ (b - a)`, then
`φ(c) - φ(b) ≤ k (1 + k)ᵐ (φ(b) - φ(a))`. -/
theorem lv27_compare {φ : ℝ → ℝ} {k : ℝ} (h : IsKQuasisymmetricOn φ univ k) (m : ℕ) {a b c : ℝ} (hab : a < b)
    (hr : c - b ≤ 2 ^ m * (b - a)) : φ c - φ b ≤ k * (1 + k) ^ m * (φ b - φ a) := by
  obtain ⟨hm, hk1, hq⟩ := lv27_qs h
  have hh : 0 < b - a := sub_pos.2 hab
  have h1 : φ c - φ b ≤ φ (b + 2 ^ m * (b - a)) - φ b := by
    linarith [hm.monotone (show c ≤ b + 2 ^ m * (b - a) by linarith)]
  have h2 := lv27_double_at h b m hh
  have h3 := (hq b (b - a) hh).2
  rw [sub_sub_cancel] at h3
  have hk0 : 0 < k := by linarith
  have hP : 0 ≤ (1 + k) ^ m := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h3 hP]

/-- **Unlabelled** (Ch. II §7.1, P1:2680). The composition of two functions quasisymmetric on the real axis is
quasisymmetric on the real axis. -/
theorem quasisymmetric_comp {φ₁ φ₂ : ℝ → ℝ} (h₁ : IsQuasisymmetricOn φ₁ univ) (h₂ : IsQuasisymmetricOn φ₂ univ) :
    IsQuasisymmetricOn (φ₂ ∘ φ₁) univ := by
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  obtain ⟨hm₁, hk₁1, hq₁⟩ := lv27_qs hk₁
  obtain ⟨hm₂, hk₂1, -⟩ := lv27_qs hk₂
  have hk₂0 : 0 < k₂ := by linarith
  obtain ⟨m, hmk⟩ := pow_unbounded_of_one_lt k₁ (one_lt_two : (1 : ℝ) < 2)
  have hc₁ : Continuous φ₁ := continuousOn_univ.1 hk₁.2.1
  have hc₂ : Continuous φ₂ := continuousOn_univ.1 hk₂.2.1
  refine ⟨k₂ * (1 + k₂) ^ m, ordConnected_univ, (hc₂.comp hc₁).continuousOn, strictMonoOn_univ.2 (hm₂.comp hm₁),
    by positivity, fun x t ht _ _ _ => ?_⟩
  have hab : φ₁ (x - t) < φ₁ x := hm₁ (by linarith)
  have hbc : φ₁ x < φ₁ (x + t) := hm₁ (by linarith)
  obtain ⟨h1, h2⟩ := hq₁ x t ht
  have hA : 0 < φ₁ x - φ₁ (x - t) := sub_pos.2 hab
  have hB : 0 < φ₁ (x + t) - φ₁ x := sub_pos.2 hbc
  simp only [Function.comp_apply]
  constructor
  · -- the mirrored comparison, through the reflection `y ↦ -φ₂(-y)`
    have := lv27_compare (lv27_reflect hk₂) m (c := -φ₁ (x - t)) (neg_lt_neg hbc)
      (by nlinarith [mul_le_mul_of_nonneg_right hmk.le hB.le])
    simp only [neg_neg] at this
    linarith
  · exact lv27_compare hk₂ m hab (by nlinarith [mul_le_mul_of_nonneg_right hmk.le hA.le])

/-- Squaring step of §7.1 (P1:2688–2704): if both halves of (7.1) hold with the constant `K ≥ 1` for all
`0 < t ≤ s`, they hold with `K²` for all `0 < t ≤ 2s` (split `t = 2τ` into steps of length `τ`). -/
theorem lv27_square {φ : ℝ → ℝ} (hm : StrictMono φ) {K s : ℝ} (hK : 1 ≤ K)
    (H : ∀ x t : ℝ, 0 < t → t ≤ s →
      φ x - φ (x - t) ≤ K * (φ (x + t) - φ x) ∧ φ (x + t) - φ x ≤ K * (φ x - φ (x - t)))
    (x t : ℝ) (ht : 0 < t) (hts : t ≤ 2 * s) :
    φ x - φ (x - t) ≤ K ^ 2 * (φ (x + t) - φ x) ∧ φ (x + t) - φ x ≤ K ^ 2 * (φ x - φ (x - t)) := by
  have hA : 0 < φ x - φ (x - t) := sub_pos.2 (hm (by linarith))
  have hB : 0 < φ (x + t) - φ x := sub_pos.2 (hm (by linarith))
  have hK0 : 0 ≤ K := by linarith
  by_cases hle : t ≤ s
  · obtain ⟨h1, h2⟩ := H x t ht hle
    have hKK : K ≤ K ^ 2 := by nlinarith
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right hKK hB.le]
    · nlinarith [mul_le_mul_of_nonneg_right hKK hA.le]
  · have hτ : 0 < t / 2 := by positivity
    have hτs : t / 2 ≤ s := by linarith
    obtain ⟨a1, b1⟩ := H x (t / 2) hτ hτs
    obtain ⟨a2, b2⟩ := H (x - t / 2) (t / 2) hτ hτs
    obtain ⟨a3, b3⟩ := H (x + t / 2) (t / 2) hτ hτs
    rw [show x - t / 2 - t / 2 = x - t by ring, show x - t / 2 + t / 2 = x by ring] at a2 b2
    rw [show x + t / 2 - t / 2 = x by ring, show x + t / 2 + t / 2 = x + t by ring] at a3 b3
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left a3 hK0, mul_le_mul_of_nonneg_left a1 hK0]
    · nlinarith [mul_le_mul_of_nonneg_left b2 hK0, mul_le_mul_of_nonneg_left b1 hK0]

/-- **Unlabelled** (Ch. II §7.1, P1:2706, Remark). If `φ` is continuous and strictly increasing on the `x`-axis and
(7.1) holds for `0 < t ≤ δ` and for `t > 2ⁿδ`, where `n` is a positive integer, then `φ` is `k^{2^n}`-quasisymmetric
on the whole `x`-axis (cited in the proof of Lemma 7.1, with `n = 2`).
[OCR?] The source as OCR'd prints the constant `k^{2n}` (probably a flattened `k^{2^n}`; the printed page could not
be checked). The argument of §7.1 (P1:2688–2704) squares the constant each time the range of `t` is doubled, which
gives `k^{2^n}`; the two agree for `n = 1, 2`, and the only application (Lemma 7.1) has `n = 2`. With `k^{2n}` the
Remark would be false for `n ≥ 6`: `φ(x) = ∫₀ˣ e^g`, with `g(s) = c|s|` on `[-2ⁿ⁻¹δ, 2ⁿ⁻¹δ]` extended periodically
and `cδ = log 2`, satisfies (7.1) with `k = 2` for `0 < t ≤ δ` and for `t > 2ⁿδ`, while its quotient at
`x = t = 2ⁿδ/4` is `2^{2^{n-2}} > 2^{2n}`. Stated here with `k^{2^n}`, the constant the argument yields.
Modelling: (7.1) multiplied out, for every real `x`; `k > 0` and `δ > 0`. -/
theorem kQuasisymmetric_of_local_and_large {φ : ℝ → ℝ} {k δ : ℝ} {n : ℕ} (hc : Continuous φ) (hm : StrictMono φ)
    (hk : 0 < k) (hδ : 0 < δ) (hn : 0 < n)
    (h : ∀ x t : ℝ, (0 < t ∧ t ≤ δ) ∨ 2 ^ n * δ < t →
      φ x - φ (x - t) ≤ k * (φ (x + t) - φ x) ∧ φ (x + t) - φ x ≤ k * (φ x - φ (x - t))) :
    IsKQuasisymmetricOn φ univ (k ^ (2 ^ n)) := by
  -- the hypothesis `0 < n` is not needed (for `n = 0` the statement holds as well)
  have _hn : n ≠ 0 := hn.ne'
  have hk1 : 1 ≤ k := by
    obtain ⟨h1, h2⟩ := h 0 δ (Or.inl ⟨hδ, le_rfl⟩)
    have hA : 0 < φ 0 - φ (0 - δ) := sub_pos.2 (hm (by linarith))
    have hB : 0 < φ (0 + δ) - φ 0 := sub_pos.2 (hm (by linarith))
    by_contra hk1
    have hk1' : k < 1 := not_le.1 hk1
    nlinarith [mul_le_mul_of_nonneg_left h2 hk.le,
      mul_pos (mul_pos (sub_pos.2 hk1') (by linarith : (0 : ℝ) < 1 + k)) hA]
  have key : ∀ m : ℕ, ∀ x t : ℝ, 0 < t → t ≤ 2 ^ m * δ →
      φ x - φ (x - t) ≤ k ^ 2 ^ m * (φ (x + t) - φ x) ∧ φ (x + t) - φ x ≤ k ^ 2 ^ m * (φ x - φ (x - t)) := by
    intro m
    induction m with
    | zero =>
      intro x t ht hts
      simpa using h x t (Or.inl ⟨ht, by simpa using hts⟩)
    | succ m ih =>
      intro x t ht hts
      have := lv27_square hm (one_le_pow₀ hk1) ih x t ht (by rw [pow_succ] at hts; linarith)
      rwa [← pow_mul, ← pow_succ] at this
  refine ⟨ordConnected_univ, hc.continuousOn, strictMonoOn_univ.2 hm, by positivity, fun x t ht _ _ _ => ?_⟩
  by_cases hts : t ≤ 2 ^ n * δ
  · exact key n x t ht hts
  · obtain ⟨h1, h2⟩ := h x t (Or.inr (not_le.1 hts))
    have hkK : k ≤ k ^ 2 ^ n := le_self_pow₀ hk1 (by positivity)
    have hA : 0 < φ x - φ (x - t) := sub_pos.2 (hm (by linarith))
    have hB : 0 < φ (x + t) - φ x := sub_pos.2 (hm (by linarith))
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right hkK hB.le]
    · nlinarith [mul_le_mul_of_nonneg_right hkK hA.le]

/-! ## §7.2 Extension of a quasisymmetric function -/

/-- **Lemma 7.1** (Ch. II §7.2). Every function `φ` which is `k`-quasisymmetric on an interval `I = {x | a ≤ x ≤ b}`
can be extended to a `K`-quasisymmetric function on the whole `x`-axis. The constant `K` is less than a number
depending only on `k`.
Modelling: `∀ k, ∃ K₀, ∀ a b φ, …` (the bound depends only on `k`; the proof gives
`max (9⁴, 2⁴(k² + k³ + k⁴)⁴)`); the extension is `K₀`-quasisymmetric (`k`-quasisymmetry is monotone in `k`); `a < b`
(the interval is nondegenerate). -/
theorem lemma2_7_1 (k : ℝ) :
    ∃ K₀ : ℝ, ∀ (a b : ℝ) (φ : ℝ → ℝ), a < b → IsKQuasisymmetricOn φ (Icc a b) k →
      ∃ Φ : ℝ → ℝ, EqOn Φ φ (Icc a b) ∧ IsKQuasisymmetricOn Φ univ K₀ := by
  sorry

/-! ## §7.3 Hölder continuity of a quasisymmetric function -/

/-- **Formula (7.8)** (Ch. II §7.3). A `k`-quasisymmetric function `φ` on the `x`-axis satisfies
`|φ(x) - φ(y)| < C₁ |x - y|^{q₁}` in every bounded interval `I`, where `q₁`, `0 < q₁ ≤ 1`, depends only on `k`, while
the finite constant `C₁` also depends on `I` and on `φ`.
Modelling: `∀ k, ∃ q₁, ∀ φ, ∀ I, ∃ C₁`; `I = [a, b]`; `x ≠ y` (for `x = y` both sides vanish). -/
theorem eq2_7_8 (k : ℝ) :
    ∃ q₁ : ℝ, 0 < q₁ ∧ q₁ ≤ 1 ∧ ∀ φ : ℝ → ℝ, IsKQuasisymmetricOn φ univ k → ∀ a b : ℝ, ∃ C₁ : ℝ,
      ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≠ y → |φ x - φ y| < C₁ * |x - y| ^ q₁ := by
  -- `k`-quasisymmetry forces `1 ≤ k` (`lv27_qs`): for `k < 1` the hypothesis on `φ` is unsatisfiable (`1/k ≤ k`
  -- fails), so the exponent `1` chosen there is never used; it is not a junk-value device.
  by_cases hk1 : 1 ≤ k
  swap
  · exact ⟨1, one_pos, le_rfl, fun φ hφ => absurd (lv27_qs hφ).2.1 hk1⟩
  have hk0 : 0 < k := by linarith
  set q := Real.logb 2 ((1 + k) / k) with hqdef
  have hq0 : 0 < q := Real.logb_pos (by norm_num) (by rw [lt_div_iff₀ hk0]; linarith)
  have hq1 : q ≤ 1 := by
    rw [hqdef, Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_one, div_le_iff₀ hk0]
    linarith
  refine ⟨q, hq0, hq1, fun φ hφ a b => ?_⟩
  obtain ⟨hm, -, -⟩ := lv27_qs hφ
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = |b - a| + 1 := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hL]; positivity
  have hab : b - a < L := by rw [hL]; linarith [le_abs_self (b - a)]
  have haL : a < b + L := by rw [hL]; linarith [neg_abs_le (b - a)]
  have hM0 : 0 < φ (b + L) - φ a := sub_pos.2 (hm haL)
  have key : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x < y →
      φ y - φ x < (φ (b + L) - φ a) * (2 / L) ^ q * (y - x) ^ q := by
    intro x hx y hy hxy
    have hh0 : 0 < y - x := sub_pos.2 hxy
    have hhL : y - x < L := by linarith [hx.1, hy.2]
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near ((one_le_div hh0).2 hhL.le) (by norm_num : (1 : ℝ) < 2)
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have hstep : y - x ≤ L / 2 ^ n := by
      rw [le_div_iff₀ h2n]
      rw [le_div_iff₀ hh0] at hn1
      linarith
    have h1 : φ y - φ x ≤ φ (x + L / 2 ^ n) - φ x := by
      linarith [hm.monotone (show y ≤ x + L / 2 ^ n by linarith)]
    have h2 := lv27_half_iter hφ x hL0 n
    have h3 : φ (x + L) - φ x ≤ φ (b + L) - φ a := by
      linarith [hm.monotone (show x + L ≤ b + L by linarith [hx.2]), hm.monotone hx.1]
    have hθ0 : 0 ≤ (k / (1 + k)) ^ n := by positivity
    have h4 : φ y - φ x ≤ (k / (1 + k)) ^ n * (φ (b + L) - φ a) :=
      h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 hθ0))
    rw [lv27_theta_pow hk1 n] at h4
    have h5 : 1 / (2 : ℝ) ^ n < 2 / L * (y - x) := by
      rw [show 2 / L * (y - x) = 2 * (y - x) / L by ring, div_lt_div_iff₀ h2n hL0]
      rw [div_lt_iff₀ hh0, pow_succ] at hn2
      linarith
    have h6 : (1 / (2 : ℝ) ^ n) ^ q < (2 / L * (y - x)) ^ q := Real.rpow_lt_rpow (by positivity) h5 hq0
    rw [Real.mul_rpow (by positivity) hh0.le] at h6
    calc φ y - φ x ≤ (1 / (2 : ℝ) ^ n) ^ q * (φ (b + L) - φ a) := h4
      _ < (2 / L) ^ q * (y - x) ^ q * (φ (b + L) - φ a) := mul_lt_mul_of_pos_right h6 hM0
      _ = (φ (b + L) - φ a) * (2 / L) ^ q * (y - x) ^ q := by ring
  refine ⟨(φ (b + L) - φ a) * (2 / L) ^ q, fun x hx y hy hxy => ?_⟩
  rcases lt_or_gt_of_ne hxy with h | h
  · rw [abs_sub_comm (φ x), abs_of_pos (sub_pos.2 (hm h)), abs_sub_comm x, abs_of_pos (sub_pos.2 h)]
    exact key x hx y hy h
  · rw [abs_of_pos (sub_pos.2 (hm h)), abs_of_pos (sub_pos.2 h)]
    exact key y hy x hx h

/-- **Formula (7.9)** (Ch. II §7.3). For a `k`-quasisymmetric function `φ` on the `x`-axis there corresponds to every
`r > 0` a finite `C₂` such that `1/|x| < C₂/|φ(x)|^{q₂}` for `|x| > r`, where `0 < q₂ ≤ 1` depends only on `k`.
[OCR] The source prints `|φ(x)^{q₂}|`.
Modelling: `∀ k, ∃ q₂, ∀ φ, ∀ r > 0, ∃ C₂`; multiplied out, `|φ(x)|^{q₂} < C₂ |x|` (this is also the reading of the
book's inequality where `φ(x) = 0`). -/
theorem eq2_7_9 (k : ℝ) :
    ∃ q₂ : ℝ, 0 < q₂ ∧ q₂ ≤ 1 ∧ ∀ φ : ℝ → ℝ, IsKQuasisymmetricOn φ univ k → ∀ r : ℝ, 0 < r → ∃ C₂ : ℝ,
      ∀ x : ℝ, r < |x| → |φ x| ^ q₂ < C₂ * |x| := by
  -- As in (7.8): for `k < 1` no `φ` is `k`-quasisymmetric (`lv27_qs`), so the exponent `1` is never used.
  by_cases hk1 : 1 ≤ k
  swap
  · exact ⟨1, one_pos, le_rfl, fun φ hφ => absurd (lv27_qs hφ).2.1 hk1⟩
  have hp1 : 1 ≤ Real.logb 2 (1 + k) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_one]
    linarith
  refine ⟨(Real.logb 2 (1 + k))⁻¹, inv_pos.2 (by linarith), inv_le_one_of_one_le₀ hp1, fun φ hφ r hr => ?_⟩
  obtain ⟨E₁, hE₁⟩ := lv27_growth hφ hr
  obtain ⟨E₂, hE₂⟩ := lv27_growth (lv27_reflect hφ) hr
  refine ⟨max E₁ E₂, fun x hx => ?_⟩
  rcases lt_abs.1 hx with h | h
  · rw [abs_of_pos (hr.trans h)]
    exact (hE₁ x h).trans_le (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  · have := hE₂ (-x) h
    simp only [neg_neg, abs_neg] at this
    rw [abs_of_neg (by linarith : x < 0)]
    exact this.trans_le (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))

/-- **Formula (7.10)** (Ch. II §7.3). Let `φ` be `k`-quasisymmetric on the `x`-axis. If `y` belongs to a bounded
interval `I` and `x` is arbitrary, then `|φ(x) - φ(y)| < C (|x - y|^{q₁} + |x - y|^{1/q₂})`, where `C` depends on `I`
and `φ` (cited in §7.4).
[OCR] The source prints `\bar φ(y)` for `φ(y)`.
Modelling: `q₁`, `q₂` are the exponents of (7.8) and (7.9); a separate declaration cannot refer to those, so they are
quantified here afresh, depending only on `k` (`∀ k, ∃ q₁ q₂, ∀ φ, ∀ I, ∃ C`); `I = [a, b]`; `x ≠ y` (for `x = y`
both sides vanish). -/
theorem eq2_7_10 (k : ℝ) :
    ∃ q₁ q₂ : ℝ, 0 < q₁ ∧ q₁ ≤ 1 ∧ 0 < q₂ ∧ q₂ ≤ 1 ∧ ∀ φ : ℝ → ℝ, IsKQuasisymmetricOn φ univ k →
      ∀ a b : ℝ, ∃ C : ℝ, ∀ y ∈ Icc a b, ∀ x : ℝ, x ≠ y →
        |φ x - φ y| < C * (|x - y| ^ q₁ + |x - y| ^ (1 / q₂)) := by
  obtain ⟨q₁, hq₁0, hq₁1, H1⟩ := eq2_7_8 k
  obtain ⟨q₂, hq₂0, hq₂1, H2⟩ := eq2_7_9 k
  refine ⟨q₁, q₂, hq₁0, hq₁1, hq₂0, hq₂1, fun φ hφ a b => ?_⟩
  obtain ⟨hm, -, -⟩ := lv27_qs hφ
  obtain ⟨C₁, hC₁⟩ := H1 φ hφ (a - 1) (b + 1)
  obtain ⟨C₂, hC₂⟩ := H2 φ hφ 1 one_pos
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = |a| + |b| := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = |φ a| + |φ b| := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B' : ℝ, B' = |φ (-1)| + |φ 1| := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = (|C₂| * (1 + R)) ^ (1 / q₂) := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hB'0 : 0 ≤ B' := by rw [hB']; positivity
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  refine ⟨|C₁| + T + B + B' + 1, fun y hy x hxy => ?_⟩
  have hd0 : 0 < |x - y| := abs_pos.2 (sub_ne_zero.2 hxy)
  have hP1 : 0 ≤ |x - y| ^ q₁ := by positivity
  have hP2 : 0 ≤ |x - y| ^ (1 / q₂) := by positivity
  have hC0 : 0 ≤ |C₁| + T + B + B' + 1 := by positivity
  have hφy : |φ y| ≤ B := by
    rw [hB, abs_le]
    constructor
    · linarith [neg_abs_le (φ a), abs_nonneg (φ b), hm.monotone hy.1]
    · linarith [le_abs_self (φ b), abs_nonneg (φ a), hm.monotone hy.2]
  rcases le_or_gt |x - y| 1 with hd1 | hd1
  · have hx' : x ∈ Icc (a - 1) (b + 1) := by
      obtain ⟨h1, h2⟩ := abs_le.1 hd1
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hy' : y ∈ Icc (a - 1) (b + 1) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have h := hC₁ x hx' y hy' hxy
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self C₁) hP1, mul_nonneg hC0 hP2,
      mul_le_mul_of_nonneg_right (show |C₁| ≤ |C₁| + T + B + B' + 1 by linarith) hP1]
  · have hP2' : 1 ≤ |x - y| ^ (1 / q₂) := Real.one_le_rpow hd1.le (by positivity)
    have hsub := abs_sub (φ x) (φ y)
    rcases le_or_gt |x| 1 with hx1 | hx1
    · have hφx : |φ x| ≤ B' := by
        obtain ⟨h1, h2⟩ := abs_le.1 hx1
        rw [hB', abs_le]
        constructor
        · linarith [neg_abs_le (φ (-1)), abs_nonneg (φ 1), hm.monotone h1]
        · linarith [le_abs_self (φ 1), abs_nonneg (φ (-1)), hm.monotone h2]
      nlinarith [le_mul_of_one_le_right (add_nonneg hB0 hB'0) hP2',
        mul_pos (by linarith [abs_nonneg C₁] : (0 : ℝ) < |C₁| + T + 1) (by linarith : (0 : ℝ) < |x - y| ^ (1 / q₂)),
        mul_nonneg hC0 hP1]
    · have h := hC₂ x hx1
      have hy0 : |y| ≤ R := by
        rw [hR, abs_le]
        constructor
        · linarith [neg_abs_le a, abs_nonneg b, hy.1]
        · linarith [le_abs_self b, abs_nonneg a, hy.2]
      have hxle : |x| ≤ (1 + R) * |x - y| := by
        have := abs_sub_abs_le_abs_sub x y
        nlinarith
      have hC₂x : C₂ * |x| ≤ |C₂| * (1 + R) * |x - y| := by
        have := mul_le_mul_of_nonneg_left hxle (abs_nonneg C₂)
        have := mul_le_mul_of_nonneg_right (le_abs_self C₂) (abs_nonneg x)
        nlinarith
      have hlt : |φ x| ^ q₂ < |C₂| * (1 + R) * |x - y| := h.trans_le hC₂x
      have h5 := Real.rpow_lt_rpow (by positivity) hlt (by positivity : (0 : ℝ) < 1 / q₂)
      rw [one_div, Real.rpow_rpow_inv (abs_nonneg _) hq₂0.ne', ← one_div,
        Real.mul_rpow (by positivity) hd0.le, ← hT] at h5
      nlinarith [le_mul_of_one_le_right hB0 hP2', mul_nonneg hC0 hP1,
        mul_le_mul_of_nonneg_right (show T + B ≤ |C₁| + T + B + B' + 1 by linarith [abs_nonneg C₁]) hP2,
        mul_pos (by linarith [abs_nonneg C₁] : (0 : ℝ) < |C₁| + B' + 1) (by linarith : (0 : ℝ) < |x - y| ^ (1 / q₂))]

/-! ## §7.4 Approximation of a quasisymmetric function -/

/-- **Definition** (the Gauss integrals `φₙ`, Ch. II §7.4). For a function `φ` on the `x`-axis and a positive integer
`n`, `φₙ(z) = c_n ∫_{-∞}^{∞} φ(r) e^{-n(r - z)²} dr`, `z` complex, where
`c_n = (∫_{-∞}^{∞} e^{-nr²} dr)⁻¹ = √(n/π)`.
Modelling: the Bochner integral over `ℝ`. Junk: `0` where the integrand is not integrable, which never happens for a
quasisymmetric `φ` by (7.10); every statement using `φₙ` concerns quasisymmetric `φ` and asserts the convergence
(`qsGaussApprox_differentiable`). -/
def qsGaussApprox (φ : ℝ → ℝ) (n : ℕ) : ℂ → ℂ :=
  fun z => (Real.sqrt ((n : ℝ) / Real.pi) : ℂ) * ∫ r : ℝ, (φ r : ℂ) * exp (-(n : ℂ) * ((r : ℂ) - z) ^ 2)

/-- **Unlabelled** (Ch. II §7.4, P1:2798). Let `φ` be `k`-quasisymmetric on the `x`-axis and `n` a positive integer.
The integral defining `φₙ` converges uniformly in every compact set of the finite plane and defines an analytic
(entire) function of `z` (used in the proof of the sewing theorem).
Modelling: the convergence is stated as the integrability of the integrand for every `z` together with the uniform
convergence, on every compact set, of the integrals over `[a, b]` as `(a, b) → (-∞, +∞)` with the two endpoints
independent (the filter `atBot ×ˢ atTop`); analyticity in the finite plane is complex differentiability everywhere.
-/
theorem qsGaussApprox_differentiable {φ : ℝ → ℝ} {k : ℝ} (hφ : IsKQuasisymmetricOn φ univ k) {n : ℕ} (hn : 1 ≤ n) :
    (∀ z : ℂ, Integrable (fun r : ℝ => (φ r : ℂ) * exp (-(n : ℂ) * ((r : ℂ) - z) ^ 2))) ∧
      (∀ S : Set ℂ, IsCompact S →
        TendstoUniformlyOn (fun (ab : ℝ × ℝ) (z : ℂ) => (Real.sqrt ((n : ℝ) / Real.pi) : ℂ) *
          ∫ r in ab.1..ab.2, (φ r : ℂ) * exp (-(n : ℂ) * ((r : ℂ) - z) ^ 2)) (qsGaussApprox φ n)
          (atBot ×ˢ atTop) S) ∧
      Differentiable ℂ (qsGaussApprox φ n) := by
  sorry

/-- **Unlabelled** (Ch. II §7.4, P1:2802, property 1°). Let `φ` be `k`-quasisymmetric on the `x`-axis and `n` a
positive integer. The restriction of `φₙ` to the `x`-axis is `k`-quasisymmetric.
Modelling: the restriction is real-valued, the real function `ψ` with `φₙ(x) = ψ(x)` for real `x`. -/
theorem qsGaussApprox_kQuasisymmetric {φ : ℝ → ℝ} {k : ℝ} (hφ : IsKQuasisymmetricOn φ univ k) {n : ℕ}
    (hn : 1 ≤ n) :
    ∃ ψ : ℝ → ℝ, (∀ x : ℝ, qsGaussApprox φ n x = (ψ x : ℂ)) ∧ IsKQuasisymmetricOn ψ univ k := by
  sorry

/-- **Unlabelled** (Ch. II §7.4, P1:2810, property 2°). Let `φ` be `k`-quasisymmetric on the `x`-axis and `n` a
positive integer. The derivative of `φₙ` is positive at every point of the `x`-axis.
Modelling: `φₙ` has at every real `x` a complex derivative which is a positive real number (no `deriv` junk). -/
theorem qsGaussApprox_deriv_pos {φ : ℝ → ℝ} {k : ℝ} (hφ : IsKQuasisymmetricOn φ univ k) {n : ℕ} (hn : 1 ≤ n) :
    ∀ x : ℝ, ∃ c : ℝ, 0 < c ∧ HasDerivAt (qsGaussApprox φ n) (c : ℂ) (x : ℂ) := by
  sorry

/-- **Unlabelled** (Ch. II §7.4, P1:2818, property 3°). Let `φ` be `k`-quasisymmetric on the `x`-axis. As `n → ∞`,
`φₙ(x)` converges uniformly to `φ(x)` on every bounded segment of the real axis.
Modelling: the bounded segment is `[a, b]`. -/
theorem qsGaussApprox_tendstoUniformlyOn {φ : ℝ → ℝ} {k : ℝ} (hφ : IsKQuasisymmetricOn φ univ k) (a b : ℝ) :
    TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => qsGaussApprox φ n x) (fun x : ℝ => (φ x : ℂ)) atTop (Icc a b) := by
  sorry

/-! ## §7.5 A sewing theorem for conformal mappings -/

/-- **Sewing theorem** (Ch. II §7.5; Lehto–Virtanen, Pfluger, footnote 25). Let `φ` be a quasisymmetric function on
the real axis. Then the upper and lower half-planes can be mapped conformally onto disjoint Jordan domains such that
the boundary values `f₁` and `f₂` satisfy the relation `f₁(x) = f₂(φ(x))` (cited in V.1).
Modelling: `f₁`, `f₂` are conformal mappings of `H₁`, `H₂` which are at the same time their extensions to
homeomorphisms of the closed half-planes onto the closures of the image domains (I.2.2); their boundary values are
their values at the real points. -/
theorem sewing_theorem {φ : ℝ → ℝ} (hφ : IsQuasisymmetricOn φ univ) :
    ∃ f₁ f₂ : ExtPlane → ExtPlane, IsConformalMap f₁ (toExt upperHalf) ∧ IsConformalMap f₂ (toExt lowerHalf) ∧
      IsJordanDomainExt (f₁ '' toExt upperHalf) ∧ IsJordanDomainExt (f₂ '' toExt lowerHalf) ∧
      Disjoint (f₁ '' toExt upperHalf) (f₂ '' toExt lowerHalf) ∧
      IsHomeoOn f₁ (closure (toExt upperHalf)) (closure (f₁ '' toExt upperHalf)) ∧
      IsHomeoOn f₂ (closure (toExt lowerHalf)) (closure (f₂ '' toExt lowerHalf)) ∧
      ∀ x : ℝ, f₁ ((x : ℂ) : ExtPlane) = f₂ ((φ x : ℂ) : ExtPlane) := by
  sorry

end LehtoVirtanen1973
