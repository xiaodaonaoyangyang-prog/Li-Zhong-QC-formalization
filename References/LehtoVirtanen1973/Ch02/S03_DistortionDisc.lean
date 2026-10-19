import References.LehtoVirtanen1973.Ch02.S02_GrotzschModule
import LiZhongQC.Ch03.S15_Distortion

/-!
# Lehto–Virtanen, Chapter II §3: Distortion under a bounded quasiconformal mapping of a disc

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. II §3
(pp. 63–68; `full.md` P1:1874–2121).

The mappings are `K`-quasiconformal mappings (Ch. I §3.2) of the unit disc `|z| < 1` (resp. of a disc `|z| < r`)
into the unit disc (resp. into `|w| < R`); "`w` maps `|z| < 1` onto a subdomain of `|w| < 1`" is
`w(D) ⊆ D`, the image being a domain by the invariance of domains. Their values are finite and are read with
`finiteMap`. The hypothesis `IsKQuasiconformal w G K` forces `K ≥ 1`. The boundary values of a quasiconformal
self-map of the disc (Theorem 3.2) are those of the homeomorphic extension to the closed disc (Ch. I §8.2).

* Definition (the inverse function `μ⁻¹` of `μ`, and the distortion function `φ_K` (3.1), §3.1, with the limits
  `φ_K(0) = 0`, `φ_K(1) = 1` of §3.2) — `grotzschMuInv`, `distortionPhi`
* Theorem 3.1 (Hersch–Pfluger, §3.1) — `thm2_3_1_i`, `thm2_3_1_ii`
* Formula (3.6) (§3.2) — `eq2_3_6`
* Formula (3.8) (§3.2) — `eq2_3_8`
* Formula (3.9) (§3.3) — `eq2_3_9`
* Formula (3.10) (§3.3) — `eq2_3_10`
* Theorem 3.2 (Mori, §3.4) — `thm2_3_2_i`, `thm2_3_2_ii`
* Formula (3.18) (§3.4, Remark) — `eq2_3_18`

Not stated (inventory U−, never cited later or used only in the derivations of this section): the introductory remark of
§3.4 that without special hypotheses there is no bound for the euclidean distortion valid near the boundary
(P1:2038–2040); the inequality `μ(|z|) ≤ K μ(|w(z)|)` (P1:1883), a step towards (3.2); the double inequality (3.4) with
its sharpness (P1:1914–1922) and the rescaled bound (3.5) (P1:1924–1927); the properties of `φ_K` listed in §3.2
(monotonicity, continuity, `φ_K(r) ≥ r` for `K ≥ 1`, `φ_{K₁K₂} = φ_{K₁} ∘ φ_{K₂}`, `φ₂(r) = 2√r/(1 + r)`; P1:1930–1942);
the monotonicity of `log(1/r) - μ(r)` (P1:1950); the limit `r^{-1/K} φ_K(r) → 4^{1 - 1/K}` (P1:1991); the hyperbolic
metric (3.11), the hyperbolic distance (3.12) and the reformulation (3.13) of (3.10) (P1:2018–2036), not used again in
the book; the proof steps (3.3), (3.7), (3.15)–(3.17); and the conjecture closing §3.4 (P1:2120).
-/

open Complex Set Filter Topology
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve IsMobius grotzschMu unitDisc)
open References (IsDomainExt IsJordanDomainExt finitePart)

/-! ## §3.1 Alteration of the distance from the origin -/

open scoped Classical in
/-- **Definition** (the inverse function `μ⁻¹`, Ch. II §3.1, notation of (3.1)). `μ` is a strictly decreasing
continuous map of `(0, 1)` onto `(0, ∞)` (§1.1, §2.2–2.4), and `μ⁻¹(x)` is the `r ∈ (0, 1)` with `μ(r) = x`.
Junk: `0` when there is no such `r`, i.e. for `x ≤ 0`, never used (all arguments are values `μ(r)/K > 0`). -/
def grotzschMuInv (x : ℝ) : ℝ :=
  if h : ∃ r ∈ Ioo (0 : ℝ) 1, grotzschMu r = x then h.choose else 0

/-- **Definition** (the distortion function `φ_K`, (3.1), Ch. II §3.1–3.2). For `K > 0` and `0 < r < 1`,
`φ_K(r) = μ⁻¹(μ(r)/K)`; at the end points `φ_K(0) = 0` and `φ_K(1) = 1`, the limits of §3.2, set explicitly.
Junk: `0` for `r < 0` and `1` for `r > 1`; for `K ≤ 0` the value on `(0, 1)` is the junk `0` of `μ⁻¹`. No statement
sees them: the arguments lie in `[0, 1]`, and `K ≥ 1` (forced by the `K`-quasiconformality hypotheses) or `K > 1`. -/
def distortionPhi (K r : ℝ) : ℝ :=
  if r ≤ 0 then 0 else if 1 ≤ r then 1 else grotzschMuInv (grotzschMu r / K)

/-- For `K > 1` and `0 < r < 1`, `φ_K(r)` lies in `(r, 1)` and solves `μ(φ_K(r)) = μ(r)/K` (§3.1–3.2): the value
`μ(r)/K` is attained on `(0, 1)` by the intermediate value theorem (`μ` continuous, `μ → 0` at `1`), so the
`if` of `grotzschMuInv` is not in its junk branch. -/
theorem lv23_phi_spec {K : ℝ} (hK : 1 < K) {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    r < distortionPhi K r ∧ distortionPhi K r < 1 ∧ grotzschMu (distortionPhi K r) = grotzschMu r / K := by
  have hμ : 0 < grotzschMu r := by
    have := lv22_neg_log_lt hr₀ hr₁
    have : Real.log r < 0 := Real.log_neg hr₀ hr₁
    linarith
  have hK0 : 0 < K := by linarith
  have hlt : grotzschMu r / K < grotzschMu r := div_lt_self hμ hK
  have hev : ∀ᶠ x in 𝓝[<] (1 : ℝ), grotzschMu x < grotzschMu r / K :=
    grotzschMu_tendsto_one.eventually (gt_mem_nhds (div_pos hμ hK0))
  have hev2 : ∀ᶠ x in 𝓝[<] (1 : ℝ), x ∈ Ioo r 1 := Ioo_mem_nhdsLT hr₁
  obtain ⟨r₂, hr₂, hr₂'⟩ := (hev.and hev2).exists
  have hcont : ContinuousOn grotzschMu (Icc r r₂) :=
    LiZhongQC.s15_grotzschMu_continuousOn.mono fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, hr₂'.2]⟩
  obtain ⟨c, hc, hcμ⟩ := intermediate_value_Icc' hr₂'.1.le hcont ⟨hr₂.le, hlt.le⟩
  have hex : ∃ x ∈ Ioo (0 : ℝ) 1, grotzschMu x = grotzschMu r / K :=
    ⟨c, ⟨by linarith [hc.1], by linarith [hc.2, hr₂'.2]⟩, hcμ⟩
  have hφ : distortionPhi K r = hex.choose := by
    simp only [distortionPhi, grotzschMuInv, not_le.2 hr₀, not_le.2 hr₁, ite_false]
    exact dite_eq_left_of_eq_true (eq_true hex)
  obtain ⟨⟨h0, h1⟩, hμφ⟩ := hex.choose_spec
  rw [hφ]
  refine ⟨?_, h1, hμφ⟩
  by_contra hle
  rcases (not_lt.1 hle).lt_or_eq with h | h
  · have := LiZhongQC.grotzschMu_strictAntiOn ⟨h0, h1⟩ ⟨hr₀, hr₁⟩ h
    linarith
  · rw [h] at hμφ
    linarith

/-- Helper (Tier 1). If `w` maps `toExt U` into `toExt V`, the finite core `{z ∈ ℂ : z ∈ toExt U, w(z) ≠ ∞}` of `w`
is `U`, `finiteMap w` maps `U` into `V`, and `w = finiteMap w` on `U`. -/
theorem lv23_core {w : ExtPlane → ExtPlane} {U V : Set ℂ} (hwD : w '' toExt U ⊆ toExt V) :
    {z : ℂ | (z : ExtPlane) ∈ toExt U ∧ w z ≠ extInf} = U ∧ finiteMap w '' U ⊆ V ∧
      ∀ z ∈ U, w z = ((finiteMap w z : ℂ) : ExtPlane) := by
  have hfin : ∀ z ∈ U, ∃ v ∈ V, w z = (v : ExtPlane) := fun z hz => by
    obtain ⟨v, hv, hve⟩ := hwD ⟨(z : ExtPlane), ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨v, hv, hve.symm⟩
  have hval : ∀ z ∈ U, ∀ v : ℂ, w z = (v : ExtPlane) → finiteMap w z = v := fun z _ v hv => by
    show finiteValue (w z) = v
    rw [hv]
    rfl
  refine ⟨?_, ?_, fun z hz => ?_⟩
  · ext z
    constructor
    · rintro ⟨⟨u, hu, hue⟩, -⟩
      rw [← OnePoint.coe_injective hue]
      exact hu
    · intro hz
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      obtain ⟨v, -, hv⟩ := hfin z hz
      rw [hv]
      exact OnePoint.coe_ne_infty v
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨v, hv, hve⟩ := hfin z hz
    rw [hval z hz v hve]
    exact hv
  · obtain ⟨v, -, hve⟩ := hfin z hz
    rw [hval z hz v hve]
    exact hve

/-- Helper (Tier 1). A `K`-quasiconformal `w` of `toExt U` with `w(toExt U) ⊆ toExt V` is, as `finiteMap w`, a
`K`-quasiconformal mapping of `U` into `V` in Li Zhong's sense (`lv13_isKQC_of_isKQuasiconformal`). -/
theorem lv23_isKQC {w : ExtPlane → ExtPlane} {U V : Set ℂ} {K : ℝ} (hw : IsKQuasiconformal w (toExt U) K)
    (hwD : w '' toExt U ⊆ toExt V) : LiZhongQC.IsKQC (finiteMap w) U K ∧ finiteMap w '' U ⊆ V := by
  obtain ⟨hcore, hsub, -⟩ := lv23_core hwD
  have h := lv13_isKQC_of_isKQuasiconformal hw
  rw [hcore] at h
  exact ⟨h, hsub⟩

/-- Helper (Tier 1). `φ₁(r) = r` for `0 < r < 1`: `μ` is injective on `(0, 1)`. -/
theorem lv23_phi_one {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) : distortionPhi 1 r = r := by
  have hex : ∃ x ∈ Ioo (0 : ℝ) 1, grotzschMu x = grotzschMu r / 1 := ⟨r, ⟨hr₀, hr₁⟩, (div_one _).symm⟩
  have hφ : distortionPhi 1 r = hex.choose := by
    simp only [distortionPhi, grotzschMuInv, not_le.2 hr₀, not_le.2 hr₁, ite_false]
    exact dite_eq_left_of_eq_true (eq_true hex)
  obtain ⟨hx, hμ⟩ := hex.choose_spec
  have hμ' : grotzschMu hex.choose = grotzschMu r := by rw [hμ, div_one]
  rw [hφ]
  exact LiZhongQC.grotzschMu_strictAntiOn.injOn hx ⟨hr₀, hr₁⟩ hμ'

/-- Helper (Tier 1; (3.2) for Li Zhong's mappings). A `K`-quasiconformal mapping `f` of `Δ` into `Δ` with `f(0) = 0`
satisfies `|f(z)| ≤ φ_K(|z|)`: `μ(|z|) ≤ K μ(|f(z)|)` (`LiZhongQC.eq15_1`), and `μ` decreases strictly. -/
theorem lv23_le_phi {f : ℂ → ℂ} {K : ℝ} (hf : LiZhongQC.IsKQCDiscInto f K) (hf0 : f 0 = 0) {z : ℂ}
    (hz : z ∈ unitDisc) : ‖f z‖ ≤ distortionPhi K ‖z‖ := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp [hf0, distortionPhi]
  have hr₀ : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hr₁ : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hfz : ‖f z‖ < 1 := mem_ball_zero_iff.1 (hf.2 (mem_image_of_mem f hz))
  have h := LiZhongQC.eq15_1 hf hf0 hz hz0
  have hK : 1 ≤ K := hf.1.2.1
  by_contra hlt
  rw [not_le] at hlt
  rcases hK.lt_or_eq with hK1 | hK1
  · obtain ⟨hφr, hφ1, hμφ⟩ := lv23_phi_spec hK1 hr₀ hr₁
    have hφ0 : 0 < distortionPhi K ‖z‖ := hr₀.trans hφr
    have hμ := LiZhongQC.grotzschMu_strictAntiOn ⟨hφ0, hφ1⟩ ⟨hφ0.trans hlt, hfz⟩ hlt
    rw [hμφ] at hμ
    have hK0 : 0 < K := by linarith
    have h' := (lt_div_iff₀ hK0).1 hμ
    nlinarith
  · rw [← hK1, lv23_phi_one hr₀ hr₁] at hlt
    rw [← hK1, one_mul] at h
    have hμ := LiZhongQC.grotzschMu_strictAntiOn ⟨hr₀, hr₁⟩ ⟨hr₀.trans hlt, hfz⟩ hlt
    linarith

/-- **Theorem 3.1** (Ch. II §3.1, Hersch–Pfluger), the distortion bound. Let `w` be a `K`-quasiconformal mapping of
the unit disc `|z| < 1` onto a subdomain `G′` of `|w| < 1`, normalized by `w(0) = 0`. Then `|w(z)| ≤ φ_K(|z|)`
(3.2). -/
theorem thm2_3_1_i {w : ExtPlane → ExtPlane} {K : ℝ} (hw : IsKQuasiconformal w (toExt unitDisc) K)
    (hwD : w '' toExt unitDisc ⊆ toExt unitDisc) (hw0 : w ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane))
    {z : ℂ} (hz : z ∈ unitDisc) : ‖finiteMap w z‖ ≤ distortionPhi K ‖z‖ := by
  obtain ⟨hf, hsub⟩ := lv23_isKQC hw hwD
  have hf0 : finiteMap w 0 = 0 := by
    show finiteValue (w ((0 : ℂ) : ExtPlane)) = 0
    rw [hw0]
    rfl
  exact lv23_le_phi ⟨hf, hsub⟩ hf0 hz

/-- **Theorem 3.1** (Ch. II §3.1, Hersch–Pfluger), sharpness. The bound (3.2) can be attained for every given `z`
and `K`, `|z| < 1`, `K ≥ 1`, by a mapping with `G′` the whole disc `|w| < 1`. -/
theorem thm2_3_1_ii {z : ℂ} (hz : z ∈ unitDisc) {K : ℝ} (hK : 1 ≤ K) :
    ∃ w : ExtPlane → ExtPlane, IsKQuasiconformal w (toExt unitDisc) K ∧ w '' toExt unitDisc = toExt unitDisc ∧
      w ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧ ‖finiteMap w z‖ = distortionPhi K ‖z‖ := by
  sorry

/-! ## §3.2 The distortion function `φ_K` -/

/-- **Formula (3.6)** (Ch. II §3.2). For every `K > 1` and `0 < r < 1`, `φ_K(r) < 4^{1 - 1/K} r^{1/K}`.
[OCR] The source prints `γ` for `r`. -/
theorem eq2_3_6 {K : ℝ} (hK : 1 < K) {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    distortionPhi K r < (4 : ℝ) ^ (1 - 1 / K) * r ^ (1 / K) := by
  obtain ⟨hφr, hφ1, hμφ⟩ := lv23_phi_spec hK hr₀ hr₁
  have hφ0 : 0 < distortionPhi K r := hr₀.trans hφr
  have hg := LiZhongQC.w15_a_g_antitoneOn ⟨hr₀, hr₁⟩ ⟨hφ0, hφ1⟩ hφr.le
  simp only at hg
  have h210 := (eq2_2_10 hr₀ hr₁).2
  rw [Real.log_div (by norm_num) hr₀.ne'] at h210
  have hK0 : 0 < K := by linarith
  have hc : 0 < 1 - 1 / K := by
    rw [sub_pos, div_lt_one hK0]
    exact hK
  have hlog : Real.log (distortionPhi K r) < (1 - 1 / K) * Real.log 4 + 1 / K * Real.log r := by
    have hm := mul_lt_mul_of_pos_left h210 hc
    have e : grotzschMu r / K = 1 / K * grotzschMu r := by ring
    rw [hμφ, e] at hg
    nlinarith
  have hR : (4 : ℝ) ^ (1 - 1 / K) * r ^ (1 / K) = Real.exp ((1 - 1 / K) * Real.log 4 + 1 / K * Real.log r) := by
    rw [Real.exp_add, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), Real.rpow_def_of_pos hr₀,
      mul_comm (Real.log 4), mul_comm (Real.log r)]
  rw [hR]
  calc distortionPhi K r = Real.exp (Real.log (distortionPhi K r)) := (Real.exp_log hφ0).symm
    _ < _ := Real.exp_lt_exp.2 hlog

/-- **Formula (3.8)** (Ch. II §3.2). For every `K > 1` and `0 < r < 1`,
`φ_K(r) > 4^{1 - 1/K} r^{1/K} (1 - 12 r^{2/K})`.
Modelling: `K > 1`, the standing assumption of the derivation ("for every `K > 1`", P1:1950). -/
theorem eq2_3_8 {K : ℝ} (hK : 1 < K) {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    (4 : ℝ) ^ (1 - 1 / K) * r ^ (1 / K) * (1 - 12 * r ^ (2 / K)) < distortionPhi K r := by
  obtain ⟨hφr, hφ1, hμφ⟩ := lv23_phi_spec hK hr₀ hr₁
  have h36 := eq2_3_6 hK hr₀ hr₁
  have hφ0 : 0 < distortionPhi K r := hr₀.trans hφr
  have hK0 : 0 < K := by linarith
  have h14 := (eq2_2_14 hφ0 hφ1).2
  rw [hμφ] at h14
  set φ := distortionPhi K r with hφdef
  set A := (4 : ℝ) ^ (1 - 1 / K) * r ^ (1 / K) with hA
  have h4K : 0 < (4 : ℝ) ^ (1 / K) := by positivity
  have hrK : 0 < r ^ (1 / K) := by positivity
  have hA0 : 0 < A := by positivity
  have h4A : (4 / r) ^ (1 / K) = 4 / A := by
    rw [hA, Real.div_rpow (by norm_num) hr₀.le, Real.rpow_sub (by norm_num), Real.rpow_one]
    field_simp
  have hexp : Real.exp (grotzschMu r / K) < 4 / A := by
    rw [← h4A, Real.rpow_def_of_pos (by positivity)]
    apply Real.exp_lt_exp.2
    rw [show grotzschMu r / K = grotzschMu r * (1 / K) by ring]
    exact mul_lt_mul_of_pos_right (eq2_2_10 hr₀ hr₁).2 (by positivity)
  have key1 : A * (4 - φ ^ 2 - 2 * φ ^ 4) < 4 * φ := by
    have h : 4 / φ - φ - 2 * φ ^ 3 < 4 / A := by linarith
    have e : (4 / φ - φ - 2 * φ ^ 3) * (φ * A) = A * (4 - φ ^ 2 - 2 * φ ^ 4) := by
      field_simp
    have e2 : 4 / A * (φ * A) = 4 * φ := by
      field_simp
    have := mul_lt_mul_of_pos_right h (mul_pos hφ0 hA0)
    rwa [e, e2] at this
  have hA2 : A ^ 2 ≤ 16 * r ^ (2 / K) := by
    have ha : (4 : ℝ) ^ (1 - 1 / K) ≤ 4 := by
      calc (4 : ℝ) ^ (1 - 1 / K) ≤ (4 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [one_div_pos.2 hK0])
        _ = 4 := Real.rpow_one 4
    have ha0 : 0 < (4 : ℝ) ^ (1 - 1 / K) := by positivity
    have hb : (r ^ (1 / K)) ^ 2 = r ^ (2 / K) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr₀.le]
      congr 1
      push_cast
      ring
    rw [hA, mul_pow, hb]
    have : ((4 : ℝ) ^ (1 - 1 / K)) ^ 2 ≤ 16 := by nlinarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hφ4 : φ ^ 4 < φ ^ 2 := by
    have h1 : 0 < 1 - φ ^ 2 := by nlinarith
    nlinarith [mul_pos (pow_pos hφ0 2) h1]
  have hφA : φ ^ 2 < A ^ 2 := by nlinarith
  nlinarith [mul_lt_mul_of_pos_left hφ4 hA0, mul_lt_mul_of_pos_left hφA hA0,
    mul_le_mul_of_nonneg_left hA2 hA0.le]

/-! ## §3.3 Distortion of hyperbolic distances in the disc -/

/-- Helper (Tier 1; (3.9) for Li Zhong's mappings). A `K`-quasiconformal mapping `f` of `Δ` into `Δ` satisfies
`|(f(z₁) - f(z₂))/(1 - \overline{f(z₂)} f(z₁))| ≤ φ_K(|(z₁ - z₂)/(1 - z̄₂ z₁)|)`: `lv23_le_phi` for
`M_{f(z₂)} ∘ f ∘ M_{-z₂}` at `M_{z₂}(z₁)` (the Blaschke normalization of `LiZhongQC.thm15_1`). -/
theorem lv23_hyp {f : ℂ → ℂ} {K : ℝ} (hf : LiZhongQC.IsKQCDiscInto f K) {z₁ z₂ : ℂ} (h₁ : z₁ ∈ unitDisc)
    (h₂ : z₂ ∈ unitDisc) :
    ‖(f z₁ - f z₂) / (1 - starRingEnd ℂ (f z₂) * f z₁)‖ ≤
      distortionPhi K ‖(z₁ - z₂) / (1 - starRingEnd ℂ z₂ * z₁)‖ := by
  have h₁n : ‖z₁‖ < 1 := mem_ball_zero_iff.mp h₁
  have h₂n : ‖z₂‖ < 1 := mem_ball_zero_iff.mp h₂
  have hfz₂n : ‖f z₂‖ < 1 := mem_ball_zero_iff.mp (hf.2 (mem_image_of_mem f h₂))
  have hneg : ‖-z₂‖ < 1 := by rwa [norm_neg]
  have hcB1 := LiZhongQC.isConformalOnto_blaschke hneg
  have hcB2 := LiZhongQC.isConformalOnto_blaschke hfz₂n
  have hc1 : LiZhongQC.IsKQC (f ∘ LiZhongQC.blaschke (-z₂)) unitDisc (1 * K) :=
    LiZhongQC.thm7_1_comp (LiZhongQC.isKQC_one_of_conformal Metric.isOpen_ball hcB1) hf.1 (Eq.subset hcB1.2.2)
  have hc1img : (f ∘ LiZhongQC.blaschke (-z₂)) '' unitDisc ⊆ unitDisc := by
    rw [image_comp, hcB1.2.2]
    exact hf.2
  have hc2 := LiZhongQC.thm7_1_comp hc1 (LiZhongQC.isKQC_one_of_conformal Metric.isOpen_ball hcB2) hc1img
  rw [one_mul, mul_one] at hc2
  have himg : (LiZhongQC.blaschke (f z₂) ∘ (f ∘ LiZhongQC.blaschke (-z₂))) '' unitDisc ⊆ unitDisc := by
    rw [image_comp]
    exact (image_mono hc1img).trans (Eq.subset hcB2.2.2)
  have hg0 : (LiZhongQC.blaschke (f z₂) ∘ (f ∘ LiZhongQC.blaschke (-z₂))) 0 = 0 := by
    simp only [Function.comp_apply, LiZhongQC.blaschke_neg_zero, LiZhongQC.blaschke_self]
  have hζ : LiZhongQC.blaschke z₂ z₁ ∈ unitDisc :=
    mem_ball_zero_iff.mpr (LiZhongQC.blaschke_mem_unitDisc h₂n h₁n)
  have key := lv23_le_phi ⟨hc2, himg⟩ hg0 hζ
  simp only [Function.comp_apply, LiZhongQC.blaschke_neg_blaschke h₂n h₁n] at key
  exact key

/-- **Formula (3.9)** (Ch. II §3.3). Let `w` be a `K`-quasiconformal mapping of the unit disc `|z| < 1` onto a
subdomain of the disc `|w| < 1`. For every pair of points `z₁, z₂` in `|z| < 1`,
`|(w(z₁) - w(z₂)) / (1 - \overline{w(z₂)} w(z₁))| ≤ φ_K(|(z₁ - z₂) / (1 - z̄₂ z₁)|)`. -/
theorem eq2_3_9 {w : ExtPlane → ExtPlane} {K : ℝ} (hw : IsKQuasiconformal w (toExt unitDisc) K)
    (hwD : w '' toExt unitDisc ⊆ toExt unitDisc) {z₁ z₂ : ℂ} (h₁ : z₁ ∈ unitDisc) (h₂ : z₂ ∈ unitDisc) :
    ‖(finiteMap w z₁ - finiteMap w z₂) / (1 - starRingEnd ℂ (finiteMap w z₂) * finiteMap w z₁)‖ ≤
      distortionPhi K ‖(z₁ - z₂) / (1 - starRingEnd ℂ z₂ * z₁)‖ := by
  obtain ⟨hf, hsub⟩ := lv23_isKQC hw hwD
  exact lv23_hyp ⟨hf, hsub⟩ h₁ h₂

/-- Helper (Tier 1). The rescaling identity behind (3.10): for `ρ > 0` and `|a|, |b| < ρ`,
`|(a/ρ - b/ρ)/(1 - \overline{b/ρ} (a/ρ))| = ρ |(a - b)/(ρ² - \bar b a)|`. -/
theorem lv23_scale {ρ : ℝ} (hρ : 0 < ρ) {a b : ℂ} (ha : ‖a‖ < ρ) (hb : ‖b‖ < ρ) :
    ‖(a / ρ - b / ρ) / (1 - starRingEnd ℂ (b / ρ) * (a / ρ))‖ =
      ρ * ‖(a - b) / ((ρ : ℂ) ^ 2 - starRingEnd ℂ b * a)‖ := by
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  set X : ℂ := (ρ : ℂ) ^ 2 - starRingEnd ℂ b * a with hX
  have hD : X ≠ 0 := by
    intro h
    have h1 : starRingEnd ℂ b * a = (ρ : ℂ) ^ 2 := (sub_eq_zero.1 h).symm
    have h2 := congrArg (fun x : ℂ => ‖x‖) h1
    simp only [norm_mul, Complex.norm_conj, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ] at h2
    nlinarith [mul_pos hρ (sub_pos.2 ha), mul_nonneg (norm_nonneg a) (sub_pos.2 hb).le]
  have e2 : 1 - starRingEnd ℂ (b / ρ) * (a / ρ) = X / (ρ : ℂ) ^ 2 := by
    rw [map_div₀, Complex.conj_ofReal, hX]
    field_simp
  have e : (a / ρ - b / ρ) / (1 - starRingEnd ℂ (b / ρ) * (a / ρ)) = ρ * ((a - b) / X) := by
    rw [e2]
    field_simp
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]

/-- **Formula (3.10)** (Ch. II §3.3). For a `K`-quasiconformal mapping `w` of `|z| < r` into `|w| < R` and
`|z₁|, |z₂| < r`,
`R |(w(z₁) - w(z₂)) / (R² - \overline{w(z₂)} w(z₁))| ≤ φ_K(r |(z₁ - z₂) / (r² - z̄₂ z₁)|)`.
Modelling: `0 < r`, `0 < R` (the discs are nonempty); the denominators do not vanish. -/
theorem eq2_3_10 {r R : ℝ} (hr : 0 < r) (hR : 0 < R) {w : ExtPlane → ExtPlane} {K : ℝ}
    (hw : IsKQuasiconformal w (toExt (Metric.ball (0 : ℂ) r)) K)
    (hwD : w '' toExt (Metric.ball (0 : ℂ) r) ⊆ toExt (Metric.ball (0 : ℂ) R)) {z₁ z₂ : ℂ} (h₁ : ‖z₁‖ < r)
    (h₂ : ‖z₂‖ < r) :
    R * ‖(finiteMap w z₁ - finiteMap w z₂) / ((R : ℂ) ^ 2 - starRingEnd ℂ (finiteMap w z₂) * finiteMap w z₁)‖ ≤
      distortionPhi K (r * ‖(z₁ - z₂) / ((r : ℂ) ^ 2 - starRingEnd ℂ z₂ * z₁)‖) := by
  obtain ⟨hf, hsub⟩ := lv23_isKQC hw hwD
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  -- `g(ζ) = w(rζ)/R` is a `K`-quasiconformal mapping of the unit disc into itself
  have hc₁ : LiZhongQC.IsConformalOnto (fun ζ : ℂ => (r : ℂ) * ζ) unitDisc
      ((fun ζ : ℂ => (r : ℂ) * ζ) '' unitDisc) :=
    ⟨(differentiable_id.const_mul _).differentiableOn, fun a _ b _ h => mul_left_cancel₀ hr' h, rfl⟩
  have hc₂ : LiZhongQC.IsConformalOnto (fun v : ℂ => v / (R : ℂ)) (Metric.ball 0 R)
      ((fun v : ℂ => v / (R : ℂ)) '' Metric.ball 0 R) :=
    ⟨(differentiable_id.div_const _).differentiableOn, fun a _ b _ h => (div_left_inj' hR').1 h, rfl⟩
  have hm₁ : (fun ζ : ℂ => (r : ℂ) * ζ) '' unitDisc ⊆ Metric.ball 0 r := by
    rintro _ ⟨ζ, hζ, rfl⟩
    refine mem_ball_zero_iff.2 ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_lt_of_lt_one_right hr (mem_ball_zero_iff.1 hζ)
  have hk₁ := LiZhongQC.thm7_1_comp (LiZhongQC.isKQC_one_of_conformal Metric.isOpen_ball hc₁) hf hm₁
  have hm₂ : (finiteMap w ∘ fun ζ : ℂ => (r : ℂ) * ζ) '' unitDisc ⊆ Metric.ball 0 R := by
    rw [image_comp]
    exact (image_mono hm₁).trans hsub
  have hk₂ := LiZhongQC.thm7_1_comp hk₁ (LiZhongQC.isKQC_one_of_conformal Metric.isOpen_ball hc₂) hm₂
  rw [one_mul, mul_one] at hk₂
  have himg : ((fun v : ℂ => v / (R : ℂ)) ∘ (finiteMap w ∘ fun ζ : ℂ => (r : ℂ) * ζ)) '' unitDisc ⊆
      unitDisc := by
    rw [image_comp]
    refine (image_mono hm₂).trans ?_
    rintro _ ⟨v, hv, rfl⟩
    refine mem_ball_zero_iff.2 ?_
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_lt_one hR]
    exact mem_ball_zero_iff.1 hv
  -- (3.9) for `g` at `zᵢ/r`
  have hζ : ∀ z : ℂ, ‖z‖ < r → z / (r : ℂ) ∈ unitDisc := fun z hz => by
    refine mem_ball_zero_iff.2 ?_
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_lt_one hr]
    exact hz
  have key := lv23_hyp ⟨hk₂, himg⟩ (hζ z₁ h₁) (hζ z₂ h₂)
  have e : ∀ z : ℂ, (r : ℂ) * (z / (r : ℂ)) = z := fun z => mul_div_cancel₀ z hr'
  simp only [Function.comp_apply, e] at key
  have ha : ‖finiteMap w z₁‖ < R :=
    mem_ball_zero_iff.1 (hsub (mem_image_of_mem _ (mem_ball_zero_iff.2 h₁)))
  have hb : ‖finiteMap w z₂‖ < R :=
    mem_ball_zero_iff.1 (hsub (mem_image_of_mem _ (mem_ball_zero_iff.2 h₂)))
  rw [lv23_scale hR ha hb, lv23_scale hr h₁ h₂] at key
  exact key

/-! ## §3.4 Distortion of euclidean distance under normalized mappings -/

/-- **Theorem 3.2** (Ch. II §3.4, Mori), the bound. Let `w` be a `K`-quasiconformal mapping of the unit disc onto
itself, normalized by `w(0) = 0`. Then for every pair of points `z₁, z₂` with `|z₁| ≤ 1`, `|z₂| ≤ 1`,
`|w(z₁) - w(z₂)| ≤ 16 |z₁ - z₂|^{1/K}` (3.14).
Modelling: on the unit circle `w` means its extension to a homeomorphism `W` of the closed disc (Ch. I §8.2; the
extension exists and is unique); the statement is made for every such `W`. -/
theorem thm2_3_2_i {w W : ExtPlane → ExtPlane} {K : ℝ} (hw : IsKQuasiconformal w (toExt unitDisc) K)
    (hwD : w '' toExt unitDisc = toExt unitDisc) (hw0 : w ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane))
    (hW : EqOn W w (toExt unitDisc)) (hWc : IsHomeoOn W (closure (toExt unitDisc)) (closure (toExt unitDisc)))
    {z₁ z₂ : ℂ} (h₁ : ‖z₁‖ ≤ 1) (h₂ : ‖z₂‖ ≤ 1) :
    ‖finiteMap W z₁ - finiteMap W z₂‖ ≤ 16 * ‖z₁ - z₂‖ ^ (1 / K) := by
  obtain ⟨hf, hsub⟩ := lv23_isKQC hw hwD.subset
  have honto : finiteMap w '' unitDisc = unitDisc := by
    refine hsub.antisymm fun v hv => ?_
    have hv' : (v : ExtPlane) ∈ w '' toExt unitDisc := by
      rw [hwD]
      exact ⟨v, hv, rfl⟩
    obtain ⟨_, ⟨z, hz, rfl⟩, hze⟩ := hv'
    refine ⟨z, hz, ?_⟩
    show finiteValue (w z) = v
    rw [hze]
    rfl
  have hf0 : finiteMap w 0 = 0 := by
    show finiteValue (w ((0 : ℂ) : ExtPlane)) = 0
    rw [hw0]
    rfl
  have hK : 1 ≤ K := hf.2.1
  have hK0 : 0 < 1 / K := one_div_pos.2 (by linarith)
  -- `finiteMap W` is continuous on the closed disc
  have hbd : Bornology.IsBounded unitDisc := Metric.isBounded_ball
  have hcl : closure (toExt unitDisc) = toExt (Metric.closedBall 0 1) := by
    rw [LiZhongQC.closure_toExt_of_isBounded hbd]
    congr 1
    exact closure_ball 0 one_ne_zero
  have hWin : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, W z = ((finiteMap W z : ℂ) : ExtPlane) := fun z hz => by
    have hz' : (z : ExtPlane) ∈ closure (toExt unitDisc) := by
      rw [hcl]
      exact ⟨z, hz, rfl⟩
    have h1 : W z ∈ closure (toExt unitDisc) := by
      rw [← hWc.2.2.1]
      exact mem_image_of_mem W hz'
    rw [hcl] at h1
    obtain ⟨v, -, hve⟩ := h1
    show W z = ((finiteValue (W z) : ℂ) : ExtPlane)
    rw [← hve]
    rfl
  have hFc : ContinuousOn (finiteMap W) (Metric.closedBall 0 1) := by
    rw [OnePoint.isOpenEmbedding_coe.toIsEmbedding.toIsInducing.continuousOn_iff]
    refine (hWc.1.comp OnePoint.continuous_coe.continuousOn fun z hz => ?_).congr fun z hz => (hWin z hz).symm
    rw [hcl]
    exact ⟨z, hz, rfl⟩
  -- the bound inside (Mori, `LiZhongQC.thm15_2_mori`)
  have hin : ∀ z ∈ unitDisc, finiteMap W z = finiteMap w z := fun z hz => by
    show finiteValue (W z) = finiteValue (w z)
    rw [hW ⟨z, hz, rfl⟩]
  have hopen : ∀ ζ₁ ∈ unitDisc, ∀ ζ₂ ∈ unitDisc,
      ‖finiteMap W ζ₁ - finiteMap W ζ₂‖ ≤ 16 * ‖ζ₁ - ζ₂‖ ^ (1 / K) := fun ζ₁ hζ₁ ζ₂ hζ₂ => by
    rw [hin ζ₁ hζ₁, hin ζ₂ hζ₂]
    rcases eq_or_ne ζ₁ ζ₂ with rfl | hne
    · simp only [sub_self, norm_zero]
      positivity
    · exact (LiZhongQC.thm15_2_mori hf honto hf0 hζ₁ hζ₂ hne).le
  -- the closed disc: the limit `t → 1⁻` at `t z₁`, `t z₂`
  have htz : ∀ z : ℂ, ‖z‖ ≤ 1 → ∀ t : ℝ, 0 ≤ t → t < 1 → (t : ℂ) * z ∈ unitDisc := fun z hz t ht0 ht1 => by
    refine mem_ball_zero_iff.2 ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    nlinarith [norm_nonneg z]
  have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT one_pos
  have hlim : ∀ z : ℂ, ‖z‖ ≤ 1 →
      Tendsto (fun t : ℝ => finiteMap W ((t : ℂ) * z)) (𝓝[<] 1) (𝓝 (finiteMap W z)) := fun z hz => by
    have h0 : Tendsto (fun t : ℝ => (t : ℂ) * z) (𝓝 1) (𝓝 z) := by
      have hc : Continuous (fun t : ℝ => (t : ℂ) * z) := Complex.continuous_ofReal.mul continuous_const
      simpa using hc.tendsto 1
    have h1 : Tendsto (fun t : ℝ => (t : ℂ) * z) (𝓝[<] 1) (𝓝[Metric.closedBall 0 1] z) := by
      refine tendsto_nhdsWithin_iff.2 ⟨h0.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [hev] with t ht
      exact mem_closedBall_zero_iff.2 (mem_ball_zero_iff.1 (htz z hz t ht.1.le ht.2)).le
    exact (hFc z (mem_closedBall_zero_iff.2 hz)).tendsto.comp h1
  have hRHS : Tendsto (fun t : ℝ => 16 * ‖(t : ℂ) * z₁ - (t : ℂ) * z₂‖ ^ (1 / K)) (𝓝[<] 1)
      (𝓝 (16 * ‖z₁ - z₂‖ ^ (1 / K))) := by
    have hc : Continuous (fun t : ℝ => 16 * ‖(t : ℂ) * z₁ - (t : ℂ) * z₂‖ ^ (1 / K)) :=
      continuous_const.mul ((((Complex.continuous_ofReal.mul continuous_const).sub
        (Complex.continuous_ofReal.mul continuous_const)).norm).rpow_const fun _ => Or.inr hK0.le)
    have := hc.tendsto 1
    simp only [Complex.ofReal_one, one_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto (((hlim z₁ h₁).sub (hlim z₂ h₂)).norm) hRHS ?_
  filter_upwards [hev] with t ht
  exact hopen _ (htz z₁ h₁ t ht.1.le ht.2) _ (htz z₂ h₂ t ht.1.le ht.2)

/-- **Theorem 3.2** (Ch. II §3.4, Mori), sharpness. The number `16` in (3.14) cannot be replaced by any smaller bound
if the inequality is to hold for all `K`: for every `c < 16` there are a `K`, a mapping `w` as in Theorem 3.2 with
its extension `W` to the closed disc, and points `|z₁|, |z₂| ≤ 1` with `|W(z₁) - W(z₂)| > c |z₁ - z₂|^{1/K}`. -/
theorem thm2_3_2_ii {c : ℝ} (hc : c < 16) :
    ∃ (K : ℝ) (w W : ExtPlane → ExtPlane) (z₁ z₂ : ℂ), IsKQuasiconformal w (toExt unitDisc) K ∧
      w '' toExt unitDisc = toExt unitDisc ∧ w ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧
      EqOn W w (toExt unitDisc) ∧ IsHomeoOn W (closure (toExt unitDisc)) (closure (toExt unitDisc)) ∧
      ‖z₁‖ ≤ 1 ∧ ‖z₂‖ ≤ 1 ∧ c * ‖z₁ - z₂‖ ^ (1 / K) < ‖finiteMap W z₁ - finiteMap W z₂‖ := by
  sorry

/-- **Formula (3.18)** (Ch. II §3.4, Remark). Let `w` be as in Theorem 3.2, extended to the homeomorphism `W` of the
closed disc. If `z₁` and `z₂` lie on the boundary of the unit disc, the constant `16` in (3.14) can be replaced by
`16^{1 - 1/K}`: `|w(z₁) - w(z₂)| ≤ 16^{1 - 1/K} |z₁ - z₂|^{1/K}`. -/
theorem eq2_3_18 {w W : ExtPlane → ExtPlane} {K : ℝ} (hw : IsKQuasiconformal w (toExt unitDisc) K)
    (hwD : w '' toExt unitDisc = toExt unitDisc) (hw0 : w ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane))
    (hW : EqOn W w (toExt unitDisc)) (hWc : IsHomeoOn W (closure (toExt unitDisc)) (closure (toExt unitDisc)))
    {z₁ z₂ : ℂ} (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) :
    ‖finiteMap W z₁ - finiteMap W z₂‖ ≤ (16 : ℝ) ^ (1 - 1 / K) * ‖z₁ - z₂‖ ^ (1 / K) := by
  sorry

end LehtoVirtanen1973
