import References.GardinerLakic2000.Ch16.S06_ZygmundSpaces

/-!
# Gardiner–Lakic 2000, Ch. 16 §16.7 The Hilbert transform

Source `teichmuller.txt`, lines 12536–12599 (Chapter 16, §16.7).

* Formula (16.22) (the kernel `R(x, ζ) = x(x − 1)/(ζ(ζ − 1)(ζ − x))`, l. 12551) — `kernelR`
* Formula (16.21) (the representation `V(x) = −(1/π) ∬ μ(ζ) R(x, ζ)`, l. 12541) — `IsKernelRepr`
* Formula (16.24) (the Hilbert transform as the principal value of `(1/π) ∫ V(ξ) R(x, ξ) dξ`, l. 12563; it differs
  from (16.23) by a linear polynomial) — `hilbertPV`
* Formula (16.26) (`μ̃ = −iμ` on `ℍ`, `+iμ` on `ℍ*`, l. 12582) — `hilbertLift`
* Definition (the representative normalized to vanish at `0`, `1`, `∞`, l. 12537; used in Theorem 7, §18.3, §18.4) —
  `zInfCoeff`, `zNormalize`
* Formula (16.27) (l. 12590) — `eq16_27`
* Theorem 7 (l. 12596) — `thm16_7`

Not items: (16.23) (the classical form, the same class modulo linear polynomials); (16.25) (Stokes, the derivation of
(16.27)); the `C^{1+α}` remark (l. 12593) and the Remark (Kerckhoff, Nag–Verjovsky, l. 12598). Near misses:
`LiZhongQC.hilbertH` (the plane Beurling transform), `GarnettMarshall2005.conjugateFunction` (on `∂𝔻`). The printed
(16.26) has "`ℍ*`" in both cases; GL1:5202 has `ℍ` and `ℍ*` [OCR]. Modelling [reading, E0.4]: `Z`, `Z₀` on `ℝ̄` are
batch A's `zCrSet extRealLine` (bounded cross-ratio norm, equivalent to (16.15), Exercise 1) and
`HasVanishingCrDistortion extRealLine`, for real-valued `V` on `ℝ`; "preserves" is modulo quadratic polynomials.
Theorem 7's "the almost complex structures are given by `H`" is read as (16.27) (`H` lifts to `μ ↦ μ̃`, which is
multiplication by `−i` on the Beltrami differentials of `ℍ`) together with `H² = −1` modulo quadratic polynomials;
the identification with the complex structures of `T(Δ)`, `T₀(Δ)`, `AT(Δ)` is not captured beyond that.
`H` acts on the representative `zNormalize V` normalized to vanish at `0`, `1`, `∞` (l. 12537); `hilbertPV` and
`hilbertLift` are (16.24), (16.26) as printed. The kernel `R(x, ξ)` has non-integrable poles at `ξ = 0, 1`, so
`hilbertPV` of a field not vanishing there is the junk `0` [CORRECTION, `thm16_7`]. The book's kernel `1/(ξ − x)`
((16.23), called classical there) is minus the standard one, for which `Im F = H(Re F)` when `F` is holomorphic in `ℍ`;
§18.3, §18.4 use the standard sign [CORRECTION there].
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (extRealLine upperHalf lowerHalf)

/-- **Formula (16.22)** (§16.7, l. 12551). `R(x, ζ) = x(x − 1)/(ζ(ζ − 1)(ζ − x))`. -/
def kernelR (x ζ : ℂ) : ℂ := x * (x - 1) / (ζ * (ζ - 1) * (ζ - x))

/-- **Formula (16.21)** (§16.7, l. 12541). `V(x) = −(1/π) ∬_ℂ μ(ζ) R(x, ζ) dξ dη` on `ℝ`, with `μ ∈ L∞(ℂ)` symmetric,
`μ(z̄) = conj μ(z)`. -/
def IsKernelRepr (V μ : ℂ → ℂ) : Prop :=
  (∃ k : ℝ, LiZhongQC.IsBeltramiCoeff μ univ k) ∧ (∀ z, μ (conj z) = conj (μ z)) ∧
    ∀ x : ℝ, V x = -(1 / π) * ∫ ζ, μ ζ * kernelR x ζ

/-- **Formula (16.24)** (§16.7, l. 12563). `HV(x) = p.v. (1/π) ∫ V(ξ) {1/(ξ − x) − x/(ξ − 1) + (x − 1)/ξ} dξ`, the
principal value at `ξ = x`. -/
def hilbertPV (V : ℂ → ℂ) (x : ℝ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε => (1 / π) * ∫ ξ in {ξ : ℝ | ε < |ξ - x|}, V ξ * kernelR x ξ

/-- **Formula (16.26)** (§16.7, l. 12582). `μ̃ = −iμ` on `ℍ` and `+iμ` on `ℍ*`. -/
def hilbertLift (μ : ℂ → ℂ) (z : ℂ) : ℂ := if 0 < z.im then -I * μ z else if z.im < 0 then I * μ z else 0

/-- Helper (§16.7, l. 12537). The coefficient `c = lim_{x → ±∞} V(x)/x²` of `V` at `∞` (junk: `0` when `V(x)/x²` has
no limit, which does not happen on `Z`). -/
def zInfCoeff (V : ℂ → ℂ) : ℂ := limUnder (cocompact ℝ) fun x : ℝ => V x / (x : ℂ) ^ 2

/-- Helper (§16.7, l. 12537). The representative of `V` modulo quadratic polynomials normalized to vanish at `0`, `1`
and `∞`: `V(z) − V(0) − (V(1) − V(0)) z − c (z² − z)`, `c = zInfCoeff V`. `H` is applied to it: `hilbertPV` of a field
not vanishing at `0`, `1` is the junk `0` (the kernel's poles there). -/
def zNormalize (V : ℂ → ℂ) : ℂ → ℂ := fun z => V z - V 0 - (V 1 - V 0) * z - zInfCoeff V * (z ^ 2 - z)

/-- Helper for `eq16_27` (§16.7). The kernel (16.22) is the project's first-variation kernel `LiZhongQC.ahKer`. -/
theorem gl16_kernelR_eq : kernelR = LiZhongQC.ahKer := rfl

/-- Helper for `eq16_27` (§16.7, P1a). The pointwise scaling identity `K_p(pw) = −K_{1/p}(w)` (also at the poles,
where both sides are `0`). -/
theorem gl16_ahKer_mul_eq {p : ℂ} (hp : p ≠ 0) (w : ℂ) :
    LiZhongQC.ahKer p (p * w) = -LiZhongQC.ahKer p⁻¹ w := by
  unfold LiZhongQC.ahKer
  have e1 : p * w - 1 = p * (w - p⁻¹) := by field_simp
  have e2 : p * w - p = p * (w - 1) := by ring
  rw [e1, e2]
  simp only [div_eq_mul_inv, mul_inv]
  have hp' : p⁻¹ - 1 = -(p - 1) * p⁻¹ := by
    field_simp
    ring
  rw [hp']
  field_simp

/-- Helper for `eq16_27` (§16.7, P1a). Scaling `ζ = p w`: `∬ |K_p| = |p|² ∬ |K_{1/p}|`, since `K_p(pw) = −K_{1/p}(w)`.
-/
theorem gl16_ahKer_lintegral_scale {p : ℂ} (hp : p ≠ 0) :
    ∫⁻ ζ, ‖LiZhongQC.ahKer p ζ‖ₑ = ENNReal.ofReal (‖p‖ ^ 2) * ∫⁻ ζ, ‖LiZhongQC.ahKer p⁻¹ ζ‖ₑ := by
  set L : ℂ →ₗ[ℝ] ℂ := Algebra.lmul ℝ ℂ p with hL
  have hdet : LinearMap.det L = ‖p‖ ^ 2 := by
    rw [hL, ← Algebra.norm_apply, Algebra.norm_complex_eq]
    simp [Complex.normSq_eq_norm_sq]
  have hdet0 : LinearMap.det L ≠ 0 := by
    rw [hdet]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 hp)
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure ℂ)) hdet0
  have hLc : Measurable L := L.continuous_of_finiteDimensional.measurable
  have hmeas : Measurable fun ζ => ‖LiZhongQC.ahKer p ζ‖ₑ := (LiZhongQC.ahK_measurable p).enorm
  -- `∫⁻ ‖K_p(p w)‖ = |det|⁻¹ ∫⁻ ‖K_p‖`
  have key : ∫⁻ w, ‖LiZhongQC.ahKer p (L w)‖ₑ =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| * ∫⁻ ζ, ‖LiZhongQC.ahKer p ζ‖ₑ := by
    rw [← lintegral_map hmeas hLc, hmap, lintegral_smul_measure]
    rfl
  have hLw : ∀ w, L w = p * w := fun w => rfl
  simp only [hLw, gl16_ahKer_mul_eq hp, enorm_neg] at key
  rw [hdet, abs_of_pos (by positivity : (0 : ℝ) < (‖p‖ ^ 2)⁻¹)] at key
  rw [key, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    mul_inv_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.2 hp)), ENNReal.ofReal_one, one_mul]

/-- Helper for `eq16_27` (§16.7, P1b). `K₁ = 0`. -/
theorem gl16_ahKer_one (ζ : ℂ) : LiZhongQC.ahKer 1 ζ = 0 := by
  simp [LiZhongQC.ahKer]

/-- Helper for `eq16_27` (§16.7, P1b). Near the poles: for `‖p‖ ≤ 2`,
`∬ |K_p| ≤ A √|p|` and `∬ |K_p| ≤ A √|p − 1|` (S13's `ahK_lintegral_sub_le` at `w = 0` and `w = 1`). -/
theorem gl16_ahKer_lintegral_le_small :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p : ℂ, ‖p‖ ≤ 2 →
      ∫⁻ ζ, ‖LiZhongQC.ahKer p ζ‖ₑ ≤ ENNReal.ofReal (A * min √‖p‖ √‖p - 1‖) := by
  obtain ⟨C, hC0, hC⟩ := LiZhongQC.ahK_lintegral_sub_le (R := 2) (by norm_num)
  have hπ := Real.pi_pos
  refine ⟨C + (C + 32 * π) * 2, by positivity, fun p hp => ?_⟩
  -- a bound `C √d + (C + 32π) d ≤ (C + 2(C + 32π)) √d` for `0 ≤ d ≤ 4`
  have hsq : ∀ d : ℝ, 0 ≤ d → d ≤ 4 → C * √d + (C + 32 * π) * d ≤ (C + (C + 32 * π) * 2) * √d := by
    intro d hd0 hd4
    have h1 : d = √d * √d := (Real.mul_self_sqrt hd0).symm
    have h2 : √d ≤ 2 := by
      rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hd4
    have h3 : 0 ≤ √d := Real.sqrt_nonneg d
    have h5 : d ≤ 2 * √d := by nlinarith [mul_nonneg (sub_nonneg.2 h2) h3]
    have h4 : (C + 32 * π) * d ≤ (C + 32 * π) * 2 * √d := by
      have : 0 ≤ C + 32 * π := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h5 this]
    linarith
  -- the two bounds
  have hb0 : ∫⁻ ζ, ‖LiZhongQC.ahKer p ζ‖ₑ ≤ ENNReal.ofReal ((C + (C + 32 * π) * 2) * √‖p‖) := by
    by_cases hp0 : p = 0
    · subst hp0
      simp [LiZhongQC.ahK_ker_zero]
    have h := hC p 0 hp (by simp) hp0
    simp only [LiZhongQC.ahK_ker_zero, sub_zero] at h
    exact h.trans (ENNReal.ofReal_le_ofReal (hsq _ (norm_nonneg _) (by linarith)))
  have hb1 : ∫⁻ ζ, ‖LiZhongQC.ahKer p ζ‖ₑ ≤ ENNReal.ofReal ((C + (C + 32 * π) * 2) * √‖p - 1‖) := by
    by_cases hp1 : p = 1
    · subst hp1
      simp [gl16_ahKer_one]
    have h := hC p 1 hp (by norm_num) hp1
    simp only [gl16_ahKer_one, sub_zero] at h
    have hd : ‖p - 1‖ ≤ 4 := by
      have := norm_sub_le p 1
      rw [norm_one] at this
      linarith
    exact h.trans (ENNReal.ofReal_le_ofReal (hsq _ (norm_nonneg _) hd))
  rcases le_total √‖p‖ √‖p - 1‖ with h | h
  · rw [min_eq_left h]
    exact hb0
  · rw [min_eq_right h]
    exact hb1

/-- Helper for `eq16_27` (§16.7, P1b). A global `L¹` bound for the kernel:
`∬ |K_p| ≤ C min(√|p|, √|p − 1|) (1 + |p|)`. For bounded `p` it is S13's `ahK_lintegral_sub_le` at `w = 0` and
`w = 1` (`K₀ = K₁ = 0`); for large `p` it is the scaling P1a. -/
theorem gl16_ahKer_lintegral_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℂ,
      ∫⁻ ζ, ‖LiZhongQC.ahKer p ζ‖ₑ ≤ ENNReal.ofReal (C * min √‖p‖ √‖p - 1‖ * (1 + ‖p‖)) := by
  obtain ⟨A, hA0, hA⟩ := gl16_ahKer_lintegral_le_small
  refine ⟨2 * A, by positivity, fun p => ?_⟩
  have hm0 : 0 ≤ min √‖p‖ √‖p - 1‖ := le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rcases le_or_gt ‖p‖ 2 with hp | hp
  · refine (hA p hp).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : 1 ≤ 1 + ‖p‖ := by linarith [norm_nonneg p]
    nlinarith [mul_nonneg hA0 hm0]
  · -- large `p`: the scaling P1a and the small bound at `1/p`
    have hp0 : p ≠ 0 := by
      intro h
      rw [h, norm_zero] at hp
      linarith
    have hpn : 0 < ‖p‖ := norm_pos_iff.2 hp0
    have hinv : ‖p⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      exact (inv_le_one_of_one_le₀ (by linarith)).trans (by norm_num)
    rw [gl16_ahKer_lintegral_scale hp0]
    refine (mul_le_mul' le_rfl (hA p⁻¹ hinv)).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    -- `‖p‖² · A min(√|1/p|, …) ≤ A ‖p‖^{3/2} ≤ 2A min(√|p|, √|p − 1|)(1 + ‖p‖)`
    have hs : min √‖p⁻¹‖ √‖p⁻¹ - 1‖ ≤ √‖p⁻¹‖ := min_le_left _ _
    have hsp : √‖p⁻¹‖ * √‖p‖ = 1 := by
      rw [← Real.sqrt_mul (norm_nonneg _), norm_inv, inv_mul_cancel₀ hpn.ne', Real.sqrt_one]
    have hq : ‖p‖ / 2 ≤ ‖p - 1‖ := by
      have := norm_sub_norm_le p 1
      rw [norm_one] at this
      linarith
    have hm : √(‖p‖ / 2) ≤ min √‖p‖ √‖p - 1‖ :=
      le_min (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_le_sqrt hq)
    have hsq2 : √(‖p‖ / 2) * √2 = √‖p‖ := by
      rw [← Real.sqrt_mul (by positivity), div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    have h2 : √2 ≤ 2 := by
      rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hspos : 0 ≤ √‖p‖ := Real.sqrt_nonneg _
    have hsp2 : 0 ≤ √(‖p‖ / 2) := Real.sqrt_nonneg _
    have hpp : ‖p‖ = √‖p‖ * √‖p‖ := (Real.mul_self_sqrt (norm_nonneg p)).symm
    -- LHS ≤ ‖p‖² A √|1/p| = A ‖p‖ √‖p‖
    have hL : ‖p‖ ^ 2 * (A * min √‖p⁻¹‖ √‖p⁻¹ - 1‖) ≤ A * ‖p‖ * √‖p‖ := by
      have e : ‖p‖ ^ 2 * √‖p⁻¹‖ = ‖p‖ * √‖p‖ := by
        have : ‖p‖ ^ 2 * √‖p⁻¹‖ = ‖p‖ * (√‖p‖ * √‖p‖) * √‖p⁻¹‖ := by rw [← hpp]; ring
        rw [this]
        calc ‖p‖ * (√‖p‖ * √‖p‖) * √‖p⁻¹‖ = ‖p‖ * √‖p‖ * (√‖p⁻¹‖ * √‖p‖) := by ring
          _ = ‖p‖ * √‖p‖ := by rw [hsp, mul_one]
      calc ‖p‖ ^ 2 * (A * min √‖p⁻¹‖ √‖p⁻¹ - 1‖) ≤ ‖p‖ ^ 2 * (A * √‖p⁻¹‖) := by
            have := mul_le_mul_of_nonneg_left hs hA0
            exact mul_le_mul_of_nonneg_left this (by positivity)
        _ = A * (‖p‖ ^ 2 * √‖p⁻¹‖) := by ring
        _ = A * ‖p‖ * √‖p‖ := by rw [e]; ring
    refine hL.trans ?_
    -- `A ‖p‖ √‖p‖ = A ‖p‖ √2 √(‖p‖/2) ≤ 2A ‖p‖ min(…) ≤ 2A min(…)(1 + ‖p‖)`
    have h3 : √‖p‖ ≤ 2 * min √‖p‖ √‖p - 1‖ := by
      have := mul_le_mul_of_nonneg_left h2 hsp2
      linarith [hsq2, this, hm]
    calc A * ‖p‖ * √‖p‖ ≤ A * ‖p‖ * (2 * min √‖p‖ √‖p - 1‖) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ 2 * A * min √‖p‖ √‖p - 1‖ * (1 + ‖p‖) := by nlinarith [mul_nonneg hA0 hm0]

/-- Helper for `eq16_27` (§16.7, P1c). `G_x` through first-variation kernels: for `u ≠ 0`, `x ± u ∉ {0, 1}` and
`Im ζ ≠ 0`, `G_x(u, ζ) = (c₊ K_{x+u}(ζ) − c₋ K_{x−u}(ζ))/u` with `c± = x(x − 1)/(p±(p± − 1))`, `p± = x ± u`. -/
theorem gl16_G_eq_ahKer {x u : ℝ} {ζ : ℂ} (hζ : ζ.im ≠ 0) (hu : u ≠ 0) (h₁ : x + u ≠ 0) (h₂ : x + u ≠ 1)
    (h₃ : x - u ≠ 0) (h₄ : x - u ≠ 1) :
    (x : ℂ) * (x - 1) / (ζ * (ζ - 1)) * (2 / ((ζ - x) ^ 2 - (u : ℂ) ^ 2)) =
      (1 / (u : ℂ)) * ((x : ℂ) * (x - 1) / (((x + u : ℝ) : ℂ) * (((x + u : ℝ) : ℂ) - 1)) *
          LiZhongQC.ahKer ((x + u : ℝ) : ℂ) ζ -
        (x : ℂ) * (x - 1) / (((x - u : ℝ) : ℂ) * (((x - u : ℝ) : ℂ) - 1)) * LiZhongQC.ahKer ((x - u : ℝ) : ℂ) ζ) := by
  have him : ∀ r : ℝ, ζ - (r : ℂ) ≠ 0 := fun r h => hζ (by simpa using congrArg Complex.im h)
  have hz0 : ζ ≠ 0 := fun h => hζ (by rw [h, Complex.zero_im])
  have hz1 : ζ - 1 ≠ 0 := by simpa using him 1
  have hzp := him (x + u)
  have hzm := him (x - u)
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  have hp0 : ((x + u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h₁
  have hp1 : ((x + u : ℝ) : ℂ) - 1 ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact_mod_cast sub_ne_zero.2 h₂
  have hm0 : ((x - u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h₃
  have hm1 : ((x - u : ℝ) : ℂ) - 1 ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact_mod_cast sub_ne_zero.2 h₄
  have hD : (ζ - x) ^ 2 - (u : ℂ) ^ 2 = (ζ - ((x + u : ℝ) : ℂ)) * (ζ - ((x - u : ℝ) : ℂ)) := by
    push_cast
    ring
  unfold LiZhongQC.ahKer
  rw [hD]
  field_simp
  push_cast
  ring

/-- Helper for `eq16_27` (§16.7, P1c). For real `p ∉ {0, 1}`:
`min(√|p|, √|p − 1|)(1 + |p|)/(|p| |p − 1|) ≤ 3(|p|^{−1/2} + |p − 1|^{−1/2})`. -/
theorem gl16_min_sqrt_div_le {p : ℝ} (h0 : p ≠ 0) (h1 : p ≠ 1) :
    min √‖p‖ √‖p - 1‖ * (1 + ‖p‖) / (‖p‖ * ‖p - 1‖) ≤ 3 * (‖p‖ ^ (-(1 / 2 : ℝ)) + ‖p - 1‖ ^ (-(1 / 2 : ℝ))) := by
  have ha : 0 < ‖p‖ := norm_pos_iff.2 h0
  have hb : 0 < ‖p - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 h1)
  have hab : 1 ≤ ‖p‖ + ‖p - 1‖ := by
    have := norm_sub_le p (p - 1)
    rw [show p - (p - 1) = 1 by ring, norm_one] at this
    linarith
  have hra : ‖p‖ ^ (-(1 / 2 : ℝ)) = (√‖p‖)⁻¹ := by
    rw [Real.rpow_neg ha.le, Real.sqrt_eq_rpow]
  have hrb : ‖p - 1‖ ^ (-(1 / 2 : ℝ)) = (√‖p - 1‖)⁻¹ := by
    rw [Real.rpow_neg hb.le, Real.sqrt_eq_rpow]
  rw [hra, hrb]
  have hsa : 0 < √‖p‖ := Real.sqrt_pos.2 ha
  have hsb : 0 < √‖p - 1‖ := Real.sqrt_pos.2 hb
  have hsa2 : √‖p‖ * √‖p‖ = ‖p‖ := Real.mul_self_sqrt ha.le
  have hsb2 : √‖p - 1‖ * √‖p - 1‖ = ‖p - 1‖ := Real.mul_self_sqrt hb.le
  have hpos : 0 < ‖p‖ * ‖p - 1‖ := mul_pos ha hb
  rw [div_le_iff₀ hpos]
  have hia : 0 < (√‖p‖)⁻¹ := inv_pos.2 hsa
  have hib : 0 < (√‖p - 1‖)⁻¹ := inv_pos.2 hsb
  rcases le_total ‖p‖ ‖p - 1‖ with hle | hle
  · -- `|p| ≤ |p − 1|`: then `|p − 1| ≥ 1/2` and `1 + |p| ≤ 3|p − 1|`
    have hm : min √‖p‖ √‖p - 1‖ = √‖p‖ := min_eq_left (Real.sqrt_le_sqrt hle)
    rw [hm]
    have h3 : 1 + ‖p‖ ≤ 3 * ‖p - 1‖ := by linarith
    -- `√a (1 + a) ≤ 3 √a b = 3 (√a)⁻¹ a b`
    have e : 3 * (√‖p‖)⁻¹ * (‖p‖ * ‖p - 1‖) = 3 * √‖p‖ * ‖p - 1‖ := by
      calc 3 * (√‖p‖)⁻¹ * (‖p‖ * ‖p - 1‖) = 3 * (√‖p‖)⁻¹ * ((√‖p‖ * √‖p‖) * ‖p - 1‖) := by rw [hsa2]
        _ = 3 * √‖p‖ * ‖p - 1‖ := by field_simp
    have h4 : √‖p‖ * (1 + ‖p‖) ≤ 3 * √‖p‖ * ‖p - 1‖ := by nlinarith
    have h5 : 0 ≤ 3 * (√‖p - 1‖)⁻¹ * (‖p‖ * ‖p - 1‖) := by positivity
    nlinarith
  · have hm : min √‖p‖ √‖p - 1‖ = √‖p - 1‖ := min_eq_right (Real.sqrt_le_sqrt hle)
    rw [hm]
    have h3 : 1 + ‖p‖ ≤ 3 * ‖p‖ := by linarith
    have e : 3 * (√‖p - 1‖)⁻¹ * (‖p‖ * ‖p - 1‖) = 3 * √‖p - 1‖ * ‖p‖ := by
      calc 3 * (√‖p - 1‖)⁻¹ * (‖p‖ * ‖p - 1‖) = 3 * (√‖p - 1‖)⁻¹ * (‖p‖ * (√‖p - 1‖ * √‖p - 1‖)) := by
            rw [hsb2]
        _ = 3 * √‖p - 1‖ * ‖p‖ := by field_simp
    have h4 : √‖p - 1‖ * (1 + ‖p‖) ≤ 3 * √‖p - 1‖ * ‖p‖ := by nlinarith
    have h5 : 0 ≤ 3 * (√‖p‖)⁻¹ * (‖p‖ * ‖p - 1‖) := by positivity
    nlinarith

/-- Helper for `eq16_27` (§16.7, P1c). The pointwise `enorm` form of the triangle inequality for a combination of
two kernels. -/
theorem gl16_enorm_comb_le (a b c K₁ K₂ : ℂ) :
    ‖a * (b * K₁ - c * K₂)‖ₑ ≤ ‖a‖ₑ * (‖b‖ₑ * ‖K₁‖ₑ + ‖c‖ₑ * ‖K₂‖ₑ) := by
  rw [enorm_mul]
  gcongr
  refine enorm_sub_le.trans ?_
  rw [enorm_mul, enorm_mul]

/-- Helper for `eq16_27` (§16.7, P1c). The general `u`-wise bound (no cancellation): for `u > 0`, `x ± u ∉ {0, 1}`,
`∬ |G_x(u, ·)| ≤ (A/u) Σ (|x ± u|^{−1/2} + |x ± u − 1|^{−1/2})` (P1b and `gl16_min_sqrt_div_le`). -/
theorem gl16_G_inner_le (x : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : ℝ, 0 < u → x + u ≠ 0 → x + u ≠ 1 → x - u ≠ 0 → x - u ≠ 1 →
      ∫⁻ ζ, ‖(x : ℂ) * (x - 1) / (ζ * (ζ - 1)) * (2 / ((ζ - x) ^ 2 - (u : ℂ) ^ 2))‖ₑ ≤
        ENNReal.ofReal (A / u * (‖x + u‖ ^ (-(1 / 2 : ℝ)) + ‖x + u - 1‖ ^ (-(1 / 2 : ℝ)) +
          (‖x - u‖ ^ (-(1 / 2 : ℝ)) + ‖x - u - 1‖ ^ (-(1 / 2 : ℝ))))) := by
  obtain ⟨C, hC0, hC⟩ := gl16_ahKer_lintegral_le
  refine ⟨3 * C * ‖x * (x - 1)‖, by positivity, fun u hu h₁ h₂ h₃ h₄ => ?_⟩
  have h0 : ∀ᵐ ζ : ℂ, ζ.im ≠ 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 LiZhongQC.gzE_volume_im_eq_zero] with ζ hζ
    exact hζ
  -- the coefficients `c± = x(x − 1)/(p±(p± − 1))`, a real number each
  set cp : ℂ := (x : ℂ) * (x - 1) / (((x + u : ℝ) : ℂ) * (((x + u : ℝ) : ℂ) - 1)) with hcp
  set cm : ℂ := (x : ℂ) * (x - 1) / (((x - u : ℝ) : ℂ) * (((x - u : ℝ) : ℂ) - 1)) with hcm
  have hrepr : (fun ζ => ‖(x : ℂ) * (x - 1) / (ζ * (ζ - 1)) * (2 / ((ζ - x) ^ 2 - (u : ℂ) ^ 2))‖ₑ) =ᵐ[volume]
      fun ζ => ‖(1 / (u : ℂ)) *
        (cp * LiZhongQC.ahKer ((x + u : ℝ) : ℂ) ζ - cm * LiZhongQC.ahKer ((x - u : ℝ) : ℂ) ζ)‖ₑ := by
    filter_upwards [h0] with ζ hζ
    rw [gl16_G_eq_ahKer hζ hu.ne' h₁ h₂ h₃ h₄]
  rw [lintegral_congr_ae hrepr]
  refine (lintegral_mono fun ζ => gl16_enorm_comb_le _ _ _ _ _).trans ?_
  rw [lintegral_const_mul' _ _ enorm_ne_top,
    lintegral_add_left' ((LiZhongQC.ahK_measurable _).enorm.aemeasurable.const_mul _),
    lintegral_const_mul' _ _ enorm_ne_top, lintegral_const_mul' _ _ enorm_ne_top]
  -- the norms of the real coefficients and of `1/u`
  have hnorm : ∀ r : ℝ, ‖((r : ℂ))‖ₑ = ENNReal.ofReal ‖r‖ := fun r => by
    rw [← ofReal_norm, Complex.norm_real]
  have hcpR : cp = ((x * (x - 1) / ((x + u) * (x + u - 1)) : ℝ) : ℂ) := by rw [hcp]; push_cast; ring
  have hcmR : cm = ((x * (x - 1) / ((x - u) * (x - u - 1)) : ℝ) : ℂ) := by rw [hcm]; push_cast; ring
  have huR : (1 / (u : ℂ)) = ((1 / u : ℝ) : ℂ) := by push_cast; ring
  rw [hcpR, hcmR, huR, hnorm, hnorm, hnorm]
  -- the kernel bounds (P1b), with `‖(p : ℂ)‖ = |p|`
  have hK : ∀ r : ℝ, ∫⁻ ζ, ‖LiZhongQC.ahKer (r : ℂ) ζ‖ₑ ≤ ENNReal.ofReal (C * min √‖r‖ √‖r - 1‖ * (1 + ‖r‖)) := by
    intro r
    have h := hC (r : ℂ)
    rwa [Complex.norm_real, show (r : ℂ) - 1 = ((r - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real] at h
  refine (mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl (hK _)) (mul_le_mul' le_rfl (hK _)))).trans ?_
  -- now everything is `ofReal` of nonnegative reals
  have hm0 : ∀ r : ℝ, 0 ≤ C * min √‖r‖ √‖r - 1‖ * (1 + ‖r‖) := fun r => by
    have := le_min (Real.sqrt_nonneg ‖r‖) (Real.sqrt_nonneg ‖r - 1‖)
    positivity
  rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_add
    (by positivity) (mul_nonneg (norm_nonneg _) (hm0 _)), ← ENNReal.ofReal_mul (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- the real inequality, term by term
  have key : ∀ r : ℝ, r ≠ 0 → r ≠ 1 →
      ‖x * (x - 1) / (r * (r - 1))‖ * (C * min √‖r‖ √‖r - 1‖ * (1 + ‖r‖)) ≤
        3 * C * ‖x * (x - 1)‖ * (‖r‖ ^ (-(1 / 2 : ℝ)) + ‖r - 1‖ ^ (-(1 / 2 : ℝ))) := by
    intro r hr0 hr1
    have h := gl16_min_sqrt_div_le hr0 hr1
    have hpos : 0 < ‖r‖ * ‖r - 1‖ := mul_pos (norm_pos_iff.2 hr0) (norm_pos_iff.2 (sub_ne_zero.2 hr1))
    rw [norm_div, norm_mul r]
    calc ‖x * (x - 1)‖ / (‖r‖ * ‖r - 1‖) * (C * min √‖r‖ √‖r - 1‖ * (1 + ‖r‖))
        = C * ‖x * (x - 1)‖ * (min √‖r‖ √‖r - 1‖ * (1 + ‖r‖) / (‖r‖ * ‖r - 1‖)) := by ring
      _ ≤ C * ‖x * (x - 1)‖ * (3 * (‖r‖ ^ (-(1 / 2 : ℝ)) + ‖r - 1‖ ^ (-(1 / 2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 3 * C * ‖x * (x - 1)‖ * (‖r‖ ^ (-(1 / 2 : ℝ)) + ‖r - 1‖ ^ (-(1 / 2 : ℝ))) := by ring
  have k1 := key (x + u) h₁ h₂
  have k2 := key (x - u) h₃ h₄
  have hu1 : ‖1 / u‖ = 1 / u := by rw [Real.norm_of_nonneg (by positivity)]
  rw [hu1]
  calc 1 / u * (‖x * (x - 1) / ((x + u) * (x + u - 1))‖ * (C * min √‖x + u‖ √‖x + u - 1‖ * (1 + ‖x + u‖)) +
        ‖x * (x - 1) / ((x - u) * (x - u - 1))‖ * (C * min √‖x - u‖ √‖x - u - 1‖ * (1 + ‖x - u‖)))
      ≤ 1 / u * (3 * C * ‖x * (x - 1)‖ * (‖x + u‖ ^ (-(1 / 2 : ℝ)) + ‖x + u - 1‖ ^ (-(1 / 2 : ℝ))) +
          3 * C * ‖x * (x - 1)‖ * (‖x - u‖ ^ (-(1 / 2 : ℝ)) + ‖x - u - 1‖ ^ (-(1 / 2 : ℝ)))) :=
        mul_le_mul_of_nonneg_left (add_le_add k1 k2) (by positivity)
    _ = 3 * C * ‖x * (x - 1)‖ / u * (‖x + u‖ ^ (-(1 / 2 : ℝ)) + ‖x + u - 1‖ ^ (-(1 / 2 : ℝ)) +
          (‖x - u‖ ^ (-(1 / 2 : ℝ)) + ‖x - u - 1‖ ^ (-(1 / 2 : ℝ)))) := by ring

/-- Helper for `eq16_27` (§16.7, P1c). The coefficients `c± = x(x−1)/(p±(p±−1))`, `p± = x ± u`, for small `u`:
`|c₊| ≤ 4` and `|c₊ − c₋| ≤ 32 u |2x − 1|/|x(x − 1)|` when `0 < u < min(|x|, |x − 1|)/2`. -/
theorem gl16_coef_small {x u : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hu : 0 < u) (hu₀ : u < min ‖x‖ ‖x - 1‖ / 2) :
    ‖x * (x - 1) / ((x + u) * (x + u - 1))‖ ≤ 4 ∧
      ‖x * (x - 1) / ((x + u) * (x + u - 1)) - x * (x - 1) / ((x - u) * (x - u - 1))‖ ≤
        32 * u * ‖2 * x - 1‖ / ‖x * (x - 1)‖ := by
  have ha : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hb : 0 < ‖x - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hx1)
  have hua : u < ‖x‖ / 2 := lt_of_lt_of_le hu₀ (by have := min_le_left ‖x‖ ‖x - 1‖; linarith)
  have hub : u < ‖x - 1‖ / 2 := lt_of_lt_of_le hu₀ (by have := min_le_right ‖x‖ ‖x - 1‖; linarith)
  -- `|x ± u| ≥ |x|/2`, `|x ± u − 1| ≥ |x − 1|/2`
  have hp : ∀ s : ℝ, |s| ≤ u → ‖x‖ / 2 ≤ ‖x + s‖ ∧ ‖x - 1‖ / 2 ≤ ‖x + s - 1‖ := by
    intro s hs
    have h1 := norm_sub_norm_le x (-s)
    have h2 := norm_sub_norm_le (x - 1) (-s)
    rw [sub_neg_eq_add, norm_neg, Real.norm_eq_abs s] at h1
    rw [show x - 1 - -s = x + s - 1 by ring, norm_neg, Real.norm_eq_abs s] at h2
    exact ⟨by linarith, by linarith⟩
  obtain ⟨hp1, hp2⟩ := hp u (by rw [abs_of_pos hu])
  obtain ⟨hm1, hm2⟩ := hp (-u) (by rw [abs_neg, abs_of_pos hu])
  rw [show x + -u = x - u by ring] at hm1 hm2
  have hP : 0 < ‖x + u‖ * ‖x + u - 1‖ := mul_pos (by linarith) (by linarith)
  have hM : 0 < ‖x - u‖ * ‖x - u - 1‖ := mul_pos (by linarith) (by linarith)
  have hP' : ‖x‖ * ‖x - 1‖ / 4 ≤ ‖x + u‖ * ‖x + u - 1‖ := by nlinarith
  have hM' : ‖x‖ * ‖x - 1‖ / 4 ≤ ‖x - u‖ * ‖x - u - 1‖ := by nlinarith
  have hxx : 0 < ‖x‖ * ‖x - 1‖ := mul_pos ha hb
  constructor
  · rw [norm_div, norm_mul, norm_mul, div_le_iff₀ hP]
    linarith
  · -- `c₊ − c₋ = x(x − 1)(p₋(p₋ − 1) − p₊(p₊ − 1))/(p₊(p₊−1)p₋(p₋−1))`, and the bracket is `−2u(2x − 1)`
    have hne1 : (x + u) * (x + u - 1) ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_mul]
      exact hP.ne'
    have hne2 : (x - u) * (x - u - 1) ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_mul]
      exact hM.ne'
    have e : x * (x - 1) / ((x + u) * (x + u - 1)) - x * (x - 1) / ((x - u) * (x - u - 1)) =
        x * (x - 1) * (-(2 * u) * (2 * x - 1)) / (((x + u) * (x + u - 1)) * ((x - u) * (x - u - 1))) := by
      rw [div_sub_div _ _ hne1 hne2]
      congr 1
      ring
    rw [e]
    simp only [norm_div, norm_mul, norm_neg, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      Real.norm_of_nonneg hu.le]
    have hprod : ‖x‖ * ‖x - 1‖ / 4 * (‖x‖ * ‖x - 1‖ / 4) ≤ ‖x + u‖ * ‖x + u - 1‖ * (‖x - u‖ * ‖x - u - 1‖) :=
      mul_le_mul hP' hM' (by positivity) hP.le
    have hden : 0 < ‖x + u‖ * ‖x + u - 1‖ * (‖x - u‖ * ‖x - u - 1‖) := mul_pos hP hM
    rw [div_le_div_iff₀ hden hxx]
    have h2x : 0 ≤ ‖2 * x - 1‖ := norm_nonneg _
    have hkey : ‖x‖ * ‖x - 1‖ * (2 * u * ‖2 * x - 1‖) * (‖x‖ * ‖x - 1‖) ≤
        32 * u * ‖2 * x - 1‖ * (‖x + u‖ * ‖x + u - 1‖ * (‖x - u‖ * ‖x - u - 1‖)) := by
      have h16 : (‖x‖ * ‖x - 1‖) * (‖x‖ * ‖x - 1‖) ≤ 16 * (‖x + u‖ * ‖x + u - 1‖ * (‖x - u‖ * ‖x - u - 1‖)) := by
        nlinarith
      have h0 : 0 ≤ 2 * u * ‖2 * x - 1‖ := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h16 h0]
    linarith

/-- Helper for `eq16_27` (§16.7, P1c). The `u`-wise bound near `u = 0`, by cancellation: for `x ∉ {0, 1}` and
`0 < u < min(|x|, |x − 1|)/2`, `∬ |G_x(u, ·)| ≤ A u^{−1/2} + B` (S13's difference estimate for `K_{x+u} − K_{x−u}`,
`gl16_coef_small`, P1b for `K_{x−u}`). -/
theorem gl16_G_inner_small {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ u : ℝ, 0 < u → u < min ‖x‖ ‖x - 1‖ / 2 →
      ∫⁻ ζ, ‖(x : ℂ) * (x - 1) / (ζ * (ζ - 1)) * (2 / ((ζ - x) ^ 2 - (u : ℂ) ^ 2))‖ₑ ≤
        ENNReal.ofReal (A * u ^ (-(1 / 2 : ℝ)) + B) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := LiZhongQC.ahK_lintegral_sub_le (R := 2 * ‖x‖ + 1) (by linarith [norm_nonneg x])
  obtain ⟨C, hC0, hC⟩ := gl16_ahKer_lintegral_le
  have hπ := Real.pi_pos
  set B₀ : ℝ := C * √(2 * ‖x‖ + 1) * (2 * ‖x‖ + 2) with hB₀
  have hB₀0 : 0 ≤ B₀ := by positivity
  have hxx : 0 < ‖x * (x - 1)‖ := by
    rw [norm_mul]
    exact mul_pos (norm_pos_iff.2 hx0) (norm_pos_iff.2 (sub_ne_zero.2 hx1))
  refine ⟨4 * C₁ * √2, 4 * (C₁ + 32 * π) * 2 + 32 * ‖2 * x - 1‖ / ‖x * (x - 1)‖ * B₀, by positivity, by positivity,
    fun u hu hu₀ => ?_⟩
  obtain ⟨hcp, hcd⟩ := gl16_coef_small hx0 hx1 hu hu₀
  have hua : u < ‖x‖ / 2 := lt_of_lt_of_le hu₀ (by have := min_le_left ‖x‖ ‖x - 1‖; linarith)
  have hub : u < ‖x - 1‖ / 2 := lt_of_lt_of_le hu₀ (by have := min_le_right ‖x‖ ‖x - 1‖; linarith)
  -- `x ± u ∉ {0, 1}`
  have hne : ∀ s : ℝ, |s| ≤ u → x + s ≠ 0 ∧ x + s ≠ 1 := by
    intro s hs
    have h1 := norm_sub_norm_le x (-s)
    have h2 := norm_sub_norm_le (x - 1) (-s)
    rw [sub_neg_eq_add, norm_neg, Real.norm_eq_abs s] at h1
    rw [show x - 1 - -s = x + s - 1 by ring, norm_neg, Real.norm_eq_abs s] at h2
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, norm_zero] at h1
      linarith [norm_nonneg x]
    · rw [h, sub_self, norm_zero] at h2
      linarith [norm_nonneg (x - 1)]
  obtain ⟨h₁, h₂⟩ := hne u (by rw [abs_of_pos hu])
  obtain ⟨h₃, h₄⟩ := hne (-u) (by rw [abs_neg, abs_of_pos hu])
  rw [show x + -u = x - u by ring] at h₃ h₄
  have h0 : ∀ᵐ ζ : ℂ, ζ.im ≠ 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 LiZhongQC.gzE_volume_im_eq_zero] with ζ hζ
    exact hζ
  set cp : ℝ := x * (x - 1) / ((x + u) * (x + u - 1)) with hcpdef
  set cm : ℝ := x * (x - 1) / ((x - u) * (x - u - 1)) with hcmdef
  set Kp := LiZhongQC.ahKer ((x + u : ℝ) : ℂ) with hKp
  set Km := LiZhongQC.ahKer ((x - u : ℝ) : ℂ) with hKm
  -- the representation, rewritten with the cancellation `c₊K₊ − c₋K₋ = c₊(K₊ − K₋) + (c₊ − c₋)K₋`
  have hrepr : (fun ζ => ‖(x : ℂ) * (x - 1) / (ζ * (ζ - 1)) * (2 / ((ζ - x) ^ 2 - (u : ℂ) ^ 2))‖ₑ) =ᵐ[volume]
      fun ζ => ‖((1 / u : ℝ) : ℂ) * ((cp : ℂ) * (Kp ζ - Km ζ) + ((cp - cm : ℝ) : ℂ) * Km ζ)‖ₑ := by
    filter_upwards [h0] with ζ hζ
    rw [gl16_G_eq_ahKer hζ hu.ne' h₁ h₂ h₃ h₄, hcpdef, hcmdef, hKp, hKm]
    push_cast
    congr 1
    ring
  rw [lintegral_congr_ae hrepr]
  have hpt : ∀ ζ, ‖((1 / u : ℝ) : ℂ) * ((cp : ℂ) * (Kp ζ - Km ζ) + ((cp - cm : ℝ) : ℂ) * Km ζ)‖ₑ ≤
      ENNReal.ofReal (1 / u) * (ENNReal.ofReal ‖cp‖ * ‖Kp ζ - Km ζ‖ₑ + ENNReal.ofReal ‖cp - cm‖ * ‖Km ζ‖ₑ) := by
    intro ζ
    have hnorm : ∀ r : ℝ, ‖((r : ℂ))‖ₑ = ENNReal.ofReal ‖r‖ := fun r => by
      rw [← ofReal_norm, Complex.norm_real]
    rw [enorm_mul, hnorm, Real.norm_of_nonneg (by positivity)]
    gcongr
    refine (enorm_add_le _ _).trans ?_
    rw [enorm_mul, enorm_mul, hnorm, hnorm]
  refine (lintegral_mono hpt).trans ?_
  have hmK : Measurable fun ζ => ‖Kp ζ - Km ζ‖ₑ :=
    ((LiZhongQC.ahK_measurable _).sub (LiZhongQC.ahK_measurable _)).enorm
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' (hmK.aemeasurable.const_mul _),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- the two kernel integrals
  have hnp : ‖((x + u : ℝ) : ℂ)‖ ≤ 2 * ‖x‖ + 1 := by
    rw [Complex.norm_real]
    have := norm_add_le x u
    rw [Real.norm_of_nonneg hu.le] at this
    linarith [norm_nonneg x]
  have hnm : ‖((x - u : ℝ) : ℂ)‖ ≤ 2 * ‖x‖ + 1 := by
    rw [Complex.norm_real]
    have := norm_sub_le x u
    rw [Real.norm_of_nonneg hu.le] at this
    linarith [norm_nonneg x]
  have hpm : ((x + u : ℝ) : ℂ) ≠ ((x - u : ℝ) : ℂ) := by
    intro h
    have := Complex.ofReal_injective h
    linarith
  have hdist : ‖((x + u : ℝ) : ℂ) - ((x - u : ℝ) : ℂ)‖ = 2 * u := by
    rw [← Complex.ofReal_sub, Complex.norm_real, show x + u - (x - u) = 2 * u by ring,
      Real.norm_of_nonneg (by positivity)]
  have hI1 := hC₁ _ _ hnp hnm hpm
  rw [hdist] at hI1
  have hI2 : ∫⁻ ζ, ‖Km ζ‖ₑ ≤ ENNReal.ofReal B₀ := by
    refine (hC _).trans (ENNReal.ofReal_le_ofReal ?_)
    have hm : min √‖((x - u : ℝ) : ℂ)‖ √‖((x - u : ℝ) : ℂ) - 1‖ ≤ √(2 * ‖x‖ + 1) :=
      (min_le_left _ _).trans (Real.sqrt_le_sqrt hnm)
    have hm0 : 0 ≤ min √‖((x - u : ℝ) : ℂ)‖ √‖((x - u : ℝ) : ℂ) - 1‖ :=
      le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [hB₀]
    have h1 : 1 + ‖((x - u : ℝ) : ℂ)‖ ≤ 2 * ‖x‖ + 2 := by linarith
    calc C * min √‖((x - u : ℝ) : ℂ)‖ √‖((x - u : ℝ) : ℂ) - 1‖ * (1 + ‖((x - u : ℝ) : ℂ)‖)
        ≤ C * √(2 * ‖x‖ + 1) * (1 + ‖((x - u : ℝ) : ℂ)‖) := by
          gcongr
      _ ≤ C * √(2 * ‖x‖ + 1) * (2 * ‖x‖ + 2) := by gcongr
  refine (mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl hI1) (mul_le_mul' le_rfl hI2))).trans ?_
  rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (norm_nonneg _),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- the real arithmetic: `(1/u)(4(C₁√(2u) + 2(C₁ + 32π)u) + 32u|2x−1|B₀/|x(x−1)|)`
  have hsu : √(2 * u) / u = √2 * u ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_mul (by norm_num), Real.rpow_neg hu.le, Real.sqrt_eq_rpow u, mul_div_assoc]
    congr 1
    have hsu0 : 0 < u ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hu _
    have hsq : u ^ (1 / 2 : ℝ) * u ^ (1 / 2 : ℝ) = u := by
      rw [← Real.rpow_add hu]
      norm_num
    field_simp
    linarith [hsq]
  have hcd' : ‖cp - cm‖ * B₀ ≤ 32 * u * ‖2 * x - 1‖ / ‖x * (x - 1)‖ * B₀ := mul_le_mul_of_nonneg_right hcd hB₀0
  have hcp' : ‖cp‖ * (C₁ * √(2 * u) + (C₁ + 32 * π) * (2 * u)) ≤ 4 * (C₁ * √(2 * u) + (C₁ + 32 * π) * (2 * u)) :=
    mul_le_mul_of_nonneg_right hcp (by positivity)
  calc 1 / u * (‖cp‖ * (C₁ * √(2 * u) + (C₁ + 32 * π) * (2 * u)) + ‖cp - cm‖ * B₀)
      ≤ 1 / u * (4 * (C₁ * √(2 * u) + (C₁ + 32 * π) * (2 * u)) + 32 * u * ‖2 * x - 1‖ / ‖x * (x - 1)‖ * B₀) :=
        mul_le_mul_of_nonneg_left (add_le_add hcp' hcd') (by positivity)
    _ = 4 * C₁ * (√(2 * u) / u) + (4 * (C₁ + 32 * π) * 2 + 32 * ‖2 * x - 1‖ / ‖x * (x - 1)‖ * B₀) := by
        have hu0 : u ≠ 0 := hu.ne'
        have hxx0 : ‖x * (x - 1)‖ ≠ 0 := hxx.ne'
        field_simp
        ring_nf
    _ = 4 * C₁ * √2 * u ^ (-(1 / 2 : ℝ)) +
          (4 * (C₁ + 32 * π) * 2 + 32 * ‖2 * x - 1‖ / ‖x * (x - 1)‖ * B₀) := by
        rw [hsu]
        ring

/-- Helper for `eq16_27` (§16.7, P1c). `‖t‖^{−1/2}` is locally integrable on `ℝ`. -/
theorem gl16_locInt_rpow : LocallyIntegrable (fun t : ℝ => ‖t‖ ^ (-(1 / 2 : ℝ))) volume := by
  refine locallyIntegrable_of_norm_le_rpow (μ := volume) (by simp) (C := 1) (α := 1 / 2) (by simp; norm_num) ?_ ?_
  · refine Filter.Eventually.of_forall fun t => ?_
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg t) _), one_mul]
  · exact (continuous_norm.measurable.pow_const _).aestronglyMeasurable

/-- Helper for `eq16_27` (§16.7, P1c). `u⁻¹ ‖u − r‖^{−1/2}` is integrable on `[a, ∞)` for `a > 0`: local
integrability on `[a, R]` and `√2 u^{−3/2}` beyond `R = max(a, 2|r| + 1)`. -/
theorem gl16_integrableOn_inv_mul_rpow {a : ℝ} (ha : 0 < a) (r : ℝ) :
    IntegrableOn (fun u : ℝ => u⁻¹ * ‖u - r‖ ^ (-(1 / 2 : ℝ))) (Ici a) := by
  set R : ℝ := max a (2 * |r| + 1) with hR
  have haR : a ≤ R := le_max_left _ _
  have hRr : 2 * |r| + 1 ≤ R := le_max_right _ _
  have hsplit : Ici a = Icc a R ∪ Ioi R := by
    ext u
    simp only [mem_Ici, mem_union, mem_Icc, mem_Ioi]
    constructor
    · intro h
      rcases le_or_gt u R with hu | hu
      · exact Or.inl ⟨h, hu⟩
      · exact Or.inr hu
    · rintro (⟨h, -⟩ | h)
      · exact h
      · exact haR.trans h.le
  rw [hsplit]
  have hmeas : AEStronglyMeasurable (fun u : ℝ => u⁻¹ * ‖u - r‖ ^ (-(1 / 2 : ℝ))) volume :=
    ((measurable_id.inv).mul ((measurable_id.sub_const r).norm.pow_const _)).aestronglyMeasurable
  refine IntegrableOn.union ?_ ?_
  · -- on `[a, R]`: `u⁻¹ ≤ a⁻¹`, and `‖u − r‖^{−1/2}` is locally integrable
    have h1 : IntegrableOn (fun u : ℝ => ‖u - r‖ ^ (-(1 / 2 : ℝ))) (Icc a R) := by
      have hloc : IntegrableOn (fun t : ℝ => ‖t‖ ^ (-(1 / 2 : ℝ))) (Icc (a - r) (R - r)) :=
        LocallyIntegrable.integrableOn_isCompact gl16_locInt_rpow isCompact_Icc
      have hii := ((intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 hloc).comp_sub_right r
      simp only [sub_add_cancel] at hii
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le haR).1 hii
    refine (h1.const_mul a⁻¹).mono' hmeas.restrict ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun u hu => ?_)
    have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
    rw [norm_mul, norm_inv, Real.norm_of_nonneg hu0.le,
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ ha hu.1) (Real.rpow_nonneg (norm_nonneg _) _)
  · -- on `(R, ∞)`: `‖u − r‖ ≥ u/2`, so the function is at most `√2 u^{−3/2}`
    have hR0 : 0 < R := by linarith [abs_nonneg r]
    have h2 : IntegrableOn (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) (Ioi R) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) hR0
    refine (h2.const_mul (√2)).mono' hmeas.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
    have hu' : R < u := hu
    have hu0 : 0 < u := hR0.trans hu'
    have hur : u / 2 ≤ ‖u - r‖ := by
      have := norm_sub_norm_le u r
      rw [Real.norm_of_nonneg hu0.le, Real.norm_eq_abs] at this
      linarith
    have hpos : 0 < u / 2 := by positivity
    have hrp : ‖u - r‖ ^ (-(1 / 2 : ℝ)) ≤ (u / 2) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hpos hur (by norm_num)
    have he : (u / 2) ^ (-(1 / 2 : ℝ)) = √2 * u ^ (-(1 / 2 : ℝ)) := by
      rw [Real.div_rpow hu0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_eq_rpow,
        div_eq_mul_inv, inv_inv]
      ring
    have he2 : u⁻¹ * u ^ (-(1 / 2 : ℝ)) = u ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hu0]
      norm_num
    rw [norm_mul, norm_inv, Real.norm_of_nonneg hu0.le, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    calc u⁻¹ * ‖u - r‖ ^ (-(1 / 2 : ℝ)) ≤ u⁻¹ * (√2 * u ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (hrp.trans he.le) (inv_nonneg.2 hu0.le)
      _ = √2 * u ^ (-(3 / 2 : ℝ)) := by rw [← he2]; ring

/-- Helper for `eq16_27` (§16.7, P1c). The symmetrized kernel
`G_x(u, ζ) = x(x − 1)/(ζ(ζ − 1)) · 2/((ζ − x)² − u²)` has `u`-wise `L¹` norms in `L¹(0, ∞)`.
- Near `u = 0`, use the cancellation `G = (c₊K_{x+u} − c₋K_{x−u})/u`, where `c± = x(x − 1)/(p±(p± − 1))`, together
  with S13's difference estimate.
- Near `p± ∈ {0, 1}` and at `∞`, use P1b. -/
theorem gl16_G_lintegral_lt_top (x : ℝ) :
    ∫⁻ u in Ioi (0 : ℝ), ∫⁻ ζ, ‖(x : ℂ) * (x - 1) / (ζ * (ζ - 1)) * (2 / ((ζ - x) ^ 2 - (u : ℂ) ^ 2))‖ₑ < ⊤ := by
  by_cases hx : x = 0 ∨ x = 1
  · have h0 : ∀ u : ℝ, ∀ ζ : ℂ, (x : ℂ) * (x - 1) / (ζ * (ζ - 1)) * (2 / ((ζ - x) ^ 2 - (u : ℂ) ^ 2)) = 0 := by
      intro u ζ
      rcases hx with rfl | rfl <;> simp
    simp only [h0, enorm_zero, lintegral_zero]
    exact ENNReal.zero_lt_top
  have hx0 : x ≠ 0 := fun h => hx (Or.inl h)
  have hx1 : x ≠ 1 := fun h => hx (Or.inr h)
  set u₀ : ℝ := min ‖x‖ ‖x - 1‖ / 2 with hu₀
  have hu₀pos : 0 < u₀ := by
    have := lt_min (norm_pos_iff.2 hx0) (norm_pos_iff.2 (sub_ne_zero.2 hx1))
    positivity
  obtain ⟨A₁, B₁, hA₁, hB₁, hsmall⟩ := gl16_G_inner_small hx0 hx1
  obtain ⟨A₂, hA₂, hlarge⟩ := gl16_G_inner_le x
  have hsplit : Ioi (0 : ℝ) = Ioo 0 u₀ ∪ Ici u₀ := by
    ext u
    simp only [mem_Ioi, mem_union, mem_Ioo, mem_Ici]
    constructor
    · intro h
      rcases lt_or_ge u u₀ with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr h'
    · rintro (⟨h, -⟩ | h)
      · exact h
      · exact lt_of_lt_of_le hu₀pos h
  have hdisj : Disjoint (Ioo (0 : ℝ) u₀) (Ici u₀) :=
    Set.disjoint_left.2 fun u hu1 hu2 => (not_lt.2 (show u₀ ≤ u from hu2)) hu1.2
  rw [hsplit, lintegral_union measurableSet_Ici hdisj]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · -- near `0`: `A₁ u^{−1/2} + B₁`
    have hint : IntegrableOn (fun u : ℝ => A₁ * u ^ (-(1 / 2 : ℝ)) + B₁) (Ioo 0 u₀) := by
      refine (((intervalIntegral.integrableOn_Ioo_rpow_iff hu₀pos).2 (by norm_num)).const_mul A₁).add ?_
      exact integrableOn_const (by simp)
    refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioo fun u hu => by exact hsmall u hu.1 hu.2) ?_
    exact hint.setLIntegral_lt_top
  · -- away from `0`: `(A₂/u) Σ ‖u − r‖^{−1/2}` off the four points where `x ± u ∈ {0, 1}`
    have hbad : ∀ᵐ u ∂(volume.restrict (Ici u₀)), x + u ≠ 0 ∧ x + u ≠ 1 ∧ x - u ≠ 0 ∧ x - u ≠ 1 := by
      have hfin : ({-x, 1 - x, x, x - 1} : Set ℝ).Countable := (Set.toFinite _).countable
      have h := measure_eq_zero_iff_ae_notMem.1 (hfin.measure_zero volume)
      refine ae_restrict_of_ae (h.mono fun u hu => ?_)
      simp only [mem_insert_iff, mem_singleton_iff, not_or] at hu
      obtain ⟨h1, h2, h3, h4⟩ := hu
      refine ⟨fun h => h1 (by linarith), fun h => h2 (by linarith), fun h => h3 (by linarith),
        fun h => h4 (by linarith)⟩
    have hint : IntegrableOn (fun u : ℝ => A₂ / u * (‖x + u‖ ^ (-(1 / 2 : ℝ)) + ‖x + u - 1‖ ^ (-(1 / 2 : ℝ)) +
        (‖x - u‖ ^ (-(1 / 2 : ℝ)) + ‖x - u - 1‖ ^ (-(1 / 2 : ℝ))))) (Ici u₀) := by
      have i1 := gl16_integrableOn_inv_mul_rpow hu₀pos (-x)
      have i2 := gl16_integrableOn_inv_mul_rpow hu₀pos (1 - x)
      have i3 := gl16_integrableOn_inv_mul_rpow hu₀pos x
      have i4 := gl16_integrableOn_inv_mul_rpow hu₀pos (x - 1)
      refine IntegrableOn.congr_fun (((i1.add i2).add (i3.add i4)).const_mul A₂) (fun u _ => ?_)
        measurableSet_Ici
      simp only [Pi.add_apply]
      rw [show u - -x = x + u by ring, show u - (1 - x) = x + u - 1 by ring, norm_sub_rev u x,
        show u - (x - 1) = -(x - u - 1) by ring, norm_neg]
      ring
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint.setLIntegral_lt_top
    filter_upwards [hbad, ae_restrict_mem measurableSet_Ici] with u ⟨h1, h2, h3, h4⟩ hu
    exact hlarge u (lt_of_lt_of_le hu₀pos hu) h1 h2 h3 h4

/-- Helper for `eq16_27` (§16.7, P1). Joint integrability of `G_x` on `(0, ∞) × ℂ` (P1c and Tonelli). -/
theorem gl16_G_integrable (x : ℝ) :
    Integrable (fun q : ℝ × ℂ => (x : ℂ) * (x - 1) / (q.2 * (q.2 - 1)) * (2 / ((q.2 - x) ^ 2 - (q.1 : ℂ) ^ 2)))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hmeas : Measurable fun q : ℝ × ℂ =>
      (x : ℂ) * (x - 1) / (q.2 * (q.2 - 1)) * (2 / ((q.2 - x) ^ 2 - (q.1 : ℂ) ^ 2)) := by
    fun_prop
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_prod _ hmeas.enorm.aemeasurable]
  exact gl16_G_lintegral_lt_top x

/-- Helper for `eq16_27` (§16.7, P2). For `Im w ≠ 0` the denominator `w² − u²` does not vanish on `ℝ`. -/
theorem gl16_T0_den_ne {w : ℂ} (hw : w.im ≠ 0) (u : ℝ) : w ^ 2 - (u : ℂ) ^ 2 ≠ 0 := by
  intro h
  have h' : (w - u) * (w + u) = 0 := by
    rw [← h]
    ring
  rcases mul_eq_zero.1 h' with h1 | h1
  · exact hw (by simpa using congrArg Complex.im h1)
  · exact hw (by simpa using congrArg Complex.im h1)

/-- Helper for `eq16_27` (§16.7, P2). `u ↦ 2/(w² − u²)` is continuous for `Im w ≠ 0`. -/
theorem gl16_T0_continuous {w : ℂ} (hw : w.im ≠ 0) : Continuous fun u : ℝ => 2 / (w ^ 2 - (u : ℂ) ^ 2) :=
  continuous_const.div (continuous_const.sub (Complex.continuous_ofReal.pow 2)) (gl16_T0_den_ne hw)

/-- Helper for `eq16_27` (§16.7, P2). `u ↦ 2/(w² − u²)` is integrable on `(0, ∞)` for `Im w ≠ 0` (continuous on
`[0, R]`, at most `4u⁻²` beyond `R = 2|w| + 1`). -/
theorem gl16_T0_integrableOn {w : ℂ} (hw : w.im ≠ 0) :
    IntegrableOn (fun u : ℝ => 2 / (w ^ 2 - (u : ℂ) ^ 2)) (Ioi 0) := by
  have hcont := gl16_T0_continuous hw
  set R : ℝ := 2 * ‖w‖ + 1 with hR
  have hR0 : 0 < R := by positivity
  have hsplit : Ioi (0 : ℝ) ⊆ Icc 0 R ∪ Ioi R := fun u hu => by
    rcases le_or_gt u R with h | h
    · exact Or.inl ⟨le_of_lt hu, h⟩
    · exact Or.inr h
  refine IntegrableOn.mono_set (IntegrableOn.union hcont.continuousOn.integrableOn_Icc ?_) hsplit
  have h2 : IntegrableOn (fun u : ℝ => u ^ (-2 : ℝ)) (Ioi R) := integrableOn_Ioi_rpow_of_lt (by norm_num) hR0
  refine (h2.const_mul 4).mono' hcont.aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
  have hu' : R < u := hu
  have hu0 : 0 < u := hR0.trans hu'
  have hwu : ‖w‖ ≤ u / 2 := by linarith [norm_nonneg w]
  have hden : u ^ 2 / 2 ≤ ‖w ^ 2 - (u : ℂ) ^ 2‖ := by
    have h1 := norm_sub_norm_le ((u : ℂ) ^ 2) (w ^ 2)
    rw [norm_sub_rev, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu0.le] at h1
    have h3 : ‖w‖ ^ 2 ≤ u ^ 2 / 4 := by nlinarith [norm_nonneg w]
    linarith [sq_nonneg u]
  have hden0 : 0 < ‖w ^ 2 - (u : ℂ) ^ 2‖ := lt_of_lt_of_le (by positivity) hden
  have hpow : u ^ (-2 : ℝ) = (u ^ 2)⁻¹ := by
    rw [Real.rpow_neg hu0.le]
    norm_cast
  rw [norm_div, hpow, show ‖(2 : ℂ)‖ = 2 by simp, div_le_iff₀ hden0]
  have hu2 : 0 < u ^ 2 := by positivity
  calc (2 : ℝ) = 4 * (u ^ 2)⁻¹ * (u ^ 2 / 2) := by field_simp; ring
    _ ≤ 4 * (u ^ 2)⁻¹ * ‖w ^ 2 - (u : ℂ) ^ 2‖ := mul_le_mul_of_nonneg_left hden (by positivity)

/-- Helper for `eq16_27` (§16.7, P2). For `Im w ≠ 0`, `Log(w + L) − Log(w − L) → −iπ sgn(Im w)` as `L → ∞`. -/
theorem gl16_log_diff_tendsto {w : ℂ} (hw : w.im ≠ 0) :
    Tendsto (fun L : ℝ => Complex.log (w + L) - Complex.log (w - L)) atTop
      (𝓝 (if 0 < w.im then -(π * I) else π * I)) := by
  -- `w ± L = L (1 ± w/L)` and `1 ± w/L → 1`
  have hwL : Tendsto (fun L : ℝ => w / (L : ℂ)) atTop (𝓝 0) := by
    have h := ((Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero).const_mul w
    simp only [Function.comp_apply, Complex.ofReal_zero, mul_zero] at h
    refine h.congr fun L => ?_
    rw [Complex.ofReal_inv, div_eq_mul_inv]
  have hp : Tendsto (fun L : ℝ => 1 + w / (L : ℂ)) atTop (𝓝 1) := by simpa using hwL.const_add 1
  have hm : Tendsto (fun L : ℝ => 1 - w / (L : ℂ)) atTop (𝓝 1) := by simpa using hwL.const_sub 1
  have h1 : (1 : ℂ) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.2 (Or.inl (by norm_num))
  -- moduli: `log ‖w + L‖ − log ‖w − L‖ = log ‖1 + w/L‖ − log ‖1 − w/L‖ → 0`
  have hre : Tendsto (fun L : ℝ => Real.log ‖w + L‖ - Real.log ‖w - L‖) atTop (𝓝 0) := by
    have hc : Tendsto (fun L : ℝ => Real.log ‖1 + w / (L : ℂ)‖ - Real.log ‖1 - w / (L : ℂ)‖) atTop
        (𝓝 (Real.log ‖(1 : ℂ)‖ - Real.log ‖(1 : ℂ)‖)) :=
      ((Real.continuousAt_log (by simp)).tendsto.comp hp.norm).sub
        ((Real.continuousAt_log (by simp)).tendsto.comp hm.norm)
    rw [sub_self] at hc
    refine hc.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    have e1 : w + L = (L : ℂ) * (1 + w / L) := by field_simp; ring
    have e2 : w - L = -((L : ℂ) * (1 - w / L)) := by field_simp; ring
    have hn1 : ‖1 + w / (L : ℂ)‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      intro h
      have : w + L = 0 := by rw [e1, h, mul_zero]
      exact hw (by simpa using congrArg Complex.im this)
    have hn2 : ‖1 - w / (L : ℂ)‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      intro h
      have : w - L = 0 := by rw [e2, h, mul_zero, neg_zero]
      exact hw (by simpa using congrArg Complex.im this)
    have hLn : ‖(L : ℂ)‖ ≠ 0 := by simpa using hL.ne'
    rw [e1, e2, norm_neg, norm_mul, norm_mul, Real.log_mul hLn hn1, Real.log_mul hLn hn2]
    ring
  -- arguments: `arg(w + L) → 0`, `arg(w − L) → ±π`
  have harg1 : Tendsto (fun L : ℝ => Complex.arg (w + L)) atTop (𝓝 0) := by
    have hc : Tendsto (fun L : ℝ => Complex.arg (1 + w / (L : ℂ))) atTop (𝓝 (Complex.arg 1)) :=
      (Complex.continuousAt_arg h1).tendsto.comp hp
    rw [Complex.arg_one] at hc
    refine hc.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    have e1 : w + L = (L : ℂ) * (1 + w / L) := by field_simp; ring
    rw [e1, Complex.arg_real_mul _ hL]
  have harg2 : Tendsto (fun L : ℝ => Complex.arg (w - L)) atTop (𝓝 (if 0 < w.im then π else -π)) := by
    have hc : Tendsto (fun L : ℝ => Complex.arg (1 - w / (L : ℂ))) atTop (𝓝 (Complex.arg 1)) :=
      (Complex.continuousAt_arg h1).tendsto.comp hm
    rw [Complex.arg_one] at hc
    have hev : ∀ᶠ L : ℝ in atTop, Complex.arg (w - L) =
        Complex.arg (1 - w / (L : ℂ)) + (if 0 < w.im then π else -π) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      have e2 : w - L = (L : ℂ) * -(1 - w / L) := by field_simp; ring
      have him : (1 - w / (L : ℂ)).im = -(w.im / L) := by
        rw [Complex.sub_im, Complex.one_im, Complex.div_ofReal_im]
        ring
      rw [e2, Complex.arg_real_mul _ hL]
      split_ifs with h
      · have : (1 - w / (L : ℂ)).im < 0 := by rw [him]; exact neg_neg_of_pos (div_pos h hL)
        rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg this]
      · have hneg : w.im < 0 := lt_of_le_of_ne (not_lt.1 h) hw
        have : 0 < (1 - w / (L : ℂ)).im := by rw [him]; exact neg_pos.2 (div_neg_of_neg_of_pos hneg hL)
        rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos this]
        ring
    have hc' := hc.add_const (if 0 < w.im then π else -π)
    rw [zero_add] at hc'
    exact hc'.congr' (hev.mono fun L hL => hL.symm)
  -- assemble `Log z = log ‖z‖ + i arg z`
  have hlog : ∀ z : ℂ, Complex.log z = (Real.log ‖z‖ : ℂ) + (Complex.arg z : ℂ) * I := fun z => by
    apply Complex.ext <;> simp [Complex.log_re, Complex.log_im]
  have hsum := (Complex.continuous_ofReal.tendsto _ |>.comp hre).add
    ((Complex.continuous_ofReal.tendsto _ |>.comp (harg1.sub harg2)).mul_const I)
  refine (hsum.congr fun L => ?_).trans ?_
  · simp only [Function.comp_apply, hlog]
    push_cast
    ring
  · split_ifs with h <;> simp

/-- Helper for `eq16_27` (§16.7, P2). For `Im w ≠ 0`, `u ↦ 2/(w² − u²)` is integrable on `(0, ∞)` and
`∫₀^∞ 2/(w² − u²) du = −iπ sgn(Im w)/w` (antiderivative `Log(w + u) − Log(w − u)`). -/
theorem gl16_T0 {w : ℂ} (hw : w.im ≠ 0) :
    IntegrableOn (fun u : ℝ => 2 / (w ^ 2 - (u : ℂ) ^ 2)) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), 2 / (w ^ 2 - (u : ℂ) ^ 2) = (if 0 < w.im then -(π * I) else π * I) / w := by
  have hint := gl16_T0_integrableOn hw
  refine ⟨hint, ?_⟩
  have hw0 : w ≠ 0 := fun h => hw (by rw [h, Complex.zero_im])
  have hslit : ∀ u : ℝ, w + u ∈ Complex.slitPlane ∧ w - u ∈ Complex.slitPlane := fun u =>
    ⟨Complex.mem_slitPlane_iff.2 (Or.inr (by simpa using hw)),
      Complex.mem_slitPlane_iff.2 (Or.inr (by simpa using hw))⟩
  have hderiv : ∀ u : ℝ, HasDerivAt (fun u : ℝ => (Complex.log (w + u) - Complex.log (w - u)) / w)
      (2 / (w ^ 2 - (u : ℂ) ^ 2)) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => w + (u : ℂ)) 1 u := (hasDerivAt_id u).ofReal_comp.const_add w
    have h2 : HasDerivAt (fun u : ℝ => w - (u : ℂ)) (-1) u := by
      simpa using (hasDerivAt_id u).ofReal_comp.const_sub w
    have hd := ((h1.clog_real (hslit u).1).sub (h2.clog_real (hslit u).2)).div_const w
    convert hd using 1
    have hp : w + (u : ℂ) ≠ 0 := Complex.slitPlane_ne_zero (hslit u).1
    have hm : w - (u : ℂ) ≠ 0 := Complex.slitPlane_ne_zero (hslit u).2
    have hden := gl16_T0_den_ne hw u
    field_simp
    ring
  have hFTC : ∀ L : ℝ, ∫ u in (0 : ℝ)..L, 2 / (w ^ 2 - (u : ℂ) ^ 2) =
      (Complex.log (w + L) - Complex.log (w - L)) / w := by
    intro L
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
      ((gl16_T0_continuous hw).intervalIntegrable _ _)]
    simp
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  have hlim2 := (gl16_log_diff_tendsto hw).div_const w
  refine tendsto_nhds_unique (hlim.congr fun L => ?_) hlim2
  rw [id, hFTC L]

/-- Helper for `eq16_27` (§16.7). The cancellation: `R(x + u, ζ) R(x, x + u) + R(x − u, ζ) R(x, x − u)
= x(x − 1)/(ζ(ζ − 1)) · 2/((ζ − x)² − u²)` for `Im ζ ≠ 0`, `u ≠ 0` and `x ± u ∉ {0, 1}`. -/
theorem gl16_kernelR_sym {x u : ℝ} {ζ : ℂ} (hζ : ζ.im ≠ 0) (hu : u ≠ 0) (h₁ : x + u ≠ 0) (h₂ : x + u ≠ 1)
    (h₃ : x - u ≠ 0) (h₄ : x - u ≠ 1) :
    kernelR ((x + u : ℝ) : ℂ) ζ * kernelR x ((x + u : ℝ) : ℂ) +
        kernelR ((x - u : ℝ) : ℂ) ζ * kernelR x ((x - u : ℝ) : ℂ) =
      (x : ℂ) * (x - 1) / (ζ * (ζ - 1)) * (2 / ((ζ - x) ^ 2 - (u : ℂ) ^ 2)) := by
  have him : ∀ r : ℝ, ζ - (r : ℂ) ≠ 0 := fun r h => hζ (by simpa using congrArg Complex.im h)
  have hz0 : ζ ≠ 0 := fun h => hζ (by rw [h, Complex.zero_im])
  have hz1 : ζ - 1 ≠ 0 := by simpa using him 1
  have hzp := him (x + u)
  have hzm := him (x - u)
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  have hp0 : ((x + u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h₁
  have hp1 : ((x + u : ℝ) : ℂ) - 1 ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact_mod_cast sub_ne_zero.2 h₂
  have hm0 : ((x - u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h₃
  have hm1 : ((x - u : ℝ) : ℂ) - 1 ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact_mod_cast sub_ne_zero.2 h₄
  have hpx : ((x + u : ℝ) : ℂ) - x ≠ 0 := by
    rw [← Complex.ofReal_sub, show x + u - x = u by ring]
    exact hu'
  have hmx : ((x - u : ℝ) : ℂ) - x ≠ 0 := by
    rw [← Complex.ofReal_sub, show x - u - x = -u by ring, Complex.ofReal_neg]
    exact neg_ne_zero.2 hu'
  have hD : (ζ - x) ^ 2 - (u : ℂ) ^ 2 = (ζ - ((x + u : ℝ) : ℂ)) * (ζ - ((x - u : ℝ) : ℂ)) := by
    push_cast
    ring
  unfold kernelR
  rw [hD]
  field_simp
  push_cast
  ring

/-- Helper for `eq16_27` (§16.7, P3). The right half `(x + ε, ∞)` of the principal-value domain, translated:
integrability and integral of `f` there are those of `u ↦ f(x + u)` on `(ε, ∞)`. -/
theorem gl16_setIntegral_right {f : ℝ → ℂ} {x ε : ℝ} (hf : IntegrableOn f (Ioi (x + ε))) :
    IntegrableOn (fun u => f (x + u)) (Ioi ε) ∧ ∫ ξ in Ioi (x + ε), f ξ = ∫ u in Ioi ε, f (x + u) := by
  have hind : ∀ u : ℝ, (Ioi (x + ε)).indicator f (x + u) = (Ioi ε).indicator (fun u => f (x + u)) u := by
    intro u
    by_cases hu : ε < u
    · rw [indicator_of_mem (show x + u ∈ Ioi (x + ε) from by simp only [mem_Ioi]; linarith),
        indicator_of_mem (show u ∈ Ioi ε from hu)]
    · rw [indicator_of_notMem (show x + u ∉ Ioi (x + ε) from by simp only [mem_Ioi]; linarith),
        indicator_of_notMem (show u ∉ Ioi ε from hu)]
  have hI : Integrable ((Ioi (x + ε)).indicator f) := (integrable_indicator_iff measurableSet_Ioi).2 hf
  refine ⟨?_, ?_⟩
  · rw [← integrable_indicator_iff measurableSet_Ioi]
    exact (hI.comp_add_left x).congr (Filter.Eventually.of_forall hind)
  · rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
      ← integral_add_left_eq_self _ x]
    exact integral_congr_ae (Filter.Eventually.of_forall hind)

/-- Helper for `eq16_27` (§16.7, P3). The left half `(−∞, x − ε)`, reflected: integrability and integral of `f`
there are those of `u ↦ f(x − u)` on `(ε, ∞)`. -/
theorem gl16_setIntegral_left {f : ℝ → ℂ} {x ε : ℝ} (hf : IntegrableOn f (Iio (x - ε))) :
    IntegrableOn (fun u => f (x - u)) (Ioi ε) ∧ ∫ ξ in Iio (x - ε), f ξ = ∫ u in Ioi ε, f (x - u) := by
  have hind : ∀ u : ℝ, (Iio (x - ε)).indicator f (x - u) = (Ioi ε).indicator (fun u => f (x - u)) u := by
    intro u
    by_cases hu : ε < u
    · rw [indicator_of_mem (show x - u ∈ Iio (x - ε) from by simp only [mem_Iio]; linarith),
        indicator_of_mem (show u ∈ Ioi ε from hu)]
    · rw [indicator_of_notMem (show x - u ∉ Iio (x - ε) from by simp only [mem_Iio]; linarith),
        indicator_of_notMem (show u ∉ Ioi ε from hu)]
  have hI : Integrable ((Iio (x - ε)).indicator f) := (integrable_indicator_iff measurableSet_Iio).2 hf
  refine ⟨?_, ?_⟩
  · rw [← integrable_indicator_iff measurableSet_Ioi]
    exact (hI.comp_sub_left x).congr (Filter.Eventually.of_forall hind)
  · rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi,
      ← integral_sub_left_eq_self _ volume x]
    exact integral_congr_ae (Filter.Eventually.of_forall hind)

/-- Helper for `eq16_27` (§16.7, P3). `{ξ | ε < |ξ − x|} = (x + ε, ∞) ∪ (−∞, x − ε)`, a disjoint union for `ε ≥ 0`. -/
theorem gl16_pv_domain {x ε : ℝ} (hε : 0 ≤ ε) :
    {ξ : ℝ | ε < |ξ - x|} = Ioi (x + ε) ∪ Iio (x - ε) ∧ Disjoint (Ioi (x + ε)) (Iio (x - ε)) := by
  refine ⟨?_, Set.disjoint_left.2 fun ξ h1 h2 => by
    simp only [mem_Ioi, mem_Iio] at h1 h2
    linarith⟩
  ext ξ
  simp only [mem_ofPred_eq, mem_union, mem_Ioi, mem_Iio, lt_abs]
  constructor
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)

/-- Helper for `eq16_27` (§16.7, P3). The principal-value domain folded at `x`:
`∫_{|ξ − x| > ε} f = ∫_ε^∞ (f(x + u) + f(x − u)) du` for `ε ≥ 0`. -/
theorem gl16_setIntegral_fold {f : ℝ → ℂ} {x ε : ℝ} (hε : 0 ≤ ε) (hf : IntegrableOn f {ξ : ℝ | ε < |ξ - x|}) :
    IntegrableOn (fun u => f (x + u) + f (x - u)) (Ioi ε) ∧
      ∫ ξ in {ξ : ℝ | ε < |ξ - x|}, f ξ = ∫ u in Ioi ε, (f (x + u) + f (x - u)) := by
  obtain ⟨hdom, hdisj⟩ := gl16_pv_domain (x := x) hε
  rw [hdom] at hf ⊢
  obtain ⟨hR, hRe⟩ := gl16_setIntegral_right (hf.mono_set subset_union_left)
  obtain ⟨hL, hLe⟩ := gl16_setIntegral_left (hf.mono_set subset_union_right)
  refine ⟨hR.add hL, ?_⟩
  rw [setIntegral_union hdisj measurableSet_Iio (hf.mono_set subset_union_left) (hf.mono_set subset_union_right),
    hRe, hLe, integral_add hR hL]

/-- Helper for `eq16_27` (§16.7). The facts used from `IsBeltramiCoeff μ univ k`: `μ` is a.e. strongly measurable,
`|μ| ≤ k` a.e., and `k ≥ 0`. -/
theorem gl16_beltrami_facts {μ : ℂ → ℂ} {k : ℝ} (hμ : LiZhongQC.IsBeltramiCoeff μ univ k) :
    AEStronglyMeasurable μ volume ∧ (∀ᵐ ζ : ℂ, ‖μ ζ‖ ≤ k) ∧ 0 ≤ k := by
  obtain ⟨hm, hb⟩ := hμ
  rw [Measure.restrict_univ] at hm hb
  obtain ⟨ζ, hζ⟩ := hb.exists
  exact ⟨hm, hb, (norm_nonneg _).trans hζ⟩

/-- Helper for `eq16_27` (§16.7, P6). Translating integrability back: `u ↦ f(x + u)` integrable on `(ε, ∞)` gives `f`
integrable on `(x + ε, ∞)`. -/
theorem gl16_integrableOn_Ioi_of_comp {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {x ε : ℝ}
    (hf : IntegrableOn (fun u => f (x + u)) (Ioi ε)) :
    IntegrableOn f (Ioi (x + ε)) := by
  have hI : Integrable ((Ioi ε).indicator fun u => f (x + u)) := (integrable_indicator_iff measurableSet_Ioi).2 hf
  rw [← integrable_indicator_iff measurableSet_Ioi]
  refine (hI.comp_add_left (-x)).congr (Filter.Eventually.of_forall fun ξ => ?_)
  simp only
  by_cases hξ : x + ε < ξ
  · rw [indicator_of_mem (show -x + ξ ∈ Ioi ε from by simp only [mem_Ioi]; linarith),
      indicator_of_mem (show ξ ∈ Ioi (x + ε) from hξ)]
    simp
  · rw [indicator_of_notMem (show -x + ξ ∉ Ioi ε from by simp only [mem_Ioi]; linarith),
      indicator_of_notMem (show ξ ∉ Ioi (x + ε) from hξ)]

/-- Helper for `eq16_27` (§16.7, P6). Reflecting integrability back: `u ↦ f(x − u)` integrable on `(ε, ∞)` gives `f`
integrable on `(−∞, x − ε)`. -/
theorem gl16_integrableOn_Iio_of_comp {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {x ε : ℝ}
    (hf : IntegrableOn (fun u => f (x - u)) (Ioi ε)) :
    IntegrableOn f (Iio (x - ε)) := by
  have hI : Integrable ((Ioi ε).indicator fun u => f (x - u)) := (integrable_indicator_iff measurableSet_Ioi).2 hf
  rw [← integrable_indicator_iff measurableSet_Iio]
  refine (hI.comp_sub_left x).congr (Filter.Eventually.of_forall fun ξ => ?_)
  simp only
  by_cases hξ : ξ < x - ε
  · rw [indicator_of_mem (show x - ξ ∈ Ioi ε from by simp only [mem_Ioi]; linarith),
      indicator_of_mem (show ξ ∈ Iio (x - ε) from hξ)]
    simp
  · rw [indicator_of_notMem (show x - ξ ∉ Ioi ε from by simp only [mem_Ioi]; linarith),
      indicator_of_notMem (show ξ ∉ Iio (x - ε) from hξ)]

/-- Helper for `eq16_27` (§16.7, P6). The majorant `(‖ξ‖^{−1/2} + ‖ξ − 1‖^{−1/2}) ‖ξ − x‖⁻¹` is integrable away
from `x` (fold at `x` and `gl16_integrableOn_inv_mul_rpow`). -/
theorem gl16_maj_integrableOn (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun ξ : ℝ => (‖ξ‖ ^ (-(1 / 2 : ℝ)) + ‖ξ - 1‖ ^ (-(1 / 2 : ℝ))) * ‖ξ - x‖⁻¹)
      {ξ : ℝ | ε < |ξ - x|} := by
  obtain ⟨hdom, -⟩ := gl16_pv_domain (x := x) hε.le
  rw [hdom]
  have hs : Ioi ε ⊆ Ici ε := Ioi_subset_Ici_self
  refine IntegrableOn.union (gl16_integrableOn_Ioi_of_comp ?_) (gl16_integrableOn_Iio_of_comp ?_)
  · refine (((gl16_integrableOn_inv_mul_rpow hε (-x)).add
      (gl16_integrableOn_inv_mul_rpow hε (1 - x))).mono_set hs).congr_fun
      (fun u hu => ?_) measurableSet_Ioi
    have hu0 : 0 < u := hε.trans hu
    simp only [Pi.add_apply]
    rw [show x + u - x = u by ring, show u - -x = x + u by ring, show u - (1 - x) = x + u - 1 by ring,
      Real.norm_of_nonneg hu0.le]
    ring
  · refine (((gl16_integrableOn_inv_mul_rpow hε x).add
      (gl16_integrableOn_inv_mul_rpow hε (x - 1))).mono_set hs).congr_fun
      (fun u hu => ?_) measurableSet_Ioi
    have hu0 : 0 < u := hε.trans hu
    simp only [Pi.add_apply]
    rw [show x - u - x = -u by ring, norm_neg, norm_sub_rev u x, show u - (x - 1) = -(x - u - 1) by ring, norm_neg,
      Real.norm_of_nonneg hu0.le]
    ring

/-- Helper for `eq16_27` (§16.7, P6). `ξ ↦ ∫ μ(ζ) R(ξ, ζ) dζ` is a.e. strongly measurable on `ℝ`. -/
theorem gl16_V_aestronglyMeasurable {μ : ℂ → ℂ} (hμ : AEStronglyMeasurable μ volume) :
    AEStronglyMeasurable (fun ξ : ℝ => ∫ ζ, μ ζ * kernelR ξ ζ) volume := by
  refine AEStronglyMeasurable.integral_prod_right' (f := fun q : ℝ × ℂ => μ q.2 * kernelR q.1 q.2) ?_
  have hk : Measurable fun q : ℝ × ℂ => kernelR (q.1 : ℂ) q.2 := by
    unfold kernelR
    fun_prop
  exact hμ.comp_snd.mul hk.aestronglyMeasurable

/-- Helper for `eq16_27` (§16.7, P6). `ξ ↦ V(ξ) R(x, ξ)` is integrable away from `x`. This follows from P1 and
`|V(ξ)| ≤ (k/π) ∬ |μ| |K_ξ|`. So the truncations in `hilbertPV` are genuine integrals, not junk. -/
theorem gl16_V_integrableOn {V μ : ℂ → ℂ} (hV : IsKernelRepr V μ) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun ξ : ℝ => V ξ * kernelR x ξ) {ξ : ℝ | ε < |ξ - x|} := by
  obtain ⟨⟨k, hk⟩, -, hrep⟩ := hV
  obtain ⟨hμm, -, hk0⟩ := gl16_beltrami_facts hk
  obtain ⟨C, hC0, hC⟩ := gl16_ahKer_lintegral_le
  set M : ℝ := (1 / π) * k * C * ‖x * (x - 1)‖ * 3 with hM
  -- measurability
  have hmeas : AEStronglyMeasurable (fun ξ : ℝ => V ξ * kernelR x ξ) volume := by
    have hV' : (fun ξ : ℝ => V ξ) = fun ξ : ℝ => -(1 / (π : ℂ)) * ∫ ζ, μ ζ * kernelR ξ ζ := funext fun ξ => hrep ξ
    have hk' : Measurable fun ξ : ℝ => kernelR (x : ℂ) (ξ : ℂ) := by
      unfold kernelR
      fun_prop
    rw [show (fun ξ : ℝ => V ξ * kernelR x ξ) = fun ξ : ℝ => (fun ξ : ℝ => V ξ) ξ * kernelR x ξ from rfl, hV']
    exact ((gl16_V_aestronglyMeasurable hμm).const_mul _).mul hk'.aestronglyMeasurable
  -- the pointwise bound off `ξ ∈ {0, 1, x}`
  have hbound : ∀ ξ : ℝ, ξ ≠ 0 → ξ ≠ 1 → ξ ≠ x →
      ‖V ξ * kernelR x ξ‖ ≤ M * ((‖ξ‖ ^ (-(1 / 2 : ℝ)) + ‖ξ - 1‖ ^ (-(1 / 2 : ℝ))) * ‖ξ - x‖⁻¹) := by
    intro ξ h0 h1 hx
    have hVξ : ‖V ξ‖ ≤ (1 / π) * (∫ ζ, ‖LiZhongQC.ahKer ξ ζ‖) * k := by
      rw [hrep ξ]
      exact LiZhongQC.ah_var_bound (ξ : ℂ) hk
    have hKξ : ∫ ζ, ‖LiZhongQC.ahKer (ξ : ℂ) ζ‖ ≤ C * min √‖ξ‖ √‖ξ - 1‖ * (1 + ‖ξ‖) := by
      rw [integral_norm_eq_lintegral_enorm (LiZhongQC.ahK_measurable _).aestronglyMeasurable]
      have h := hC (ξ : ℂ)
      rw [Complex.norm_real, show (ξ : ℂ) - 1 = ((ξ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real] at h
      exact ENNReal.toReal_le_of_le_ofReal (by
        have := le_min (Real.sqrt_nonneg ‖ξ‖) (Real.sqrt_nonneg ‖ξ - 1‖)
        positivity) h
    have hR : ‖kernelR x ξ‖ = ‖x * (x - 1)‖ / (‖ξ‖ * ‖ξ - 1‖ * ‖ξ - x‖) := by
      unfold kernelR
      rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        show (ξ : ℂ) - 1 = ((ξ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        show (ξ : ℂ) - x = ((ξ - x : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, norm_mul]
    have hmin := gl16_min_sqrt_div_le h0 h1
    have ha : 0 < ‖ξ‖ := norm_pos_iff.2 h0
    have hb : 0 < ‖ξ - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 h1)
    have hc : 0 < ‖ξ - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
    have hπ := Real.pi_pos
    rw [norm_mul, hR]
    have hK0 : 0 ≤ ∫ ζ, ‖LiZhongQC.ahKer (ξ : ℂ) ζ‖ := integral_nonneg fun _ => norm_nonneg _
    calc ‖V ξ‖ * (‖x * (x - 1)‖ / (‖ξ‖ * ‖ξ - 1‖ * ‖ξ - x‖))
        ≤ (1 / π) * (C * min √‖ξ‖ √‖ξ - 1‖ * (1 + ‖ξ‖)) * k * (‖x * (x - 1)‖ / (‖ξ‖ * ‖ξ - 1‖ * ‖ξ - x‖)) := by
          refine mul_le_mul_of_nonneg_right (hVξ.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKξ (by positivity)) hk0
      _ = (1 / π) * k * C * ‖x * (x - 1)‖ * (min √‖ξ‖ √‖ξ - 1‖ * (1 + ‖ξ‖) / (‖ξ‖ * ‖ξ - 1‖)) * ‖ξ - x‖⁻¹ := by
          field_simp
      _ ≤ (1 / π) * k * C * ‖x * (x - 1)‖ * (3 * (‖ξ‖ ^ (-(1 / 2 : ℝ)) + ‖ξ - 1‖ ^ (-(1 / 2 : ℝ)))) * ‖ξ - x‖⁻¹ := by
          gcongr
      _ = M * ((‖ξ‖ ^ (-(1 / 2 : ℝ)) + ‖ξ - 1‖ ^ (-(1 / 2 : ℝ))) * ‖ξ - x‖⁻¹) := by
          rw [hM]
          ring
  -- domination on the domain, off the null set `{0, 1}`
  refine ((gl16_maj_integrableOn x hε).const_mul M).mono' hmeas.restrict ?_
  have hnull : ∀ᵐ ξ ∂(volume : Measure ℝ), ξ ∉ ({0, 1} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 ((Set.toFinite _).countable.measure_zero volume)
  filter_upwards [ae_restrict_of_ae hnull, ae_restrict_mem (show MeasurableSet {ξ : ℝ | ε < |ξ - x|} from
    measurableSet_lt measurable_const (measurable_id.sub_const x).abs)] with ξ hξ hdom
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hξ
  have hx : ξ ≠ x := by
    intro h
    rw [h, sub_self, abs_zero] at hdom
    linarith
  exact hbound ξ hξ.1 hξ.2 hx

/-- Helper for `eq16_27` (§16.7, P4). The joint integrability of `μ(ζ) G_x(u, ζ)` on `(ε, ∞) × ℂ` for `ε ≥ 0`
(P1d restricted, `μ` bounded). -/
theorem gl16_muG_integrable {μ : ℂ → ℂ} {k : ℝ} (hμ : LiZhongQC.IsBeltramiCoeff μ univ k) (x : ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) :
    Integrable (fun q : ℝ × ℂ => μ q.2 * ((x : ℂ) * (x - 1) / (q.2 * (q.2 - 1)) *
      (2 / ((q.2 - x) ^ 2 - (q.1 : ℂ) ^ 2)))) ((volume.restrict (Ioi ε)).prod volume) := by
  obtain ⟨hμm, hμb, -⟩ := gl16_beltrami_facts hμ
  have hG := gl16_G_integrable x
  have hG' : Integrable (fun q : ℝ × ℂ => (x : ℂ) * (x - 1) / (q.2 * (q.2 - 1)) *
      (2 / ((q.2 - x) ^ 2 - (q.1 : ℂ) ^ 2))) ((volume.restrict (Ioi ε)).prod volume) := by
    have e1 : (volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℂ) =
        ((volume : Measure ℝ).prod (volume : Measure ℂ)).restrict (Ioi 0 ×ˢ univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    have e2 : (volume.restrict (Ioi ε)).prod (volume : Measure ℂ) =
        ((volume : Measure ℝ).prod (volume : Measure ℂ)).restrict (Ioi ε ×ˢ univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [e1] at hG
    rw [e2]
    exact IntegrableOn.mono_set hG (prod_mono (Ioi_subset_Ioi hε) subset_rfl)
  refine hG'.bdd_mul (c := k) (hμm.comp_snd) ?_
  exact MeasureTheory.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd hμb

/-- Helper for `eq16_27` (§16.7, P4). Fubini on `(ε, ∞) × ℂ`. The truncated principal-value integral of `V R(x, ·)`
is computed through the representation (16.21), the fold P3 and the cancellation. -/
theorem gl16_pv_trunc {V μ : ℂ → ℂ} (hV : IsKernelRepr V μ) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ ξ in {ξ : ℝ | ε < |ξ - x|}, V ξ * kernelR x ξ =
      -(1 / π) * ∫ ζ, μ ζ * ((x : ℂ) * (x - 1) / (ζ * (ζ - 1))) *
        ∫ u in Ioi ε, 2 / ((ζ - x) ^ 2 - (u : ℂ) ^ 2) := by
  have hint := gl16_V_integrableOn hV x hε
  obtain ⟨⟨k, hk⟩, -, hrep⟩ := hV
  obtain ⟨hμm, hμb, hk0⟩ := gl16_beltrami_facts hk
  rw [(gl16_setIntegral_fold hε.le hint).2]
  -- the integrability of `μ K_p`
  have hμK : ∀ p : ℂ, Integrable fun ζ => μ ζ * kernelR p ζ := fun p =>
    (LiZhongQC.ah_ker_integrable p).bdd_mul (c := k) hμm hμb
  -- for `u > ε` off four points, the folded integrand is `−(1/π) ∫ μ G`
  have hnull : ∀ᵐ u ∂(volume.restrict (Ioi ε)), x + u ≠ 0 ∧ x + u ≠ 1 ∧ x - u ≠ 0 ∧ x - u ≠ 1 := by
    have hfin : ({-x, 1 - x, x, x - 1} : Set ℝ).Countable := (Set.toFinite _).countable
    have h := measure_eq_zero_iff_ae_notMem.1 (hfin.measure_zero volume)
    refine ae_restrict_of_ae (h.mono fun u hu => ?_)
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hu
    obtain ⟨h1, h2, h3, h4⟩ := hu
    exact ⟨fun h => h1 (by linarith), fun h => h2 (by linarith), fun h => h3 (by linarith),
      fun h => h4 (by linarith)⟩
  have h0 : ∀ᵐ ζ : ℂ, ζ.im ≠ 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 LiZhongQC.gzE_volume_im_eq_zero] with ζ hζ
    exact hζ
  have hpt : ∀ᵐ u ∂(volume.restrict (Ioi ε)),
      V ((x + u : ℝ) : ℂ) * kernelR x ((x + u : ℝ) : ℂ) + V ((x - u : ℝ) : ℂ) * kernelR x ((x - u : ℝ) : ℂ) =
        -(1 / π) * ∫ ζ, μ ζ * ((x : ℂ) * (x - 1) / (ζ * (ζ - 1)) * (2 / ((ζ - x) ^ 2 - (u : ℂ) ^ 2))) := by
    filter_upwards [hnull, ae_restrict_mem measurableSet_Ioi] with u ⟨h₁, h₂, h₃, h₄⟩ hu
    have hu0 : u ≠ 0 := (hε.trans hu).ne'
    rw [hrep, hrep]
    have e : ∀ a b c d : ℂ, -(1 / (π : ℂ)) * a * b + -(1 / (π : ℂ)) * c * d = -(1 / (π : ℂ)) * (a * b + c * d) :=
      fun a b c d => by ring
    rw [e]
    congr 1
    rw [← integral_mul_const, ← integral_mul_const, ← integral_add ((hμK _).mul_const _) ((hμK _).mul_const _)]
    refine integral_congr_ae (h0.mono fun ζ hζ => ?_)
    simp only
    rw [← gl16_kernelR_sym hζ hu0 h₁ h₂ h₃ h₄]
    ring
  rw [integral_congr_ae hpt, integral_const_mul]
  congr 1
  -- Fubini, then pull the `u`-independent factor out of the inner integral
  have hF := gl16_muG_integrable hk x hε.le
  rw [integral_integral_swap (f := fun (u : ℝ) (ζ : ℂ) => μ ζ * ((x : ℂ) * (x - 1) / (ζ * (ζ - 1)) *
    (2 / ((ζ - x) ^ 2 - (u : ℂ) ^ 2)))) hF]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
  simp only
  rw [integral_const_mul, integral_const_mul, mul_assoc]

/-- Helper for `eq16_27` (§16.7, P5). For `Im ζ ≠ 0`, `∫_ε^∞ g → ∫₀^∞ g` as `ε → 0+`, for `g = 2/((ζ − x)² − u²)`
(dominated convergence for indicators). -/
theorem gl16_T_tendsto {w : ℂ} (hw : w.im ≠ 0) :
    Tendsto (fun ε : ℝ => ∫ u in Ioi ε, 2 / (w ^ 2 - (u : ℂ) ^ 2)) (𝓝[>] 0)
      (𝓝 (∫ u in Ioi (0 : ℝ), 2 / (w ^ 2 - (u : ℂ) ^ 2))) := by
  have hint := (gl16_T0 hw).1
  have heq : ∀ᶠ (ε : ℝ) in 𝓝[>] (0 : ℝ), ∫ u in Ioi ε, 2 / (w ^ 2 - (u : ℂ) ^ 2) =
      ∫ u in Ioi (0 : ℝ), (Ioi ε).indicator (fun u : ℝ => 2 / (w ^ 2 - (u : ℂ) ^ 2)) u := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_right.2 (le_of_lt hε)]
  refine Tendsto.congr' (EventuallyEq.symm heq) ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun u => ‖2 / (w ^ 2 - (u : ℂ) ^ 2)‖) ?_ ?_ hint.norm ?_
  · exact Filter.Eventually.of_forall fun ε =>
      ((gl16_T0_continuous hw).aestronglyMeasurable.indicator measurableSet_Ioi).restrict
  · exact Filter.Eventually.of_forall fun ε => Filter.Eventually.of_forall fun u => by
      by_cases hu : u ∈ Ioi ε
      · rw [indicator_of_mem hu]
      · rw [indicator_of_notMem hu, norm_zero]
        exact norm_nonneg _
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun u hu => ?_
    have hu' : (0 : ℝ) < u := hu
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [Ioo_mem_nhdsGT hu'] with ε hε
    rw [indicator_of_mem (show u ∈ Ioi ε from hε.2)]

/-- Helper for `eq16_27` (§16.7, P5). Dominated convergence as `ε → 0+`, with the majorant `k ∫₀^∞ |G_x(u, ζ)| du`
(integrable by P1). -/
theorem gl16_pv_tendsto {μ : ℂ → ℂ} {k : ℝ} (hμ : LiZhongQC.IsBeltramiCoeff μ univ k) (x : ℝ) :
    Tendsto (fun ε : ℝ => ∫ ζ, μ ζ * ((x : ℂ) * (x - 1) / (ζ * (ζ - 1))) *
        ∫ u in Ioi ε, 2 / ((ζ - x) ^ 2 - (u : ℂ) ^ 2)) (𝓝[>] 0)
      (𝓝 (∫ ζ, μ ζ * ((x : ℂ) * (x - 1) / (ζ * (ζ - 1))) *
        ∫ u in Ioi (0 : ℝ), 2 / ((ζ - x) ^ 2 - (u : ℂ) ^ 2))) := by
  obtain ⟨hμm, hμb, hk0⟩ := gl16_beltrami_facts hμ
  have hG := gl16_G_integrable x
  set G : ℝ × ℂ → ℂ := fun q => (x : ℂ) * (x - 1) / (q.2 * (q.2 - 1)) * (2 / ((q.2 - x) ^ 2 - (q.1 : ℂ) ^ 2))
    with hGdef
  have h0 : ∀ᵐ ζ : ℂ, ζ.im ≠ 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 LiZhongQC.gzE_volume_im_eq_zero] with ζ hζ
    exact hζ
  -- the `ζ`-integrand as `μ ζ * ∫_ε^∞ G(u, ζ) du`
  have hform : ∀ ε : ℝ, ∀ ζ : ℂ, μ ζ * ((x : ℂ) * (x - 1) / (ζ * (ζ - 1))) *
      ∫ u in Ioi ε, 2 / ((ζ - x) ^ 2 - (u : ℂ) ^ 2) = μ ζ * ∫ u in Ioi ε, G (u, ζ) := by
    intro ε ζ
    simp only [hGdef]
    rw [integral_const_mul, mul_assoc]
  simp only [hform]
  refine tendsto_integral_filter_of_dominated_convergence (fun ζ => k * ∫ u in Ioi (0 : ℝ), ‖G (u, ζ)‖) ?_ ?_
    (hG.integral_norm_prod_right.const_mul k) ?_
  · -- measurability
    refine Filter.Eventually.of_forall fun ε => hμm.mul ?_
    have hGm : Measurable G := by
      rw [hGdef]
      fun_prop
    exact (hGm.stronglyMeasurable.integral_prod_left' (μ := volume.restrict (Ioi ε))).aestronglyMeasurable
  · -- the bound
    filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [hμb, h0] with ζ hζ hζim
    rw [norm_mul]
    refine mul_le_mul hζ ?_ (norm_nonneg _) hk0
    have hgi : IntegrableOn (fun u : ℝ => G (u, ζ)) (Ioi 0) := by
      have hw : (ζ - (x : ℂ)).im ≠ 0 := by simpa using hζim
      simp only [hGdef]
      exact (gl16_T0 (w := ζ - x) hw).1.const_mul _
    calc ‖∫ u in Ioi ε, G (u, ζ)‖ ≤ ∫ u in Ioi ε, ‖G (u, ζ)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ u in Ioi (0 : ℝ), ‖G (u, ζ)‖ :=
          setIntegral_mono_set hgi.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            (Ioi_subset_Ioi (le_of_lt hε)).eventuallySubset
  · -- the pointwise limit
    filter_upwards [h0] with ζ hζ
    refine Tendsto.const_mul _ ?_
    have hw : (ζ - x).im ≠ 0 := by simpa using hζ
    have h := (gl16_T_tendsto hw).const_mul ((x : ℂ) * (x - 1) / (ζ * (ζ - 1)))
    simpa [hGdef, integral_const_mul] using h

/-- **Formula (16.27)** (§16.7, l. 12590). If `V` is represented by `μ` as in (16.21), then
`HV(x) = −(1/π) ∬ μ̃(ζ) R(x, ζ) dξ dη`. -/
theorem eq16_27 {V μ : ℂ → ℂ} (hV : IsKernelRepr V μ) (x : ℝ) :
    hilbertPV V x = -(1 / π) * ∫ ζ, hilbertLift μ ζ * kernelR x ζ := by
  obtain ⟨k, hk⟩ := hV.1
  -- the real axis is null, and off it the limit integrand is `π · hilbertLift μ · kernelR x` (P2)
  have h0 : ∀ᵐ ζ : ℂ, ζ.im ≠ 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 LiZhongQC.gzE_volume_im_eq_zero] with ζ hζ
    exact hζ
  have hae : (fun ζ => μ ζ * ((x : ℂ) * (x - 1) / (ζ * (ζ - 1))) *
      ∫ u in Ioi (0 : ℝ), 2 / ((ζ - x) ^ 2 - (u : ℂ) ^ 2)) =ᵐ[volume]
        fun ζ => (π : ℂ) * (hilbertLift μ ζ * kernelR x ζ) := by
    filter_upwards [h0] with ζ hζ
    have him : (ζ - (x : ℂ)).im = ζ.im := by simp
    rw [(gl16_T0 (by rw [him]; exact hζ)).2, him]
    unfold hilbertLift kernelR
    split_ifs with h1 h2
    · simp only [div_eq_mul_inv, mul_inv]
      ring
    · simp only [div_eq_mul_inv, mul_inv]
      ring
    · exact absurd (le_antisymm (not_lt.1 h1) (not_lt.1 h2)) hζ
  -- the truncations through Fubini (P4) and their limit (P5)
  unfold hilbertPV
  refine Tendsto.limUnder_eq ?_
  have hlim := (gl16_pv_tendsto hk x).const_mul (-(1 / π) * (1 / π) : ℂ)
  have htr : (fun ε : ℝ => (1 / π : ℂ) * ∫ ξ in {ξ : ℝ | ε < |ξ - x|}, V ξ * kernelR x ξ) =ᶠ[𝓝[>] 0]
      fun ε => (-(1 / π) * (1 / π) : ℂ) * ∫ ζ, μ ζ * ((x : ℂ) * (x - 1) / (ζ * (ζ - 1))) *
        ∫ u in Ioi ε, 2 / ((ζ - x) ^ 2 - (u : ℂ) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [gl16_pv_trunc hV x hε]
    ring
  have hL : (-(1 / π) * (1 / π) : ℂ) * ∫ ζ, μ ζ * ((x : ℂ) * (x - 1) / (ζ * (ζ - 1))) *
      ∫ u in Ioi (0 : ℝ), 2 / ((ζ - x) ^ 2 - (u : ℂ) ^ 2) = -(1 / π) * ∫ ζ, hilbertLift μ ζ * kernelR x ζ := by
    rw [integral_congr_ae hae, integral_const_mul]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rw [← hL]
  exact hlim.congr' htr.symm

/-- **Theorem 7** (§16.7, l. 12596). The Hilbert transform preserves `Z` and `Z₀` (modulo quadratic polynomials),
lifts to `μ ↦ μ̃` of (16.26), and satisfies `H² = −1` modulo quadratic polynomials: it gives the almost complex
structures. **[CORRECTION]** `H` acts on the normalized representative `zNormalize V` (l. 12537); on a field not
vanishing at `0`, `1`, `hilbertPV` is the junk `0`, and `H² = −1` would fail. -/
theorem thm16_7 {V : ℂ → ℂ} (hVr : ∀ x : ℝ, (V x).im = 0) (hV : V ∈ zCrSet extRealLine) :
    (∃ W : ℂ → ℂ, W ∈ zCrSet extRealLine ∧ (∀ x : ℝ, W x = hilbertPV (zNormalize V) x) ∧
      (HasVanishingCrDistortion extRealLine V → HasVanishingCrDistortion extRealLine W)) ∧
    (∀ μ : ℂ → ℂ, IsKernelRepr V μ → ∀ W : ℂ → ℂ, (∀ x : ℝ, W x = hilbertPV (zNormalize V) x) →
      IsKernelRepr W (hilbertLift μ)) ∧
    ∀ W : ℂ → ℂ, (∀ x : ℝ, W x = hilbertPV (zNormalize V) x) →
      ∃ a b c : ℂ, ∀ x : ℝ, hilbertPV (zNormalize W) x = -V x + a * x ^ 2 + b * x + c := by
  sorry

end GardinerLakic2000
