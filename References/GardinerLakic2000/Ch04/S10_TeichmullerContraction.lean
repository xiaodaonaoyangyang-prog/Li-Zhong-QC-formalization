import References.GardinerLakic2000.Ch04.S09_FundamentalInequalities

/-!
# Gardiner–Lakic 2000, Ch. 4 §4.10 Teichmüller contraction

Source `teichmuller.txt`, lines 4387–4488.

* Definition (efficiency `e(μ) = ‖μ‖∞ − k₀`, l. 4388–4392; Definition 3 (1), the efficiency `e(kμ) = k − k₀` at `k`,
  l. 4424) — `efficiency`
* Definition (infinitesimal efficiency `j(μ) = ‖μ‖∞ − sup Re ∬ μφ`, l. 4394–4400) — `jEfficiency`
* Definition (`I(kμ)`, `J(kμ)`, l. 4410–4420) — `bigI`, `bigJ`
* Definition 3 (2), (3) (the `i`-value and the `j`-value at `k`, l. 4422–4427) — `iValue`, `jValue`
* Theorem 10 (Teichmüller contraction, l. 4429) — `thm4_10_a` (e and i), `thm4_10_b` (i and j)
* Lemma 5 (l. 4471; cited Ch. 14, l. 10981, 10993, 11015) — `lemma4_5`
* Corollary 2 (Hamilton–Krushkal, Reich–Strebel, l. 4479; cited l. 7265) — `cor4_10_2`

Not items (DESIGN §3): the claim `C₁ e(μ) ≤ j(μ) ≤ C₂ e(μ)` of l. 4402–4408 (restated as Theorem 10), the geodesic
remark (l. 4408; §7.4), the historical remark after Corollary 2 (l. 4487).

**[reading] Theorem 10.** The standing assumption is `‖μ‖∞ = 1` (l. 4410). The constants depend on `k₁`
(`C₂ = (1 − k₁)⁻²`), so the printed range "for all `k` with `0 < k < 1`" (GL8:4296) is read `0 < k ≤ k₁`; Lemma 5,
which gives `C₃`, also needs `k ≤ k₁`. Near misses for Corollary 2: `LiZhongQC.thm36_2_hamilton` (the ⇒ half, in the
Fuchsian model) and `LiZhongQC.thm35_4` (the ⇐ half on the disc).

**Conventions.** Suprema over `φ ∈ A(R)` with `‖φ‖ = 1` are real suprema of bounded families (bounded by `‖μ‖∞`); the
statements assume `A(R) ≠ 0`. The coefficient `kμ` is given as an element `ν ∈ M(R)` with `ν = kμ`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsFuchsian IsUniformization quadDiffNorm)

variable {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
  [IsManifold 𝓘(ℂ) ω R]

/-- **Definition** (efficiency, §4.10, l. 4388; Definition 3 (1), l. 4424). `e(μ) = ‖μ‖∞ − k₀`, `k₀` the norm of an
extremal representative of the class of `μ`; for `‖μ‖∞ = 1`, `e(kμ) = k − k₀`. -/
def efficiency (p : UpperHalfPlane → R) (ν : beltramiBall R) : ℝ :=
  (beltramiNormRS ν.1).toReal - extremalK p (Quot.mk (teichRel p) ν)

/-- **Definition** (infinitesimal efficiency, §4.10, l. 4394). `j(μ) = ‖μ‖∞ − sup_{‖φ‖=1} Re ∬_R μφ`. -/
def jEfficiency (μ : R → ℂ → ℂ) : ℝ :=
  (beltramiNormRS μ).toReal -
    ⨆ (φ : R → ℂ → ℂ) (_ : φ ∈ integrableHolQDSet R ∧ quadDiffNorm φ = 1), (pairingRS φ μ).re

/-- **Definition** (§4.10, l. 4413). `I(μ) = sup_{‖φ‖=1} |Re ∬_R μφ/(1 − |μ|²)|`. -/
def bigI (μ : R → ℂ → ℂ) : ℝ :=
  ⨆ (φ : R → ℂ → ℂ) (_ : φ ∈ integrableHolQDSet R ∧ quadDiffNorm φ = 1),
    |(pairingRS φ fun x z => μ x z / (1 - ‖μ x z‖ ^ 2)).re|

/-- **Definition** (§4.10, l. 4419). `J(μ) = sup_{‖φ‖=1} |Re ∬_R μφ|`. -/
def bigJ (μ : R → ℂ → ℂ) : ℝ :=
  ⨆ (φ : R → ℂ → ℂ) (_ : φ ∈ integrableHolQDSet R ∧ quadDiffNorm φ = 1), |(pairingRS φ μ).re|

/-- **Definition 3** (2) (§4.10, l. 4426). The `i`-value of `μ` at `k`: `i(kμ) = k/(1 − k²) − I(kμ)`. -/
def iValue (k : ℝ) (μ : R → ℂ → ℂ) : ℝ := k / (1 - k ^ 2) - bigI fun x z => k * μ x z

/-- **Definition 3** (3) (§4.10, l. 4427). The `j`-value of `μ` at `k`: `j(kμ) = k − J(kμ)`. -/
def jValue (k : ℝ) (μ : R → ℂ → ℂ) : ℝ := k - bigJ fun x z => k * μ x z

/-- **Theorem 10** (Teichmüller contraction, §4.10, l. 4429), the efficiency and the `i`-value. Fix `0 < k₁ < 1` and
`μ` with `‖μ‖∞ = 1`. Then `C₁ e(kμ) ≤ i(kμ) ≤ C₂ e(kμ)` for `0 < k ≤ k₁`, with `C₁ = 1/4` and `C₂ = (1 − k₁)⁻²`
[reading of the range of `k`]. -/
theorem thm4_10_a {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (hA : ∃ φ ∈ integrableHolQDSet R, quadDiffNorm φ = 1) {k₁ : ℝ} (hk₁ : 0 < k₁)
    (hk₁' : k₁ < 1) {μ : R → ℂ → ℂ} (hμ : μ ∈ beltramiSpace R) (hμ1 : beltramiNormRS μ = 1) {k : ℝ} (hk : 0 < k)
    (hkk : k ≤ k₁) (ν : beltramiBall R) (hν : ν.1 = fun x z => k * μ x z) :
    1 / 4 * efficiency p ν ≤ iValue k μ ∧ iValue k μ ≤ ((1 - k₁) ^ 2)⁻¹ * efficiency p ν := by
  sorry

/-- Helper for Theorem 10 and Lemma 5. Lemma 5 in real coordinates `x = Re z`, `r = |z|`, allowing `r = 1`:
`k − kx ≤ k/(1 − k²) − kx/(1 − k²r²) ≤ (2/(1 − k₁)²)(k − kx)` for `0 ≤ k ≤ k₁ < 1`, `|x| ≤ r ≤ 1`. -/
theorem gl4_lemma4_5_real {k k₁ x r : ℝ} (hk : 0 ≤ k) (hkk : k ≤ k₁) (hk₁ : k₁ < 1) (hxr : x ≤ r)
    (hrx : -r ≤ x) (hr1 : r ≤ 1) :
    k - k * x ≤ k / (1 - k ^ 2) - k * x / (1 - k ^ 2 * r ^ 2) ∧
      k / (1 - k ^ 2) - k * x / (1 - k ^ 2 * r ^ 2) ≤ 2 / (1 - k₁) ^ 2 * (k - k * x) := by
  have hk1 : k < 1 := lt_of_le_of_lt hkk hk₁
  have hr0 : 0 ≤ r := by linarith
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hx1 : x ≤ 1 := hxr.trans hr1
  have ha : 0 < 1 - k ^ 2 := by nlinarith
  have hkr : k ^ 2 * r ^ 2 ≤ k ^ 2 := by nlinarith [sq_nonneg k]
  have hb : 0 < 1 - k ^ 2 * r ^ 2 := by linarith
  have hab : 1 - k ^ 2 ≤ 1 - k ^ 2 * r ^ 2 := by linarith
  have hk3 : 0 ≤ k ^ 3 := pow_nonneg hk 3
  have hxr2 : x * r ^ 2 ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hxr (sq_nonneg r), mul_le_mul_of_nonneg_left hr1 (sq_nonneg r)]
  constructor
  · rw [← sub_nonneg]
    have e : k / (1 - k ^ 2) - k * x / (1 - k ^ 2 * r ^ 2) - (k - k * x) =
        k ^ 3 * ((1 - k ^ 2 * r ^ 2) - (1 - k ^ 2) * (x * r ^ 2)) / ((1 - k ^ 2) * (1 - k ^ 2 * r ^ 2)) := by
      field_simp
      ring
    rw [e]
    refine div_nonneg (mul_nonneg hk3 ?_) (mul_pos ha hb).le
    nlinarith [mul_le_mul_of_nonneg_left hxr2 ha.le]
  · have e : k / (1 - k ^ 2) - k * x / (1 - k ^ 2 * r ^ 2) =
        k * (1 - x) / (1 - k ^ 2) + k ^ 3 * (x * (1 - r ^ 2)) / ((1 - k ^ 2) * (1 - k ^ 2 * r ^ 2)) := by
      field_simp
      ring
    have hE : k ^ 3 * (x * (1 - r ^ 2)) / ((1 - k ^ 2) * (1 - k ^ 2 * r ^ 2)) ≤
        2 * k ^ 3 * (1 - x) / (1 - k ^ 2) ^ 2 := by
      rw [div_le_div_iff₀ (mul_pos ha hb) (pow_pos ha 2)]
      have key : x * (1 - r ^ 2) * (1 - k ^ 2) ≤ 2 * (1 - x) * (1 - k ^ 2 * r ^ 2) := by
        rcases le_or_gt x 0 with hx | hx
        · have hneg : x * (1 - r ^ 2) * (1 - k ^ 2) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hx (by linarith)) ha.le
          have hpos : 0 ≤ 2 * (1 - x) * (1 - k ^ 2 * r ^ 2) :=
            mul_nonneg (mul_nonneg zero_le_two (by linarith)) hb.le
          linarith
        · have hxx : x * x ≤ r * r := mul_le_mul hxr hxr hx.le hr0
          have h1 : x * (1 - r ^ 2) ≤ 2 * (1 - x) := by
            nlinarith [mul_nonneg hx.le (by linarith : (0 : ℝ) ≤ 1 - x)]
          nlinarith [mul_le_mul_of_nonneg_right h1 ha.le,
            mul_le_mul_of_nonneg_left hab (by linarith : (0 : ℝ) ≤ 2 * (1 - x))]
      nlinarith [mul_le_mul_of_nonneg_left key (mul_nonneg hk3 ha.le)]
    have hC : k * (1 - x) / (1 - k ^ 2) + 2 * k ^ 3 * (1 - x) / (1 - k ^ 2) ^ 2 ≤
        2 / (1 - k₁) ^ 2 * (k - k * x) := by
      have hkx : 0 ≤ k * (1 - x) := mul_nonneg hk (by linarith)
      have e2 : k * (1 - x) / (1 - k ^ 2) + 2 * k ^ 3 * (1 - x) / (1 - k ^ 2) ^ 2 =
          k * (1 - x) * ((1 + k ^ 2) / (1 - k ^ 2) ^ 2) := by
        field_simp
        ring
      have hk₁0 : 0 < 1 - k₁ := by linarith
      have h3 : (1 + k ^ 2) / (1 - k ^ 2) ^ 2 ≤ 2 / (1 - k₁) ^ 2 := by
        rw [div_le_div_iff₀ (pow_pos ha 2) (pow_pos hk₁0 2)]
        have h1 : (1 - k₁) ^ 2 ≤ (1 - k) ^ 2 := by nlinarith
        have h2 : 1 + k ^ 2 ≤ (1 + k) ^ 2 := by nlinarith
        have h4 : (1 + k ^ 2) * (1 - k₁) ^ 2 ≤ (1 + k) ^ 2 * (1 - k) ^ 2 :=
          mul_le_mul h2 h1 (sq_nonneg _) (sq_nonneg _)
        have h5 : (1 + k) ^ 2 * (1 - k) ^ 2 = (1 - k ^ 2) ^ 2 := by ring
        nlinarith [sq_nonneg (1 - k ^ 2)]
      rw [e2, show k - k * x = k * (1 - x) by ring, mul_comm (2 / (1 - k₁) ^ 2)]
      exact mul_le_mul_of_nonneg_left h3 hkx
    rw [e]
    linarith

/-- Helper for Theorem 10. Lemma 5 against the weight `|φ|` at one point: with `u = φ/|φ|` and `|m| ≤ 1`,
`|φ|(k − k Re(mu)) ≤ |φ|(k/(1 − k²) − k Re(mu)/(1 − |km|²)) ≤ (2/(1 − k₁)²) |φ|(k − k Re(mu))`. -/
theorem gl4_pt_ineq {k k₁ : ℝ} (hk : 0 ≤ k) (hkk : k ≤ k₁) (hk₁ : k₁ < 1) {m φv : ℂ} (hm : ‖m‖ ≤ 1) :
    ‖φv‖ * (k - k * (m * (φv / (‖φv‖ : ℂ))).re) ≤
        ‖φv‖ * (k / (1 - k ^ 2) - k * (m * (φv / (‖φv‖ : ℂ))).re / (1 - ‖(k : ℂ) * m‖ ^ 2)) ∧
      ‖φv‖ * (k / (1 - k ^ 2) - k * (m * (φv / (‖φv‖ : ℂ))).re / (1 - ‖(k : ℂ) * m‖ ^ 2)) ≤
        2 / (1 - k₁) ^ 2 * (‖φv‖ * (k - k * (m * (φv / (‖φv‖ : ℂ))).re)) := by
  by_cases h0 : φv = 0
  · simp [h0]
  have hn : 0 < ‖φv‖ := norm_pos_iff.2 h0
  have hu : ‖φv / (‖φv‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hn.le, div_self hn.ne']
  have hmu : ‖m * (φv / (‖φv‖ : ℂ))‖ = ‖m‖ := by rw [norm_mul, hu, mul_one]
  have hkm : ‖(k : ℂ) * m‖ ^ 2 = k ^ 2 * ‖m * (φv / (‖φv‖ : ℂ))‖ ^ 2 := by
    rw [hmu, norm_mul, Complex.norm_real, Real.norm_of_nonneg hk, mul_pow]
  have h := gl4_lemma4_5_real hk hkk hk₁ (Complex.re_le_norm (m * (φv / (‖φv‖ : ℂ))))
    (neg_le_of_abs_le (Complex.abs_re_le_norm _)) (hmu.trans_le hm)
  rw [hkm]
  refine ⟨mul_le_mul_of_nonneg_left h.1 hn.le, ?_⟩
  calc _ ≤ ‖φv‖ * (2 / (1 - k₁) ^ 2 * (k - k * (m * (φv / (‖φv‖ : ℂ))).re)) :=
        mul_le_mul_of_nonneg_left h.2 hn.le
    _ = _ := by ring

/-- Helper for Theorem 10. The real parts of the integrands of `J` and `I` against the weight `|φ|`:
`Re(φ · km) = |φ| k Re(m φ/|φ|)` and `Re(φ · km/(1 − |km|²)) = |φ| k Re(m φ/|φ|)/(1 − |km|²)`. -/
theorem gl4_pt_re (k : ℝ) (m φv : ℂ) :
    (φv * ((k : ℂ) * m)).re = ‖φv‖ * (k * (m * (φv / (‖φv‖ : ℂ))).re) ∧
      (φv * ((k : ℂ) * m / (1 - (‖(k : ℂ) * m‖ : ℂ) ^ 2))).re =
        ‖φv‖ * (k * (m * (φv / (‖φv‖ : ℂ))).re / (1 - ‖(k : ℂ) * m‖ ^ 2)) := by
  by_cases h0 : φv = 0
  · simp [h0]
  have hn : (‖φv‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 h0)
  have e : φv = (‖φv‖ : ℂ) * (φv / (‖φv‖ : ℂ)) := (mul_div_cancel₀ _ hn).symm
  have hden : (1 - (‖(k : ℂ) * m‖ : ℂ) ^ 2) = ((1 - ‖(k : ℂ) * m‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  constructor
  · conv_lhs => rw [e]
    rw [show (‖φv‖ : ℂ) * (φv / (‖φv‖ : ℂ)) * ((k : ℂ) * m) =
      ((‖φv‖ * k : ℝ) : ℂ) * (m * (φv / (‖φv‖ : ℂ))) by push_cast; ring, Complex.re_ofReal_mul]
    ring
  · conv_lhs => rw [e]
    rw [hden, show (‖φv‖ : ℂ) * (φv / (‖φv‖ : ℂ)) * ((k : ℂ) * m / ((1 - ‖(k : ℂ) * m‖ ^ 2 : ℝ) : ℂ)) =
      ((‖φv‖ * k / (1 - ‖(k : ℂ) * m‖ ^ 2) : ℝ) : ℂ) * (m * (φv / (‖φv‖ : ℂ))) by push_cast; ring,
      Complex.re_ofReal_mul]
    ring

/-- Helper for Theorem 10. Lemma 5 integrated over one chart piece `Ω` against `|f|` (`f` the local expression of
`φ`, `m` that of `μ`, `|m| ≤ 1`): with `W = ∬_Ω |f|`, `A = ∬_Ω f km`, `B = ∬_Ω f km/(1 − |km|²)`,
`|A| ≤ kW`, `|B| ≤ kW/(1 − k²)` and `kW − Re A ≤ kW/(1 − k²) − Re B ≤ (2/(1 − k₁)²)(kW − Re A)`. -/
theorem gl4_piece {k k₁ : ℝ} (hk : 0 ≤ k) (hkk : k ≤ k₁) (hk₁ : k₁ < 1) {Ω : Set ℂ} (hΩ : MeasurableSet Ω)
    {f m : ℂ → ℂ} (hf : ContinuousOn f Ω) (hfi : ∫⁻ z in Ω, ENNReal.ofReal ‖f z‖ ≠ ⊤)
    (hm : AEStronglyMeasurable m (volume.restrict Ω)) (hm1 : ∀ᵐ z ∂(volume.restrict Ω), ‖m z‖ ≤ 1) :
    ‖∫ z in Ω, f z * ((k : ℂ) * m z)‖ ≤ k * ∫ z in Ω, ‖f z‖ ∧
      ‖∫ z in Ω, f z * ((k : ℂ) * m z / (1 - (‖(k : ℂ) * m z‖ : ℂ) ^ 2))‖ ≤ k / (1 - k ^ 2) * ∫ z in Ω, ‖f z‖ ∧
      k * (∫ z in Ω, ‖f z‖) - (∫ z in Ω, f z * ((k : ℂ) * m z)).re ≤
        k / (1 - k ^ 2) * (∫ z in Ω, ‖f z‖) -
          (∫ z in Ω, f z * ((k : ℂ) * m z / (1 - (‖(k : ℂ) * m z‖ : ℂ) ^ 2))).re ∧
      k / (1 - k ^ 2) * (∫ z in Ω, ‖f z‖) -
          (∫ z in Ω, f z * ((k : ℂ) * m z / (1 - (‖(k : ℂ) * m z‖ : ℂ) ^ 2))).re ≤
        2 / (1 - k₁) ^ 2 * (k * (∫ z in Ω, ‖f z‖) - (∫ z in Ω, f z * ((k : ℂ) * m z)).re) := by
  have hk1 : k < 1 := lt_of_le_of_lt hkk hk₁
  have ha : 0 < 1 - k ^ 2 := by nlinarith
  have hfm : AEStronglyMeasurable f (volume.restrict Ω) := hf.aestronglyMeasurable hΩ
  have hwi : Integrable (fun z => ‖f z‖) (volume.restrict Ω) := by
    refine ⟨hfm.norm, (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => norm_nonneg _)).2 ?_⟩
    exact lt_top_iff_ne_top.2 hfi
  -- the pointwise denominators
  have hden : ∀ z, ‖m z‖ ≤ 1 → 0 < 1 - ‖(k : ℂ) * m z‖ ^ 2 ∧
      ‖(1 - (‖(k : ℂ) * m z‖ : ℂ) ^ 2)‖ = 1 - ‖(k : ℂ) * m z‖ ^ 2 ∧ 1 - k ^ 2 ≤ 1 - ‖(k : ℂ) * m z‖ ^ 2 ∧
        ‖(k : ℂ) * m z‖ ≤ k := by
    intro z hz
    have h1 : ‖(k : ℂ) * m z‖ ≤ k := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hk]
      nlinarith [norm_nonneg (m z)]
    have h2 : ‖(k : ℂ) * m z‖ ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : 0 < 1 - ‖(k : ℂ) * m z‖ ^ 2 := by linarith
    refine ⟨h3, ?_, by linarith, h1⟩
    rw [show (1 - (‖(k : ℂ) * m z‖ : ℂ) ^ 2) = ((1 - ‖(k : ℂ) * m z‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg h3.le]
  have hbA : ∀ᵐ z ∂(volume.restrict Ω), ‖f z * ((k : ℂ) * m z)‖ ≤ k * ‖f z‖ := by
    filter_upwards [hm1] with z hz
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hk]
    calc ‖f z‖ * (k * ‖m z‖) ≤ ‖f z‖ * (k * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz hk) (norm_nonneg _)
      _ = k * ‖f z‖ := by ring
  have hbB : ∀ᵐ z ∂(volume.restrict Ω), ‖f z * ((k : ℂ) * m z / (1 - (‖(k : ℂ) * m z‖ : ℂ) ^ 2))‖ ≤
      k / (1 - k ^ 2) * ‖f z‖ := by
    filter_upwards [hm1] with z hz
    obtain ⟨h3, h4, h5, h1⟩ := hden z hz
    rw [norm_mul, norm_div, h4]
    have h6 : ‖(k : ℂ) * m z‖ / (1 - ‖(k : ℂ) * m z‖ ^ 2) ≤ k / (1 - k ^ 2) := by
      rw [div_le_div_iff₀ h3 ha]
      nlinarith [norm_nonneg ((k : ℂ) * m z), mul_nonneg (norm_nonneg ((k : ℂ) * m z)) hk]
    calc ‖f z‖ * (‖(k : ℂ) * m z‖ / (1 - ‖(k : ℂ) * m z‖ ^ 2)) ≤ ‖f z‖ * (k / (1 - k ^ 2)) :=
          mul_le_mul_of_nonneg_left h6 (norm_nonneg _)
      _ = k / (1 - k ^ 2) * ‖f z‖ := mul_comm _ _
  have hmB : AEStronglyMeasurable (fun z => f z * ((k : ℂ) * m z / (1 - (‖(k : ℂ) * m z‖ : ℂ) ^ 2)))
      (volume.restrict Ω) :=
    (hfm.aemeasurable.mul ((hm.aemeasurable.const_mul _).div
      (((hm.aemeasurable.const_mul (k : ℂ)).norm.complex_ofReal).pow_const 2 |>.const_sub 1))).aestronglyMeasurable
  have hAi : Integrable (fun z => f z * ((k : ℂ) * m z)) (volume.restrict Ω) :=
    Integrable.mono' (hwi.const_mul k) (hfm.mul (hm.const_mul _)) hbA
  have hBi : Integrable (fun z => f z * ((k : ℂ) * m z / (1 - (‖(k : ℂ) * m z‖ : ℂ) ^ 2)))
      (volume.restrict Ω) :=
    Integrable.mono' (hwi.const_mul (k / (1 - k ^ 2))) hmB hbB
  have hAre : Integrable (fun z => (f z * ((k : ℂ) * m z)).re) (volume.restrict Ω) := hAi.re
  have hBre : Integrable (fun z => (f z * ((k : ℂ) * m z / (1 - (‖(k : ℂ) * m z‖ : ℂ) ^ 2))).re)
      (volume.restrict Ω) := hBi.re
  refine ⟨?_, ?_, ?_⟩
  · rw [← integral_const_mul]
    exact norm_integral_le_of_norm_le (hwi.const_mul k) hbA
  · rw [← integral_const_mul]
    exact norm_integral_le_of_norm_le (hwi.const_mul _) hbB
  -- the two inequalities, pointwise from `gl4_pt_ineq`
  have eA : k * (∫ z in Ω, ‖f z‖) - (∫ z in Ω, f z * ((k : ℂ) * m z)).re =
      ∫ z in Ω, ‖f z‖ * (k - k * (m z * (f z / (‖f z‖ : ℂ))).re) := by
    have hre : (∫ z in Ω, f z * ((k : ℂ) * m z)).re = ∫ z in Ω, (f z * ((k : ℂ) * m z)).re :=
      (integral_re hAi).symm
    rw [hre, ← integral_const_mul, ← integral_sub (hwi.const_mul k) hAre]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [(gl4_pt_re k (m z) (f z)).1]
    ring
  have eB : k / (1 - k ^ 2) * (∫ z in Ω, ‖f z‖) -
      (∫ z in Ω, f z * ((k : ℂ) * m z / (1 - (‖(k : ℂ) * m z‖ : ℂ) ^ 2))).re =
      ∫ z in Ω, ‖f z‖ * (k / (1 - k ^ 2) - k * (m z * (f z / (‖f z‖ : ℂ))).re / (1 - ‖(k : ℂ) * m z‖ ^ 2)) := by
    have hre : (∫ z in Ω, f z * ((k : ℂ) * m z / (1 - (‖(k : ℂ) * m z‖ : ℂ) ^ 2))).re =
        ∫ z in Ω, (f z * ((k : ℂ) * m z / (1 - (‖(k : ℂ) * m z‖ : ℂ) ^ 2))).re :=
      (integral_re hBi).symm
    rw [hre, ← integral_const_mul, ← integral_sub (hwi.const_mul _) hBre]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [(gl4_pt_re k (m z) (f z)).2]
    ring
  have iA : Integrable (fun z => ‖f z‖ * (k - k * (m z * (f z / (‖f z‖ : ℂ))).re)) (volume.restrict Ω) :=
    ((hwi.const_mul k).sub hAre).congr (Filter.Eventually.of_forall fun z => by
      simp only [Pi.sub_apply]
      rw [(gl4_pt_re k (m z) (f z)).1]
      ring)
  have iB : Integrable (fun z => ‖f z‖ * (k / (1 - k ^ 2) -
      k * (m z * (f z / (‖f z‖ : ℂ))).re / (1 - ‖(k : ℂ) * m z‖ ^ 2))) (volume.restrict Ω) :=
    ((hwi.const_mul (k / (1 - k ^ 2))).sub hBre).congr (Filter.Eventually.of_forall fun z => by
      simp only [Pi.sub_apply]
      rw [(gl4_pt_re k (m z) (f z)).2]
      ring)
  rw [eA, eB]
  refine ⟨integral_mono_ae iA iB ?_, ?_⟩
  · filter_upwards [hm1] with z hz
    exact (gl4_pt_ineq hk hkk hk₁ hz).1
  · rw [← integral_const_mul]
    refine integral_mono_ae iB (iA.const_mul _) ?_
    filter_upwards [hm1] with z hz
    exact (gl4_pt_ineq hk hkk hk₁ hz).2

/-- Helper for Theorem 10. `gl4_piece` summed over a chart partition `(x, P)` on which the weights `∬ |φ|` add up
to `‖φ‖ = 1`: for `A = Σ_i ∬_{Ω_i} φ kμ` and `B = Σ_i ∬_{Ω_i} φ kμ/(1 − |kμ|²)` (`Ω_i` the chart images of the
pieces), `|Re A| ≤ k`, `|Re B| ≤ k/(1 − k²)` and `k − Re A ≤ k/(1 − k²) − Re B ≤ (2/(1 − k₁)²)(k − Re A)`. -/
theorem gl4_phi_sum {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {k k₁ : ℝ} (hk : 0 ≤ k) (hkk : k ≤ k₁)
    (hk₁ : k₁ < 1) {μ φ : S → ℂ → ℂ} {x : ℕ → S} {P : ℕ → Set S} (hP : LiZhongQC.IsChartPartition S x P)
    (hW : ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖φ (x i) z‖ = 1)
    (hφd : ∀ y : S, DifferentiableOn ℂ (φ y) (chartAt ℂ y).target)
    (hμm : ∀ y : S, AEStronglyMeasurable (μ y) (volume.restrict (chartAt ℂ y).target))
    (hμb : ∀ y : S, ∀ᵐ z ∂(volume.restrict (chartAt ℂ y).target), ‖μ y z‖ ≤ 1) :
    |(∑' i, ∫ z in chartAt ℂ (x i) '' P i, φ (x i) z * ((k : ℂ) * μ (x i) z)).re| ≤ k ∧
      |(∑' i, ∫ z in chartAt ℂ (x i) '' P i, φ (x i) z *
        ((k : ℂ) * μ (x i) z / (1 - (‖(k : ℂ) * μ (x i) z‖ : ℂ) ^ 2))).re| ≤ k / (1 - k ^ 2) ∧
      k - (∑' i, ∫ z in chartAt ℂ (x i) '' P i, φ (x i) z * ((k : ℂ) * μ (x i) z)).re ≤
        k / (1 - k ^ 2) - (∑' i, ∫ z in chartAt ℂ (x i) '' P i, φ (x i) z *
          ((k : ℂ) * μ (x i) z / (1 - (‖(k : ℂ) * μ (x i) z‖ : ℂ) ^ 2))).re ∧
      k / (1 - k ^ 2) - (∑' i, ∫ z in chartAt ℂ (x i) '' P i, φ (x i) z *
          ((k : ℂ) * μ (x i) z / (1 - (‖(k : ℂ) * μ (x i) z‖ : ℂ) ^ 2))).re ≤
        2 / (1 - k₁) ^ 2 * (k - (∑' i, ∫ z in chartAt ℂ (x i) '' P i, φ (x i) z * ((k : ℂ) * μ (x i) z)).re) := by
  have hk1 : k < 1 := lt_of_le_of_lt hkk hk₁
  have ha : 0 < 1 - k ^ 2 := by nlinarith
  have hsub : ∀ i, chartAt ℂ (x i) '' P i ⊆ (chartAt ℂ (x i)).target := fun i =>
    (image_mono (hP.1 i).1).trans (chartAt ℂ (x i)).image_source_eq_target.le
  have hfin : ∀ i, ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖φ (x i) z‖ ≠ ⊤ := fun i => by
    have h := ENNReal.le_tsum (f := fun j => ∫⁻ z in chartAt ℂ (x j) '' P j, ENNReal.ofReal ‖φ (x j) z‖) i
    rw [hW] at h
    exact ne_top_of_le_ne_top ENNReal.one_ne_top h
  have hpc := fun i => gl4_piece hk hkk hk₁ (hP.1 i).2 ((hφd (x i)).continuousOn.mono (hsub i)) (hfin i)
    ((hμm (x i)).mono_measure (Measure.restrict_mono (hsub i) le_rfl))
    (ae_restrict_of_ae_restrict_of_subset (hsub i) (hμb (x i)))
  -- the weights `W i = ∬_{Ω_i} |φ|` sum to `1`
  set W : ℕ → ℝ := fun i => ∫ z in chartAt ℂ (x i) '' P i, ‖φ (x i) z‖ with hWdef
  have hWe : ∀ i, W i = (∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖φ (x i) z‖).toReal := fun i =>
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => norm_nonneg _)
      ((((hφd (x i)).continuousOn.mono (hsub i)).aestronglyMeasurable (hP.1 i).2).norm)
  have hWs : Summable W := by
    rw [show W = fun i => (∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖φ (x i) z‖).toReal from funext hWe]
    exact ENNReal.summable_toReal (by rw [hW]; exact ENNReal.one_ne_top)
  have hW1 : ∑' i, W i = 1 := by
    simp only [hWe]
    rw [← ENNReal.tsum_toReal_eq hfin, hW, ENNReal.toReal_one]
  have hW0 : ∀ i, 0 ≤ W i := fun i => integral_nonneg fun z => norm_nonneg _
  set A : ℕ → ℂ := fun i => ∫ z in chartAt ℂ (x i) '' P i, φ (x i) z * ((k : ℂ) * μ (x i) z) with hAdef
  set B : ℕ → ℂ := fun i => ∫ z in chartAt ℂ (x i) '' P i, φ (x i) z *
    ((k : ℂ) * μ (x i) z / (1 - (‖(k : ℂ) * μ (x i) z‖ : ℂ) ^ 2)) with hBdef
  have hAn : Summable fun i => ‖A i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => (hpc i).1) (hWs.mul_left k)
  have hBn : Summable fun i => ‖B i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => (hpc i).2.1) (hWs.mul_left (k / (1 - k ^ 2)))
  have hAs : Summable A := hAn.of_norm
  have hBs : Summable B := hBn.of_norm
  have hAre : Summable fun i => (A i).re := Complex.reCLM.summable hAs
  have hBre : Summable fun i => (B i).re := Complex.reCLM.summable hBs
  rw [Complex.re_tsum hAs, Complex.re_tsum hBs]
  have hkW : k = ∑' i, k * W i := by rw [tsum_mul_left, hW1, mul_one]
  have hkW' : k / (1 - k ^ 2) = ∑' i, k / (1 - k ^ 2) * W i := by rw [tsum_mul_left, hW1, mul_one]
  have eA : k - ∑' i, (A i).re = ∑' i, (k * W i - (A i).re) := by
    rw [(hWs.mul_left k).tsum_sub hAre, ← hkW]
  have eB : k / (1 - k ^ 2) - ∑' i, (B i).re = ∑' i, (k / (1 - k ^ 2) * W i - (B i).re) := by
    rw [(hWs.mul_left _).tsum_sub hBre, ← hkW']
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc |∑' i, (A i).re| ≤ ∑' i, |(A i).re| := by
          rw [← Real.norm_eq_abs]
          refine (norm_tsum_le_tsum_norm ?_).trans_eq ?_
          · exact hAre.abs
          · simp only [Real.norm_eq_abs]
      _ ≤ ∑' i, k * W i := Summable.tsum_le_tsum (fun i => (Complex.abs_re_le_norm _).trans (hpc i).1)
          hAre.abs (hWs.mul_left k)
      _ = k := hkW.symm
  · calc |∑' i, (B i).re| ≤ ∑' i, |(B i).re| := by
          rw [← Real.norm_eq_abs]
          refine (norm_tsum_le_tsum_norm ?_).trans_eq ?_
          · exact hBre.abs
          · simp only [Real.norm_eq_abs]
      _ ≤ ∑' i, k / (1 - k ^ 2) * W i := Summable.tsum_le_tsum
          (fun i => (Complex.abs_re_le_norm _).trans (hpc i).2.1) hBre.abs (hWs.mul_left _)
      _ = k / (1 - k ^ 2) := hkW'.symm
  · rw [eA, eB]
    exact Summable.tsum_le_tsum (fun i => (hpc i).2.2.1) ((hWs.mul_left k).sub hAre)
      ((hWs.mul_left _).sub hBre)
  · rw [eA, eB, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun i => (hpc i).2.2.2) ((hWs.mul_left _).sub hBre)
      (((hWs.mul_left k).sub hAre).mul_left _)

/-- Helper for Theorem 10. The pairing estimates of `gl4_phi_sum` for `φ ∈ A(R)` with `‖φ‖ = 1` and `μ ∈ L∞(R)`
with `‖μ‖∞ = 1`, on the chart partition chosen by `pairingRS` (its weights sum to `‖φ‖` by partition independence,
`s26v_surfaceIntegral_eq_tsum`). -/
theorem gl4_phi {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] {k k₁ : ℝ}
    (hk : 0 ≤ k) (hkk : k ≤ k₁) (hk₁ : k₁ < 1) {μ : S → ℂ → ℂ} (hμ : μ ∈ beltramiSpace S)
    (hμ1 : beltramiNormRS μ = 1) {φ : S → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet S) (hφ1 : quadDiffNorm φ = 1) :
    |(pairingRS φ fun x z => (k : ℂ) * μ x z).re| ≤ k ∧
      |(pairingRS φ fun x z => (k : ℂ) * μ x z / (1 - (‖(k : ℂ) * μ x z‖ : ℂ) ^ 2)).re| ≤ k / (1 - k ^ 2) ∧
      k - (pairingRS φ fun x z => (k : ℂ) * μ x z).re ≤
        k / (1 - k ^ 2) - (pairingRS φ fun x z => (k : ℂ) * μ x z / (1 - (‖(k : ℂ) * μ x z‖ : ℂ) ^ 2)).re ∧
      k / (1 - k ^ 2) - (pairingRS φ fun x z => (k : ℂ) * μ x z / (1 - (‖(k : ℂ) * μ x z‖ : ℂ) ^ 2)).re ≤
        2 / (1 - k₁) ^ 2 * (k - (pairingRS φ fun x z => (k : ℂ) * μ x z).re) := by
  have hex : ∃ (x : ℕ → S) (P : ℕ → Set S), LiZhongQC.IsChartPartition S x P := by
    by_contra h
    have htop : quadDiffNorm φ = ⊤ := by
      change LiZhongQC.surfaceIntegral φ (fun _ _ => 1) = ⊤
      unfold LiZhongQC.surfaceIntegral
      exact iInf_eq_top.2 fun x => iInf_eq_top.2 fun P => iInf_eq_top.2 fun hP => absurd ⟨x, P, hP⟩ h
    rw [hφ1] at htop
    exact ENNReal.one_ne_top htop
  have hpair : ∀ ν : S → ℂ → ℂ, pairingRS φ ν = ∑' i, ∫ z in chartAt ℂ (hex.choose i) '' hex.choose_spec.choose i,
      φ (hex.choose i) z * ν (hex.choose i) z := fun ν => by
    unfold pairingRS
    exact dite_eq_left hex
  have hP := hex.choose_spec.choose_spec
  have hq : LiZhongQC.IsHolQuadDiff φ := hφ.1
  have hq' : LiZhongQC.IsDiffFamily 2 0 φ ∧ ∀ y : S, DifferentiableOn ℂ (φ y) (chartAt ℂ y).target := hq
  have hW : ∑' i, ∫⁻ z in chartAt ℂ (hex.choose i) '' hex.choose_spec.choose i,
      ENNReal.ofReal ‖φ (hex.choose i) z‖ = 1 := by
    have h := LiZhongQC.s26v_surfaceIntegral_eq_tsum hq (fun _ => 1) hP
    simp only [one_mul] at h
    rw [← h]
    exact hφ1
  obtain ⟨k₀, -, hbc⟩ := hμ
  have hμb : ∀ y : S, ∀ᵐ z ∂(volume.restrict (chartAt ℂ y).target), ‖μ y z‖ ≤ 1 := by
    intro y
    have h1 : eLpNorm (μ y) ⊤ (volume.restrict (chartAt ℂ y).target) ≤ beltramiNormRS μ :=
      le_iSup (fun y => eLpNorm (μ y) ⊤ (volume.restrict (chartAt ℂ y).target)) y
    rw [hμ1, eLpNorm_exponent_top (hbc y).1] at h1
    filter_upwards [ae_le_eLpNormEssSup (f := μ y) (μ := volume.restrict (chartAt ℂ y).target)] with z hz
    have h2 := hz.trans h1
    rwa [← ofReal_norm, ENNReal.ofReal_le_one] at h2
  rw [hpair, hpair]
  exact gl4_phi_sum hk hkk hk₁ hP hW hq'.2 (fun y => (hbc y).1) hμb

/-- Helper for Theorem 10. `A(R)` with the unit sphere is symmetric under `φ ↦ −φ`, and the pairing is odd. -/
theorem gl4_neg {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {φ : S → ℂ → ℂ}
    (hφ : φ ∈ integrableHolQDSet S) (hφ1 : quadDiffNorm φ = 1) :
    (-φ ∈ integrableHolQDSet S ∧ quadDiffNorm (-φ) = 1) ∧ ∀ ν : S → ℂ → ℂ, pairingRS (-φ) ν = -pairingRS φ ν := by
  have e : quadDiffNorm (-φ) = quadDiffNorm φ := by
    change LiZhongQC.surfaceIntegral (-φ) (fun _ _ => 1) = LiZhongQC.surfaceIntegral φ (fun _ _ => 1)
    unfold LiZhongQC.surfaceIntegral
    simp only [Pi.neg_apply, norm_neg]
  refine ⟨⟨⟨(LiZhongQC.holQuadDiffSubmodule S).neg_mem hφ.1, by rw [e]; exact hφ.2⟩, e.trans hφ1⟩, fun ν => ?_⟩
  unfold pairingRS
  split_ifs with h
  · simp only [Pi.neg_apply, neg_mul, integral_neg, tsum_neg]
  · simp

/-- Helper for Theorem 10. A real supremum `⨆ φ, ⨆ (_ : P φ), g φ` of a bounded family is an upper bound of the
values on `P` (the junk value of the inner supremum on `¬ P φ` is `0`). -/
theorem gl4_le_sup {X : Type*} {P : X → Prop} {g : X → ℝ} {B : ℝ} (hB : ∀ y, P y → g y ≤ B) {y : X} (hy : P y) :
    g y ≤ ⨆ y, ⨆ (_ : P y), g y := by
  have hbdd : BddAbove (range fun y => ⨆ (_ : P y), g y) := by
    refine ⟨max B 0, ?_⟩
    rintro _ ⟨y', rfl⟩
    show ⨆ (_ : P y'), g y' ≤ max B 0
    by_cases hy' : P y'
    · rw [ciSup_pos hy']
      exact le_max_of_le_left (hB y' hy')
    · have : IsEmpty (P y') := ⟨hy'⟩
      rw [Real.iSup_of_isEmpty]
      exact le_max_right _ _
  refine le_of_eq_of_le ?_ (le_ciSup hbdd y)
  rw [ciSup_pos hy]

/-- Helper for Theorem 10. An upper bound `c ≥ 0` of the values on `P` bounds `⨆ φ, ⨆ (_ : P φ), g φ`. -/
theorem gl4_sup_le {X : Type*} {P : X → Prop} {g : X → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ y, P y → g y ≤ c) :
    ⨆ y, ⨆ (_ : P y), g y ≤ c :=
  Real.iSup_le (fun y => Real.iSup_le (fun hy => h y hy) hc) hc

/-- **Theorem 10** (Teichmüller contraction, §4.10, l. 4429), the `i`-value and the `j`-value:
`C₃ i(kμ) ≤ j(kμ) ≤ C₄ i(kμ)` for `0 < k ≤ k₁`, with `C₃ = (1 − k₁)²/2` and `C₄ = 1`. -/
theorem thm4_10_b (hA : ∃ φ ∈ integrableHolQDSet R, quadDiffNorm φ = 1) {k₁ : ℝ} (hk₁ : 0 < k₁) (hk₁' : k₁ < 1)
    {μ : R → ℂ → ℂ} (hμ : μ ∈ beltramiSpace R) (hμ1 : beltramiNormRS μ = 1) {k : ℝ} (hk : 0 < k) (hkk : k ≤ k₁) :
    (1 - k₁) ^ 2 / 2 * iValue k μ ≤ jValue k μ ∧ jValue k μ ≤ 1 * iValue k μ := by
  -- the standing assumptions `T2Space R`, `ConnectedSpace R` of the file are not needed here
  have _hT2 : T2Space R := inferInstance
  have _hconn : ConnectedSpace R := inferInstance
  -- `0 < k₁` follows from `0 < k ≤ k₁`
  have _hk₁ := hk₁
  obtain ⟨φ₀, hφ₀, hφ₀1⟩ := hA
  have hk1 : k < 1 := lt_of_le_of_lt hkk hk₁'
  have ha : 0 < 1 - k ^ 2 := by nlinarith
  have hk₁0 : 0 < 1 - k₁ := by linarith
  have hC : 0 < 2 / (1 - k₁) ^ 2 := by positivity
  -- the per-`φ` estimates (Lemma 5 integrated) and the symmetry `φ ↦ −φ`
  have hφ := fun (φ : R → ℂ → ℂ) (h : φ ∈ integrableHolQDSet R ∧ quadDiffNorm φ = 1) =>
    gl4_phi hk.le hkk hk₁' hμ hμ1 h.1 h.2
  have hneg := fun (φ : R → ℂ → ℂ) (h : φ ∈ integrableHolQDSet R ∧ quadDiffNorm φ = 1) => gl4_neg h.1 h.2
  set SJ : ℝ := bigJ (fun x z => (k : ℂ) * μ x z) with hSJ
  set SI : ℝ := bigI (fun x z => (k : ℂ) * μ x z) with hSI
  have hJle : ∀ φ, φ ∈ integrableHolQDSet R ∧ quadDiffNorm φ = 1 →
      |(pairingRS φ fun x z => (k : ℂ) * μ x z).re| ≤ SJ := fun φ h =>
    gl4_le_sup (g := fun φ => |(pairingRS φ fun x z => (k : ℂ) * μ x z).re|) (fun ψ hψ => (hφ ψ hψ).1) h
  have hIle : ∀ φ, φ ∈ integrableHolQDSet R ∧ quadDiffNorm φ = 1 →
      |(pairingRS φ fun x z => (k : ℂ) * μ x z / (1 - (‖(k : ℂ) * μ x z‖ : ℂ) ^ 2)).re| ≤ SI := fun φ h =>
    gl4_le_sup (g := fun φ => |(pairingRS φ fun x z => (k : ℂ) * μ x z / (1 - (‖(k : ℂ) * μ x z‖ : ℂ) ^ 2)).re|)
      (fun ψ hψ => (hφ ψ hψ).2.1) h
  have hSJ0 : 0 ≤ SJ := (abs_nonneg _).trans (hJle φ₀ ⟨hφ₀, hφ₀1⟩)
  have hd : 0 ≤ k / (1 - k ^ 2) - k := by
    rw [sub_nonneg, le_div_iff₀ ha]
    nlinarith [sq_nonneg k, hk.le]
  -- `j ≤ i`
  have hI : SI ≤ SJ + (k / (1 - k ^ 2) - k) := by
    refine gl4_sup_le (by linarith) fun φ h => abs_le.2 ⟨?_, ?_⟩
    · have h2 := (hφ _ (hneg φ h).1).2.2.1
      have h3 := hJle _ (hneg φ h).1
      rw [(hneg φ h).2, (hneg φ h).2, neg_re, neg_re] at h2
      rw [(hneg φ h).2, neg_re, abs_neg] at h3
      linarith [le_abs_self (pairingRS φ fun x z => (k : ℂ) * μ x z).re,
        neg_abs_le (pairingRS φ fun x z => (k : ℂ) * μ x z).re]
    · have h2 := (hφ φ h).2.2.1
      linarith [le_abs_self (pairingRS φ fun x z => (k : ℂ) * μ x z).re, hJle φ h]
  -- `i ≤ (2/(1 − k₁)²) j`
  have hJ : SJ ≤ k - (k / (1 - k ^ 2) - SI) / (2 / (1 - k₁) ^ 2) := by
    have key : ∀ φ, φ ∈ integrableHolQDSet R ∧ quadDiffNorm φ = 1 →
        (pairingRS φ fun x z => (k : ℂ) * μ x z).re ≤ k - (k / (1 - k ^ 2) - SI) / (2 / (1 - k₁) ^ 2) := by
      intro φ h
      have h2 := (hφ φ h).2.2.2
      have h3 := (le_abs_self _).trans (hIle φ h)
      rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hC]
      nlinarith
    have hc : 0 ≤ k - (k / (1 - k ^ 2) - SI) / (2 / (1 - k₁) ^ 2) := by
      have h1 := key φ₀ ⟨hφ₀, hφ₀1⟩
      have h2 := key _ (hneg φ₀ ⟨hφ₀, hφ₀1⟩).1
      rw [(hneg φ₀ ⟨hφ₀, hφ₀1⟩).2, neg_re] at h2
      linarith
    refine gl4_sup_le hc fun φ h => abs_le.2 ⟨?_, key φ h⟩
    have h2 := key _ (hneg φ h).1
    rw [(hneg φ h).2, neg_re] at h2
    linarith
  show (1 - k₁) ^ 2 / 2 * (k / (1 - k ^ 2) - SI) ≤ k - SJ ∧ k - SJ ≤ 1 * (k / (1 - k ^ 2) - SI)
  refine ⟨?_, by linarith⟩
  have e : (k / (1 - k ^ 2) - SI) / (2 / (1 - k₁) ^ 2) = (1 - k₁) ^ 2 / 2 * (k / (1 - k ^ 2) - SI) := by
    field_simp
  linarith

/-- **Lemma 5** (§4.10, l. 4471). Let `0 ≤ k ≤ k₁ < 1` and `|z| < 1`, `z = x + iy`. Then
`k − kx ≤ k/(1 − k²) − kx/(1 − |kz|²) ≤ (2/(1 − k₁)²)(k − kx)`. -/
theorem lemma4_5 {k k₁ : ℝ} (hk : 0 ≤ k) (hkk : k ≤ k₁) (hk₁ : k₁ < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    k - k * z.re ≤ k / (1 - k ^ 2) - k * z.re / (1 - ‖(k : ℂ) * z‖ ^ 2) ∧
      k / (1 - k ^ 2) - k * z.re / (1 - ‖(k : ℂ) * z‖ ^ 2) ≤ 2 / (1 - k₁) ^ 2 * (k - k * z.re) := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hk, mul_pow]
  exact gl4_lemma4_5_real hk hkk hk₁ (Complex.re_le_norm z) (neg_le_of_abs_le (Complex.abs_re_le_norm z)) hz.le

/-- **Corollary 2** (Hamilton–Krushkal, Reich–Strebel, §4.10, l. 4479). A Beltrami coefficient `μ` of a
quasiconformal map is an extremal representative of its Teichmüller class if and only if
`‖μ‖∞ = sup_{‖φ‖=1} |Re ∬_R φμ|`. -/
theorem cor4_10_2 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (hA : ∃ φ ∈ integrableHolQDSet R, quadDiffNorm φ = 1) (μ : beltramiBall R) :
    IsExtremalRS p μ ↔ (beltramiNormRS μ.1).toReal = bigJ μ.1 := by
  sorry

end GardinerLakic2000
