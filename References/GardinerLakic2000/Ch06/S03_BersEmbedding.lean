import References.GardinerLakic2000.Ch06.S02_SchwarzianDistortion
import References.GardinerLakic2000.Ch02.S05_ConstantCurvature

/-!
# Gardiner–Lakic 2000, Ch. 6 §6.3 The Bers embedding

Source `teichmuller.txt`, lines 5653–5754.

* Lemma 3 (i) ⇔ (ii) (`w_μ = w_ν` on `ℝ` iff `w^μ = w^ν` on `ℝ`, l. 5666) — exists: `LiZhongQC.lemma33_1`
* Lemma 3 (ii) ⇔ (iii) (`w^μ = w^ν` on `ℝ` iff on the lower half-plane, l. 5669) — `lemma6_3_b`
* Lemma 4 (`w^μ γ (w^μ)⁻¹` is a Möbius transformation preserving `ℍ^μ`, l. 5683) — `lemma6_4`
* Lemma 5 (`S(w^μ)` is a quadratic differential for `G` on `𝕃`, `|φ y²| ≤ 3/2`, l. 5693) — exists:
  `LiZhongQC.bersFunctionGamma_mem` (y² normalization; the strict bound < 3/2)
* Definition 1 (the Banach space `B(G)` of bounded cusp forms, l. 5703) — `cuspNorm`, `boundedCuspForms`
* Theorem 1 (Bers embedding, one-to-one, l. 5711) — exists: `LiZhongQC.bersMapGamma_injective`
* Theorem 1 (Bers embedding, open image, l. 5711) — exists: `LiZhongQC.thm33_1_bers` (openness in the y² norm, which
  differs from ‖·‖_B by the factor 4 only)
* Theorem 1 (the image contains the ball of radius 2, is contained in the ball of radius 6) — `thm6_1_c`, `thm6_1_d`
* Lemma 6 (Ahlfors–Weill, l. 5717; cited l. 5992, 9219, 10371, 10420, 10646) — exists: `LiZhongQC.lemma33_3` (for a
  Fuchsian group Γ; the group-free first sentence is the case of the trivial group)
* Definition (harmonic Beltrami differential, l. 5753; used l. 5955 and Ch. 14) — `IsHarmonicBeltrami`

Not items (DESIGN §3): `M(G)` and the maps `w_μ`, `w^μ` (l. 5654–5664; Part A §0: `LiZhongQC.BeltramiGamma`,
`LiZhongQC.fMuSym`, `LiZhongQC.normalizedSolution`), the equivalence `μ ∈ M(G) ⇔ μ̂ ∈ M(R)` (l. 5658, Part A's lift),
(6.12), (6.13) and the remark after Lemma 6 (proof steps).

**Conventions (B0.4).** The cusp norm is the book's `‖φ‖_B = sup |φ| ρ⁻²`, `ρ` the Poincaré density of curvature −4
(Part A's `poincareDensityGL`); on a half-plane it is `4 sup y²|φ|`, four times `LiZhongQC.bersNormL`. The constants of
Theorem 1 (2 and 6) are in this norm. The Bers map is `LiZhongQC.bersMapGamma` (the Schwarzian of `w^μ` on `𝕃`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (BeltramiH BeltramiGamma TeichGamma normalizedSolution lowerHalf upperHalf mobiusFn bersMapGamma
  IsFuchsian)

/-- **Definition 1** (§6.3, l. 5703), the norm. `‖φ‖_B = sup_{z ∈ Ω} |φ(z)| ρ(z)⁻²`, `ρ` the Poincaré density of `Ω`
(curvature −4). -/
def cuspNorm (Ω : Set ℂ) (φ : ℂ → ℂ) : ℝ≥0∞ :=
  ⨆ z ∈ Ω, ENNReal.ofReal (‖φ z‖ * poincareDensityGL Ω z ^ (-2 : ℤ))

/-- **Definition 1** (§6.3, l. 5703). The Banach space `B(G)` of bounded cusp forms for a group `G` of Möbius
transformations acting on the domain `Ω`: holomorphic `φ` on `Ω` with `φ(γ(z)) γ′(z)² = φ(z)` for `γ ∈ G`, `z ∈ Ω`,
and `‖φ‖_B < ∞`. Modelling: `G ≤ SL(2, ℝ)` (Part A §0) acting on `Ω = ℍ` or `𝕃`; as a set. -/
def boundedCuspForms (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (Ω : Set ℂ) : Set (ℂ → ℂ) :=
  {φ | DifferentiableOn ℂ φ Ω ∧ (∀ γ ∈ Γ, ∀ z ∈ Ω,
      φ ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = φ z) ∧
    cuspNorm Ω φ < ⊤}

/-- **Lemma 3** (ii) ⇔ (iii) (§6.3, l. 5666–5669, 5681). For `μ, ν ∈ M(ℍ)`, `w^μ = w^ν` on `ℝ` if and only if
`w^μ = w^ν` on the lower half-plane. -/
theorem lemma6_3_b (μ ν : BeltramiH) :
    (∀ x : ℝ, normalizedSolution μ.1 x = normalizedSolution ν.1 x) ↔
      ∀ z ∈ lowerHalf, normalizedSolution μ.1 z = normalizedSolution ν.1 z := by
  have h := LiZhongQC.fMu_lower_model μ ν
  refine ⟨fun hx z hz => h.2 hx hz, fun hz => h.1 ?_⟩
  intro z hz'
  exact hz z hz'

/-- Helper for Lemma 4. For `γ ∈ G` and `z ∈ ℍ`, the Möbius map `g` of `k24_rel_exists` (`w^μ ∘ γ = g ∘ w^μ` on
`ℂ̄`) has no pole at `w^μ(z)`, and `w^μ(γ z) = g(w^μ(z))`. -/
theorem gl6_lemma6_4_rel {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (μ : BeltramiGamma Γ)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} {g : Matrix.SpecialLinearGroup (Fin 2) ℂ}
    (hg : ∀ p : LiZhongQC.ExtPlane, OnePoint.map (normalizedSolution μ.1.1)
      (LiZhongQC.mobiusSL (LiZhongQC.slRealToComplex γ) p) =
        LiZhongQC.mobiusSL g (OnePoint.map (normalizedSolution μ.1.1) p))
    {z : ℂ} (hz : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0) :
    g 1 0 * normalizedSolution μ.1.1 z + g 1 1 ≠ 0 ∧
      normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        mobiusFn (g 0 0) (g 0 1) (g 1 0) (g 1 1) (normalizedSolution μ.1.1 z) := by
  have h := hg (z : LiZhongQC.ExtPlane)
  rw [LiZhongQC.k24_mobiusSL_real, LiZhongQC.mobiusExt_coe hz, OnePoint.map_some, OnePoint.map_some] at h
  change _ = LiZhongQC.mobiusExt (g 0 0) (g 0 1) (g 1 0) (g 1 1) _ at h
  by_cases hw : g 1 0 * normalizedSolution μ.1.1 z + g 1 1 = 0
  · rw [LiZhongQC.mobiusExt_coe_of_eq_zero hw] at h
    exact absurd h (OnePoint.coe_ne_infty _)
  · rw [LiZhongQC.mobiusExt_coe hw] at h
    exact ⟨hw, OnePoint.coe_injective h⟩

/-- **Lemma 4** (§6.3, l. 5683). For `μ ∈ M(G)` and `γ ∈ G`, `γ^μ = w^μ ∘ γ ∘ (w^μ)⁻¹` is a linear fractional
transformation `(az + b)/(cz + d)`, `ad − bc = 1`, `a, b, c, d` complex, which leaves `ℍ^μ = w^μ(ℍ)` invariant.
Modelling: `w^μ ∘ γ = γ^μ ∘ w^μ` off the poles. -/
theorem lemma6_4 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (μ : BeltramiGamma Γ) {γ : _} (hγ : γ ∈ Γ) :
    ∃ a b c d : ℂ, a * d - b * c = 1 ∧
      (∀ z : ℂ, (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 → c * normalizedSolution μ.1.1 z + d ≠ 0 →
        normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
          mobiusFn a b c d (normalizedSolution μ.1.1 z)) ∧
      mobiusFn a b c d '' (normalizedSolution μ.1.1 '' upperHalf) = normalizedSolution μ.1.1 '' upperHalf := by
  obtain ⟨g, hg⟩ := LiZhongQC.k24_rel_exists μ.1 μ.2 hγ
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := g.2
    rwa [Matrix.det_fin_two] at h
  have hγdet : ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ, 0 < δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 := by
    intro δ
    have h := δ.2
    rw [Matrix.det_fin_two] at h
    rw [h]
    exact one_pos
  have hden : ∀ z ∈ upperHalf, (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := fun z hz =>
    LiZhongQC.realMobius_den_ne_zero (hγdet γ) hz
  refine ⟨g 0 0, g 0 1, g 1 0, g 1 1, hdet, fun z hz _ => (gl6_lemma6_4_rel μ hg hz).2, ?_⟩
  ext w
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨_, LiZhongQC.h36p_m_mem γ hz, (gl6_lemma6_4_rel μ hg (hden z hz)).2⟩
  · rintro ⟨z, hz, rfl⟩
    have hz' : LiZhongQC.h36p_m γ⁻¹ z ∈ upperHalf := LiZhongQC.h36p_m_mem γ⁻¹ hz
    have hzz : mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (LiZhongQC.h36p_m γ⁻¹ z) = z := by
      have h := LiZhongQC.h36p_m_inv_m γ⁻¹ hz
      rwa [inv_inv] at h
    refine ⟨normalizedSolution μ.1.1 (LiZhongQC.h36p_m γ⁻¹ z), ⟨_, hz', rfl⟩, ?_⟩
    rw [← (gl6_lemma6_4_rel μ hg (hden _ hz')).2, hzz]

/-- Helper for Theorem 1 and §6.5. The Poincaré density (curvature −4) of the half-plane `{ζ : Im ζ · Im w > 0}`
containing `w` is `1/(2|Im w|)`: `q ↦ Re w + i Im w (1 + q)/(1 − q)` is a competitor with `|g′(0)| = 2|Im w|`, and
the Schwarz lemma for `(g − w)/(g − w̄)` gives `|g′(0)| ≤ 2|Im w|` for every competitor. -/
theorem gl6_density_half {w : ℂ} (hw : w.im ≠ 0) :
    poincareDensityGL {ζ : ℂ | 0 < ζ.im * w.im} w = 1 / (2 * |w.im|) := by
  have hb2 : 0 < w.im ^ 2 := by positivity
  have hbabs : 0 < 2 * |w.im| := by positivity
  have hww : ‖w - conj w‖ = 2 * |w.im| := by
    rw [Complex.sub_conj, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_mul,
      abs_two]
  have hww0 : w - conj w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hww
    linarith
  -- the Cayley-type map `ζ ↦ (ζ − w)/(ζ − w̄)` sends the half-plane into the disc
  have hC : ∀ ζ : ℂ, 0 < ζ.im * w.im → ζ - conj w ≠ 0 ∧ ‖(ζ - w) / (ζ - conj w)‖ < 1 := by
    intro ζ hζ
    have hne : ζ - conj w ≠ 0 := by
      intro h
      have h1 := congrArg Complex.im h
      rw [Complex.sub_im, Complex.conj_im, Complex.zero_im] at h1
      have h3 : ζ.im = -w.im := by linarith
      rw [h3] at hζ
      nlinarith
    refine ⟨hne, ?_⟩
    rw [norm_div, div_lt_one (norm_pos_iff.2 hne)]
    rw [← pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
    nlinarith
  -- the competitor
  have hq1 : ∀ q ∈ LiZhongQC.unitDisc, (1 : ℂ) - q ≠ 0 := by
    intro q hq h
    have h1 : q = 1 := by linear_combination -h
    have h2 := mem_ball_zero_iff.1 hq
    rw [h1, norm_one] at h2
    exact lt_irrefl _ h2
  set g : ℂ → ℂ := fun q => (w.re : ℂ) + (w.im : ℂ) * I * ((1 + q) / (1 - q)) with hgdef
  have hgd : DifferentiableOn ℂ g LiZhongQC.unitDisc := fun q hq =>
    (((differentiableAt_const _).add ((differentiableAt_const _).mul
      (((differentiableAt_const 1).add differentiableAt_id).div ((differentiableAt_const 1).sub differentiableAt_id)
        (hq1 q hq))))).differentiableWithinAt
  have hg0 : g 0 = w := by
    simp only [hgdef, add_zero, sub_zero, div_one, mul_one]
    exact Complex.re_add_im w
  have hu : HasDerivAt (fun q : ℂ => (1 + q) / (1 - q)) 2 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).const_add 1).div ((hasDerivAt_id (0 : ℂ)).const_sub 1) (by norm_num)
    convert h using 1
    · funext q
      simp only [Pi.div_apply, id]
    · norm_num
  have hg' : HasDerivAt g ((w.im : ℂ) * I * 2) 0 := (hu.const_mul _).const_add _
  have hgn : ‖deriv g 0‖ = 2 * |w.im| := by
    rw [hg'.deriv, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Real.norm_eq_abs, mul_comm]
  have hgm : MapsTo g LiZhongQC.unitDisc {ζ : ℂ | 0 < ζ.im * w.im} := by
    intro q hq
    have hN : 0 < Complex.normSq (1 - q) := Complex.normSq_pos.2 (hq1 q hq)
    have hq2 : q.re ^ 2 + q.im ^ 2 < 1 := by
      have h := mem_ball_zero_iff.1 hq
      have h2 : ‖q‖ ^ 2 < 1 := by nlinarith [norm_nonneg q]
      rwa [Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq] at h2
    have hre : ((1 + q) / (1 - q)).re = (1 - q.re ^ 2 - q.im ^ 2) / Complex.normSq (1 - q) := by
      rw [Complex.div_re]
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
      rw [← add_div]
      ring_nf
    have him : (g q).im = w.im * ((1 + q) / (1 - q)).re := by
      simp only [hgdef, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
        Complex.I_re, Complex.I_im]
      ring
    show 0 < (g q).im * w.im
    rw [him, hre]
    have : 0 < (1 - q.re ^ 2 - q.im ^ 2) / Complex.normSq (1 - q) := div_pos (by linarith) hN
    nlinarith
  have hgne : deriv g 0 ≠ 0 := by
    rw [← norm_pos_iff, hgn]
    exact hbabs
  have hmem : 1 / (2 * |w.im|) ∈ {r : ℝ | ∃ g : ℂ → ℂ, DifferentiableOn ℂ g LiZhongQC.unitDisc ∧
      MapsTo g LiZhongQC.unitDisc {ζ : ℂ | 0 < ζ.im * w.im} ∧ g 0 = w ∧ deriv g 0 ≠ 0 ∧ r = 1 / ‖deriv g 0‖} :=
    ⟨g, hgd, hgm, hg0, hgne, by rw [hgn]⟩
  unfold poincareDensityGL
  apply le_antisymm
  · refine csInf_le ⟨0, ?_⟩ hmem
    rintro r ⟨f, -, -, -, -, rfl⟩
    positivity
  · refine le_csInf ⟨_, hmem⟩ ?_
    rintro r ⟨f, hfd, hfm, hf0, hfne, rfl⟩
    -- the Schwarz lemma for `h = (f − w)/(f − w̄)`
    have hfa : ∀ q ∈ ball (0 : ℂ) 1, DifferentiableAt ℂ f q := fun q hq =>
      hfd.differentiableAt (isOpen_ball.mem_nhds hq)
    have hhd : DifferentiableOn ℂ (fun q => (f q - w) / (f q - conj w)) (ball 0 1) := fun q hq =>
      (((hfa q hq).sub_const w).div ((hfa q hq).sub_const (conj w)) (hC _ (hfm hq)).1).differentiableWithinAt
    have hh0 : (fun q => (f q - w) / (f q - conj w)) 0 = 0 := by
      show (f 0 - w) / (f 0 - conj w) = 0
      rw [hf0, sub_self, zero_div]
    have hhm : MapsTo (fun q => (f q - w) / (f q - conj w)) (ball 0 1)
        (closedBall ((fun q => (f q - w) / (f q - conj w)) 0) 1) := by
      intro q hq
      rw [hh0, mem_closedBall_zero_iff]
      exact (hC _ (hfm hq)).2.le
    have hsch := Complex.norm_deriv_le_one_of_mapsTo_ball hhd hhm one_pos
    have hd0 : HasDerivAt (fun q => (f q - w) / (f q - conj w))
        ((deriv f 0 * (f 0 - conj w) - (f 0 - w) * deriv f 0) / (f 0 - conj w) ^ 2) 0 :=
      ((hfa 0 (mem_ball_self one_pos)).hasDerivAt.sub_const w).div
        ((hfa 0 (mem_ball_self one_pos)).hasDerivAt.sub_const (conj w)) (by rw [hf0]; exact hww0)
    rw [hd0.deriv, hf0, sub_self, zero_mul, sub_zero, sq, mul_div_mul_right _ _ hww0, norm_div, hww,
      div_le_one hbabs] at hsch
    exact one_div_le_one_div_of_le (norm_pos_iff.2 hfne) hsch

/-- Helper for Theorem 1. `ρ_𝕃(z) = 1/(2|Im z|)` (`gl6_density_half`). -/
theorem gl6_density_lowerHalf {z : ℂ} (hz : z ∈ lowerHalf) : poincareDensityGL lowerHalf z = 1 / (2 * |z.im|) := by
  have hz' : z.im < 0 := hz
  have e : {ζ : ℂ | 0 < ζ.im * z.im} = lowerHalf := by
    ext ζ
    constructor
    · intro h
      show ζ.im < 0
      by_contra h'
      have : ζ.im * z.im ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (not_lt.1 h') hz'.le
      exact absurd h (not_lt.2 this)
    · intro h
      exact mul_pos_of_neg_of_neg h hz'
  rw [← e]
  exact gl6_density_half hz'.ne

/-- Helper for §6.5. `ρ_ℍ(z) = 1/(2 Im z)` (`gl6_density_half`). -/
theorem gl6_density_upperHalf {z : ℂ} (hz : z ∈ upperHalf) : poincareDensityGL upperHalf z = 1 / (2 * |z.im|) := by
  have hz' : 0 < z.im := hz
  have e : {ζ : ℂ | 0 < ζ.im * z.im} = upperHalf := by
    ext ζ
    constructor
    · intro h
      show 0 < ζ.im
      exact pos_of_mul_pos_left h hz'.le
    · intro h
      exact mul_pos h hz'
  rw [← e]
  exact gl6_density_half hz'.ne'

/-- Helper for Theorem 1 and §6.5. On a half-plane the cusp norm is `4 sup y²|φ|`. -/
theorem gl6_cuspNorm_half (φ : ℂ → ℂ) {Ω : Set ℂ} (hΩ : ∀ z ∈ Ω, poincareDensityGL Ω z = 1 / (2 * |z.im|)) :
    cuspNorm Ω φ = 4 * ⨆ z ∈ Ω, ENNReal.ofReal (‖φ z‖ * z.im ^ 2) := by
  unfold cuspNorm
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun z => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun hz => ?_
  rw [hΩ z hz, zpow_neg, zpow_ofNat, div_pow, one_pow, mul_pow, sq_abs, one_div, inv_inv,
    show ‖φ z‖ * (2 ^ 2 * z.im ^ 2) = 4 * (‖φ z‖ * z.im ^ 2) by ring, ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_ofNat]

/-- Helper for Theorem 1. `‖φ‖_B = 4 · bersNormL φ` on `𝕃`. -/
theorem gl6_cuspNorm_lowerHalf (φ : ℂ → ℂ) : cuspNorm lowerHalf φ = 4 * LiZhongQC.bersNormL φ :=
  gl6_cuspNorm_half φ fun _ hz => gl6_density_lowerHalf hz

/-- **Theorem 1** (the Bers embedding, §6.3, l. 5711), the ball of radius 2. Every `φ ∈ B(G)` (on `𝕃`) with
`‖φ‖_B < 2` is `Φ(μ) = S(w^μ)` for some `μ ∈ M(G)`. -/
theorem thm6_1_c {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {φ : ℂ → ℂ}
    (hφ : φ ∈ boundedCuspForms Γ lowerHalf) (hφ0 : ∀ z ∉ lowerHalf, φ z = 0) (h2 : cuspNorm lowerHalf φ < 2) :
    ∃ p : TeichGamma Γ, bersMapGamma Γ p = φ := by
  obtain ⟨hd, haut, -⟩ := hφ
  have hA : φ ∈ LiZhongQC.automorphicQD Γ := ⟨hd, hφ0, haut⟩
  rw [gl6_cuspNorm_lowerHalf] at h2
  have hlt : LiZhongQC.bersNormL φ < ENNReal.ofReal (1 / 2) := by
    have e : (2 : ℝ≥0∞) = 4 * ENNReal.ofReal (1 / 2) := by
      rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num),
        show (4 : ℝ) * (1 / 2) = 2 by norm_num, ENNReal.ofReal_ofNat]
    rw [e] at h2
    exact lt_of_not_ge fun h => absurd h2 (not_lt.2 (mul_le_mul_of_nonneg_left h zero_le))
  obtain ⟨μ, -, hμ⟩ := (LiZhongQC.lemma33_3 hΓ).2 φ hA hlt
  exact ⟨_, hμ⟩

/-- **Theorem 1** (the Bers embedding, §6.3, l. 5711), the ball of radius 6. The image of `T(G)` lies in the ball of
radius 6 of `B(G)`. -/
theorem thm6_1_d {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (p : TeichGamma Γ) :
    bersMapGamma Γ p ∈ boundedCuspForms Γ lowerHalf ∧ cuspNorm lowerHalf (bersMapGamma Γ p) < 6 := by
  obtain ⟨hA, hlt, -⟩ := LiZhongQC.bersMapGamma_mem hΓ p
  obtain ⟨hd, -, haut⟩ := hA
  have h6 : cuspNorm lowerHalf (bersMapGamma Γ p) < 6 := by
    rw [gl6_cuspNorm_lowerHalf]
    have e : (6 : ℝ≥0∞) = 4 * ENNReal.ofReal (3 / 2) := by
      rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num),
        show (4 : ℝ) * (3 / 2) = 6 by norm_num, ENNReal.ofReal_ofNat]
    rw [e]
    exact ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) hlt
  exact ⟨⟨hd, haut, h6.trans_le le_top⟩, h6⟩

/-- **Definition** (harmonic Beltrami differential, §6.3, l. 5753). A Beltrami differential of the form
`μ = conj(φ) ρ_Ω⁻²` on a domain `Ω`, `φ` holomorphic on `Ω`, `ρ_Ω` the Poincaré density (on `𝕃` this is
`φ(z̄) y²` up to the constant of the density). -/
def IsHarmonicBeltrami (Ω : Set ℂ) (μ : ℂ → ℂ) : Prop :=
  ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Ω ∧ ∀ z ∈ Ω, μ z = conj (φ z) * (poincareDensityGL Ω z ^ (-2 : ℤ) : ℝ)

end GardinerLakic2000
