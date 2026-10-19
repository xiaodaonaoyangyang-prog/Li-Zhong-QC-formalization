import References.GardinerLakic2000.Ch05.S04_ProofOfLemma2
import References.GardinerLakic2000.Ch03.S06_CrossRatioNorm

/-!
# Gardiner–Lakic 2000, Ch. 6 §6.1 Cross-ratios and Schwarzian derivatives

Chapter 6 *The Bers embedding*, §6.1 (and the chapter introduction, l. 5258–5272, no items); source
`teichmuller.txt`, lines 5274–5568.

* Formula (6.3) (Möbius invariance of the cross-ratio, l. 5325; cited l. 5493) — `eq6_3`
* Definition (the Schwarzian `S(f)`, l. 5339, 5353) — exists: `LiZhongQC.schwarzian` (the operator form; the book's
  limit form is (6.5))
* Unlabelled (the cocycle rule for `S`, l. 5349; cited l. 5501, 5623, 5647, 5695, 10347, 10587) — exists:
  `LiZhongQC.eq19_1_chain_rule`
* Formula (6.5) (the limit form equals `f‴/f′ − (3/2)(f″/f′)²`, l. 5442) — `eq6_5`
* Formula (6.6) (`S(f) = −2 f′^{1/2} (f′^{−1/2})″`, l. 5477; cited l. 10379, 10402) — `eq6_6`
* Lemma 1 (preserving cross-ratios ⇔ Möbius ⇔ `S(f) = 0`, l. 5483) — `lemma6_1_a`
* Lemma 1, last sentence (same Schwarzian iff `L ∘ f = g`, l. 5491) — exists: `LiZhongQC.thm19_1_unique` (⇒)
  `Pommerenke1992.eq1_2_16` (⇐, with τ = id); both for locally univalent meromorphic maps, which contain the book's
  locally univalent analytic maps
* Definition (the best approximating Möbius transformation, (6.7), l. 5504–5525) — `bestApproxMobius`
* Formula (6.8) (`η = f′^{−1/2}` solves `2η″ + φη = 0`, `φ = S(f)`, l. 5530; used in Lemma 2) — `eq6_8`
* Lemma 2 (Thurston, l. 5536) — `lemma6_2_a` (`f = η₁/η₂`), `lemma6_2_b` (the formula for `L_{z₀}`)

Not items (DESIGN §3): the cross-ratio of four points (Part A's `crossRatioGL`); the group of anharmonic ratios
(l. 5292), (6.1), (6.2) (l. 5304, 5318), the cocycles `c(f)` and `N(f)` and their cocycle rules (l. 5336–5351), the
distortion bounds and (6.4) (l. 5360–5413): not used later (U−).

**Conventions.** Lemma 2's "Moreover" formula is read at an arbitrary point `z₁` of `U`, with the normalized
solutions (the proof, l. 5551–5567, computes it with `η₂ = f′^{−1/2}`, `η₁ = f′^{−1/2} f`, which agree with them up to
a common sign); at `z₁ = z₀` the printed formula would give `z − z₀` [reading].
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GardinerLakic2000

/-- **Formula (6.5)** (§6.1, l. 5442). For `f` analytic at `z` with `f′(z) ≠ 0`, the book's definition
`S(f)(z) = 6 lim_{w → z} ∂²/∂w∂z log((f(w) − f(z))/(w − z))` agrees with `f‴/f′ − (3/2)(f″/f′)²`. Modelling: the mixed
derivative of the logarithm is written out, `f′(z)f′(w)/(f(z) − f(w))² − 1/(z − w)²` (l. 5395, 5449), which is
branch-free. -/
theorem eq6_5 {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hf' : deriv f z ≠ 0) :
    Tendsto (fun w => 6 * (deriv f z * deriv f w / (f z - f w) ^ 2 - 1 / (z - w) ^ 2)) (𝓝[≠] z)
      (𝓝 (LiZhongQC.schwarzian f z)) := by
  sorry

/-- **Formula (6.6)** (§6.1, l. 5477). `S(f) = (−2) f′^{1/2} (f′^{−1/2})″`, the same branch of the square root in
both factors. Modelling: `η` analytic near `z` with `η² f′ = 1` near `z` (a branch of `f′^{−1/2}`), so that
`f′^{1/2} = 1/η`. -/
theorem eq6_6 {f η : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hη : AnalyticAt ℂ η z)
    (hηf : ∀ᶠ w in 𝓝 z, η w ^ 2 * deriv f w = 1) :
    LiZhongQC.schwarzian f z = -2 * deriv (deriv η) z / η z := by
  have hηne : ∀ᶠ w in 𝓝 z, η w ≠ 0 := hηf.mono fun w hw h0 => by
    rw [h0] at hw
    simp at hw
  -- `f''/f' = −2 η'/η` near `z` (`f' = η⁻²` near every point close to `z`)
  have hratio : (fun w => deriv (deriv f) w / deriv f w) =ᶠ[𝓝 z] fun w => -2 * deriv η w / η w := by
    filter_upwards [hη.eventually_analyticAt, hηf.eventually_nhds, hηne] with w hηw hηfw hne
    have hfd : deriv f =ᶠ[𝓝 w] fun v => (η v ^ 2)⁻¹ := hηfw.mono fun v hv => eq_inv_of_mul_eq_one_right hv
    have hd : HasDerivAt (fun v => (η v ^ 2)⁻¹) _ w :=
      (hηw.differentiableAt.hasDerivAt.pow 2).inv (pow_ne_zero 2 hne)
    have hf1 : deriv f w = (η w ^ 2)⁻¹ := hfd.eq_of_nhds
    rw [hfd.deriv_eq, hd.deriv, hf1]
    norm_num
    field_simp
  have hz0 : η z ≠ 0 := hηne.self_of_nhds
  have hηd : HasDerivAt η (deriv η z) z := hη.differentiableAt.hasDerivAt
  have hη'd : HasDerivAt (deriv η) (deriv (deriv η) z) z := hη.deriv.differentiableAt.hasDerivAt
  have hR : HasDerivAt (fun w => -2 * deriv η w / η w) _ z := (hη'd.const_mul (-2)).div hηd hz0
  have hr0 : deriv (deriv f) z / deriv f z = -2 * deriv η z / η z := hratio.eq_of_nhds
  rw [LiZhongQC.schwarzian_of_analyticAt hf, LiZhongQC.schwarzianHol, hratio.deriv_eq, hR.deriv, hr0]
  field_simp
  ring

/-- **Formula (6.8)** (§6.1, l. 5527–5530). If `η = f′^{−1/2}`, then `2η″ + φη = 0`, where `φ` is the Schwarzian
derivative of `f`. Modelling: as in (6.6). -/
theorem eq6_8 {f η : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hη : AnalyticAt ℂ η z)
    (hηf : ∀ᶠ w in 𝓝 z, η w ^ 2 * deriv f w = 1) :
    ∀ᶠ w in 𝓝 z, 2 * deriv (deriv η) w + LiZhongQC.schwarzian f w * η w = 0 := by
  filter_upwards [hf.eventually_analyticAt, hη.eventually_analyticAt, hηf.eventually_nhds] with w hfw hηw hηfw
  have hne : η w ≠ 0 := by
    intro h0
    have h1 := hηfw.self_of_nhds
    rw [h0] at h1
    simp at h1
  rw [eq6_6 hfw hηw hηfw, div_mul_cancel₀ _ hne]
  ring

/-- **Formula (6.3)** (§6.1, l. 5322–5325). Cross-ratios are invariant under Möbius transformations
`A(z) = (az + b)/(cz + d)`, `ad − bc ≠ 0`: `cr(z₁, z₂, z₃, z₄) = cr(A(z₁), A(z₂), A(z₃), A(z₄))` for distinct finite
points with finite images. Modelling: the cross-ratio is Part A's `crossRatioGL`. -/
theorem eq6_3 {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) {z₁ z₂ z₃ z₄ : ℂ} (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃)
    (h14 : z₁ ≠ z₄) (h23 : z₂ ≠ z₃) (h24 : z₂ ≠ z₄) (h34 : z₃ ≠ z₄) (h₁ : c * z₁ + d ≠ 0) (h₂ : c * z₂ + d ≠ 0)
    (h₃ : c * z₃ + d ≠ 0) (h₄ : c * z₄ + d ≠ 0) :
    crossRatioGL z₁ z₂ z₃ z₄ = crossRatioGL (LiZhongQC.mobiusFn a b c d z₁) (LiZhongQC.mobiusFn a b c d z₂)
      (LiZhongQC.mobiusFn a b c d z₃) (LiZhongQC.mobiusFn a b c d z₄) := by
  -- `h13`, `h24` (the diagonals) are not needed: the cross-ratio involves only the four sides
  have _h13 := h13
  have _h24 := h24
  -- `A z − A w = (ad − bc)(z − w)/((cz + d)(cw + d))`
  have key : ∀ z w : ℂ, c * z + d ≠ 0 → c * w + d ≠ 0 →
      LiZhongQC.mobiusFn a b c d z - LiZhongQC.mobiusFn a b c d w =
        (a * d - b * c) * (z - w) / ((c * z + d) * (c * w + d)) := by
    intro z w hz hw
    show (a * z + b) / (c * z + d) - (a * w + b) / (c * w + d) = _
    rw [div_sub_div _ _ hz hw]
    congr 1
    ring
  have e1 : z₃ - z₂ ≠ 0 := sub_ne_zero.2 h23.symm
  have e2 : z₁ - z₄ ≠ 0 := sub_ne_zero.2 h14
  have e3 : z₂ - z₁ ≠ 0 := sub_ne_zero.2 h12.symm
  have e4 : z₄ - z₃ ≠ 0 := sub_ne_zero.2 h34.symm
  unfold crossRatioGL
  rw [key z₃ z₂ h₃ h₂, key z₁ z₄ h₁ h₄, key z₂ z₁ h₂ h₁, key z₄ z₃ h₄ h₃]
  -- the factors `ad − bc` and `cz_i + d` cancel; keep them as atoms for `field_simp`
  generalize a * d - b * c = D at hdet ⊢
  generalize c * z₁ + d = p₁ at h₁ ⊢
  generalize c * z₂ + d = p₂ at h₂ ⊢
  generalize c * z₃ + d = p₃ at h₃ ⊢
  generalize c * z₄ + d = p₄ at h₄ ⊢
  field_simp

/-- **Lemma 1** (§6.1, l. 5483). For `f` analytic in a domain `U` (with `f′ ≠ 0`), the following are equivalent:
`f` preserves the cross-ratios of all quadruples in `U`; `f` is identically equal to a Möbius transformation in
`U`; `S(f) = 0` in `U`. Modelling: quadruples of distinct points of `U`. -/
theorem lemma6_1_a {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hf' : ∀ z ∈ U, deriv f z ≠ 0) :
    List.TFAE [∀ z₁ ∈ U, ∀ z₂ ∈ U, ∀ z₃ ∈ U, ∀ z₄ ∈ U, z₁ ≠ z₂ → z₁ ≠ z₃ → z₁ ≠ z₄ → z₂ ≠ z₃ → z₂ ≠ z₄ →
        z₃ ≠ z₄ → crossRatioGL (f z₁) (f z₂) (f z₃) (f z₄) = crossRatioGL z₁ z₂ z₃ z₄,
      ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧ ∀ z ∈ U, c * z + d ≠ 0 ∧ f z = LiZhongQC.mobiusFn a b c d z,
      ∀ z ∈ U, LiZhongQC.schwarzian f z = 0] := by
  sorry

/-- **Definition** ((6.7), §6.1, l. 5504–5525). The best approximating Möbius transformation of `f` at `z₀`:
`L(z) = ((a₁² − a₂a₀)(z − z₀) + a₀a₁)/(−a₂(z − z₀) + a₁)`, where `f(z) = a₀ + a₁(z − z₀) + a₂(z − z₀)² + ⋯`. It has
the same terms of order `0, 1, 2` at `z₀` as `f` (and determinant `a₁³ ≠ 0` when `f′(z₀) ≠ 0`). -/
def bestApproxMobius (f : ℂ → ℂ) (z₀ z : ℂ) : ℂ :=
  ((deriv f z₀ ^ 2 - deriv (deriv f) z₀ / 2 * f z₀) * (z - z₀) + f z₀ * deriv f z₀) /
    (-(deriv (deriv f) z₀ / 2) * (z - z₀) + deriv f z₀)

/-- **Lemma 2** (Thurston, §6.1, l. 5536), first part. Let `f` be univalent in the domain `U` with `S(f) = φ`
holomorphic in `U` and `f(z) = (z − z₀) + O((z − z₀)³)`. Then `f = η₁/η₂`, where `η₁`, `η₂` are the solutions of
(6.8) with `η₁(z₀) = 0`, `η₁′(z₀) = 1`, `η₂(z₀) = 1`, `η₂′(z₀) = 0`. Modelling: the solutions are given on `U`; the
conclusion is `f η₂ = η₁` on `U` (so `η₂ ≠ 0` there, `f` being holomorphic).
[CORRECTION] (AUDIT5_GL L1) The book assumes only `f(z) = (z − z₀) + h.o.t.`, but its proof matches the 2-jets of `f` and
`η₁/η₂`, and `(η₁/η₂)″(z₀) = 0`. Without `f″(z₀) = 0` the statement is false: `f = z/(1 − z)` on `Δ`, `z₀ = 0`,
`η₁ = z`, `η₂ = 1`. The hypothesis `h2` is added. -/
theorem lemma6_2_a {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (h0 : f z₀ = 0) (h1 : deriv f z₀ = 1)
    (h2 : deriv (deriv f) z₀ = 0) {η₁ η₂ : ℂ → ℂ}
    (hη₁ : DifferentiableOn ℂ η₁ U) (hη₂ : DifferentiableOn ℂ η₂ U)
    (hode₁ : ∀ z ∈ U, 2 * deriv (deriv η₁) z + LiZhongQC.schwarzian f z * η₁ z = 0)
    (hode₂ : ∀ z ∈ U, 2 * deriv (deriv η₂) z + LiZhongQC.schwarzian f z * η₂ z = 0)
    (hi₁ : η₁ z₀ = 0 ∧ deriv η₁ z₀ = 1) (hi₂ : η₂ z₀ = 1 ∧ deriv η₂ z₀ = 0) :
    ∀ z ∈ U, f z * η₂ z = η₁ z := by
  sorry

/-- **Lemma 2** (Thurston, §6.1, l. 5536–5540), second part. In the situation of the first part, the best
approximating Möbius transformation of `f` at a point `z₁ ∈ U` is
`L_{z₁}(z) = (η₁(z₁) + η₁′(z₁)(z − z₁))/(η₂(z₁) + η₂′(z₁)(z − z₁))` [reading: see the module docstring].
[CORRECTION] `h2` as in the first part (same counterexample, at `z₁ = 0`, `z = 1/2`). -/
theorem lemma6_2_b {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (h0 : f z₀ = 0) (h1 : deriv f z₀ = 1)
    (h2 : deriv (deriv f) z₀ = 0) {η₁ η₂ : ℂ → ℂ}
    (hη₁ : DifferentiableOn ℂ η₁ U) (hη₂ : DifferentiableOn ℂ η₂ U)
    (hode₁ : ∀ z ∈ U, 2 * deriv (deriv η₁) z + LiZhongQC.schwarzian f z * η₁ z = 0)
    (hode₂ : ∀ z ∈ U, 2 * deriv (deriv η₂) z + LiZhongQC.schwarzian f z * η₂ z = 0)
    (hi₁ : η₁ z₀ = 0 ∧ deriv η₁ z₀ = 1) (hi₂ : η₂ z₀ = 1 ∧ deriv η₂ z₀ = 0) {z₁ : ℂ} (hz₁ : z₁ ∈ U) (z : ℂ)
    (hz : η₂ z₁ + deriv η₂ z₁ * (z - z₁) ≠ 0) :
    bestApproxMobius f z₁ z = (η₁ z₁ + deriv η₁ z₁ * (z - z₁)) / (η₂ z₁ + deriv η₂ z₁ * (z - z₁)) := by
  sorry

end GardinerLakic2000
