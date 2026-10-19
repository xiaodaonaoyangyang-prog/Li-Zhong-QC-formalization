import References.Pommerenke1992.Ch04.S04_HarmonicMeasure

/-!
# Pommerenke 1992, Ch. 4 §4.5 Length Distortion

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §4.5; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 3655–3829.

* Proposition 4.17 — `prop4_17`
* Formula (4.5.2) (Corollary 1.4 written with `d_f`; cited at l. 3889) — exists: `Pommerenke1992.cor1_4` (the same
  two inequalities)
* Corollary 4.18 — `cor4_18`
* Proposition 4.19 — `prop4_19`
* Theorem 4.20 (the Gehring–Hayman theorem) — `thm4_20`
* Gehring–Hayman Theorem (named, the §4.1 form, l. 3006: any curve in `𝔻`, lengths only) — `gehring_hayman_curve`
* Lemma 4.21 — `lemma4_21`

Helper definitions: `arcT` (an arc of `𝕋`), `openArcLength` (the length of the image of an open parameter interval),
`segParam` (the parametrization of the non-euclidean segment), `orthoGeodesic` (the non-euclidean line through a real
point orthogonal to `ℝ`). The arcs `arcT t₁ t₂` are closed; since `ω(z₀, ·)` has no atoms, the statements for open
arcs follow with the constants changed by bounded factors (a closed sub-arc carries half the harmonic measure).

Not items (DESIGN §3): the forward reference to Corollary 9.20 (l. 3707); the remark on quasiconformal maps in higher
dimensions (l. 3810).

**Conventions.** As in §4.2–§4.4. "`f` maps `𝔻` conformally into `ℂ`" is `DifferentiableOn ℂ f 𝔻 ∧ InjOn f 𝔻`. The
constants `K₁, K₂, …` are absolute: `∃ K, ∀ f, …`. An arc `I` of `𝕋` is `{e^{it} : t₁ ≤ t ≤ t₂}` with
`t₁ < t₂ ≤ t₁ + 2π`. Lengths of image curves are `eVariationOn` of the composed parametrization, over the compact
subintervals of the (open or half-open) parameter interval; diameters are `ℝ≥0∞`-valued (`Metric.ediam`). A
non-euclidean segment from `z₀ ∈ 𝔻` to `ζ ∈ 𝕋` is `nonEuclideanSegment z₀ ζ` (§1.2); a segment between two points of
`𝔻̄` is `τ((x₁, x₂))` for a conformal self-map `τ(z) = c(z - a)/(1 - āz)` of `𝔻` and `-1 ≤ x₁ < x₂ ≤ 1` (every
non-euclidean segment is of this form; the proof of Theorem 4.20 uses this normalization).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsConformalOnto)

/-- The arc `{e^{it} : t₁ ≤ t ≤ t₂}` of `𝕋` (helper). -/
def arcT (t₁ t₂ : ℝ) : Set ℂ :=
  (fun t : ℝ => exp (t * I)) '' Icc t₁ t₂

/-- The length `Λ(g((a, b)))` of the image curve of the open parameter interval `(a, b)` (helper): the supremum of the
variations of `g` on the compact subintervals of `(a, b)`. -/
def openArcLength (g : ℝ → ℂ) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ s ∈ Ioo a b, ⨆ t ∈ Ioo s b, eVariationOn g (Icc s t)

/-- The parametrization `t ↦ (t w + z₁)/(1 + z̄₁ t w)`, `w = (z₂ - z₁)/(1 - z̄₁ z₂)`, `0 ≤ t ≤ 1`, of the non-euclidean
segment `nonEuclideanSegment z₁ z₂` from `z₁ ∈ 𝔻` to `z₂ ∈ 𝔻̄` (helper). -/
def segParam (z₁ z₂ : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) * ((z₂ - z₁) / (1 - conj z₁ * z₂)) + z₁) / (1 + conj z₁ * ((t : ℂ) * ((z₂ - z₁) / (1 - conj z₁ * z₂))))

/-- **Proposition 4.17** (§4.5). Let `f` map `𝔻` conformally into `ℂ`. If `z₀ ∈ 𝔻` and if `I` is an arc of `𝕋`, then
there is `ζ ∈ I` such that (4.5.1) `|log f'(z) - log f'(z₀)| < K₁/ω(z₀, I)` for `z ∈ S`, where `S` is the
non-euclidean segment from `z₀` to `ζ`.
Modelling: `log f'` is any holomorphic logarithm `L` of `f'`; `z ∈ S ∩ 𝔻`. -/
theorem prop4_17 :
    ∃ K₁ : ℝ, ∀ (f L : ℂ → ℂ), DifferentiableOn ℂ f unitDisc → InjOn f unitDisc →
      DifferentiableOn ℂ L unitDisc → (∀ z ∈ unitDisc, exp (L z) = deriv f z) →
      ∀ z₀ ∈ unitDisc, ∀ t₁ t₂ : ℝ, t₁ < t₂ → t₂ ≤ t₁ + 2 * π →
        ∃ ζ ∈ arcT t₁ t₂, ∀ z ∈ nonEuclideanSegment z₀ ζ ∩ unitDisc,
          ‖L z - L z₀‖ < K₁ / harmonicMeasure z₀ (arcT t₁ t₂) := by
  sorry

/-- **Corollary 4.18** (§4.5). If `z₀ ∈ 𝔻` and if `I` is an arc of `𝕋`, then (4.5.3)
`Λ(f(S)) < d_f(z₀) exp[K₂/ω(z₀, I)]`, where `S` is the non-euclidean segment from `z₀` to a suitable point of `I`.
Modelling: `f` maps `𝔻` conformally into `ℂ` (as in Proposition 4.17); `Λ(f(S))` is the length of the image of the
half-open segment `[z₀, ζ)`, `t ↦ f(segParam z₀ ζ t)`, `0 ≤ t < 1` (the length (1.1.12) of a half-open curve,
`HalfOpenCurve.length`, written out). -/
theorem cor4_18 :
    ∃ K₂ : ℝ, ∀ f : ℂ → ℂ, DifferentiableOn ℂ f unitDisc → InjOn f unitDisc →
      ∀ z₀ ∈ unitDisc, ∀ t₁ t₂ : ℝ, t₁ < t₂ → t₂ ≤ t₁ + 2 * π →
        ∃ ζ ∈ arcT t₁ t₂,
          (⨆ τ ∈ Ico (0 : ℝ) 1, eVariationOn (fun t => f (segParam z₀ ζ t)) (Icc 0 τ)) <
            ENNReal.ofReal (distToBoundary f z₀ * Real.exp (K₂ / harmonicMeasure z₀ (arcT t₁ t₂))) := by
  sorry

/-- **Proposition 4.19** (§4.5). Let `f` map `𝔻` conformally into `ℂ`. If `z₀ ∈ 𝔻` and `I` is an arc on `𝕋`, then
(4.5.4) `d_f(z₀) ≤ dist(f(z₀), f(I)) ≤ K₃ diam f(I)/ω(z₀, I)^{5/2}`, where `f(I)` is the set of angular limits on `I`
whenever they exist.
Modelling: the diameter is `Metric.ediam` (`∞` for unbounded `f(I)`). The angular limits are values in `Ĉ`; the
distance to `f(I)` is the distance to its finite points, and if `∞ ∈ f(I)` then `diam f(I) = ∞` and the second
inequality says nothing, so it is stated when no angular limit on `I` is `∞`. -/
theorem prop4_19 :
    ∃ K₃ : ℝ, ∀ f : ℂ → ℂ, DifferentiableOn ℂ f unitDisc → InjOn f unitDisc →
      ∀ z₀ ∈ unitDisc, ∀ t₁ t₂ : ℝ, t₁ < t₂ → t₂ ≤ t₁ + 2 * π →
        distToBoundary f z₀ ≤
            infDist (f z₀) {w : ℂ | ∃ ζ ∈ arcT t₁ t₂, HasAngularLimit (fun z => (f z : ExtPlane)) ζ w} ∧
          ((∀ ζ ∈ arcT t₁ t₂, ¬ HasAngularLimit (fun z => (f z : ExtPlane)) ζ extInf) → ENNReal.ofReal
              (infDist (f z₀) {w : ℂ | ∃ ζ ∈ arcT t₁ t₂, HasAngularLimit (fun z => (f z : ExtPlane)) ζ w}) ≤
            ENNReal.ofReal K₃ *
              Metric.ediam {w : ℂ | ∃ ζ ∈ arcT t₁ t₂, HasAngularLimit (fun z => (f z : ExtPlane)) ζ w} /
              ENNReal.ofReal (harmonicMeasure z₀ (arcT t₁ t₂) ^ ((5 : ℝ) / 2))) := by
  sorry

/-- **Theorem 4.20** (§4.5; the Gehring–Hayman theorem). Let `f` map `𝔻` conformally into `ℂ`. If `z₁, z₂ ∈ 𝔻̄`, then
(4.5.5) `Λ(f(S)) ≤ K₅ Λ(f(C))` and (4.5.6) `diam f(S) ≤ K₆ diam f(C)`, where `S` is the non-euclidean segment from
`z₁` to `z₂` and `C` is any Jordan arc in `𝔻` from `z₁` to `z₂`.
Modelling: `S = τ((x₁, x₂))` with `τ(z) = c(z - a)/(1 - āz)`, `-1 ≤ x₁ < x₂ ≤ 1`, `z_j = τ(x_j)` (see the file header);
`C = γ([0, 1])` with `γ` continuous and injective on `[0, 1]`, `γ(0) = z₁`, `γ(1) = z₂`, `γ((0, 1)) ⊆ 𝔻`; the lengths
and diameters are those of the images of the open arcs. The OCR splits the display numbers "(5)" and (6). -/
theorem thm4_20 :
    ∃ K₅ K₆ : ℝ, ∀ f : ℂ → ℂ, DifferentiableOn ℂ f unitDisc → InjOn f unitDisc →
      ∀ (c a : ℂ) (x₁ x₂ : ℝ), ‖c‖ = 1 → ‖a‖ < 1 → -1 ≤ x₁ → x₁ < x₂ → x₂ ≤ 1 →
      ∀ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 1) → InjOn γ (Icc 0 1) →
        γ 0 = c * (x₁ - a) / (1 - conj a * x₁) → γ 1 = c * (x₂ - a) / (1 - conj a * x₂) →
        γ '' Ioo 0 1 ⊆ unitDisc →
        openArcLength (fun x : ℝ => f (c * (x - a) / (1 - conj a * x))) x₁ x₂ ≤
            ENNReal.ofReal K₅ * openArcLength (fun t => f (γ t)) 0 1 ∧
          Metric.ediam (f '' ((fun x : ℝ => c * (x - a) / (1 - conj a * x)) '' Ioo x₁ x₂)) ≤
            ENNReal.ofReal K₆ * Metric.ediam (f '' (γ '' Ioo 0 1)) := by
  sorry

/-- **Gehring–Hayman Theorem** (§4.1, named, l. 3006; the form of the overview, proved in §4.5 as Theorem 4.20). If
`C` is a curve in `𝔻` and if `S` is the non-euclidean segment connecting the endpoints of `C`, then
`Λ(f(S)) ≤ K Λ(f(C))`, `K` an absolute constant.
Modelling: `f` maps `𝔻` conformally into `ℂ` (as in §4.5); `C = γ([0, 1])` for a continuous `γ` with `γ([0, 1]) ⊆ 𝔻`
(the end points are in `𝔻`); `S` is parametrized by `segParam (γ 0) (γ 1)`. The lengths are `eVariationOn` of the
image curves on `[0, 1]`: `Λ(f(C))` is the length of `f ∘ γ` as a parametrized curve, counted with multiplicity, which
is the book's length of a curve (§1.1). `K` is absolute (`∃ K, ∀ f`). -/
theorem gehring_hayman_curve :
    ∃ K : ℝ, ∀ f : ℂ → ℂ, DifferentiableOn ℂ f unitDisc → InjOn f unitDisc →
      ∀ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 1) → γ '' Icc 0 1 ⊆ unitDisc →
        eVariationOn (fun t => f (segParam (γ 0) (γ 1) t)) (Icc 0 1) ≤
          ENNReal.ofReal K * eVariationOn (fun t => f (γ t)) (Icc 0 1) := by
  sorry

/-- The non-euclidean line `T` through `ξ ∈ (-1, 1)` orthogonal to `ℝ` (helper, Lemma 4.21): the image of the diameter
`{iy : -1 < y < 1}` under `u ↦ (u + ξ)/(1 + ξu)`. -/
def orthoGeodesic (ξ : ℝ) : Set ℂ :=
  {z | ∃ y ∈ Ioo (-1 : ℝ) 1, z = (y * I + ξ) / (1 + ξ * (y * I))}

/-- **Lemma 4.21** (§4.5). Let `-1 ≤ ξ₁ < ξ₂ ≤ 1` and assume (4.5.7) `λ(ξ₁, ξ₂) ≥ 1`. For `j = 1, 2`, let `T_j` be the
non-euclidean line through `ξ_j` orthogonal to `ℝ` if `|ξ_j| < 1`, and `T_j = {ξ_j}` otherwise. Then (4.5.8)
`diam f(S) ≤ K₇ diam f(C)`, where `S = (ξ₁, ξ₂)` and `C` is any Jordan arc from `T₁` to `T₂`.
Modelling: `f` maps `𝔻` conformally into `ℂ`; `λ(ξ₁, ξ₂) = ∞` when an end point lies on `𝕋`; `C = γ([0, 1])` with `γ`
continuous and injective on `[0, 1]`, `γ(0) ∈ T₁`, `γ(1) ∈ T₂`, `γ((0, 1)) ⊆ 𝔻`; diameters of the images of the
open arcs. -/
theorem lemma4_21 :
    ∃ K₇ : ℝ, ∀ f : ℂ → ℂ, DifferentiableOn ℂ f unitDisc → InjOn f unitDisc →
      ∀ ξ₁ ξ₂ : ℝ, -1 ≤ ξ₁ → ξ₁ < ξ₂ → ξ₂ ≤ 1 → (ξ₁ = -1 ∨ ξ₂ = 1 ∨ 1 ≤ hypDistD ξ₁ ξ₂) →
      ∀ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 1) → InjOn γ (Icc 0 1) → γ '' Ioo 0 1 ⊆ unitDisc →
        γ 0 ∈ (if |ξ₁| < 1 then orthoGeodesic ξ₁ else {(ξ₁ : ℂ)}) →
        γ 1 ∈ (if |ξ₂| < 1 then orthoGeodesic ξ₂ else {(ξ₂ : ℂ)}) →
        Metric.ediam (f '' ((fun x : ℝ => (x : ℂ)) '' Ioo ξ₁ ξ₂)) ≤
          ENNReal.ofReal K₇ * Metric.ediam (f '' (γ '' Ioo 0 1)) := by
  sorry

end Pommerenke1992
