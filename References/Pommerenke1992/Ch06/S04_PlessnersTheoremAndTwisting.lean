import References.Pommerenke1992.Ch06.S03_RectifiableCurves
import LiZhongQC.Ch05.S20_SchwarzDomains

/-!
# Pommerenke 1992, Ch. 6 §6.4 Plessner's Theorem and Twisting

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §6.4; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 5972–6184.

* Theorem 6.13 (Plessner's theorem, Ple27; cited at l. 6037, 6043) with the definition of a Plessner point (l. 5982)
  — `IsPlessnerPoint`, `thm6_13`
* Fatou's theorem (named, l. 5984; cited by name at l. 5394, 6020 and P2 l. 2413) — `fatou_theorem`
* Corollary 6.14 (the Privalov uniqueness theorem, Pri19, Pri56; cited by name at P2 l. 305) — `cor6_14`
* Corollary 6.15 (cited at l. 6151) — `cor6_15`
* Corollary 6.16 ((6.4.6); cited at l. 6340) — `cor6_16`
* Definition (twisting at `ζ`, (6.4.9); cited "(9)" at l. 6080, 6159 and P2 l. 2437, 2871) — `IsTwistingAt`
* Proposition 6.17 (cited at l. 6151) — `prop6_17`
* Theorem 6.18 (the McMillan twist theorem, McM69b; cited at l. 6155, 6159, 6194, 6409, 6419 and P2 l. 2871) —
  `thm6_18`
* Lemma 6.19 (cited at l. 6131, 6348) — `lemma6_19`
* Corollary 6.20 (McM69b) — `cor6_20`
* Corollary 6.21 — `cor6_21`

Not items (DESIGN §3): the partition of `𝕋` restating Theorem 6.13 and the triangles of CoLo66 in place of Stolz
angles (l. 5982, quoted, not cited); the "Riesz uniqueness theorem" (CoLo66, named inside the proofs of Theorem 6.13
and Theorem 10.14, with no statement; its content is a special case of Corollary 6.14); the Lusin–Privalov
construction, (6.4.1)–(6.4.5) and Fig. 6.1 (the proof of Theorem 6.13); (6.4.7), (6.4.8) (Fatou's iteration example)
and the first-category example of CoLo66 (l. 6053–6067, examples); (6.4.10)–(6.4.15) and Fig. 6.3 (the proof of
Theorem 6.18); "conformal always implies isogonal" (the recall of (4.3.6), `eq4_3_6`) and "there is a conformal map
onto a quasidisk that is twisting almost everywhere" (l. 6161, a remark with Proposition 4.12, not cited); Exercises
6.4.1–6.4.6.

**Conventions.** As in §6.2–§6.3. "`f` maps `𝔻` conformally into `ℂ`" is `DifferentiableOn ℂ f 𝔻 ∧ InjOn f 𝔻` (Ch. 4).
A meromorphic function `g` in `𝔻` is `MeromorphicOn g 𝔻` with values in `Ĉ` through `LiZhongQC.meroToExt` (poles have
the value `∞`), as in Ch. 4 (leader ruling Q6.10); "`g ≢ 0`" is germ-based, `meroToExt g z ≠ 0` for some `z ∈ 𝔻`. A
Stolz angle at `ζ` is `stolzAngleP ζ α ρ` with `0 < α < π/2`, `0 < ρ < 2 cos α` (Ch. 1); angular limits, angular
derivatives, "conformal at `ζ`" and "isogonal at `ζ`" are those of Ch. 1 and §4.3. `arg[f(z) - f(ζ)]` is a
continuous branch `θ` on `𝔻` with `f(z) - f(ζ) = |f(z) - f(ζ)| e^{iθ(z)}` (it exists because `f(ζ) ∉ f(𝔻)` and `𝔻` is
simply connected; two branches differ by a constant, so the unboundedness in (6.4.9) does not depend on the branch).
The harmonic measure `ω(z, I)` is `harmonicMeasure` (§4.4), `d_f(z)` is `distToBoundary` (§1.3).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsConformalOnto meroToExt)
open References (finitePart)

/-- **Definition** (§6.4, l. 5982; used by Theorem 6.13 and Exercise 6.4.2). `ζ ∈ 𝕋` is a Plessner point of the
meromorphic function `g`: (ii) of Theorem 6.13 holds, `g(Δ)` is dense in `ℂ` for every Stolz angle `Δ` at `ζ`.
Modelling: `g(Δ) ⊆ Ĉ` through `meroToExt`; "dense in `ℂ`" is the density of its finite part (equivalently, `g(Δ)` is
dense in `Ĉ`, the form of §6.1). -/
def IsPlessnerPoint (g : ℂ → ℂ) (ζ : ℂ) : Prop :=
  ζ ∈ sphere (0 : ℂ) 1 ∧ ∀ α ρ : ℝ, 0 < α → α < π / 2 → 0 < ρ → ρ < 2 * Real.cos α →
    Dense (finitePart (meroToExt g '' stolzAngleP ζ α ρ))

/-- **Theorem 6.13** (§6.4; Plessner's theorem, Ple27; cited at l. 6037, 6043). If `g` is meromorphic in `𝔻`, then,
for almost all `ζ ∈ 𝕋`, either (i) `g` has a finite angular limit at `ζ`, or (ii) `g(Δ)` is dense in `ℂ` for every
Stolz angle `Δ` at `ζ` (`ζ` is a Plessner point). -/
theorem thm6_13 {g : ℂ → ℂ} (hg : MeromorphicOn g unitDisc) :
    ∀ᵐ t : ℝ, (∃ w : ℂ, HasAngularLimit (meroToExt g) (exp (t * I)) w) ∨ IsPlessnerPoint g (exp (t * I)) := by
  sorry

/-- **Fatou's theorem** (§6.4, named, l. 5984; cited by name at l. 5394, 6020 and P2 l. 2413). If `g` is bounded and
analytic in `𝔻`, then `g` has an angular limit at almost all points of `𝕋`.
Modelling: the angular limit is finite (`g` is bounded). -/
theorem fatou_theorem {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) (hb : ∃ M : ℝ, ∀ z ∈ unitDisc, ‖g z‖ ≤ M) :
    ∀ᵐ t : ℝ, ∃ w : ℂ, HasAngularLimit (fun z => (g z : ExtPlane)) (exp (t * I)) w := by
  sorry

/-- **Corollary 6.14** (§6.4; the Privalov uniqueness theorem, Pri19, Pri56; cited by name at P2 l. 305). Let
`g(z) ≢ 0` be meromorphic in `𝔻`. Then `g` has the angular limit `0` almost nowhere on `𝕋`.
Modelling: `g ≢ 0` is germ-based (leader ruling Q6.10): with a literal `∃ z, g z ≠ 0` the statement would be false for
a function that vanishes except at one point (its germs are all zero). -/
theorem cor6_14 {g : ℂ → ℂ} (hg : MeromorphicOn g unitDisc)
    (hg0 : ∃ z ∈ unitDisc, meroToExt g z ≠ ((0 : ℂ) : ExtPlane)) :
    ∀ᵐ t : ℝ, ¬ HasAngularLimit (meroToExt g) (exp (t * I)) ((0 : ℂ) : ExtPlane) := by
  sorry

/-- **Corollary 6.15** (§6.4; cited at l. 6151). If `g ∈ 𝓑`, then, for almost all `ζ ∈ 𝕋`, either `g` has a finite
angular limit, or the radial cluster set `C_{[0,ζ)}(g, ζ)` is `Ĉ`. -/
theorem cor6_15 {g : ℂ → ℂ} (hg : IsBloch g) :
    ∀ᵐ t : ℝ, (∃ w : ℂ, HasAngularLimit (fun z => (g z : ExtPlane)) (exp (t * I)) w) ∨
      clusterSetAlong (fun z => (g z : ExtPlane)) (radius (exp (t * I))) (exp (t * I)) = univ := by
  sorry

/-- **Corollary 6.16** (§6.4; cited at l. 6340). If `f` maps `𝔻` conformally into `ℂ`, then, for almost all
`ζ ∈ 𝕋`, either `f` has a finite nonzero angular derivative `f'(ζ)`, or (6.4.6)
`liminf_{r → 1} |f'(rζ)| = 0`, `limsup_{r → 1} |f'(rζ)| = +∞`.
Modelling: "finite nonzero angular derivative" is `IsConformalAtBoundary` (§4.3); the lower and upper limits are taken
in `[0, ∞]` as `r → 1-`. -/
theorem cor6_16 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) :
    ∀ᵐ t : ℝ, IsConformalAtBoundary f (exp (t * I)) ∨
      (liminf (fun r : ℝ => ‖deriv f (r * exp (t * I))‖ₑ) (𝓝[<] 1) = 0 ∧
        limsup (fun r : ℝ => ‖deriv f (r * exp (t * I))‖ₑ) (𝓝[<] 1) = ⊤) := by
  sorry

/-- **Definition (6.4.9)** (§6.4; cited "(9)" at l. 6080, 6159 and P2 l. 2437, 2871). Let `f` map `𝔻` conformally
onto `G ⊆ ℂ`. `f` is twisting at `ζ ∈ 𝕋`: the angular limit `f(ζ) ≠ ∞` exists and
`liminf arg[f(z) - f(ζ)] = -∞`, `limsup arg[f(z) - f(ζ)] = +∞` as `z → ζ`, `z ∈ Γ`, for every curve `Γ ⊆ 𝔻` ending at
`ζ`.
Modelling: `arg[f(z) - f(ζ)]` is a continuous branch `θ` on `𝔻` (see the file header); the lower and upper limits
along `Γ` are "`θ` is unbounded below and above on `Γ` near `ζ`"; curves ending at `ζ` are `IsCurveEndingAt`. -/
def IsTwistingAt (f : ℂ → ℂ) (ζ : ℂ) : Prop :=
  ∃ w : ℂ, HasAngularLimit (fun z => (f z : ExtPlane)) ζ w ∧ ∃ θ : ℂ → ℝ, ContinuousOn θ unitDisc ∧
    (∀ z ∈ unitDisc, f z - w = (‖f z - w‖ : ℂ) * exp (θ z * I)) ∧
    ∀ Γ : Set ℂ, IsCurveEndingAt Γ ζ →
      (∀ M : ℝ, ∃ᶠ z in 𝓝[Γ] ζ, θ z < M) ∧ ∀ M : ℝ, ∃ᶠ z in 𝓝[Γ] ζ, M < θ z

/-- **Proposition 6.17** (§6.4; cited at l. 6151). Let `f` map `𝔻` conformally into `ℂ` and let `f(ζ) ≠ ∞` exist at
`ζ ∈ 𝕋`. Then `f` is twisting at `ζ` if and only if (6.4.9) holds with `Γ` replaced by a Stolz angle `Δ`.
Modelling: `f(ζ) = w` is the angular limit and `θ` a continuous branch of `arg[f(z) - w]` on `𝔻`; the equivalence
holds for every Stolz angle `Δ` at `ζ` (the proof shows that a non-twisting `f` has `arg` bounded below or above in
every Stolz angle, and the converse uses `[0, ζ) ⊆ Δ`). -/
theorem prop6_17 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {ζ w : ℂ}
    (hw : HasAngularLimit (fun z => (f z : ExtPlane)) ζ w) {θ : ℂ → ℝ} (hθc : ContinuousOn θ unitDisc)
    (hθ : ∀ z ∈ unitDisc, f z - w = (‖f z - w‖ : ℂ) * exp (θ z * I)) {α ρ : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 2 * Real.cos α) :
    IsTwistingAt f ζ ↔ (∀ M : ℝ, ∃ᶠ z in 𝓝[stolzAngleP ζ α ρ] ζ, θ z < M) ∧
      ∀ M : ℝ, ∃ᶠ z in 𝓝[stolzAngleP ζ α ρ] ζ, M < θ z := by
  sorry

/-- **Theorem 6.18** (§6.4; the McMillan twist theorem, McM69b; cited at l. 6155, 6159, 6194, 6409, 6419 and P2
l. 2871). Every conformal map of `𝔻` into `ℂ` is either conformal or twisting at almost all points of `𝕋`. -/
theorem thm6_18 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) :
    ∀ᵐ t : ℝ, IsConformalAtBoundary f (exp (t * I)) ∨ IsTwistingAt f (exp (t * I)) := by
  sorry

/-- **Lemma 6.19** (§6.4; the stronger version of Corollary 4.18; cited at l. 6131, 6348). Let `f` map `𝔻`
conformally into `ℂ` and let `0 < δ < 1`. If `z ∈ 𝔻` and `I` is an arc of `𝕋` with `ω(z, I) ≥ α > 0`, then there
exists a Borel set `B ⊆ I` with `ω(z, B) > (1 - δ)ω(z, I)` such that `|f(ζ) - f(z)| ≤ Λ(f(S)) < K(δ, α) d_f(z)` for
`ζ ∈ B`, where `S` is the non-euclidean segment from `z` to `ζ` and where `K(δ, α)` depends only on `δ` and `α`.
Modelling:
- [misprint] The crop prints `d_f(ζ)`; it is read `d_f(z)` (leader ruling): `d_f(ζ)` is not defined (or `0`) for
  `ζ ∈ 𝕋`, and the three uses (l. 6134 `K₁ d_f(r_n)`, (6.5.17), and Corollary 9.20 (10), P2 l. 1462) all have the
  interior point.
- `K` depends only on `δ` and `α` (`∀ δ α, ∃ K, ∀ f z I`); the arcs are `arcT t₁ t₂`, `t₁ < t₂ ≤ t₁ + 2π`; `f(ζ)` is
  the angular limit, whose existence at the points of `B` is part of the conclusion; `f(S)` is the image of the
  half-open segment `S ∩ 𝔻` and `Λ(f(S))` its linear measure (its length, Proposition 6.2). -/
theorem lemma6_19 {δ α : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hα : 0 < α) :
    ∃ K : ℝ, ∀ f : ℂ → ℂ, DifferentiableOn ℂ f unitDisc → InjOn f unitDisc →
      ∀ z ∈ unitDisc, ∀ t₁ t₂ : ℝ, t₁ < t₂ → t₂ ≤ t₁ + 2 * π → α ≤ harmonicMeasure z (arcT t₁ t₂) →
        ∃ B ⊆ arcT t₁ t₂, MeasurableSet B ∧ (1 - δ) * harmonicMeasure z (arcT t₁ t₂) < harmonicMeasure z B ∧
          ∀ ζ ∈ B, ∃ w : ℂ, HasAngularLimit (fun u => (f u : ExtPlane)) ζ w ∧
            ENNReal.ofReal ‖w - f z‖ ≤ μH[1] (f '' (nonEuclideanSegment z ζ ∩ unitDisc)) ∧
            μH[1] (f '' (nonEuclideanSegment z ζ ∩ unitDisc)) < ENNReal.ofReal (K * distToBoundary f z) := by
  sorry

/-- **Corollary 6.20** (§6.4; McM69b). Let `f` map `𝔻` conformally into `𝔻` and let `A ⊆ 𝕋` be measurable. If
`f(ζ)` exists for `ζ ∈ A` and if `f(A) ⊆ 𝕋`, then `f` is conformal at almost all points of `A`.
Modelling: `f(ζ)` is the angular limit; "`f(ζ)` exists and `f(A) ⊆ 𝕋`" is: at every `ζ ∈ A` the angular limit exists
and lies on `𝕋`. -/
theorem cor6_20 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    (hfD : MapsTo f unitDisc unitDisc) {A : Set ℂ} (hAT : A ⊆ sphere (0 : ℂ) 1) (hA : IsLinearlyMeasurable A)
    (hfA : ∀ ζ ∈ A, ∃ w ∈ sphere (0 : ℂ) 1, HasAngularLimit (fun z => (f z : ExtPlane)) ζ w) :
    circleMeasure {ζ ∈ A | ¬ IsConformalAtBoundary f ζ} = 0 := by
  sorry

/-- **Corollary 6.21** (§6.4). A conformal map of `𝔻` into `ℂ` is conformal at almost all points where it is
isogonal. -/
theorem cor6_21 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) :
    ∀ᵐ t : ℝ, IsIsogonalAt f (exp (t * I)) → IsConformalAtBoundary f (exp (t * I)) := by
  sorry

end Pommerenke1992
