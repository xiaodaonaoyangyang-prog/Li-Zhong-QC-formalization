import References.Pommerenke1992.Ch06.S04_PlessnersTheoremAndTwisting

/-!
# Pommerenke 1992, Ch. 6 §6.5 Sectorial Accessibility

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §6.5; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 6185–6438.

* Definition (open triangle of vertex `w`; `Sect(f)`, the set of `ζ` where `f(ζ)` is sectorially accessible,
  l. 6187; used in Ch. 6–8) — `IsOpenTriangleAt`, `sect`
* Proposition 6.22 (cited at l. 6264, 6340, 6469, 6488 and P2 l. 2871) — `prop6_22`
* Proposition 6.23 ((6.5.1); cited at l. 6238) — `prop6_23`
* Formulas (6.5.2), (6.5.3) (`Sect(f)` is an `F_σ`-set, `f(Sect(f))` is an `F_σ`-set of sigma-finite linear
  measure; (6.5.3) cited "(3)" at l. 6291 and "(6.5.3)" at l. 6480; the §6.1 form at l. 5420) — `eq6_5_3`
* Theorem 6.24 (the McMillan sector theorem, McM69b; (6.5.5); cited at l. 6279, 6419, 6488 and P2 l. 2871) —
  `thm6_24`
* Theorem 6.25 (the Makarov compression theorem, Mak84, Mak85; (6.5.8) cited at l. 6578; cited at l. 6528, 6560,
  6566) — `thm6_25`
* Corollary 6.26 (Mak84; (6.5.12); cited at l. 6321 and P2 l. 1604, 1998) — `cor6_26`
* Definition (the dyadic points, (6.5.14); cited at P2 l. 2150, 2351, 2602) — `dyadicPoint`
* Definition (the dyadic arcs `I_{nν} = I(z_{nν})`, (6.5.15)) — exists: `Pommerenke1992.arcI` (the arc I(z) of
  (5.2.4) at the dyadic point; for the point of index n, ν it is the arc of the e^{it} with 2π(ν - 1)/2ⁿ ≤ t ≤ 2πν/2ⁿ,
  an immediate computation)
* Unlabelled (§6.5, l. 6340–6384: the construction (6.5.16)–(6.5.19) of the proof of Theorem 6.25, cited "(6.5.17)",
  "(6.5.18)", "(6.5.19)" in the proof of Theorem 6.30, l. 6534–6554; leader ruling on U+ proof steps) —
  `thm6_25_dyadic`
* Theorem 6.27 ((6.5.22); announced at l. 2877; cited at l. 6508) — `thm6_27_a`, `thm6_27_b`

Not items (DESIGN §3): (6.5.4), the isosceles triangles and Fig. 6.5 (the proof of Proposition 6.23); (6.5.6), (6.5.7)
(the proof of Theorem 6.24); (6.5.9)–(6.5.11) (consequences of Theorems 6.24, 6.25 and (6.5.3), not cited by number;
the OCR splits the tags) and the remark l. 6299 (`f(A₁)` is large when `∂G` is not sigma-finite); the results quoted
from Pir72 and BiJo90, (6.5.13), and "`f(A₀)` lies on no rectifiable curve" (l. 6309–6321, quoted, not cited); the
properties of dyadic arcs and dyadic points at l. 6335 (nesting, bounded non-euclidean distance, `ω(z_{nν}, I_{nν}) >
1/2`; used in the proof of Theorem 6.25); (6.5.20), (6.5.21) (the recall of Theorem 3.18, `thm3_18_a`); (6.5.23) and
Fig. 6.8 (the proof of Theorem 6.27); Exercises 6.5.1–6.5.6.

**Standing assumption** (l. 6187): `f` maps `𝔻` conformally onto `G ⊆ ℂ`, that is, `f` is analytic and injective in
`𝔻` and `G = f(𝔻)`.

**Conventions.** As in §6.4. `Sect` is defined for maps with values in `Ĉ` (`f : ℂ → Ĉ`), so that §6.6 can apply it to
the exterior map `f*` (leader ruling Q6.9); a map `f : ℂ → ℂ` enters as `z ↦ (f z : Ĉ)`. The book's `f(E)` for
`E ⊆ 𝕋` is the set of radial limits (6.2.20) (`radialImage`; for conformal maps radial and angular limits agree,
Corollary 2.17), measured through its finite part. Theorems 6.25 and 6.26 use the angular limits of the book as radial
limits in the same way. The function `β` of Theorem 6.27 is that of Theorem 3.18 (`thm3_18_a`): `β(t)` is the radial
limit of `t + Im L(re^{it})` for a holomorphic logarithm `L` of `f(z)/z`; it is determined up to an additive constant
`2πk`, which does not affect the statements.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsConformalOnto)
open LehtoVirtanen1973 (IsRectifiableJordanCurve)
open References (finitePart)

/-- **Definition** (§6.5, l. 6187; used in `Sect(f)`, Corollary 6.26, (6.6.2), Theorem 6.27 and l. 7235). `T` is an
open triangle of vertex `w`: the interior of a non-degenerate triangle with the vertex `w`. -/
def IsOpenTriangleAt (T : Set ℂ) (w : ℂ) : Prop :=
  ∃ a b : ℂ, AffineIndependent ℝ ![w, a, b] ∧ T = interior (convexHull ℝ {w, a, b})

/-- **Definition** (§6.5, l. 6187; index "103, 127, 144, 151, 169"). `Sect(f)` is the set of all `ζ ∈ 𝕋` such that
`f(ζ)` is sectorially accessible, that is, the angular limit `f(ζ) ≠ ∞` exists and `f` maps a domain `V ⊆ 𝔻` with
`ζ ∈ V̄` onto an open triangle of vertex `f(ζ)`.
Modelling: `f` has values in `Ĉ` (see the file header); a domain is an open connected set; only the values of `f` on
`𝔻` enter. -/
def sect (f : ℂ → ExtPlane) : Set ℂ :=
  {ζ ∈ sphere (0 : ℂ) 1 | ∃ w : ℂ, HasAngularLimit f ζ w ∧ ∃ V : Set ℂ, V ⊆ unitDisc ∧ IsOpen V ∧ IsConnected V ∧
    ζ ∈ closure V ∧ ∃ T : Set ℂ, IsOpenTriangleAt T w ∧ f '' V = toExt T}

/-- **Proposition 6.22** (§6.5; cited at l. 6264, 6340, 6469, 6488 and P2 l. 2871). All points where `f` is conformal
belong to `Sect(f)`, and `f` is conformal at almost all points of `Sect(f)`. -/
theorem prop6_22 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) :
    (∀ ζ ∈ sphere (0 : ℂ) 1, IsConformalAtBoundary f ζ → ζ ∈ sect (fun z => (f z : ExtPlane))) ∧
      circleMeasure {ζ ∈ sect (fun z => (f z : ExtPlane)) | ¬ IsConformalAtBoundary f ζ} = 0 := by
  sorry

/-- **Proposition 6.23** (§6.5; Sak64, McM69b; cited at l. 6238). There exist countably many domains `G_n ⊆ G` and
closed sets `A_n ⊆ 𝕋 ∩ ∂f⁻¹(G_n)` such that `∂G_n` is a rectifiable Jordan curve, `f(A_n)` is closed and (6.5.1)
`Sect(f) = ⋃_n A_n`.
Modelling: the families are indexed by `ℕ` (repetitions allowed); the `G_n` are bounded (`Bornology.IsBounded`), so
that `G_n` is the inner domain of the Jordan curve `∂G_n`, the boundary in `ℂ` (without it the exterior domain of a
curve would qualify, which the proof of Theorem 6.24 cannot use); `f(A_n)` is the set of radial limits on `A_n`,
which are finite. -/
theorem prop6_23 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) :
    ∃ Gs As : ℕ → Set ℂ, (∀ n, IsOpen (Gs n) ∧ IsConnected (Gs n) ∧ Bornology.IsBounded (Gs n) ∧
      Gs n ⊆ f '' unitDisc ∧ IsRectifiableJordanCurve (frontier (Gs n)) ∧ IsClosed (As n) ∧
      As n ⊆ sphere (0 : ℂ) 1 ∩ frontier (unitDisc ∩ f ⁻¹' Gs n) ∧
      IsClosed (finitePart (radialImage (fun z => (f z : ExtPlane)) (As n)))) ∧
      sect (fun z => (f z : ExtPlane)) = ⋃ n, As n := by
  sorry

/-- **Formulas (6.5.2), (6.5.3)** (§6.5, l. 6204–6214; (6.5.3) cited "(3)" at l. 6291 and "(6.5.3)" at l. 6480; the
§6.1 form "the image of `Sect(f)` has sigma-finite linear measure", l. 5420). It follows from Proposition 6.23 that
`Sect(f)` is an `F_σ`-set, furthermore that (6.5.2) `f(Sect(f)) = ⋃_n f(A_n)`, where `f(A_n)`, the set of angular
limits, is a closed set of finite linear measure; hence (6.5.3) `f(Sect(f))` is an `F_σ`-set of sigma-finite linear
measure.
Modelling: `f(Sect(f))` is the set of the (finite) radial limits on `Sect(f)`. The conjuncts are: `Sect(f)` is an
`F_σ`-set; (6.5.2), as a decomposition of `f(Sect(f))` into countably many closed sets of finite linear measure (the
sets `f(A_n)` of Proposition 6.23 are such a decomposition); and (6.5.3), with sigma-finite linear measure as
`SigmaFinite ((μH[1] : Measure ℂ).restrict …)` (§6.2), the form cited at l. 5420, 6291 and 6480. -/
theorem eq6_5_3 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) :
    IsFSigma (sect (fun z => (f z : ExtPlane))) ∧
      (∃ Es : ℕ → Set ℂ,
        finitePart (radialImage (fun z => (f z : ExtPlane)) (sect (fun z => (f z : ExtPlane)))) = ⋃ n, Es n ∧
          ∀ n, IsClosed (Es n) ∧ μH[1] (Es n) < ⊤) ∧
      IsFSigma (finitePart (radialImage (fun z => (f z : ExtPlane)) (sect (fun z => (f z : ExtPlane))))) ∧
      SigmaFinite ((μH[1] : Measure ℂ).restrict
        (finitePart (radialImage (fun z => (f z : ExtPlane)) (sect (fun z => (f z : ExtPlane)))))) := by
  sorry

/-- **Theorem 6.24** (§6.5; the McMillan sector theorem, McM69b; cited at l. 6279, 6419, 6488 and P2 l. 2871). Let `f`
map `𝔻` conformally into `ℂ`. If `E ⊆ Sect(f)`, then (6.5.5) `Λ(E) = 0 ⇔ Λ(f(E)) = 0`.
Modelling: `E` is any subset of `Sect(f)` (outer measures). -/
theorem thm6_24 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) {E : Set ℂ}
    (hE : E ⊆ sect (fun z => (f z : ExtPlane))) :
    circleMeasure E = 0 ↔ μH[1] (finitePart (radialImage (fun z => (f z : ExtPlane)) E)) = 0 := by
  sorry

/-- **Theorem 6.25** (§6.5; the Makarov compression theorem, Mak84, Mak85; (6.5.8) cited at l. 6578). If `f` maps `𝔻`
conformally onto `G ⊆ ℂ`, then (6.5.8) `𝕋 = Sect(f) ∪ A₀ ∪ A₁`, where `Λ(f(A₀)) = 0` and `Λ(A₁) = 0`.
Modelling: the three pieces are pairwise disjoint (the "partition" of §6.1, l. 5422; leader ruling, Q6.8(f)), a free
strengthening: replacing `A₀` by `A₀ ∖ Sect(f)` and `A₁` by `A₁ ∖ (Sect(f) ∪ A₀)` keeps both null conditions. -/
theorem thm6_25 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) :
    ∃ A₀ A₁ : Set ℂ, sphere (0 : ℂ) 1 = sect (fun z => (f z : ExtPlane)) ∪ A₀ ∪ A₁ ∧
      Disjoint (sect (fun z => (f z : ExtPlane))) A₀ ∧ Disjoint (sect (fun z => (f z : ExtPlane))) A₁ ∧
      Disjoint A₀ A₁ ∧ μH[1] (finitePart (radialImage (fun z => (f z : ExtPlane)) A₀)) = 0 ∧
      circleMeasure A₁ = 0 := by
  sorry

/-- **Corollary 6.26** (§6.5; Mak84; cited at l. 6321 and P2 l. 1604, 1998). If the points on `∂G` that are vertex of
an open triangle in `G` form a set of zero linear measure, then there is a set `A₀ ⊆ 𝕋` such that (6.5.12)
`Λ(A₀) = 2π`, `Λ(f(A₀)) = 0`.
Modelling: `∂G` is the boundary of `G = f(𝔻)` in `ℂ` (the vertices are finite points). -/
theorem cor6_26 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc)
    (hS : μH[1] {w ∈ frontier (f '' unitDisc) | ∃ T : Set ℂ, IsOpenTriangleAt T w ∧ T ⊆ f '' unitDisc} = 0) :
    ∃ A₀ ⊆ sphere (0 : ℂ) 1, circleMeasure A₀ = ENNReal.ofReal (2 * π) ∧
      μH[1] (finitePart (radialImage (fun z => (f z : ExtPlane)) A₀)) = 0 := by
  sorry

/-- **Definition (6.5.14)** (§6.5; cited at P2 l. 2150, 2351, 2602). The dyadic points
`z_{nν} = (1 - 1/2ⁿ) exp(iπ(2ν - 1)/2ⁿ)` (`ν = 1, …, 2ⁿ`; `n = 1, 2, …`).
Modelling: the formula for all natural `n`, `ν`; the statements restrict the indices to `n ≥ 1`, `1 ≤ ν ≤ 2ⁿ`. -/
def dyadicPoint (n ν : ℕ) : ℂ :=
  ((1 - 1 / 2 ^ n : ℝ) : ℂ) * exp ((π * (2 * (ν : ℝ) - 1) / 2 ^ n : ℝ) * I)

/-- **Unlabelled claim** (§6.5, l. 6340–6384, the construction (6.5.16)–(6.5.19) of the proof of Theorem 6.25; cited
"(6.5.17)", "(6.5.18)", "(6.5.19)" as results in the proof of Theorem 6.30, l. 6534–6554). There are absolute
constants `K₁, K₂` with the following property. Let `f` map `𝔻` conformally onto `G` and let (6.5.16)
`A = {ζ ∈ 𝕋 : liminf_{r → 1} |f'(rζ)| = 0}`. For `k = 1, 2, …` there are dyadic points `ζ_{kj}` with
`|f'(ζ_{kj})| < K₁ 2^{-k}` whose dyadic arcs `J_{kj} = I(ζ_{kj})` cover `A` and are disjoint except for their end
points, and Borel sets `B_{kj} ⊆ J_{kj}` with `f(B_{kj}) ⊆ D_{kj}`, where (6.5.17)
`D_{kj} = D(f(ζ_{kj}), K₂(1 - |ζ_{kj}|)|f'(ζ_{kj})|)`, and (6.5.18) `Λ(B_{kj}) > Λ(J_{kj})/2 > 1 - |ζ_{kj}|`. The sets
(6.5.19) `Z_m = A ∩ ⋃_{k ≥ m} ⋃_j B_{kj}`, `A₀ = ⋂_{m ≥ 1} Z_m` satisfy (6.5.8): `𝕋 = Sect(f) ∪ A₀ ∪ A₁` with
`Λ(f(A₀)) = 0` and `Λ(A₁) = 0`.
Modelling: the dyadic points of level `k` are indexed by a set `P k` of index pairs `(n, ν)`, `n ≥ 1`,
`1 ≤ ν ≤ 2ⁿ` (`ζ_{kj} = dyadicPoint n ν`); `B k p` is the Borel set `B_{kj}`; "disjoint except for their end points"
is a finite intersection; `f(B_{kj}) ⊆ D_{kj}` is `B_{kj} ⊆ f⁻¹(D_{kj})` (6.2.16), as used at l. 6534 (the limits
exist at the points of `B_{kj}`, Lemma 6.19); the lower limit is taken in `[0, ∞]`. `K₁, K₂` are absolute
(`∃ K₁ K₂, ∀ f`). -/
theorem thm6_25_dyadic :
    ∃ K₁ K₂ : ℝ, ∀ f : ℂ → ℂ, DifferentiableOn ℂ f unitDisc → InjOn f unitDisc →
      ∃ (P : ℕ → Set (ℕ × ℕ)) (B : ℕ → ℕ × ℕ → Set ℂ) (A A₀ A₁ : Set ℂ),
        A = {ζ ∈ sphere (0 : ℂ) 1 | liminf (fun r : ℝ => ‖deriv f (r * ζ)‖ₑ) (𝓝[<] 1) = 0} ∧
        (∀ k, 1 ≤ k → ∀ p ∈ P k, 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.2 ≤ 2 ^ p.1 ∧
          ‖deriv f (dyadicPoint p.1 p.2)‖ < K₁ / 2 ^ k ∧
          MeasurableSet (B k p) ∧ B k p ⊆ arcI (dyadicPoint p.1 p.2) ∧
          B k p ⊆ radialPreimage (fun z => (f z : ExtPlane)) (toExt (ball (f (dyadicPoint p.1 p.2))
            (K₂ * (1 - ‖dyadicPoint p.1 p.2‖) * ‖deriv f (dyadicPoint p.1 p.2)‖))) ∧
          circleMeasure (arcI (dyadicPoint p.1 p.2)) / 2 < circleMeasure (B k p) ∧
          ENNReal.ofReal (1 - ‖dyadicPoint p.1 p.2‖) < circleMeasure (arcI (dyadicPoint p.1 p.2)) / 2) ∧
        (∀ k, 1 ≤ k → ∀ p ∈ P k, ∀ q ∈ P k, p ≠ q →
          (arcI (dyadicPoint p.1 p.2) ∩ arcI (dyadicPoint q.1 q.2)).Finite) ∧
        (∀ k, 1 ≤ k → A ⊆ ⋃ p ∈ P k, arcI (dyadicPoint p.1 p.2)) ∧
        A₀ = ⋂ m ∈ Ici 1, (A ∩ ⋃ k ∈ Ici m, ⋃ p ∈ P k, B k p) ∧
        sphere (0 : ℂ) 1 = sect (fun z => (f z : ExtPlane)) ∪ A₀ ∪ A₁ ∧
        μH[1] (finitePart (radialImage (fun z => (f z : ExtPlane)) A₀)) = 0 ∧ circleMeasure A₁ = 0 := by
  sorry

/-- **Theorem 6.27** (§6.5; announced at l. 2877; cited at l. 6508), first part, (6.5.22). Let `f` be starlike in
`𝔻`. Then `f` is conformal and satisfies `Re[e^{it} f'(e^{it})/f(e^{it})] = β'(t) ≠ ∞` for almost all `e^{it}`.
Modelling: `β` is the increasing function (6.5.21) of Theorem 3.18 (see the file header); at almost every `t`, `f` has
a nonzero finite angular derivative `a = f'(e^{it})` and a finite angular limit `f(e^{it}) ≠ 0`, and `β` has the
finite derivative `Re[e^{it} a/f(e^{it})]` at `t`. -/
theorem thm6_27_a {f : ℂ → ℂ} (hf : IsStarlikeFunction f) {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L unitDisc)
    (hLf : ∀ z ∈ unitDisc, z ≠ 0 → z * exp (L z) = f z) {β : ℝ → ℝ}
    (hβ : ∀ t : ℝ, Tendsto (fun r : ℝ => t + (L (r * exp (t * I))).im) (𝓝[<] 1) (𝓝 (β t))) :
    ∀ᵐ t : ℝ, ∃ a fζ : ℂ, a ≠ 0 ∧ HasAngularDerivative f (exp (t * I)) a ∧
      HasAngularLimit (fun z => (f z : ExtPlane)) (exp (t * I)) fζ ∧ fζ ≠ 0 ∧
      HasDerivAt β (exp (t * I) * a / fζ).re t := by
  sorry

/-- **Theorem 6.27** (§6.5), second part. `β` is absolutely continuous if and only if, for almost all `ϑ`, there
exists `w ∈ ∂G` with `arg w = ϑ` such that `G` contains some triangle of vertex `w` symmetric to `[0, w]`.
Modelling: `G = f(𝔻)`, `∂G` its boundary in `ℂ`; `β` as in `thm6_27_a`, absolutely continuous on `[0, 2π]`
(`β(t + 2π) = β(t) + 2π`); `arg w = ϑ` is `w = |w| e^{iϑ}` with `w ≠ 0`; "a triangle of vertex `w` symmetric to
`[0, w]`" is an open triangle of vertex `w` that is invariant under the reflection `z ↦ w z̄/w̄` in the line through
`0` and `w` (an isosceles triangle with apex `w` and axis on that line; in a starlike `G` it points towards `0`). -/
theorem thm6_27_b {f : ℂ → ℂ} (hf : IsStarlikeFunction f) {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L unitDisc)
    (hLf : ∀ z ∈ unitDisc, z ≠ 0 → z * exp (L z) = f z) {β : ℝ → ℝ}
    (hβ : ∀ t : ℝ, Tendsto (fun r : ℝ => t + (L (r * exp (t * I))).im) (𝓝[<] 1) (𝓝 (β t))) :
    AbsolutelyContinuousOnInterval β 0 (2 * π) ↔
      ∀ᵐ ϑ : ℝ, ∃ w ∈ frontier (f '' unitDisc), w ≠ 0 ∧ w = (‖w‖ : ℂ) * exp (ϑ * I) ∧
        ∃ T : Set ℂ, IsOpenTriangleAt T w ∧ T ⊆ f '' unitDisc ∧ (fun z => w * conj z / conj w) '' T = T := by
  sorry

end Pommerenke1992
