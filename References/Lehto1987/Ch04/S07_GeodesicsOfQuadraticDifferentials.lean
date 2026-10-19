import References.Lehto1987.Ch04.S06_TrajectoriesOfQuadraticDifferentials

/-!
# Lehto, Chapter IV §7: Geodesics of quadratic differentials

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. IV §7 (`full.md`
P1:5781–5966).

Conventions (see §6). `φ` is a holomorphic quadratic differential `q` on a Riemann surface `S`, `q ≠ 0`. The metric of
`φ` is the project's:
- the length of a path is `LiZhongQC.phiLengthPathInv q γ`, its `φ`-length up to reparametrization;
- the distance is `LiZhongQC.phiDistRS q`, the infimum of the lengths;
- a geodesic arc is a locally shortest path, `LiZhongQC.IsPhiGeodesicRS q γ`.

Open geodesic curves (for maximal geodesics) are maps `γ : ℝ → S` on an open interval, locally injective, whose
points lie metrically between nearby points (`IsGeodesicCurve`). A plane domain `G` is the Riemann surface
`TopologicalSpace.Opens ℂ`, and a quadratic differential `φ` on it is the family `fun _ => G.indicator φ` (its single
chart is the inclusion). Distinct curves are curves with distinct traces.

* Definition (line element `|φ|^{1/2}|dz|`, length, area, §7.1) — exists: `LiZhongQC.phiLengthPath`,
  `LiZhongQC.phiLengthPathInv`, `LiZhongQC.quadDiffNorm` (the area of S is the L¹-norm of φ)
* Formula (7.1) (§7.1) — exists: `LiZhongQC.phiLengthPath` (the integral of the line element)
* Unlabelled (§7.1, P1:5805–5807): on a torus the lifted `φ` is constant and the `φ`-metric is euclidean —
  `para4_7_1`
* Theorem 7.1 (§7.2) — `thm4_7_1`
* Formula (7.2) (§7.2) — omitted: (6.1) in the natural parameter, a step of the proof of Theorem 7.1
* Formula (7.3) (§7.2, the angle condition) — `eq4_7_3`
* Definition (geodesic, §7.3) — exists: `LiZhongQC.IsPhiGeodesicRS` (locally shortest for the φ-distance, which is
  the same as being shortest among nearby arcs for small neighbourhoods)
* Definition (geodesic polygon, simple closed polygon, §7.3) — exists: `LiZhongQC.PhiPolygon` (the simple closed
  polygons, placed in the unit disc, with their angles)
* Argument Principle (§7.3, boundary zeros weighted by `θⱼ/2π`) — omitted: a classical result quoted for, and cited
  only in, the proof of Lemma 7.1
* Lemma 7.1 (§7.3, Teichmüller's Lemma) — `lemma4_7_1`
* Formula (7.4) (§7.3) — `lemma4_7_1` (the identity of Lemma 7.1)
* Formula (7.5) (§7.3) — omitted: a step of the proof of Lemma 7.1
* Formula (7.6) (§7.3) — omitted: immediate from (7.4)
* Formula (7.7) (§7.3) — exists: `LiZhongQC.thm25_2_polygon` (at least three angles below 2π/(nⱼ + 2), for polygons
  in the unit disc)
* Lemma 7.2 (§7.4) — `lemma4_7_2`
* Definition (maximal geodesic, §7.4) — `IsMaximalGeodesic`
* Lemma 7.3 (§7.4) — `lemma4_7_3`
* Theorem 7.2 (§7.4) — `thm4_7_2`
* Unlabelled (§7.4, P1:5919): a horizontal arc is uniquely length minimizing in its homotopy class — `para4_7_4`
* Unlabelled (§7.5, P1:5925–5929): for a compact surface, every point of the universal covering surface has infinite
  distance to the boundary — `para4_7_5`
* Theorem 7.3 (§7.5) — `thm4_7_3`
* Lemma 7.4 (§7.6) — exists: `LiZhongQC.lemma26_1` (lengths in [0, ∞], for horizontal arcs of finite length)
  (that statement now assumes genus > 1; see its 2026-10-12 correction)
* Unlabelled (§7.6, P1:5965): `liminf l(f(α))/l(α) ≥ 1` — omitted: U−

Helper (not a book notion): `IsGeodesicCurve` (an open locally shortest curve).
-/

open Complex Set Filter Topology
open scoped ENNReal ContDiff Manifold

noncomputable section

namespace Lehto1987

universe u

open LiZhongQC (IsHolQuadDiff HasGenus IsDiffFamily IsZeroOfOrder IsNaturalParameterAtZero phiLengthPathInv phiDistRS
  IsPhiGeodesicRS IsHorizontalArcRS PhiPolygon unitDisc)

/-! ## §7.1 Definition of the induced metric -/

/-- **Unlabelled** (Ch. IV §7.1, P1:5805–5807). If `S` is a torus, its universal covering surface is the plane, and
the lift of `φ` to the plane is bounded, hence constant: the `φ`-metric is euclidean.
Modelling: `S` compact of genus 1 with an analytic universal covering `p : ℂ → S`; the lift `q̃` of (3.4) is a
non-zero constant in the (identity) chart of `ℂ`. -/
theorem para4_7_1 {S : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] (hS : HasGenus S 1) {p : ℂ → S} (hp : IsUniversalCoveringSurface p)
    (hpa : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0)
    {q' : ℂ → ℂ → ℂ} (hq' : IsDiffLift 2 0 p q q') : ∃ c : ℂ, c ≠ 0 ∧ ∀ z w : ℂ, q' z w = c := by
  sorry

/-! ## §7.2 Locally shortest curves -/

/-- **Theorem 7.1** (Ch. IV §7.2). Every point of a Riemann surface has a neighbourhood in which any two points can be
joined by a unique shortest curve.
Modelling: shortest for the `φ`-distance of `S`; unique up to reparametrization (the trace) (near miss:
`LiZhongQC.exists_local_shortest_nbhd`, existence only). -/
theorem thm4_7_1 {S : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) (p : S) :
    ∃ V ∈ 𝓝 p, ∀ a ∈ V, ∀ b ∈ V, ∃ γ : Path a b, phiLengthPathInv q γ = phiDistRS q a b ∧
      ∀ γ' : Path a b, phiLengthPathInv q γ' = phiDistRS q a b → range γ' = range γ := by
  sorry

/-- **Formula (7.3)** (Ch. IV §7.2, the angle condition). Near a zero `p` of order `n` of `φ`, with a natural parameter
`ζ` at `p`: if the shortest curve joining two points `p₁`, `p₂` passes through `p` (it is then the union of two radii
of the `ζ`-plane), both angles `θ` between the radii satisfy `θ ≥ 2π/(n + 2)`.
Modelling: `ζ` in the preferred chart at `p`; the smaller angle is `|arg(ζ₁/ζ₂)|`. -/
theorem eq4_7_3 {S : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) {p : S} {n : ℕ}
    (hn : 1 ≤ n) (hp : IsZeroOfOrder q p n) {ζ : ℂ → ℂ} (hζ : IsNaturalParameterAtZero q p n ζ) :
    ∃ V ∈ 𝓝 p, ∀ a ∈ V, ∀ b ∈ V, a ≠ p → b ≠ p →
      (∃ γ : Path a b, phiLengthPathInv q γ = phiDistRS q a b ∧ p ∈ range γ) →
        2 * Real.pi / (n + 2) ≤ |arg (ζ (chartAt ℂ p a) / ζ (chartAt ℂ p b))| := by
  sorry

/-! ## §7.3 Geodesic polygons -/

/-- **Lemma 7.1** (Ch. IV §7.3, Teichmüller's Lemma). Let `φ` be holomorphic in the closure of a plane domain `A`
bounded by a simple closed polygon of the `φ`-metric, whose sides form the angles `θⱼ` at the vertices. If `mᵢ` and
`nⱼ` are the orders of the zeros of `φ` in `A` and at the vertices, then
`Σ (1 − (nⱼ + 2) θⱼ/(2π)) = 2 + Σ mᵢ` (7.4).
Modelling: the polygon is a `LiZhongQC.PhiPolygon` in the unit disc (`A` placed there by a similarity), `φ`
holomorphic in the disc and not identically zero; the orders are those of `φ` (`0` at a vertex where `φ ≠ 0`); the
sum over `A` is over its zeros. -/
theorem lemma4_7_1 {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {n : ℕ}
    [NeZero n] (P : PhiPolygon φ n) :
    ∑ j : Fin n, (1 - (((WithTop.untop₀ (meromorphicOrderAt φ (P.vert j)) : ℤ) : ℝ) + 2) * P.angle j / (2 * Real.pi)) =
      2 + ∑ᶠ z ∈ P.dom, ((WithTop.untop₀ (meromorphicOrderAt φ z) : ℤ) : ℝ) := by
  sorry

/-! ## §7.4 Minimum property of geodesics -/

/-- **Lemma 7.2** (Ch. IV §7.4). Let `S = G` be a simply connected domain of the plane and `z₁`, `z₂` points of `G`.
Then there is at most one geodesic from `z₁` to `z₂`.
Modelling: geodesic arcs that are not constant on any subinterval; "one" up to reparametrization (the trace) (near
miss: `LiZhongQC.thm25_3_unique_geodesic`, the unit disc). -/
theorem lemma4_7_2 {G : TopologicalSpace.Opens ℂ} [SimplyConnectedSpace G] [ConnectedSpace G] {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ G) (hne : ∃ z ∈ (G : Set ℂ), φ z ≠ 0) {z₁ z₂ : G} {γ₁ γ₂ : Path z₁ z₂}
    (h₁ : IsPhiGeodesicRS (fun _ => (G : Set ℂ).indicator φ) γ₁)
    (h₂ : IsPhiGeodesicRS (fun _ => (G : Set ℂ).indicator φ) γ₂)
    (hp₁ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ₁.extend u ≠ γ₁.extend s)
    (hp₂ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ₂.extend u ≠ γ₂.extend s) :
    range γ₁ = range γ₂ := by
  sorry

/-- Helper. `γ` is an (open) geodesic curve on the open interval `J`: continuous, and near every parameter it is
injective and each of its points lies metrically between the two endpoints of the sub-arc (the sub-arc is shortest). -/
def IsGeodesicCurve {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] (q : S → ℂ → ℂ) (γ : ℝ → S)
    (J : Set ℝ) : Prop :=
  IsOpen J ∧ J.OrdConnected ∧ J.Nonempty ∧ ContinuousOn γ J ∧ ∀ t₀ ∈ J, ∃ δ > (0 : ℝ),
    InjOn γ (J ∩ Ioo (t₀ - δ) (t₀ + δ)) ∧ ∀ s ∈ J, ∀ v ∈ J, ∀ t ∈ J, t₀ - δ < s → s ≤ v → v ≤ t → t < t₀ + δ →
      phiDistRS q (γ s) (γ v) + phiDistRS q (γ v) (γ t) = phiDistRS q (γ s) (γ t)

/-- **Definition** (maximal geodesic, Ch. IV §7.4): a geodesic which is not a proper subset of any other geodesic.
Modelling: an open geodesic curve whose trace is contained in the trace of no larger one. -/
def IsMaximalGeodesic {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] (q : S → ℂ → ℂ) (γ : ℝ → S)
    (J : Set ℝ) : Prop :=
  IsGeodesicCurve q γ J ∧ ∀ (γ' : ℝ → S) (J' : Set ℝ), IsGeodesicCurve q γ' J' → γ '' J ⊆ γ' '' J' →
    γ' '' J' = γ '' J

/-- **Lemma 7.3** (Ch. IV §7.4). In a simply connected subdomain of the plane every maximal geodesic is a cross-cut.
Modelling: both ends of the curve leave every compact subset of `G`. -/
theorem lemma4_7_3 {G : TopologicalSpace.Opens ℂ} [SimplyConnectedSpace G] [ConnectedSpace G] {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ G) (hne : ∃ z ∈ (G : Set ℂ), φ z ≠ 0) {γ : ℝ → G} {J : Set ℝ}
    (hγ : IsMaximalGeodesic (fun _ => (G : Set ℂ).indicator φ) γ J) (K : Set G) (hK : IsCompact K) :
    ∃ s₁ ∈ J, ∃ s₂ ∈ J, ∀ v ∈ J, (v < s₁ ∨ s₂ < v) → γ v ∉ K := by
  sorry

/-- **Theorem 7.2** (Ch. IV §7.4). Let `S` be a Riemann surface and `p`, `q` points of `S`. Then a geodesic arc from
`p` to `q` is strictly shorter than any other curve in its homotopy class.
Modelling: "other": a homotopic path with a different trace. -/
theorem thm4_7_2 {S : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] {φ : S → ℂ → ℂ} (hφ : IsHolQuadDiff φ) (hne : φ ≠ 0) {p q : S}
    {γ γ' : Path p q} (hγ : IsPhiGeodesicRS φ γ) (hh : γ'.Homotopic γ) (hne' : range γ' ≠ range γ) :
    phiLengthPathInv φ γ < phiLengthPathInv φ γ' := by
  sorry

/-- **Unlabelled** (Ch. IV §7.4, P1:5919). Every horizontal arc is uniquely length minimizing in its homotopy class.
Modelling: as `thm4_7_2`, for a horizontal arc (`LiZhongQC.IsHorizontalArcRS`). -/
theorem para4_7_4 {S : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] {φ : S → ℂ → ℂ} (hφ : IsHolQuadDiff φ) (hne : φ ≠ 0) {p q : S}
    {α γ' : Path p q} (hα : IsHorizontalArcRS φ α) (hh : γ'.Homotopic α) (hne' : range γ' ≠ range α) :
    phiLengthPathInv φ α < phiLengthPathInv φ γ' := by
  sorry

/-! ## §7.5 Existence of geodesics -/

/-- **Unlabelled** (Ch. IV §7.5, P1:5925–5929, Ahlfors). If `S` is compact, every point of the universal covering
surface `D` of `S` has an infinite distance to the boundary of `D` in the metric of the lifted `φ`.
Modelling: `D` a simply connected Riemann surface with an analytic universal covering `p`, `q′` the lift of `φ`
(`IsDiffLift`); the `q′`-distance from `z₀` tends to `∞` off the compact subsets of `D`. -/
theorem para4_7_5 {S D : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] [TopologicalSpace D] [T2Space D]
    [SecondCountableTopology D] [ConnectedSpace D] [ChartedSpace ℂ D] [IsManifold 𝓘(ℂ) ω D] [SimplyConnectedSpace D]
    {p : D → S} (hp : IsUniversalCoveringSurface p) (hpa : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) {q : S → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (hne : q ≠ 0) {q' : D → ℂ → ℂ} (hq' : IsDiffLift 2 0 p q q') (z₀ : D) :
    Tendsto (fun w => phiDistRS q' z₀ w) (cocompact D) (𝓝 ⊤) := by
  sorry

/-- **Theorem 7.3** (Ch. IV §7.5). Let `S` be a compact Riemann surface and `p`, `q` points of `S`. Then each homotopy
class of curves joining `p` and `q` on `S` contains a unique shortest (hence geodesic) arc.
Modelling: unique up to reparametrization (the trace) (near miss: `LiZhongQC.thm25_4_shortest_exists` and
`LiZhongQC.thm25_4_cor_unique_geodesic`, the latter for genus `> 1`). -/
theorem thm4_7_3 {S : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {φ : S → ℂ → ℂ} (hφ : IsHolQuadDiff φ) (hne : φ ≠ 0)
    {p q : S} (α : Path p q) :
    ∃ γ : Path p q, γ.Homotopic α ∧ IsPhiGeodesicRS φ γ ∧
      (∀ γ' : Path p q, γ'.Homotopic α → phiLengthPathInv φ γ ≤ phiLengthPathInv φ γ') ∧
      ∀ γ' : Path p q, γ'.Homotopic α → phiLengthPathInv φ γ' = phiLengthPathInv φ γ → range γ' = range γ := by
  sorry

end Lehto1987
