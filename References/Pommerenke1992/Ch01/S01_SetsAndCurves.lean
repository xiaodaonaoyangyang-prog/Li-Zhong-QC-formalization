import References.LehtoVirtanen1973.Ch01.S01_TopologicalProperties

/-!
# Pommerenke 1992, Ch. 1 §1.1 Sets and Curves

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §1.1; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 167–311.

* Definition (notation `D(a, r)`, `𝔻`, `𝕋`, `Ĉ`, §1.1.1) — exists: `Metric.ball` `LiZhongQC.unitDisc`
  `Metric.sphere` `LiZhongQC.ExtPlane` (the disc `D(a, r)`, the unit disc, the unit circle `sphere 0 1`, the Riemann
  sphere)
* Definition (the exterior `𝔻* = {|z| > 1} ∪ {∞}`, §1.1.1) — `extDiscExterior`
* Definition (the chordal metric `d#`, (1.1.1)) — `chordalDist`
* Definition (the rotations of the sphere, (1.1.2)) — `IsSphereRotation`
* Formula (1.1.2) (`d#` is invariant under the rotations of the sphere) — `eq1_1_2`
* Definition (the spherical diameter `diam#`, §1.1.1) — `chordalDiam`
* Definition (the euclidean diameter `diam A` of `A ⊆ ℂ`, §1.1.1) — exists: `Metric.diam` `Metric.ediam` (the real
  diameter is used for the bounded sets of the statements; the extended one is infinite for unbounded sets)
* Definition (connected set, §1.1.2) — exists: `IsPreconnected` (the empty set is connected, as in the book)
* Definition (continuum, §1.1.2) — `IsContinuum`
* Definition (domain; components, §1.1.2) — exists: `References.IsDomainExt` `connectedComponentIn`
* Definition (curve (1.1.4), closed curve (1.1.5), §1.1.3) — `Curve`, `Curve.trace`, `Curve.IsClosed`
* Definition (Jordan arc and Jordan curve, §1.1.3) — exists: `LehtoVirtanen1973.IsClosedJordanArc`
  `LiZhongQC.IsJordanCurve` (as sets; a continuous injective map of a compact interval is an embedding)
* Definition (open Jordan arc (1.1.6), §1.1.3) — `IsOpenJordanArcP`
* Jordan Curve Theorem (quoted, §1.1.3) — exists: `LehtoVirtanen1973.jordan_curve_theorem` (the complement of a
  Jordan curve of the sphere is the union of two disjoint domains, both bounded by the curve)
* Definition (Jordan domain, §1.1.3) — exists: `References.IsJordanDomainExt`
* Definition (the inner domain of a Jordan curve of `ℂ`, §1.1.3) — `innerDomain`
* Definition (two points separated by a closed set, §1.1.3) — exists: `LehtoVirtanen1973.Separates` (applied to the
  singletons of the two points)
* Janiszewski's Theorem (quoted, §1.1.3) — exists: `LehtoVirtanen1973.lemma1_1_3` (the same statement: closed sets
  with connected intersection)
* Definition (length (1.1.7); rectifiable curve, §1.1.4) — exists: `eVariationOn` `BoundedVariationOn` (the length of
  a curve with parameter interval `[α, β]` is the supremum over partitions of that interval)
* Definition (the length of a union of disjoint curves, §1.1.4) — `lengthUnion`
* Definition (half-open curve (1.1.11), its length (1.1.12), "ends at `b`" (1.1.13), §1.1.4) — `HalfOpenCurve`,
  `HalfOpenCurve.length`, `HalfOpenCurve.EndsAt`
* Proposition 1.1 — `prop1_1`

Not items (DESIGN §3): the equivalence of the spherical and euclidean metrics on bounded sets of `ℂ` (l. 203, a
standard fact, used as a convention in §2.4, l. 1288, 1358–1360); the facts on connected sets, continua and domains
quoted in §1.1.2 (standard, not cited); the decomposition (1.1.3) of an open set into components (not cited by
number); "not separated by `A`" means "joinable by a curve avoiding `A`" (l. 250, a remark on the definition);
(1.1.8) `diam C ≤ Λ(C)` and the integral formulas (1.1.9), (1.1.10) for the length (not cited).

**Conventions.** The Riemann sphere `Ĉ` is `LiZhongQC.ExtPlane`; "connected" allows the empty set
(`IsPreconnected`). The book's spherical metric is the *chordal* metric `d#`, which is not a constant multiple of the
Lehto–Virtanen spherical distance (`d# = sin k`), so it is defined here.
-/

open Complex Set Metric Filter Topology
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve mobiusExt)

/-- **Definition** (§1.1.1). The exterior of the unit circle, `𝔻* = {z ∈ ℂ : |z| > 1} ∪ {∞}`, a subset of `Ĉ`. -/
def extDiscExterior : Set ExtPlane :=
  toExt {z : ℂ | 1 < ‖z‖} ∪ {extInf}

/-- **Definition (1.1.1)** (§1.1.1). The spherical (chordal) metric of `Ĉ`:
`d#(z, w) = |z - w|/√((1 + |z|²)(1 + |w|²))` for `z, w ∈ ℂ`, `d#(z, ∞) = 1/√(1 + |z|²)` and `d#(∞, ∞) = 0`. -/
def chordalDist (z w : ExtPlane) : ℝ :=
  OnePoint.elim z (OnePoint.elim w 0 fun b => 1 / Real.sqrt (1 + ‖b‖ ^ 2))
    fun a => OnePoint.elim w (1 / Real.sqrt (1 + ‖a‖ ^ 2))
      fun b => ‖a - b‖ / Real.sqrt ((1 + ‖a‖ ^ 2) * (1 + ‖b‖ ^ 2))

/-- **Definition (1.1.2)** (§1.1.1). `τ` is a rotation of the sphere: a Möbius transformation
`τ(z) = (a z - b)/(b̄ z + ā)` with `|a|² + |b|² > 0`. -/
def IsSphereRotation (τ : ExtPlane → ExtPlane) : Prop :=
  ∃ a b : ℂ, 0 < ‖a‖ ^ 2 + ‖b‖ ^ 2 ∧ τ = mobiusExt a (-b) (conj b) (conj a)

/-- **Formula (1.1.2)** (§1.1.1; cited as (1.1.2) in §1.2). The spherical metric is invariant under the rotations of
the sphere. -/
theorem eq1_1_2 {τ : ExtPlane → ExtPlane} (hτ : IsSphereRotation τ) (z w : ExtPlane) :
    chordalDist (τ z) (τ w) = chordalDist z w := by
  sorry

/-- **Definition** (§1.1.1). The spherical diameter `diam# A` of `A ⊆ Ĉ` (for the chordal metric; `0` for the empty
set). The chordal distances are at most `1`, so the supremum is genuine. -/
def chordalDiam (A : Set ExtPlane) : ℝ :=
  sSup (image2 chordalDist A A)

/-- **Definition** (§1.1.2). A continuum: a compact connected set with more than one point.
Modelling: unlike `LehtoVirtanen1973.IsContinuum` (compact and connected, with no condition on the number of
points), the book requires more than one point. -/
def IsContinuum (A : Set ExtPlane) : Prop :=
  IsCompact A ∧ IsConnected A ∧ A.Nontrivial

/-- **Definition (1.1.4)** (§1.1.3). A curve `C : φ(t), α ≤ t ≤ β`, with `φ` continuous on `[α, β]`, in the space
`X` (`X = ℂ` or `Ĉ`). A curve is its parametric representation. -/
structure Curve (X : Type*) [TopologicalSpace X] where
  /-- The parametrization `φ`. -/
  toFun : ℝ → X
  /-- The initial parameter `α`. -/
  α : ℝ
  /-- The final parameter `β`. -/
  β : ℝ
  le : α ≤ β
  cont : ContinuousOn toFun (Icc α β)

/-- The point set of a curve, `φ([α, β])` (the book writes `C ⊂ E` when it lies in `E`). -/
def Curve.trace {X : Type*} [TopologicalSpace X] (C : Curve X) : Set X :=
  C.toFun '' Icc C.α C.β

/-- **Definition (1.1.5)** (§1.1.3). The curve is closed: `φ(α) = φ(β)`. A closed curve can equivalently be
parametrized by the unit circle. -/
def Curve.IsClosed {X : Type*} [TopologicalSpace X] (C : Curve X) : Prop :=
  C.toFun C.α = C.toFun C.β

/-- **Definition (1.1.6)** (§1.1.3). `C ⊆ Ĉ` is an open Jordan arc: it has a parametrization `φ(t)`, `α < t < β`,
with `φ` continuous and injective on `(α, β)`.
Modelling: the book asks only for continuity and injectivity, not for a homeomorphism onto the image, so this is
weaker than `LehtoVirtanen1973.IsOpenJordanArc` (approved by the leader, 2026-09-28). -/
def IsOpenJordanArcP (C : Set ExtPlane) : Prop :=
  ∃ (φ : ℝ → ExtPlane) (α β : ℝ), α < β ∧ ContinuousOn φ (Ioo α β) ∧ InjOn φ (Ioo α β) ∧ φ '' Ioo α β = C

/-- **Definition** (§1.1.3). The inner domain of a Jordan curve `J ⊆ ℂ`: the bounded component of `ℂ ∖ J`.
Modelling: the union of the bounded components of `ℂ ∖ J`; by the Jordan curve theorem there is exactly one. -/
def innerDomain (J : Set ℂ) : Set ℂ :=
  {z | z ∉ J ∧ Bornology.IsBounded (connectedComponentIn Jᶜ z)}

/-- **Definition** (§1.1.4). The length of a union of disjoint curves `C₁, C₂, …` of `ℂ`: `Λ(⋃ C_k) = Σ Λ(C_k)`,
where `Λ(C_k)` is the length (1.1.7) of `C_k` (`eVariationOn` of its parametrization); `Λ(∅) = 0` (the empty
family).
Modelling: the definition is the sum for any family; the book, and the statements that use it, take the curves
disjoint. -/
def lengthUnion {ι : Type*} (C : ι → Curve ℂ) : ℝ≥0∞ :=
  ∑' k, eVariationOn (C k).toFun (Icc (C k).α (C k).β)

/-- **Definition (1.1.11)** (§1.1.4). A half-open curve `C : φ(t), α ≤ t < β` of `ℂ`, with `φ` continuous in
`[α, β)`. -/
structure HalfOpenCurve where
  /-- The parametrization `φ`. -/
  toFun : ℝ → ℂ
  /-- The initial parameter `α`. -/
  α : ℝ
  /-- The final (excluded) parameter `β`. -/
  β : ℝ
  lt : α < β
  cont : ContinuousOn toFun (Ico α β)

/-- **Definition (1.1.12)** (§1.1.4). The length of a half-open curve: `Λ(C) = lim_{τ → β} Λ(C_τ)`, where `C_τ` is
the curve `φ(t)`, `α ≤ t ≤ τ`.
Modelling: `Λ(C_τ)` increases with `τ`, so the limit is the supremum. -/
def HalfOpenCurve.length (C : HalfOpenCurve) : ℝ≥0∞ :=
  ⨆ τ ∈ Ico C.α C.β, eVariationOn C.toFun (Icc C.α τ)

/-- **Definition (1.1.13)** (§1.1.4). The half-open curve `C` ends at `b ∈ Ĉ`: `b = lim_{t → β} φ(t)` exists. -/
def HalfOpenCurve.EndsAt (C : HalfOpenCurve) (b : ExtPlane) : Prop :=
  Tendsto (fun t => (C.toFun t : ExtPlane)) (𝓝[<] C.β) (𝓝 b)

/-- **Proposition 1.1** (§1.1.4). If `C` is a half-open curve in the open set `G ⊆ ℂ` and if `Λ(C) < ∞`, then `C`
ends at a point `b ∈ Ḡ`.
Modelling: `Ḡ` is the closure of `G` in `ℂ`, so `b` is finite (a curve of finite length is bounded; the proof of
Theorem 1.7 uses this form). -/
theorem prop1_1 {G : Set ℂ} (hG : IsOpen G) {C : HalfOpenCurve} (hCG : C.toFun '' Ico C.α C.β ⊆ G)
    (hC : C.length < ⊤) : ∃ b ∈ closure G, C.EndsAt (b : ExtPlane) := by
  sorry

end Pommerenke1992
