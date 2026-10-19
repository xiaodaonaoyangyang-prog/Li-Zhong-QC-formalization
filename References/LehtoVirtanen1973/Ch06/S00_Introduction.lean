import References.LehtoVirtanen1973.Ch04.S05_ComplexDilatation
import References.LehtoVirtanen1973.Ch05.S05_ApplicationOfHilbertTransformation

/-!
# Lehto–Virtanen, Chapter VI, Introduction: Quasiconformal functions

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Introduction to
Chapter VI (p. 239; `full.md` second part P2:1568–1592).

Conventions of Chapter VI. The quasiconformal functions of this chapter are mappings of domains `G` of the plane
`ℂ̄ = LiZhongQC.ExtPlane` into `ℂ̄` which need not be one-to-one; they are maps `ExtPlane → ExtPlane` whose values
outside `G` do not matter. Continuity is in the spherical metric (footnote 53), i.e. in the topology of `ℂ̄`. Analytic
functions may have poles (P2:1574) and may be defined at `∞`: analyticity is read in the charts of I.1.6 and I.2.1
(`localRep`), as for conformal mappings. "A set `E ⊂ G` of isolated points" is a set without accumulation points in
`G` (`Filter.codiscreteWithin`). "Differentiable" refers to finite points with finite values (I.9), through the finite
part `finiteMap f`. `L^p`-derivatives and generalized `L^p`-solutions of a mapping of a domain of `ℂ̄` are the notions
of IV.1.1 and IV.5.3 (`HasLpDerivativesExt`, `IsGeneralizedLpSolution`: the `L^p`-derivatives are those of III.6.1
for the finite part of the mapping on `G − {∞} − f⁻¹(∞)`, and the equation is required almost everywhere on the
finite part of `G`), which are defined for arbitrary mappings; for a quasiconformal function `f⁻¹(∞)`
has no accumulation point in `G`, so this set is a domain of the finite plane. "Almost everywhere in `G`" refers to
the area measure of the finite part of `G`. The extremal exponent `p(K)` of V.5.4 is `limitExponent` (`ℝ≥0∞`-valued,
harmonization H6).

* Definition (analytic function in a domain of the plane, poles and the point `∞` allowed, Introduction) —
  `IsExtAnalyticOn`
* Definition (`K`-quasiconformal function, quasiconformal function, Introduction) — `IsKQuasiconformalFunction`,
  `IsQuasiconformalFunction`
* Definition (locally homeomorphic, and sense-preserving, up to a set of isolated points; Introduction and §1.1) —
  `IsLocalHomeoOffIsolated`, `IsSensePreservingLocalHomeoOffIsolated`
* Unlabelled (Introduction, P2:1584; cited P2:1596, 1598): a quasiconformal function `f = φ ∘ w` is continuous and
  locally homeomorphic (and sense-preserving) up to the isolated points which `w` maps onto zeros of `φ′` or multiple
  poles of `φ`; a `K`-quasiconformal function satisfies the module condition `M(f(Q)) ≤ K M(Q)` —
  `qcFunction_localHomeo`, `kqcFunction_module_condition`
* Unlabelled (Introduction, P2:1586; cited P2:1765): a `K`-quasiconformal function has `L²`-derivatives and
  `L^p`-derivatives for `p < p(K)`, satisfies the dilatation condition almost everywhere, and is a generalized
  `L^p`-solution of a Beltrami equation with `|κ| ≤ (K − 1)/(K + 1)`, `p < p(K)` — `kqcFunction_hasLpDerivatives`,
  `kqcFunction_dilatation_ae`, `kqcFunction_isGeneralizedLpSolution`

The claims of P2:1584 and P2:1586 are stated because §1 and §2 cite them (P2:1596–1598: the geometric properties
"mentioned in the Introduction"; P2:1765: "a `K`-quasiconformal function naturally has `L^p`-derivatives for every
`p < p(K)`"). The closing announcement (P2:1592: theorems of Chapters I, II, IV and V carry over to quasiconformal
functions, "such generalizations will not be dealt with") contains no item.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt)
open References (IsDomainExt finitePart)

/-- **Definition** (analytic function in a domain of `ℂ̄`, Ch. VI Introduction, P2:1574). "Since we shall consider
mappings into the whole plane we allow the analytic functions to have poles": `φ` is analytic in the open set `U` of
`ℂ̄` if it is continuous on `U` (as a mapping into `ℂ̄`) and analytic at every point `z ∈ U` in the charts at `z` and
at `φ(z)` (`localRep`), the book's convention for conformal mappings (I.1.6, I.2.1): at a finite point with a finite
value this is complex differentiability of `φ`, at a pole that of `1/φ`, and at `∞` that of `φ(1/ζ)` at `0`.
Modelling: this is `IsConformalMap` (I.2.1) without the requirements that `U` be a domain and `φ` one-to-one.
Continuity makes the chart representation a germ of `φ` (the chart at a finite value has a junk value at `∞`), which
needs `U` open; every use is on an open set `w(G)`, `w` a homeomorphism of a domain `G`. The constant `∞` is not
excluded; the analytic functions of the Definition and of Stoilow's theorem are non-constant. -/
def IsExtAnalyticOn (φ : ExtPlane → ExtPlane) (U : Set ExtPlane) : Prop :=
  ContinuousOn φ U ∧ ∀ z ∈ U, DifferentiableAt ℂ (localRep φ z) 0

/-- **Definition** (Ch. VI Introduction, P2:1576–1582). A function `f` is called `K`-quasiconformal in a plane domain
`G` if it permits a representation `f = φ ∘ w`, where `w : G → G′` is a `K`-quasiconformal homeomorphism and `φ` is a
non-constant analytic function in `G′`.
Modelling: `G′ = w(G)`; the representation is required on `G` (the values of `f` outside `G` do not matter);
analytic functions may have poles (`IsExtAnalyticOn`); "non-constant": `φ` takes two different values in `w(G)`. `G`
is a domain of `ℂ̄` (part of `IsKQuasiconformal`); `K ≥ 1` is implied, since the maximal dilatation of `w` is at least
`1` (I.3.1). -/
def IsKQuasiconformalFunction (f : ExtPlane → ExtPlane) (G : Set ExtPlane) (K : ℝ) : Prop :=
  ∃ w φ : ExtPlane → ExtPlane, IsKQuasiconformal w G K ∧ IsExtAnalyticOn φ (w '' G) ∧
    (∃ a ∈ w '' G, ∃ b ∈ w '' G, φ a ≠ φ b) ∧ ∀ z ∈ G, f z = φ (w z)

/-- **Definition** (Ch. VI Introduction, P2:1582). A function is quasiconformal if it is `K`-quasiconformal for some
`K`. -/
def IsQuasiconformalFunction (f : ExtPlane → ExtPlane) (G : Set ExtPlane) : Prop :=
  ∃ K : ℝ, IsKQuasiconformalFunction f G K

/-- **Definition** (Ch. VI Introduction, P2:1584, and §1.1, P2:1596). `f` is locally homeomorphic in the domain `G`
up to the set `E ⊂ G` of isolated points ("with the possible exception of isolated points"): every point of `G − E`
has a neighbourhood which `f` maps homeomorphically onto an open set.
Modelling: "a set `E ⊂ G` of isolated points" is read as "`E` has no accumulation point in `G`"
(`G − E ∈ codiscreteWithin G`). The local homeomorphism property is Mathlib's `IsLocalHomeomorphOn`, which depends only
on `f` near the points of `G − E` (`G` is open in every statement). As a hypothesis, the weaker reading "every point of
`E` is isolated in `E`" gives the same notion: the points of `G` at which `f` is not a local homeomorphism form a set
which is closed in `G`; when it is contained in such an `E` it is discrete, hence without accumulation points in `G`,
and it can replace `E`. In conclusions (Theorem 1.2) the stronger reading is asserted. -/
def IsLocalHomeoOffIsolated (f : ExtPlane → ExtPlane) (G E : Set ExtPlane) : Prop :=
  E ⊆ G ∧ G \ E ∈ Filter.codiscreteWithin G ∧ IsLocalHomeomorphOn f (G \ E)

/-- **Definition** (Ch. VI §1.1, P2:1600). `f` is locally homeomorphic and sense-preserving in the domain `G` up to the
set `E ⊂ G` of isolated points: `IsLocalHomeoOffIsolated f G E`, and every point of `G − E` has an open neighbourhood
`U ⊂ G` such that `f` is a sense-preserving homeomorphism of `U` (I.1.5).
Modelling: as for `IsLocalHomeoOffIsolated`; the points at which `f` is not locally a sense-preserving homeomorphism
also form a set which is closed in `G`. -/
def IsSensePreservingLocalHomeoOffIsolated (f : ExtPlane → ExtPlane) (G E : Set ExtPlane) : Prop :=
  IsLocalHomeoOffIsolated f G E ∧ ∀ z ∈ G \ E, ∃ U, IsOpen U ∧ z ∈ U ∧ U ⊆ G ∧ IsSensePreservingOn f U

/-- **Unlabelled** (Ch. VI Introduction, P2:1584; cited at P2:1596, 1598). If `f = φ ∘ w` is quasiconformal in a
domain `G`, then `f` is continuous, and it is locally homeomorphic in `G` up to the points which `w` maps onto zeros
of the derivative `φ′` or onto multiple poles of `φ`, i.e. with the possible exception of isolated points.
Modelling: the hypotheses are those of the Definition (`w` quasiconformal in `G`, `φ` non-constant and analytic in
`w(G)`, `f = φ ∘ w` on `G`). "`φ′(ζ) = 0` or `ζ` a multiple pole of `φ`" (also at `ζ = ∞`) is read in the charts,
`deriv (localRep φ ζ) 0 = 0`: a genuine derivative, since `localRep φ ζ` is complex differentiable at `0` for
`ζ ∈ w(G)`. That this exceptional set has no accumulation point in `G` is part of the conclusion. Sense-preservation
off this set is included, which the book leaves implicit (`f` is there locally a conformal mapping composed with the
sense-preserving `w`): the characterization announced at P2:1596–1598 (Theorem 1.1) assumes it. -/
theorem qcFunction_localHomeo {f w φ : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G)
    (hφ : IsExtAnalyticOn φ (w '' G)) (hφc : ∃ a ∈ w '' G, ∃ b ∈ w '' G, φ a ≠ φ b)
    (hf : ∀ z ∈ G, f z = φ (w z)) :
    ContinuousOn f G ∧
      IsSensePreservingLocalHomeoOffIsolated f G {z ∈ G | deriv (localRep φ (w z)) 0 = 0} := by
  sorry

/-- **Unlabelled** (Ch. VI Introduction, P2:1584; cited at P2:1598). A `K`-quasiconformal function `f` in `G`
satisfies the module condition `M(f(Q)) ≤ K M(Q)` for every quadrilateral `Q` such that `Q̄ ⊂ G` and `Q̄` is mapped
topologically by `f`.
Modelling: the conclusion names the image quadrilateral: `f` is a homeomorphism of `Q` onto a quadrilateral `Q′`
whose vertices are the images of those of `Q` (I.2.3, `IsQuadHomeo`; the image vertices are positively ordered, `f`
being sense-preserving on `Q̄`), and `M(Q′) ≤ K M(Q)`. -/
theorem kqcFunction_module_condition {f : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ}
    (hf : IsKQuasiconformalFunction f G K) {Q : Quadrilateral} (hQG : closure Q.dom ⊆ G)
    (hQ : IsHomeoOn f (closure Q.dom) (f '' closure Q.dom)) :
    ∃ Q' : Quadrilateral, IsQuadHomeo f Q Q' ∧ Q'.module ≤ K * Q.module := by
  sorry

/-- **Unlabelled** (Ch. VI Introduction, P2:1586; cited at P2:1765). A `K`-quasiconformal function `f` in `G` has
`L²`-derivatives, and even `L^p`-derivatives for every `p < p(K)` (cf. V.5.4).
Modelling: `L^p`-derivatives in a domain of `ℂ̄` are those of IV.1.1 (`HasLpDerivativesExt`: the notion of III.6.1 for
the finite part of `f` on `G − {∞} − f⁻¹(∞)`), which the book defines for homeomorphisms; it is the only possible
reading for a function with poles, and `G − {∞} − f⁻¹(∞)` is a domain of the finite plane. The exponents are real with
`1 ≤ p` (III.6.1), compared with `p(K) = limitExponent K` in `[0, ∞]`; the case `p = 2` is stated separately, as in the
book (it does not need V.5). -/
theorem kqcFunction_hasLpDerivatives {f : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ}
    (hf : IsKQuasiconformalFunction f G K) :
    HasLpDerivativesExt f G 2 ∧
      ∀ p : ℝ, 1 ≤ p → ENNReal.ofReal p < limitExponent K → HasLpDerivativesExt f G p := by
  sorry

/-- **Unlabelled** (Ch. VI Introduction, P2:1586). A `K`-quasiconformal function `f` in `G` satisfies the dilatation
condition `max_α |∂_α f(z)| ≤ K min_α |∂_α f(z)|` almost everywhere in `G`.
Modelling: as in Theorem IV.1.1 (`thm4_1_1`): almost every point of `G` is a finite point with a finite value (the
points `∞` and `f⁻¹(∞)` form a null set), at which `f` is differentiable (its finite part `finiteMap f`, I.9) and
satisfies the inequality; the differentiability is asserted, so the value of the derivative at points of
non-differentiability is not used. -/
theorem kqcFunction_dilatation_ae {f : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ}
    (hf : IsKQuasiconformalFunction f G K) :
    ∀ᵐ z ∂(volume.restrict (finitePart G)), DifferentiableAt ℝ (finiteMap f) z ∧
      (⨆ α : ℝ, ‖dirDeriv (finiteMap f) z α‖) ≤ K * ⨅ α : ℝ, ‖dirDeriv (finiteMap f) z α‖ := by
  sorry

/-- **Unlabelled** (Ch. VI Introduction, P2:1586; the necessity half of the analytic characterization announced at
P2:1588). A `K`-quasiconformal function `f` in `G` is a generalized `L^p`-solution of a Beltrami equation
`f_{\bar z} = κ f_z`, where `|κ| ≤ (K − 1)/(K + 1)`, `p < p(K)`.
Modelling: [OCR] the equation is OCR'd as `f_z = x f_z` (P2:1586). `κ` is a measurable function on the finite part
of `G` with the bound at every point (multiplied by `K + 1 > 0`), so that `f_{\bar z} = κ f_z` is a Beltrami
equation in the sense of IV.5.3; one `κ` serves for every `p`. Generalized `L^p`-solutions are those of IV.5.3
(`IsGeneralizedLpSolution`, defined for arbitrary mappings of `ℂ̄`), with real `p ≥ 1` as in
`kqcFunction_hasLpDerivatives`. -/
theorem kqcFunction_isGeneralizedLpSolution {f : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ}
    (hf : IsKQuasiconformalFunction f G K) :
    ∃ κ : ℂ → ℂ, AEStronglyMeasurable κ (volume.restrict (finitePart G)) ∧
      (∀ z ∈ finitePart G, (K + 1) * ‖κ z‖ ≤ K - 1) ∧
      ∀ p : ℝ, 1 ≤ p → ENNReal.ofReal p < limitExponent K → IsGeneralizedLpSolution f κ G p := by
  sorry

end LehtoVirtanen1973
