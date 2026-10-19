import References.LehtoVirtanen1973.Ch04.S03_VariantsGeometricDefinition
import References.LehtoVirtanen1973.Ch02.S01_ExtremalRingDomains
import References.Pommerenke1992.Ch01.S03_KoebeDistortionTheorem
import References.Pommerenke1992.Ch04.S06_HyperbolicMetric

/-!
# Lehto, Chapter I §1: Conformal invariants

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. I §1 (`full.md`
P1:349–596).

Standing conventions of the book, as modelled here (see the root file `References/Lehto1987.lean`): the *plane* is
the Riemann sphere `ℂ̄ = LiZhongQC.ExtPlane` (P1:353); domains, Jordan curves and Jordan domains are those of `ℂ̄`
(`References.IsDomainExt`, `LiZhongQC.IsJordanCurve`, `References.IsJordanDomainExt`); conformal mappings,
quadrilaterals, their modules, ring domains and their modules are the Lehto–Virtanen notions
(`LehtoVirtanen1973.IsConformalMap`, `Quadrilateral`, `quadModule`, `IsRingDomain`, `ringModule`), which this chapter
summarizes. The Poincaré density `η_A = |f′|/(1 − |f|²)` (`f : A → D` conformal) is Gehring's `hypDensity`, taken at
the finite points of `A`; `d(z, ∂A)` is the euclidean distance from `z` to the finite boundary points of `A`.

* Formula (1.1) (§1.1) — exists: `Pommerenke1992.eq1_2_8` (the hyperbolic distance of the unit disc for the metric
  with density 1/(1 − |z|²), which is the book's metric; the same formula written with the quotient
  |z₁ − z₂|/|1 − z̄₁z₂|)
* Definition (Poincaré density `η_A`, hyperbolic metric, hyperbolic segments, §1.1) — exists:
  `Gehring1978.hypDensity`, `Pommerenke1992.IsHypGeodesicSegment` (the density |f′|/(1 − |f|²) for a conformal map f
  of A onto the unit disc; hyperbolic segments as images of non-euclidean segments of the disc)
* Formula (1.2) (§1.1) — `eq1_1_2`
* Formula (1.3) (§1.1) — `eq1_1_3`
* Formula (1.4) (§1.1) — `eq1_1_4`
* Koebe one-quarter theorem (§1.1, quoted from Nehari) — exists: `Pommerenke1992.cor1_4` (at z = 0, where the
  distance d_f(0) to the boundary of f(D) is at least |f′(0)|/4; the hypotheses are weaker: f holomorphic and
  one-to-one in the disc, no normalization)
* Formula (1.5) (§1.1) — `eq1_1_5`
* Definition (Jordan curve, Jordan domain, §1.2) — exists: `LiZhongQC.IsJordanCurve`,
  `References.IsJordanDomainExt`
* Definition (local connectivity at a boundary point, §1.2) — `IsLocConnAtExt`
* Unlabelled (§1.2, P1:435): a conformal map of a disc onto a domain which is locally connected at every boundary
  point extends to a homeomorphism of the closures, and the boundary is a Jordan curve — `para1_1_2_a`
* Unlabelled (§1.2, P1:437): a conformal map of a Jordan domain onto a Jordan domain has a homeomorphic extension
  to the closures — `para1_1_2_b`
* Unlabelled (§1.2, P1:437): the images of three boundary points can be prescribed modulo orientation — exists:
  `LehtoVirtanen1973.conformal_three_point` (for positively ordered triples on the boundaries of two Jordan domains
  there is a unique conformal map with the prescribed boundary values)
* Definition (quadrilateral, sides, canonical mapping and canonical rectangle, module `M(Q)`; existence of a
  canonical mapping and independence of the module from it, §1.2) — exists: `LehtoVirtanen1973.Quadrilateral`,
  `LehtoVirtanen1973.Quadrilateral.side`, `LehtoVirtanen1973.IsCanonicalMap`, `LehtoVirtanen1973.quadModule`,
  `LehtoVirtanen1973.exists_canonicalMap`, `LehtoVirtanen1973.module_eq_of_isCanonicalMap` (Lehto's definitions are
  those of LV, to which he refers)
* Unlabelled (§1.2, P1:451): `M(Q(z₁, z₂, z₃, z₄)) = 1/M(Q(z₂, z₃, z₄, z₁))` — exists:
  `LehtoVirtanen1973.module_rotate` (its second conjunct)
* Unlabelled (§1.2, P1:453): the module is a conformal invariant — exists:
  `LehtoVirtanen1973.quad_confEquiv_iff_module_eq` (a conformal map of quadrilaterals, vertices to vertices, which
  is what the book's formula with the images f(zᵢ) of the vertices means, preserves the module)
* Formula (1.6) (§1.3) — omitted: the step of the proof of (1.7) which writes M(Q) with the canonical mapping
* Definition (the class `P` of admissible densities of `Q` and the area `m_ρ(Q)`, §1.3) — exists:
  `LiZhongQC.densitiesP0`, `LiZhongQC.rhoArea`
* Formula (1.7) (§1.3) — exists: `LehtoVirtanen1973.module_quad_joining_arcs` (the module of the family of the
  Jordan arcs in Q which join the sides (z₁, z₂) and (z₃, z₄), in which only the locally rectifiable members count,
  equals M(Q); the module of a family is the infimum of the areas of its admissible densities)
* Formula (1.8) (§1.4, Rengel's inequality) — exists: `LehtoVirtanen1973.rengel_inequality` (its right half; s₁ is
  the distance of the a-sides in Q and m(Q) the area)
* Unlabelled (§1.4, P1:505): equality in (1.8) holds if and only if `Q` is a rectangle with its usual vertices —
  exists: `LehtoVirtanen1973.rengel_eq_right_iff`
* Unlabelled (§1.4, P1:507): continuity of the module under convergence from inside — exists:
  `LehtoVirtanen1973.lemma1_4_3` (LV requires only that the closures of the Qₙ lie in the closure of Q, a weaker
  hypothesis than the book's closures in Q)
* Theorem 1.1 (§1.4) — exists: `LehtoVirtanen1973.thm1_5_1` (a sense-preserving homeomorphism of a domain which
  leaves the modules of the quadrilaterals with closure in the domain invariant has maximal dilatation at most 1 by
  the definition of the maximal dilatation, i.e. it is 1-quasiconformal, and LV Theorem I.5.1 concludes that it is
  conformal)
* Definition (ring domain, canonical mapping, module `M(B) = log R`; the mapping theorem for ring domains, §1.5) —
  exists: `LehtoVirtanen1973.IsRingDomain`, `LehtoVirtanen1973.IsCanonicalRingMap`, `LehtoVirtanen1973.ringModule`,
  `LehtoVirtanen1973.ring_mapping_theorem`
* Unlabelled (§1.5, P1:533): `M(B) = 2π inf_{ρ ∈ P} m_ρ(B)` over the separating curves — exists:
  `LehtoVirtanen1973.module_ring_separating_curves` (the module of the family of Jordan curves in B separating the
  boundary components is M(B)/2π; the infimum over P is that module)
* Formula (1.9) (§1.5) — exists: `LehtoVirtanen1973.lemma1_6_1` (the same statement with LV's spherical distance,
  which is the book's s; δ > 0 as in the book)
* Formula (1.10) (§1.5) — exists: `LehtoVirtanen1973.lemma1_6_2` (the same statement)
* Definition (Grötzsch ring domain, `μ(r)`, §1.5) — exists: `LiZhongQC.grotzschDomain`, `LiZhongQC.grotzschMu`
* Unlabelled (§1.5, P1:553, Grötzsch): a ring domain separating the unit circle from `0` and `r` has module at most
  `μ(r)` — exists: `LehtoVirtanen1973.grotzsch_module_theorem`
* Formula (1.11) (§1.5) — exists: `LehtoVirtanen1973.thm2_1_1_ii` (the Teichmüller ring domain bounded by the
  segments from −r₁ to 0 and from r₂ to ∞ is a ring domain with module 2μ(√(r₁/(r₁ + r₂))))
* Formula (1.12) (§1.5) — exists: `LehtoVirtanen1973.teichmuller_module_theorem` (with z₁ ≠ 0, which the book's
  "points 0 and z₁" presupposes; for z₁ = 0 the bound is meaningless)
* Definition (path, curve, §1.6) — omitted: terminology; paths are modelled by their point sets, as in LV
* Definition (admissible `ρ`, module `M(Γ)` of a path family, §1.6) — exists: `LehtoVirtanen1973.IsAdmissibleFor`,
  `LehtoVirtanen1973.arcFamilyModule`

Not stated (inventory U−): that `η_A` does not depend on `f`, `η_H = 1/(2 Im z)` and that the geodesics are the
hyperbolic segments (P1:384, statements about the definition); the sharpness of (1.3) and (1.4) (P1:410); the
extension of a conformal map of Jordan domains to the whole plane (P1:437, a remark after `para1_1_2_b`, not cited);
the conformal invariance of the module of a path family (P1:590, not cited). The Möbius self-maps of `D` (P1:357) and
Schwarz's lemma are quoted classics.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Lehto1987

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve unitDisc)
open References (IsDomainExt IsJordanDomainExt finitePart)
open LehtoVirtanen1973 (IsConformalMap IsHomeoOn)
open Gehring1978 (hypDensity IsHypSimplyConnectedExt)

/-! ## §1.1 Hyperbolic metric -/

/-- **Formula (1.2)** (Ch. I §1.1). The Poincaré density is monotonic with respect to the domain: if `A₁` is a
simply connected subdomain of `A` and `z ∈ A₁`, then `η_A(z) ≤ η_{A₁}(z)`.
Modelling: `A` and `A₁` are simply connected domains of `ℂ̄` with more than one boundary point (Gehring's
`IsHypSimplyConnectedExt`, the domains for which `η` is defined, P1:376); `z` is a finite point. -/
theorem eq1_1_2 {A A₁ : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) (hA₁ : IsHypSimplyConnectedExt A₁)
    (hsub : A₁ ⊆ A) {z : ℂ} (hz : (z : ExtPlane) ∈ A₁) : hypDensity A z ≤ hypDensity A₁ z := by
  sorry

/-- **Formula (1.3)** (Ch. I §1.1). `η_A(z) ≤ 1/d(z, ∂A)`.
Modelling: `A` is a simply connected domain with more than one boundary point and `z ∈ A` a finite point;
`d(z, ∂A)` is the euclidean distance from `z` to the finite points of `∂A` (there are some, `∂A` having at least two
points), which is positive since this set is closed and does not contain `z`. -/
theorem eq1_1_3 {A : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) {z : ℂ} (hz : (z : ExtPlane) ∈ A) :
    hypDensity A z ≤ 1 / Metric.infDist z (finitePart (frontier A)) := by
  sorry

/-- **Formula (1.4)** (Ch. I §1.1). For domains `A` not containing `∞`, `η_A(z) ≥ 1/(4 d(z, ∂A))`.
Modelling: as in `eq1_1_3`. -/
theorem eq1_1_4 {A : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) (hinf : extInf ∉ A) {z : ℂ}
    (hz : (z : ExtPlane) ∈ A) : 1 / (4 * Metric.infDist z (finitePart (frontier A))) ≤ hypDensity A z := by
  sorry

/-- **Formula (1.5)** (Ch. I §1.1). Let `A` be a simply connected domain and `w₁, w₂` finite points outside `A`.
Then `η_A(z) ≥ |w₁ − w₂| / (4 |z − w₁| |z − w₂|)` for every `z ∈ A`.
Modelling: `A` has more than one boundary point, as for every use of `η_A`; `z` is a finite point of `A` (the right
side is written for finite `z`). -/
theorem eq1_1_5 {A : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) {w₁ w₂ : ℂ} (hw₁ : (w₁ : ExtPlane) ∉ A)
    (hw₂ : (w₂ : ExtPlane) ∉ A) {z : ℂ} (hz : (z : ExtPlane) ∈ A) :
    ‖w₁ - w₂‖ / (4 * ‖z - w₁‖ * ‖z - w₂‖) ≤ hypDensity A z := by
  sorry

/-! ## §1.2 Module of a quadrilateral -/

/-- **Definition** (local connectivity at a boundary point, Ch. I §1.2). The domain `A` is locally connected at the
point `z` of its boundary: every neighbourhood `U ∋ z` in the plane contains a neighbourhood `V` of `z` such that
`V ∩ A` is connected. -/
def IsLocConnAtExt (A : Set ExtPlane) (z : ExtPlane) : Prop :=
  ∀ U ∈ 𝓝 z, ∃ V ∈ 𝓝 z, V ⊆ U ∧ IsPreconnected (V ∩ A)

/-- **Unlabelled** (Ch. I §1.2, P1:435). Let `f` be a conformal mapping of a disc `D` onto a domain `A` which is
locally connected at every point of its boundary. Then `f` can be extended to a homeomorphism between the closures
of `D` and `A`; in particular `∂A` is a Jordan curve.
Modelling: `D` is the unit disc (the book's notation `D`, P1:355). -/
theorem para1_1_2_a {f : ExtPlane → ExtPlane} {A : Set ExtPlane} (hf : IsConformalMap f (toExt unitDisc))
    (hfA : f '' toExt unitDisc = A) (hloc : ∀ z ∈ frontier A, IsLocConnAtExt A z) :
    (∃ F : ExtPlane → ExtPlane, EqOn F f (toExt unitDisc) ∧
      IsHomeoOn F (closure (toExt unitDisc)) (closure A)) ∧ IsJordanCurve (frontier A) := by
  sorry

/-- **Unlabelled** (Ch. I §1.2, P1:437). A conformal mapping of a Jordan domain onto another Jordan domain has a
homeomorphic extension to the boundary. -/
theorem para1_1_2_b {f : ExtPlane → ExtPlane} {A A' : Set ExtPlane} (hA : IsJordanDomainExt A)
    (hA' : IsJordanDomainExt A') (hf : IsConformalMap f A) (hfA : f '' A = A') :
    ∃ F : ExtPlane → ExtPlane, EqOn F f A ∧ IsHomeoOn F (closure A) (closure A') := by
  sorry

end Lehto1987
