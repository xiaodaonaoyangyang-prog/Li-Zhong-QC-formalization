import References.LehtoVirtanen1973.Ch02.S07_QuasisymmetricFunctions
import References.LehtoVirtanen1973.Ch01.S08_ExtensionTheorems
import LiZhongQC.Ch04.S18_BoundedTurning

/-!
# Lehto–Virtanen, Chapter II §8: Quasiconformal continuation

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. II §8
(pp. 96–105; `full.md` P1:2890–3094).

Mappings and domains are those of Chapter I on `ℂ̄`; "a quasiconformal mapping of the whole plane" is a
quasiconformal mapping of the domain `univ = ℂ̄`. Circles are the circles of `ℂ̄` of I.8.4 (`IsGenCircle`, lines
included; a linear transformation carries one onto another and is conformal). Anti-quasiconformal mappings are those
of I.3.2. The upper and lower half-planes are `H₁ = toExt LiZhongQC.upperHalf` and `H₂ = toExt LiZhongQC.lowerHalf`.
Spherical diameters and distances are `sphericalDiam` and `sphericalDist` (I.1.1, I.6.5).

* Definition (quasiconformal continuation, §8.1) — `IsQCContinuation`
* Theorem 8.1 (§8.1) — `thm2_8_1`
* Definition (quasiconformal arc, quasiconformal curve, §8.2) — `IsQuasiconformalArc`, `IsQuasiconformalCurve`
* Unlabelled (§8.2, P1:2922–2924): every closed quasiconformal arc and every quasiconformal curve is the image of a
  line segment, resp. of a circle, under a quasiconformal mapping of the whole plane —
  `isQuasiconformalArc_eq_image_segment`, `isQuasiconformalCurve_eq_image_circle`
* Unlabelled (§8.2, P1:2926): subarcs of quasiconformal curves are quasiconformal; a closed Jordan arc is
  quasiconformal if and only if it is a subarc of a quasiconformal curve — `isQuasiconformalArc_of_subset_curve`,
  `isQuasiconformalArc_iff_subset_curve`
* Theorem 8.2 (§8.3) — `thm2_8_2`
* Theorem 8.3 (§8.3, Springer) — `thm2_8_3`
* Definition (Jordan curve bounding two domains; quasiconformal reflection, §8.4) — `JordanCurveBounds`,
  `IsQuasiconformalReflection`
* Unlabelled (§8.4, P1:2942–2944): a Jordan curve admits a quasiconformal reflection if and only if it is
  quasiconformal — `exists_qcReflection_iff`
* Definition (conjugate quadrilaterals, §8.5) — `AreConjugateQuads`
* Theorem 8.4 (§8.5, footnote 27) — `thm2_8_4`
* Theorem 8.5 (§8.6, Tienari) — `thm2_8_5`
* Definition (Jordan curve of bounded turning, §8.7) — exists: `LiZhongQC.IsBoundedTurning` (used as: there is M
  with IsBoundedTurning C M; for any two distinct finite points of the Jordan curve C, one of the two arcs into which
  they divide C does not pass through the point at infinity and has euclidean diameter at most M times their
  distance; an arc through the point at infinity has infinite diameter, so this is the arc of smaller diameter of the
  book, and the normalization M ≥ 1 is harmless)
* Theorem 8.6 (§8.7) — `thm2_8_6`
* Unlabelled (§8.8, P1:3034–3036): bounded turning expressed in the spherical metric — `boundedTurning_iff_spherical`
* Definition (Jordan arc of bounded turning, §8.8) — `IsBoundedTurningArc`
* Formula (8.5) (§8.8) — `eq2_8_5`
* Unlabelled (§8.8, P1:3058–3060; cited P1:3074): every closed subarc of a quasiconformal curve is of bounded
  turning — `isBoundedTurningArc_of_subset_curve`
* Unlabelled (§8.9, P1:3062–3064): a closed quasiconformal arc is of bounded turning —
  `isBoundedTurningArc_of_isQuasiconformalArc`
* Rickman's theorem (§8.9, quoted) — `rickman_theorem`
* Theorem 8.7 (§8.9) — `thm2_8_7`

Not stated (inventory U−: immediate, steps of proofs, or examples): analytic arcs and curves are quasiconformal
(P1:2928, "by definition"); the polygon-bounded compact set of the proof of Theorem 8.1 (cited "cf. II.8.1" at
P1:4425, a proof step); closed subarcs of an open Jordan arc of bounded turning are
quasiconformal (P1:3066–3068, a weaker form of Rickman's theorem, not cited); the examples of §8.10 (P1:3078–3091,
including the non-rectifiable quasiconformal arcs of Fig. 11; examples, although cited at P1:5103, 5161, P2:161)
and the quoted result of Gehring–Väisälä on Hausdorff dimensions (P1:3093); the proof steps (8.1)–(8.4); the
condition (8.6), which is the spherical condition in
`boundedTurning_iff_spherical` and `IsBoundedTurningArc` (footnote 28: the smaller arc for curves).
-/

open Complex Set Filter Topology
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve IsMobius upperHalf lowerHalf)
open References (IsDomainExt IsJordanDomainExt finitePart)

/-! ## §8.1 Continuation to the exterior of a compact set -/

/-- **Definition** (quasiconformal continuation, Ch. II §8.1). An extension of the quasiconformal mapping `w` of `G`
to a quasiconformal mapping `W` of a domain `G₁` containing `G` as a proper subset. -/
def IsQCContinuation (w : ExtPlane → ExtPlane) (G : Set ExtPlane) (W : ExtPlane → ExtPlane) (G₁ : Set ExtPlane) :
    Prop :=
  IsQuasiconformalMap w G ∧ G ⊂ G₁ ∧ IsQuasiconformalMap W G₁ ∧ EqOn W w G

/-- **Theorem 8.1** (Ch. II §8.1). Let `w₀ : G → G′` be a `K`-quasiconformal mapping and `F` a compact subset of the
domain `G`. Then there exists a quasiconformal mapping of the whole plane which coincides with `w₀` in `F` and whose
maximal dilatation is bounded by a number depending only on `K`, `G` and `F`.
Modelling: `∀ G F K, ∃ K′, ∀ w₀, …` (the bound depends only on `K`, `G` and `F`). -/
theorem thm2_8_1 (G F : Set ExtPlane) (K : ℝ) (hG : IsDomainExt G) (hF : IsCompact F) (hFG : F ⊆ G) :
    ∃ K' : ℝ, ∀ w₀ : ExtPlane → ExtPlane, IsKQuasiconformal w₀ G K →
      ∃ W : ExtPlane → ExtPlane, IsKQuasiconformal W univ K' ∧ EqOn W w₀ F := by
  sorry

/-! ## §8.2 Quasiconformal arcs and curves -/

/-- **Definition** (quasiconformal arc, Ch. II §8.2). A Jordan arc `C` is quasiconformal if there exists a
quasiconformal mapping of a domain `G ⊃ C` which carries `C` into a line segment or a circle.
[OCR] The source prints "`G > C`".
Modelling: line segments are bounded segments of the finite plane (I.1.3); circles are the circles of `ℂ̄`
(`IsGenCircle`, lines included, which changes nothing since a linear transformation carries a line onto a circle and
is conformal). -/
def IsQuasiconformalArc (C : Set ExtPlane) : Prop :=
  IsJordanArc C ∧ ∃ (G : Set ExtPlane) (w : ExtPlane → ExtPlane), C ⊆ G ∧ IsQuasiconformalMap w G ∧
    ((∃ a b : ℂ, w '' C ⊆ toExt (segment ℝ a b)) ∨ ∃ Γ, IsGenCircle Γ ∧ w '' C ⊆ Γ)

/-- **Definition** (quasiconformal curve, Ch. II §8.2). A Jordan curve `C` is quasiconformal if there exists a
quasiconformal mapping of a domain `G ⊃ C` which carries `C` into a line segment or a circle (the book's definition
covers arcs and curves at once; a Jordan curve can only be carried onto a circle).
Modelling: as for `IsQuasiconformalArc`. -/
def IsQuasiconformalCurve (C : Set ExtPlane) : Prop :=
  IsJordanCurve C ∧ ∃ (G : Set ExtPlane) (w : ExtPlane → ExtPlane), C ⊆ G ∧ IsQuasiconformalMap w G ∧
    ((∃ a b : ℂ, w '' C ⊆ toExt (segment ℝ a b)) ∨ ∃ Γ, IsGenCircle Γ ∧ w '' C ⊆ Γ)

/-- **Unlabelled** (Ch. II §8.2, P1:2922–2924). By Theorem 8.1, every closed quasiconformal arc is the image of a
line segment under a quasiconformal mapping of the whole plane (cited in §8.2–8.9). -/
theorem isQuasiconformalArc_eq_image_segment {C : Set ExtPlane} (hC : IsClosedJordanArc C)
    (hqc : IsQuasiconformalArc C) :
    ∃ (w : ExtPlane → ExtPlane) (a b : ℂ), IsQuasiconformalMap w univ ∧ C = w '' toExt (segment ℝ a b) := by
  sorry

/-- **Unlabelled** (Ch. II §8.2, P1:2922–2924). By Theorem 8.1, every quasiconformal curve is the image of a circle
under a quasiconformal mapping of the whole plane (cited in §8.4, §8.5 and §8.7). -/
theorem isQuasiconformalCurve_eq_image_circle {C : Set ExtPlane} (hqc : IsQuasiconformalCurve C) :
    ∃ (w : ExtPlane → ExtPlane) (c : ℂ) (r : ℝ), 0 < r ∧ IsQuasiconformalMap w univ ∧
      C = w '' toExt (Metric.sphere c r) := by
  sorry

/-- **Unlabelled** (Ch. II §8.2, P1:2926). A subarc of a quasiconformal curve is quasiconformal (cited in §8.9). -/
theorem isQuasiconformalArc_of_subset_curve {A C : Set ExtPlane} (hC : IsQuasiconformalCurve C)
    (hA : IsJordanArc A) (hAC : A ⊆ C) : IsQuasiconformalArc A := by
  sorry

/-- **Unlabelled** (Ch. II §8.2, P1:2926). A closed Jordan arc is quasiconformal if and only if it is a subarc of a
quasiconformal curve (cited in §8.9). -/
theorem isQuasiconformalArc_iff_subset_curve {A : Set ExtPlane} (hA : IsClosedJordanArc A) :
    IsQuasiconformalArc A ↔ ∃ C : Set ExtPlane, IsQuasiconformalCurve C ∧ A ⊆ C := by
  sorry

/-! ## §8.3 Continuation over a boundary arc -/

/-- **Theorem 8.2** (Ch. II §8.3). Let `G` and `G′` be two domains having `C` and `C′` as either free boundary arcs or
free boundary curves. Further let `w : G → G′` be a quasiconformal mapping under which `C` and `C′` correspond. If `C`
and `C′` are quasiconformal, then `w` can be continued to a quasiconformal mapping of a domain `G₁` containing
`G ∪ C`.
Modelling: `C`, `C′` are both free boundary arcs or both free boundary curves (I.1.9); correspondence as in I.1.8. -/
theorem thm2_8_2 {w : ExtPlane → ExtPlane} {G G' C C' : Set ExtPlane} (hw : IsQuasiconformalMap w G)
    (hwG : w '' G = G')
    (hC : (IsFreeBoundaryArc G C ∧ IsFreeBoundaryArc G' C' ∧ IsQuasiconformalArc C ∧ IsQuasiconformalArc C') ∨
      (IsFreeBoundaryCurve G C ∧ IsFreeBoundaryCurve G' C' ∧ IsQuasiconformalCurve C ∧ IsQuasiconformalCurve C'))
    (hcorr : Corresponds w G G' C C') :
    ∃ (G₁ : Set ExtPlane) (W : ExtPlane → ExtPlane), G ∪ C ⊆ G₁ ∧ IsQCContinuation w G W G₁ := by
  sorry

/-- **Theorem 8.3** (Ch. II §8.3, Springer). Let `G` and `G′` be two `n`-tuply connected domains whose boundary curves
are quasiconformal. Then every quasiconformal mapping `w : G → G′` can be extended to a quasiconformal mapping of the
whole plane.
Modelling: `n ≥ 1`. I.1.7 calls a domain `n`-tuply connected for `n > 1`; `n = 1` is the simply connected case (here a
domain bounded by one quasiconformal curve), as LV apply the theorem in the proof of Theorem 8.5 (§8.6, P1:2960) and
again at P2:161.
"`n`-tuply connected" is written as "the complement has `n` components", as in the theorem on correspondence of
boundaries (I.2.2); every boundary component is a quasiconformal curve. -/
theorem thm2_8_3 {G G' : Set ExtPlane} {n : ℕ} (hn : 1 ≤ n)
    (hG : IsDomainExt G ∧ Nat.card (ConnectedComponents ↥Gᶜ) = n)
    (hG' : IsDomainExt G' ∧ Nat.card (ConnectedComponents ↥G'ᶜ) = n)
    (hC : ∀ x ∈ frontier G, IsQuasiconformalCurve (connectedComponentIn (frontier G) x))
    (hC' : ∀ x ∈ frontier G', IsQuasiconformalCurve (connectedComponentIn (frontier G') x))
    {w : ExtPlane → ExtPlane} (hw : IsQuasiconformalMap w G) (hwG : w '' G = G') :
    ∃ W : ExtPlane → ExtPlane, EqOn W w G ∧ IsQuasiconformalMap W univ := by
  sorry

/-! ## §8.4 Quasiconformal reflection -/

/-- **Definition** (Jordan curve bounding two domains, Ch. II §8.4–8.6). `C` is a Jordan curve bounding the domains
`G₁` and `G₂`: its complement consists of the disjoint domains `G₁` and `G₂`. -/
def JordanCurveBounds (C G₁ G₂ : Set ExtPlane) : Prop :=
  IsJordanCurve C ∧ IsDomainExt G₁ ∧ IsDomainExt G₂ ∧ Disjoint G₁ G₂ ∧ Cᶜ = G₁ ∪ G₂

/-- **Definition** (quasiconformal reflection, Ch. II §8.4, Ahlfors). Let `C` be a Jordan curve bounding the domains
`G₁` and `G₂`. An anti-quasiconformal mapping of `G₁` onto `G₂` which leaves the points of `C` invariant is called a
quasiconformal reflection in `C`.
Modelling: "leaves the points of `C` invariant" is read as: the mapping extends continuously to `G₁ ∪ C` by the
identity on `C`. -/
def IsQuasiconformalReflection (C G₁ G₂ : Set ExtPlane) (Φ : ExtPlane → ExtPlane) : Prop :=
  JordanCurveBounds C G₁ G₂ ∧ IsAntiQuasiconformalMap Φ G₁ ∧ Φ '' G₁ = G₂ ∧ ContinuousOn Φ (G₁ ∪ C) ∧
    ∀ p ∈ C, Φ p = p

/-- **Unlabelled** (Ch. II §8.4, P1:2942–2944). A Jordan curve admits a quasiconformal reflection if and only if it
is quasiconformal (cited in the proof of Theorem 8.4). -/
theorem exists_qcReflection_iff {C G₁ G₂ : Set ExtPlane} (hC : JordanCurveBounds C G₁ G₂) :
    IsQuasiconformalCurve C ↔ ∃ Φ : ExtPlane → ExtPlane, IsQuasiconformalReflection C G₁ G₂ Φ := by
  sorry

/-! ## §8.5 Characterization of quasiconformal curves by module conditions -/

/-- **Definition** (conjugate quadrilaterals, Ch. II §8.5). Let `C` be a Jordan curve bounding the domains `G₁` and
`G₂`, and `z₁, z₂, z₃, z₄` points of `C` which define the positive orientation with respect to `G₁`. The
quadrilaterals `Q₁ = G₁(z₁, z₂, z₃, z₄)` and `Q₂ = G₂(z₄, z₃, z₂, z₁)` are called conjugate with respect to `C`.
Modelling: the positive orders with respect to `G₁` and `G₂` are part of `Quadrilateral`; the vertices of `Q₂` are
those of `Q₁` in reverse order (`Fin.rev`). -/
def AreConjugateQuads (C : Set ExtPlane) (Q₁ Q₂ : Quadrilateral) : Prop :=
  JordanCurveBounds C Q₁.dom Q₂.dom ∧ Q₂.vert = Q₁.vert ∘ Fin.rev

/-- **Theorem 8.4** (Ch. II §8.5; cf. Pfluger, footnote 27). A Jordan curve `C` is quasiconformal if and only if for
all conjugate quadrilaterals `Q₁`, `Q₂` with `M(Q₁) = 1`, the module of `Q₂` has a fixed upper bound.
Modelling: `C` bounds the domains `G₁` and `G₂`, and `Q₁` is formed from `G₁`, as in the definition of §8.5. -/
theorem thm2_8_4 {C G₁ G₂ : Set ExtPlane} (hC : JordanCurveBounds C G₁ G₂) :
    IsQuasiconformalCurve C ↔ ∃ M₀ : ℝ, ∀ Q₁ Q₂ : Quadrilateral, Q₁.dom = G₁ → AreConjugateQuads C Q₁ Q₂ →
      Q₁.module = 1 → Q₂.module ≤ M₀ := by
  sorry

/-! ## §8.6 Characterization of a quasiconformal curve by means of conformal mappings -/

/-- **Theorem 8.5** (Ch. II §8.6, Tienari). Let the Jordan curve `C` bound the domains `G₁` and `G₂`, and let
`f₁ : H₁ → G₁` and `f₂ : H₂ → G₂` be conformal mappings of the upper and lower half-planes with the same value at
infinity. Then `C` is quasiconformal if and only if `f₂⁻¹ ∘ f₁` is quasisymmetric on the real axis.
Modelling: `f₁`, `f₂` are conformal mappings onto `G₁`, `G₂` which are at the same time their extensions to
homeomorphisms of the closed half-planes (I.2.2), so that "the value at infinity" is `fᵢ(∞)`; `f₂⁻¹ ∘ f₁` on the real
axis is the real function `h` with `f₂(h(x)) = f₁(x)` (it exists and is unique under these hypotheses). -/
theorem thm2_8_5 {C G₁ G₂ : Set ExtPlane} (hC : JordanCurveBounds C G₁ G₂) {f₁ f₂ : ExtPlane → ExtPlane}
    (hf₁ : IsConformalMap f₁ (toExt upperHalf) ∧ f₁ '' toExt upperHalf = G₁ ∧
      IsHomeoOn f₁ (closure (toExt upperHalf)) (closure G₁))
    (hf₂ : IsConformalMap f₂ (toExt lowerHalf) ∧ f₂ '' toExt lowerHalf = G₂ ∧
      IsHomeoOn f₂ (closure (toExt lowerHalf)) (closure G₂))
    (hinf : f₁ extInf = f₂ extInf) {h : ℝ → ℝ}
    (hh : ∀ x : ℝ, f₂ ((h x : ℂ) : ExtPlane) = f₁ ((x : ℂ) : ExtPlane)) :
    IsQuasiconformalCurve C ↔ IsQuasisymmetricOn h univ := by
  sorry

/-! ## §8.7 Metric characterization of quasiconformal curves -/

/-- **Theorem 8.6** (Ch. II §8.7; cf. Ahlfors). A Jordan curve is quasiconformal if and only if it is of bounded
turning (the proof gives the bound `h = 2e^{πK}`). -/
theorem thm2_8_6 {C : Set ExtPlane} (hC : IsJordanCurve C) :
    IsQuasiconformalCurve C ↔ ∃ M : ℝ, LiZhongQC.IsBoundedTurning C M := by
  sorry

/-! ## §8.8 Turning in the spherical metric -/

/-- **Unlabelled** (Ch. II §8.8, P1:3034–3036). A Jordan curve `C` is of bounded turning if and only if, for all
(finite or infinite) points `z₁ ≠ z₂` of `C`, the quotient of the smaller of the spherical diameters of the two arcs
into which `z₁`, `z₂` divide `C` and the spherical distance `k(z₁, z₂)` is bounded (used in §8.9, (8.6) for curves).
Modelling: the arcs are the components of `C \ {z₁, z₂}` (open arcs; their closures have the same diameter); "the
smaller diameter is at most `h k(z₁, z₂)`" is "one of the arcs has diameter at most `h k(z₁, z₂)`". -/
theorem boundedTurning_iff_spherical {C : Set ExtPlane} (hC : IsJordanCurve C) :
    (∃ M : ℝ, LiZhongQC.IsBoundedTurning C M) ↔
      ∃ h : ℝ, ∀ z₁ ∈ C, ∀ z₂ ∈ C, z₁ ≠ z₂ → ∃ p ∈ C \ {z₁, z₂},
        sphericalDiam (connectedComponentIn (C \ {z₁, z₂}) p) ≤ h * sphericalDist z₁ z₂ := by
  sorry

/-- **Definition** (Jordan arc of bounded turning, Ch. II §8.8). The Jordan arc `C` is of bounded turning if the ratio
of the spherical diameter of its subarc `z₁z₂` to the spherical distance between `z₁` and `z₂` is bounded for all
pairs `z₁, z₂ ∈ C`.
Modelling: the subarc between `γ(s₁)` and `γ(s₂)` is `γ([s₁, s₂])` for a parametric representation `γ` of `C` over a
real interval `I` (I.1.3); the subarc does not depend on the parametrization. -/
def IsBoundedTurningArc (C : Set ExtPlane) : Prop :=
  ∃ (I : Set ℝ) (γ : ℝ → ExtPlane), I.OrdConnected ∧ I.Nontrivial ∧ IsEmbedding (I.domRestrict γ) ∧ γ '' I = C ∧
    ∃ h : ℝ, ∀ s₁ ∈ I, ∀ s₂ ∈ I, sphericalDiam (γ '' uIcc s₁ s₂) ≤ h * sphericalDist (γ s₁) (γ s₂)

/-- **Formula (8.5)** (Ch. II §8.8). A bounded Jordan arc `C` is of bounded turning if and only if there exists a
finite number `h` such that `|z₁ - z₂| ≤ h |z₁ - z₃|` (8.5) for all points `z₁, z₂, z₃` lying in this order on `C`
(cited in §8.10).
Modelling: `C = γ(I)` for an embedding `γ` of a real interval `I` into the finite plane with bounded image; the points
`γ(s₁), γ(s₂), γ(s₃)` lie in this order on `C` when `s₂` lies between `s₁` and `s₃`. -/
theorem eq2_8_5 {I : Set ℝ} {γ : ℝ → ℂ} (hI : I.OrdConnected) (hIn : I.Nontrivial)
    (hγ : IsEmbedding (I.domRestrict γ)) (hb : Bornology.IsBounded (γ '' I)) :
    IsBoundedTurningArc (toExt (γ '' I)) ↔
      ∃ h : ℝ, ∀ s₁ ∈ I, ∀ s₂ ∈ I, ∀ s₃ ∈ I, s₂ ∈ uIcc s₁ s₃ → ‖γ s₁ - γ s₂‖ ≤ h * ‖γ s₁ - γ s₃‖ := by
  sorry

/-! ## §8.9 Local characterization of a quasiconformal curve -/

/-- **Unlabelled** (Ch. II §8.8, P1:3058–3060; cited P1:3074 "as we have just seen"). Every closed subarc of a
quasiconformal curve is of bounded turning. -/
theorem isBoundedTurningArc_of_subset_curve {C A : Set ExtPlane} (hC : IsQuasiconformalCurve C)
    (hA : IsClosedJordanArc A) (hAC : A ⊆ C) : IsBoundedTurningArc A := by
  sorry

/-- **Unlabelled** (Ch. II §8.9, P1:3062–3064). A closed quasiconformal arc is of bounded turning (with Rickman's
theorem, this characterizes the closed quasiconformal arcs). -/
theorem isBoundedTurningArc_of_isQuasiconformalArc {C : Set ExtPlane} (hC : IsClosedJordanArc C)
    (hqc : IsQuasiconformalArc C) : IsBoundedTurningArc C := by
  sorry

/-- **Rickman's theorem** (Ch. II §8.9, quoted from Rickman, without proof). A closed Jordan arc of bounded turning is
quasiconformal. -/
theorem rickman_theorem {C : Set ExtPlane} (hC : IsClosedJordanArc C) (hbt : IsBoundedTurningArc C) :
    IsQuasiconformalArc C := by
  sorry

/-- **Theorem 8.7** (Ch. II §8.9). A Jordan curve `C` is quasiconformal if and only if every point of `C` belongs to
an open subarc of `C` of bounded turning. -/
theorem thm2_8_7 {C : Set ExtPlane} (hC : IsJordanCurve C) :
    IsQuasiconformalCurve C ↔ ∀ z ∈ C, ∃ A ⊆ C, z ∈ A ∧ IsOpenJordanArc A ∧ IsBoundedTurningArc A := by
  sorry

end LehtoVirtanen1973
