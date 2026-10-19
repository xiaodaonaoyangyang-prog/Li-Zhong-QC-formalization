import LiZhongQC.Ch03.S14_PoincareMetric

/-!
# Katok 1992, Ch. 1 §1.1 The hyperbolic metric

S. Katok, *Fuchsian Groups* (1992), Chapter 1 *Hyperbolic Geometry*, §1.1; source `full.md` of
`Fuchsian groups (Katok, Svetlana) …-3766f6b7…`, lines 93–175.

* Definition (the upper half-plane ℍ, l. 95) — exists: `UpperHalfPlane` `LiZhongQC.upperHalf` (Mathlib's type ℍ is
  the subtype of the project set upperHalf)
* Formula (1.1.1) (the hyperbolic metric ds = |dz|/y, l. 98) — exists: `LiZhongQC.poincareDensity`
  `LiZhongQC.poincareDensity_upperHalf` (the density of the upper half-plane is 1/Im z)
* Definition (hyperbolic length h of a path, l. 104) — exists: `LiZhongQC.LRCurve.rhoLength` `LiZhongQC.IsPathIn`
  (the length with density 1/Im z of a Lipschitz path in the upper half-plane; the infimum over Lipschitz paths equals
  the infimum over piecewise differentiable paths)
* Definition (hyperbolic distance ρ as the infimum of h, l. 110) — exists: `UpperHalfPlane.dist_eq`
  `LiZhongQC.poincareDist_upperHalf` `LiZhongQC.poincareDensity_upperHalf` (Mathlib's dist on ℍ, identified with the
  infimum of the lengths for the density 1/Im z by the project bridge)
* Unlabelled (§1.1, l. 118: ρ is a distance; cited at l. 829) — exists: `UpperHalfPlane.instMetricSpace`
  `dist_triangle`
* Definition (SL(2,ℝ) and the trace, l. 126) — exists: `Matrix.SpecialLinearGroup` `Matrix.trace`
* Formula (1.1.2) (the Möbius transformations and PSL(2,ℝ) ≈ SL(2,ℝ)/{±1}, l. 128–132) — exists:
  `Matrix.ProjectiveSpecialLinearGroup` `Matrix.ProjectiveSpecialLinearGroup.toPGL_injective`
  `UpperHalfPlane.instMulActionProjGenLinGroupFinOfNatNatReal` `UpperHalfPlane.SLAction` `UpperHalfPlane.neg_smul`
  (PSL(2,ℝ) is Mathlib's quotient of SL(2,ℝ) by its center; it maps injectively to PGL(2,ℝ), which acts on ℍ; g and
  −g act in the same way)
* Definition (the action of PSL(2,ℝ) on ℍ by the transformations (1.1.2), l. 128–132) — `pslAction`
* Definition (tr²(T) and Tr(T) = |tr g|, l. 132–136; cited at l. 707) — `Tr`, `trSq`
* Theorem 1.1.1 (PSL(2,ℝ) acts on ℍ by homeomorphisms; cited at l. 707) — exists: `UpperHalfPlane.SLAction`
  `UpperHalfPlane.instContinuousSMulSL2R` `Homeomorph.smul` (a lift g acts as T; the jointly continuous group action
  gives the homeomorphism Homeomorph.smul g)
* Formula (1.1.3) (Im(Tz) = Im z/|cz + d|²; cited at l. 368, 813, 919) — exists:
  `UpperHalfPlane.im_smul_eq_div_normSq` (stated for GL(2,ℝ) with the factor |det g|, which is 1 on SL(2,ℝ))
* Definition (isometry of ℍ, l. 156) — exists: `IsometryEquiv` (a distance-preserving map of ℍ onto itself)
* Unlabelled (§1.1, l. 158: Isom(ℍ) is a group) — exists: `IsometryEquiv.instGroup`
* Theorem 1.1.2 (PSL(2,ℝ) ⊂ Isom(ℍ); cited at l. 186, 202, 244, 280, 829) — exists:
  `UpperHalfPlane.instIsIsometricSMulSpecialLinearGroupFinOfNatNatReal` (every lift g acts isometrically, and onto by
  the group action)
* Definition (geodesic = shortest curve, l. 101; geodesic segment and complete geodesic) — `IsGeodesicSegment`,
  `IsGeodesic`

Not items (DESIGN §3): the identity `Id` (the unit `1` of PSL(2,ℝ)); the remark that PSL(2,ℝ) contains the maps with
`ad − bc > 0`, `z ↦ az + b` and `z ↦ −1/z` (l. 136; immediate, used inside proofs); (1.1.4) (a step of the proof of
Theorem 1.1.2; cited only in a hint); the preview of geodesics and parallels with Fig. 1 (l. 101; stated later as
Theorem 1.2.1, Corollary 1.2.2); the exercises.

**Conventions.** ℍ is Mathlib's `UpperHalfPlane`, ρ is its `dist` (`ds = |dz|/Im z`, curvature `−1`, Katok's
normalization). The disc model (§1.2) uses the project's `LiZhongQC.poincareDensityDisc` `2/(1 − |z|²)`, also curvature
`−1`; Pommerenke's `hypDistD` and Gehring's `hypDensity` (curvature `−4`) are NOT used, since the stated constants of
the chapter (Theorem 1.2.6, Gauss–Bonnet, the trigonometric rules) depend on the normalization. PSL(2,ℝ) is Mathlib's
`Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℝ` with its quotient topology; it acts on ℍ by the scoped instance
`pslAction` (through `toPGL` and Mathlib's PGL(2,ℝ) action; no proof obligation). Isom(ℍ) is `ℍ ≃ᵢ ℍ`. The
exercises are not items; where a statement needs an exercise's content, the content is written into it.
-/

open Complex Set Metric Filter Topology
open scoped UpperHalfPlane MatrixGroups ComplexConjugate

noncomputable section

namespace Katok1992

/-- **Definition** (§1.1; l. 128–132). The group `PSL(2,ℝ)` of the transformations (1.1.2)
`z ↦ (az + b)/(cz + d)`, `ad − bc = 1`, acting on ℍ.
Modelling: `MulAction.compHom` of Mathlib's `PGL(2,ℝ)` action along the injective `toPGL`; `T = ±g` acts as
`g • z`. -/
scoped instance pslAction : MulAction PSL(2, ℝ) ℍ :=
  MulAction.compHom ℍ Matrix.ProjectiveSpecialLinearGroup.toPGL

/-- **Definition** (§1.1; l. 132–136; cited at l. 707). `Tr(T) = |tr(g)|` for `T ∈ PSL(2,ℝ)` represented by `±g`.
Modelling: `|tr|` of the representative `Quotient.out T`; the value does not depend on the lift since
`tr(−g) = −tr(g)` and the center of `SL(2,ℝ)` is `{±1}`. -/
def Tr (T : PSL(2, ℝ)) : ℝ :=
  |Matrix.trace ((Quotient.out T : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)|

/-- **Definition** (§1.1; l. 135). `tr²(T) = tr²(g)` for `T ∈ PSL(2,ℝ)` represented by `±g`. -/
def trSq (T : PSL(2, ℝ)) : ℝ := Tr T ^ 2

/-- **Definition** (§1.1; l. 101). A geodesic segment `S` from `z` to `w`: a shortest curve for ρ, parametrized by
arc length.
Modelling: `S` is the image of an isometric map of `[0, ρ(z, w)]` sending `0` to `z` and `ρ(z, w)` to `w`. -/
def IsGeodesicSegment (S : Set ℍ) (z w : ℍ) : Prop :=
  ∃ γ : ℝ → ℍ, γ 0 = z ∧ γ (dist z w) = w ∧
    (∀ s ∈ Icc (0 : ℝ) (dist z w), ∀ t ∈ Icc (0 : ℝ) (dist z w), dist (γ s) (γ t) = |s - t|) ∧
    S = γ '' Icc 0 (dist z w)

/-- **Definition** (§1.1; l. 101). A (complete) geodesic of ℍ.
Modelling: the image of an isometric map `ℝ → ℍ`. -/
def IsGeodesic (L : Set ℍ) : Prop :=
  ∃ γ : ℝ → ℍ, Isometry γ ∧ L = range γ

end Katok1992
