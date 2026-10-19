import References.Pommerenke1992.Ch04.S06_HyperbolicMetric
import LiZhongQC.Ch01.S10_AnalyticDefinition
import LiZhongQC.Ch04.S18_BoundedTurning

/-!
# Pommerenke 1992, Ch. 5 §5.1 An Overview

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 5 *Quasidisks*, §5.1; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 3948–4006.

* Definition (quasicircle, quasidisk, §5.1; defined again as (5.4.1), cited 3×) — `IsQuasicircle`, `IsQuasidisk`
* Quasicircle Theorem (named, §5.1) — `quasicircle_theorem`
* Definition (quasisymmetric map of `𝕋` into `ℂ`, Ahlfors' form (5.1.1); cited at l. 4630) — `IsQuasisymmetricA`
* Definition (quasiconformal, `κ`-quasiconformal map of `ℂ` onto `ℂ`, (5.1.2), (5.1.3); cited at l. 5296) —
  `IsKappaQC`, `IsQCPlane`

Not items (DESIGN §3): the introduction of John and linearly connected domains (defined in §5.2, §5.3) and "a
quasidisk is a linearly connected John domain" (Theorem 5.9); the plan of the proof; the mention of the
Bojarski–Ahlfors–Bers embedding (stated in §5.6, `embedding_theorem`); the remarks on `ℝⁿ` and on the universal
Teichmüller space.

**Conventions.** The book's quasicircles are the geometric ones (Ahlfors' condition), which is the project's bounded
turning (`LiZhongQC.IsBoundedTurning`, reused under the book's name); the project's proved `LiZhongQC.thm18_1` is the
implication (a) ⟺ (d) of the Quasicircle Theorem, in its Möbius-normalized form. The quasisymmetric maps are defined
here by (5.1.1) and in §5.4 by Väisälä's (5.4.4); they are new definitions (the leader's decision Q4). A
quasiconformal map of `ℂ` onto `ℂ` is the book's analytic definition (5.1.2), (5.1.3), built on the project's
`LiZhongQC.IsGenHomeoSolution` (a homeomorphism with locally `L²` generalized derivatives solving the Beltrami
equation) and `LiZhongQC.IsBeltramiCoeff` (`|μ| ≤ κ` a.e.) (Q3). The conformal map `f` of `𝔻` onto the inner domain
of a Jordan curve has the continuous extension `F` to `𝔻̄` (Theorem 2.6).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsConformalOnto IsJordanCurve)

/-- **Definition** (§5.1 and (5.4.1)). The Jordan curve `J ⊆ ℂ` is a quasicircle: `diam J(a, b) ≤ M|a - b|` for
`a, b ∈ J`, where `J(a, b)` is the arc (of smaller diameter) of `J` between `a` and `b`.
Modelling: this is the project's bounded turning (`LiZhongQC.IsBoundedTurning`, §18.1), reused under the book's name:
for `a ≠ b` the two arcs of `J` between `a` and `b` are the closures of the two components of `J ∖ {a, b}` (same
diameters), and the arc of smaller diameter satisfies the bound if and only if one of them does; `M ≥ 1` is no
restriction. For Jordan curves of `ℂ`, the project's proved `LiZhongQC.thm18_1` says that this is equivalent to
`LiZhongQC.IsQuasicircle (toExt J)`, the image of a circle under a quasiconformal map (condition (d) of the
Quasicircle Theorem, Möbius-normalized). -/
def IsQuasicircle (J : Set ℂ) : Prop :=
  ∃ M : ℝ, LiZhongQC.IsBoundedTurning (toExt J) M

/-- **Definition** (§5.1 and (5.4.1)). A quasidisk: the inner domain of a quasicircle. -/
def IsQuasidisk (G : Set ℂ) : Prop :=
  ∃ J : Set ℂ, IsQuasicircle J ∧ G = innerDomain J

/-- **Definition (5.1.1)** (§5.1; Ahlfors; cited at l. 4630). A quasisymmetric map of `𝕋` into `ℂ` (Ahlfors' form): a
homeomorphism `h` of `𝕋` into `ℂ` such that, for `z₁, z₂, z₃ ∈ 𝕋`, `|z₁ - z₂| = |z₂ - z₃|` implies
`|h(z₁) - h(z₂)| ≤ M |h(z₂) - h(z₃)|`.
Modelling: continuous and injective on the compact `𝕋`, hence a homeomorphism onto its image. -/
def IsQuasisymmetricA (h : ℂ → ℂ) : Prop :=
  ContinuousOn h (sphere 0 1) ∧ InjOn h (sphere 0 1) ∧ ∃ M : ℝ, ∀ z₁ ∈ sphere (0 : ℂ) 1, ∀ z₂ ∈ sphere (0 : ℂ) 1,
    ∀ z₃ ∈ sphere (0 : ℂ) 1, ‖z₁ - z₂‖ = ‖z₂ - z₃‖ → ‖h z₁ - h z₂‖ ≤ M * ‖h z₂ - h z₃‖

/-- **Definition (5.1.2), (5.1.3)** (§5.1; cited at l. 5296). `h` is a `κ`-quasiconformal map of `ℂ` onto `ℂ`: a
homeomorphism of `ℂ` onto `ℂ` that is absolutely continuous on lines with locally square-integrable partial derivatives
satisfying the Beltrami equation `∂h/∂z̄ = μ(z) ∂h/∂z` almost everywhere, with a measurable `μ`, `|μ(z)| ≤ κ < 1`.
Modelling: `LiZhongQC.IsGenHomeoSolution h μ univ 2` (the `L²` generalized homeomorphic solutions, which are exactly the
ACL maps with locally square-integrable partials) with `LiZhongQC.IsBeltramiCoeff μ univ κ`, and `h(ℂ) = ℂ`. -/
def IsKappaQC (h : ℂ → ℂ) (κ : ℝ) : Prop :=
  0 ≤ κ ∧ κ < 1 ∧ h '' univ = univ ∧
    ∃ μ : ℂ → ℂ, LiZhongQC.IsBeltramiCoeff μ univ κ ∧ LiZhongQC.IsGenHomeoSolution h μ univ 2

/-- **Definition** (§5.1). `h` is a quasiconformal map of `ℂ` onto `ℂ`: `κ`-quasiconformal for some `κ < 1`. -/
def IsQCPlane (h : ℂ → ℂ) : Prop :=
  ∃ κ : ℝ, IsKappaQC h κ

/-- **Quasicircle Theorem** (§5.1, named; proved in §5.4–§5.6). Let `J` be a Jordan curve in `ℂ` and let `f` map `𝔻`
conformally onto the inner domain of `J`. Then the following conditions are equivalent: (a) `J` is a quasicircle;
(b) `f` is quasisymmetric on `𝕋`; (c) `f` has a quasiconformal extension to `ℂ`; (d) there is a quasiconformal map
of `ℂ` onto `ℂ` that maps `𝕋` onto `J`.
Modelling: (b) uses the definition (5.1.1) given in §5.1, for the boundary values `F` of `f`; the maps in (c), (d) are
those of (5.1.2), (5.1.3). Condition (a) is the project's bounded turning (`IsQuasicircle`), and (a) ⟺ (d) is, in its
Möbius-normalized form with geometric `K`-quasiconformal maps (`LiZhongQC.IsQuasicircle (toExt J)`), the project's
proved `LiZhongQC.thm18_1`. -/
theorem quasicircle_theorem {J : Set ℂ} (hJ : IsJordanCurve (toExt J)) {f F : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc (innerDomain J)) (hFc : ContinuousOn F (closedBall 0 1))
    (hFf : EqOn F f unitDisc) :
    List.TFAE [IsQuasicircle J, IsQuasisymmetricA F,
      ∃ h : ℂ → ℂ, IsQCPlane h ∧ EqOn h f unitDisc,
      ∃ h : ℂ → ℂ, IsQCPlane h ∧ h '' sphere 0 1 = J] := by
  sorry

end Pommerenke1992
