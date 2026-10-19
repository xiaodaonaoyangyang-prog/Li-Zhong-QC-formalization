import References.GardinerLakic2000.Ch02.S02_Uniformization

/-!
# Gardiner–Lakic 2000, Ch. 2 §2.3 Extremal length

Source `teichmuller.txt`, lines 1188–1305 (Chapter 2, §2.3).

* Formula (2.1) (extremal length `Λ(F) = sup_ρ L(ρ)²/A(ρ)`, l. 1189–1207; used in §2.4 and Ch. 4, 12) — exists:
  `LiZhongQC.extremalLength` (plane reading, leader ruling A0.3: curve families in a plane domain, Borel densities
  of finite positive area; local square integrability is implied by finite area)
* Proposition 1 (l. 1272) — `prop2_1`
* Formula (2.2) (the composition law for two adjacent quadrilaterals, l. 1295–1304) — `eq2_2`

Not items: the two Examples (rectangle and annulus, l. 1213–1266; their content is
`LiZhongQC.thm4_1_modulus_eq_inv_extremalLength` and `LiZhongQC.extremalLength_annulusSeparating`); the Remarks
(l. 1268, 1270); the geometric-definition consequence (l. 1291, U−); the comparison principle (l. 1293, U−, it is
`LiZhongQC.thm3_2_comparison`). Modelling: a Riemann surface `R` is read as a plane domain (A0.3); the curve family
`F′ = f(F)` is `LiZhongQC.IsCurveImage`. For (2.2) the adjacency "the right side of `Q₁` coincides with the left side of
`Q₂`, `Q = Q₁ ∪ Q₂`" is written with `LiZhongQC.TopQuad.side` (side 0 and side 2 are the sides joined by
`joiningCurves 0`); near miss `LiZhongQC.thm3_3_composition_ii` (needs that every curve of `F` contains curves of
`F₁` and `F₂`, which is the content of the book's argument, not an unfolding).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (IsKQC LRCurve IsCurveImage extremalLength TopQuad toExt)

/-- **Proposition 1** (§2.3, l. 1272; plane reading). If `f` is `K`-quasiconformal on the domain `Ω` and takes the
curve family `F` in `Ω` onto the curve family `F′`, then `K⁻¹ Λ(F) ≤ Λ(F′) ≤ K Λ(F)`. -/
theorem prop2_1 {f : ℂ → ℂ} {Ω : Set ℂ} {K : ℝ} (hf : IsKQC f Ω K) (hc : IsConnected Ω) {F F' : Set LRCurve}
    (hF : ∀ γ ∈ F, γ.trace ⊆ Ω) (himg : IsCurveImage f F F') :
    (ENNReal.ofReal K)⁻¹ * extremalLength F ≤ extremalLength F' ∧
      extremalLength F' ≤ ENNReal.ofReal K * extremalLength F := by
  sorry

/-- **Formula (2.2)** (§2.3, l. 1295–1304). Let `Q₁`, `Q₂` be disjoint quadrilaterals such that the right side of `Q₁`
coincides with the left side of `Q₂`, and let `Q` be their union (with the common side), with left side that of `Q₁`
and right side that of `Q₂`. If `F`, `F₁`, `F₂` are the families of arcs joining the left and right sides, then
`Λ(F) ≥ Λ(F₁) + Λ(F₂)`. -/
theorem eq2_2 (Q Q₁ Q₂ : TopQuad) (hdisj : Disjoint Q₁.dom Q₂.dom) (hcommon : Q₁.side 2 = Q₂.side 0)
    (hleft : Q.side 0 = Q₁.side 0) (hright : Q.side 2 = Q₂.side 2)
    (hunion : toExt Q.dom = toExt Q₁.dom ∪ toExt Q₂.dom ∪ (Q₁.side 2 \ {Q₁.vert 2, Q₁.vert 3})) :
    extremalLength (Q₁.joiningCurves 0) + extremalLength (Q₂.joiningCurves 0) ≤
      extremalLength (Q.joiningCurves 0) := by
  sorry

end GardinerLakic2000
