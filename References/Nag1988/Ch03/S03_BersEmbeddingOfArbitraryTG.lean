import References.Nag1988.Ch03.S02_ComplexStructuresOnTargetSpaces

/-!
# Nag, Chapter 3 §3.3: The Bers embedding of an arbitrary `T(G)`

Source: S. Nag, *The Complex Analytic Theory of Teichmüller Spaces*, Wiley 1988, Ch. 3 §3.3 (`full.md` N2:67–484; folder
`c10f6cd1`, cited `N2:<line>`). Only Proposition 3.3.2 is new here.

**Model** (N-D1, Chapter 5): the complex structure of `T(G)` is the one for which the Bers embedding is biholomorphic onto the open
domain `T_β(G) = bersImage Γ` of `B₂(L, G)`; `Φ_β` is `bersFunctionGamma`, `β = bersMapGamma`.

* Lemma 3.3.1 (`μ ∼ ν` iff `w^μ = w^ν` on `ℝ` iff on `𝕃`; N2:98) — exists: `LiZhongQC.lemma33_1`
* Proposition 3.3.2 (for `G` torsion free of finite type `(g, n)` the Bers complex structure coincides with the structure of
  Section 3.2; N2:105) — `prop3_3_2` (the unique complex structure of `thm3_2_3` makes `β ∘ F⁻¹` biholomorphic)
* Lemmas A, B, C (Schwarzian chain rule, vanishing iff Möbius; N2:181–243) — exists: `Lehto1987.eq2_1_2_b`,
  `LiZhongQC.eq19_1_chain_rule`
* Sections 3.3.4–3.3.5 (`Φ_β(μ) ∈ B₂(L, G)`, injectivity of `β`; N2:243) — exists: `LiZhongQC.eq33_11`,
  `LiZhongQC.bersMapGamma_injective`
* Theorem 3.3.6 (Kraus–Nehari: `‖Sw‖ ≤ 3/2` for schlicht `w` on `L`; N2:289) — exists: `LiZhongQC.thm19_2_nehari`
* Area theorem (Gronwall–Bieberbach, quoted in the proof of 3.3.6) — exists: `Pommerenke1992.area_theorem`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff MatrixGroups

noncomputable section

namespace Nag1988

open LiZhongQC (TeichGamma BeltramiGamma IsFuchsian lowerHalf bersMapGamma bersFunctionGamma)
open GardinerLakic2000 (cuspNorm cuspFormsL)

/-- **Proposition 3.3.2** (§3.3.2; N2:105). In the setting of `thm3_2_3` (finite type `(g, n)`, Fricke system `G`, Fricke map
`Ft` of `L^∞(U, Γ)₁`; `𝒜` the complex structure of `thm3_2_3`, i.e. an `IsFrickeHolAtlas`), the Bers embedding is a biholomorphic map of `Im F` (with the complex structure of `thm3_2_3`) onto an open
domain of `B₂(L, Γ)`: for every chart `c` of such an atlas the map `c ∘ F ∘ β⁻¹` (defined on the Bers image of the points of the
chart) is well defined, a biholomorphism of the Bers image of the chart domain onto the chart target, in the Banach sense
(`IsBBiholOn` for the Nehari norm on `B₂(L, Γ)`). -/
theorem prop3_3_2 {Γ : Subgroup SL2R} {g n : ℕ} (hΓ : IsFuchsian Γ) (hT : IsOfType3 Γ g n 0)
    (hχ : 0 < 2 * (g : ℤ) - 2 + n) (h0 : g = 0 → 3 < n) (G : FrickeGenerators Γ g n 0)
    (Ft : (ℂ → ℂ) → FrickeSpace g n 0) (hFt : ∀ μ : BeltramiGamma Γ, IsFrickeCoords G μ (Ft μ.1.1))
    {𝒜 : Set (OpenPartialHomeomorph (FrickeSpace g n 0) (EuclideanSpace ℂ (Fin (3 * g + n - 3))))}
    (h𝒜 : IsFrickeHolAtlas G Ft 𝒜)
    (c : OpenPartialHomeomorph (FrickeSpace g n 0) (EuclideanSpace ℂ (Fin (3 * g + n - 3)))) (hc : c ∈ 𝒜) :
    ∃ H : (ℂ → ℂ) → EuclideanSpace ℂ (Fin (3 * g + n - 3)),
      (∀ μ : BeltramiGamma Γ, Ft μ.1.1 ∈ c.source → H (bersFunctionGamma μ) = c (Ft μ.1.1)) ∧
        IsBBiholOn (cuspNorm lowerHalf) (fun v : EuclideanSpace ℂ (Fin (3 * g + n - 3)) => ENNReal.ofReal ‖v‖)
          {φ | ∃ μ : BeltramiGamma Γ, Ft μ.1.1 ∈ c.source ∧ bersFunctionGamma μ = φ} c.target H := by
  sorry

end Nag1988
