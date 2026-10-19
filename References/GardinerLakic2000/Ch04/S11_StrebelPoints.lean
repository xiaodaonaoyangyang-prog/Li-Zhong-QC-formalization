import References.GardinerLakic2000.Ch04.S10_TeichmullerContraction

/-!
# Gardiner–Lakic 2000, Ch. 4 §4.11 Strebel points

Source `teichmuller.txt`, lines 4489–4581.

* Theorem 11 (Strebel point ⇔ Reich–Strebel functional ⇔ no degenerating Hamilton sequence, l. 4492; cited
  l. 10805) — `thm4_11`
* Definition (`H*(μ)`, the boundary dilatation `H(μ)`, l. 4501–4506; used in Exercises 3–4 and Ch. 15) —
  `boundaryDilatationStarK`, `boundaryDilatationH` (K₀(μ) is Part A's minimal dilatation)
* Unlabelled (§4.11, l. 4509, 4572; used in the proof of Theorem 12: `τ` is a Strebel point iff `H(τ) < K₀(τ)`) —
  `para4_11_strebel_iff`
* Theorem 12 (the Strebel points are open and dense in `T(R)`, l. 4571) — `thm4_12`

Not items (DESIGN §3): `H(f ∘ g) ≤ H(f)H(g)` (l. 4515) and the continuity of `H` and `K₀` on `T(R)` (l. 4572), used
in proofs only.

Near miss (dupcheck): `LiZhongQC.boundaryDilatation`, the boundary dilatation of a boundary correspondence of the
disc (via annulus extensions); `boundaryDilatationH` is the book's `H` of a Teichmüller class on any `R`.

**Conventions.** Open and dense are for Part A's `teichDist` (B0.3). `K_z(f^μ) = (1 + |μ|)/(1 − |μ|)`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsFuchsian IsUniformization quadDiffNorm)

variable {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
  [IsManifold 𝓘(ℂ) ω R]

/-- **[CORRECTION]** (AUDIT4 G7) `0 < ‖μ‖∞` is added: for `μ = 0` on a surface with `dim A(R) < ∞` (i) and (ii) fail (`k₀ = 0`) and (iii) holds.
**Theorem 11** (§4.11, l. 4492). For an extremal Beltrami coefficient `μ` the following are equivalent:
(i) `μ` represents a Strebel point; (ii) `μ` represents a Reich–Strebel functional; (iii) `μ` has no degenerating
Hamilton sequence. -/
theorem thm4_11 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (μ : beltramiBall R) (hμ : IsExtremalRS p μ) (hμ0 : 0 < beltramiNormRS μ.1) :
    List.TFAE [IsStrebelPoint p (Quot.mk (teichRel p) μ), IsReichStrebelFunctional (fun φ => pairingRS φ μ.1),
      ¬ ∃ φ : ℕ → R → ℂ → ℂ, IsDegHamiltonSeq μ.1 φ] := by
  sorry

/-- **Definition** (§4.11, l. 4503). `H*(μ) = inf_E sup_{z ∈ R − E} K_z(f^μ)` over the compact sets `E ⊆ R`
(essential supremum). -/
def boundaryDilatationStarK (μ : R → ℂ → ℂ) : ℝ≥0∞ :=
  ⨅ (E : Set R) (_ : IsCompact E), ⨆ x : R,
    essSup (fun z => ENNReal.ofReal ((1 + ‖μ x z‖) / (1 - ‖μ x z‖)))
      (volume.restrict ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Eᶜ))

/-- **Definition** (the boundary dilatation, §4.11, l. 4504). `H(μ) = inf H*(ν)` over the `ν` in the Teichmüller
class of `μ`; it depends only on the class. -/
def boundaryDilatationH (p : UpperHalfPlane → R) (P : TeichSpace R p) : ℝ≥0∞ :=
  ⨅ (ν : beltramiBall R) (_ : Quot.mk (teichRel p) ν = P), boundaryDilatationStarK ν.1

/-- **[CORRECTION]** (AUDIT4 G7) `0 < k₀` (`extremalK p P`) is added: at the base point of a compact `R` the left side is false (`ess sup < 0`)
while `H = 0 < K₀ = 1`.
**Unlabelled** (§4.11, l. 4509, 4572). A point `τ ∈ T(R)` is a Strebel point if and only if `H(τ) < K₀(τ)`. -/
theorem para4_11_strebel_iff {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) (P : TeichSpace R p) (hP0 : 0 < extremalK p P) :
    IsStrebelPoint p P ↔ boundaryDilatationH p P < minimalDilatation p P := by
  sorry

/-- **[CORRECTION]** (AUDIT4 G7) `A(R) ≠ 0` is added: for `T(R)` a point (type `(0, 3, 0)`) its only point is the base point, which is not a
frame-mapping class, so "dense" fails.
**Theorem 12** (§4.11, l. 4571). The set of Strebel points is open and dense in `T(R)`. -/
theorem thm4_12 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (hA : ∃ φ ∈ integrableHolQDSet R, quadDiffNorm φ = 1) :
    (∀ P : TeichSpace R p, IsStrebelPoint p P → ∃ δ > 0, ∀ Q, teichDist p P Q < δ → IsStrebelPoint p Q) ∧
      ∀ (P : TeichSpace R p) (ε : ℝ), 0 < ε → ∃ Q, IsStrebelPoint p Q ∧ teichDist p P Q < ε := by
  sorry

end GardinerLakic2000
