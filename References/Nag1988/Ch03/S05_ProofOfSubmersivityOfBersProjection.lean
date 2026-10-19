import References.Nag1988.Ch03.S03_BersEmbeddingOfArbitraryTG
import References.GardinerLakic2000.Ch14.S05_BersLOperators

/-!
# Nag, Chapter 3 §3.5: The proof of the submersivity of `Φ_β` (Bers' main theorem)

Source: S. Nag, *The Complex Analytic Theory of Teichmüller Spaces*, Wiley 1988, Ch. 3 §3.5 (`full.md` N2:1063–1532; folder
`c10f6cd1`, cited `N2:<line>`). New: the operator `ℒ_C`, its boundedness and injectivity for Jordan curves, its surjectivity for
quasicircles, and Bers' main theorem; the proof steps (the reproducing formula, the integral estimates, 3.5.4–3.5.5) are not items.

**Model.** The configuration of a curve `C` through `∞` and its two complementary regions `D₁ = Ω`, `D₂ = Ω*` of the plane is as in
Gardiner–Lakic Chapter 14 (`GardinerLakic2000.IsQCConfiguration`; here the Jordan version `IsJordanConfiguration` for 3.5.2). The
Poincaré density is `GardinerLakic2000.poincareDensityGL` (curvature `−4`, Nag's `λ`), `B₂(D)` is `GardinerLakic2000.boundedCuspFormsC ⊥ D`
(for the trivial group), `B₂(D, Γ)` is `boundedCuspFormsC Γ D`. The operator `ℒ_C` of (5.2)' is `bersLC D₁`: it equals
`−(π/6)` times the Bers operator `bersLOmega` of Gardiner–Lakic (14.23) applied to the Bers Beltrami differential
`λ_{D₁}^{-2} ψ̄`. A curve not through `∞` is reduced to this case by a Möbius map (the book does the same in 3.5.3); this reduction is
an omitted generality of 3.5.2.

* Lemma (the antilinear isometry `B ψ = λ^{-2} ψ̄` of `B₂(D₁, Γ)` into `L^∞(D₁, Γ)`; N2:1121) — omitted: trivial verification
  (the case of a quasi-Fuchsian group is lemma14_5 of Gardiner–Lakic)
* Exercise (`d₀Φ^μ = −(6/π) ℒ β₂^*`; N2:1115) — omitted: exercise
* Bers' main theorem (`ℒ : B₂(U^μ, G^μ) → B₂(L^μ, G^μ)` is an antilinear Banach space isomorphism; N2:1086, 1106) — `thm3_5_1`
* Proposition 3.5.2 (`ℒ_C` is bounded antilinear injective with `‖ℒ_C‖ ≤ 16π` for any Jordan curve; N2:1139) — `prop3_5_2`
* Proposition 3.5.3 (`ℒ_C` is surjective for a quasicircle; N2:1175) — `prop3_5_3`
* Sections 3.5.4–3.5.5 (generalized reproducing formula; automorphy implies the general case; N2:1250–1480) — omitted: proof steps
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff MatrixGroups

noncomputable section

namespace Nag1988

open LiZhongQC (ExtPlane IsQuasiFuchsian IsJordanCurve extInf)
open GardinerLakic2000 (bersLOmega poincareDensityGL boundedCuspFormsC cuspNorm IsQCConfiguration)

/-- **The operator `ℒ_C`** (5.2)': `(ℒ_C ψ)(z) = ∬_{D₁} conj ψ(ζ) λ_{D₁}(ζ)^{-2} (ζ - z)^{-4} dξ dη`, for `z ∈ D₂`. -/
def bersLC (D₁ : Set ℂ) (ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(π / 6 : ℂ) * bersLOmega D₁ (fun ζ => (poincareDensityGL D₁ ζ ^ (-2 : ℤ) : ℝ) * conj (ψ ζ)) z

/-- A **Jordan configuration**: a Jordan curve `C` through `∞` separating the extended plane into the plane domains
`D₁`, `D₂` (as `GardinerLakic2000.IsQCConfiguration` with a Jordan curve in place of a quasicircle). -/
def IsJordanConfiguration (C : Set ExtPlane) (D₁ D₂ : Set ℂ) : Prop :=
  IsJordanCurve C ∧ extInf ∈ C ∧ IsOpen D₁ ∧ IsOpen D₂ ∧ IsConnected D₁ ∧ IsConnected D₂ ∧ Disjoint D₁ D₂ ∧
    LiZhongQC.toExt D₁ ∪ LiZhongQC.toExt D₂ = Cᶜ

/-- **Proposition 3.5.2** (N2:1139). For the complementary regions `D₁`, `D₂` of any Jordan curve `C` through `∞`, `ℒ_C` maps
`B₂(D₁)` into `B₂(D₂)`, is antilinear, bounded with `‖ℒ_C ψ‖_{B₂(D₂)} ≤ 16π ‖ψ‖_{B₂(D₁)}`, and injective. -/
theorem prop3_5_2 {C : Set ExtPlane} {D₁ D₂ : Set ℂ} (hC : IsJordanConfiguration C D₁ D₂) :
    (∀ ψ ∈ boundedCuspFormsC ⊥ D₁, DifferentiableOn ℂ (bersLC D₁ ψ) D₂ ∧
      cuspNorm D₂ (bersLC D₁ ψ) ≤ ENNReal.ofReal (16 * π) * cuspNorm D₁ ψ) ∧
    (∀ (a : ℂ) (ψ ψ' : ℂ → ℂ), ψ ∈ boundedCuspFormsC ⊥ D₁ → ψ' ∈ boundedCuspFormsC ⊥ D₁ →
      ∀ z ∈ D₂, bersLC D₁ (a • ψ + ψ') z = conj a * bersLC D₁ ψ z + bersLC D₁ ψ' z) ∧
    ∀ ψ ∈ boundedCuspFormsC ⊥ D₁, (∀ z ∈ D₂, bersLC D₁ ψ z = 0) → ∀ z ∈ D₁, ψ z = 0 := by
  sorry

/-- **Proposition 3.5.3** (N2:1175). If `C` is a quasicircle through `∞` with complementary regions `D₁`, `D₂`, then `ℒ_C` maps
`B₂(D₁)` onto `B₂(D₂)`. -/
theorem prop3_5_3 {C : Set ExtPlane} {D₁ D₂ : Set ℂ} (hC : IsQCConfiguration C D₁ D₂) :
    ∀ φ ∈ boundedCuspFormsC ⊥ D₂, ∃ ψ ∈ boundedCuspFormsC ⊥ D₁, ∀ z ∈ D₂, bersLC D₁ ψ z = φ z := by
  sorry

/-- **Bers' main theorem** (§3.5.1; N2:1106). For a quasi-Fuchsian group `Γ` of the quasicircle `C` with complementary regions
`D₁ = U^μ`, `D₂ = L^μ` (a `Γ`-invariant configuration), `ℒ` is an antilinear Banach space isomorphism of `B₂(D₁, Γ)` onto
`B₂(D₂, Γ)`: it is bijective (with `ℒ ψ` automorphic; `ψ` is determined on `D₁` only, as `ℒ` integrates over `D₁`) and the inverse is bounded. -/
theorem thm3_5_1 {C : Set ExtPlane} {D₁ D₂ : Set ℂ} {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)}
    (hC : IsQCConfiguration C D₁ D₂) (hΓ : IsQuasiFuchsian Γ C) :
    (∀ ψ ∈ boundedCuspFormsC Γ D₁, D₂.indicator (bersLC D₁ ψ) ∈ boundedCuspFormsC Γ D₂) ∧
      (∀ φ ∈ boundedCuspFormsC Γ D₂, ∃ ψ ∈ boundedCuspFormsC Γ D₁, (∀ z ∈ D₂, bersLC D₁ ψ z = φ z) ∧
        ∀ ψ' ∈ boundedCuspFormsC Γ D₁, (∀ z ∈ D₂, bersLC D₁ ψ' z = φ z) → ∀ z ∈ D₁, ψ' z = ψ z) ∧
      ∃ M : ℝ, ∀ ψ ∈ boundedCuspFormsC Γ D₁, cuspNorm D₁ ψ ≤ ENNReal.ofReal M * cuspNorm D₂ (bersLC D₁ ψ) := by
  sorry

end Nag1988
