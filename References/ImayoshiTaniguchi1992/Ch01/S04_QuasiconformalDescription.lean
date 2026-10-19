import LiZhongQC.Ch06.S23_QCOnSurfaces
import LiZhongQC.Ch07.S27_TeichmullerExistence

/-!
# Imayoshi–Taniguchi, Chapter 1 §1.4–§1.5: Quasiconformal description of `T(R)`; conformal structures

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 1 §1.4–§1.5 (`full.md` IT1:514–763,
folder `An Introduction to Teichmuller Spaces … ef13744b`).

Conventions: as in `Ch01/S03`; the Beltrami coefficient `μ_f` of a quasiconformal homeomorphism `f : R → S` in the chart at `x`
is `LiZhongQC.complexDilatation (LiZhongQC.localMapExpr f x)` (independent of the chart on `S`, IT (1.4)), the action of
`ω ∈ Diff₊(R)` on `μ_f` is `ω^*(μ_f) = μ_{f ∘ ω⁻¹}` (IT (1.9), second expression); equalities of Beltrami coefficients are
almost everywhere on the common domain of the local expressions. **Reading:** the smooth diffeomorphism groups `Diff₊(R)`,
`Diff₀(R)` of IT are the groups of quasiconformal homeomorphisms of `R` (the groups the Teichmüller theory of this project uses).

* Proposition 1.5 (composition formula (1.8) of Beltrami coefficients, IT1:593) — exists:
  `LiZhongQC.eq6_8_complexDilatation_comp` (the pointwise plane formula, applied in charts)
* Proposition 1.5, last assertion (`f₂ ∘ f₁⁻¹` is biholomorphic iff `μ_{f₁} = μ_{f₂}`, IT1:621) — `prop1_5`
* Theorem 1.6 (there is a biholomorphic `h : S → S'` iff `μ_g = ω^*(μ_f)` for some `ω`; the homotopy assertion, IT1:627) —
  `thm1_6`
* Corollary to Theorem 1.6 (`T(R) ≅ B(R)₁ / Diff₀(R)`, `M_g ≅ B(R)₁ / Diff₊(R)`, IT1:639) — deferred: needs the space `B(R)₁`
  of Beltrami coefficients of `R` as a topological space with the action of `Diff₀(R)`, `Diff₊(R)` (smooth structure on `R`
  and group of diffeomorphisms), which is not installed; the project's Beltrami model is `LiZhongQC.teichGamma_equiv_teichSpace`
  (`T(Γ)` as `M(Γ)` modulo equal boundary values), which is a different quotient
* Theorem 1.7 (a diffeomorphism is conformal for metrics iff biholomorphic for the induced complex structures, IT1:695) —
  deferred: needs a smooth/Riemannian layer (diffeomorphisms, metrics, isothermal coordinates) that is not installed
* Theorem 1.8 (`T(R) ≅ ℳ(R)/Diff₀(R)`, `M_g ≅ ℳ(R)/Diff₊(R)` through Riemannian metrics, IT1:748) — deferred: as Theorem 1.7
-/

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

noncomputable section

namespace ImayoshiTaniguchi1992

open LiZhongQC (IsQCRS IsBiholomorphic complexDilatation localMapExpr localMapDomain)

variable {R S S' : Type} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R] [IsManifold 𝓘(ℂ) ω R]
  [CompactSpace R] [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
  [CompactSpace S] [TopologicalSpace S'] [T2Space S'] [ConnectedSpace S'] [ChartedSpace ℂ S'] [IsManifold 𝓘(ℂ) ω S']
  [CompactSpace S']

/-- **Proposition 1.5, last assertion** (Ch. 1 §1.4.2). For orientation-preserving (quasiconformal) homeomorphisms
`f_j : R → S_j` (`j = 1, 2`), the map `f₂ ∘ f₁⁻¹ : S₁ → S₂` is biholomorphic if and only if `μ_{f₁} = μ_{f₂}`. -/
theorem prop1_5 (f₁ : R ≃ₜ S) (f₂ : R ≃ₜ S') (h₁ : IsQCRS f₁) (h₂ : IsQCRS f₂) :
    IsBiholomorphic (f₁.symm.trans f₂ : S ≃ₜ S') ↔
      ∀ x : R, ∀ᵐ z ∂(volume.restrict (localMapDomain f₁ x ∩ localMapDomain f₂ x)),
        complexDilatation (localMapExpr f₁ x) z = complexDilatation (localMapExpr f₂ x) z := by
  sorry

/-- **Theorem 1.6** (Ch. 1 §1.4.3). For orientation-preserving (quasiconformal) homeomorphisms `f : R → S` and `g : R → S'`,
there exists a biholomorphic map `h : S → S'` if and only if `μ_g = ω^*(μ_f) = μ_{f ∘ ω⁻¹}` for some orientation-preserving
(quasiconformal) homeomorphism `ω` of `R`. (The second assertion of the book, that `g⁻¹ ∘ h ∘ f` is homotopic to the identity
iff `ω ∈ Diff₀(R)`, for `ω = g⁻¹ ∘ h ∘ f`, restates the definition and is omitted.) -/
theorem thm1_6 (f : R ≃ₜ S) (g : R ≃ₜ S') (hf : IsQCRS f) (hg : IsQCRS g) :
    (∃ h : S ≃ₜ S', IsBiholomorphic h) ↔
      ∃ w : R ≃ₜ R, IsQCRS w ∧ ∀ x : R,
        ∀ᵐ z ∂(volume.restrict (localMapDomain g x ∩ localMapDomain (w.symm.trans f : R ≃ₜ S) x)),
          complexDilatation (localMapExpr g x) z = complexDilatation (localMapExpr (w.symm.trans f : R ≃ₜ S) x) z := by
  sorry

end ImayoshiTaniguchi1992
