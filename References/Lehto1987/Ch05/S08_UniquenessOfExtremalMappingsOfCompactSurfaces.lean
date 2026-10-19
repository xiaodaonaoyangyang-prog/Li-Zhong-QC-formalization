import References.Lehto1987.Ch05.S07_ExtremalMappingsOfRiemannSurfaces

/-!
# Lehto, Chapter V §8: Uniqueness of extremal mappings of compact surfaces

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. V §8 (`full.md`
P2:1464–1736).

Conventions (see §1). Compact surfaces of genus `p > 1` (`LiZhongQC.HasGenus S p`, `1 < p`). Quadratic differentials
are the project's (`LiZhongQC.IsHolQuadDiff`, `LiZhongQC.holQuadDiffSubmodule`). The complex dilatation `k φ̄/|φ|` is
`LiZhongQC.teichmullerBeltrami k φ`. The project's Li Zhong §26–§27 carries most of this section:
- a Teichmüller mapping with its initial and terminal differentials is `LiZhongQC.IsTeichmullerMap`;
- the stretching function and the Jacobian are `LiZhongQC.lambdaStretch` and `LiZhongQC.jacobianQD`;
- the `φ`-area of `S` is `LiZhongQC.quadDiffNorm φ`.

* Definition (Teichmüller mapping of a Riemann surface, (8.1), §8.1) — `IsTeichmullerMapRS` (near miss:
  LiZhongQC.IsTeichmullerMap, which also names the terminal differential)
* Formula (8.1) (§8.1) — `IsDeterminedBy`
* Definition (the pair `(φ, k)` determines `f`, §8.1) — `IsDeterminedBy`
* Unlabelled (§8.1, P2:1482): `k` is determined and `φ` is unique up to a positive factor — `para5_8_1`
* Unlabelled (§8.1, P2:1484): the maximal dilatation is `(1 + k)/(1 − k)` — omitted: U−
* Theorem 8.1 (§8.2) — `thm5_8_1`
* Formula (8.2) (§8.2) — `thm5_8_1` (through LiZhongQC.IsTeichmullerMap)
* Formula (8.3) (§8.2) — omitted: a step of the proof of Theorem 8.1
* Formula (8.4) (§8.2) — omitted: (8.2) in real coordinates
* Definition (initial and terminal differential, §8.2) — exists: `LiZhongQC.IsTeichmullerMap` (its fields initial
  and terminal)
* Definition (the stretching function `λ_f`, (8.5), §8.3) — exists: `LiZhongQC.lambdaStretch`
* Formula (8.5) (§8.3) — exists: `LiZhongQC.lambdaStretch`
* Formula (8.6) (§8.3) — exists: `LiZhongQC.eq26_9` (for f : S → S and ψ = φ, the case used in Lemma 8.1)
* Definition (the Jacobian `J_f`, §8.3) — exists: `LiZhongQC.jacobianQD`
* Unlabelled (§8.3, P2:1561): `∫_S J_f |φ| = |S′|` — exists: `LiZhongQC.eq26_14` (its second conjunct)
* Lemma 8.1 (§8.4) — exists: `LiZhongQC.lemma26_2`
* Formula (8.7) (§8.4) — omitted: a step of the proof of Lemma 8.1
* Formula (8.8) (§8.4) — omitted: a step of the proof of Lemma 8.1
* Formula (8.9) (§8.4) — omitted: a step of the proof of Lemma 8.1
* Theorem 8.2 (§8.5, Teichmüller's uniqueness theorem) — exists: `LiZhongQC.thm27_2_existence`,
  `LiZhongQC.thm26_2_uniqueness` (jointly: a Teichmüller map in each class, uniquely extremal, and every Teichmüller
  map is uniquely extremal in its class)
* Formula (8.10) (§8.5) — exists: `LiZhongQC.thm26_2_uniqueness` (its first conjunct)
* Formula (8.11) (§8.5) — omitted: a step of the proof of Theorem 8.2
* Formula (8.12) (§8.5) — omitted: a step of the proof of Theorem 8.2
* Formula (8.13) (§8.5) — exists: `LiZhongQC.eq26_13`
* Formula (8.14) (§8.5) — omitted: a step of the proof of Theorem 8.2
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate ContDiff Manifold

noncomputable section

namespace Lehto1987

universe u

open LiZhongQC (IsQCRS IsBiholomorphic HasGenus IsHolQuadDiff IsTeichmullerMap teichmullerBeltrami)
open GardinerLakic2000 (HasBeltramiCoeff)

/-! ## §8.1 Teichmüller mappings and quadratic differentials -/

/-- **Definition** (the pair `(φ, k)` determines `f`, (8.1), Ch. V §8.1): `f` is quasiconformal with complex
dilatation `k φ̄/|φ|`, `0 < k < 1`, `φ` a holomorphic quadratic differential of `S`, not identically zero. -/
def IsDeterminedBy {S S' : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [TopologicalSpace S']
    [ChartedSpace ℂ S'] (f : S ≃ₜ S') (φ : S → ℂ → ℂ) (k : ℝ) : Prop :=
  IsQCRS f ∧ IsHolQuadDiff φ ∧ φ ≠ 0 ∧ 0 < k ∧ k < 1 ∧ HasBeltramiCoeff f (teichmullerBeltrami k φ)

/-- **Definition** (Teichmüller mapping of a Riemann surface, Ch. V §7.7 and §8.1): a quasiconformal mapping which is
conformal or whose complex dilatation is of the form `k φ̄/|φ|` (8.1). -/
def IsTeichmullerMapRS {S S' : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [TopologicalSpace S']
    [ChartedSpace ℂ S'] (f : S ≃ₜ S') : Prop :=
  IsBiholomorphic f ∨ ∃ (φ : S → ℂ → ℂ) (k : ℝ), IsDeterminedBy f φ k

/-- **Unlabelled** (Ch. V §8.1, P2:1482). If the Teichmüller mapping `f` is determined by `(φ, k)` and by
`(φ₁, k₁)`, then `k₁ = k`, and `φ₁/φ` is a positive constant. -/
theorem para5_8_1 {S S' : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] [TopologicalSpace S'] [T2Space S'] [ConnectedSpace S']
    [ChartedSpace ℂ S'] [IsManifold 𝓘(ℂ) ω S'] {f : S ≃ₜ S'} {φ φ₁ : S → ℂ → ℂ} {k k₁ : ℝ}
    (h : IsDeterminedBy f φ k) (h₁ : IsDeterminedBy f φ₁ k₁) : k₁ = k ∧ ∃ c : ℝ, 0 < c ∧ φ₁ = (c : ℂ) • φ := by
  sorry

/-! ## §8.2 Local representation of Teichmüller mappings -/

/-- **Theorem 8.1** (Ch. V §8.2, Teichmüller). Let `f : S → S′` be a Teichmüller mapping determined by `(φ, k)`.
Then there exists a unique holomorphic quadratic differential `ψ` on `S′` with: 1° a zero of `φ` of order `n ≥ 0` at
`p` gives a zero of `ψ` of the same order at `f(p)`; 2° near a regular point `p` of `φ`, in natural parameters `ζ` of
`φ` and `ζ′` of `ψ`, `ζ′ ∘ f = (ζ + kζ̄)/(1 − k)` (8.2).
Modelling: 1° and 2° are the conditions of `LiZhongQC.IsTeichmullerMap f φ ψ k`. -/
theorem thm5_8_1 {S S' : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] [TopologicalSpace S'] [T2Space S'] [ConnectedSpace S']
    [ChartedSpace ℂ S'] [IsManifold 𝓘(ℂ) ω S'] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) {f : S ≃ₜ S'}
    {φ : S → ℂ → ℂ} {k : ℝ} (hf : IsDeterminedBy f φ k) :
    ∃ ψ : S' → ℂ → ℂ, IsTeichmullerMap f φ ψ k ∧ ∀ ψ' : S' → ℂ → ℂ, IsTeichmullerMap f φ ψ' k → ψ' = ψ := by
  sorry

end Lehto1987
