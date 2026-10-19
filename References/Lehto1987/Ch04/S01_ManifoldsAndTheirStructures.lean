import References.Lehto1987.Ch03.S05_InnerRadiusOfUnivalence
import References.GardinerLakic2000.Ch02.S09_FundamentalDomains

/-!
# Lehto, Chapter IV §1: Manifolds and their structures

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. IV §1 (`full.md`
P1:4738–4917).

Conventions of Chapter IV (INVENTORY Part B, decisions B0.4, B0.7, B0.9, B0.12):
- Lehto's manifolds are Hausdorff with a countable base. A *surface* is a type `S` with
  `[TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S] [ChartedSpace ℂ S]` (charts to
  `ℂ = ℝ²`, no smoothness). A *Riemann surface* adds `[IsManifold 𝓘(ℂ) ω S]` (the shared convention
  `References.IsRiemannSurface`, with second countability). Analytic maps are `MDifferentiable 𝓘(ℂ) 𝓘(ℂ)`.
- Differentials are the project's local-coefficient families (`LiZhongQC.IsDiffFamily m n`): `q x` is the coefficient
  in the preferred chart at `x`.
- A conformal structure on a type with a topology is given as an explicit `c : ChartedSpace ℂ X`; two structures are
  the same when they have the same holomorphic functions on every open set (as in `GardinerLakic2000.thm2_2_c`).

* Definition (real manifold, local parameter, atlas, parameter transformation, differentiable, `C^k` and
  real-analytic structures, differentiable maps, paths, §1.1) — exists: `ChartedSpace`, `IsManifold`, `ContMDiff`,
  `Path` (Mathlib; with `T2Space` and `SecondCountableTopology` for Lehto's countable base)
* Definition (measurable map on a `C¹` manifold, §1.1) — `IsChartMeasurable`
* Unlabelled (§1.1, P1:4770): Borel measurable maps — omitted: not cited
* Definition (surface, §1.1) — exists: `ChartedSpace` (charts to ℂ, with `T2Space`, `SecondCountableTopology` and
  `ConnectedSpace`)
* Unlabelled (§1.1, P1:4772): a surface is pathwise connected — omitted: standard (U−)
* Definition (complex manifold, complex analytic structure, §1.2) — exists: `IsManifold` (over ℂⁿ)
* Definition (Riemann surface, §1.2) — exists: `References.IsRiemannSurface` (with second countability, decision
  B0.4)
* Definition (analytic, holomorphic, meromorphic maps, §1.2) — exists: `MDifferentiable`
* Definition (conformal mapping of a Riemann surface, §1.2) — `IsConformalMapRS`
* Unlabelled (§1.2, P1:4792): local parameters are conformal mappings — omitted: immediate (U−)
* Definition (bordered surface, §1.3) — `IsBorderedSurface`
* Definition (border of a bordered surface, §1.3) — `border`
* Unlabelled (§1.3, P1:4798–4800): interior points are well defined, `S` is a surface dense in `S*`, `B` is a closed
  one-dimensional manifold — omitted: U−, not cited
* Definition (bordered Riemann surface, §1.3) — `IsBorderedRS`
* Formula (1.1) (§1.4) — omitted: the chain rule
* Definition (`(m, n)`-differential, holomorphic differential, §1.4) — exists: `LiZhongQC.IsDiffFamily`,
  `LiZhongQC.diffFamilySubmodule` (holomorphic: holomorphic coefficients, as in `LiZhongQC.holQuadDiffSubmodule`)
* Formula (1.2) (§1.4) — exists: `LiZhongQC.IsDiffFamily` (the transformation law of its definition)
* Definition (meromorphic differential, §1.4) — `IsMeroDiff`
* Definition (quadratic differential, Abelian differential, §1.4) — exists: `LiZhongQC.IsHolQuadDiff`,
  `LiZhongQC.IsMeroQuadDiff` (m = 2, n = 0; an Abelian differential is a holomorphic or meromorphic (1, 0)-family)
* Definition (Beltrami differential, §1.4) — exists: `LiZhongQC.IsBeltramiDifferential` (with a bound k < 1)
* Unlabelled (§1.4, P1:4808–4834): equality, linear structure, products of differentials, `(1, 1)`-differentials as
  area elements — omitted: U−, not cited
* Formula (1.3) (§1.5) — omitted: the line element of a surface in ℝ³, a step of §1.5
* Formula (1.4) (§1.5) — omitted: a step of §1.5
* Formula (1.5) (§1.5) — omitted: a step of §1.5
* Definition (isothermal coordinates, §1.5) — `IsIsothermalChart`
* Unlabelled (§1.5, P1:4882–4888): isothermal coordinates define a conformal structure on an orientable `C¹`
  surface — `para4_1_5`
* Theorem 1.1 (§1.6) — `thm4_1_1`

Helpers (not book notions): `IsSurfaceParam` (a local parametrization of a surface in ℝ³) and `IsOrientedAtlas3` (an
oriented atlas of such parametrizations).
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate ContDiff Manifold

noncomputable section

namespace Lehto1987

/-! ## §1.1 Real manifolds -/

/-- **Definition** (measurable map on a manifold, Ch. IV §1.1). `f : M → N` is (Lebesgue) measurable on `M` if for
every local parameter `h` of `M` with domain `U` and every open `G ⊂ N`, the set `h(U ∩ f⁻¹(G))` is Lebesgue
measurable.
Modelling: the local parameters are the charts of the atlas (Lebesgue measurability is invariant under the `C¹`
parameter transformations); Lebesgue measurable is `NullMeasurableSet` for `volume` on `ℂ = ℝ²`. -/
def IsChartMeasurable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [TopologicalSpace N] (f : M → N) :
    Prop :=
  ∀ e ∈ atlas ℂ M, ∀ G : Set N, IsOpen G → NullMeasurableSet (e '' (e.source ∩ f ⁻¹' G)) volume

/-! ## §1.2 Complex analytic manifolds -/

/-- **Definition** (conformal mapping of a Riemann surface, Ch. IV §1.2): an injective analytic map. (Not
`LehtoVirtanen1973.IsConformalMap`, which is for domains of `ℂ̄`.) -/
def IsConformalMapRS {S W : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [TopologicalSpace W]
    [ChartedSpace ℂ W] (f : S → W) : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ Function.Injective f

/-! ## §1.3 Border of a surface -/

/-- **Definition** (bordered surface, Ch. IV §1.3): a connected Hausdorff space with a countable base which is covered
by open sets homeomorphic to open subsets of the closed half-plane `H̄ = {y ≥ 0}`.
Modelling: `H̄` is the subtype `{z : ℂ // 0 ≤ z.im}`; the local parameters are partial homeomorphisms with open source
and open target in `H̄`. -/
def IsBorderedSurface (X : Type*) [TopologicalSpace X] : Prop :=
  T2Space X ∧ SecondCountableTopology X ∧ ConnectedSpace X ∧
    ∀ p : X, ∃ e : OpenPartialHomeomorph X {z : ℂ // 0 ≤ z.im}, p ∈ e.source

/-- **Definition** (border, Ch. IV §1.3): the points of a bordered surface mapped onto the boundary `ℝ` of `H̄` by a
local parameter (then by all local parameters, P1:4798). -/
def border (X : Type*) [TopologicalSpace X] : Set X :=
  {p | ∃ e : OpenPartialHomeomorph X {z : ℂ // 0 ≤ z.im}, p ∈ e.source ∧ (e p : ℂ).im = 0}

/-- **Definition** (bordered Riemann surface, Ch. IV §1.3): a bordered surface `S* = S ∪ B` with a conformal structure
on `S` determined by an atlas `A` on `S*`.
Modelling: `A` covers `S*` and its parameter transformations, read as functions of the finite plane, are holomorphic
at the interior points (`Im > 0`) of their domains. -/
def IsBorderedRS (X : Type*) [TopologicalSpace X] (A : Set (OpenPartialHomeomorph X {z : ℂ // 0 ≤ z.im})) :
    Prop :=
  IsBorderedSurface X ∧ (∀ p : X, ∃ e ∈ A, p ∈ e.source) ∧
    ∀ e ∈ A, ∀ e' ∈ A, DifferentiableOn ℂ
      (fun z : ℂ => if h : 0 ≤ z.im then ((e' (e.symm ⟨z, h⟩) : {z : ℂ // 0 ≤ z.im}) : ℂ) else 0)
      {z : ℂ | ∃ h : 0 < z.im, (⟨z, h.le⟩ : {z : ℂ // 0 ≤ z.im}) ∈ (e.symm.trans e').source}

/-! ## §1.4 Differentials on Riemann surfaces -/

/-- **Definition** (meromorphic differential, Ch. IV §1.4): an `(m, n)`-differential whose local representations are
meromorphic.
Modelling: `LiZhongQC.IsDiffFamily m n` with meromorphic chart coefficients (near miss: `LiZhongQC.IsMeroQuadDiff`,
the case `(2, 0)`). -/
def IsMeroDiff {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] (m n : ℤ) (q : S → ℂ → ℂ) : Prop :=
  LiZhongQC.IsDiffFamily m n q ∧ ∀ x : S, MeromorphicOn (q x) (chartAt ℂ x).target

/-! ## §1.5 Isothermal coordinates -/

/-- Helper. `f` is a local parametrization of class `C^k` of the set `S ⊂ ℝ³` on the open set `U ⊂ ℂ`: the inverse
of a local parameter of the surface `S`. It is `C^k`, injective, a homeomorphism of `U` onto a relatively open subset
of `S`, and an immersion (`∂f/∂x`, `∂f/∂y` linearly independent). -/
def IsSurfaceParam (k : ℕ∞) (S : Set (EuclideanSpace ℝ (Fin 3))) (f : ℂ → EuclideanSpace ℝ (Fin 3)) (U : Set ℂ) :
    Prop :=
  IsOpen U ∧ ContDiffOn ℝ k f U ∧ InjOn f U ∧ ContinuousOn (Function.invFunOn f U) (f '' U) ∧
    (∃ O : Set (EuclideanSpace ℝ (Fin 3)), IsOpen O ∧ f '' U = O ∩ S) ∧
    ∀ z ∈ U, LinearIndependent ℝ ![fderiv ℝ f z 1, fderiv ℝ f z I]

/-- Helper. `A` is an oriented atlas of `C^k` local parametrizations of `S ⊂ ℝ³`: the parametrizations cover `S`,
and every parameter transformation `g⁻¹ ∘ f` has positive Jacobian (`S` is orientable). -/
def IsOrientedAtlas3 (k : ℕ∞) (S : Set (EuclideanSpace ℝ (Fin 3)))
    (A : Set ((ℂ → EuclideanSpace ℝ (Fin 3)) × Set ℂ)) : Prop :=
  (∀ a ∈ A, IsSurfaceParam k S a.1 a.2) ∧ (∀ x ∈ S, ∃ a ∈ A, x ∈ a.1 '' a.2) ∧
    ∀ a ∈ A, ∀ b ∈ A, ∀ z ∈ a.2 ∩ a.1 ⁻¹' (b.1 '' b.2),
      0 < LinearMap.det (fderiv ℝ (Function.invFunOn b.1 b.2 ∘ a.1) z : ℂ →ₗ[ℝ] ℂ)

/-- **Definition** (isothermal coordinates, Ch. IV §1.5): local coordinates `z` of a surface in ℝ³ in which the line
element is `ds = λ|dz|`, i.e. the Gaussian quantities satisfy `E = G`, `F = 0`.
Modelling: for the parametrization `f` (the inverse of the local parameter) on `U`: `|∂f/∂x| = |∂f/∂y|` and
`⟨∂f/∂x, ∂f/∂y⟩ = 0`. -/
def IsIsothermalChart (f : ℂ → EuclideanSpace ℝ (Fin 3)) (U : Set ℂ) : Prop :=
  ∀ z ∈ U, ‖fderiv ℝ f z 1‖ = ‖fderiv ℝ f z I‖ ∧ inner ℝ (fderiv ℝ f z 1) (fderiv ℝ f z I) = 0

/-- **Unlabelled** (Ch. IV §1.5, P1:4882–4888). Isothermal coordinates define a natural conformal structure for an
orientable `C¹` surface: if `z` and `w` are isothermal coordinates whose parameter transformation `z ↦ w` preserves
the orientation, then it is conformal.
Modelling: `f`, `g` are the parametrizations; the transformation is `g⁻¹ ∘ f` on `U ∩ f⁻¹(g(V))`. -/
theorem para4_1_5 {S : Set (EuclideanSpace ℝ (Fin 3))} {f g : ℂ → EuclideanSpace ℝ (Fin 3)} {U V : Set ℂ}
    (hf : IsSurfaceParam 1 S f U) (hg : IsSurfaceParam 1 S g V) (hfi : IsIsothermalChart f U)
    (hgi : IsIsothermalChart g V)
    (hor : ∀ z ∈ U ∩ f ⁻¹' (g '' V), 0 < LinearMap.det (fderiv ℝ (Function.invFunOn g V ∘ f) z : ℂ →ₗ[ℝ] ℂ)) :
    DifferentiableOn ℂ (Function.invFunOn g V ∘ f) (U ∩ f ⁻¹' (g '' V)) := by
  sorry

/-! ## §1.6 Riemann surfaces and quasiconformal mappings -/

/-- **Theorem 1.1** (Ch. IV §1.6, Gauss). Every orientable `C²`-surface in ℝ³ can be made into a Riemann surface.
Modelling: given an oriented `C²` atlas `A` of `S`, there is an atlas `B` of isothermal coordinates such that `A ∪ B`
is an oriented `C¹` atlas (the new coordinates are orientation-preserving `C¹` changes of the old ones) and every
parameter transformation of `B` is holomorphic: `B` is a conformal structure on `S`. -/
theorem thm4_1_1 {S : Set (EuclideanSpace ℝ (Fin 3))} {A : Set ((ℂ → EuclideanSpace ℝ (Fin 3)) × Set ℂ)}
    (hA : IsOrientedAtlas3 2 S A) :
    ∃ B : Set ((ℂ → EuclideanSpace ℝ (Fin 3)) × Set ℂ), IsOrientedAtlas3 1 S (A ∪ B) ∧
      (∀ x ∈ S, ∃ b ∈ B, x ∈ b.1 '' b.2) ∧ (∀ b ∈ B, IsIsothermalChart b.1 b.2) ∧
      ∀ a ∈ B, ∀ b ∈ B, DifferentiableOn ℂ (Function.invFunOn b.1 b.2 ∘ a.1) (a.2 ∩ a.1 ⁻¹' (b.1 '' b.2)) := by
  sorry

end Lehto1987
