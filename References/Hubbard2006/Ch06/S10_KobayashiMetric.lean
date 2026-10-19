import References.Common.HyperbolicSurface
import References.Hubbard2006.Ch01.S08_FirstClassification
import References.Hubbard2006.Ch05.S02_HolomorphicMotions
import References.GardinerLakic2000.Ch07.S02_TeichmullerKobayashi

/-!
# Hubbard 2006, Chapter 6 §6.10: The Kobayashi metric (new items)

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H2` lines 3368–3485.

**Conventions.** A tangent vector `ξ ∈ T_x X` of a Riemann surface is a complex number in the preferred chart
(`TangentSpace 𝓘(ℂ) x = ℂ`). The unit disc is `LiZhongQC.unitDiscOpens`, with the base point `0`
(`Hubbard2006.discOrigin`). The hyperbolic norm is `References.hypNormSurf` (`ρ_ℍ = |dz| / Im z`, curvature `−1`, so
that `ρ_𝔻(0) = 2`), which is why the Kobayashi ball is defined with the factor `1/2`.

* Def. 6.10.1 (the Kobayashi ball `K_x(X) = { ½ γ'(0) | γ : 𝔻 → X holomorphic, γ(0) = x }` of a Riemann surface; it is
  bounded for all `x` iff the surface is Kobayashi-hyperbolic) — `kobayashiBall`, `IsKobayashiHyperbolicRS`
* Prop. 6.10.2 (1) (holomorphic maps send Kobayashi balls into Kobayashi balls) — `prop6_10_2_a`
* Prop. 6.10.2 (2) (holomorphic coverings map Kobayashi balls onto Kobayashi balls) — `prop6_10_2_b`
* Cor. 6.10.3 (a Riemann surface is Kobayashi-hyperbolic iff it is hyperbolic, and then the Kobayashi ball is the unit
  ball of the hyperbolic metric) — `cor6_10_3_a`, `cor6_10_3_b`
* Prop. 6.10.4 (the Kobayashi ball of the unit ball of a Banach space at the origin is `½ B`) — `prop6_10_4`
* Prop. 6.10.5 (Slodkowski's theorem restated: every holomorphic disc in `𝒯_X` lifts to a holomorphic disc in `ℳ(X)`) —
  `prop6_10_5`
* Thm 6.10.6 (the infinitesimal Kobayashi metric of `𝒯_X` is the dual of the `L¹` norm, i.e. the infinitesimal
  Teichmüller metric) — deferred: needs the tangent spaces of `𝒯_X` (Banach-analytic structure) and the differential of
  the Bers chart; the installed global statement is the equality of the Kobayashi and Teichmüller distances
* Cor. 6.10.7 (analytic maps of Teichmüller spaces contract the Teichmüller metric), Cor. 6.10.8 (the Kobayashi ball of
  the universal curve) — deferred: need the Banach-analytic structure of `𝒯_S` and `Ξ_S`
-/

open Set
open scoped Manifold ContDiff

namespace Hubbard2006

open LiZhongQC

/-- **The Kobayashi ball** `K_x(X)` of a Riemann surface `X` at `x` (Definition 6.10.1, H2:3380): the set of vectors
`½ γ'(0) ∈ T_x X = ℂ` for `γ : 𝔻 → X` holomorphic with `γ(0) = x`. -/
def kobayashiBall (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] (x : X) : Set ℂ :=
  {v | ∃ γ : unitDiscOpens → X, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) γ ∧ γ discOrigin = x ∧
    v = (1 / 2 : ℂ) * (show ℂ from mfderiv 𝓘(ℂ) 𝓘(ℂ) γ discOrigin (1 : ℂ))}

/-- **Kobayashi-hyperbolic** (Definition 6.10.1): the infinitesimal Kobayashi semi-norms are norms, i.e. the Kobayashi
balls are bounded (the velocity vectors of maps `𝔻 → X` taking `0` to `x` are bounded). -/
def IsKobayashiHyperbolicRS (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∀ x : X, Bornology.IsBounded (kobayashiBall X x)

/-- **Proposition 6.10.2 (1)** (Contraction for the Kobayashi metric, H2:3390). If `f : X → Y` is holomorphic then
`[Df(x)](K_x) ⊂ K_{f(x)}`. -/
theorem prop6_10_2_a {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (x : X) :
    (fun v : ℂ => show ℂ from mfderiv 𝓘(ℂ) 𝓘(ℂ) f x v) '' kobayashiBall X x ⊆ kobayashiBall Y (f x) := by
  sorry

/-- **Proposition 6.10.2 (2)** (H2:3390). If `f : X → Y` is a holomorphic covering map then
`[Df(x)](K_x) = K_{f(x)}`. -/
theorem prop6_10_2_b {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hcov : IsCoveringMap f) (x : X) :
    (fun v : ℂ => show ℂ from mfderiv 𝓘(ℂ) 𝓘(ℂ) f x v) '' kobayashiBall X x = kobayashiBall Y (f x) := by
  sorry

/-- **Corollary 6.10.3, first part** (H2:3398). A Riemann surface is Kobayashi-hyperbolic if and only if it is
hyperbolic. -/
theorem cor6_10_3_a {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : IsKobayashiHyperbolicRS X ↔ IsHyperbolicRS X := by
  sorry

/-- **Corollary 6.10.3, second part** (H2:3398). If `X = ℍ/Γ` is hyperbolic, uniformized by `p`, the Kobayashi ball at
`p(z)` is the closed unit ball for the hyperbolic norm `References.hypNormSurf`. -/
theorem cor6_10_3_b {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (z : UpperHalfPlane) :
    kobayashiBall X (p z) = {v | References.hypNormSurf p z v ≤ 1} := by
  sorry

/-- **Proposition 6.10.4 (Kobayashi metrics of balls in Banach spaces)** (H2:3405). Let `B` be the unit ball of a
complex Banach space `E`. The Kobayashi ball of `B` at the origin, `{½ γ'(0) | γ : 𝔻 → B holomorphic, γ(0) = 0}`, is
`½ B`. *Correction:* the ball is the closed ball of radius `1/2` (the maps `t ↦ t ξ`, `‖ξ‖ = 1`, attain the
boundary). -/
theorem prop6_10_4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] :
    {v : E | ∃ γ : ℂ → E, DifferentiableOn ℂ γ unitDisc ∧ γ 0 = 0 ∧ (∀ t ∈ unitDisc, ‖γ t‖ < 1) ∧
      v = (1 / 2 : ℂ) • deriv γ 0} = Metric.closedBall 0 (1 / 2) := by
  sorry

/-- **Proposition 6.10.5 (Slodkowski's theorem restated)** (H2:3412). Every holomorphic map `γ : 𝔻 → 𝒯_X` lifts to a
holomorphic map `γ̃ : 𝔻 → ℳ(X)` with `Φ_X ∘ γ̃ = γ`. Holomorphic discs of `𝒯_X` and of `ℳ(X)` are the installed
`GardinerLakic2000.holDiscsT` and `holDiscsM` (the Bers image is holomorphic, resp. the integrals against `L¹`
functions). -/
theorem prop6_10_5 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {γ : ℂ → TeichGamma Γ} (hγ : γ ∈ GardinerLakic2000.holDiscsT Γ) :
    ∃ g ∈ GardinerLakic2000.holDiscsM Γ, ∀ t ∈ unitDisc, Quotient.mk (teichSetoidGamma Γ) (g t) = γ t := by
  sorry

end Hubbard2006
