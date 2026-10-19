import References.Common.HyperbolicSurface

/-!
# Hubbard 2006, Chapter 4 §4.8: Beltrami forms and complex structures (new items)

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 4516–4943.

**Conventions.** One-dimensional complex vector spaces are modelled by `ℂ`: an `ℝ`-linear map `u : ℂ → ℂ` is
`u(z) = a z + b z̄` with `a = ∂u` (`linCoeff u`) and `b = ∂̄u` (`antilinCoeff u`); a constant Beltrami form is the
antilinear map `z ↦ β z̄` with `|β| < 1`, identified with the number `β`. The constant Beltrami form of an
orientation preserving `u` is `μ(u) = (u')⁻¹ ∘ u'' = (b / a) z̄` (equation (4.8.9)), written `constBeltrami u = b / a`.
A Beltrami form on a Riemann surface `X` is the family of its local coefficients, `LiZhongQC.IsBeltramiDifferential`
(a `(−1, 1)` differential, measurable, bounded by `k < 1`). The Riemann surface `X_μ` is described by its universal
property: a quasiconformal homeomorphism `g : X → Y` onto a Riemann surface `Y` with Beltrami form `μ`.

* Prop. 4.8.1 (an `ℝ`-linear map is uniquely a `ℂ`-linear plus a `ℂ`-antilinear map) — `prop4_8_1`
* Def. 4.8.6 (constant Beltrami form on a one-dimensional complex vector space: antilinear, norm `< 1`) —
  `IsConstBeltrami`
* Def. 4.8.7 (the constant Beltrami form `μ(u) = (u')⁻¹ ∘ u''` of an orientation preserving isomorphism `u`; it is a
  Beltrami form) — `linCoeff`, `antilinCoeff`, `constBeltrami`, `OrientPres`, `prop4_8_7`
* Prop. and Def. 4.8.10 (pullback `u*` of constant Beltrami forms: existence, uniqueness, the formula (4.8.13), and
  analyticity) — `pullbackFormula`, `prop4_8_10_a`, `prop4_8_10_b`, `prop4_8_10_c`
* Def. 4.8.11 (Beltrami form on a Riemann surface `X`, an element of the unit ball of `L^∞_*(TX, TX)`) — exists:
  `LiZhongQC.IsBeltramiDifferential`
* Prop. and Def. 4.8.12 (the Riemann surface `X_μ` with the structure for which the identity of `X` is a quasiconformal
  map with Beltrami form `μ`; existence and independence) — `prop4_8_12_a`, `prop4_8_12_b`
* Prop. 4.8.13, 4.8.14, Lemma 4.8.15, Prop. 4.8.17, 4.8.19 (the universal curve over `ℳ(X)`, the Bers fibre space
  description, analytic dependence of pullbacks and of inverses) — deferred: need Banach-analytic manifold structures on
  `ℳ(X)` and `ℳ(X) × X`
* Notation 4.8.2, Exercises 4.8.5, 4.8.8, 4.8.9, 4.8.16, Example 4.8.18 — omitted: exercise / notation
-/

open Set Metric MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

namespace Hubbard2006

open LiZhongQC

/-- **Proposition 4.8.1** (Linear and antilinear maps, H1:4552). If `E`, `F` are complex vector spaces, every `ℝ`-linear
map `u : E → F` can be written uniquely `u = u' + u''` with `u'` `ℂ`-linear and `u''` `ℂ`-antilinear. -/
theorem prop4_8_1 {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (u : E →ₗ[ℝ] F) :
    ∃! p : (E →ₗ[ℂ] F) × (E →ₛₗ[starRingEnd ℂ] F), ∀ w, u w = p.1 w + p.2 w := by
  sorry

/-- **Constant Beltrami form** (Definition 4.8.6, H1:4602): a `ℂ`-antilinear map `E → E` of norm less than `1` on a
one-dimensional complex normed space `E` (the operator norm does not depend on the choice of norm, Remark 4.8.4). -/
def IsConstBeltrami {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (μ : E →SL[starRingEnd ℂ] E) : Prop :=
  Module.finrank ℂ E = 1 ∧ ‖μ‖ < 1

/-- The `ℂ`-linear coefficient `a = ∂u = (u(1) − i u(i)) / 2` of an `ℝ`-linear `u : ℂ → ℂ`, `u(z) = a z + b z̄`
(equation (4.8.4), Example 4.8.3). -/
noncomputable def linCoeff (u : ℂ →L[ℝ] ℂ) : ℂ := (u 1 - Complex.I * u Complex.I) / 2

/-- The `ℂ`-antilinear coefficient `b = ∂̄u = (u(1) + i u(i)) / 2` of an `ℝ`-linear `u : ℂ → ℂ`. -/
noncomputable def antilinCoeff (u : ℂ →L[ℝ] ℂ) : ℂ := (u 1 + Complex.I * u Complex.I) / 2

/-- `u : ℂ → ℂ` is an orientation preserving isomorphism: its real determinant is positive. -/
def OrientPres (u : ℂ →L[ℝ] ℂ) : Prop := 0 < LinearMap.det (u : ℂ →ₗ[ℝ] ℂ)

/-- **The constant Beltrami form of an orientation preserving isomorphism** (Definition 4.8.7, equation (4.8.9)):
`μ(u) = (u')⁻¹ ∘ u'' : z ↦ (b / a) z̄`, recorded by its coefficient `b / a`. -/
noncomputable def constBeltrami (u : ℂ →L[ℝ] ℂ) : ℂ := antilinCoeff u / linCoeff u

/-- **Definition 4.8.7, well-definedness** (H1:4608). For an orientation preserving isomorphism `u`, `μ(u)` is a
Beltrami form: `|b / a| < 1` (equivalently `|a| > |b|`, Exercise 4.8.5). -/
theorem prop4_8_7 {u : ℂ →L[ℝ] ℂ} (hu : OrientPres u) : ‖constBeltrami u‖ < 1 := by
  sorry

/-- **The pullback formula** (equation (4.8.13), H1:4660): for `u(z) = a z + b z̄`, `u* μ = (ā μ + b) / (b̄ μ + a)`. -/
noncomputable def pullbackFormula (u : ℂ →L[ℝ] ℂ) (β : ℂ) : ℂ :=
  (conj (linCoeff u) * β + antilinCoeff u) / (conj (antilinCoeff u) * β + linCoeff u)

/-- **Proposition 4.8.10, existence** (Pullback of Beltrami forms, H1:4646). For an orientation preserving `u`, the map
`T = pullbackFormula u` sends the unit disc to itself and satisfies `T (μ(v)) = μ(v ∘ u)` for every orientation
preserving isomorphism `v` (equation (4.8.10)). -/
theorem prop4_8_10_a {u : ℂ →L[ℝ] ℂ} (hu : OrientPres u) :
    MapsTo (pullbackFormula u) (ball 0 1) (ball 0 1) ∧
      ∀ v : ℂ →L[ℝ] ℂ, OrientPres v → pullbackFormula u (constBeltrami v) = constBeltrami (v.comp u) := by
  sorry

/-- **Proposition 4.8.10, uniqueness** (H1:4646). A transformation `T` of the unit disc with
`T (μ(v)) = μ(v ∘ u)` for all orientation preserving isomorphisms `v` agrees with `pullbackFormula u` on the unit
disc. -/
theorem prop4_8_10_b {u : ℂ →L[ℝ] ℂ} (hu : OrientPres u) {T : ℂ → ℂ} (hT : MapsTo T (ball 0 1) (ball 0 1))
    (hv : ∀ v : ℂ →L[ℝ] ℂ, OrientPres v → T (constBeltrami v) = constBeltrami (v.comp u)) :
    EqOn T (pullbackFormula u) (ball 0 1) := by
  sorry

/-- **Proposition 4.8.10, analyticity** (H1:4646). The pullback `u* : M(ℂ) → M(ℂ)` is analytic (an automorphism of the
unit disc). -/
theorem prop4_8_10_c {u : ℂ →L[ℝ] ℂ} (hu : OrientPres u) : DifferentiableOn ℂ (pullbackFormula u) (ball 0 1) := by
  sorry

/-- **Proposition and Definition 4.8.12, existence** (The Riemann surface `X_μ`, H1:4776). Let `X` be a Riemann surface
and `μ` a Beltrami form on `X` (`‖μ‖_∞ ≤ k < 1`). There is a Riemann surface `Y` (this is `X_μ`: the same space with the
atlas `ψ_i ∘ φ_i`) and a quasiconformal homeomorphism `g : X → Y` (the identity) whose local expressions have complex
dilatation `μ` almost everywhere. -/
theorem prop4_8_12_a {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {μ : X → ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : IsBeltramiDifferential μ k) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (_ : ConnectedSpace Y) (_ : ChartedSpace ℂ Y)
      (_ : IsManifold 𝓘(ℂ) ω Y) (g : X ≃ₜ Y), IsKQCRS g ((1 + k) / (1 - k)) ∧
        ∀ x : X, ∀ᵐ z ∂(volume.restrict (localMapDomain g x)), complexDilatation (localMapExpr g x) z = μ x z := by
  sorry

/-- **Proposition and Definition 4.8.12, independence** (H1:4776). The Riemann surface structure of `X_μ` is unique: if
`g : X → Y` and `g' : X → Y'` are quasiconformal homeomorphisms onto Riemann surfaces with Beltrami form `μ`, then
`g' ∘ g⁻¹ : Y → Y'` is biholomorphic. -/
theorem prop4_8_12_b {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {μ : X → ℂ → ℂ} {Y Y' : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    [TopologicalSpace Y'] [ChartedSpace ℂ Y'] [IsManifold 𝓘(ℂ) ω Y'] {g : X ≃ₜ Y} {g' : X ≃ₜ Y'}
    (hg : IsQCRS g) (hg' : IsQCRS g')
    (hgμ : ∀ x : X, ∀ᵐ z ∂(volume.restrict (localMapDomain g x)), complexDilatation (localMapExpr g x) z = μ x z)
    (hgμ' : ∀ x : X, ∀ᵐ z ∂(volume.restrict (localMapDomain g' x)), complexDilatation (localMapExpr g' x) z = μ x z) :
    IsBiholomorphic (g'.toFun ∘ g.symm.toFun) := by
  sorry

end Hubbard2006
