import References.GardinerLakic2000.Ch08.S02_AutomorphismsOfTeichmullerDiscs

/-!
# Gardiner–Lakic 2000, Ch. 8 §8.3 Rotational transitivity

Source `teichmuller.txt`, lines 6664–6722 (Chapter 8, §8.3).

* Definition (the pull-back `c*φ(z) = φ(c(z)) c′(z)²` of a quadratic differential, l. 6669) — `pullbackQDRS`
* Definition (a complex-linear isometry of one normed set of functions onto another, l. 6669) — `IsLinearIsometryOnto`
* Definition 1 (the isometry property, l. 6669; used in §8.5, §8.6, Ch. 11) — `HasIsometryProperty`
* Definition (exceptional type `2g + n ≤ 4`, l. 6671) — `IsExceptionalGL`
* Definition 2 (`α`-rotational transitivity, l. 6673; cited at l. 8781) — `IsRotTransitive`
* Theorem 5 (l. 6675; cited at l. 8783) — `thm8_5`
* Theorem 6 (l. 6699; cited at l. 6783) — `thm8_6`

Not items: "the exceptional surfaces do not have the isometry property; their Teichmüller spaces have dimension at most
three" (l. 6671, U−, not cited). Modelling: the isometry property is surface level (C0.1): chart families of `A(R₁)`,
`A(R₂)` with `quadDiffNorm`; `c*φ` is computed in the preferred charts through the local expression
`LiZhongQC.localMapExpr c` (near miss `LiZhongQC.pullbackQD`, pull-backs from the closed surface of a finite type
structure only); equality `L φ = α c*φ` is read on every chart target. Surfaces quasiconformally equivalent to `R` are
bundles (`RSBundle`) in the universe of `R`. Theorems 5 and 6 connect the surface `R` with its Fuchsian model through a
uniformization `p : ℍ → R` with covering group `Γ`; in Theorem 6 "`R` quasiconformal to the unit disc minus a compact
set" allows the empty compact set (the disc itself).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsQCRS IsBiholomorphic localMapExpr quadDiffNorm unitDisc TeichGamma BeltramiGamma teichSetoidGamma
  upperHalf IsFuchsian ActsFreely IsUniformization integrableAutomorphicQD phiArea IsFundamentalDomainH)

/-- **Definition** (§8.3, l. 6669). The pull-back `c*φ = φ(c(z)) c′(z)²` of a quadratic differential `φ` on `R₁` by a
holomorphic map `c : R₂ → R₁`, as a chart family: in the chart at `x`, `φ_{c x}(c(z)) · (c_{loc})′(z)²`. -/
def pullbackQDRS {R₁ R₂ : Type*} [TopologicalSpace R₁] [ChartedSpace ℂ R₁] [TopologicalSpace R₂]
    [ChartedSpace ℂ R₂] (c : R₂ → R₁) (φ : R₁ → ℂ → ℂ) : R₂ → ℂ → ℂ :=
  fun x z => φ (c x) (localMapExpr c x z) * deriv (localMapExpr c x) z ^ 2

/-- Helper (§8.3–§8.9). `L` is a complex-linear isometry of `A` onto `B` (for the norms `nA`, `nB`): it maps `A` onto
`B`, is additive and homogeneous on `A`, injective on `A`, and preserves the norm. -/
def IsLinearIsometryOnto {X Y : Type*} [Add X] [SMul ℂ X] [Add Y] [SMul ℂ Y] (A : Set X) (B : Set Y)
    (nA : X → ℝ≥0∞) (nB : Y → ℝ≥0∞) (L : X → Y) : Prop :=
  MapsTo L A B ∧ SurjOn L A B ∧ InjOn L A ∧ (∀ a ∈ A, ∀ b ∈ A, L (a + b) = L a + L b) ∧
    (∀ c : ℂ, ∀ a ∈ A, L (c • a) = c • L a) ∧ ∀ a ∈ A, nB (L a) = nA a

/-- **Definition 1** (the isometry property, §8.3, l. 6669). For all surfaces `R₁`, `R₂` quasiconformally equivalent
to `R`, every linear isometry `L` of `A(R₁)` onto `A(R₂)` is `L(φ) = α c*φ` for a conformal map `c : R₂ → R₁` and a
constant `|α| = 1`. -/
def HasIsometryProperty (R : Type u) [TopologicalSpace R] [ChartedSpace ℂ R] : Prop :=
  ∀ Y₁ Y₂ : RSBundle.{u}, (∃ f : R ≃ₜ Y₁.carrier, IsQCRS f) → (∃ f : R ≃ₜ Y₂.carrier, IsQCRS f) →
    ∀ L : (Y₁.carrier → ℂ → ℂ) → (Y₂.carrier → ℂ → ℂ),
      IsLinearIsometryOnto (integrableHolQDSet Y₁.carrier) (integrableHolQDSet Y₂.carrier) quadDiffNorm quadDiffNorm
        L →
      ∃ (c : Y₂.carrier ≃ₜ Y₁.carrier) (α : ℂ), IsBiholomorphic (c : Y₂.carrier → Y₁.carrier) ∧ ‖α‖ = 1 ∧
        ∀ φ ∈ integrableHolQDSet Y₁.carrier, ∀ x : Y₂.carrier,
          EqOn (L φ x) (fun z => α * pullbackQDRS (c : Y₂.carrier → Y₁.carrier) φ x z) (chartAt ℂ x).target

/-- **Definition** (exceptional type, §8.3, l. 6671). `R` has finite analytic type `(g, n)` with `2g + n ≤ 4`. -/
def IsExceptionalGL (R : Type u) [TopologicalSpace R] [ChartedSpace ℂ R] : Prop :=
  ∃ g n : ℕ, IsFiniteAnalyticType R g n ∧ 2 * g + n ≤ 4

/-- **Definition 2** (`α`-rotational transitivity, §8.3, l. 6673). For every `[t|φ|/φ] ∈ D_φ` there is a
quasiconformal self-map `g` (possibly depending on `t`) with `ρ_g(D_φ) = D_φ` and `ρ_g([t|φ|/φ]) = [αt|φ|/φ]`. -/
def IsRotTransitive (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (φ : ℂ → ℂ) (α : ℂ) : Prop :=
  ∀ t ∈ unitDisc, ∃ g ∈ qcNormalizer Γ, ∃ Φ : TeichGamma Γ → TeichGamma Γ, IsRhoGamma Γ Γ g Φ ∧
    Φ '' teichmullerDisc Γ φ = teichmullerDisc Γ φ ∧
    ∀ μ ν : BeltramiGamma Γ, (∀ z ∈ upperHalf, μ.1.1 z = t * (conj (φ z) / ‖φ z‖)) →
      (∀ z ∈ upperHalf, ν.1.1 z = α * t * (conj (φ z) / ‖φ z‖)) →
        Φ (Quotient.mk (teichSetoidGamma Γ) μ) = Quotient.mk (teichSetoidGamma Γ) ν

/-- **Theorem 5** (§8.3, l. 6675). If `R` has the isometry property and `G` is a holomorphic automorphism of `T(R)`
fixing `[id]` with `G′([id]) = αI`, `|α| = 1`, then every Teichmüller disc through `[id]` is `α`-rotationally
transitive. -/
theorem thm8_5 {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] (hR : HasIsometryProperty R) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {G : TeichGamma Γ → TeichGamma Γ} (hG : IsHolAutT Γ Γ G) {o : TeichGamma Γ}
    (ho : IsBasePointT Γ o) (hGo : G o = o) {α : ℂ} (hα1 : ‖α‖ = 1) (hα : HasScalarDerivAtBase Γ G o α) :
    ∀ φ ∈ integrableAutomorphicQD Γ F, phiArea φ F = 1 → IsRotTransitive Γ φ α := by
  sorry

/-- **Theorem 6** (§8.3, l. 6699). If `R` is quasiconformal to the unit disc or to the unit disc with a compact subset
removed, there are Teichmüller discs in `T(R)` that are not `α`-rotationally transitive unless `α = 1`. -/
theorem thm8_6 {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hfree : ActsFreely Γ) {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F)
    (hR : ∃ (U : TopologicalSpace.Opens ℂ) (K : Set ℂ), IsCompact K ∧ K ⊆ unitDisc ∧ (U : Set ℂ) = unitDisc \ K ∧
      ∃ f : R ≃ₜ U, IsQCRS f) :
    ∃ φ ∈ integrableAutomorphicQD Γ F, phiArea φ F = 1 ∧ ∀ α : ℂ, ‖α‖ = 1 → IsRotTransitive Γ φ α → α = 1 := by
  sorry

end GardinerLakic2000
