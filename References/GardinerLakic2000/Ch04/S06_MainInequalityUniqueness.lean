import References.GardinerLakic2000.Ch04.S05_InfiniteAnalyticType
import References.GardinerLakic2000.Ch03.S01_IntegrableQuadraticDifferentials

/-!
# Gardiner–Lakic 2000, Ch. 4 §4.6 The main inequality and uniqueness

Source `teichmuller.txt`, lines 4040–4111.

* Definition (extremal Beltrami coefficient: `‖μ‖∞` minimal in its Teichmüller class, l. 4123, 4141; used throughout
  Ch. 4–7) — `IsExtremalRS`
* Definition (`k₀ = (K₀ − 1)/(K₀ + 1)` of a Teichmüller class, l. 4104, 4123) — `extremalK`
* Theorem 4 (the main inequality (4.21), l. 4043) — `thm4_4`
* Definition (Teichmüller form `k|φ|/φ`, l. 4070, 4121) — `IsTeichmullerForm`
* Formula (4.22) (l. 4089; cited l. 4320) — `eq4_22`
* Theorem 5 (Teichmüller's uniqueness theorem, l. 4093) — `thm4_5`

Not items (DESIGN §3): the composition formula for `σ` (l. 4063, inside the proof), the wings and the horocycles
(l. 4068), the initial and terminal differentials (l. 4077, not used later), the computation after (4.21).

**[misprint] Theorem 4.** The book prints both wings with `1 + (…)φ/|φ|` but `θ` with the factors of the `−` form,
`θ = (p̄/p)(1 − conj(μφ)/|φ|)(1 − μφ/|φ|)⁻¹`, and "`p = f_z̄/f_z`" (GL8:3909–3922). The composition formula (l. 4063)
has `λ = p̄/p`, `p = f_z`, and the proof ends "the minus signs may be changed to plus signs" (l. 4066). So the
statement proved is the `−` form, which is stated here (as `LiZhongQC.thm35_2_main_inequality` does on the disc);
the `+` form follows by `φ ↦ −φ`, with `θ` changed accordingly.

**Conventions.** The Part A setting (B0.1): `R` with a uniformization `p` by a Fuchsian group; classes are
`Quot.mk (teichRel p) μ` for `μ ∈ beltramiBall R`; Beltrami coefficients of maps are `beltramiCoeffRS`; `A(R)` is
`integrableHolQDSet R` with `LiZhongQC.quadDiffNorm`. "`f₁ ∘ f` homotopic to the identity relative to the boundary"
is Part A's `IsTeichEquiv p (f.trans f₁) id` (its conformal map `c` is harmless: `c ∘ f₁` has the coefficient of
`f₁`). The integrals `∬_R (…) |φ| dx dy` are `LiZhongQC.surfaceIntegral φ`, with chart-invariant integrands; at the
zeros of `φ` the junk value of `φ/|φ|` is multiplied by `|φ| = 0`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsQCRS IsFuchsian IsUniformization quadDiffNorm surfaceIntegral dz localMapExpr)

variable {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
  [IsManifold 𝓘(ℂ) ω R]

/-- **Definition** (extremal coefficient, §4.7, l. 4123, 4141). `μ ∈ M(R)` is extremal in its Teichmüller class:
`‖μ‖∞ ≤ ‖ν‖∞` for every `ν` in the same class. -/
def IsExtremalRS (p : UpperHalfPlane → R) (μ : beltramiBall R) : Prop :=
  ∀ ν : beltramiBall R, Quot.mk (teichRel p) ν = Quot.mk (teichRel p) μ → beltramiNormRS μ.1 ≤ beltramiNormRS ν.1

/-- **Definition** (§4.6–4.7, l. 4104, 4123). `k₀ = (K₀ − 1)/(K₀ + 1)` for the minimal dilatation `K₀` of the class
`P` (the norm of an extremal coefficient). -/
def extremalK (p : UpperHalfPlane → R) (P : TeichSpace R p) : ℝ :=
  ((minimalDilatation p P).toReal - 1) / ((minimalDilatation p P).toReal + 1)

/-- **Theorem 4** (the main inequality (4.21), §4.6, l. 4043). Let `f : R → f(R)` have Beltrami coefficient `μ`,
`f₁ : f(R) → R` have Beltrami coefficient `μ₁`, with `f₁ ∘ f` homotopic to the identity relative to the boundary,
and `φ ∈ A(R)` with `‖φ‖ = 1`. Then
`1 ≤ ∬_R |1 − μφ/|φ||²/(1 − |μ|²) · |1 − μ₁(f) θ φ/|φ||²/(1 − |μ₁(f)|²) · |φ| dx dy`,
`θ = (p̄/p)(1 − conj(μφ)/|φ|)(1 − μφ/|φ|)⁻¹`, `p = f_z` [misprint: see the module docstring]. Modelling: `μ₁(f) p̄/p` is the
pull-back `ν = f^*μ₁`, a Beltrami differential on `R`; by the composition rule
`κ = (μ + ν)/(1 + μ̄ν)` for the coefficient `κ` of `f₁ ∘ f`, so `ν = (κ − μ)/(1 − μ̄κ)` and `|μ₁(f)| = |ν|`. The statement is
written with the chart families `μ` (`HasBeltramiCoeff f μ`) and `κ` (`HasBeltramiCoeff (f₁ ∘ f) κ`); the integrand is
chart invariant.
[CORRECTION] (AUDIT4 G9, AUDITR2_GL15 R2G-2) The integrand read `beltramiCoeffRS f x z`, `beltramiCoeffRS f₁ (f x) (localMapExpr f x z)` and
`dz (localMapExpr f x) z` at every point of the chart target, i.e. junk values off the local domains of the expressions, inside
the partition infimum of `surfaceIntegral`. -/
theorem thm4_4 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) {Y : RSBundle.{u}} (f : R ≃ₜ Y.carrier) (hf : IsQCRS f)
    (f₁ : Y.carrier ≃ₜ R) (hf₁ : IsQCRS f₁)
    (hhom : IsTeichEquiv p (Y₀ := selfBundle R) (Y₁ := selfBundle R) (f.trans f₁) (Homeomorph.refl R))
    {μ κ : R → ℂ → ℂ} (hμ : μ ∈ beltramiBall R) (hfμ : HasBeltramiCoeff f μ) (hκ : κ ∈ beltramiBall R)
    (hfκ : HasBeltramiCoeff (f.trans f₁) κ)
    {φ : R → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet R) (hφ1 : quadDiffNorm φ = 1) :
    1 ≤ surfaceIntegral φ fun x z =>
      ENNReal.ofReal (‖1 - μ x z * (φ x z / ‖φ x z‖)‖ ^ 2 / (1 - ‖μ x z‖ ^ 2) *
        (‖1 - (κ x z - μ x z) / (1 - conj (μ x z) * κ x z) *
            ((1 - conj (μ x z * φ x z) / ‖φ x z‖) / (1 - μ x z * φ x z / ‖φ x z‖)) * (φ x z / ‖φ x z‖)‖ ^ 2 /
          (1 - ‖(κ x z - μ x z) / (1 - conj (μ x z) * κ x z)‖ ^ 2))) := by
  sorry

/-- **Definition** (Teichmüller form, §4.6–4.7, l. 4070, 4121). The Beltrami differential `μ` is of Teichmüller
form `k|φ|/φ` (`= k φ̄/|φ|`), `φ ∈ A(R)` with `‖φ‖ = 1` and `0 ≤ k < 1` (almost everywhere in every chart). -/
def IsTeichmullerForm (μ φ : R → ℂ → ℂ) (k : ℝ) : Prop :=
  φ ∈ integrableHolQDSet R ∧ quadDiffNorm φ = 1 ∧ 0 ≤ k ∧ k < 1 ∧
    ∀ x : R, ∀ᵐ z ∂(volume.restrict (chartAt ℂ x).target), μ x z = k * (conj (φ x z) / ‖φ x z‖)

/-- **Formula (4.22)** (§4.6, l. 4070–4089). Let `g : R → R₁` have Beltrami coefficient of Teichmüller form
`k|φ|/φ` (`‖φ‖ = 1`, `K = (1 + k)/(1 − k)`), and let `f : R → R₁` be quasiconformal, Teichmüller equivalent to `g`,
with Beltrami coefficient `μ`. Then `K ≤ ∬_R |φ| |1 + μφ/|φ||²/(1 − |μ|²) dx dy`. Modelling: the book's `f₁⁻¹` is
`g`; "`f ∘ f₁` isotopic to the identity" is `IsTeichEquiv p f g`. [CORRECTION, AUDIT4 G9: the coefficients of `g` and `f` are families `μg`, `μ`
with `HasBeltramiCoeff`, not `beltramiCoeffRS`, which is junk off the local domain of the expression.] -/
theorem eq4_22 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) {Y₀ Y₁ : RSBundle.{u}} (f : R ≃ₜ Y₀.carrier) (hf : IsQCRS f)
    (g : R ≃ₜ Y₁.carrier) (hg : IsQCRS g) {φ : R → ℂ → ℂ} {k : ℝ} {μg : R → ℂ → ℂ} (hμg : HasBeltramiCoeff g μg)
    (hform : IsTeichmullerForm μg φ k) (hfg : IsTeichEquiv p f g) {μ : R → ℂ → ℂ} (hμ : μ ∈ beltramiBall R)
    (hfμ : HasBeltramiCoeff f μ) :
    ENNReal.ofReal ((1 + k) / (1 - k)) ≤ surfaceIntegral φ fun x z =>
      ENNReal.ofReal (‖1 + μ x z * (φ x z / ‖φ x z‖)‖ ^ 2 /
        (1 - ‖μ x z‖ ^ 2)) := by
  sorry

/-- **Theorem 5** (Teichmüller's uniqueness theorem, §4.6, l. 4093). Suppose `f₀ : R → R₁` has Beltrami
coefficient `k₀|φ|/φ`, `0 ≤ k₀ < 1`, `φ` an integrable holomorphic quadratic differential. Let `f : R → R₁` be any
quasiconformal map with `f⁻¹ ∘ f₀` homotopic to the identity relative to the boundary, and `μ` its Beltrami
coefficient. Then either `|μ| > k₀` on a set of positive measure, or `μ = k₀|φ|/φ` almost everywhere. Modelling: the
homotopy is Part A's `IsTeichEquiv p f f₀`; `φ ∈ A(R)` of any positive norm (`k₀|φ|/φ` is unchanged by scaling
`φ`). [CORRECTION, AUDIT4 G9: `μ` is the coefficient family of `f` (`HasBeltramiCoeff`), not `beltramiCoeffRS f`, junk off the local domain.] -/
theorem thm4_5 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) {Y : RSBundle.{u}} (f₀ : R ≃ₜ Y.carrier) (hf₀ : IsQCRS f₀) {φ : R → ℂ → ℂ}
    (hφ : φ ∈ integrableHolQDSet R) (hφ0 : quadDiffNorm φ ≠ 0) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) (hk₀1 : k₀ < 1)
    (hμ₀ : HasBeltramiCoeff f₀ fun x z => k₀ * (conj (φ x z) / ‖φ x z‖)) (f : R ≃ₜ Y.carrier) (hf : IsQCRS f)
    (hff₀ : IsTeichEquiv p f f₀) {μ : R → ℂ → ℂ} (hμ : μ ∈ beltramiBall R) (hfμ : HasBeltramiCoeff f μ) :
    (∃ x : R, 0 < volume {z | z ∈ (chartAt ℂ x).target ∧ k₀ < ‖μ x z‖}) ∨
      ∀ x : R, ∀ᵐ z ∂(volume.restrict (chartAt ℂ x).target),
        μ x z = k₀ * (conj (φ x z) / ‖φ x z‖) := by
  sorry

end GardinerLakic2000
