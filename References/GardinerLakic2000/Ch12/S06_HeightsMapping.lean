import References.GardinerLakic2000.Ch12.S05_Projectivizations

/-!
# Gardiner–Lakic 2000, Ch. 12 §12.6 The heights mapping

Source `teichmuller.txt`, lines 9202–9271.

* Definition (the image `f(γ)` of a loop, l. 9225) — `loopMap`
* Unlabelled (§12.6, l. 9229–9247; used in Ch. 13, l. 9580, 9734: the heights mapping `f* : A(Ṙ) → A(Ṙ_μ)`,
  `h_φ[γ] = h_{f*φ}[f(γ)]`, a positive homogeneous homeomorphism) — `para12_6_heights_mapping`
* Formula (12.8) (`M_μ(|dv|)`, l. 9260) — `dirichletMmu`

Not items (DESIGN §3): the `C¹` representatives (l. 9219) and the induced foliation `|dṽ|` (l. 9223–9227), used in the
argument; "the infimum (12.8) depends only on the Teichmüller class" (l. 9270, U−); the Remark (l. 9248).

**Modelling.** `f : Ṙ → Ṙ_μ` is a quasiconformal map onto a surface `Y` of the same type (Part A `RSBundle`). The
side conditions of (12.8) compare heights of `f(γ)` on `Y` with heights of `γ` for `|dv|`. "Homeomorphism" is
sequential, as in Theorem 1.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (Loop quadDiffNorm IsQCRS)

/-- Helper (§12.6, l. 9225). The image `f(β)` of a loop under a homeomorphism. -/
def loopMap {R Y : Type*} [TopologicalSpace R] [TopologicalSpace Y] (f : R ≃ₜ Y) (β : Loop R) : Loop Y :=
  ⟨f β.1, β.2.map f.continuous⟩

variable {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
  [IsManifold 𝓘(ℂ) ω R]

/-- **Unlabelled** (§12.6, l. 9229–9247). A quasiconformal `f : Ṙ → Ṙ_μ` (surfaces of finite analytic type) induces
`f* : A(Ṙ) ∖ {0} → A(Ṙ_μ) ∖ {0}`, `h_φ[γ] = h_{f*φ}[f(γ)]` for all `γ ∈ 𝒮`; `f*` is bijective, positive homogeneous
and a homeomorphism. -/
theorem para12_6_heights_mapping {g n : ℕ} (hR : IsFiniteAnalyticType R g n) {Y : RSBundle.{u}}
    (hY : IsFiniteAnalyticType Y.carrier g n) (f : R ≃ₜ Y.carrier) (hf : IsQCRS f) :
    ∃ fs : (R → ℂ → ℂ) → Y.carrier → ℂ → ℂ,
      (∀ φ ∈ integrableHolQDSet R, φ ≠ 0 → fs φ ∈ integrableHolQDSet Y.carrier ∧ fs φ ≠ 0 ∧
        ∀ β : Loop R, IsEssentialLoop β → qdHeight (fs φ) (loopMap f β) = qdHeight φ β) ∧
      (∀ ψ ∈ integrableHolQDSet Y.carrier, ψ ≠ 0 → ∃! φ, φ ∈ integrableHolQDSet R ∧ φ ≠ 0 ∧ fs φ = ψ) ∧
      (∀ φ ∈ integrableHolQDSet R, φ ≠ 0 → ∀ c : ℝ, 0 < c →
        fs (fun x z => (c : ℂ) * φ x z) = fun y w => (c : ℂ) * fs φ y w) ∧
      ∀ (φs : ℕ → R → ℂ → ℂ) (φ : R → ℂ → ℂ), (∀ m, φs m ∈ integrableHolQDSet R ∧ φs m ≠ 0) →
        φ ∈ integrableHolQDSet R → φ ≠ 0 →
        (Tendsto (fun m => quadDiffNorm (φs m - φ)) atTop (𝓝 0) ↔
          Tendsto (fun m => quadDiffNorm (fs (φs m) - fs φ)) atTop (𝓝 0)) := by
  sorry

/-- **Formula (12.8)** (§12.6, l. 9260). `M_μ(|dv|) = inf ∬_{Ṙ_μ} |ψ|` over the continuous quadratic differentials
`ψ` on `Ṙ_μ` with `h_ψ[f(γ)] ≥ h_v[γ]` for all `γ ∈ 𝒮`. -/
def dirichletMmu {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] (f : R ≃ₜ Y) {ι : Type*} (U : ι → Set R)
    (v : ι → R → ℝ) : ℝ≥0∞ :=
  ⨅ (ψ : Y → ℂ → ℂ) (_ : IsContinuousQD ψ ∧
      ∀ β : Loop R, IsEssentialLoop β → folHeight U v β ≤ qdHeightSimple ψ (loopMap f β)), quadDiffNorm ψ

end GardinerLakic2000
