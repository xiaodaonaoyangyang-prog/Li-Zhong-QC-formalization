import References.Common.HyperbolicSurface
import References.Nag1988.Ch05.S02_UniversalFamily

/-!
# Hubbard 2006, Chapter 7 §7.5: Analytic sections of the universal Teichmüller curve (new items)

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H2` lines 4336–4435.

**Conventions.** For a compact Riemann surface `S = ℍ/Γ` of genus `g ≥ 2`, the Teichmüller space `𝒯_S` is the Bers image
`LiZhongQC.bersImage Γ ⊂ B(Γ)`, and the universal curve `Ξ_S → 𝒯_S` is the Bers quotient
`V(Γ) = F(Γ)/Γ` with its projection (`LiZhongQC.BersQuotient`, `LiZhongQC.bersProjection`; Hubbard's Corollary 6.9.4
identifies the two). A section `σ : 𝒯_S → V(Γ)` is *analytic* if, near every `φ₀`, it lifts to a holomorphic function
`ζ` on an open set of `B(Γ)` (Nag's `IsBHolOn` for the cusp norm) with `σ(φ) = [φ, ζ(φ)]`, `(φ, ζ(φ)) ∈ F(Γ)`.

* Def. (analytic section of the universal curve) — `IsAnalyticSection`
* Thm 7.5.1 (the universal curve has no analytic sections for `g ≥ 3`, and exactly six, the Weierstrass points, for
  `g = 2`) — `thm7_5_1_a`, `thm7_5_1_b`
* Cor. 7.5.2 (the universal curve admits no horizontally analytic trivialization) — `cor7_5_2`
* Prop. 7.5.3, Cor. 7.5.4, Prop. 7.5.5 (the derivative of a section is an isometric embedding, the norm one projector
  `Q¹(X) → Q¹(X − {x})`, the non-existence of such projectors) — deferred: need the tangent spaces and Kobayashi balls
  of `Ξ_S` (as for Cor. 6.10.8)
-/

open Set
open scoped Manifold ContDiff

namespace Hubbard2006

open LiZhongQC Nag1988 GardinerLakic2000

/-- **An analytic section of the universal curve** `V(Γ) → 𝒯_S`: a map `σ : 𝒯_S → V(Γ)` with
`pr ∘ σ = id` that is locally of the form `φ ↦ [φ, ζ(φ)]` for a holomorphic function `ζ` on an open set `U` of `B(Γ)`
(norm `GardinerLakic2000.cuspNorm`, holomorphy in the sense of `Nag1988.IsBHolOn`), with `(φ, ζ(φ)) ∈ F(Γ)`. -/
def IsAnalyticSection (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (σ : bersImage Γ → BersQuotient Γ) : Prop :=
  (∀ φ : bersImage Γ, bersProjection Γ (σ φ) = φ.1) ∧
    ∀ φ₀ : bersImage Γ, ∃ (U : Set (ℂ → ℂ)) (ζ : (ℂ → ℂ) → ℂ), IsBOpen (cuspNorm lowerHalf) (cuspFormsL Γ) U ∧
      φ₀.1 ∈ U ∧ IsBHolOn (cuspNorm lowerHalf) (fun w : ℂ => ENNReal.ofReal ‖w‖) U ζ ∧
      ∀ φ : bersImage Γ, φ.1 ∈ U → ∃ h : (φ.1, ζ φ.1) ∈ BersFiberSpace Γ, σ φ = Quot.mk _ ⟨(φ.1, ζ φ.1), h⟩

/-- **Theorem 7.5.1 (a)** (H2:4342). For a compact surface of genus `g ≥ 3`, the universal curve has no analytic
section. -/
theorem thm7_5_1_a {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} {g : ℕ}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (hS : HasGenus S g) (hg : 3 ≤ g) :
    ¬ ∃ σ : bersImage Γ → BersQuotient Γ, IsAnalyticSection Γ σ := by
  sorry

/-- **Theorem 7.5.1 (b)** (H2:4342). For a compact surface of genus `2`, the universal curve has exactly six analytic
sections (the Weierstrass points). -/
theorem thm7_5_1_b {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (hS : HasGenus S 2) :
    Set.ncard {σ : bersImage Γ → BersQuotient Γ | IsAnalyticSection Γ σ} = 6 := by
  sorry

/-- **Corollary 7.5.2** (H2:4346). For a compact surface of genus `g ≥ 2` the universal curve admits no horizontally
analytic trivialization: there is no infinite family `y ↦ H y` of analytic sections that is pointwise injective (a
trivialization with fibre `y ∈ Y` over each point has an infinite fibre, a surface, and each `φ ↦ H y φ` would be
analytic). -/
theorem cor7_5_2 {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} {g : ℕ}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (hS : HasGenus S g) (hg : 2 ≤ g) :
    ¬ ∃ (Y : Type) (_ : Infinite Y) (H : Y → bersImage Γ → BersQuotient Γ),
      (∀ y, IsAnalyticSection Γ (H y)) ∧ ∀ φ, Function.Injective (fun y => H y φ) := by
  sorry

end Hubbard2006
