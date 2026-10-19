import References.Common.HyperbolicSurface
import References.GardinerLakic2000.Ch01.S06_HolomorphicMotions
import References.Hubbard2006.AppA6_CompactPerturbations

/-!
# Hubbard 2006, Chapter 5 §5.2: Holomorphic motions and Slodkowski's theorem (new items)

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H2` lines 557–970.

**Conventions.** `ℙ¹ = References.RiemannSphere = LiZhongQC.ExtPlane` with its charts (`open scoped References`); a map
into `ℙ¹` is holomorphic when it is `MDifferentiable`. The parameter space `Λ` of a holomorphic motion is a complex
analytic manifold modelled on a complex Banach space `E` (`ChartedSpace E Λ`, `IsManifold 𝓘(ℂ, E) ω Λ`). The unit
disc `𝔻` is `LiZhongQC.unitDiscOpens` with base point `0`. A `K`-quasiconformal homeomorphism of `ℙ¹` is read
through `IsKQCP1` (a homeomorphism that is `K`-quasiconformal on the open set where it is finite; the points `∞`,
`F⁻¹(∞)` are removable). Quasiconformality of the map `x ↦ φ(λ, x)` on an arbitrary subset `X ⊂ ℙ¹` is read as
"restriction of a quasiconformal homeomorphism of `ℙ¹`" (Theorem 5.2.3). The installed
`GardinerLakic2000.IsHolMotion` (motions of subsets of `ℂ` with values in `ℂ`, parametrized by the disc) and its
Theorems 1.2, 1.3 are near misses for these statements (subsets and values in `ℙ¹`, arbitrary parameter manifolds).

* Def. 5.2.1 (holomorphic motion of `X ⊂ ℙ¹` parametrized by a manifold `Λ` with base point `λ₀`) — `IsHolMotionP1`,
  `IsKQCP1`
* Thm 5.2.3 (the `λ`-lemma of Mañé–Sad–Sullivan: every `φ_λ` is quasiconformal) — `thm5_2_3`
* Cor. 5.2.4 (a holomorphic motion is continuous and extends to the closure of `X`) — `cor5_2_4`
* Thm 5.2.5 (Slodkowski's theorem: a holomorphic motion over the disc extends to all of `ℙ¹`) — `thm5_2_5`
* Thm 5.2.9 (Riesz perturbation theorem: `id + T` is a quasi-isomorphism of index `0`) — exists:
  `Hubbard2006.thmA6_1_2_c` (with `f = id`)
* Thm 5.2.10 (convolving with the Cauchy kernel) — exists: `Hubbard2006.thmA6_3_2`
* Def. of equivariance and Thm 5.2.13 (equivariant Slodkowski theorem) — `IsRhoEquivariant`, `thm5_2_13`
* Thm 5.2.6, Lemmas 5.2.7, Prop. 5.2.8, Lemma 5.2.11, Prop. 5.2.12 (finite sets, Chirka's integral equation, the
  covering argument in the proof of Slodkowski's theorem) — omitted: proof step
* Examples 5.2.2, Exercises — omitted: example / exercise
-/

open Set Metric Filter
open scoped Manifold ContDiff References

namespace Hubbard2006

open LiZhongQC References

/-- **Holomorphic motion** (Definition 5.2.1, H2:560). A holomorphic motion of `X ⊂ ℙ¹` parametrized by a complex
manifold `Λ` with base point `λ₀` is a map `φ : Λ × X → ℙ¹` such that (1) for each `x ∈ X`, `λ ↦ φ(λ, x)` is
holomorphic, (2) for each `λ`, `x ↦ φ(λ, x)` is injective, (3) `φ(λ₀, x) = x`. -/
def IsHolMotionP1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {Λ : Type*} [TopologicalSpace Λ]
    [ChartedSpace E Λ] (l₀ : Λ) (X : Set RiemannSphere) (φ : Λ → RiemannSphere → RiemannSphere) : Prop :=
  (∀ x ∈ X, MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ) (fun l => φ l x)) ∧ (∀ l, InjOn (φ l) X) ∧ ∀ x ∈ X, φ l₀ x = x

/-- **`K`-quasiconformal homeomorphism of `ℙ¹`**: a continuous bijection `F : ℙ¹ → ℙ¹` that is `K`-quasiconformal on the
open set `{z ∈ ℂ | F z ≠ ∞}` (the points `∞` and `F⁻¹(∞)` are removable). -/
def IsKQCP1 (F : RiemannSphere → RiemannSphere) (K : ℝ) : Prop :=
  Continuous F ∧ Function.Bijective F ∧
    IsKQC (fun z : ℂ => extToC (F (z : ExtPlane))) {z : ℂ | F (z : ExtPlane) ≠ extInf} K

/-- The base point `0` of the unit disc `𝔻 = unitDiscOpens`. -/
noncomputable def discOrigin : unitDiscOpens := ⟨0, Metric.mem_ball_self one_pos⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {Λ : Type*} [TopologicalSpace Λ] [ChartedSpace E Λ]
  [IsManifold 𝓘(ℂ, E) ω Λ]

/-- **Theorem 5.2.3 (`λ`-lemma of Mañé–Sad–Sullivan)** (H2:580). Let `Λ` be a connected complex analytic manifold
(perhaps Banach analytic), `X ⊂ ℙ¹` a subset and `φ : Λ × X → ℙ¹` a holomorphic motion. Then for every `λ ∈ Λ` the map
`x ↦ φ(λ, x)` is quasiconformal: it is the restriction to `X` of a `K`-quasiconformal homeomorphism of `ℙ¹`, for some
`K` (depending on `λ`). -/
theorem thm5_2_3 [ConnectedSpace Λ] {l₀ : Λ} {X : Set RiemannSphere} {φ : Λ → RiemannSphere → RiemannSphere}
    (hφ : IsHolMotionP1 (E := E) l₀ X φ) (l : Λ) :
    ∃ (K : ℝ) (F : RiemannSphere → RiemannSphere), IsKQCP1 F K ∧ ∀ x ∈ X, F x = φ l x := by
  sorry

/-- **Corollary 5.2.4** (H2:586). A holomorphic motion `φ : Λ × X → ℙ¹` is continuous, and it extends to a holomorphic
motion `φ̂` of the closure `X̄` of `X` in `ℙ¹` (continuity: jointly in `(λ, x)` on `Λ × X`). -/
theorem cor5_2_4 [ConnectedSpace Λ] {l₀ : Λ} {X : Set RiemannSphere} {φ : Λ → RiemannSphere → RiemannSphere}
    (hφ : IsHolMotionP1 (E := E) l₀ X φ) :
    ContinuousOn (fun p : Λ × RiemannSphere => φ p.1 p.2) (univ ×ˢ X) ∧
      ∃ φ' : Λ → RiemannSphere → RiemannSphere, IsHolMotionP1 (E := E) l₀ (closure X) φ' ∧
        ∀ l, ∀ x ∈ X, φ' l x = φ l x := by
  sorry

/-- **Theorem 5.2.5 (Slodkowski's theorem)** (H2:600). Let `X ⊂ ℙ¹` be a subset. Any holomorphic motion
`φ : 𝔻 × X → ℙ¹` extends to a holomorphic motion `φ̂ : 𝔻 × ℙ¹ → ℙ¹` (of the whole sphere, with the same parameter
disc and base point `0`). -/
theorem thm5_2_5 {X : Set RiemannSphere} {φ : unitDiscOpens → RiemannSphere → RiemannSphere}
    (hφ : IsHolMotionP1 (E := ℂ) discOrigin X φ) :
    ∃ φ' : unitDiscOpens → RiemannSphere → RiemannSphere,
      IsHolMotionP1 (E := ℂ) discOrigin univ φ' ∧
        ∀ l, ∀ x ∈ X, φ' l x = φ l x := by
  sorry

/-- **`ρ`-equivariant holomorphic motion** (equation (5.2.32), H2:918). Let `Γ ⊂ Aut ℙ¹ = PSL(2, ℂ)` (a subgroup of
`SL(2, ℂ)`, acting by Möbius maps `mobiusSL`) and `ρ : 𝔻 × Γ → Aut ℙ¹` (matrices `ρ λ γ`) be holomorphic in `λ`
(entrywise), with `ρ(0, γ) = γ` as Möbius maps, such that for each `λ` the map `γ ↦ ρ(λ, γ)` is an isomorphism (of
Möbius maps) onto a discrete subgroup. `φ` is `ρ`-equivariant if `φ(λ, γ x) = γ_λ (φ(λ, x))` for `x ∈ X`. -/
def IsRhoEquivariant (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ))
    (ρ : ℂ → Matrix.SpecialLinearGroup (Fin 2) ℂ → Matrix.SpecialLinearGroup (Fin 2) ℂ) (X : Set RiemannSphere)
    (φ : ℂ → RiemannSphere → RiemannSphere) : Prop :=
  (∀ γ ∈ Γ, ∀ i j, DifferentiableOn ℂ (fun l => ρ l γ i j) (ball 0 1)) ∧
    (∀ γ ∈ Γ, mobiusSL (ρ 0 γ) = mobiusSL γ) ∧
    (∀ l ∈ ball (0 : ℂ) 1, (∀ γ ∈ Γ, ∀ δ ∈ Γ, mobiusSL (ρ l (γ * δ)) = mobiusSL (ρ l γ) ∘ mobiusSL (ρ l δ)) ∧
      (∀ γ ∈ Γ, ∀ δ ∈ Γ, mobiusSL (ρ l γ) = mobiusSL (ρ l δ) → mobiusSL γ = mobiusSL δ) ∧
      DiscreteTopology (Subgroup.closure (ρ l '' (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℂ))))) ∧
    (∀ γ ∈ Γ, ∀ x ∈ X, mobiusSL γ x ∈ X) ∧
    ∀ l ∈ ball (0 : ℂ) 1, ∀ γ ∈ Γ, ∀ x ∈ X, φ l (mobiusSL γ x) = mobiusSL (ρ l γ) (φ l x)

/-- **Theorem 5.2.13 (Equivariant Slodkowski theorem)** (H2:931). Let `Γ ⊂ Aut ℙ¹` and `ρ` be as above, `X ⊂ ℙ¹` a
`Γ`-invariant subset containing the fixed points of all non-trivial elements of `Γ`, and
`φ : 𝔻 × X → ℙ¹` a `ρ`-equivariant holomorphic motion. Then `φ` admits a `ρ`-equivariant extension to a holomorphic
motion `Φ : 𝔻 × ℙ¹ → ℙ¹`. (The motions are written as functions on `ℂ`, restricted to the disc `|λ| < 1`.) -/
theorem thm5_2_13 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)}
    {ρ : ℂ → Matrix.SpecialLinearGroup (Fin 2) ℂ → Matrix.SpecialLinearGroup (Fin 2) ℂ} {X : Set RiemannSphere}
    {φ : ℂ → RiemannSphere → RiemannSphere} (hρφ : IsRhoEquivariant Γ ρ X φ)
    (hmot : IsHolMotionP1 (E := ℂ) discOrigin X
      (fun l : unitDiscOpens => φ (l : ℂ)))
    (hfix : ∀ γ ∈ Γ, mobiusSL γ ≠ id → ∀ p : RiemannSphere, mobiusSL γ p = p → p ∈ X) :
    ∃ Φ : ℂ → RiemannSphere → RiemannSphere,
      IsHolMotionP1 (E := ℂ) discOrigin univ
        (fun l : unitDiscOpens => Φ (l : ℂ)) ∧
        IsRhoEquivariant Γ ρ univ Φ ∧ ∀ l, ∀ x ∈ X, Φ l x = φ l x := by
  sorry

end Hubbard2006
