import References.Common.HyperbolicSurface

/-!
# Hubbard 2006, Chapter 4 §4.4: Normal families of quasiconformal maps (new items)

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 3625–3780.

**Conventions.** A hyperbolic surface `X` carries the distance `d_X = References.hypDistSurf p` of a uniformization
`(Γ, p)` (`IsFuchsian Γ`, `ActsFreely Γ`, `IsUniformization Γ p`). `K`-quasiconformal maps of surfaces are
`LiZhongQC.IsKQCRS`. Surfaces are quantified over `Type` (universe `0`).

* Thm 4.4.1 (`K`-quasiconformal maps between hyperbolic surfaces are equicontinuous for the hyperbolic metrics, with a
  modulus `δ_K` independent of the surfaces) — `thm4_4_1`
* Cor. 4.4.3 (the `K`-quasiconformal self-maps of `𝔻` fixing `0` form a compact family for locally uniform
  convergence) — `cor4_4_3`
* Cor. 4.4.8 (`K`-quasiconformal maps are locally Hölder continuous of exponent `1/K`; planar domains and surfaces in
  charts) — `cor4_4_8_a`, `cor4_4_8_b`
* Lemmas 4.4.2, 4.4.4–4.4.7 (the double cover ramified at two points, the modulus estimates, the Hölder estimate in
  the hyperbolic metric) — omitted: proof step
* Exercise 4.4.9 — omitted: exercise
-/

open Set Metric
open scoped Manifold ContDiff

namespace Hubbard2006

open LiZhongQC References

/-- **Theorem 4.4.1** (`K`-quasiconformal maps are equicontinuous, H1:3629). For `K ≥ 1` there is a function
`δ_K : ℝ₊ → ℝ₊` such that for all hyperbolic Riemann surfaces `X`, `Y` (with uniformizations `(Γ, p)`, `(Γ', p')`) and
every `K`-quasiconformal homeomorphism `f : X → Y`, `d_Y(f x₁, f x₂) < δ_K(d_X(x₁, x₂))`. -/
theorem thm4_4_1 {K : ℝ} (hK : 1 ≤ K) :
    ∃ δ : ℝ → ℝ, (∀ t, 0 < δ t) ∧
      ∀ (X Y : Type) [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
        [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
        (Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → X) (p' : UpperHalfPlane → Y),
        IsFuchsian Γ → ActsFreely Γ → IsUniformization Γ p →
        IsFuchsian Γ' → ActsFreely Γ' → IsUniformization Γ' p' →
        ∀ f : X ≃ₜ Y, IsKQCRS f K → ∀ x₁ x₂ : X, hypDistSurf p' (f x₁) (f x₂) < δ (hypDistSurf p x₁ x₂) := by
  sorry

/-- **Corollary 4.4.3** (H1:3689). Let `ℱ_K(𝔻)` be the set of `K`-quasiconformal homeomorphisms `f : 𝔻 → 𝔻` with
`f(0) = 0` (restrictions to `𝔻`, as continuous maps `𝔻 → ℂ`). It is compact for the topology of uniform convergence on
compact subsets (the compact-open topology of `C(𝔻, ℂ)`). -/
theorem cor4_4_3 (K : ℝ) :
    IsCompact {F : C(↥unitDisc, ℂ) | ∃ f : ℂ → ℂ, IsKQC f unitDisc K ∧ f '' unitDisc = unitDisc ∧ f 0 = 0 ∧
      ∀ z : ↥unitDisc, F z = f z} := by
  sorry

/-- **Corollary 4.4.8, planar form** (H1:3761). A `K`-quasiconformal map `f` of an open set `U ⊂ ℂ` is locally Hölder
continuous of exponent `1/K`: every `z₀ ∈ U` has a disc `D(z₀, r) ⊂ U` and a constant `C` with
`|f z − f w| ≤ C |z − w|^{1/K}` on it. -/
theorem cor4_4_8_a {U : Set ℂ} {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f U K) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ r > 0, ball z₀ r ⊆ U ∧ ∃ C : ℝ, ∀ z ∈ ball z₀ r, ∀ w ∈ ball z₀ r,
      ‖f z - f w‖ ≤ C * ‖z - w‖ ^ (1 / K) := by
  sorry

/-- **Corollary 4.4.8, surfaces** (H1:3761). A `K`-quasiconformal homeomorphism `f : X → Y` of Riemann surfaces is
Hölder continuous of exponent `1/K` (the meaning is chart independent, as the book notes): for every `x ∈ X` the local
expression `φ_{f x} ∘ f ∘ φ_x⁻¹` is Hölder continuous of exponent `1/K` on a disc around `φ_x(x)` in its domain. -/
theorem cor4_4_8_b {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (f : X ≃ₜ Y) {K : ℝ} (hf : IsKQCRS f K) (x : X) :
    ∃ r > 0, ball (chartAt ℂ x x) r ⊆ localMapDomain f x ∧ ∃ C : ℝ, ∀ z ∈ ball (chartAt ℂ x x) r,
      ∀ w ∈ ball (chartAt ℂ x x) r, ‖localMapExpr f x z - localMapExpr f x w‖ ≤ C * ‖z - w‖ ^ (1 / K) := by
  sorry

end Hubbard2006
