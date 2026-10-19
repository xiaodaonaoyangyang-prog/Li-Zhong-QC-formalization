import References.GardinerLakic2000.Ch08.S06_IsometryProperty
import References.GardinerLakic2000.Ch10.S01_MCGForCoveringGroup
import References.GardinerLakic2000.Ch06.S04_ManifoldStructure
import References.GardinerLakic2000.Ch07.S01_KobayashiMetric
import References.Lehto1987.Ch05.S09_TeichmullerSpacesOfCompactSurfaces

/-!
# Imayoshi–Taniguchi, Chapter 6 §6.4: Royden's theorems

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 6 §6.4 (`full.md` IT1:5988–6159,
folder `An Introduction to Teichmuller Spaces … ef13744b`).

Conventions: `T(Γ)` is `LiZhongQC.TeichGamma Γ` for the Fuchsian model `Γ` of a closed Riemann surface of genus `g ≥ 2`
(`IsUniformization`); its complex structure is the Bers one (`GardinerLakic2000.IsHolAutT`: a bijection which, with its
inverse, maps holomorphic discs to holomorphic discs). `Mod(Γ)` is `GardinerLakic2000.mcgGamma Γ`, and `[ω]_*` is the map
`ρ_ω : [f] ↦ [f ∘ ω⁻¹]` (`GardinerLakic2000.IsRhoGamma`). Teichmüller distance (IT-D3): IT's `d` (`d([id],[w^μ]) = log K`) is
**twice** `LiZhongQC.teichDistance`/`teichDistanceGamma` (`½ log K`); statements below use the project's distance and say so.

* Definition (Kobayashi pseudo-distance `d_M`, §6.4, IT1:6004) — exists: `GardinerLakic2000.kobayashiPseudo` (IT's
  limit of the chain distances is the largest admissible pseudometric by `GardinerLakic2000.thm7_1`)
* Definition (hyperbolic, complete complex manifold, §6.4, IT1:6028) — omitted: used only in the proof of Theorem 6.23
* Unlabelled (holomorphic maps decrease `d_M`, §6.4, IT1:6030) — exists: `GardinerLakic2000.para7_1_contraction`
* Theorem 6.20 (a) (Royden, `g = 2`, IT1:5992) — `thm6_20_a`
* Theorem 6.20 (b) (Royden, `g > 2`, IT1:5992) — `thm6_20_b`
* Theorem 6.21 (Teichmüller distance = Kobayashi distance, IT1:6038) — exists: `Lehto1987.thm5_9_4` (the project's
  distance is one half of IT's d = log K, the Kobayashi side being normalized by the same Poincaré metric)
* Theorem 6.22 (linear isometries of `A₂` are geometric, IT1:6142) — `thm6_22`
* Theorem 6.23 (`T(Γ)` is a Stein manifold, IT1:6158) — `IsDomainOfHolomorphy`, `thm6_23`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace ImayoshiTaniguchi1992

open LiZhongQC (TeichGamma HasGenus IsFuchsian ActsFreely IsUniformization bersImage)
open GardinerLakic2000 (qcNormalizer mcgGamma IsRhoGamma IsHolAutT HasIsometryProperty cuspFormsL)

/-- The group `Aut(T(Γ))` of biholomorphic automorphisms of the Teichmüller space `T(Γ)`, as a set of maps
(`GardinerLakic2000.IsHolAutT`). -/
def AutT (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Type :=
  {F : TeichGamma Γ → TeichGamma Γ // IsHolAutT Γ Γ F}

/-- **Theorem 6.20 (a)** (Royden, Ch. 6 §6.4). For `g = 2`, `Aut(T(Γ)) ≅ Mod(Γ)/ℤ₂`: the map `i_*([ω]) = [ω]_*` (`ρ_ω`,
IT1:5998) of `Mod(Γ)` is a surjection onto the biholomorphic automorphisms with kernel of order exactly two. Modelling:
`Mod(Γ)`, `Aut(T(Γ))` carry no group instances; the group-homomorphism property of `i_*` is expressed by `i_*([ω]) = ρ_ω`
for every `ω ∈ QC(Γ)` (`ρ_{ω₁ ∘ ω₂} = ρ_{ω₁} ∘ ρ_{ω₂}` is then automatic). -/
theorem thm6_20_a {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (hS : HasGenus S 2) :
    ∃ i : mcgGamma Γ → AutT Γ, Function.Surjective i ∧
      (∀ (w : ℂ → ℂ) (hw : w ∈ qcNormalizer Γ), IsRhoGamma Γ Γ w (i (Quot.mk _ ⟨w, hw⟩)).1) ∧
        Set.ncard {c : mcgGamma Γ | (i c).1 = id} = 2 := by
  sorry

/-- **Theorem 6.20 (b)** (Royden, Ch. 6 §6.4). For `g > 2`, `i_* : Mod(Γ) → Aut(T(Γ))`, `[ω] ↦ [ω]_* = ρ_ω`, is an
isomorphism (a bijection compatible with `ρ_ω`; see Theorem 6.20 (a)). -/
theorem thm6_20_b {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} {g : ℕ}
    (hg : 2 < g) (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (hS : HasGenus S g) :
    ∃ i : mcgGamma Γ → AutT Γ, Function.Bijective i ∧
      ∀ (w : ℂ → ℂ) (hw : w ∈ qcNormalizer Γ), IsRhoGamma Γ Γ w (i (Quot.mk _ ⟨w, hw⟩)).1 := by
  sorry

/-- **Theorem 6.22** (Royden, Ch. 6 §6.4). Every complex-linear isometry `α : A₂(H, Γ^μ) → A₂(H, Γ^ν)` for the
infinitesimal cometric of the Teichmüller distance (the `L¹` norm) is geometric: `α(φ) = c (φ ∘ h̃)(h̃')²` for a
biholomorphic `h : H/Γ^ν → H/Γ^μ` and a constant `|c| = 1`. Modelling: this is `GardinerLakic2000.HasIsometryProperty` of
the closed surface `S`; the factor `2` of IT's normalization of the norm does not affect isometries. Near miss:
`GardinerLakic2000.thm8_11`, which excludes the exceptional type containing closed genus `2`. -/
theorem thm6_22 {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) : HasIsometryProperty S := by
  sorry

/-- **Domain of holomorphy** in `ℂ^N` (recalled): `Ω` is open and there are no connected open `U₂ ⊄ Ω` and nonempty open
`U₁ ⊆ U₂ ∩ Ω` such that every holomorphic function on `Ω` coincides on `U₁` with a holomorphic function on `U₂`.
Modelling: for a bounded domain of `ℂ^N`, being a domain of holomorphy is equivalent to being Stein (Cartan–Thullen,
Oka); this is how Stein is read in `thm6_23`. -/
def IsDomainOfHolomorphy {N : ℕ} (Ω : Set (Fin N → ℂ)) : Prop :=
  IsOpen Ω ∧ ¬∃ U₁ U₂ : Set (Fin N → ℂ), IsOpen U₁ ∧ IsOpen U₂ ∧ IsConnected U₂ ∧ U₁.Nonempty ∧ U₁ ⊆ U₂ ∩ Ω ∧
    ¬U₂ ⊆ Ω ∧ ∀ f : (Fin N → ℂ) → ℂ, DifferentiableOn ℂ f Ω → ∃ F : (Fin N → ℂ) → ℂ, DifferentiableOn ℂ F U₂ ∧ EqOn F f U₁

/-- **Theorem 6.23** (Ch. 6 §6.4). The Teichmüller space `T(Γ)` of a closed surface of genus `g ≥ 2` is a Stein manifold.
Modelling: through the Bers embedding, `T(Γ) = T_B(Γ) ⊆ B(Γ) ≅ ℂ^{3g-3}` (a linear coordinate map `Λ` of the space of
bounded cusp forms), and Stein is read as: `Λ(T_B(Γ))` is a domain of holomorphy. -/
theorem thm6_23 {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S} {g : ℕ}
    (hg : 1 < g) (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (hS : HasGenus S g) :
    ∃ Λ : (ℂ → ℂ) → (Fin (3 * g - 3) → ℂ), IsLinearMap ℂ Λ ∧ InjOn Λ (cuspFormsL Γ) ∧ Λ '' cuspFormsL Γ = univ ∧
      IsDomainOfHolomorphy (Λ '' bersImage Γ) := by
  sorry

end ImayoshiTaniguchi1992
