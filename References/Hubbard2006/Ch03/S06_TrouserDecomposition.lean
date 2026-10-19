import References.Hubbard2006.Ch03.S05_Trousers

/-!
# Hubbard 2006, Chapter 3 §3.6: Trouser decomposition

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 2517–2579.

**Conventions.** A hyperbolic surface is given with a uniformization `(Γ, p)` (see `S03`). A multicurve (Def. 3.6.1) is
the shared `References.IsMulticurve`, a geodesic multicurve `References.IsGeodesicMulticurve Γ p`. For a set `Y` of
curves let `Z = ⋃₀ Y` and `Z̄` its closure. The closure of a component `K` of `X ∖ Z̄` is described through its lift: if
`z ∈ ℍ` lies over `K`, let `C̃` be the closure of the component of `p⁻¹(K)` containing `z`, and `Γ_C̃` the stabilizer of
`C̃` in `Γ`; the closure of `K` is `C̃/Γ_C̃`, and "the closure of `K` is isometric to a trouser (half-annulus,
half-plane)" is the statement that the pair `(Γ_C̃, C̃)` is a `References.HypSurfBdry` which is a trouser
(`References.IsTrouserCore`), a half-annulus (`IsHalfAnnulusModel`) or a half-plane (`IsHalfPlaneModel`).
(`liftStabModel` says `S'` is that pair.) A *simple infinite geodesic* is the image under `p` of a complete geodesic
line of `ℍ` on which `p` is injective (`IsSimpleGeodesicLine`).

* Definition 3.6.1 (multicurve; geodesic multicurve) — exists: `References.IsMulticurve`,
  `References.IsGeodesicMulticurve`
* Definition (the conclusion of Thm 3.6.2: trouser decomposition) — `IsTrouserDecomposition`
* Theorem 3.6.2 (existence of a trouser decomposition) — `thm3_6_2`
* Corollary 3.6.3 (a finite multicurve is contained in the decomposition) — `cor3_6_3`
* Corollary 3.6.4 (finite type iff there is a finite multicurve with trousers as complement) — `cor3_6_4`
-/

open Set
open scoped Manifold ContDiff Topology
open LiZhongQC References

namespace Hubbard2006

/-- **Half-plane model** (Thm 3.6.2 (3)): `S = C` with trivial group, `C` a closed half-plane of `ℍ` (the half-plane
`{Im z ≥ 0}` of `𝔻` with its hyperbolic metric). -/
def IsHalfPlaneModel (S : HypSurfBdry) : Prop :=
  (∀ h ∈ S.Γ, h = 1 ∨ h = -1) ∧ IsClosedHalfPlaneH S.C

/-- A **simple infinite geodesic** of `X = ℍ/Γ`: the image under `p` of a complete geodesic line of `ℍ` on which `p` is
injective. -/
def IsSimpleGeodesicLine {X : Type*} (p : UpperHalfPlane → X) (L : Set X) : Prop :=
  ∃ f : ℝ → UpperHalfPlane, Isometry f ∧ Function.Injective (p ∘ f) ∧ L = range (p ∘ f)

/-- **`S'` is the pair (stabilizer, lifted region) of the component `K`** of the complement of the curves, seen from a
point `z ∈ ℍ` over `K`: `S'.C` is the closure of the component of `p⁻¹(K)` containing `z`, and `S'.Γ` is its stabilizer
in `Γ`. -/
def liftStabModel {X : Type*} [TopologicalSpace X] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (p : UpperHalfPlane → X) (K : Set X) (z : UpperHalfPlane) (S' : HypSurfBdry) : Prop :=
  S'.C = closure (connectedComponentIn (p ⁻¹' K) z) ∧
    ∀ γ, γ ∈ S'.Γ ↔ γ ∈ Γ ∧ (fun w : UpperHalfPlane => γ • w) '' S'.C = S'.C

/-- **Trouser decomposition** (the conclusion of Thm 3.6.2): a geodesic multicurve `Y`, with `Z = ⋃₀ Y`, such that the
closure of each component `K` of `X ∖ Z̄` is isometric to a trouser (with `0` to `3` cusps), a half-annulus, or a
half-plane (each `liftStabModel`), and each component of `Z̄ ∖ Z` is a simple infinite geodesic bounding a half-plane
(it lies in the closure of a component whose model is a half-plane). -/
def IsTrouserDecomposition {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → X) (Y : Set (Set X)) : Prop :=
  IsGeodesicMulticurve Γ p Y ∧
    (∀ x ∈ (closure (⋃₀ Y))ᶜ, ∀ z : UpperHalfPlane, p z ∈ connectedComponentIn (closure (⋃₀ Y))ᶜ x →
      ∃ S' : HypSurfBdry, liftStabModel Γ p (connectedComponentIn (closure (⋃₀ Y))ᶜ x) z S' ∧
        (IsTrouserCore S' ∨ IsHalfAnnulusModel S' ∨ IsHalfPlaneModel S')) ∧
    ∀ y ∈ closure (⋃₀ Y) \ ⋃₀ Y,
      IsSimpleGeodesicLine p (connectedComponentIn (closure (⋃₀ Y) \ ⋃₀ Y) y) ∧
        ∃ x ∈ (closure (⋃₀ Y))ᶜ, ∃ z : UpperHalfPlane, p z ∈ connectedComponentIn (closure (⋃₀ Y))ᶜ x ∧
          ∃ S' : HypSurfBdry, liftStabModel Γ p (connectedComponentIn (closure (⋃₀ Y))ᶜ x) z S' ∧
            IsHalfPlaneModel S' ∧
            connectedComponentIn (closure (⋃₀ Y) \ ⋃₀ Y) y ⊆ closure (connectedComponentIn (closure (⋃₀ Y))ᶜ x)

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Theorem 3.6.2** (trouser decomposition, Ch. 3 §3.6, H1:2529). Let `X` be a connected hyperbolic Riemann surface
that is not simply connected and not the punctured disc `𝔻*`. Then there is a (geodesic) multicurve `Y` such that, with
`Z` the union of its curves, the closure of each component of `X ∖ Z̄` is isometric to a trouser (with `0` to `3`
cusps), a half-annulus or a half-plane; moreover each component of `Z̄ ∖ Z` is a simple infinite geodesic bounding a
half-plane. Modelling: see `IsTrouserDecomposition`; `𝔻*` is `ℍ/⟨g⟩` for a parabolic `g` (hypothesis `hnp`).

**Correction** (2026-10-09, leader audit). The book's hypothesis "not simply connected" does not exclude `X = 𝔻*` (`Γ`
parabolic cyclic): `𝔻*` has no simple closed geodesic, so `Y = ∅`, and the only component of `X ∖ Z̄` is `X` itself,
whose lift `(⟨g⟩, ℍ)` is neither a trouser, nor a half-annulus, nor a half-plane (it is `IsPuncturedDiscModel`). The
hypothesis `hnp` ("`X` is not `𝔻*`") is added. Every other non-simply-connected case works: an annulus gives two
half-annuli along its core geodesic, and a group that is not parabolic cyclic contains a hyperbolic element. -/
theorem thm3_6_2 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (hX : ¬ SimplyConnectedSpace X)
    (hnp : ¬ ∃ g ∈ Γ, IsParabolic g ∧ ∀ h ∈ Γ, ∃ n : ℤ, h = g ^ n ∨ h = -g ^ n) :
    ∃ Y : Set (Set X), IsTrouserDecomposition Γ p Y := by
  sorry

/-- **Corollary 3.6.3** (Ch. 3 §3.6, H1:2574). A finite (geodesic) multicurve `Δ` may be contained in the multicurve `Y`
of Theorem 3.6.2.

**Correction** (2026-10-09, leader audit). The hypothesis `hnp` ("`X` is not `𝔻*`") of Theorem 3.6.2 is carried over:
for `X = 𝔻*` and `Δ = ∅` the conclusion fails with the theorem. -/
theorem cor3_6_3 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (hX : ¬ SimplyConnectedSpace X)
    (hnp : ¬ ∃ g ∈ Γ, IsParabolic g ∧ ∀ h ∈ Γ, ∃ n : ℤ, h = g ^ n ∨ h = -g ^ n)
    {Δ : Set (Set X)} (hΔ : Δ.Finite) (hΔm : IsGeodesicMulticurve Γ p Δ) :
    ∃ Y : Set (Set X), IsTrouserDecomposition Γ p Y ∧ Δ ⊆ Y := by
  sorry

/-- **Corollary 3.6.4** (Ch. 3 §3.6, H1:2578). A hyperbolic Riemann surface `X` is of finite type iff there is a finite
(geodesic) multicurve on `X` for which every component of the complement is a trouser: for the closure `Z̄` of the union
  of its curves, every component `K` of `X ∖ Z̄` has closure isometric to a trouser (`IsTrouserCore` for the lifted
  pair). -/
theorem cor3_6_4 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) :
    IsFiniteTypeRS X ↔ ∃ Y : Set (Set X), Y.Finite ∧ IsGeodesicMulticurve Γ p Y ∧
      ∀ x ∈ (closure (⋃₀ Y))ᶜ, ∀ z : UpperHalfPlane, p z ∈ connectedComponentIn (closure (⋃₀ Y))ᶜ x →
        ∃ S' : HypSurfBdry, liftStabModel Γ p (connectedComponentIn (closure (⋃₀ Y))ᶜ x) z S' ∧
          IsTrouserCore S' := by
  sorry

end Hubbard2006
