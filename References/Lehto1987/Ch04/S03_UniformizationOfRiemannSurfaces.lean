import References.Lehto1987.Ch04.S02_TopologyOfCoveringSurfaces

/-!
# Lehto, Chapter IV §3: Uniformization of Riemann surfaces

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. IV §3 (`full.md`
P1:5072–5260).

Conventions (see §1, §2):
- A Riemann surface is a surface with `[IsManifold 𝓘(ℂ) ω S]`.
- A conformal structure on a type `X` is an explicit `c : ChartedSpace ℂ X`. Two structures are equal when they have
  the same holomorphic functions on every open set (`GardinerLakic2000.IsHolomorphicOnFor`).
- The universal covering surface `D` of §3.3–§3.6 is a simply connected Riemann surface. Lehto normalizes it to the
  unit disc, the plane or the sphere. Statements about the disc use the upper half-plane `ℍ`, conformally
  equivalent to it, with the project's Fuchsian groups `Γ ≤ SL(2, ℝ)` (`LiZhongQC.IsUniformization`).
- The hyperbolic metric of `ℍ` is Lehto's `|dz|/(2 Im z)`, which is half of Mathlib's metric on `ℍ`.

* Theorem 3.1 (§3.1) — `thm4_3_1`
* Unlabelled (§3.1, P1:5084): Theorem 3.1 for branched coverings — omitted: quoted (Ahlfors–Sario), not cited
* Unlabelled (§3.1, P1:5088): cover transformations are conformal — `para4_3_1`
* Theorem 3.2 (§3.1) — `thm4_3_2`
* Remark (§3.1, P1:5096): a properly discontinuous conformal group with fixed points — `rem4_3_2`
* Theorem 3.3 (§3.2, Riemann Mapping Theorem) — exists: `LiZhongQC.thm22_2_uniformization` (the sphere encoded as a
  compact surface whose complement of a point is conformally the plane)
* Unlabelled (§3.2, P1:5106–5114): parabolic and hyperbolic surfaces, Green's functions, Ohtsuka's theorem — omitted:
  a sketch of a proof
* Unlabelled (§3.3, P1:5124): every Riemann surface has the disc, the plane or the sphere as universal covering
  surface — `para4_3_3_a`
* Unlabelled (§3.3, P1:5126): the elements of the covering group are Möbius transformations — `para4_3_3_b`
* Theorem 3.4 (§3.3) — `thm4_3_4`
* Unlabelled (§3.3, P1:5136): `D/G` is a Riemann surface for every properly discontinuous conformal group `G` acting
  on `D` — omitted: the case `W = D` of the Remark after Theorem 3.2 (`rem4_3_2`)
* Unlabelled (§3.4, P1:5144): if the sphere is the universal covering surface, the covering group is trivial and the
  surface is the sphere — `para4_3_4_a`
* Definition (lift of a continuous mapping, (3.1), §3.4) — `IsLiftMap`
* Formula (3.1) (§3.4) — `IsLiftMap` (its defining relation)
* Definition (the homomorphism induced by a lift, (3.2), §3.4) — `IsInducedHom`
* Formula (3.2) (§3.4) — `IsInducedHom` (its defining relation)
* Definition (equivalent homomorphisms, §3.4) — `AreEquivalentHoms`
* Unlabelled (§3.4, P1:5146–5193): lifts exist; a lift induces a homomorphism; all lifts are `h ∘ f`; induced
  homomorphisms are equivalent; equivalent homomorphisms can be realized; a homeomorphism induces an isomorphism —
  `para4_3_4_b`
* Definition (homotopy of homeomorphisms, §3.5) — exists: `ContinuousMap.Homotopic`
* Unlabelled (§3.5, P1:5199): homotopy lifting — `para4_3_5`
* Theorem 3.5 (§3.5) — `thm4_3_5`
* Formula (3.3) (§3.5) — `thm4_3_5` (the common induced isomorphism)
* Unlabelled (§3.6, P1:5219): a non-constant analytic mapping is a covering surface — `para4_3_6_a`
* Definition (lift of a differential, (3.4), §3.6) — `IsDiffLift`
* Formula (3.4) (§3.6) — `IsDiffLift` (its defining relation)
* Unlabelled (§3.6, P1:5233): the induced linear map of holomorphic differentials — omitted: U−, not cited
* Definition (differential for the group `G`, (3.5), §3.6) — `IsDiffForGroup`
* Formula (3.5) (§3.6) — `IsDiffForGroup` (its defining relation)
* Unlabelled (§3.6, P1:5247): differentials on `S` and differentials for `G` correspond — `para4_3_6_b`
* Formula (3.6) (§3.6) — `eq4_3_6`
* Definition (hyperbolic length of an arc on a Riemann surface, §3.6) — `hypLengthRS`
* Unlabelled (§3.6, P1:5259): geodesics and the hyperbolic distance on `S` — omitted: U−, not cited

Helpers (not book notions): `IsLiftedStructure` (a conformal structure on `W` making `f` analytic) and
`IsProjectedStructure` (a conformal structure on `W/G` making the projection analytic).
-/

open Complex Set Filter Topology
open scoped ENNReal ComplexConjugate ContDiff Manifold MatrixGroups UpperHalfPlane

noncomputable section

namespace Lehto1987

universe u v

open LiZhongQC (IsUniformization IsDiffFamily IsBiholomorphic upperHalf unitDisc)
open GardinerLakic2000 (IsHolomorphicOnFor)

/-! ## §3.1 Lifted and projected conformal structures -/

/-- Helper. `c` is a conformal structure on `W` for which `f : W → S` is analytic. -/
def IsLiftedStructure {W : Type u} {S : Type v} [TopologicalSpace W] [TopologicalSpace S] [ChartedSpace ℂ S]
    (c : ChartedSpace ℂ W) (f : W → S) : Prop :=
  letI := c
  IsManifold 𝓘(ℂ) ω W ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f

/-- **Theorem 3.1** (Ch. IV §3.1). Let `S` be a Riemann surface and `(W, f)` a smooth covering surface of `S`. Then `W`
carries a unique conformal structure which makes the projection `f` analytic.
Modelling: uniqueness: two such structures have the same holomorphic functions on every open set. -/
theorem thm4_3_1 {W : Type u} {S : Type v} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W]
    [ConnectedSpace W] [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] {f : W → S} (hf : IsLocalHomeomorph f) :
    (∃ c : ChartedSpace ℂ W, IsLiftedStructure c f) ∧
      ∀ c₁ c₂ : ChartedSpace ℂ W, IsLiftedStructure c₁ f → IsLiftedStructure c₂ f →
        ∀ (U : Set W) (u : W → ℂ), IsOpen U → (IsHolomorphicOnFor c₁ u U ↔ IsHolomorphicOnFor c₂ u U) := by
  sorry

/-- **Unlabelled** (Ch. IV §3.1, P1:5088). Let `S` be a Riemann surface and `(W, f)` a smooth covering surface of `S`,
with the lifted structure. Then the cover transformations of `W` over `S` are conformal. -/
theorem para4_3_1 {W : Type u} {S : Type v} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W]
    [ConnectedSpace W] [ChartedSpace ℂ W] [IsManifold 𝓘(ℂ) ω W] [TopologicalSpace S] [T2Space S]
    [SecondCountableTopology S] [ConnectedSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] {f : W → S}
    (hf : IsLocalHomeomorph f) (hfa : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {g : W ≃ₜ W} (hg : g ∈ deck f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g : W → W) := by
  sorry

/-- Helper. `c` is a conformal structure on `W/G` for which the canonical projection `W → W/G` is analytic (the
structure projected from `W`). -/
def IsProjectedStructure {W : Type u} [TopologicalSpace W] [ChartedSpace ℂ W] (G : Subgroup (W ≃ₜ W))
    (c : ChartedSpace ℂ (MulAction.orbitRel.Quotient G W)) : Prop :=
  letI := c
  IsManifold 𝓘(ℂ) ω (MulAction.orbitRel.Quotient G W) ∧
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Quotient.mk (MulAction.orbitRel G W))

/-- **Theorem 3.2** (Ch. IV §3.1). Let `W` be a Riemann surface and `G` a properly discontinuous fixed point free group
of conformal self-mappings of `W`. Then `W/G` carries a unique conformal structure which lifts to the original
conformal structure of `W`.
Modelling: the projection is analytic for that structure (then the lifted structure is that of `W`, by Theorem 3.1);
uniqueness as in `thm4_3_1`. -/
theorem thm4_3_2 {W : Type u} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W] [ConnectedSpace W]
    [ChartedSpace ℂ W] [IsManifold 𝓘(ℂ) ω W] (G : Subgroup (W ≃ₜ W)) [ProperlyDiscontinuousSMul G W]
    (hfree : ∀ g : G, ∀ q : W, g • q = q → g = 1) (hconf : ∀ g ∈ G, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g : W → W)) :
    (∃ c, IsProjectedStructure G c) ∧ ∀ c₁ c₂, IsProjectedStructure G c₁ → IsProjectedStructure G c₂ →
      ∀ (U : Set (MulAction.orbitRel.Quotient G W)) (u : MulAction.orbitRel.Quotient G W → ℂ), IsOpen U →
        (IsHolomorphicOnFor c₁ u U ↔ IsHolomorphicOnFor c₂ u U) := by
  sorry

/-- **Remark** (Ch. IV §3.1, P1:5096). If `G` is a properly discontinuous group of conformal self-mappings of a
Riemann surface `W`, but not fixed point free, then `W/G` is still a surface carrying a conformal structure which makes
the projection analytic, and `W` is a covering surface of `W/G`, branched at the fixed points of `G`.
Modelling: `W/G` is Hausdorff and second countable, and the projection is a covering surface (`IsCoveringSurface`). -/
theorem rem4_3_2 {W : Type u} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W] [ConnectedSpace W]
    [ChartedSpace ℂ W] [IsManifold 𝓘(ℂ) ω W] (G : Subgroup (W ≃ₜ W)) [ProperlyDiscontinuousSMul G W]
    (hconf : ∀ g ∈ G, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g : W → W)) :
    T2Space (MulAction.orbitRel.Quotient G W) ∧ SecondCountableTopology (MulAction.orbitRel.Quotient G W) ∧
      (∃ c, IsProjectedStructure G c) ∧ IsCoveringSurface (Quotient.mk (MulAction.orbitRel G W)) := by
  sorry

/-! ## §3.3 Representation of Riemann surfaces -/

/-- **Unlabelled** (Ch. IV §3.3, P1:5124). Every Riemann surface admits as its universal covering surface the unit
disc, the finite plane, or the extended plane.
Modelling: the disc is represented by `ℍ` (conformally equivalent); the covering is analytic; a surface covered by
the extended plane is compact and simply connected (it is the sphere, `LiZhongQC.thm22_2_uniformization`). -/
theorem para4_3_3_a (S : Type u) [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] :
    (∃ p : ℍ → S, IsUniversalCoveringSurface p ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) ∨
      (∃ p : ℂ → S, IsUniversalCoveringSurface p ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) ∨
      (CompactSpace S ∧ SimplyConnectedSpace S) := by
  sorry

/-- **Unlabelled** (Ch. IV §3.3, P1:5126). The elements of the covering group of `D` over `S` are Möbius
transformations.
Modelling: for `D = ℍ`, every cover transformation is `z ↦ γ • z` with `γ ∈ SL(2, ℝ)`; for `D = ℂ`, it is affine
(a Möbius transformation fixing `∞`). -/
theorem para4_3_3_b (S : Type u) [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] :
    (∀ p : ℍ → S, IsUniversalCoveringSurface p → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p →
      ∀ g ∈ deck p, ∃ γ : SL(2, ℝ), ∀ z : ℍ, g z = γ • z) ∧
    ∀ p : ℂ → S, IsUniversalCoveringSurface p → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p →
      ∀ g ∈ deck p, ∃ a b : ℂ, a ≠ 0 ∧ ∀ z : ℂ, g z = a * z + b := by
  sorry

/-- **Theorem 3.4** (Ch. IV §3.3). Given an arbitrary Riemann surface `S`, let `D` be its universal covering surface
and `G` the covering group of `D` over `S`. Then `S` is conformally equivalent to the Riemann surface `D/G`.
Modelling: `D` is a simply connected Riemann surface with an analytic universal covering `p`; `D/G` carries the
projected structure (it exists); the homeomorphism `[z] ↦ p(z)` is biholomorphic for it. -/
theorem thm4_3_4 {D : Type u} {S : Type v} [TopologicalSpace D] [T2Space D] [SecondCountableTopology D]
    [ConnectedSpace D] [ChartedSpace ℂ D] [IsManifold 𝓘(ℂ) ω D] [SimplyConnectedSpace D] [TopologicalSpace S]
    [T2Space S] [SecondCountableTopology S] [ConnectedSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    {p : D → S} (hp : IsUniversalCoveringSurface p) (hpa : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) :
    (∃ c, IsProjectedStructure (deck p) c) ∧
      ∃ e : MulAction.orbitRel.Quotient (deck p) D ≃ₜ S,
        (∀ z : D, e (Quotient.mk (MulAction.orbitRel (deck p) D) z) = p z) ∧
        ∀ c, IsProjectedStructure (deck p) c →
          letI := c; IsBiholomorphic (e : MulAction.orbitRel.Quotient (deck p) D → S) := by
  sorry

/-! ## §3.4 Lifting of continuous mappings -/

/-- **Unlabelled** (Ch. IV §3.4, P1:5144). If the extended plane is the universal covering surface of a Riemann
surface `S`, the covering group is trivial and `S` is conformally equivalent to the extended plane.
Modelling: the extended plane is a compact simply connected Riemann surface `D`; the covering `p` is biholomorphic. -/
theorem para4_3_4_a {D : Type u} {S : Type v} [TopologicalSpace D] [T2Space D] [SecondCountableTopology D]
    [ConnectedSpace D] [ChartedSpace ℂ D] [IsManifold 𝓘(ℂ) ω D] [SimplyConnectedSpace D] [CompactSpace D]
    [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {p : D → S} (hp : IsUniversalCoveringSurface p) (hpa : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) :
    deck p = ⊥ ∧ IsBiholomorphic p := by
  sorry

/-- **Definition** (lift of a continuous mapping, (3.1), Ch. IV §3.4): for universal coverings `πᵢ : D → Sᵢ`, a
continuous `f : D → D` with `φ ∘ π₁ = π₂ ∘ f`. -/
def IsLiftMap {D : Type u} {S₁ S₂ : Type v} [TopologicalSpace D] (φ : S₁ → S₂) (π₁ : D → S₁) (π₂ : D → S₂)
    (f : D → D) : Prop :=
  Continuous f ∧ ∀ z : D, φ (π₁ z) = π₂ (f z)

/-- **Definition** (the homomorphism induced by a lift, (3.2), Ch. IV §3.4): `θ : G₁ → G₂` between the covering
groups with `θ(g) ∘ f = f ∘ g`. -/
def IsInducedHom {D : Type u} {S₁ S₂ : Type v} [TopologicalSpace D] (π₁ : D → S₁) (π₂ : D → S₂) (f : D → D)
    (θ : deck π₁ →* deck π₂) : Prop :=
  ∀ (g : deck π₁) (z : D), ((θ g : D ≃ₜ D) : D → D) (f z) = f ((g : D ≃ₜ D) z)

/-- **Definition** (equivalent homomorphisms, Ch. IV §3.4): `θ′ = h ∘ θ ∘ h⁻¹` for some `h ∈ G₂` (they differ by an
inner automorphism of `G₂`). -/
def AreEquivalentHoms {D : Type u} {S₁ S₂ : Type v} [TopologicalSpace D] {π₁ : D → S₁} {π₂ : D → S₂}
    (θ θ' : deck π₁ →* deck π₂) : Prop :=
  ∃ h : deck π₂, ∀ g : deck π₁, θ' g = h * θ g * h⁻¹

/-- **Unlabelled** (Ch. IV §3.4, P1:5146–5193). Let `πᵢ : D → Sᵢ` be universal covering surfaces (`D` the disc or
the plane) and `φ : S₁ → S₂` continuous. Then:
(a) `φ` has a lift `f`;
(b) every lift induces a unique homomorphism `θ` by (3.2);
(c) all lifts are `h ∘ f`, `h ∈ G₂`;
(d) all induced homomorphisms are equivalent;
(e) if `φ′` induces a homomorphism equivalent to `θ`, then `φ′` has a lift inducing `θ`;
(f) if `φ` is a homeomorphism, every lift is a homeomorphism and induces an isomorphism.
Modelling: `D` is a simply connected non-compact Riemann surface; the coverings are analytic. -/
theorem para4_3_4_b {D : Type u} {S₁ S₂ : Type v} [TopologicalSpace D] [T2Space D] [SecondCountableTopology D]
    [ConnectedSpace D] [ChartedSpace ℂ D] [IsManifold 𝓘(ℂ) ω D] [SimplyConnectedSpace D] [NoncompactSpace D]
    [TopologicalSpace S₁] [T2Space S₁] [SecondCountableTopology S₁] [ConnectedSpace S₁] [ChartedSpace ℂ S₁]
    [IsManifold 𝓘(ℂ) ω S₁] [TopologicalSpace S₂] [T2Space S₂] [SecondCountableTopology S₂] [ConnectedSpace S₂]
    [ChartedSpace ℂ S₂] [IsManifold 𝓘(ℂ) ω S₂] {π₁ : D → S₁} {π₂ : D → S₂}
    (h₁ : IsUniversalCoveringSurface π₁) (h₂ : IsUniversalCoveringSurface π₂)
    (h₁a : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π₁) (h₂a : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π₂) (φ : C(S₁, S₂)) :
    (∃ f, IsLiftMap φ π₁ π₂ f) ∧
    (∀ f, IsLiftMap φ π₁ π₂ f → ∃! θ : deck π₁ →* deck π₂, IsInducedHom π₁ π₂ f θ) ∧
    (∀ f f', IsLiftMap φ π₁ π₂ f → IsLiftMap φ π₁ π₂ f' → ∃ h : deck π₂, ∀ z, f' z = (h : D ≃ₜ D) (f z)) ∧
    (∀ f f' θ θ', IsLiftMap φ π₁ π₂ f → IsLiftMap φ π₁ π₂ f' → IsInducedHom π₁ π₂ f θ →
      IsInducedHom π₁ π₂ f' θ' → AreEquivalentHoms θ θ') ∧
    (∀ (φ' : C(S₁, S₂)) f f' θ θ', IsLiftMap φ π₁ π₂ f → IsInducedHom π₁ π₂ f θ → IsLiftMap φ' π₁ π₂ f' →
      IsInducedHom π₁ π₂ f' θ' → AreEquivalentHoms θ θ' → ∃ f'', IsLiftMap φ' π₁ π₂ f'' ∧ IsInducedHom π₁ π₂ f'' θ) ∧
    (Function.Bijective φ → IsOpenMap φ → ∀ f θ, IsLiftMap φ π₁ π₂ f → IsInducedHom π₁ π₂ f θ →
      (∃ F : D ≃ₜ D, ⇑F = f) ∧ Function.Bijective θ) := by
  sorry

/-! ## §3.5 Homotopic mappings -/

/-- **Unlabelled** (Ch. IV §3.5, P1:5199). Homotopy lifting: if `H` is a homotopy from `φ₀` to `φ₁` and `f₀` a lift of
`φ₀`, the maps `H(·, t)` can be lifted to a homotopy `F` from `f₀` to a lift of `φ₁`.
Modelling: as `para4_3_4_b`; `F(t, ·)` is a lift of `H(t, ·)` for every `t`. -/
theorem para4_3_5 {D : Type u} {S₁ S₂ : Type v} [TopologicalSpace D] [T2Space D] [SecondCountableTopology D]
    [ConnectedSpace D] [ChartedSpace ℂ D] [IsManifold 𝓘(ℂ) ω D] [SimplyConnectedSpace D] [NoncompactSpace D]
    [TopologicalSpace S₁] [T2Space S₁] [SecondCountableTopology S₁] [ConnectedSpace S₁] [ChartedSpace ℂ S₁]
    [IsManifold 𝓘(ℂ) ω S₁] [TopologicalSpace S₂] [T2Space S₂] [SecondCountableTopology S₂] [ConnectedSpace S₂]
    [ChartedSpace ℂ S₂] [IsManifold 𝓘(ℂ) ω S₂] {π₁ : D → S₁} {π₂ : D → S₂}
    (h₁ : IsUniversalCoveringSurface π₁) (h₂ : IsUniversalCoveringSurface π₂)
    (h₁a : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π₁) (h₂a : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π₂) {φ₀ φ₁ : C(S₁, S₂)}
    (H : ContinuousMap.Homotopy φ₀ φ₁) {f₀ : D → D} (hf₀ : IsLiftMap φ₀ π₁ π₂ f₀) :
    ∃ F : C(unitInterval × D, D), (∀ z, F (0, z) = f₀ z) ∧
      ∀ t : unitInterval, IsLiftMap (fun x => H (t, x)) π₁ π₂ (fun z => F (t, z)) := by
  sorry

/-- **Theorem 3.5** (Ch. IV §3.5). Two homeomorphisms `φᵢ : S₁ → S₂`, `i = 0, 1`, induce the same group isomorphisms
if and only if they are homotopic.
Modelling: "the same": they have lifts `f₀`, `f₁` inducing the same `θ`, i.e. `f₀ ∘ g ∘ f₀⁻¹ = f₁ ∘ g ∘ f₁⁻¹` (3.3);
the setting is that of `para4_3_4_b`.
[reading] `D` is non-compact (the disc or the plane): Lehto excludes the extended plane in §3.4 (P1:5146). With
`D = ℂ̄` the statement would be false: the covering group is trivial, so a sense-reversing homeomorphism of the sphere
induces the same (trivial) isomorphism as the identity without being homotopic to it. -/
theorem thm4_3_5 {D : Type u} {S₁ S₂ : Type v} [TopologicalSpace D] [T2Space D] [SecondCountableTopology D]
    [ConnectedSpace D] [ChartedSpace ℂ D] [IsManifold 𝓘(ℂ) ω D] [SimplyConnectedSpace D] [NoncompactSpace D]
    [TopologicalSpace S₁] [T2Space S₁] [SecondCountableTopology S₁] [ConnectedSpace S₁] [ChartedSpace ℂ S₁]
    [IsManifold 𝓘(ℂ) ω S₁] [TopologicalSpace S₂] [T2Space S₂] [SecondCountableTopology S₂] [ConnectedSpace S₂]
    [ChartedSpace ℂ S₂] [IsManifold 𝓘(ℂ) ω S₂] {π₁ : D → S₁} {π₂ : D → S₂}
    (h₁ : IsUniversalCoveringSurface π₁) (h₂ : IsUniversalCoveringSurface π₂)
    (h₁a : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π₁) (h₂a : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π₂) (φ₀ φ₁ : S₁ ≃ₜ S₂) :
    (∃ (f₀ f₁ : D → D) (θ : deck π₁ →* deck π₂), IsLiftMap φ₀ π₁ π₂ f₀ ∧ IsLiftMap φ₁ π₁ π₂ f₁ ∧
      IsInducedHom π₁ π₂ f₀ θ ∧ IsInducedHom π₁ π₂ f₁ θ) ↔
      (φ₀ : C(S₁, S₂)).Homotopic (φ₁ : C(S₁, S₂)) := by
  sorry

/-! ## §3.6 Lifting of differentials -/

/-- **Unlabelled** (Ch. IV §3.6, P1:5219). If `f : W → S` is a non-constant analytic mapping between Riemann surfaces,
then `(W, f)` is a covering surface of `S`. -/
theorem para4_3_6_a {W : Type u} {S : Type v} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W]
    [ConnectedSpace W] [ChartedSpace ℂ W] [IsManifold 𝓘(ℂ) ω W] [TopologicalSpace S] [T2Space S]
    [SecondCountableTopology S] [ConnectedSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] {f : W → S}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hnc : ∃ x y : W, f x ≠ f y) : IsCoveringSurface f := by
  sorry

/-- **Definition** (lift of a differential, (3.4), Ch. IV §3.6). For an analytic `f : W → S` and an
`(m, n)`-differential `φ` on `S`, the lift `ψ` to `W` is given locally by `ψᵢ = φⱼ (dwⱼ/dzᵢ)^m conj(dwⱼ/dzᵢ)^n`.
Modelling: `ψ` is an `(m, n)`-family on `W` (`LiZhongQC.IsDiffFamily`) whose coefficient in the preferred chart at
`p` is `φ` at `f(p)` composed with the local expression `τ` of `f`, times `τ′^m conj(τ′)^n`, wherever `τ` is
defined.
**Correction** (Lehto-fix4, audit AUDITR2_Lehto R2L-1): the relation is a germ equality on punctured neighbourhoods
(`𝓝[≠] z`), so that a ramification point of `f` (where `τ′ = 0` and Lean's `deriv`, `0⁻¹` are junk) is not read
pointwise; for `m < 0` or `n < 0` the pointwise relation forced the value `0` at such points. At the points where
`τ′ ≠ 0` the germ relation is the pointwise relation. -/
def IsDiffLift {W : Type u} {S : Type v} [TopologicalSpace W] [ChartedSpace ℂ W] [TopologicalSpace S]
    [ChartedSpace ℂ S] (m n : ℤ) (f : W → S) (φ : S → ℂ → ℂ) (ψ : W → ℂ → ℂ) : Prop :=
  IsDiffFamily m n ψ ∧ ∀ p : W, ∀ z ∈ (chartAt ℂ p).target, f ((chartAt ℂ p).symm z) ∈ (chartAt ℂ (f p)).source →
    ∀ᶠ u in 𝓝[≠] z, ψ p u = φ (f p) (chartAt ℂ (f p) (f ((chartAt ℂ p).symm u))) *
      deriv (fun w => chartAt ℂ (f p) (f ((chartAt ℂ p).symm w))) u ^ m *
      conj (deriv (fun w => chartAt ℂ (f p) (f ((chartAt ℂ p).symm w))) u) ^ n

/-- **Definition** (`(m, n)`-differential for the group `G`, (3.5), Ch. IV §3.6): a function `φ` on `D` with
`φ(g(z)) g′(z)^m conj(g′(z))^n = φ(z)` for every `g ∈ G`.
Modelling: `D = ℍ` and `G = Γ ≤ SL(2, ℝ)` acting by `z ↦ (az + b)/(cz + d)`, `g′(z) = (cz + d)⁻²` (near miss:
`LiZhongQC.IsGammaCompatible`, the a.e. version for `(−1, 1)`). -/
def IsDiffForGroup (m n : ℤ) (Γ : Subgroup SL(2, ℝ)) (φ : ℂ → ℂ) : Prop :=
  ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
    φ ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) * (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2)⁻¹ ^ m *
      conj ((((γ 1 0 : ℂ) * z + γ 1 1) ^ 2)⁻¹) ^ n = φ z

/-- **Unlabelled** (Ch. IV §3.6, P1:5247). Let `D = ℍ` be the universal covering surface of `S` with covering group
`Γ`. The lift of an `(m, n)`-differential of `S` to `D` is a global function satisfying (3.5); conversely, every
function satisfying (3.5) defines an `(m, n)`-differential of `S`.
Modelling: `S = ℍ/Γ` through `LiZhongQC.IsUniformization`; the global function `ψ` (vanishing off `ℍ`) is the
coefficient of the lift in the (single) chart of `ℍ`. -/
theorem para4_3_6_b {S : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S} (hΓ : LiZhongQC.IsFuchsian Γ)
    (hfree : LiZhongQC.ActsFreely Γ) (hp : IsUniformization Γ p) (m n : ℤ) :
    (∀ φ : S → ℂ → ℂ, IsDiffFamily m n φ →
      ∃! ψ : ℂ → ℂ, upperHalf.indicator ψ = ψ ∧ IsDiffLift m n p φ (fun _ => ψ) ∧ IsDiffForGroup m n Γ ψ) ∧
    ∀ ψ : ℂ → ℂ, upperHalf.indicator ψ = ψ → IsDiffForGroup m n Γ ψ →
      ∃! φ : S → ℂ → ℂ, IsDiffFamily m n φ ∧ IsDiffLift m n p φ (fun _ => ψ) := by
  sorry

/-- **Formula (3.6)** (Ch. IV §3.6). The Poincaré density `η(z) = 1/(1 − |z|²)` of the unit disc satisfies
`(η ∘ g)|g′| = η` for every cover transformation `g`.
Modelling: for every conformal self-map `g(z) = e^{iθ}(z − a)/(1 − āz)`, `|a| < 1`, of the disc (the cover
transformations are among them). -/
theorem eq4_3_6 {a : ℂ} (ha : ‖a‖ < 1) (θ : ℝ) {z : ℂ} (hz : z ∈ unitDisc) :
    1 / (1 - ‖exp (θ * I) * (z - a) / (1 - conj a * z)‖ ^ 2) *
        ‖deriv (fun w => exp (θ * I) * (w - a) / (1 - conj a * w)) z‖ = 1 / (1 - ‖z‖ ^ 2) := by
  sorry

/-- **Definition** (hyperbolic length of an arc on a Riemann surface, Ch. IV §3.6): the hyperbolic length of a lift
of the arc to the universal covering surface (independent of the lift, by (3.6)).
Modelling: `D = ℍ` with Lehto's metric `|dz|/(2 Im z)`, half of Mathlib's metric of `ℍ`; the length of a path is its
variation; `[0, ∞]`-valued, the infimum over the lifts (all equal). Not `LiZhongQC.hypLength` (curves in `ℍ`, the metric
`|dz|/Im z`). -/
def hypLengthRS {S : Type u} [TopologicalSpace S] (p : ℍ → S) {x y : S} (γ : Path x y) : ℝ≥0∞ :=
  ⨅ (a : ℍ) (b : ℍ) (Γ : Path a b) (_ : ∀ t, p (Γ t) = γ t),
    (1 / 2 : ℝ≥0∞) * eVariationOn (fun t : ℝ => Γ.extend t) (Icc 0 1)

end Lehto1987
