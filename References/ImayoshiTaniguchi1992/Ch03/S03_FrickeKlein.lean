import References.ImayoshiTaniguchi1992.Ch03.S02_FenchelNielsen

/-!
# Imayoshi–Taniguchi, Chapter 3 §3.3: Fricke–Klein embedding

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 3 §3.3 (`full.md` IT1:2031–2157,
folder `An Introduction to Teichmuller Spaces … ef13744b`).

Conventions: as in `S02_FenchelNielsen`. For each `j` the curves `Δ_j^0`, `Δ_j^1` are given as loops (`IsFrickeKleinData`):
`Δ_j^0` is a simple closed geodesic contained in `W_j = P_{j,1} ∪ L_j ∪ P_{j,2}` (the pieces of the decomposition whose closure
contains `L_j`) which intersects `L_j` and is different from it, and `Δ_j^1` is the simple closed geodesic freely homotopic to the
image of `Δ_j^0` under a Dehn twist along `L_j`. The map `ℓ̃ = (ℓ₁, …, ℓ_{9g-9})`
is a function `F_g → Fin 3 → Fin (3g-3) → ℝ` (the first index selects `L`, `Δ⁰`, `Δ¹`).

* Definition (the curves `Δ_j^0`, `Δ_j^1` and the map `ℓ̃`, IT1:2035) — `IsFrickeKleinData`, `loops9`, `IsLengthVec9`
* Theorem 3.12 (`ℓ̃` is a proper embedding of `F_g` into `(ℝ⁺)^{9g-9}`, IT1:2056) — `thm3_12`
* Definition (the twist path `t(s)`, IT1:2062) — exists: `ImayoshiTaniguchi1992.IsFNDeformationPath`
* Proposition 3.13 (strict convexity of the length along a twist, IT1:2072) — `prop3_13`
* Lemma 3.14 (strict convexity of the distance between geodesics, IT1:2076) — `lemma3_14`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace ImayoshiTaniguchi1992

open LiZhongQC (MarkedRS StandardGenerators IsUniformization IsFuchsian ActsFreely HasGenus Loop FreelyHomotopic)
open GardinerLakic2000 (IsSimpleLoop)
open References (IsSimpleClosedGeodesicOf markedLength)

variable {S₀ : Type} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]

/-- **The data `Δ_j^0`, `Δ_j^1`** (Ch. 3 §3.3, IT1:2035): for each `j`, `Δ_j^0` is a simple closed geodesic contained in
`W_j = L_j ∪ ⋃ {P : L_j ⊆ closure P}` (`P` the components of the complement of `⋃ L_k`, `pantsComp`) which meets `L_j` and is not `L_j`
itself (so it crosses `L_j` transversally), and `Δ_j^1` is a simple closed geodesic freely homotopic to the image of `Δ_j^0` under
a Dehn twist `T` along `L_j` (`IsDehnTwist`).
**Correction** (IT-fix2, audit AUDIT3_IT finding 2): the earlier version asked only that `Δ_j^0` meets `L_j` and dropped `Δ_j^0 ⊆ W_j`;
`Δ_j^0 = Δ_j^1 = L_j` satisfied it, and then `ℓ̃` does not separate the points of `F_g` (`thm3_12` false) and `ℓ(Δ_j^0)` is constant
along the twist path (`prop3_13` false). -/
def IsFrickeKleinData {N : ℕ} (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → S₀)
    (L D0 D1 : Fin N → Loop S₀) : Prop :=
  ∀ j, IsSimpleClosedGeodesicOf Γ p (range ((D0 j).2 : unitInterval → S₀)) ∧
    IsSimpleClosedGeodesicOf Γ p (range ((D1 j).2 : unitInterval → S₀)) ∧
    (range ((D0 j).2 : unitInterval → S₀) ∩ range ((L j).2 : unitInterval → S₀)).Nonempty ∧
    range ((D0 j).2 : unitInterval → S₀) ≠ range ((L j).2 : unitInterval → S₀) ∧
    range ((D0 j).2 : unitInterval → S₀) ⊆ (range ((L j).2 : unitInterval → S₀) ∪
      ⋃ y : {y : S₀ // range ((L j).2 : unitInterval → S₀) ⊆ closure (pantsComp L y)}, pantsComp L y.1) ∧
    ∃ T : S₀ ≃ₜ S₀, IsDehnTwist T (range ((L j).2 : unitInterval → S₀)) ∧
      FreelyHomotopic (D1 j) ⟨T (D0 j).1, (D0 j).2.map T.continuous⟩

/-- The `9g - 9` loops `L_j`, `Δ_j^0`, `Δ_j^1` (first index `0, 1, 2`). -/
def loops9 {N : ℕ} (L D0 D1 : Fin N → Loop S₀) : Fin 3 → Fin N → Loop S₀ := ![L, D0, D1]

/-- **`ℓ̃`** (Ch. 3 §3.3): `ℓ̃(c) k j` is the length of the closed geodesic of the `j`-th curve of the `k`-th family on every
marked surface with Fricke coordinates `c`. -/
def IsLengthVec9 {g : ℕ} {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p₀ : UpperHalfPlane → S₀)
    (G : StandardGenerators Γ₀ g) (Λ : Fin 3 → Fin (3 * g - 3) → Loop S₀) (ℓt : FC g → Fin 3 → Fin (3 * g - 3) → ℝ) : Prop :=
  ∀ (m : MarkedRS S₀) (c : FC g), IsFrickeCoordsIT p₀ G m c → ∀ k j, markedLength m (Λ k j) (ℓt c k j)

/-- **Theorem 3.12** (Ch. 3 §3.3). The map `ℓ̃ : F_g → (ℝ⁺)^{9g-9}` is a proper embedding: it has positive values, it is a
homeomorphism onto its image, and the preimage in `F_g` of every compact subset of `(ℝ⁺)^{9g-9}` is compact. -/
theorem thm3_12 {g : ℕ} (hg : 1 < g) [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hΓ : IsFuchsian Γ₀) (hfree : ActsFreely Γ₀) (hp : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g)
    {L D0 D1 : Fin (3 * g - 3) → Loop S₀} (hL : IsDecomposingSystemLoops Γ₀ p₀ L)
    (hD : IsFrickeKleinData Γ₀ p₀ L D0 D1) :
    ∃ ℓt : FC g → Fin 3 → Fin (3 * g - 3) → ℝ, IsLengthVec9 p₀ G (loops9 L D0 D1) ℓt ∧
      (∀ c ∈ frickeSpaceIT p₀ G, ∀ k j, 0 < ℓt c k j) ∧
      Topology.IsEmbedding ((frickeSpaceIT p₀ G).domRestrict ℓt) ∧
      ∀ K : Set (Fin 3 → Fin (3 * g - 3) → ℝ), IsCompact K → (∀ x ∈ K, ∀ k j, 0 < x k j) →
        IsCompact (frickeSpaceIT p₀ G ∩ ℓt ⁻¹' K) := by
  sorry

/-- **Proposition 3.13** (Ch. 3 §3.3). Along a Fenchel–Nielsen twist deformation `t(s) = Ψ̃⁻¹(a₁, …, a_{3g-3}, α₁, …, α_j + s, …)`
the positive function `f(s) = ℓ(Δ_j^0(t(s)))` is strictly convex and proper on `ℝ`; in particular it attains its minimum at
exactly one `s`. Modelling: `ℓΔ` is the length function of the loop `Δ_j^0`; the proper condition is
`f(s) → ∞` as `|s| → ∞`. -/
theorem prop3_13 {g : ℕ} (hg : 1 < g) [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hΓ : IsFuchsian Γ₀) (hfree : ActsFreely Γ₀) (hp : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g)
    {L D0 D1 : Fin (3 * g - 3) → Loop S₀} (hL : IsDecomposingSystemLoops Γ₀ p₀ L)
    (hD : IsFrickeKleinData Γ₀ p₀ L D0 D1) {x : S₀} {σg σa σb : Fin (3 * g - 3) → Path x x}
    (hDat : IsAdjacentPantsDatum Γ₀ p₀ L σg σa σb) (ℓ θ : Fin (3 * g - 3) → FC g → ℝ)
    (hℓ : ∀ j (m : MarkedRS S₀) (c : FC g), IsFrickeCoordsIT p₀ G m c → markedLength m (L j) (ℓ j c))
    (hθ : ∀ j (m : MarkedRS S₀) (c : FC g), IsFrickeCoordsIT p₀ G m c → IsTwistAngleIT m (σg j) (σa j) (σb j) (θ j c))
    (hθc : ∀ j, ContinuousOn (θ j) (frickeSpaceIT p₀ G)) (j : Fin (3 * g - 3)) (ℓΔ : FC g → ℝ)
    (hΔ : ∀ (m : MarkedRS S₀) (c : FC g), IsFrickeCoordsIT p₀ G m c → markedLength m (D0 j) (ℓΔ c))
    (a α : Fin (3 * g - 3) → ℝ) (path : ℝ → FC g)
    (hpath : IsFNDeformationPath (frickeSpaceIT p₀ G) (fenchelNielsenIT ℓ θ) a α j path) :
    (∀ s, 0 < ℓΔ (path s)) ∧ StrictConvexOn ℝ univ (fun s => ℓΔ (path s)) ∧
      Tendsto (fun s => ℓΔ (path s)) (cocompact ℝ) atTop ∧ ∃! s₀ : ℝ, ∀ s, ℓΔ (path s₀) ≤ ℓΔ (path s) := by
  sorry

/-- **Lemma 3.14** (Ch. 3 §3.3). Let `L₁`, `L₂` be disjoint geodesics in `ℍ`, parametrized by arc length
(`c₁`, `c₂` isometric embeddings of `ℝ`). Then the hyperbolic distance `ρ(z, w)` is strictly convex on
`{(z, w) : z ∈ L₁, w ∈ L₂}`, i.e. `(s, u) ↦ ρ(c₁ s, c₂ u)` is strictly convex on `ℝ²`. -/
theorem lemma3_14 {c₁ c₂ : ℝ → UpperHalfPlane} (h₁ : Isometry c₁) (h₂ : Isometry c₂) (hd : Disjoint (range c₁) (range c₂)) :
    StrictConvexOn ℝ univ (fun x : ℝ × ℝ => dist (c₁ x.1) (c₂ x.2)) := by
  sorry

end ImayoshiTaniguchi1992
