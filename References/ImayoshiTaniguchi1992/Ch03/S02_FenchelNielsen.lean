import References.ImayoshiTaniguchi1992.Ch03.S01_HyperbolicGeometry
import References.Common.FenchelNielsen

/-!
# Imayoshi–Taniguchi, Chapter 3 §3.2: Fenchel–Nielsen coordinates

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 3 §3.2 (`full.md` IT1:1816–2030,
folder `An Introduction to Teichmuller Spaces … ef13744b`).

Conventions: `R = S₀` is a closed Riemann surface of genus `g ≥ 2` with a uniformization `(Γ₀, p₀)` and a standard system of
generators `G` (`LiZhongQC.StandardGenerators`, the normalization (i), (ii) of Ch. 2 §2.5); `T_g` is `LiZhongQC.TeichSpace S₀`
and `F_g ⊆ ℝ^{6g-6}` is IT's Fricke space (IT-D1, ruling "fallback"): the coordinates are the entries `(a, c, d)` of the generators
`α_j, β_j` (`j ≤ g - 1`) with the lift normalized by `c > 0` (`frickeCoordinatesIT`), near miss `LiZhongQC.frickeCoordinates`
(`(σ, τ, λ)` coordinates). Real-analytic = `AnalyticOnNhd ℝ` on the product space `FC g`. A system of decomposing curves is a
maximal geodesic multicurve (`References.IsMaximalMulticurve`), indexed by loops `L : Fin (3g - 3) → Loop S₀`.
Lengths `ℓ_j` are `References.markedLength`. **Twisting parameter** (IT-D2): IT keeps the angle `θ_j = 2π τ_j / ℓ_j`, with
`τ_j` the oriented displacement `References.footDisp G A B` along the axis of `G` between the feet of the common perpendiculars
from the axes of `A` and `B` (the two adjacent boundary classes), the data `(σg j, σa j, σb j)` being three based loops;
the statements below hold for the data
satisfying `IsAdjacentPantsDatum` (the lifts `G, A, B` generate the stabilizers of the two adjacent lifted pants). `θ_j` is defined mod `2π` (`IsTwistAngleIT`).

* Teichmüller's theorem 5.15 (quoted, IT1:1816) — omitted: Ch. 5 item (concordance)
* Unlabelled (maximal cutting gives pairs of pants, §3.2.1, IT1:1822) — `para3_2_1`
* Definition (system of decomposing curves, pants decomposition, IT1:1828) — `IsDecomposingSystem`,
  `IsDecomposingSystemLoops`
* Proposition 3.6 (`N = 3g - 3`, `M = 2g - 2`, IT1:1835) — `prop3_6`
* Unlabelled (geodesic representatives of `f_t(L_j)` form a decomposing system, §3.2.2, IT1:1859) — `para3_2_2`
* Definition (geodesic length function `ℓ_j`, IT1:1863) — exists: `References.markedLength`
* Definition (Fricke coordinates and space of IT, Ch. 2, recalled) — `FC`, `entryTriple`, `frickeCoordinatesIT`,
  `IsFrickeCoordsIT`, `frickeSpaceIT`
* Lemma 3.7 (`ℓ_j` is real-analytic on `F_g`, IT1:1865) — `lemma3_7`
* Definition (twisting parameter `θ_j`, §3.2.3, IT1:1882) — `IsFootDispOfLoops`, `pantsComp`, `pantsLift`, `IsAdjacentPantsDatum`, `IsTwistAngleIT`
* Lemma 3.8 (`e^{iθ_j}` is real-analytic on `F_g`, IT1:1884) — `lemma3_8`
* Definition (the map `Ψ`, IT1:1905; Fenchel–Nielsen coordinates, IT1:1927) — `fenchelNielsenIT`, `fnTarget`
* Lemma 3.9 (`Ψ̃` is real-analytic, IT1:1915) — `lemma3_9`
* Theorem 3.10 (`Ψ̃` is a homeomorphism onto `(ℝ⁺)^{3g-3} × ℝ^{3g-3}`, IT1:1925) — `thm3_10`
* Klein's combination theorem, Painlevé's theorem (named, inside the proof of Theorem 3.10) — omitted: quoted inside a proof
* Definition (Dehn twist, IT1:2006) — `IsDehnTwist`
* Unlabelled (a Dehn twist changes `θ_j` by `2π`, IT1:2008) — `para3_2_4`
* Theorem 3.11 (Brouwer's invariance of domain, IT1:2013) — `thm3_11`
* Definition (Fenchel–Nielsen deformation, IT1:2027) — `IsFNDeformationPath`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace ImayoshiTaniguchi1992

open LiZhongQC (MarkedRS StandardGenerators IsNormalizedLift IsInducedGenerators IsUniformization IsFuchsian ActsFreely
  HasGenus Loop FreelyHomotopic freeHomotopyLength poincareLengthLoop IsQCRS)
open GardinerLakic2000 (IsSimpleLoop)
open References (IsSimpleClosedGeodesicOf IsGeodesicMulticurve markedLength LiftsTo footDisp axisH)
open LiZhongQC (IsHyperbolic)

/-! ## Fricke coordinates of IT -/

/-- The space `ℝ^{6g-6}` of IT's Fricke coordinates `(a_j, c_j, d_j, a'_j, c'_j, d'_j)_{j ≤ g-1}`. -/
abbrev FC (g : ℕ) : Type := Fin (g - 1) → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)

/-- The coordinates `(a, c, d)` of a hyperbolic transformation `γ = (az + b)/(cz + d)`, with the lift to `SL(2, ℝ)` normalized
by `c > 0` (IT1:1440): `(ε a, |c|, ε d)` with `ε = sign c`. *Junk:* `c = 0` gives `(0, 0, 0)`; it does not occur for generators
other than `β_g` (Ch. 2 Lemma 2.24). -/
def entryTriple (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : ℝ × ℝ × ℝ :=
  ((SignType.sign (γ 1 0) : ℝ) * γ 0 0, |γ 1 0|, (SignType.sign (γ 1 0) : ℝ) * γ 1 1)

/-- **The Fricke coordinates `ℱ_g`** of a standard system of generators (Ch. 2 §2.5, IT1:1454):
`(a₁, c₁, d₁, a'₁, c'₁, d'₁, …)`. Near miss `LiZhongQC.frickeCoordinates`. -/
def frickeCoordinatesIT {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {g : ℕ} (G : StandardGenerators Γ g) : FC g :=
  fun j => (entryTriple (G.first j).1, entryTriple (G.first j).2)

variable {S₀ : Type} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]

/-- `c` are the (IT) Fricke coordinates of the marked surface `m` with respect to the fixed uniformization `p₀` and the standard
system `G` of `S₀` (as `LiZhongQC.IsFrickeCoords`, with `frickeCoordinatesIT`). -/
def IsFrickeCoordsIT {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {g : ℕ} (p₀ : UpperHalfPlane → S₀)
    (G : StandardGenerators Γ₀ g) (m : MarkedRS S₀) (c : FC g) : Prop :=
  ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → m.X.carrier)
    (F : UpperHalfPlane ≃ₜ UpperHalfPlane) (Gb : LiZhongQC.ExtPlane → LiZhongQC.ExtPlane) (G' : StandardGenerators Γ g),
    IsUniformization Γ p ∧ IsNormalizedLift p₀ p m.marking F Gb ∧ IsInducedGenerators F G G' ∧
      c = frickeCoordinatesIT G'

/-- **The Fricke space `F_g ⊆ ℝ^{6g-6}`** of IT: the Fricke coordinates of all marked surfaces; with the relative topology of
`ℝ^{6g-6}`. -/
def frickeSpaceIT {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {g : ℕ} (p₀ : UpperHalfPlane → S₀)
    (G : StandardGenerators Γ₀ g) : Set (FC g) :=
  {c | ∃ m : MarkedRS S₀, IsFrickeCoordsIT p₀ G m c}

/-! ## §3.2.1 Systems of decomposing curves -/

/-- **System of decomposing curves** (Ch. 3 §3.2.1): a maximal set of mutually disjoint simple closed geodesics of
`R = ℍ/Γ`, i.e. a maximal geodesic multicurve. -/
def IsDecomposingSystem {R : Type} [TopologicalSpace R] [ChartedSpace ℂ R]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → R) (Y : Set (Set R)) : Prop :=
  IsGeodesicMulticurve Γ p Y ∧ ∀ Y' : Set (Set R), IsGeodesicMulticurve Γ p Y' → Y ⊆ Y' → Y' = Y

/-- A system of decomposing curves `L₁, …, L_N`, given by simple loops with pairwise different ranges. -/
def IsDecomposingSystemLoops {R : Type} [TopologicalSpace R] [ChartedSpace ℂ R]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → R) {N : ℕ} (L : Fin N → Loop R) : Prop :=
  (∀ j, IsSimpleLoop (L j)) ∧ Function.Injective (fun j => range ((L j).2 : unitInterval → R)) ∧
    IsDecomposingSystem Γ p (range fun j => range ((L j).2 : unitInterval → R))

/-- **Unlabelled claim** (Ch. 3 §3.2.1, IT1:1822). Cutting a closed `R` of genus `g ≥ 2` along a system of decomposing curves
(a maximal set of disjoint simple closed geodesics), every piece is a pair of pants of `R`. -/
theorem para3_2_1 {g : ℕ} (hg : 1 < g) [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hΓ : IsFuchsian Γ₀) (hfree : ActsFreely Γ₀) (hp : IsUniformization Γ₀ p₀) {Y : Set (Set S₀)}
    (hY : IsDecomposingSystem Γ₀ p₀ Y) {x : S₀} (hx : x ∉ ⋃₀ Y) :
    IsPantsOf Γ₀ p₀ (connectedComponentIn (⋃₀ Y)ᶜ x) := by
  sorry

/-- **Proposition 3.6** (Ch. 3 §3.2.1). For every system of decomposing curves `𝓛 = {L_j}_{j=1}^N` on a closed Riemann surface
`R` of genus `g ≥ 2`, with pants decomposition `𝓟 = {P_k}_{k=1}^M` (the components of `R - ⋃ L_j`): `N = 3g - 3` and
`M = 2g - 2`. (Both sets are asserted finite: `Set.ncard` of an infinite set is `0`.) -/
theorem prop3_6 {g : ℕ} (hg : 1 < g) [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hΓ : IsFuchsian Γ₀) (hfree : ActsFreely Γ₀) (hp : IsUniformization Γ₀ p₀) {Y : Set (Set S₀)}
    (hY : IsDecomposingSystem Γ₀ p₀ Y) :
    Y.ncard = 3 * g - 3 ∧ {P : Set S₀ | ∃ x ∉ ⋃₀ Y, P = connectedComponentIn (⋃₀ Y)ᶜ x}.ncard = 2 * g - 2 := by
  sorry

/-- **Unlabelled claim** (Ch. 3 §3.2.2, IT1:1859). Let `f_t : R → R_t` be a marking-preserving homeomorphism. For `L_j ∈ 𝓛` let
`L_j(t)` be the unique closed geodesic freely homotopic to `f_t(L_j)`. Then each `L_j(t)` is simple, `L_j(t) ∩ L_{j'}(t) = ∅`
for `j ≠ j'`, and `𝓛_t = {L_j(t)}` is a system of decomposing curves on `R_t`. Modelling: `f_t` is the marking `m.marking` of a
marked surface `m`, `R_t = m.X` with any uniformization. -/
theorem para3_2_2 {g : ℕ} (hg : 1 < g) [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hΓ : IsFuchsian Γ₀) (hfree : ActsFreely Γ₀) (hp : IsUniformization Γ₀ p₀) {L : Fin (3 * g - 3) → Loop S₀}
    (hL : IsDecomposingSystemLoops Γ₀ p₀ L) (m : MarkedRS S₀) {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p' : UpperHalfPlane → m.X.carrier} (hΓ' : IsFuchsian Γ') (hfree' : ActsFreely Γ') (hp' : IsUniformization Γ' p') :
    ∃ C' : Fin (3 * g - 3) → Set m.X.carrier,
      Function.Injective C' ∧ IsDecomposingSystem Γ' p' (range C') ∧
        ∀ j, ∃ β : Loop m.X.carrier, IsSimpleLoop β ∧ range (β.2 : unitInterval → m.X.carrier) = C' j ∧
          FreelyHomotopic β ⟨m.marking (L j).1, (L j).2.map m.marking.continuous⟩ ∧
          poincareLengthLoop p' β = freeHomotopyLength p' ⟨m.marking (L j).1, (L j).2.map m.marking.continuous⟩ := by
  sorry

/-! ## §3.2.2 – §3.2.4 Lengths, twisting parameters and the map `Ψ̃` -/

/-- **Lemma 3.7** (Ch. 3 §3.2.2). Every geodesic length function `ℓ_j(t)` is real-analytic on `F_g`: there is a function
`ℓ : ℝ^{6g-6} → ℝ`, real-analytic on `F_g`, with `ℓ(c)` the length of the closed geodesic of `L_j` on every marked surface with
Fricke coordinates `c`. -/
theorem lemma3_7 {g : ℕ} (hg : 1 < g) [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hΓ : IsFuchsian Γ₀) (hfree : ActsFreely Γ₀) (hp : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g)
    {L : Fin (3 * g - 3) → Loop S₀} (hL : IsDecomposingSystemLoops Γ₀ p₀ L) (j : Fin (3 * g - 3)) :
    ∃ ℓ : FC g → ℝ, (∀ (m : MarkedRS S₀) (c : FC g), IsFrickeCoordsIT p₀ G m c → markedLength m (L j) (ℓ c)) ∧
      AnalyticOnNhd ℝ ℓ (frickeSpaceIT p₀ G) := by
  sorry

/-- **`t` is the oriented displacement of three loops** (the quantity `τ_j` of Ch. 3 §3.2.3): for some uniformization
`(Γ, p)` and a point `z₀` over the base point, the lifts of the loops `σg, σa, σb` from `z₀` end at `G z₀, A z₀, B z₀` and
`t = References.footDisp G A B`, the signed displacement along the axis of `G` (in its direction of translation) from the foot
of the common perpendicular of the axis of `A` to that of `B`. As `References.IsTwistOfLoops` with `footDisp` in place of
`twistLength` (IT's sign, not Hubbard's). A relation, as there. -/
def IsFootDispOfLoops {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y] {y : Y} (σg σa σb : Path y y) (t : ℝ) : Prop :=
  ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → Y), IsFuchsian Γ ∧ ActsFreely Γ ∧
    IsUniformization Γ p ∧ ∃ z₀ : UpperHalfPlane, p z₀ = y ∧ ∃ G ∈ Γ, ∃ A ∈ Γ, ∃ B ∈ Γ, LiftsTo p z₀ G σg ∧
      LiftsTo p z₀ A σa ∧ LiftsTo p z₀ B σb ∧ t = footDisp G A B

/-- The pair of pants of the decomposition containing `y`: the component of `S₀ - ⋃ L_k` containing `y`. -/
def pantsComp {S₀ : Type} [TopologicalSpace S₀] {N : ℕ} (L : Fin N → Loop S₀) (y : S₀) : Set S₀ :=
  connectedComponentIn (⋃ k, range ((L k).2 : unitInterval → S₀))ᶜ y

/-- The component of the preimage `p⁻¹(P)` of a pair of pants containing `w`. -/
def pantsLift {S₀ : Type} [TopologicalSpace S₀] (p : UpperHalfPlane → S₀) (P : Set S₀) (w : UpperHalfPlane) :
    Set UpperHalfPlane :=
  connectedComponentIn (p ⁻¹' P) w

/-- **The datum of the twisting parameters** (Ch. 3 §3.2.3): three based loops `σg j, σa j, σb j` at `x` for each `j`, with
lifts `G, A, B ∈ Γ₀` from one point `z₀` over `x` (`References.LiftsTo`) such that
1. `G` is hyperbolic and its closed geodesic is `L_j`: `p₀ '' axisH G = range (L j)`;
2. there are two pairs of pants `P₁, P₂` of the decomposition (components of the complement of `⋃ L_k`, `IsPantsOf`) and
   components `S₁`, `S₂` of `p₀⁻¹(P₁)`, `p₀⁻¹(P₂)` (distinct) whose closures contain `axisH G`, with
   `Γ_{S₁} = ⟨G, A⟩` and `Γ_{S₂} = ⟨G, B⟩` modulo `±1` (`stabSubgroup ⊔ ⟨−1⟩ = ⟨G, A⟩ ⊔ ⟨−1⟩`: the stabilizers are free on `G, A` and
   `G, B` as groups of Möbius maps; `−1` is allowed in `Γ₀`, IT-fix2);
3. `A`, `B` are hyperbolic and their axes lie in the frontiers of `S₁`, `S₂` (boundary classes of the two adjacent pants;
   `P₁ = P₂` is allowed, the lifts differ).
Why this pins down the twist: `Γ_{S₁} = ⟨G, A⟩` (as Möbius maps) is free of rank two, so `A ∉ ⟨G⟩` (excluding `A = G`, for which
`busemannSum A` is constant on `axisH G` and the foot is arbitrary); a basis `(G, A')` of `Γ_{S₁}` with `axisH A'` in the frontier
is `A' = G^k A^{±1} G^{-k}` or `G^k (AG)^{±1} G^{-k}` (the other boundary lines at distance zero from `axisH G`), which changes the
angle `θ_j = 2π τ_j/ℓ_j` by `2πk` or by `π + 2πk`, i.e. by a constant depending only on the datum; other conjugates of `A` do not
generate `Γ_{S₁}` with `G`. So `θ_j` is well defined modulo `2π` up to a constant. Shared with Hubbard 2006 (batch 4, D20). -/
def IsAdjacentPantsDatum {N : ℕ} (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p₀ : UpperHalfPlane → S₀)
    (L : Fin N → Loop S₀) {x : S₀} (σg σa σb : Fin N → Path x x) : Prop :=
  ∀ j, ∃ z₀ : UpperHalfPlane, p₀ z₀ = x ∧ ∃ G ∈ Γ₀, ∃ A ∈ Γ₀, ∃ B ∈ Γ₀, LiftsTo p₀ z₀ G (σg j) ∧
    LiftsTo p₀ z₀ A (σa j) ∧ LiftsTo p₀ z₀ B (σb j) ∧ IsHyperbolic G ∧
    p₀ '' axisH G = range ((L j).2 : unitInterval → S₀) ∧ IsHyperbolic A ∧ IsHyperbolic B ∧
    ∃ (y₁ y₂ : S₀) (w₁ w₂ : UpperHalfPlane),
      IsPantsOf Γ₀ p₀ (pantsComp L y₁) ∧ IsPantsOf Γ₀ p₀ (pantsComp L y₂) ∧ p₀ w₁ ∈ pantsComp L y₁ ∧
      p₀ w₂ ∈ pantsComp L y₂ ∧ (pantsLift p₀ (pantsComp L y₁) w₁ ≠ pantsLift p₀ (pantsComp L y₂) w₂) ∧
      axisH G ⊆ closure (pantsLift p₀ (pantsComp L y₁) w₁) ∧ axisH G ⊆ closure (pantsLift p₀ (pantsComp L y₂) w₂) ∧
      stabSubgroup Γ₀ (pantsLift p₀ (pantsComp L y₁) w₁) ⊔ Subgroup.zpowers (-1) = Subgroup.closure {G, A} ⊔ Subgroup.zpowers (-1) ∧
      stabSubgroup Γ₀ (pantsLift p₀ (pantsComp L y₂) w₂) ⊔ Subgroup.zpowers (-1) = Subgroup.closure {G, B} ⊔ Subgroup.zpowers (-1) ∧
      axisH A ⊆ frontier (pantsLift p₀ (pantsComp L y₁) w₁) ∧ axisH B ⊆ frontier (pantsLift p₀ (pantsComp L y₂) w₂)

/-- **Twisting parameter `θ_j`** (Ch. 3 §3.2.3, IT1:1882) of the marked surface `m`, as a relation on the real numbers modulo
`2π`: `θ = 2π τ / ℓ + 2π k`, `ℓ` the length of the geodesic of `σg` and `τ` the oriented displacement of the three loops
(`IsFootDispOfLoops`). -/
def IsTwistAngleIT (m : MarkedRS S₀) {x : S₀} (σg σa σb : Path x x) (θ : ℝ) : Prop :=
  ∃ ℓ τ : ℝ, 0 < ℓ ∧ markedLength m ⟨x, σg⟩ ℓ ∧
    IsFootDispOfLoops (σg.map m.marking.continuous) (σa.map m.marking.continuous) (σb.map m.marking.continuous) τ ∧
    ∃ k : ℤ, θ = 2 * Real.pi * τ / ℓ + 2 * Real.pi * k

/-- **Lemma 3.8** (Ch. 3 §3.2.3). For every `j`, `e^{iθ_j}` is well defined and real-analytic on `F_g`: every marked surface with
coordinates `c` has a twisting parameter and `e^{iθ_j} = w(c)` for a function `w` real-analytic on `F_g`. -/
theorem lemma3_8 {g : ℕ} (hg : 1 < g) [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hΓ : IsFuchsian Γ₀) (hfree : ActsFreely Γ₀) (hp : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g)
    {L : Fin (3 * g - 3) → Loop S₀} (hL : IsDecomposingSystemLoops Γ₀ p₀ L) {x : S₀}
    {σg σa σb : Fin (3 * g - 3) → Path x x} (hD : IsAdjacentPantsDatum Γ₀ p₀ L σg σa σb) (j : Fin (3 * g - 3)) :
    ∃ w : FC g → ℂ, (∀ (m : MarkedRS S₀) (c : FC g), IsFrickeCoordsIT p₀ G m c →
        (∃ θ, IsTwistAngleIT m (σg j) (σa j) (σb j) θ) ∧
          ∀ θ, IsTwistAngleIT m (σg j) (σa j) (σb j) θ → w c = Complex.exp (θ * Complex.I)) ∧
      AnalyticOnNhd ℝ w (frickeSpaceIT p₀ G) := by
  sorry

/-- **The map `Ψ̃`** (Ch. 3 §3.2.4, IT1:1905, 1927; the Fenchel–Nielsen coordinates): `Ψ̃(t) = (ℓ₁(t), …, ℓ_N(t), θ₁(t), …, θ_N(t))`
for functions `ℓ`, `θ` (the lengths and single-valued branches of the twisting parameters). -/
def fenchelNielsenIT {g : ℕ} (ℓ θ : Fin (3 * g - 3) → FC g → ℝ) : FC g → (Fin (3 * g - 3) → ℝ) × (Fin (3 * g - 3) → ℝ) :=
  fun c => (fun j => ℓ j c, fun j => θ j c)

/-- The target `(ℝ⁺)^{3g-3} × ℝ^{3g-3}` of `Ψ̃`. -/
def fnTarget (g : ℕ) : Set ((Fin (3 * g - 3) → ℝ) × (Fin (3 * g - 3) → ℝ)) := {x | ∀ j, 0 < x.1 j}

/-- **Lemma 3.9** (Ch. 3 §3.2.4). Fix a single-valued continuous branch `θ̃_j` of each twisting parameter on `F_g` (and the length
functions `ℓ_j`). Then `Ψ̃ = (ℓ, θ̃)` is real-analytic on `F_g`. -/
theorem lemma3_9 {g : ℕ} (hg : 1 < g) [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hΓ : IsFuchsian Γ₀) (hfree : ActsFreely Γ₀) (hp : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g)
    {L : Fin (3 * g - 3) → Loop S₀} (hL : IsDecomposingSystemLoops Γ₀ p₀ L) {x : S₀}
    {σg σa σb : Fin (3 * g - 3) → Path x x} (hD : IsAdjacentPantsDatum Γ₀ p₀ L σg σa σb) (ℓ θ : Fin (3 * g - 3) → FC g → ℝ)
    (hℓ : ∀ j (m : MarkedRS S₀) (c : FC g), IsFrickeCoordsIT p₀ G m c → markedLength m (L j) (ℓ j c))
    (hθ : ∀ j (m : MarkedRS S₀) (c : FC g), IsFrickeCoordsIT p₀ G m c → IsTwistAngleIT m (σg j) (σa j) (σb j) (θ j c))
    (hθc : ∀ j, ContinuousOn (θ j) (frickeSpaceIT p₀ G)) :
    AnalyticOnNhd ℝ (fenchelNielsenIT ℓ θ) (frickeSpaceIT p₀ G) := by
  sorry

/-- **Theorem 3.10** (Ch. 3 §3.2.4). In the situation of Lemma 3.9, `Ψ̃` is a homeomorphism of `F_g` onto
`(ℝ⁺)^{3g-3} × ℝ^{3g-3}`; in particular it gives global coordinates on `F_g`, hence on `T_g`. -/
theorem thm3_10 {g : ℕ} (hg : 1 < g) [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hΓ : IsFuchsian Γ₀) (hfree : ActsFreely Γ₀) (hp : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g)
    {L : Fin (3 * g - 3) → Loop S₀} (hL : IsDecomposingSystemLoops Γ₀ p₀ L) {x : S₀}
    {σg σa σb : Fin (3 * g - 3) → Path x x} (hD : IsAdjacentPantsDatum Γ₀ p₀ L σg σa σb) (ℓ θ : Fin (3 * g - 3) → FC g → ℝ)
    (hℓ : ∀ j (m : MarkedRS S₀) (c : FC g), IsFrickeCoordsIT p₀ G m c → markedLength m (L j) (ℓ j c))
    (hθ : ∀ j (m : MarkedRS S₀) (c : FC g), IsFrickeCoordsIT p₀ G m c → IsTwistAngleIT m (σg j) (σa j) (σb j) (θ j c))
    (hθc : ∀ j, ContinuousOn (θ j) (frickeSpaceIT p₀ G)) :
    ∃ e : ↥(frickeSpaceIT p₀ G) ≃ₜ ↥(fnTarget g), ∀ c : ↥(frickeSpaceIT p₀ G), (e c : _ × _) = fenchelNielsenIT ℓ θ c := by
  sorry

/-! ## The Dehn twist and the invariance of domain -/

/-- **Dehn twist** along the simple closed curve `C ⊆ S₀` (Ch. 3 §3.2.4, IT1:2006): a homeomorphism `T` of `S₀` which is the
identity off a collar `e(S¹ × [0,1])` of `C = {e(z, 1/2)}` and rotates by the angle `2π s` in the circles `s = const`:
`T(e(z, s)) = e(z e^{2πis}, s)`. Modelling: the collar is an injective continuous map `e : S¹ × [0,1] → S₀`. -/
def IsDehnTwist (T : S₀ ≃ₜ S₀) (C : Set S₀) : Prop :=
  ∃ e : Circle × unitInterval → S₀, Continuous e ∧ Function.Injective e ∧ (∀ x, x ∉ range e → T x = x) ∧
    (∀ (z : Circle) (s : unitInterval), T (e (z, s)) = e (z * Circle.exp (2 * Real.pi * (s : ℝ)), s)) ∧
      C = range fun z : Circle => e (z, ⟨1 / 2, by norm_num, by norm_num⟩)

/-- **Unlabelled claim [weaker]** (Ch. 3 §3.2.4, IT1:2008). Applying the Dehn twist `T_j` along `L_j` to the marking changes the
twisting parameter `θ̃_j` by `2π` (by `+2π` or `-2π` according to the orientation of the twist; IT does not fix the
orientation of `T_j` in the text) and leaves the lengths `ℓ_k` and the twisting parameters `θ̃_k`, `k ≠ j`, unchanged. -/
theorem para3_2_4 {g : ℕ} (hg : 1 < g) [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hΓ : IsFuchsian Γ₀) (hfree : ActsFreely Γ₀) (hp : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g)
    {L : Fin (3 * g - 3) → Loop S₀} (hL : IsDecomposingSystemLoops Γ₀ p₀ L) {x : S₀}
    {σg σa σb : Fin (3 * g - 3) → Path x x} (hD : IsAdjacentPantsDatum Γ₀ p₀ L σg σa σb) (ℓ θ : Fin (3 * g - 3) → FC g → ℝ)
    (hℓ : ∀ j (m : MarkedRS S₀) (c : FC g), IsFrickeCoordsIT p₀ G m c → markedLength m (L j) (ℓ j c))
    (hθ : ∀ j (m : MarkedRS S₀) (c : FC g), IsFrickeCoordsIT p₀ G m c → IsTwistAngleIT m (σg j) (σa j) (σb j) (θ j c))
    (hθc : ∀ j, ContinuousOn (θ j) (frickeSpaceIT p₀ G)) (j : Fin (3 * g - 3)) (T : S₀ ≃ₜ S₀)
    (hT : IsDehnTwist T (range ((L j).2 : unitInterval → S₀))) (m : MarkedRS S₀)
    (hqc : IsQCRS (T.trans m.marking)) (c c' : FC g) (hc : IsFrickeCoordsIT p₀ G m c)
    (hc' : IsFrickeCoordsIT p₀ G ⟨m.X, T.trans m.marking, hqc⟩ c') :
    (∀ k, ℓ k c' = ℓ k c) ∧ (θ j c' = θ j c + 2 * Real.pi ∨ θ j c' = θ j c - 2 * Real.pi) ∧
      ∀ k, k ≠ j → θ k c' = θ k c := by
  sorry

/-- **Theorem 3.11 (Brouwer's invariance of domain)** (Ch. 3 §3.2.4). Let `n ≥ 2` and `φ : ℝⁿ → ℝⁿ` a continuous injection.
Then `D = φ(ℝⁿ)` is a domain (open and connected) and `φ` is a homeomorphism of `ℝⁿ` onto `D`. Near misses (dimension 2
only): `LiZhongQC.isOpen_image_of_continuousOn_injOn`, `LehtoVirtanen1973.invariance_of_domains`. -/
theorem thm3_11 {n : ℕ} (hn : 2 ≤ n) {φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hc : Continuous φ)
    (hi : Function.Injective φ) : IsOpen (range φ) ∧ IsConnected (range φ) ∧ Topology.IsOpenEmbedding φ := by
  sorry

/-- **Fenchel–Nielsen deformation** (Ch. 3 §3.2.4, IT1:2027): the curve `ξ ↦ Ψ̃⁻¹(a₁, …, a_N, α₁, …, α_{j-1}, ξ, α_{j+1}, …)`
in `F_g`, as a relation: `path ξ ∈ F_g` and `Ψ̃(path ξ) = (a, α with α_j replaced by ξ)`. -/
def IsFNDeformationPath {g : ℕ} (F : Set (FC g)) (Ψ : FC g → (Fin (3 * g - 3) → ℝ) × (Fin (3 * g - 3) → ℝ))
    (a α : Fin (3 * g - 3) → ℝ) (j : Fin (3 * g - 3)) (path : ℝ → FC g) : Prop :=
  ∀ ξ : ℝ, path ξ ∈ F ∧ Ψ (path ξ) = (a, Function.update α j ξ)

end ImayoshiTaniguchi1992
