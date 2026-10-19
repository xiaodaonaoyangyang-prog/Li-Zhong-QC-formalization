import References.FarkasKra1992.Ch04.S06_ExceptionalSurfaces
import References.GardinerLakic2000.Ch02.S09_FundamentalDomains
import LiZhongQC.Ch09.S31_FiniteType

/-!
# Farkas–Kra, Chapter IV §9: Discontinuous groups and branched coverings

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. IV §9 (`full.md` FK2:1652–2288).

Conventions: as in `Ch04/S05_Uniformization` and `Ch04/S06_ExceptionalSurfaces`. `G ⊂ SL(2, ℂ)` is a group of Möbius
transformations; the orbit space `D/G` of a connected open `G`-invariant `D ⊆ Ω(G)` is given by an orbit projection
`π : D → N` onto a Riemann surface `N` (`IsOrbitProjection`). The order of a stabilizer is taken in
`PSL(2, ℂ) = SL(2, ℂ)/±I` (`stabilizerOrder`; it is finite on `Ω(G)`). Surfaces of finite type are those of
`LiZhongQC.IsFiniteType S g n 0` (a compact surface of genus `g` minus `n` points); FK's *genus* of `M` is the genus
of the compact surface `M̌`. A *puncture* is `IsPuncture`; the signature and the characteristic are
`HasSignature` and `signatureChar`, with `1/∞ = 0`.

* IV.9.1 (finite type, genus) — exists: `LiZhongQC.IsFiniteType`
* IV.9.1 (puncture) — `IsPuncture`
* IV.9.1 (ramification index of the orbit projection) — `stabilizerOrder`
* IV.9.1 (finite type over `D`) — `IsFiniteTypeOver`
* IV.9.1 (signature) — `HasSignature`
* IV.9.1 (characteristic) — `signatureChar`
* Definition IV.9.2 (fundamental domain) — `IsAnalyticArc`, `IsFundamentalDomainFK`
* Proposition IV.9.2 — `prop4_9_2`
* Definition IV.9.2 (Fuchsian equivalent) — `ActsDiscontinuouslyAt`, `IsFuchsianEquivalent`
* IV.9.2 (properties of the Fuchsian equivalent) — `para4_9_2_a`, `para4_9_2_b`, `para4_9_2_c`
* IV.9.3 (discontinuous groups on `ℂ̂`) — `para4_9_3`
* Lemma IV.9.4 — `lemma4_9_4`
* Corollary IV.9.4 — `cor4_9_4`
* IV.9.5 (discontinuous groups on `ℂ`) — `para4_9_5`
* Lemma IV.9.7 — `lemma4_9_7`
* Definition IV.9.7 (disc corresponding to a puncture) — `IsDiscCorrespondingToPuncture`
* Lemma IV.9.8 — `lemma4_9_8`
* Lemma IV.9.9 — `lemma4_9_9`
* Theorem IV.9.10 — `thm4_9_10`
* Corollary IV.9.10, part 1 — `IsFuchsianOn`, `cor4_9_10_a`, `ParabolicFixedPoints`, `cor4_9_10_b`
* Corollary IV.9.10, part 2 — `cor4_9_10_c`
* Theorem IV.9.11 — `thm4_9_11`
* Corollary IV.9.11 (i) — `cor4_9_11_a`
* Corollary IV.9.11 (ii) — `cor4_9_11_b`
* Corollary IV.9.11 (iii) — `cor4_9_11_c`
* Theorem IV.9.12 (existence) — `thm4_9_12_a`
* Theorem IV.9.12 (uniqueness) — `thm4_9_12_b`
* Theorem IV.9.12 (the type of `M̃` and the characteristic) — `thm4_9_12_c`

Omitted (U−): IV.9.6 (no precise claim), the Exercises, the Remark after IV.9.12.
-/

open scoped Manifold ContDiff MatrixGroups Topology References
open Set Filter

noncomputable section

namespace FarkasKra1992

open LiZhongQC (mobiusSL toExt limitSet IsMobius slRealToComplex IsBiholomorphic RSConformallyEquivalent
  IsFiniteType HasGenus)
open Lehto1987 (discontinuitySet IsKleinian IsInvariantDomain IsParabolicMob IsHyperbolicMob)
open References (RiemannSphere)

/-- The canonical map `SL(2, ℂ) → PSL(2, ℂ) = SL(2, ℂ)/±I` (helper). -/
abbrev toPSL : SL(2, ℂ) →* SL(2, ℂ) ⧸ Subgroup.center SL(2, ℂ) := QuotientGroup.mk' (Subgroup.center SL(2, ℂ))

/-- **Order of the stabilizer** (Ch. IV §9.1, ramification index). The number of elements of `G ⊂ PSL(2, ℂ)` fixing
the point `y`. Modelling: this is the ramification index of the orbit projection at `y` (the order of the
cyclic stabilizer). Junk value `0` for an infinite stabilizer; only used at points of `Ω(G)`, where stabilizers are
finite. -/
def stabilizerOrder (G : Subgroup SL(2, ℂ)) (y : RiemannSphere) : ℕ :=
  (toPSL '' {g | g ∈ G ∧ mobiusSL g y = y}).ncard

/-- **Puncture** (Ch. IV §9.1). A *puncture* on a Riemann surface `N` is a domain `D₀ ⊂ N` conformally equivalent to
`{z ; 0 < |z| < 1}` such that every sequence `z_n → 0` is discrete on `N` (has no accumulation point in `N`). The
puncture is identified with `z = 0`. Modelling: `D₀` is open, `φ : D₀ → Δ*` is a biholomorphic homeomorphism, and
for every compact `K ⊂ N` the points `φ⁻¹(z)` lie outside `K` for `|z|` small. -/
def IsPuncture {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω N] (D₀ : Set N) : Prop :=
  ∃ hD : IsOpen D₀, ∃ φ : ↥(⟨D₀, hD⟩ : TopologicalSpace.Opens N) ≃ₜ ↥Forster1981.punctUnitDisc,
    IsBiholomorphic (φ : _ → _) ∧ ∀ K : Set N, IsCompact K → ∃ ε > 0, ∀ z : ↥Forster1981.punctUnitDisc,
      ‖(z : ℂ)‖ < ε → ((φ.symm z : ↥(⟨D₀, hD⟩ : TopologicalSpace.Opens N)) : N) ∉ K

/-- **`G` of finite type over `D`** (Ch. IV §9.1). `G` is a Kleinian group, `D` is a connected, open, `G`-invariant
subset of `Ω(G)`, `π : D → N` is the orbit projection, `D/G = N` is of finite type, and `π` is ramified over only
finitely many points. Modelling: "ramified over `x`" = some point of `π⁻¹(x)` has a non-trivial stabilizer. -/
def IsFiniteTypeOver {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω N] (G : Subgroup SL(2, ℂ))
    (D : TopologicalSpace.Opens RiemannSphere) (π : D → N) : Prop :=
  IsKleinian G ∧ (D : Set RiemannSphere) ⊆ discontinuitySet G ∧ (∀ g ∈ G, mobiusSL g '' (D : Set RiemannSphere) = D) ∧
    IsConnected (D : Set RiemannSphere) ∧ IsOrbitProjection G D π ∧ (∃ p n : ℕ, IsFiniteType N p n 0) ∧
    {x : N | ∃ y : D, π y = x ∧ 2 ≤ stabilizerOrder G y}.Finite

/-- **Signature** (Ch. IV §9.1). `G` is of finite type over `D` and its *signature* with respect to `D` is
`(p; ν₁, …, ν_n)`: `p` is the genus of `D/G`, and `ν₁ ≤ … ≤ ν_n` (in `ℕ∞`, `2 ≤ ν_j ≤ ∞`) are the ramification
indices of the ramified points of `π`, with `ν = ∞` for each of the punctures of `D/G`. Modelling: the punctures
of `D/G = N` are the `n` points at infinity of the finite type structure; since `π` is ramified over finitely many
points, a deleted neighbourhood of every puncture consists of images of ordinary points. -/
def HasSignature {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω N] (G : Subgroup SL(2, ℂ))
    (D : TopologicalSpace.Opens RiemannSphere) (π : D → N) (p : ℕ) (ν : List ℕ∞) : Prop :=
  IsFiniteTypeOver G D π ∧ ∃ n : ℕ, IsFiniteType N p n 0 ∧ ∃ (R : Finset N) (idx : N → ℕ),
    (∀ y : D, π y ∈ R ↔ 2 ≤ stabilizerOrder G y) ∧ (∀ y : D, π y ∈ R → idx (π y) = stabilizerOrder G y) ∧
    (ν : Multiset ℕ∞) = R.val.map (fun x => (idx x : ℕ∞)) + Multiset.replicate n ⊤ ∧
    ν.Pairwise (· ≤ ·)

/-- **Characteristic** (Ch. IV §9.1). For a signature `(p; ν₁, …, ν_n)`: `χ = 2p − 2 + Σ_j (1 − 1/ν_j)` in `ℚ`,
where `1/∞ = 0`. (FK put `χ = ∞` if `G` is not of finite type over `D`; this is not needed in the statements.) -/
def signatureChar (p : ℕ) (ν : List ℕ∞) : ℚ :=
  2 * p - 2 + (ν.map fun v => 1 - (if v = ⊤ then 0 else 1 / (v.toNat : ℚ))).sum

/-- **Analytic arc** (Ch. IV §9.2, helper). An analytic arc in `ℂ̂`: the image of `[0, 1]` under a regular injective
real-analytic map `γ` into `ℂ`, after a Möbius transformation (so that arcs through `∞` are included). -/
def IsAnalyticArc (A : Set RiemannSphere) : Prop :=
  ∃ T : RiemannSphere → RiemannSphere, IsMobius T ∧ ∃ γ : ℝ → ℂ, AnalyticOnNhd ℝ γ (Icc 0 1) ∧
    InjOn γ (Icc 0 1) ∧ (∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0) ∧ T '' A = toExt (γ '' Icc 0 1)

/-- **Fundamental domain** (Ch. IV §9.2). Let `G` be a Kleinian group and `D ⊂ Ω(G)` a `G`-invariant open set. A
*fundamental domain for `G` with respect to `D`* is an open subset `ω` of `D` such that (i) no two points of `ω` are
equivalent under `G`; (ii) every point of `D` is `G`-equivalent to at least one point of `Cl ω`; (iii) the relative
boundary `δω` of `ω` in `D` consists of piecewise analytic arcs (a locally finite union of analytic arcs); (iv) for
every side `c` of `δω` there is an arc `c' ⊂ δω` and an element `g ∈ G` with `g c = c'`.
**[reading]** in (iv) `g` is not the identity of `PSL(2, ℂ)` (`g ∉ center`): with `g = 1`, `c' = c` the printed
condition would be vacuous; the intended content is the side pairing of the boundary arcs.
[CORRECTION, FK-fix3] (iv) is required for the arcs `A ∈ F` of the (locally finite) family of sides in (iii), not for every analytic
arc inside `δω`: an analytic arc through an accidental vertex (two sides meeting at angle `π`) lies on no single side and is
mapped into `δω` by no single `g` (AUDIT5_FK N3, AUDITR2_FK R2FK-5).
Near misses: `LiZhongQC.IsFundamentalDomainH` (a specific domain), `GardinerLakic2000.hypArea` (area only). -/
def IsFundamentalDomainFK (G : Subgroup SL(2, ℂ)) (D W : Set RiemannSphere) : Prop :=
  IsOpen W ∧ W ⊆ D ∧ (∀ x ∈ W, ∀ y ∈ W, x ≠ y → ∀ g ∈ G, mobiusSL g x ≠ y) ∧
    (∀ z ∈ D, ∃ g ∈ G, mobiusSL g z ∈ closure W) ∧
    ∃ F : Set (Set RiemannSphere), (∀ A ∈ F, IsAnalyticArc A) ∧ frontier W ∩ D = ⋃₀ F ∧
      (∀ x ∈ D, ∃ V ∈ 𝓝 x, {A ∈ F | (A ∩ V).Nonempty}.Finite) ∧
      ∀ A ∈ F, ∃ g ∈ G, g ∉ Subgroup.center SL(2, ℂ) ∧ mobiusSL g '' A ⊆ frontier W ∩ D

/-- **Proposition IV.9.2** (Ch. IV §9.2). Every Kleinian group `G` has a fundamental domain (with respect to
`Ω(G)`). -/
theorem prop4_9_2 {G : Subgroup SL(2, ℂ)} (hG : IsKleinian G) :
    ∃ W, IsFundamentalDomainFK G (discontinuitySet G) W := by
  sorry

/-- **Acting discontinuously at a point** (Ch. IV §9.2, after IV.5.1; helper). A group `Γ` of homeomorphisms of a
space acts (properly) discontinuously at `x` if the isotropy subgroup `Γ_x` is finite and there is a neighbourhood
`U` of `x` with `g(U) = U` for `g ∈ Γ_x` and `g(U) ∩ U = ∅` for `g ∈ Γ ∖ Γ_x`. This is FK's (5.1.1), (5.1.2) for a
general group of automorphisms. -/
def ActsDiscontinuouslyAt {X : Type*} [TopologicalSpace X] (Γ : Subgroup (X ≃ₜ X)) (x : X) : Prop :=
  {γ | γ ∈ Γ ∧ γ x = x}.Finite ∧ ∃ U ∈ 𝓝 x, (∀ γ ∈ Γ, γ x = x → γ '' U = U) ∧
    ∀ γ ∈ Γ, γ x ≠ x → γ '' U ∩ U = ∅

/-- **Fuchsian equivalent** (Ch. IV §9.2, Definition). Let `G` be a Kleinian group, `D` a `G`-invariant domain,
`ρ : D̃ → D` a holomorphic universal covering map. The *Fuchsian equivalent* of `G` with respect to `D` is
`Γ = {γ ∈ Aut D̃ ; ρ ∘ γ = g ∘ ρ for some g ∈ G}`.
Modelling: a predicate on the subgroup `Γ` of the homeomorphism group of `D̃` (the book's group is determined by it). -/
def IsFuchsianEquivalent {Dt : Type} [TopologicalSpace Dt] [ChartedSpace ℂ Dt] {D : TopologicalSpace.Opens RiemannSphere}
    (G : Subgroup SL(2, ℂ)) (ρ : Dt → D) (Γ : Subgroup (Dt ≃ₜ Dt)) : Prop :=
  ∀ γ : Dt ≃ₜ Dt, γ ∈ Γ ↔ IsBiholomorphic (γ : Dt → Dt) ∧
    ∃ g ∈ G, ∀ x, (ρ (γ x) : RiemannSphere) = mobiusSL g (ρ x : RiemannSphere)

/-- **Unlabelled** (Ch. IV §9.2, FK2:1712–1713). `G` acts discontinuously on `D` if and only if its Fuchsian
equivalent `Γ` acts discontinuously on `D̃`.
Modelling: "`G` acts discontinuously on `D`" = every point of `D` is in `Ω(G)`. -/
theorem para4_9_2_a {Dt : Type} [TopologicalSpace Dt] [T2Space Dt] [ConnectedSpace Dt] [ChartedSpace ℂ Dt]
    [IsManifold 𝓘(ℂ) ω Dt] [SimplyConnectedSpace Dt] {G : Subgroup SL(2, ℂ)}
    {D : TopologicalSpace.Opens RiemannSphere} (hD : IsConnected (D : Set RiemannSphere))
    (hinv : ∀ g ∈ G, mobiusSL g '' (D : Set RiemannSphere) = D) {ρ : Dt → D}
    (hρ : Forster1981.IsUniversalCovering ρ) (hρa : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ρ) {Γ : Subgroup (Dt ≃ₜ Dt)}
    (hΓ : IsFuchsianEquivalent G ρ Γ) :
    (D : Set RiemannSphere) ⊆ discontinuitySet G ↔ ∀ x : Dt, ActsDiscontinuouslyAt Γ x := by
  sorry

/-- **Unlabelled** (Ch. IV §9.2, FK2:1712–1722). The map `ρ* : Γ → G` is onto: for every `g ∈ G` there is `γ ∈ Γ`
with `ρ ∘ γ = g ∘ ρ` (the homomorphism `ρ*` sends `γ` to the unique `g ∈ PSL(2, ℂ)` with `ρ ∘ γ = g ∘ ρ`; the
exact sequence `1 → ker ρ* → Γ → G → 1`). -/
theorem para4_9_2_b {Dt : Type} [TopologicalSpace Dt] [T2Space Dt] [ConnectedSpace Dt] [ChartedSpace ℂ Dt]
    [IsManifold 𝓘(ℂ) ω Dt] [SimplyConnectedSpace Dt] {G : Subgroup SL(2, ℂ)}
    {D : TopologicalSpace.Opens RiemannSphere} (hD : IsConnected (D : Set RiemannSphere))
    (hinv : ∀ g ∈ G, mobiusSL g '' (D : Set RiemannSphere) = D) {ρ : Dt → D}
    (hρ : Forster1981.IsUniversalCovering ρ) (hρa : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ρ) {Γ : Subgroup (Dt ≃ₜ Dt)}
    (hΓ : IsFuchsianEquivalent G ρ Γ) :
    ∀ g ∈ G, ∃ γ ∈ Γ, ∀ x, (ρ (γ x) : RiemannSphere) = mobiusSL g (ρ x : RiemannSphere) := by
  sorry

/-- **Unlabelled** (Ch. IV §9.2, FK2:1712). `D̃/Γ ≅ D/G`: if `π : D → N` is the orbit projection of `G`, then
`π ∘ ρ : D̃ → N` is the quotient projection of `D̃` by the action of `Γ`. -/
theorem para4_9_2_c {Dt N : Type} [TopologicalSpace Dt] [T2Space Dt] [ConnectedSpace Dt] [ChartedSpace ℂ Dt]
    [IsManifold 𝓘(ℂ) ω Dt] [SimplyConnectedSpace Dt] [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω N]
    {G : Subgroup SL(2, ℂ)} {D : TopologicalSpace.Opens RiemannSphere} (hD : IsConnected (D : Set RiemannSphere))
    (hinv : ∀ g ∈ G, mobiusSL g '' (D : Set RiemannSphere) = D) {ρ : Dt → D}
    (hρ : Forster1981.IsUniversalCovering ρ) (hρa : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ρ) {Γ : Subgroup (Dt ≃ₜ Dt)}
    (hΓ : IsFuchsianEquivalent G ρ Γ) {π : D → N} (hπ : IsOrbitProjection G D π) :
    IsRelProjection (π ∘ ρ) fun x y => ∃ γ ∈ Γ, γ x = y := by
  sorry

/-- **Unlabelled** (Ch. IV §9.3, FK2:1742–1830). Let `G` be a discontinuous group with `Ω(G) = ℂ ∪ {∞}`. Then `G` is
finite, of order `N` (in `PSL(2, ℂ)`), the genus of `ℂ̂/G` is `0`, the characteristic is `χ = −2/N < 0`, and the
signature `(p; ν₁, …, ν_n)` and the order `N` are, with `2 ≤ ν`, one of: `(0; —)` with `N = 1`; `(0; ν, ν)` with
`N = ν`; `(0; 2, 2, ν)` with `N = 2ν`; `(0; 2, 3, 3)` with `N = 12`; `(0; 2, 3, 4)` with `N = 24`;
`(0; 2, 3, 5)` with `N = 60`.
Modelling: `D = ℂ̂` and `Ω(G) = ℂ̂`; the signature relative to an orbit projection `π : ℂ̂ → N`. -/
theorem para4_9_3 {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω N] {G : Subgroup SL(2, ℂ)}
    (hΩ : discontinuitySet G = univ) {π : (⊤ : TopologicalSpace.Opens RiemannSphere) → N} {p : ℕ}
    {ν : List ℕ∞} (hs : HasSignature G ⊤ π p ν) :
    (toPSL '' (G : Set SL(2, ℂ))).Finite ∧ p = 0 ∧
      signatureChar p ν = -2 / (toPSL '' (G : Set SL(2, ℂ))).ncard ∧
      ((ν = [] ∧ (toPSL '' (G : Set SL(2, ℂ))).ncard = 1) ∨
        (∃ v : ℕ, 2 ≤ v ∧ ((ν = [v, v] ∧ (toPSL '' (G : Set SL(2, ℂ))).ncard = v) ∨
          (ν = [2, 2, v] ∧ (toPSL '' (G : Set SL(2, ℂ))).ncard = 2 * v))) ∨
        (ν = [2, 3, 3] ∧ (toPSL '' (G : Set SL(2, ℂ))).ncard = 12) ∨
        (ν = [2, 3, 4] ∧ (toPSL '' (G : Set SL(2, ℂ))).ncard = 24) ∨
        (ν = [2, 3, 5] ∧ (toPSL '' (G : Set SL(2, ℂ))).ncard = 60)) := by
  sorry

/-- **Lemma IV.9.4** (Ch. IV §9.4). Let `A` and `B` be two non-parabolic Möbius transformations with exactly one
fixed point in common. Then `C = A⁻¹ ∘ B ∘ A ∘ B⁻¹` is parabolic. -/
theorem lemma4_9_4 (g h : SL(2, ℂ)) (hg : ¬ IsParabolicMob g) (hh : ¬ IsParabolicMob h)
    (hc : (mobiusFixSet g ∩ mobiusFixSet h).encard = 1) : IsParabolicMob (g⁻¹ * h * g * h⁻¹) := by
  sorry

/-- **Corollary IV.9.4** (Ch. IV §9.4). Let `G` be a group of Möbius transformations and `z ∈ ℂ ∪ {∞}`. If the
stabilizer `G_z` of `z` in `G` is finite, it is cyclic.
Modelling: `G_z` is taken in `PSL(2, ℂ)` (the image of `{g ∈ G ; g z = z}`). -/
theorem cor4_9_4 (G : Subgroup SL(2, ℂ)) (z : RiemannSphere)
    (hfin : (toPSL '' {g | g ∈ G ∧ mobiusSL g z = z}).Finite) :
    ∃ g₀ ∈ G, mobiusSL g₀ z = z ∧ ∀ g ∈ G, mobiusSL g z = z → ∃ n : ℤ, toPSL g = toPSL g₀ ^ n := by
  sorry

/-- **Unlabelled** (Ch. IV §9.5, FK2:1854–1963). The discontinuous groups `G` acting on `ℂ` (not on `ℂ ∪ {∞}`, i.e.
`ℂ` is an invariant component of `Ω(G)`) of finite type over `ℂ` have characteristic `χ = 0`, and their signatures
`(p; ν₁, …, ν_n)` are exactly `(0; ∞, ∞)`, `(0; 2, 2, ∞)`, `(1; —)`, `(0; 2, 2, 2, 2)`, `(0; 2, 3, 6)`, `(0; 2, 4, 4)`,
`(0; 3, 3, 3)`.
Modelling: `D = ℂ` is an invariant component of `Ω(G)`; the listing is of the possible signatures (not of the
existence of each; existence is IV.9.12). -/
theorem para4_9_5 {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω N] {G : Subgroup SL(2, ℂ)}
    (hD : IsInvariantDomain G (finitePlaneOpens : Set RiemannSphere))
    {π : finitePlaneOpens → N} {p : ℕ} {ν : List ℕ∞} (hs : HasSignature G finitePlaneOpens π p ν) :
    signatureChar p ν = 0 ∧
      ((p = 0 ∧ ν = [⊤, ⊤]) ∨ (p = 0 ∧ ν = [2, 2, ⊤]) ∨ (p = 1 ∧ ν = []) ∨ (p = 0 ∧ ν = [2, 2, 2, 2]) ∨
        (p = 0 ∧ ν = [2, 3, 6]) ∨ (p = 0 ∧ ν = [2, 4, 4]) ∨ (p = 0 ∧ ν = [3, 3, 3])) := by
  sorry

/-- **Fuchsian group acting on a disc** (Ch. IV §9.7, helper). A Fuchsian group `G` operating on the disc or half
plane `D`: a Kleinian group leaving `D` invariant (IV.5.4). -/
def IsFuchsianOn (G : Subgroup SL(2, ℂ)) (D : Set RiemannSphere) : Prop :=
  IsKleinian G ∧ IsGeneralizedDisc D ∧ ∀ g ∈ G, mobiusSL g '' D = D

/-- **Disc corresponding to a puncture** (Ch. IV §9.7, Definition). For a Fuchsian group `G` acting on `U` with
orbit projection `π : U → N`: the disc (half plane) `D̃ ⊂ U` corresponding to the deleted neighbourhood `D'` of a
puncture is a disc such that `D' = π(D̃) ≅ D̃/G₀`, where `G₀` is the cyclic group generated by a parabolic element
`T ∈ G`, and two points of `D̃` are equivalent under `G` if and only if they are equivalent under `G₀`. -/
def IsDiscCorrespondingToPuncture {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω N] (G : Subgroup SL(2, ℂ))
    (π : upperHalfPlaneOpens → N) (D' : Set N) (Dt : Set RiemannSphere) : Prop :=
  IsPuncture D' ∧ IsGeneralizedDisc Dt ∧ Dt ⊆ (upperHalfPlaneOpens : Set RiemannSphere) ∧
    π '' {x | (x : RiemannSphere) ∈ Dt} = D' ∧
    ∃ T ∈ G, IsParabolicMob T ∧ ∀ x y : upperHalfPlaneOpens, (x : RiemannSphere) ∈ Dt → (y : RiemannSphere) ∈ Dt →
      (π x = π y ↔ ∃ n : ℤ, mobiusSL (T ^ n) (x : RiemannSphere) = (y : RiemannSphere))

/-- **Lemma IV.9.7** (Ch. IV §9.7). Let `G` be a Fuchsian group operating on the upper half plane `U`. Assume that `P`
is a puncture on `U/G` (and that the natural projection `π` is unramified over a deleted neighbourhood of `P`).
Then there exists a deleted neighbourhood `D` of `P` in `U/G`, a disc `D̃` in `U`, and a parabolic element `T ∈ G`
such that `D ≅ D̃/G₀`, where `G₀` is the cyclic group generated by `T`, and two points in `D̃` are equivalent under
`G` if and only if they are equivalent under `G₀`.
Modelling: `P` is represented by a puncture neighbourhood `D₀` over which `π` is unramified; `D ⊂ D₀`. -/
theorem lemma4_9_7 {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω N] {G : Subgroup SL(2, ℂ)}
    (hG : IsFuchsianOn G (upperHalfPlaneOpens : Set RiemannSphere)) {π : upperHalfPlaneOpens → N}
    (hπ : IsOrbitProjection G upperHalfPlaneOpens π) {D₀ : Set N} (hP : IsPuncture D₀)
    (hun : ∀ y, π y ∈ D₀ → stabilizerOrder G y = 1) :
    ∃ (D' : Set N) (Dt : Set RiemannSphere), D' ⊆ D₀ ∧ IsDiscCorrespondingToPuncture G π D' Dt := by
  sorry

/-- **Lemma IV.9.8** (Ch. IV §9.8). Let `A(z) = (az + b)(cz + d)⁻¹` with `ad − bc = 1` and `T(z) = z + 1`. Then the
group generated by `A` and `T` is not discrete if `0 < |c| < 1`.
Modelling: `A, T ∈ SL(2, ℂ)`, `T` the matrix `[[1, 1], [0, 1]]`. -/
theorem lemma4_9_8 (A T : SL(2, ℂ)) (hT : T 0 0 = 1 ∧ T 0 1 = 1 ∧ T 1 0 = 0 ∧ T 1 1 = 1)
    (hc : 0 < ‖A 1 0‖ ∧ ‖A 1 0‖ < 1) : ¬ IsDiscreteGroup (Subgroup.closure {A, T}) := by
  sorry

/-- **Lemma IV.9.9** (Ch. IV §9.9). Let `G` be a Fuchsian group operating on the upper half plane `U`. Assume that `G`
contains a parabolic element `T` with fixed point `x ∈ ℝ ∪ {∞}`. Then `G_x`, the stabilizer of `x` in `G`, is
infinite cyclic. Modelling: `G_x` is taken in `PSL(2, ℂ)`. -/
theorem lemma4_9_9 {G : Subgroup SL(2, ℂ)} (hG : IsFuchsianOn G (upperHalfPlaneOpens : Set RiemannSphere))
    {T : SL(2, ℂ)} (hT : T ∈ G) (hp : IsParabolicMob T) {x : RiemannSphere} (hx : mobiusSL T x = x) :
    (toPSL '' {g | g ∈ G ∧ mobiusSL g x = x}).Infinite ∧
      ∃ g₀ ∈ G, mobiusSL g₀ x = x ∧ ∀ g ∈ G, mobiusSL g x = x → ∃ n : ℤ, toPSL g = toPSL g₀ ^ n := by
  sorry

/-- **Theorem IV.9.10** (Ch. IV §9.10). Let `G` be a Fuchsian group operating on the upper half plane `U`. Let
`T(z) = z + 1` be an element of `G`, the generator of the stabilizer of `∞`, `G_∞`. If `A ∈ G ∖ G_∞`, then
`A U₁ ∩ U₁ = ∅`, where `U₁ = {z ; Im z > 1}`. -/
theorem thm4_9_10 {G : Subgroup SL(2, ℂ)} (hG : IsFuchsianOn G (upperHalfPlaneOpens : Set RiemannSphere))
    {T : SL(2, ℂ)} (hTG : T ∈ G) (hT : T 0 0 = 1 ∧ T 0 1 = 1 ∧ T 1 0 = 0 ∧ T 1 1 = 1)
    (hgen : ∀ g ∈ G, mobiusSL g LiZhongQC.extInf = LiZhongQC.extInf → ∃ n : ℤ, toPSL g = toPSL T ^ n) :
    ∀ A ∈ G, mobiusSL A LiZhongQC.extInf ≠ LiZhongQC.extInf →
      mobiusSL A '' toExt {z | 1 < z.im} ∩ toExt {z | 1 < z.im} = ∅ := by
  sorry

/-- **Corollary IV.9.10(a)** (Ch. IV §9.10, Corollary 1). Let `G` be a Fuchsian group operating on `U` (with orbit
projection `π : U → N`). If `G` contains a parabolic element, then `U/G` contains a puncture over which `π` is
unramified. -/
theorem cor4_9_10_a {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω N] {G : Subgroup SL(2, ℂ)}
    (hG : IsFuchsianOn G (upperHalfPlaneOpens : Set RiemannSphere)) {π : upperHalfPlaneOpens → N}
    (hπ : IsOrbitProjection G upperHalfPlaneOpens π) {T : SL(2, ℂ)} (hTG : T ∈ G) (hp : IsParabolicMob T) :
    ∃ D₀ : Set N, IsPuncture D₀ ∧ ∀ y, π y ∈ D₀ → stabilizerOrder G y = 1 := by
  sorry

/-- The set of parabolic fixed points of a group of Möbius transformations (helper). -/
abbrev ParabolicFixedPoints (G : Subgroup SL(2, ℂ)) : Type :=
  {x : RiemannSphere // ∃ T ∈ G, IsParabolicMob T ∧ mobiusSL T x = x}

/-- **Corollary IV.9.10(b)** (Ch. IV §9.10, Corollary 1, second part). The punctures on `U/G` (over which `π` is
unramified, as in the Remark after IV.9.10) are in one-to-one correspondence with the conjugacy classes of parabolic
subgroups of `G`.
**[reading]** printed "conjugacy classes of parabolic elements"; a puncture corresponds to the cyclic parabolic
stabilizer `G_x`, i.e. to the `G`-orbit of a parabolic fixed point `x` (all powers of a generator are parabolic).
Modelling: punctures are identified as germs (`D₀`, `D₀'` define the same puncture when some puncture
neighbourhood lies in both): there is an assignment `x ↦ Φ x` of an unramified puncture neighbourhood to every
parabolic fixed point such that `x`, `x'` are `G`-equivalent exactly when `Φ x`, `Φ x'` define the same puncture, and
every unramified puncture arises. -/
theorem cor4_9_10_b {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω N] {G : Subgroup SL(2, ℂ)}
    (hG : IsFuchsianOn G (upperHalfPlaneOpens : Set RiemannSphere)) {π : upperHalfPlaneOpens → N}
    (hπ : IsOrbitProjection G upperHalfPlaneOpens π) :
    ∃ Φ : ParabolicFixedPoints G → Set N,
      (∀ x, IsPuncture (Φ x) ∧ ∀ y, π y ∈ Φ x → stabilizerOrder G y = 1) ∧
      (∀ x x' : ParabolicFixedPoints G, (∃ g ∈ G, mobiusSL g (x : RiemannSphere) = (x' : RiemannSphere)) ↔
        ∃ D₁ : Set N, IsPuncture D₁ ∧ D₁ ⊆ Φ x ∩ Φ x') ∧
      ∀ D₀ : Set N, IsPuncture D₀ → (∀ y, π y ∈ D₀ → stabilizerOrder G y = 1) →
        ∃ x, ∃ D₁ : Set N, IsPuncture D₁ ∧ D₁ ⊆ D₀ ∩ Φ x := by
  sorry

/-- **Corollary IV.9.10(c)** (Ch. IV §9.10, Corollary 2). Let `G` be a Fuchsian group. If `G` is the covering group of
a compact Riemann surface of genus `p ≥ 2`, then `G` contains only hyperbolic elements.
Modelling: `G` acts on `U` with orbit projection `π : U → N`, `N` compact of genus `p ≥ 2`, and `G` acts freely
(covering group); the elements are those other than `±I`. -/
theorem cor4_9_10_c {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω N] [CompactSpace N] {p : ℕ} (hp : 2 ≤ p) (hN : HasGenus N p) {G : Subgroup SL(2, ℂ)}
    (hG : IsFuchsianOn G (upperHalfPlaneOpens : Set RiemannSphere)) {π : upperHalfPlaneOpens → N}
    (hπ : IsOrbitProjection G upperHalfPlaneOpens π)
    (hfree : ∀ g ∈ G, g ∉ Subgroup.center SL(2, ℂ) → ∀ z ∈ (upperHalfPlaneOpens : Set RiemannSphere),
      mobiusSL g z ≠ z) :
    ∀ g ∈ G, g ∉ Subgroup.center SL(2, ℂ) → IsHyperbolicMob g := by
  sorry

/-- **Theorem IV.9.11** (Ch. IV §9.11). Let `G` be a Fuchsian group operating on `U` which is of finite type over `U`
with characteristic `χ`. Then `Area(U/G) = 2πχ`.
Modelling: `Area(U/G)` is the hyperbolic area (`GardinerLakic2000.hypArea`, the area form `dx dy / y²` of the metric
`λ_U = 1/y`, FK's normalization) of a fundamental domain `W` of `G` with respect to `U`, which has the same area as
`U/G` since the boundary `δW` is a null set. -/
theorem thm4_9_11 {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω N] {G : Subgroup SL(2, ℂ)}
    (hG : IsFuchsianOn G (upperHalfPlaneOpens : Set RiemannSphere)) {π : upperHalfPlaneOpens → N} {p : ℕ}
    {ν : List ℕ∞} (hs : HasSignature G upperHalfPlaneOpens π p ν) {W : Set RiemannSphere}
    (hW : IsFundamentalDomainFK G (upperHalfPlaneOpens : Set RiemannSphere) W) :
    GardinerLakic2000.hypArea {z : ℂ | (z : RiemannSphere) ∈ W} =
      ENNReal.ofReal (2 * Real.pi * (signatureChar p ν : ℝ)) := by
  sorry

/-- **Corollary IV.9.11(i)** (Ch. IV §9.11). Let `G` be a group of conformal automorphisms of a simply connected
Riemann surface `D` operating discontinuously on `D`, of finite type over `D`. Then `χ < 0` if and only if
`D ≅ ℂ ∪ {∞}`.
**[reading]** `D` is an invariant component of `Ω(G)` (the case of `G` acting on all of `D = ℂ` but with `∞` an
ordinary point, e.g. `G = 1`, `D = ℂ`, has `χ = −1` with a puncture at `∞`, so the printed statement needs this
reading). Modelling: by uniformization `D` is conformally one of `ℂ̂`, `ℂ`, `U`, and `G` is a group of Möbius
transformations preserving `D`; `D` is an open subset of `ℂ̂` with `IsInvariantDomain G D`. -/
theorem cor4_9_11_a {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω N] {G : Subgroup SL(2, ℂ)}
    {D : TopologicalSpace.Opens RiemannSphere} (hD : IsInvariantDomain G (D : Set RiemannSphere))
    [SimplyConnectedSpace D] {π : D → N} {p : ℕ} {ν : List ℕ∞} (hs : HasSignature G D π p ν) :
    signatureChar p ν < 0 ↔ RSConformallyEquivalent D RiemannSphere := by
  sorry

/-- **Corollary IV.9.11(ii)** (Ch. IV §9.11). In the situation of `cor4_9_11_a`: `χ = 0` if and only if
`D ≅ ℂ`. -/
theorem cor4_9_11_b {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω N] {G : Subgroup SL(2, ℂ)}
    {D : TopologicalSpace.Opens RiemannSphere} (hD : IsInvariantDomain G (D : Set RiemannSphere))
    [SimplyConnectedSpace D] {π : D → N} {p : ℕ} {ν : List ℕ∞} (hs : HasSignature G D π p ν) :
    signatureChar p ν = 0 ↔ RSConformallyEquivalent D ℂ := by
  sorry

/-- **Corollary IV.9.11(iii)** (Ch. IV §9.11). In the situation of `cor4_9_11_a`: `χ > 0` if and only if
`D ≅ Δ`. -/
theorem cor4_9_11_c {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω N] {G : Subgroup SL(2, ℂ)}
    {D : TopologicalSpace.Opens RiemannSphere} (hD : IsInvariantDomain G (D : Set RiemannSphere))
    [SimplyConnectedSpace D] {π : D → N} {p : ℕ} {ν : List ℕ∞} (hs : HasSignature G D π p ν) :
    0 < signatureChar p ν ↔ RSConformallyEquivalent D ↥Forster1981.unitDiscOpen := by
  sorry

/-- **Theorem IV.9.12** (Ch. IV §9.12, existence). Let `M` be a Riemann surface and `X = {x₁, x₂, …}` a discrete
sequence on `M` (a closed discrete subset). To each point `x_k` assign `ν_k`, an integer `≥ 2` or `∞`. If `M = ℂ ∪ {∞}`
we exclude (i) `X` is one point and `ν₁ ≠ ∞`, and (ii) `X` consists of two points and `ν₁ ≠ ν₂`. Let
`M' = M ∖ {x_k ; ν_k = ∞}` and `M'' = M ∖ X`. Then there is a simply connected Riemann surface `M̃` and a Kleinian group
`G` of self mappings of `M̃` such that (a) `M̃/G ≅ M'` and `M̃_G/G ≅ M''`, where `M̃_G` is `M̃` with the fixed points of
the elliptic elements of `G` deleted; (b) the natural projection `π : M̃ → M'` is unramified except over the points
`x_k` with `ν_k < ∞`, where `b_π(x̂) = ν_k − 1` for all `x̂ ∈ π⁻¹(x_k)`.
Modelling: `M̃` is `D ∈ {ℂ̂, ℂ, U}` (uniformization); `π : D → M` is holomorphic, open, with fibres the `G`-orbits and
image `M'`; (b) is `stabilizerOrder G y = ν_k` over `x_k` and `= 1` elsewhere, and `M̃_G/G ≅ M''` follows from it.
Here `ν : M → ℕ∞` is read on `X`. -/
theorem thm4_9_12_a {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] {X : Set M} (hX : IsClosed X ∧ DiscreteTopology X) {ν : M → ℕ∞}
    (hν : ∀ x ∈ X, 2 ≤ ν x)
    (hex : ¬ (RSConformallyEquivalent M RiemannSphere ∧
      ((∃ x, X = {x} ∧ ν x ≠ ⊤) ∨ (∃ x y, x ≠ y ∧ X = {x, y} ∧ ν x ≠ ν y)))) :
    ∃ (D : TopologicalSpace.Opens RiemannSphere) (G : Subgroup SL(2, ℂ)) (π : D → M),
      (D = ⊤ ∨ D = finitePlaneOpens ∨ D = upperHalfPlaneOpens) ∧ (∀ g ∈ G, mobiusSL g '' (D : Set RiemannSphere) = D) ∧
      (D : Set RiemannSphere) ⊆ discontinuitySet G ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π ∧ IsOpenMap π ∧ range π = {x | x ∉ X ∨ ν x ≠ ⊤} ∧
      (∀ y z : D, π y = π z ↔ ∃ g ∈ G, mobiusSL g (y : RiemannSphere) = (z : RiemannSphere)) ∧
      ∀ y : D, (π y ∈ X → (stabilizerOrder G y : ℕ∞) = ν (π y)) ∧ (π y ∉ X → stabilizerOrder G y = 1) := by
  sorry

/-- **Theorem IV.9.12** (Ch. IV §9.12, uniqueness). `G` is uniquely determined up to conjugation in the full group of
automorphisms of `M̃`: if `(G, π)` and `(G₁, π₁)` are two groups of Möbius transformations of the same `D ∈ {ℂ̂, ℂ, U}`
with orbit projections onto `M'` as in `thm4_9_12_a`, with the same stabilizer orders over `X`, then there is a
conformal automorphism `A` of `D` with `π₁ ∘ A = π` (so `G₁ = A G A⁻¹`).
Modelling: both groups satisfy the conclusion of `thm4_9_12_a` for the same data. -/
theorem thm4_9_12_b {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] {X : Set M} {ν : M → ℕ∞} {D : TopologicalSpace.Opens RiemannSphere}
    (hD : D = ⊤ ∨ D = finitePlaneOpens ∨ D = upperHalfPlaneOpens) {G G₁ : Subgroup SL(2, ℂ)} {π π₁ : D → M}
    (hG : (∀ g ∈ G, mobiusSL g '' (D : Set RiemannSphere) = D) ∧ (D : Set RiemannSphere) ⊆ discontinuitySet G ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π ∧ IsOpenMap π ∧ range π = {x | x ∉ X ∨ ν x ≠ ⊤} ∧
      (∀ y z : D, π y = π z ↔ ∃ g ∈ G, mobiusSL g (y : RiemannSphere) = (z : RiemannSphere)) ∧
      ∀ y : D, (π y ∈ X → (stabilizerOrder G y : ℕ∞) = ν (π y)) ∧ (π y ∉ X → stabilizerOrder G y = 1))
    (hG₁ : (∀ g ∈ G₁, mobiusSL g '' (D : Set RiemannSphere) = D) ∧ (D : Set RiemannSphere) ⊆ discontinuitySet G₁ ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π₁ ∧ IsOpenMap π₁ ∧ range π₁ = {x | x ∉ X ∨ ν x ≠ ⊤} ∧
      (∀ y z : D, π₁ y = π₁ z ↔ ∃ g ∈ G₁, mobiusSL g (y : RiemannSphere) = (z : RiemannSphere)) ∧
      ∀ y : D, (π₁ y ∈ X → (stabilizerOrder G₁ y : ℕ∞) = ν (π₁ y)) ∧ (π₁ y ∉ X → stabilizerOrder G₁ y = 1)) :
    ∃ A : D ≃ₜ D, IsBiholomorphic (A : D → D) ∧ ∀ y, π₁ (A y) = π y := by
  sorry

/-- **Theorem IV.9.12** (Ch. IV §9.12, the type of `M̃` and the characteristic). The conformality type of `M̃` is
uniquely determined by the characteristic of the data, i.e. by the genus `p` of `M` and the sequence `ν₁, ν₂, …`: if
`χ = 2p − 2 + Σ_j (1 − 1/ν_j)`, then `χ < 0` if and only if `M̃ ≅ ℂ ∪ {∞}`, `χ = 0` if and only if `M̃ ≅ ℂ`, and
`χ > 0` if and only if `M̃ ≅ U`.
**[CORRECTION/reading]** (1) The printed statement is for a compact `M` with finitely many `x_k` (otherwise `χ` is not
the characteristic of `G`: for non-compact `M` the punctures of `M` are not in the data; e.g. `M = ℂ`, `X = ∅` gives
`χ = −2` but `M̃ = ℂ`). (2) The exclusions (i), (ii) for `M = ℂ̂` are not enough: `M = ℂ̂`, `X = {x}`, `ν = ∞` has
`M' = ℂ`, `M̃ = ℂ` and `χ = −1 < 0`; this case is excluded too. Modelling: `M` compact of genus `p`, `X` finite, `(D, G, π)` as in
`thm4_9_12_a`. -/
theorem thm4_9_12_c {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] [CompactSpace M] {p : ℕ} (hM : HasGenus M p) {X : Finset M} {ν : M → ℕ∞}
    (hν : ∀ x ∈ X, 2 ≤ ν x)
    (hex : ¬ (RSConformallyEquivalent M RiemannSphere ∧
      ((∃ x, (X : Set M) = {x}) ∨ (∃ x y, x ≠ y ∧ (X : Set M) = {x, y} ∧ ν x ≠ ν y))))
    {D : TopologicalSpace.Opens RiemannSphere} {G : Subgroup SL(2, ℂ)} {π : D → M}
    (hD : D = ⊤ ∨ D = finitePlaneOpens ∨ D = upperHalfPlaneOpens)
    (hG : (∀ g ∈ G, mobiusSL g '' (D : Set RiemannSphere) = D) ∧ (D : Set RiemannSphere) ⊆ discontinuitySet G ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π ∧ IsOpenMap π ∧ range π = {x | x ∉ (X : Set M) ∨ ν x ≠ ⊤} ∧
      (∀ y z : D, π y = π z ↔ ∃ g ∈ G, mobiusSL g (y : RiemannSphere) = (z : RiemannSphere)) ∧
      ∀ y : D, (π y ∈ (X : Set M) → (stabilizerOrder G y : ℕ∞) = ν (π y)) ∧
        (π y ∉ (X : Set M) → stabilizerOrder G y = 1)) :
    let chi : ℚ := 2 * p - 2 + (X.val.map fun x => 1 - (if ν x = ⊤ then 0 else 1 / ((ν x).toNat : ℚ))).sum
    (chi < 0 ↔ D = ⊤) ∧ (chi = 0 ↔ D = finitePlaneOpens) ∧ (0 < chi ↔ D = upperHalfPlaneOpens) := by
  sorry

end FarkasKra1992
