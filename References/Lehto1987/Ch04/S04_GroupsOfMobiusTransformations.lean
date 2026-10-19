import References.Lehto1987.Ch04.S03_UniformizationOfRiemannSurfaces
import References.LehtoVirtanen1973.Ch02.S05_ConvergenceTheorems

/-!
# Lehto, Chapter IV §4: Groups of Möbius transformations

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. IV §4 (`full.md`
P1:5261–5471).

Conventions (see §3; decision B0.12):
- A group of Möbius transformations is a subgroup `G` of `SL(2, ℂ)` acting on `ℂ̄` by `LiZhongQC.mobiusSL`, i.e.
  `z ↦ (az + b)/(cz + d)`. The matrices `±γ` give the same transformation (Lehto's isomorphism (4.2) with
  `SL(2)/±I`).
- A Fuchsian group in Lehto's sense acts properly discontinuously and fixed point free on a disc. It is taken on the
  upper half-plane: `Γ ≤ SL(2, ℝ)` with `LiZhongQC.IsFuchsian Γ ∧ LiZhongQC.ActsFreely Γ`. Its limit set is
  `LiZhongQC.fuchsianLimitSet Γ`, the limit set of the complexified group.
- The hyperbolic metric of `ℍ` is Mathlib's distance on `ℍ`, which is twice Lehto's; comparisons of distances are
  unaffected.
- "Tangent" to a curve at a finite point `p` is `HasTangentAt` below; fixed points at `∞` are brought to finite
  points by a Möbius transformation.

* Definition (orbits, fundamental domain, §4.1) — `IsFundamentalRegion`
* Unlabelled (§4.1, P1:5269–5277): the groups of translations are trivial, cyclic (S the punctured plane) or of rank 2
  (S a torus) — `para4_4_1`
* Definition (Fuchsian group, §4.2) — exists: `LiZhongQC.IsFuchsian`, `LiZhongQC.ActsFreely` (on ℍ, jointly)
* Definition (elliptic, hyperbolic, loxodromic, parabolic transformation, §4.2) — `IsEllipticMob`, `IsHyperbolicMob`,
  `IsLoxodromicMob`, `IsParabolicMob`
* Unlabelled (§4.2, P1:5289–5293): invariance of the classes under conjugation; loxodromic transformations keep no
  disc invariant — omitted: U−, not cited
* Unlabelled (§4.2, P1:5293): the elements of a Fuchsian group are hyperbolic or parabolic, with fixed points on the
  boundary of the disc — `para4_4_2_a`
* Definition (Dirichlet region, §4.2) — exists: `GardinerLakic2000.dirichletDomain`
* Unlabelled (§4.2, P1:5303–5311): the Dirichlet regions are non-empty, open, disjoint and congruent, cover `H` with
  their closures, are connected, and are fundamental domains — `para4_4_2_b`
* Definition (free and inner sides, §4.2) — `innerSides`
* Unlabelled (§4.2, P1:5315): inner sides are pairwise equivalent; free sides have no equivalent points — omitted:
  U−, not cited
* Theorem 4.1 (§4.2) — `thm4_4_1`
* Definition (limit set, §4.3) — exists: `LiZhongQC.limitSet` (the limit points of 2.5 for the action on ℂ̄)
* Unlabelled (§4.3, P1:5325): the limit set is invariant and closed — `para4_4_3_a`
* Definition (elementary group, §4.3) — `IsElementary`
* Unlabelled (§4.3, P1:5327–5333): the list of elementary groups — omitted: a survey, quoted
* Formula (4.1) (§4.3) — `example4_4_3` (the invariant function)
* Example (§4.3, P1:5335–5353): `H/⟨z ↦ az⟩` is the annulus `1 < |w| < e^{2π²/log a}` — `example4_4_3`
* Definition (set of discontinuity, ordinary points, §4.4) — `discontinuitySet`
* Definition (Kleinian group, §4.4) — `IsKleinian`
* Unlabelled (§4.4, P1:5361): a Kleinian group is countable — omitted: quoted, not cited
* Formula (4.2) (§4.4) — omitted: the isomorphism of the Möbius group with `SL(2)/±I` (the model's convention)
* Definition (discrete group, §4.4) — exists: `DiscreteTopology`
* Unlabelled (§4.4, P1:5379): discreteness and infinitesimal transformations; a Kleinian group is discrete — omitted:
  not cited
* Unlabelled (§4.4, P1:5381): `{g|A}` is a normal family if and only if `A ⊂ Ω` — `para4_4_4`
* Lemma 4.1 (§4.5) — `lemma4_4_1`
* Unlabelled (§4.5, P1:5389): the limit set of a non-elementary group is perfect — `para4_4_5_a`
* Formula (4.3) (§4.5) — `eq4_4_3`
* Unlabelled (§4.5, P1:5397–5399): the limit set of a Kleinian group is nowhere dense; that of a Fuchsian group is
  the boundary circle or nowhere dense in it — `para4_4_5_b`
* Definition (first and second kind, §4.5) — exists: `GardinerLakic2000.IsFirstKind`
* Unlabelled (§4.5, P1:5401): `Ω` has two components for groups of the first kind, one otherwise — omitted: U−, not
  cited
* Unlabelled (§4.5, P1:5405): without elliptic elements of finite period, the fixed points are dense in `L` —
  `para4_4_5_c`
* Unlabelled (§4.5, P1:5407): for a Fuchsian group of the first kind on `H`, the fixed points are dense in `ℝ` —
  `para4_4_5_d`
* Formula (4.4) (§4.5) — `eq4_4_4`
* Definition (the bordered surface `S* = (H ∪ (ℝ ∖ L))/G`, §4.5) — `borderedQuotient`
* Unlabelled (§4.5, P1:5423): `S*` is a bordered Riemann surface with border `(ℝ ∖ L)/G` — `para4_4_5_e`
* Definition (double and mirror image of `S = H/G`, §4.5) — `doubleSurface`, `mirrorImage`
* Definition (invariant domain, §4.6) — `IsInvariantDomain`
* Definition (Fuchsian as a Kleinian group with an invariant disc, §4.6) — omitted: conjugate to the Fuchsian groups
  on `H` of §4.2 (U−)
* Definition (quasi-Fuchsian group, §4.6) — `IsQuasiFuchsianLehto`
* Lemma 4.2 (§4.6) — `lemma4_4_2`
* Formula (4.5) (§4.6) — omitted: a step of the proof of Lemma 4.2
* Theorem 4.2 (§4.6) — `thm4_4_2`
* Unlabelled (§4.6, P1:5461–5467): Klein's method of chains of discs — omitted: a construction, not cited

Helpers (not book notions): `mobQuot` (the quotient of a subset of `ℂ̄` by a Möbius group) and `HasTangentAt` (a
tangent line of a set at a finite point).
-/

open Complex Set Filter Topology
open scoped ComplexConjugate ContDiff Manifold MatrixGroups UpperHalfPlane

noncomputable section

namespace Lehto1987

universe u

open LiZhongQC (ExtPlane extInf toExt upperHalf lowerHalf extRealLine mobiusSL mobiusExt IsMobius limitSet
  fuchsianLimitSet ordinarySet fuchsianFixedPoints slRealToComplex IsFuchsian ActsFreely RSConformallyEquivalent
  puncturedPlaneOpens)
open References (IsJordanDomainExt)

/-! ## §4.1 Covering groups acting on the plane -/

/-- **Definition** (fundamental domain, Ch. IV §4.1): a subdomain of `D` which contains at most one point of every
orbit of `G` and whose closure meets every orbit. -/
def IsFundamentalRegion {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace X] (F : Set X) : Prop :=
  IsOpen F ∧ IsConnected F ∧ (∀ x ∈ F, ∀ y ∈ F, (∃ g : G, g • x = y) → x = y) ∧ ∀ x : X, ∃ g : G, g • x ∈ closure F

/-- **Unlabelled** (Ch. IV §4.1, P1:5269–5277). If the plane is the universal covering surface of `S`, the covering
group consists of translations and is either trivial (`S` is conformally the plane), or generated by one translation
`z ↦ z + ω` (`S` is conformally the punctured plane), or generated by two translations `z ↦ z + ω₁`, `z ↦ z + ω₂`
with `Im(ω₁/ω₂) ≠ 0` (`S` is compact, a torus).
Modelling: the periods are named `w`, `w₁`, `w₂`. -/
theorem para4_4_1 {S : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] {p : ℂ → S} (hp : IsUniversalCoveringSurface p)
    (hpa : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) :
    (∀ g ∈ deck p, ∃ a : ℂ, ∀ z : ℂ, g z = z + a) ∧
      ((deck p = ⊥ ∧ RSConformallyEquivalent S ℂ) ∨
        (∃ w : ℂ, w ≠ 0 ∧ (∀ g : ℂ ≃ₜ ℂ, g ∈ deck p ↔ ∃ n : ℤ, ∀ z, g z = z + n * w) ∧
          RSConformallyEquivalent S puncturedPlaneOpens) ∨
        (∃ w₁ w₂ : ℂ, (w₁ / w₂).im ≠ 0 ∧
          (∀ g : ℂ ≃ₜ ℂ, g ∈ deck p ↔ ∃ m n : ℤ, ∀ z, g z = z + m * w₁ + n * w₂) ∧ CompactSpace S)) := by
  sorry

/-! ## §4.2 Fuchsian groups -/

/-- **Definition** (elliptic transformation, Ch. IV §4.2): with two fixed points, normal form
`(w − z₁)/(w − z₂) = ρe^{iθ}(z − z₁)/(z − z₂)` with `ρ = 1`, `θ ≠ 0`.
Modelling: `g` is conjugate by a Möbius `M` (sending `z₁, z₂` to `0, ∞`) to `w ↦ kw` with `|k| = 1`, `k ≠ 1`. -/
def IsEllipticMob (g : SL(2, ℂ)) : Prop :=
  ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ ∃ k : ℂ, ‖k‖ = 1 ∧ k ≠ 1 ∧
    ∀ z : ExtPlane, M (mobiusSL g z) = mobiusExt k 0 0 1 (M z)

/-- **Definition** (hyperbolic transformation, Ch. IV §4.2): the normal form with `ρ ≠ 1`, `θ = 0`, i.e. conjugate to
`w ↦ ρw` with `ρ > 0`, `ρ ≠ 1`. -/
def IsHyperbolicMob (g : SL(2, ℂ)) : Prop :=
  ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ ≠ 1 ∧
    ∀ z : ExtPlane, M (mobiusSL g z) = mobiusExt (ρ : ℂ) 0 0 1 (M z)

/-- **Definition** (loxodromic transformation, Ch. IV §4.2): the normal form with `ρ ≠ 1`, `θ ≠ 0`, i.e. conjugate to
`w ↦ kw` with `|k| ≠ 1` and `k` not a positive real. -/
def IsLoxodromicMob (g : SL(2, ℂ)) : Prop :=
  ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ ∃ k : ℂ, ‖k‖ ≠ 1 ∧ ¬ (k.im = 0 ∧ 0 < k.re) ∧
    ∀ z : ExtPlane, M (mobiusSL g z) = mobiusExt k 0 0 1 (M z)

/-- **Definition** (parabolic transformation, Ch. IV §4.2): a Möbius transformation with only one fixed point.
Modelling: conjugate to `w ↦ w + 1` (the fixed point sent to `∞`). -/
def IsParabolicMob (g : SL(2, ℂ)) : Prop :=
  ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ ∀ z : ExtPlane, M (mobiusSL g z) = mobiusExt 1 1 0 1 (M z)

/-- **Unlabelled** (Ch. IV §4.2, P1:5293). The elements of a Fuchsian group, other than the identity, are hyperbolic
or parabolic, with fixed points on the boundary of the invariant disc.
Modelling: `Γ` on `ℍ`; the elements `γ ≠ ±1`; the boundary is `ℝ̂` (`LiZhongQC.extRealLine`). -/
theorem para4_4_2_a {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {γ : SL(2, ℝ)}
    (hγ : γ ∈ Γ) (h1 : γ ≠ 1) (h2 : γ ≠ -1) :
    (IsHyperbolicMob (slRealToComplex γ) ∨ IsParabolicMob (slRealToComplex γ)) ∧
      ∀ z : ExtPlane, mobiusSL (slRealToComplex γ) z = z → z ∈ extRealLine := by
  sorry

/-- **Unlabelled** (Ch. IV §4.2, P1:5303–5311). For a Fuchsian group `Γ` on `H` and `z₀ ∈ H`, the Dirichlet region
`N` with center `z₀` is non-empty, open and connected (a convex polygon), its images `N_j` under `Γ` are the
Dirichlet regions with centers `γ z₀`, they are mutually disjoint, their closures cover `H`, and `N` is a fundamental
domain of `Γ`.
Modelling: `N` read in `ℍ` (`GardinerLakic2000.dirichletDomain` is a subset of `ℂ`); the disjointness and the
covering are the fundamental-domain property `IsFundamentalRegion` for the action of `Γ` on `ℍ`. -/
theorem para4_4_2_b {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (z₀ : ℍ) :
    {τ : ℍ | (τ : ℂ) ∈ GardinerLakic2000.dirichletDomain Γ z₀}.Nonempty ∧
      IsFundamentalRegion (G := Γ) {τ : ℍ | (τ : ℂ) ∈ GardinerLakic2000.dirichletDomain Γ z₀} ∧
      ∀ γ ∈ Γ, {τ : ℍ | (τ : ℂ) ∈ GardinerLakic2000.dirichletDomain Γ (γ • z₀)} =
        (γ • ·) '' {τ : ℍ | (τ : ℂ) ∈ GardinerLakic2000.dirichletDomain Γ z₀} := by
  sorry

/-- **Definition** (inner sides of a Dirichlet region, Ch. IV §4.2): the boundary arcs of the Dirichlet region `N`
which lie in `H`. Each lies on the hyperbolic perpendicular bisector of `z₀` and some `γ z₀`.
Modelling: as subsets of `ℍ`, the non-degenerate intersections of the frontier of `N` in `ℍ` with these bisectors
(the boundary arcs on `ℝ`, the free sides, are not in `ℍ`). -/
def innerSides (Γ : Subgroup SL(2, ℝ)) (z₀ : ℍ) : Set (Set ℍ) :=
  {s | ∃ γ ∈ Γ, γ • z₀ ≠ z₀ ∧ s.Nontrivial ∧
    s = frontier {τ : ℍ | (τ : ℂ) ∈ GardinerLakic2000.dirichletDomain Γ z₀} ∩ {τ | dist τ z₀ = dist τ (γ • z₀)}}

/-- **Theorem 4.1** (Ch. IV §4.2). The elements of a Fuchsian group which map the inner sides of a Dirichlet region
onto each other generate the whole group.
Modelling: up to the sign `±1` of `SL(2, ℝ)` (the same transformation). -/
theorem thm4_4_1 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (z₀ : ℍ) :
    ∀ γ ∈ Γ, γ ∈ Subgroup.closure {δ ∈ Γ | ∃ s ∈ innerSides Γ z₀, ∃ s' ∈ innerSides Γ z₀, (δ • ·) '' s = s'} ∨
      -γ ∈ Subgroup.closure {δ ∈ Γ | ∃ s ∈ innerSides Γ z₀, ∃ s' ∈ innerSides Γ z₀, (δ • ·) '' s = s'} := by
  sorry

/-! ## §4.3 Elementary groups -/

/-- **Unlabelled** (Ch. IV §4.3, P1:5325). The limit set `L` of a group `G` of Möbius transformations satisfies
`g(L) = L` for every `g ∈ G`, and `L` is closed. -/
theorem para4_4_3_a (G : Subgroup SL(2, ℂ)) :
    (∀ g ∈ G, mobiusSL g '' limitSet G = limitSet G) ∧ IsClosed (limitSet G) := by
  sorry

/-- **Definition** (elementary group, Ch. IV §4.3): the limit set contains at most two points. (Not
`Katok1992.IsElementary`, Katok's definition for subgroups of `PSL(2, ℝ)` by a finite orbit.) -/
def IsElementary (G : Subgroup SL(2, ℂ)) : Prop := (limitSet G).encard ≤ 2

/-- **Example** (Ch. IV §4.3, P1:5335–5353). For `a > 1`, the real cyclic group `G = {z ↦ aⁿz}` acting on `H` has
the limit set `{0, ∞}`, and the function `z ↦ e^{−2πi log z / log a}` (4.1), invariant under `G`, maps `H` onto the
annulus `A = {1 < |w| < e^{2π²/log a}}`, identifying exactly the points of the same orbit: `G` is the covering group
of `H` over `A`.
Modelling: `Γ` is any subgroup of `SL(2, ℝ)` whose elements act as `z ↦ aⁿz`, `n ∈ ℤ`; principal logarithm. -/
theorem example4_4_3 {a : ℝ} (ha : 1 < a) {Γ : Subgroup SL(2, ℝ)}
    (hΓ : ∀ γ : SL(2, ℝ), γ ∈ Γ ↔ ∃ n : ℤ, ∀ z : ℍ, ((γ • z : ℍ) : ℂ) = (a : ℂ) ^ n * z) :
    fuchsianLimitSet Γ = {((0 : ℂ) : ExtPlane), extInf} ∧
      (fun z : ℂ => exp (-2 * Real.pi * I * log z / Real.log a)) '' upperHalf =
        {w : ℂ | 1 < ‖w‖ ∧ ‖w‖ < Real.exp (2 * Real.pi ^ 2 / Real.log a)} ∧
      ∀ z ∈ upperHalf, ∀ w ∈ upperHalf, (exp (-2 * Real.pi * I * log z / Real.log a) =
        exp (-2 * Real.pi * I * log w / Real.log a) ↔ ∃ n : ℤ, w = (a : ℂ) ^ n * z) := by
  sorry

/-! ## §4.4 Kleinian groups -/

/-- **Definition** (set of discontinuity, ordinary points, Ch. IV §4.4): `Ω` is the complement of the limit set in the
extended plane. -/
def discontinuitySet (G : Subgroup SL(2, ℂ)) : Set ExtPlane := (limitSet G)ᶜ

/-- **Definition** (Kleinian group, Ch. IV §4.4): a group of Möbius transformations whose set of discontinuity is not
empty (near miss: `LiZhongQC.IsKleinGroup`, which also asks for more than two limit points). -/
def IsKleinian (G : Subgroup SL(2, ℂ)) : Prop := (discontinuitySet G).Nonempty

/-- **Unlabelled** (Ch. IV §4.4, P1:5381, Lehner). Let `A` be a plane domain and `G` a Kleinian group. The family
`{g|A | g ∈ G}` is normal if and only if `A ⊂ Ω`.
Modelling: normality for the spherical metric (`LehtoVirtanen1973.IsNormalFamilySph`). -/
theorem para4_4_4 {G : Subgroup SL(2, ℂ)} (hG : IsKleinian G) {A : Set ℂ} (hA : IsOpen A) (hAc : IsConnected A) :
    LehtoVirtanen1973.IsNormalFamilySph {w | ∃ g ∈ G, w = mobiusSL g} (toExt A) ↔ toExt A ⊆ discontinuitySet G := by
  sorry

/-! ## §4.5 Structure of the limit set -/

/-- **Lemma 4.1** (Ch. IV §4.5, Lehner). For a Kleinian group `G`, every point `ζ ∈ L` is a cluster point of each orbit
`G(z)`, with the possible exception of `z = ζ` and one other point `z ∈ L`.
Modelling: `ζ` is a limit of `gₙ(z)` for distinct `gₙ ∈ G`. -/
theorem lemma4_4_1 {G : Subgroup SL(2, ℂ)} (hG : IsKleinian G) {ζ : ExtPlane} (hζ : ζ ∈ limitSet G) :
    ∃ z₁ ∈ limitSet G, ∀ z : ExtPlane, z ≠ ζ → z ≠ z₁ →
      ∃ gs : ℕ → G, Function.Injective gs ∧ Tendsto (fun n => mobiusSL (gs n) z) atTop (𝓝 ζ) := by
  sorry

/-- **Unlabelled** (Ch. IV §4.5, P1:5389). If the Kleinian group `G` is not elementary, its limit set is perfect. -/
theorem para4_4_5_a {G : Subgroup SL(2, ℂ)} (hG : IsKleinian G) (hne : ¬ IsElementary G) : Perfect (limitSet G) := by
  sorry

/-- **Formula (4.3)** (Ch. IV §4.5). The limit set of a Kleinian group agrees with the boundary of the set of
discontinuity: `L = ∂Ω`. -/
theorem eq4_4_3 {G : Subgroup SL(2, ℂ)} (hG : IsKleinian G) : limitSet G = frontier (discontinuitySet G) := by
  sorry

/-- **Unlabelled** (Ch. IV §4.5, P1:5397–5399). The limit set of a Kleinian group is nowhere dense in the plane. The
limit set of a Fuchsian group acting on a disc `D` is either the whole boundary `∂D` or a nowhere dense subset of
`∂D`.
Modelling: the Fuchsian group on `ℍ`, `∂D = ℝ̂`; "nowhere dense in `ℝ̂`": no open set meets `ℝ̂` inside `L` only. -/
theorem para4_4_5_b :
    (∀ G : Subgroup SL(2, ℂ), IsKleinian G → interior (limitSet G) = ∅) ∧
    ∀ Γ : Subgroup SL(2, ℝ), IsFuchsian Γ → ActsFreely Γ →
      fuchsianLimitSet Γ = extRealLine ∨ ∀ U : Set ExtPlane, IsOpen U → (U ∩ extRealLine).Nonempty →
        ¬ U ∩ extRealLine ⊆ fuchsianLimitSet Γ := by
  sorry

/-- **Unlabelled** (Ch. IV §4.5, P1:5405). If a Kleinian group does not contain elliptic transformations of finite
period, then the closure of the set `F` of the fixed points of its elements (other than the identity) is its limit
set. -/
theorem para4_4_5_c {G : Subgroup SL(2, ℂ)} (hG : IsKleinian G)
    (hell : ∀ g ∈ G, IsEllipticMob g → ∀ n : ℕ, 1 ≤ n → g ^ n ≠ 1 ∧ g ^ n ≠ -1) :
    closure {z : ExtPlane | ∃ g ∈ G, g ≠ 1 ∧ g ≠ -1 ∧ mobiusSL g z = z} = limitSet G := by
  sorry

/-- **Unlabelled** (Ch. IV §4.5, P1:5407). If `G` is a Fuchsian group of the first kind acting on the upper half-plane,
then the fixed points of `G` are everywhere dense on the real axis. -/
theorem para4_4_5_d {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (hfirst : GardinerLakic2000.IsFirstKind Γ) : Dense (fuchsianFixedPoints Γ) := by
  sorry

/-- **Formula (4.4)** (Ch. IV §4.5). Let `F_h`, `F_l`, `F_p` be the sets of fixed points of the hyperbolic, loxodromic
and parabolic elements of a Kleinian group `G`. Then `L = cl F_h`, `L = cl F_l`, `L = cl F_p`, whenever `G` contains
an element of the class in question. -/
theorem eq4_4_4 {G : Subgroup SL(2, ℂ)} (hG : IsKleinian G) :
    ((∃ g ∈ G, IsHyperbolicMob g) →
      limitSet G = closure {z | ∃ g ∈ G, IsHyperbolicMob g ∧ mobiusSL g z = z}) ∧
    ((∃ g ∈ G, IsLoxodromicMob g) →
      limitSet G = closure {z | ∃ g ∈ G, IsLoxodromicMob g ∧ mobiusSL g z = z}) ∧
    ((∃ g ∈ G, IsParabolicMob g) →
      limitSet G = closure {z | ∃ g ∈ G, IsParabolicMob g ∧ mobiusSL g z = z}) := by
  sorry

/-- Helper. The quotient `X/G` of a subset `X` of `ℂ̄` by the action of a group `G` of Möbius transformations (two
points are identified when some `g ∈ G` maps one onto the other), with the quotient topology. -/
abbrev mobQuot (G : Subgroup SL(2, ℂ)) (X : Set ExtPlane) : Type :=
  Quot fun x y : X => ∃ g ∈ G, mobiusSL g x = y

/-- **Definition** (the bordered surface `S*`, Ch. IV §4.5): for a Fuchsian group `G` of the second kind on `H`,
`S* = (H ∪ (ℝ ∖ L))/G`.
Modelling: `ℝ ∖ L` is `LiZhongQC.ordinarySet Γ = ℝ̂ ∖ L`; the group acts through its complexification. -/
abbrev borderedQuotient (Γ : Subgroup SL(2, ℝ)) : Type :=
  mobQuot (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ))) (toExt upperHalf ∪ ordinarySet Γ)

/-- **Unlabelled** (Ch. IV §4.5, P1:5423). If `G` is a Fuchsian group of the second kind acting on `H`, then
`S* = (H ∪ (ℝ ∖ L))/G` is a bordered Riemann surface with `(ℝ ∖ L)/G` as its border. -/
theorem para4_4_5_e {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (hsecond : ¬ GardinerLakic2000.IsFirstKind Γ) :
    (∃ A, IsBorderedRS (borderedQuotient Γ) A) ∧
      border (borderedQuotient Γ) =
        {q | ∃ x : ↥(toExt upperHalf ∪ ordinarySet Γ), (x : ExtPlane) ∈ ordinarySet Γ ∧ q = Quot.mk _ x} := by
  sorry

/-- **Definition** (the double of `S = H/G`, Ch. IV §4.5): `Ω/G`, the group acting on the plane. -/
abbrev doubleSurface (Γ : Subgroup SL(2, ℝ)) : Type :=
  mobQuot (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ))) (fuchsianLimitSet Γ)ᶜ

/-- **Definition** (the mirror image of `S = H/G`, Ch. IV §4.5): `(Ω ∖ (H ∪ ℝ))/G`, i.e. the quotient of the lower
half-plane. -/
abbrev mirrorImage (Γ : Subgroup SL(2, ℝ)) : Type :=
  mobQuot (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ))) (toExt lowerHalf)

/-! ## §4.6 Invariant domains -/

/-- **Definition** (invariant domain, Ch. IV §4.6): a component of the set of discontinuity of a Kleinian group which
is mapped onto itself by every element of the group. -/
def IsInvariantDomain (G : Subgroup SL(2, ℂ)) (A : Set ExtPlane) : Prop :=
  (∃ z ∈ discontinuitySet G, A = connectedComponentIn (discontinuitySet G) z) ∧ ∀ g ∈ G, mobiusSL g '' A = A

/-- **Definition** (quasi-Fuchsian group, Ch. IV §4.6): a Kleinian group with no fixed points in `Ω` which has a
Jordan domain as an invariant component (near miss: `LiZhongQC.IsQuasiFuchsian`, defined by an invariant Jordan
curve). -/
def IsQuasiFuchsianLehto (G : Subgroup SL(2, ℂ)) : Prop :=
  IsKleinian G ∧ (∀ g ∈ G, g ≠ 1 → g ≠ -1 → ∀ z ∈ discontinuitySet G, mobiusSL g z ≠ z) ∧
    ∃ A : Set ExtPlane, IsInvariantDomain G A ∧ IsJordanDomainExt A

/-- Helper. The set `C` has a tangent at the finite point `p`: there is a line `p + e^{iθ}ℝ` such that, for every
`a > 0`, the points of `C` near `p` lie in the double angle of opening `a` about the line. (Not
`GarnettMarshall2005.HasTangentAt` or `Pommerenke1992.HasTangentAt`, which are for parametrized arcs and for the
boundary of a conformal image.) -/
def HasTangentAt (C : Set ExtPlane) (p : ℂ) : Prop :=
  ∃ θ : ℝ, ∀ a : ℝ, 0 < a → ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, (z : ExtPlane) ∈ C → z ≠ p → ‖z - p‖ < r →
    |Real.sin (arg ((z - p) * exp (-(θ * I))))| < Real.sin (min a (Real.pi / 2))

/-- **Lemma 4.2** (Ch. IV §4.6). Let `G` be a Kleinian group such that `Ω` has an invariant component `A` which is a
Jordan domain different from a disc. Then `∂A` does not have a tangent at a fixed point of a loxodromic element of `G`.
Modelling: at the finite fixed points (a fixed point `∞` is moved by a Möbius conjugation); "disc" is
`IsDiscExt`. -/
theorem lemma4_4_2 {G : Subgroup SL(2, ℂ)} (hG : IsKleinian G) {A : Set ExtPlane} (hA : IsInvariantDomain G A)
    (hJ : IsJordanDomainExt A) (hnd : ¬ IsDiscExt A) {g : SL(2, ℂ)} (hg : g ∈ G) (hlox : IsLoxodromicMob g)
    {p : ℂ} (hp : mobiusSL g p = p) : ¬ HasTangentAt (frontier A) p := by
  sorry

/-- **Theorem 4.2** (Ch. IV §4.6). The boundary of an invariant component of a quasi-Fuchsian group is either a circle
or a Jordan curve which fails to have a tangent on an everywhere dense set.
Modelling: "circle" is a circle or line of `ℂ̄` (`LehtoVirtanen1973.IsGenCircle`); the dense set consists of finite
points. -/
theorem thm4_4_2 {G : Subgroup SL(2, ℂ)} (hG : IsQuasiFuchsianLehto G) {A : Set ExtPlane}
    (hA : IsInvariantDomain G A) (hJ : IsJordanDomainExt A) :
    LehtoVirtanen1973.IsGenCircle (frontier A) ∨
      ∃ E : Set ℂ, toExt E ⊆ frontier A ∧ frontier A ⊆ closure (toExt E) ∧ ∀ p ∈ E, ¬ HasTangentAt (frontier A) p := by
  sorry

end Lehto1987
