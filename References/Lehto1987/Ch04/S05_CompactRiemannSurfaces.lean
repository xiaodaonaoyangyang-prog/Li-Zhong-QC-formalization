import References.Lehto1987.Ch04.S04_GroupsOfMobiusTransformations

/-!
# Lehto, Chapter IV §5: Compact Riemann surfaces

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. IV §5 (`full.md`
P1:5472–5607).

Conventions (see §1–§4; decision B0.11):
- The genus of a compact surface is the project's `LiZhongQC.HasGenus S p`: compact, with fundamental group the
  surface group of genus `p`. Lehto's normal polygon is not defined.
- Divisors are `LiZhongQC.Divisor S` (finitely supported `S → ℤ`) with `LiZhongQC.Divisor.deg`.
- The divisor of a meromorphic differential is given relationally (`IsDivisorOfDiff`). A meromorphic function is a
  meromorphic `(0, 0)`-differential.
- A differential is non-zero when some local representation is not identically zero.
- `Q` is `LiZhongQC.holQuadDiffSubmodule S`.
- The covering group of `H` over `S` is `Γ ≤ SL(2, ℝ)` with `LiZhongQC.IsUniformization`.

* Theorem 5.1 (§5.1) — `thm4_5_1`
* Theorem 5.2 (§5.1) — `thm4_5_2`
* Definition (normal polygon, pattern (5.1), §5.2) — omitted: used only to define the genus (decision B0.11)
* Formula (5.1) (§5.2) — omitted: the pattern of a normal polygon (see the previous bullet)
* Definition (genus of a compact surface, §5.2) — exists: `LiZhongQC.HasGenus`
* Unlabelled (§5.2, P1:5504): a torus has genus 1; a compact surface covered by the half-plane has genus `> 1` —
  `para4_5_2_a`
* Unlabelled (§5.2, P1:5506): compact orientable surfaces are homeomorphic if and only if they have the same genus —
  `para4_5_2_b`
* Theorem 5.3 (§5.3) — `thm4_5_3`
* Unlabelled (§5.3, P1:5520): injective meromorphic functions exist only for `p = 0` — omitted: U−, not cited
* Unlabelled (§5.3, P1:5524, quoted): the space of holomorphic Abelian differentials has dimension `p` — `para4_5_3`
* Definition (divisor, sum, degree, order, §5.4) — exists: `LiZhongQC.Divisor`, `LiZhongQC.Divisor.deg`
* Definition (divisor of a meromorphic differential, §5.4) — `IsDivisorOfDiff`
* Unlabelled (§5.4, P1:5532): zeros and poles of differentials and their orders are invariant — omitted: U−
* Unlabelled (§5.4, P1:5536): `deg D_f = 0` for a meromorphic function — `para4_5_4_a`
* Unlabelled (§5.4, P1:5536): the divisors of differentials of the same type have the same degree — `para4_5_4_b`
* Definition (dimension of a divisor, §5.4) — `divDim`
* Formula (5.2) (§5.4) — `eq4_5_2`
* Formula (5.3) (§5.4) — `eq4_5_3`
* Definition (the space `Q` of holomorphic quadratic differentials, §5.5) — exists: `LiZhongQC.holQuadDiffSubmodule`
* Formula (5.4) (§5.5) — `eq4_5_4`
* Formula (5.5) (§5.5) — `eq4_5_5`
* Theorem 5.4 (§5.5, Riemann–Roch) — exists: `LiZhongQC.thm22_4_riemann_roch` (with ℓ(α) = dim(−α): Lehto's
  dim D is ℓ(−D), and D₁ is any canonical divisor)
* Formula (5.6) (§5.5) — exists: `LiZhongQC.thm22_4_riemann_roch` (the Riemann–Roch equation)
* Unlabelled (§5.5, P1:5576–5582): `deg D_{φ₁} = 2p − 2` for every meromorphic Abelian differential — exists:
  `LiZhongQC.deg_canonical`
* Formula (5.7) (§5.5) — `eq4_5_7`
* Theorem 5.5 (§5.5) — `thm4_5_5_a`; exists: `LiZhongQC.thm22_5_dim_quadratic_differentials` (the case p > 1)
* Formula (5.8) (§5.5) — omitted: a step of the proof of Theorem 5.5
* Unlabelled (§5.5, P1:5606): `Q = 0` for `p = 0` — omitted: U−, not cited
-/

open Complex Set Filter Topology
open scoped ContDiff Manifold MatrixGroups UpperHalfPlane

noncomputable section

namespace Lehto1987

universe u

open LiZhongQC (IsUniformization IsFuchsian ActsFreely HasGenus Divisor IsDiffFamily IsMeromorphicRS ordRS ellDim
  holQuadDiffSubmodule)

/-! ## §5.1 Covering groups over compact surfaces -/

/-- **Theorem 5.1** (Ch. IV §5.1). Let `S` be a Riemann surface and `G` the covering group of the upper half-plane
`H` over `S`. Then `S` is compact if and only if the Dirichlet regions of `G` are bounded in the hyperbolic metric of
`H`.
Modelling: all Dirichlet regions (they are congruent), as subsets of `ℍ` with its metric. -/
theorem thm4_5_1 {S : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S} (hΓ : IsFuchsian Γ)
    (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) :
    CompactSpace S ↔
      ∀ z₀ : ℍ, Bornology.IsBounded {τ : ℍ | (τ : ℂ) ∈ GardinerLakic2000.dirichletDomain Γ z₀} := by
  sorry

/-- **Theorem 5.2** (Ch. IV §5.1). The covering group of the upper half-plane over a compact Riemann surface is
finitely generated and of the first kind. -/
theorem thm4_5_2 {S : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) :
    Γ.FG ∧ GardinerLakic2000.IsFirstKind Γ := by
  sorry

/-! ## §5.2 Genus of a compact surface -/

/-- **Unlabelled** (Ch. IV §5.2, P1:5504). A torus has genus 1, and every compact Riemann surface which has the upper
half-plane as a universal covering surface has genus `p > 1`.
Modelling: a torus is a compact Riemann surface with the plane as analytic universal covering surface. -/
theorem para4_5_2_a {S : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] :
    (∀ q : ℂ → S, IsUniversalCoveringSurface q → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) q → HasGenus S 1) ∧
    ∀ (Γ : Subgroup SL(2, ℝ)) (q : ℍ → S), IsFuchsian Γ → ActsFreely Γ → IsUniformization Γ q →
      ∃ g : ℕ, 1 < g ∧ HasGenus S g := by
  sorry

/-- **Unlabelled** (Ch. IV §5.2, P1:5506). Two compact orientable surfaces are homeomorphic if and only if they have
the same genus.
Modelling: compact Riemann surfaces (orientable). -/
theorem para4_5_2_b {S S' : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] [TopologicalSpace S'] [T2Space S'] [SecondCountableTopology S']
    [ConnectedSpace S'] [ChartedSpace ℂ S'] [IsManifold 𝓘(ℂ) ω S'] {g g' : ℕ} (hg : HasGenus S g)
    (hg' : HasGenus S' g') : Nonempty (S ≃ₜ S') ↔ g = g' := by
  sorry

/-! ## §5.3 Function theory on compact Riemann surfaces -/

/-- **Theorem 5.3** (Ch. IV §5.3). On a compact Riemann surface, a non-constant meromorphic function assumes every
value the same finite number of times (counted with multiplicity).
Modelling: `f` is meromorphic in the charts (`LiZhongQC.IsMeromorphicRS`) and not equal to a constant off a discrete
set; the multiplicity of the value `c ∈ ℂ` at `x` is the order of `f − c` at `x` when positive, that of `∞` is minus
the order of `f` at a pole. -/
theorem thm4_5_3 {S : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {f : S → ℂ} (hf : IsMeromorphicRS f)
    (hnc : ∀ c : ℂ, ¬ ∀ᶠ x in Filter.codiscrete S, f x = c) :
    ∃ N : ℕ, 0 < N ∧
      (∀ c : ℂ, (∑ᶠ x : S, max 0 (WithTop.untop₀ (ordRS (fun y => f y - c) x))) = (N : ℤ)) ∧
      (∑ᶠ x : S, max 0 (-WithTop.untop₀ (ordRS f x))) = (N : ℤ) := by
  sorry

/-- **Unlabelled** (Ch. IV §5.3, P1:5524, quoted, Springer). On a compact Riemann surface of genus `p`, the dimension
of the space of holomorphic Abelian differentials is `p`.
Modelling: a basis of `p` holomorphic `(1, 0)`-differentials. -/
theorem para4_5_3 {S : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : HasGenus S g) :
    ∃ b : Fin g → S → ℂ → ℂ,
      (∀ i, IsDiffFamily 1 0 (b i) ∧ ∀ x : S, DifferentiableOn ℂ (b i x) (chartAt ℂ x).target) ∧
      LinearIndependent ℂ b ∧
      ∀ a : S → ℂ → ℂ, IsDiffFamily 1 0 a → (∀ x : S, DifferentiableOn ℂ (a x) (chartAt ℂ x).target) →
        a ∈ Submodule.span ℂ (Set.range b) := by
  sorry

/-! ## §5.4 Divisors on compact surfaces -/

/-- **Definition** (divisor of a meromorphic differential, Ch. IV §5.4): `D_φ` takes the value `m` at a zero of order
`m`, `−n` at a pole of order `n`, and vanishes elsewhere.
Modelling: relational: `D` is the divisor of the differential `q` when `D(x)` is the order of the representation of
`q` in the preferred chart at `x` (as `LiZhongQC.IsCanonicalDivisor` for `(1, 0)`). -/
def IsDivisorOfDiff {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] (q : S → ℂ → ℂ) (D : Divisor S) : Prop :=
  ∀ x : S, (D x : WithTop ℤ) = meromorphicOrderAt (q x) (chartAt ℂ x x)

/-- **Unlabelled** (Ch. IV §5.4, P1:5536). For a non-zero meromorphic function `f` on a compact Riemann surface,
`deg D_f = 0` (by Theorem 5.3).
Modelling: `f` as a meromorphic `(0, 0)`-differential `q`. -/
theorem para4_5_4_a {S : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {q : S → ℂ → ℂ} (hq : IsMeroDiff 0 0 q)
    (hne : ∃ x : S, meromorphicOrderAt (q x) (chartAt ℂ x x) ≠ ⊤) {D : Divisor S} (hD : IsDivisorOfDiff q D) :
    D.deg = 0 := by
  sorry

/-- **Unlabelled** (Ch. IV §5.4, P1:5536). The divisors of non-zero meromorphic differentials of the same type `m`
on a compact Riemann surface all have the same degree. -/
theorem para4_5_4_b {S : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {m : ℤ} {q₁ q₂ : S → ℂ → ℂ} (h₁ : IsMeroDiff m 0 q₁)
    (h₂ : IsMeroDiff m 0 q₂) (hne₁ : ∃ x : S, meromorphicOrderAt (q₁ x) (chartAt ℂ x x) ≠ ⊤)
    (hne₂ : ∃ x : S, meromorphicOrderAt (q₂ x) (chartAt ℂ x x) ≠ ⊤) {D₁ D₂ : Divisor S}
    (hD₁ : IsDivisorOfDiff q₁ D₁) (hD₂ : IsDivisorOfDiff q₂ D₂) : D₁.deg = D₂.deg := by
  sorry

/-- **Definition** (dimension of a divisor, Ch. IV §5.4): `dim D` is the dimension of the space of meromorphic
functions `f` with `D_f ≥ D`, together with `0`.
Modelling: the project's `ℓ(−D)` (`LiZhongQC.ellDim α` is the dimension of `{f | (f) ≥ −α}`). -/
def divDim {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] (D : Divisor S) : ℕ := ellDim (-D)

/-- **Formula (5.2)** (Ch. IV §5.4). `dim 0 = 1`: the functions with `D_f ≥ 0` are the constants. -/
theorem eq4_5_2 {S : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] : divDim (0 : Divisor S) = 1 := by
  sorry

/-- **Formula (5.3)** (Ch. IV §5.4). `dim D = 0` if `deg D > 0`. -/
theorem eq4_5_3 {S : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {D : Divisor S} (hD : 0 < D.deg) : divDim D = 0 := by
  sorry

/-! ## §5.5 Riemann–Roch theorem -/

/-- **Formula (5.4)** (Ch. IV §5.5). If `D₂` is the divisor of a non-zero `ψ ∈ Q`, then `dim Q = dim(−D₂)`. -/
theorem eq4_5_4 {S : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {ψ : S → ℂ → ℂ} (hψ : ψ ∈ holQuadDiffSubmodule S)
    (hne : ∃ x : S, meromorphicOrderAt (ψ x) (chartAt ℂ x x) ≠ ⊤) {D₂ : Divisor S} (hD : IsDivisorOfDiff ψ D₂) :
    Module.finrank ℂ (holQuadDiffSubmodule S) = divDim (-D₂) := by
  sorry

/-- **Formula (5.5)** (Ch. IV §5.5). If `D₁` is the divisor of a non-zero holomorphic Abelian differential on a
compact Riemann surface of genus `p`, then `dim(−D₁) = p`. -/
theorem eq4_5_5 {S : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : HasGenus S g) {a : S → ℂ → ℂ}
    (ha : IsDiffFamily 1 0 a) (hah : ∀ x : S, DifferentiableOn ℂ (a x) (chartAt ℂ x).target)
    (hne : ∃ x : S, meromorphicOrderAt (a x) (chartAt ℂ x x) ≠ ⊤) {D₁ : Divisor S} (hD : IsDivisorOfDiff a D₁) :
    divDim (-D₁) = g := by
  sorry

/-- **Formula (5.7)** (Ch. IV §5.5). On a compact Riemann surface of genus `p`, the divisor of a non-zero meromorphic
quadratic differential has degree `4p − 4`; in particular a non-zero holomorphic quadratic differential has `4p − 4`
zeros (counted with multiplicity). -/
theorem eq4_5_7 {S : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : HasGenus S g) {q : S → ℂ → ℂ} (hq : IsMeroDiff 2 0 q)
    (hne : ∃ x : S, meromorphicOrderAt (q x) (chartAt ℂ x x) ≠ ⊤) {D : Divisor S} (hD : IsDivisorOfDiff q D) :
    D.deg = 4 * (g : ℤ) - 4 := by
  sorry

/-- **Theorem 5.5** (Ch. IV §5.5), the case `p = 1`. On a compact Riemann surface of genus 1, the space of holomorphic
quadratic differentials has dimension 1 (the case `p > 1`, dimension `3p − 3`, is
`LiZhongQC.thm22_5_dim_quadratic_differentials`). -/
theorem thm4_5_5_a {S : Type u} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [ConnectedSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] (hg : HasGenus S 1) : Module.finrank ℂ (holQuadDiffSubmodule S) = 1 := by
  sorry

end Lehto1987
