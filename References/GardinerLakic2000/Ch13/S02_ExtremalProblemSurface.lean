import References.GardinerLakic2000.Ch13.S01_ExtremalProblemDisc

/-!
# Gardiner–Lakic 2000, Ch. 13 §13.2 Extremal problem for a surface

Source `teichmuller.txt`, lines 9577–9603.

* Definition (finite topological type, the double `S^d`, l. 9578) — exists: `LiZhongQC.IsFiniteType`
  `LiZhongQC.IsSchottkyDouble`
* Definition (obstacle set: compact, finitely many simply connected components, l. 9580) — `IsObstacleSet`
* Definition (the family `𝓕` of pairs `(f, S_f)`, `φ_f`, `M_f`, l. 9580–9586) — `IsObstacleFamilyMember`,
  `IsHeightTransport`, `obstacleValue`
* Formula (13.1) (`M = sup M_f`, l. 9592) — `obstacleSup`
* Definition (`f(E) = S_f ∖ f(S ∖ E)`, l. 9582; slits along horizontal arcs, l. 9597) — `slitImage`, `IsSlitSet`
* Theorem 1 (existence, l. 9597) — `thm13_1`
* Theorem 2 (uniqueness, l. 9600) — `thm13_2`

**Modelling (calibration D0.1, D0.7).** The family `𝓕` consists of conformal injective maps `f : S ∖ E → S_f`
(`S_f` a Part A `RSBundle`) together with a quasiconformal homeomorphism `g : S → S_f` equal to `f` off a compact
neighbourhood of `E` and homotopic to `f` on `S ∖ E`. This `g` records the marking (homotopy class) that `f` determines;
it replaces the book's isomorphism of fundamental groups (l. 9580: `f` induces an isomorphism of `π₁(S)` onto `π₁(S_f)`)
[reading]. [CORRECTION] (AUDITR2_GL614 R2-3) Without the homotopy clause `g` could be any compactly supported
quasiconformal map, e.g. a power of a Dehn twist, and then `obstacleSup = ⊤` for every `E` and `φ ≠ 0`. `φ_f` is the element of
`A(S_f)` with the heights of `φ`, transported by `g` (the heights mapping, `para12_6_heights_mapping`), and
`M_f = ‖φ_f‖`. Theorems 1 and 2 are stated for surfaces of finite analytic type, i.e. for `S = S^d`. The bordered case
is the `J`-symmetric instance of this problem on the double: the family and the obstacle extend by symmetry, and by
uniqueness the extremal is symmetric (l. 9580, 9850) [reading]. The symmetric form is stated where the book states it
separately (Theorem 4, `thm13_4`). A critical point of `φ_f` on `S_f` is a zero (the poles lie at the punctures).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (Loop quadDiffNorm IsQCRS IsHorizontalArcRS IsBiholomorphic localMapExpr localMapDomain)

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- **Definition** (obstacle set, §13.2, l. 9580). A compact subset `E` of `S` with finitely many components, each of
them simply connected. -/
def IsObstacleSet (E : Set S) : Prop :=
  IsCompact E ∧ (range fun x : E => connectedComponentIn E x).Finite ∧
    ∀ x ∈ E, SimplyConnectedSpace (connectedComponentIn E x)

/-- **Definition** (the family `𝓕`, §13.2, l. 9580; D0.7). `(f, S_f)` belongs to `𝓕`: `f` is conformal and injective
on `S ∖ E`, and a quasiconformal homeomorphism `g : S → S_f` agrees with `f` off a compact neighbourhood of `E` and is
homotopic to `f` on `S ∖ E` (AUDITR2_GL614 R2-3: this clause fixes the marking). -/
def IsObstacleFamilyMember (E : Set S) {Y : RSBundle.{u}} (f : S → Y.carrier) (g : S ≃ₜ Y.carrier) : Prop :=
  ((∀ x ∉ E, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x) ∧ InjOn f Eᶜ ∧ IsQCRS g ∧
    ∃ N : Set S, IsCompact N ∧ E ⊆ interior N ∧ ∀ x ∉ N, g x = f x) ∧
    ∃ H : C(unitInterval × ↥Eᶜ, Y.carrier), (∀ x : ↥Eᶜ, H (0, x) = g x) ∧ ∀ x : ↥Eᶜ, H (1, x) = f x

/-- **Definition** (`φ_f`, §13.2, l. 9580). `φ′ ∈ A(S_f)` has the heights of `φ`, transported by `g`:
`h_{φ′}[g(γ)] = h_φ[γ]` for every essential simple closed curve `γ` on `S`. -/
def IsHeightTransport (φ : S → ℂ → ℂ) {Y : RSBundle.{u}} (g : S ≃ₜ Y.carrier) (φ' : Y.carrier → ℂ → ℂ) : Prop :=
  φ' ∈ integrableHolQDSet Y.carrier ∧ ∀ β : Loop S, IsEssentialLoop β → qdHeight φ' (loopMap g β) = qdHeight φ β

/-- **Definition** (`M_f = ‖φ_f‖`, §13.2, l. 9585). -/
def obstacleValue (φ : S → ℂ → ℂ) {Y : RSBundle.{u}} (g : S ≃ₜ Y.carrier) : ℝ≥0∞ :=
  ⨅ (φ' : Y.carrier → ℂ → ℂ) (_ : IsHeightTransport φ g φ'), quadDiffNorm φ'

/-- **Formula (13.1)** (§13.2, l. 9592). `M = sup {M_f : (f, S_f) ∈ 𝓕}`. -/
def obstacleSup (φ : S → ℂ → ℂ) (E : Set S) : ℝ≥0∞ :=
  ⨆ (Y : RSBundle.{u}) (f : S → Y.carrier) (g : S ≃ₜ Y.carrier) (_ : IsObstacleFamilyMember E f g),
    obstacleValue φ g

/-- **Definition** (§13.2, l. 9582). `f(E) = S_f ∖ f(S ∖ E)`. -/
def slitImage (E : Set S) {Y : Type*} (f : S → Y) : Set Y := (f '' Eᶜ)ᶜ

/-- **Definition** (§13.2, l. 9597). Every point of `K ⊆ S_f` is a critical point (a zero) of `φ′` or lies on an arc
of a horizontal trajectory of `φ′` contained in `K`: the components of `K` are arcs of horizontal trajectories or
connected unions of such arcs and critical points.
[CORRECTION] (AUDITR2_GL614 R2-6) An isolated point of `K` (a point component, the image of a point component of `E`) is a
degenerate arc and is allowed; constant paths are not horizontal arcs, so without this disjunct `thm13_1` fails for
`E = {x₀}` at a regular point of `φ'`. -/
def IsSlitSet {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] (φ' : Y → ℂ → ℂ) (K : Set Y) : Prop :=
  ∀ y ∈ K, φ' y (chartAt ℂ y y) = 0 ∨
    (∃ (a b : Y) (α : Path a b), IsHorizontalArcRS φ' α ∧ range α ⊆ K ∧ y ∈ range α) ∨
    ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ U ∩ K = {y}

variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- **Theorem 1** (existence, §13.2, l. 9597). Let `S` be a surface of finite (analytic) type, `φ` a nonzero integrable
holomorphic quadratic differential on `S`, and `E` an obstacle set. Then some `(f, S_f) ∈ 𝓕` realizes the supremum
(13.1), and each component of `f(E)` is an arc of a horizontal trajectory of `φ_f` or a connected union of such arcs
and critical points of `φ_f`. -/
theorem thm13_1 {g n : ℕ} (hS : IsFiniteAnalyticType S g n) {φ : S → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet S)
    (hφ0 : φ ≠ 0) {E : Set S} (hE : IsObstacleSet E) :
    ∃ (Y : RSBundle.{u}) (f : S → Y.carrier) (G : S ≃ₜ Y.carrier) (φ' : Y.carrier → ℂ → ℂ),
      IsObstacleFamilyMember E f G ∧ IsHeightTransport φ G φ' ∧ quadDiffNorm φ' = obstacleSup φ E ∧
        IsSlitSet φ' (slitImage E f) := by
  sorry

/-- **Theorem 2** (uniqueness, §13.2, l. 9600). Under the hypotheses of Theorem 1, the extremal point is unique: if
`(f, S_f)` realizes (13.1) and `(g, S_g) ∈ 𝓕` is such that the components of `g(E)` lie in horizontal arcs and
critical points of `φ_g`, then `h = g ∘ f⁻¹` extends to a conformal map `S_f → S_g` with `φ_g(h(z)) h′(z)² = φ_f`. -/
theorem thm13_2 {g n : ℕ} (hS : IsFiniteAnalyticType S g n) {φ : S → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet S)
    (hφ0 : φ ≠ 0) {E : Set S} (hE : IsObstacleSet E) {Y₁ Y₂ : RSBundle.{u}} {f₁ : S → Y₁.carrier}
    {G₁ : S ≃ₜ Y₁.carrier} {φ₁ : Y₁.carrier → ℂ → ℂ} (h₁ : IsObstacleFamilyMember E f₁ G₁)
    (hφ₁ : IsHeightTransport φ G₁ φ₁) (hext : quadDiffNorm φ₁ = obstacleSup φ E) {f₂ : S → Y₂.carrier}
    {G₂ : S ≃ₜ Y₂.carrier} {φ₂ : Y₂.carrier → ℂ → ℂ} (h₂ : IsObstacleFamilyMember E f₂ G₂)
    (hφ₂ : IsHeightTransport φ G₂ φ₂) (hslit : IsSlitSet φ₂ (slitImage E f₂)) :
    ∃ c : Y₁.carrier ≃ₜ Y₂.carrier, IsBiholomorphic (c : Y₁.carrier → Y₂.carrier) ∧ (∀ x ∉ E, c (f₁ x) = f₂ x) ∧
      ∀ y : Y₁.carrier, ∀ z ∈ localMapDomain c y,
        φ₁ y z = φ₂ (c y) (localMapExpr c y z) * deriv (localMapExpr c y) z ^ 2 := by
  sorry

end GardinerLakic2000
