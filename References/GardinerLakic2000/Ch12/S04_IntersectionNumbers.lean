import References.GardinerLakic2000.Ch12.S03_Convergence

/-!
# Gardiner–Lakic 2000, Ch. 12 §12.4 Intersection numbers

Source `teichmuller.txt`, lines 9079–9186.

* Definition 1 (intersection number, l. 9080) — `intersectionNumber`
* Definition (closed Poincaré geodesic, l. 9082) — `IsClosedPoincareGeodesic`
* Lemma 2 (l. 9083) — `lemma12_2`
* Lemma 3 (l. 9104) — `lemma12_3`
* Definition 2 (`𝒮′`, finite unions of disjoint essential simple closed curves, l. 9147) — `IsMulticurve`
* Definition 3 (`𝒥𝒮`, formal sums `Σ bⱼ αⱼ`, l. 9159) — `IsJSFormalSum`
* Definition (the intersection map `i*`, l. 9164) — `intersectionMap`

Not items (DESIGN §3): the uniqueness of the Poincaré geodesic in a class (l. 9082), `𝒮 ⊂ 𝒮′ ⊂ 𝒥𝒮`, the injectivity
of `i*` and the diagram of Figure 12.1 (l. 9161–9183), used in the discussion only (U−).

**Misprints.** Lemma 3 prints `h_{φ[α]}[α] = Σ bⱼ i(αⱼ, σ)` (also GL1:1802); the left side is `h_{φ[α]}[σ]`. l. 9162
cites "Theorem 3 of Chapter 10" for the existence of Jenkins–Strebel differentials: it is Theorem 11.3 (`thm11_3`).

**Modelling.** Homotopy classes are represented by loops; "`αⱼ` has height `bⱼ`" is part C's `HasJSProperties`.
Lemma 2 compares distinct unoriented classes (for `α = β` the book's count is not finite) [reading]. A closed
Poincaré geodesic is the projection by the uniformization `p` of a segment of a unit-speed hyperbolic geodesic of `ℍ`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (Loop FreelyHomotopic IsFuchsian IsUniformization)

variable {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R]

/-- **Definition 1** (§12.4, l. 9080). `i(α, β)`: the minimum number of intersection points of simple loops `α′`,
`β′` freely homotopic to `α` and `β`. -/
def intersectionNumber (α β : Loop R) : ℕ∞ :=
  ⨅ (α' : Loop R) (β' : Loop R) (_ : IsSimpleLoop α' ∧ IsSimpleLoop β' ∧ FreelyHomotopic α' α ∧
      FreelyHomotopic β' β), (range α'.2 ∩ range β'.2).encard

/-- **Definition** (§12.4, l. 9082). `α` is a closed Poincaré geodesic of `R = ℍ/Γ` (through the uniformization `p`):
the projection of a segment of a unit-speed hyperbolic geodesic of `ℍ`. -/
def IsClosedPoincareGeodesic (p : UpperHalfPlane → R) (α : Loop R) : Prop :=
  ∃ (c : ℝ → UpperHalfPlane) (T : ℝ), 0 < T ∧ (∀ s t, dist (c s) (c t) = |s - t|) ∧
    ∀ t : unitInterval, α.2 t = p (c (T * t))

/-- **Definition 2** (§12.4, l. 9147). A representative of an element of `𝒮′`: finitely many simple closed curves,
pairwise disjoint, none homotopically trivial or homotopic to a puncture (components may be homotopic). -/
def IsMulticurve {m : ℕ} (γ : Fin m → Loop R) : Prop :=
  (∀ j, IsEssentialLoop (γ j)) ∧ ∀ i j, i ≠ j → Disjoint (range (γ i).2) (range (γ j).2)

/-- **Definition 3** (§12.4, l. 9159). A formal sum `Σ_{j ≤ k} bⱼ αⱼ` of `𝒥𝒮`: positive weights on the curves of an
admissible system. -/
def IsJSFormalSum {k : ℕ} (α : Fin k → Loop R) (b : Fin k → ℝ) : Prop :=
  IsAdmissibleSystem α ∧ ∀ j, 0 < b j

/-- **Definition** (§12.4, l. 9164). The intersection map `i*(Σ bⱼ αⱼ) = (σ ↦ Σ bⱼ i(αⱼ, σ))`. -/
def intersectionMap {k : ℕ} (α : Fin k → Loop R) (b : Fin k → ℝ) (σ : Loop R) : ℝ≥0∞ :=
  ∑ j, ENNReal.ofReal (b j) * (intersectionNumber (α j) σ : ℝ≥0∞)

variable [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R]

/-- **Lemma 2** (§12.4, l. 9083). If `α₀` and `β₀` are closed Poincaré geodesics on `Ṙ` representing elements `α`,
`β` of `𝒮`, then `i(α, β)` is the number of points of `α₀ ∩ β₀`. -/
theorem lemma12_2 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hfree : LiZhongQC.ActsFreely Γ) {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) {α₀ β₀ : Loop R}
    (hα : IsClosedPoincareGeodesic p α₀) (hβ : IsClosedPoincareGeodesic p β₀) (hαe : IsEssentialLoop α₀)
    (hβe : IsEssentialLoop β₀) (hne : ¬ FreelyHomotopic α₀ β₀) (hne' : ¬ FreelyHomotopic α₀ ⟨β₀.1, β₀.2.symm⟩) :
    intersectionNumber α₀ β₀ = (range α₀.2 ∩ range β₀.2).encard := by
  sorry

/-- **Lemma 3** (§12.4, l. 9104). Let `R` be of finite analytic type, `α = {α₁, …, α_k}` an admissible system,
`b₁, …, b_k > 0`, and `φ[α]` the Jenkins–Strebel differential of `α` whose cylinders have heights `bⱼ`. Then for every
`σ ∈ 𝒮`, `h_{φ[α]}[σ] = Σ bⱼ i(αⱼ, σ)` [misprint corrected, see the module docstring]. -/
theorem lemma12_3 {g n : ℕ} (hR : IsFiniteAnalyticType R g n) {k : ℕ} {α : Fin k → Loop R}
    {b : Fin k → ℝ} (hα : IsJSFormalSum α b) {φ : R → ℂ → ℂ} {A : Fin k → Set R} (hφ : HasJSProperties φ α b A)
    {σ : Loop R} (hσ : IsEssentialLoop σ) :
    qdHeight φ σ = intersectionMap α b σ := by
  sorry

end GardinerLakic2000
