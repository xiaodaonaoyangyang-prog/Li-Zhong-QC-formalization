import References.Forster1981.Ch01.S04_BranchedAndUnbranchedCoverings

/-!
# Forster, Chapter 1 §5: The universal covering and covering transformations

Source: O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §5 (`full.md` F1:1375–1650).

Conventions: a manifold is a Hausdorff space with a charted structure over `ℝⁿ` (`EuclideanSpace ℝ (Fin n)`); the group
of covering transformations `Deck(Y/X)` is Mathlib's `deck p`; `π₁` is `FundamentalGroup` (whose multiplication is the
opposite of Forster's; the groups are isomorphic by inversion, so isomorphism statements are insensitive to the order).
`D`, `D*`, `H` (left half plane) and `ℂ*` are the open submanifolds `unitDiscOpen`, `punctUnitDisc`, `leftHalfPlane`,
`punctPlane` of `ℂ`; `p_k(z) = zᵏ`.

* Definition 5.1 (universal covering, F1:1379) — `IsUniversalCovering`
* Theorem 5.2 (F1:1383) — `thm5_2`
* Theorem 5.3 (F1:1387) — `thm5_3`
* Remark after 5.3 (the universal covering of a Riemann surface is a Riemann surface, F1:1435) — exists:
  `LiZhongQC.exists_universal_covering` (a project statement, currently unproved)
* Definition 5.4 (covering transformations, F1:1437) — exists: `deck`
* Definition 5.5 (Galois covering, F1:1439) — `IsGaloisCovering`
* Theorem 5.6 (F1:1447) — `thm5_6_a`, `thm5_6_b`
* Examples 5.7 (F1:1475) — `expToPunctPlane`, `expToPunctDisc`, `example5_7_a`, `example5_7_b`, `example5_7_c`,
  `example5_7_c_cons`
* Definition 5.8 (equivalence modulo a subgroup, F1:1515) — exists: `MulAction.orbitRel`
* Theorem 5.9 (F1:1517) — `thm5_9`
* Theorem 5.10 (F1:1527) — `thm5_10_i`, `thm5_10_ii`
* Theorem 5.11 (F1:1565) — `thm5_11`

Helpers (not book notions): the open submanifolds `unitDiscOpen`, `punctUnitDisc`, `leftHalfPlane`, `punctPlane` of `ℂ`.
Omitted (U−): uniqueness of the universal covering up to isomorphism (F1:1381), the remark, example and "cf. (8.12)"
around 5.5 (F1:1439–1445), Remark (18.3) after 5.7 (F1:1513).
-/

open scoped Manifold ContDiff Topology References
open Set Filter

universe u v

namespace Forster1981

open scoped Forster1981

/-- The unit disc `D`, as an open submanifold of `ℂ` (helper). -/
def unitDiscOpen : TopologicalSpace.Opens ℂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

/-- The punctured unit disc `D* = D ∖ {0}`, as an open submanifold of `ℂ` (helper). -/
def punctUnitDisc : TopologicalSpace.Opens ℂ :=
  ⟨Metric.ball 0 1 \ {0}, Metric.isOpen_ball.sdiff isClosed_singleton⟩

/-- The left half plane `H = {z : Re z < 0}`, as an open submanifold of `ℂ` (helper). -/
def leftHalfPlane : TopologicalSpace.Opens ℂ := ⟨{z | z.re < 0}, isOpen_lt Complex.continuous_re continuous_const⟩

/-- The punctured plane `ℂ* = ℂ ∖ {0}`, as an open submanifold of `ℂ` (helper). -/
def punctPlane : TopologicalSpace.Opens ℂ := ⟨{0}ᶜ, isOpen_compl_singleton⟩

/-- The exponential map `exp : ℂ → ℂ*` (Example 5.7(a)). -/
noncomputable def expToPunctPlane (z : ℂ) : ↥punctPlane := ⟨Complex.exp z, Complex.exp_ne_zero z⟩

/-- The exponential map `exp : H → D*` of the left half plane onto the punctured disc (Example 5.7(b)). -/
noncomputable def expToPunctDisc (z : ↥leftHalfPlane) : ↥punctUnitDisc :=
  ⟨Complex.exp z, by
    refine ⟨?_, ?_⟩
    · have hz : (z : ℂ).re < 0 := z.2
      simp only [Metric.mem_ball, dist_zero_right, Complex.norm_exp]
      exact Real.exp_lt_one_iff.2 hz
    · exact Complex.exp_ne_zero z⟩

/-- **Definition 5.1** (universal covering, Ch. 1 §5, F1:1379). A covering map `p : Y → X` with `Y` connected is a
*universal covering* of `X` if for every covering map `q : Z → X` with `Z` connected and all `y₀`, `z₀` with
`p(y₀) = q(z₀)` there is exactly one fibre-preserving continuous map `f : Y → Z` (`q ∘ f = p`) with `f(y₀) = z₀`.
Modelling: `Z` is taken in the universe of `Y`. -/
def IsUniversalCovering {Y : Type u} {X : Type v} [TopologicalSpace Y] [TopologicalSpace X] (p : Y → X) : Prop :=
  IsCoveringMap p ∧ ConnectedSpace Y ∧ ∀ (Z : Type u) [TopologicalSpace Z] (q : Z → X), IsCoveringMap q →
    ConnectedSpace Z → ∀ (y₀ : Y) (z₀ : Z), p y₀ = q z₀ → ∃! f : C(Y, Z), (q ∘ f) = p ∧ f y₀ = z₀

/-- **Definition 5.5** (Galois covering, Ch. 1 §5, F1:1439). A covering map `p : Y → X` is *Galois* (normal, regular) if
for any two points `y₀, y₁` of the same fibre there is a covering transformation `σ` with `σ(y₀) = y₁`. -/
def IsGaloisCovering {Y : Type u} {X : Type v} [TopologicalSpace Y] [TopologicalSpace X] (p : Y → X) : Prop :=
  IsCoveringMap p ∧ ∀ y₀ y₁ : Y, p y₀ = p y₁ → ∃ σ ∈ deck p, σ y₀ = y₁

/-- **Theorem 5.2** (Ch. 1 §5, F1:1383). Let `X`, `Y` be connected manifolds, `Y` simply connected, and `p : Y → X` a
covering map. Then `p` is the universal covering of `X`. -/
theorem thm5_2 {n : ℕ} {X Y : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y] [SimplyConnectedSpace Y] {p : Y → X} (hp : IsCoveringMap p) :
    IsUniversalCovering p := by
  sorry

/-- **Theorem 5.3** (Ch. 1 §5, F1:1387). Every connected manifold `X` has a connected, simply connected manifold `X̃`
together with a covering map `p : X̃ → X` (which is then the universal covering). -/
theorem thm5_3 {n : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] :
    ∃ (Xt : Type) (_ : TopologicalSpace Xt) (_ : ChartedSpace (EuclideanSpace ℝ (Fin n)) Xt),
      T2Space Xt ∧ ConnectedSpace Xt ∧ SimplyConnectedSpace Xt ∧ ∃ p : Xt → X, IsCoveringMap p := by
  sorry

/-- **Theorem 5.6(a)** (Ch. 1 §5, F1:1447). The universal covering `p : X̃ → X` of a connected manifold is a Galois
covering. -/
theorem thm5_6_a {n : ℕ} {X Xt : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [TopologicalSpace Xt] {p : Xt → X} (hp : IsUniversalCovering p) :
    IsGaloisCovering p := by
  sorry

/-- **Theorem 5.6(b)** (Ch. 1 §5, F1:1447). For the universal covering `p : X̃ → X` of a connected manifold, the group
of covering transformations is isomorphic to the fundamental group: `Deck(X̃/X) ≅ π₁(X)`.
Modelling: `π₁` is Mathlib's `FundamentalGroup` (the opposite multiplication; the groups are isomorphic by inversion, so the
existence of an isomorphism is the book's statement). -/
theorem thm5_6_b {n : ℕ} {X Xt : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [TopologicalSpace Xt] {p : Xt → X} (hp : IsUniversalCovering p)
    (x₀ : X) : Nonempty (deck p ≃* FundamentalGroup X x₀) := by
  sorry

/-- **Example 5.7(a)** (Ch. 1 §5, F1:1475). The exponential function `exp : ℂ → ℂ*` is the universal covering of `ℂ*`; its
covering transformations are the translations `z ↦ z + 2πin` (`n ∈ ℤ`), and `π₁(ℂ*) ≅ ℤ`. -/
theorem example5_7_a :
    IsUniversalCovering expToPunctPlane ∧
      (∀ σ ∈ deck expToPunctPlane, ∃ n : ℤ, ∀ z, σ z = z + 2 * Real.pi * Complex.I * n) ∧
      (∀ n : ℤ, ∃ σ ∈ deck expToPunctPlane, ∀ z, σ z = z + 2 * Real.pi * Complex.I * n) ∧
      Nonempty (FundamentalGroup ↥punctPlane (⟨1, one_ne_zero⟩ : ↥punctPlane) ≃* Multiplicative ℤ) := by
  sorry

/-- **Example 5.7(b)** (Ch. 1 §5, F1:1485). The exponential function `exp : H → D*` is the universal covering of the
punctured disc; its covering transformations are the translations by `2πin` (`n ∈ ℤ`), and `π₁(D*) ≅ ℤ`. -/
theorem example5_7_b :
    IsUniversalCovering expToPunctDisc ∧
      (∀ σ ∈ deck expToPunctDisc, ∃ n : ℤ, ∀ z, (σ z : ℂ) = z + 2 * Real.pi * Complex.I * n) ∧
      (∀ n : ℤ, ∃ σ ∈ deck expToPunctDisc, ∀ z, (σ z : ℂ) = z + 2 * Real.pi * Complex.I * n) ∧
      ∃ x₀ : ↥punctUnitDisc, Nonempty (FundamentalGroup ↥punctUnitDisc x₀ ≃* Multiplicative ℤ) := by
  sorry

/-- **Example 5.7(c)** (Ch. 1 §5, F1:1495). For a lattice `Γ = ℤω₁ + ℤω₂`, the projection `π : ℂ → ℂ/Γ` onto the torus is
the universal covering; its covering transformations are the translations `z ↦ z + γ` (`γ ∈ Γ`), and
`π₁(ℂ/Γ) ≅ Γ ≅ ℤ × ℤ`. -/
theorem example5_7_c {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (L : PeriodPair) {π : ℂ → X} (hπ : IsTorusProjection L π) (x₀ : X) :
    IsUniversalCovering π ∧ (∀ σ ∈ deck π, ∃ g ∈ L.lattice, ∀ z, σ z = z + g) ∧
      (∀ g ∈ L.lattice, ∃ σ ∈ deck π, ∀ z, σ z = z + g) ∧
      Nonempty (FundamentalGroup X x₀ ≃* Multiplicative ↥L.lattice) ∧
      Nonempty (FundamentalGroup X x₀ ≃* Multiplicative (ℤ × ℤ)) := by
  sorry

/-- **Consequence of Example 5.7(c)** (Ch. 1 §5, F1:1511). No holomorphic function on a torus `ℂ/Γ` into `ℙ¹` (that is,
no doubly periodic meromorphic function) has, modulo `Γ`, a single pole of first order: a non-constant holomorphic
`F : X → ℙ¹` does not take the value `∞` exactly once, counting multiplicities. -/
theorem example5_7_c_cons {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (L : PeriodPair) {π : ℂ → X} (hπ : IsTorusProjection L π)
    {F : X → References.RiemannSphere} (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hnc : ¬ ∃ c, ∀ x, F x = c) :
    valenceCount F References.RiemannSphere.infty ≠ 1 := by
  sorry

/-- **Theorem 5.9** (Ch. 1 §5, F1:1517). Let `X`, `Y` be connected manifolds, `q : Y → X` a covering map and
`p : X̃ → X` the universal covering. Then every fibre-preserving continuous map `f : X̃ → Y` (`q ∘ f = p`) is a covering
map, and there is a subgroup `G ⊆ Deck(X̃/X)` such that `f(x) = f(x′)` iff `x` and `x′` are equivalent modulo `G`;
moreover `G ≅ π₁(Y)`. -/
theorem thm5_9 {n : ℕ} {X Y Xt : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y] [TopologicalSpace Xt] {q : Y → X} (hq : IsCoveringMap q)
    {p : Xt → X} (hp : IsUniversalCovering p) {f : Xt → Y} (hf : Continuous f) (hfq : (q ∘ f) = p) (y₀ : Y) :
    IsCoveringMap f ∧ ∃ G : Subgroup (deck p), (∀ x x' : Xt, f x = f x' ↔ ∃ σ : G, ((σ : deck p) : Xt ≃ₜ Xt) x = x') ∧
      Nonempty (G ≃* FundamentalGroup Y y₀) := by
  sorry

/-- **Theorem 5.10(i)** (Ch. 1 §5, F1:1527). Let `f : X → D*` be an unbranched holomorphic covering map of a Riemann
surface onto the punctured disc. If `f` has infinitely many sheets, there is a biholomorphic map `φ : X → H` with
`exp ∘ φ = f`. -/
theorem thm5_10_i {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {f : X → ↥punctUnitDisc} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hc : IsCoveringMap f)
    (hu : IsUnbranched f) (hinf : ∃ y, ¬ (f ⁻¹' {y}).Finite) :
    ∃ φ : X → ↥leftHalfPlane, LiZhongQC.IsBiholomorphic φ ∧ ∀ x, Complex.exp (φ x) = (f x : ℂ) := by
  sorry

/-- **Theorem 5.10(ii)** (Ch. 1 §5, F1:1527). Let `f : X → D*` be an unbranched holomorphic covering map of a Riemann
surface onto the punctured disc. If `f` is `k`-sheeted, there is a biholomorphic map `φ : X → D*` with `φ(x)ᵏ = f(x)`
(`p_k ∘ φ = f`). -/
theorem thm5_10_ii {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {f : X → ↥punctUnitDisc} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hc : IsCoveringMap f)
    (hu : IsUnbranched f) {k : ℕ} (hk : 1 ≤ k) (hsheets : ∀ y, (f ⁻¹' {y}).Finite ∧ (f ⁻¹' {y}).ncard = k) :
    ∃ φ : X → ↥punctUnitDisc, LiZhongQC.IsBiholomorphic φ ∧ ∀ x, (φ x : ℂ) ^ k = (f x : ℂ) := by
  sorry

/-- **Theorem 5.11** (Ch. 1 §5, F1:1565). Let `f : X → D` be a proper non-constant holomorphic map of a Riemann surface
into the unit disc which is unbranched over `D*`. Then there are `k ≥ 1` and a biholomorphic map `φ : X → D` with
`φ(x)ᵏ = f(x)` (`p_k ∘ φ = f`). -/
theorem thm5_11 {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {f : X → ↥unitDiscOpen} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hp : IsProperMap f)
    (hnc : ¬ ∃ c, ∀ x, f x = c) (hu : ∀ x, (f x : ℂ) ≠ 0 → ¬ IsBranchPoint f x) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ φ : X → ↥unitDiscOpen, LiZhongQC.IsBiholomorphic φ ∧ ∀ x, (φ x : ℂ) ^ k = (f x : ℂ) := by
  sorry

end Forster1981
