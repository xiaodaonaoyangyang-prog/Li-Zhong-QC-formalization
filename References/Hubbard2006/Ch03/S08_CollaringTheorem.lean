import References.Hubbard2006.Ch03.S07_IdealBoundaries

/-!
# Hubbard 2006, Chapter 3 §3.8: The collaring theorem

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 2618–2712.

**Conventions.** A complete hyperbolic surface is `X = ℍ/Γ` (torsion-free Fuchsian `Γ`, uniformization `p`). A simple
closed
geodesic is the image `p '' axisH g` of the axis of a hyperbolic `g ∈ Γ` that is simple modulo `⟨g⟩`
(`IsSimpleAxis p g`); its
length is `translationLength g`. Distances in `ℍ` are Mathlib's `dist` (curvature `−1`). A **`δ`-collar** (Def. 3.8.2)
is
modelled as the injectivity of the projection of the `δ`-neighbourhood of the axis modulo `⟨g⟩` (`AdmitsCollar`): the
neighbourhood `A_δ(γ) = p(N_δ(axis))` is then isometric to `N_δ(axis)/⟨g⟩`, the `δ`-neighbourhood of the unique simple
closed
geodesic of the cylinder of modulus `π/l` (Prop. 3.3.7). A *simple geodesic* entering a collar is a complete geodesic
line of
`ℍ` projecting injectively (`IsSimpleGeodesicLine`), or a closed one.

* Exercise 3.8.1 (formula for the collar function) — omitted: exercise (the function `collarFn` is defined by the
  formula)
* Definition 3.8.2 (collar function `η`; collar) — `collarFn`, `IsSimpleAxis`, `AdmitsCollar`
* Theorem 3.8.3 (the collaring theorem) — `thm3_8_3`
* Remark 3.8.4 (`η` is maximal) — omitted: remark (not cited)
* Corollary 3.8.5 (`ℓ₂ < 2η(ℓ₁)` ⇒ equal or disjoint) — `cor3_8_5`
* Remark 3.8.6 (sharpness of the bound `2η`) — omitted: remark (its sharp instance is part of Cor. 3.8.7)
* Corollary 3.8.7 (a) (geodesics shorter than `ln(3 + 2√2)` are equal or disjoint) — `cor3_8_7_a`
* Corollary 3.8.7 (b) (`ln(3 + 2√2)` is the largest such number) — `cor3_8_7_b`
* Corollary 3.8.8 (a simple geodesic entering a collar meets the core geodesic or spirals toward it) — `cor3_8_8`
* Proposition 3.8.9 (collars around punctures) — `prop3_8_9`
-/

open Set Filter Metric
open scoped Manifold ContDiff Topology Real
open LiZhongQC References

namespace Hubbard2006

/-- **The collar function** `η(l) = ½ ln ((cosh (l/2) + 1)/(cosh (l/2) − 1))` (Def. 3.8.2, formula (3.8.1)): the
distance
between a geodesic `γ ⊂ ℍ` and the geodesic `δ` joining the endpoints of the perpendiculars to `γ` at the ends of a
segment of
`γ` of length `l`. *Junk:* for `l = 0` the quotient is `1/0 = 0` (and `ln 0 = 0`); `η` is used for `l > 0`. -/
noncomputable def collarFn (l : ℝ) : ℝ :=
  (1 / 2) * Real.log ((Real.cosh (l / 2) + 1) / (Real.cosh (l / 2) - 1))

/-- **`g` is a simple hyperbolic element for `p`**: `g` is hyperbolic and two points of its axis with the same image
under
`p` differ by a power of `g` (so `p '' axisH g` is a simple closed geodesic and `g` is primitive modulo `±1`). -/
def IsSimpleAxis {X : Type*} (p : UpperHalfPlane → X) (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Prop :=
  IsHyperbolic g ∧ ∀ z ∈ axisH g, ∀ w ∈ axisH g, p z = p w → ∃ n : ℤ, w = g ^ n • z

/-- **`δ`-collar around a simple closed geodesic** (Def. 3.8.2): the projection `p` is injective modulo `⟨g⟩` on the
`δ`-neighbourhood of the axis of `g` (if `z` is at distance `< δ` from the axis and `p w = p z`, then `w = g^n z`). -/
def AdmitsCollar {X : Type*} (p : UpperHalfPlane → X) (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (δ : ℝ) : Prop :=
  ∀ z w : UpperHalfPlane, infDist z (axisH g) < δ → p z = p w → ∃ n : ℤ, w = g ^ n • z

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Theorem 3.8.3** (the collaring theorem, Ch. 3 §3.8, H1:2653). Let `X` be a complete hyperbolic surface and `Y` a
(finite or
infinite) collection of disjoint simple closed geodesics. Then each geodesic `p '' axisH g ∈ Y`, of length
`ℓ = translationLength g`,
admits an `η(ℓ)`-collar, and the collars around two distinct geodesics of `Y` are disjoint. -/
theorem thm3_8_3 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) {Y : Set (Set X)}
    (hY : ∀ C ∈ Y, IsSimpleClosedGeodesicOf Γ p C) (hdisj : Y.Pairwise Disjoint) :
    (∀ g ∈ Γ, IsSimpleAxis p g → p '' axisH g ∈ Y → AdmitsCollar p g (collarFn (translationLength g))) ∧
    ∀ g ∈ Γ, ∀ h ∈ Γ, IsSimpleAxis p g → IsSimpleAxis p h → p '' axisH g ∈ Y → p '' axisH h ∈ Y →
      p '' axisH g ≠ p '' axisH h → ∀ z w : UpperHalfPlane,
        infDist z (axisH g) < collarFn (translationLength g) →
        infDist w (axisH h) < collarFn (translationLength h) → p z ≠ p w := by
  sorry

/-- **Corollary 3.8.5** (Ch. 3 §3.8, H1:2668). Let `γ₁ = p '' axisH g₁`, `γ₂ = p '' axisH g₂` be simple closed geodesics
of
lengths `ℓ₁`, `ℓ₂`. If `ℓ₂ < 2η(ℓ₁)`, then `γ₁ = γ₂` or `γ₁ ∩ γ₂ = ∅`. -/
theorem cor3_8_5 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) {g₁ g₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h₁ : g₁ ∈ Γ) (h₂ : g₂ ∈ Γ) (hs₁ : IsSimpleAxis p g₁) (hs₂ : IsSimpleAxis p g₂)
    (hl : translationLength g₂ < 2 * collarFn (translationLength g₁)) :
    p '' axisH g₁ = p '' axisH g₂ ∨ Disjoint (p '' axisH g₁) (p '' axisH g₂) := by
  sorry

/-- **Corollary 3.8.7 (a)** (Ch. 3 §3.8, H1:2677). Two simple closed geodesics of lengths `< ln(3 + 2√2)` are equal or
disjoint. -/
theorem cor3_8_7_a {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) {g₁ g₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h₁ : g₁ ∈ Γ) (h₂ : g₂ ∈ Γ) (hs₁ : IsSimpleAxis p g₁) (hs₂ : IsSimpleAxis p g₂)
    (hl₁ : translationLength g₁ < Real.log (3 + 2 * √2)) (hl₂ : translationLength g₂ < Real.log (3 + 2 * √2)) :
    p '' axisH g₁ = p '' axisH g₂ ∨ Disjoint (p '' axisH g₁) (p '' axisH g₂) := by
  sorry

/-- **Corollary 3.8.7 (b)** (sharpness, Ch. 3 §3.8, H1:2677). The number `ln(3 + 2√2)` is the largest for which (a)
holds: there is
a hyperbolic surface (the once-punctured torus `𝔻/⟨A, B⟩`) with two distinct, intersecting simple closed geodesics of
length
exactly `ln(3 + 2√2)`. -/
theorem cor3_8_7_b :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : ConnectedSpace X) (_ : ChartedSpace ℂ X)
      (_ : IsManifold 𝓘(ℂ) ω X) (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → X),
      IsFuchsian Γ ∧ ActsFreely Γ ∧ IsUniformization Γ p ∧
        ∃ g₁ ∈ Γ, ∃ g₂ ∈ Γ, IsSimpleAxis p g₁ ∧ IsSimpleAxis p g₂ ∧
          translationLength g₁ = Real.log (3 + 2 * √2) ∧ translationLength g₂ = Real.log (3 + 2 * √2) ∧
          p '' axisH g₁ ≠ p '' axisH g₂ ∧ ¬ Disjoint (p '' axisH g₁) (p '' axisH g₂) := by
  sorry

/-- **Corollary 3.8.8** (Ch. 3 §3.8, H1:2687). Let `X` be a complete hyperbolic surface and `γ = p '' axisH g` a simple
closed
geodesic of length `ℓ` with its collar. A simple geodesic line `δ = p ∘ f` (`f : ℝ → ℍ` an isometric embedding, `p ∘ f`
injective) that enters the collar around `γ` (`d(f t, axis) < η(ℓ)` for some `t`, at the lift `f t`) either intersects
`γ` or
spirals toward `γ` (the distance in `ℍ` from `f t` to the set `p⁻¹(γ)` of all lifts of `γ` tends to `0` as `t → +∞` or
as
`t → −∞`). A simple *closed* geodesic that enters the collar intersects `γ`. -/
theorem cor3_8_8 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) {g : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hg : g ∈ Γ) (hs : IsSimpleAxis p g) :
    (∀ f : ℝ → UpperHalfPlane, Isometry f → Function.Injective (p ∘ f) →
      (∃ t, infDist (f t) (axisH g) < collarFn (translationLength g)) →
      (∃ t, p (f t) ∈ p '' axisH g) ∨
        Tendsto (fun t => infDist (f t) (p ⁻¹' (p '' axisH g))) atTop (𝓝 0) ∨
        Tendsto (fun t => infDist (f t) (p ⁻¹' (p '' axisH g))) atBot (𝓝 0)) ∧
    ∀ h ∈ Γ, IsSimpleAxis p h → (∃ z ∈ axisH h, infDist z (axisH g) < collarFn (translationLength g)) →
      ¬ Disjoint (p '' axisH h) (p '' axisH g) := by
  sorry

/-- **Proposition 3.8.9** (collars around punctures, Ch. 3 §3.8, H1:2698). Let `X*` be a hyperbolic surface with a
puncture,
modelled with the cusp at `∞`: `T = (z ↦ z + 1) ∈ Γ` generates (up to `±1`) the stabilizer of `∞`. Let
`V = {Im z > 1/2}`, the region above the horocycle of length `2` (the horocycle `Im z = 1/2` has length `2` modulo `T`).
Then `p : V → X*` is an embedding modulo `⟨T⟩` (`p z = p w` with `z, w ∈ V` implies `w = Tⁿ z`), and its image
`A_x = p(V)` is
disjoint from the collars `p(N_η(ℓ)(axis h))` around all simple closed geodesics `p '' axisH h` of `X*`. -/
theorem prop3_8_9 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hp : IsUniformization Γ p)
    {T : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hT : T ∈ Γ) (hT00 : T 0 0 = 1) (hT01 : T 0 1 = 1) (hT10 : T 1 0 = 0)
    (hT11 : T 1 1 = 1) (hstab : ∀ h ∈ Γ, h 1 0 = 0 → ∃ n : ℤ, h = T ^ n ∨ h = -T ^ n) :
    (∀ z w : UpperHalfPlane, 1 / 2 < z.im → 1 / 2 < w.im → p z = p w → ∃ n : ℤ, w = T ^ n • z) ∧
    ∀ h ∈ Γ, IsSimpleAxis p h → ∀ z w : UpperHalfPlane, 1 / 2 < z.im →
      infDist w (axisH h) < collarFn (translationLength h) → p z ≠ p w := by
  sorry

end Hubbard2006
