import References.Forster1981.Ch01.S09_DifferentialForms

/-!
# Forster, Chapter 1 §10: The integration of differential forms

Source: O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §10 (`full.md` F1:2751–3270).

Conventions: forms are the coefficient pairs of §9 (`Form1`, `Form2`). Integrals are relations (`HasCurveIntegralRS`,
`HasClosedFormIntegral`, `HasIntegral2`) with the book's well-definedness claims as separate statements (`para10_1`,
`rem10_9`, `para10_18`); the value functions (`curveIntegralRS`, `period`) take the junk value `0` when the relation has no
solution. "The universal covering" quantifies over every universal covering (all are isomorphic). `∬ ω` is the integral of
the coefficient `f` of `ω = f dx ∧ dy`; for the coefficient `c` of `dz ∧ dz̄` one has `f = −2i c`
(`dz ∧ dz̄ = −2i dx ∧ dy`, 9.11). Periods are indexed by Mathlib's `FundamentalGroup`.

* Paragraph 10.1 (piecewise `C^1` curves, `∫_c ω`, F1:2757) — `curveExt`, `IsPartitionFor`, `IsPiecewiseC1`,
  `HasCurveIntegralRS`, `curveIntegralRS`, `para10_1`
* Theorem 10.2 (F1:2783) — `thm10_2`
* Definition 10.3 (primitive, F1:2801) — `IsPrimitive`, `para10_3`
* Paragraph 10.4 (local existence of primitives, F1:2807) — `para10_4_a`, `para10_4_b`
* Theorem 10.5 (F1:2867) — `thm10_5`
* Corollary 10.6 (F1:2877) — `cor10_6`
* Corollary 10.7 (F1:2881) — `cor10_7`
* Theorem 10.8 (F1:2885) — `thm10_8`
* Remark 10.9 (`∫_u ω` for closed `ω`, F1:2899) — `HasClosedFormIntegral`, `rem10_9`
* Theorem 10.10 (F1:2907) — `thm10_10_a`, `thm10_10_b`
* Paragraph 10.11 (periods, F1:2931) — `period`, `para10_11`
* Paragraph 10.12 (summands of automorphy, F1:2959) — `deckAct`, `IsAdditivelyAutomorphic`, `para10_12_a`, `para10_12_b`
* Theorem 10.13 (F1:2977) — `DeckCorrespondence`, `thm10_13_a`, `thm10_13_b`
* Example 10.14 (F1:3005) — `example10_14`
* Theorem 10.15 (F1:3009) — `thm10_15`
* Corollary 10.16 (F1:3025) — `cor10_16`
* Paragraph 10.17 (`∬_U ω`, invariance, F1:3031) — `integral2Plane`, `para10_17`
* Paragraph 10.18 (`∬_X ω`, F1:3069) — `Form2.pointValue`, `Form1.pointValue`, `HasIntegral2`, `para10_18`
* Paragraph 10.19 (Stokes' theorem in the plane, F1:3129) — `circleFormIntegral`, `para10_19`
* Theorem 10.20 (F1:3181) — `thm10_20`
* The Residue Theorem 10.21 (F1:3205) — `thm10_21`
* Corollary 10.22 (F1:3243) — exists: `Forster1981.cor4_25`

Omitted (U−): the sheaf of primitives in the proof of 10.5, the example `dz/z` of 10.11, the remark `f(x) = ∫_{x₀}^x ω`
after 10.15.
-/

open scoped Manifold ContDiff Topology Real
open Set Filter MeasureTheory intervalIntegral

namespace Forster1981

section Defs

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- A curve `c : [0, 1] → X`, extended constantly to `ℝ`. -/
noncomputable def curveExt (c : C(unitInterval, X)) : ℝ → X := Set.IccExtend (zero_le_one : (0 : ℝ) ≤ 1) c

/-- **Admissible subdivision for a piecewise `C^1` curve** (10.1, Ch. 1 §10, F1:2757): `0 = t₀ < ⋯ < tₙ = 1` and points
`x_k` with `c([t_{k-1}, t_k])` inside the chart domain of `x_k` and `chartAt x_k ∘ c` of class `C^1` there. -/
def IsPartitionFor (c : C(unitInterval, X)) (n : ℕ) (t : ℕ → ℝ) (x : ℕ → X) : Prop :=
  t 0 = 0 ∧ t n = 1 ∧ (∀ k < n, t k < t (k + 1)) ∧
    ∀ k < n, (∀ s ∈ Icc (t k) (t (k + 1)), curveExt c s ∈ (chartAt ℂ (x k)).source) ∧
      ContDiffOn ℝ 1 (fun s => chartAt ℂ (x k) (curveExt c s)) (Icc (t k) (t (k + 1)))

/-- **Piecewise `C^1` curves** (10.1, Ch. 1 §10, F1:2757). -/
def IsPiecewiseC1 (c : C(unitInterval, X)) : Prop := ∃ (n : ℕ) (t : ℕ → ℝ) (x : ℕ → X), IsPartitionFor c n t x

/-- **The integral `∫_c ω` along a piecewise `C^1` curve** (10.1, Ch. 1 §10, F1:2757): `v` is the sum over an admissible
subdivision of the integrals `∫ (c10 ∘ z) ż + (c01 ∘ z) conj ż` of the coefficients in the charts, `z = chartAt x_k ∘ c`. -/
def HasCurveIntegralRS (w : Form1 X) (c : C(unitInterval, X)) (v : ℂ) : Prop :=
  ∃ (n : ℕ) (t : ℕ → ℝ) (x : ℕ → X), IsPartitionFor c n t x ∧
    v = ∑ k ∈ Finset.range n, ∫ s in (t k)..(t (k + 1)),
      (w.1 (x k) (chartAt ℂ (x k) (curveExt c s)) * deriv (fun s => chartAt ℂ (x k) (curveExt c s)) s +
        w.2 (x k) (chartAt ℂ (x k) (curveExt c s)) *
          starRingEnd ℂ (deriv (fun s => chartAt ℂ (x k) (curveExt c s)) s))

open scoped Classical in
/-- The value of `∫_c ω` (10.1, Ch. 1 §10, F1:2757); junk value `0` if `c` is not piecewise `C^1`. -/
noncomputable def curveIntegralRS (w : Form1 X) (c : C(unitInterval, X)) : ℂ :=
  if h : ∃ v, HasCurveIntegralRS w c v then h.choose else 0

/-- **Primitives** (Definition 10.3, Ch. 1 §10, F1:2801): `F ∈ ℰ(X)` with `dF = ω`. -/
def IsPrimitive (F : X → ℂ) (w : Form1 X) : Prop :=
  ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F ∧ dForm F = w

/-- **The integral `∫_u ω` of a closed form along a continuous curve** (Remark 10.9, Ch. 1 §10, F1:2899): for some universal
covering `p : X̃ → X`, primitive `F` of `p^*ω` and lift `û` of `u`, the value is `F(û(1)) − F(û(0))`. -/
def HasClosedFormIntegral (w : Form1 X) (u : C(unitInterval, X)) (v : ℂ) : Prop :=
  ∃ (Xt : Type) (_ : TopologicalSpace Xt) (_ : ChartedSpace ℂ Xt), References.IsRiemannSurface Xt ∧
    ∃ p : Xt → X, IsUniversalCovering p ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p ∧
      ∃ F : Xt → ℂ, IsPrimitive F (Form1.pullback p w) ∧
        ∃ û : C(unitInterval, Xt), (fun t => p (û t)) = u ∧ v = F (û 1) - F (û 0)

open scoped Classical in
/-- **The period `∫_σ ω`** of a closed form along a class `σ ∈ π₁(X, x₀)` (10.11, Ch. 1 §10, F1:2931): the value of
`HasClosedFormIntegral` on a representative loop (junk value `0` when there is none, e.g. for non-closed `ω`). -/
noncomputable def period (w : Form1 X) {x₀ : X} (σ : FundamentalGroup X x₀) : ℂ :=
  if h : ∃ v, HasClosedFormIntegral w σ.toPath.out.toContinuousMap v then h.choose else 0

/-- **The action `σ f = f ∘ σ⁻¹` of a covering transformation** (10.12, Ch. 1 §10, F1:2959). -/
def deckAct {Y : Type*} [TopologicalSpace Y] (σ : Y ≃ₜ Y) (f : Y → ℂ) : Y → ℂ := f ∘ σ.symm

/-- **Additive automorphy** (10.12, Ch. 1 §10, F1:2959): `F − σF` is the constant `a_σ` for every covering transformation
`σ` of `p`. -/
def IsAdditivelyAutomorphic {Y : Type*} [TopologicalSpace Y] {Z : Type*} [TopologicalSpace Z] (p : Y → Z) (F : Y → ℂ)
    (a : ↥(deck p) → ℂ) : Prop :=
  ∀ (σ : ↥(deck p)) (y : Y), F y - deckAct σ.1 F y = a σ

/-- **The correspondence `Deck(X̃/X) ≅ π₁(X)`** of the proof of 5.6 (A0.7): the covering transformation `σ` corresponds to
the class `g ∈ π₁(X, p y₀)` of the image `p ∘ v` of a path `v` from `y₀` to `σ y₀`. -/
def DeckCorrespondence {Y : Type*} [TopologicalSpace Y] {Z : Type*} [TopologicalSpace Z] (p : Y → Z)
    (hp : Continuous p) (y₀ : Y) (σ : ↥(deck p)) (g : FundamentalGroup Z (p y₀)) : Prop :=
  ∃ (v : Path y₀ (σ.1 y₀)) (h : p (σ.1 y₀) = p y₀),
    g.toPath = Path.Homotopic.Quotient.mk ((v.map hp).cast rfl h.symm)

/-- **The coefficient of a 2-form in the preferred chart at a point** (10.18, Ch. 1 §10, F1:3069), the pointwise value used
for supports. -/
noncomputable def Form2.pointValue (c : Form2 X) (a : X) : ℂ := c a (chartAt ℂ a a)

/-- **The pointwise value of a 1-form** (10.18, Ch. 1 §10, F1:3069): the pair of coefficients at the chart centre. -/
noncomputable def Form1.pointValue (w : Form1 X) (a : X) : ℂ × ℂ := (w.1 a (chartAt ℂ a a), w.2 a (chartAt ℂ a a))

/-- **The integral `∬_X ω` of a compactly supported 2-form** (10.18, Ch. 1 §10, F1:3069): for a finite family of charts
with compactly supported smooth functions `ρ_k` (supported in the chart domains) summing to `1` on the support of `ω`,
the sum of the plane integrals `∬ (ρ_k ω)` in the charts. -/
def HasIntegral2 (c : Form2 X) (v : ℂ) : Prop :=
  IsCompact (tsupport (Form2.pointValue c)) ∧
    ∃ (n : ℕ) (x : Fin n → X) (ρ : Fin n → X → ℝ),
      (∀ k, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun a => (ρ k a : ℂ)) ∧ tsupport (ρ k) ⊆ (chartAt ℂ (x k)).source) ∧
      (∀ a ∈ tsupport (Form2.pointValue c), ∑ k, ρ k a = 1) ∧
      v = ∑ k, ∫ z in (chartAt ℂ (x k)).target,
        (-2 * Complex.I) * (ρ k ((chartAt ℂ (x k)).symm z) : ℂ) * c (x k) z

end Defs

/-- **The plane integral `∬_U ω`** (10.17, Ch. 1 §10, F1:3031) of `ω = c dz ∧ dz̄` over `U ⊆ ℂ`: the integral of the
coefficient `f = −2i c` of `ω = f dx ∧ dy`. -/
noncomputable def integral2Plane (c : ℂ → ℂ) (U : Set ℂ) : ℂ := ∫ z in U, (-2 * Complex.I) * c z

/-- **The boundary integral of `ω = f dx + g dy`** over the circle of radius `R` (10.19, Ch. 1 §10, F1:3129), with
parametrization `θ ↦ R e^{iθ}`. -/
noncomputable def circleFormIntegral (f g : ℂ → ℂ) (R : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..2 * π,
    (f (R * Complex.exp (θ * Complex.I)) * (Complex.I * (R * Complex.exp (θ * Complex.I))).re +
      g (R * Complex.exp (θ * Complex.I)) * (Complex.I * (R * Complex.exp (θ * Complex.I))).im)

section Statements

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Paragraph 10.1** (Ch. 1 §10, F1:2757). The integral `∫_c ω` of a differentiable 1-form along a piecewise `C^1` curve
exists and is independent of the subdivision and the charts. -/
theorem para10_1 {w : Form1 X} (hw : w.IsForm) (hs : w.IsSmoothOn univ) {c : C(unitInterval, X)}
    (hc : IsPiecewiseC1 c) :
    (∃ v, HasCurveIntegralRS w c v) ∧ ∀ v₁ v₂, HasCurveIntegralRS w c v₁ → HasCurveIntegralRS w c v₂ → v₁ = v₂ := by
  sorry

/-- **Theorem 10.2** (Ch. 1 §10, F1:2783). For a piecewise `C^1` curve `c` and `F ∈ ℰ(X)`: `∫_c dF = F(c(1)) − F(c(0))`. -/
theorem thm10_2 {c : C(unitInterval, X)} (hc : IsPiecewiseC1 c) {F : X → ℂ}
    (hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F) : HasCurveIntegralRS (dForm F) c (F (c 1) - F (c 0)) := by
  sorry

/-- **Paragraph 10.3** (Ch. 1 §10, F1:2801). If `F` is a primitive of `ω`, so is `F + c` for a constant `c`, and any two
primitives of `ω` differ by a constant. -/
theorem para10_3 {w : Form1 X} {F : X → ℂ} (hF : IsPrimitive F w) :
    (∀ c : ℂ, IsPrimitive (fun x => F x + c) w) ∧ ∀ G, IsPrimitive G w → ∃ c : ℂ, ∀ x, G x = F x + c := by
  sorry

/-- **Paragraph 10.4(a)** (Ch. 1 §10, F1:2807). On a disc `{|z| < r}`, every closed 1-form `ω = f dx + g dy` has a primitive
`F(x, y) = ∫₀¹ (f(tx, ty) x + g(tx, ty) y) dt`; in the coefficients of `dz`, `dz̄` this is
`F(z) = ∫₀¹ (c10(tz) z + c01(tz) z̄) dt`.
Modelling: the surface is `ℂ` and the form is read on the disc through the set argument of the predicates. -/
theorem para10_4_a {r : ℝ} (hr : 0 < r) {w : Form1 ℂ} (hw : w.IsForm) (hc : w.IsClosed (Metric.ball 0 r)) :
    ∃ F : ℂ → ℂ, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F (Metric.ball 0 r) ∧ Form1.EqOn w (dForm F) (Metric.ball 0 r) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) r,
        F z = ∫ t in (0 : ℝ)..1, (w.1 0 (t * z) * z + w.2 0 (t * z) * starRingEnd ℂ z) := by
  sorry

/-- **Paragraph 10.4(b)** (Ch. 1 §10, F1:2807). A holomorphic 1-form `ω = f dz` on a disc has a holomorphic primitive. -/
theorem para10_4_b {r : ℝ} (hr : 0 < r) {w : Form1 ℂ} (hw : w.IsForm) (hh : w.IsHolomorphicOn (Metric.ball 0 r)) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball 0 r) ∧ Form1.EqOn w (dForm F) (Metric.ball 0 r) := by
  sorry

/-- **Theorem 10.5** (Ch. 1 §10, F1:2867). For a closed 1-form `ω ∈ ℰ^(1)(X)` there are a covering `p : X̂ → X` with `X̂`
a Riemann surface and a primitive `F ∈ ℰ(X̂)` of `p^*ω`. -/
theorem thm10_5 {w : Form1 X} (hw : w.IsForm) (hc : w.IsClosed univ) :
    ∃ (Xh : Type) (_ : TopologicalSpace Xh) (_ : ChartedSpace ℂ Xh), References.IsRiemannSurface Xh ∧
      ∃ p : Xh → X, IsCoveringMap p ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p ∧ ∃ F, IsPrimitive F (Form1.pullback p w) := by
  sorry

/-- **Corollary 10.6** (Ch. 1 §10, F1:2877). On the universal covering `π : X̃ → X`, the form `π^*ω` of a closed
1-form `ω` has a primitive. -/
theorem cor10_6 {Xt : Type} [TopologicalSpace Xt] [T2Space Xt] [ConnectedSpace Xt] [ChartedSpace ℂ Xt]
    [IsManifold 𝓘(ℂ) ω Xt] {p : Xt → X} (hp : IsUniversalCovering p) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p)
    {w : Form1 X} (hw : w.IsForm) (hc : w.IsClosed univ) : ∃ F, IsPrimitive F (Form1.pullback p w) := by
  sorry

/-- **Corollary 10.7** (Ch. 1 §10, F1:2881). On a simply connected Riemann surface every closed 1-form has a primitive. -/
theorem cor10_7 [SimplyConnectedSpace X] {w : Form1 X} (hw : w.IsForm) (hc : w.IsClosed univ) :
    ∃ F, IsPrimitive F w := by
  sorry

/-- **Theorem 10.8** (Ch. 1 §10, F1:2885). Let `p : X̃ → X` be the universal covering, `ω` a closed 1-form, `F` a primitive
of `p^*ω`, `c` a piecewise `C^1` curve in `X` and `ĉ` a lifting of `c`. Then `∫_c ω = F(ĉ(1)) − F(ĉ(0))`. -/
theorem thm10_8 {Xt : Type} [TopologicalSpace Xt] [T2Space Xt] [ConnectedSpace Xt] [ChartedSpace ℂ Xt]
    [IsManifold 𝓘(ℂ) ω Xt] {p : Xt → X} (hp : IsUniversalCovering p) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p)
    {w : Form1 X} (hw : w.IsForm) (hc : w.IsClosed univ) {F : Xt → ℂ} (hF : IsPrimitive F (Form1.pullback p w))
    {c : C(unitInterval, X)} (hcc : IsPiecewiseC1 c) {ĉ : C(unitInterval, Xt)} (hl : (fun t => p (ĉ t)) = c) :
    HasCurveIntegralRS w c (F (ĉ 1) - F (ĉ 0)) := by
  sorry

/-- **Remark 10.9** (Ch. 1 §10, F1:2899). For a closed 1-form the value `F(û(1)) − F(û(0))` does not depend on the
universal covering, the primitive or the lifting, so `∫_u ω` of a continuous curve is well defined (and agrees with 10.1 for
piecewise `C^1` curves, by 10.8). -/
theorem rem10_9 {w : Form1 X} (hw : w.IsForm) (hc : w.IsClosed univ) (u : C(unitInterval, X)) :
    (∃ v, HasClosedFormIntegral w u v) ∧ (∀ v₁ v₂, HasClosedFormIntegral w u v₁ → HasClosedFormIntegral w u v₂ → v₁ = v₂) ∧
      (IsPiecewiseC1 u → ∀ v, HasClosedFormIntegral w u v ↔ HasCurveIntegralRS w u v) := by
  sorry

/-- **Theorem 10.10(a)** (Ch. 1 §10, F1:2907). For a closed 1-form, homotopic curves (with fixed endpoints) have the same
integral. -/
theorem thm10_10_a {w : Form1 X} (hw : w.IsForm) (hc : w.IsClosed univ) {a b : X} {u v : Path a b}
    (huv : u.Homotopic v) (r : ℂ) :
    HasClosedFormIntegral w u.toContinuousMap r ↔ HasClosedFormIntegral w v.toContinuousMap r := by
  sorry

/-- **Theorem 10.10(b)** (Ch. 1 §10, F1:2907). For a closed 1-form, free homotopic closed curves have the same integral. -/
theorem thm10_10_b {w : Form1 X} (hw : w.IsForm) (hc : w.IsClosed univ) {x y : X} {u : Path x x} {v : Path y y}
    (huv : AreFreeHomotopic u v) (r : ℂ) :
    HasClosedFormIntegral w u.toContinuousMap r ↔ HasClosedFormIntegral w v.toContinuousMap r := by
  sorry

/-- **Paragraph 10.11** (Ch. 1 §10, F1:2931). For a closed 1-form, `∫_{σ·τ} ω = ∫_σ ω + ∫_τ ω`, so `σ ↦ ∫_σ ω` is a
homomorphism `π₁(X) → ℂ` (the period homomorphism).
Modelling: `FundamentalGroup` carries the opposite multiplication of Forster's, which is immaterial for a homomorphism
into the commutative group `ℂ`. -/
theorem para10_11 {w : Form1 X} (hw : w.IsForm) (hc : w.IsClosed univ) (x₀ : X) (σ τ : FundamentalGroup X x₀) :
    period w (σ * τ) = period w σ + period w τ := by
  sorry

/-- **Paragraph 10.12(a)** (Ch. 1 §10, F1:2959). Let `F` be additively automorphic with summands `a_σ`. Then
`a_{στ} = a_σ + a_τ`: the summands form a homomorphism `Deck(X̃/X) → ℂ`. Modelling: `Xt` is nonempty (a surface); for the empty
type the premise is vacuous and the conclusion false. -/
theorem para10_12_a {Xt : Type} [TopologicalSpace Xt] [Nonempty Xt] {Z : Type} [TopologicalSpace Z] {p : Xt → Z} {F : Xt → ℂ}
    {a : ↥(deck p) → ℂ} (ha : IsAdditivelyAutomorphic p F a) (σ τ : ↥(deck p)) : a (σ * τ) = a σ + a τ := by
  sorry

/-- **Paragraph 10.12(b)** (Ch. 1 §10, F1:2959). For the universal covering `p : X̃ → X`, a function `F` on `X̃` invariant
under all covering transformations is `p^*f₀` for a unique `f₀ : X → ℂ`, which is differentiable (holomorphic) if `F` is. -/
theorem para10_12_b {Xt : Type} [TopologicalSpace Xt] [T2Space Xt] [ConnectedSpace Xt] [ChartedSpace ℂ Xt]
    [IsManifold 𝓘(ℂ) ω Xt] {p : Xt → X} (hp : IsUniversalCovering p) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p)
    {F : Xt → ℂ} (hinv : ∀ σ : ↥(deck p), deckAct σ.1 F = F) :
    ∃ f₀ : X → ℂ, F = f₀ ∘ p ∧ (∀ g : X → ℂ, F = g ∘ p → g = f₀) ∧
      (ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F → ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f₀) ∧
      (MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f₀) := by
  sorry

/-- **Theorem 10.13(a)** (Ch. 1 §10, F1:2977). A primitive `F` of `p^*ω` (`ω` closed, `p` the universal covering) is
additively automorphic with constant summands, which are the periods of `ω`: `a_σ = ∫_{[σ]} ω` under `π₁(X) ≅ Deck(X̃/X)`.
Modelling: as printed ("the summands are exactly the periods"); the last display of the book's proof ends with `−a_σ`,
contradicting its own `−a_σ := σF − F` (a sign slip in the proof, A0.12(6)). -/
theorem thm10_13_a {Xt : Type} [TopologicalSpace Xt] [T2Space Xt] [ConnectedSpace Xt] [ChartedSpace ℂ Xt]
    [IsManifold 𝓘(ℂ) ω Xt] {p : Xt → X} (hp : IsUniversalCovering p) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p)
    {w : Form1 X} (hw : w.IsForm) (hc : w.IsClosed univ) {F : Xt → ℂ} (hF : IsPrimitive F (Form1.pullback p w))
    (y₀ : Xt) :
    ∃ a : ↥(deck p) → ℂ, IsAdditivelyAutomorphic p F a ∧
      ∀ (σ : ↥(deck p)) (g : FundamentalGroup X (p y₀)), DeckCorrespondence p hp.1.continuous y₀ σ g → a σ = period w g := by
  sorry

/-- **Theorem 10.13(b)** (Ch. 1 §10, F1:2977). Conversely, an additively automorphic `F ∈ ℰ(X̃)` with constant summands
satisfies `dF = p^*ω` for exactly one closed `ω ∈ ℰ^(1)(X)`. -/
theorem thm10_13_b {Xt : Type} [TopologicalSpace Xt] [T2Space Xt] [ConnectedSpace Xt] [ChartedSpace ℂ Xt]
    [IsManifold 𝓘(ℂ) ω Xt] {p : Xt → X} (hp : IsUniversalCovering p) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p)
    {F : Xt → ℂ} (hF : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F) {a : ↥(deck p) → ℂ}
    (ha : IsAdditivelyAutomorphic p F a) :
    ∃! w : Form1 X, w.IsForm ∧ w.IsClosed univ ∧ dForm F = Form1.pullback p w := by
  sorry

/-- **Example 10.14** (Ch. 1 §10, F1:3005). On the torus `X = ℂ/Γ` there is a holomorphic 1-form `ω` with `π^*ω = dz`
whose periods are exactly the elements of `Γ`. -/
theorem example10_14 (L : PeriodPair) {pr : ℂ → X} (hpr : IsTorusProjection L pr) (x₀ : X) :
    ∃ w : Form1 X, w.IsForm ∧ w.IsHolomorphicOn univ ∧ Form1.pullback pr w = dForm id ∧
      Set.range (period w : FundamentalGroup X x₀ → ℂ) = (L.lattice : Set ℂ) := by
  sorry

/-- **Theorem 10.15** (Ch. 1 §10, F1:3009). A closed 1-form `ω ∈ ℰ^(1)(X)` has a primitive on `X` if and only if all its
periods vanish. -/
theorem thm10_15 {w : Form1 X} (hw : w.IsForm) (hc : w.IsClosed univ) :
    (∃ F, IsPrimitive F w) ↔ ∀ (x₀ : X) (σ : FundamentalGroup X x₀), period w σ = 0 := by
  sorry

/-- **Corollary 10.16** (Ch. 1 §10, F1:3025). On a compact Riemann surface, two holomorphic 1-forms with the same period
homomorphism are equal. -/
theorem cor10_16 [CompactSpace X] {w₁ w₂ : Form1 X} (h₁ : w₁.IsForm) (h₂ : w₂.IsForm) (hh₁ : w₁.IsHolomorphicOn univ)
    (hh₂ : w₂.IsHolomorphicOn univ) (hp : ∀ (x₀ : X) (σ : FundamentalGroup X x₀), period w₁ σ = period w₂ σ) :
    w₁ = w₂ := by
  sorry

/-- **Paragraph 10.17** (Ch. 1 §10, F1:3031). For a biholomorphic map `φ : V → U` of open sets of `ℂ` and a continuous
2-form `ω = c dz ∧ dz̄` with compact support in `U`: `∬_U ω = ∬_V φ^*ω`, the pull-back having coefficient
`c(φ(z)) |φ′(z)|²`. -/
theorem para10_17 {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ V)
    (hinj : InjOn φ V) (himg : φ '' V = U) {c : ℂ → ℂ} (hcc : Continuous c) (hsupp : IsCompact (tsupport c))
    (hsub : tsupport c ⊆ U) :
    integral2Plane c U = integral2Plane (fun z => c (φ z) * ((‖deriv φ z‖ ^ 2 : ℝ) : ℂ)) V := by
  sorry

/-- **Paragraph 10.18** (Ch. 1 §10, F1:3069). The integral `∬_X ω` of a compactly supported differentiable 2-form exists and
does not depend on the charts and the partition of unity chosen. -/
theorem para10_18 {c : Form2 X} (hc : c.IsForm) (hs : c.IsSmoothOn univ) (hcs : IsCompact (tsupport (Form2.pointValue c))) :
    (∃ v, HasIntegral2 c v) ∧ ∀ v₁ v₂, HasIntegral2 c v₁ → HasIntegral2 c v₂ → v₁ = v₂ := by
  sorry

/-- **Paragraph 10.19** (Stokes' theorem in the plane, Ch. 1 §10, F1:3129). Let `ω = f dx + g dy` be a differentiable
1-form on an open `U ⊆ ℂ`. For the annulus `A = {ε ≤ |z| ≤ R} ⊆ U`:
`∬_A (g_x − f_y) dx dy = ∫_{|z|=R} ω − ∫_{|z|=ε} ω`, and for a closed disc `{|z| ≤ R} ⊆ U`:
`∬ (g_x − f_y) dx dy = ∫_{|z|=R} ω`. -/
theorem para10_19 {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ} (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U) :
    (∀ ε R : ℝ, 0 < ε → ε < R → {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R} ⊆ U →
      ∫ z in {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ R}, (fderiv ℝ g z 1 - fderiv ℝ f z Complex.I) =
        circleFormIntegral f g R - circleFormIntegral f g ε) ∧
    (∀ R : ℝ, 0 < R → Metric.closedBall (0 : ℂ) R ⊆ U →
      ∫ z in Metric.closedBall (0 : ℂ) R, (fderiv ℝ g z 1 - fderiv ℝ f z Complex.I) = circleFormIntegral f g R) := by
  sorry

/-- **Theorem 10.20** (Ch. 1 §10, F1:3181). For a differentiable 1-form `ω` with compact support on `X`: `∬_X dω = 0`. -/
theorem thm10_20 {w : Form1 X} (hw : w.IsForm) (hs : w.IsSmoothOn univ) (hcs : IsCompact (tsupport (Form1.pointValue w))) :
    HasIntegral2 (Form1.d w) 0 := by
  sorry

/-- **The Residue Theorem 10.21** (Ch. 1 §10, F1:3205). Let `X` be a compact Riemann surface, `a₁, …, aₙ` distinct points
and `ω` a holomorphic 1-form on `X \ {a₁, …, aₙ}`. Then the residues exist and `Σ Res_{a_k}(ω) = 0`. -/
theorem thm10_21 [CompactSpace X] (S : Finset X) {w : Form1 X} (hw : w.IsForm) (hh : w.IsHolomorphicOn (↑S)ᶜ) :
    (∃ r : X → ℂ, ∀ a ∈ S, HasResidue w a (r a)) ∧
      ∀ r : X → ℂ, (∀ a ∈ S, HasResidue w a (r a)) → ∑ a ∈ S, r a = 0 := by
  sorry

end Statements

end Forster1981
