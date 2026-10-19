import References.GardinerLakic2000.Ch13.S06_Existence

/-!
# Gardiner–Lakic 2000, Ch. 13 §13.8 Slit mappings

Source `teichmuller.txt`, lines 9827–9853.

* Definition (a plane domain bounded by `n` contours, l. 9828) — `IsNContourDomain`
* Definition (a conformal map of `Ω` into the annulus `1 < |w| < R` with the two selected components going to the
  two circles, l. 9828) — `IsAnnularMap`
* Circular slit mapping theorem (l. 9830, 9832) — `para13_8_circular_slit`
* Radial slit mapping theorem (l. 9832) — `para13_8_radial_slit`
* Vertical and horizontal slit mapping theorems (l. 9834) — `para13_8_parallel_slit`

Not items (DESIGN §3): the examples `p(z) dz²/q(z)` (l. 9836–9839), bordered surfaces and their doubles
(l. 9841–9850), and the conformal polygon family (l. 9852; the polygon itself is `IsConformalPolygon` in §13.9).

**Modelling.** The classical theorems are stated as the book states them, as consequences of Theorems 1–2 (their
proofs use `±(dz/z)²` and `±dz²`). A plane domain bounded by `n` contours is a bounded domain whose complement has `n`
components, none of them a single point. "As `|w| → 1`, `z` approaches one component" is `|f(z)| → 1` as `z → A`
within `Ω`. A circular (radial) slit is a component of the annulus minus `f(Ω)` lying in a circle `|w| = r` (in a ray
from `0`). "Unique up to postcomposition by an affine map" is: every other map of the same form is `a f + b`. For the
parallel slit theorems the maps are normalized by `f(z) − z → 0` at `∞` ("suitably normalized", l. 9834) [reading];
a vertical slit is a component of the complement of `f(ℂ ∖ E)` lying in a vertical line.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (annulus)

/-- **Definition** (§13.8, l. 9828). `Ω ⊆ ℂ` is a bounded domain whose complement has `n` components, none of them a
point (the `n` boundary contours). -/
def IsNContourDomain (Ω : Set ℂ) (n : ℕ) : Prop :=
  IsOpen Ω ∧ IsConnected Ω ∧ Bornology.IsBounded Ω ∧
    {K : Set ℂ | ∃ x ∈ Ωᶜ, K = connectedComponentIn Ωᶜ x}.ncard = n ∧
    ∀ x ∈ Ωᶜ, (connectedComponentIn Ωᶜ x).Nontrivial

/-- **Definition** (§13.8, l. 9828). `f` maps `Ω` conformally into `1 < |w| < R`, with `|f(z)| → 1` as `z` approaches
the component `A` of the complement and `|f(z)| → R` as `z` approaches the component `B`. -/
def IsAnnularMap (Ω A B : Set ℂ) (f : ℂ → ℂ) (R : ℝ) : Prop :=
  1 < R ∧ DifferentiableOn ℂ f Ω ∧ InjOn f Ω ∧ f '' Ω ⊆ annulus 1 R ∧
    Tendsto (fun z => ‖f z‖) (𝓝ˢ A ⊓ 𝓟 Ω) (𝓝 1) ∧ Tendsto (fun z => ‖f z‖) (𝓝ˢ B ⊓ 𝓟 Ω) (𝓝 R)

/-- **Unlabelled** (circular slit mapping theorem, §13.8, l. 9830–9832). Let `Ω` be bounded by `n ≥ 3` contours and
`A ≠ B` two components of its complement. Some `f` maps `Ω` into an annulus `1 < |w| < R` as in `IsAnnularMap` with
the smallest possible `R`; the complement of `f(Ω)` in the annulus consists of `n − 2` concentric circular slits; and
any map of `Ω` of this form is `f` up to postcomposition by an affine map. -/
theorem para13_8_circular_slit {Ω : Set ℂ} {n : ℕ} (hΩ : IsNContourDomain Ω n) (hn : 3 ≤ n) {A B : Set ℂ}
    (hA : ∃ x ∈ Ωᶜ, A = connectedComponentIn Ωᶜ x) (hB : ∃ x ∈ Ωᶜ, B = connectedComponentIn Ωᶜ x) (hAB : A ≠ B) :
    ∃ (f : ℂ → ℂ) (R : ℝ), IsAnnularMap Ω A B f R ∧
      {K : Set ℂ | ∃ w ∈ annulus 1 R \ f '' Ω, K = connectedComponentIn (annulus 1 R \ f '' Ω) w}.ncard = n - 2 ∧
      (∀ w ∈ annulus 1 R \ f '' Ω, connectedComponentIn (annulus 1 R \ f '' Ω) w ⊆ sphere 0 ‖w‖) ∧
      (∀ (g : ℂ → ℂ) (R' : ℝ), IsAnnularMap Ω A B g R' → R ≤ R') ∧
      ∀ (g : ℂ → ℂ) (R' : ℝ), IsAnnularMap Ω A B g R' →
        (∀ w ∈ annulus 1 R' \ g '' Ω, connectedComponentIn (annulus 1 R' \ g '' Ω) w ⊆ sphere 0 ‖w‖) →
        ∃ a b : ℂ, ∀ z ∈ Ω, g z = a * f z + b := by
  sorry

/-- **Unlabelled** (radial slit mapping theorem, §13.8, l. 9832). In the situation of the circular slit mapping
theorem, some `f` as in `IsAnnularMap` has the largest possible `R`; the complement of `f(Ω)` in the annulus consists of
`n − 2` radial slits; and any map of `Ω` of this form is `f` up to postcomposition by an affine map. -/
theorem para13_8_radial_slit {Ω : Set ℂ} {n : ℕ} (hΩ : IsNContourDomain Ω n) (hn : 3 ≤ n) {A B : Set ℂ}
    (hA : ∃ x ∈ Ωᶜ, A = connectedComponentIn Ωᶜ x) (hB : ∃ x ∈ Ωᶜ, B = connectedComponentIn Ωᶜ x) (hAB : A ≠ B) :
    ∃ (f : ℂ → ℂ) (R : ℝ), IsAnnularMap Ω A B f R ∧
      {K : Set ℂ | ∃ w ∈ annulus 1 R \ f '' Ω, K = connectedComponentIn (annulus 1 R \ f '' Ω) w}.ncard = n - 2 ∧
      (∀ w ∈ annulus 1 R \ f '' Ω, connectedComponentIn (annulus 1 R \ f '' Ω) w ⊆
        (fun t : ℝ => (t : ℂ) * (w / ‖w‖)) '' Ioi 0) ∧
      (∀ (g : ℂ → ℂ) (R' : ℝ), IsAnnularMap Ω A B g R' → R' ≤ R) ∧
      ∀ (g : ℂ → ℂ) (R' : ℝ), IsAnnularMap Ω A B g R' →
        (∀ w ∈ annulus 1 R' \ g '' Ω, connectedComponentIn (annulus 1 R' \ g '' Ω) w ⊆
          (fun t : ℝ => (t : ℂ) * (w / ‖w‖)) '' Ioi 0) →
        ∃ a b : ℂ, ∀ z ∈ Ω, g z = a * f z + b := by
  sorry

/-- **Unlabelled** (vertical and horizontal slit mapping theorems, §13.8, l. 9834). Let `E ⊆ ℂ` be an obstacle set.
There is a conformal map `f` of `ℂ ∖ E`, normalized by `f(z) − z → 0` at `∞`, onto the complement of finitely many
vertical slits, and likewise a map `g` onto the complement of finitely many horizontal slits. -/
theorem para13_8_parallel_slit {E : Set ℂ} (hE : IsObstacleSet E) :
    (∃ f : ℂ → ℂ, DifferentiableOn ℂ f Eᶜ ∧ InjOn f Eᶜ ∧ Tendsto (fun z => f z - z) (cocompact ℂ) (𝓝 0) ∧
      {K : Set ℂ | ∃ w ∈ (f '' Eᶜ)ᶜ, K = connectedComponentIn (f '' Eᶜ)ᶜ w}.Finite ∧
      ∀ w ∈ (f '' Eᶜ)ᶜ, connectedComponentIn (f '' Eᶜ)ᶜ w ⊆ {u : ℂ | u.re = w.re}) ∧
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Eᶜ ∧ InjOn g Eᶜ ∧ Tendsto (fun z => g z - z) (cocompact ℂ) (𝓝 0) ∧
      {K : Set ℂ | ∃ w ∈ (g '' Eᶜ)ᶜ, K = connectedComponentIn (g '' Eᶜ)ᶜ w}.Finite ∧
      ∀ w ∈ (g '' Eᶜ)ᶜ, connectedComponentIn (g '' Eᶜ)ᶜ w ⊆ {u : ℂ | u.im = w.im} := by
  sorry

end GardinerLakic2000
