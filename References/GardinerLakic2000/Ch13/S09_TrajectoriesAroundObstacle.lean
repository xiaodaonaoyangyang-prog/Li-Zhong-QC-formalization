import References.GardinerLakic2000.Ch13.S08_SlitMappings

/-!
# Gardiner–Lakic 2000, Ch. 13 §13.9 Trajectories around the obstacle

Source `teichmuller.txt`, lines 9854–9896.

* Definition (conformal polygon: the unit disc with `n ≥ 4` marked vertices on its boundary, l. 9852, 9873) —
  `IsConformalPolygon`
* Definition (the strips `S_k` of `φ` and the horizontally slit rectangles `R_k` of `ψ`, l. 9875, 9884) —
  `slitRect`, `IsSlitStripSystem`
* Theorem 6 (l. 9877), properties (1)–(5) — `thm13_6`

Not items (DESIGN §3): the properties 1–5 for a general surface (l. 9866–9870, restated in Theorem 6 for polygons),
the exercises (l. 9890–9896).

**Modelling.** The quadratic differentials "belonging to `P`" are `aSigma σ` (§13.1). A strip system of `q` on `D`
is a finite family of branches `hₖ` of the inverse of the natural parameter `∫ q^{1/2} dz`, defined on rectangles
`(0, aₖ) × (0, bₖ)` with finitely many closed horizontal slits removed (`q(hₖ(ζ)) hₖ′(ζ)² = 1`), injective with
disjoint images, whose vertical sides go to the sides `s₁ₖ`, `s₂ₖ` of `P`; outside the images, `D` is covered by
finitely many horizontal arcs of `q` and finitely many points (critical trajectories and critical points). So `aₖ` is
the width and `bₖ` the height of the strip or rectangle, as in the book (l. 9875). The strips of `φ` (no slits) are
part of the conclusion, as the book asserts them (l. 9875). "Only finitely many horizontal trajectories of `ψ`
terminate at `E`" is: finitely many horizontal arcs contain every horizontal arc of `ψ` in `P ∖ E` whose closure meets
`E`. The five properties share the witnesses `ψ`, `R_k`, `S_k`, so Theorem 6 is one conjunction (the inventory planned
`thm13_6_a`–`_e`) [reading]. The norm of `ψ` is `∬_{P∖E} |ψ|`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (unitDisc phiArea phiLengthPath IsHorizontalArc)

/-- **Definition** (conformal polygon, §13.8 l. 9852, §13.9 l. 9873). The unit disc with a set `σ` of `n ≥ 4` marked
vertices on its boundary. -/
def IsConformalPolygon (σ : Finset ℂ) : Prop := (↑σ : Set ℂ) ⊆ sphere 0 1 ∧ 4 ≤ σ.card

/-- Helper (§13.9). The rectangle `(0, a) × (0, b)` with the set `L` (of horizontal slits) removed. -/
def slitRect (a b : ℝ) (L : Set ℂ) : Set ℂ := Ioo 0 a ×ℂ Ioo 0 b \ L

/-- **Definition** (§13.9, l. 9875, 9884). A strip system of `q` on `D ⊆ Δ` for the polygon `σ` (see the module
docstring): branches `hₖ` of the inverse natural parameter on the slit rectangles `(0, aₖ) × (0, bₖ) ∖ Lₖ`, where
`Lₖ` is a finite union of closed horizontal segments, with disjoint images in `D`, left and right vertical sides going
to the sides of `P` through `s₁ₖ` and `s₂ₖ`, and covering `D` up to finitely many horizontal arcs and points. -/
def IsSlitStripSystem (σ : Finset ℂ) (q : ℂ → ℂ) (D : Set ℂ) {m : ℕ} (a b : Fin m → ℝ) (L : Fin m → Set ℂ)
    (h : Fin m → ℂ → ℂ) (s₁ s₂ : Fin m → ℂ) : Prop :=
  (∀ k, 0 < a k ∧ 0 < b k ∧
    (∃ (N : ℕ) (x₁ x₂ y : Fin N → ℝ), (∀ j, 0 ≤ x₁ j ∧ x₁ j < x₂ j ∧ x₂ j ≤ a k ∧ 0 < y j ∧ y j < b k) ∧
      L k = ⋃ j, Icc (x₁ j) (x₂ j) ×ℂ {y j}) ∧
    DifferentiableOn ℂ (h k) (slitRect (a k) (b k) (L k)) ∧ InjOn (h k) (slitRect (a k) (b k) (L k)) ∧
    h k '' slitRect (a k) (b k) (L k) ⊆ D ∧
    (∀ ζ ∈ slitRect (a k) (b k) (L k), q (h k ζ) * deriv (h k) ζ ^ 2 = 1) ∧
    (∀ y ∈ Ioo 0 (b k), Tendsto (h k) (𝓝[slitRect (a k) (b k) (L k)] (y * I))
      (𝓝ˢ (closure (circleSide σ (s₁ k))))) ∧
    ∀ y ∈ Ioo 0 (b k), Tendsto (h k) (𝓝[slitRect (a k) (b k) (L k)] (a k + y * I))
      (𝓝ˢ (closure (circleSide σ (s₂ k))))) ∧
  (∀ k l, k ≠ l → Disjoint (h k '' slitRect (a k) (b k) (L k)) (h l '' slitRect (a l) (b l) (L l))) ∧
  ∃ (N : ℕ) (α : Fin N → ℝ → ℂ) (F : Finset ℂ), (∀ j, IsHorizontalArc q (α j) 0 1) ∧
    D \ ⋃ k, h k '' slitRect (a k) (b k) (L k) ⊆ (⋃ j, α j '' Icc 0 1) ∪ ↑F

/-- **Theorem 6** (§13.9, l. 9877). Let `P = (Δ, σ)` be a conformal polygon, `φ ≠ 0` a quadratic differential belonging
to `P` with its strips `S_k` (width `a_k`, height `b_k`), and `E ⊆ Δ` compact with finitely many simply connected
components. Then some `ψ` holomorphic on `P ∖ E` has:
(1) only finitely many horizontal trajectories of `ψ` terminate at `E`;
(2) branches of `Ψ = ∫ ψ^{1/2} dz` map `P ∖ E` onto horizontally slit rectangles `R_k` whose vertical sides lie on
sides of `P`;
(3) `R_k` joins the same sides as `S_k` and has the same height `b_k`;
(4) every crosscut in `P ∖ E` joining the sides joined by `S_k` has `|ψ|^{1/2}`-length at least the width `a′_k` of
`R_k`;
(5) `‖ψ‖ = Σ a′_k b_k ≥ Σ a_k b_k = ‖φ‖`, with strict inequality unless `ψ = φ`. -/
theorem thm13_6 {σ : Finset ℂ} (hσ : IsConformalPolygon σ) {φ : ℂ → ℂ} (hφ : φ ∈ aSigma σ)
    (hφ0 : ∃ z ∈ unitDisc, φ z ≠ 0) {E : Set ℂ} (hE : IsObstacleSet E) (hEΔ : E ⊆ unitDisc) :
    ∃ (m : ℕ) (a b a' : Fin m → ℝ) (L : Fin m → Set ℂ) (hφs hψs : Fin m → ℂ → ℂ) (s₁ s₂ : Fin m → ℂ)
      (ψ : ℂ → ℂ),
      IsSlitStripSystem σ φ unitDisc a b (fun _ => ∅) hφs s₁ s₂ ∧ DifferentiableOn ℂ ψ (unitDisc \ E) ∧
      (∃ (N : ℕ) (α : Fin N → ℝ → ℂ), (∀ j, IsHorizontalArc ψ (α j) 0 1) ∧
        ∀ c : ℝ → ℂ, IsHorizontalArc ψ c 0 1 → c '' Ioo 0 1 ⊆ unitDisc \ E →
          (closure (c '' Ioo 0 1) ∩ E).Nonempty → c '' Ioo 0 1 ⊆ ⋃ j, α j '' Icc 0 1) ∧
      IsSlitStripSystem σ ψ (unitDisc \ E) a' b L hψs s₁ s₂ ∧
      (∀ k {x y : ℂ} (γ : Path x y), IsCrosscut σ γ → range γ ∩ E = ∅ →
        ((x ∈ circleSide σ (s₁ k) ∧ y ∈ circleSide σ (s₂ k)) ∨
          (x ∈ circleSide σ (s₂ k) ∧ y ∈ circleSide σ (s₁ k))) →
        ENNReal.ofReal (a' k) ≤ phiLengthPath (fun _ : ℂ => ψ) γ) ∧
      phiArea ψ (unitDisc \ E) = ENNReal.ofReal (∑ k, a' k * b k) ∧
      phiArea φ unitDisc = ENNReal.ofReal (∑ k, a k * b k) ∧ ∑ k, a k * b k ≤ ∑ k, a' k * b k ∧
      ((∀ z ∈ unitDisc \ E, ψ z = φ z) ∨ ∑ k, a k * b k < ∑ k, a' k * b k) := by
  sorry

end GardinerLakic2000
