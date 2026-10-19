import References.Katok1992.Ch01.S03_Isometries

/-!
# Katok 1992, Ch. 1 §1.4 Hyperbolic area and the Gauss–Bonnet formula

S. Katok, *Fuchsian Groups* (1992), Chapter 1 *Hyperbolic Geometry*, §1.4; source `full.md` of
`Fuchsian groups (Katok, Svetlana) …-3766f6b7…`, lines 338–412.

* Formula (1.4.1) (the hyperbolic area μ(A) = ∫_A dx dy/y², l. 340–345; cited at l. 693 and throughout Ch. 3–4) —
  exists: `UpperHalfPlane.instMeasureSpace` `UpperHalfPlane.volume_eq_lintegral` (Mathlib's measure on ℍ has density
  1/y² against Lebesgue measure; it is defined on every set, with values in [0, ∞])
* Theorem 1.4.1 (l. 348; cited at l. 385, 1281) — exists: `MeasureTheory.measure_smul`
  `UpperHalfPlane.instSMulInvariantMeasureGeneralLinearGroupFinOfNatNatRealVolume` (stronger: invariance under all of
  GL(2,ℝ), for every set; T(A) = g • A for a lift g of T)
* Definition (hyperbolic n-sided polygon and its vertices, ideal vertices allowed, l. 370; cited at l. 1687, 1802,
  1820, 2047, 2063, 2092) — `IsHypPolygon`
* Definition (hyperbolic triangle and its angles, l. 372–383; cited at l. 1251, 1826, 2120) — `vertexAngle`,
  `polygonAngle`
* Theorem 1.4.2 (Gauss–Bonnet, l. 379; cited at l. 1251, 1826, 2120, hint l. 3299) — `thm1_4_2`

Not items (DESIGN §3): Fig. 2 (the four types of triangles) and "the area of a triangle depends only on its angles"
(l. 375–377; restates Theorem 1.4.2); the steps of the proof (the Jacobian, Cases 1 and 2); the exercises.

**Conventions.** A polygon is a set `P ⊆ ℍ` with a cyclic list of distinct vertices `v : Fin n → ℍ̃` (in `ℂ̂`); side
`i` is the closed geodesic arc `geodArc (v i) (v (i + 1))`. "Bounded by the sides" is: `P` is closed, the closure of
its interior, and its frontier in ℍ is the union of the sides; "no segment of ℝ belongs to a polygon" is: the closure
of `P` in `ℂ̂` meets `ℝ ∪ {∞}` only in vertices (this excludes the outer regions). A triangle is a 3-gon. The angle at
a vertex in ℍ is `hypAngle` between the two sides (in `[0, π]`: the interior angle of a convex polygon), and `0` at a
vertex in `ℝ ∪ {∞}` (l. 383). Areas are `volume` in `[0, ∞]`; finiteness is part of the conclusion.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped UpperHalfPlane MatrixGroups ComplexConjugate Real

noncomputable section

namespace Katok1992

open LiZhongQC (ExtPlane)

/-- **Definition** (§1.4; l. 370). `P` is a hyperbolic `n`-sided polygon with vertices `v 0, …, v (n − 1)` (in this
cyclic order), vertices in `ℝ ∪ {∞}` allowed.
Modelling: see the conventions; `finRotate n` is `i ↦ i + 1` mod `n`. -/
def IsHypPolygon {n : ℕ} (P : Set ℍ) (v : Fin n → ExtPlane) : Prop :=
  3 ≤ n ∧ Function.Injective v ∧ (∀ i, v i ∈ closureH) ∧ IsClosed P ∧ closure (interior P) = P ∧
    frontier P = ⋃ i, geodArc (v i) (v (finRotate n i)) ∧
    closure ((fun z : ℍ => (((z : ℂ)) : ExtPlane)) '' P) ∩ pointsAtInfinity ⊆ range v

/-- **Definition** (§1.4; l. 372–383). The angle at a vertex `p` between the sides towards `q` and `r`: `hypAngle`
for `p ∈ ℍ`, and `0` for `p ∈ ℝ ∪ {∞}` (l. 383). Junk `0` for `p` in the lower half-plane (not a vertex). -/
def vertexAngle (p q r : ExtPlane) : ℝ :=
  p.elim 0 fun a => if h : 0 < a.im then hypAngle ⟨a, h⟩ q r else 0

/-- **Definition** (§1.4; l. 372–383). The angle of the polygon with vertices `v` at the vertex `v i`, between the
sides towards `v (i − 1)` and `v (i + 1)`. -/
def polygonAngle {n : ℕ} (v : Fin n → ExtPlane) (i : Fin n) : ℝ :=
  vertexAngle (v i) (v ((finRotate n).symm i)) (v (finRotate n i))

/-- **Theorem 1.4.2** (Gauss–Bonnet; §1.4; l. 379; cited at l. 1251, 1826, 2120). Let `Δ` be a hyperbolic triangle
with angles `α, β, γ`. Then `μ(Δ) = π − α − β − γ`.
Modelling: a triangle is `IsHypPolygon Δ v` with `v : Fin 3 → ℂ̂` (0 to 3 ideal vertices); `μ(Δ)` is finite. -/
theorem thm1_4_2 {Δ : Set ℍ} {v : Fin 3 → ExtPlane} (hΔ : IsHypPolygon Δ v) :
    volume Δ ≠ ⊤ ∧ (volume Δ).toReal = π - polygonAngle v 0 - polygonAngle v 1 - polygonAngle v 2 := by
  sorry

end Katok1992
