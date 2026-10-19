import References.Katok1992.Ch03.S04_LimitSet

/-!
# Katok 1992, Ch. 3 §3.5 Structure of a Dirichlet region

S. Katok, *Fuchsian Groups* (1992), Chapter 3, §3.5; source `full.md` of `Fuchsian groups (Katok, Svetlana)
…-3766f6b7…`, lines 1620–1704.

* Definition (locally finite fundamental region; l. 1638) — `IsLocallyFiniteRegion`
* Theorem 3.5.1 (a Dirichlet region is locally finite; l. 1640) — `thm3_5_1`
* Definition (congruent points, cycles of vertices, elliptic cycles; l. 1654–1660) — `ellipticSet`, `stabPSL`,
  `ellipticCycles`
* Definition (maximal finite cyclic subgroups up to conjugacy; l. 1663–1668) — `maxFiniteCyclic`, `maxFiniteCyclicClasses`
* Theorem 3.5.2 (elliptic cycles ↔ conjugacy classes of maximal finite cyclic subgroups; l. 1659) — `thm3_5_2`
* Definition (the periods of `Γ`; l. 1663) — `HasPeriods`
* Example A (the modular group: the cycles of the Dirichlet region and the periods `2, 3`; l. 1661, 1668) — omitted: example
  (its content follows from Example A of §3.2 and Theorem 3.5.2)
* Definition (the angle of a region at a point: the measure of its tangent cone) — `rayPoint`, `coneAngle`
* Theorem 3.5.3 (the angle sum at a cycle of vertices is `2π/m`; l. 1671) — `thm3_5_3`
* Theorem 3.5.4 (the side-pairing transformations generate `Γ`; l. 1697) — `IsSidePairing`, `thm3_5_4`

**Conventions.** *Sides and vertices are not modelled as polygons.* A *side-pairing transformation* of a convex fundamental
region `F` is an element `T ≠ Id` such that `F ∩ T F` has two distinct points (then, by convexity, it contains a geodesic
segment of positive length: a side of `F` congruent to a side of `F` via `T`; if `T` is an elliptic element of order 2 whose
fixed point lies in the middle of a side, `F ∩ T F` is this side, as in the book's convention to count the two halves
as two sides). The *angle of a region at a point* `u` is the Lebesgue measure of the set of directions `θ ∈ [0, 2π)`
for which the geodesic ray from `u` in the direction `θ` enters `F` immediately: `coneAngle F u`. Junk check: it is `2π` at
an interior point, `π` at a point inside a geodesic side, the interior angle at a corner of a convex polygon, and `0`
at a point outside `F`; `rayPoint u θ t` is the point at hyperbolic distance `t` from `u` in the direction `θ` (the angle of the
tangent plane `T_u ℍ ≅ ℂ` measured from the horizontal direction; `f`-image of `tanh(t/2) e^{iθ}`, where `f = cayleyKInv`
and the normalization `z ↦ (z − Re u)/Im u` moves `u` to `i`; `f′(i) > 0` so the angles are preserved). Congruent points
are points of one `Γ`-orbit; the elliptic cycles of `F` are the classes of congruent points of `F` with a non-trivial
stabilizer (the vertices fixed by elliptic elements, including the order-2 points on sides).

**Near misses.** `Hubbard2006.polygonVertices`, `Hubbard2006.IsVertexAngle`, `Hubbard2006.vertexAngleSum` (vertices and
angles of the raw data `PolygonData` of a paired polygon: sides are part of the data, here they are not);
`Hubbard2006.prop3_9_13` (the Ford domain of a group with a parabolic element normalized at `∞` is a paired polygon and its
side-pairing elements generate the group, for subgroups of `SL(2, ℝ)`).
-/

open Set Metric Filter Topology MeasureTheory
open scoped UpperHalfPlane MatrixGroups Real Pointwise

noncomputable section

namespace Katok1992

/-- **Definition** (§3.5; l. 1638). A fundamental region `F` for `Γ` is *locally finite* if the tessellation
`{T(F) | T ∈ Γ}` is a locally finite family. -/
def IsLocallyFiniteRegion (Γ : Subgroup PSL(2, ℝ)) (F : Set ℍ) : Prop :=
  IsFundamentalRegion Γ F ∧ IsLocallyFiniteFamily fun T : Γ => (T : PSL(2, ℝ)) • F

/-- **Theorem 3.5.1** (§3.5; l. 1640). A Dirichlet region is locally finite. -/
theorem thm3_5_1 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) {p : ℍ} (hp : ∀ T ∈ Γ, T ≠ 1 → T • p ≠ p) :
    IsLocallyFiniteRegion Γ (dirichletRegion Γ p) := by
  sorry

/-- **The fixed points of the elliptic elements of `Γ`** (§3.5; l. 1654): points of `ℍ` with a non-trivial stabilizer in
`Γ` (an element of `PSL(2, ℝ)` with a fixed point in `ℍ` is elliptic, or the identity). -/
def ellipticSet (Γ : Subgroup PSL(2, ℝ)) : Set ℍ := {z | ∃ T ∈ Γ, T ≠ 1 ∧ T • z = z}

/-- **The stabilizer of `z` in `Γ`**, as a subgroup of `PSL(2, ℝ)`. -/
def stabPSL (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) : Subgroup PSL(2, ℝ) := (MulAction.stabilizer Γ z).map Γ.subtype

/-- **Elliptic cycles of `F`** (§3.5; l. 1654–1660). The points of `F` fixed by elliptic elements of `Γ`, up to congruence
(`u ~ v` if `v = T u`, `T ∈ Γ`; the quotient by the generated equivalence relation). -/
def ellipticCycles (Γ : Subgroup PSL(2, ℝ)) (F : Set ℍ) : Type :=
  Quot fun u v : {z : ℍ // z ∈ F ∧ z ∈ ellipticSet Γ} => ∃ T ∈ Γ, T • (u : ℍ) = (v : ℍ)

/-- **The non-trivial maximal finite cyclic subgroups of `Γ`** (§3.5; l. 1662–1668): finite cyclic subgroups of `Γ`
different from `{Id}` that are not contained in a larger finite cyclic subgroup of `Γ`. -/
def maxFiniteCyclic (Γ : Subgroup PSL(2, ℝ)) : Set (Subgroup PSL(2, ℝ)) :=
  {H | H ≤ Γ ∧ H ≠ ⊥ ∧ IsCyclic H ∧ Finite H ∧
    ∀ K : Subgroup PSL(2, ℝ), H ≤ K → K ≤ Γ → IsCyclic K → Finite K → K = H}

/-- **Conjugacy classes (in `Γ`) of the maximal finite cyclic subgroups** (§3.5): the quotient by the generated relation
`K = g H g⁻¹`, `g ∈ Γ`. -/
def maxFiniteCyclicClasses (Γ : Subgroup PSL(2, ℝ)) : Type :=
  Quot fun H K : maxFiniteCyclic Γ => ∃ g ∈ Γ, (K : Subgroup PSL(2, ℝ)) = (H : Subgroup PSL(2, ℝ)).map (MulAut.conj g).toMonoidHom

/-- **Theorem 3.5.2** (§3.5; l. 1659). Let `F` be a Dirichlet region for `Γ`. The stabilizer of a point of an elliptic
cycle of `F` is a non-trivial maximal finite cyclic subgroup, and there is a one-to-one correspondence between the
elliptic cycles of `F` and the conjugacy classes of non-trivial maximal finite cyclic subgroups of `Γ`, given by
`cycle of u ↦ class of Γ_u`. -/
theorem thm3_5_2 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) {p : ℍ} (hp : ∀ T ∈ Γ, T ≠ 1 → T • p ≠ p) :
    ∃ hmem : ∀ u : {z : ℍ // z ∈ dirichletRegion Γ p ∧ z ∈ ellipticSet Γ}, stabPSL Γ (u : ℍ) ∈ maxFiniteCyclic Γ,
      ∃ e : ellipticCycles Γ (dirichletRegion Γ p) ≃ maxFiniteCyclicClasses Γ,
        ∀ u : {z : ℍ // z ∈ dirichletRegion Γ p ∧ z ∈ ellipticSet Γ},
          e (Quot.mk _ u) = Quot.mk _ ⟨stabPSL Γ (u : ℍ), hmem u⟩ := by
  sorry

/-- **Definition** (§3.5; l. 1663–1668). `m : Fin r → ℕ` is the list of the *periods* of `Γ`: the orders of the non-conjugate
maximal finite cyclic subgroups of `Γ`, each repeated as many times as there are conjugacy classes of that order. -/
def HasPeriods (Γ : Subgroup PSL(2, ℝ)) {r : ℕ} (m : Fin r → ℕ) : Prop :=
  ∃ e : Fin r ≃ maxFiniteCyclicClasses Γ, ∀ i (H : maxFiniteCyclic Γ), e i = Quot.mk _ H → Nat.card (H : Subgroup PSL(2, ℝ)) = m i

/-- **The point at distance `t` from `u` in the direction `θ`** (the geodesic ray of `ℍ` from `u`; the tangent plane at
`u` is `ℂ`, angles measured from the horizontal direction). With `A_u(z) = (z − Re u)/Im u` (so `A_u(u) = i`) and
Katok's Cayley map `f`, `rayPoint u θ t = A_u⁻¹ (f⁻¹ (tanh(t/2) e^{iθ}))`, a point of `ℂ`. -/
def rayPoint (u : ℍ) (θ t : ℝ) : ℂ :=
  (u : ℂ).re + (u : ℂ).im * cayleyKInv ((Real.tanh (t / 2) : ℝ) * Complex.exp (θ * Complex.I))

/-- **The angle of a region at a point** (§3.5; the interior angle at a vertex): the Lebesgue measure of the set of
directions `θ ∈ [0, 2π)` such that the geodesic ray from `u` in the direction `θ` lies in `F` for all small `t > 0`. -/
def coneAngle (F : Set ℍ) (u : ℍ) : ℝ :=
  (volume {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ ∃ ε > 0, ∀ t ∈ Ioo 0 ε, rayPoint u θ t ∈ ((↑) '' F : Set ℂ)}).toReal

/-- **Theorem 3.5.3** (§3.5; l. 1671). Let `F` be a Dirichlet region for `Γ` and `v ∈ ℍ`. Let `θ₁, …, θ_t` be the internal
angles of `F` at the congruent points `u₁, …, u_t` of `F` (the points of `F` in the orbit of `v`) and `m` the order of the
stabilizer of `v` in `Γ`. Then `θ₁ + ⋯ + θ_t = 2π/m`. (The book states it for the vertices of a cycle; for a point that is
not a vertex the sum is `2π` over the one or two points, with `m = 1`.) -/
theorem thm3_5_3 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) {p : ℍ} (hp : ∀ T ∈ Γ, T ≠ 1 → T • p ≠ p) (v : ℍ) :
    ∑ᶠ u ∈ dirichletRegion Γ p ∩ MulAction.orbit Γ v, coneAngle (dirichletRegion Γ p) u =
      2 * π / Nat.card (MulAction.stabilizer Γ v) := by
  sorry

/-- **Side-pairing transformation of `F`** (§3.5; l. 1678–1693). `T ∈ Γ − {Id}` is a side-pairing transformation of `F`
if `F ∩ T F` has two distinct points (a common side of `F` and `T F`; see the module docstring). -/
def IsSidePairing (Γ : Subgroup PSL(2, ℝ)) (F : Set ℍ) (T : PSL(2, ℝ)) : Prop :=
  T ∈ Γ ∧ T ≠ 1 ∧ ∃ x ∈ F ∩ T • F, ∃ y ∈ F ∩ T • F, x ≠ y

/-- **Theorem 3.5.4** (§3.5; l. 1697). Let `{T_i}` be the set of those elements of `Γ` which pair the sides of some fixed
Dirichlet region `F`. Then `{T_i}` is a set of generators for `Γ`. -/
theorem thm3_5_4 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) {p : ℍ} (hp : ∀ T ∈ Γ, T ≠ 1 → T • p ≠ p) :
    Subgroup.closure {T | IsSidePairing Γ (dirichletRegion Γ p) T} = Γ := by
  sorry

end Katok1992
