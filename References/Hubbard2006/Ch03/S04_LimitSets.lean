import References.Hubbard2006.Ch03.S03_HyperbolicMetric

/-!
# Hubbard 2006, Chapter 3 §3.4: Limit sets and the convex core of a hyperbolic Riemann surface

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 2356–2409.

**Conventions.** A Fuchsian group is a subgroup `Γ ⊆ SL(2, ℝ)` with `LiZhongQC.IsFuchsian Γ`, acting on `ℍ` (`ℍ ≅ 𝔻`).
The boundary `∂ℍ = ℝ ∪ {∞}` is the subset `idealBoundaryH` of `ℂ̄ = LiZhongQC.ExtPlane`; `Γ` acts on `ℂ̄` by the Möbius
transformations of the complexified matrices (`bdryAct`). Hubbard's limit set `Λ_Γ(z) = closure(Γz) ∩ ∂𝔻` is
`limitSetAt Γ z`, the closure in `ℂ̄` of the orbit intersected with `∂ℍ`. The convex hull is the shared
`References.HypConvex` / `References.convexCore` (for torsion-free `Γ`; the hull of a general subset of `𝔻̄` is used
only inside proofs and is not stated). "Non-elementary" is `References.IsNonElementary`.

* Proposition and Definition 3.4.1 (the limit set does not depend on the base point) — `limitSetAt`, `prop3_4_1`
* Remark after Proposition 3.4.1 (closed, empty iff `Γ` finite, circle or Cantor set; cardinal `0, 1, 2` for elementary
  groups) — omitted: unlabelled remark covered by Cor. 3.4.6 and Prop. 3.1.2
* Definition 3.4.2 (convex hull, convex core) — exists: `References.HypConvex`, `References.convexCore`
* Proposition 3.4.3 (the limit set is the smallest closed invariant subset) — `prop3_4_3`
* Exercise 3.4.4 — omitted: exercise (its content is used inside the proof of Prop. 3.4.3 only)
* Corollary 3.4.5 (a) (the limit set is the closure of the fixed points of the hyperbolic elements) — `cor3_4_5_a`
* Corollary 3.4.5 (b) (the same for the parabolic elements, if there are any) — `cor3_4_5_b`
* Corollary 3.4.6 (the limit set of a non-elementary Fuchsian group is the circle or a Cantor set) — `cor3_4_6`
-/

open Set Filter
open scoped Topology
open LiZhongQC

namespace Hubbard2006

/-- The **ideal boundary of `ℍ`** in `ℂ̄`: `ℝ ∪ {∞}`. -/
def idealBoundaryH : Set ExtPlane :=
  {α | α = OnePoint.infty ∨ ∃ x : ℝ, α = OnePoint.some (x : ℂ)}

/-- The action of `γ ∈ SL(2, ℝ)` on `ℂ̄` (and so on `∂ℍ`): the Möbius transformation of its complexification. -/
noncomputable def bdryAct (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : ExtPlane → ExtPlane :=
  mobiusSL (γ.map (algebraMap ℝ ℂ))

/-- **The limit set of `Γ` at `z`** (Prop. and Def. 3.4.1, H1:2360): `Λ_Γ(z) = closure(Γ z) ∩ ∂ℍ`, the closure of the
orbit of `z ∈ ℍ` in `ℂ̄` intersected with the ideal boundary. Near misses: `LiZhongQC.limitSet` and `Katok1992.limitSet`
(limits along sequences of distinct elements; the base point is existentially hidden), which agree for Fuchsian
groups. -/
def limitSetAt (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (z : UpperHalfPlane) : Set ExtPlane :=
  closure (range fun γ : Γ => (OnePoint.some (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z : UpperHalfPlane) : ℂ) :
    ExtPlane)) ∩ idealBoundaryH

/-- **Proposition 3.4.1** (the limit set of a Fuchsian group, Ch. 3 §3.4, H1:2360). If `z₁, z₂ ∈ ℍ`, then
`Λ_Γ(z₁) = Λ_Γ(z₂)`. -/
theorem prop3_4_1 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (z₁ z₂ : UpperHalfPlane) : limitSetAt Γ z₁ = limitSetAt Γ z₂ := by
  sorry

/-- **Proposition 3.4.3** (the limit set is the smallest closed invariant set, Ch. 3 §3.4, H1:2382). Let `Γ` be a
Fuchsian
group whose limit set has more than two points and `Z ⊆ ∂ℍ` a closed non-empty set with `ΓZ = Z`. Then `Λ_Γ ⊆ Z`.
Modelling: `Λ_Γ` is `limitSetAt Γ z` for any `z` (Prop. 3.4.1); `ΓZ = Z` is `bdryAct γ '' Z = Z` for all `γ ∈ Γ`. -/
theorem prop3_4_3 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (z : UpperHalfPlane)
    (hΛ : 2 < (limitSetAt Γ z).encard) {Z : Set ExtPlane} (hZ : Z ⊆ idealBoundaryH) (hcl : IsClosed Z)
    (hne : Z.Nonempty) (hinv : ∀ γ ∈ Γ, bdryAct γ '' Z = Z) : limitSetAt Γ z ⊆ Z := by
  sorry

/-- **Corollary 3.4.5 (a)** (fixed points are dense in the limit set, Ch. 3 §3.4, H1:2400). The limit set of a
non-elementary Fuchsian group is the closure of the set of fixed points (in `∂ℍ`) of its hyperbolic elements. -/
theorem cor3_4_5_a {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hne : References.IsNonElementary Γ) (z : UpperHalfPlane) :
    limitSetAt Γ z = closure {ξ | ξ ∈ idealBoundaryH ∧ ∃ g ∈ Γ, IsHyperbolic g ∧ bdryAct g ξ = ξ} := by
  sorry

/-- **Corollary 3.4.5 (b)** (Ch. 3 §3.4, H1:2400). If a non-elementary Fuchsian group `Γ` contains parabolic elements,
its limit set is also the closure of the set of fixed points of its parabolic elements. -/
theorem cor3_4_5_b {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hne : References.IsNonElementary Γ) (hpar : ∃ g ∈ Γ, IsParabolic g) (z : UpperHalfPlane) :
    limitSetAt Γ z = closure {ξ | ξ ∈ idealBoundaryH ∧ ∃ g ∈ Γ, IsParabolic g ∧ bdryAct g ξ = ξ} := by
  sorry

/-- **Corollary 3.4.6** (Ch. 3 §3.4, H1:2404). The limit set of a non-elementary Fuchsian group is the circle `∂ℍ` or a
Cantor set (non-empty, compact, perfect and totally disconnected). -/
theorem cor3_4_6 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hne : References.IsNonElementary Γ) (z : UpperHalfPlane) :
    limitSetAt Γ z = idealBoundaryH ∨
      ((limitSetAt Γ z).Nonempty ∧ IsCompact (limitSetAt Γ z) ∧ Perfect (limitSetAt Γ z) ∧
        IsTotallyDisconnected (limitSetAt Γ z)) := by
  sorry

end Hubbard2006
