/- Derived from https://github.com/mccorvie/classification-of-surfaces (commit e3c7230fe78d7b056a415d9ecae6f77887046b32),
   Apache License 2.0. Modified for LiZhongQC: bundled with other upstream files, imports renamed,
   local proof repairs. See NOTICE.Classification and LICENSE.Apache-2.0 in this directory. -/
/- Classification layer 02: pinned sources; see BUNDLE_MAP.json and licenses/. -/
import LiZhongExternal.Classification.SchottkyClassification01
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Convex.Segment
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.Order.Fin.Finset

/- BEGIN ClassificationOfSurfaces.Moise.AmbientHomeomorph | 63d5bda4196b8a9e69836f9b7ac2a98f01b3464eda22d21378a9162362940940 -/
section r78_classification02_block_01
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Extending a homeomorphism of a closed planar patch

Moise's elementary free-triangle move is first constructed on a finite polygonal patch.  Since
the move fixes the patch frontier, it extends to an ambient homeomorphism by the identity.  This
file proves that pasting step independently of the particular triangulated patch.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- Changing only the proof that a point belongs to an equal set does not change the point. -/
theorem coe_setCongr_apply {X : Type*} [TopologicalSpace X] {s t : Set X}
    (h : s = t) (z : s) : ((Homeomorph.setCongr h z : t) : X) = z := by
  subst t
  rfl

namespace TriangleMesh

variable (M : TriangleMesh)

/-- Repositioning a fixed abstract triangle mesh gives a canonical homeomorphism between the old
and new geometric supports, obtained by preserving barycentric coordinates. -/
noncomputable def repositionHomeomorph (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex))) :
    M.toPlaneComplex.support ≃ₜ
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.support :=
  (M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2).symm.trans
    ((M.reposition position' hposition_injective haffineIndependent
      htriangle_inter).toPlaneComplex.realizationHomeomorph
        (M.reposition position' hposition_injective haffineIndependent
          htriangle_inter).toPlaneComplex_isPure2)

@[simp] theorem repositionHomeomorph_apply_realization (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (x : GeometricRealization M.toPlaneComplex.Vertex M.toPlaneComplex.cells) :
    M.repositionHomeomorph position' hposition_injective haffineIndependent htriangle_inter
        (M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2 x) =
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.realizationHomeomorph
          (M.reposition position' hposition_injective haffineIndependent
            htriangle_inter).toPlaneComplex_isPure2 x := by
  exact congrArg
    ((M.reposition position' hposition_injective haffineIndependent
      htriangle_inter).toPlaneComplex.realizationHomeomorph
        (M.reposition position' hposition_injective haffineIndependent
          htriangle_inter).toPlaneComplex_isPure2)
    ((M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2).symm_apply_apply x)

theorem coe_repositionHomeomorph_apply_realization (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (x : GeometricRealization M.toPlaneComplex.Vertex M.toPlaneComplex.cells) :
    (M.repositionHomeomorph position' hposition_injective haffineIndependent htriangle_inter
        (M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2 x) : Plane) =
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.baryEval x.1 := by
  exact congrArg Subtype.val (M.repositionHomeomorph_apply_realization position'
    hposition_injective haffineIndependent htriangle_inter x)

theorem coe_repositionHomeomorph_apply (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (z : M.toPlaneComplex.support) :
    (M.repositionHomeomorph position' hposition_injective haffineIndependent
        htriangle_inter z : Plane) =
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.baryEval
          ((M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2).symm z).1 := by
  let x := (M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2).symm z
  have hz : z = M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2 x := by
    exact
      (M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2).apply_symm_apply z |>.symm
  change (M.repositionHomeomorph position' hposition_injective haffineIndependent
      htriangle_inter z : Plane) =
    (M.reposition position' hposition_injective haffineIndependent
      htriangle_inter).toPlaneComplex.baryEval x.1
  rw [hz, repositionHomeomorph_apply_realization]
  rfl

theorem coe_repositionHomeomorph_trans_setCongr_apply
    (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (hsupport :
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.support = M.toPlaneComplex.support)
    (z : M.toPlaneComplex.support) :
    (((M.repositionHomeomorph position' hposition_injective haffineIndependent
        htriangle_inter).trans (Homeomorph.setCongr hsupport)) z : Plane) =
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.baryEval
          ((M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2).symm z).1 := by
  exact M.coe_repositionHomeomorph_apply position' hposition_injective haffineIndependent
    htriangle_inter z

end TriangleMesh

/-- Extend a homeomorphism of a closed planar patch by the identity outside the patch. -/
noncomputable def extendHomeomorphByIdentity {P : Set Plane} (hP : IsClosed P)
    (e : P ≃ₜ P)
    (hfrontier : ∀ x (hx : x ∈ frontier P), (e ⟨x, hP.frontier_subset hx⟩).1 = x) :
    Plane ≃ₜ Plane := by
  classical
  let f : Plane → Plane := fun x => if hx : x ∈ P then (e ⟨x, hx⟩).1 else x
  let g : Plane → Plane := fun x => if hx : x ∈ P then (e.symm ⟨x, hx⟩).1 else x
  have hgf : Function.LeftInverse g f := by
    intro x
    by_cases hx : x ∈ P
    · simp [f, g, hx]
    · simp [f, g, hx]
  have hfg : Function.RightInverse g f := by
    intro x
    by_cases hx : x ∈ P
    · simp [f, g, hx]
    · simp [f, g, hx]
  have hfrontierSymm :
      ∀ x (hx : x ∈ frontier P), (e.symm ⟨x, hP.frontier_subset hx⟩).1 = x := by
    intro x hx
    have he : e ⟨x, hP.frontier_subset hx⟩ = ⟨x, hP.frontier_subset hx⟩ := by
      apply Subtype.ext
      exact hfrontier x hx
    have := congrArg Subtype.val (e.symm_apply_eq.mpr he.symm)
    exact this
  have hfContinuousOn : ContinuousOn f P := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hcont : Continuous fun x : P => (e x).1 :=
      continuous_subtype_val.comp e.continuous
    convert hcont using 1
    funext x
    simp [f, x.property]
  have hgContinuousOn : ContinuousOn g P := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hcont : Continuous fun x : P => (e.symm x).1 :=
      continuous_subtype_val.comp e.symm.continuous
    convert hcont using 1
    funext x
    simp [g, x.property]
  have hfContinuous : Continuous f := by
    have hpaste : Set.piecewise P f id = f := by
      funext x
      by_cases hx : x ∈ P <;> simp [Set.piecewise, f, hx]
    rw [← hpaste]
    apply continuous_piecewise
    · intro x hx
      have hxP := hP.frontier_subset hx
      simp [f, hxP, hfrontier x hx]
    · simpa [hP.closure_eq] using hfContinuousOn
    · exact continuous_id.continuousOn
  have hgContinuous : Continuous g := by
    have hpaste : Set.piecewise P g id = g := by
      funext x
      by_cases hx : x ∈ P <;> simp [Set.piecewise, g, hx]
    rw [← hpaste]
    apply continuous_piecewise
    · intro x hx
      have hxP := hP.frontier_subset hx
      simp [g, hxP, hfrontierSymm x hx]
    · simpa [hP.closure_eq] using hgContinuousOn
    · exact continuous_id.continuousOn
  exact
    { toEquiv := Equiv.mk f g hgf hfg
      continuous_toFun := hfContinuous
      continuous_invFun := hgContinuous }

theorem extendHomeomorphByIdentity_apply_mem {P : Set Plane} (hP : IsClosed P)
    (e : P ≃ₜ P)
    (hfrontier : ∀ x (hx : x ∈ frontier P), (e ⟨x, hP.frontier_subset hx⟩).1 = x)
    {x : Plane} (hx : x ∈ P) :
    extendHomeomorphByIdentity hP e hfrontier x = (e ⟨x, hx⟩).1 := by
  classical
  simp [extendHomeomorphByIdentity, hx]

theorem extendHomeomorphByIdentity_apply_not_mem {P : Set Plane} (hP : IsClosed P)
    (e : P ≃ₜ P)
    (hfrontier : ∀ x (hx : x ∈ frontier P), (e ⟨x, hP.frontier_subset hx⟩).1 = x)
    {x : Plane} (hx : x ∉ P) :
    extendHomeomorphByIdentity hP e hfrontier x = x := by
  classical
  simp [extendHomeomorphByIdentity, hx]

namespace TriangleMesh

variable (M : TriangleMesh)

/-- A repositioning with unchanged support and fixed support frontier extends to an ambient plane
homeomorphism. -/
noncomputable def ambientRepositionHomeomorph (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (hsupport :
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.support = M.toPlaneComplex.support)
    (hfrontier : ∀ x (hx : x ∈ frontier M.toPlaneComplex.support),
      (((M.repositionHomeomorph position' hposition_injective haffineIndependent
        htriangle_inter).trans (Homeomorph.setCongr hsupport))
          ⟨x, M.toPlaneComplex.isCompact_support.isClosed.frontier_subset hx⟩).1 = x) :
    Plane ≃ₜ Plane :=
  extendHomeomorphByIdentity M.toPlaneComplex.isCompact_support.isClosed
    ((M.repositionHomeomorph position' hposition_injective haffineIndependent
      htriangle_inter).trans (Homeomorph.setCongr hsupport)) hfrontier

theorem ambientRepositionHomeomorph_eqOn_compl (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (hsupport :
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.support = M.toPlaneComplex.support)
    (hfrontier : ∀ x (hx : x ∈ frontier M.toPlaneComplex.support),
      (((M.repositionHomeomorph position' hposition_injective haffineIndependent
        htriangle_inter).trans (Homeomorph.setCongr hsupport))
          ⟨x, M.toPlaneComplex.isCompact_support.isClosed.frontier_subset hx⟩).1 = x) :
    Set.EqOn
      (M.ambientRepositionHomeomorph position' hposition_injective haffineIndependent
        htriangle_inter hsupport hfrontier)
      id M.toPlaneComplex.supportᶜ := by
  intro x hx
  exact extendHomeomorphByIdentity_apply_not_mem _ _ _ hx

end TriangleMesh

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end r78_classification02_block_01
/- END ClassificationOfSurfaces.Moise.AmbientHomeomorph -/

/- BEGIN ClassificationOfSurfaces.Moise.BrokenLine | 146fe660bd345e0f82c767f0daa77c0f358952f5d11a483509482a0439b9b2cd -/
section r78_classification02_block_02
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Broken-line connectivity of open connected sets in the plane

Moise, *Geometric Topology in Dimensions 2 and 3*, Ch. 1: any two points of an open connected
subset of the plane are joined by a broken line (a finite polygonal chain of straight segments)
lying in the set.  This is the elementary input to the PL-approximation chapter (Thm 6.1); see
the docstrings of `ClassificationOfSurfaces/Moise/PLApproximation.lean` for the wider context.

`JoinedByBrokenLine U a b` records a chain of `n` segments inside `U` from `a` to `b`, as a
vertex list `v : Fin (n + 1) → Plane` whose consecutive closed segments all lie in `U`.  The
relation is reflexive (at points of `U`), symmetric, transitive, and monotone in `U`.

The main theorem `IsPreconnected.joinedByBrokenLine` is the standard clopen-chain argument:
for fixed `a`, both `{x ∈ U | JoinedByBrokenLine U a x}` and its complement in `U` are open,
because any metric ball inside `U` is convex, so the segment from a ball's centre to any of its
points extends or truncates a broken line by one segment.  Preconnectedness of `U` then forces
the complement to be empty.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- `a` and `b` are joined by a broken line inside `U`: there is a finite chain of vertices
starting at `a` and ending at `b` such that every consecutive closed segment lies in `U`. -/
def JoinedByBrokenLine (U : Set Plane) (a b : Plane) : Prop :=
  ∃ (n : ℕ) (v : Fin (n + 1) → Plane), v 0 = a ∧ v (Fin.last n) = b ∧
    ∀ i : Fin n, segment ℝ (v i.castSucc) (v i.succ) ⊆ U

namespace JoinedByBrokenLine

/-- A single segment inside `U` is a broken line. -/
theorem of_segment {U : Set Plane} {a b : Plane} (h : segment ℝ a b ⊆ U) :
    JoinedByBrokenLine U a b :=
  ⟨1, ![a, b], rfl, rfl, fun i => by fin_cases i; simpa using h⟩

/-- Any point of `U` is joined to itself by a (degenerate) broken line in `U`. -/
protected theorem refl {U : Set Plane} {a : Plane} (ha : a ∈ U) :
    JoinedByBrokenLine U a a :=
  of_segment (by rw [segment_same]; exact Set.singleton_subset_iff.2 ha)

/-- Broken-line connectivity is symmetric: traverse the chain backwards. -/
protected theorem symm {U : Set Plane} {a b : Plane} (h : JoinedByBrokenLine U a b) :
    JoinedByBrokenLine U b a := by
  obtain ⟨n, v, hv0, hvl, hvseg⟩ := h
  refine ⟨n, fun i => v i.rev, ?_, ?_, fun i => ?_⟩
  · simp only [Fin.rev_zero]
    exact hvl
  · simp only [Fin.rev_last]
    exact hv0
  · simp only [Fin.rev_castSucc, Fin.rev_succ]
    rw [segment_symm]
    exact hvseg i.rev

/-- Extend a broken line from `a` to `b` by one further segment from `b` to `c` inside `U`. -/
theorem snoc {U : Set Plane} {a b c : Plane} (hab : JoinedByBrokenLine U a b)
    (hseg : segment ℝ b c ⊆ U) : JoinedByBrokenLine U a c := by
  obtain ⟨n, v, hv0, hvl, hvseg⟩ := hab
  refine ⟨n + 1, Fin.snoc v c, ?_, Fin.snoc_last _ _, fun i => ?_⟩
  · rw [← Fin.castSucc_zero, Fin.snoc_castSucc, hv0]
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_castSucc, hvl, Fin.succ_last, Fin.snoc_last]
      exact hseg
    · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hvseg j

/-- Broken-line connectivity is transitive: concatenate the two chains. -/
protected theorem trans {U : Set Plane} {a b c : Plane} (hab : JoinedByBrokenLine U a b)
    (hbc : JoinedByBrokenLine U b c) : JoinedByBrokenLine U a c := by
  have aux : ∀ m (w : Fin (m + 1) → Plane), w 0 = b →
      (∀ i : Fin m, segment ℝ (w i.castSucc) (w i.succ) ⊆ U) →
      JoinedByBrokenLine U a (w (Fin.last m)) := by
    intro m
    induction m with
    | zero =>
      intro w hw0 _
      rw [Fin.last_zero, hw0]
      exact hab
    | succ m ih =>
      intro w hw0 hwseg
      have h1 : JoinedByBrokenLine U a (w (Fin.last m).castSucc) :=
        ih (fun j => w j.castSucc)
          (by simp only [Fin.castSucc_zero]; exact hw0)
          (fun j => by
            simp only [← Fin.succ_castSucc]
            exact hwseg j.castSucc)
      have h2 := h1.snoc (hwseg (Fin.last m))
      rwa [Fin.succ_last] at h2
  obtain ⟨m, w, hw0, hwl, hwseg⟩ := hbc
  have h := aux m w hw0 hwseg
  rwa [hwl] at h

/-- Transport a broken line along an inclusion `U ⊆ V`. -/
theorem mono {U V : Set Plane} {a b : Plane} (h : JoinedByBrokenLine U a b) (hUV : U ⊆ V) :
    JoinedByBrokenLine V a b := by
  obtain ⟨n, v, hv0, hvl, hvseg⟩ := h
  exact ⟨n, v, hv0, hvl, fun i => (hvseg i).trans hUV⟩

end JoinedByBrokenLine

/-- **Broken-line connectivity** (Moise, Ch. 1): any two points of an open preconnected subset
of the plane are joined by a broken line lying in the set. -/
theorem IsPreconnected.joinedByBrokenLine {U : Set Plane} (hU : IsOpen U)
    (hconn : IsPreconnected U) {a b : Plane} (ha : a ∈ U) (hb : b ∈ U) :
    JoinedByBrokenLine U a b := by
  classical
  -- The set of points of `U` joined to `a`, and its complement in `U`.
  set W : Set Plane := {x | x ∈ U ∧ JoinedByBrokenLine U a x} with hW
  set W' : Set Plane := {x | x ∈ U ∧ ¬JoinedByBrokenLine U a x} with hW'
  -- `W` is open: a ball around `x ∈ W` inside `U` is convex, so each of its points is joined
  -- to `x` by a single segment in `U`, hence to `a`.
  have hWopen : IsOpen W := by
    rw [Metric.isOpen_iff]
    rintro x ⟨hxU, hxJ⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hxU
    refine ⟨ε, hε, fun y hy => ⟨hball hy, hxJ.trans (.of_segment ?_)⟩⟩
    exact ((convex_ball x ε).segment_subset (Metric.mem_ball_self hε) hy).trans hball
  -- `W'` is open: if some point of a convex ball around `x ∈ W'` inside `U` were joined to
  -- `a`, then so would `x` be, via one more segment in the ball.
  have hW'open : IsOpen W' := by
    rw [Metric.isOpen_iff]
    rintro x ⟨hxU, hxN⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hxU
    refine ⟨ε, hε, fun y hy => ⟨hball hy, fun hyJ => hxN (hyJ.trans (.of_segment ?_))⟩⟩
    exact ((convex_ball x ε).segment_subset hy (Metric.mem_ball_self hε)).trans hball
  -- Apply preconnectedness to the open cover `W ∪ W'` of `U`.
  by_contra hbN
  have hsub : U ⊆ W ∪ W' := fun x hx => by
    by_cases hx' : JoinedByBrokenLine U a x
    · exact Or.inl ⟨hx, hx'⟩
    · exact Or.inr ⟨hx, hx'⟩
  have hne : (U ∩ W).Nonempty := ⟨a, ha, ha, .refl ha⟩
  have hne' : (U ∩ W').Nonempty := ⟨b, hb, hb, hbN⟩
  obtain ⟨x, -, ⟨-, hxJ⟩, ⟨-, hxN⟩⟩ := hconn W W' hWopen hW'open hsub hne hne'
  exact hxN hxJ

/-- A positive metric thickening of a preconnected plane set is preconnected. -/
theorem IsPreconnected.thickening {A : Set Plane} (hA : IsPreconnected A)
    {ε : ℝ} (_ : 0 < ε) : IsPreconnected (Metric.thickening ε A) := by
  let add : Plane × Plane → Plane := fun p => p.1 + p.2
  have hball : IsPreconnected (Metric.ball (0 : Plane) ε) :=
    (convex_ball (0 : Plane) ε).isPreconnected
  have hprod : IsPreconnected (A ×ˢ Metric.ball (0 : Plane) ε) :=
    IsPreconnected.prod hA hball
  have hadd : Continuous add := continuous_fst.add continuous_snd
  have himage : add '' (A ×ˢ Metric.ball 0 ε) = Metric.thickening ε A := by
    rw [Metric.thickening_eq_biUnion_ball]
    ext x
    simp only [Set.mem_image, Set.mem_prod, Metric.mem_ball, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨a, v⟩, ⟨ha, hv⟩, rfl⟩
      refine ⟨a, ha, ?_⟩
      simpa [add, dist_eq_norm] using hv
    · rintro ⟨a, ha, hxa⟩
      refine ⟨(a, x - a), ⟨ha, ?_⟩, ?_⟩
      · simpa [dist_eq_norm] using hxa
      · simp [add]
  rw [← himage]
  exact IsPreconnected.image hprod add hadd.continuousOn

/-- Moise Chapter 6, Theorem 1: the endpoints of an embedded edge can be joined by a broken
line in every positive metric neighborhood of its image. -/
theorem brokenLine_in_thickening_of_preconnected {A : Set Plane}
    (hA : IsPreconnected A) {a b : Plane} (ha : a ∈ A) (hb : b ∈ A)
    {ε : ℝ} (hε : 0 < ε) :
    JoinedByBrokenLine (Metric.thickening ε A) a b := by
  apply IsPreconnected.joinedByBrokenLine Metric.isOpen_thickening
    (IsPreconnected.thickening hA hε)
  · exact Metric.self_subset_thickening hε A ha
  · exact Metric.self_subset_thickening hε A hb

/-- A preconnected set admits broken-line approximations whose vertices stay in its convex hull.

The thickening supplies room for the polygonal chain, while convex-hull containment records the
extra fact needed to preserve convex target regions such as a half-plane. -/
theorem brokenLine_in_thickening_inter_convexHull_of_preconnected {A : Set Plane}
    (hA : IsPreconnected A) {a b : Plane} (ha : a ∈ A) (hb : b ∈ A)
    {ε : ℝ} (hε : 0 < ε) :
    JoinedByBrokenLine (Metric.thickening ε A ∩ convexHull ℝ A) a b := by
  let U := Metric.thickening ε A ∩ convexHull ℝ A
  apply hA.induction₂ (fun x y => JoinedByBrokenLine U x y)
  · intro x hx
    filter_upwards [inter_mem_nhdsWithin A (Metric.ball_mem_nhds x hε)] with y hy
    apply JoinedByBrokenLine.of_segment
    intro z hz
    refine ⟨?_, segment_subset_convexHull hx hy.1 hz⟩
    apply Metric.mem_thickening_iff.mpr
    refine ⟨x, hx, ?_⟩
    exact (convex_ball x ε).segment_subset (Metric.mem_ball_self hε) hy.2 hz
  · intro x y z _ _ _ hxy hyz
    exact hxy.trans hyz
  · intro x y _ _ hxy
    exact hxy.symm
  · exact ha
  · exact hb

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end r78_classification02_block_02
/- END ClassificationOfSurfaces.Moise.BrokenLine -/

/- BEGIN ClassificationOfSurfaces.Moise.IntrinsicComplex | 38c1d85f6d55baaf8ee2dd5b4a28171e51242a41a3cf751e648b40b2f9eb582a -/
section r78_classification02_block_03
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Intrinsic finite PL complexes

The complexes used during the Rado induction are not generally realized by straight triangles
in one global copy of the plane.  Their honest carrier is instead the canonical barycentric
realization `GeometricRealization`.  This file supplies the small intrinsic PL layer needed to
state chart-transition approximation and refinement without pretending that source is planar.

A subdivision contains a homeomorphism between the two canonical realizations, together with
facewise affine formulas and subordination to old faces.  Thus an arbitrary homeomorphism cannot
be installed as a subdivision by bookkeeping alone.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- A finite pure two-dimensional abstract simplicial complex.  Lower-dimensional faces are
implicit in the supports of the listed triangles, exactly as in `GeometricRealization`. -/
structure IntrinsicTwoComplex where
  /-- The `Vertex` declaration. -/
  Vertex : Type
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  /-- The `faces` declaration. -/
  faces : Finset (Finset Vertex)
  faces_card : ∀ t ∈ faces, t.card = 3

attribute [instance] IntrinsicTwoComplex.vertexFintype
attribute [instance] IntrinsicTwoComplex.vertexDecidableEq

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex)

/-- The canonical barycentric realization of an intrinsic complex. -/
abbrev realization : Type :=
  GeometricRealization K.Vertex K.faces

/-- The closed barycentric carrier of a vertex set. -/
def ambientFaceCarrier (t : Finset K.Vertex) : Set (K.Vertex → ℝ) :=
  {x | x ∈ stdSimplex ℝ K.Vertex ∧ ∀ v ∉ t, x v = 0}

/-- The carrier of a listed triangle as a subset of the realization. -/
def faceCarrier (t : Finset K.Vertex) : Set K.realization :=
  {x | ∀ v ∉ t, x.1 v = 0}

theorem mem_realization_iff (x : K.Vertex → ℝ) :
    x ∈ GeometricRealization K.Vertex K.faces ↔
      ∃ t ∈ K.faces, x ∈ K.ambientFaceCarrier t := by
  simp only [GeometricRealization, ambientFaceCarrier, Set.mem_setOf_eq]
  tauto

theorem mem_faceCarrier_iff (t : Finset K.Vertex) (x : K.realization) :
    x ∈ K.faceCarrier t ↔ ∀ v ∉ t, x.1 v = 0 :=
  Iff.rfl

theorem faceCarrier_eq_preimage (t : Finset K.Vertex) :
    K.faceCarrier t = Subtype.val ⁻¹' K.ambientFaceCarrier t := by
  ext x
  simp only [faceCarrier, ambientFaceCarrier, Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · exact fun hx => ⟨x.2.1, hx⟩
  · exact fun hx => hx.2

theorem faceCarrier_closed (t : Finset K.Vertex) : IsClosed (K.faceCarrier t) := by
  rw [K.faceCarrier_eq_preimage t]
  have hclosed : IsClosed (K.ambientFaceCarrier t) := by
    have hrepr : K.ambientFaceCarrier t =
        stdSimplex ℝ K.Vertex ∩ ⋂ v ∈ {v : K.Vertex | v ∉ t},
          {x : K.Vertex → ℝ | x v = 0} := by
      ext x
      simp [ambientFaceCarrier]
    rw [hrepr]
    exact (isClosed_stdSimplex ℝ K.Vertex).inter
      (isClosed_biInter fun v _ => isClosed_eq (continuous_apply v) continuous_const)
  exact hclosed.preimage continuous_subtype_val

theorem realization_eq_iUnion_faceCarrier :
    (Set.univ : Set K.realization) = ⋃ t : {t // t ∈ K.faces}, K.faceCarrier t.1 := by
  apply Set.Subset.antisymm
  · intro x _
    rcases x.2.2 with ⟨t, ht, hxt⟩
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, hxt⟩
  · exact Set.subset_univ _

/-- The intrinsic subcomplex obtained by retaining a selected family of maximal faces. -/
def restrictFaces (p : Finset K.Vertex → Prop) [DecidablePred p] : IntrinsicTwoComplex where
  Vertex := K.Vertex
  faces := K.faces.filter p
  faces_card := by
    intro t ht
    exact K.faces_card t (Finset.mem_filter.mp ht).1

@[simp] theorem restrictFaces_faces (p : Finset K.Vertex → Prop) [DecidablePred p] :
    (K.restrictFaces p).faces = K.faces.filter p := rfl

/-- The canonical inclusion of a face restriction into the old realization. -/
def restrictFacesInclusion (p : Finset K.Vertex → Prop) [DecidablePred p] :
    (K.restrictFaces p).realization → K.realization :=
  fun x => ⟨x.1, x.2.1, by
    rcases x.2.2 with ⟨t, ht, hxt⟩
    exact ⟨t, (Finset.mem_filter (p := p)).mp ht |>.1, hxt⟩⟩

@[simp] theorem restrictFacesInclusion_val (p : Finset K.Vertex → Prop) [DecidablePred p]
    (x : (K.restrictFaces p).realization) :
    (K.restrictFacesInclusion p x).1 = x.1 := rfl

theorem isEmbedding_restrictFacesInclusion (p : Finset K.Vertex → Prop) [DecidablePred p] :
    _root_.Topology.IsEmbedding (K.restrictFacesInclusion p) := by
  have hcomp : _root_.Topology.IsEmbedding
      ((Subtype.val : K.realization → (K.Vertex → ℝ)) ∘ K.restrictFacesInclusion p) := by
    change _root_.Topology.IsEmbedding
      (Subtype.val : (K.restrictFaces p).realization → (K.Vertex → ℝ))
    exact _root_.Topology.IsEmbedding.subtypeVal
  exact _root_.Topology.IsEmbedding.subtypeVal.of_comp_iff.mp hcomp

theorem restrictFacesInclusion_mem_faceCarrier_iff
    (p : Finset K.Vertex → Prop) [DecidablePred p]
    (t : Finset K.Vertex) (x : (K.restrictFaces p).realization) :
    K.restrictFacesInclusion p x ∈ K.faceCarrier t ↔
      x ∈ (K.restrictFaces p).faceCarrier t :=
  Iff.rfl

theorem restrictFacesInclusion_range (p : Finset K.Vertex → Prop) [DecidablePred p] :
    Set.range (K.restrictFacesInclusion p) =
      {x : K.realization | ∃ t ∈ K.faces, p t ∧ x ∈ K.faceCarrier t} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rcases y.2.2 with ⟨t, ht, hyt⟩
    exact ⟨t, ((Finset.mem_filter (p := p)).mp ht).1,
      ((Finset.mem_filter (p := p)).mp ht).2, hyt⟩
  · rintro ⟨t, ht, hpt, hxt⟩
    let y : (K.restrictFaces p).realization :=
      ⟨x.1, x.2.1, ⟨t, (Finset.mem_filter (p := p)).mpr ⟨ht, hpt⟩, hxt⟩⟩
    exact ⟨y, Subtype.ext rfl⟩

/-! ## Intrinsic vertices and edges -/

/-- The edges of an intrinsic two-complex. -/
def edges : Finset (Finset K.Vertex) :=
  K.faces.biUnion fun t => t.powersetCard 2

/-- The abstract two-complex has surface edge valence when every edge is contained in at most
two maximal triangles. -/
def HasSurfaceEdgeValence : Prop :=
  ∀ e ∈ K.edges, (K.faces.filter fun t => e ⊆ t).card ≤ 2

theorem card_of_mem_edges {e : Finset K.Vertex} (he : e ∈ K.edges) : e.card = 2 := by
  rcases Finset.mem_biUnion.mp he with ⟨t, ht, het⟩
  exact (Finset.mem_powersetCard.mp het).2

theorem exists_face_of_mem_edges {e : Finset K.Vertex} (he : e ∈ K.edges) :
    ∃ t ∈ K.faces, e ⊆ t := by
  rcases Finset.mem_biUnion.mp he with ⟨t, ht, het⟩
  exact ⟨t, ht, (Finset.mem_powersetCard.mp het).1⟩

/-- The finite edge type. -/
abbrev Edge : Type := {e : Finset K.Vertex // e ∈ K.edges}

/-- The intrinsic one-skeleton, as the finite union of all barycentric edge carriers. -/
def oneSkeleton : Set K.realization :=
  {x | ∃ e : K.Edge, x ∈ K.faceCarrier e.1}

theorem mem_oneSkeleton_iff (x : K.realization) :
    x ∈ K.oneSkeleton ↔ ∃ e : K.Edge, x ∈ K.faceCarrier e.1 :=
  Iff.rfl

theorem faceCarrier_edge_subset_oneSkeleton (e : K.Edge) :
    K.faceCarrier e.1 ⊆ K.oneSkeleton :=
  fun _ hx => ⟨e, hx⟩

theorem oneSkeleton_eq_iUnion_faceCarrier :
    K.oneSkeleton = ⋃ e : K.Edge, K.faceCarrier e.1 := by
  ext x
  simp [oneSkeleton]

theorem oneSkeleton_closed : IsClosed K.oneSkeleton := by
  rw [K.oneSkeleton_eq_iUnion_faceCarrier]
  exact isClosed_iUnion_of_finite fun e => K.faceCarrier_closed e.1

/-! ### Cyclic data on a maximal face -/

/-- A maximal two-face of the intrinsic complex. -/
abbrev Face : Type := {t : Finset K.Vertex // t ∈ K.faces}

/-- A chosen cyclic enumeration of the three vertices of a maximal face. -/
noncomputable def faceVertexEquiv (t : K.Face) : Fin 3 ≃ t.1 :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_coe, K.faces_card t.1 t.2])

/-- Cyclically indexed vertices of a maximal face. -/
noncomputable def faceVertex (t : K.Face) (i : ZMod 3) : K.Vertex :=
  (K.faceVertexEquiv t ((ZMod.finEquiv 3).symm i)).1

theorem faceVertex_mem (t : K.Face) (i : ZMod 3) : K.faceVertex t i ∈ t.1 :=
  (K.faceVertexEquiv t ((ZMod.finEquiv 3).symm i)).2

theorem faceVertex_injective (t : K.Face) : Function.Injective (K.faceVertex t) := by
  intro i j hij
  apply (ZMod.finEquiv 3).symm.injective
  apply (K.faceVertexEquiv t).injective
  exact Subtype.ext hij

theorem faceVertex_ne_next (t : K.Face) (i : ZMod 3) :
    K.faceVertex t i ≠ K.faceVertex t (i + 1) := by
  intro h
  have hi : i = i + 1 := K.faceVertex_injective t h
  have hone : (0 : ZMod 3) = 1 := by
    calc
      0 = i - i := by abel
      _ = (i + 1) - i := congrArg (fun z => z - i) hi
      _ = 1 := by abel
  exact (by decide : (0 : ZMod 3) ≠ 1) hone

theorem faceVertex_ne_add_two (t : K.Face) (i : ZMod 3) :
    K.faceVertex t i ≠ K.faceVertex t (i + 2) := by
  intro h
  have hi : i = i + 2 := K.faceVertex_injective t h
  have htwo : (0 : ZMod 3) = 2 := by
    calc
      0 = i - i := by abel
      _ = (i + 2) - i := congrArg (fun z => z - i) hi
      _ = 2 := by abel
  exact (by decide : (0 : ZMod 3) ≠ 2) htwo

/-- The intrinsic edge joining two consecutive cyclic vertices of a maximal face. -/
noncomputable def faceEdge (t : K.Face) (i : ZMod 3) : K.Edge := by
  refine ⟨{K.faceVertex t i, K.faceVertex t (i + 1)}, ?_⟩
  rw [edges]
  apply Finset.mem_biUnion.mpr
  refine ⟨t.1, t.2, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact K.faceVertex_mem t i
    · exact K.faceVertex_mem t (i + 1)
  · simp [K.faceVertex_ne_next t i]

@[simp] theorem faceEdge_val (t : K.Face) (i : ZMod 3) :
    (K.faceEdge t i).1 = {K.faceVertex t i, K.faceVertex t (i + 1)} := rfl

/-- The consecutive face edges share exactly their common cyclic vertex. -/
theorem faceEdge_inter_next (t : K.Face) (i : ZMod 3) :
    (K.faceEdge t i).1 ∩ (K.faceEdge t (i + 1)).1 =
      {K.faceVertex t (i + 1)} := by
  ext v
  simp only [faceEdge_val, Finset.mem_inter, Finset.mem_insert,
    Finset.mem_singleton, add_assoc, one_add_one_eq_two]
  constructor
  · rintro ⟨hvi | hvi, hvnext | hvtwo⟩
    · exact (K.faceVertex_ne_next t i (hvi.symm.trans hvnext)).elim
    · exact (K.faceVertex_ne_add_two t i (hvi.symm.trans hvtwo)).elim
    · exact hvi
    · exact hvi
  · intro hv
    exact ⟨Or.inr hv, Or.inl hv⟩

theorem faceEdge_ne_next (t : K.Face) (i : ZMod 3) :
    K.faceEdge t i ≠ K.faceEdge t (i + 1) := by
  intro h
  have hval := congrArg (fun e : K.Edge => e.1) h
  have hmem : K.faceVertex t i ∈ (K.faceEdge t (i + 1)).1 := by
    rw [← hval]
    simp
  simp only [faceEdge_val, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hi | hi
  · exact K.faceVertex_ne_next t i hi
  · have hz : i = i + 2 := K.faceVertex_injective t (by
        simpa only [one_add_one_eq_two, add_assoc] using hi)
    have htwo : (0 : ZMod 3) = 2 := by
      calc
        0 = i - i := by abel
        _ = (i + 2) - i := congrArg (fun z => z - i) hz
        _ = 2 := by abel
    exact (by decide : (0 : ZMod 3) ≠ 2) htwo

/-- Vertices which actually occur in a maximal face. -/
abbrev UsedVertex : Type := {v : K.Vertex // ∃ t ∈ K.faces, v ∈ t}

/-- A cyclic face vertex with explicit evidence that it occurs in the complex. -/
noncomputable def faceUsedVertex (t : K.Face) (i : ZMod 3) : K.UsedVertex :=
  ⟨K.faceVertex t i, t.1, t.2, K.faceVertex_mem t i⟩

/-- A chosen maximal face containing a used vertex. -/
noncomputable def usedVertexParent (v : K.UsedVertex) : Finset K.Vertex :=
  Classical.choose v.2

theorem usedVertexParent_mem (v : K.UsedVertex) : K.usedVertexParent v ∈ K.faces :=
  (Classical.choose_spec v.2).1

theorem usedVertex_mem_parent (v : K.UsedVertex) : v.1 ∈ K.usedVertexParent v :=
  (Classical.choose_spec v.2).2

/-- The canonical barycentric point of a used vertex. -/
noncomputable def vertexPoint (v : K.UsedVertex) : K.realization :=
  ⟨Pi.single v.1 1, single_mem_stdSimplex ℝ v.1, by
    refine ⟨K.usedVertexParent v, K.usedVertexParent_mem v, ?_⟩
    intro w hw
    have hwv : w ≠ v.1 := by
      intro h
      subst w
      exact hw (K.usedVertex_mem_parent v)
    simp [hwv]⟩

theorem injective_vertexPoint : Function.Injective K.vertexPoint := by
  intro v w hvw
  apply Subtype.ext
  by_contra hvw'
  have hcoord := congrArg (fun x : K.realization => x.1 v.1) hvw
  simp [vertexPoint, hvw'] at hcoord

theorem vertexPoint_mem_faceCarrier_iff (v : K.UsedVertex) (s : Finset K.Vertex) :
    K.vertexPoint v ∈ K.faceCarrier s ↔ v.1 ∈ s := by
  constructor
  · intro hv
    by_contra hvs
    have := hv v.1 hvs
    simp [vertexPoint] at this
  · intro hvs w hw
    have hwv : w ≠ v.1 := by
      intro h
      subst w
      exact hw hvs
    simp [vertexPoint, hwv]

/-- A chosen old face containing an edge. -/
noncomputable def edgeParent (e : K.Edge) : Finset K.Vertex :=
  Classical.choose (K.exists_face_of_mem_edges e.2)

theorem edgeParent_mem (e : K.Edge) : K.edgeParent e ∈ K.faces :=
  (Classical.choose_spec (K.exists_face_of_mem_edges e.2)).1

theorem edge_subset_parent (e : K.Edge) : e.1 ⊆ K.edgeParent e :=
  (Classical.choose_spec (K.exists_face_of_mem_edges e.2)).2

/-- The chosen first endpoint of an intrinsic edge. -/
noncomputable def edgeFirst (e : K.Edge) : K.Vertex :=
  (Finset.card_eq_two.mp (K.card_of_mem_edges e.2)).choose

/-- The chosen second endpoint of an intrinsic edge. -/
noncomputable def edgeSecond (e : K.Edge) : K.Vertex :=
  (Finset.card_eq_two.mp (K.card_of_mem_edges e.2)).choose_spec.choose

theorem edgeFirst_ne_edgeSecond (e : K.Edge) : K.edgeFirst e ≠ K.edgeSecond e :=
  (Finset.card_eq_two.mp (K.card_of_mem_edges e.2)).choose_spec.choose_spec.1

theorem edge_eq_pair (e : K.Edge) : e.1 = {K.edgeFirst e, K.edgeSecond e} :=
  (Finset.card_eq_two.mp (K.card_of_mem_edges e.2)).choose_spec.choose_spec.2

theorem edgeFirst_mem (e : K.Edge) : K.edgeFirst e ∈ e.1 := by
  rw [K.edge_eq_pair e]
  simp

theorem edgeSecond_mem (e : K.Edge) : K.edgeSecond e ∈ e.1 := by
  rw [K.edge_eq_pair e]
  simp

/-- The canonical barycentric realization point associated to a vertex of an edge. -/
noncomputable def edgeVertexPoint (e : K.Edge) (v : K.Vertex) (hv : v ∈ e.1) :
    K.realization :=
  ⟨Pi.single v 1, single_mem_stdSimplex ℝ v, by
    refine ⟨K.edgeParent e, K.edgeParent_mem e, ?_⟩
    intro w hw
    have hwv : w ≠ v := by
      intro h
      subst w
      exact hw (K.edge_subset_parent e hv)
    simp [hwv]⟩

theorem edgeVertexPoint_eq_vertexPoint (e : K.Edge) (v : K.Vertex) (hv : v ∈ e.1) :
    K.edgeVertexPoint e v hv = K.vertexPoint
      ⟨v, K.edgeParent e, K.edgeParent_mem e, K.edge_subset_parent e hv⟩ := by
  apply Subtype.ext
  rfl

/-- Canonical first endpoint in the barycentric realization. -/
noncomputable def edgeFirstPoint (e : K.Edge) : K.realization :=
  K.edgeVertexPoint e (K.edgeFirst e) (K.edgeFirst_mem e)

/-- Canonical second endpoint in the barycentric realization. -/
noncomputable def edgeSecondPoint (e : K.Edge) : K.realization :=
  K.edgeVertexPoint e (K.edgeSecond e) (K.edgeSecond_mem e)

/-- The first endpoint as a used vertex. -/
noncomputable def edgeFirstUsed (e : K.Edge) : K.UsedVertex :=
  ⟨K.edgeFirst e, K.edgeParent e, K.edgeParent_mem e,
    K.edge_subset_parent e (K.edgeFirst_mem e)⟩

/-- The second endpoint as a used vertex. -/
noncomputable def edgeSecondUsed (e : K.Edge) : K.UsedVertex :=
  ⟨K.edgeSecond e, K.edgeParent e, K.edgeParent_mem e,
    K.edge_subset_parent e (K.edgeSecond_mem e)⟩

theorem edgeFirstUsed_ne_edgeSecondUsed (e : K.Edge) :
    K.edgeFirstUsed e ≠ K.edgeSecondUsed e := by
  intro h
  exact K.edgeFirst_ne_edgeSecond e (congrArg Subtype.val h)

theorem vertexPoint_edgeFirstUsed (e : K.Edge) :
    K.vertexPoint (K.edgeFirstUsed e) = K.edgeFirstPoint e := by
  apply Subtype.ext
  rfl

theorem vertexPoint_edgeSecondUsed (e : K.Edge) :
    K.vertexPoint (K.edgeSecondUsed e) = K.edgeSecondPoint e := by
  apply Subtype.ext
  rfl

/-- The canonical first endpoint depends only on its underlying used vertex, not on the chosen
maximal face witnessing that the vertex is used. -/
theorem edgeFirstPoint_eq_vertexPoint_of_eq (e : K.Edge) (v : K.UsedVertex)
    (h : K.edgeFirst e = v.1) :
    K.edgeFirstPoint e = K.vertexPoint v := by
  apply Subtype.ext
  simp [edgeFirstPoint, edgeVertexPoint, vertexPoint, h]

/-- The analogous proof-independence statement for the second endpoint. -/
theorem edgeSecondPoint_eq_vertexPoint_of_eq (e : K.Edge) (v : K.UsedVertex)
    (h : K.edgeSecond e = v.1) :
    K.edgeSecondPoint e = K.vertexPoint v := by
  apply Subtype.ext
  simp [edgeSecondPoint, edgeVertexPoint, vertexPoint, h]

/-- The arbitrary endpoint ordering of a cyclic face edge is one of its two cyclic
orientations. -/
theorem faceEdge_endpoint_order (t : K.Face) (i : ZMod 3) :
    (K.edgeFirst (K.faceEdge t i) = K.faceVertex t i ∧
        K.edgeSecond (K.faceEdge t i) = K.faceVertex t (i + 1)) ∨
      (K.edgeFirst (K.faceEdge t i) = K.faceVertex t (i + 1) ∧
        K.edgeSecond (K.faceEdge t i) = K.faceVertex t i) := by
  have hfirst := K.edgeFirst_mem (K.faceEdge t i)
  have hsecond := K.edgeSecond_mem (K.faceEdge t i)
  rw [K.faceEdge_val t i] at hfirst hsecond
  simp only [Finset.mem_insert, Finset.mem_singleton] at hfirst hsecond
  rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
  · exact (K.edgeFirst_ne_edgeSecond (K.faceEdge t i) (hfirst.trans hsecond.symm)).elim
  · exact Or.inl ⟨hfirst, hsecond⟩
  · exact Or.inr ⟨hfirst, hsecond⟩
  · exact (K.edgeFirst_ne_edgeSecond (K.faceEdge t i) (hfirst.trans hsecond.symm)).elim

/-- The canonical interval parametrization of an intrinsic edge. -/
noncomputable def edgePath (e : K.Edge) (r : Set.Icc (0 : ℝ) 1) : K.realization := by
  let x := AffineMap.lineMap (K.edgeFirstPoint e).1 (K.edgeSecondPoint e).1 r.1
  refine ⟨x, ?_, ?_⟩
  · exact convex_stdSimplex ℝ K.Vertex |>.lineMap_mem
      (K.edgeFirstPoint e).2.1 (K.edgeSecondPoint e).2.1 r.2
  · refine ⟨K.edgeParent e, K.edgeParent_mem e, ?_⟩
    intro w hw
    have hwFirst : w ≠ K.edgeFirst e := by
      intro h
      subst w
      exact hw (K.edge_subset_parent e (K.edgeFirst_mem e))
    have hwSecond : w ≠ K.edgeSecond e := by
      intro h
      subst w
      exact hw (K.edge_subset_parent e (K.edgeSecond_mem e))
    simp [x, edgeFirstPoint, edgeSecondPoint, edgeVertexPoint,
      AffineMap.lineMap_apply_module, hwFirst, hwSecond]

theorem continuous_edgePath (e : K.Edge) : Continuous (K.edgePath e) := by
  apply Continuous.subtype_mk
  exact (AffineMap.lineMap (k := ℝ) (K.edgeFirstPoint e).1
    (K.edgeSecondPoint e).1).continuous_of_finiteDimensional.comp continuous_subtype_val

theorem edgePath_zero (e : K.Edge) :
    K.edgePath e ⟨0, by simp⟩ = K.edgeFirstPoint e := by
  apply Subtype.ext
  simp [edgePath, AffineMap.lineMap_apply_module]

theorem edgePath_one (e : K.Edge) :
    K.edgePath e ⟨1, by simp⟩ = K.edgeSecondPoint e := by
  apply Subtype.ext
  simp [edgePath, AffineMap.lineMap_apply_module]

@[simp] theorem edgePath_apply_first (e : K.Edge) (r : Set.Icc (0 : ℝ) 1) :
    (K.edgePath e r).1 (K.edgeFirst e) = 1 - r.1 := by
  simp [edgePath, edgeFirstPoint, edgeSecondPoint, edgeVertexPoint,
    AffineMap.lineMap_apply_module, K.edgeFirst_ne_edgeSecond e]

@[simp] theorem edgePath_apply_second (e : K.Edge) (r : Set.Icc (0 : ℝ) 1) :
    (K.edgePath e r).1 (K.edgeSecond e) = r.1 := by
  simp [edgePath, edgeFirstPoint, edgeSecondPoint, edgeVertexPoint,
    AffineMap.lineMap_apply_module, K.edgeFirst_ne_edgeSecond e]

theorem injective_edgePath (e : K.Edge) : Function.Injective (K.edgePath e) := by
  intro r s hrs
  apply Subtype.ext
  have hcoord := congrArg (fun x : K.realization => x.1 (K.edgeSecond e)) hrs
  simpa using hcoord

/-- An ambient map restricted to the canonical interval of one intrinsic edge. -/
noncomputable def mappedEdgePath (h : K.realization → Plane) (e : K.Edge) :
    Set.Icc (0 : ℝ) 1 → Plane :=
  h ∘ K.edgePath e

theorem continuous_mappedEdgePath {h : K.realization → Plane} (hh : Continuous h)
    (e : K.Edge) : Continuous (K.mappedEdgePath h e) :=
  hh.comp (K.continuous_edgePath e)

theorem injective_mappedEdgePath {h : K.realization → Plane} (hh : Function.Injective h)
    (e : K.Edge) : Function.Injective (K.mappedEdgePath h e) :=
  hh.comp (K.injective_edgePath e)

theorem mappedEdgePath_zero (h : K.realization → Plane) (e : K.Edge) :
    K.mappedEdgePath h e ⟨0, by simp⟩ = h (K.edgeFirstPoint e) := by
  change h (K.edgePath e ⟨0, by simp⟩) = _
  rw [K.edgePath_zero e]

theorem mappedEdgePath_one (h : K.realization → Plane) (e : K.Edge) :
    K.mappedEdgePath h e ⟨1, by simp⟩ = h (K.edgeSecondPoint e) := by
  change h (K.edgePath e ⟨1, by simp⟩) = _
  rw [K.edgePath_one e]

/-- Intrinsic face carriers meet exactly in the carrier of the common vertex set. -/
theorem faceCarrier_inter (s t : Finset K.Vertex) :
    K.faceCarrier s ∩ K.faceCarrier t = K.faceCarrier (s ∩ t) := by
  ext x
  constructor
  · rintro ⟨hs, ht⟩ v hv
    simp only [Finset.mem_inter, not_and_or] at hv
    exact hv.elim (hs v) (ht v)
  · intro hst
    constructor
    · intro v hv
      exact hst v (by simp [hv])
    · intro v hv
      exact hst v (by simp [hv])

/-- The canonical interval path covers exactly the barycentric carrier of its edge. -/
theorem range_edgePath (e : K.Edge) :
    Set.range (K.edgePath e) = K.faceCarrier e.1 := by
  ext x
  constructor
  · rintro ⟨r, rfl⟩ v hv
    have hvFirst : v ≠ K.edgeFirst e := by
      intro h
      subst v
      exact hv (K.edgeFirst_mem e)
    have hvSecond : v ≠ K.edgeSecond e := by
      intro h
      subst v
      exact hv (K.edgeSecond_mem e)
    simp [edgePath, edgeFirstPoint, edgeSecondPoint, edgeVertexPoint,
      AffineMap.lineMap_apply_module, hvFirst, hvSecond]
  · intro hx
    let r : Set.Icc (0 : ℝ) 1 :=
      ⟨x.1 (K.edgeSecond e), mem_Icc_of_mem_stdSimplex x.2.1 (K.edgeSecond e)⟩
    refine ⟨r, Subtype.ext ?_⟩
    funext v
    by_cases hvFirst : v = K.edgeFirst e
    · subst v
      rw [K.edgePath_apply_first]
      have hsumPair : x.1 (K.edgeFirst e) + x.1 (K.edgeSecond e) = 1 := by
        calc
          x.1 (K.edgeFirst e) + x.1 (K.edgeSecond e) = ∑ w ∈ e.1, x.1 w := by
            rw [K.edge_eq_pair e]
            simp [K.edgeFirst_ne_edgeSecond e]
          _ = ∑ w, x.1 w := Finset.sum_subset (Finset.subset_univ e.1)
            (fun w _ hw => hx w hw)
          _ = 1 := x.2.1.2
      dsimp [r]
      linarith
    · by_cases hvSecond : v = K.edgeSecond e
      · subst v
        rw [K.edgePath_apply_second]
      · have hv : v ∉ e.1 := by
          rw [K.edge_eq_pair e]
          simp [hvFirst, hvSecond]
        rw [hx v hv]
        simp [edgePath, edgeFirstPoint, edgeSecondPoint, edgeVertexPoint,
          AffineMap.lineMap_apply_module, hvFirst, hvSecond]

/-- The open barycentric carriers of distinct intrinsic edges are disjoint. -/
theorem disjoint_edgePath_image_Ioo {e d : K.Edge} (hed : e ≠ d) :
    Disjoint (K.edgePath e '' {r : Set.Icc (0 : ℝ) 1 | 0 < r.1 ∧ r.1 < 1})
      (K.edgePath d '' {r : Set.Icc (0 : ℝ) 1 | 0 < r.1 ∧ r.1 < 1}) := by
  rw [Set.disjoint_left]
  rintro x ⟨r, hr, rfl⟩ ⟨s, hs, hpaths⟩
  change 0 < r.1 ∧ r.1 < 1 at hr
  change 0 < s.1 ∧ s.1 < 1 at hs
  have hsCarrier : K.edgePath d s ∈ K.faceCarrier d.1 := by
    rw [← K.range_edgePath d]
    exact ⟨s, rfl⟩
  have hedSubset : e.1 ⊆ d.1 := by
    intro v hv
    by_contra hvd
    have hzero : (K.edgePath d s).1 v = 0 := hsCarrier v hvd
    have hcoord := congrArg (fun y : K.realization => y.1 v) hpaths
    have hpositive : 0 < (K.edgePath e r).1 v := by
      rw [K.edge_eq_pair e] at hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · rw [K.edgePath_apply_first]
        exact sub_pos.mpr hr.2
      · rw [K.edgePath_apply_second]
        exact hr.1
    linarith
  have hedge : e.1 = d.1 := Finset.eq_of_subset_of_card_le hedSubset (by
    rw [K.card_of_mem_edges e.2, K.card_of_mem_edges d.2])
  exact hed (Subtype.ext hedge)

theorem faceCarrier_empty : K.faceCarrier ∅ = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hsum := x.2.1.2
  have hzero : ∀ v, x.1 v = 0 := by
    intro v
    exact hx v (Finset.notMem_empty v)
  simp_rw [hzero] at hsum
  norm_num at hsum

/-- A realization point supported on one used vertex is its canonical vertex point. -/
theorem eq_vertexPoint_of_mem_faceCarrier_singleton
    (v : K.UsedVertex) (x : K.realization)
    (hx : x ∈ K.faceCarrier ({v.1} : Finset K.Vertex)) :
    x = K.vertexPoint v := by
  have hxv : x.1 v.1 = 1 := by
    have hsum := x.2.1.2
    rw [Finset.sum_eq_single v.1] at hsum
    · exact hsum
    · intro w _ hwv
      exact hx w (by simp [hwv])
    · intro hv
      exact False.elim (hv (Finset.mem_univ v.1))
  apply Subtype.ext
  funext w
  by_cases hwv : w = v.1
  · subst w
    simp [vertexPoint, hxv]
  · simp [vertexPoint, hwv, hx w (by simp [hwv])]

/-- A nonempty barycentric carrier with at most one vertex, contained in a listed face,
consists of one canonical vertex point. -/
theorem exists_eq_vertexPoint_of_mem_faceCarrier_of_card_le_one
    (t : K.Face) {s : Finset K.Vertex} (hst : s ⊆ t.1)
    (hcard : s.card ≤ 1) {x : K.realization}
    (hx : x ∈ K.faceCarrier s) :
    ∃ v : K.UsedVertex, x = K.vertexPoint v := by
  have hsNonempty : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hs
    subst s
    rw [K.faceCarrier_empty] at hx
    exact hx
  have hsCard : s.card = 1 := by
    have := Finset.card_pos.mpr hsNonempty
    omega
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsCard
  have hvt : v ∈ t.1 := hst (by simp)
  let vUsed : K.UsedVertex := ⟨v, t.1, t.2, hvt⟩
  exact ⟨vUsed, K.eq_vertexPoint_of_mem_faceCarrier_singleton vUsed x (by
    simpa [vUsed] using hx)⟩

/-- Exact range of an intrinsic edge after applying an ambient map. -/
theorem range_mappedEdgePath (h : K.realization → Plane) (e : K.Edge) :
    Set.range (K.mappedEdgePath h e) = h '' K.faceCarrier e.1 := by
  ext y
  constructor
  · rintro ⟨r, rfl⟩
    have hr : K.edgePath e r ∈ K.faceCarrier e.1 := by
      rw [← K.range_edgePath e]
      exact ⟨r, rfl⟩
    exact ⟨K.edgePath e r, hr, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rw [← K.range_edgePath e] at hx
    rcases hx with ⟨r, rfl⟩
    exact ⟨r, rfl⟩

theorem isCompact_range_mappedEdgePath {h : K.realization → Plane} (hh : Continuous h)
    (e : K.Edge) : IsCompact (Set.range (K.mappedEdgePath h e)) := by
  exact isCompact_range (K.continuous_mappedEdgePath hh e)

/-- Nonincident intrinsic edges have disjoint ranges under an injective map. -/
theorem disjoint_range_mappedEdgePath {h : K.realization → Plane}
    (hh : Function.Injective h) {e d : K.Edge} (hed : Disjoint e.1 d.1) :
    Disjoint (Set.range (K.mappedEdgePath h e))
      (Set.range (K.mappedEdgePath h d)) := by
  rw [K.range_mappedEdgePath h e, K.range_mappedEdgePath h d,
    Set.disjoint_iff_inter_eq_empty, ← Set.image_inter hh,
    K.faceCarrier_inter e.1 d.1]
  have hinter : e.1 ∩ d.1 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hed
  rw [hinter, K.faceCarrier_empty, Set.image_empty]

/-- `f` is affine on an intrinsic set when it is the restriction of an ambient affine map in
barycentric coordinates. -/
def IsAffineOnSetTo {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : K.realization → E) (A : Set K.realization) : Prop :=
  ∃ a : (K.Vertex → ℝ) →ᵃ[ℝ] E,
    ∀ x : K.realization, x ∈ A → f x = a x.1

/-- Restrict an intrinsic affine-on-set certificate to a smaller source set. -/
theorem IsAffineOnSetTo.mono {E : Type*} [AddCommGroup E] [Module ℝ E]
    {f : K.realization → E} {A B : Set K.realization}
    (hf : K.IsAffineOnSetTo f A) (hBA : B ⊆ A) :
    K.IsAffineOnSetTo f B := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨a, fun x hx => ha x (hBA hx)⟩

/-- The plane-target specialization of intrinsic affinity on an arbitrary set. -/
abbrev IsAffineOnSet (f : K.realization → Plane) (A : Set K.realization) : Prop :=
  K.IsAffineOnSetTo f A

/-- Intrinsic affine-on-set maps to the plane are continuous on that set. -/
theorem IsAffineOnSet.continuousOn {f : K.realization → Plane}
    {A : Set K.realization} (hf : K.IsAffineOnSet f A) :
    ContinuousOn f A := by
  obtain ⟨a, ha⟩ := hf
  exact (a.continuous_of_finiteDimensional.comp continuous_subtype_val).continuousOn.congr
    fun x hx => ha x hx

/-- `f` is affine on one intrinsic face when it is the restriction of an ambient affine map in
barycentric coordinates. -/
def IsAffineOnFaceTo {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : K.realization → E) (t : Finset K.Vertex) : Prop :=
  ∃ a : (K.Vertex → ℝ) →ᵃ[ℝ] E,
    ∀ x : K.realization, x ∈ K.faceCarrier t → f x = a x.1

/-- The plane-target specialization used by PL approximation. -/
abbrev IsAffineOnFace (f : K.realization → Plane) (t : Finset K.Vertex) : Prop :=
  K.IsAffineOnFaceTo f t

theorem IsAffineOnFace.continuousOn {f : K.realization → Plane}
    {t : Finset K.Vertex} (hf : K.IsAffineOnFace f t) :
    ContinuousOn f (K.faceCarrier t) := by
  obtain ⟨a, ha⟩ := hf
  exact (a.continuous_of_finiteDimensional.comp continuous_subtype_val).continuousOn.congr
    fun x hx => ha x hx

/-- A faithful intrinsic subdivision.  The refined realization is homeomorphic to the original;
the homeomorphism is affine on each refined face and carries that face into an old face. -/
structure Subdivision where
  /-- The `refined` declaration. -/
  refined : IntrinsicTwoComplex
  /-- The `homeo` declaration. -/
  homeo : refined.realization ≃ₜ K.realization
  affineOnFace : ∀ t ∈ refined.faces,
    ∃ a : (refined.Vertex → ℝ) →ᵃ[ℝ] (K.Vertex → ℝ),
      ∀ x : refined.realization, x ∈ refined.faceCarrier t → (homeo x).1 = a x.1
  subordinate : ∀ t ∈ refined.faces,
    ∃ u ∈ K.faces, ∀ x : refined.realization,
      x ∈ refined.faceCarrier t → homeo x ∈ K.faceCarrier u

namespace Subdivision

/-- Every intrinsic complex is a subdivision of itself. -/
noncomputable def refl : K.Subdivision where
  refined := K
  homeo := Homeomorph.refl K.realization
  affineOnFace := by
    intro t ht
    refine ⟨AffineMap.id ℝ (K.Vertex → ℝ), ?_⟩
    intro x hx
    rfl
  subordinate := by
    intro t ht
    exact ⟨t, ht, fun x hx => hx⟩

@[simp] theorem refl_refined : (refl K).refined = K := rfl


/-- Faithful intrinsic subdivisions compose. -/
noncomputable def trans {K : IntrinsicTwoComplex}
    (R : K.Subdivision) (Q : R.refined.Subdivision) : K.Subdivision where
  refined := Q.refined
  homeo := Q.homeo.trans R.homeo
  affineOnFace := by
    intro t ht
    obtain ⟨u, hu, htu⟩ := Q.subordinate t ht
    obtain ⟨a, ha⟩ := Q.affineOnFace t ht
    obtain ⟨b, hb⟩ := R.affineOnFace u hu
    refine ⟨b.comp a, ?_⟩
    intro x hx
    rw [AffineMap.comp_apply]
    change (R.homeo (Q.homeo x)).1 = b (a x.1)
    rw [hb (Q.homeo x) (htu x hx), ha x hx]
  subordinate := by
    intro t ht
    obtain ⟨u, hu, htu⟩ := Q.subordinate t ht
    obtain ⟨s, hs, hus⟩ := R.subordinate u hu
    exact ⟨s, hs, fun x hx => hus (Q.homeo x) (htu x hx)⟩

@[simp] theorem trans_refined (R : K.Subdivision) (Q : R.refined.Subdivision) :
    (R.trans Q).refined = Q.refined := rfl

theorem trans_homeo_apply (R : K.Subdivision) (Q : R.refined.Subdivision)
    (x : Q.refined.realization) :
    (R.trans Q).homeo x = R.homeo (Q.homeo x) := rfl

end Subdivision

/-- A map from an intrinsic complex to the plane is PL when it becomes affine on every face of
a faithful finite subdivision. -/
def IsPLMap (f : K.realization → Plane) : Prop :=
  ∃ R : K.Subdivision,
    ∀ t ∈ R.refined.faces, R.refined.IsAffineOnFace (f ∘ R.homeo) t

/-- The target-vector-space form of intrinsic piecewise linearity. -/
def IsPLMapTo {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : K.realization → E) : Prop :=
  ∃ R : K.Subdivision,
    ∀ t ∈ R.refined.faces, R.refined.IsAffineOnFaceTo (f ∘ R.homeo) t

theorem isPLMap_iff_isPLMapTo (f : K.realization → Plane) :
    K.IsPLMap f ↔ K.IsPLMapTo f :=
  Iff.rfl

namespace IsPLMap

/-- Intrinsic PL maps into the plane are continuous.  Continuity is glued over the finite family
of closed refined faces and transported back through the subdivision homeomorphism. -/
theorem continuous {f : K.realization → Plane} (hf : K.IsPLMap f) : Continuous f := by
  obtain ⟨R, hR⟩ := hf
  have hclosed : ∀ t : {t // t ∈ R.refined.faces},
      IsClosed (R.refined.faceCarrier t.1) :=
    fun t => R.refined.faceCarrier_closed t.1
  have hlocal : ∀ t : {t // t ∈ R.refined.faces},
      ContinuousOn (f ∘ R.homeo) (R.refined.faceCarrier t.1) :=
    fun t => (hR t.1 t.2).continuousOn
  let carriers : {t // t ∈ R.refined.faces} → Set R.refined.realization :=
    fun t => R.refined.faceCarrier t.1
  have hfinite : LocallyFinite carriers := locallyFinite_of_finite carriers
  have hcomp : Continuous (f ∘ R.homeo) :=
    hfinite.continuous R.refined.realization_eq_iUnion_faceCarrier.symm hclosed hlocal
  simpa only [Function.comp_def, R.homeo.apply_symm_apply] using
    hcomp.comp R.homeo.symm.continuous

end IsPLMap

/-- A globally affine map in barycentric coordinates is intrinsically PL. -/
theorem isPLMap_of_affine (f : K.realization → Plane)
    (a : (K.Vertex → ℝ) →ᵃ[ℝ] Plane)
    (ha : ∀ x : K.realization, f x = a x.1) : K.IsPLMap f := by
  refine ⟨Subdivision.refl K, ?_⟩
  intro t ht
  exact ⟨a, fun x hx => ha x⟩

/-- The affine barycentric map determined by positions assigned to the vertices. -/
noncomputable def barycentricMap (p : K.Vertex → Plane) (x : K.realization) : Plane :=
  ∑ v, x.1 v • p v

theorem barycentricMap_isPL (p : K.Vertex → Plane) :
    K.IsPLMap (K.barycentricMap p) := by
  let a : (K.Vertex → ℝ) →ₗ[ℝ] Plane :=
    ∑ v, (LinearMap.proj v).smulRight (p v)
  refine K.isPLMap_of_affine (K.barycentricMap p) a.toAffineMap ?_
  intro x
  simp [barycentricMap, a]

/-- A homeomorphism of canonical realizations that is intrinsically PL in both directions. -/
structure PLHomeomorph (L : IntrinsicTwoComplex) where
  /-- The `toHomeomorph` declaration. -/
  toHomeomorph : K.realization ≃ₜ L.realization
  isPL_to : K.IsPLMapTo (fun x => (toHomeomorph x).1)
  isPL_inv : L.IsPLMapTo (fun x => (toHomeomorph.symm x).1)

namespace PLHomeomorph

/-- The identity intrinsic PL homeomorphism. -/
noncomputable def refl : K.PLHomeomorph K where
  toHomeomorph := Homeomorph.refl K.realization
  isPL_to := by
    refine ⟨Subdivision.refl K, ?_⟩
    intro t ht
    refine ⟨AffineMap.id ℝ (K.Vertex → ℝ), ?_⟩
    intro x hx
    rfl
  isPL_inv := by
    refine ⟨Subdivision.refl K, ?_⟩
    intro t ht
    refine ⟨AffineMap.id ℝ (K.Vertex → ℝ), ?_⟩
    intro x hx
    rfl

@[simp] theorem refl_apply (x : K.realization) : (refl K).toHomeomorph x = x := rfl

end PLHomeomorph

/-- A faithful subdivision is itself a PL homeomorphism between the refined and original
realizations.  For the inverse direction, use the same subdivision as the witness: after
precomposition with its homeomorphism the inverse is the identity. -/
noncomputable def Subdivision.toPLHomeomorph (R : K.Subdivision) :
    R.refined.PLHomeomorph K where
  toHomeomorph := R.homeo
  isPL_to := by
    refine ⟨Subdivision.refl R.refined, ?_⟩
    intro t ht
    obtain ⟨a, ha⟩ := R.affineOnFace t ht
    exact ⟨a, fun x hx => ha x hx⟩
  isPL_inv := by
    refine ⟨R, ?_⟩
    intro t ht
    refine ⟨AffineMap.id ℝ (R.refined.Vertex → ℝ), ?_⟩
    intro x hx
    exact congrArg Subtype.val (R.homeo.symm_apply_apply x)

/-- A PL map on a refinement is PL on the original intrinsic complex. -/
theorem IsPLMap.of_subdivision (R : K.Subdivision) {f : K.realization → Plane}
    (hf : R.refined.IsPLMap (f ∘ R.homeo)) : K.IsPLMap f := by
  obtain ⟨Q, hQ⟩ := hf
  refine ⟨R.trans Q, ?_⟩
  intro t ht
  change Q.refined.IsAffineOnFace (fun x => f (R.homeo (Q.homeo x))) t
  exact hQ t ht

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end r78_classification02_block_03
/- END ClassificationOfSurfaces.Moise.IntrinsicComplex -/

/- BEGIN ClassificationOfSurfaces.Moise.LineSubdivision | 21a6e46f134c76a4bb0ac1021781e669fd18bd29f436faab1c505ff2509a2852 -/
section r78_classification02_block_04
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Subdividing finite plane complexes by affine lines

Moise Chapter 2 cuts a polygonal region by the finitely many lines containing its edges.  This
file develops that construction from its local primitive: when an affine functional has opposite
signs at the endpoints of an edge, its zero gives the new subdivision vertex on that edge.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- Three affinely independent points form an affine basis of the plane. -/
noncomputable def affineBasisOfTriangle (p : Fin 3 → Plane) (hp : AffineIndependent ℝ p) :
    AffineBasis (Fin 3) ℝ Plane where
  toFun := p
  ind' := hp
  tot' := (hp.affineSpan_eq_top_iff_card_eq_finrank_add_one).2 (by
    simp [Plane])

/-- The affine equivalence carrying one ordered nondegenerate plane triangle to another. -/
noncomputable def triangleAffineEquiv (p q : Fin 3 → Plane)
    (hp : AffineIndependent ℝ p) (hq : AffineIndependent ℝ q) : Plane ≃ᵃ[ℝ] Plane :=
  let bp := affineBasisOfTriangle p hp
  let bq := affineBasisOfTriangle q hq
  AffineEquiv.ofLinearEquiv
    ((bp.basisOf 0).equiv (bq.basisOf 0) (Equiv.refl _)) (p 0) (q 0)

@[simp] theorem triangleAffineEquiv_apply (p q : Fin 3 → Plane)
    (hp : AffineIndependent ℝ p) (hq : AffineIndependent ℝ q) (i : Fin 3) :
    triangleAffineEquiv p q hp hq (p i) = q i := by
  fin_cases i
  · simp [triangleAffineEquiv]
  · change ((affineBasisOfTriangle p hp).basisOf 0).equiv
        ((affineBasisOfTriangle q hq).basisOf 0) (Equiv.refl _)
          (p 1 - p 0) + q 0 = q 1
    let j : {j : Fin 3 // j ≠ 0} := ⟨1, by decide⟩
    have hpvec : p 1 - p 0 =
        (affineBasisOfTriangle p hp).basisOf 0 j := by
      have h := (affineBasisOfTriangle p hp).basisOf_apply 0 j
      change (affineBasisOfTriangle p hp).basisOf 0 j = p 1 - p 0 at h
      exact h.symm
    have hqvec : (affineBasisOfTriangle q hq).basisOf 0 j =
        q 1 - q 0 := by
      have h := (affineBasisOfTriangle q hq).basisOf_apply 0 j
      change (affineBasisOfTriangle q hq).basisOf 0 j = q 1 - q 0 at h
      exact h
    have hequiv := ((affineBasisOfTriangle p hp).basisOf 0).equiv_apply
      j ((affineBasisOfTriangle q hq).basisOf 0) (Equiv.refl _)
    rw [hpvec]
    rw [hequiv]
    simp only [Equiv.refl_apply]
    rw [hqvec]
    abel
  · change ((affineBasisOfTriangle p hp).basisOf 0).equiv
        ((affineBasisOfTriangle q hq).basisOf 0) (Equiv.refl _)
          (p 2 - p 0) + q 0 = q 2
    let j : {j : Fin 3 // j ≠ 0} := ⟨2, by decide⟩
    have hpvec : p 2 - p 0 =
        (affineBasisOfTriangle p hp).basisOf 0 j := by
      have h := (affineBasisOfTriangle p hp).basisOf_apply 0 j
      change (affineBasisOfTriangle p hp).basisOf 0 j = p 2 - p 0 at h
      exact h.symm
    have hqvec : (affineBasisOfTriangle q hq).basisOf 0 j =
        q 2 - q 0 := by
      have h := (affineBasisOfTriangle q hq).basisOf_apply 0 j
      change (affineBasisOfTriangle q hq).basisOf 0 j = q 2 - q 0 at h
      exact h
    have hequiv := ((affineBasisOfTriangle p hp).basisOf 0).equiv_apply
      j ((affineBasisOfTriangle q hq).basisOf 0) (Equiv.refl _)
    rw [hpvec]
    rw [hequiv]
    simp only [Equiv.refl_apply]
    rw [hqvec]
    abel

theorem triangleAffineEquiv_image_convexHull (p q : Fin 3 → Plane)
    (hp : AffineIndependent ℝ p) (hq : AffineIndependent ℝ q) :
    triangleAffineEquiv p q hp hq '' convexHull ℝ (Set.range p) =
      convexHull ℝ (Set.range q) := by
  change (triangleAffineEquiv p q hp hq).toAffineMap '' convexHull ℝ (Set.range p) = _
  rw [(triangleAffineEquiv p q hp hq).toAffineMap.image_convexHull]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (triangleAffineEquiv_apply p q hp hq i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨p i, ⟨i, rfl⟩, triangleAffineEquiv_apply p q hp hq i⟩

/-- The affine equivalence between ordered triangles carries corresponding line-map points to
corresponding line-map points. -/
theorem triangleAffineEquiv_apply_lineMap (p q : Fin 3 → Plane)
    (hp : AffineIndependent ℝ p) (hq : AffineIndependent ℝ q)
    (i j : Fin 3) (c : ℝ) :
    triangleAffineEquiv p q hp hq (AffineMap.lineMap (p i) (p j) c) =
      AffineMap.lineMap (q i) (q j) c := by
  let e := triangleAffineEquiv p q hp hq
  have h := AffineMap.apply_lineMap e.toAffineMap (p i) (p j) c
  change e (AffineMap.lineMap (p i) (p j) c) =
    AffineMap.lineMap (e (p i)) (e (p j)) c at h
  rw [h, triangleAffineEquiv_apply, triangleAffineEquiv_apply]

/-- The determinant criterion for three points in the Euclidean plane. -/
theorem affineIndependent_plane_triple_of_det_ne_zero {p₀ p₁ p₂ : Plane}
    (hdet : (p₁ - p₀) 0 * (p₂ - p₀) 1 - (p₁ - p₀) 1 * (p₂ - p₀) 0 ≠ 0) :
    AffineIndependent ℝ ![p₀, p₁, p₂] := by
  rw [affineIndependent_iff_not_collinear_set]
  intro hcol
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (Set.mem_insert p₀ {p₁, p₂})).mp hcol
  obtain ⟨a, ha⟩ := hv p₁ (by simp)
  obtain ⟨b, hb⟩ := hv p₂ (by simp)
  have ha0 := congrArg (fun x : Plane => x 0) ha
  have ha1 := congrArg (fun x : Plane => x 1) ha
  have hb0 := congrArg (fun x : Plane => x 0) hb
  have hb1 := congrArg (fun x : Plane => x 1) hb
  apply hdet
  simp only [PiLp.sub_apply, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    at ha0 ha1 hb0 hb1 ⊢
  rw [ha0, ha1, hb0, hb1]
  ring

/-- An affine supporting hyperplane cuts a finite convex hull in precisely the hull of the
vertices lying on that hyperplane. -/
theorem convexHull_inter_affine_zero_of_nonneg (s : Finset Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ s, 0 ≤ f x) :
    convexHull ℝ (s : Set Plane) ∩ {x | f x = 0} =
      convexHull ℝ ((s.filter fun x => f x = 0 : Finset Plane) : Set Plane) := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨hxconv, hxzero⟩
    obtain ⟨w, hw0, hw1, hwcenter⟩ := Finset.mem_convexHull.mp hxconv
    have hsumf : ∑ y ∈ s, w y * f y = 0 := by
      calc
        ∑ y ∈ s, w y * f y = s.affineCombination ℝ f w := by
          simpa only [smul_eq_mul] using
            (Finset.affineCombination_eq_linear_combination s f w hw1).symm
        _ = f (s.affineCombination ℝ id w) :=
          (s.map_affineCombination id w hw1 f).symm
        _ = f (s.centerMass w id) := by
          congr 1
          rw [Finset.affineCombination_eq_linear_combination s id w hw1,
            Finset.centerMass_eq_of_sum_1 s id hw1]
        _ = f x := by rw [hwcenter]
        _ = 0 := hxzero
    have hterm0 : ∀ y ∈ s, w y * f y = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun y hy => mul_nonneg (hw0 y hy) (hf y hy)).mp hsumf
    have hwzero : ∀ y ∈ s, f y ≠ 0 → w y = 0 := by
      intro y hy hfy
      exact (mul_eq_zero.mp (hterm0 y hy)).resolve_right hfy
    let z := s.filter fun y => f y = 0
    have hzsub : z ⊆ s := Finset.filter_subset _ _
    have hsumz : ∑ y ∈ z, w y = 1 := by
      calc
        ∑ y ∈ z, w y = ∑ y ∈ s, w y := Finset.sum_subset hzsub fun y hy hynot =>
          hwzero y hy (by
            intro hfy
            apply hynot
            simp only [z, Finset.mem_filter, hy, hfy, and_self])
        _ = 1 := hw1
    apply Finset.mem_convexHull.mpr
    refine ⟨w, fun y hy => hw0 y (hzsub hy), hsumz, ?_⟩
    have hcenter : z.centerMass w id = s.centerMass w id := by
      rw [Finset.centerMass_eq_of_sum_1 z id hsumz,
        Finset.centerMass_eq_of_sum_1 s id hw1]
      exact Finset.sum_subset hzsub fun y hy hynot => by
        rw [hwzero y hy (by
          intro hfy
          apply hynot
          simp only [z, Finset.mem_filter, hy, hfy, and_self]), zero_smul]
    exact hcenter.trans hwcenter
  · apply convexHull_min
    · intro x hx
      have hx' := subset_convexHull ℝ (s : Set Plane)
        (show x ∈ s from (Finset.mem_filter.mp hx).1)
      exact ⟨hx', (Finset.mem_filter.mp hx).2⟩
    · exact (convex_convexHull ℝ (s : Set Plane)).inter
        ((convex_singleton (0 : ℝ)).affine_preimage f)

/-- Set-valued version of the supporting-hyperplane face formula.  Convex-hull membership uses
only finitely many points, so the finite formula above applies to each witness. -/
theorem convexHull_inter_affine_zero_of_nonneg_set (s : Set Plane)
    (f : Plane →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ s, 0 ≤ f x) :
    convexHull ℝ s ∩ {x | f x = 0} =
      convexHull ℝ (s ∩ {x | f x = 0}) := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨hxHull, hxZero⟩
    obtain ⟨ι, _, w, z, hw0, hw1, hz, hwz⟩ :=
      (mem_convexHull_iff_exists_fintype.mp hxHull)
    let t : Finset Plane := Finset.univ.image z
    have hxt : x ∈ convexHull ℝ (t : Set Plane) := by
      exact mem_convexHull_of_exists_fintype w z hw0 hw1
        (fun i => Finset.mem_coe.mpr
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
        (by simp only [hwz])
    have htNonneg : ∀ y ∈ t, 0 ≤ f y := by
      intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      exact hf (z i) (hz i)
    have hxFace :
        x ∈ convexHull ℝ ((t.filter fun y => f y = 0 : Finset Plane) : Set Plane) := by
      rw [← convexHull_inter_affine_zero_of_nonneg t f htNonneg]
      exact ⟨hxt, hxZero⟩
    apply convexHull_mono ?_ hxFace
    intro y hy
    have hyt := Finset.mem_filter.mp hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hyt.1
    exact ⟨hz i, hyt.2⟩
  · apply convexHull_min
    · intro x hx
      exact ⟨subset_convexHull ℝ s hx.1, hx.2⟩
    · exact (convex_convexHull ℝ s).inter
        ((convex_singleton (0 : ℝ)).affine_preimage f)

/-- Two finite convex hulls lying on opposite sides of an affine hyperplane intersect in their
common zero face. -/
theorem convexHull_inter_of_affine_separation (s t u : Finset Plane)
    (f : Plane →ᵃ[ℝ] ℝ) (hs : ∀ x ∈ s, 0 ≤ f x) (ht : ∀ x ∈ t, f x ≤ 0)
    (hszero : s.filter (fun x => f x = 0) = u)
    (htzero : t.filter (fun x => f x = 0) = u) :
    convexHull ℝ (s : Set Plane) ∩ convexHull ℝ (t : Set Plane) =
      convexHull ℝ (u : Set Plane) := by
  let g : Plane →ᵃ[ℝ] ℝ := -f
  have hg : ∀ x ∈ t, 0 ≤ g x := by
    intro x hx
    change 0 ≤ -f x
    linarith [ht x hx]
  have hgzero : t.filter (fun x => g x = 0) = u := by
    rw [← htzero]
    apply Finset.filter_congr
    intro x hx
    simp [g]
  have hsface := convexHull_inter_affine_zero_of_nonneg s f hs
  rw [hszero] at hsface
  have htface := convexHull_inter_affine_zero_of_nonneg t g hg
  rw [hgzero] at htface
  apply Set.Subset.antisymm
  · intro x hx
    have hsnonneg : 0 ≤ f x := by
      apply convexHull_min (fun y hy => hs y hy)
        ((convex_Ici (0 : ℝ)).affine_preimage f) hx.1
    have htnonpos : f x ≤ 0 := by
      apply convexHull_min (fun y hy => ht y hy)
        ((convex_Iic (0 : ℝ)).affine_preimage f) hx.2
    have hxzero : f x = 0 := le_antisymm htnonpos hsnonneg
    rw [← hsface]
    exact ⟨hx.1, hxzero⟩
  · intro x hx
    have hxs : x ∈ convexHull ℝ (s : Set Plane) := by
      rw [← hsface] at hx
      exact hx.1
    have hxt : x ∈ convexHull ℝ (t : Set Plane) := by
      rw [← htface] at hx
      exact hx.1
    exact ⟨hxs, hxt⟩

/-- Vertex-indexed form of `convexHull_inter_of_affine_separation`.  This is the form used when
checking the maximal triangles of a mesh. -/
theorem convexHull_image_inter_of_affine_separation {V : Type*} [DecidableEq V]
    (position : V → Plane) (_ : Function.Injective position) (s t : Finset V)
    (f : Plane →ᵃ[ℝ] ℝ) (hs : ∀ v ∈ s, 0 ≤ f (position v))
    (ht : ∀ v ∈ t, f (position v) ≤ 0)
    (hszero : ∀ v ∈ s, f (position v) = 0 ↔ v ∈ (s ∩ t))
    (htzero : ∀ v ∈ t, f (position v) = 0 ↔ v ∈ (s ∩ t)) :
    convexHull ℝ (position '' (s : Set V)) ∩ convexHull ℝ (position '' (t : Set V)) =
      convexHull ℝ (position '' ((s ∩ t : Finset V) : Set V)) := by
  classical
  have hsfilter : (s.image position).filter (fun x => f x = 0) =
      (s ∩ t).image position := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, hvzero⟩
      exact ⟨v, (hszero v hv).mp hvzero, rfl⟩
    · rintro ⟨v, hvst, rfl⟩
      exact ⟨⟨v, (Finset.mem_inter.mp hvst).1, rfl⟩,
        (hszero v (Finset.mem_inter.mp hvst).1).mpr hvst⟩
  have htfilter : (t.image position).filter (fun x => f x = 0) =
      (s ∩ t).image position := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, hvzero⟩
      exact ⟨v, (htzero v hv).mp hvzero, rfl⟩
    · rintro ⟨v, hvst, rfl⟩
      exact ⟨⟨v, (Finset.mem_inter.mp hvst).2, rfl⟩,
        (htzero v (Finset.mem_inter.mp hvst).2).mpr hvst⟩
  simpa only [Finset.coe_image] using
    convexHull_inter_of_affine_separation (s.image position) (t.image position)
      ((s ∩ t).image position) f
      (by rintro x hx; obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx; exact hs v hv)
      (by rintro x hx; obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx; exact ht v hv)
      hsfilter htfilter

/-! ## The reference split of a triangle -/

/-- A point of the Euclidean plane with the displayed Cartesian coordinates. -/
def planePoint (x y : ℝ) : Plane :=
  WithLp.toLp 2 ![x, y]

@[simp] theorem planePoint_apply_zero (x y : ℝ) : planePoint x y 0 = x := rfl
@[simp] theorem planePoint_apply_one (x y : ℝ) : planePoint x y 1 = y := rfl

/-- Vertices of the reference line split: the standard triangle vertices followed by one point
on each edge issuing from the origin. -/
def referenceSplitPosition (a b : ℝ) : Fin 5 → Plane :=
  ![planePoint 0 0, planePoint 1 0, planePoint 0 1, planePoint a 0, planePoint 0 b]

/-- The `referenceSplitTriangles` declaration. -/
def referenceSplitTriangles : Finset (Finset (Fin 5)) :=
  {{0, 3, 4}, {1, 2, 3}, {2, 3, 4}}

theorem referenceSplitPosition_injective {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1) : Function.Injective (referenceSplitPosition a b) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals
    exfalso
    dsimp [referenceSplitPosition] at hij
    have h0 := congrArg (fun x : Plane => x 0) hij
    have h1 := congrArg (fun x : Plane => x 1) hij
    simp only [planePoint_apply_zero] at h0
    simp only [planePoint_apply_one] at h1
    linarith

theorem referenceSplit_triangle0_affineIndependent {a b : ℝ} (ha0 : 0 < a)
    (hb0 : 0 < b) :
    AffineIndependent ℝ ![planePoint 0 0, planePoint a 0, planePoint 0 b] := by
  apply affineIndependent_plane_triple_of_det_ne_zero
  simp only [planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
  nlinarith

theorem referenceSplit_triangle1_affineIndependent {a : ℝ} (ha1 : a < 1) :
    AffineIndependent ℝ ![planePoint a 0, planePoint 1 0, planePoint 0 1] := by
  apply affineIndependent_plane_triple_of_det_ne_zero
  simp only [planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
  nlinarith

theorem referenceSplit_triangle2_affineIndependent {a b : ℝ} (ha0 : 0 < a)
    (hb1 : b < 1) :
    AffineIndependent ℝ ![planePoint a 0, planePoint 0 1, planePoint 0 b] := by
  apply affineIndependent_plane_triple_of_det_ne_zero
  simp only [planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
  nlinarith

/-- The first Cartesian coordinate, regarded as an affine functional. -/
noncomputable def cartesianX : Plane →ᵃ[ℝ] ℝ :=
  ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).comp
    (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap).toAffineMap

/-- The second Cartesian coordinate, regarded as an affine functional. -/
noncomputable def cartesianY : Plane →ᵃ[ℝ] ℝ :=
  ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).comp
    (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap).toAffineMap

@[simp] theorem cartesianX_apply (p : Plane) : cartesianX p = p 0 := rfl
@[simp] theorem cartesianY_apply (p : Plane) : cartesianY p = p 1 := rfl

/-- The affine line through the two new edge points in the reference split. -/
noncomputable def referenceOuterAffine (a b : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  a⁻¹ • cartesianX + b⁻¹ • cartesianY - AffineMap.const ℝ Plane 1

/-- The affine line through `(a,0)` and `(0,1)` in the reference split. -/
noncomputable def referenceDiagonalAffine (a : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  cartesianX + a • cartesianY - AffineMap.const ℝ Plane a

/-- A line through `(a,0)` lying strictly between the other two rays of the reference split.
Its second coefficient is chosen between `a` and `a / b`. -/
noncomputable def referenceVertexAffine (a b : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  cartesianX + (a * (1 + b) / (2 * b)) • cartesianY - AffineMap.const ℝ Plane a

@[simp] theorem referenceOuterAffine_planePoint (a b x y : ℝ) :
    referenceOuterAffine a b (planePoint x y) = a⁻¹ * x + b⁻¹ * y - 1 := rfl

@[simp] theorem referenceDiagonalAffine_planePoint (a x y : ℝ) :
    referenceDiagonalAffine a (planePoint x y) = x + a * y - a := rfl

@[simp] theorem referenceVertexAffine_planePoint (a b x y : ℝ) :
    referenceVertexAffine a b (planePoint x y) =
      x + (a * (1 + b) / (2 * b)) * y - a := rfl

private theorem affineIndependent_referenceTriangle0 {a b : ℝ} (ha0 : 0 < a)
    (hb0 : 0 < b) :
    AffineIndependent ℝ fun v : ({0, 3, 4} : Finset (Fin 5)) =>
      referenceSplitPosition a b v := by
  let e := (Fin.orderIsoTriple (0 : Fin 5) 3 4 (by decide) (by decide)).toEquiv
  apply (affineIndependent_equiv e).mp
  have heq : ((fun v : ({0, 3, 4} : Finset (Fin 5)) =>
      referenceSplitPosition a b v) ∘ e) =
      ![planePoint 0 0, planePoint a 0, planePoint 0 b] := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact referenceSplit_triangle0_affineIndependent ha0 hb0

private theorem affineIndependent_referenceTriangle1 {a b : ℝ} (ha1 : a < 1) :
    AffineIndependent ℝ fun v : ({1, 2, 3} : Finset (Fin 5)) =>
      referenceSplitPosition a b v := by
  let e := (Fin.orderIsoTriple (1 : Fin 5) 2 3 (by decide) (by decide)).toEquiv
  apply (affineIndependent_equiv e).mp
  have h : AffineIndependent ℝ ![planePoint 1 0, planePoint 0 1, planePoint a 0] := by
    apply affineIndependent_plane_triple_of_det_ne_zero
    simp only [planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
    nlinarith
  have heq : ((fun v : ({1, 2, 3} : Finset (Fin 5)) =>
      referenceSplitPosition a b v) ∘ e) =
      ![planePoint 1 0, planePoint 0 1, planePoint a 0] := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact h

private theorem affineIndependent_referenceTriangle2 {a b : ℝ} (ha0 : 0 < a)
    (hb1 : b < 1) :
    AffineIndependent ℝ fun v : ({2, 3, 4} : Finset (Fin 5)) =>
      referenceSplitPosition a b v := by
  let e := (Fin.orderIsoTriple (2 : Fin 5) 3 4 (by decide) (by decide)).toEquiv
  apply (affineIndependent_equiv e).mp
  have h : AffineIndependent ℝ ![planePoint 0 1, planePoint a 0, planePoint 0 b] := by
    apply affineIndependent_plane_triple_of_det_ne_zero
    simp only [planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
    nlinarith
  have heq : ((fun v : ({2, 3, 4} : Finset (Fin 5)) =>
      referenceSplitPosition a b v) ∘ e) =
      ![planePoint 0 1, planePoint a 0, planePoint 0 b] := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact h

/-- The three triangles produced when a line meets the two edges issuing from the origin of the
standard triangle. -/
noncomputable def referenceSplitMesh (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1) : TriangleMesh where
  Vertex := Fin 5
  position := referenceSplitPosition a b
  position_injective := referenceSplitPosition_injective ha0 ha1 hb0 hb1
  triangles := referenceSplitTriangles
  card_triangle := by
    intro t ht
    simp only [referenceSplitTriangles, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> decide
  affineIndependent_triangle := by
    intro t ht
    simp only [referenceSplitTriangles, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact affineIndependent_referenceTriangle0 ha0 hb0
    · exact affineIndependent_referenceTriangle1 ha1
    · exact affineIndependent_referenceTriangle2 ha0 hb1
  triangle_inter := by
    intro s hs t ht
    simp only [referenceSplitTriangles, Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl
    · simp
    · apply convexHull_image_inter_of_affine_separation _
        (referenceSplitPosition_injective ha0 ha1 hb0 hb1) _ _ (-referenceVertexAffine a b)
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp only [referenceSplitPosition, Fin.isValue, Matrix.cons_val_zero, AffineMap.coe_neg,
            Pi.neg_apply, referenceVertexAffine_planePoint, mul_zero, add_zero, zero_sub, neg_neg,
            Matrix.cons_val, sub_self, neg_zero, Std.le_refl, zero_add, neg_sub, sub_nonneg] <;>
          (try field_simp) <;> nlinarith
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp only [referenceSplitPosition, Fin.isValue, Matrix.cons_val_one,
            Matrix.cons_val_zero, AffineMap.coe_neg, Pi.neg_apply,
            referenceVertexAffine_planePoint, mul_zero, add_zero, neg_sub, tsub_le_iff_right,
            zero_add, Matrix.cons_val, mul_one, sub_self, neg_zero, Std.le_refl] <;>
          (try field_simp) <;> nlinarith
      · intro x hx
        fin_cases x <;>
          simp only [Fin.isValue, Fin.zero_eta, Finset.mem_insert, Fin.reduceEq,
            Finset.mem_singleton, or_self, or_false, referenceSplitPosition, Matrix.cons_val_zero,
            AffineMap.coe_neg, Pi.neg_apply, referenceVertexAffine_planePoint, mul_zero, add_zero,
            zero_sub, neg_neg, one_ne_zero, not_false_eq_true, Finset.inter_insert_of_notMem,
            or_true, Finset.inter_singleton_of_mem, iff_false, Fin.mk_one, Fin.reduceFinMk,
            Matrix.cons_val, sub_self, neg_zero, zero_add, neg_sub] at hx ⊢ <;>
          (try field_simp) <;> nlinarith
      · intro x hx
        fin_cases x <;>
          simp only [Fin.isValue, Fin.zero_eta, Finset.mem_insert, zero_ne_one, Fin.reduceEq,
            Finset.mem_singleton, or_self, Fin.mk_one, or_false, referenceSplitPosition,
            Matrix.cons_val_one, Matrix.cons_val_zero, AffineMap.coe_neg, Pi.neg_apply,
            referenceVertexAffine_planePoint, mul_zero, add_zero, neg_sub, one_ne_zero,
            not_false_eq_true, Finset.inter_insert_of_notMem, or_true,
            Finset.inter_singleton_of_mem, iff_false, Fin.reduceFinMk, Matrix.cons_val, mul_one,
            zero_add, sub_self, neg_zero] at hx ⊢ <;>
          (try field_simp) <;> nlinarith
    · apply convexHull_image_inter_of_affine_separation _
        (referenceSplitPosition_injective ha0 ha1 hb0 hb1) _ _ (-referenceOuterAffine a b)
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceSplitPosition, referenceOuterAffine_planePoint, ha0.ne', hb0.ne']
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp only [referenceSplitPosition, Fin.isValue, Matrix.cons_val, AffineMap.coe_neg,
            Pi.neg_apply, referenceOuterAffine_planePoint, mul_zero, mul_one, zero_add, neg_sub,
            tsub_le_iff_right, ne_eq, ha0.ne', not_false_eq_true, inv_mul_cancel₀, add_zero,
            sub_self, neg_zero, Std.le_refl, hb0.ne'];
          (try field_simp); nlinarith
      · intro x hx
        fin_cases x <;> simp [referenceSplitPosition, referenceOuterAffine_planePoint,
          ha0.ne', hb0.ne'] at hx ⊢
      · intro x hx
        fin_cases x <;> simp [referenceSplitPosition, referenceOuterAffine_planePoint,
          ha0.ne', hb0.ne'] at hx ⊢; field_simp; nlinarith
    · rw [Set.inter_comm]
      apply convexHull_image_inter_of_affine_separation _
        (referenceSplitPosition_injective ha0 ha1 hb0 hb1) _ _ (-referenceVertexAffine a b)
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp only [referenceSplitPosition, Fin.isValue, Matrix.cons_val_zero, AffineMap.coe_neg,
            Pi.neg_apply, referenceVertexAffine_planePoint, mul_zero, add_zero, zero_sub, neg_neg,
            Matrix.cons_val, sub_self, neg_zero, Std.le_refl, zero_add, neg_sub, sub_nonneg] <;>
          (try field_simp) <;> nlinarith
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp only [referenceSplitPosition, Fin.isValue, Matrix.cons_val_one,
            Matrix.cons_val_zero, AffineMap.coe_neg, Pi.neg_apply,
            referenceVertexAffine_planePoint, mul_zero, add_zero, neg_sub, tsub_le_iff_right,
            zero_add, Matrix.cons_val, mul_one, sub_self, neg_zero, Std.le_refl] <;>
          (try field_simp) <;> nlinarith
      · intro x hx
        fin_cases x <;>
          simp only [Fin.isValue, Fin.zero_eta, Finset.mem_insert, Fin.reduceEq,
            Finset.mem_singleton, or_self, or_false, referenceSplitPosition, Matrix.cons_val_zero,
            AffineMap.coe_neg, Pi.neg_apply, referenceVertexAffine_planePoint, mul_zero, add_zero,
            zero_sub, neg_neg, one_ne_zero, not_false_eq_true, Finset.inter_insert_of_notMem,
            or_true, Finset.inter_singleton_of_mem, iff_false, Fin.mk_one, Fin.reduceFinMk,
            Matrix.cons_val, sub_self, neg_zero, zero_add, neg_sub] at hx ⊢ <;>
          (try field_simp) <;> nlinarith
      · intro x hx
        fin_cases x <;>
          simp only [Fin.isValue, Fin.zero_eta, Finset.mem_insert, zero_ne_one, Fin.reduceEq,
            Finset.mem_singleton, or_self, Fin.mk_one, or_false, referenceSplitPosition,
            Matrix.cons_val_one, Matrix.cons_val_zero, AffineMap.coe_neg, Pi.neg_apply,
            referenceVertexAffine_planePoint, mul_zero, add_zero, neg_sub, one_ne_zero,
            not_false_eq_true, Finset.inter_insert_of_notMem, or_true,
            Finset.inter_singleton_of_mem, iff_false, Fin.reduceFinMk, Matrix.cons_val, mul_one,
            zero_add, sub_self, neg_zero] at hx ⊢ <;>
          (try field_simp) <;> nlinarith
    · simp
    · apply convexHull_image_inter_of_affine_separation _
        (referenceSplitPosition_injective ha0 ha1 hb0 hb1) _ _ (referenceDiagonalAffine a)
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceSplitPosition, referenceDiagonalAffine_planePoint]; nlinarith
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceSplitPosition, referenceDiagonalAffine_planePoint]; nlinarith
      · intro x hx
        fin_cases x <;>
          simp [referenceSplitPosition, referenceDiagonalAffine_planePoint] at hx ⊢;
          nlinarith
      · intro x hx
        fin_cases x <;>
          simp [referenceSplitPosition, referenceDiagonalAffine_planePoint] at hx ⊢;
          nlinarith
    · rw [Set.inter_comm]
      apply convexHull_image_inter_of_affine_separation _
        (referenceSplitPosition_injective ha0 ha1 hb0 hb1) _ _ (-referenceOuterAffine a b)
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceSplitPosition, referenceOuterAffine_planePoint, ha0.ne', hb0.ne']
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceSplitPosition, referenceOuterAffine_planePoint, ha0.ne', hb0.ne'];
          field_simp; nlinarith
      · intro x hx
        fin_cases x <;> simp [referenceSplitPosition, referenceOuterAffine_planePoint,
          ha0.ne', hb0.ne'] at hx ⊢
      · intro x hx
        fin_cases x <;> simp [referenceSplitPosition, referenceOuterAffine_planePoint,
          ha0.ne', hb0.ne'] at hx ⊢; field_simp; nlinarith
    · rw [Set.inter_comm]
      apply convexHull_image_inter_of_affine_separation _
        (referenceSplitPosition_injective ha0 ha1 hb0 hb1) _ _ (referenceDiagonalAffine a)
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceSplitPosition, referenceDiagonalAffine_planePoint]; nlinarith
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceSplitPosition, referenceDiagonalAffine_planePoint]; nlinarith
      · intro x hx
        fin_cases x <;>
          simp [referenceSplitPosition, referenceDiagonalAffine_planePoint] at hx ⊢;
          nlinarith
      · intro x hx
        fin_cases x <;>
          simp [referenceSplitPosition, referenceDiagonalAffine_planePoint] at hx ⊢;
          nlinarith
    · simp

/-- A three-term nonnegative affine combination belongs to the corresponding triangle. -/
theorem mem_convexHull_range_fin3_of_weights (p : Fin 3 → Plane) (x : Plane)
    (w : Fin 3 → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : w 0 + w 1 + w 2 = 1)
    (hx : w 0 • p 0 + w 1 • p 1 + w 2 • p 2 = x) :
    x ∈ convexHull ℝ (Set.range p) := by
  rw [convexHull_range_eq_exists_affineCombination]
  refine ⟨Finset.univ, w, fun i _ => hw i, ?_, ?_⟩
  · simpa [Fin.sum_univ_succ, add_assoc] using hsum
  · rw [Finset.affineCombination_eq_linear_combination]
    · simpa [Fin.sum_univ_succ, add_assoc] using hx
    · simpa [Fin.sum_univ_succ, add_assoc] using hsum

/-- Cartesian membership criterion for the standard closed triangle. -/
theorem mem_standardTriangle_iff (x : Plane) :
    x ∈ convexHull ℝ (Set.range ![planePoint 0 0, planePoint 1 0, planePoint 0 1]) ↔
      0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 := by
  constructor
  · intro hx
    refine ⟨?_, ?_, ?_⟩
    · apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage cartesianX) hx
      rintro p ⟨i, rfl⟩
      fin_cases i <;> simp
    · apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage cartesianY) hx
      rintro p ⟨i, rfl⟩
      fin_cases i <;> simp
    · let f : Plane →ᵃ[ℝ] ℝ := cartesianX + cartesianY
      apply convexHull_min _ ((convex_Iic (1 : ℝ)).affine_preimage f) hx
      rintro p ⟨i, rfl⟩
      fin_cases i <;> simp [f]
  · rintro ⟨hx0, hx1, hxsum⟩
    apply mem_convexHull_range_fin3_of_weights _ x
      ![1 - x 0 - x 1, x 0, x 1]
    · intro i
      fin_cases i <;> simp <;> linarith
    · simp
      ring
    · ext i
      fin_cases i <;> simp [planePoint]

private theorem referenceTriangle0_carrier (a b : ℝ) :
    referenceSplitPosition a b '' (({0, 3, 4} : Finset (Fin 5)) : Set (Fin 5)) =
      Set.range ![planePoint 0 0, planePoint a 0, planePoint 0 b] := by
  ext x
  simp [referenceSplitPosition]
  tauto

private theorem referenceTriangle1_carrier (a b : ℝ) :
    referenceSplitPosition a b '' (({1, 2, 3} : Finset (Fin 5)) : Set (Fin 5)) =
      Set.range ![planePoint 1 0, planePoint 0 1, planePoint a 0] := by
  ext x
  simp [referenceSplitPosition]
  tauto

private theorem referenceTriangle2_carrier (a b : ℝ) :
    referenceSplitPosition a b '' (({2, 3, 4} : Finset (Fin 5)) : Set (Fin 5)) =
      Set.range ![planePoint 0 1, planePoint a 0, planePoint 0 b] := by
  ext x
  simp [referenceSplitPosition]
  tauto

/-- The three reference triangles cover exactly the standard triangle. -/
theorem referenceSplit_union (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1) :
    (⋃ t ∈ referenceSplitTriangles,
      convexHull ℝ (referenceSplitPosition a b '' (t : Set (Fin 5)))) =
      convexHull ℝ (Set.range ![planePoint 0 0, planePoint 1 0, planePoint 0 1]) := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨t, ht, hxt⟩
    have ht' : t = {0, 3, 4} ∨ t = {1, 2, 3} ∨ t = {2, 3, 4} := by
      simpa only [referenceSplitTriangles, Finset.mem_insert, Finset.mem_singleton] using ht
    rcases ht' with rfl | rfl | rfl
    · rw [referenceTriangle0_carrier] at hxt
      apply convexHull_min _ (convex_convexHull ℝ _) hxt
      rintro p ⟨i, rfl⟩
      fin_cases i <;> apply (mem_standardTriangle_iff _).mpr <;>
        simp [ha0.le, ha1.le, hb0.le, hb1.le]
    · rw [referenceTriangle1_carrier] at hxt
      apply convexHull_min _ (convex_convexHull ℝ _) hxt
      rintro p ⟨i, rfl⟩
      fin_cases i <;> apply (mem_standardTriangle_iff _).mpr <;>
        simp [ha0.le, ha1.le]
    · rw [referenceTriangle2_carrier] at hxt
      apply convexHull_min _ (convex_convexHull ℝ _) hxt
      rintro p ⟨i, rfl⟩
      fin_cases i <;> apply (mem_standardTriangle_iff _).mpr <;>
        simp [ha0.le, ha1.le, hb0.le, hb1.le]
  · intro hx
    obtain ⟨hx0, hx1, hxsum⟩ := (mem_standardTriangle_iff x).mp hx
    by_cases houter : x 0 / a + x 1 / b ≤ 1
    · refine ⟨{0, 3, 4}, Finset.mem_insert_self _ _, ?_⟩
      rw [referenceTriangle0_carrier]
      apply mem_convexHull_range_fin3_of_weights _ x
        ![1 - x 0 / a - x 1 / b, x 0 / a, x 1 / b]
      · intro i
        fin_cases i
        · simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero, sub_nonneg]
          linarith
        · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
          exact div_nonneg hx0 ha0.le
        · simp only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val]
          exact div_nonneg hx1 hb0.le
      · simp
        ring
      · ext i
        fin_cases i <;> simp [planePoint] <;> field_simp
    · have houter' : 1 ≤ x 0 / a + x 1 / b := le_of_not_ge houter
      by_cases hdiag : 0 ≤ x 0 + a * x 1 - a
      · have h1a : 1 - a ≠ 0 := by linarith
        refine ⟨{1, 2, 3}, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩
        rw [referenceTriangle1_carrier]
        apply mem_convexHull_range_fin3_of_weights _ x
          ![(x 0 + a * x 1 - a) / (1 - a), x 1,
            (1 - x 0 - x 1) / (1 - a)]
        · intro i
          fin_cases i
          · simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero]
            exact div_nonneg hdiag (by linarith)
          · simpa using hx1
          · simp only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val]
            exact div_nonneg (by linarith) (by linarith)
        · simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val]
          field_simp [h1a]
          ring
        · ext i
          fin_cases i <;> simp [planePoint] ; field_simp [h1a] ; ring
      · have hdiag' : x 0 + a * x 1 - a ≤ 0 := le_of_not_ge hdiag
        have h1b : 1 - b ≠ 0 := by linarith
        have hnum0 : 0 ≤ x 1 - b + b * (x 0 / a) := by
          have hy : 1 - x 0 / a ≤ x 1 / b := by linarith
          have hy' : (1 - x 0 / a) * b ≤ x 1 := (le_div_iff₀ hb0).mp hy
          linarith
        have hnum2 : 0 ≤ 1 - x 1 - x 0 / a := by
          have hxdiv : x 0 / a ≤ 1 - x 1 :=
            (div_le_iff₀ ha0).mpr (by nlinarith [hdiag'])
          linarith
        refine ⟨{2, 3, 4}, Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), ?_⟩
        rw [referenceTriangle2_carrier]
        apply mem_convexHull_range_fin3_of_weights _ x
          ![(x 1 - b + b * (x 0 / a)) / (1 - b), x 0 / a,
            (1 - x 1 - x 0 / a) / (1 - b)]
        · intro i
          fin_cases i
          · simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero]
            exact div_nonneg hnum0 (by linarith)
          · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
            exact div_nonneg hx0 ha0.le
          · simp only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val]
            exact div_nonneg hnum2 (by linarith)
        · simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          field_simp [h1b, ha0.ne']
          ring
        · ext i
          fin_cases i <;> simp [planePoint] <;>
            field_simp [h1b, ha0.ne']; ring

/-- The reference line split preserves the support of the standard triangle. -/
theorem referenceSplitMesh_support (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1) :
    (referenceSplitMesh a b ha0 ha1 hb0 hb1).toPlaneComplex.support =
      convexHull ℝ (Set.range ![planePoint 0 0, planePoint 1 0, planePoint 0 1]) := by
  rw [TriangleMesh.toPlaneComplex_support]
  change (⋃ t ∈ referenceSplitTriangles,
    convexHull ℝ (referenceSplitPosition a b '' (t : Set (Fin 5)))) = _
  exact referenceSplit_union a b ha0 ha1 hb0 hb1

/-! ## The reference split through one vertex -/

/-- The `referenceEdgeSplitPosition` declaration. -/
def referenceEdgeSplitPosition (c : ℝ) : Fin 4 → Plane :=
  ![planePoint 0 0, planePoint 1 0, planePoint 0 1, planePoint c 0]

/-- The `referenceEdgeSplitTriangles` declaration. -/
def referenceEdgeSplitTriangles : Finset (Finset (Fin 4)) :=
  {{0, 2, 3}, {1, 2, 3}}

theorem referenceEdgeSplitPosition_injective {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    Function.Injective (referenceEdgeSplitPosition c) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals
    exfalso
    dsimp [referenceEdgeSplitPosition] at hij
    have h0 := congrArg (fun x : Plane => x 0) hij
    have h1 := congrArg (fun x : Plane => x 1) hij
    simp only [planePoint_apply_zero] at h0
    simp only [planePoint_apply_one] at h1
    linarith

private theorem affineIndependent_referenceEdgeTriangle0 {c : ℝ} (hc0 : 0 < c) :
    AffineIndependent ℝ fun v : ({0, 2, 3} : Finset (Fin 4)) =>
      referenceEdgeSplitPosition c v := by
  let e := (Fin.orderIsoTriple (0 : Fin 4) 2 3 (by decide) (by decide)).toEquiv
  apply (affineIndependent_equiv e).mp
  have h : AffineIndependent ℝ ![planePoint 0 0, planePoint 0 1, planePoint c 0] := by
    apply affineIndependent_plane_triple_of_det_ne_zero
    simp only [planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
    nlinarith
  have heq : ((fun v : ({0, 2, 3} : Finset (Fin 4)) =>
      referenceEdgeSplitPosition c v) ∘ e) =
      ![planePoint 0 0, planePoint 0 1, planePoint c 0] := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact h

private theorem affineIndependent_referenceEdgeTriangle1 {c : ℝ} (hc1 : c < 1) :
    AffineIndependent ℝ fun v : ({1, 2, 3} : Finset (Fin 4)) =>
      referenceEdgeSplitPosition c v := by
  let e := (Fin.orderIsoTriple (1 : Fin 4) 2 3 (by decide) (by decide)).toEquiv
  apply (affineIndependent_equiv e).mp
  have h : AffineIndependent ℝ ![planePoint 1 0, planePoint 0 1, planePoint c 0] := by
    apply affineIndependent_plane_triple_of_det_ne_zero
    simp only [planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
    nlinarith
  have heq : ((fun v : ({1, 2, 3} : Finset (Fin 4)) =>
      referenceEdgeSplitPosition c v) ∘ e) =
      ![planePoint 1 0, planePoint 0 1, planePoint c 0] := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact h

/-- The two-triangle reference mesh used when the cutting line passes through vertex `2`. -/
noncomputable def referenceEdgeSplitMesh (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    TriangleMesh where
  Vertex := Fin 4
  position := referenceEdgeSplitPosition c
  position_injective := referenceEdgeSplitPosition_injective hc0 hc1
  triangles := referenceEdgeSplitTriangles
  card_triangle := by
    intro t ht
    simp only [referenceEdgeSplitTriangles, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> decide
  affineIndependent_triangle := by
    intro t ht
    simp only [referenceEdgeSplitTriangles, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact affineIndependent_referenceEdgeTriangle0 hc0
    · exact affineIndependent_referenceEdgeTriangle1 hc1
  triangle_inter := by
    intro s hs t ht
    simp only [referenceEdgeSplitTriangles, Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · simp
    · apply convexHull_image_inter_of_affine_separation _
        (referenceEdgeSplitPosition_injective hc0 hc1) _ _ (-referenceDiagonalAffine c)
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceEdgeSplitPosition, referenceDiagonalAffine_planePoint]; nlinarith
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceEdgeSplitPosition, referenceDiagonalAffine_planePoint]; nlinarith
      · intro x hx
        fin_cases x <;>
          simp [referenceEdgeSplitPosition, referenceDiagonalAffine_planePoint] at hx ⊢;
          nlinarith
      · intro x hx
        fin_cases x <;>
          simp [referenceEdgeSplitPosition, referenceDiagonalAffine_planePoint] at hx ⊢;
          nlinarith
    · rw [Set.inter_comm]
      apply convexHull_image_inter_of_affine_separation _
        (referenceEdgeSplitPosition_injective hc0 hc1) _ _ (-referenceDiagonalAffine c)
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceEdgeSplitPosition, referenceDiagonalAffine_planePoint]; nlinarith
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceEdgeSplitPosition, referenceDiagonalAffine_planePoint]; nlinarith
      · intro x hx
        fin_cases x <;>
          simp [referenceEdgeSplitPosition, referenceDiagonalAffine_planePoint] at hx ⊢;
          nlinarith
      · intro x hx
        fin_cases x <;>
          simp [referenceEdgeSplitPosition, referenceDiagonalAffine_planePoint] at hx ⊢;
          nlinarith
    · simp

private theorem referenceEdgeTriangle0_carrier (c : ℝ) :
    referenceEdgeSplitPosition c '' (({0, 2, 3} : Finset (Fin 4)) : Set (Fin 4)) =
      Set.range ![planePoint 0 0, planePoint 0 1, planePoint c 0] := by
  ext x
  simp [referenceEdgeSplitPosition]
  tauto

private theorem referenceEdgeTriangle1_carrier (c : ℝ) :
    referenceEdgeSplitPosition c '' (({1, 2, 3} : Finset (Fin 4)) : Set (Fin 4)) =
      Set.range ![planePoint 1 0, planePoint 0 1, planePoint c 0] := by
  ext x
  simp [referenceEdgeSplitPosition]
  tauto

theorem referenceEdgeSplit_union (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    (⋃ t ∈ referenceEdgeSplitTriangles,
      convexHull ℝ (referenceEdgeSplitPosition c '' (t : Set (Fin 4)))) =
      convexHull ℝ (Set.range ![planePoint 0 0, planePoint 1 0, planePoint 0 1]) := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨t, ht, hxt⟩
    have ht' : t = {0, 2, 3} ∨ t = {1, 2, 3} := by
      simpa only [referenceEdgeSplitTriangles, Finset.mem_insert,
        Finset.mem_singleton, or_false] using ht
    rcases ht' with rfl | rfl
    · rw [referenceEdgeTriangle0_carrier] at hxt
      apply convexHull_min _ (convex_convexHull ℝ _) hxt
      rintro p ⟨i, rfl⟩
      fin_cases i <;> apply (mem_standardTriangle_iff _).mpr <;> simp [hc0.le, hc1.le]
    · rw [referenceEdgeTriangle1_carrier] at hxt
      apply convexHull_min _ (convex_convexHull ℝ _) hxt
      rintro p ⟨i, rfl⟩
      fin_cases i <;> apply (mem_standardTriangle_iff _).mpr <;> simp [hc0.le, hc1.le]
  · intro hx
    obtain ⟨hx0, hx1, hxsum⟩ := (mem_standardTriangle_iff x).mp hx
    by_cases hd : x 0 + c * x 1 - c ≤ 0
    · refine ⟨{0, 2, 3}, Finset.mem_insert_self _ _, ?_⟩
      rw [referenceEdgeTriangle0_carrier]
      apply mem_convexHull_range_fin3_of_weights _ x
        ![1 - x 1 - x 0 / c, x 1, x 0 / c]
      · intro i
        fin_cases i
        · simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero, sub_nonneg]
          have hxdiv : x 0 / c ≤ 1 - x 1 :=
            (div_le_iff₀ hc0).mpr (by nlinarith [hd])
          have : x 0 / c + x 1 ≤ 1 := by linarith
          linarith
        · simpa using hx1
        · simp only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val]
          exact div_nonneg hx0 hc0.le
      · simp
        ring
      · ext i
        fin_cases i <;> simp [planePoint] ; field_simp [hc0.ne']
    · have hd' : 0 ≤ x 0 + c * x 1 - c := le_of_not_ge hd
      have h1c : 1 - c ≠ 0 := by linarith
      refine ⟨{1, 2, 3}, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩
      rw [referenceEdgeTriangle1_carrier]
      apply mem_convexHull_range_fin3_of_weights _ x
        ![(x 0 + c * x 1 - c) / (1 - c), x 1,
          (1 - x 0 - x 1) / (1 - c)]
      · intro i
        fin_cases i
        · simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero]
          exact div_nonneg hd' (by linarith)
        · simpa using hx1
        · simp only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val]
          exact div_nonneg (by linarith) (by linarith)
      · simp
        field_simp [h1c]
        ring
      · ext i
        fin_cases i <;> simp [planePoint] ; field_simp [h1c] ; ring

theorem referenceEdgeSplitMesh_support (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    (referenceEdgeSplitMesh c hc0 hc1).toPlaneComplex.support =
      convexHull ℝ (Set.range ![planePoint 0 0, planePoint 1 0, planePoint 0 1]) := by
  rw [TriangleMesh.toPlaneComplex_support]
  change (⋃ t ∈ referenceEdgeSplitTriangles,
    convexHull ℝ (referenceEdgeSplitPosition c '' (t : Set (Fin 4)))) = _
  exact referenceEdgeSplit_union c hc0 hc1

/-- The point where the affine functional `f` vanishes along the oriented edge from `p` to `q`.
The useful case is `f p > 0 > f q`. -/
noncomputable def affineCutPoint (f : Plane →ᵃ[ℝ] ℝ) (p q : Plane) : Plane :=
  AffineMap.lineMap p q (f p / (f p - f q))

namespace affineCutPoint

variable (f : Plane →ᵃ[ℝ] ℝ) (p q : Plane)

theorem parameter_pos (hp : 0 < f p) (hq : f q < 0) :
    0 < f p / (f p - f q) := by
  exact div_pos hp (by linarith)

theorem parameter_lt_one (hp : 0 < f p) (hq : f q < 0) :
    f p / (f p - f q) < 1 := by
  apply (div_lt_one (by linarith : 0 < f p - f q)).mpr
  linarith

theorem parameter_mem_Icc (hp : 0 < f p) (hq : f q < 0) :
    f p / (f p - f q) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(parameter_pos f p q hp hq).le, (parameter_lt_one f p q hp hq).le⟩

theorem mem_segment (hp : 0 < f p) (hq : f q < 0) :
    affineCutPoint f p q ∈ segment ℝ p q := by
  rw [segment_eq_image_lineMap]
  exact ⟨f p / (f p - f q), parameter_mem_Icc f p q hp hq, rfl⟩

@[simp] theorem apply_eq_zero (hp : 0 < f p) (hq : f q < 0) :
    f (affineCutPoint f p q) = 0 := by
  rw [affineCutPoint, f.apply_lineMap, AffineMap.lineMap_apply_module]
  have hden : f p - f q ≠ 0 := by linarith
  field_simp [hden]
  ring

theorem ne_left (hp : 0 < f p) (hq : f q < 0) : affineCutPoint f p q ≠ p := by
  intro h
  have := congrArg f h
  rw [apply_eq_zero f p q hp hq] at this
  linarith

theorem ne_right (hp : 0 < f p) (hq : f q < 0) : affineCutPoint f p q ≠ q := by
  intro h
  have := congrArg f h
  rw [apply_eq_zero f p q hp hq] at this
  linarith

theorem eq_reverse (hp : 0 < f p) (hq : f q < 0) :
    affineCutPoint f p q = affineCutPoint f q p := by
  unfold affineCutPoint
  rw [← AffineMap.lineMap_apply_one_sub p q]
  congr 1
  have hden : f p - f q ≠ 0 := by linarith
  have hden' : f q - f p ≠ 0 := by linarith
  field_simp [hden, hden']
  ring

/-- The cut point is the unique zero of `f` on an oppositely signed edge. -/
theorem eq_of_mem_segment_of_apply_eq_zero (hp : 0 < f p) (hq : f q < 0)
    {x : Plane} (hx : x ∈ segment ℝ p q) (hfx : f x = 0) :
    x = affineCutPoint f p q := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  rw [f.apply_lineMap, AffineMap.lineMap_apply_module] at hfx
  have hden : f p - f q ≠ 0 := by linarith
  unfold affineCutPoint
  congr 1
  apply (eq_div_iff hden).mpr
  simp only [smul_eq_mul] at hfx
  linarith

/-- Negating the affine functional does not change its geometric cut point. -/
theorem neg (f : Plane →ᵃ[ℝ] ℝ) (p q : Plane) :
    affineCutPoint (-f) p q = affineCutPoint f p q := by
  unfold affineCutPoint
  congr 1
  simp only [AffineMap.coe_neg, Pi.neg_apply]
  by_cases h : f p - f q = 0
  · have hpq : f p = f q := sub_eq_zero.mp h
    rw [hpq]
    simp
  · have hneg : -f p + f q ≠ 0 := by
      intro hneg
      apply h
      linarith
    field_simp [h, hneg]
    ring

end affineCutPoint

/-! ## The transported split of an arbitrary triangle -/

/-- The ordered vertices of the standard triangle. -/
def standardTrianglePosition : Fin 3 → Plane :=
  ![planePoint 0 0, planePoint 1 0, planePoint 0 1]

theorem standardTrianglePosition_affineIndependent :
    AffineIndependent ℝ standardTrianglePosition := by
  apply affineIndependent_plane_triple_of_det_ne_zero
  norm_num [standardTrianglePosition, planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]

/-- The parameter at which a line cuts the edge from the positive vertex to a negative vertex. -/
noncomputable def triangleCutParameter (f : Plane →ᵃ[ℝ] ℝ) (p q : Plane) : ℝ :=
  f p / (f p - f q)

/-- The reference split transported to an arbitrary ordered triangle.  The first vertex is on
the positive side of the line and the other two are on its negative side. -/
noncomputable def triangleLineSplitMesh (p : Fin 3 → Plane) (hp : AffineIndependent ℝ p)
    (f : Plane →ᵃ[ℝ] ℝ) (hp0 : 0 < f (p 0)) (hp1 : f (p 1) < 0)
    (hp2 : f (p 2) < 0) : TriangleMesh :=
  let a := triangleCutParameter f (p 0) (p 1)
  let b := triangleCutParameter f (p 0) (p 2)
  let R := referenceSplitMesh a b
    (affineCutPoint.parameter_pos f (p 0) (p 1) hp0 hp1)
    (affineCutPoint.parameter_lt_one f (p 0) (p 1) hp0 hp1)
    (affineCutPoint.parameter_pos f (p 0) (p 2) hp0 hp2)
    (affineCutPoint.parameter_lt_one f (p 0) (p 2) hp0 hp2)
  R.mapAffineEquiv
    (triangleAffineEquiv standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp)

/-- Splitting a triangle along an affine line preserves its support. -/
theorem triangleLineSplitMesh_support (p : Fin 3 → Plane) (hp : AffineIndependent ℝ p)
    (f : Plane →ᵃ[ℝ] ℝ) (hp0 : 0 < f (p 0)) (hp1 : f (p 1) < 0)
    (hp2 : f (p 2) < 0) :
    (triangleLineSplitMesh p hp f hp0 hp1 hp2).toPlaneComplex.support =
      convexHull ℝ (Set.range p) := by
  let a := triangleCutParameter f (p 0) (p 1)
  let b := triangleCutParameter f (p 0) (p 2)
  have ha0 : 0 < a := affineCutPoint.parameter_pos f (p 0) (p 1) hp0 hp1
  have ha1 : a < 1 := affineCutPoint.parameter_lt_one f (p 0) (p 1) hp0 hp1
  have hb0 : 0 < b := affineCutPoint.parameter_pos f (p 0) (p 2) hp0 hp2
  have hb1 : b < 1 := affineCutPoint.parameter_lt_one f (p 0) (p 2) hp0 hp2
  change ((referenceSplitMesh a b ha0 ha1 hb0 hb1).mapAffineEquiv
    (triangleAffineEquiv standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp)).toPlaneComplex.support = _
  rw [TriangleMesh.mapAffineEquiv_support,
    referenceSplitMesh_support a b ha0 ha1 hb0 hb1]
  exact triangleAffineEquiv_image_convexHull standardTrianglePosition p
    standardTrianglePosition_affineIndependent hp

/-! ## Coherent cut vertices for a finite mesh -/

namespace TriangleMesh

variable (M : TriangleMesh) (f : Plane →ᵃ[ℝ] ℝ)

/-- The maximal triangles, packaged with their membership proof. -/
abbrev Triangle := {t : Finset M.Vertex // t ∈ M.triangles}

/-- A proof-independent ordering of the three vertices of a maximal triangle. -/
noncomputable def triangleEquiv (t : M.Triangle) : t.1 ≃ Fin 3 :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe, M.card_triangle t.1 t.2])

/-- A proof-independent ordering of the three vertices of a maximal triangle. -/
noncomputable def orderedVertex (t : M.Triangle) : Fin 3 → M.Vertex :=
  fun i => ((M.triangleEquiv t).symm i).1

theorem orderedVertex_injective (t : M.Triangle) :
    Function.Injective (M.orderedVertex t) := by
  intro i j hij
  exact (M.triangleEquiv t).symm.injective (Subtype.ext hij)

theorem range_orderedVertex (t : M.Triangle) :
    Set.range (M.orderedVertex t) = (t.1 : Set M.Vertex) := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ((M.triangleEquiv t).symm i).2
  · intro hv
    let vt : t.1 := ⟨v, hv⟩
    exact ⟨M.triangleEquiv t vt, by
      simp only [orderedVertex, Equiv.symm_apply_apply, vt]⟩

theorem orderedVertex_mem (t : M.Triangle) (i : Fin 3) : M.orderedVertex t i ∈ t.1 := by
  have h : M.orderedVertex t i ∈ Set.range (M.orderedVertex t) := Set.mem_range_self i
  rwa [M.range_orderedVertex t] at h

theorem orderedVertex_affineIndependent (t : M.Triangle) :
    AffineIndependent ℝ (M.position ∘ M.orderedVertex t) := by
  let e : Fin 3 ≃ t.1 := (M.triangleEquiv t).symm
  have h := (affineIndependent_equiv e).mpr (M.affineIndependent_triangle t.1 t.2)
  have heq : ((fun v : t.1 => M.position v) ∘ e) =
      M.position ∘ M.orderedVertex t := by
    rfl
  rw [← heq]
  exact h

/-- Ordered pairs of old vertices whose values under `f` have opposite signs.  Both orientations
are retained; their geometric cut positions are equal and are deduplicated in `refinementPoints`.
-/
noncomputable def crossingPairs : Finset (M.Vertex × M.Vertex) :=
  (Finset.univ ×ˢ Finset.univ).filter fun uv =>
    f (M.position uv.1) * f (M.position uv.2) < 0

/-- The geometric zero of `f` on an oppositely signed pair of old vertices. -/
noncomputable def pairCutPosition (u v : M.Vertex) : Plane :=
  affineCutPoint f (M.position u) (M.position v)

/-- All old vertex positions together with all possible cut positions.  Using geometric points
as the new vertex labels automatically identifies the cut computed from the two orientations of
one edge, and the same edge as seen from its two incident triangles. -/
noncomputable def refinementPoints : Finset Plane :=
  Finset.univ.image M.position ∪
    (M.crossingPairs f).image fun uv => M.pairCutPosition f uv.1 uv.2

/-- Vertex type used by the coherent refinement. -/
abbrev RefinedVertex := {p : Plane // p ∈ M.refinementPoints f}

/-- An old vertex as a vertex of the coherent refinement. -/
noncomputable def oldRefinedVertex (v : M.Vertex) : M.RefinedVertex f :=
  ⟨M.position v, by
    unfold refinementPoints
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩

/-- The cut point of an oppositely signed pair as a vertex of the coherent refinement. -/
noncomputable def cutRefinedVertex (u v : M.Vertex)
    (huv : f (M.position u) * f (M.position v) < 0) : M.RefinedVertex f :=
  ⟨M.pairCutPosition f u v, by
    unfold refinementPoints
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨(u, v), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, huv⟩, rfl⟩⟩

@[simp] theorem oldRefinedVertex_val (v : M.Vertex) :
    (M.oldRefinedVertex f v : Plane) = M.position v := rfl

@[simp] theorem cutRefinedVertex_val (u v : M.Vertex)
    (huv : f (M.position u) * f (M.position v) < 0) :
    (M.cutRefinedVertex f u v huv : Plane) = M.pairCutPosition f u v := rfl

theorem pairCutPosition_eq_reverse (u v : M.Vertex)
    (huv : f (M.position u) * f (M.position v) < 0) :
    M.pairCutPosition f u v = M.pairCutPosition f v u := by
  rcases mul_neg_iff.mp huv with huv | huv
  · exact affineCutPoint.eq_reverse f (M.position u) (M.position v) huv.1 huv.2
  · exact (affineCutPoint.eq_reverse f (M.position v) (M.position u) huv.2 huv.1).symm

theorem pairCutPosition_apply_eq_zero (u v : M.Vertex)
    (huv : f (M.position u) * f (M.position v) < 0) :
    f (M.pairCutPosition f u v) = 0 := by
  rcases mul_neg_iff.mp huv with huv | huv
  · exact affineCutPoint.apply_eq_zero f (M.position u) (M.position v) huv.1 huv.2
  · rw [M.pairCutPosition_eq_reverse f u v (mul_neg_iff.mpr (Or.inr huv))]
    exact affineCutPoint.apply_eq_zero f (M.position v) (M.position u) huv.2 huv.1

theorem crossingPairs_neg : M.crossingPairs (-f) = M.crossingPairs f := by
  classical
  unfold crossingPairs
  apply Finset.filter_congr
  intro uv huv
  simp only [AffineMap.coe_neg, Pi.neg_apply]
  ring_nf

theorem refinementPoints_neg : M.refinementPoints (-f) = M.refinementPoints f := by
  classical
  unfold refinementPoints pairCutPosition
  rw [M.crossingPairs_neg f]
  congr 1
  apply Finset.image_congr
  intro uv huv
  exact affineCutPoint.neg f (M.position uv.1) (M.position uv.2)

/-- Identifying the coherent vertex pools for `f` and `-f`; geometrically this is the identity. -/
noncomputable def refinedVertexNegEquiv : M.RefinedVertex (-f) ≃ M.RefinedVertex f where
  toFun v := ⟨v.1, by rw [← M.refinementPoints_neg f]; exact v.2⟩
  invFun v := ⟨v.1, by rw [M.refinementPoints_neg f]; exact v.2⟩
  left_inv v := Subtype.ext rfl
  right_inv v := Subtype.ext rfl

@[simp] theorem refinedVertexNegEquiv_val (v : M.RefinedVertex (-f)) :
    (M.refinedVertexNegEquiv f v : Plane) = v := rfl

/-- The five vertices of the strict `+--` model in the coherent global vertex pool. -/
noncomputable def strictModelVertex (t : M.Triangle)
    (h0 : 0 < f (M.position (M.orderedVertex t 0)))
    (h1 : f (M.position (M.orderedVertex t 1)) < 0)
    (h2 : f (M.position (M.orderedVertex t 2)) < 0) : Fin 5 → M.RefinedVertex f :=
  ![M.oldRefinedVertex f (M.orderedVertex t 0),
    M.oldRefinedVertex f (M.orderedVertex t 1),
    M.oldRefinedVertex f (M.orderedVertex t 2),
    M.cutRefinedVertex f (M.orderedVertex t 0) (M.orderedVertex t 1)
      (mul_neg_iff.mpr (Or.inl ⟨h0, h1⟩)),
    M.cutRefinedVertex f (M.orderedVertex t 0) (M.orderedVertex t 2)
      (mul_neg_iff.mpr (Or.inl ⟨h0, h2⟩))]

/-- The geometric five-point list underlying a strict split. -/
noncomputable def strictModelPosition (p : Fin 3 → Plane) (f : Plane →ᵃ[ℝ] ℝ) : Fin 5 → Plane :=
  ![p 0, p 1, p 2, affineCutPoint f (p 0) (p 1), affineCutPoint f (p 0) (p 2)]

theorem strictModelVertex_val (t : M.Triangle)
    (h0 : 0 < f (M.position (M.orderedVertex t 0)))
    (h1 : f (M.position (M.orderedVertex t 1)) < 0)
    (h2 : f (M.position (M.orderedVertex t 2)) < 0) (i : Fin 5) :
    (M.strictModelVertex f t h0 h1 h2 i : Plane) =
      strictModelPosition (M.position ∘ M.orderedVertex t) f i := by
  fin_cases i <;> rfl

/-- Geometric identification of the strict five-point list with the affine image of the reference
split. -/
theorem strictModelPosition_eq_affineReference (p : Fin 3 → Plane)
    (hp : AffineIndependent ℝ p) (_ : 0 < f (p 0)) (_ : f (p 1) < 0)
    (_ : f (p 2) < 0) (i : Fin 5) :
    strictModelPosition p f i =
      triangleAffineEquiv standardTrianglePosition p standardTrianglePosition_affineIndependent hp
        (referenceSplitPosition (triangleCutParameter f (p 0) (p 1))
          (triangleCutParameter f (p 0) (p 2)) i) := by
  let e := triangleAffineEquiv standardTrianglePosition p
    standardTrianglePosition_affineIndependent hp
  fin_cases i
  · simp only [strictModelPosition, referenceSplitPosition]
    exact (triangleAffineEquiv_apply standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp 0).symm
  · simp only [strictModelPosition, referenceSplitPosition]
    exact (triangleAffineEquiv_apply standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp 1).symm
  · simp only [strictModelPosition, referenceSplitPosition]
    exact (triangleAffineEquiv_apply standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp 2).symm
  · simp only [strictModelPosition, referenceSplitPosition]
    change affineCutPoint f (p 0) (p 1) =
      e (planePoint (triangleCutParameter f (p 0) (p 1)) 0)
    rw [show planePoint (triangleCutParameter f (p 0) (p 1)) 0 =
        AffineMap.lineMap (standardTrianglePosition 0) (standardTrianglePosition 1)
          (triangleCutParameter f (p 0) (p 1)) by
      ext j; fin_cases j <;> simp [standardTrianglePosition, planePoint,
        AffineMap.lineMap_apply_module]]
    exact (triangleAffineEquiv_apply_lineMap standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp 0 1
        (triangleCutParameter f (p 0) (p 1))).symm
  · simp only [strictModelPosition, referenceSplitPosition]
    change affineCutPoint f (p 0) (p 2) =
      e (planePoint 0 (triangleCutParameter f (p 0) (p 2)))
    rw [show planePoint 0 (triangleCutParameter f (p 0) (p 2)) =
        AffineMap.lineMap (standardTrianglePosition 0) (standardTrianglePosition 2)
          (triangleCutParameter f (p 0) (p 2)) by
      ext j; fin_cases j <;> simp [standardTrianglePosition, planePoint,
        AffineMap.lineMap_apply_module]]
    exact (triangleAffineEquiv_apply_lineMap standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp 0 2
        (triangleCutParameter f (p 0) (p 2))).symm

/-- The strict local model embedded into the shared refinement vertex type. -/
noncomputable def strictLocalEmbedding (t : M.Triangle)
    (h0 : 0 < f (M.position (M.orderedVertex t 0)))
    (h1 : f (M.position (M.orderedVertex t 1)) < 0)
    (h2 : f (M.position (M.orderedVertex t 2)) < 0) : Fin 5 ↪ M.RefinedVertex f where
  toFun := M.strictModelVertex f t h0 h1 h2
  inj' := by
    intro i j hij
    have hpos := congrArg Subtype.val hij
    rw [M.strictModelVertex_val f t h0 h1 h2,
      M.strictModelVertex_val f t h0 h1 h2,
      strictModelPosition_eq_affineReference f _ (M.orderedVertex_affineIndependent t) h0 h1 h2,
      strictModelPosition_eq_affineReference f _ (M.orderedVertex_affineIndependent t) h0 h1 h2]
      at hpos
    apply (referenceSplitPosition_injective
      (affineCutPoint.parameter_pos f _ _ h0 h1)
      (affineCutPoint.parameter_lt_one f _ _ h0 h1)
      (affineCutPoint.parameter_pos f _ _ h0 h2)
      (affineCutPoint.parameter_lt_one f _ _ h0 h2))
    exact (triangleAffineEquiv standardTrianglePosition (M.position ∘ M.orderedVertex t)
      standardTrianglePosition_affineIndependent
        (M.orderedVertex_affineIndependent t)).injective hpos

/-- The strict local split, now using the coherent global vertex pool. -/
noncomputable def strictLocalMesh (t : M.Triangle)
    (h0 : 0 < f (M.position (M.orderedVertex t 0)))
    (h1 : f (M.position (M.orderedVertex t 1)) < 0)
    (h2 : f (M.position (M.orderedVertex t 2)) < 0) : TriangleMesh :=
  let a := triangleCutParameter f (M.position (M.orderedVertex t 0))
    (M.position (M.orderedVertex t 1))
  let b := triangleCutParameter f (M.position (M.orderedVertex t 0))
    (M.position (M.orderedVertex t 2))
  let R := referenceSplitMesh a b
    (affineCutPoint.parameter_pos f _ _ h0 h1)
    (affineCutPoint.parameter_lt_one f _ _ h0 h1)
    (affineCutPoint.parameter_pos f _ _ h0 h2)
    (affineCutPoint.parameter_lt_one f _ _ h0 h2)
  let e := triangleAffineEquiv standardTrianglePosition (M.position ∘ M.orderedVertex t)
    standardTrianglePosition_affineIndependent (M.orderedVertex_affineIndependent t)
  (R.mapAffineEquiv e).reindex ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
    (M.strictLocalEmbedding f t h0 h1 h2) (by
      intro i
      calc
        ((M.strictLocalEmbedding f t h0 h1 h2 i : M.RefinedVertex f) : Plane) =
            strictModelPosition (M.position ∘ M.orderedVertex t) f i :=
          M.strictModelVertex_val f t h0 h1 h2 i
        _ = e (referenceSplitPosition a b i) :=
          strictModelPosition_eq_affineReference f _ (M.orderedVertex_affineIndependent t)
            h0 h1 h2 i
        _ = (R.mapAffineEquiv e).position i := rfl)

theorem strictLocalMesh_support (t : M.Triangle)
    (h0 : 0 < f (M.position (M.orderedVertex t 0)))
    (h1 : f (M.position (M.orderedVertex t 1)) < 0)
    (h2 : f (M.position (M.orderedVertex t 2)) < 0) :
    (M.strictLocalMesh f t h0 h1 h2).toPlaneComplex.support =
      convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) := by
  let a := triangleCutParameter f (M.position (M.orderedVertex t 0))
    (M.position (M.orderedVertex t 1))
  let b := triangleCutParameter f (M.position (M.orderedVertex t 0))
    (M.position (M.orderedVertex t 2))
  let R := referenceSplitMesh a b
    (affineCutPoint.parameter_pos f _ _ h0 h1)
    (affineCutPoint.parameter_lt_one f _ _ h0 h1)
    (affineCutPoint.parameter_pos f _ _ h0 h2)
    (affineCutPoint.parameter_lt_one f _ _ h0 h2)
  let e := triangleAffineEquiv standardTrianglePosition (M.position ∘ M.orderedVertex t)
    standardTrianglePosition_affineIndependent (M.orderedVertex_affineIndependent t)
  rw [show M.strictLocalMesh f t h0 h1 h2 =
      (R.mapAffineEquiv e).reindex ((↑) : M.RefinedVertex f → Plane)
        Subtype.val_injective (M.strictLocalEmbedding f t h0 h1 h2) (by
          intro i
          calc
            ((M.strictLocalEmbedding f t h0 h1 h2 i : M.RefinedVertex f) : Plane) =
                strictModelPosition (M.position ∘ M.orderedVertex t) f i :=
              M.strictModelVertex_val f t h0 h1 h2 i
            _ = e (referenceSplitPosition a b i) :=
              strictModelPosition_eq_affineReference f _
                (M.orderedVertex_affineIndependent t) h0 h1 h2 i
            _ = (R.mapAffineEquiv e).position i := rfl) by rfl]
  erw [TriangleMesh.reindex_support, TriangleMesh.mapAffineEquiv_support,
    referenceSplitMesh_support]
  change e '' convexHull ℝ (Set.range standardTrianglePosition) =
    convexHull ℝ (M.position '' (t.1 : Set M.Vertex))
  have hrange : Set.range (M.position ∘ M.orderedVertex t) =
      M.position '' (t.1 : Set M.Vertex) := by
    rw [Set.range_comp, M.range_orderedVertex t]
  rw [← hrange]
  exact triangleAffineEquiv_image_convexHull standardTrianglePosition
    (M.position ∘ M.orderedVertex t) standardTrianglePosition_affineIndependent
      (M.orderedVertex_affineIndependent t)

/-- The strict `-++` local split, obtained by applying the `+--` model to `-f` and identifying
the two coherent vertex pools. -/
noncomputable def strictNegativeLocalMesh (t : M.Triangle)
    (h0 : f (M.position (M.orderedVertex t 0)) < 0)
    (h1 : 0 < f (M.position (M.orderedVertex t 1)))
    (h2 : 0 < f (M.position (M.orderedVertex t 2))) : TriangleMesh :=
  let N := M.strictLocalMesh (-f) t (by simpa) (by simpa) (by simpa)
  N.reindex ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
    (M.refinedVertexNegEquiv f).toEmbedding (fun _ => rfl)

theorem strictNegativeLocalMesh_support (t : M.Triangle)
    (h0 : f (M.position (M.orderedVertex t 0)) < 0)
    (h1 : 0 < f (M.position (M.orderedVertex t 1)))
    (h2 : 0 < f (M.position (M.orderedVertex t 2))) :
    (M.strictNegativeLocalMesh f t h0 h1 h2).toPlaneComplex.support =
      convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) := by
  rw [show M.strictNegativeLocalMesh f t h0 h1 h2 =
      (M.strictLocalMesh (-f) t (by simpa) (by simpa) (by simpa)).reindex
        ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
        (M.refinedVertexNegEquiv f).toEmbedding (fun _ => rfl) by rfl]
  erw [TriangleMesh.reindex_support]
  exact M.strictLocalMesh_support (-f) t (by simpa) (by simpa) (by simpa)

/-! The same strict model for an arbitrary ordering of three vertices. -/

/-- The `strictVertices` declaration. -/
noncomputable def strictVertices (v : Fin 3 → M.Vertex)
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) : Fin 5 → M.RefinedVertex f :=
  ![M.oldRefinedVertex f (v 0), M.oldRefinedVertex f (v 1), M.oldRefinedVertex f (v 2),
    M.cutRefinedVertex f (v 0) (v 1) (mul_neg_iff.mpr (Or.inl ⟨h0, h1⟩)),
    M.cutRefinedVertex f (v 0) (v 2) (mul_neg_iff.mpr (Or.inl ⟨h0, h2⟩))]

theorem strictVertices_val (v : Fin 3 → M.Vertex)
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) (i : Fin 5) :
    (M.strictVertices f v h0 h1 h2 i : Plane) = strictModelPosition (M.position ∘ v) f i := by
  fin_cases i <;> rfl

/-- The `strictVerticesEmbedding` declaration. -/
noncomputable def strictVerticesEmbedding (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) : Fin 5 ↪ M.RefinedVertex f where
  toFun := M.strictVertices f v h0 h1 h2
  inj' := by
    intro i j hij
    have hpos := congrArg Subtype.val hij
    rw [M.strictVertices_val f v h0 h1 h2, M.strictVertices_val f v h0 h1 h2,
      strictModelPosition_eq_affineReference f _ hv h0 h1 h2,
      strictModelPosition_eq_affineReference f _ hv h0 h1 h2] at hpos
    apply referenceSplitPosition_injective
      (affineCutPoint.parameter_pos f _ _ h0 h1)
      (affineCutPoint.parameter_lt_one f _ _ h0 h1)
      (affineCutPoint.parameter_pos f _ _ h0 h2)
      (affineCutPoint.parameter_lt_one f _ _ h0 h2)
    exact (triangleAffineEquiv standardTrianglePosition (M.position ∘ v)
      standardTrianglePosition_affineIndependent hv).injective hpos

/-- The `strictMeshFor` declaration. -/
noncomputable def strictMeshFor (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) : TriangleMesh :=
  let a := triangleCutParameter f (M.position (v 0)) (M.position (v 1))
  let b := triangleCutParameter f (M.position (v 0)) (M.position (v 2))
  let R := referenceSplitMesh a b
    (affineCutPoint.parameter_pos f _ _ h0 h1)
    (affineCutPoint.parameter_lt_one f _ _ h0 h1)
    (affineCutPoint.parameter_pos f _ _ h0 h2)
    (affineCutPoint.parameter_lt_one f _ _ h0 h2)
  let e := triangleAffineEquiv standardTrianglePosition (M.position ∘ v)
    standardTrianglePosition_affineIndependent hv
  (R.mapAffineEquiv e).reindex ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
    (M.strictVerticesEmbedding f v hv h0 h1 h2) (by
      intro i
      calc
        ((M.strictVerticesEmbedding f v hv h0 h1 h2 i : M.RefinedVertex f) : Plane) =
            strictModelPosition (M.position ∘ v) f i := M.strictVertices_val f v h0 h1 h2 i
        _ = e (referenceSplitPosition a b i) :=
          strictModelPosition_eq_affineReference f _ hv h0 h1 h2 i
        _ = (R.mapAffineEquiv e).position i := rfl)

theorem strictMeshFor_support (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) :
    (M.strictMeshFor f v hv h0 h1 h2).toPlaneComplex.support =
      convexHull ℝ (Set.range (M.position ∘ v)) := by
  let a := triangleCutParameter f (M.position (v 0)) (M.position (v 1))
  let b := triangleCutParameter f (M.position (v 0)) (M.position (v 2))
  let R := referenceSplitMesh a b
    (affineCutPoint.parameter_pos f _ _ h0 h1)
    (affineCutPoint.parameter_lt_one f _ _ h0 h1)
    (affineCutPoint.parameter_pos f _ _ h0 h2)
    (affineCutPoint.parameter_lt_one f _ _ h0 h2)
  let e := triangleAffineEquiv standardTrianglePosition (M.position ∘ v)
    standardTrianglePosition_affineIndependent hv
  rw [show M.strictMeshFor f v hv h0 h1 h2 =
      (R.mapAffineEquiv e).reindex ((↑) : M.RefinedVertex f → Plane)
        Subtype.val_injective (M.strictVerticesEmbedding f v hv h0 h1 h2) (by
          intro i
          calc
            ((M.strictVerticesEmbedding f v hv h0 h1 h2 i : M.RefinedVertex f) : Plane) =
                strictModelPosition (M.position ∘ v) f i :=
              M.strictVertices_val f v h0 h1 h2 i
            _ = e (referenceSplitPosition a b i) :=
              strictModelPosition_eq_affineReference f _ hv h0 h1 h2 i
            _ = (R.mapAffineEquiv e).position i := rfl) by rfl]
  erw [TriangleMesh.reindex_support, TriangleMesh.mapAffineEquiv_support,
    referenceSplitMesh_support]
  change e '' convexHull ℝ (Set.range standardTrianglePosition) =
    convexHull ℝ (Set.range (M.position ∘ v))
  exact triangleAffineEquiv_image_convexHull standardTrianglePosition (M.position ∘ v)
    standardTrianglePosition_affineIndependent hv

/-- The `strictNegativeMeshFor` declaration. -/
noncomputable def strictNegativeMeshFor (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : f (M.position (v 0)) < 0) (h1 : 0 < f (M.position (v 1)))
    (h2 : 0 < f (M.position (v 2))) : TriangleMesh :=
  let N := M.strictMeshFor (-f) v hv (by simpa) (by simpa) (by simpa)
  N.reindex ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
    (M.refinedVertexNegEquiv f).toEmbedding (fun _ => rfl)

theorem strictNegativeMeshFor_support (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : f (M.position (v 0)) < 0) (h1 : 0 < f (M.position (v 1)))
    (h2 : 0 < f (M.position (v 2))) :
    (M.strictNegativeMeshFor f v hv h0 h1 h2).toPlaneComplex.support =
      convexHull ℝ (Set.range (M.position ∘ v)) := by
  rw [show M.strictNegativeMeshFor f v hv h0 h1 h2 =
      (M.strictMeshFor (-f) v hv (by simpa) (by simpa) (by simpa)).reindex
        ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
        (M.refinedVertexNegEquiv f).toEmbedding (fun _ => rfl) by rfl]
  erw [TriangleMesh.reindex_support]
  exact M.strictMeshFor_support (-f) v hv (by simpa) (by simpa) (by simpa)

/-! The two-triangle model when vertex `2` lies on the cutting line. -/

/-- The `edgeModelPosition` declaration. -/
noncomputable def edgeModelPosition (p : Fin 3 → Plane) (f : Plane →ᵃ[ℝ] ℝ) : Fin 4 → Plane :=
  ![p 0, p 1, p 2, affineCutPoint f (p 0) (p 1)]

theorem edgeModelPosition_eq_affineReference (p : Fin 3 → Plane)
    (hp : AffineIndependent ℝ p) (_ : 0 < f (p 0)) (_ : f (p 1) < 0)
    (i : Fin 4) :
    edgeModelPosition p f i =
      triangleAffineEquiv standardTrianglePosition p standardTrianglePosition_affineIndependent hp
        (referenceEdgeSplitPosition (triangleCutParameter f (p 0) (p 1)) i) := by
  let e := triangleAffineEquiv standardTrianglePosition p
    standardTrianglePosition_affineIndependent hp
  fin_cases i
  · simp only [edgeModelPosition, referenceEdgeSplitPosition]
    exact (triangleAffineEquiv_apply standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp 0).symm
  · simp only [edgeModelPosition, referenceEdgeSplitPosition]
    exact (triangleAffineEquiv_apply standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp 1).symm
  · simp only [edgeModelPosition, referenceEdgeSplitPosition]
    exact (triangleAffineEquiv_apply standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp 2).symm
  · simp only [edgeModelPosition, referenceEdgeSplitPosition]
    change affineCutPoint f (p 0) (p 1) =
      e (planePoint (triangleCutParameter f (p 0) (p 1)) 0)
    rw [show planePoint (triangleCutParameter f (p 0) (p 1)) 0 =
        AffineMap.lineMap (standardTrianglePosition 0) (standardTrianglePosition 1)
          (triangleCutParameter f (p 0) (p 1)) by
      ext j; fin_cases j <;> simp [standardTrianglePosition, planePoint,
        AffineMap.lineMap_apply_module]]
    exact (triangleAffineEquiv_apply_lineMap standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp 0 1
        (triangleCutParameter f (p 0) (p 1))).symm

/-- The `edgeVertices` declaration. -/
noncomputable def edgeVertices (v : Fin 3 → M.Vertex)
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0) :
    Fin 4 → M.RefinedVertex f :=
  ![M.oldRefinedVertex f (v 0), M.oldRefinedVertex f (v 1), M.oldRefinedVertex f (v 2),
    M.cutRefinedVertex f (v 0) (v 1) (mul_neg_iff.mpr (Or.inl ⟨h0, h1⟩))]

theorem edgeVertices_val (v : Fin 3 → M.Vertex)
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0) (i : Fin 4) :
    (M.edgeVertices f v h0 h1 i : Plane) = edgeModelPosition (M.position ∘ v) f i := by
  fin_cases i <;> rfl

/-- The `edgeVerticesEmbedding` declaration. -/
noncomputable def edgeVerticesEmbedding (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0) :
    Fin 4 ↪ M.RefinedVertex f where
  toFun := M.edgeVertices f v h0 h1
  inj' := by
    intro i j hij
    have hpos := congrArg Subtype.val hij
    rw [M.edgeVertices_val f v h0 h1, M.edgeVertices_val f v h0 h1,
      edgeModelPosition_eq_affineReference f _ hv h0 h1,
      edgeModelPosition_eq_affineReference f _ hv h0 h1] at hpos
    apply referenceEdgeSplitPosition_injective
      (affineCutPoint.parameter_pos f _ _ h0 h1)
      (affineCutPoint.parameter_lt_one f _ _ h0 h1)
    exact (triangleAffineEquiv standardTrianglePosition (M.position ∘ v)
      standardTrianglePosition_affineIndependent hv).injective hpos

/-- The `edgeMeshFor` declaration. -/
noncomputable def edgeMeshFor (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0) : TriangleMesh :=
  let c := triangleCutParameter f (M.position (v 0)) (M.position (v 1))
  let R := referenceEdgeSplitMesh c
    (affineCutPoint.parameter_pos f _ _ h0 h1)
    (affineCutPoint.parameter_lt_one f _ _ h0 h1)
  let e := triangleAffineEquiv standardTrianglePosition (M.position ∘ v)
    standardTrianglePosition_affineIndependent hv
  (R.mapAffineEquiv e).reindex ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
    (M.edgeVerticesEmbedding f v hv h0 h1) (by
      intro i
      calc
        ((M.edgeVerticesEmbedding f v hv h0 h1 i : M.RefinedVertex f) : Plane) =
            edgeModelPosition (M.position ∘ v) f i := M.edgeVertices_val f v h0 h1 i
        _ = e (referenceEdgeSplitPosition c i) :=
          edgeModelPosition_eq_affineReference f _ hv h0 h1 i
        _ = (R.mapAffineEquiv e).position i := rfl)

theorem edgeMeshFor_support (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0) :
    (M.edgeMeshFor f v hv h0 h1).toPlaneComplex.support =
      convexHull ℝ (Set.range (M.position ∘ v)) := by
  let c := triangleCutParameter f (M.position (v 0)) (M.position (v 1))
  let R := referenceEdgeSplitMesh c
    (affineCutPoint.parameter_pos f _ _ h0 h1)
    (affineCutPoint.parameter_lt_one f _ _ h0 h1)
  let e := triangleAffineEquiv standardTrianglePosition (M.position ∘ v)
    standardTrianglePosition_affineIndependent hv
  rw [show M.edgeMeshFor f v hv h0 h1 =
      (R.mapAffineEquiv e).reindex ((↑) : M.RefinedVertex f → Plane)
        Subtype.val_injective (M.edgeVerticesEmbedding f v hv h0 h1) (by
          intro i
          calc
            ((M.edgeVerticesEmbedding f v hv h0 h1 i : M.RefinedVertex f) : Plane) =
                edgeModelPosition (M.position ∘ v) f i := M.edgeVertices_val f v h0 h1 i
            _ = e (referenceEdgeSplitPosition c i) :=
              edgeModelPosition_eq_affineReference f _ hv h0 h1 i
            _ = (R.mapAffineEquiv e).position i := rfl) by rfl]
  erw [TriangleMesh.reindex_support, TriangleMesh.mapAffineEquiv_support,
    referenceEdgeSplitMesh_support]
  change e '' convexHull ℝ (Set.range standardTrianglePosition) =
    convexHull ℝ (Set.range (M.position ∘ v))
  exact triangleAffineEquiv_image_convexHull standardTrianglePosition (M.position ∘ v)
    standardTrianglePosition_affineIndependent hv

/-- The `edgeNegativeMeshFor` declaration. -/
noncomputable def edgeNegativeMeshFor (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : f (M.position (v 0)) < 0) (h1 : 0 < f (M.position (v 1))) : TriangleMesh :=
  let N := M.edgeMeshFor (-f) v hv (by simpa) (by simpa)
  N.reindex ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
    (M.refinedVertexNegEquiv f).toEmbedding (fun _ => rfl)

theorem edgeNegativeMeshFor_support (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : f (M.position (v 0)) < 0) (h1 : 0 < f (M.position (v 1))) :
    (M.edgeNegativeMeshFor f v hv h0 h1).toPlaneComplex.support =
      convexHull ℝ (Set.range (M.position ∘ v)) := by
  rw [show M.edgeNegativeMeshFor f v hv h0 h1 =
      (M.edgeMeshFor (-f) v hv (by simpa) (by simpa)).reindex
        ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
        (M.refinedVertexNegEquiv f).toEmbedding (fun _ => rfl) by rfl]
  erw [TriangleMesh.reindex_support]
  exact M.edgeMeshFor_support (-f) v hv (by simpa) (by simpa)

/-! ## Choosing the local model from the signs -/

theorem orderedVertex_perm_affineIndependent (t : M.Triangle) (σ : Equiv.Perm (Fin 3)) :
    AffineIndependent ℝ (M.position ∘ M.orderedVertex t ∘ σ) := by
  exact (M.orderedVertex_affineIndependent t).comp_embedding σ.toEmbedding

theorem range_orderedVertex_perm (t : M.Triangle) (σ : Equiv.Perm (Fin 3)) :
    Set.range (M.position ∘ M.orderedVertex t ∘ σ) =
      M.position '' (t.1 : Set M.Vertex) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨M.orderedVertex t (σ i), ?_, rfl⟩
    have hmem : M.orderedVertex t (σ i) ∈ Set.range (M.orderedVertex t) :=
      Set.mem_range_self (σ i)
    rw [M.range_orderedVertex t] at hmem
    exact hmem
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ Set.range (M.orderedVertex t) := by
      rw [M.range_orderedVertex t]
      exact hv
    obtain ⟨j, rfl⟩ := hv'
    exact ⟨σ.symm j, by simp⟩

/-- A vertex ordering with one positive value followed by two negative values. -/
structure PositiveStrictOrdering (t : M.Triangle) where
  /-- The `perm` declaration. -/
  perm : Equiv.Perm (Fin 3)
  positive : 0 < f (M.position (M.orderedVertex t (perm 0)))
  negative_one : f (M.position (M.orderedVertex t (perm 1))) < 0
  negative_two : f (M.position (M.orderedVertex t (perm 2))) < 0

/-- A vertex ordering with one negative value followed by two positive values. -/
structure NegativeStrictOrdering (t : M.Triangle) where
  /-- The `perm` declaration. -/
  perm : Equiv.Perm (Fin 3)
  negative : f (M.position (M.orderedVertex t (perm 0))) < 0
  positive_one : 0 < f (M.position (M.orderedVertex t (perm 1)))
  positive_two : 0 < f (M.position (M.orderedVertex t (perm 2)))

/-- A vertex ordering with one positive, one negative, and one zero value. -/
structure PositiveEdgeOrdering (t : M.Triangle) where
  /-- The `perm` declaration. -/
  perm : Equiv.Perm (Fin 3)
  positive : 0 < f (M.position (M.orderedVertex t (perm 0)))
  negative : f (M.position (M.orderedVertex t (perm 1))) < 0
  zero : f (M.position (M.orderedVertex t (perm 2))) = 0

/-- A vertex ordering with one negative, one positive, and one zero value. -/
structure NegativeEdgeOrdering (t : M.Triangle) where
  /-- The `perm` declaration. -/
  perm : Equiv.Perm (Fin 3)
  negative : f (M.position (M.orderedVertex t (perm 0))) < 0
  positive : 0 < f (M.position (M.orderedVertex t (perm 1)))
  zero : f (M.position (M.orderedVertex t (perm 2))) = 0

/-- The `oldVerticesEmbedding` declaration. -/
noncomputable def oldVerticesEmbedding (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v)) : Fin 3 ↪ M.RefinedVertex f where
  toFun i := M.oldRefinedVertex f (v i)
  inj' := by
    intro i j hij
    apply hv.injective
    exact congrArg Subtype.val hij

/-- The `unchangedMeshFor` declaration. -/
noncomputable def unchangedMeshFor (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v)) : TriangleMesh :=
  (TriangleMesh.single (M.position ∘ v) hv).reindex
    ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
      (M.oldVerticesEmbedding f v hv) (fun _ => rfl)

theorem unchangedMeshFor_support (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v)) :
    (M.unchangedMeshFor f v hv).toPlaneComplex.support =
      convexHull ℝ (Set.range (M.position ∘ v)) := by
  rw [show M.unchangedMeshFor f v hv =
      (TriangleMesh.single (M.position ∘ v) hv).reindex
        ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
          (M.oldVerticesEmbedding f v hv) (fun _ => rfl) by rfl]
  erw [TriangleMesh.reindex_support, TriangleMesh.single_support]

/-- The canonical local refinement mesh for one old triangle. -/
noncomputable def localRefinementMesh (t : M.Triangle) : TriangleMesh := by
  classical
  exact if hp : Nonempty (M.PositiveStrictOrdering f t) then
    let o := Classical.choice hp
    M.strictMeshFor f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm)
      o.positive o.negative_one o.negative_two
  else if hn : Nonempty (M.NegativeStrictOrdering f t) then
    let o := Classical.choice hn
    M.strictNegativeMeshFor f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm)
      o.negative o.positive_one o.positive_two
  else if hep : Nonempty (M.PositiveEdgeOrdering f t) then
    let o := Classical.choice hep
    M.edgeMeshFor f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm) o.positive o.negative
  else if hen : Nonempty (M.NegativeEdgeOrdering f t) then
    let o := Classical.choice hen
    M.edgeNegativeMeshFor f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm) o.negative o.positive
  else
    M.unchangedMeshFor f (M.orderedVertex t) (M.orderedVertex_affineIndependent t)

theorem localRefinementMesh_support (t : M.Triangle) :
    (M.localRefinementMesh f t).toPlaneComplex.support =
      convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) := by
  classical
  unfold localRefinementMesh
  split_ifs with hp hn hep hen
  · let o := Classical.choice hp
    rw [M.strictMeshFor_support]
    exact congrArg (convexHull ℝ) (M.range_orderedVertex_perm t o.perm)
  · let o := Classical.choice hn
    rw [M.strictNegativeMeshFor_support]
    exact congrArg (convexHull ℝ) (M.range_orderedVertex_perm t o.perm)
  · let o := Classical.choice hep
    rw [M.edgeMeshFor_support]
    exact congrArg (convexHull ℝ) (M.range_orderedVertex_perm t o.perm)
  · let o := Classical.choice hen
    rw [M.edgeNegativeMeshFor_support]
    exact congrArg (convexHull ℝ) (M.range_orderedVertex_perm t o.perm)
  · rw [M.unchangedMeshFor_support]
    congr 1
    rw [Set.range_comp, M.range_orderedVertex t]

/-- Every maximal triangle lies wholly on one closed side of the cutting line. -/
def IsMonochromatic (N : TriangleMesh) (f : Plane →ᵃ[ℝ] ℝ) : Prop :=
  ∀ s ∈ N.triangles,
    (∀ v ∈ s, 0 ≤ f (N.position v)) ∨ (∀ v ∈ s, f (N.position v) ≤ 0)

theorem IsMonochromatic.of_neg {N : TriangleMesh}
    (hN : N.IsMonochromatic (-f)) : N.IsMonochromatic f := by
  intro s hs
  rcases hN s hs with h | h
  · right
    intro v hv
    simpa using h v hv
  · left
    intro v hv
    simpa using h v hv

theorem IsMonochromatic.reindex {N : TriangleMesh} {V' : Type} [Fintype V']
    [DecidableEq V'] (position' : V' → Plane) (hposition_injective : Function.Injective position')
    (e : N.Vertex ↪ V') (hposition : ∀ v, position' (e v) = N.position v)
    (g : Plane →ᵃ[ℝ] ℝ) (hN : N.IsMonochromatic g) :
    (N.reindex position' hposition_injective e hposition).IsMonochromatic g := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
  rcases hN t ht with h | h
  · left
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
    change 0 ≤ g (position' (e w))
    rw [hposition]
    exact h w hw
  · right
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
    change g (position' (e w)) ≤ 0
    rw [hposition]
    exact h w hw

theorem strictVertices_f (v : Fin 3 → M.Vertex)
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) (i : Fin 5) :
    f (M.strictVertices f v h0 h1 h2 i : Plane) =
      ![f (M.position (v 0)), f (M.position (v 1)), f (M.position (v 2)), 0, 0] i := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact M.pairCutPosition_apply_eq_zero f (v 0) (v 1)
      (mul_neg_iff.mpr (Or.inl ⟨h0, h1⟩))
  · exact M.pairCutPosition_apply_eq_zero f (v 0) (v 2)
      (mul_neg_iff.mpr (Or.inl ⟨h0, h2⟩))

theorem edgeVertices_f (v : Fin 3 → M.Vertex)
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (hzero : f (M.position (v 2)) = 0) (i : Fin 4) :
    f (M.edgeVertices f v h0 h1 i : Plane) =
      ![f (M.position (v 0)), f (M.position (v 1)), 0, 0] i := by
  fin_cases i
  · rfl
  · rfl
  · exact hzero
  · exact M.pairCutPosition_apply_eq_zero f (v 0) (v 1)
      (mul_neg_iff.mpr (Or.inl ⟨h0, h1⟩))

/-- Monochromaticity stated directly for triangles in the shared refined vertex pool. -/
def RefinedTrianglesMonochromatic (T : Finset (Finset (M.RefinedVertex f))) : Prop :=
  ∀ s ∈ T,
    (∀ x ∈ s, 0 ≤ f (x : Plane)) ∨ (∀ x ∈ s, f (x : Plane) ≤ 0)

theorem strictTriangles_monochromatic (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) :
    M.RefinedTrianglesMonochromatic f
      (referenceSplitTriangles.image fun t =>
        t.map (M.strictVerticesEmbedding f v hv h0 h1 h2)) := by
  intro s hs
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
  have hr' : r = {0, 3, 4} ∨ r = {1, 2, 3} ∨ r = {2, 3, 4} := by
    simpa only [referenceSplitTriangles, Finset.mem_insert, Finset.mem_singleton] using hr
  rcases hr' with rfl | rfl | rfl
  · left
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact h0.le
    · change 0 ≤ f (M.strictVertices f v h0 h1 h2 3 : Plane)
      rw [M.strictVertices_f f v h0 h1 h2]
      change 0 ≤ (0 : ℝ)
      norm_num
    · change 0 ≤ f (M.strictVertices f v h0 h1 h2 4 : Plane)
      rw [M.strictVertices_f f v h0 h1 h2]
      change 0 ≤ (0 : ℝ)
      norm_num
  · right
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact h1.le
    · exact h2.le
    · change f (M.strictVertices f v h0 h1 h2 3 : Plane) ≤ 0
      rw [M.strictVertices_f f v h0 h1 h2]
      change (0 : ℝ) ≤ 0
      norm_num
  · right
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact h2.le
    · change f (M.strictVertices f v h0 h1 h2 3 : Plane) ≤ 0
      rw [M.strictVertices_f f v h0 h1 h2]
      change (0 : ℝ) ≤ 0
      norm_num
    · change f (M.strictVertices f v h0 h1 h2 4 : Plane) ≤ 0
      rw [M.strictVertices_f f v h0 h1 h2]
      change (0 : ℝ) ≤ 0
      norm_num

theorem edgeTriangles_monochromatic (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (hzero : f (M.position (v 2)) = 0) :
    M.RefinedTrianglesMonochromatic f
      (referenceEdgeSplitTriangles.image fun t =>
        t.map (M.edgeVerticesEmbedding f v hv h0 h1)) := by
  intro s hs
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
  have hr' : r = {0, 2, 3} ∨ r = {1, 2, 3} := by
    simpa only [referenceEdgeSplitTriangles, Finset.mem_insert,
      Finset.mem_singleton, or_false] using hr
  rcases hr' with rfl | rfl
  · left
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact h0.le
    · change 0 ≤ f (M.edgeVertices f v h0 h1 2 : Plane)
      rw [M.edgeVertices_f f v h0 h1 hzero]
      change 0 ≤ (0 : ℝ)
      norm_num
    · change 0 ≤ f (M.edgeVertices f v h0 h1 3 : Plane)
      rw [M.edgeVertices_f f v h0 h1 hzero]
      change 0 ≤ (0 : ℝ)
      norm_num
  · right
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact h1.le
    · change f (M.edgeVertices f v h0 h1 2 : Plane) ≤ 0
      rw [M.edgeVertices_f f v h0 h1 hzero]
      change (0 : ℝ) ≤ 0
      norm_num
    · change f (M.edgeVertices f v h0 h1 3 : Plane) ≤ 0
      rw [M.edgeVertices_f f v h0 h1 hzero]
      change (0 : ℝ) ≤ 0
      norm_num

/-- The abstract three-triangle combinatorial pattern of a strict cut. -/
def strictPatternTriangles {V : Type*} [DecidableEq V] (z : Fin 5 → V) :
    Finset (Finset V) :=
  {{z 0, z 3, z 4}, {z 1, z 2, z 3}, {z 2, z 3, z 4}}

/-- The abstract two-triangle combinatorial pattern of a cut through vertex `2`. -/
def edgePatternTriangles {V : Type*} [DecidableEq V] (z : Fin 4 → V) :
    Finset (Finset V) :=
  {{z 0, z 2, z 3}, {z 1, z 2, z 3}}

theorem exists_index_of_mem_strictPattern {V : Type*} [DecidableEq V]
    (z : Fin 5 → V) {s : Finset V} (hs : s ∈ strictPatternTriangles z)
    {x : V} (hx : x ∈ s) : ∃ i, x = z i := by
  simp only [strictPatternTriangles, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

theorem exists_index_of_mem_edgePattern {V : Type*} [DecidableEq V]
    (z : Fin 4 → V) {s : Finset V} (hs : s ∈ edgePatternTriangles z)
    {x : V} (hx : x ∈ s) : ∃ i, x = z i := by
  simp only [edgePatternTriangles, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

theorem strictMeshFor_triangles (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) :
    (M.strictMeshFor f v hv h0 h1 h2).triangles =
      strictPatternTriangles (M.strictVertices f v h0 h1 h2) := by
  ext s
  simp [strictMeshFor, strictPatternTriangles, referenceSplitMesh,
    referenceSplitTriangles, TriangleMesh.reindex, TriangleMesh.mapAffineEquiv,
    strictVerticesEmbedding]
  rfl

theorem edgeMeshFor_triangles (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0) :
    (M.edgeMeshFor f v hv h0 h1).triangles =
      edgePatternTriangles (M.edgeVertices f v h0 h1) := by
  simp [edgeMeshFor, edgePatternTriangles, referenceEdgeSplitMesh,
    referenceEdgeSplitTriangles, TriangleMesh.reindex, TriangleMesh.mapAffineEquiv,
    edgeVerticesEmbedding]
  rfl

theorem strictNegativeMeshFor_monochromatic (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : f (M.position (v 0)) < 0) (h1 : 0 < f (M.position (v 1)))
    (h2 : 0 < f (M.position (v 2))) :
    M.RefinedTrianglesMonochromatic f
      (M.strictNegativeMeshFor f v hv h0 h1 h2).triangles := by
  intro s hs
  unfold strictNegativeMeshFor at hs
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
  have hm := M.strictTriangles_monochromatic (-f) v hv (by simpa) (by simpa) (by simpa) r
  have hr' : r ∈ referenceSplitTriangles.image (fun t ↦
      t.map (M.strictVerticesEmbedding (-f) v hv (by simpa) (by simpa) (by simpa))) := hr
  rcases hm hr' with hm | hm
  · right
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    change f ((M.strictMeshFor (-f) v hv (by simpa) (by simpa) (by simpa)).position y) ≤ 0
    simpa only [strictMeshFor, TriangleMesh.reindex, AffineMap.coe_neg, Pi.neg_apply,
      neg_nonneg] using hm y hy
  · left
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    change 0 ≤ f ((M.strictMeshFor (-f) v hv (by simpa) (by simpa) (by simpa)).position y)
    simpa only [strictMeshFor, TriangleMesh.reindex, AffineMap.coe_neg, Pi.neg_apply,
      neg_nonpos] using hm y hy

theorem edgeNegativeMeshFor_monochromatic (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : f (M.position (v 0)) < 0) (h1 : 0 < f (M.position (v 1)))
    (h2 : f (M.position (v 2)) = 0) :
    M.RefinedTrianglesMonochromatic f
      (M.edgeNegativeMeshFor f v hv h0 h1).triangles := by
  intro s hs
  unfold edgeNegativeMeshFor at hs
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
  have hm := M.edgeTriangles_monochromatic (-f) v hv (by simpa) (by simpa) (by simpa) r
  have hr' : r ∈ referenceEdgeSplitTriangles.image (fun t ↦
      t.map (M.edgeVerticesEmbedding (-f) v hv (by simpa) (by simpa))) := hr
  rcases hm hr' with hm | hm
  · right
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    change f ((M.edgeMeshFor (-f) v hv (by simpa) (by simpa)).position y) ≤ 0
    simpa only [edgeMeshFor, TriangleMesh.reindex, AffineMap.coe_neg, Pi.neg_apply,
      neg_nonneg] using hm y hy
  · left
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    change 0 ≤ f ((M.edgeMeshFor (-f) v hv (by simpa) (by simpa)).position y)
    simpa only [edgeMeshFor, TriangleMesh.reindex, AffineMap.coe_neg, Pi.neg_apply,
      neg_nonpos] using hm y hy

theorem strictPattern_monochromatic_positive (z : Fin 5 → M.RefinedVertex f)
    (h0 : 0 ≤ f (z 0 : Plane)) (h1 : f (z 1 : Plane) ≤ 0)
    (h2 : f (z 2 : Plane) ≤ 0) (h3 : f (z 3 : Plane) = 0)
    (h4 : f (z 4 : Plane) = 0) :
    M.RefinedTrianglesMonochromatic f (strictPatternTriangles z) := by
  intro s hs
  simp only [strictPatternTriangles, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl
  · left
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> linarith
  · right
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> linarith
  · right
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> linarith

theorem strictPattern_monochromatic_negative (z : Fin 5 → M.RefinedVertex f)
    (h0 : f (z 0 : Plane) ≤ 0) (h1 : 0 ≤ f (z 1 : Plane))
    (h2 : 0 ≤ f (z 2 : Plane)) (h3 : f (z 3 : Plane) = 0)
    (h4 : f (z 4 : Plane) = 0) :
    M.RefinedTrianglesMonochromatic f (strictPatternTriangles z) := by
  intro s hs
  simp only [strictPatternTriangles, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl
  · right
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> linarith
  · left
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> linarith
  · left
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> linarith

theorem edgePattern_monochromatic_positive (z : Fin 4 → M.RefinedVertex f)
    (h0 : 0 ≤ f (z 0 : Plane)) (h1 : f (z 1 : Plane) ≤ 0)
    (h2 : f (z 2 : Plane) = 0) (h3 : f (z 3 : Plane) = 0) :
    M.RefinedTrianglesMonochromatic f (edgePatternTriangles z) := by
  intro s hs
  simp only [edgePatternTriangles, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  · left
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> linarith
  · right
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> linarith

theorem edgePattern_monochromatic_negative (z : Fin 4 → M.RefinedVertex f)
    (h0 : f (z 0 : Plane) ≤ 0) (h1 : 0 ≤ f (z 1 : Plane))
    (h2 : f (z 2 : Plane) = 0) (h3 : f (z 3 : Plane) = 0) :
    M.RefinedTrianglesMonochromatic f (edgePatternTriangles z) := by
  intro s hs
  simp only [edgePatternTriangles, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  · right
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> linarith
  · left
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> linarith

private theorem same_closed_side_of_pairwise_products {a b c : ℝ}
    (hab : 0 ≤ a * b) (hac : 0 ≤ a * c) (hbc : 0 ≤ b * c) :
    (0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0) := by
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · by_cases hc : 0 ≤ c
      · exact Or.inl ⟨ha, hb, hc⟩
      · have hc' : c < 0 := lt_of_not_ge hc
        have ha0 : a = 0 := by nlinarith [hac]
        have hb0 : b = 0 := by nlinarith [hbc]
        exact Or.inr ⟨ha0.le, hb0.le, hc'.le⟩
    · have hb' : b < 0 := lt_of_not_ge hb
      have ha0 : a = 0 := by nlinarith [hab]
      have hc : c ≤ 0 := by
        by_contra hc
        have hc' : 0 < c := lt_of_not_ge hc
        nlinarith [hbc]
      exact Or.inr ⟨ha0.le, hb'.le, hc⟩
  · have ha' : a < 0 := lt_of_not_ge ha
    have hb : b ≤ 0 := by
      by_contra hb
      have hb' : 0 < b := lt_of_not_ge hb
      nlinarith [hab]
    have hc : c ≤ 0 := by
      by_contra hc
      have hc' : 0 < c := lt_of_not_ge hc
      nlinarith [hac]
    exact Or.inr ⟨ha'.le, hb, hc⟩

private theorem signs_of_two_crossings {a b c : ℝ}
    (hab : a * b < 0) (hac : a * c < 0) :
    (0 < a ∧ b < 0 ∧ c < 0) ∨ (a < 0 ∧ 0 < b ∧ 0 < c) := by
  rcases mul_neg_iff.mp hab with hab | hab
  · rcases mul_neg_iff.mp hac with hac | hac
    · exact Or.inl ⟨hab.1, hab.2, hac.2⟩
    · linarith
  · rcases mul_neg_iff.mp hac with hac | hac
    · linarith
    · exact Or.inr ⟨hab.1, hab.2, hac.2⟩

private theorem third_eq_zero_of_one_crossing {a b c : ℝ}
    (hab : a * b < 0) (hac : ¬ a * c < 0) (hbc : ¬ b * c < 0) : c = 0 := by
  rcases mul_neg_iff.mp hab with hab | hab
  · by_contra hc
    rcases lt_or_gt_of_ne hc with hc | hc
    · exact hac (mul_neg_of_pos_of_neg hab.1 hc)
    · exact hbc (mul_neg_of_neg_of_pos hab.2 hc)
  · by_contra hc
    rcases lt_or_gt_of_ne hc with hc | hc
    · exact hbc (mul_neg_of_pos_of_neg hab.2 hc)
    · exact hac (mul_neg_of_neg_of_pos hab.1 hc)

/-- The old vertex numbered `i` in a triangle, regarded as a refined vertex. -/
noncomputable def localOldVertex (t : M.Triangle) (i : Fin 3) : M.RefinedVertex f :=
  M.oldRefinedVertex f (M.orderedVertex t i)

/-- The cut vertex on the pair of locally numbered vertices `i,j`. -/
noncomputable def localCutVertex (t : M.Triangle) (i j : Fin 3)
    (hij : f (M.position (M.orderedVertex t i)) *
      f (M.position (M.orderedVertex t j)) < 0) : M.RefinedVertex f :=
  M.cutRefinedVertex f (M.orderedVertex t i) (M.orderedVertex t j) hij

@[simp] theorem localOldVertex_val (t : M.Triangle) (i : Fin 3) :
    (M.localOldVertex f t i : Plane) = M.position (M.orderedVertex t i) := rfl

theorem localCutVertex_apply_eq_zero (t : M.Triangle) (i j : Fin 3)
    (hij : f (M.position (M.orderedVertex t i)) *
      f (M.position (M.orderedVertex t j)) < 0) :
    f (M.localCutVertex f t i j hij : Plane) = 0 :=
  M.pairCutPosition_apply_eq_zero f _ _ hij

private theorem pairwise_nonnegative_of_no_orderings (t : M.Triangle)
    (hp : ¬ Nonempty (M.PositiveStrictOrdering f t))
    (hn : ¬ Nonempty (M.NegativeStrictOrdering f t))
    (hep : ¬ Nonempty (M.PositiveEdgeOrdering f t))
    (hen : ¬ Nonempty (M.NegativeEdgeOrdering f t)) :
    0 ≤ f (M.position (M.orderedVertex t 0)) * f (M.position (M.orderedVertex t 1)) ∧
    0 ≤ f (M.position (M.orderedVertex t 0)) * f (M.position (M.orderedVertex t 2)) ∧
    0 ≤ f (M.position (M.orderedVertex t 1)) * f (M.position (M.orderedVertex t 2)) := by
  let a := f (M.position (M.orderedVertex t 0))
  let b := f (M.position (M.orderedVertex t 1))
  let c := f (M.position (M.orderedVertex t 2))
  have h01 : ¬ a * b < 0 := by
    intro hab
    rcases mul_neg_iff.mp hab with hab | hab
    · rcases lt_trichotomy c 0 with hc | hc | hc
      · apply hp
        exact ⟨⟨Equiv.refl _, hab.1, hab.2, hc⟩⟩
      · apply hep
        exact ⟨⟨Equiv.refl _, hab.1, hab.2, hc⟩⟩
      · apply hn
        refine ⟨⟨Equiv.swap 0 1, ?_, ?_, ?_⟩⟩
        · simpa [b, Equiv.swap_apply_def] using hab.2
        · simpa [a, Equiv.swap_apply_def] using hab.1
        · simpa [c, Equiv.swap_apply_def] using hc
    · rcases lt_trichotomy c 0 with hc | hc | hc
      · apply hp
        refine ⟨⟨Equiv.swap 0 1, ?_, ?_, ?_⟩⟩
        · simpa [b, Equiv.swap_apply_def] using hab.2
        · simpa [a, Equiv.swap_apply_def] using hab.1
        · simpa [c, Equiv.swap_apply_def] using hc
      · apply hen
        exact ⟨⟨Equiv.refl _, hab.1, hab.2, hc⟩⟩
      · apply hn
        exact ⟨⟨Equiv.refl _, hab.1, hab.2, hc⟩⟩
  have h02 : ¬ a * c < 0 := by
    intro hac
    rcases mul_neg_iff.mp hac with hac | hac
    · rcases lt_trichotomy b 0 with hb | hb | hb
      · apply hp
        exact ⟨⟨Equiv.refl _, hac.1, hb, hac.2⟩⟩
      · apply hep
        refine ⟨⟨Equiv.swap 1 2, ?_, ?_, ?_⟩⟩
        · simpa [a, Equiv.swap_apply_def] using hac.1
        · simpa [c, Equiv.swap_apply_def] using hac.2
        · simpa [b, Equiv.swap_apply_def] using hb
      · apply hn
        refine ⟨⟨Equiv.swap 0 2, ?_, ?_, ?_⟩⟩
        · simpa [c, Equiv.swap_apply_def] using hac.2
        · simpa [b, Equiv.swap_apply_def] using hb
        · simpa [a, Equiv.swap_apply_def] using hac.1
    · rcases lt_trichotomy b 0 with hb | hb | hb
      · apply hp
        refine ⟨⟨Equiv.swap 0 2, ?_, ?_, ?_⟩⟩
        · simpa [c, Equiv.swap_apply_def] using hac.2
        · simpa [b, Equiv.swap_apply_def] using hb
        · simpa [a, Equiv.swap_apply_def] using hac.1
      · apply hen
        refine ⟨⟨Equiv.swap 1 2, ?_, ?_, ?_⟩⟩
        · simpa [a, Equiv.swap_apply_def] using hac.1
        · simpa [c, Equiv.swap_apply_def] using hac.2
        · simpa [b, Equiv.swap_apply_def] using hb
      · apply hn
        exact ⟨⟨Equiv.refl _, hac.1, hb, hac.2⟩⟩
  have h12 : ¬ b * c < 0 := by
    intro hbc
    rcases mul_neg_iff.mp hbc with hbc | hbc
    · rcases lt_trichotomy a 0 with ha | ha | ha
      · apply hp
        refine ⟨⟨Equiv.swap 0 1, ?_, ?_, ?_⟩⟩
        · simpa [b, Equiv.swap_apply_def] using hbc.1
        · simpa [a, Equiv.swap_apply_def] using ha
        · simpa [c, Equiv.swap_apply_def] using hbc.2
      · apply hen
        refine ⟨⟨Equiv.swap 0 2, ?_, ?_, ?_⟩⟩
        · simpa [c, Equiv.swap_apply_def] using hbc.2
        · simpa [b, Equiv.swap_apply_def] using hbc.1
        · simpa [a, Equiv.swap_apply_def] using ha
      · apply hn
        refine ⟨⟨Equiv.swap 0 2, ?_, ?_, ?_⟩⟩
        · simpa [c, Equiv.swap_apply_def] using hbc.2
        · simpa [b, Equiv.swap_apply_def] using hbc.1
        · simpa [a, Equiv.swap_apply_def] using ha
    · rcases lt_trichotomy a 0 with ha | ha | ha
      · apply hp
        refine ⟨⟨Equiv.swap 0 2, ?_, ?_, ?_⟩⟩
        · simpa [c, Equiv.swap_apply_def] using hbc.2
        · simpa [b, Equiv.swap_apply_def] using hbc.1
        · simpa [a, Equiv.swap_apply_def] using ha
      · apply hep
        refine ⟨⟨Equiv.swap 0 2, ?_, ?_, ?_⟩⟩
        · simpa [c, Equiv.swap_apply_def] using hbc.2
        · simpa [b, Equiv.swap_apply_def] using hbc.1
        · simpa [a, Equiv.swap_apply_def] using ha
      · apply hn
        refine ⟨⟨Equiv.swap 0 1, ?_, ?_, ?_⟩⟩
        · simpa [b, Equiv.swap_apply_def] using hbc.1
        · simpa [a, Equiv.swap_apply_def] using ha
        · simpa [c, Equiv.swap_apply_def] using hbc.2
  exact ⟨not_lt.mp h01, not_lt.mp h02, not_lt.mp h12⟩

/-- Canonical local triangulation after cutting one old triangle by `f`.  There are three
triangles when one vertex is strictly separated from the other two, two triangles when the line
passes through one vertex and cuts the opposite edge, and the old triangle when the line already
meets it in a face. -/
noncomputable def localRefinementTriangles (t : M.Triangle) :
    Finset (Finset (M.RefinedVertex f)) := by
  let p : Fin 3 → Plane := M.position ∘ M.orderedVertex t
  let o : Fin 3 → M.RefinedVertex f := M.localOldVertex f t
  if h01 : f (p 0) * f (p 1) < 0 then
    let q01 := M.localCutVertex f t 0 1 h01
    if h02 : f (p 0) * f (p 2) < 0 then
      let q02 := M.localCutVertex f t 0 2 h02
      exact strictPatternTriangles ![o 0, o 1, o 2, q01, q02]
    else if h12 : f (p 1) * f (p 2) < 0 then
      let q12 := M.localCutVertex f t 1 2 h12
      exact strictPatternTriangles ![o 1, o 0, o 2, q01, q12]
    else
      exact edgePatternTriangles ![o 0, o 1, o 2, q01]
  else if h02 : f (p 0) * f (p 2) < 0 then
    let q02 := M.localCutVertex f t 0 2 h02
    if h12 : f (p 1) * f (p 2) < 0 then
      let q12 := M.localCutVertex f t 1 2 h12
      exact strictPatternTriangles ![o 2, o 0, o 1, q02, q12]
    else
      exact edgePatternTriangles ![o 0, o 2, o 1, q02]
  else if h12 : f (p 1) * f (p 2) < 0 then
    let q12 := M.localCutVertex f t 1 2 h12
    exact edgePatternTriangles ![o 1, o 2, o 0, q12]
  else
    exact {{o 0, o 1, o 2}}

/-- Cutting one old triangle by an affine line produces triangles contained in the two closed
half-planes. -/
theorem localRefinementTriangles_monochromatic (t : M.Triangle) :
    M.RefinedTrianglesMonochromatic f (M.localRefinementTriangles f t) := by
  classical
  unfold localRefinementTriangles
  dsimp only
  split_ifs with h01 h02 h12 h02' h12' h12''
  · rcases signs_of_two_crossings h01 h02 with h | h
    · apply M.strictPattern_monochromatic_positive
      · simpa using h.1.le
      · simpa using h.2.1.le
      · simpa using h.2.2.le
      · simpa using M.localCutVertex_apply_eq_zero f t 0 1 h01
      · simpa using M.localCutVertex_apply_eq_zero f t 0 2 h02
    · apply M.strictPattern_monochromatic_negative
      · simpa using h.1.le
      · simpa using h.2.1.le
      · simpa using h.2.2.le
      · simpa using M.localCutVertex_apply_eq_zero f t 0 1 h01
      · simpa using M.localCutVertex_apply_eq_zero f t 0 2 h02
  · have h10 : f (M.position (M.orderedVertex t 1)) *
        f (M.position (M.orderedVertex t 0)) < 0 := by simpa [mul_comm] using h01
    rcases signs_of_two_crossings h10 h12 with h | h
    · apply M.strictPattern_monochromatic_positive
      · simpa using h.1.le
      · simpa using h.2.1.le
      · simpa using h.2.2.le
      · simpa using M.localCutVertex_apply_eq_zero f t 0 1 h01
      · simpa using M.localCutVertex_apply_eq_zero f t 1 2 h12
    · apply M.strictPattern_monochromatic_negative
      · simpa using h.1.le
      · simpa using h.2.1.le
      · simpa using h.2.2.le
      · simpa using M.localCutVertex_apply_eq_zero f t 0 1 h01
      · simpa using M.localCutVertex_apply_eq_zero f t 1 2 h12
  · have hz := third_eq_zero_of_one_crossing h01 h02 h12
    rcases mul_neg_iff.mp h01 with h | h
    · apply M.edgePattern_monochromatic_positive
      · simpa using h.1.le
      · simpa using h.2.le
      · simpa using hz
      · simpa using M.localCutVertex_apply_eq_zero f t 0 1 h01
    · apply M.edgePattern_monochromatic_negative
      · simpa using h.1.le
      · simpa using h.2.le
      · simpa using hz
      · simpa using M.localCutVertex_apply_eq_zero f t 0 1 h01
  · have h20 : f (M.position (M.orderedVertex t 2)) *
        f (M.position (M.orderedVertex t 0)) < 0 := by simpa [mul_comm] using h02'
    have h21 : f (M.position (M.orderedVertex t 2)) *
        f (M.position (M.orderedVertex t 1)) < 0 := by simpa [mul_comm] using h12'
    rcases signs_of_two_crossings h20 h21 with h | h
    · apply M.strictPattern_monochromatic_positive
      · simpa using h.1.le
      · simpa using h.2.1.le
      · simpa using h.2.2.le
      · simpa using M.localCutVertex_apply_eq_zero f t 0 2 h02'
      · simpa using M.localCutVertex_apply_eq_zero f t 1 2 h12'
    · apply M.strictPattern_monochromatic_negative
      · simpa using h.1.le
      · simpa using h.2.1.le
      · simpa using h.2.2.le
      · simpa using M.localCutVertex_apply_eq_zero f t 0 2 h02'
      · simpa using M.localCutVertex_apply_eq_zero f t 1 2 h12'
  · have h21 : ¬ f (M.position (M.orderedVertex t 2)) *
        f (M.position (M.orderedVertex t 1)) < 0 := by simpa [mul_comm] using h12'
    have hz := third_eq_zero_of_one_crossing h02' h01 h21
    rcases mul_neg_iff.mp h02' with h | h
    · apply M.edgePattern_monochromatic_positive
      · simpa using h.1.le
      · simpa using h.2.le
      · simpa using hz
      · simpa using M.localCutVertex_apply_eq_zero f t 0 2 h02'
    · apply M.edgePattern_monochromatic_negative
      · simpa using h.1.le
      · simpa using h.2.le
      · simpa using hz
      · simpa using M.localCutVertex_apply_eq_zero f t 0 2 h02'
  · have h21 : f (M.position (M.orderedVertex t 2)) *
        f (M.position (M.orderedVertex t 1)) < 0 := by simpa [mul_comm] using h12''
    have h10 : ¬ f (M.position (M.orderedVertex t 1)) *
        f (M.position (M.orderedVertex t 0)) < 0 := by simpa [mul_comm] using h01
    have h20 : ¬ f (M.position (M.orderedVertex t 2)) *
        f (M.position (M.orderedVertex t 0)) < 0 := by simpa [mul_comm] using h02'
    have hz := third_eq_zero_of_one_crossing h12'' h10 h20
    rcases mul_neg_iff.mp h12'' with h | h
    · apply M.edgePattern_monochromatic_positive
      · simpa using h.1.le
      · simpa using h.2.le
      · simpa using hz
      · simpa using M.localCutVertex_apply_eq_zero f t 1 2 h12''
    · apply M.edgePattern_monochromatic_negative
      · simpa using h.1.le
      · simpa using h.2.le
      · simpa using hz
      · simpa using M.localCutVertex_apply_eq_zero f t 1 2 h12''
  · have hsign := same_closed_side_of_pairwise_products
        (not_lt.mp h01) (not_lt.mp h02') (not_lt.mp h12'')
    intro s hs
    simp only [Finset.mem_singleton] at hs
    subst s
    rcases hsign with h | h
    · left
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · simpa using h.1
      · simpa using h.2.1
      · simpa using h.2.2
    · right
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · simpa using h.1
      · simpa using h.2.1
      · simpa using h.2.2

/-- The maximal triangles selected by the certified local model, exposed on the fixed shared
vertex pool. -/
noncomputable def localMeshTriangles (t : M.Triangle) :
    Finset (Finset (M.RefinedVertex f)) := by
  classical
  exact if hp : Nonempty (M.PositiveStrictOrdering f t) then
    let o := Classical.choice hp
    (M.strictMeshFor f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm)
      o.positive o.negative_one o.negative_two).triangles
  else if hn : Nonempty (M.NegativeStrictOrdering f t) then
    let o := Classical.choice hn
    (M.strictNegativeMeshFor f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm)
      o.negative o.positive_one o.positive_two).triangles
  else if hep : Nonempty (M.PositiveEdgeOrdering f t) then
    let o := Classical.choice hep
    (M.edgeMeshFor f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm) o.positive o.negative).triangles
  else if hen : Nonempty (M.NegativeEdgeOrdering f t) then
    let o := Classical.choice hen
    (M.edgeNegativeMeshFor f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm) o.negative o.positive).triangles
  else
    (M.unchangedMeshFor f (M.orderedVertex t)
      (M.orderedVertex_affineIndependent t)).triangles

theorem card_of_mem_localMeshTriangles (t : M.Triangle)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t) : s.card = 3 := by
  classical
  unfold localMeshTriangles at hs
  by_cases hp : Nonempty (M.PositiveStrictOrdering f t)
  · erw [dite_eq_left hp] at hs
    exact (M.strictMeshFor f _ _ _ _ _).card_triangle s hs
  erw [dite_eq_right hp] at hs
  by_cases hn : Nonempty (M.NegativeStrictOrdering f t)
  · erw [dite_eq_left hn] at hs
    exact (M.strictNegativeMeshFor f _ _ _ _ _).card_triangle s hs
  erw [dite_eq_right hn] at hs
  by_cases hep : Nonempty (M.PositiveEdgeOrdering f t)
  · erw [dite_eq_left hep] at hs
    exact (M.edgeMeshFor f _ _ _ _).card_triangle s hs
  erw [dite_eq_right hep] at hs
  by_cases hen : Nonempty (M.NegativeEdgeOrdering f t)
  · erw [dite_eq_left hen] at hs
    exact (M.edgeNegativeMeshFor f _ _ _ _).card_triangle s hs
  erw [dite_eq_right hen] at hs
  exact (M.unchangedMeshFor f _ _).card_triangle s hs

theorem affineIndependent_of_mem_localMeshTriangles (t : M.Triangle)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t) :
    AffineIndependent ℝ fun v : s => (v.1 : Plane) := by
  classical
  unfold localMeshTriangles at hs
  by_cases hp : Nonempty (M.PositiveStrictOrdering f t)
  · erw [dite_eq_left hp] at hs
    exact (M.strictMeshFor f _ _ _ _ _).affineIndependent_triangle s hs
  erw [dite_eq_right hp] at hs
  by_cases hn : Nonempty (M.NegativeStrictOrdering f t)
  · erw [dite_eq_left hn] at hs
    exact (M.strictNegativeMeshFor f _ _ _ _ _).affineIndependent_triangle s hs
  erw [dite_eq_right hn] at hs
  by_cases hep : Nonempty (M.PositiveEdgeOrdering f t)
  · erw [dite_eq_left hep] at hs
    exact (M.edgeMeshFor f _ _ _ _).affineIndependent_triangle s hs
  erw [dite_eq_right hep] at hs
  by_cases hen : Nonempty (M.NegativeEdgeOrdering f t)
  · erw [dite_eq_left hen] at hs
    exact (M.edgeNegativeMeshFor f _ _ _ _).affineIndependent_triangle s hs
  erw [dite_eq_right hen] at hs
  exact (M.unchangedMeshFor f _ _).affineIndependent_triangle s hs

theorem localMeshTriangles_monochromatic (t : M.Triangle) :
    M.RefinedTrianglesMonochromatic f (M.localMeshTriangles f t) := by
  classical
  unfold localMeshTriangles
  by_cases hp : Nonempty (M.PositiveStrictOrdering f t)
  · erw [dite_eq_left hp]
    let o := Classical.choice hp
    rw [M.strictMeshFor_triangles]
    apply M.strictPattern_monochromatic_positive
    · simpa [o, strictVertices, Function.comp_apply] using o.positive.le
    · simpa [o, strictVertices, Function.comp_apply] using o.negative_one.le
    · simpa [o, strictVertices, Function.comp_apply] using o.negative_two.le
    · rw [M.strictVertices_f]
      simp
    · rw [M.strictVertices_f]
      simp
  erw [dite_eq_right hp]
  by_cases hn : Nonempty (M.NegativeStrictOrdering f t)
  · erw [dite_eq_left hn]
    let o := Classical.choice hn
    exact M.strictNegativeMeshFor_monochromatic f _ _
      o.negative o.positive_one o.positive_two
  erw [dite_eq_right hn]
  by_cases hep : Nonempty (M.PositiveEdgeOrdering f t)
  · erw [dite_eq_left hep]
    let o := Classical.choice hep
    rw [M.edgeMeshFor_triangles]
    apply M.edgePattern_monochromatic_positive
    · simpa [o, edgeVertices, Function.comp_apply] using o.positive.le
    · simpa [o, edgeVertices, Function.comp_apply] using o.negative.le
    · rw [M.edgeVertices_f f _ o.positive o.negative o.zero]
      rfl
    · rw [M.edgeVertices_f f _ o.positive o.negative o.zero]
      rfl
  erw [dite_eq_right hep]
  by_cases hen : Nonempty (M.NegativeEdgeOrdering f t)
  · erw [dite_eq_left hen]
    let o := Classical.choice hen
    exact M.edgeNegativeMeshFor_monochromatic f _ _ o.negative o.positive o.zero
  erw [dite_eq_right hen]
  have hpair := pairwise_nonnegative_of_no_orderings M f t hp hn hep hen
  have hsign := same_closed_side_of_pairwise_products hpair.1 hpair.2.1 hpair.2.2
  intro s hs
  unfold unchangedMeshFor at hs
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
  have hr : r = Finset.univ := Finset.mem_singleton.mp hr
  subst r
  rcases hsign with h | h
  · left
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
    fin_cases i
    · change 0 ≤ f (M.position (M.orderedVertex t 0)); exact h.1
    · change 0 ≤ f (M.position (M.orderedVertex t 1)); exact h.2.1
    · change 0 ≤ f (M.position (M.orderedVertex t 2)); exact h.2.2
  · right
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
    fin_cases i
    · change f (M.position (M.orderedVertex t 0)) ≤ 0; exact h.1
    · change f (M.position (M.orderedVertex t 1)) ≤ 0; exact h.2.1
    · change f (M.position (M.orderedVertex t 2)) ≤ 0; exact h.2.2

/-- A vertex used by a local line refinement is either an old vertex of its parent triangle or
lies on the cutting line. -/
theorem local_child_vertex_old_or_zero (t : M.Triangle)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t)
    {x : M.RefinedVertex f} (hx : x ∈ s) :
    (∃ v ∈ t.1, (x : Plane) = M.position v) ∨ f (x : Plane) = 0 := by
  classical
  unfold localMeshTriangles at hs
  by_cases hp : Nonempty (M.PositiveStrictOrdering f t)
  · erw [dite_eq_left hp] at hs
    let o := Classical.choice hp
    rw [M.strictMeshFor_triangles] at hs
    obtain ⟨i, rfl⟩ := exists_index_of_mem_strictPattern _ hs hx
    fin_cases i
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · right
      rw [M.strictVertices_f]
      rfl
    · right
      rw [M.strictVertices_f]
      rfl
  erw [dite_eq_right hp] at hs
  by_cases hn : Nonempty (M.NegativeStrictOrdering f t)
  · erw [dite_eq_left hn] at hs
    let o := Classical.choice hn
    unfold strictNegativeMeshFor at hs
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    rw [M.strictMeshFor_triangles] at hr
    obtain ⟨i, rfl⟩ := exists_index_of_mem_strictPattern _ hr hy
    fin_cases i
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · right
      change f (M.strictVertices (-f) (M.orderedVertex t ∘ o.perm)
        (by simpa using o.negative) (by simpa using o.positive_one)
        (by simpa using o.positive_two) 3 : Plane) = 0
      have h := M.strictVertices_f (-f) (M.orderedVertex t ∘ o.perm)
        (by simpa using o.negative) (by simpa using o.positive_one)
        (by simpa using o.positive_two) 3
      simpa using h
    · right
      change f (M.strictVertices (-f) (M.orderedVertex t ∘ o.perm)
        (by simpa using o.negative) (by simpa using o.positive_one)
        (by simpa using o.positive_two) 4 : Plane) = 0
      have h := M.strictVertices_f (-f) (M.orderedVertex t ∘ o.perm)
        (by simpa using o.negative) (by simpa using o.positive_one)
        (by simpa using o.positive_two) 4
      simpa using h
  erw [dite_eq_right hn] at hs
  by_cases hep : Nonempty (M.PositiveEdgeOrdering f t)
  · erw [dite_eq_left hep] at hs
    let o := Classical.choice hep
    rw [M.edgeMeshFor_triangles] at hs
    obtain ⟨i, rfl⟩ := exists_index_of_mem_edgePattern _ hs hx
    fin_cases i
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · right
      rw [M.edgeVertices_f f _ o.positive o.negative o.zero]
      rfl
  erw [dite_eq_right hep] at hs
  by_cases hen : Nonempty (M.NegativeEdgeOrdering f t)
  · erw [dite_eq_left hen] at hs
    let o := Classical.choice hen
    unfold edgeNegativeMeshFor at hs
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    rw [M.edgeMeshFor_triangles] at hr
    obtain ⟨i, rfl⟩ := exists_index_of_mem_edgePattern _ hr hy
    fin_cases i
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · right
      change f (M.edgeVertices (-f) (M.orderedVertex t ∘ o.perm)
        (by simpa using o.negative) (by simpa using o.positive) 3 : Plane) = 0
      have h := M.edgeVertices_f (-f) (M.orderedVertex t ∘ o.perm)
        (by simpa using o.negative) (by simpa using o.positive) (by simpa using o.zero) 3
      simpa using h
  erw [dite_eq_right hen] at hs
  unfold unchangedMeshFor at hs
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
  have hr : r = Finset.univ := Finset.mem_singleton.mp hr
  subst r
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
  left
  exact ⟨_, M.orderedVertex_mem t i, rfl⟩

theorem localMeshTriangles_support (t : M.Triangle) :
    (⋃ s ∈ M.localMeshTriangles f t,
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (s : Set (M.RefinedVertex f)))) =
      convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) := by
  classical
  unfold localMeshTriangles
  by_cases hp : Nonempty (M.PositiveStrictOrdering f t)
  · erw [dite_eq_left hp]
    let o := Classical.choice hp
    dsimp only [Function.comp_apply]
    have h := M.strictMeshFor_support f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm)
      o.positive o.negative_one o.negative_two
    rw [(M.strictMeshFor f (M.orderedVertex t ∘ o.perm) _
      o.positive o.negative_one o.negative_two).toPlaneComplex_support] at h
    rw [M.range_orderedVertex_perm t o.perm] at h
    exact h
  erw [dite_eq_right hp]
  by_cases hn : Nonempty (M.NegativeStrictOrdering f t)
  · erw [dite_eq_left hn]
    let o := Classical.choice hn
    dsimp only [Function.comp_apply]
    have h := M.strictNegativeMeshFor_support f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm)
      o.negative o.positive_one o.positive_two
    rw [(M.strictNegativeMeshFor f (M.orderedVertex t ∘ o.perm) _
      o.negative o.positive_one o.positive_two).toPlaneComplex_support] at h
    rw [M.range_orderedVertex_perm t o.perm] at h
    exact h
  erw [dite_eq_right hn]
  by_cases hep : Nonempty (M.PositiveEdgeOrdering f t)
  · erw [dite_eq_left hep]
    let o := Classical.choice hep
    dsimp only [Function.comp_apply]
    have h := M.edgeMeshFor_support f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm) o.positive o.negative
    rw [(M.edgeMeshFor f (M.orderedVertex t ∘ o.perm) _
      o.positive o.negative).toPlaneComplex_support] at h
    rw [M.range_orderedVertex_perm t o.perm] at h
    exact h
  erw [dite_eq_right hep]
  by_cases hen : Nonempty (M.NegativeEdgeOrdering f t)
  · erw [dite_eq_left hen]
    let o := Classical.choice hen
    dsimp only [Function.comp_apply]
    have h := M.edgeNegativeMeshFor_support f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm) o.negative o.positive
    rw [(M.edgeNegativeMeshFor f (M.orderedVertex t ∘ o.perm) _
      o.negative o.positive).toPlaneComplex_support] at h
    rw [M.range_orderedVertex_perm t o.perm] at h
    exact h
  erw [dite_eq_right hen]
  simp only [unchangedMeshFor, TriangleMesh.reindex, TriangleMesh.single,
    oldVerticesEmbedding]
  have h := M.unchangedMeshFor_support f (M.orderedVertex t)
    (M.orderedVertex_affineIndependent t)
  rw [(M.unchangedMeshFor f (M.orderedVertex t) _).toPlaneComplex_support] at h
  rw [Set.range_comp, M.range_orderedVertex t] at h
  exact h

theorem localMeshTriangles_inter (t : M.Triangle)
    {s u : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t)
    (hu : u ∈ M.localMeshTriangles f t) :
    convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (s : Set (M.RefinedVertex f))) ∩
        convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (u : Set (M.RefinedVertex f))) =
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        ((s ∩ u : Finset (M.RefinedVertex f)) : Set (M.RefinedVertex f))) := by
  classical
  unfold localMeshTriangles at hs hu
  by_cases hp : Nonempty (M.PositiveStrictOrdering f t)
  · erw [dite_eq_left hp] at hs hu
    exact (M.strictMeshFor f _ _ _ _ _).triangle_inter s hs u hu
  erw [dite_eq_right hp] at hs hu
  by_cases hn : Nonempty (M.NegativeStrictOrdering f t)
  · erw [dite_eq_left hn] at hs hu
    exact (M.strictNegativeMeshFor f _ _ _ _ _).triangle_inter s hs u hu
  erw [dite_eq_right hn] at hs hu
  by_cases hep : Nonempty (M.PositiveEdgeOrdering f t)
  · erw [dite_eq_left hep] at hs hu
    exact (M.edgeMeshFor f _ _ _ _).triangle_inter s hs u hu
  erw [dite_eq_right hep] at hs hu
  by_cases hen : Nonempty (M.NegativeEdgeOrdering f t)
  · erw [dite_eq_left hen] at hs hu
    exact (M.edgeNegativeMeshFor f _ _ _ _).triangle_inter s hs u hu
  erw [dite_eq_right hen] at hs hu
  exact (M.unchangedMeshFor f _ _).triangle_inter s hs u hu

theorem convexHull_child_subset_parent (t : M.Triangle)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t) :
    convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (s : Set (M.RefinedVertex f))) ⊆
      convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) := by
  rw [← M.localMeshTriangles_support f t]
  exact Set.subset_iUnion_of_subset s
    (Set.subset_iUnion_of_subset hs subset_rfl)

theorem child_vertex_mem_parent (t : M.Triangle)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t)
    {v : M.RefinedVertex f} (hv : v ∈ s) :
    (v : Plane) ∈ convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) := by
  apply M.convexHull_child_subset_parent f t hs
  exact subset_convexHull ℝ _ ⟨v, hv, rfl⟩

/-! ## Barycentric traces on old parent edges -/

/-- The barycentric coordinate opposite the `k`-th edge of an old triangle. -/
noncomputable def oppositeCoord (t : M.Triangle) (k : Fin 3) : Plane →ᵃ[ℝ] ℝ :=
  (affineBasisOfTriangle (M.position ∘ M.orderedVertex t)
    (M.orderedVertex_affineIndependent t)).coord k

@[simp] theorem oppositeCoord_vertex (t : M.Triangle) (k i : Fin 3) :
    M.oppositeCoord t k (M.position (M.orderedVertex t i)) = if k = i then 1 else 0 := by
  exact AffineBasis.coord_apply _ _ _

/-- The two old geometric vertices of the edge opposite `k`. -/
noncomputable def oppositeEdgePoints (t : M.Triangle) (k : Fin 3) : Finset Plane :=
  (Finset.univ.erase k).image (M.position ∘ M.orderedVertex t)

theorem oppositeEdgePoints_subset_parentPoints (t : M.Triangle) (k : Fin 3) :
    M.oppositeEdgePoints t k ⊆ Finset.univ.image (M.position ∘ M.orderedVertex t) := by
  exact Finset.image_subset_image (Finset.erase_subset _ _)

theorem oppositeCoord_nonneg_of_mem_parent (t : M.Triangle) (k : Fin 3)
    {x : Plane} (hx : x ∈ convexHull ℝ (M.position '' (t.1 : Set M.Vertex))) :
    0 ≤ M.oppositeCoord t k x := by
  have hrange : Set.range (M.position ∘ M.orderedVertex t) =
      M.position '' (t.1 : Set M.Vertex) := by
    rw [Set.range_comp, M.range_orderedVertex t]
  rw [← hrange] at hx
  apply convexHull_min ?_ ((convex_Ici (0 : ℝ)).affine_preimage (M.oppositeCoord t k)) hx
  rintro x ⟨i, rfl⟩
  change 0 ≤ M.oppositeCoord t k (M.position (M.orderedVertex t i))
  rw [M.oppositeCoord_vertex]
  split_ifs <;> norm_num

theorem parent_inter_oppositeCoord_zero (t : M.Triangle) (k : Fin 3) :
    convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) ∩
        {x | M.oppositeCoord t k x = 0} =
      convexHull ℝ ((M.oppositeEdgePoints t k : Finset Plane) : Set Plane) := by
  let p : Fin 3 → Plane := M.position ∘ M.orderedVertex t
  have hp : Function.Injective p :=
    M.position_injective.comp (M.orderedVertex_injective t)
  have hrange : M.position '' (t.1 : Set M.Vertex) =
      ((Finset.univ.image p : Finset Plane) : Set Plane) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.range_comp,
      M.range_orderedVertex t]
  rw [hrange]
  rw [convexHull_inter_affine_zero_of_nonneg]
  · apply congrArg (convexHull ℝ)
    ext x
    change x ∈ (Finset.univ.image p).filter (fun x ↦ M.oppositeCoord t k x = 0) ↔
      x ∈ M.oppositeEdgePoints t k
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      oppositeEdgePoints, Finset.mem_erase]
    constructor
    · rintro ⟨⟨i, hix⟩, hi⟩
      refine ⟨i, ⟨?_, trivial⟩, hix⟩
      intro hki
      subst i
      have hzero : M.oppositeCoord t k (M.position (M.orderedVertex t k)) = 0 := by
        change M.oppositeCoord t k (p k) = 0
        rw [hix]
        exact hi
      rw [M.oppositeCoord_vertex] at hzero
      norm_num at hzero
    · rintro ⟨i, ⟨hik, -⟩, hix⟩
      refine ⟨⟨i, hix⟩, ?_⟩
      rw [← hix]
      change M.oppositeCoord t k (M.position (M.orderedVertex t i)) = 0
      rw [M.oppositeCoord_vertex]
      simp [Ne.symm hik]
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    change 0 ≤ M.oppositeCoord t k (M.position (M.orderedVertex t i))
    rw [M.oppositeCoord_vertex]
    split_ifs <;> norm_num

/-- Vertices of a child triangle lying on the old edge opposite `k`. -/
noncomputable def childEdgeTrace (t : M.Triangle) (k : Fin 3)
    (s : Finset (M.RefinedVertex f)) : Finset (M.RefinedVertex f) :=
  s.filter fun v => M.oppositeCoord t k (v : Plane) = 0

theorem child_inter_oppositeEdge (t : M.Triangle) (k : Fin 3)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t) :
    convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (s : Set (M.RefinedVertex f))) ∩
        convexHull ℝ ((M.oppositeEdgePoints t k : Finset Plane) : Set Plane) =
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        (M.childEdgeTrace f t k s : Set (M.RefinedVertex f))) := by
  classical
  let A := convexHull ℝ
    (((↑) : M.RefinedVertex f → Plane) '' (s : Set (M.RefinedVertex f)))
  let P := convexHull ℝ (M.position '' (t.1 : Set M.Vertex))
  let Z : Set Plane := {x | M.oppositeCoord t k x = 0}
  have hAP : A ⊆ P := M.convexHull_child_subset_parent f t hs
  have hedge : P ∩ Z =
      convexHull ℝ ((M.oppositeEdgePoints t k : Finset Plane) : Set Plane) :=
    M.parent_inter_oppositeCoord_zero t k
  rw [← hedge]
  have hinter : A ∩ (P ∩ Z) = A ∩ Z := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1, hx.2.2⟩
    · exact fun hx => ⟨hx.1, hAP hx.1, hx.2⟩
  rw [hinter]
  dsimp only [A]
  simp only [← Finset.coe_image]
  rw [convexHull_inter_affine_zero_of_nonneg]
  · apply congrArg (convexHull ℝ)
    ext x
    change x ∈ (s.image ((↑) : M.RefinedVertex f → Plane)).filter
        (fun x ↦ M.oppositeCoord t k x = 0) ↔
      x ∈ (M.childEdgeTrace f t k s).image ((↑) : M.RefinedVertex f → Plane)
    simp only [Finset.mem_filter, Finset.mem_image, childEdgeTrace]
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, hz⟩
      exact ⟨v, ⟨hv, hz⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv.1, rfl⟩, hv.2⟩
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact M.oppositeCoord_nonneg_of_mem_parent t k
      (M.child_vertex_mem_parent f t hs hv)

theorem exists_oppositeEdgePoints_eq (t : M.Triangle) {e : Finset M.Vertex}
    (het : e ⊆ t.1) (hecard : e.card = 2) :
    ∃ k : Fin 3, M.oppositeEdgePoints t k = e.image M.position := by
  have hne : e ≠ t.1 := by
    intro h
    have hc := hecard
    rw [h, M.card_triangle t.1 t.2] at hc
    omega
  have hss : e ⊂ t.1 := Finset.ssubset_iff_subset_ne.mpr ⟨het, hne⟩
  obtain ⟨w, hwt, hwe⟩ := Finset.exists_of_ssubset hss
  have hwrange : w ∈ Set.range (M.orderedVertex t) := by
    rw [M.range_orderedVertex t]
    exact hwt
  obtain ⟨k, hwk⟩ := hwrange
  have herase : t.1.erase w = e := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      exact Finset.mem_erase.mpr ⟨fun hvw => hwe (hvw ▸ hv), het hv⟩
    · rw [Finset.card_erase_of_mem hwt, M.card_triangle t.1 t.2, hecard]
  refine ⟨k, ?_⟩
  apply Finset.ext
  intro x
  simp only [oppositeEdgePoints, Finset.mem_image, Finset.mem_erase, Finset.mem_univ,
    and_true]
  constructor
  · rintro ⟨i, hik, rfl⟩
    refine ⟨M.orderedVertex t i, ?_, rfl⟩
    rw [← herase]
    exact Finset.mem_erase.mpr ⟨fun hiw => hik (M.orderedVertex_injective t
      (hiw.trans hwk.symm)), M.orderedVertex_mem t i⟩
  · rintro ⟨v, hve, rfl⟩
    have hvt : v ∈ t.1 := het hve
    have hvrange : v ∈ Set.range (M.orderedVertex t) := by
      rw [M.range_orderedVertex t]
      exact hvt
    obtain ⟨i, rfl⟩ := hvrange
    refine ⟨i, ?_, rfl⟩
    intro hik
    subst i
    apply hwe
    simpa [hwk] using hve

/-- An affine functional taking different values at the endpoints of a segment is injective on
that segment. -/
theorem affine_apply_injectiveOn_segment {g : Plane →ᵃ[ℝ] ℝ} {p q : Plane}
    (hpq : g p ≠ g q) : Set.InjOn g (segment ℝ p q) := by
  intro x hx y hy hxy
  rw [segment_eq_image_lineMap] at hx hy
  obtain ⟨a, -, rfl⟩ := hx
  obtain ⟨b, -, rfl⟩ := hy
  rw [AffineMap.apply_lineMap, AffineMap.apply_lineMap] at hxy
  simp only [AffineMap.lineMap_apply_module, smul_eq_mul] at hxy
  have hd : g q - g p ≠ 0 := sub_ne_zero.mpr hpq.symm
  have hab : a = b := by
    rcases lt_or_gt_of_ne hd with hdneg | hdpos <;> nlinarith
  rw [hab]

theorem eq_endpoint_of_mem_segment_apply_zero_of_mul_nonneg
    {g : Plane →ᵃ[ℝ] ℝ} {p q x : Plane}
    (hprod : 0 ≤ g p * g q) (hnotboth : ¬ (g p = 0 ∧ g q = 0))
    (hx : x ∈ segment ℝ p q) (hzero : g x = 0) : x = p ∨ x = q := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  rw [g.apply_lineMap, AffineMap.lineMap_apply_module] at hzero
  simp only [smul_eq_mul] at hzero
  by_cases hp : g p = 0
  · have hq : g q ≠ 0 := fun hq => hnotboth ⟨hp, hq⟩
    have ht0 : t = 0 := by
      rw [hp] at hzero
      apply (mul_eq_zero.mp (by linarith : t * g q = 0)).resolve_right hq
    left
    simp [ht0, AffineMap.lineMap_apply_module]
  · by_cases hq : g q = 0
    · have ht1 : t = 1 := by
        rw [hq] at hzero
        have : (1 - t) * g p = 0 := by linarith
        have := (mul_eq_zero.mp this).resolve_right hp
        linarith
      right
      simp [ht1, AffineMap.lineMap_apply_module]
    · have hpos : 0 < g p * g q := lt_of_le_of_ne hprod (mul_ne_zero hp hq).symm
      rcases mul_pos_iff.mp hpos with hsign | hsign
      · have ht0 := ht.1
        have ht1 := ht.2
        nlinarith [mul_nonneg (sub_nonneg.mpr ht1) hsign.1.le,
          mul_nonneg ht0 hsign.2.le]
      · have ht0 := ht.1
        have ht1 := ht.2
        nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (neg_nonneg.mpr hsign.1.le),
          mul_nonneg ht0 (neg_nonneg.mpr hsign.2.le)]

theorem affineIndependent_subset_pair {p q : Plane} (hpq : p ≠ q)
    {s : Set Plane} (hs : s ⊆ {p, q}) :
    AffineIndependent ℝ ((↑) : s → Plane) := by
  have h := (affineIndependent_of_ne (k := ℝ) hpq).range
  apply h.mono
  simpa [Set.pair_comm] using hs

theorem old_vertex_mem_of_oppositeCoord_zero (t : M.Triangle) (k : Fin 3)
    {e : Finset M.Vertex} (hedge : M.oppositeEdgePoints t k = e.image M.position)
    {v : M.Vertex} (hvt : v ∈ t.1)
    (hzero : M.oppositeCoord t k (M.position v) = 0) : v ∈ e := by
  have hvrange : v ∈ Set.range (M.orderedVertex t) := by
    rw [M.range_orderedVertex t]
    exact hvt
  obtain ⟨i, rfl⟩ := hvrange
  have hik : k ≠ i := by
    intro hki
    subst i
    rw [M.oppositeCoord_vertex] at hzero
    norm_num at hzero
  have hp : M.position (M.orderedVertex t i) ∈ M.oppositeEdgePoints t k := by
    unfold oppositeEdgePoints
    exact Finset.mem_image.mpr ⟨i, Finset.mem_erase.mpr ⟨hik.symm, Finset.mem_univ _⟩, rfl⟩
  rw [hedge] at hp
  obtain ⟨w, hwe, hw⟩ := Finset.mem_image.mp hp
  exact M.position_injective hw |>.symm ▸ hwe

theorem trace_vertex_old_edge_or_zero (t : M.Triangle) (k : Fin 3)
    {e : Finset M.Vertex} (hedge : M.oppositeEdgePoints t k = e.image M.position)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t)
    {x : M.RefinedVertex f} (hx : x ∈ M.childEdgeTrace f t k s) :
    (∃ v ∈ e, (x : Plane) = M.position v) ∨ f (x : Plane) = 0 := by
  have hxs : x ∈ s := (Finset.mem_filter.mp hx).1
  have hxcoord : M.oppositeCoord t k (x : Plane) = 0 := (Finset.mem_filter.mp hx).2
  rcases M.local_child_vertex_old_or_zero f t hs hxs with hold | hzero
  · obtain ⟨v, hvt, hxv⟩ := hold
    left
    refine ⟨v, M.old_vertex_mem_of_oppositeCoord_zero t k hedge hvt ?_, hxv⟩
    rw [← hxv]
    exact hxcoord
  · exact Or.inr hzero

theorem trace_vertex_mem_oppositeEdgeHull (t : M.Triangle) (k : Fin 3)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t)
    {x : M.RefinedVertex f} (hx : x ∈ M.childEdgeTrace f t k s) :
    (x : Plane) ∈ convexHull ℝ ((M.oppositeEdgePoints t k : Finset Plane) : Set Plane) := by
  rw [← M.parent_inter_oppositeCoord_zero t k]
  exact ⟨M.child_vertex_mem_parent f t hs (Finset.mem_filter.mp hx).1,
    (Finset.mem_filter.mp hx).2⟩

theorem trace_vertex_eq_endpoint_or_cut (t : M.Triangle) (k : Fin 3)
    {a b : M.Vertex} (hab : a ≠ b)
    (hedge : M.oppositeEdgePoints t k = ({a, b} : Finset M.Vertex).image M.position)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t)
    (ha : 0 < f (M.position a)) (hb : f (M.position b) < 0)
    {x : M.RefinedVertex f} (hx : x ∈ M.childEdgeTrace f t k s) :
    x = M.oldRefinedVertex f a ∨ x = M.oldRefinedVertex f b ∨
      x = M.cutRefinedVertex f a b (mul_neg_of_pos_of_neg ha hb) := by
  rcases M.trace_vertex_old_edge_or_zero f t k hedge hs hx with hold | hzero
  · obtain ⟨v, hv, hxv⟩ := hold
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Or.inl (Subtype.ext hxv)
    · exact Or.inr (Or.inl (Subtype.ext hxv))
  · right; right
    apply Subtype.ext
    apply affineCutPoint.eq_of_mem_segment_of_apply_eq_zero f (M.position a) (M.position b)
      ha hb
    · have hxedge := M.trace_vertex_mem_oppositeEdgeHull f t k hs hx
      rw [hedge] at hxedge
      simp only [Finset.coe_image, Finset.coe_insert, Finset.coe_singleton,
        Set.image_insert_eq, Set.image_singleton] at hxedge
      rwa [convexHull_pair] at hxedge
    · exact hzero

theorem trace_vertex_eq_endpoint_of_mul_nonneg (t : M.Triangle) (k : Fin 3)
    {a b : M.Vertex} (hab : a ≠ b)
    (hedge : M.oppositeEdgePoints t k = ({a, b} : Finset M.Vertex).image M.position)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t)
    (hprod : 0 ≤ f (M.position a) * f (M.position b))
    (hnotboth : ¬ (f (M.position a) = 0 ∧ f (M.position b) = 0))
    {x : M.RefinedVertex f} (hx : x ∈ M.childEdgeTrace f t k s) :
    x = M.oldRefinedVertex f a ∨ x = M.oldRefinedVertex f b := by
  rcases M.trace_vertex_old_edge_or_zero f t k hedge hs hx with hold | hzero
  · obtain ⟨v, hv, hxv⟩ := hold
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Or.inl (Subtype.ext hxv)
    · exact Or.inr (Subtype.ext hxv)
  · have hxedge := M.trace_vertex_mem_oppositeEdgeHull f t k hs hx
    rw [hedge] at hxedge
    simp only [Finset.coe_image, Finset.coe_insert, Finset.coe_singleton,
      Set.image_insert_eq, Set.image_singleton] at hxedge
    rw [convexHull_pair] at hxedge
    rcases eq_endpoint_of_mem_segment_apply_zero_of_mul_nonneg hprod hnotboth hxedge hzero
      with hxa | hxb
    · exact Or.inl (Subtype.ext hxa)
    · exact Or.inr (Subtype.ext hxb)

theorem orderedVertex_eq_endpoint_of_ne_opposite (t : M.Triangle) (k j : Fin 3)
    {a b : M.Vertex}
    (hedge : M.oppositeEdgePoints t k = ({a, b} : Finset M.Vertex).image M.position)
    (hjk : j ≠ k) : M.orderedVertex t j = a ∨ M.orderedVertex t j = b := by
  have hp : M.position (M.orderedVertex t j) ∈ M.oppositeEdgePoints t k := by
    unfold oppositeEdgePoints
    exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ _⟩, rfl⟩
  rw [hedge] at hp
  obtain ⟨v, hv, hpos⟩ := Finset.mem_image.mp hp
  have hvj : v = M.orderedVertex t j := M.position_injective hpos
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact Or.inl hvj.symm
  · exact Or.inr hvj.symm

theorem trace_vertex_eq_endpoint_of_edge_in_line (t : M.Triangle) (k : Fin 3)
    {a b : M.Vertex} (_ : a ≠ b)
    (hedge : M.oppositeEdgePoints t k = ({a, b} : Finset M.Vertex).image M.position)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t)
    (ha : f (M.position a) = 0) (hb : f (M.position b) = 0)
    {x : M.RefinedVertex f} (hx : x ∈ M.childEdgeTrace f t k s) :
    x = M.oldRefinedVertex f a ∨ x = M.oldRefinedVertex f b := by
  classical
  have hzero (j : Fin 3) (hjk : j ≠ k) :
      f (M.position (M.orderedVertex t j)) = 0 := by
    rcases M.orderedVertex_eq_endpoint_of_ne_opposite t k j hedge hjk with hj | hj
    · simpa [hj] using ha
    · simpa [hj] using hb
  have hp : ¬ Nonempty (M.PositiveStrictOrdering f t) := by
    rintro ⟨o⟩
    have hne : o.perm 0 ≠ o.perm 1 := o.perm.injective.ne (by decide)
    by_cases h0k : o.perm 0 = k
    · have h1k : o.perm 1 ≠ k := fun h => hne (h0k.trans h.symm)
      linarith [hzero (o.perm 1) h1k, o.negative_one]
    · linarith [hzero (o.perm 0) h0k, o.positive]
  have hn : ¬ Nonempty (M.NegativeStrictOrdering f t) := by
    rintro ⟨o⟩
    have hne : o.perm 0 ≠ o.perm 1 := o.perm.injective.ne (by decide)
    by_cases h0k : o.perm 0 = k
    · have h1k : o.perm 1 ≠ k := fun h => hne (h0k.trans h.symm)
      linarith [hzero (o.perm 1) h1k, o.positive_one]
    · linarith [hzero (o.perm 0) h0k, o.negative]
  have hep : ¬ Nonempty (M.PositiveEdgeOrdering f t) := by
    rintro ⟨o⟩
    have hne : o.perm 0 ≠ o.perm 1 := o.perm.injective.ne (by decide)
    by_cases h0k : o.perm 0 = k
    · have h1k : o.perm 1 ≠ k := fun h => hne (h0k.trans h.symm)
      linarith [hzero (o.perm 1) h1k, o.negative]
    · linarith [hzero (o.perm 0) h0k, o.positive]
  have hen : ¬ Nonempty (M.NegativeEdgeOrdering f t) := by
    rintro ⟨o⟩
    have hne : o.perm 0 ≠ o.perm 1 := o.perm.injective.ne (by decide)
    by_cases h0k : o.perm 0 = k
    · have h1k : o.perm 1 ≠ k := fun h => hne (h0k.trans h.symm)
      linarith [hzero (o.perm 1) h1k, o.positive]
    · linarith [hzero (o.perm 0) h0k, o.negative]
  unfold localMeshTriangles at hs
  simp only [hp, hn, hep, hen, ↓reduceDIte] at hs
  unfold unchangedMeshFor at hs
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
  have hr : r = Finset.univ := Finset.mem_singleton.mp hr
  subst r
  have hxs := (Finset.mem_filter.mp hx).1
  obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hxs
  have hjk : j ≠ k := by
    intro hjk
    subst j
    have hz := (Finset.mem_filter.mp hx).2
    change M.oppositeCoord t k
        (M.oldRefinedVertex f (M.orderedVertex t k) : Plane) = 0 at hz
    change M.oppositeCoord t k (M.position (M.orderedVertex t k)) = 0 at hz
    rw [M.oppositeCoord_vertex] at hz
    norm_num at hz
  rcases M.orderedVertex_eq_endpoint_of_ne_opposite t k j hedge hjk with hj | hj
  · left
    change M.oldRefinedVertex f (M.orderedVertex t j) = M.oldRefinedVertex f a
    rw [hj]
  · right
    change M.oldRefinedVertex f (M.orderedVertex t j) = M.oldRefinedVertex f b
    rw [hj]

theorem childEdgeTrace_monochromatic (t : M.Triangle) (k : Fin 3)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t) :
    (∀ x ∈ M.childEdgeTrace f t k s, 0 ≤ f (x : Plane)) ∨
      (∀ x ∈ M.childEdgeTrace f t k s, f (x : Plane) ≤ 0) := by
  rcases M.localMeshTriangles_monochromatic f t s hs with h | h
  · exact Or.inl fun x hx => h x (Finset.mem_filter.mp hx).1
  · exact Or.inr fun x hx => h x (Finset.mem_filter.mp hx).1

private theorem convexHull_inter_of_opposite_three_point_subsets
    {a b z : M.RefinedVertex f}
    (ha : 0 < f (a : Plane)) (hb : f (b : Plane) < 0) (hz : f (z : Plane) = 0)
    {C D : Finset (M.RefinedVertex f)}
    (hCclass : ∀ x ∈ C, x = a ∨ x = b ∨ x = z)
    (hDclass : ∀ x ∈ D, x = a ∨ x = b ∨ x = z)
    (hC : ∀ x ∈ C, 0 ≤ f (x : Plane)) (hD : ∀ x ∈ D, f (x : Plane) ≤ 0) :
    convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (C : Set (M.RefinedVertex f))) ∩
        convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (D : Set (M.RefinedVertex f))) =
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        ((C ∩ D : Finset (M.RefinedVertex f)) : Set (M.RefinedVertex f))) := by
  classical
  let val : M.RefinedVertex f → Plane := (↑)
  simp only [← Finset.coe_image]
  have hCsub : C ⊆ {a, z} := by
    intro x hx
    rcases hCclass x hx with rfl | rfl | rfl
    · simp
    · exfalso; linarith [hC _ hx]
    · simp
  have hDsub : D ⊆ {b, z} := by
    intro x hx
    rcases hDclass x hx with rfl | rfl | rfl
    · exfalso; linarith [hD _ hx]
    · simp
    · simp
  by_cases hzC : z ∈ C
  · by_cases hzD : z ∈ D
    · have hCzero : (C.image val).filter (fun p ↦ f p = 0) = {(z : Plane)} := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨x, hx, rfl⟩, hxzero⟩
          rcases hCclass x hx with rfl | rfl | rfl
          · exfalso; linarith
          · exfalso; linarith
          · rfl
        · rintro rfl
          exact ⟨⟨z, hzC, rfl⟩, hz⟩
      have hDzero : (D.image val).filter (fun p ↦ f p = 0) = {(z : Plane)} := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨x, hx, rfl⟩, hxzero⟩
          rcases hDclass x hx with rfl | rfl | rfl
          · exfalso; linarith
          · exfalso; linarith
          · rfl
        · rintro rfl
          exact ⟨⟨z, hzD, rfl⟩, hz⟩
      have hinter := convexHull_inter_of_affine_separation
        (C.image val) (D.image val) ({(z : Plane)} : Finset Plane) f
        (by
          intro p hp
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
          exact hC x hx)
        (by
          intro p hp
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
          exact hD x hx)
        hCzero hDzero
      have hCD : C ∩ D = {z} := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_singleton]
        constructor
        · rintro ⟨hxC, hxD⟩
          have hxpair := hCsub hxC
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
          rcases hxpair with hxa | hxz
          · subst x
            exfalso
            linarith [hD a hxD]
          · exact hxz
        · rintro rfl
          exact ⟨hzC, hzD⟩
      rw [hCD]
      simpa [val] using hinter
    · have hDsingle : D ⊆ {b} := by
        intro x hx
        have hxpair := hDsub hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
        rcases hxpair with hxb | hxz
        · simp [hxb]
        · exact False.elim (hzD (hxz ▸ hx))
      have hDgeom : convexHull ℝ ((D.image val : Finset Plane) : Set Plane) ⊆ {(b : Plane)} :=
        convexHull_min (by
          intro p hp
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
          simpa [val] using hDsingle hx) (convex_singleton _)
      have hCnonneg : convexHull ℝ ((C.image val : Finset Plane) : Set Plane) ⊆
          {p | 0 ≤ f p} := convexHull_min (by
        intro p hp
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
        exact hC x hx) ((convex_Ici (0 : ℝ)).affine_preimage f)
      have hleft : convexHull ℝ ((C.image val : Finset Plane) : Set Plane) ∩
          convexHull ℝ ((D.image val : Finset Plane) : Set Plane) = ∅ := by
        apply Set.Subset.antisymm
        · intro p hp
          have hpb := hDgeom hp.2
          simp only [Set.mem_singleton_iff] at hpb
          subst p
          exfalso
          have hbnonneg : 0 ≤ f (b : Plane) := hCnonneg hp.1
          linarith
        · exact Set.empty_subset _
      have hCD : C ∩ D = ∅ := by
        ext x
        constructor
        · intro hx
          have hx' := Finset.mem_inter.mp hx
          have hxb := hDsingle hx'.2
          simp only [Finset.mem_singleton] at hxb
          subst x
          exfalso
          linarith [hC b hx'.1]
        · intro hx
          simp at hx
      rw [hleft, hCD]
      simp
  · have hCsingle : C ⊆ {a} := by
      intro x hx
      have hxpair := hCsub hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
      rcases hxpair with hxa | hxz
      · simp [hxa]
      · exact False.elim (hzC (hxz ▸ hx))
    have hCgeom : convexHull ℝ ((C.image val : Finset Plane) : Set Plane) ⊆ {(a : Plane)} :=
      convexHull_min (by
        intro p hp
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
        simpa [val] using hCsingle hx) (convex_singleton _)
    have hDnonpos : convexHull ℝ ((D.image val : Finset Plane) : Set Plane) ⊆
        {p | f p ≤ 0} := convexHull_min (by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      exact hD x hx) ((convex_Iic (0 : ℝ)).affine_preimage f)
    have hleft : convexHull ℝ ((C.image val : Finset Plane) : Set Plane) ∩
        convexHull ℝ ((D.image val : Finset Plane) : Set Plane) = ∅ := by
      apply Set.Subset.antisymm
      · intro p hp
        have hpa := hCgeom hp.1
        simp only [Set.mem_singleton_iff] at hpa
        subst p
        exfalso
        have hanonpos : f (a : Plane) ≤ 0 := hDnonpos hp.2
        linarith
      · exact Set.empty_subset _
    have hCD : C ∩ D = ∅ := by
      ext x
      constructor
      · intro hx
        have hx' := Finset.mem_inter.mp hx
        have hxa := hCsingle hx'.1
        simp only [Finset.mem_singleton] at hxa
        subst x
        exfalso
        linarith [hD a hx'.2]
      · intro hx
        simp at hx
    rw [hleft, hCD]
    simp

/-- The finite one-dimensional calculation behind compatibility on a cut edge. -/
theorem convexHull_inter_of_signed_three_point_subsets
    {a b z : M.RefinedVertex f}
    (ha : 0 < f (a : Plane)) (hb : f (b : Plane) < 0) (hz : f (z : Plane) = 0)
    {A B : Finset (M.RefinedVertex f)}
    (hAclass : ∀ x ∈ A, x = a ∨ x = b ∨ x = z)
    (hBclass : ∀ x ∈ B, x = a ∨ x = b ∨ x = z)
    (hAmono : (∀ x ∈ A, 0 ≤ f (x : Plane)) ∨ (∀ x ∈ A, f (x : Plane) ≤ 0))
    (hBmono : (∀ x ∈ B, 0 ≤ f (x : Plane)) ∨ (∀ x ∈ B, f (x : Plane) ≤ 0)) :
    convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (A : Set (M.RefinedVertex f))) ∩
        convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (B : Set (M.RefinedVertex f))) =
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        ((A ∩ B : Finset (M.RefinedVertex f)) : Set (M.RefinedVertex f))) := by
  classical
  let val : M.RefinedVertex f → Plane := (↑)
  let AP : Finset Plane := A.image val
  let BP : Finset Plane := B.image val
  have ha_ne_z : (a : Plane) ≠ (z : Plane) := by
    intro h
    have := congrArg f h
    linarith
  have hb_ne_z : (b : Plane) ≠ (z : Plane) := by
    intro h
    have := congrArg f h
    linarith
  have sameSide
      (hA : ∀ x ∈ A, 0 ≤ f (x : Plane))
      (hB : ∀ x ∈ B, 0 ≤ f (x : Plane)) :
      convexHull ℝ (AP : Set Plane) ∩ convexHull ℝ (BP : Set Plane) =
        convexHull ℝ ((AP ∩ BP : Finset Plane) : Set Plane) := by
    have hAsub : A ⊆ {a, z} := by
      intro x hx
      rcases hAclass x hx with rfl | rfl | rfl
      · simp
      · exfalso; linarith [hA _ hx]
      · simp
    have hBsub : B ⊆ {a, z} := by
      intro x hx
      rcases hBclass x hx with rfl | rfl | rfl
      · simp
      · exfalso; linarith [hB _ hx]
      · simp
    have hPsub : (AP ∪ BP : Finset Plane) ⊆ {(a : Plane), (z : Plane)} := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
        simpa [val] using hAsub hv
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
        simpa [val] using hBsub hv
    have hAI : AffineIndependent ℝ
        ((↑) : (AP ∪ BP : Finset Plane) → Plane) := by
      apply affineIndependent_subset_pair ha_ne_z
      intro x hx
      change x = (a : Plane) ∨ x = (z : Plane)
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hPsub hx
    simpa only [Finset.coe_inter] using (hAI.convexHull_inter').symm
  have sameSideNeg
      (hA : ∀ x ∈ A, f (x : Plane) ≤ 0)
      (hB : ∀ x ∈ B, f (x : Plane) ≤ 0) :
      convexHull ℝ (AP : Set Plane) ∩ convexHull ℝ (BP : Set Plane) =
        convexHull ℝ ((AP ∩ BP : Finset Plane) : Set Plane) := by
    have hAsub : A ⊆ {b, z} := by
      intro x hx
      rcases hAclass x hx with rfl | rfl | rfl
      · exfalso; linarith [hA _ hx]
      · simp
      · simp
    have hBsub : B ⊆ {b, z} := by
      intro x hx
      rcases hBclass x hx with rfl | rfl | rfl
      · exfalso; linarith [hB _ hx]
      · simp
      · simp
    have hPsub : (AP ∪ BP : Finset Plane) ⊆ {(b : Plane), (z : Plane)} := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
        simpa [val] using hAsub hv
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
        simpa [val] using hBsub hv
    have hAI : AffineIndependent ℝ
        ((↑) : (AP ∪ BP : Finset Plane) → Plane) := by
      apply affineIndependent_subset_pair hb_ne_z
      intro x hx
      change x = (b : Plane) ∨ x = (z : Plane)
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hPsub hx
    simpa only [Finset.coe_inter] using (hAI.convexHull_inter').symm
  have oppositeSide {C D : Finset (M.RefinedVertex f)}
      (hCclass : ∀ x ∈ C, x = a ∨ x = b ∨ x = z)
      (hDclass : ∀ x ∈ D, x = a ∨ x = b ∨ x = z)
      (hC : ∀ x ∈ C, 0 ≤ f (x : Plane))
      (hD : ∀ x ∈ D, f (x : Plane) ≤ 0) :
      convexHull ℝ ((C.image val : Finset Plane) : Set Plane) ∩
          convexHull ℝ ((D.image val : Finset Plane) : Set Plane) =
        convexHull ℝ (((C ∩ D).image val : Finset Plane) : Set Plane) := by
    simpa only [← Finset.coe_image] using
      convexHull_inter_of_opposite_three_point_subsets (M := M) (f := f)
        ha hb hz hCclass hDclass hC hD
  simp only [← Finset.coe_image]
  change convexHull ℝ (AP : Set Plane) ∩ convexHull ℝ (BP : Set Plane) =
    convexHull ℝ (((A ∩ B).image val : Finset Plane) : Set Plane)
  have himageInter : (A ∩ B).image val = AP ∩ BP := by
    exact Finset.image_inter _ _ Subtype.val_injective
  rcases hAmono with hA | hA <;> rcases hBmono with hB | hB
  · exact (sameSide hA hB).trans (congrArg (fun S : Set Plane => convexHull ℝ S)
      (by simpa only [Finset.coe_inj] using himageInter.symm))
  · exact oppositeSide hAclass hBclass hA hB
  · rw [Set.inter_comm, Finset.inter_comm]
    exact oppositeSide hBclass hAclass hB hA
  · exact (sameSideNeg hA hB).trans (congrArg (fun S : Set Plane => convexHull ℝ S)
      (by simpa only [Finset.coe_inj] using himageInter.symm))

theorem convexHull_inter_of_two_point_subsets
    {a b : M.RefinedVertex f} (hab : (a : Plane) ≠ (b : Plane))
    {A B : Finset (M.RefinedVertex f)}
    (hA : ∀ x ∈ A, x = a ∨ x = b) (hB : ∀ x ∈ B, x = a ∨ x = b) :
    convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (A : Set (M.RefinedVertex f))) ∩
        convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (B : Set (M.RefinedVertex f))) =
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        ((A ∩ B : Finset (M.RefinedVertex f)) : Set (M.RefinedVertex f))) := by
  classical
  let AP := A.image ((↑) : M.RefinedVertex f → Plane)
  let BP := B.image ((↑) : M.RefinedVertex f → Plane)
  have hsub : (AP ∪ BP : Finset Plane) ⊆ {(a : Plane), (b : Plane)} := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      simpa using hA x hx
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      simpa using hB x hx
  have hAI : AffineIndependent ℝ ((↑) : (AP ∪ BP : Finset Plane) → Plane) := by
    apply affineIndependent_subset_pair hab
    intro p hp
    change p = (a : Plane) ∨ p = (b : Plane)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hsub hp
  have hinter := (hAI.convexHull_inter').symm
  simp only [← Finset.coe_image]
  have hi : (A ∩ B).image ((↑) : M.RefinedVertex f → Plane) = AP ∩ BP :=
    Finset.image_inter _ _ Subtype.val_injective
  exact hinter.trans (congrArg (fun S : Set Plane => convexHull ℝ S)
    (by simpa only [Finset.coe_inter] using
      congrArg ((↑) : Finset Plane → Set Plane) hi.symm))

/-- The cutting line contains no old edge of the mesh. -/
def TransverseToEdges : Prop :=
  ∀ (t : M.Triangle) (i j : Fin 3), i ≠ j →
    ¬ (f (M.position (M.orderedVertex t i)) = 0 ∧
      f (M.position (M.orderedVertex t j)) = 0)

theorem lineRefinementTriangles_inter_of_parent_inter_card_two
    (T U : M.Triangle)
    (hcard : (T.1 ∩ U.1).card = 2)
    {s q : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f T)
    (hq : q ∈ M.localMeshTriangles f U) :
    convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (s : Set (M.RefinedVertex f))) ∩
        convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (q : Set (M.RefinedVertex f))) =
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        ((s ∩ q : Finset (M.RefinedVertex f)) : Set (M.RefinedVertex f))) := by
  classical
  let e : Finset M.Vertex := T.1 ∩ U.1
  have heT : e ⊆ T.1 := Finset.inter_subset_left
  have heU : e ⊆ U.1 := Finset.inter_subset_right
  obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp hcard
  have he' : e = {a, b} := he
  obtain ⟨kT, hkT⟩ := M.exists_oppositeEdgePoints_eq T heT hcard
  obtain ⟨kU, hkU⟩ := M.exists_oppositeEdgePoints_eq U heU hcard
  have hkT' : M.oppositeEdgePoints T kT = ({a, b} : Finset M.Vertex).image M.position := by
    rw [hkT, ← he']
  have hkU' : M.oppositeEdgePoints U kU = ({a, b} : Finset M.Vertex).image M.position := by
    rw [hkU, ← he']
  let A := M.childEdgeTrace f T kT s
  let B := M.childEdgeTrace f U kU q
  let S := convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
    (s : Set (M.RefinedVertex f)))
  let Q := convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
    (q : Set (M.RefinedVertex f)))
  let PT := convexHull ℝ (M.position '' (T.1 : Set M.Vertex))
  let PU := convexHull ℝ (M.position '' (U.1 : Set M.Vertex))
  let F := convexHull ℝ (M.position '' (e : Set M.Vertex))
  have hparent : PT ∩ PU = F := M.triangle_inter T.1 T.2 U.1 U.2
  have hSsub : S ⊆ PT := M.convexHull_child_subset_parent f T hs
  have hQsub : Q ⊆ PU := M.convexHull_child_subset_parent f U hq
  have hrestrict : S ∩ Q = (S ∩ F) ∩ (Q ∩ F) := by
    ext x
    constructor
    · intro hx
      have hxF : x ∈ F := by
        rw [← hparent]
        exact ⟨hSsub hx.1, hQsub hx.2⟩
      exact ⟨⟨hx.1, hxF⟩, hx.2, hxF⟩
    · intro hx
      exact ⟨hx.1.1, hx.2.1⟩
  have hTF : convexHull ℝ ((M.oppositeEdgePoints T kT : Finset Plane) : Set Plane) = F := by
    dsimp only [F]
    rw [hkT]
    simp only [Finset.coe_image]
  have hUF : convexHull ℝ ((M.oppositeEdgePoints U kU : Finset Plane) : Set Plane) = F := by
    dsimp only [F]
    rw [hkU]
    simp only [Finset.coe_image]
  have hST := M.child_inter_oppositeEdge f T kT hs
  have hQU := M.child_inter_oppositeEdge f U kU hq
  rw [hTF] at hST
  rw [hUF] at hQU
  have htraceInter : s ∩ q = A ∩ B := by
    ext x
    simp only [Finset.mem_inter]
    constructor
    · intro hx
      have hxparent : (x : Plane) ∈ PT ∩ PU :=
        ⟨M.child_vertex_mem_parent f T hs hx.1,
          M.child_vertex_mem_parent f U hq hx.2⟩
      rw [hparent] at hxparent
      have hxTzero : M.oppositeCoord T kT (x : Plane) = 0 := by
        have hxedge : (x : Plane) ∈
            convexHull ℝ ((M.oppositeEdgePoints T kT : Finset Plane) : Set Plane) := by
          rw [hTF]
          exact hxparent
        rw [← M.parent_inter_oppositeCoord_zero T kT] at hxedge
        exact hxedge.2
      have hxUzero : M.oppositeCoord U kU (x : Plane) = 0 := by
        have hxedge : (x : Plane) ∈
            convexHull ℝ ((M.oppositeEdgePoints U kU : Finset Plane) : Set Plane) := by
          rw [hUF]
          exact hxparent
        rw [← M.parent_inter_oppositeCoord_zero U kU] at hxedge
        exact hxedge.2
      exact ⟨Finset.mem_filter.mpr ⟨hx.1, hxTzero⟩,
        Finset.mem_filter.mpr ⟨hx.2, hxUzero⟩⟩
    · intro hx
      exact ⟨(Finset.mem_filter.mp hx.1).1, (Finset.mem_filter.mp hx.2).1⟩
  have hAB :
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (A : Set (M.RefinedVertex f))) ∩
          convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (B : Set (M.RefinedVertex f))) =
        convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
          ((A ∩ B : Finset (M.RefinedVertex f)) : Set (M.RefinedVertex f))) := by
    by_cases hcross : f (M.position a) * f (M.position b) < 0
    · rcases mul_neg_iff.mp hcross with hsign | hsign
      · let z := M.cutRefinedVertex f a b hcross
        apply M.convexHull_inter_of_signed_three_point_subsets f
          (a := M.oldRefinedVertex f a) (b := M.oldRefinedVertex f b) (z := z)
          hsign.1 hsign.2
          (by simpa [z] using M.pairCutPosition_apply_eq_zero f a b hcross)
        · intro x hx
          exact M.trace_vertex_eq_endpoint_or_cut f T kT hab hkT' hs hsign.1 hsign.2 hx
        · intro x hx
          exact M.trace_vertex_eq_endpoint_or_cut f U kU hab hkU' hq hsign.1 hsign.2 hx
        · exact M.childEdgeTrace_monochromatic f T kT hs
        · exact M.childEdgeTrace_monochromatic f U kU hq
      · have hcross' : f (M.position b) * f (M.position a) < 0 := by
          simpa [mul_comm] using hcross
        let z := M.cutRefinedVertex f b a hcross'
        apply M.convexHull_inter_of_signed_three_point_subsets f
          (a := M.oldRefinedVertex f b) (b := M.oldRefinedVertex f a) (z := z)
          hsign.2 hsign.1
          (by simpa [z] using M.pairCutPosition_apply_eq_zero f b a hcross')
        · intro x hx
          exact M.trace_vertex_eq_endpoint_or_cut f T kT hab.symm
            (by simpa [Finset.pair_comm] using hkT') hs hsign.2 hsign.1 hx
        · intro x hx
          exact M.trace_vertex_eq_endpoint_or_cut f U kU hab.symm
            (by simpa [Finset.pair_comm] using hkU') hq hsign.2 hsign.1 hx
        · exact M.childEdgeTrace_monochromatic f T kT hs
        · exact M.childEdgeTrace_monochromatic f U kU hq
    · apply M.convexHull_inter_of_two_point_subsets f
          (a := M.oldRefinedVertex f a) (b := M.oldRefinedVertex f b)
          (fun h => hab (M.position_injective h))
      · intro x hx
        by_cases hboth : f (M.position a) = 0 ∧ f (M.position b) = 0
        · exact M.trace_vertex_eq_endpoint_of_edge_in_line f T kT hab hkT' hs
            hboth.1 hboth.2 hx
        · exact M.trace_vertex_eq_endpoint_of_mul_nonneg f T kT hab hkT' hs
            (not_lt.mp hcross) hboth hx
      · intro x hx
        by_cases hboth : f (M.position a) = 0 ∧ f (M.position b) = 0
        · exact M.trace_vertex_eq_endpoint_of_edge_in_line f U kU hab hkU' hq
            hboth.1 hboth.2 hx
        · exact M.trace_vertex_eq_endpoint_of_mul_nonneg f U kU hab hkU' hq
            (not_lt.mp hcross) hboth hx
  rw [hrestrict, hST, hQU, hAB, ← htraceInter]

/-- A nonnegative affine functional vanishing only at the `i`-th old vertex. -/
noncomputable def vertexSupportCoord (t : M.Triangle) (i : Fin 3) : Plane →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ Plane 1 - M.oppositeCoord t i

@[simp] theorem vertexSupportCoord_vertex (t : M.Triangle) (i j : Fin 3) :
    M.vertexSupportCoord t i (M.position (M.orderedVertex t j)) =
      if i = j then 0 else 1 := by
  change 1 - M.oppositeCoord t i (M.position (M.orderedVertex t j)) = _
  rw [M.oppositeCoord_vertex]
  split_ifs <;> ring

theorem vertexSupportCoord_nonneg_of_mem_parent (t : M.Triangle) (i : Fin 3)
    {x : Plane} (hx : x ∈ convexHull ℝ (M.position '' (t.1 : Set M.Vertex))) :
    0 ≤ M.vertexSupportCoord t i x := by
  have hrange : Set.range (M.position ∘ M.orderedVertex t) =
      M.position '' (t.1 : Set M.Vertex) := by
    rw [Set.range_comp, M.range_orderedVertex t]
  rw [← hrange] at hx
  apply convexHull_min ?_
    ((convex_Ici (0 : ℝ)).affine_preimage (M.vertexSupportCoord t i)) hx
  rintro x ⟨j, rfl⟩
  change 0 ≤ M.vertexSupportCoord t i (M.position (M.orderedVertex t j))
  rw [M.vertexSupportCoord_vertex]
  split_ifs <;> norm_num

theorem parent_inter_vertexSupportCoord_zero (t : M.Triangle) (i : Fin 3) :
    convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) ∩
        {x | M.vertexSupportCoord t i x = 0} =
      {M.position (M.orderedVertex t i)} := by
  let p : Fin 3 → Plane := M.position ∘ M.orderedVertex t
  have hrange : M.position '' (t.1 : Set M.Vertex) =
      ((Finset.univ.image p : Finset Plane) : Set Plane) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.range_comp,
      M.range_orderedVertex t]
  rw [hrange]
  rw [convexHull_inter_affine_zero_of_nonneg]
  · have hfilter : (Finset.univ.image p).filter
        (fun x => M.vertexSupportCoord t i x = 0) = {p i} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨j, hj⟩, hzero⟩
        have hij : i = j := by
          by_contra hij
          have : M.vertexSupportCoord t i (p j) = 1 := by
            change M.vertexSupportCoord t i (M.position (M.orderedVertex t j)) = 1
            rw [M.vertexSupportCoord_vertex, ite_eq_right hij]
          have hzero' : M.vertexSupportCoord t i (p j) = 0 := by
            rw [hj]
            exact hzero
          rw [this] at hzero'
          norm_num at hzero'
        subst j
        exact hj.symm
      · rintro rfl
        refine ⟨⟨i, rfl⟩, ?_⟩
        change M.vertexSupportCoord t i (M.position (M.orderedVertex t i)) = 0
        simp
    rw [hfilter, Finset.coe_singleton, convexHull_singleton]
    simp [p]
  · intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    change 0 ≤ M.vertexSupportCoord t i (M.position (M.orderedVertex t j))
    rw [M.vertexSupportCoord_vertex]
    split_ifs <;> norm_num

theorem old_vertex_mem_child_of_position_mem (t : M.Triangle) (i : Fin 3)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t)
    (hmem : M.position (M.orderedVertex t i) ∈
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        (s : Set (M.RefinedVertex f)))) :
    M.oldRefinedVertex f (M.orderedVertex t i) ∈ s := by
  classical
  let g := M.vertexSupportCoord t i
  let points : Finset Plane := s.image ((↑) : M.RefinedVertex f → Plane)
  have hg : ∀ x ∈ points, 0 ≤ g x := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact M.vertexSupportCoord_nonneg_of_mem_parent t i
      (M.child_vertex_mem_parent f t hs hv)
  have hinter := convexHull_inter_affine_zero_of_nonneg points g hg
  have hcorner : M.position (M.orderedVertex t i) ∈
      convexHull ℝ (points.filter (fun x => g x = 0) : Set Plane) := by
    rw [← hinter]
    refine ⟨?_, ?_⟩
    · simpa [points, Finset.coe_image] using hmem
    · change M.vertexSupportCoord t i (M.position (M.orderedVertex t i)) = 0
      simp
  have hne : (points.filter fun x => g x = 0).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hcorner
    simp at hcorner
  obtain ⟨p, hp⟩ := hne
  have hp' := Finset.mem_filter.mp hp
  obtain ⟨v, hv, hvp⟩ := Finset.mem_image.mp hp'.1
  have hvparent := M.child_vertex_mem_parent f t hs hv
  have hvcorner : (v : Plane) = M.position (M.orderedVertex t i) := by
    have : (v : Plane) ∈
        convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) ∩ {x | g x = 0} := by
      refine ⟨hvparent, ?_⟩
      change g (v : Plane) = 0
      have hpzero := hp'.2
      rw [← hvp] at hpzero
      exact hpzero
    rw [show g = M.vertexSupportCoord t i by rfl,
      M.parent_inter_vertexSupportCoord_zero t i] at this
    simpa using this
  have hvEq : v = M.oldRefinedVertex f (M.orderedVertex t i) := Subtype.ext hvcorner
  rwa [← hvEq]

theorem lineRefinementTriangles_inter_of_parent_inter_card_zero
    (T U : M.Triangle) (hcard : (T.1 ∩ U.1).card = 0)
    {s q : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f T)
    (hq : q ∈ M.localMeshTriangles f U) :
    convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (s : Set (M.RefinedVertex f))) ∩
        convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (q : Set (M.RefinedVertex f))) =
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        ((s ∩ q : Finset (M.RefinedVertex f)) : Set (M.RefinedVertex f))) := by
  have he : T.1 ∩ U.1 = ∅ := Finset.card_eq_zero.mp hcard
  have hparents := M.triangle_inter T.1 T.2 U.1 U.2
  rw [he] at hparents
  have hinter : convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        (s : Set (M.RefinedVertex f))) ∩
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        (q : Set (M.RefinedVertex f))) = ∅ := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxparent : x ∈ convexHull ℝ (M.position '' (T.1 : Set M.Vertex)) ∩
          convexHull ℝ (M.position '' (U.1 : Set M.Vertex)) :=
        ⟨M.convexHull_child_subset_parent f T hs hx.1,
          M.convexHull_child_subset_parent f U hq hx.2⟩
      rw [hparents] at hxparent
      simp at hxparent
    · exact Set.empty_subset _
  have hsq : s ∩ q = ∅ := by
    ext v
    constructor
    · intro hv
      have hv' := Finset.mem_inter.mp hv
      have hvparent : (v : Plane) ∈
          convexHull ℝ (M.position '' (T.1 : Set M.Vertex)) ∩
            convexHull ℝ (M.position '' (U.1 : Set M.Vertex)) :=
        ⟨M.child_vertex_mem_parent f T hs hv'.1,
          M.child_vertex_mem_parent f U hq hv'.2⟩
      rw [hparents] at hvparent
      simp at hvparent
    · intro hv
      simp at hv
  rw [hinter, hsq]
  simp

theorem lineRefinementTriangles_inter_of_parent_inter_card_one
    (T U : M.Triangle) (hcard : (T.1 ∩ U.1).card = 1)
    {s q : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f T)
    (hq : q ∈ M.localMeshTriangles f U) :
    convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (s : Set (M.RefinedVertex f))) ∩
        convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (q : Set (M.RefinedVertex f))) =
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        ((s ∩ q : Finset (M.RefinedVertex f)) : Set (M.RefinedVertex f))) := by
  classical
  obtain ⟨a, hea⟩ := Finset.card_eq_one.mp hcard
  have haT : a ∈ T.1 := Finset.mem_of_mem_inter_left (by rw [hea]; simp)
  have haU : a ∈ U.1 := Finset.mem_of_mem_inter_right (by rw [hea]; simp)
  have harangeT : a ∈ Set.range (M.orderedVertex T) := by
    rw [M.range_orderedVertex T]
    exact haT
  have harangeU : a ∈ Set.range (M.orderedVertex U) := by
    rw [M.range_orderedVertex U]
    exact haU
  obtain ⟨iT, hiT⟩ := harangeT
  obtain ⟨iU, hiU⟩ := harangeU
  have hparents := M.triangle_inter T.1 T.2 U.1 U.2
  rw [hea] at hparents
  simp only [Finset.coe_singleton, Set.image_singleton, convexHull_singleton] at hparents
  apply Set.Subset.antisymm
  · intro x hx
    have hxparent : x ∈ convexHull ℝ (M.position '' (T.1 : Set M.Vertex)) ∩
        convexHull ℝ (M.position '' (U.1 : Set M.Vertex)) :=
      ⟨M.convexHull_child_subset_parent f T hs hx.1,
        M.convexHull_child_subset_parent f U hq hx.2⟩
    rw [hparents] at hxparent
    have hxa : x = M.position a := by simpa using hxparent
    have haS : M.oldRefinedVertex f a ∈ s := by
      rw [← hiT]
      apply M.old_vertex_mem_child_of_position_mem f T iT hs
      simpa [hiT, hxa] using hx.1
    have haQ : M.oldRefinedVertex f a ∈ q := by
      rw [← hiU]
      apply M.old_vertex_mem_child_of_position_mem f U iU hq
      simpa [hiU, hxa] using hx.2
    apply subset_convexHull ℝ
    exact ⟨M.oldRefinedVertex f a, Finset.mem_inter.mpr ⟨haS, haQ⟩,
      by simpa using hxa.symm⟩
  · intro x hx
    exact ⟨convexHull_mono (Set.image_mono Finset.inter_subset_left) hx,
      convexHull_mono (Set.image_mono Finset.inter_subset_right) hx⟩

/-- All maximal triangles of the coherent line refinement. -/
noncomputable def lineRefinementTriangles : Finset (Finset (M.RefinedVertex f)) :=
  Finset.univ.biUnion fun t : M.Triangle => M.localMeshTriangles f t

theorem mem_lineRefinementTriangles_iff {s : Finset (M.RefinedVertex f)} :
    s ∈ M.lineRefinementTriangles f ↔
      ∃ t : M.Triangle, s ∈ M.localMeshTriangles f t := by
  constructor
  · intro hs
    obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp hs
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, ht⟩

theorem card_of_mem_lineRefinementTriangles {s : Finset (M.RefinedVertex f)}
    (hs : s ∈ M.lineRefinementTriangles f) : s.card = 3 := by
  obtain ⟨t, ht⟩ := M.mem_lineRefinementTriangles_iff f |>.mp hs
  exact M.card_of_mem_localMeshTriangles f t ht

theorem affineIndependent_of_mem_lineRefinementTriangles
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.lineRefinementTriangles f) :
    AffineIndependent ℝ fun v : s => (v.1 : Plane) := by
  obtain ⟨t, ht⟩ := M.mem_lineRefinementTriangles_iff f |>.mp hs
  exact M.affineIndependent_of_mem_localMeshTriangles f t ht

theorem lineRefinementTriangles_support :
    (⋃ s ∈ M.lineRefinementTriangles f,
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (s : Set (M.RefinedVertex f)))) =
      M.toPlaneComplex.support := by
  rw [M.toPlaneComplex_support]
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨s, hs, hxs⟩
    obtain ⟨t, hst⟩ := M.mem_lineRefinementTriangles_iff f |>.mp hs
    refine ⟨t.1, t.2, ?_⟩
    rw [← M.localMeshTriangles_support f t]
    exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hst, hxs⟩⟩
  · rintro ⟨t, ht, hxt⟩
    let T : M.Triangle := ⟨t, ht⟩
    rw [← M.localMeshTriangles_support f T] at hxt
    obtain ⟨s, hxt⟩ := Set.mem_iUnion.mp hxt
    obtain ⟨hs, hxs⟩ := Set.mem_iUnion.mp hxt
    exact ⟨s, M.mem_lineRefinementTriangles_iff f |>.mpr ⟨T, hs⟩, hxs⟩

theorem lineRefinementTriangles_inter
    {s q : Finset (M.RefinedVertex f)} (hs : s ∈ M.lineRefinementTriangles f)
    (hq : q ∈ M.lineRefinementTriangles f) :
    convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (s : Set (M.RefinedVertex f))) ∩
        convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (q : Set (M.RefinedVertex f))) =
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        ((s ∩ q : Finset (M.RefinedVertex f)) : Set (M.RefinedVertex f))) := by
  obtain ⟨T, hsT⟩ := M.mem_lineRefinementTriangles_iff f |>.mp hs
  obtain ⟨U, hqU⟩ := M.mem_lineRefinementTriangles_iff f |>.mp hq
  by_cases hTU : T = U
  · subst U
    exact M.localMeshTriangles_inter f T hsT hqU
  · have hle : (T.1 ∩ U.1).card ≤ 3 := by
      calc
        (T.1 ∩ U.1).card ≤ T.1.card := Finset.card_le_card Finset.inter_subset_left
        _ = 3 := M.card_triangle T.1 T.2
    have hne3 : (T.1 ∩ U.1).card ≠ 3 := by
      intro hc
      have hT : T.1 ∩ U.1 = T.1 := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_left (by rw [M.card_triangle T.1 T.2, hc])
      have hU : T.1 ∩ U.1 = U.1 := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_right (by rw [M.card_triangle U.1 U.2, hc])
      apply hTU
      apply Subtype.ext
      exact hT.symm.trans hU
    have hcases : (T.1 ∩ U.1).card = 0 ∨ (T.1 ∩ U.1).card = 1 ∨
        (T.1 ∩ U.1).card = 2 := by omega
    rcases hcases with hc | hc | hc
    · exact M.lineRefinementTriangles_inter_of_parent_inter_card_zero f T U hc hsT hqU
    · exact M.lineRefinementTriangles_inter_of_parent_inter_card_one f T U hc hsT hqU
    · exact M.lineRefinementTriangles_inter_of_parent_inter_card_two f T U hc hsT hqU

/-- Subdivision of a finite triangle mesh by one affine line transverse to its old edges. -/
noncomputable def lineRefinementMesh : TriangleMesh where
  Vertex := M.RefinedVertex f
  position := (↑)
  position_injective := Subtype.val_injective
  triangles := M.lineRefinementTriangles f
  card_triangle := fun _ hs => M.card_of_mem_lineRefinementTriangles f hs
  affineIndependent_triangle := fun _ hs =>
    M.affineIndependent_of_mem_lineRefinementTriangles f hs
  triangle_inter := fun _ hs _ hq => M.lineRefinementTriangles_inter f hs hq

theorem lineRefinementMesh_support :
    (M.lineRefinementMesh f).toPlaneComplex.support = M.toPlaneComplex.support := by
  rw [TriangleMesh.toPlaneComplex_support]
  exact M.lineRefinementTriangles_support f

/-- Cutting every triangle of a mesh by one affine line gives a subdivision of the original
plane complex. -/
theorem lineRefinementMesh_subdivides :
    (M.lineRefinementMesh f).toPlaneComplex.Subdivides M.toPlaneComplex := by
  constructor
  · exact M.lineRefinementMesh_support f
  · intro s hs
    obtain ⟨-, u, hu, hsu⟩ :=
      (M.lineRefinementMesh f).mem_faces_iff.mp hs
    obtain ⟨t, hut⟩ := M.mem_lineRefinementTriangles_iff f |>.mp hu
    refine ⟨t.1, M.mem_faces_iff.mpr ⟨?_, t.1, t.2, subset_rfl⟩, ?_⟩
    · exact Finset.card_pos.mp (by rw [M.card_triangle t.1 t.2]; omega)
    · exact (convexHull_mono (Set.image_mono hsu)).trans
        (M.convexHull_child_subset_parent f t hut)

theorem lineRefinementMesh_isMonochromatic :
    (M.lineRefinementMesh f).IsMonochromatic f := by
  intro s hs
  obtain ⟨t, hst⟩ := M.mem_lineRefinementTriangles_iff f |>.mp hs
  exact M.localMeshTriangles_monochromatic f t s hst

theorem lineRefinementMesh_preserves_monochromatic (g : Plane →ᵃ[ℝ] ℝ)
    (hM : M.IsMonochromatic g) : (M.lineRefinementMesh f).IsMonochromatic g := by
  intro s hs
  obtain ⟨t, hst⟩ := M.mem_lineRefinementTriangles_iff f |>.mp hs
  rcases hM t.1 t.2 with ht | ht
  · left
    intro v hv
    have hvparent := M.child_vertex_mem_parent f t hst hv
    apply convexHull_min ?_ ((convex_Ici (0 : ℝ)).affine_preimage g) hvparent
    rintro x ⟨w, hw, rfl⟩
    exact ht w hw
  · right
    intro v hv
    have hvparent := M.child_vertex_mem_parent f t hst hv
    apply convexHull_min ?_ ((convex_Iic (0 : ℝ)).affine_preimage g) hvparent
    rintro x ⟨w, hw, rfl⟩
    exact ht w hw

/-- Successively subdivide a mesh by a finite list of affine lines. -/
noncomputable def refineByLines : TriangleMesh → List (Plane →ᵃ[ℝ] ℝ) → TriangleMesh
  | M, [] => M
  | M, g :: gs => refineByLines (M.lineRefinementMesh g) gs

theorem refineByLines_support (lines : List (Plane →ᵃ[ℝ] ℝ)) :
    (M.refineByLines lines).toPlaneComplex.support = M.toPlaneComplex.support := by
  induction lines generalizing M with
  | nil => rfl
  | cons g gs ih =>
      rw [refineByLines, ih, lineRefinementMesh_support]

/-- Successive line cuts remain a subdivision of the original mesh. -/
theorem refineByLines_subdivides (lines : List (Plane →ᵃ[ℝ] ℝ)) :
    (M.refineByLines lines).toPlaneComplex.Subdivides M.toPlaneComplex := by
  induction lines generalizing M with
  | nil => exact PlaneComplex.Subdivides.refl M.toPlaneComplex
  | cons g gs ih =>
      change (M.lineRefinementMesh g).refineByLines gs |>.toPlaneComplex |>.Subdivides
        M.toPlaneComplex
      exact (ih (M := M.lineRefinementMesh g)).trans (M.lineRefinementMesh_subdivides g)

theorem refineByLines_preserves_monochromatic
    (lines : List (Plane →ᵃ[ℝ] ℝ)) (g : Plane →ᵃ[ℝ] ℝ)
    (hM : M.IsMonochromatic g) : (M.refineByLines lines).IsMonochromatic g := by
  induction lines generalizing M with
  | nil => exact hM
  | cons f fs ih =>
      exact ih (M := M.lineRefinementMesh f)
        (M.lineRefinementMesh_preserves_monochromatic f g hM)

theorem refineByLines_isMonochromatic_of_mem
    (lines : List (Plane →ᵃ[ℝ] ℝ)) {g : Plane →ᵃ[ℝ] ℝ} (hg : g ∈ lines) :
    (M.refineByLines lines).IsMonochromatic g := by
  induction lines generalizing M with
  | nil => simp at hg
  | cons h hs ih =>
      simp only [List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact (M.lineRefinementMesh g).refineByLines_preserves_monochromatic hs g
          (M.lineRefinementMesh_isMonochromatic g)
      · exact ih (M := M.lineRefinementMesh h) hg

end TriangleMesh

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end r78_classification02_block_04
/- END ClassificationOfSurfaces.Moise.LineSubdivision -/
