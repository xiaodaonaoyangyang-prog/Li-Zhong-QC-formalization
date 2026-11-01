/- Derived from https://github.com/mccorvie/classification-of-surfaces (commit e3c7230fe78d7b056a415d9ecae6f77887046b32),
   Apache License 2.0. Modified for LiZhongQC: bundled with other upstream files, imports renamed,
   local proof repairs. See NOTICE.Classification and LICENSE.Apache-2.0 in this directory. -/
/- Classification layer 01: pinned sources; see BUNDLE_MAP.json and licenses/. -/
import Mathlib.Analysis.Complex.Circle
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Setoid.Basic
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.UnitInterval
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Topology.LocallyFinite

/- BEGIN ClassificationOfSurfaces.LeanEval.ChallengeDeps | cc1ea7b804f0b6915b0809c05a9af9435cc24067bdba31c2e743736375135b6e -/
section r78_classification01_block_01
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
DO NOT EDIT OR MODIFY

This is the problem definition vendored from
https://github.com/leanprover/lean-eval
with the sparse checkout
generated/topological_classification_of_surfaces


The final submitted solution will live at
https://github.com/leanprover/lean-eval
which is a pristine verbatim clone of
leanprover/lean-eval/generated/topological_classification_of_surfaces

-/

/-!
Benchmark statements for topological classification of compact connected surfaces with boundary.

The representative surface in each homeomorphism class is obtained by
gluing certain arcs in the boundary of the unit disc.

Reference: Jean Gallier & Dianna Xu, *A Guide to the Classification Theorem for Compact Surfaces*,
Definition 6.5, Lemma 6.1, Theorem 6.1.
https://www.cis.upenn.edu/~jean/surfclassif-root.pdf
-/

namespace Complex

/-- The closed unit disc in the complex plane. -/
abbrev ClosedUnitDisc : Type := Metric.closedBall (0 : ℂ) 1

/-- The boundary point exp(2πir) on the boundary of the closed unit disc in the complex plane. -/
noncomputable def ClosedUnitDisc.bdyPtOfReal (r : ℝ) : ClosedUnitDisc :=
  ⟨r.fourierChar, r.fourierChar.2.le⟩

end Complex

namespace LeanEval.Topology.ClassificationOfSurfaces

open Complex Set

/-- The representative orientable surface homeomorphic to a closed orientable genus `p`
surface with `n` discs removed, obtained by identifying the boundary of a disc in the pattern
`a₁b₁a₁⁻¹b₁⁻¹⋯aₚbₚaₚ⁻¹bₚ⁻¹c₁h₁c₁⁻¹⋯cₙhₙcₙ⁻¹`. -/
inductive OrientableRel (p n : ℕ) : ClosedUnitDisc → ClosedUnitDisc → Prop
  | a (x : Icc (0 : ℝ) 1) (i : Fin p) : OrientableRel p n
      (.bdyPtOfReal <| (4 * i + x) / (4 * p + 3 * n))
      (.bdyPtOfReal <| (4 * i + 3 - x) / (4 * p + 3 * n))
  | b (x : Icc (0 : ℝ) 1) (i : Fin p) : OrientableRel p n
      (.bdyPtOfReal <| (4 * i + 1 + x) / (4 * p + 3 * n))
      (.bdyPtOfReal <| (4 * i + 4 - x) / (4 * p + 3 * n))
  | c (x : Icc (0 : ℝ) 1) (i : Fin n) : OrientableRel p n
      (.bdyPtOfReal <| - (3 * i + x) / (4 * p + 3 * n))
      (.bdyPtOfReal <| - (3 * i + 3 - x) / (4 * p + 3 * n))

/-- The representative non-orientable surface homeomorphic to a direct sum of `p` projective
planes with `n` discs removed, obtained by identifying the boundary of a disc in the pattern
`a₁a₁⋯aₚaₚc₁h₁c₁⁻¹⋯cₙhₙcₙ⁻¹`. -/
inductive NonOrientableRel (p n : ℕ) : ClosedUnitDisc → ClosedUnitDisc → Prop
  | a (x : Icc (0 : ℝ) 1) (i : Fin p) : NonOrientableRel p n
      (.bdyPtOfReal <| (2 * i + x) / (2 * p + 3 * n))
      (.bdyPtOfReal <| (2 * i + 1 + x) / (2 * p + 3 * n))
  | c (x : Icc (0 : ℝ) 1) (i : Fin n) : NonOrientableRel p n
      (.bdyPtOfReal <| -(3 * i + x) / (2 * p + 3 * n))
      (.bdyPtOfReal <| -(3 * i + 3 - x) / (2 * p + 3 * n))



end LeanEval.Topology.ClassificationOfSurfaces
end r78_classification01_block_01
/- END ClassificationOfSurfaces.LeanEval.ChallengeDeps -/

/- BEGIN ClassificationOfSurfaces.Surface | a79e0bf519f6cb767fcaffa98db76e810a2313f74117d235f5304c47cbf2f951 -/
section r78_classification01_block_02
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Surface hypotheses and boundary interface

This file records the manifold assumptions used by the Lean Eval target.
-/

open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-- Topological invariance of the boundary stratum for C0 half-space charts: a mathlib
manifold-boundary point is sent by every preferred half-space chart containing it to the frontier
of that chart's extended target.

The unconditional C0 instance is proved in `Moise/BoundaryInvariant.lean`; the interface remains
here so low-level surface declarations do not import the invariance-of-domain development. -/
class ChartBoundaryInvariant (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S] where
  chartAt_extend_mem_frontier_target_of_boundary :
    ∀ (x : S) {y : S},
      y ∈ (chartAt (EuclideanHalfSpace 2) x).source →
      y ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S →
      (chartAt (EuclideanHalfSpace 2) x).extend (modelWithCornersEuclideanHalfSpace 2) y ∈
        frontier
          (((chartAt (EuclideanHalfSpace 2) x).extend
            (modelWithCornersEuclideanHalfSpace 2)).target)

instance chartBoundaryInvariant_of_contMDiff
    (S : Type*) [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 S] :
    ChartBoundaryInvariant S where
  chartAt_extend_mem_frontier_target_of_boundary := by
    intro x y hySource hyBoundary
    let I := modelWithCornersEuclideanHalfSpace 2
    exact
      (I.isBoundaryPoint_iff_of_mem_atlas (M := S) (n := 1) (by norm_num)
        (chart_mem_atlas (EuclideanHalfSpace 2) x) hySource).mp hyBoundary

/-- The topological hypotheses in the Lean Eval statement.

Most theorem statements should keep using the typeclass hypotheses directly. This wrapper is useful
for blueprint references and for APIs that want to pass the full Eval-surface bundle as data. -/
structure EvalSurface (S : Type*) [TopologicalSpace S] where
  t2 : T2Space S
  connected : ConnectedSpace S
  compact : CompactSpace S
  /-- The `charted` declaration. -/
  charted : ChartedSpace (EuclideanHalfSpace 2) S
  manifold : IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S

section EvalHypotheses

variable (S : Type*) [TopologicalSpace S]
variable [T2Space S] [ConnectedSpace S] [CompactSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]

/-- Package the active typeclass hypotheses as an `EvalSurface`. -/
def evalSurface : EvalSurface S where
  t2 := inferInstance
  connected := inferInstance
  compact := inferInstance
  charted := inferInstance
  manifold := inferInstance

/-- Marker theorem packaging the active Eval assumptions. -/
theorem eval_surface_hypotheses : Nonempty (EvalSurface S) :=
  ⟨evalSurface S⟩

end EvalHypotheses

end ClassificationOfSurfaces
end Topology
end LeanEval
end r78_classification01_block_02
/- END ClassificationOfSurfaces.Surface -/

/- BEGIN ClassificationOfSurfaces.Moise.GeometricTriangulation | 0fafc52d970495214c5f7f7f4961d13d0cf21bcc325e83d00b3f32c1aa2418d4 -/
section r78_classification01_block_03
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Geometric triangulations

The faithful statement of "the space `S` admits a finite triangulation": `S` is homeomorphic to
the geometric realization of a finite two-dimensional simplicial complex.

The realization is concrete: for a finite vertex type `V` and a finite family `F` of faces
(3-element vertex sets), `GeometricRealization V F` is the subset of the standard simplex
`stdSimplex ℝ V` consisting of points supported on some face.  This is the classical geometric
realization by barycentric coordinates; it is a compact Hausdorff polyhedron by construction, so
the definition cannot be satisfied by junk witnesses (`Empty` face types, arbitrary `realization`
fields, and so on): the homeomorphism type pins `S` to an actual finite union of geometric
2-simplexes.

Semantic anchors (see `Moise/Countermodels.lean` and the Definition Faithfulness section of
`docs/AUTOFORMALIZATION_GUIDE.md`):

* must-imply: `GeometricTriangulation.compactSpace`, `GeometricTriangulation.t2Space`;
* positive example: the standard 2-simplex triangulates itself;
* non-example: `ℝ` and `ℚ` admit no geometric triangulation (they are not compact).
-/

/-- A finite closed cover of a preconnected set has a connected intersection graph.

This is the closed-cover counterpart of `IsPreconnected.transGen_of_iUnion`, whose open-cover
hypothesis is not available for the closed simplexes of a geometric realization. -/
theorem IsPreconnected.transGen_of_finite_iUnion
    {α ι : Type*} [TopologicalSpace α] [Finite ι] {s : ι → Set α}
    (hs : IsPreconnected (⋃ n, s n)) (hs' : ∀ i, IsClosed (s i))
    (i j : ι) (hi : (s i).Nonempty) (hj : (s j).Nonempty) :
    Relation.TransGen (fun a b ↦ (s a ∩ s b).Nonempty) i j := by
  by_contra hij
  let R := fun a b : ι ↦ (s a ∩ s b).Nonempty
  let S : Set ι := {k | Relation.TransGen R i k}
  let U : Set α := ⋃ k ∈ S, s k
  let V : Set α := ⋃ k ∈ Sᶜ, s k
  have hUclosed : IsClosed U := by
    exact Set.toFinite S |>.isClosed_biUnion fun k _ ↦ hs' k
  have hVclosed : IsClosed V := by
    exact Set.toFinite Sᶜ |>.isClosed_biUnion fun k _ ↦ hs' k
  have hsplit : (⋃ n, s n) = U ∪ V := iSup_split s (· ∈ S)
  have hUV : Disjoint U V := by
    rw [Set.disjoint_left]
    intro x hxU hxV
    simp only [Set.mem_iUnion, exists_prop, Set.mem_compl_iff, U, V] at hxU hxV
    obtain ⟨k, hk, hxk⟩ := hxU
    obtain ⟨l, hl, hxl⟩ := hxV
    exact hl (hk.tail ⟨x, hxk, hxl⟩)
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb⟩ := hj
  have hiS : i ∈ S := Relation.TransGen.single ⟨a, ha, ha⟩
  have haU : a ∈ U := Set.mem_iUnion₂_of_mem hiS ha
  have hjS : j ∉ S := hij
  have hbV : b ∈ V := Set.mem_iUnion₂_of_mem hjS hb
  have hcover : (⋃ n, s n) ⊆ Vᶜ ∪ Uᶜ := by
    intro x hx
    rcases hsplit.le hx with hxU | hxV
    · exact Or.inl (fun hxV ↦ Set.disjoint_left.mp hUV hxU hxV)
    · exact Or.inr (fun hxU ↦ Set.disjoint_left.mp hUV hxU hxV)
  have hUne : ((⋃ n, s n) ∩ Vᶜ).Nonempty :=
    ⟨a, Set.mem_iUnion_of_mem i ha,
      fun haV ↦ Set.disjoint_left.mp hUV haU haV⟩
  have hVne : ((⋃ n, s n) ∩ Uᶜ).Nonempty :=
    ⟨b, Set.mem_iUnion_of_mem j hb,
      fun hbU ↦ Set.disjoint_left.mp hUV hbU hbV⟩
  obtain ⟨x, hxall, hxV, hxU⟩ := hs Vᶜ Uᶜ
    hVclosed.isOpen_compl hUclosed.isOpen_compl hcover hUne hVne
  rcases hsplit.le hxall with hxU' | hxV'
  · exact hxU hxU'
  · exact hxV hxV'

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-- The geometric realization of a finite family `F` of faces on a finite vertex type `V`: the
points of the standard simplex on `V` whose support lies inside some face of `F`.  For a face `t`
this carves out the geometric simplex spanned by `t`, so the realization is the finite union of
the geometric simplexes of `F`, glued along shared barycentric-coordinate faces. -/
def GeometricRealization (V : Type*) [Fintype V] (F : Finset (Finset V)) : Set (V → ℝ) :=
  {x | x ∈ stdSimplex ℝ V ∧ ∃ t ∈ F, ∀ v ∉ t, x v = 0}

/-- The geometric simplex carried by one finite set of vertices. -/
def GeometricFace (V : Type*) [Fintype V] (t : Finset V) : Set (V → ℝ) :=
  {x | x ∈ stdSimplex ℝ V ∧ ∀ v ∉ t, x v = 0}

namespace GeometricFace

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Semantic anchor: two barycentric faces meet in exactly their common face. -/
theorem inter (t u : Finset V) :
    GeometricFace V t ∩ GeometricFace V u = GeometricFace V (t ∩ u) := by
  ext x
  constructor
  · rintro ⟨⟨hx, ht⟩, _, hu⟩
    refine ⟨hx, ?_⟩
    intro v hv
    rw [Finset.mem_inter, not_and_or] at hv
    rcases hv with hv | hv
    · exact ht v hv
    · exact hu v hv
  · rintro ⟨hx, htu⟩
    refine ⟨⟨hx, ?_⟩, hx, ?_⟩
    · intro v hv
      exact htu v (fun hmem => hv (Finset.mem_inter.mp hmem).1)
    · intro v hv
      exact htu v (fun hmem => hv (Finset.mem_inter.mp hmem).2)

omit [DecidableEq V] in
/-- A barycentric face is nonempty exactly when it has a vertex. -/
theorem nonempty_iff (t : Finset V) :
    (GeometricFace V t).Nonempty ↔ t.Nonempty := by
  classical
  constructor
  · rintro ⟨x, hxstd, hxsupp⟩
    by_contra ht
    have ht' : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    have hxzero : x = 0 := by
      funext v
      exact hxsupp v (by simp [ht'])
    rw [hxzero] at hxstd
    norm_num [stdSimplex] at hxstd
  · rintro ⟨v, hv⟩
    refine ⟨Pi.single v 1, single_mem_stdSimplex ℝ v, ?_⟩
    intro w hw
    by_cases hwv : w = v
    · subst w
      exact (hw hv).elim
    · simp [hwv]

omit [DecidableEq V] in
/-- Each barycentric face is closed in the ambient coordinate space. -/
theorem isClosed (t : Finset V) :
    IsClosed (GeometricFace V t) := by
  classical
  have hrepr : GeometricFace V t =
      stdSimplex ℝ V ∩ ⋂ v ∈ {v : V | v ∉ t}, {x : V → ℝ | x v = 0} := by
    ext x
    simp [GeometricFace]
  rw [hrepr]
  exact (isClosed_stdSimplex ℝ V).inter
    (isClosed_biInter fun v _ ↦ isClosed_eq (continuous_apply v) continuous_const)

end GeometricFace

namespace GeometricRealization

variable {V : Type*} [Fintype V] {F : Finset (Finset V)}

/-- The global realization is literally the finite union of its geometric faces. -/
theorem eq_biUnion_geometricFace :
    GeometricRealization V F = ⋃ t ∈ F, GeometricFace V t := by
  ext x
  simp [GeometricRealization, GeometricFace]

theorem subset_stdSimplex : GeometricRealization V F ⊆ stdSimplex ℝ V :=
  fun _ hx => hx.1

theorem isClosed : IsClosed (GeometricRealization V F) := by
  have hrepr : GeometricRealization V F =
      stdSimplex ℝ V ∩ ⋃ t ∈ F, {x : V → ℝ | ∀ v ∉ t, x v = 0} := by
    ext x
    simp [GeometricRealization, Set.mem_iUnion]
  rw [hrepr]
  refine (isClosed_stdSimplex ℝ V).inter ?_
  refine Set.Finite.isClosed_biUnion F.finite_toSet ?_
  intro t _
  have hInter : {x : V → ℝ | ∀ v ∉ t, x v = 0} =
      ⋂ v ∈ {v : V | v ∉ t}, {x : V → ℝ | x v = 0} := by
    ext x
    simp
  rw [hInter]
  exact isClosed_biInter fun v _ => isClosed_eq (continuous_apply v) continuous_const

theorem isCompact : IsCompact (GeometricRealization V F) :=
  (isCompact_stdSimplex ℝ V).of_isClosed_subset isClosed subset_stdSimplex

instance : CompactSpace (GeometricRealization V F) :=
  isCompact_iff_compactSpace.mp isCompact

/-- The realization of the empty face family is empty. -/
theorem eq_empty_of_no_faces : GeometricRealization V (∅ : Finset (Finset V)) = ∅ := by
  ext x
  simp [GeometricRealization]

instance : IsEmpty (GeometricRealization V (∅ : Finset (Finset V))) :=
  Set.isEmpty_coe_sort.mpr eq_empty_of_no_faces

end GeometricRealization

namespace TriangleFamily

variable {Vertex : Type*} [DecidableEq Vertex]

/-- A listed maximal face of a finite triangle family. -/
abbrev Face (faces : Finset (Finset Vertex)) :=
  {t : Finset Vertex // t ∈ faces}

/-- The two-vertex faces occurring in a finite triangle family. -/
def edges (faces : Finset (Finset Vertex)) : Finset (Finset Vertex) :=
  faces.biUnion fun t => t.powersetCard 2

/-- Two listed triangles are dual-adjacent when they share a two-vertex face. -/
def FaceAdjacent (faces : Finset (Finset Vertex)) (f g : Face faces) : Prop :=
  ∃ e : Finset Vertex, e.card = 2 ∧ e ⊆ f.1 ∧ e ⊆ g.1

/-- Two listed triangles are adjacent at `v` when they share a two-vertex face containing `v`.

Unlike `FaceAdjacent`, this relation remembers the vertex star in which the adjacency step
occurs. -/
def FaceAdjacentAtVertex (faces : Finset (Finset Vertex)) (v : Vertex)
    (f g : Face faces) : Prop :=
  ∃ e : Finset Vertex, e.card = 2 ∧ v ∈ e ∧ e ⊆ f.1 ∧ e ⊆ g.1

/-- Two listed triangles meet when their vertex sets have a common vertex. -/
def FaceIntersects (faces : Finset (Finset Vertex)) (f g : Face faces) : Prop :=
  (f.1 ∩ g.1).Nonempty

omit [DecidableEq Vertex] in
theorem faceAdjacent_symm {faces : Finset (Finset Vertex)} {f g : Face faces}
    (h : FaceAdjacent faces f g) : FaceAdjacent faces g f := by
  rcases h with ⟨e, hecard, hef, heg⟩
  exact ⟨e, hecard, heg, hef⟩

omit [DecidableEq Vertex] in
/-- Fixed-vertex face adjacency is symmetric. -/
theorem faceAdjacentAtVertex_symm
    {faces : Finset (Finset Vertex)} {v : Vertex} {f g : Face faces}
    (h : FaceAdjacentAtVertex faces v f g) :
    FaceAdjacentAtVertex faces v g f := by
  rcases h with ⟨e, hecard, hve, hef, heg⟩
  exact ⟨e, hecard, hve, heg, hef⟩

omit [DecidableEq Vertex] in
/-- A fixed-vertex adjacency step is an ordinary dual-adjacency step. -/
theorem faceAdjacent_of_faceAdjacentAtVertex
    {faces : Finset (Finset Vertex)} {v : Vertex} {f g : Face faces}
    (h : FaceAdjacentAtVertex faces v f g) :
    FaceAdjacent faces f g := by
  rcases h with ⟨e, hecard, _hve, hef, heg⟩
  exact ⟨e, hecard, hef, heg⟩

omit [DecidableEq Vertex] in
/-- The left endpoint of a fixed-vertex adjacency step contains the fixed vertex. -/
theorem mem_left_of_faceAdjacentAtVertex
    {faces : Finset (Finset Vertex)} {v : Vertex} {f g : Face faces}
    (h : FaceAdjacentAtVertex faces v f g) : v ∈ f.1 := by
  rcases h with ⟨e, _hecard, hve, hef, _heg⟩
  exact hef hve

omit [DecidableEq Vertex] in
/-- The right endpoint of a fixed-vertex adjacency step contains the fixed vertex. -/
theorem mem_right_of_faceAdjacentAtVertex
    {faces : Finset (Finset Vertex)} {v : Vertex} {f g : Face faces}
    (h : FaceAdjacentAtVertex faces v f g) : v ∈ g.1 := by
  rcases h with ⟨e, _hecard, hve, _hef, heg⟩
  exact heg hve

/-- Faces in different dual components share at most one vertex. -/
theorem card_inter_le_one_of_not_faceAdjacent
    {faces : Finset (Finset Vertex)} {f g : Face faces}
    (h : ¬ FaceAdjacent faces f g) :
    (f.1 ∩ g.1).card ≤ 1 := by
  by_contra hcard
  have htwo : 2 ≤ (f.1 ∩ g.1).card := by omega
  obtain ⟨e, heSub, heCard⟩ := Finset.exists_subset_card_eq htwo
  apply h
  exact ⟨e, heCard, heSub.trans Finset.inter_subset_left,
    heSub.trans Finset.inter_subset_right⟩

omit [DecidableEq Vertex] in
theorem reflTransGen_faceAdjacent_symm {faces : Finset (Finset Vertex)}
    {f g : Face faces} (h : Relation.ReflTransGen (FaceAdjacent faces) f g) :
    Relation.ReflTransGen (FaceAdjacent faces) g f := by
  apply Relation.ReflTransGen.mono (fun _ _ hab => faceAdjacent_symm hab)
  exact h.swap

omit [DecidableEq Vertex] in
/-- A chain of fixed-vertex adjacency steps is an ordinary dual-adjacency chain. -/
theorem reflTransGen_faceAdjacent_of_faceAdjacentAtVertex
    {faces : Finset (Finset Vertex)} {v : Vertex} {f g : Face faces}
    (h : Relation.ReflTransGen (FaceAdjacentAtVertex faces v) f g) :
    Relation.ReflTransGen (FaceAdjacent faces) f g := by
  apply Relation.ReflTransGen.mono
    (fun _ _ hab => faceAdjacent_of_faceAdjacentAtVertex hab)
  exact h

omit [DecidableEq Vertex] in
/-- Fixed-vertex adjacency chains can be traversed in reverse. -/
theorem reflTransGen_faceAdjacentAtVertex_symm
    {faces : Finset (Finset Vertex)} {v : Vertex} {f g : Face faces}
    (h : Relation.ReflTransGen (FaceAdjacentAtVertex faces v) f g) :
    Relation.ReflTransGen (FaceAdjacentAtVertex faces v) g f := by
  apply Relation.ReflTransGen.mono
    (fun _ _ hab => faceAdjacentAtVertex_symm hab)
  exact h.swap

omit [DecidableEq Vertex] in
/-- Every endpoint reached from a face containing `v` through fixed-vertex adjacency still
contains `v`. -/
theorem mem_of_reflTransGen_faceAdjacentAtVertex
    {faces : Finset (Finset Vertex)} {v : Vertex} {f g : Face faces}
    (hvf : v ∈ f.1)
    (h : Relation.ReflTransGen (FaceAdjacentAtVertex faces v) f g) :
    v ∈ g.1 := by
  induction h with
  | refl => exact hvf
  | tail _h hstep _ih => exact mem_right_of_faceAdjacentAtVertex hstep

/-- Every two listed triangles are connected by a finite chain of shared edges. -/
def IsDualConnected (faces : Finset (Finset Vertex)) : Prop :=
  ∀ f g : Face faces, Relation.ReflTransGen (FaceAdjacent faces) f g

/-- Every pair of triangles incident to one vertex can be joined through shared edges.

For a triangulated surface this is the local connectedness assertion carried by the link of the
vertex. This compatibility predicate does not require its intermediate faces to remain incident
to that vertex; use `IsStrongVertexStarConnected` when that fixed-star invariant is needed. -/
def IsVertexStarConnected (faces : Finset (Finset Vertex)) : Prop :=
  ∀ (v : Vertex) (f g : Face faces), v ∈ f.1 → v ∈ g.1 →
    Relation.ReflTransGen (FaceAdjacent faces) f g

/-- Every pair of triangles incident to one vertex can be joined by a chain whose every adjacency
step shares an edge containing that same vertex. -/
def IsStrongVertexStarConnected (faces : Finset (Finset Vertex)) : Prop :=
  ∀ (v : Vertex) (f g : Face faces), v ∈ f.1 → v ∈ g.1 →
    Relation.ReflTransGen (FaceAdjacentAtVertex faces v) f g

omit [DecidableEq Vertex] in
/-- Strong fixed-star connectivity implies the legacy vertex-star connectivity predicate. -/
theorem IsStrongVertexStarConnected.isVertexStarConnected
    {faces : Finset (Finset Vertex)}
    (hstar : IsStrongVertexStarConnected faces) :
    IsVertexStarConnected faces := by
  intro v f g hvf hvg
  exact reflTransGen_faceAdjacent_of_faceAdjacentAtVertex
    (hstar v f g hvf hvg)

section Geometric

variable [Fintype Vertex]

/-- Geometric simplexes intersect exactly when their combinatorial faces share a vertex. -/
theorem geometricFace_inter_nonempty_iff
    {faces : Finset (Finset Vertex)} (f g : Face faces) :
    (GeometricFace Vertex f.1 ∩ GeometricFace Vertex g.1).Nonempty ↔
      FaceIntersects faces f g := by
  rw [GeometricFace.inter]
  simpa [FaceIntersects] using GeometricFace.nonempty_iff (f.1 ∩ g.1)

/-- Connectedness of a finite geometric realization connects all maximal faces through
nonempty intersections. -/
theorem isFaceIntersectionConnected_of_isPreconnected
    {faces : Finset (Finset Vertex)}
    (hface : ∀ f : Face faces, f.1.Nonempty)
    (hpre : IsPreconnected (GeometricRealization Vertex faces)) :
    ∀ f g : Face faces,
      Relation.ReflTransGen (FaceIntersects faces) f g := by
  have hunion :
      GeometricRealization Vertex faces =
        ⋃ f : Face faces, GeometricFace Vertex f.1 := by
    ext x
    simp [GeometricRealization, GeometricFace]
  have hpre' :
      IsPreconnected (⋃ f : Face faces, GeometricFace Vertex f.1) := by
    rw [← hunion]
    exact hpre
  intro f g
  have hchain := hpre'.transGen_of_finite_iUnion
    (fun f : Face faces ↦ GeometricFace.isClosed f.1) f g
    ((GeometricFace.nonempty_iff f.1).2 (hface f))
    ((GeometricFace.nonempty_iff g.1).2 (hface g))
  exact (Relation.ReflTransGen.mono
    (r := fun a b : Face faces ↦
      (GeometricFace Vertex a.1 ∩ GeometricFace Vertex b.1).Nonempty)
    (p := FaceIntersects faces)
    (fun a b h ↦ (geometricFace_inter_nonempty_iff a b).mp h))
    f g hchain.to_reflTransGen

end Geometric

/-- Connected vertex stars upgrade connectivity through arbitrary face intersections to
connectivity through shared edges. -/
theorem IsVertexStarConnected.isDualConnected
    {faces : Finset (Finset Vertex)}
    (hstar : IsVertexStarConnected faces)
    (hinter : ∀ f g : Face faces,
      Relation.ReflTransGen (FaceIntersects faces) f g) :
    IsDualConnected faces := by
  intro f g
  exact (Relation.reflTransGen_closed
    (r := FaceIntersects faces) (p := FaceAdjacent faces)
    (fun a b hab ↦ by
      rcases hab with ⟨v, hv⟩
      exact hstar v a b (Finset.mem_inter.mp hv).1
        (Finset.mem_inter.mp hv).2)) f g (hinter f g)
/-- Regard a face of a subfamily as a face of a larger family. -/
def faceOfSubset {faces faces' : Finset (Finset Vertex)} (h : faces ⊆ faces') :
    Face faces → Face faces' :=
  fun f => ⟨f.1, h f.2⟩

omit [DecidableEq Vertex] in
@[simp]
theorem faceOfSubset_val {faces faces' : Finset (Finset Vertex)} (h : faces ⊆ faces')
    (f : Face faces) : (faceOfSubset h f).1 = f.1 :=
  rfl

omit [DecidableEq Vertex] in
theorem faceAdjacent_faceOfSubset {faces faces' : Finset (Finset Vertex)}
    (h : faces ⊆ faces') {f g : Face faces} (hfg : FaceAdjacent faces f g) :
    FaceAdjacent faces' (faceOfSubset h f) (faceOfSubset h g) := by
  rcases hfg with ⟨e, hecard, hef, heg⟩
  exact ⟨e, hecard, hef, heg⟩

omit [DecidableEq Vertex] in
theorem reflTransGen_faceAdjacent_faceOfSubset
    {faces faces' : Finset (Finset Vertex)} (h : faces ⊆ faces') {f g : Face faces}
    (hfg : Relation.ReflTransGen (FaceAdjacent faces) f g) :
    Relation.ReflTransGen (FaceAdjacent faces') (faceOfSubset h f) (faceOfSubset h g) := by
  induction hfg with
  | refl => exact Relation.ReflTransGen.refl
  | tail _hab hbc ih =>
      exact ih.tail (faceAdjacent_faceOfSubset h hbc)

/-- Two dual-connected face families with a cross-adjacent pair have dual-connected union. -/
theorem isDualConnected_union {left right : Finset (Finset Vertex)}
    (hleft : IsDualConnected left) (hright : IsDualConnected right)
    (fleft : Face left) (fright : Face right)
    (hcross : FaceAdjacent (left ∪ right)
      (faceOfSubset Finset.subset_union_left fleft)
      (faceOfSubset Finset.subset_union_right fright)) :
    IsDualConnected (left ∪ right) := by
  intro f g
  rcases Finset.mem_union.mp f.2 with hf | hf <;>
    rcases Finset.mem_union.mp g.2 with hg | hg
  · let f' : Face left := ⟨f.1, hf⟩
    let g' : Face left := ⟨g.1, hg⟩
    have hpath := reflTransGen_faceAdjacent_faceOfSubset (faces' := left ∪ right)
      Finset.subset_union_left (hleft f' g')
    simpa [f', g', faceOfSubset] using hpath
  · let f' : Face left := ⟨f.1, hf⟩
    let g' : Face right := ⟨g.1, hg⟩
    have hfirst := reflTransGen_faceAdjacent_faceOfSubset (faces' := left ∪ right)
      Finset.subset_union_left (hleft f' fleft)
    have hlast := reflTransGen_faceAdjacent_faceOfSubset (faces' := left ∪ right)
      Finset.subset_union_right (hright fright g')
    have hpath := (hfirst.tail hcross).trans hlast
    simpa [f', g', faceOfSubset] using hpath
  · let f' : Face right := ⟨f.1, hf⟩
    let g' : Face left := ⟨g.1, hg⟩
    have hfirst := reflTransGen_faceAdjacent_faceOfSubset (faces' := left ∪ right)
      Finset.subset_union_right (hright f' fright)
    have hlast := reflTransGen_faceAdjacent_faceOfSubset (faces' := left ∪ right)
      Finset.subset_union_left (hleft fleft g')
    have hpath := (hfirst.tail (faceAdjacent_symm hcross)).trans hlast
    simpa [f', g', faceOfSubset] using hpath
  · let f' : Face right := ⟨f.1, hf⟩
    let g' : Face right := ⟨g.1, hg⟩
    have hpath := reflTransGen_faceAdjacent_faceOfSubset (faces' := left ∪ right)
      Finset.subset_union_right (hright f' g')
    simpa [f', g', faceOfSubset] using hpath

/-- A face from each family shares a genuine two-vertex edge in the union family. -/
def HasCrossEdge (left right : Finset (Finset Vertex)) : Prop :=
  ∃ (fleft : Face left) (fright : Face right),
      FaceAdjacent (left ∪ right)
        (faceOfSubset Finset.subset_union_left fleft)
        (faceOfSubset Finset.subset_union_right fright)

/-- Two dual-connected face families with a shared cross-edge have dual-connected union. -/
theorem isDualConnected_union_of_hasCrossEdge
    {left right : Finset (Finset Vertex)}
    (hleft : IsDualConnected left) (hright : IsDualConnected right)
    (hcross : HasCrossEdge left right) :
    IsDualConnected (left ∪ right) := by
  rcases hcross with ⟨fleft, fright, hcross⟩
  exact isDualConnected_union hleft hright fleft fright hcross

omit [DecidableEq Vertex] in
/-- A face family consisting of one triangle is dual-connected. -/
theorem isDualConnected_singleton (face : Finset Vertex) :
    IsDualConnected {face} := by
  intro f g
  have hfg : f = g := by
    apply Subtype.ext
    exact (Finset.mem_singleton.mp f.2).trans (Finset.mem_singleton.mp g.2).symm
  subst g
  exact Relation.ReflTransGen.refl

/-- Adding a triangle along an edge of a dual-connected family preserves dual connectivity. -/
theorem isDualConnected_insert {faces : Finset (Finset Vertex)}
    (hfaces : IsDualConnected faces) (face : Finset Vertex) (anchor : Face faces)
    (hcross : FaceAdjacent (insert face faces)
      ⟨face, Finset.mem_insert_self face faces⟩
      (faceOfSubset (Finset.subset_insert face faces) anchor)) :
    IsDualConnected (insert face faces) := by
  apply isDualConnected_union_of_hasCrossEdge
    (isDualConnected_singleton face) hfaces
  refine ⟨⟨face, Finset.mem_singleton_self face⟩, anchor, ?_⟩
  simpa [faceOfSubset] using hcross

/-- Strong fixed-star connectivity supplies dual connectivity whenever the face-intersection
graph is connected. -/
theorem IsStrongVertexStarConnected.isDualConnected
    {faces : Finset (Finset Vertex)}
    (hstar : IsStrongVertexStarConnected faces)
    (hinter : ∀ f g : Face faces,
      Relation.ReflTransGen (FaceIntersects faces) f g) :
    IsDualConnected faces :=
  hstar.isVertexStarConnected.isDualConnected hinter

/-- Incidence conditions making a finite family of triangles a connected pseudomanifold with
boundary: it is nonempty, no edge has valence above two, and its dual graph is connected. -/
structure SurfaceIncidence (faces : Finset (Finset Vertex)) : Prop where
  faces_nonempty : faces.Nonempty
  edge_valence_le_two :
    ∀ e ∈ edges faces, (faces.filter fun t => e ⊆ t).card ≤ 2
  dual_connected : IsDualConnected faces

end TriangleFamily

/-- A finite triangulation of the topological space `S` by geometric 2-simplexes: a finite vertex
type, a finite family of 3-element faces, and a homeomorphism from the geometric realization of
that family onto `S`.

There is no separate `realization` field to weaken: the realization is computed from the
combinatorial data, so a `GeometricTriangulation S` exists only when `S` really is a finite
two-dimensional polyhedron. -/
structure GeometricTriangulation (S : Type*) [TopologicalSpace S] where
  /-- The (finite) vertex type of the triangulation. -/
  Vertex : Type
  /-- The vertex type is finite. -/
  [vertexFintype : Fintype Vertex]
  /-- Vertices have decidable equality. -/
  [vertexDecidableEq : DecidableEq Vertex]
  /-- The faces: each is a set of vertices spanning a geometric 2-simplex. -/
  faces : Finset (Finset Vertex)
  /-- Every face has exactly three vertices, so the complex is purely two-dimensional. -/
  faces_card : ∀ t ∈ faces, t.card = 3
  /-- The geometric realization of the face family is homeomorphic to `S`. -/
  homeo : GeometricRealization Vertex faces ≃ₜ S

attribute [instance] GeometricTriangulation.vertexFintype
attribute [instance] GeometricTriangulation.vertexDecidableEq

/-- Expanded, independently inspectable form of `GeometricTriangulation`.

This theorem pins the public meaning of the structure: no realization or incidence data is hidden
behind an additional field. -/
theorem nonempty_geometricTriangulation_iff_explicit
    {S : Type*} [TopologicalSpace S] :
    Nonempty (GeometricTriangulation S) ↔
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
        (F : Finset (Finset V)),
        (∀ t ∈ F, t.card = 3) ∧ Nonempty (GeometricRealization V F ≃ₜ S) := by
  constructor
  · rintro ⟨T⟩
    exact ⟨T.Vertex, T.vertexFintype, T.vertexDecidableEq, T.faces,
      T.faces_card, ⟨T.homeo⟩⟩
  · rintro ⟨V, hVfinite, hVdecidable, F, hF, ⟨h⟩⟩
    letI : Fintype V := hVfinite
    letI : DecidableEq V := hVdecidable
    exact ⟨{ Vertex := V, faces := F, faces_card := hF, homeo := h }⟩

namespace GeometricTriangulation

variable {S : Type*} [TopologicalSpace S] (T : GeometricTriangulation S)

/-- Surface-incidence certificate for a faithful geometric triangulation. -/
abbrev SurfaceIncidence : Prop :=
  TriangleFamily.SurfaceIncidence T.faces

/-- The realization of the triangulation, as a polyhedron in barycentric coordinates. -/
abbrev realization : Set (T.Vertex → ℝ) :=
  GeometricRealization T.Vertex T.faces

include T in
/-- Must-imply anchor: a finitely triangulated space is compact.  This is what rules out the
empty/junk triangulations that satisfied the previous `SurfaceTriangulable` predicate. -/
theorem compactSpace : CompactSpace S :=
  Homeomorph.compactSpace T.homeo

include T in
/-- Must-imply anchor: a finitely triangulated space is Hausdorff (the realization is a subspace
of a finite product of lines). -/
theorem t2Space : T2Space S :=
  Topology.IsEmbedding.t2Space (Homeomorph.isEmbedding T.homeo.symm)

/-- A triangulation of a nonempty space has at least one two-dimensional face. -/
theorem faces_nonempty [Nonempty S] : T.faces.Nonempty := by
  let s : S := Classical.choice inferInstance
  rcases (T.homeo.symm s).2.2 with ⟨t, ht, _⟩
  exact ⟨t, ht⟩

/-- On a connected realization, local edge-connectedness of every vertex star is enough to
deduce global dual connectivity. -/
theorem faces_isDualConnected_of_isVertexStarConnected [ConnectedSpace S]
    (hstar : TriangleFamily.IsVertexStarConnected T.faces) :
    TriangleFamily.IsDualConnected T.faces := by
  letI : ConnectedSpace T.realization :=
    T.homeo.connectedSpace_iff.mpr inferInstance
  have hpre : IsPreconnected (GeometricRealization T.Vertex T.faces) := by
    simpa only [Subtype.range_val] using
      (isPreconnected_range
        (continuous_subtype_val :
          Continuous (fun x : T.realization ↦ (x : T.Vertex → ℝ))))
  apply hstar.isDualConnected
  apply TriangleFamily.isFaceIntersectionConnected_of_isPreconnected _ hpre
  intro f
  rw [← Finset.card_pos, T.faces_card f.1 f.2]
  decide

/-- On a connected realization, strong fixed-star connectivity also implies global dual
connectivity. -/
theorem faces_isDualConnected_of_isStrongVertexStarConnected [ConnectedSpace S]
    (hstar : TriangleFamily.IsStrongVertexStarConnected T.faces) :
    TriangleFamily.IsDualConnected T.faces :=
  T.faces_isDualConnected_of_isVertexStarConnected hstar.isVertexStarConnected

/-- A triangulation of a nonempty space has at least three available vertices. -/
theorem three_le_card_vertex [Nonempty S] : 3 ≤ Fintype.card T.Vertex := by
  obtain ⟨t, ht⟩ := T.faces_nonempty
  calc
    3 = t.card := (T.faces_card t ht).symm
    _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ t)
    _ = Fintype.card T.Vertex := Finset.card_univ

/-- The edges of the triangulation: the 2-element subsets of its faces. -/
def edges : Finset (Finset T.Vertex) :=
  T.faces.biUnion fun t => t.powersetCard 2

theorem card_of_mem_edges {e : Finset T.Vertex} (he : e ∈ T.edges) : e.card = 2 := by
  rcases Finset.mem_biUnion.mp he with ⟨t, _ht, het⟩
  exact (Finset.mem_powersetCard.mp het).2

theorem mem_edges_of_subset_face {e t : Finset T.Vertex} (ht : t ∈ T.faces) (het : e ⊆ t)
    (he : e.card = 2) : e ∈ T.edges :=
  Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_powersetCard.mpr ⟨het, he⟩⟩

/-- The edge type of the triangulation. -/
abbrev Edge : Type :=
  {e : Finset T.Vertex // e ∈ T.edges}

/-- The triangle (face) type of the triangulation. -/
abbrev Triangle : Type :=
  {t : Finset T.Vertex // t ∈ T.faces}

theorem edge_card (e : T.Edge) : e.1.card = 2 :=
  T.card_of_mem_edges e.2

theorem triangle_card (t : T.Triangle) : t.1.card = 3 :=
  T.faces_card t.1 t.2

/-- The chosen first endpoint of an edge. -/
noncomputable def edgeSource (e : T.Edge) : T.Vertex :=
  (Finset.card_eq_two.mp (T.edge_card e)).choose

/-- The chosen second endpoint of an edge. -/
noncomputable def edgeTarget (e : T.Edge) : T.Vertex :=
  (Finset.card_eq_two.mp (T.edge_card e)).choose_spec.choose

theorem edgeSource_ne_edgeTarget (e : T.Edge) : T.edgeSource e ≠ T.edgeTarget e :=
  (Finset.card_eq_two.mp (T.edge_card e)).choose_spec.choose_spec.1

theorem edge_eq_pair (e : T.Edge) : e.1 = {T.edgeSource e, T.edgeTarget e} :=
  (Finset.card_eq_two.mp (T.edge_card e)).choose_spec.choose_spec.2

theorem edgeSource_mem (e : T.Edge) : T.edgeSource e ∈ e.1 := by
  rw [T.edge_eq_pair e]
  simp

theorem edgeTarget_mem (e : T.Edge) : T.edgeTarget e ∈ e.1 := by
  rw [T.edge_eq_pair e]
  simp

/-- An edge is a boundary edge when it lies in exactly one face. -/
def IsBoundaryEdge (e : T.Edge) : Prop :=
  (T.faces.filter fun t => e.1 ⊆ t).card = 1

end GeometricTriangulation

end ClassificationOfSurfaces
end Topology
end LeanEval
end r78_classification01_block_03
/- END ClassificationOfSurfaces.Moise.GeometricTriangulation -/

/- BEGIN ClassificationOfSurfaces.Moise.FrontierGlue | a7cf1e41713ddc27a376c9c3e765aaee5a40c39cb6c6b2b382de89f664e69016 -/
section r78_classification01_block_04
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Gluing a vanishing approximation across an open frontier

Moise Chapter 8 replaces a chart-transition map on an open, locally finite subcomplex.  The
replacement is controlled by a tolerance which tends to zero at the frontier, so it fits
continuously with the unchanged map outside the open set.  This file isolates that analytic
argument from the later complex bookkeeping.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

open Filter
open scoped Topology

/-- A positive control on `U` is strongly positive when it has a positive lower bound on every
compact subset of `U`.  This is Moise's notation `phi >> 0`, stated without continuity. -/
def StronglyPositiveOn {X : Type*} [TopologicalSpace X]
    (U : Set X) (phi : X → ℝ) : Prop :=
  ∀ C : Set X, IsCompact C → C ⊆ U →
    ∃ eps : ℝ, 0 < eps ∧ ∀ x ∈ C, eps ≤ phi x

/-- Distance to the complement, the canonical frontier-vanishing control on an open set. -/
noncomputable def frontierDistance {X : Type*} [PseudoMetricSpace X]
    (U : Set X) (x : X) : ℝ :=
  Metric.infDist x Uᶜ

theorem frontierDistance_pos {X : Type*} [PseudoMetricSpace X]
    {U : Set X} (hU : IsOpen U) (hUc : Uᶜ.Nonempty) {x : X} (hx : x ∈ U) :
    0 < frontierDistance U x := by
  apply (hU.isClosed_compl.notMem_iff_infDist_pos hUc).mp
  simpa

/-- Distance to the complement is strongly positive on the open set. -/
theorem stronglyPositiveOn_frontierDistance {X : Type*} [PseudoMetricSpace X]
    {U : Set X} (hU : IsOpen U) (hUc : Uᶜ.Nonempty) :
    StronglyPositiveOn U (frontierDistance U) := by
  intro C hC hCU
  by_cases hCempty : C = ∅
  · exact ⟨1, by norm_num, by simp [hCempty]⟩
  · have hCne : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hCempty
    obtain ⟨x, hxC, hxMin⟩ := hC.exists_isMinOn hCne
      (Metric.continuous_infDist_pt Uᶜ).continuousOn
    refine ⟨frontierDistance U x, frontierDistance_pos hU hUc (hCU hxC), ?_⟩
    intro y hyC
    exact hxMin hyC

/-- The control tends to zero when points of `U` approach its frontier. -/
def VanishesAtFrontier {X : Type*} [TopologicalSpace X]
    (U : Set X) (phi : X → ℝ) : Prop :=
  ∀ x ∈ frontier U, Tendsto phi (nhdsWithin x U) (nhds 0)

/-- Distance to the complement tends to zero along the open set at every frontier point. -/
theorem vanishesAtFrontier_frontierDistance {X : Type*} [PseudoMetricSpace X]
    {U : Set X} (hU : IsOpen U) : VanishesAtFrontier U (frontierDistance U) := by
  intro x hx
  have hxnot : x ∉ U := by
    rw [frontier, hU.interior_eq] at hx
    exact hx.2
  have hxzero : frontierDistance U x = 0 :=
    Metric.infDist_zero_of_mem (Set.mem_compl hxnot)
  rw [← hxzero]
  exact ((Metric.continuous_infDist_pt Uᶜ).tendsto x).mono_left inf_le_left

/-! ## Compact exhaustion of a proper open set -/

/-- The `n`-th compact core of an open set, cut out by distance to its complement. -/
noncomputable def frontierCore {X : Type*} [PseudoMetricSpace X]
    (U : Set X) (n : ℕ) : Set X :=
  {x | 1 / (n + 1 : ℝ) ≤ frontierDistance U x}

theorem isCompact_frontierCore {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (U : Set X) (n : ℕ) : IsCompact (frontierCore U n) := by
  apply IsClosed.isCompact
  exact isClosed_Ici.preimage (Metric.continuous_infDist_pt Uᶜ)

theorem frontierCore_subset {X : Type*} [PseudoMetricSpace X]
    {U : Set X} (_ : Uᶜ.Nonempty) (n : ℕ) : frontierCore U n ⊆ U := by
  intro x hx
  by_contra hxU
  have hzero : frontierDistance U x = 0 :=
    Metric.infDist_zero_of_mem (Set.mem_compl hxU)
  rw [frontierCore, Set.mem_setOf_eq, hzero] at hx
  have hpos : 0 < 1 / (n + 1 : ℝ) := by positivity
  linarith

theorem iUnion_frontierCore {X : Type*} [PseudoMetricSpace X]
    {U : Set X} (hU : IsOpen U) (hUc : Uᶜ.Nonempty) :
    (⋃ n : ℕ, frontierCore U n) = U := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact frontierCore_subset hUc n hn
  · intro x hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (frontierDistance_pos hU hUc hx)
    exact Set.mem_iUnion.mpr ⟨n, hn.le⟩

theorem frontierCore_subset_interior_succ {X : Type*} [PseudoMetricSpace X]
    (U : Set X) (n : ℕ) :
    frontierCore U n ⊆ interior (frontierCore U (n + 1)) := by
  let V : Set X := {x | 1 / (n + 2 : ℝ) < frontierDistance U x}
  have hVopen : IsOpen V :=
    isOpen_Ioi.preimage (Metric.continuous_infDist_pt Uᶜ)
  have hVsub : V ⊆ frontierCore U (n + 1) := by
    intro x hx
    change 1 / (n + 2 : ℝ) < frontierDistance U x at hx
    simp only [frontierCore, Set.mem_setOf_eq]
    have hden : (((n + 1 : ℕ) : ℝ) + 1) = n + 2 := by
      push_cast
      ring
    rw [hden]
    exact hx.le
  have hVint : V ⊆ interior (frontierCore U (n + 1)) :=
    interior_maximal hVsub hVopen
  intro x hx
  apply hVint
  have hden : (0 : ℝ) < n + 1 := by positivity
  have hlt : 1 / (n + 2 : ℝ) < 1 / (n + 1 : ℝ) := by
    apply one_div_lt_one_div_of_lt hden
    norm_num
  exact hlt.trans_le hx

/-- Replace `h` by `g` on `U`. -/
noncomputable def frontierGlue {X Y : Type*} (U : Set X) (g h : X → Y) : X → Y := by
  classical
  exact U.piecewise g h

@[simp] theorem frontierGlue_of_mem {X Y : Type*} {U : Set X} {g h : X → Y}
    {x : X} (hx : x ∈ U) : frontierGlue U g h x = g x := by
  classical
  simp [frontierGlue, hx]

@[simp] theorem frontierGlue_of_notMem {X Y : Type*} {U : Set X} {g h : X → Y}
    {x : X} (hx : x ∉ U) : frontierGlue U g h x = h x := by
  classical
  simp [frontierGlue, hx]

/-- A replacement agrees asymptotically with the old map at the frontier of its open domain.
This is the topology-only form of Moise's condition `phi(P) → 0`. -/
def MatchesAtFrontier {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (U : Set X) (g h : X → Y) : Prop :=
  ∀ x ∈ frontier U, Tendsto g (nhdsWithin x U) (nhds (h x))

/-- A frontier-matching replacement on an open set glues continuously to the unchanged map.
Unlike `continuous_frontierGlue`, this form does not require a metric on the target. -/
theorem continuous_frontierGlue_of_matches {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {U : Set X} (hU : IsOpen U) {g h : X → Y}
    (hg : ContinuousOn g U) (hh : Continuous h)
    (hmatch : MatchesAtFrontier U g h) :
    Continuous (frontierGlue U g h) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hxU : x ∈ U
  · have heq : frontierGlue U g h =ᶠ[nhds x] g := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      exact frontierGlue_of_mem hy
    exact (hg.continuousAt (hU.mem_nhds hxU)).congr_of_eventuallyEq heq
  · by_cases hxClosure : x ∈ closure U
    · have hxFrontier : x ∈ frontier U := by
        rw [frontier, hU.interior_eq]
        exact ⟨hxClosure, hxU⟩
      rw [ContinuousAt]
      intro V hV
      rw [frontierGlue_of_notMem hxU] at hV
      have hgV : g ⁻¹' V ∈ nhdsWithin x U := hmatch x hxFrontier hV
      obtain ⟨W, hW, hWsub⟩ :=
        mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hgV
      have hhV : h ⁻¹' V ∈ nhds x := hh.continuousAt hV
      apply Filter.mem_of_superset (inter_mem hW hhV)
      intro y hy
      by_cases hyU : y ∈ U
      · rw [Set.mem_preimage, frontierGlue_of_mem hyU]
        exact hWsub ⟨hy.1, hyU⟩
      · rw [Set.mem_preimage, frontierGlue_of_notMem hyU]
        exact hy.2
    · have houtside : Uᶜ ∈ nhds x := by
        exact Filter.mem_of_superset
          ((isOpen_compl_iff.mpr isClosed_closure).mem_nhds hxClosure)
          (Set.compl_subset_compl.mpr subset_closure)
      have heq : frontierGlue U g h =ᶠ[nhds x] h := by
        filter_upwards [houtside] with y hy
        exact frontierGlue_of_notMem hy
      exact hh.continuousAt.congr_of_eventuallyEq heq

/-- A replacement on an open set glues continuously to the old map when its error tends to zero
at the frontier.  No local finiteness or PL data enters this lemma. -/
theorem continuous_frontierGlue {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {U : Set X} (hU : IsOpen U) {g h : X → Y}
    (hg : ContinuousOn g U) (hh : Continuous h) {phi : X → ℝ}
    (hphi : VanishesAtFrontier U phi)
    (hclose : ∀ x ∈ U, dist (g x) (h x) ≤ |phi x|) :
    Continuous (frontierGlue U g h) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hxU : x ∈ U
  · have heq : frontierGlue U g h =ᶠ[nhds x] g := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      exact frontierGlue_of_mem hy
    exact (hg.continuousAt (hU.mem_nhds hxU)).congr_of_eventuallyEq heq
  · by_cases hxClosure : x ∈ closure U
    · have hxFrontier : x ∈ frontier U := by
        rw [frontier, hU.interior_eq]
        exact ⟨hxClosure, hxU⟩
      rw [Metric.continuousAt_iff']
      intro eps heps
      have heps2 : 0 < eps / 2 := half_pos heps
      have hhsmall : ∀ᶠ y in nhds x, dist (h y) (h x) < eps / 2 :=
        (Metric.continuousAt_iff'.mp hh.continuousAt) (eps / 2) heps2
      have hphismallWithin : {y | dist (phi y) 0 < eps / 2} ∈ nhdsWithin x U :=
        (Metric.tendsto_nhds.mp (hphi x hxFrontier)) (eps / 2) heps2
      obtain ⟨V, hV, hVU⟩ :=
        mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hphismallWithin
      filter_upwards [hV, hhsmall] with y hyV hyh
      rw [frontierGlue_of_notMem hxU]
      by_cases hyU : y ∈ U
      · rw [frontierGlue_of_mem hyU]
        have hphiSmall : |phi y| < eps / 2 := by
          have := hVU ⟨hyV, hyU⟩
          simpa [Real.dist_eq] using this
        calc
          dist (g y) (h x) ≤ dist (g y) (h y) + dist (h y) (h x) :=
            dist_triangle _ _ _
          _ < eps / 2 + eps / 2 :=
            add_lt_add (lt_of_le_of_lt (hclose y hyU) hphiSmall) hyh
          _ = eps := by ring
      · rw [frontierGlue_of_notMem hyU]
        exact hyh.trans (half_lt_self heps)
    · have houtside : Uᶜ ∈ nhds x := by
        exact Filter.mem_of_superset
          ((isOpen_compl_iff.mpr isClosed_closure).mem_nhds hxClosure)
          (Set.compl_subset_compl.mpr subset_closure)
      have heq : frontierGlue U g h =ᶠ[nhds x] h := by
        filter_upwards [houtside] with y hy
        exact frontierGlue_of_notMem hy
      exact hh.continuousAt.congr_of_eventuallyEq heq

/-- Metric closeness controlled by a frontier-vanishing function supplies the topology-only
matching condition.  This is the bridge from the quantitative Chapter 6 approximation to the
metric-free paste in the ambient surface. -/
theorem matchesAtFrontier_of_vanishing_close {X Y : Type*}
    [TopologicalSpace X] [PseudoMetricSpace Y]
    {U : Set X} (hU : IsOpen U) {g h : X → Y}
    (hg : ContinuousOn g U) (hh : Continuous h) {phi : X → ℝ}
    (hphi : VanishesAtFrontier U phi)
    (hclose : ∀ x ∈ U, dist (g x) (h x) ≤ |phi x|) :
    MatchesAtFrontier U g h := by
  have hglue := continuous_frontierGlue hU hg hh hphi hclose
  intro x hx
  have hxU : x ∉ U := by
    rw [frontier, hU.interior_eq] at hx
    exact hx.2
  have ht : Tendsto (frontierGlue U g h) (nhdsWithin x U)
      (nhds (frontierGlue U g h x)) :=
    hglue.continuousAt.mono_left inf_le_left
  rw [frontierGlue_of_notMem hxU] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact frontierGlue_of_mem hy

/-- The range of a frontier glue is exactly the union of the replacement image and the
unchanged image.  This set-level formula is the one used in Moise Chapter 8 when the modified
old complex is united with the finite chart complex. -/
theorem range_frontierGlue {X Y : Type*} {U : Set X} {g h : X → Y} :
    Set.range (frontierGlue U g h) = g '' U ∪ h '' Uᶜ := by
  classical
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    by_cases hx : x ∈ U
    · exact Set.mem_union_left _ ⟨x, hx, (frontierGlue_of_mem hx).symm⟩
    · exact Set.mem_union_right _ ⟨x, hx, (frontierGlue_of_notMem hx).symm⟩
  · rintro y (hy | hy)
    · obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, frontierGlue_of_mem hx⟩
    · obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, frontierGlue_of_notMem hx⟩

/-- A replacement which is injective on the open set and misses the unchanged outside image
glues to a globally injective map.  No compactness or continuity is needed for this part. -/
theorem injective_frontierGlue {X Y : Type*} {U : Set X} {g h : X → Y}
    (hg : Set.InjOn g U) (hh : Function.Injective h)
    (hcross : Disjoint (g '' U) (h '' Uᶜ)) :
    Function.Injective (frontierGlue U g h) := by
  classical
  intro x y hxy
  by_cases hx : x ∈ U
  · by_cases hy : y ∈ U
    · apply hg hx hy
      simpa only [frontierGlue_of_mem hx, frontierGlue_of_mem hy] using hxy
    · have hgx : g x ∈ g '' U := ⟨x, hx, rfl⟩
      have hhy : h y ∈ h '' Uᶜ := ⟨y, hy, rfl⟩
      have : g x = h y := by
        simpa only [frontierGlue_of_mem hx, frontierGlue_of_notMem hy] using hxy
      exact False.elim (Set.disjoint_left.mp hcross hgx (this ▸ hhy))
  · by_cases hy : y ∈ U
    · have hgy : g y ∈ g '' U := ⟨y, hy, rfl⟩
      have hhx : h x ∈ h '' Uᶜ := ⟨x, hx, rfl⟩
      have : h x = g y := by
        simpa only [frontierGlue_of_notMem hx, frontierGlue_of_mem hy] using hxy
      exact False.elim (Set.disjoint_left.mp hcross hgy (this.symm ▸ hhx))
    · apply hh
      simpa only [frontierGlue_of_notMem hx, frontierGlue_of_notMem hy] using hxy

/-- On a compact source, the continuous injective frontier glue is a topological embedding.
This packages the exact analytic conclusion used for Moise's modified map `f'_n`. -/
theorem isEmbedding_frontierGlue {X Y : Type*} [TopologicalSpace X]
    [CompactSpace X] [PseudoMetricSpace Y] [T2Space Y]
    {U : Set X} (hU : IsOpen U)
    {g h : X → Y} (hgcont : ContinuousOn g U) (hhcont : Continuous h)
    {phi : X → ℝ} (hphi : VanishesAtFrontier U phi)
    (hclose : ∀ x ∈ U, dist (g x) (h x) ≤ |phi x|)
    (hginj : Set.InjOn g U) (hhinj : Function.Injective h)
    (hcross : Disjoint (g '' U) (h '' Uᶜ)) :
    _root_.Topology.IsEmbedding (frontierGlue U g h) := by
  have hcontinuous := continuous_frontierGlue hU hgcont hhcont hphi hclose
  exact (hcontinuous.isClosedEmbedding
    (injective_frontierGlue hginj hhinj hcross)).isEmbedding

/-- Compact-to-Hausdorff embedding form of the topology-only frontier glue. -/
theorem isEmbedding_frontierGlue_of_matches {X Y : Type*}
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [T2Space Y]
    {U : Set X} (hU : IsOpen U) {g h : X → Y}
    (hgcont : ContinuousOn g U) (hhcont : Continuous h)
    (hmatch : MatchesAtFrontier U g h)
    (hginj : Set.InjOn g U) (hhinj : Function.Injective h)
    (hcross : Disjoint (g '' U) (h '' Uᶜ)) :
    _root_.Topology.IsEmbedding (frontierGlue U g h) := by
  have hcontinuous := continuous_frontierGlue_of_matches hU hgcont hhcont hmatch
  exact (hcontinuous.isClosedEmbedding
    (injective_frontierGlue hginj hhinj hcross)).isEmbedding

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end r78_classification01_block_04
/- END ClassificationOfSurfaces.Moise.FrontierGlue -/

/- BEGIN ClassificationOfSurfaces.Topology.InvarianceOfDomain | d75eafa147b4a9bd9eca4c847636278c305fcaa3c1d13ddda628799ac67ce846 -/
section r78_classification01_block_05
/-
Copyright (c) 2025 Steven Sivek and 2026 Kai Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sivek, Kai Lam
-/


/-!
# Invariance of domain

This file contains the completed invariance-of-domain portion of Kai Lam's development in
[mathlib4 PR #36770](https://github.com/leanprover-community/mathlib4/pull/36770), adapted from
commit `230d75acb32d80e7d7c4f4cd028b139f3dc28be7`. It proves invariance of domain for
finite-dimensional real inner product spaces, conditional on Brouwer's fixed-point theorem for the
closed unit ball.

The chart-independence layer is adapted from Steven Sivek's
[`TopologicalManifolds`](https://github.com/stevensivek/TopologicalManifolds) development at commit
`05f80330d5a41b05376ae90eb8aa32c0166721db`. It packages invariance of domain as a reusable
topological typeclass and applies it to the interior and boundary strata of charted spaces.

The proof follows Terry Tao's exposition, using the Tietze extension theorem,
Stone-Weierstrass approximation, and a measure-theoretic perturbation argument.

## Main declarations

* `BrouwerFixedPoint`: the required fixed-point principle for the closed unit ball.
* `differentiable_approx_of_continuous`: differentiable approximation on compact sets.
* `stability_of_zero`: stability of a zero under a bounded perturbation.
* `invariance_of_domain_interior`: the closed-ball form of invariance of domain.
* `invariance_of_domain_open_map`: the open-set form of invariance of domain.
* `invariance_of_domain_partial_equiv`: the neighbourhood form for partial equivalences.
* `HasInvarianceOfDomain`: a reusable topological form of invariance of domain.
* `isInteriorPoint_iff_any_chart`: chart independence of interior points.
* `isBoundaryPoint_iff_any_chart`: chart independence of boundary points.

## Reference

* Terry Tao, "Brouwer's fixed point and invariance of domain theorems, and Hilbert's fifth
  problem", 2011.
-/


namespace LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain

open MeasureTheory Metric Set ContinuousLinearMap LinearMap Topology Polynomial

variable {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (E) in
/-- `BrouwerFixedPoint E` is a typeclass asserting that the Brouwer fixed point theorem holds for
  the closed unit ball in the inner product space `E`.  That is: for every continuous map
  `f : closedBall 0 1 → closedBall 0 1`, there exists `x` such that `f x = x`.
  This is assumed and used to prove invariance of domain. -/
class BrouwerFixedPoint : Prop where
  brouwer_fixed_point (f : (closedBall (0 : E) 1) → (closedBall 0 1))
    (hf : Continuous f) : ∃ x, f x = x

/-- On a compact set, any continuous map can be uniformly approximated by a differentiable map. -/
theorem differentiable_approx_of_continuous {δ : ℝ} (hδ : 0 < δ) {U : Set E}
    (hUcompact : IsCompact U) (G : E → E) (hG_cont : Continuous G) [Nontrivial E] :
    ∃ (P : C(E, E)), Differentiable ℝ P ∧ ∀ y ∈ U, ‖P y - G y‖ < δ := by
  let basis := stdOrthonormalBasis ℝ E
  let n := Module.finrank ℝ E
  -- We construct the subalgebra of polynomials from `ℝ^n` to `ℝ` and show they are differentiable
  -- Projecting onto one of the axes is continuous and differentiable
  let coord (i : Fin n) : C(E, ℝ) :=
    { toFun := fun x => basis.toBasis.equivFunL x i
      continuous_toFun := by fun_prop}
  have hcoord_diff (i : Fin n) : Differentiable ℝ (coord i) :=
    ((ContinuousLinearMap.proj i).comp
    (basis.toBasis.equivFunL : E →L[ℝ] (Fin n → ℝ))).differentiable
  -- This gives us the subalgebra of polynomials.
  let generator : Set C(E, ℝ) := Set.range coord
  have hgen_diff : ∀ f ∈ generator, Differentiable ℝ f := by
    rintro _ ⟨i, rfl⟩
    exact hcoord_diff i
  let A : Subalgebra ℝ C(E, ℝ) := Algebra.adjoin ℝ generator
  have hA_diff : ∀ f ∈ A, Differentiable ℝ f := by
    let D : Subalgebra ℝ C(E, ℝ) :=
      { carrier := {f | Differentiable ℝ f}
        zero_mem' := differentiable_const 0
        one_mem' := differentiable_const 1
        add_mem' := fun hf hg => hf.add hg
        mul_mem' := fun hf hg => hf.mul hg
        algebraMap_mem' := fun r => differentiable_const r }
    have hA_sub : A ≤ D := Algebra.adjoin_le hgen_diff
    exact fun f hf => hA_sub hf
  -- This subalgebra of polynomials separates points.
  have hAsep : A.SeparatesPoints := by
    intro x y hxy
    have hequiv: basis.toBasis.equivFunL x ≠ basis.toBasis.equivFunL y := by simpa
    obtain ⟨i, hi⟩ : ∃ i : (Fin n), basis.toBasis.equivFunL x i ≠ basis.toBasis.equivFunL y i := by
      contrapose! hequiv
      ext i
      exact (hequiv i)
    have hf_mem : coord i ∈ A := Algebra.subset_adjoin (Set.mem_range_self i)
    exact ⟨coord i, Set.mem_image_of_mem (fun f ↦ f.1) hf_mem, hi⟩
  let G_i (i : Fin n) : C(E, ℝ) :=
    {toFun := fun y => basis.toBasis.equivFunL (G y) i, continuous_toFun := by fun_prop}
  let coordEquiv := basis.toBasis.equivFunL
  have hpos_symm : 0 < ‖(coordEquiv.symm : ((Fin n) → ℝ) →L[ℝ] E)‖ := by
    refine lt_of_le_of_ne (norm_nonneg _) fun h_eq => ?_
    let w : Fin n → ℝ := fun _ => 1
    have hw : w ≠ 0 := by
      haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp Module.finrank_pos
      obtain ⟨i⟩ := (inferInstance : Nonempty (Fin n))
      intro h
      have : w i = 0 := congr_fun h i
      linarith
    have hw0 : (coordEquiv.symm : (Fin n → ℝ) →L[ℝ] E) w = 0 := by
      rw [norm_eq_zero.1 h_eq.symm]
      rfl
    have hfalse : coordEquiv (coordEquiv.symm w) = coordEquiv 0 := congrArg coordEquiv hw0
    rw [coordEquiv.apply_symm_apply w, map_zero] at hfalse
    exact hw hfalse
  -- Define `C` as the operator norm for l.symm
  let C := ‖(coordEquiv.symm : (Fin n → ℝ) →L[ℝ] E)‖
  let ε' := δ / (2 * C)
  have hε' : 0 < ε' := div_pos (hδ) (mul_pos zero_lt_two hpos_symm)
  -- Using the Stone-Weierstrass theorem, pick each `P_i` to be `ε'-close` to each `G_i`.
  have approx (i : Fin n) :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
    hAsep (G_i i) hUcompact hε'
  choose p_i hp_i using approx
  -- Construct `P` as a function from `ℝ^n` to `ℝ^n` using the component functions `P_i`.
  let P : C(E, E) :=
    { toFun := fun y => basis.toBasis.equivFunL.symm (fun i => (p_i i : C(E, ℝ)) y),
      continuous_toFun := by fun_prop}
  -- The difference between `P` and `G` on `Σ` is bounded by `δ`
  have hP_bound : ∀ y ∈ U , ‖P y - G y‖ < δ := by
    intro y hy
    let v : Fin n → ℝ := fun i => (p_i i : C(E, ℝ)) y - (basis.toBasis.equivFunL (G y)) i
    have hv i : |v i| < ε' := by
      grind only [ContinuousMap.coe_mk, Real.norm_eq_abs, (hp_i i).2 y hy]
    have hnorm_v : ‖v‖ < ε' := by rw [pi_norm_lt_iff hε']; exact fun i => hv i
    have hP_eq : P y - G y = coordEquiv.symm v := by
      apply coordEquiv.injective
      rw [map_sub, coordEquiv.apply_symm_apply]
      ext i
      change
        (coordEquiv (coordEquiv.symm (fun j => (p_i j : C(E, ℝ)) y)) - coordEquiv (G y)) i =
          (fun j => (p_i j : C(E, ℝ)) y - coordEquiv (G y) j) i
      rw [coordEquiv.apply_symm_apply]
      rfl
    rw [hP_eq]
    calc
      ‖coordEquiv.symm v‖
      ≤ C * ‖v‖ := le_opNorm (coordEquiv.symm : (Fin n → ℝ) →L[ℝ] E) v
    _ < C * ε' := mul_lt_mul_of_pos_left hnorm_v hpos_symm
    _ = δ / 2 := by
        unfold ε'
        field_simp [ne_of_gt hpos_symm]
        exact div_self (ne_of_gt hpos_symm)
    _ < δ := half_lt_self hδ
  have hp_i_diff (i : Fin n) : Differentiable ℝ (p_i i) := hA_diff (p_i i) (hp_i i).1
  have hP_diff : Differentiable ℝ P :=
    (basis.toBasis.equivFunL.symm : (Fin n → ℝ) →L[ℝ] E).differentiable.comp
    (differentiable_pi.mpr hp_i_diff)
  use P

variable [BrouwerFixedPoint E]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Stability of zero (Lemma 6). If `G` is a left inverse of `f` on the closed ball,
    and `Gtilde` is a continuous function on `f(Bⁿ)` with `‖G - Gtilde‖ ≤ 1` pointwise,
    then `Gtilde` has a zero in `f(Bⁿ)`. -/
lemma stability_of_zero (f : E → E) (hf_cont : ContinuousOn f (closedBall 0 1))
    (G : C(E, E)) (hG_left_inv : ∀ x ∈ closedBall 0 1, G (f x) = x)
    (Gtilde : E → E) (hGtilde_cont : ContinuousOn Gtilde (f '' closedBall 0 1))
    (hbound : ∀ y ∈ f '' closedBall 0 1, ‖G y - Gtilde y‖ ≤ 1) :
    ∃ y ∈ f '' closedBall 0 1, Gtilde y = 0 := by
  -- Define the function whose fixed point gives the zero of `Gtilde`
  let diff_fun : E → E := fun x => x - Gtilde (f x)
  -- `B^n` contains the image of itself under diff_fun.
  have hMapsTo : Set.MapsTo diff_fun (closedBall 0 1) (closedBall 0 1) :=
    fun x hx => by grind [mem_closedBall_zero_iff]
  -- `diff_fun` is continuous on `B^n`
  have diff_fun_cont_on : ContinuousOn diff_fun (closedBall 0 1) :=
    (continuousOn_id' _).sub (hGtilde_cont.comp hf_cont (mapsTo_image f _))
  obtain ⟨x, hx⟩ := BrouwerFixedPoint.brouwer_fixed_point
    (Set.MapsTo.restrict diff_fun (closedBall 0 1) (closedBall 0 1) hMapsTo)
    (ContinuousOn.mapsToRestrict diff_fun_cont_on hMapsTo)
  have hx_eq : diff_fun (x : E) = (x : E) := congr_arg Subtype.val hx
  grind

omit [FiniteDimensional ℝ E] [BrouwerFixedPoint E] in
private theorem radialProjection_mem_sep_union_sphere (c : E) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) {s : Set E} (hc : c ∉ s) {y : E} (hy : y ∈ s) :
    c + max (epsilon / ‖y - c‖) (1 : ℝ) • (y - c) ∈
      {z ∈ s | ‖z - c‖ ≥ epsilon} ∪ sphere c epsilon := by
  by_cases h : epsilon < ‖y - c‖
  · have hyc : 0 < ‖y - c‖ := hepsilon.trans h
    grind [max_eq_right_of_lt, one_smul, add_sub_cancel, div_lt_one hyc]
  · right
    simp only [not_lt] at h
    have hy_neq_c : c ≠ y := fun hcy ↦ hc (hcy ▸ hy)
    have hleft : 1 ≤ epsilon / ‖y - c‖ :=
      (one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr hy_neq_c.symm))).mpr h
    rw [max_eq_left hleft]
    simp [norm_smul, sub_ne_zero_of_ne hy_neq_c.symm, hepsilon.le]

/-- Let `B^n` be the closed unit ball (closedBall 0 1).
Let `f : B^n → ℝ^n` be an continuous injective map.
Then `f(0)` lies in the interior of `f(B^n)`. -/
theorem invariance_of_domain_interior (f : E → E)
    (hf_cont : ContinuousOn f (closedBall 0 1)) (hf_inj : Set.InjOn f (closedBall 0 1))
    : f 0 ∈ interior (f ''(closedBall 0 1)) := by
  -- In the case where `n = 0`, `ℝ^0` has only a single point.
  cases subsingleton_or_nontrivial E
  · have himage : f '' closedBall 0 1 = Set.univ := by
      ext y
      simp only [Set.mem_image, Set.mem_univ, iff_true]
      exact ⟨0, by simp, Subsingleton.elim _ _⟩
    rw [himage, interior_univ]; exact Set.mem_univ _
  -- The equivalence between `B^n` and `f(B^n)`.
  let FEquiv := Equiv.Set.imageOfInjOn f (closedBall 0 1) hf_inj
  -- The inverse map of `f` is continuous.
  let FInvCmap : C(f '' closedBall 0 1, (closedBall (0 : E) 1)) :=
  ⟨FEquiv.symm,  Continuous.continuous_symm_of_equiv_compact_to_t2 (continuous_induced_rng.mpr <|
    ContinuousOn.restrict hf_cont)⟩
  -- `f(B^n)` is closed.
  have hballimageclosed : IsClosed (f '' closedBall 0 1) :=
    ((isCompact_closedBall 0 1).image_of_continuousOn hf_cont).isClosed
  -- The Tietze extension theorem, finding a continuous function `G` that extends `f⁻¹`.
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hballimageclosed FInvCmap
  -- `G` has a zero at `f 0`.
  have hG0 : G (f 0) = (0 : E) := by
    let fzero' : (f '' closedBall 0 1) := ⟨f 0, ⟨0, by simp, rfl⟩⟩
    have := congr($hG fzero')
    conv_lhs at this => simp [fzero']
    have H : (⟨f 0, ⟨0, by simp, rfl⟩⟩ : f '' closedBall 0 1) = FEquiv ⟨0, by simp⟩ :=
      Subtype.ext rfl
    simp [this, FInvCmap, fzero', H]
  let G' : C(E, E) := ⟨fun x => (G x : E), continuous_subtype_val.comp (ContinuousMap.continuous G)⟩
  -- Prove that `G` restricted to the image equals `FInvCmap`
  have hG_eq : ∀ y (hy : y ∈ f '' closedBall 0 1), G y = FInvCmap ⟨y, hy⟩ := by
    grind [ContinuousMap.restrict_apply]
  -- Now prove the left‑inverse property for `G'`
  have hG'_left_inv : ∀ x ∈ closedBall 0 1, G' (f x) = x := fun x hx =>
    (congr_arg Subtype.val (hG_eq (f x) (mem_image_of_mem f hx))).trans
    (congr_arg Subtype.val (FEquiv.symm_apply_apply ⟨x, hx⟩))
  -- Let `Gtilde : f(B^n) → ℝ^n` be a continuous function such that
  -- `‖G(y) - Gtilde(y)‖ ≤ 1 ∀ y ∈ f(B^n)`. Then `∃ y ∈ f (B^n)` such that `Gtilde(y)=0`.
  have hStability_of_zero (Gtilde : E → E) (hGtilde : ContinuousOn Gtilde (f '' closedBall 0 1))
      (hy : ∀ y ∈ (f '' closedBall 0 1), ‖G y - Gtilde y‖ ≤ 1) :
      ∃ y ∈ f '' closedBall 0 1, Gtilde y = 0 :=
    stability_of_zero f hf_cont G' hG'_left_inv Gtilde hGtilde hy
  -- By way of contradiction, we assume that `f(0)` is not an interior point of `f(B^n)` .
  -- From this, we construct a `Gtilde` as in the above lemma to derive a contradiction.
  by_contra hnotinterior
  -- `G` is continuous at `f(0)`.
  have hG_cont_at_f0 : ContinuousAt (fun x => (G x : E)) (f 0) := Continuous.continuousAt
    (continuous_subtype_val.comp (ContinuousMap.continuous G))
  rw [continuousAt_iff] at hG_cont_at_f0
  -- `G` is continuous on the whole space, so by picking `ε > 0` small enough,
  -- we can ensure `‖G(y)‖ ≤ 0.1` whenever `y ∈ ℝ^n` and `‖y - f(0)‖ ≤ 2ε`.
  obtain ⟨twoε, h2εpos, h2ε1⟩ := hG_cont_at_f0 0.1 (by norm_num)
  let ε : ℝ := twoε /2
  have hε1 : ε > 0 := half_pos h2εpos
  have h2εeq : twoε = 2 * ε := by ring
  -- As `f(0)` is not an interior point of `f(B^n)`, there exists a point `c ∈ ℝ^n` with
  -- `‖c - f(0)‖ < ε` not in `f(B^n)`.
  obtain ⟨c, hc1, hc2⟩ : ∃ c, dist c (f 0) < ε ∧ c ∉ f '' closedBall 0 1 := by
    rw [mem_interior] at hnotinterior
    push Not at hnotinterior
    specialize hnotinterior (ball (f 0) ε)
    simp only [isOpen_ball, mem_ball, dist_self, forall_const, imp_not_comm] at hnotinterior
    have hnotball := hnotinterior hε1
    rw [Set.not_subset] at hnotball
    obtain ⟨c, hc⟩ := hnotball
    exact ⟨c, ⟨mem_ball.mp hc.1, (Set.mem_compl_iff (f '' closedBall 0 1) c).mp hc.2⟩⟩
  -- `‖G(y)‖ ≤ 0.1` whenever `‖y - c‖ ≤ ε`.
  have hG_small (y : E) (h : ‖y - c‖ ≤ ε) : ‖(G y : E)‖ ≤ 0.1 := by
    rw [dist_eq_norm] at hc1
    have hdist : ‖y - f 0‖ < 2 * ε := by
      have hineq := norm_add_le (y - c) (c - f 0)
      simp only [sub_add_sub_cancel] at hineq; linarith
    grind [dist_zero_right, dist_eq_norm]
  -- Let `Σ₁ := {y ∈ f(B^n): ‖y - c‖ ≥ ε}`.
  let sigma1 : Set (E) := {y ∈ f '' closedBall 0 1 | ‖y - c‖ ≥ ε}
  -- Let `Σ₂ := {y ∈ ℝ^n : ‖y - c‖ = ε}`.
  let sigma2 : Set (E) := sphere c ε
  -- Let `Σ := Σ₁ ∪ Σ₂`.
  let sigma := sigma1 ∪ sigma2
  -- By construction, `Σ` is compact.
  -- `Σ₁` is compact.
  have hsigma1compact : IsCompact sigma1 := by
    rw [isCompact_iff_isClosed_bounded]
    -- `Σ₁` is the complement of the open ball, so it is closed.
    have hcompl : {y | ‖y - c‖ ≥ ε }ᶜ = ball c ε := by
      ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, mem_ball_iff_norm]
    have hopen : IsOpen {y | ‖y - c‖ ≥ ε }ᶜ := hcompl ▸ isOpen_ball
    -- `f(B^n)` is compact as it is the image of a compact set under a continuous function
    -- As compact sets are bounded and `Σ₁` is contained in this, `Σ₁` is bounded.
    have himgcompact := IsCompact.image_of_continuousOn (isCompact_closedBall 0 1) hf_cont
    exact ⟨(IsClosed.and hballimageclosed ({isOpen_compl := (hopen) })), Bornology.IsBounded.subset
    (IsCompact.isBounded himgcompact) (Set.sep_subset (f '' closedBall 0 1) fun x ↦ ‖x - c‖ ≥ ε)⟩
  -- It remains to be shown that `Σ₂` is compact, which follows from it being a sphere.
  have hsigmacompact : IsCompact sigma := IsCompact.union hsigma1compact (isCompact_sphere c ε)
  -- Let `Φ` be the function `Φ(y) := max(ε / ‖y - c‖, 1)) * (y - c)`.
  let Phi : (E) → (E) := fun y => c + (max (ε / ‖y - c‖) (1 : ℝ)) • (y - c)
  -- The image of `f(B^n)` under `Φ` is `Σ`.
  have hPhiimg (y : E) (hy : y ∈ f '' closedBall 0 1) : Phi y ∈ sigma := by
    simpa only [Phi, sigma, sigma1, sigma2] using
      radialProjection_mem_sep_union_sphere c hε1 hc2 hy
  -- `Φ` is continuous.
  have hPhicont : ContinuousOn Phi (f '' closedBall 0 1) := by
    refine ContinuousOn.add continuousOn_const (ContinuousOn.smul ?_
    (ContinuousOn.sub (continuousOn_id' (f '' closedBall 0 1)) continuousOn_const))
    rw [continuousOn_iff_continuous_restrict]
    exact Continuous.max ((Continuous.div continuous_const (Continuous.norm
    (Continuous.sub continuous_subtype_val continuous_const)))
    (fun y ↦ by
      change ‖(y : E) - c‖ ≠ 0
      rw [norm_ne_zero_iff, sub_ne_zero]
      intro hyc
      exact hc2 (hyc ▸ y.property)))
      continuous_const
  -- By construction, `G` is non-zero on `Σ₁`
  have hGavoids : ∀ y ∈ sigma1, G y ≠ (0 : (E)) := by
    intro y hy
    by_contra hGeq
    have hG_inj_on_image : Set.InjOn G (f '' closedBall 0 1) := by
      intro x hx y hy h
      have hx_eq : G x = FInvCmap ⟨x, hx⟩ := by grind
      have hy_eq : G y = FInvCmap ⟨y, hy⟩ := by grind
      rw [hx_eq, hy_eq] at h
      exact congr_arg Subtype.val (FEquiv.symm.injective h)
    have hyeq : y = f 0 := by
      have hf0_image : f 0 ∈ f '' closedBall 0 1 := ⟨0, by simp, rfl⟩
      have heq : G y = G (f 0) := SetCoe.ext (Eq.trans hGeq hG0.symm)
      exact hG_inj_on_image hy.1 hf0_image heq
    rw [Set.mem_sep_iff, hyeq] at hy
    rw [dist_eq_norm, ← norm_neg, neg_sub] at hc1; linarith
  -- The norm of `G` is continuous on `Σ₁`
  let normG : E → ℝ := fun y => ‖(G y : E)‖
  have hGconton : ContinuousOn G (f '' closedBall 0 1) := (ContinuousMap.continuous G).continuousOn
  have hgnormconton1 : ContinuousOn normG sigma1 :=
    ContinuousOn.norm (continuous_subtype_val.comp_continuousOn
    (ContinuousOn.mono hGconton (Set.sep_subset (f '' closedBall 0 1) fun x ↦ ‖x - c‖ ≥ ε)))
  -- As `Σ₁` is compact, `G` is bounded below on `Σ₁` by some `δ > 0`.
  -- We can shrink `δ` to assume `δ < 0.1`.
  obtain ⟨δ, hδ1, hδ2, hδ3⟩ : ∃ (δ : ℝ), 0 < δ ∧ δ < 0.1 ∧ ∀ y ∈ sigma1, δ ≤ ‖(G y : E)‖ := by
    by_cases hP : sigma1.Nonempty
    · obtain ⟨z, hz, hmin⟩ := IsCompact.exists_isMinOn hsigma1compact hP hgnormconton1
      let δ := min (normG z) (0.05)
      have hδ_pos : 0 < δ := lt_min_iff.mpr ⟨norm_pos_iff.mpr (hGavoids z hz), by norm_num⟩
      have hδ_lt_0_1 : δ < 0.1 := (min_le_right _ 0.05).trans_lt (by norm_num)
      have hδ_lower : ∀ y ∈ sigma1, normG y ≥ δ := fun y hy => (min_le_left _ _).trans (hmin hy)
      exact ⟨δ, hδ_pos, hδ_lt_0_1, hδ_lower⟩
    · exact ⟨0.05, by norm_num, by norm_num, fun y hy ↦ False.elim (hP ⟨y, hy⟩)⟩
  obtain ⟨P, hP_diff, hP_bound⟩ :=
    differentiable_approx_of_continuous hδ1 hsigmacompact (fun (y : E) => (G y : E)) (by fun_prop)
  have h0_notin_image : (0 : E) ∉ P '' sigma1 := by
    rintro ⟨y, hy, h⟩
    have hG : ‖(G y : E)‖ ≥ δ := hδ3 y hy
    have hP : ‖P y - G y‖ < δ := hP_bound y (Set.subset_union_left hy)
    simp only [h, _root_.zero_sub, norm_neg] at hP
    linarith
  -- It is possible that `P` vanishes on `Σ₂`, so we construct a perturbation `P'` that does not.
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  -- `Σ₂` has measure `0`; `P` is differentiable. The image of `Σ₂` under P also has measure `0`.
  have hP_image_null : volume (P '' (sphere c ε)) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    hP_diff.differentiableOn
    (MeasureTheory.Measure.addHaar_sphere_of_ne_zero volume c (ne_of_gt hε1))
  -- As the image of `Σ₂` under P also has measure `0`, we can find a point v in the ball of radius
  -- δ that is neither in `Σ₁` nor `Σ₂`
  obtain ⟨v, hvnorm, hv1, hv2⟩ : ∃ (v : E), ‖v‖ < δ ∧ ¬ v ∈ P '' sigma1 ∧ ¬ v ∈ P '' sigma2 := by
    obtain hsigma1empty | hsigma1nonempty := sigma1.eq_empty_or_nonempty
    · have hball_pos := measure_ball_pos volume (0 : E) hδ1
      have hnot_subset2 : ¬ (ball 0 δ ⊆ P '' sigma2) := by
        intro hsub
        have : volume (ball (0 : E) δ) ≤ volume (P '' sigma2) := measure_mono hsub
        rw [show volume (P '' sigma2) = 0 by simpa [sigma2] using hP_image_null] at this
        exact (not_lt_of_ge this) (measure_ball_pos volume (0 : E) hδ1)
      rcases Set.not_subset.1 hnot_subset2 with ⟨v, hv_in_ball, hv_notin_sigma2⟩
      exact ⟨v, mem_ball_zero_iff.mp hv_in_ball, by simp [hsigma1empty], hv_notin_sigma2⟩
    have hP_cont : ContinuousOn (fun v => ‖P v‖) sigma1 := by fun_prop
    -- Let `d` be a point of `Σ₁` such that `‖P(d)‖` takes its minimum value.
    let ⟨d, _, hd⟩ := IsCompact.exists_isMinOn hsigma1compact hsigma1nonempty hP_cont
    -- Let `k` be the minimum of these two, to ensure both properties.
    let k := min ‖P d‖ δ
    obtain ⟨v, hvnorm, hv1⟩ : ∃ a ∈ ball 0 k, a ∉ P '' sphere c ε := by
      rw [← Set.not_subset]
      intro hsub
      have : volume (ball (0 : E) k) ≤ 0 := by rw [← hP_image_null]; exact measure_mono hsub
      exact LT.lt.false (lt_of_lt_of_le (measure_ball_pos volume (0 : E)
        (lt_min_iff.mpr ⟨by simp only [norm_pos_iff, ne_eq]; grind, hδ1⟩)) this)
    refine ⟨v, ⟨by linarith [mem_ball_zero_iff.mp hvnorm, min_le_right ‖P d‖ δ],
      ⟨fun hin1 => ?_, fun hin2 ↦ hv1 hin2⟩⟩⟩
    rcases hin1 with ⟨x, hx, rfl⟩
    linarith [(isMinOn_iff.mp hd) x hx, mem_ball_zero_iff.mp hvnorm, min_le_left ‖P d‖ δ]
  -- Let `P'` be the perturbation of `P` such that `P'(y) = P(y) - v`.
  let P' : C(E, E) := {toFun := fun y => P y - v, continuous_toFun:= by fun_prop}
  -- `v` is not in `Σ`.
  have hv_notin_sigma : v ∉ P '' sigma := by grind
  -- Define `Gtilde : f(B^n) → ℝ^n` as `Gtilde(y) = P'(Φ(y))`.
  let Gtilde : E → E := fun y => P' (Phi y)
  -- `Gtilde` is continuous.
  have hGtilde_cont : ContinuousOn Gtilde (f '' closedBall 0 1) :=
    (ContinuousMap.continuous P').comp_continuousOn hPhicont
  -- `P'` is never `0` on `Σ`. `Gtilde` is never `0`.
  have hGtilde_nonzero : ∀ y ∈ f '' closedBall 0 1, (P' ∘ Phi) y ≠ 0 :=
    fun y hy h_eq => (hv_notin_sigma) ⟨Phi y, hPhiimg y hy, sub_eq_zero.mp h_eq⟩
  -- We bound the difference between `G` and `Gtilde` by `1`.
  have hpeturb_bound : ∀ y ∈ f '' (closedBall (0 : E) 1), ‖G y - Gtilde y‖ ≤ 1 := by
    intro y hy
    -- There are two possible cases for the norm of `y - c`.
    by_cases hP : ε < ‖y - c‖
    · -- If `ε < ‖y - c‖`, then `Φ(y) = y`
      -- Thus `Gtilde(y) = G(Φ(y))`
      have hPhi : Phi y = y := by
        have hright : ε / ‖y - c‖ < 1 := by
          have hyc : 0 < ‖y - c‖ := by linarith
          rwa [div_lt_one hyc]
        simp [Phi, max_eq_right_of_lt hright]
      simp only [hPhi, Gtilde]
      -- We are using `P' = P - v`, `∀ y ∈ Σ, ‖P y - ↑(G y)‖ < δ` and `‖v‖ < δ`
      calc
        ‖G y - P' y‖ = ‖G y - (P y - v)‖ := rfl
        _ ≤ _ := by grw [sub_sub_eq_add_sub, add_sub_right_comm, norm_add_le, norm_sub_rev,
          hP_bound y (Or.inl ⟨hy, le_of_lt hP⟩), add_comm, hvnorm]
        _ ≤ _ := by linarith
    · -- If `‖y - c‖ ≤ ε`, then `Φ y ∈ Σ₂`.
      simp only [not_lt] at hP
      have hy_neq_c : c ≠ y := by grind
      have hleft : 1 ≤ ε / ‖y - c‖ :=
        (one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hy_neq_c)))).mpr hP
      have hPhi : Phi y = c + (ε / ‖y - c‖) • (y - c) := by grind [max_eq_left]
      have hyimg : Phi y ∈ sphere c ε := by
        simp [hPhi, mem_sphere_iff_norm, add_sub_cancel_left, norm_smul,
          (sub_ne_zero_of_ne (Ne.symm hy_neq_c)), hε1.le]
      have hP_approx_le : ‖P (Phi y)‖ ≤ ‖(G (Phi y) : E)‖ + δ := by
        linarith [norm_sub_rev (P (Phi y)) (G (Phi y) : E), hP_bound (Phi y) (Or.inr hyimg),
        norm_le_norm_add_norm_sub' (P (Phi y)) (G (Phi y))]
      have hG_phi_small : ‖(G (Phi y) : E)‖ ≤ 0.1 := by
        rw [dist_eq_norm] at hc1
        have hdist : ‖Phi y - f 0‖ < 2 * ε := calc
          ‖Phi y - f 0‖  ≤ ‖Phi y - c‖ + ‖c - f 0‖ := by grw [← sub_add_sub_cancel,norm_add_le]
          _ = ε + ‖c - f 0‖ := by rw [mem_sphere_iff_norm.mp hyimg]
          _ < ε + ε := add_lt_add_right hc1 ε
          _ = 2 * ε := by ring
        rw [← h2εeq, ← dist_eq_norm] at hdist
        grind [h2ε1 hdist, dist_zero_right]
      specialize hG_small y hP
      calc
        ‖G y - P' (Phi y)‖
          = ‖G y - (P (Phi y) - v)‖ := rfl
        _ ≤ ‖(G y : E)‖ + ‖P (Phi y)‖ + ‖v‖ := by grw [sub_sub_eq_add_sub, add_sub_right_comm,
          norm_add_le, norm_sub_le]
        _ ≤ _ := by linarith
  -- We derive a contradiction using the lemma for the stability of zero.
  obtain ⟨y, hy1, hy2⟩ := (((hStability_of_zero)) Gtilde hGtilde_cont) hpeturb_bound
  exact hGtilde_nonzero y hy1 hy2

/-- The invariance of domain theorem: if `U ⊆ E` is open,
  `f : E → E` is continuous on `U` and injective on `U`, then the image `f '' U` is open in `E`. -/
theorem invariance_of_domain_open_map (f : E → E) (U : Set E) (hU : IsOpen U)
    (hf_cont : ContinuousOn f U) (hf_inj : Set.InjOn f U) : IsOpen (f '' U) := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨x, hxU, hfx⟩
  rw [isOpen_iff] at hU
  have hclosedball: ∀ x' ∈ U, ∃ ε' > 0, closedBall x' ε' ⊆ U := by
    intro x' hx'
    obtain ⟨ε, hε, hball⟩ := hU x' hx'
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (div_two_lt_of_pos hε)).trans hball⟩
  obtain ⟨ε, hε , hclosedball⟩ := hclosedball x hxU
  -- Define `g` as a scaling and translating function.
  let g := fun (v : E) => ε • v + x
  have hg_inj : Function.Injective g := by simp [Function.Injective, g, hε.ne']
  have h_g_eq : g '' closedBall 0 1 = closedBall x ε := by
    rw [← Set.image_image (fun v ↦ v + x) (fun v ↦ ε • v) (closedBall 0 1), Set.image_smul,
      smul_unitClosedBall]
    simp only [Real.norm_eq_abs, Set.image_add_right, preimage_add_right_closedBall,
      sub_neg_eq_add, zero_add]
    rw [abs_of_pos hε]
  let e := f ∘ g
  have he_cont : ContinuousOn e (closedBall 0 1):=
    ContinuousOn.image_comp_continuous (h_g_eq ▸ hf_cont.mono hclosedball) (by fun_prop)
  have he_inj : Set.InjOn e (closedBall 0 1) := by
    rw [Set.InjOn.comp_iff hg_inj.injOn, h_g_eq]
    exact Set.InjOn.mono hclosedball hf_inj
  -- `e(0)` is in the interior using the prior version.
  have h_interior : e 0 ∈ interior (e '' closedBall 0 1) :=
    invariance_of_domain_interior e he_cont he_inj
  refine ⟨interior (f '' U), ⟨interior_subset, isOpen_interior, ?_⟩⟩
  unfold e g at h_interior
  rw [Set.image_comp, h_g_eq] at h_interior
  simp only [Function.comp_apply, smul_zero, zero_add] at h_interior
  grw [hfx, hclosedball] at h_interior
  exact h_interior

/-- If `f` is a partial equivalence continuous on its source, then it maps
    neighbourhoods of `x` (contained in the source) to neighbourhoods of `f(x)`. -/
theorem invariance_of_domain_partial_equiv {x : E} {s : Set E} {f : PartialEquiv E E}
    (hCont : ContinuousOn f f.source) : s ∈ nhds x → s ⊆ f.source →
    f '' s ∈ nhds (f x) := by
  intro hsin hsubset
  obtain ⟨a, ha1, ha2, ha3⟩ := _root_.mem_nhds_iff.mp hsin
  exact _root_.mem_nhds_iff.mpr ⟨f '' a, Set.image_mono ha1, invariance_of_domain_open_map (↑f) a
  ha2 (ContinuousOn.mono hCont (ha1.trans hsubset)) (Set.InjOn.mono (ha1.trans hsubset)
  (PartialEquiv.injOn f)), Set.mem_image_of_mem (↑f) ha3⟩

open Function ModelWithCorners TopologicalSpace

/-- A topological space has invariance of domain if each continuous partial equivalence maps
neighbourhoods contained in its source to neighbourhoods of the corresponding image point. -/
class HasInvarianceOfDomain (X : Type*) [TopologicalSpace X] : Prop where
  invariance_of_domain {x : X} {s : Set X} {f : PartialEquiv X X}
      (hCont : ContinuousOn f f.source) :
    s ∈ nhds x → s ⊆ f.source → f '' s ∈ nhds (f x)

/-- Apply a `HasInvarianceOfDomain` instance to a continuous partial equivalence. -/
theorem maps_nhds_to_nhds (X : Type*) [TopologicalSpace X]
    [instID : HasInvarianceOfDomain X] {x : X} {s : Set X} {f : PartialEquiv X X}
    (hCont : ContinuousOn f f.source) :
    s ∈ nhds x → s ⊆ f.source → f '' s ∈ nhds (f x) :=
  instID.invariance_of_domain hCont

/-- Brouwer's fixed-point theorem supplies invariance of domain in a finite-dimensional real
inner product space. -/
instance instHasInvarianceOfDomainOfBrouwerFixedPoint : HasInvarianceOfDomain E where
  invariance_of_domain := invariance_of_domain_partial_equiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

omit [ChartedSpace H M] in
variable (I) (M) in
/-- If some `OpenPartialHomeomorph M H` sends a point to the interior of `range I`, then
so does any other `OpenPartialHomeomorph M H`. -/
theorem independence_of_interior [HasInvarianceOfDomain E] {x : M}
    {f g : OpenPartialHomeomorph M H} (hfSource : x ∈ f.source) (hgSource : x ∈ g.source) :
    I (f x) ∈ interior (range I) → I (g x) ∈ interior (range I) := by
  intro hfInterior
  apply mem_interior_iff_mem_nhds.mp at hfInterior
  apply mem_interior_iff_mem_nhds.mpr
  let f' : PartialEquiv M E := f.toPartialEquiv.trans I.toPartialEquiv
  have hf'symmCont : ContinuousOn f'.symm f'.target := by
    apply ContinuousOn.comp (OpenPartialHomeomorph.continuousOn f.symm) ?_ ?_
    · simp only [PartialEquiv.restr_coe_symm, toPartialEquiv_coe_symm]
      exact continuousOn_symm I
    · simp only [PartialEquiv.symm_source, PartialEquiv.restr_coe_symm,
        toPartialEquiv_coe_symm, OpenPartialHomeomorph.symm_toPartialEquiv]
      simp only [f', PartialEquiv.trans_target, target_eq, toPartialEquiv_coe_symm]
      exact fun _ hy ↦ mem_preimage.mp <| mem_of_mem_inter_right hy
  let U₀ : Set M := f.source ∩ g.source
  have hU₀nhds : U₀ ∈ nhds x := by
    apply IsOpen.mem_nhds (IsOpen.inter f.open_source g.open_source) ⟨hfSource, hgSource⟩
  let U : Set E := (f') '' U₀
  have hUf'target : U ⊆ f'.target := by
    rw [← f'.image_source_eq_target]
    apply image_mono
    simpa only [f', PartialEquiv.trans_source, source_eq, preimage_univ, inter_univ] using
      (inter_subset_left : U₀ ⊆ f.source)
  have hf'MapsToU : MapsTo f'.symm U U₀ := by
    intro _ ⟨_, _, hzy⟩
    subst hzy
    simp_all [f', U₀]
  let g' : PartialEquiv M E := g.toPartialEquiv.trans I.toPartialEquiv
  have hg'Cont : ContinuousOn g' U₀ := by
    apply ContinuousOn.mono ?_ <| show U₀ ⊆ g.source by exact inter_subset_right
    apply ContinuousOn.comp ?_ g.continuousOn g.mapsTo
    apply ContinuousOn.mono ?_ (subset_univ _)
    exact continuousOn_univ.mpr <| I.continuous
  let φ : PartialEquiv E E := f'.symm.trans g'
  have hφCont : ContinuousOn φ U := by
    simp only [PartialEquiv.coe_trans, φ]
    apply ContinuousOn.comp (g := g') hg'Cont ?_ hf'MapsToU
    exact ContinuousOn.mono hf'symmCont hUf'target
  rw [← show φ (I (f x)) = I (g x)
      by simp [φ, f', g', OpenPartialHomeomorph.left_inv f hfSource]]
  have hUφsource : U ⊆ φ.source := by
    rw [PartialEquiv.trans_source]
    simp only [PartialEquiv.symm_source, subset_inter_iff]
    simp_all only [PartialEquiv.coe_trans_symm, OpenPartialHomeomorph.coe_toPartialEquiv_symm,
      toPartialEquiv_coe_symm, PartialEquiv.trans_target, target_eq, Filter.inter_mem_iff,
      PartialEquiv.coe_trans, toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe, Function.comp_apply,
      subset_inter_iff, image_subset_iff, mapsTo_inter, mapsTo_image_iff, and_self,
      PartialEquiv.trans_source, source_eq, preimage_univ, inter_univ, true_and, f', U₀, U, g', φ]
    exact hf'MapsToU.2
  have hUNhds : U ∈ nhds (I (f x)) := by
    apply nhds_of_nhdsWithin_of_nhds hfInterior
    rw [show U = I '' (f '' U₀) by rw [← image_comp I f U₀]; rfl]
    apply image_mem_nhdsWithin I
    exact OpenPartialHomeomorph.image_mem_nhds f hfSource hU₀nhds
  let φ' : PartialEquiv E E := φ.restr U
  have hφCont'U : ContinuousOn φ' U := by
    simpa only [φ', PartialEquiv.restr_coe] using hφCont
  have hφ'Cont : ContinuousOn φ' φ'.source := by
    rw [PartialEquiv.restr_source φ U]
    exact ContinuousOn.mono hφCont'U inter_subset_right
  have : U ⊆ φ'.source := by
    rw [PartialEquiv.restr_source]
    exact subset_inter hUφsource fun _ a ↦ a
  obtain hMapsNhds := maps_nhds_to_nhds E hφ'Cont hUNhds this
  have : (φ') '' U ⊆ range I := by
    rintro _ ⟨z, _, hzy⟩
    rw [← hzy]
    exact mem_range_self (g (f'.symm z))
  exact Filter.mem_of_superset hMapsNhds this

variable (I) in
/-- A point lies in the interior of M iff *any* `OpenPartialHomeomorph M H`
sends it to the interior of `range I`. -/
theorem isInteriorPoint_iff_any_chart {x : M} [HasInvarianceOfDomain E]
    {f : OpenPartialHomeomorph M H} (hfSource : x ∈ f.source) :
    I.IsInteriorPoint x ↔ I (f x) ∈ interior (range I) := by
  constructor <;> intro hx
  · apply isInteriorPoint_iff.mp at hx
    exact (independence_of_interior I M (ChartedSpace.mem_chart_source x) hfSource)
          (by exact (interior_mono <| extChartAt_target_subset_range x) hx)
  · apply isInteriorPoint_iff.mpr
    apply (chartAt H x).mem_interior_extend_target
          ((chartAt H x).map_source <| ChartedSpace.mem_chart_source x)
    exact independence_of_interior I M hfSource (ChartedSpace.mem_chart_source x) hx

variable (I) in
/-- A point lies on the boundary of M iff *any* `OpenPartialHomeomorph M H`
sends it to the frontier of `range I`. -/
theorem isBoundaryPoint_iff_any_chart {x : M} [HasInvarianceOfDomain E]
    {f : OpenPartialHomeomorph M H} (hfSource : x ∈ f.source) :
    (I.IsBoundaryPoint x ↔ I (f x) ∈ frontier (range I)) := by
  apply not_iff_not.mp
  apply Iff.trans <| Iff.symm <| I.isInteriorPoint_iff_not_isBoundaryPoint x
  obtain hInt := isInteriorPoint_iff_any_chart I hfSource
  rw [← self_sdiff_frontier] at hInt
  constructor <;> intro hx
  · exact notMem_of_mem_sdiff <| hInt.mp hx
  · exact hInt.mpr <| mem_sdiff_of_mem (mem_range_self (f x)) hx

/-- An embedded open part of the model vector space has open image in a manifold modeled on
`I`.  This is the manifold-with-boundary form of invariance of domain needed at an interior
edge of an embedded finite triangle complex.

The use of the *extended* target chart is important: if the image point were on the manifold
boundary, invariance of domain would produce an ambient vector-space neighborhood contained in
`range I`, which is impossible there. -/
theorem isOpen_range_of_isOpen_of_continuous_injective
    (I : ModelWithCorners 𝕜 E H) [HasInvarianceOfDomain E]
    {U : Set E} (hU : IsOpen U) (f : U → M)
    (hfcont : Continuous f) (hfinj : Function.Injective f) :
    IsOpen (Set.range f) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨u, rfl⟩
  let c : PartialEquiv M E := extChartAt I (f u)
  let f₀ : E → M :=
    Function.extend ((↑) : U → E) f (fun _ ↦ f u)
  have hf₀_eq (x : U) : f₀ x.1 = f x := by
    exact Function.Injective.extend_apply Subtype.val_injective f
      (fun _ ↦ f u) x
  have hf₀_cont : ContinuousOn f₀ U := by
    rw [continuousOn_iff_continuous_restrict]
    convert hfcont using 1
    funext x
    exact hf₀_eq x
  let W : Set E := U ∩ f₀ ⁻¹' c.source
  have hWopen : IsOpen W :=
    hf₀_cont.isOpen_inter_preimage hU (isOpen_extChartAt_source (I := I) (f u))
  have huW : u.1 ∈ W := by
    refine ⟨u.2, ?_⟩
    change f₀ u.1 ∈ c.source
    rw [hf₀_eq u]
    exact mem_extChartAt_source (I := I) (f u)
  let g : E → E := fun x ↦ c (f₀ x)
  have hg_cont : ContinuousOn g W := by
    apply (continuousOn_extChartAt (I := I) (f u)).comp
      (hf₀_cont.mono inter_subset_left)
    exact fun x hx ↦ hx.2
  have hg_inj : Set.InjOn g W := by
    intro x hx y hy hxy
    have hf₀xy : f₀ x = f₀ y :=
      c.injOn hx.2 hy.2 hxy
    have hfx :
        f (⟨x, hx.1⟩ : U) = f (⟨y, hy.1⟩ : U) := by
      rw [← hf₀_eq ⟨x, hx.1⟩, ← hf₀_eq ⟨y, hy.1⟩]
      exact hf₀xy
    exact congrArg Subtype.val (hfinj hfx)
  let φ : PartialEquiv E E :=
    hg_inj.toPartialEquiv g W
  have hφ_cont : ContinuousOn φ φ.source := by
    change ContinuousOn g W
    exact hg_cont
  have hWnhds : W ∈ nhds u.1 :=
    hWopen.mem_nhds huW
  have himage :
      g '' W ∈ nhds (g u.1) := by
    have h :=
      maps_nhds_to_nhds E hφ_cont hWnhds
        (show W ⊆ φ.source by
          change W ⊆ W
          exact subset_rfl)
    change g '' W ∈ nhds (g u.1) at h
    exact h
  obtain ⟨O, hOsub, hOopen, hguO⟩ :=
    _root_.mem_nhds_iff.mp himage
  let Z : Set M := c.source ∩ c ⁻¹' O
  have hZopen : IsOpen Z :=
    (continuousOn_extChartAt (I := I) (f u)).isOpen_inter_preimage
      (isOpen_extChartAt_source (I := I) (f u)) hOopen
  have hfuZ : f u ∈ Z := by
    refine ⟨mem_extChartAt_source (I := I) (f u), ?_⟩
    change c (f u) ∈ O
    rw [← hf₀_eq u]
    exact hguO
  have hZrange : Z ⊆ Set.range f := by
    intro y hy
    have hcyO : c y ∈ O := hy.2
    obtain ⟨x, hxW, hxcoord⟩ := hOsub hcyO
    have hcy :
        c y = c (f₀ x) := by
      exact hxcoord.symm
    have hyf₀ : y = f₀ x :=
      c.injOn hy.1 hxW.2 hcy
    refine ⟨⟨x, hxW.1⟩, ?_⟩
    rw [← hf₀_eq ⟨x, hxW.1⟩]
    exact hyf₀.symm
  exact Filter.mem_of_superset (hZopen.mem_nhds hfuZ) hZrange

/-- Embedding-form wrapper for
`isOpen_range_of_isOpen_of_continuous_injective`. -/
theorem isOpen_range_of_isOpen_of_isEmbedding
    (I : ModelWithCorners 𝕜 E H) [HasInvarianceOfDomain E]
    {U : Set E} (hU : IsOpen U) (f : U → M)
    (hf : _root_.Topology.IsEmbedding f) :
    IsOpen (Set.range f) :=
  isOpen_range_of_isOpen_of_continuous_injective I hU f
    hf.continuous hf.injective

/-- At an interior point of the ambient manifold, re-embedding a fixed source cannot turn the
corresponding local sheet into a boundary point of the new image.

This is deliberately an interior-point statement.  It is false at a manifold-boundary point:
an embedding of a half-plane may bend its boundary into the ambient interior. -/
theorem mem_interior_range_of_eq_of_mem_interior_range_of_isInteriorPoint
    (I : ModelWithCorners 𝕜 E H) [HasInvarianceOfDomain E]
    {X : Type*} [TopologicalSpace X]
    {f g : X → M} (hf : _root_.Topology.IsEmbedding f)
    (hg : _root_.Topology.IsEmbedding g) {x : X}
    (hx : f x ∈ interior (Set.range f))
    (hxi : I.IsInteriorPoint (f x)) :
    g x ∈ interior (Set.range g) := by
  let z : M := f x
  let c : PartialEquiv M E := extChartAt I z
  let W : Set E :=
    interior c.target ∩ c.symm ⁻¹' interior (Set.range f)
  have hWopen : IsOpen W := by
    apply
      ((continuousOn_extChartAt_symm (I := I) z).mono interior_subset
        ).isOpen_inter_preimage isOpen_interior isOpen_interior
  have hzTarget : c z ∈ interior c.target := by
    exact I.isInteriorPoint_iff.mp hxi
  have hcz : c.symm (c z) = z :=
    c.left_inv (mem_extChartAt_source (I := I) z)
  have hczW : c z ∈ W := by
    refine ⟨hzTarget, ?_⟩
    change c.symm (c z) ∈ interior (Set.range f)
    rw [hcz]
    exact hx
  have hcSymm : Continuous (fun w : W ↦ c.symm w.1) := by
    apply ContinuousOn.restrict
    exact (continuousOn_extChartAt_symm (I := I) z).mono fun w hw ↦
      interior_subset hw.1
  let toOldRange : W → Set.range f :=
    fun w ↦ ⟨c.symm w.1, interior_subset w.2.2⟩
  have htoOldRange : Continuous toOldRange :=
    Continuous.subtype_mk hcSymm _
  let source : W → X :=
    fun w ↦ hf.toHomeomorph.symm (toOldRange w)
  have hsourceCont : Continuous source :=
    hf.toHomeomorph.symm.continuous.comp htoOldRange
  have hsourceInj : Function.Injective source := by
    intro u v huv
    have huvRange : toOldRange u = toOldRange v :=
      hf.toHomeomorph.symm.injective huv
    have huvSurface : c.symm u.1 = c.symm v.1 :=
      congrArg Subtype.val huvRange
    apply Subtype.ext
    exact c.symm.injOn (interior_subset u.2.1) (interior_subset v.2.1)
      huvSurface
  let localMap : W → M := fun w ↦ g (source w)
  have hlocalCont : Continuous localMap :=
    hg.continuous.comp hsourceCont
  have hlocalInj : Function.Injective localMap :=
    hg.injective.comp hsourceInj
  have hlocalOpen : IsOpen (Set.range localMap) :=
    isOpen_range_of_isOpen_of_continuous_injective I hWopen localMap
      hlocalCont hlocalInj
  let w₀ : W := ⟨c z, hczW⟩
  have hsourceW₀ : source w₀ = x := by
    apply hf.injective
    change (hf.toHomeomorph (source w₀)).1 = f x
    rw [hf.toHomeomorph.apply_symm_apply]
    change c.symm (c z) = f x
    exact hcz
  have hlocalAt : localMap w₀ = g x := by
    rw [show localMap w₀ = g (source w₀) by rfl, hsourceW₀]
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset
    (hlocalOpen.mem_nhds ⟨w₀, hlocalAt⟩)
  rintro y ⟨w, rfl⟩
  exact Set.mem_range_self (source w)

end LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain
end r78_classification01_block_05
/- END ClassificationOfSurfaces.Topology.InvarianceOfDomain -/

/- BEGIN ClassificationOfSurfaces.PolygonalQuotient | 6c4e3ab33438355370f3336e06b8ed879d428484542226fe22132ae7b251856e -/
section r78_classification01_block_06
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Polygonal quotient spaces

This file supplies the geometric foundation for realizing a finite surface cell complex. A
`PolygonCell n` is a genuinely indexed closed disk with `n` labelled boundary arcs. This
topological model keeps monogons and digons as genuine disks, unlike a convex hull of one or two
Euclidean vertices. Its sides are circular arcs; only their interval reparameterizations are
affine. A later PL bridge is therefore still needed if consumers require straight Euclidean edges.

For a family of cells, `PolygonGluing.PreRealization` is their disjoint union with the sum topology.
A set of `PolygonGluing.Identification`s prescribes either the identity or the affine reversal
`t ↦ 1 - t` between pairs of sides. `PolygonGluing.setoid` is the equivalence relation generated
by those point identifications, and `PolygonGluing.Realization` has the quotient topology.

`PolygonCell 0` is a disk with no marked sides. It is deliberately not identified with the
empty-word sphere. The cell-complex adapter therefore presents the sphere as two oppositely
oriented monogons instead of using `PolygonCell 0`. Keeping that choice out of this generic layer
prevents a side-free disk from silently acquiring the wrong topology.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-- A closed disk whose boundary is divided into `n` labelled sides. -/
structure PolygonCell (_n : ℕ) where
  /-- The `val` declaration. -/
  val : ℂ
  property : val ∈ Metric.closedBall (0 : ℂ) 1

namespace PolygonCell

instance (n : ℕ) : CoeOut (PolygonCell n) ℂ :=
  ⟨val⟩

@[ext]
theorem ext {n : ℕ} {x y : PolygonCell n} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  simp_all

noncomputable instance (n : ℕ) : TopologicalSpace (PolygonCell n) :=
  TopologicalSpace.induced val inferInstance

theorem continuous_val {n : ℕ} : Continuous (fun x : PolygonCell n => x.val) :=
  continuous_induced_dom

/-- The side count is marking data only: changing it does not change the underlying closed
disk. -/
noncomputable def castHomeomorph {m n : ℕ} (h : m = n) :
    PolygonCell m ≃ₜ PolygonCell n := by
  subst n
  exact Homeomorph.refl _

theorem castHomeomorph_val {m n : ℕ} (h : m = n) (x : PolygonCell m) :
    (castHomeomorph h x).val = x.val := by
  subst n
  rfl

/-- The unit circle included in a polygonal cell. -/
def ofCircle (n : ℕ) : C(Circle, PolygonCell n) where
  toFun z := ⟨z, by
    rw [Metric.mem_closedBall]
    exact z.property.le⟩
  continuous_toFun := continuous_induced_rng.2 continuous_subtype_val

/-- The angle swept out by side `i` at parameter `t`. -/
noncomputable def sideAngle {n : ℕ} (i : Fin n) (t : unitInterval) : ℝ :=
  2 * Real.pi * ((i.val : ℝ) + t) / n

theorem continuous_sideAngle {n : ℕ} (i : Fin n) : Continuous (sideAngle i) := by
  unfold sideAngle
  fun_prop

/-- Side `i` of an `n`-sided cell, parameterized in boundary order. -/
noncomputable def side {n : ℕ} (i : Fin n) : C(unitInterval, PolygonCell n) where
  toFun t := ofCircle n (Circle.exp (sideAngle i t))
  continuous_toFun :=
    (ofCircle n).continuous.comp (Circle.exp.continuous.comp (continuous_sideAngle i))

/-- Side `i` traversed in the opposite direction. -/
noncomputable def reversedSide {n : ℕ} (i : Fin n) : C(unitInterval, PolygonCell n) where
  toFun t := side i (unitInterval.symm t)
  continuous_toFun := (side i).continuous.comp unitInterval.continuous_symm

theorem reversedSide_apply {n : ℕ} (i : Fin n) (t : unitInterval) :
    reversedSide i t = side i (unitInterval.symm t) :=
  rfl

theorem castHomeomorph_side {m n : ℕ} (h : m = n) (i : Fin m)
    (t : unitInterval) :
    castHomeomorph h (side i t) = side (Fin.cast h i) t := by
  subst n
  rfl

theorem reversedSide_zero {n : ℕ} (i : Fin n) : reversedSide i 0 = side i 1 := by
  rw [reversedSide_apply]
  simp only [unitInterval.symm_zero]

@[simp]
theorem reversedSide_one {n : ℕ} (i : Fin n) : reversedSide i 1 = side i 0 := by
  rw [reversedSide_apply]
  simp only [unitInterval.symm_one]

/-- Consecutive sides meet at their common cyclic endpoint. -/
theorem side_one_eq_rotate_zero {n : ℕ} (i : Fin n) :
    side i 1 = side (finRotate n i) 0 := by
  apply PolygonCell.ext
  change (Circle.exp (sideAngle i 1) : ℂ) =
    (Circle.exp (sideAngle (finRotate n i) 0) : ℂ)
  apply congr_arg (fun z : Circle => (z : ℂ))
  apply Circle.exp_eq_exp.mpr
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt i.pos)
  by_cases hi : i = Fin.last n
  · subst i
    refine ⟨1, ?_⟩
    rw [finRotate_last]
    simp [sideAngle]
    field_simp
  · refine ⟨0, ?_⟩
    simp only [sideAngle, Nat.succ_eq_add_one, finRotate_apply, Int.cast_zero, zero_mul,
      add_zero]
    rw [Fin.val_add_one_of_lt (Fin.val_lt_last hi)]
    push_cast
    rw [add_zero]

/-- Every side lies on the boundary circle of its polygonal cell. -/
theorem side_mem_sphere {n : ℕ} (i : Fin n) (t : unitInterval) :
    (side i t : ℂ) ∈ Metric.sphere 0 1 := by
  exact (Circle.exp (sideAngle i t)).property

/-- Every boundary point of a cell with at least one side belongs to a marked side. -/
theorem exists_side_eq_of_mem_sphere {n : ℕ} (hn : 0 < n) (x : PolygonCell n)
    (hx : (x : ℂ) ∈ Metric.sphere 0 1) :
    ∃ i : Fin n, ∃ t : unitInterval, side i t = x := by
  let z : Circle := ⟨x.val, hx⟩
  obtain ⟨θ, hθ, hθeq⟩ :=
    Circle.periodic_exp.exists_mem_Ico₀ Real.two_pi_pos z.val.arg
  have hθz : Circle.exp θ = z := hθeq.symm.trans (Circle.exp_arg z)
  let r : ℝ := θ * n / (2 * Real.pi)
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg (mul_nonneg hθ.1 (Nat.cast_nonneg n)) Real.two_pi_pos.le
  have hr_lt : r < n := by
    dsimp [r]
    rw [div_lt_iff₀ Real.two_pi_pos]
    exact (mul_lt_mul_of_pos_right hθ.2 (Nat.cast_pos.2 hn)).trans_eq (mul_comm _ _)
  let i : Fin n := ⟨⌊r⌋₊, (Nat.floor_lt hr_nonneg).2 hr_lt⟩
  let t : unitInterval := ⟨r - ⌊r⌋₊, sub_nonneg.2 (Nat.floor_le hr_nonneg), by
    have ht : r - (⌊r⌋₊ : ℝ) < 1 := by
      rw [sub_lt_iff_lt_add]
      simpa only [add_comm] using Nat.lt_floor_add_one r
    exact ht.le⟩
  refine ⟨i, t, ?_⟩
  apply PolygonCell.ext
  change (Circle.exp (sideAngle i t) : ℂ) = x.val
  have hangle : sideAngle i t = θ := by
    dsimp [sideAngle, i, t, r]
    field_simp [hn.ne', Real.pi_ne_zero]
    ring
  rw [hangle, hθz]

/-- Boundary membership is equivalent to membership in one of the marked sides. -/
theorem mem_sphere_iff_exists_side {n : ℕ} (hn : 0 < n) (x : PolygonCell n) :
    (x : ℂ) ∈ Metric.sphere 0 1 ↔
      ∃ i : Fin n, ∃ t : unitInterval, side i t = x := by
  constructor
  · exact exists_side_eq_of_mem_sphere hn x
  · rintro ⟨i, t, rfl⟩
    exact side_mem_sphere i t

/-- The marked sides cover exactly the boundary circle of a nonzero-sided cell. -/
theorem iUnion_range_side {n : ℕ} (hn : 0 < n) :
    (⋃ i : Fin n, Set.range (side i)) =
      {x : PolygonCell n | (x : ℂ) ∈ Metric.sphere 0 1} := by
  ext x
  simpa only [Set.mem_iUnion, Set.mem_range, Set.mem_setOf_eq] using
    (mem_sphere_iff_exists_side hn x).symm

/-- The unique side of a monogon is a loop. -/
theorem side_zero_eq_side_one_monogon (i : Fin 1) : side i 0 = side i 1 := by
  simpa using (side_one_eq_rotate_zero i).symm

/-- The two sides of a digon meet at their middle vertex. -/
theorem side_zero_one_eq_side_one_zero_digon :
    side (0 : Fin 2) 1 = side (1 : Fin 2) 0 := by
  simpa using side_one_eq_rotate_zero (0 : Fin 2)

end PolygonCell

namespace PolygonGluing

universe u

/-- The disjoint union of a family of polygonal cells. -/
abbrev PreRealization (Face : Type u) (sideCount : Face → ℕ) : Type u :=
  Σ f, PolygonCell (sideCount f)

/-- A labelled side in a family of polygonal cells. -/
structure Side (Face : Type u) (sideCount : Face → ℕ) where
  /-- The `face` declaration. -/
  face : Face
  /-- The `index` declaration. -/
  index : Fin (sideCount face)

namespace Side

/-- A point on a labelled side, included in the disjoint union. -/
noncomputable def point {Face : Type u} {sideCount : Face → ℕ}
    (s : Side Face sideCount) (t : unitInterval) : PreRealization Face sideCount :=
  ⟨s.face, PolygonCell.side s.index t⟩

end Side

/-- The two affine self-homeomorphisms of the unit interval used to glue polygon sides. -/
inductive ParameterDirection where
  | same
  | opposite
deriving DecidableEq, Repr

namespace ParameterDirection

/-- The affine interval homeomorphism associated to a parameter direction. -/
def homeomorph : ParameterDirection → (unitInterval ≃ₜ unitInterval)
  | same => Homeomorph.refl unitInterval
  | opposite => unitInterval.symmHomeomorph

theorem homeomorph_same : homeomorph same = Homeomorph.refl unitInterval :=
  rfl

theorem homeomorph_opposite : homeomorph opposite = unitInterval.symmHomeomorph :=
  rfl

@[simp]
theorem homeomorph_same_apply (t : unitInterval) : homeomorph same t = t :=
  rfl

theorem homeomorph_opposite_apply (t : unitInterval) :
    homeomorph opposite t = unitInterval.symm t :=
  rfl

end ParameterDirection

/-- Instructions for identifying two polygon sides with an affine parameter map. -/
structure Identification (Face : Type u) (sideCount : Face → ℕ) where
  /-- The `source` declaration. -/
  source : Side Face sideCount
  /-- The `target` declaration. -/
  target : Side Face sideCount
  /-- The `direction` declaration. -/
  direction : ParameterDirection

namespace Identification

/-- The affine parameter homeomorphism of a side identification. -/
def parameter {Face : Type u} {sideCount : Face → ℕ}
    (identification : Identification Face sideCount) : unitInterval ≃ₜ unitInterval :=
  identification.direction.homeomorph

/-- Identify two sides with the same parameter direction. -/
def sameDirection {Face : Type u} {sideCount : Face → ℕ}
    (source target : Side Face sideCount) : Identification Face sideCount where
  source := source
  target := target
  direction := .same

/-- Identify two sides with the parameter direction reversed. -/
def oppositeDirection {Face : Type u} {sideCount : Face → ℕ}
    (source target : Side Face sideCount) : Identification Face sideCount where
  source := source
  target := target
  direction := .opposite

@[simp]
theorem parameter_sameDirection {Face : Type u} {sideCount : Face → ℕ}
    (source target : Side Face sideCount) :
    (sameDirection source target).parameter = Homeomorph.refl unitInterval :=
  rfl

@[simp]
theorem parameter_oppositeDirection {Face : Type u} {sideCount : Face → ℕ}
    (source target : Side Face sideCount) :
    (oppositeDirection source target).parameter = unitInterval.symmHomeomorph :=
  rfl

end Identification

/-- The elementary point identifications prescribed by a collection of side gluings. -/
inductive Generator {Face : Type u} {sideCount : Face → ℕ}
    (identifications : Set (Identification Face sideCount)) :
    PreRealization Face sideCount → PreRealization Face sideCount → Prop
  | glue (identification : Identification Face sideCount)
      (h : identification ∈ identifications) (t : unitInterval) :
      Generator identifications (identification.source.point t)
        (identification.target.point (identification.parameter t))

/-- The equivalence relation generated by the prescribed side identifications. -/
def setoid {Face : Type u} {sideCount : Face → ℕ}
    (identifications : Set (Identification Face sideCount)) :
    Setoid (PreRealization Face sideCount) :=
  Relation.EqvGen.setoid (Generator identifications)

@[simp]
theorem setoid_empty {Face : Type u} {sideCount : Face → ℕ} :
    setoid (∅ : Set (Identification Face sideCount)) = ⊥ := by
  apply Setoid.ext
  intro x y
  constructor
  · intro h
    change Relation.EqvGen (Generator ∅) x y at h
    induction h with
    | rel _ _ hxy =>
        cases hxy with
        | glue identification hi t => simp at hi
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    change x = y at h
    subst y
    exact Relation.EqvGen.refl x

theorem related_of_mem {Face : Type u} {sideCount : Face → ℕ}
    {identifications : Set (Identification Face sideCount)}
    (identification : Identification Face sideCount) (h : identification ∈ identifications)
    (t : unitInterval) :
    setoid identifications (identification.source.point t)
      (identification.target.point (identification.parameter t)) :=
  Relation.EqvGen.rel _ _ (Generator.glue identification h t)

/-- The quotient of the polygonal disjoint union by the generated side identifications. -/
abbrev Realization {Face : Type u} {sideCount : Face → ℕ}
    (identifications : Set (Identification Face sideCount)) : Type u :=
  Quotient (setoid identifications)

/-- The quotient map from the disjoint union to the glued realization. -/
def mk {Face : Type u} {sideCount : Face → ℕ}
    (identifications : Set (Identification Face sideCount)) :
    PreRealization Face sideCount → Realization identifications :=
  @Quotient.mk' _ (setoid identifications)

theorem continuous_mk {Face : Type u} {sideCount : Face → ℕ}
    (identifications : Set (Identification Face sideCount)) :
    Continuous (mk identifications) :=
  continuous_quotient_mk'

theorem isQuotientMap_mk {Face : Type u} {sideCount : Face → ℕ}
    (identifications : Set (Identification Face sideCount)) :
    _root_.Topology.IsQuotientMap (mk identifications) :=
  isQuotientMap_quotient_mk'

/-- A prescribed side gluing identifies the corresponding points in the quotient. -/
theorem mk_source_eq_mk_target {Face : Type u} {sideCount : Face → ℕ}
    {identifications : Set (Identification Face sideCount)}
    (identification : Identification Face sideCount) (h : identification ∈ identifications)
    (t : unitInterval) :
    mk identifications (identification.source.point t) =
      mk identifications (identification.target.point (identification.parameter t)) :=
  Quotient.sound (related_of_mem identification h t)

/-- A relation-preserving homeomorphism descends to polygonal realizations. -/
noncomputable def realizationCongr
    {Face₁ : Type u} {sideCount₁ : Face₁ → ℕ}
    {Face₂ : Type u} {sideCount₂ : Face₂ → ℕ}
    {identifications₁ : Set (Identification Face₁ sideCount₁)}
    {identifications₂ : Set (Identification Face₂ sideCount₂)}
    (e : PreRealization Face₁ sideCount₁ ≃ₜ PreRealization Face₂ sideCount₂)
    (h : ∀ x y, setoid identifications₁ x y ↔ setoid identifications₂ (e x) (e y)) :
    Realization identifications₁ ≃ₜ Realization identifications₂ :=
  Homeomorph.Quotient.congr e h

/-- Equal generated relations give homeomorphic realizations on a fixed pre-space. -/
noncomputable def realizationCongrRight
    {Face : Type u} {sideCount : Face → ℕ}
    {identifications₁ identifications₂ : Set (Identification Face sideCount)}
    (h : ∀ x y, setoid identifications₁ x y ↔ setoid identifications₂ x y) :
    Realization identifications₁ ≃ₜ Realization identifications₂ :=
  Homeomorph.Quotient.congrRight h

end PolygonGluing

end ClassificationOfSurfaces
end Topology
end LeanEval
end r78_classification01_block_06
/- END ClassificationOfSurfaces.PolygonalQuotient -/

/- BEGIN ClassificationOfSurfaces.PolygonCellRadial | db451e85a50b7bb2e1ce0d69b0e09ee7fe8e871f03c3664a1190e187a6bd0293 -/
section r78_classification01_block_07
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Radial extension of circle homeomorphisms

Every `PolygonCell n` has the closed unit disk as its carrier. This file implements the radial
extension (Alexander trick) of a homeomorphism of the unit circle. The extension preserves the
norm exactly, is continuous at the origin by that norm identity, and restricts to the selected
circle homeomorphism on the boundary.

The side-count indices of the source and target cells are independent phantom parameters. A
later boundary reparameterization only needs to construct a circle homeomorphism with the desired
action on marked arcs; `PolygonCell.radialHomeomorph` then supplies the disk homeomorphism.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

open Complex

namespace Circle

/-- The direction of a nonzero complex number as a point of the unit circle. -/
noncomputable def direction (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨z / ‖z‖, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_norm]
    exact div_self (norm_ne_zero_iff.mpr hz)⟩

@[simp]
theorem coe_direction (z : ℂ) (hz : z ≠ 0) :
    (direction z hz : ℂ) = z / ‖z‖ :=
  rfl

theorem continuous_direction :
    Continuous (fun w : {w : ℂ // w ≠ 0} =>
      direction (w : ℂ) w.property) := by
  apply continuous_induced_rng.2
  change Continuous (fun w : {w : ℂ // w ≠ 0} =>
    (w : ℂ) / ‖(w : ℂ)‖)
  have hnorm : Continuous (fun w : {w : ℂ // w ≠ 0} =>
      (‖(w : ℂ)‖ : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_subtype_val.norm
  exact continuous_subtype_val.div₀ hnorm fun w =>
    ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr w.property)

/-- Radially extend a circle homeomorphism to the complex plane, fixing the origin. -/
noncomputable def radialMap (h : Circle ≃ₜ Circle) (z : ℂ) : ℂ :=
  if hz : z = 0 then 0
  else (‖z‖ : ℂ) * (h (direction z hz) : ℂ)

@[simp]
theorem radialMap_zero (h : Circle ≃ₜ Circle) :
    radialMap h 0 = 0 := by
  simp [radialMap]

theorem radialMap_of_ne (h : Circle ≃ₜ Circle) {z : ℂ} (hz : z ≠ 0) :
    radialMap h z = (‖z‖ : ℂ) * (h (direction z hz) : ℂ) := by
  simp [radialMap, hz]

/-- Radial extension preserves distance from the origin exactly. -/
@[simp]
theorem norm_radialMap (h : Circle ≃ₜ Circle) (z : ℂ) :
    ‖radialMap h z‖ = ‖z‖ := by
  by_cases hz : z = 0
  · subst z
    simp
  · rw [radialMap_of_ne h hz, norm_mul, Circle.norm_coe]
    simp

theorem radialMap_ne_zero (h : Circle ≃ₜ Circle) {z : ℂ} (hz : z ≠ 0) :
    radialMap h z ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_radialMap]
  exact norm_ne_zero_iff.mpr hz

/-- The direction of a radial image is the selected image direction. -/
theorem direction_radialMap (h : Circle ≃ₜ Circle) {z : ℂ} (hz : z ≠ 0) :
    direction (radialMap h z) (radialMap_ne_zero h hz) =
      h (direction z hz) := by
  apply Subtype.ext
  rw [coe_direction, radialMap_of_ne h hz]
  simp only [norm_mul, Circle.norm_coe, mul_one, norm_real,
    Real.norm_eq_abs, abs_norm]
  field_simp [norm_ne_zero_iff.mpr hz]

/-- Extending the inverse circle homeomorphism gives the inverse radial map. -/
theorem radialMap_symm_apply (h : Circle ≃ₜ Circle) (z : ℂ) :
    radialMap h.symm (radialMap h z) = z := by
  by_cases hz : z = 0
  · subst z
    simp
  · rw [radialMap_of_ne h.symm (radialMap_ne_zero h hz),
      direction_radialMap h hz, h.symm_apply_apply, norm_radialMap,
      coe_direction]
    field_simp [norm_ne_zero_iff.mpr hz]

theorem continuousAt_radialMap_zero (h : Circle ≃ₜ Circle) :
    ContinuousAt (radialMap h) 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro z hz
  rw [radialMap_zero, dist_zero_right, norm_radialMap,
    ← dist_zero_right]
  exact hz

theorem continuousAt_radialMap_of_ne (h : Circle ≃ₜ Circle)
    {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt (radialMap h) z := by
  have hrestrict :
      Continuous (fun w : {w : ℂ // w ≠ 0} => radialMap h w) := by
    have heq :
        (fun w : {w : ℂ // w ≠ 0} => radialMap h w) =
          fun w : {w : ℂ // w ≠ 0} => (‖(w : ℂ)‖ : ℂ) *
            (h (direction (w : ℂ) w.property) : ℂ) := by
      funext w
      exact radialMap_of_ne h w.property
    rw [heq]
    have hnorm : Continuous (fun w : {w : ℂ // w ≠ 0} =>
        (‖(w : ℂ)‖ : ℂ)) :=
      Complex.continuous_ofReal.comp continuous_subtype_val.norm
    exact hnorm.mul
      (continuous_subtype_val.comp
        (h.continuous.comp continuous_direction))
  have hOn : ContinuousOn (radialMap h) ({0}ᶜ : Set ℂ) := by
    rw [continuousOn_iff_continuous_restrict]
    exact hrestrict
  exact (hOn z hz).continuousAt (isOpen_compl_singleton.mem_nhds hz)

theorem continuous_radialMap (h : Circle ≃ₜ Circle) :
    Continuous (radialMap h) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst z
    exact continuousAt_radialMap_zero h
  · exact continuousAt_radialMap_of_ne h hz

/-- On the unit circle, radial extension is exactly the original homeomorphism. -/
@[simp]
theorem radialMap_coe (h : Circle ≃ₜ Circle) (z : Circle) :
    radialMap h (z : ℂ) = (h z : ℂ) := by
  rw [radialMap_of_ne h z.coe_ne_zero, z.norm_coe]
  have hdirection : direction (z : ℂ) z.coe_ne_zero = z := by
    apply Circle.ext
    rw [coe_direction, z.norm_coe]
    simp
  rw [hdirection]
  simp

end Circle

namespace PolygonCell

/-- Radially extend a circle homeomorphism between closed polygon-cell carriers. -/
noncomputable def radialHomeomorph {n m : ℕ} (h : Circle ≃ₜ Circle) :
    PolygonCell n ≃ₜ PolygonCell m where
  toFun z := ⟨Circle.radialMap h z.val, by
    rw [Metric.mem_closedBall, dist_zero_right, Circle.norm_radialMap]
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property⟩
  invFun z := ⟨Circle.radialMap h.symm z.val, by
    rw [Metric.mem_closedBall, dist_zero_right, Circle.norm_radialMap]
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property⟩
  left_inv := by
    intro z
    apply PolygonCell.ext
    exact Circle.radialMap_symm_apply h z.val
  right_inv := by
    intro z
    apply PolygonCell.ext
    exact Circle.radialMap_symm_apply h.symm z.val
  continuous_toFun := by
    apply continuous_induced_rng.2
    exact Circle.continuous_radialMap h |>.comp PolygonCell.continuous_val
  continuous_invFun := by
    apply continuous_induced_rng.2
    exact Circle.continuous_radialMap h.symm |>.comp PolygonCell.continuous_val

@[simp]
theorem radialHomeomorph_apply_val {n m : ℕ} (h : Circle ≃ₜ Circle)
    (z : PolygonCell n) :
    (radialHomeomorph (n := n) (m := m) h z).val =
      Circle.radialMap h z.val :=
  rfl

/-- The radial cell homeomorphism restricts to the selected circle homeomorphism. -/
@[simp]
theorem radialHomeomorph_ofCircle {n m : ℕ} (h : Circle ≃ₜ Circle)
    (z : Circle) :
    radialHomeomorph h (ofCircle n z) = ofCircle m (h z) := by
  apply PolygonCell.ext
  exact Circle.radialMap_coe h z

end PolygonCell

end LeanEval.Topology.ClassificationOfSurfaces
end r78_classification01_block_07
/- END ClassificationOfSurfaces.PolygonCellRadial -/

/- BEGIN ClassificationOfSurfaces.Representatives | 4610448be8faca5b5e36288421751025c706acf654d54fd84aff4a72a2630076 -/
section r78_classification01_block_08
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Eval representatives and normal-form indices

The Lean-Eval challenge owns `Complex.ClosedUnitDisc`, `OrientableRel`, and
`NonOrientableRel`; they are imported verbatim from `LeanEval/ChallengeDeps.lean`. This file adds
only the project-owned sphere abbreviation and the index type used by the normal-form reduction.
-/

open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-- The sphere branch in the eval theorem. -/
abbrev SphereRepresentative : Type :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The named normal forms that should eventually be realized by quotient spaces. -/
inductive NormalForm where
  | sphere
  | orientable (handles boundaryComponents : ℕ)
  | nonOrientable (crosscaps boundaryComponents : ℕ)
deriving DecidableEq, Repr

/-- The normal forms that actually appear in the Lean Eval conclusion.

The orientable sphere is represented by the separate sphere branch, so an orientable polygonal
normal form must have a handle or a boundary component; nonorientable forms must have at least one
crosscap. -/
def NormalForm.IsEvalAdmissible : NormalForm → Prop
  | NormalForm.sphere => True
  | NormalForm.orientable handles boundaryComponents =>
      1 ≤ handles ∨ 1 ≤ boundaryComponents
  | NormalForm.nonOrientable crosscaps _boundaryComponents => 1 ≤ crosscaps

end ClassificationOfSurfaces
end Topology
end LeanEval
end r78_classification01_block_08
/- END ClassificationOfSurfaces.Representatives -/

/- BEGIN ClassificationOfSurfaces.Moise.PlaneComplex | b0577b783eaff2f58bb05ce499f2bdbe03f4bafbdf40f0b8905e53701fb57066 -/
section r78_classification01_block_09
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Finite simplicial complexes in the plane

The shared geometric foundation for the Moise route (Moise, *Geometric Topology in Dimensions
2 and 3*, Ch. 0 and Ch. 7 conventions): finite complexes of genuine affine simplexes in the
Euclidean plane.

The support of a `PlaneComplex` is *defined* as the union of the convex hulls of its faces, vertex
positions are actual points, faces are affinely independent, and distinct faces meet in the hull
of their shared vertex set. None of these fields is satisfiable by bookkeeping alone:
`face_inter` is a genuine geometric constraint (it fails, for example, for two triangles that
overlap in an open region).

`IsAffineOn`/`IsPLOn` give the honest piecewise-linear predicates: a map is PL on a complex when
it is affine on every face of some subdivision.  A generic continuous map is *not* PL on any
complex with a 2-face, in contrast to the vacuous `IsPLOnSimplexes` this replaces.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- The Euclidean plane used throughout the Moise route. -/
abbrev Plane : Type :=
  EuclideanSpace ℝ (Fin 2)

/-- A closed triangle in the plane: the convex hull of three affinely independent points. -/
def IsTriangle (C : Set Plane) : Prop :=
  ∃ p : Fin 3 → Plane, AffineIndependent ℝ p ∧ C = convexHull ℝ (Set.range p)

/-- Two plane points with equal coordinates are equal. -/
theorem plane_ext {p q : Plane} (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- Affine independence transports to the inclusion of a finite set of points contained in the
range of the independent family. -/
theorem affineIndependent_finset_coe {ι : Type*} {f : ι → Plane}
    (hf : AffineIndependent ℝ f) {S : Finset Plane} (hS : ∀ a ∈ S, a ∈ Set.range f) :
    AffineIndependent ℝ ((↑) : S → Plane) := by
  classical
  choose g hg using fun a : S => hS a.1 a.2
  have hinj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    rw [← hg a, ← hg b, hab]
  have heq : ((↑) : S → Plane) = f ∘ g := by
    funext a
    exact (hg a).symm
  rw [heq]
  exact hf.comp_embedding ⟨g, hinj⟩

/-- Every finite set of at most two distinct plane points is affinely independent. -/
theorem affineIndependent_finset_of_card_le_two (A : Finset Plane) (hcard : A.card ≤ 2) :
    AffineIndependent ℝ ((↑) : A → Plane) := by
  interval_cases h : A.card
  · rw [Finset.card_eq_zero.mp h]
    exact affineIndependent_of_subsingleton ℝ _
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact affineIndependent_of_subsingleton ℝ _
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    have hp : AffineIndependent ℝ ![a, b] := affineIndependent_of_ne (k := ℝ) hab
    apply affineIndependent_finset_coe hp
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- Adjacent edges of an affinely independent triple meet exactly in the shared vertex. -/
theorem segment_inter_segment_of_affineIndependent {x y z : Plane}
    (h : AffineIndependent ℝ ![x, y, z]) :
    segment ℝ x y ∩ segment ℝ y z = {y} := by
  classical
  have hxz : x ≠ z := h.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hS : AffineIndependent ℝ ((↑) : ({x, y, z} : Finset Plane) → Plane) := by
    refine affineIndependent_finset_coe h fun a ha => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have hsub₁ : ({x, y} : Finset Plane) ⊆ {x, y, z} := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
    tauto
  have hsub₂ : ({y, z} : Finset Plane) ⊆ {x, y, z} := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
    tauto
  have hmain := hS.convexHull_inter hsub₁ hsub₂
  have hinter : ({x, y} ∩ {y, z} : Finset Plane) = {y} := by
    ext a
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h₁, rfl | rfl⟩
      · rfl
      · rcases h₁ with rfl | rfl
        · exact absurd rfl hxz
        · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, Or.inl rfl⟩
  rw [← Finset.coe_inter, hinter] at hmain
  simpa [Finset.coe_insert, Finset.coe_singleton, convexHull_pair, convexHull_singleton]
    using hmain.symm

/-- Every positive ball about one endpoint of a nondegenerate segment contains a relative
interior point of that segment. -/
theorem exists_mem_openSegment_inter_ball {a b : Plane} (hab : a ≠ b)
    {r : ℝ} (hr : 0 < r) :
    ∃ x : Plane, x ∈ openSegment ℝ a b ∧ x ∈ Metric.ball a r := by
  let d := dist a b
  have hd : 0 < d := dist_pos.mpr hab
  let t := min ((1 : ℝ) / 2) (r / (2 * d))
  have ht : 0 < t := by
    dsimp [t]
    exact lt_min (by norm_num) (div_pos hr (by positivity))
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  let x := AffineMap.lineMap a b t
  refine ⟨x, ?_, ?_⟩
  · rw [openSegment_eq_image_lineMap]
    exact ⟨t, ⟨ht, ht1⟩, rfl⟩
  · rw [Metric.mem_ball, show dist x a = ‖t‖ * d by
      simp [x, d]]
    rw [Real.norm_eq_abs, abs_of_pos ht]
    have htle : t ≤ r / (2 * d) := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_right htle hd.le
    have hcalc : (r / (2 * d)) * d = r / 2 := by
      field_simp [hd.ne']
    rw [hcalc] at hmul
    linarith

/-- An endpoint of a nondegenerate segment cannot lie strictly between two distinct points of
that segment. -/
theorem endpoint_not_mem_openSegment_of_mem_segment {a b x y : Plane}
    (hab : a ≠ b) (hxy : x ≠ y) (hx : x ∈ segment ℝ a b)
    (hy : y ∈ segment ℝ a b) : a ∉ openSegment ℝ x y := by
  rw [segment_eq_image_lineMap] at hx hy
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  intro ha
  rw [openSegment_eq_image_lineMap] at ha
  obtain ⟨u, hu, huEq⟩ := ha
  let c := (1 - u) * s + u * t
  have hmaps : AffineMap.lineMap (k := ℝ) a b 0 = AffineMap.lineMap (k := ℝ) a b c := by
    calc
      AffineMap.lineMap (k := ℝ) a b 0 = a := by simp
      _ = AffineMap.lineMap (k := ℝ) (AffineMap.lineMap (k := ℝ) a b s)
          (AffineMap.lineMap (k := ℝ) a b t) u := huEq.symm
      _ = AffineMap.lineMap (k := ℝ) a b c := by
        ext i
        simp [c, AffineMap.lineMap_apply_module]
        ring
  have hc : c = 0 := by
    exact (AffineMap.lineMap_injective ℝ hab hmaps).symm
  have hcoeff : 0 < 1 - u := sub_pos.mpr hu.2
  have htermS : 0 ≤ (1 - u) * s := mul_nonneg hcoeff.le hs.1
  have htermT : 0 ≤ u * t := mul_nonneg hu.1.le ht.1
  have htermS0 : (1 - u) * s = 0 := by
    dsimp [c] at hc
    nlinarith
  have htermT0 : u * t = 0 := by
    dsimp [c] at hc
    nlinarith
  have hs0 : s = 0 := (mul_eq_zero.mp htermS0).resolve_left hcoeff.ne'
  have ht0 : t = 0 := (mul_eq_zero.mp htermT0).resolve_left hu.1.ne'
  apply hxy
  rw [hs0, ht0]

/-- If two collinear points bracket the midpoint of a segment and neither lies in its relative
interior, then they bracket the whole segment. -/
theorem segment_subset_of_midpoint_mem_openSegment
    {P Q A B : Plane} (hPQ : P ≠ Q)
    (hAline : A ∈ affineSpan ℝ ({P, Q} : Set Plane))
    (hBline : B ∈ affineSpan ℝ ({P, Q} : Set Plane))
    (hmid : AffineMap.lineMap P Q (1 / 2 : ℝ) ∈ openSegment ℝ A B)
    (hAoutside : A ∉ openSegment ℝ P Q)
    (hBoutside : B ∉ openSegment ℝ P Q) :
    segment ℝ P Q ⊆ segment ℝ A B := by
  obtain ⟨a, ha⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hAline
  obtain ⟨b, hb⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hBline
  rw [openSegment_eq_image_lineMap] at hmid
  obtain ⟨u, hu, hum⟩ := hmid
  have hcompose :
      AffineMap.lineMap A B u =
        AffineMap.lineMap P Q ((1 - u) * a + u * b) := by
    rw [← ha, ← hb]
    ext k
    simp [AffineMap.lineMap_apply_module]
    ring
  have hparam : (1 - u) * a + u * b = 1 / 2 := by
    apply AffineMap.lineMap_injective ℝ hPQ
    rw [← hcompose]
    exact hum
  have haOutside : a ≤ 0 ∨ 1 ≤ a := by
    by_cases ha0 : a ≤ 0
    · exact Or.inl ha0
    · right
      apply le_of_not_gt
      intro ha1
      exact hAoutside (ha ▸ lineMap_mem_openSegment ℝ P Q ⟨lt_of_not_ge ha0, ha1⟩)
  have hbOutside : b ≤ 0 ∨ 1 ≤ b := by
    by_cases hb0 : b ≤ 0
    · exact Or.inl hb0
    · right
      apply le_of_not_gt
      intro hb1
      exact hBoutside (hb ▸ lineMap_mem_openSegment ℝ P Q ⟨lt_of_not_ge hb0, hb1⟩)
  have hbracket : (a ≤ 0 ∧ 1 ≤ b) ∨ (b ≤ 0 ∧ 1 ≤ a) := by
    rcases haOutside with ha0 | ha1 <;> rcases hbOutside with hb0 | hb1
    · have hleft : (1 - u) * a ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith [hu.2]) ha0
      have hright : u * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu.1.le hb0
      exfalso
      norm_num at hparam
      linarith
    · exact Or.inl ⟨ha0, hb1⟩
    · exact Or.inr ⟨hb0, ha1⟩
    · have hleft : 0 ≤ (1 - u) * (a - 1) :=
        mul_nonneg (by linarith [hu.2]) (sub_nonneg.mpr ha1)
      have hright : 0 ≤ u * (b - 1) :=
        mul_nonneg hu.1.le (sub_nonneg.mpr hb1)
      exfalso
      norm_num at hparam
      nlinarith
  have endpoints_mem (h : a ≤ 0 ∧ 1 ≤ b) :
      P ∈ segment ℝ A B ∧ Q ∈ segment ℝ A B := by
    have hab : a ≤ b := (h.1.trans (by norm_num : (0 : ℝ) ≤ 1)).trans h.2
    have hpScalar : Wbtw ℝ a 0 b :=
      (wbtw_iff_of_le hab).mpr ⟨h.1, (by norm_num : (0 : ℝ) ≤ 1).trans h.2⟩
    have hqScalar : Wbtw ℝ a 1 b :=
      (wbtw_iff_of_le hab).mpr ⟨h.1.trans (by norm_num), h.2⟩
    have hp := hpScalar.map (AffineMap.lineMap P Q)
    have hq := hqScalar.map (AffineMap.lineMap P Q)
    rw [ha, hb] at hp hq
    simpa using And.intro hp.mem_segment hq.mem_segment
  have endpoints_mem_rev (h : b ≤ 0 ∧ 1 ≤ a) :
      P ∈ segment ℝ B A ∧ Q ∈ segment ℝ B A := by
    have hba : b ≤ a := (h.1.trans (by norm_num : (0 : ℝ) ≤ 1)).trans h.2
    have hpScalar : Wbtw ℝ b 0 a :=
      (wbtw_iff_of_le hba).mpr ⟨h.1, (by norm_num : (0 : ℝ) ≤ 1).trans h.2⟩
    have hqScalar : Wbtw ℝ b 1 a :=
      (wbtw_iff_of_le hba).mpr ⟨h.1.trans (by norm_num), h.2⟩
    have hp := hpScalar.map (AffineMap.lineMap P Q)
    have hq := hqScalar.map (AffineMap.lineMap P Q)
    rw [ha, hb] at hp hq
    simpa using And.intro hp.mem_segment hq.mem_segment
  rcases hbracket with hab | hba
  · obtain ⟨hp, hq⟩ := endpoints_mem hab
    exact (convex_segment A B).segment_subset hp hq
  · obtain ⟨hp, hq⟩ := endpoints_mem_rev hba
    rw [segment_symm] at hp hq
    exact (convex_segment A B).segment_subset hp hq

/-- If a nondegenerate segment contains two distinct points on the horizontal axis, then both
endpoints lie on that axis. -/
theorem endpoint_secondCoords_eq_zero_of_two_axis_points {a b x y : Plane}
    (_ : a ≠ b) (hxy : x ≠ y) (hx : x ∈ segment ℝ a b)
    (hy : y ∈ segment ℝ a b) (hx0 : x 1 = 0) (hy0 : y 1 = 0) :
    a 1 = 0 ∧ b 1 = 0 := by
  rw [segment_eq_image_lineMap] at hx hy
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, hty⟩ := hy
  have hst : s ≠ t := by
    intro h
    apply hxy
    rw [← hsx, ← hty, h]
  have hsCoord := congrArg (fun p : Plane => p 1) hsx
  have htCoord := congrArg (fun p : Plane => p 1) hty
  simp only [Fin.isValue, AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, hx0] at hsCoord
  simp only [Fin.isValue, AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, hy0] at htCoord
  have hprod : (s - t) * (b 1 - a 1) = 0 := by
    nlinarith
  have hba : b 1 = a 1 := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hst))
  have ha : a 1 = 0 := by
    rw [hba] at hsCoord
    nlinarith
  exact ⟨ha, hba.trans ha⟩

/-- A finite simplicial complex of affine simplexes in the plane: finitely many vertices at
genuine positions, faces of at most three affinely independent vertices, closed under nonempty
subsets, with any two face carriers meeting exactly in the carrier of their shared vertex set. -/
structure PlaneComplex where
  /-- The (finite) vertex type. -/
  Vertex : Type
  /-- The vertex type is finite. -/
  [vertexFintype : Fintype Vertex]
  /-- Vertices have decidable equality. -/
  [vertexDecidableEq : DecidableEq Vertex]
  /-- The position of each vertex in the plane. -/
  position : Vertex → Plane
  /-- Distinct vertices sit at distinct points. -/
  position_injective : Function.Injective position
  /-- The faces (simplexes) of the complex, as vertex sets. -/
  simplexes : Finset (Finset Vertex)
  /-- Faces are nonempty. -/
  nonempty_of_mem : ∀ s ∈ simplexes, s.Nonempty
  /-- Faces have at most three vertices: the complex is at most two-dimensional. -/
  card_le_three : ∀ s ∈ simplexes, s.card ≤ 3
  /-- Faces are closed under passing to nonempty subsets. -/
  down_closed : ∀ s ∈ simplexes, ∀ s' ⊆ s, s'.Nonempty → s' ∈ simplexes
  /-- The vertices of each face are affinely independent, so its carrier is a genuine geometric
  simplex of dimension `card - 1`. -/
  affineIndependent : ∀ s ∈ simplexes, AffineIndependent ℝ fun v : s => position v
  /-- Face carriers intersect exactly in the carrier of their shared vertices.  This is the
  face-to-face condition that makes the complex simplicial rather than an arbitrary union. -/
  face_inter : ∀ s ∈ simplexes, ∀ t ∈ simplexes,
    convexHull ℝ (position '' s) ∩ convexHull ℝ (position '' t) =
      convexHull ℝ (position '' ((s ∩ t : Finset Vertex) : Set Vertex))

/-- A finite mesh specified only by its maximal triangles.  This is the convenient construction
interface for line subdivision: all vertices, edges, and singleton faces are generated by
`TriangleMesh.toPlaneComplex`. -/
structure TriangleMesh where
  /-- The `Vertex` declaration. -/
  Vertex : Type
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  /-- The `position` declaration. -/
  position : Vertex → Plane
  position_injective : Function.Injective position
  /-- The `triangles` declaration. -/
  triangles : Finset (Finset Vertex)
  card_triangle : ∀ t ∈ triangles, t.card = 3
  affineIndependent_triangle : ∀ t ∈ triangles,
    AffineIndependent ℝ fun v : t => position v
  triangle_inter : ∀ s ∈ triangles, ∀ t ∈ triangles,
    convexHull ℝ (position '' s) ∩ convexHull ℝ (position '' t) =
      convexHull ℝ (position '' ((s ∩ t : Finset Vertex) : Set Vertex))

attribute [instance] PlaneComplex.vertexFintype
attribute [instance] PlaneComplex.vertexDecidableEq
attribute [instance] TriangleMesh.vertexFintype
attribute [instance] TriangleMesh.vertexDecidableEq

namespace TriangleMesh

variable (M : TriangleMesh)

/-- The mesh consisting of one geometric triangle. -/
noncomputable def single (p : Fin 3 → Plane) (hp : AffineIndependent ℝ p) : TriangleMesh where
  Vertex := Fin 3
  position := p
  position_injective := hp.injective
  triangles := {Finset.univ}
  card_triangle := by simp
  affineIndependent_triangle := by
    intro t ht
    simp only [Finset.mem_singleton] at ht
    subst t
    exact hp.comp_embedding (Function.Embedding.subtype _)
  triangle_inter := by
    intro s hs t ht
    simp only [Finset.mem_singleton] at hs ht
    subst s
    subst t
    simp

/-- Transport a triangle mesh by an affine equivalence of the plane. -/
noncomputable def mapAffineEquiv (e : Plane ≃ᵃ[ℝ] Plane) : TriangleMesh where
  Vertex := M.Vertex
  position := e ∘ M.position
  position_injective := e.injective.comp M.position_injective
  triangles := M.triangles
  card_triangle := M.card_triangle
  affineIndependent_triangle := by
    intro t ht
    exact (M.affineIndependent_triangle t ht).map' e.toAffineMap e.injective
  triangle_inter := by
    intro s hs t ht
    have hinter := M.triangle_inter s hs t ht
    simp only [Function.comp_apply, ← Set.image_image]
    change convexHull ℝ (e.toAffineMap '' (M.position '' (s : Set M.Vertex))) ∩
        convexHull ℝ (e.toAffineMap '' (M.position '' (t : Set M.Vertex))) =
      convexHull ℝ (e.toAffineMap '' (M.position '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    rw [← e.toAffineMap.image_convexHull, ← e.toAffineMap.image_convexHull,
      ← e.toAffineMap.image_convexHull]
    have hinj : Function.Injective e.toAffineMap := e.injective
    rw [← Set.image_inter hinj, hinter]

/-- Reposition the vertices of a triangle mesh while retaining its abstract triangles.  The
caller supplies the geometric nondegeneracy and face-to-face proofs for the new positions. -/
noncomputable def reposition (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex))) :
    TriangleMesh where
  Vertex := M.Vertex
  position := position'
  position_injective := hposition_injective
  triangles := M.triangles
  card_triangle := M.card_triangle
  affineIndependent_triangle := haffineIndependent
  triangle_inter := htriangle_inter

@[simp] theorem reposition_triangles (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex))) :
    (M.reposition position' hposition_injective haffineIndependent htriangle_inter).triangles =
      M.triangles := rfl

/-- Delete one maximal triangle from a mesh.  Vertices no longer used by any triangle are retained;
this keeps the vertex type and geometric positions definitionally unchanged. -/
noncomputable def eraseTriangle (t : Finset M.Vertex) : TriangleMesh where
  Vertex := M.Vertex
  position := M.position
  position_injective := M.position_injective
  triangles := M.triangles.erase t
  card_triangle := by
    intro s hs
    exact M.card_triangle s (Finset.mem_of_mem_erase hs)
  affineIndependent_triangle := by
    intro s hs
    exact M.affineIndependent_triangle s (Finset.mem_of_mem_erase hs)
  triangle_inter := by
    intro s hs u hu
    exact M.triangle_inter s (Finset.mem_of_mem_erase hs) u (Finset.mem_of_mem_erase hu)

@[simp] theorem eraseTriangle_triangles (t : Finset M.Vertex) :
    (M.eraseTriangle t).triangles = M.triangles.erase t := rfl

theorem card_eraseTriangle_triangles {t : Finset M.Vertex} (ht : t ∈ M.triangles) :
    (M.eraseTriangle t).triangles.card + 1 = M.triangles.card := by
  change (M.triangles.erase t).card + 1 = M.triangles.card
  rw [Finset.card_erase_of_mem ht]
  have : 0 < M.triangles.card := Finset.card_pos.mpr ⟨t, ht⟩
  omega

/-- Reindex a triangle mesh inside a larger finite vertex type without changing any geometric
positions.  Extra vertices of the target type may be unused. -/
noncomputable def reindex {V' : Type} [Fintype V'] [DecidableEq V']
    (position' : V' → Plane) (hposition_injective : Function.Injective position')
    (e : M.Vertex ↪ V')
    (hposition : ∀ v, position' (e v) = M.position v) : TriangleMesh where
  Vertex := V'
  position := position'
  position_injective := hposition_injective
  triangles := M.triangles.image fun t => t.map e
  card_triangle := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    rw [Finset.card_map, M.card_triangle s hs]
  affineIndependent_triangle := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    let es : s ≃ s.map e := Equiv.ofBijective
      (fun v => ⟨e v, Finset.mem_map.mpr ⟨v, v.2, rfl⟩⟩)
      ⟨fun u v huv => Subtype.ext (e.injective (congrArg Subtype.val huv)), by
        rintro ⟨v', hv'⟩
        obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hv'
        exact ⟨⟨v, hv⟩, rfl⟩⟩
    apply (affineIndependent_equiv es).mp
    have h := M.affineIndependent_triangle s hs
    convert h using 1
    funext v
    exact hposition v
  triangle_inter := by
    intro s hs t ht
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp ht
    have hinter := M.triangle_inter S hS T hT
    have himage (A : Finset M.Vertex) :
        position' '' ((A.map e : Finset V') : Set V') = M.position '' (A : Set M.Vertex) := by
      ext x
      simp only [Set.mem_image, Finset.mem_coe, Finset.mem_map]
      constructor
      · rintro ⟨v', ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨v, hv, (hposition v).symm⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨e v, ⟨v, hv, rfl⟩, hposition v⟩
    rw [himage, himage]
    rw [← Finset.map_inter, himage]
    exact hinter

/-- Keep a selected collection of maximal triangles.  Unused vertices remain in the ambient
finite vertex type; they do not contribute faces or support. -/
noncomputable def restrictTriangles (p : Finset M.Vertex → Prop) [DecidablePred p] :
    TriangleMesh where
  Vertex := M.Vertex
  position := M.position
  position_injective := M.position_injective
  triangles := M.triangles.filter p
  card_triangle := fun t ht => M.card_triangle t (Finset.mem_filter.mp ht).1
  affineIndependent_triangle := fun t ht =>
    M.affineIndependent_triangle t (Finset.mem_filter.mp ht).1
  triangle_inter := fun s hs t ht =>
    M.triangle_inter s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1

@[simp] theorem mem_restrictTriangles_triangles (p : Finset M.Vertex → Prop)
    [DecidablePred p] {t : Finset M.Vertex} :
    t ∈ (M.restrictTriangles p).triangles ↔ t ∈ M.triangles ∧ p t := by
  change t ∈ M.triangles.filter p ↔ t ∈ M.triangles ∧ p t
  rw [Finset.mem_filter]

theorem mapAffineEquiv_triangles (e : Plane ≃ᵃ[ℝ] Plane) :
    (M.mapAffineEquiv e).triangles = M.triangles := rfl

/-- The nonempty subfaces of all maximal triangles in a triangle mesh. -/
def faces : Finset (Finset M.Vertex) :=
  M.triangles.biUnion fun t => t.powerset.filter (·.Nonempty)

theorem mem_faces_iff {s : Finset M.Vertex} :
    s ∈ M.faces ↔ s.Nonempty ∧ ∃ t ∈ M.triangles, s ⊆ t := by
  simp only [faces, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powerset]
  aesop

/-- Every finite triangle mesh determines a finite plane complex. -/
noncomputable def toPlaneComplex : PlaneComplex where
  Vertex := M.Vertex
  position := M.position
  position_injective := M.position_injective
  simplexes := M.faces
  nonempty_of_mem := fun _ hs => (M.mem_faces_iff.mp hs).1
  card_le_three := by
    intro s hs
    obtain ⟨-, t, ht, hst⟩ := M.mem_faces_iff.mp hs
    exact (Finset.card_le_card hst).trans (M.card_triangle t ht).le
  down_closed := by
    intro s hs s' hs's hs'ne
    obtain ⟨-, t, ht, hst⟩ := M.mem_faces_iff.mp hs
    exact M.mem_faces_iff.mpr ⟨hs'ne, t, ht, hs's.trans hst⟩
  affineIndependent := by
    intro s hs
    obtain ⟨-, t, ht, hst⟩ := M.mem_faces_iff.mp hs
    exact (M.affineIndependent_triangle t ht).comp_embedding
      ⟨fun v : s => (⟨v.1, hst v.2⟩ : t), by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun q : t => q.1) h⟩
  face_inter := by
    intro s hs t ht
    obtain ⟨-, S, hS, hsS⟩ := M.mem_faces_iff.mp hs
    obtain ⟨-, T, hT, htT⟩ := M.mem_faces_iff.mp ht
    have hparent := M.triangle_inter S hS T hT
    have hposS : M.position '' (s : Set M.Vertex) ⊆ M.position '' (S : Set M.Vertex) :=
      Set.image_mono hsS
    have hposT : M.position '' (t : Set M.Vertex) ⊆ M.position '' (T : Set M.Vertex) :=
      Set.image_mono htT
    apply Set.Subset.antisymm
    · intro x hx
      have hxparent : x ∈ convexHull ℝ (M.position '' (S : Set M.Vertex)) ∩
          convexHull ℝ (M.position '' (T : Set M.Vertex)) :=
        ⟨convexHull_mono hposS hx.1, convexHull_mono hposT hx.2⟩
      rw [hparent] at hxparent
      have hSI : AffineIndependent ℝ
          ((↑) : (S.image M.position) → Plane) := by
        let e : S ≃ S.image M.position := Equiv.ofBijective
          (fun v => ⟨M.position v, Finset.mem_image.mpr ⟨v, v.2, rfl⟩⟩)
          ⟨fun a b hab => Subtype.ext (M.position_injective (congrArg Subtype.val hab)), by
            rintro ⟨p, hp⟩
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
            exact ⟨⟨v, hv⟩, rfl⟩⟩
        have heq : ((↑) : (S.image M.position) → Plane) ∘ e =
            (fun v : S => M.position v) := by rfl
        have hmono : AffineIndependent ℝ (((↑) : (S.image M.position) → Plane) ∘ e) := by
          rw [heq]
          exact M.affineIndependent_triangle S hS
        exact (affineIndependent_equiv e).mp hmono
      have hTI : AffineIndependent ℝ
          ((↑) : (T.image M.position) → Plane) := by
        let e : T ≃ T.image M.position := Equiv.ofBijective
          (fun v => ⟨M.position v, Finset.mem_image.mpr ⟨v, v.2, rfl⟩⟩)
          ⟨fun a b hab => Subtype.ext (M.position_injective (congrArg Subtype.val hab)), by
            rintro ⟨p, hp⟩
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
            exact ⟨⟨v, hv⟩, rfl⟩⟩
        have heq : ((↑) : (T.image M.position) → Plane) ∘ e =
            (fun v : T => M.position v) := by rfl
        have hmono : AffineIndependent ℝ (((↑) : (T.image M.position) → Plane) ∘ e) := by
          rw [heq]
          exact M.affineIndependent_triangle T hT
        exact (affineIndependent_equiv e).mp hmono
      have hsImage : s.image M.position ⊆ S.image M.position :=
        Finset.image_subset_image hsS
      have hSTImage : (S ∩ T).image M.position ⊆ S.image M.position :=
        Finset.image_subset_image Finset.inter_subset_left
      have hfirst := hSI.convexHull_inter hsImage hSTImage
      rw [← Finset.coe_inter] at hfirst
      have hxfirst : x ∈ convexHull ℝ ((s ∩ (S ∩ T)).image M.position : Set Plane) := by
        rw [Finset.image_inter _ _ M.position_injective, hfirst]
        constructor
        · simpa only [Finset.coe_image] using hx.1
        · simpa only [Finset.coe_image] using hxparent
      have hsST : s ∩ (S ∩ T) = s ∩ T := by
        ext v
        simp only [Finset.mem_inter]
        aesop
      rw [hsST] at hxfirst
      have hsTImage : (s ∩ T).image M.position ⊆ T.image M.position :=
        Finset.image_subset_image Finset.inter_subset_right
      have htImage : t.image M.position ⊆ T.image M.position :=
        Finset.image_subset_image htT
      have hsecond := hTI.convexHull_inter hsTImage htImage
      rw [← Finset.coe_inter] at hsecond
      have hxsecond : x ∈ convexHull ℝ (((s ∩ T) ∩ t).image M.position : Set Plane) := by
        rw [Finset.image_inter _ _ M.position_injective, hsecond]
        exact ⟨hxfirst, by simpa only [Finset.coe_image] using hx.2⟩
      have hinter : (s ∩ T) ∩ t = s ∩ t := by
        ext v
        simp only [Finset.mem_inter]
        aesop
      rw [hinter] at hxsecond
      simpa only [Finset.coe_image] using hxsecond
    · intro x hx
      exact ⟨convexHull_mono (Set.image_mono Finset.inter_subset_left) hx,
        convexHull_mono (Set.image_mono Finset.inter_subset_right) hx⟩

end TriangleMesh

namespace PlaneComplex

variable (K : PlaneComplex)

/-- The carrier of a face: the convex hull of its vertex positions. -/
def cellCarrier (s : Finset K.Vertex) : Set Plane :=
  convexHull ℝ (K.position '' s)

/-- The support of the complex: the union of its face carriers. -/
def support : Set Plane :=
  ⋃ s ∈ K.simplexes, K.cellCarrier s

theorem cellCarrier_subset_support {s : Finset K.Vertex} (hs : s ∈ K.simplexes) :
    K.cellCarrier s ⊆ K.support :=
  Set.subset_biUnion_of_mem hs

theorem isCompact_cellCarrier (s : Finset K.Vertex) : IsCompact (K.cellCarrier s) :=
  Set.Finite.isCompact_convexHull (𝕜 := ℝ) (s.finite_toSet.image K.position)

/-- The support of a finite plane complex is compact. -/
theorem isCompact_support : IsCompact K.support :=
  K.simplexes.finite_toSet.isCompact_biUnion fun s _ => K.isCompact_cellCarrier s

/-- Transport a finite plane complex through an affine equivalence. -/
noncomputable def mapAffineEquiv (e : Plane ≃ᵃ[ℝ] Plane) : PlaneComplex where
  Vertex := K.Vertex
  position := e ∘ K.position
  position_injective := e.injective.comp K.position_injective
  simplexes := K.simplexes
  nonempty_of_mem := K.nonempty_of_mem
  card_le_three := K.card_le_three
  down_closed := K.down_closed
  affineIndependent := by
    intro s hs
    exact (K.affineIndependent s hs).map' e.toAffineMap e.injective
  face_inter := by
    intro s hs t ht
    have hinter := K.face_inter s hs t ht
    simp only [Function.comp_apply, ← Set.image_image]
    change convexHull ℝ (e.toAffineMap '' (K.position '' (s : Set K.Vertex))) ∩
        convexHull ℝ (e.toAffineMap '' (K.position '' (t : Set K.Vertex))) =
      convexHull ℝ
        (e.toAffineMap '' (K.position '' ((s ∩ t : Finset K.Vertex) : Set K.Vertex)))
    rw [← e.toAffineMap.image_convexHull, ← e.toAffineMap.image_convexHull,
      ← e.toAffineMap.image_convexHull]
    rw [← Set.image_inter (f := e.toAffineMap) e.injective, hinter]

@[simp] theorem mapAffineEquiv_simplexes (e : Plane ≃ᵃ[ℝ] Plane) :
    (K.mapAffineEquiv e).simplexes = K.simplexes := rfl

theorem mapAffineEquiv_cellCarrier (e : Plane ≃ᵃ[ℝ] Plane)
    (s : Finset K.Vertex) :
    (K.mapAffineEquiv e).cellCarrier s = e '' K.cellCarrier s := by
  change convexHull ℝ ((e ∘ K.position) '' (s : Set K.Vertex)) =
    e '' convexHull ℝ (K.position '' (s : Set K.Vertex))
  rw [Set.image_comp]
  exact (e.toAffineMap.image_convexHull _).symm

theorem mapAffineEquiv_support (e : Plane ≃ᵃ[ℝ] Plane) :
    (K.mapAffineEquiv e).support = e '' K.support := by
  change (⋃ s ∈ K.simplexes, (K.mapAffineEquiv e).cellCarrier s) =
    e '' ⋃ s ∈ K.simplexes, K.cellCarrier s
  simp only [K.mapAffineEquiv_cellCarrier e, Set.image_iUnion]

/-- The two-dimensional faces. -/
def cells : Finset (Finset K.Vertex) :=
  K.simplexes.filter fun s => s.card = 3

/-- The edges (one-dimensional faces). -/
def edges : Finset (Finset K.Vertex) :=
  K.simplexes.filter fun s => s.card = 2

/-- The subcomplex consisting of the vertices and edges of `K`. -/
noncomputable def oneSkeleton : PlaneComplex where
  Vertex := K.Vertex
  position := K.position
  position_injective := K.position_injective
  simplexes := K.simplexes.filter fun s => s.card ≤ 2
  nonempty_of_mem := by
    intro s hs
    exact K.nonempty_of_mem s (Finset.mem_filter.mp hs).1
  card_le_three := by
    intro s hs
    exact (Finset.mem_filter.mp hs).2.trans (by omega)
  down_closed := by
    intro s hs t hts ht
    apply Finset.mem_filter.mpr
    exact ⟨K.down_closed s (Finset.mem_filter.mp hs).1 t hts ht,
      (Finset.card_le_card hts).trans (Finset.mem_filter.mp hs).2⟩
  affineIndependent := by
    intro s hs
    exact K.affineIndependent s (Finset.mem_filter.mp hs).1
  face_inter := by
    intro s hs t ht
    exact K.face_inter s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1

@[simp] theorem mem_oneSkeleton_simplexes {s : Finset K.Vertex} :
    s ∈ K.oneSkeleton.simplexes ↔ s ∈ K.simplexes ∧ s.card ≤ 2 := by
  classical
  exact Finset.mem_filter

@[simp] theorem oneSkeleton_position : K.oneSkeleton.position = K.position := rfl

@[simp] theorem oneSkeleton_cellCarrier (s : Finset K.Vertex) :
    K.oneSkeleton.cellCarrier s = K.cellCarrier s := rfl

theorem oneSkeleton_support_subset : K.oneSkeleton.support ⊆ K.support := by
  intro x hx
  rw [PlaneComplex.support] at hx ⊢
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨s, hs, hxs⟩ := hx
  obtain ⟨hsK, -⟩ := K.mem_oneSkeleton_simplexes.mp hs
  exact ⟨s, hsK, hxs⟩

theorem oneSkeleton_support_eq (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2) :
    K.oneSkeleton.support = K.support := by
  apply Set.Subset.antisymm K.oneSkeleton_support_subset
  intro x hx
  rw [PlaneComplex.support] at hx ⊢
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨s, hs, hxs⟩ := hx
  exact ⟨s, K.mem_oneSkeleton_simplexes.mpr ⟨hs, hgraph s hs⟩, hxs⟩

theorem oneSkeleton_isGraph :
    ∀ s ∈ K.oneSkeleton.simplexes, s.card ≤ 2 := by
  intro s hs
  exact (K.mem_oneSkeleton_simplexes.mp hs).2

/-- Keep the faces of `L` which lie in a face of `K`.  This is the standard way to turn an
ambient line arrangement into a subdivision subordinate to a pre-existing complex. -/
noncomputable def subordinateTo (L K : PlaneComplex) : PlaneComplex := by
  classical
  exact {
    Vertex := L.Vertex
    position := L.position
    position_injective := L.position_injective
    simplexes := L.simplexes.filter fun s =>
      ∃ t ∈ K.simplexes, L.cellCarrier s ⊆ K.cellCarrier t
    nonempty_of_mem := by
      intro s hs
      exact L.nonempty_of_mem s (Finset.mem_filter.mp hs).1
    card_le_three := by
      intro s hs
      exact L.card_le_three s (Finset.mem_filter.mp hs).1
    down_closed := by
      intro s hs u hus hu
      obtain ⟨hsL, t, htK, hst⟩ := Finset.mem_filter.mp hs
      apply Finset.mem_filter.mpr
      refine ⟨L.down_closed s hsL u hus hu, t, htK, ?_⟩
      exact (convexHull_mono (Set.image_mono hus)).trans hst
    affineIndependent := by
      intro s hs
      exact L.affineIndependent s (Finset.mem_filter.mp hs).1
    face_inter := by
      intro s hs t ht
      exact L.face_inter s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1 }

theorem mem_subordinateTo_simplexes_iff (L K : PlaneComplex) {s : Finset L.Vertex} :
    s ∈ (L.subordinateTo K).simplexes ↔
      s ∈ L.simplexes ∧ ∃ t ∈ K.simplexes, L.cellCarrier s ⊆ K.cellCarrier t := by
  classical
  exact Finset.mem_filter

@[simp] theorem subordinateTo_position (L K : PlaneComplex) :
    (L.subordinateTo K).position = L.position := rfl

@[simp] theorem subordinateTo_cellCarrier (L K : PlaneComplex) (s : Finset L.Vertex) :
    (L.subordinateTo K).cellCarrier s = L.cellCarrier s := rfl

theorem subordinateTo_support_subset (L K : PlaneComplex) :
    (L.subordinateTo K).support ⊆ K.support := by
  intro x hx
  rw [PlaneComplex.support] at hx ⊢
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨s, hs, hxs⟩ := hx
  obtain ⟨-, t, ht, hst⟩ := (L.mem_subordinateTo_simplexes_iff K).mp hs
  exact ⟨t, ht, hst hxs⟩

/-- Keep precisely the faces whose carriers lie in a prescribed geometric set. -/
noncomputable def restrictToSet (K : PlaneComplex) (A : Set Plane) : PlaneComplex := by
  classical
  exact {
    Vertex := K.Vertex
    position := K.position
    position_injective := K.position_injective
    simplexes := K.simplexes.filter fun s => K.cellCarrier s ⊆ A
    nonempty_of_mem := fun s hs => K.nonempty_of_mem s (Finset.mem_filter.mp hs).1
    card_le_three := fun s hs => K.card_le_three s (Finset.mem_filter.mp hs).1
    down_closed := by
      intro s hs t hts ht
      obtain ⟨hsK, hsA⟩ := Finset.mem_filter.mp hs
      apply Finset.mem_filter.mpr
      exact ⟨K.down_closed s hsK t hts ht,
        (convexHull_mono (Set.image_mono hts)).trans hsA⟩
    affineIndependent := fun s hs => K.affineIndependent s (Finset.mem_filter.mp hs).1
    face_inter := fun s hs t ht =>
      K.face_inter s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1 }

@[simp] theorem mem_restrictToSet_simplexes_iff (K : PlaneComplex) (A : Set Plane)
    {s : Finset K.Vertex} :
    s ∈ (K.restrictToSet A).simplexes ↔ s ∈ K.simplexes ∧ K.cellCarrier s ⊆ A := by
  classical
  exact Finset.mem_filter

@[simp] theorem restrictToSet_cellCarrier (K : PlaneComplex) (A : Set Plane)
    (s : Finset K.Vertex) :
    (K.restrictToSet A).cellCarrier s = K.cellCarrier s := rfl

theorem restrictToSet_support_subset (K : PlaneComplex) (A : Set Plane) :
    (K.restrictToSet A).support ⊆ A := by
  intro x hx
  rw [PlaneComplex.support] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨s, hs, hxs⟩ := hx
  exact (K.mem_restrictToSet_simplexes_iff A).mp hs |>.2 hxs

/-- A complex is purely two-dimensional when every face lies in a two-dimensional one. -/
def IsPure2 : Prop :=
  ∀ s ∈ K.simplexes, ∃ t ∈ K.simplexes, s ⊆ t ∧ t.card = 3

end PlaneComplex

namespace TriangleMesh

variable (M : TriangleMesh)

theorem toPlaneComplex_support :
    M.toPlaneComplex.support = ⋃ t ∈ M.triangles,
      convexHull ℝ (M.position '' (t : Set M.Vertex)) := by
  ext x
  rw [PlaneComplex.support]
  simp only [toPlaneComplex, PlaneComplex.cellCarrier, Set.mem_iUnion]
  constructor
  · rintro ⟨s, hs, hxs⟩
    obtain ⟨-, t, ht, hst⟩ := M.mem_faces_iff.mp hs
    exact ⟨t, ht, convexHull_mono (Set.image_mono hst) hxs⟩
  · rintro ⟨t, ht, hxt⟩
    refine ⟨t, ?_, hxt⟩
    exact M.mem_faces_iff.mpr ⟨Finset.card_pos.mp (by rw [M.card_triangle t ht]; omega),
      t, ht, subset_rfl⟩

theorem eraseTriangle_support_subset (t : Finset M.Vertex) :
    (M.eraseTriangle t).toPlaneComplex.support ⊆ M.toPlaneComplex.support := by
  rw [TriangleMesh.toPlaneComplex_support, TriangleMesh.toPlaneComplex_support]
  intro p hp
  simp only [eraseTriangle_triangles, Set.mem_iUnion] at hp ⊢
  obtain ⟨s, hs, hps⟩ := hp
  obtain ⟨_, hsM⟩ := Finset.mem_erase.mp hs
  exact ⟨s, hsM, hps⟩

/-- The support of a mesh is the union of one maximal triangle and the support left after
deleting it. -/
theorem support_eq_eraseTriangle_union_triangleCarrier {t : Finset M.Vertex}
    (ht : t ∈ M.triangles) :
    M.toPlaneComplex.support =
      (M.eraseTriangle t).toPlaneComplex.support ∪
        convexHull ℝ (M.position '' (t : Set M.Vertex)) := by
  rw [TriangleMesh.toPlaneComplex_support, TriangleMesh.toPlaneComplex_support]
  ext p
  simp only [eraseTriangle_triangles, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨s, hs, hps⟩
    by_cases hst : s = t
    · exact Or.inr (hst ▸ hps)
    · exact Or.inl ⟨s, Finset.mem_erase.mpr ⟨hst, hs⟩, hps⟩
  · rintro (⟨s, hs, hps⟩ | hpt)
    · exact ⟨s, (Finset.mem_erase.mp hs).2, hps⟩
    · exact ⟨t, ht, hpt⟩

theorem single_support (p : Fin 3 → Plane) (hp : AffineIndependent ℝ p) :
    (single p hp).toPlaneComplex.support = convexHull ℝ (Set.range p) := by
  rw [toPlaneComplex_support]
  ext x
  simp only [Set.mem_iUnion]
  unfold single
  constructor
  · rintro ⟨t, ht, hxt⟩
    change t ∈ ({Finset.univ} : Finset (Finset (Fin 3))) at ht
    have ht' : t = Finset.univ := Finset.mem_singleton.mp ht
    subst t
    change x ∈ convexHull ℝ
      (p '' (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3))) at hxt
    simpa using hxt
  · intro hx
    refine ⟨Finset.univ, ?_, ?_⟩
    · change (Finset.univ : Finset (Fin 3)) ∈
        ({Finset.univ} : Finset (Finset (Fin 3)))
      exact Finset.mem_singleton_self _
    · change x ∈ convexHull ℝ
        (p '' (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)))
      simpa using hx

theorem toPlaneComplex_isPure2 : M.toPlaneComplex.IsPure2 := by
  intro s hs
  obtain ⟨-, t, ht, hst⟩ := M.mem_faces_iff.mp hs
  exact ⟨t, M.mem_faces_iff.mpr ⟨Finset.card_pos.mp (by rw [M.card_triangle t ht]; omega),
      t, ht, subset_rfl⟩, hst, M.card_triangle t ht⟩

/-- The two-dimensional cells generated by a triangle mesh are exactly its listed maximal
triangles. -/
theorem toPlaneComplex_cells : M.toPlaneComplex.cells = M.triangles := by
  ext s
  constructor
  · intro hs
    rcases Finset.mem_filter.mp hs with ⟨hsFace, hsCard⟩
    obtain ⟨-, t, ht, hst⟩ := M.mem_faces_iff.mp hsFace
    have hstEq : s = t := by
      apply Finset.eq_of_subset_of_card_le hst
      change t.card ≤ s.card
      rw [M.card_triangle t ht, hsCard]
    rwa [hstEq]
  · intro hs
    apply Finset.mem_filter.mpr
    exact ⟨M.mem_faces_iff.mpr ⟨Finset.card_pos.mp (by
      rw [M.card_triangle s hs]
      omega), s, hs, subset_rfl⟩, M.card_triangle s hs⟩

/-- Affine transport carries the support of a triangle mesh to the affine image of its original
support. -/
theorem mapAffineEquiv_support (e : Plane ≃ᵃ[ℝ] Plane) :
    (M.mapAffineEquiv e).toPlaneComplex.support = e '' M.toPlaneComplex.support := by
  rw [toPlaneComplex_support, toPlaneComplex_support]
  change (⋃ t ∈ M.triangles,
      convexHull ℝ ((fun a : M.Vertex => e (M.position a)) '' (t : Set M.Vertex))) =
    e '' (⋃ t ∈ M.triangles, convexHull ℝ (M.position '' (t : Set M.Vertex)))
  have hcarrier (t : Finset M.Vertex) :
      convexHull ℝ ((fun a : M.Vertex => e (M.position a)) '' (t : Set M.Vertex)) =
        e '' convexHull ℝ (M.position '' (t : Set M.Vertex)) := by
    have himage : (fun a : M.Vertex => e (M.position a)) '' (t : Set M.Vertex) =
        e '' (M.position '' (t : Set M.Vertex)) := by
      exact (Set.image_image e M.position (t : Set M.Vertex)).symm
    rw [himage]
    change convexHull ℝ (e.toAffineMap '' (M.position '' (t : Set M.Vertex))) =
      e.toAffineMap '' convexHull ℝ (M.position '' (t : Set M.Vertex))
    exact (e.toAffineMap.image_convexHull _).symm
  ext x
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨t, ht, hxt⟩
    rw [hcarrier] at hxt
    obtain ⟨y, hyt, rfl⟩ := hxt
    exact ⟨y, ⟨t, ht, hyt⟩, rfl⟩
  · rintro ⟨y, ⟨t, ht, hyt⟩, rfl⟩
    exact ⟨t, ht, by rw [hcarrier]; exact ⟨y, hyt, rfl⟩⟩

/-- Reindexing without changing positions preserves support. -/
theorem reindex_support {V' : Type} [Fintype V'] [DecidableEq V']
    (position' : V' → Plane) (hposition_injective : Function.Injective position')
    (e : M.Vertex ↪ V') (hposition : ∀ v, position' (e v) = M.position v) :
    (M.reindex position' hposition_injective e hposition).toPlaneComplex.support =
      M.toPlaneComplex.support := by
  rw [toPlaneComplex_support, toPlaneComplex_support]
  change (⋃ t ∈ M.triangles.image fun s => s.map e,
      convexHull ℝ (position' '' (t : Set V'))) =
    ⋃ s ∈ M.triangles, convexHull ℝ (M.position '' (s : Set M.Vertex))
  have himage (s : Finset M.Vertex) :
      position' '' ((s.map e : Finset V') : Set V') = M.position '' (s : Set M.Vertex) := by
    ext x
    simp only [Set.mem_image, Finset.mem_coe, Finset.mem_map]
    constructor
    · rintro ⟨v', ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, (hposition v).symm⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨e v, ⟨v, hv, rfl⟩, hposition v⟩
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨t, ht, hxt⟩
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨s, hs, by rw [← himage]; exact hxt⟩
  · rintro ⟨s, hs, hxs⟩
    exact ⟨s.map e, Finset.mem_image.mpr ⟨s, hs, rfl⟩,
      by rw [himage]; exact hxs⟩

end TriangleMesh

namespace PlaneComplex

variable (K : PlaneComplex)

/-- `K'` subdivides `K`: same support, and every face carrier of `K'` lies inside some face
carrier of `K`. -/
def Subdivides (K' K : PlaneComplex) : Prop :=
  K'.support = K.support ∧
    ∀ s' ∈ K'.simplexes, ∃ s ∈ K.simplexes, K'.cellCarrier s' ⊆ K.cellCarrier s

theorem Subdivides.refl (K : PlaneComplex) : K.Subdivides K :=
  ⟨rfl, fun s hs => ⟨s, hs, subset_rfl⟩⟩

theorem Subdivides.trans {K₂ K₁ K₀ : PlaneComplex}
    (h₂₁ : K₂.Subdivides K₁) (h₁₀ : K₁.Subdivides K₀) :
    K₂.Subdivides K₀ := by
  constructor
  · exact h₂₁.1.trans h₁₀.1
  · intro s hs
    obtain ⟨t, ht, hst⟩ := h₂₁.2 s hs
    obtain ⟨u, hu, htu⟩ := h₁₀.2 t ht
    exact ⟨u, hu, hst.trans htu⟩

theorem Subdivides.mapAffineEquiv {K' K : PlaneComplex} (h : K'.Subdivides K)
    (e : Plane ≃ᵃ[ℝ] Plane) :
    (K'.mapAffineEquiv e).Subdivides (K.mapAffineEquiv e) := by
  constructor
  · rw [K'.mapAffineEquiv_support, K.mapAffineEquiv_support, h.1]
  · intro s hs
    change s ∈ K'.simplexes at hs
    obtain ⟨t, ht, hst⟩ := h.2 s hs
    refine ⟨t, ht, ?_⟩
    exact (K'.mapAffineEquiv_cellCarrier e s).trans_le
      ((Set.image_mono hst).trans_eq (K.mapAffineEquiv_cellCarrier e t).symm)

theorem subordinateTo_subdivides (L K : PlaneComplex)
    (hsupport : (L.subordinateTo K).support = K.support) :
    (L.subordinateTo K).Subdivides K := by
  refine ⟨hsupport, ?_⟩
  intro s hs
  obtain ⟨-, t, ht, hst⟩ := (L.mem_subordinateTo_simplexes_iff K).mp hs
  exact ⟨t, ht, hst⟩

end PlaneComplex

/-- `f` agrees with an affine map on `A`. -/
def IsAffineOn (f : Plane → Plane) (A : Set Plane) : Prop :=
  ∃ g : Plane →ᵃ[ℝ] Plane, Set.EqOn f g A

/-- `f` is piecewise linear on the complex `K`: affine on every face of some subdivision.

This is the honest PL predicate: a map that is not affine on any neighborhood of a point interior
to a 2-cell of `K` cannot satisfy it, in contrast to the vacuous `IsPLOnSimplexes` of the
retiring `PL.lean` layer. -/
def IsPLOn (K : PlaneComplex) (f : Plane → Plane) : Prop :=
  ∃ K' : PlaneComplex, K'.Subdivides K ∧
    ∀ s' ∈ K'.simplexes, IsAffineOn f (K'.cellCarrier s')

/-- `f` is a PL embedding of the support of `K`: piecewise linear and injective on the support. -/
def IsPLEmbeddingOn (K : PlaneComplex) (f : Plane → Plane) : Prop :=
  IsPLOn K f ∧ Set.InjOn f K.support

/-- A function is PL on a geometric set when the set is the support of a finite plane complex
on which the function is PL. -/
def IsPLOnSet (A : Set Plane) (f : Plane → Plane) : Prop :=
  ∃ K : PlaneComplex, K.support = A ∧ IsPLOn K f

namespace IsAffineOn

/-- Restrict an affine-on-set witness to a smaller set. -/
theorem mono {f : Plane → Plane} {A B : Set Plane} (hf : IsAffineOn f A) (hBA : B ⊆ A) :
    IsAffineOn f B := by
  obtain ⟨g, hfg⟩ := hf
  exact ⟨g, hfg.mono hBA⟩

/-- Composition of affine-on-set maps is affine when the first map carries the source set into
the set on which the second map is affine. -/
theorem comp {f g : Plane → Plane} {A B : Set Plane}
    (hg : IsAffineOn g B) (hf : IsAffineOn f A) (hmap : Set.MapsTo f A B) :
    IsAffineOn (g ∘ f) A := by
  obtain ⟨F, hfF⟩ := hf
  obtain ⟨G, hgG⟩ := hg
  refine ⟨G.comp F, fun x hx => ?_⟩
  change g (f x) = G (F x)
  rw [hfF hx, hgG (by rw [← hfF hx]; exact hmap hx)]

/-- A function agreeing with an affine map on a set is continuous there. -/
theorem continuousOn {f : Plane → Plane} {A : Set Plane} (hf : IsAffineOn f A) :
    ContinuousOn f A := by
  obtain ⟨g, hfg⟩ := hf
  exact g.continuous_of_finiteDimensional.continuousOn.congr fun x hx => hfg hx

/-- An affine-on-set map sends every segment contained in the set to the segment between the
endpoint images. -/
theorem image_segment {f : Plane → Plane} {A : Set Plane} (hf : IsAffineOn f A)
    {x y : Plane} (hsegment : segment ℝ x y ⊆ A) :
    f '' segment ℝ x y = segment ℝ (f x) (f y) := by
  obtain ⟨g, hfg⟩ := hf
  calc
    f '' segment ℝ x y = g '' segment ℝ x y :=
      Set.image_congr fun z hz => hfg (hsegment hz)
    _ = segment ℝ (g x) (g y) := _root_.image_segment ℝ g x y
    _ = segment ℝ (f x) (f y) := by
      rw [hfg (hsegment (left_mem_segment ℝ x y)),
        hfg (hsegment (right_mem_segment ℝ x y))]

/-- An affine-on-hull map carries a finite convex hull to the convex hull of the images. -/
theorem image_convexHull {f : Plane → Plane} {A : Set Plane}
    (hf : IsAffineOn f (convexHull ℝ A)) :
    convexHull ℝ (f '' A) = f '' convexHull ℝ A := by
  obtain ⟨g, hfg⟩ := hf
  have himageA : f '' A = g '' A := Set.image_congr fun x hx =>
    hfg (subset_convexHull ℝ A hx)
  rw [himageA, ← g.image_convexHull]
  exact Set.image_congr fun x hx => (hfg hx).symm

end IsAffineOn

namespace IsPLOn

/-- A map affine on the support is PL without further subdivision. -/
theorem of_affineOn_support {K : PlaneComplex} {f : Plane → Plane}
    (hf : IsAffineOn f K.support) : IsPLOn K f := by
  refine ⟨K, PlaneComplex.Subdivides.refl K, ?_⟩
  intro s hs
  obtain ⟨g, hfg⟩ := hf
  exact ⟨g, hfg.mono (K.cellCarrier_subset_support hs)⟩

/-- A PL witness on a subdivision is also a PL witness on the original complex. -/
theorem of_subdivision {K' K : PlaneComplex} {f : Plane → Plane}
    (hsubdivision : K'.Subdivides K) (hf : IsPLOn K' f) : IsPLOn K f := by
  obtain ⟨L, hL, haffine⟩ := hf
  exact ⟨L, hL.trans hsubdivision, haffine⟩

/-- A PL map is continuous on the support of its complex. -/
theorem continuousOn {K : PlaneComplex} {f : Plane → Plane} (hf : IsPLOn K f) :
    ContinuousOn f K.support := by
  obtain ⟨K', hsubdivision, haffine⟩ := hf
  rw [← hsubdivision.1]
  let carriers : K'.simplexes → Set Plane := fun s => K'.cellCarrier s.1
  have hlocal : LocallyFinite carriers := locallyFinite_of_finite carriers
  have hclosed : ∀ s, IsClosed (carriers s) := fun s =>
    (K'.isCompact_cellCarrier s.1).isClosed
  have hcontinuous : ∀ s, ContinuousOn f (carriers s) := fun s =>
    (haffine s.1 s.2).continuousOn
  have hglued := hlocal.continuousOn_iUnion hclosed hcontinuous
  simpa only [PlaneComplex.support, carriers, Set.iUnion_subtype] using hglued

/-- PL maps remain PL after affine changes of coordinates in source and target. -/
theorem affineConjugate {K : PlaneComplex} {f : Plane → Plane} (hf : IsPLOn K f)
    (source target : Plane ≃ᵃ[ℝ] Plane) :
    IsPLOn (K.mapAffineEquiv source) (fun x => target (f (source.symm x))) := by
  obtain ⟨K', hsubdivision, haffine⟩ := hf
  refine ⟨K'.mapAffineEquiv source, hsubdivision.mapAffineEquiv source, ?_⟩
  intro s hs
  change s ∈ K'.simplexes at hs
  obtain ⟨g, hfg⟩ := haffine s hs
  refine ⟨target.toAffineMap.comp (g.comp source.symm.toAffineMap), ?_⟩
  intro x hx
  have hx' : x ∈ source '' K'.cellCarrier s :=
    (K'.mapAffineEquiv_cellCarrier source s).le hx
  obtain ⟨y, hy, rfl⟩ := hx'
  change target (f (source.symm (source y))) =
    target (g (source.symm (source y)))
  rw [source.symm_apply_apply]
  exact congrArg target (hfg hy)

end IsPLOn

namespace PlaneComplex

variable (K : PlaneComplex)

theorem mem_simplexes_of_mem_cells {t : Finset K.Vertex} (ht : t ∈ K.cells) :
    t ∈ K.simplexes :=
  (Finset.mem_filter.mp ht).1

theorem card_of_mem_cells {t : Finset K.Vertex} (ht : t ∈ K.cells) : t.card = 3 :=
  (Finset.mem_filter.mp ht).2

/-- Barycentric evaluation: the point of the plane with the given barycentric weights. -/
noncomputable def baryEval (x : K.Vertex → ℝ) : Plane :=
  ∑ v, x v • K.position v

theorem continuous_baryEval :
    Continuous fun x : K.Vertex → ℝ => K.baryEval x := by
  unfold baryEval
  exact continuous_finsetSum _ fun v _ => (continuous_apply v).smul continuous_const

theorem baryEval_eq_sum_of_support {x : K.Vertex → ℝ} {t : Finset K.Vertex}
    (hsupp : ∀ v ∉ t, x v = 0) :
    K.baryEval x = ∑ v ∈ t, x v • K.position v :=
  (Finset.sum_subset (Finset.subset_univ t)
    (fun v _ hv => by rw [hsupp v hv, zero_smul])).symm

theorem sum_eq_sum_of_support {x : K.Vertex → ℝ} {t : Finset K.Vertex}
    (hsupp : ∀ v ∉ t, x v = 0) :
    ∑ v, x v = ∑ v ∈ t, x v :=
  (Finset.sum_subset (Finset.subset_univ t) (fun v _ hv => hsupp v hv)).symm

/-- Barycentric evaluation of weights supported on a face lands in that face's carrier. -/
theorem baryEval_mem_cellCarrier {x : K.Vertex → ℝ} {t : Finset K.Vertex}
    (hsupp : ∀ v ∉ t, x v = 0) (h0 : ∀ v, 0 ≤ x v) (h1 : ∑ v, x v = 1) :
    K.baryEval x ∈ K.cellCarrier t := by
  have hsum_t : ∑ v ∈ t, x v = 1 := by
    rw [← K.sum_eq_sum_of_support hsupp]
    exact h1
  rw [K.baryEval_eq_sum_of_support hsupp, cellCarrier,
    ← Finset.centerMass_eq_of_sum_1 _ _ hsum_t]
  exact Finset.centerMass_mem_convexHull t (fun v _ => h0 v) (by rw [hsum_t]; norm_num)
    (fun v hv => Set.mem_image_of_mem _ hv)

/-- Every point of a face carrier has barycentric weights supported on that face. -/
theorem exists_weights_of_mem_cellCarrier {p : Plane} {t : Finset K.Vertex}
    (hp : p ∈ K.cellCarrier t) :
    ∃ x : K.Vertex → ℝ, (∀ v ∉ t, x v = 0) ∧ (∀ v, 0 ≤ x v) ∧ (∑ v, x v = 1) ∧
      K.baryEval x = p := by
  classical
  rw [cellCarrier, ← Finset.coe_image, Finset.convexHull_eq] at hp
  obtain ⟨w, hw0, hw1, hwp⟩ := hp
  have himg : ∀ g : Plane → ℝ, ∑ q ∈ t.image K.position, g q = ∑ v ∈ t, g (K.position v) :=
    fun g => Finset.sum_image fun v _ v' _ h => K.position_injective h
  refine ⟨fun v => if v ∈ t then w (K.position v) else 0, fun v hv => by simp [hv], ?_, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ t
    · simpa [hv] using hw0 _ (Finset.mem_image_of_mem _ hv)
    · simp [hv]
  · rw [Finset.sum_ite_mem, Finset.univ_inter, ← himg]
    exact hw1
  · have hsupp : ∀ v ∉ t, (fun v => if v ∈ t then w (K.position v) else 0) v = 0 :=
      fun v hv => by simp [hv]
    rw [K.baryEval_eq_sum_of_support hsupp]
    have hite : ∑ v ∈ t, (if v ∈ t then w (K.position v) else 0) • K.position v =
        ∑ v ∈ t, w (K.position v) • K.position v :=
      Finset.sum_congr rfl fun v hv => by rw [ite_eq_left hv]
    have himg2 : ∑ q ∈ t.image K.position, w q • q =
        ∑ v ∈ t, w (K.position v) • K.position v :=
      Finset.sum_image fun v _ v' _ h => K.position_injective h
    rw [Finset.centerMass_eq_of_sum_1 _ id hw1] at hwp
    simp only [id_eq] at hwp
    rw [hite, ← himg2]
    exact hwp

/-- Barycentric weights on an affinely independent face are unique. -/
theorem baryEval_injOn_face {t : Finset K.Vertex} (ht : t ∈ K.simplexes)
    {x y : K.Vertex → ℝ}
    (hx : ∀ v ∉ t, x v = 0) (hy : ∀ v ∉ t, y v = 0)
    (hx1 : ∑ v, x v = 1) (hy1 : ∑ v, y v = 1)
    (heq : K.baryEval x = K.baryEval y) : x = y := by
  classical
  have hAI := K.affineIndependent t ht
  have hx1' : ∑ v : ↥t, x v.1 = 1 := by
    rw [Finset.sum_coe_sort t (fun v => x v), ← K.sum_eq_sum_of_support hx]
    exact hx1
  have hy1' : ∑ v : ↥t, y v.1 = 1 := by
    rw [Finset.sum_coe_sort t (fun v => y v), ← K.sum_eq_sum_of_support hy]
    exact hy1
  have hxcomb : Finset.univ.affineCombination ℝ (fun v : ↥t => K.position v)
      (fun v : ↥t => x v.1) = K.baryEval x := by
    rw [Finset.univ.affineCombination_eq_linear_combination _ _ hx1',
      K.baryEval_eq_sum_of_support hx, ← Finset.sum_coe_sort t (fun v => x v • K.position v)]
  have hycomb : Finset.univ.affineCombination ℝ (fun v : ↥t => K.position v)
      (fun v : ↥t => y v.1) = K.baryEval y := by
    rw [Finset.univ.affineCombination_eq_linear_combination _ _ hy1',
      K.baryEval_eq_sum_of_support hy, ← Finset.sum_coe_sort t (fun v => y v • K.position v)]
  have hind := hAI.indicator_eq_of_affineCombination_eq Finset.univ Finset.univ _ _ hx1' hy1'
    (by rw [hxcomb, hycomb, heq])
  funext v
  by_cases hv : v ∈ t
  · have := congrFun hind ⟨v, hv⟩
    simpa using this
  · rw [hx v hv, hy v hv]

end PlaneComplex

/-- The canonical barycentric homeomorphism from the abstract realization of a pure plane
complex to its geometric support. -/
noncomputable def PlaneComplex.realizationHomeomorph (K : PlaneComplex) (hpure : K.IsPure2) :
    GeometricRealization K.Vertex K.cells ≃ₜ K.support := by
  classical
  have hmem : ∀ x : GeometricRealization K.Vertex K.cells, K.baryEval x.1 ∈ K.support := by
    rintro ⟨x, ⟨h0, h1⟩, t, ht, hsupp⟩
    exact Set.mem_biUnion (K.mem_simplexes_of_mem_cells ht)
      (K.baryEval_mem_cellCarrier hsupp h0 h1)
  let φ : GeometricRealization K.Vertex K.cells → K.support :=
    fun x => ⟨K.baryEval x.1, hmem x⟩
  have hcont : Continuous φ :=
    Continuous.subtype_mk (K.continuous_baryEval.comp continuous_subtype_val) _
  have hinj : Function.Injective φ := by
    rintro ⟨x, ⟨hx0, hx1⟩, t, ht, hxsupp⟩ ⟨y, ⟨hy0, hy1⟩, u, hu, hysupp⟩ heqφ
    have heval : K.baryEval x = K.baryEval y := congrArg Subtype.val heqφ
    have hpx := K.baryEval_mem_cellCarrier hxsupp hx0 hx1
    have hpy := K.baryEval_mem_cellCarrier hysupp hy0 hy1
    have hpint : K.baryEval x ∈ K.cellCarrier (t ∩ u) := by
      have hfi := K.face_inter t (K.mem_simplexes_of_mem_cells ht) u
        (K.mem_simplexes_of_mem_cells hu)
      have : K.baryEval x ∈
          convexHull ℝ (K.position '' t) ∩ convexHull ℝ (K.position '' u) :=
        ⟨hpx, by rw [heval]; exact hpy⟩
      rw [hfi] at this
      exact this
    obtain ⟨z, hzsupp, hz0, hz1, hzeval⟩ := K.exists_weights_of_mem_cellCarrier hpint
    have hzt : ∀ v ∉ t, z v = 0 := fun v hv =>
      hzsupp v fun hmem => hv (Finset.mem_of_mem_inter_left hmem)
    have hzu : ∀ v ∉ u, z v = 0 := fun v hv =>
      hzsupp v fun hmem => hv (Finset.mem_of_mem_inter_right hmem)
    have hxz : x = z := K.baryEval_injOn_face (K.mem_simplexes_of_mem_cells ht)
      hxsupp hzt hx1 hz1 (by rw [hzeval])
    have hyz : y = z := K.baryEval_injOn_face (K.mem_simplexes_of_mem_cells hu)
      hysupp hzu hy1 hz1 (by rw [hzeval, ← heval])
    exact Subtype.ext (hxz.trans hyz.symm)
  have hsurj : Function.Surjective φ := by
    rintro ⟨p, hp⟩
    rw [PlaneComplex.support, Set.mem_iUnion₂] at hp
    obtain ⟨σ, hσ, hpσ⟩ := hp
    obtain ⟨t, ht, hσt, htcard⟩ := hpure σ hσ
    have hpt : p ∈ K.cellCarrier t := by
      rw [PlaneComplex.cellCarrier] at hpσ ⊢
      exact convexHull_mono (Set.image_mono (Finset.coe_subset.mpr hσt)) hpσ
    have htcells : t ∈ K.cells := Finset.mem_filter.mpr ⟨ht, htcard⟩
    obtain ⟨x, hxsupp, hx0, hx1, hxeval⟩ := K.exists_weights_of_mem_cellCarrier hpt
    exact ⟨⟨x, ⟨hx0, hx1⟩, t, htcells, hxsupp⟩, Subtype.ext hxeval⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective φ ⟨hinj, hsurj⟩) hcont

@[simp] theorem PlaneComplex.realizationHomeomorph_apply (K : PlaneComplex)
    (hpure : K.IsPure2) (x : GeometricRealization K.Vertex K.cells) :
    ((K.realizationHomeomorph hpure) x).1 = K.baryEval x.1 := rfl

/-- **Realization bridge** (elementary): a purely two-dimensional plane complex induces a
geometric triangulation of its support, by barycentric coordinates in the face containing each
point.  Injectivity is the uniqueness of barycentric coordinates on each affinely independent
face, glued across faces by the face-to-face intersection condition. -/
theorem PlaneComplex.toGeometricTriangulation (K : PlaneComplex) (hpure : K.IsPure2) :
    Nonempty (GeometricTriangulation K.support) := by
  exact ⟨{ Vertex := K.Vertex
           faces := K.cells
           faces_card := fun t ht => K.card_of_mem_cells ht
           homeo := K.realizationHomeomorph hpure }⟩

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end r78_classification01_block_09
/- END ClassificationOfSurfaces.Moise.PlaneComplex -/
