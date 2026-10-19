/- Derived from https://github.com/mccorvie/classification-of-surfaces (commit e3c7230fe78d7b056a415d9ecae6f77887046b32),
   Apache License 2.0. Modified for LiZhongQC: bundled with other upstream files, imports renamed,
   local proof repairs. See NOTICE.Classification and LICENSE.Apache-2.0 in this directory. -/
/- SchottkyClassification08: pinned classification sources (upstream e3c7230f); see BUNDLE_MAP.json and licenses/. -/
import LiZhongExternal.Classification.SchottkyClassification06
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Topology.Separation.Connected
import LiZhongExternal.Classification.SchottkyClassification02
import LiZhongExternal.Classification.SchottkyClassification04
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Homotopy.Lifting
import LiZhongExternal.Classification.SchottkyClassification05

/- BEGIN ClassificationOfSurfaces.Moise.ConeExtension | d3dd385e421484ab22476911938672403b390ee834c14d7b81b4e703d0f5bcf1 -/
section schottkyclassification08_block_01
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Coning a subdivided triangle boundary

This file contains the finite geometry used in Moise Chapter 5.  The central observation is
that radial segments from an interior point of a convex set meet only as dictated by their
endpoints on the frontier.  It is the face-to-face lemma behind the cone extension of a PL map
on a triangle boundary.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

open Filter
open scoped Pointwise Topology

/-- A nondegenerate plane triangle has infinitely many interior points. -/
theorem IsTriangle.infinite_interior {C : Set Plane} (hC : IsTriangle C) :
    (interior C).Infinite := by
  obtain ⟨p, hp, rfl⟩ := hC
  have hspan : affineSpan ℝ (Set.range p) = ⊤ :=
    (hp.affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr (by simp [Plane])
  have hne : (interior (convexHull ℝ (Set.range p))).Nonempty :=
    interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan
  obtain ⟨c, hc⟩ := hne
  have hp01 : p 0 ≠ p 1 := hp.injective.ne (by decide)
  let q := if p 0 = c then p 1 else p 0
  have hqc : q ≠ c := by
    dsimp [q]
    split_ifs with h
    · intro h1
      exact hp01 (h.trans h1.symm)
    · exact h
  have hqC : q ∈ convexHull ℝ (Set.range p) := by
    apply subset_convexHull ℝ
    dsimp [q]
    split_ifs <;> exact Set.mem_range_self _
  let m := midpoint ℝ c q
  have hmopen : m ∈ openSegment ℝ c q := midpoint_mem_openSegment c q
  have hm : m ∈ interior (convexHull ℝ (Set.range p)) :=
    (convex_convexHull ℝ (Set.range p)).openSegment_interior_self_subset_interior hc hqC hmopen
  have hmc : m ≠ c := by
    intro h
    have ht : (2 : ℝ)⁻¹ = 0 := by
      apply AffineMap.lineMap_injective ℝ hqc.symm
      simpa [m, midpoint] using h
    norm_num at ht
  exact (convex_convexHull ℝ (Set.range p)).interior.isPreconnected.infinite_of_nontrivial
    ⟨c, hc, m, hm, fun h => hmc h.symm⟩

theorem IsTriangle.convex {C : Set Plane} (hC : IsTriangle C) : Convex ℝ C := by
  obtain ⟨p, -, rfl⟩ := hC
  exact convex_convexHull ℝ (Set.range p)

theorem IsTriangle.isCompact {C : Set Plane} (hC : IsTriangle C) : IsCompact C := by
  obtain ⟨p, -, rfl⟩ := hC
  exact (Set.finite_range p).isCompact_convexHull (𝕜 := ℝ)

theorem IsTriangle.frontier_nonempty {C : Set Plane} (hC : IsTriangle C) :
    (frontier C).Nonempty := by
  obtain ⟨p, -, rfl⟩ := hC
  apply nonempty_frontier_iff.mpr
  constructor
  · exact ⟨p 0, subset_convexHull ℝ _ (Set.mem_range_self 0)⟩
  · intro h
    have hb := ((Set.finite_range p).isCompact_convexHull (𝕜 := ℝ)).isBounded
    rw [h] at hb
    exact NormedSpace.unbounded_univ ℝ Plane hb

/-- An interior cone point can be chosen away from any prescribed finite family of points. -/
theorem IsTriangle.exists_interior_not_mem_range {C : Set Plane} (hC : IsTriangle C)
    {ι : Type*} [Finite ι] (p : ι → Plane) :
    ∃ c ∈ interior C, c ∉ Set.range p := by
  exact hC.infinite_interior.exists_notMem_finite (Set.toFinite (Set.range p))

/-- Every point of a compact convex body lies on a radial segment from an interior point to the
frontier. -/
theorem exists_frontier_endpoint {S : Set Plane} (hS : Convex ℝ S) (hcompact : IsCompact S)
    {c x : Plane} (hc : c ∈ interior S) (hx : x ∈ S)
    (hfrontier : (frontier S).Nonempty) :
    ∃ y ∈ frontier S, x ∈ segment ℝ c y := by
  let T : Set Plane := (-c) +ᵥ S
  have hTconv : Convex ℝ T := hS.vadd (-c)
  have hTcompact : IsCompact T := hcompact.vadd (-c)
  have hzero : 0 ∈ interior T := by
    change 0 ∈ interior ((-c) +ᵥ S)
    rw [interior_vadd]
    exact ⟨c, hc, by simp⟩
  have hTnhds : T ∈ nhds 0 := mem_interior_iff_mem_nhds.mp hzero
  have hTabs : Absorbent ℝ T := absorbent_nhds_zero hTnhds
  have hTbounded : Bornology.IsVonNBounded ℝ T :=
    NormedSpace.isVonNBounded_of_isBounded ℝ hTcompact.isBounded
  let v : Plane := x - c
  have hvT : v ∈ T := by
    exact ⟨x, hx, by simp [v, sub_eq_add_neg, add_comm]⟩
  by_cases hv : v = 0
  · obtain ⟨y, hy⟩ := hfrontier
    refine ⟨y, hy, ?_⟩
    have hxc : x = c := sub_eq_zero.mp hv
    rw [hxc]
    exact left_mem_segment ℝ c y
  · let g : ℝ := gauge T v
    have hgpos : 0 < g := (gauge_pos hTabs hTbounded).mpr hv
    have hgle : g ≤ 1 := gauge_le_one_of_mem hvT
    let y0 : Plane := g⁻¹ • v
    have hyGauge : gauge T y0 = 1 := by
      change gauge T (g⁻¹ • v) = 1
      rw [gauge_smul_of_nonneg (inv_nonneg.mpr hgpos.le)]
      simp [g, hgpos.ne']
    have hy0 : y0 ∈ frontier T :=
      mem_frontier_of_gauge_eq_one hTconv (mem_of_mem_nhds hTnhds) hTabs hyGauge
    let y : Plane := c + y0
    have himage : (Homeomorph.addLeft c : Plane ≃ₜ Plane) '' T = S := by
      ext z
      simp only [Homeomorph.coe_addLeft, Set.mem_image, T, Set.mem_vadd_set]
      constructor
      · rintro ⟨w, ⟨q, hq, hqw⟩, rfl⟩
        simpa [← hqw] using hq
      · intro hz
        exact ⟨-c + z, ⟨z, hz, by simp⟩, by simp⟩
    have hy : y ∈ frontier S := by
      have hfront := (Homeomorph.addLeft c : Plane ≃ₜ Plane).image_frontier T
      rw [himage] at hfront
      rw [← hfront]
      exact ⟨y0, hy0, rfl⟩
    refine ⟨y, hy, ?_⟩
    rw [segment_eq_image_lineMap]
    refine ⟨g, ⟨hgpos.le, hgle⟩, ?_⟩
    simp [y, y0, v, AffineMap.lineMap_apply_module, g, hgpos.ne']
    module

/-- Two radial segments from an interior point of a convex set cannot share a non-central point
unless their frontier endpoints agree. -/
theorem eq_of_mem_segment_interior_frontier {S : Set Plane} (hS : Convex ℝ S)
    {c x y z : Plane} (hc : c ∈ interior S) (hx : x ∈ frontier S)
    (hy : y ∈ frontier S) (hzx : z ∈ segment ℝ c x) (hzy : z ∈ segment ℝ c y)
    (hzc : z ≠ c) : x = y := by
  have hcx : c ≠ x := by
    intro h
    subst x
    exact (disjoint_interior_frontier (s := S)).le_bot ⟨hc, hx⟩
  have hcy : c ≠ y := by
    intro h
    subst y
    exact (disjoint_interior_frontier (s := S)).le_bot ⟨hc, hy⟩
  have hzx' : Wbtw ℝ c z x := mem_segment_iff_wbtw.mp hzx
  have hzy' : Wbtw ℝ c z y := mem_segment_iff_wbtw.mp hzy
  have hzv : z - c ≠ 0 := sub_ne_zero.mpr hzc
  have hxyRay : SameRay ℝ (x -ᵥ c) (y -ᵥ c) :=
    (hzx'.sameRay_vsub_left.symm.trans hzy'.sameRay_vsub_left fun hz =>
      (hzv hz).elim)
  rcases wbtw_total_of_sameRay_vsub_left hxyRay with hxy | hyx
  · by_contra hne
    have hsbtw : Sbtw ℝ c x y := ⟨hxy, hcx.symm, hne⟩
    have hxopen : x ∈ openSegment ℝ c y := by
      rw [openSegment_eq_image_lineMap]
      exact hsbtw.mem_image_Ioo
    have hxint : x ∈ interior S :=
      hS.openSegment_interior_closure_subset_interior hc (frontier_subset_closure hy) hxopen
    exact (disjoint_interior_frontier (s := S)).le_bot ⟨hxint, hx⟩
  · by_contra hne
    have hsbtw : Sbtw ℝ c y x := ⟨hyx, hcy.symm, fun h => hne h.symm⟩
    have hyopen : y ∈ openSegment ℝ c x := by
      rw [openSegment_eq_image_lineMap]
      exact hsbtw.mem_image_Ioo
    have hyint : y ∈ interior S :=
      hS.openSegment_interior_closure_subset_interior hc (frontier_subset_closure hx) hyopen
    exact (disjoint_interior_frontier (s := S)).le_bot ⟨hyint, hy⟩

/-- Coning preserves a face-to-face intersection when the base faces lie in the frontier of a
convex set and the cone point lies in its interior. -/
theorem convexHull_insert_inter_convexHull_insert {S A B : Set Plane}
    (hS : Convex ℝ S) (hA : A.Nonempty) (hB : B.Nonempty) {c : Plane}
    (hc : c ∈ interior S) (hAS : convexHull ℝ A ⊆ frontier S)
    (hBS : convexHull ℝ B ⊆ frontier S)
    (hface : convexHull ℝ A ∩ convexHull ℝ B = convexHull ℝ (A ∩ B)) :
    convexHull ℝ (insert c A) ∩ convexHull ℝ (insert c B) =
      convexHull ℝ (insert c (A ∩ B)) := by
  apply Set.Subset.antisymm
  · rintro z ⟨hzA, hzB⟩
    rw [convexHull_insert hA, convexJoin_singleton_left] at hzA
    rw [convexHull_insert hB, convexJoin_singleton_left] at hzB
    simp only [Set.mem_iUnion] at hzA hzB
    obtain ⟨a, ha, hza⟩ := hzA
    obtain ⟨b, hb, hzb⟩ := hzB
    by_cases hzc : z = c
    · subst z
      exact subset_convexHull ℝ _ (Set.mem_insert _ _)
    · have hab : a = b := eq_of_mem_segment_interior_frontier hS hc
        (hAS ha) (hBS hb) hza hzb hzc
      have haInter : a ∈ convexHull ℝ (A ∩ B) := by
        rw [← hface]
        exact ⟨ha, hab ▸ hb⟩
      exact (convex_convexHull ℝ (insert c (A ∩ B))).segment_subset
        (subset_convexHull ℝ _ (Set.mem_insert _ _))
        (convexHull_mono (Set.subset_insert c (A ∩ B)) haInter) hza
  · intro z hz
    have hleft : insert c (A ∩ B) ⊆ insert c A := by
      rintro x (rfl | ⟨hx, -⟩)
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ hx
    have hright : insert c (A ∩ B) ⊆ insert c B := by
      rintro x (rfl | ⟨-, hx⟩)
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ hx
    exact ⟨convexHull_mono hleft hz, convexHull_mono hright hz⟩

/-- The mixed cone/base face intersection used when exactly one face contains the cone point. -/
theorem convexHull_insert_inter_convexHull {S A B : Set Plane}
    (hS : Convex ℝ S) (hA : A.Nonempty) {c : Plane}
    (hc : c ∈ interior S) (hAS : convexHull ℝ A ⊆ frontier S)
    (hBS : convexHull ℝ B ⊆ frontier S)
    (hface : convexHull ℝ A ∩ convexHull ℝ B = convexHull ℝ (A ∩ B)) :
    convexHull ℝ (insert c A) ∩ convexHull ℝ B = convexHull ℝ (A ∩ B) := by
  apply Set.Subset.antisymm
  · rintro z ⟨hzA, hzB⟩
    rw [convexHull_insert hA, convexJoin_singleton_left] at hzA
    simp only [Set.mem_iUnion] at hzA
    obtain ⟨a, ha, hza⟩ := hzA
    have hzFrontier : z ∈ frontier S := hBS hzB
    have hzc : z ≠ c := by
      intro h
      subst z
      exact (disjoint_interior_frontier (s := S)).le_bot ⟨hc, hzFrontier⟩
    have haz : a = z := eq_of_mem_segment_interior_frontier hS hc
      (hAS ha) hzFrontier hza (right_mem_segment ℝ c z) hzc
    rw [← hface]
    exact ⟨haz ▸ ha, hzB⟩
  · intro z hz
    have hzA : z ∈ convexHull ℝ A := convexHull_mono Set.inter_subset_left hz
    have hzB : z ∈ convexHull ℝ B := convexHull_mono Set.inter_subset_right hz
    exact ⟨convexHull_mono (Set.subset_insert c A) hzA, hzB⟩

/-- Cone/cone intersection, including the degenerate case where one base face is empty. -/
theorem convexHull_insert_inter_convexHull_insert' {S A B : Set Plane}
    (hS : Convex ℝ S) {c : Plane} (hc : c ∈ interior S)
    (hAS : convexHull ℝ A ⊆ frontier S) (hBS : convexHull ℝ B ⊆ frontier S)
    (hface : convexHull ℝ A ∩ convexHull ℝ B = convexHull ℝ (A ∩ B)) :
    convexHull ℝ (insert c A) ∩ convexHull ℝ (insert c B) =
      convexHull ℝ (insert c (A ∩ B)) := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · have hcone : convexHull ℝ (insert c (∅ : Set Plane)) = {c} := by simp
    rw [hcone]
    simp only [Set.empty_inter, hcone]
    apply Set.Subset.antisymm
    · exact Set.inter_subset_left
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact ⟨rfl, subset_convexHull ℝ _ (Set.mem_insert _ _)⟩
  rcases B.eq_empty_or_nonempty with rfl | hB
  · have hcone : convexHull ℝ (insert c (∅ : Set Plane)) = {c} := by simp
    rw [hcone]
    simp only [Set.inter_empty, hcone]
    apply Set.Subset.antisymm
    · exact Set.inter_subset_right
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact ⟨subset_convexHull ℝ _ (Set.mem_insert _ _), rfl⟩
  exact convexHull_insert_inter_convexHull_insert hS hA hB hc hAS hBS hface

/-- Cone/base intersection, including an empty cone base. -/
theorem convexHull_insert_inter_convexHull' {S A B : Set Plane}
    (hS : Convex ℝ S) {c : Plane} (hc : c ∈ interior S)
    (hAS : convexHull ℝ A ⊆ frontier S) (hBS : convexHull ℝ B ⊆ frontier S)
    (hface : convexHull ℝ A ∩ convexHull ℝ B = convexHull ℝ (A ∩ B)) :
    convexHull ℝ (insert c A) ∩ convexHull ℝ B = convexHull ℝ (A ∩ B) := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · have hcone : convexHull ℝ (insert c (∅ : Set Plane)) = {c} := by simp
    rw [hcone]
    simp only [Set.empty_inter, convexHull_empty]
    ext z
    constructor
    · rintro ⟨hz, hzB⟩
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact (disjoint_interior_frontier (s := S)).le_bot ⟨hc, hBS hzB⟩
    · simp
  exact convexHull_insert_inter_convexHull hS hA hc hAS hBS hface

/-- An interior point and the endpoints of a nondegenerate frontier segment are not collinear. -/
theorem not_collinear_interior_frontier_segment {S : Set Plane} (hS : Convex ℝ S)
    {c a b : Plane} (hc : c ∈ interior S) (ha : a ∈ frontier S)
    (hb : b ∈ frontier S) (hab : a ≠ b) (hsegment : segment ℝ a b ⊆ frontier S) :
    ¬Collinear ℝ ({c, a, b} : Set Plane) := by
  intro hcol
  rcases hcol.wbtw_or_wbtw_or_wbtw with hcab | habc | hcba
  · have hac : a ≠ c := by
      intro h
      subst a
      exact (disjoint_interior_frontier (s := S)).le_bot ⟨hc, ha⟩
    have hs : Sbtw ℝ c a b := ⟨hcab, hac, hab⟩
    have haOpen : a ∈ openSegment ℝ c b := by
      rw [openSegment_eq_image_lineMap]
      exact hs.mem_image_Ioo
    have haInt := hS.openSegment_interior_closure_subset_interior hc
      (frontier_subset_closure hb) haOpen
    exact (disjoint_interior_frontier (s := S)).le_bot ⟨haInt, ha⟩
  · have hba : b ≠ a := hab.symm
    have hbc : b ≠ c := by
      intro h
      subst b
      exact (disjoint_interior_frontier (s := S)).le_bot ⟨hc, hb⟩
    have hs : Sbtw ℝ a b c := ⟨habc, hba, hbc⟩
    have hbOpen : b ∈ openSegment ℝ a c := by
      rw [openSegment_eq_image_lineMap]
      exact hs.mem_image_Ioo
    have hbInt := hS.openSegment_closure_interior_subset_interior
      (frontier_subset_closure ha) hc hbOpen
    exact (disjoint_interior_frontier (s := S)).le_bot ⟨hbInt, hb⟩
  · have hcFrontier : c ∈ frontier S := hsegment (Wbtw.mem_segment hcba.symm)
    exact (disjoint_interior_frontier (s := S)).le_bot ⟨hc, hcFrontier⟩

/-- Adding an interior cone point to at most two affinely independent frontier vertices preserves
affine independence. -/
theorem affineIndependent_insert_interior_of_card_le_two {S : Set Plane} (hS : Convex ℝ S)
    {A : Finset Plane} (hAcard : A.card ≤ 2)
    (hAI : AffineIndependent ℝ ((↑) : A → Plane))
    (hAS : convexHull ℝ (A : Set Plane) ⊆ frontier S) {c : Plane}
    (hc : c ∈ interior S) :
    AffineIndependent ℝ ((↑) : ↥(insert c A) → Plane) := by
  interval_cases hcard : A.card
  · have hAempty : A = ∅ := Finset.card_eq_zero.mp hcard
    subst A
    simp only [Finset.insert_empty]
    exact affineIndependent_of_subsingleton ℝ _
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
    have haFrontier : a ∈ frontier S := by
      apply hAS
      simpa only [Finset.coe_singleton] using
        subset_convexHull ℝ ({a} : Set Plane) (Set.mem_singleton a)
    have hca : c ≠ a := by
      intro h
      subst a
      exact (disjoint_interior_frontier (s := S)).le_bot ⟨hc, haFrontier⟩
    have hpair : AffineIndependent ℝ ![c, a] := affineIndependent_of_ne (k := ℝ) hca
    apply affineIndependent_finset_coe hpair
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    have haFrontier : a ∈ frontier S := by
      apply hAS
      exact subset_convexHull ℝ (↑({a, b} : Finset Plane) : Set Plane) (by simp)
    have hbFrontier : b ∈ frontier S := by
      apply hAS
      exact subset_convexHull ℝ (↑({a, b} : Finset Plane) : Set Plane) (by simp)
    have hsegment : segment ℝ a b ⊆ frontier S := by
      simpa [convexHull_pair] using hAS
    have htriple : AffineIndependent ℝ ![c, a, b] :=
      affineIndependent_iff_not_collinear_set.mpr
        (not_collinear_interior_frontier_segment hS hc haFrontier hbFrontier hab hsegment)
    apply affineIndependent_finset_coe htriple
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

namespace PlaneComplex

variable (K : PlaneComplex)

/-- Vertices which actually occur in the geometric support.  Passing to this subtype removes
irrelevant vertices that a `PlaneComplex` is allowed to carry. -/
abbrev ActiveVertex := {v : K.Vertex // K.position v ∈ K.support}

noncomputable instance activeVertexFintype : Fintype K.ActiveVertex := Fintype.ofFinite _

/-- The `activeEmbedding` declaration. -/
def activeEmbedding : K.ActiveVertex ↪ K.Vertex := Function.Embedding.subtype _

/-- The `activeSimplexes` declaration. -/
noncomputable def activeSimplexes : Finset (Finset K.ActiveVertex) :=
  Finset.univ.filter fun s => s.map K.activeEmbedding ∈ K.simplexes

@[simp] theorem mem_activeSimplexes {s : Finset K.ActiveVertex} :
    s ∈ K.activeSimplexes ↔ s.map K.activeEmbedding ∈ K.simplexes := by
  simp [activeSimplexes]

theorem active_position_image (s : Finset K.ActiveVertex) :
    (fun v : K.ActiveVertex => K.position v.1) '' (s : Set K.ActiveVertex) =
      K.position '' ((s.map K.activeEmbedding : Finset K.Vertex) : Set K.Vertex) := by
  ext x
  simp [activeEmbedding]

/-- Delete all unused vertices without changing the support or any face geometry. -/
noncomputable def active : PlaneComplex where
  Vertex := K.ActiveVertex
  position := fun v => K.position v.1
  position_injective := fun v w h => Subtype.ext (K.position_injective h)
  simplexes := K.activeSimplexes
  nonempty_of_mem := by
    intro s hs
    have hne := K.nonempty_of_mem _ (K.mem_activeSimplexes.mp hs)
    simpa using hne
  card_le_three := by
    intro s hs
    rw [← Finset.card_map K.activeEmbedding]
    exact K.card_le_three _ (K.mem_activeSimplexes.mp hs)
  down_closed := by
    intro s hs t hts htne
    apply K.mem_activeSimplexes.mpr
    apply K.down_closed _ (K.mem_activeSimplexes.mp hs)
    · exact Finset.map_subset_map.mpr hts
    · simpa using htne
  affineIndependent := by
    intro s hs
    have h := K.affineIndependent (s.map K.activeEmbedding) (K.mem_activeSimplexes.mp hs)
    let e : s ↪ (s.map K.activeEmbedding) :=
      { toFun := fun v => ⟨v.1.1, Finset.mem_map.mpr ⟨v.1, v.2, rfl⟩⟩
        inj' := by
          intro v w hvw
          have hval : v.1.1 = w.1.1 :=
            congrArg (fun q : (s.map K.activeEmbedding) => q.1) hvw
          exact Subtype.ext (Subtype.ext hval) }
    exact h.comp_embedding e
  face_inter := by
    intro s hs t ht
    have h := K.face_inter (s.map K.activeEmbedding) (K.mem_activeSimplexes.mp hs)
      (t.map K.activeEmbedding) (K.mem_activeSimplexes.mp ht)
    rw [← Finset.map_inter] at h
    simpa only [K.active_position_image] using h

theorem active_cellCarrier (s : Finset K.ActiveVertex) :
    (active K).cellCarrier s = K.cellCarrier (s.map K.activeEmbedding) := by
  exact congrArg (convexHull ℝ) (K.active_position_image s)

theorem active_support : (active K).support = K.support := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [PlaneComplex.support] at hx ⊢
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨s, hs, hxs⟩ := hx
    exact ⟨s.map K.activeEmbedding, K.mem_activeSimplexes.mp hs,
      (K.active_cellCarrier s).subset hxs⟩
  · intro x hx
    rw [PlaneComplex.support] at hx ⊢
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨s, hs, hxs⟩ := hx
    let t : Finset K.ActiveVertex := Finset.univ.filter fun v => v.1 ∈ s
    have hmap : t.map K.activeEmbedding = s := by
      apply Finset.Subset.antisymm
      · intro v hv
        obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
        exact (Finset.mem_filter.mp hw).2
      · intro v hv
        have hvCarrier : K.position v ∈ K.cellCarrier s :=
          subset_convexHull ℝ _ ⟨v, hv, rfl⟩
        let w : K.ActiveVertex := ⟨v, K.cellCarrier_subset_support hs hvCarrier⟩
        exact Finset.mem_map.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
    have ht : t ∈ K.activeSimplexes := K.mem_activeSimplexes.mpr (hmap ▸ hs)
    refine ⟨t, ht, ?_⟩
    rw [K.active_cellCarrier, hmap]
    exact hxs

/-- Removing unused vertices preserves purity of a two-dimensional complex. -/
theorem IsPure2.active (hpure : K.IsPure2) : (active K).IsPure2 := by
  intro s hs
  obtain ⟨t, ht, hst, htcard⟩ := hpure (s.map K.activeEmbedding)
    (K.mem_activeSimplexes.mp hs)
  let t' := (Finset.univ : Finset K.ActiveVertex).filter fun v => v.1 ∈ t
  have hmap : t'.map K.activeEmbedding = t := by
    apply Finset.Subset.antisymm
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
      exact (Finset.mem_filter.mp hw).2
    · intro v hv
      have hvCarrier : K.position v ∈ K.cellCarrier t :=
        subset_convexHull ℝ _ ⟨v, hv, rfl⟩
      let w : K.ActiveVertex := ⟨v, K.cellCarrier_subset_support ht hvCarrier⟩
      exact Finset.mem_map.mpr
        ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
  refine ⟨t', K.mem_activeSimplexes.mpr (hmap ▸ ht), ?_, ?_⟩
  · intro v hv
    have hvmap : K.activeEmbedding v ∈ t :=
      hst (Finset.mem_map.mpr ⟨v, hv, rfl⟩)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvmap⟩
  · have hcardmap : (t'.map K.activeEmbedding).card = t'.card :=
      Finset.card_map K.activeEmbedding
    rw [hmap, htcard] at hcardmap
    exact hcardmap.symm

/-- A plane complex supported on the frontier of a closed set has no two-dimensional face. -/
theorem card_le_two_of_support_eq_frontier {S : Set Plane} (hSclosed : IsClosed S)
    (hsupport : K.support = frontier S) {s : Finset K.Vertex} (hs : s ∈ K.simplexes) :
    s.card ≤ 2 := by
  by_contra hnot
  have hcard : s.card = 3 := by
    have hle := K.card_le_three s hs
    omega
  have hspan : affineSpan ℝ (Set.range (fun v : s => K.position v)) = ⊤ :=
    ((K.affineIndependent s hs).affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr (by
      simp [hcard, Plane])
  have hne : (interior (K.cellCarrier s)).Nonempty := by
    rw [PlaneComplex.cellCarrier]
    have himage : Set.range (fun v : s => K.position v) =
        K.position '' (s : Set K.Vertex) := by
      ext x
      simp
    rw [← himage]
    exact interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan
  have hsubset : interior (K.cellCarrier s) ⊆ interior (frontier S) :=
    interior_mono ((K.cellCarrier_subset_support hs).trans_eq hsupport)
  rw [interior_frontier hSclosed] at hsubset
  exact hne.not_subset_empty hsubset

theorem active_subdivides_left {L K : PlaneComplex} (h : L.Subdivides K) :
    (active L).Subdivides K := by
  constructor
  · rw [L.active_support, h.1]
  · intro s hs
    obtain ⟨t, ht, hst⟩ := h.2 (s.map L.activeEmbedding) (L.mem_activeSimplexes.mp hs)
    exact ⟨t, ht, (L.active_cellCarrier s).subset.trans hst⟩

/-- Vertices which occur in at least one abstract face.  Unlike `ActiveVertex`, this removes a
vertex whose geometric position happens to lie in the support without being part of any face. -/
abbrev UsedVertex := {v : K.Vertex // ∃ s ∈ K.simplexes, v ∈ s}

noncomputable instance usedVertexFintype : Fintype K.UsedVertex := Fintype.ofFinite _

/-- The `usedEmbedding` declaration. -/
def usedEmbedding : K.UsedVertex ↪ K.Vertex := Function.Embedding.subtype _

/-- The `usedSimplexes` declaration. -/
noncomputable def usedSimplexes : Finset (Finset K.UsedVertex) :=
  Finset.univ.filter fun s => s.map K.usedEmbedding ∈ K.simplexes

@[simp] theorem mem_usedSimplexes {s : Finset K.UsedVertex} :
    s ∈ K.usedSimplexes ↔ s.map K.usedEmbedding ∈ K.simplexes := by
  simp [usedSimplexes]

theorem used_position_image (s : Finset K.UsedVertex) :
    (fun v : K.UsedVertex => K.position v.1) '' (s : Set K.UsedVertex) =
      K.position '' ((s.map K.usedEmbedding : Finset K.Vertex) : Set K.Vertex) := by
  ext x
  simp [usedEmbedding]

/-- Delete vertices unused by every face, without changing the represented complex. -/
noncomputable def used : PlaneComplex where
  Vertex := K.UsedVertex
  position := fun v => K.position v.1
  position_injective := fun v w h => Subtype.ext (K.position_injective h)
  simplexes := K.usedSimplexes
  nonempty_of_mem := by
    intro s hs
    have hne := K.nonempty_of_mem _ (K.mem_usedSimplexes.mp hs)
    simpa using hne
  card_le_three := by
    intro s hs
    rw [← Finset.card_map K.usedEmbedding]
    exact K.card_le_three _ (K.mem_usedSimplexes.mp hs)
  down_closed := by
    intro s hs t hts htne
    apply K.mem_usedSimplexes.mpr
    apply K.down_closed _ (K.mem_usedSimplexes.mp hs)
    · exact Finset.map_subset_map.mpr hts
    · simpa using htne
  affineIndependent := by
    intro s hs
    have h := K.affineIndependent (s.map K.usedEmbedding) (K.mem_usedSimplexes.mp hs)
    let e : s ↪ (s.map K.usedEmbedding) :=
      { toFun := fun v => ⟨v.1.1, Finset.mem_map.mpr ⟨v.1, v.2, rfl⟩⟩
        inj' := by
          intro v w hvw
          have hval : v.1.1 = w.1.1 := congrArg (fun q => q.1) hvw
          exact Subtype.ext (Subtype.ext hval) }
    exact h.comp_embedding e
  face_inter := by
    intro s hs t ht
    have h := K.face_inter (s.map K.usedEmbedding) (K.mem_usedSimplexes.mp hs)
      (t.map K.usedEmbedding) (K.mem_usedSimplexes.mp ht)
    rw [← Finset.map_inter] at h
    simpa only [K.used_position_image] using h

theorem used_cellCarrier (s : Finset K.UsedVertex) :
    (used K).cellCarrier s = K.cellCarrier (s.map K.usedEmbedding) := by
  exact congrArg (convexHull ℝ) (K.used_position_image s)

theorem used_support : (used K).support = K.support := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [PlaneComplex.support] at hx ⊢
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨s, hs, hxs⟩ := hx
    exact ⟨s.map K.usedEmbedding, K.mem_usedSimplexes.mp hs,
      (K.used_cellCarrier s).subset hxs⟩
  · intro x hx
    rw [PlaneComplex.support] at hx ⊢
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨s, hs, hxs⟩ := hx
    let t : Finset K.UsedVertex := Finset.univ.filter fun v => v.1 ∈ s
    have hmap : t.map K.usedEmbedding = s := by
      apply Finset.Subset.antisymm
      · intro v hv
        obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
        exact (Finset.mem_filter.mp hw).2
      · intro v hv
        let w : K.UsedVertex := ⟨v, s, hs, hv⟩
        exact Finset.mem_map.mpr
          ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
    have ht : t ∈ K.usedSimplexes := K.mem_usedSimplexes.mpr (hmap ▸ hs)
    refine ⟨t, ht, ?_⟩
    rw [K.used_cellCarrier, hmap]
    exact hxs

theorem used_vertex_face (v : K.UsedVertex) :
    ({v} : Finset (used K).Vertex) ∈ (used K).simplexes := by
  apply K.mem_usedSimplexes.mpr
  obtain ⟨s, hs, hvs⟩ := v.2
  apply K.down_closed s hs {v.1}
  · simpa [usedEmbedding] using hvs
  · exact Finset.singleton_nonempty _

/-- Every face of a complex is represented by an identical geometric face after unused vertices
are removed. -/
theorem exists_used_face_eq (s : Finset K.Vertex) (hs : s ∈ K.simplexes) :
    ∃ t : Finset (used K).Vertex, t ∈ (used K).simplexes ∧
      t.map K.usedEmbedding = s ∧ (used K).cellCarrier t = K.cellCarrier s := by
  classical
  let t : Finset K.UsedVertex := Finset.univ.filter fun v => v.1 ∈ s
  have hmap : t.map K.usedEmbedding = s := by
    apply Finset.Subset.antisymm
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
      exact (Finset.mem_filter.mp hw).2
    · intro v hv
      let w : K.UsedVertex := ⟨v, s, hs, hv⟩
      exact Finset.mem_map.mpr
        ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
  refine ⟨t, K.mem_usedSimplexes.mpr (hmap ▸ hs), hmap, ?_⟩
  rw [K.used_cellCarrier, hmap]

/-- Removing vertices unused by every face preserves two-dimensional purity. -/
theorem IsPure2.used (hpure : K.IsPure2) : (used K).IsPure2 := by
  intro s hs
  obtain ⟨t, ht, hst, htcard⟩ := hpure (s.map K.usedEmbedding)
    (K.mem_usedSimplexes.mp hs)
  let t' : Finset K.UsedVertex := Finset.univ.filter fun v => v.1 ∈ t
  have hmap : t'.map K.usedEmbedding = t := by
    apply Finset.Subset.antisymm
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
      exact (Finset.mem_filter.mp hw).2
    · intro v hv
      let w : K.UsedVertex := ⟨v, t, ht, hv⟩
      exact Finset.mem_map.mpr
        ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
  refine ⟨t', K.mem_usedSimplexes.mpr (hmap ▸ ht), ?_, ?_⟩
  · intro v hv
    have hvmap : K.usedEmbedding v ∈ t :=
      hst (Finset.mem_map.mpr ⟨v, hv, rfl⟩)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvmap⟩
  · have hcardmap : (t'.map K.usedEmbedding).card = t'.card :=
      Finset.card_map K.usedEmbedding
    rw [hmap, htcard] at hcardmap
    exact hcardmap.symm

theorem used_subdivides_left {L K : PlaneComplex} (h : L.Subdivides K) :
    (used L).Subdivides K := by
  constructor
  · rw [L.used_support, h.1]
  · intro s hs
    obtain ⟨t, ht, hst⟩ := h.2 (s.map L.usedEmbedding) (L.mem_usedSimplexes.mp hs)
    exact ⟨t, ht, (L.used_cellCarrier s).subset.trans hst⟩

/-- Values prescribed on an affinely independent family extend to an affine map of the plane. -/
theorem exists_affineMap_eqOn_affineIndependent {ι : Type*} [Nonempty ι]
    (p q : ι → Plane) (hp : AffineIndependent ℝ p) :
    ∃ g : Plane →ᵃ[ℝ] Plane, ∀ i, g (p i) = q i := by
  classical
  let e : ι ≃ Set.range p := Equiv.ofBijective
    (fun i => ⟨p i, Set.mem_range_self i⟩)
    ⟨fun i j h => hp.injective (congrArg Subtype.val h), by
      rintro ⟨x, i, rfl⟩
      exact ⟨i, rfl⟩⟩
  have hRange : AffineIndependent ℝ ((↑) : Set.range p → Plane) := by
    apply (affineIndependent_equiv e).mp
    exact hp
  obtain ⟨T, hsub, hTI, hspan⟩ :=
    exists_subset_affineIndependent_affineSpan_eq_top hRange
  let b : AffineBasis T ℝ Plane :=
    ⟨((↑) : T → Plane), hTI, by
      have hrange : Set.range ((↑) : T → Plane) = T := by ext x; simp
      rw [hrange]
      exact hspan⟩
  let embed : ι → T := fun i => ⟨p i, hsub (Set.mem_range_self i)⟩
  let Q : T → Plane := fun z =>
    if hz : (z : Plane) ∈ Set.range p then q (e.symm ⟨z, hz⟩) else 0
  let i0 : T := embed (Classical.choice inferInstance)
  let l : Plane →ₗ[ℝ] Plane :=
    (b.basisOf i0).constr ℝ (fun j => Q j - Q i0)
  let g : Plane →ᵃ[ℝ] Plane :=
    { toFun := fun x => l (x - b i0) + Q i0
      linear := l
      map_vadd' := by
        intro x v
        simp only [vadd_eq_add, map_add, map_sub]
        module }
  have hgBasis (i : T) : g (b i) = Q i := by
    by_cases hi : i = i0
    · subst i
      simp [g]
    · let j : {j : T // j ≠ i0} := ⟨i, hi⟩
      change l (b i - b i0) + Q i0 = Q i
      have hl : l (b i - b i0) = Q i - Q i0 := by
        have hbasis : (b.basisOf i0) j = b i - b i0 := by
          exact b.basisOf_apply i0 j
        rw [← hbasis]
        rw [Module.Basis.constr_basis]
      rw [hl]
      abel
  refine ⟨g, fun i => ?_⟩
  have hb : b (embed i) = p i := rfl
  rw [← hb, hgBasis]
  have hmem : p i ∈ Set.range p := Set.mem_range_self i
  exact (dif_pos hmem).trans (congrArg q (e.symm_apply_apply i))

/-- Map a one-dimensional complex by a function affine on every face and injective on its
support. -/
noncomputable def mapGraph (f : Plane → Plane)
    (hvertex : ∀ v, K.position v ∈ K.support)
    (hinj : Set.InjOn f K.support)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s)) : PlaneComplex where
  Vertex := K.Vertex
  position := f ∘ K.position
  position_injective := fun v w h => K.position_injective
    (hinj (hvertex v) (hvertex w) h)
  simplexes := K.simplexes
  nonempty_of_mem := K.nonempty_of_mem
  card_le_three := fun s hs => (hgraph s hs).trans (by omega)
  down_closed := K.down_closed
  affineIndependent := by
    intro s hs
    let A : Finset Plane := s.image (f ∘ K.position)
    have hAcard : A.card ≤ 2 := by
      rw [Finset.card_image_of_injective]
      · exact hgraph s hs
      · intro v w h
        exact K.position_injective (hinj (hvertex v) (hvertex w) h)
    have hAI := affineIndependent_finset_of_card_le_two A hAcard
    let e : s ↪ A :=
      { toFun := fun v => ⟨f (K.position v), Finset.mem_image.mpr ⟨v, v.2, rfl⟩⟩
        inj' := by
          intro v w hvw
          have hval : f (K.position v.1) = f (K.position w.1) :=
            congrArg (fun q : A => q.1) hvw
          exact Subtype.ext (K.position_injective
            (hinj (hvertex v.1) (hvertex w.1) hval)) }
    exact hAI.comp_embedding e
  face_inter := by
    intro s hs t ht
    have hcarrier (u : Finset K.Vertex) (hu : u ∈ K.simplexes) :
        convexHull ℝ ((f ∘ K.position) '' (u : Set K.Vertex)) =
          f '' K.cellCarrier u := by
      rw [Set.image_comp]
      exact IsAffineOn.image_convexHull (haffine u hu)
    rw [hcarrier s hs, hcarrier t ht]
    rw [← hinj.image_inter (K.cellCarrier_subset_support hs)
      (K.cellCarrier_subset_support ht)]
    have hface : K.cellCarrier s ∩ K.cellCarrier t = K.cellCarrier (s ∩ t) := by
      simpa [PlaneComplex.cellCarrier] using K.face_inter s hs t ht
    rw [hface]
    by_cases hne : (s ∩ t).Nonempty
    · exact (hcarrier (s ∩ t) (K.down_closed s hs _ Finset.inter_subset_left hne)).symm
    · have hempty : s ∩ t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [hempty, PlaneComplex.cellCarrier]

theorem mapGraph_cellCarrier (f : Plane → Plane)
    (hvertex : ∀ v, K.position v ∈ K.support) (hinj : Set.InjOn f K.support)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s))
    {s : Finset K.Vertex} (hs : s ∈ K.simplexes) :
    (K.mapGraph f hvertex hinj hgraph haffine).cellCarrier s = f '' K.cellCarrier s := by
  change convexHull ℝ ((f ∘ K.position) '' (s : Set K.Vertex)) = _
  rw [Set.image_comp]
  exact IsAffineOn.image_convexHull (haffine s hs)

theorem mapGraph_support (f : Plane → Plane)
    (hvertex : ∀ v, K.position v ∈ K.support) (hinj : Set.InjOn f K.support)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s)) :
    (K.mapGraph f hvertex hinj hgraph haffine).support = f '' K.support := by
  rw [PlaneComplex.support, PlaneComplex.support]
  ext x
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨s, hs, hxs⟩
    rw [K.mapGraph_cellCarrier f hvertex hinj hgraph haffine hs] at hxs
    obtain ⟨y, hy, rfl⟩ := hxs
    exact ⟨y, ⟨s, hs, hy⟩, rfl⟩
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    refine ⟨s, hs, ?_⟩
    rw [K.mapGraph_cellCarrier f hvertex hinj hgraph haffine hs]
    exact ⟨y, hy, rfl⟩

theorem mapGraph_baryEval_eq (f : Plane → Plane)
    (hvertex : ∀ v, K.position v ∈ K.support) (hinj : Set.InjOn f K.support)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s))
    {s : Finset K.Vertex} (hs : s ∈ K.simplexes) {z : K.Vertex → ℝ}
    (hzsupp : ∀ v ∉ s, z v = 0) (hz0 : ∀ v, 0 ≤ z v)
    (hzsum : ∑ v, z v = 1) :
    (K.mapGraph f hvertex hinj hgraph haffine).baryEval z = f (K.baryEval z) := by
  obtain ⟨g, hfg⟩ := haffine s hs
  have hsum : ∑ v ∈ s, z v = 1 := by
    rw [← K.sum_eq_sum_of_support hzsupp]
    exact hzsum
  have hsource : K.baryEval z = s.affineCombination ℝ K.position z := by
    rw [s.affineCombination_eq_linear_combination K.position z hsum]
    exact K.baryEval_eq_sum_of_support hzsupp
  have htarget : (K.mapGraph f hvertex hinj hgraph haffine).baryEval z =
      s.affineCombination ℝ (f ∘ K.position) z := by
    rw [s.affineCombination_eq_linear_combination (f ∘ K.position) z hsum]
    change (∑ v, z v • f (K.position v)) = ∑ v ∈ s, z v • f (K.position v)
    exact (Finset.sum_subset (Finset.subset_univ s)
      (fun v _ hv => by rw [hzsupp v hv, zero_smul])).symm
  rw [htarget, hsource]
  have hfgSource : f (s.affineCombination ℝ K.position z) =
      g (s.affineCombination ℝ K.position z) := by
    rw [← hsource]
    exact hfg (K.baryEval_mem_cellCarrier hzsupp hz0 hzsum)
  rw [hfgSource, s.map_affineCombination K.position z hsum g]
  have hfg' : ∀ v ∈ s, f (K.position v) = g (K.position v) := by
    intro v hv
    exact hfg (subset_convexHull ℝ _ ⟨v, hv, rfl⟩)
  have hcomb : s.affineCombination ℝ (f ∘ K.position) z =
      s.affineCombination ℝ (g ∘ K.position) z := by
    apply Finset.affineCombination_congr s (fun _ _ => rfl)
    intro v hv
    exact hfg' v hv
  rw [hcomb]

/-- The canonical barycentric homeomorphism using all simplexes, with no purity hypothesis. -/
noncomputable def realizationHomeomorphAll :
    GeometricRealization K.Vertex K.simplexes ≃ₜ K.support := by
  classical
  have hmem : ∀ x : GeometricRealization K.Vertex K.simplexes,
      K.baryEval x.1 ∈ K.support := by
    rintro ⟨x, ⟨h0, h1⟩, t, ht, hsupp⟩
    exact Set.mem_biUnion ht (K.baryEval_mem_cellCarrier hsupp h0 h1)
  let phi : GeometricRealization K.Vertex K.simplexes → K.support :=
    fun x => ⟨K.baryEval x.1, hmem x⟩
  have hcont : Continuous phi :=
    Continuous.subtype_mk (K.continuous_baryEval.comp continuous_subtype_val) _
  have hinj : Function.Injective phi := by
    rintro ⟨x, ⟨hx0, hx1⟩, t, ht, hxsupp⟩ ⟨y, ⟨hy0, hy1⟩, u, hu, hysupp⟩ heq
    have heval : K.baryEval x = K.baryEval y := congrArg Subtype.val heq
    have hpx := K.baryEval_mem_cellCarrier hxsupp hx0 hx1
    have hpy := K.baryEval_mem_cellCarrier hysupp hy0 hy1
    have hpint : K.baryEval x ∈ K.cellCarrier (t ∩ u) := by
      have hfi := K.face_inter t ht u hu
      have hp : K.baryEval x ∈ K.cellCarrier t ∩ K.cellCarrier u :=
        ⟨hpx, by rw [heval]; exact hpy⟩
      change K.baryEval x ∈ convexHull ℝ (K.position '' (t : Set K.Vertex)) ∩
        convexHull ℝ (K.position '' (u : Set K.Vertex)) at hp
      rw [hfi] at hp
      exact hp
    obtain ⟨z, hzsupp, hz0, hz1, hzeval⟩ := K.exists_weights_of_mem_cellCarrier hpint
    have hzt : ∀ v ∉ t, z v = 0 := fun v hv =>
      hzsupp v fun hmem => hv (Finset.mem_of_mem_inter_left hmem)
    have hzu : ∀ v ∉ u, z v = 0 := fun v hv =>
      hzsupp v fun hmem => hv (Finset.mem_of_mem_inter_right hmem)
    have hxz : x = z := K.baryEval_injOn_face ht hxsupp hzt hx1 hz1 (by rw [hzeval])
    have hyz : y = z := K.baryEval_injOn_face hu hysupp hzu hy1 hz1
      (by rw [hzeval, ← heval])
    exact Subtype.ext (hxz.trans hyz.symm)
  have hsurj : Function.Surjective phi := by
    rintro ⟨p, hp⟩
    rw [PlaneComplex.support, Set.mem_iUnion₂] at hp
    obtain ⟨t, ht, hpt⟩ := hp
    obtain ⟨x, hxsupp, hx0, hx1, hxeval⟩ := K.exists_weights_of_mem_cellCarrier hpt
    exact ⟨⟨x, ⟨hx0, hx1⟩, t, ht, hxsupp⟩, Subtype.ext hxeval⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective phi ⟨hinj, hsurj⟩) hcont

@[simp] theorem realizationHomeomorphAll_apply
    (x : GeometricRealization K.Vertex K.simplexes) :
    (K.realizationHomeomorphAll x).1 = K.baryEval x.1 := rfl

/-- Reposition a plane complex while retaining its abstract simplexes. -/
noncomputable def reposition (position' : K.Vertex → Plane)
    (hinj : Function.Injective position')
    (haff : ∀ s ∈ K.simplexes, AffineIndependent ℝ fun v : s => position' v)
    (hface : ∀ s ∈ K.simplexes, ∀ t ∈ K.simplexes,
      convexHull ℝ (position' '' (s : Set K.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set K.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset K.Vertex) : Set K.Vertex))) :
    PlaneComplex where
  Vertex := K.Vertex
  position := position'
  position_injective := hinj
  simplexes := K.simplexes
  nonempty_of_mem := K.nonempty_of_mem
  card_le_three := K.card_le_three
  down_closed := K.down_closed
  affineIndependent := haff
  face_inter := hface

/-- Preserve barycentric coordinates under a repositioning of a complex. -/
noncomputable def repositionHomeomorphAll (position' : K.Vertex → Plane)
    (hinj : Function.Injective position')
    (haff : ∀ s ∈ K.simplexes, AffineIndependent ℝ fun v : s => position' v)
    (hface : ∀ s ∈ K.simplexes, ∀ t ∈ K.simplexes,
      convexHull ℝ (position' '' (s : Set K.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set K.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset K.Vertex) : Set K.Vertex))) :
    K.support ≃ₜ (K.reposition position' hinj haff hface).support :=
  K.realizationHomeomorphAll.symm.trans
    (K.reposition position' hinj haff hface).realizationHomeomorphAll

/-- The ambient function underlying barycentric repositioning, set to zero off the source
support. -/
noncomputable def repositionMap (position' : K.Vertex → Plane)
    (hinj : Function.Injective position')
    (haff : ∀ s ∈ K.simplexes, AffineIndependent ℝ fun v : s => position' v)
    (hface : ∀ s ∈ K.simplexes, ∀ t ∈ K.simplexes,
      convexHull ℝ (position' '' (s : Set K.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set K.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset K.Vertex) : Set K.Vertex))) :
    Plane → Plane := by
  classical
  exact fun x =>
    if hx : x ∈ K.support then
      (K.repositionHomeomorphAll position' hinj haff hface ⟨x, hx⟩).1
    else 0

theorem repositionMap_apply_realization (position' : K.Vertex → Plane)
    (hinj : Function.Injective position')
    (haff : ∀ s ∈ K.simplexes, AffineIndependent ℝ fun v : s => position' v)
    (hface : ∀ s ∈ K.simplexes, ∀ t ∈ K.simplexes,
      convexHull ℝ (position' '' (s : Set K.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set K.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset K.Vertex) : Set K.Vertex)))
    (x : GeometricRealization K.Vertex K.simplexes) :
    K.repositionMap position' hinj haff hface (K.baryEval x.1) =
      (K.reposition position' hinj haff hface).baryEval x.1 := by
  have hxmem : K.baryEval x.1 ∈ K.support :=
    (K.realizationHomeomorphAll x).2
  simp only [repositionMap, dif_pos hxmem, repositionHomeomorphAll]
  change ((K.reposition position' hinj haff hface).realizationHomeomorphAll
    (K.realizationHomeomorphAll.symm ⟨K.baryEval x.1, hxmem⟩)).1 = _
  have heq : K.realizationHomeomorphAll.symm ⟨K.baryEval x.1, hxmem⟩ = x := by
    apply K.realizationHomeomorphAll.injective
    apply Subtype.ext
    simp
  rw [heq]
  rfl

/-- Barycentric repositioning sends every vertex which occurs as a zero-face to its prescribed
new position. -/
theorem repositionMap_position (position' : K.Vertex → Plane)
    (hinj : Function.Injective position')
    (haff : ∀ s ∈ K.simplexes, AffineIndependent ℝ fun v : s => position' v)
    (hface : ∀ s ∈ K.simplexes, ∀ t ∈ K.simplexes,
      convexHull ℝ (position' '' (s : Set K.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set K.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset K.Vertex) : Set K.Vertex)))
    (v : K.Vertex) (hv : ({v} : Finset K.Vertex) ∈ K.simplexes) :
    K.repositionMap position' hinj haff hface (K.position v) = position' v := by
  classical
  let w : K.Vertex → ℝ := fun u => if u = v then 1 else 0
  have hw0 : ∀ u, 0 ≤ w u := by intro u; simp only [w]; split <;> positivity
  have hw1 : ∑ u, w u = 1 := by simp [w]
  have hwsupp : ∀ u ∉ ({v} : Finset K.Vertex), w u = 0 := by
    intro u hu
    simp only [Finset.mem_singleton] at hu
    simp [w, hu]
  let x : GeometricRealization K.Vertex K.simplexes :=
    ⟨w, ⟨hw0, hw1⟩, {v}, hv, hwsupp⟩
  have hsource : K.baryEval w = K.position v := by
    simp [PlaneComplex.baryEval, w]
  have htarget : (K.reposition position' hinj haff hface).baryEval w = position' v := by
    simp only [PlaneComplex.baryEval, PlaneComplex.reposition, w, ite_smul,
      one_smul, zero_smul]
    exact @Fintype.sum_ite_eq' K.Vertex Plane _
      (K.reposition position' hinj haff hface).vertexFintype K.vertexDecidableEq
      v position'
  rw [← hsource, K.repositionMap_apply_realization position' hinj haff hface x,
    htarget]

/-- Barycentric repositioning is affine on each original face. -/
theorem repositionMap_affineOn_face (position' : K.Vertex → Plane)
    (hinj : Function.Injective position')
    (haff : ∀ s ∈ K.simplexes, AffineIndependent ℝ fun v : s => position' v)
    (hface : ∀ s ∈ K.simplexes, ∀ t ∈ K.simplexes,
      convexHull ℝ (position' '' (s : Set K.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set K.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset K.Vertex) : Set K.Vertex)))
    {s : Finset K.Vertex} (hs : s ∈ K.simplexes) :
    IsAffineOn (K.repositionMap position' hinj haff hface) (K.cellCarrier s) := by
  classical
  have hsne := K.nonempty_of_mem s hs
  letI : Nonempty s := ⟨⟨hsne.choose, hsne.choose_spec⟩⟩
  let p : s → Plane := fun v => K.position v
  let q : s → Plane := fun v => position' v
  obtain ⟨g, hg⟩ := exists_affineMap_eqOn_affineIndependent p q (K.affineIndependent s hs)
  refine ⟨g, fun x hx => ?_⟩
  obtain ⟨z, hzsupp, hz0, hz1, hzeval⟩ := K.exists_weights_of_mem_cellCarrier hx
  let xr : GeometricRealization K.Vertex K.simplexes :=
    ⟨z, ⟨hz0, hz1⟩, s, hs, hzsupp⟩
  have hmap : K.repositionMap position' hinj haff hface x =
      (K.reposition position' hinj haff hface).baryEval z := by
    rw [← hzeval]
    exact K.repositionMap_apply_realization position' hinj haff hface xr
  rw [hmap]
  have hsum : ∑ v ∈ s, z v = 1 := by
    rw [← K.sum_eq_sum_of_support hzsupp]
    exact hz1
  have hxcomb : s.affineCombination ℝ K.position z = x := by
    rw [s.affineCombination_eq_linear_combination K.position z hsum]
    exact (K.baryEval_eq_sum_of_support hzsupp).symm.trans hzeval
  rw [← hxcomb, s.map_affineCombination K.position z hsum g]
  have htarget : (K.reposition position' hinj haff hface).baryEval z =
      s.affineCombination ℝ position' z := by
    rw [s.affineCombination_eq_linear_combination position' z hsum]
    change (∑ v, z v • position' v) = ∑ v ∈ s, z v • position' v
    exact (Finset.sum_subset (Finset.subset_univ s)
      (fun v _ hv => by rw [hzsupp v hv, zero_smul])).symm
  rw [htarget]
  change s.affineCombination ℝ position' z =
    s.affineCombination ℝ (g ∘ K.position) z
  apply Finset.affineCombination_congr s (fun _ _ => rfl)
  intro v hv
  exact (hg ⟨v, hv⟩).symm

/-- Barycentric repositioning is PL on the original complex. -/
theorem repositionMap_isPL (position' : K.Vertex → Plane)
    (hinj : Function.Injective position')
    (haff : ∀ s ∈ K.simplexes, AffineIndependent ℝ fun v : s => position' v)
    (hface : ∀ s ∈ K.simplexes, ∀ t ∈ K.simplexes,
      convexHull ℝ (position' '' (s : Set K.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set K.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset K.Vertex) : Set K.Vertex))) :
    IsPLOn K (K.repositionMap position' hinj haff hface) := by
  refine ⟨K, PlaneComplex.Subdivides.refl K, ?_⟩
  intro s hs
  exact K.repositionMap_affineOn_face position' hinj haff hface hs

/-- Vertex positions for the cone on `K`, with `none` as the cone vertex. -/
def conePosition (c : Plane) : Option K.Vertex → Plane
  | none => c
  | some v => K.position v

/-- The `coneWeights` declaration. -/
def coneWeights (z : K.Vertex → ℝ) : Option K.Vertex → ℝ
  | none => 0
  | some v => z v

@[simp] theorem coneWeights_none (z : K.Vertex → ℝ) : K.coneWeights z none = 0 := rfl

@[simp] theorem coneWeights_some (z : K.Vertex → ℝ) (v : K.Vertex) :
    K.coneWeights z (some v) = z v := rfl

theorem sum_coneWeights (z : K.Vertex → ℝ) :
    ∑ v, K.coneWeights z v = ∑ v, z v := by
  simp

/-- Lift a base face to the non-cone vertices. -/
def liftFace (s : Finset K.Vertex) : Finset (Option K.Vertex) :=
  s.map Function.Embedding.some

/-- Remove the cone vertex from a cone face. -/
def baseFace (t : Finset (Option K.Vertex)) : Finset K.Vertex :=
  t.filterMap id (by
    intro a a' b ha ha'
    simpa only [id_eq, Option.mem_def] using ha.trans ha'.symm)

@[simp] theorem mem_baseFace {t : Finset (Option K.Vertex)} {v : K.Vertex} :
    v ∈ K.baseFace t ↔ some v ∈ t := by
  simp [baseFace]

@[simp] theorem baseFace_liftFace (s : Finset K.Vertex) :
    K.baseFace (K.liftFace s) = s := by
  ext v
  simp [liftFace]

@[simp] theorem baseFace_inter (t u : Finset (Option K.Vertex)) :
    K.baseFace (t ∩ u) = K.baseFace t ∩ K.baseFace u := by
  ext v
  simp

theorem position_image_inter (s t : Finset K.Vertex) :
    K.position '' (s : Set K.Vertex) ∩ K.position '' (t : Set K.Vertex) =
      K.position '' ((s ∩ t : Finset K.Vertex) : Set K.Vertex) := by
  rw [← Set.image_inter K.position_injective, ← Finset.coe_inter]

theorem conePosition_image_eq_of_not_mem_none {c : Plane}
    {t : Finset (Option K.Vertex)} (ht : none ∉ t) :
    K.conePosition c '' (t : Set (Option K.Vertex)) =
      K.position '' (K.baseFace t : Set K.Vertex) := by
  ext x
  simp only [Set.mem_image, Finset.mem_coe, mem_baseFace]
  constructor
  · rintro ⟨v, hv, rfl⟩
    cases v with
    | none => exact (ht hv).elim
    | some v => exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨some v, hv, rfl⟩

theorem conePosition_image_eq_of_mem_none {c : Plane}
    {t : Finset (Option K.Vertex)} (ht : none ∈ t) :
    K.conePosition c '' (t : Set (Option K.Vertex)) =
      insert c (K.position '' (K.baseFace t : Set K.Vertex)) := by
  ext x
  simp only [Set.mem_image, Finset.mem_coe, mem_baseFace, Set.mem_insert_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    cases v with
    | none => exact Or.inl rfl
    | some v => exact Or.inr ⟨v, hv, rfl⟩
  · rintro (rfl | ⟨v, hv, rfl⟩)
    · exact ⟨none, ht, rfl⟩
    · exact ⟨some v, hv, rfl⟩

theorem conePosition_injective {c : Plane} (hc : c ∉ Set.range K.position) :
    Function.Injective (K.conePosition c) := by
  intro v w h
  cases v with
  | none =>
      cases w with
      | none => rfl
      | some w =>
          apply (hc ⟨w, ?_⟩).elim
          exact h.symm
  | some v =>
      cases w with
      | none => exact (hc ⟨v, h⟩).elim
      | some w => exact congrArg some (K.position_injective h)

/-- All nonempty faces of cones on the faces of `K`. -/
def coneSimplexes : Finset (Finset (Option K.Vertex)) :=
  K.simplexes.biUnion fun s =>
    (insert none (K.liftFace s)).powerset.filter (·.Nonempty)

theorem mem_coneSimplexes_iff {t : Finset (Option K.Vertex)} :
    t ∈ K.coneSimplexes ↔
      t.Nonempty ∧ ∃ s ∈ K.simplexes, t ⊆ insert none (K.liftFace s) := by
  simp only [coneSimplexes, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_powerset]
  aesop

theorem baseFace_subset_of_subset_cone {s : Finset K.Vertex}
    {t : Finset (Option K.Vertex)} (ht : t ⊆ insert none (K.liftFace s)) :
    K.baseFace t ⊆ s := by
  intro v hv
  have hsv := ht (K.mem_baseFace.mp hv)
  simpa [liftFace] using hsv

theorem baseFace_mem_of_nonempty {t : Finset (Option K.Vertex)}
    (ht : t ∈ K.coneSimplexes) (hne : (K.baseFace t).Nonempty) :
    K.baseFace t ∈ K.simplexes := by
  obtain ⟨-, s, hs, hts⟩ := K.mem_coneSimplexes_iff.mp ht
  exact K.down_closed s hs (K.baseFace t) (K.baseFace_subset_of_subset_cone hts) hne

theorem baseCarrier_subset_support {t : Finset (Option K.Vertex)}
    (ht : t ∈ K.coneSimplexes) :
    convexHull ℝ (K.position '' (K.baseFace t : Set K.Vertex)) ⊆ K.support := by
  rcases (K.baseFace t).eq_empty_or_nonempty with h | h
  · rw [h]
    simp
  · simpa [PlaneComplex.cellCarrier] using
      K.cellCarrier_subset_support (K.baseFace_mem_of_nonempty ht h)

theorem baseCarrier_inter {t u : Finset (Option K.Vertex)}
    (ht : t ∈ K.coneSimplexes) (hu : u ∈ K.coneSimplexes) :
    convexHull ℝ (K.position '' (K.baseFace t : Set K.Vertex)) ∩
        convexHull ℝ (K.position '' (K.baseFace u : Set K.Vertex)) =
      convexHull ℝ (K.position '' ((K.baseFace t ∩ K.baseFace u : Finset K.Vertex) :
        Set K.Vertex)) := by
  rcases (K.baseFace t).eq_empty_or_nonempty with h | htne
  · rw [h]
    simp
  rcases (K.baseFace u).eq_empty_or_nonempty with h | hune
  · rw [h]
    simp
  exact K.face_inter _ (K.baseFace_mem_of_nonempty ht htne) _
    (K.baseFace_mem_of_nonempty hu hune)

/-- Cone a finite one-dimensional complex supported on the frontier of a convex set. -/
noncomputable def cone (S : Set Plane) (hS : Convex ℝ S) (c : Plane)
    (hc : c ∈ interior S) (havoid : c ∉ Set.range K.position)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (hsupport : K.support = frontier S) : PlaneComplex where
  Vertex := Option K.Vertex
  position := K.conePosition c
  position_injective := K.conePosition_injective havoid
  simplexes := K.coneSimplexes
  nonempty_of_mem := fun t ht => (K.mem_coneSimplexes_iff.mp ht).1
  card_le_three := by
    intro t ht
    obtain ⟨-, s, hs, hts⟩ := K.mem_coneSimplexes_iff.mp ht
    have hsCard := hgraph s hs
    refine (Finset.card_le_card hts).trans ?_
    calc
      (insert none (K.liftFace s)).card ≤ (K.liftFace s).card + 1 := Finset.card_insert_le _ _
      _ = s.card + 1 := by simp [liftFace]
      _ ≤ 3 := by omega
  down_closed := by
    intro t ht u hut hune
    obtain ⟨-, s, hs, hts⟩ := K.mem_coneSimplexes_iff.mp ht
    exact K.mem_coneSimplexes_iff.mpr ⟨hune, s, hs, hut.trans hts⟩
  affineIndependent := by
    intro t ht
    obtain ⟨-, s, hs, hts⟩ := K.mem_coneSimplexes_iff.mp ht
    let A : Finset Plane := s.image K.position
    have hAI : AffineIndependent ℝ ((↑) : A → Plane) := by
      apply affineIndependent_finset_coe (K.affineIndependent s hs)
      intro a ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
      exact ⟨⟨v, hv⟩, rfl⟩
    have hAcard : A.card ≤ 2 := by
      rw [Finset.card_image_of_injective _ K.position_injective]
      exact hgraph s hs
    have hAS : convexHull ℝ (A : Set Plane) ⊆ frontier S := by
      rw [← hsupport]
      simpa [A, Finset.coe_image, PlaneComplex.cellCarrier] using
        K.cellCarrier_subset_support hs
    have hparent : AffineIndependent ℝ ((↑) : ↥(insert c A) → Plane) :=
      affineIndependent_insert_interior_of_card_le_two hS hAcard hAI hAS hc
    let e : t ↪ ↥(insert c A) :=
      { toFun := fun ⟨v, hv⟩ => ⟨K.conePosition c v, by
          cases v with
          | none => exact Finset.mem_insert_self _ _
          | some v =>
              apply Finset.mem_insert_of_mem
              apply Finset.mem_image.mpr
              refine ⟨v, ?_, rfl⟩
              exact K.baseFace_subset_of_subset_cone hts
                (K.mem_baseFace.mpr hv)⟩
        inj' := fun v w h => Subtype.ext
          ((K.conePosition_injective havoid) (congrArg Subtype.val h)) }
    exact hparent.comp_embedding e
  face_inter := by
    intro t ht u hu
    have htBase : convexHull ℝ (K.position '' (K.baseFace t : Set K.Vertex)) ⊆
        frontier S := by
      rw [← hsupport]
      exact K.baseCarrier_subset_support ht
    have huBase : convexHull ℝ (K.position '' (K.baseFace u : Set K.Vertex)) ⊆
        frontier S := by
      rw [← hsupport]
      exact K.baseCarrier_subset_support hu
    have hinter := K.baseCarrier_inter ht hu
    have hinterSet :
        convexHull ℝ (K.position '' (K.baseFace t : Set K.Vertex)) ∩
            convexHull ℝ (K.position '' (K.baseFace u : Set K.Vertex)) =
          convexHull ℝ ((K.position '' (K.baseFace t : Set K.Vertex)) ∩
            K.position '' (K.baseFace u : Set K.Vertex)) := by
      rw [K.position_image_inter]
      exact hinter
    by_cases ht0 : none ∈ t
    · rw [K.conePosition_image_eq_of_mem_none ht0]
      by_cases hu0 : none ∈ u
      · rw [K.conePosition_image_eq_of_mem_none hu0]
        have htu0 : none ∈ t ∩ u := Finset.mem_inter.mpr ⟨ht0, hu0⟩
        rw [K.conePosition_image_eq_of_mem_none htu0, K.baseFace_inter]
        simpa [K.position_image_inter] using
          convexHull_insert_inter_convexHull_insert' hS hc htBase huBase hinterSet
      · rw [K.conePosition_image_eq_of_not_mem_none hu0]
        have htu0 : none ∉ t ∩ u := fun h => hu0 (Finset.mem_inter.mp h).2
        rw [K.conePosition_image_eq_of_not_mem_none htu0, K.baseFace_inter]
        simpa [K.position_image_inter] using
          convexHull_insert_inter_convexHull' hS hc htBase huBase hinterSet
    · rw [K.conePosition_image_eq_of_not_mem_none ht0]
      by_cases hu0 : none ∈ u
      · rw [K.conePosition_image_eq_of_mem_none hu0]
        have htu0 : none ∉ t ∩ u := fun h => ht0 (Finset.mem_inter.mp h).1
        rw [K.conePosition_image_eq_of_not_mem_none htu0, K.baseFace_inter]
        have hinterRev :
            convexHull ℝ (K.position '' (K.baseFace u : Set K.Vertex)) ∩
                convexHull ℝ (K.position '' (K.baseFace t : Set K.Vertex)) =
              convexHull ℝ ((K.position '' (K.baseFace u : Set K.Vertex)) ∩
                K.position '' (K.baseFace t : Set K.Vertex)) := by
          rw [K.position_image_inter]
          exact K.baseCarrier_inter hu ht
        have hrev := convexHull_insert_inter_convexHull' hS hc huBase htBase hinterRev
        simpa [Set.inter_comm, Finset.inter_comm, K.position_image_inter] using hrev
      · rw [K.conePosition_image_eq_of_not_mem_none hu0]
        have htu0 : none ∉ t ∩ u := fun h => ht0 (Finset.mem_inter.mp h).1
        rw [K.conePosition_image_eq_of_not_mem_none htu0, K.baseFace_inter]
        exact hinter

theorem cone_baryEval_coneWeights (S : Set Plane) (hS : Convex ℝ S) (c : Plane)
    (hc : c ∈ interior S) (havoid : c ∉ Set.range K.position)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (hsupport : K.support = frontier S) (z : K.Vertex → ℝ) :
    (K.cone S hS c hc havoid hgraph hsupport).baryEval (K.coneWeights z) =
      K.baryEval z := by
  simp only [PlaneComplex.baryEval, cone]
  change (∑ x : Option K.Vertex, K.coneWeights z x • K.conePosition c x) =
    ∑ v, z v • K.position v
  rw [Fintype.sum_option]
  simp [coneWeights, conePosition]

theorem cone_support_eq (S : Set Plane) (hS : Convex ℝ S) (hcompact : IsCompact S)
    (c : Plane) (hc : c ∈ interior S) (havoid : c ∉ Set.range K.position)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (hsupport : K.support = frontier S) (hfrontier : (frontier S).Nonempty) :
    (K.cone S hS c hc havoid hgraph hsupport).support = S := by
  change (⋃ t ∈ K.coneSimplexes,
      convexHull ℝ (K.conePosition c '' (t : Set (Option K.Vertex)))) = S
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    obtain ⟨-, s, hs, hts⟩ := K.mem_coneSimplexes_iff.mp ht
    have hcarrier :
        convexHull ℝ (K.conePosition c '' (t : Set (Option K.Vertex))) ⊆
          convexHull ℝ (insert c (K.position '' (s : Set K.Vertex))) := by
      apply convexHull_mono
      rintro z ⟨v, hv, rfl⟩
      have hvParent := hts hv
      cases v with
      | none => exact Set.mem_insert _ _
      | some v =>
          apply Set.mem_insert_of_mem
          refine ⟨v, ?_, rfl⟩
          simpa [liftFace] using hvParent
    apply hcarrier at hxt
    exact (convexHull_min (by
      rintro z (rfl | ⟨v, hv, rfl⟩)
      · exact interior_subset hc
      · have hvCarrier : K.position v ∈ K.cellCarrier s :=
          subset_convexHull ℝ _ ⟨v, hv, rfl⟩
        have hvSupport := K.cellCarrier_subset_support hs hvCarrier
        rw [hsupport] at hvSupport
        exact hcompact.isClosed.frontier_subset hvSupport) hS) hxt
  · intro x hx
    obtain ⟨y, hyFrontier, hxy⟩ :=
      exists_frontier_endpoint hS hcompact hc hx hfrontier
    have hySupport : y ∈ K.support := by simpa [hsupport] using hyFrontier
    rw [PlaneComplex.support] at hySupport
    simp only [Set.mem_iUnion] at hySupport
    obtain ⟨s, hs, hys⟩ := hySupport
    let t : Finset (Option K.Vertex) := insert none (K.liftFace s)
    have ht : t ∈ K.coneSimplexes := by
      apply K.mem_coneSimplexes_iff.mpr
      exact ⟨⟨none, Finset.mem_insert_self _ _⟩, s, hs, subset_rfl⟩
    simp only [Set.mem_iUnion]
    refine ⟨t, ht, ?_⟩
    have ht0 : none ∈ t := Finset.mem_insert_self _ _
    rw [K.conePosition_image_eq_of_mem_none ht0]
    have hbase : K.baseFace t = s := by
      ext v
      simp [t, liftFace]
    rw [hbase]
    exact (convex_convexHull ℝ (insert c (K.position '' (s : Set K.Vertex)))).segment_subset
      (subset_convexHull ℝ _ (Set.mem_insert _ _))
      (convexHull_mono (Set.subset_insert c _) hys) hxy

end PlaneComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification08_block_01
/- END ClassificationOfSurfaces.Moise.ConeExtension -/

/- BEGIN ClassificationOfSurfaces.Moise.GraphRefinement | 6739e8339544e3fccfae03b71ef374c35245d5109a7b07c0452e7e4cb5453968 -/
section schottkyclassification08_block_02
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Finite marked refinements of plane graphs

This file enlarges the edge arrangement of a finite plane graph by finitely many prescribed
points.  When the marks lie in the graph support, the subordinate arrangement is a subdivision
of the graph and every mark is a vertex of that subdivision.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace PlaneComplex

variable (K : PlaneComplex) {P : Type*} [Fintype P]

/-- The `markEquiv` declaration. -/
noncomputable def markEquiv : P ≃ Fin (Fintype.card P) :=
  Fintype.equivFin P

/-- The edge chain enlarged by an arbitrary finite family of marked points. -/
noncomputable def markedEdgeChain (point : P → Plane) :
    BrokenLineData (Set.univ : Set Plane) := by
  classical
  let m := Fintype.card K.EdgeFace
  let r := Fintype.card P
  let q := Fintype.card K.Vertex
  let vertex : Fin (2 * m + r + q + 1) → Plane := fun k =>
    if hk : k.val < 2 * m then
      let i : Fin m := ⟨k.val / 2, by omega⟩
      if k.val % 2 = 0 then K.position (K.edgeFirst i) else K.position (K.edgeSecond i)
    else if hp : k.val < 2 * m + r then
      point (markEquiv.symm ⟨k.val - 2 * m, by omega⟩)
    else if hv : k.val < 2 * m + r + q then
      K.position (K.vertexAt ⟨k.val - (2 * m + r), by omega⟩)
    else 0
  exact {
    n := 2 * m + r + q
    vertex := vertex
    segment_subset := fun _ _ _ => Set.mem_univ _ }

theorem markedEdgeChain_vertex_even (point : P → Plane)
    (i : Fin (Fintype.card K.EdgeFace)) :
    (K.markedEdgeChain point).vertex ⟨2 * i.val, by
      change 2 * i.val < 2 * Fintype.card K.EdgeFace + Fintype.card P +
        Fintype.card K.Vertex + 1
      omega⟩ = K.position (K.edgeFirst i) := by
  classical
  simp only [markedEdgeChain]
  rw [dif_pos (by omega)]
  have hmod : (2 * i.val) % 2 = 0 := by omega
  rw [if_pos hmod]
  have hdiv : 2 * i.val / 2 = i.val := by omega
  congr 2
  exact Fin.ext hdiv

theorem markedEdgeChain_vertex_odd (point : P → Plane)
    (i : Fin (Fintype.card K.EdgeFace)) :
    (K.markedEdgeChain point).vertex ⟨2 * i.val + 1, by
      change 2 * i.val + 1 < 2 * Fintype.card K.EdgeFace + Fintype.card P +
        Fintype.card K.Vertex + 1
      omega⟩ = K.position (K.edgeSecond i) := by
  classical
  simp only [markedEdgeChain]
  rw [dif_pos (by omega)]
  have hmod : (2 * i.val + 1) % 2 ≠ 0 := by omega
  rw [if_neg hmod]
  have hdiv : (2 * i.val + 1) / 2 = i.val := by omega
  congr 2
  exact Fin.ext hdiv

theorem markedEdgeChain_vertex_mark (point : P → Plane) (p : P) :
    (K.markedEdgeChain point).vertex
      ⟨2 * Fintype.card K.EdgeFace + (markEquiv p).val, by
        change 2 * Fintype.card K.EdgeFace + (markEquiv p).val <
          2 * Fintype.card K.EdgeFace + Fintype.card P + Fintype.card K.Vertex + 1
        have hp := (markEquiv p).isLt
        omega⟩ = point p := by
  classical
  simp only [markedEdgeChain]
  rw [dif_neg (by omega), dif_pos (by omega)]
  have hsub : 2 * Fintype.card K.EdgeFace + (markEquiv p).val -
      2 * Fintype.card K.EdgeFace = (markEquiv p).val := by omega
  have hfin : (⟨2 * Fintype.card K.EdgeFace + (markEquiv p).val -
      2 * Fintype.card K.EdgeFace, by omega⟩ : Fin (Fintype.card P)) = markEquiv p :=
    Fin.ext hsub
  rw [hfin, Equiv.symm_apply_apply]

theorem markedEdgeChain_vertex_original (point : P → Plane)
    (i : Fin (Fintype.card K.Vertex)) :
    (K.markedEdgeChain point).vertex
      ⟨2 * Fintype.card K.EdgeFace + Fintype.card P + i.val, by
        change 2 * Fintype.card K.EdgeFace + Fintype.card P + i.val <
          2 * Fintype.card K.EdgeFace + Fintype.card P + Fintype.card K.Vertex + 1
        omega⟩ = K.position (K.vertexAt i) := by
  classical
  simp only [markedEdgeChain]
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  have hsub : 2 * Fintype.card K.EdgeFace + Fintype.card P + i.val -
      (2 * Fintype.card K.EdgeFace + Fintype.card P) = i.val := by omega
  congr 2
  exact Fin.ext hsub

/-- The `markedEdgeChainIndex` declaration. -/
noncomputable def markedEdgeChainIndex (point : P → Plane)
    (i : Fin (Fintype.card K.EdgeFace)) : Fin (K.markedEdgeChain point).n :=
  ⟨2 * i.val, by
    change 2 * i.val < 2 * Fintype.card K.EdgeFace + Fintype.card P +
      Fintype.card K.Vertex
    have hm : 0 < Fintype.card K.EdgeFace := Fintype.card_pos_iff.mpr ⟨K.edgeAt i⟩
    omega⟩

theorem markedEdgeChain_segment (point : P → Plane)
    (i : Fin (Fintype.card K.EdgeFace)) :
    segment ℝ
        ((K.markedEdgeChain point).vertex (K.markedEdgeChainIndex point i).castSucc)
        ((K.markedEdgeChain point).vertex (K.markedEdgeChainIndex point i).succ) =
      K.cellCarrier (K.edgeAt i).1 := by
  rw [show (K.markedEdgeChainIndex point i).castSucc =
      ⟨2 * i.val, by
        change 2 * i.val < 2 * Fintype.card K.EdgeFace + Fintype.card P +
          Fintype.card K.Vertex + 1
        omega⟩ from rfl,
    show (K.markedEdgeChainIndex point i).succ =
      ⟨2 * i.val + 1, by
        change 2 * i.val + 1 < 2 * Fintype.card K.EdgeFace + Fintype.card P +
          Fintype.card K.Vertex + 1
        omega⟩ from rfl,
    K.markedEdgeChain_vertex_even point i, K.markedEdgeChain_vertex_odd point i,
    K.edgeAt_eq, PlaneComplex.cellCarrier]
  have himage : K.position ''
      (({K.edgeFirst i, K.edgeSecond i} : Finset K.Vertex) : Set K.Vertex) =
      {K.position (K.edgeFirst i), K.position (K.edgeSecond i)} := by
    ext x
    simp [eq_comm]
  rw [himage, convexHull_pair]

/-- The `markedEdgeArrangement` declaration. -/
noncomputable def markedEdgeArrangement (point : P → Plane) : PlaneComplex :=
  (K.markedEdgeChain point).arrangementMesh.toPlaneComplex

/-- The `markedEdgeSubdivision` declaration. -/
noncomputable def markedEdgeSubdivision (point : P → Plane) : PlaneComplex :=
  (K.markedEdgeArrangement point).subordinateTo K

theorem markedEdgeSubdivision_support_eq (point : P → Plane)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2) :
    (K.markedEdgeSubdivision point).support = K.support := by
  unfold markedEdgeSubdivision markedEdgeArrangement
  apply Set.Subset.antisymm
  · exact (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.subordinateTo_support_subset K
  · intro x hx
    rw [PlaneComplex.support] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    have hspos : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem s hs)
    have hscard := hgraph s hs
    have hcases : s.card = 1 ∨ s.card = 2 := by omega
    rw [PlaneComplex.support]
    simp only [Set.mem_iUnion]
    rcases hcases with hsone | hstwo
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
      have hxv : x = K.position v := by
        simpa [PlaneComplex.cellCarrier] using hxs
      obtain ⟨i, hi⟩ := K.exists_vertexAt v
      let j : Fin ((K.markedEdgeChain point).n + 1) :=
        ⟨2 * Fintype.card K.EdgeFace + Fintype.card P + i.val, by
          change 2 * Fintype.card K.EdgeFace + Fintype.card P + i.val <
            2 * Fintype.card K.EdgeFace + Fintype.card P + Fintype.card K.Vertex + 1
          omega⟩
      obtain ⟨w, hwpos, hwface⟩ :=
        (K.markedEdgeChain point).exists_arrangementVertex_position_eq j
      let u : Finset (K.markedEdgeChain point).arrangementMesh.Vertex := {w}
      refine ⟨u, ?_, ?_⟩
      · apply ((K.markedEdgeChain point).arrangementMesh.toPlaneComplex
          |>.mem_subordinateTo_simplexes_iff K).mpr
        refine ⟨hwface, {v}, hs, ?_⟩
        intro y hy
        have hyw : y = (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position w := by
          change y ∈ convexHull ℝ
            ((K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position ''
              (({w} : Finset (K.markedEdgeChain point).arrangementMesh.Vertex) :
                Set (K.markedEdgeChain point).arrangementMesh.Vertex)) at hy
          have himage : (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position ''
              (({w} : Finset (K.markedEdgeChain point).arrangementMesh.Vertex) :
                Set (K.markedEdgeChain point).arrangementMesh.Vertex) =
              {(K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position w} := by
            ext z
            constructor
            · rintro ⟨q, hq, rfl⟩
              rw [Finset.mem_singleton.mp hq]
              exact Set.mem_singleton _
            · intro hz
              rw [Set.mem_singleton_iff] at hz
              subst z
              exact ⟨w, Finset.mem_singleton_self _, rfl⟩
          rw [himage, convexHull_singleton] at hy
          exact hy
        rw [hyw, hwpos, show (K.markedEdgeChain point).vertex j = K.position v by
          rw [K.markedEdgeChain_vertex_original point i, hi]]
        exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self _, rfl⟩
      · rw [hxv]
        erw [(K.markedEdgeChain point).arrangementMesh.toPlaneComplex.subordinateTo_cellCarrier K]
        exact subset_convexHull ℝ _ ⟨w, Finset.mem_singleton_self _, by
          rw [hwpos, K.markedEdgeChain_vertex_original point i, hi]⟩
    · let e : K.EdgeFace := ⟨s, Finset.mem_filter.mpr ⟨hs, hstwo⟩⟩
      obtain ⟨i, hi⟩ := K.exists_edgeAt e
      have hsegment : segment ℝ
          ((K.markedEdgeChain point).vertex (K.markedEdgeChainIndex point i).castSucc)
          ((K.markedEdgeChain point).vertex (K.markedEdgeChainIndex point i).succ) =
          K.cellCarrier s := by
        rw [K.markedEdgeChain_segment point i, hi]
      obtain ⟨u, hu, hxu, huSegment⟩ :=
        (K.markedEdgeChain point).exists_face_on_segment
          (K.markedEdgeChainIndex point i) (hsegment.symm ▸ hxs)
      refine ⟨u, ?_, hxu⟩
      apply ((K.markedEdgeChain point).arrangementMesh.toPlaneComplex
        |>.mem_subordinateTo_simplexes_iff K).mpr
      refine ⟨hu, s, hs, ?_⟩
      rw [← hsegment]
      apply convexHull_min
      · rintro y ⟨w, hw, rfl⟩
        exact huSegment w hw
      · exact convex_segment _ _

/-- Every point of an original graph face is covered by a marked-subdivision face lying in that
same original face. -/
theorem exists_markedEdgeSubdivision_face_at (point : P → Plane)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    {s : Finset K.Vertex} (hs : s ∈ K.simplexes) {x : Plane}
    (hxs : x ∈ K.cellCarrier s) :
    ∃ u ∈ (K.markedEdgeSubdivision point).simplexes,
      x ∈ (K.markedEdgeSubdivision point).cellCarrier u ∧
      (K.markedEdgeSubdivision point).cellCarrier u ⊆ K.cellCarrier s := by
  have hspos : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem s hs)
  have hsle := hgraph s hs
  rcases (show s.card = 1 ∨ s.card = 2 by omega) with hsone | hstwo
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
    have hxv : x = K.position v := by
      simpa [PlaneComplex.cellCarrier] using hxs
    obtain ⟨i, hi⟩ := K.exists_vertexAt v
    let j : Fin ((K.markedEdgeChain point).n + 1) :=
      ⟨2 * Fintype.card K.EdgeFace + Fintype.card P + i.val, by
        change 2 * Fintype.card K.EdgeFace + Fintype.card P + i.val <
          2 * Fintype.card K.EdgeFace + Fintype.card P + Fintype.card K.Vertex + 1
        omega⟩
    obtain ⟨w, hwpos, hwface⟩ :=
      (K.markedEdgeChain point).exists_arrangementVertex_position_eq j
    let u : Finset (K.markedEdgeChain point).arrangementMesh.Vertex := {w}
    have hu : u ∈ (K.markedEdgeSubdivision point).simplexes := by
      apply ((K.markedEdgeChain point).arrangementMesh.toPlaneComplex
        |>.mem_subordinateTo_simplexes_iff K).mpr
      refine ⟨hwface, {v}, hs, ?_⟩
      intro y hy
      have hyw : y = (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position w := by
        change y ∈ convexHull ℝ
          ((K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position ''
            (({w} : Finset (K.markedEdgeChain point).arrangementMesh.Vertex) :
              Set (K.markedEdgeChain point).arrangementMesh.Vertex)) at hy
        have himage :
            (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position ''
              (({w} : Finset (K.markedEdgeChain point).arrangementMesh.Vertex) :
                Set (K.markedEdgeChain point).arrangementMesh.Vertex) =
              {(K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position w} := by
          ext z
          constructor
          · rintro ⟨q, hq, hz⟩
            rw [Finset.mem_singleton.mp hq] at hz
            exact Set.mem_singleton_iff.mpr hz.symm
          · intro hz
            exact ⟨w, Finset.mem_singleton_self _, (Set.mem_singleton_iff.mp hz).symm⟩
        rw [himage, convexHull_singleton] at hy
        exact hy
      rw [hyw, hwpos, show (K.markedEdgeChain point).vertex j = K.position v by
        rw [K.markedEdgeChain_vertex_original point i, hi]]
      exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self _, rfl⟩
    refine ⟨u, hu, ?_, ?_⟩
    · rw [hxv]
      change K.position v ∈ convexHull ℝ
        ((K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position ''
          (({w} : Finset (K.markedEdgeChain point).arrangementMesh.Vertex) :
            Set (K.markedEdgeChain point).arrangementMesh.Vertex))
      exact subset_convexHull ℝ _ ⟨w, Finset.mem_singleton_self _, by
        rw [hwpos, K.markedEdgeChain_vertex_original point i, hi]⟩
    · intro y hy
      have hyw : y = K.position v := by
        change y ∈ convexHull ℝ
          ((K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position ''
            (({w} : Finset (K.markedEdgeChain point).arrangementMesh.Vertex) :
              Set (K.markedEdgeChain point).arrangementMesh.Vertex)) at hy
        have : y = (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position w := by
          have himage :
              (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position ''
                (({w} : Finset (K.markedEdgeChain point).arrangementMesh.Vertex) :
                  Set (K.markedEdgeChain point).arrangementMesh.Vertex) =
                {(K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position w} := by
            ext z
            constructor
            · rintro ⟨q, hq, hz⟩
              rw [Finset.mem_singleton.mp hq] at hz
              exact Set.mem_singleton_iff.mpr hz.symm
            · intro hz
              exact ⟨w, Finset.mem_singleton_self _, (Set.mem_singleton_iff.mp hz).symm⟩
          rw [himage, convexHull_singleton] at hy
          exact hy
        rw [this, hwpos, K.markedEdgeChain_vertex_original point i, hi]
      rw [hyw]
      exact subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self _, rfl⟩
  · let e : K.EdgeFace := ⟨s, Finset.mem_filter.mpr ⟨hs, hstwo⟩⟩
    obtain ⟨i, hi⟩ := K.exists_edgeAt e
    have hsegment : segment ℝ
        ((K.markedEdgeChain point).vertex (K.markedEdgeChainIndex point i).castSucc)
        ((K.markedEdgeChain point).vertex (K.markedEdgeChainIndex point i).succ) =
        K.cellCarrier s := by
      rw [K.markedEdgeChain_segment point i, hi]
    obtain ⟨u, hu, hxu, huSegment⟩ :=
      (K.markedEdgeChain point).exists_face_on_segment
        (K.markedEdgeChainIndex point i) (hsegment.symm ▸ hxs)
    have huCarrier :
        (K.markedEdgeSubdivision point).cellCarrier u ⊆ K.cellCarrier s := by
      rw [← hsegment]
      apply convexHull_min
      · rintro y ⟨w, hw, rfl⟩
        exact huSegment w hw
      · exact convex_segment _ _
    have huSub : u ∈ (K.markedEdgeSubdivision point).simplexes := by
      apply ((K.markedEdgeChain point).arrangementMesh.toPlaneComplex
        |>.mem_subordinateTo_simplexes_iff K).mpr
      refine ⟨hu, s, hs, ?_⟩
      exact huCarrier
    refine ⟨u, huSub, hxu, ?_⟩
    exact huCarrier

/-- Restricting a marked edge subdivision to a union of original graph faces preserves exactly
that union. -/
theorem markedEdgeSubdivision_restrictToSet_support_eq (point : P → Plane)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2) (A : Set Plane)
    (hA : ∀ x ∈ A, ∃ s ∈ K.simplexes,
      x ∈ K.cellCarrier s ∧ K.cellCarrier s ⊆ A) :
    ((K.markedEdgeSubdivision point).restrictToSet A).support = A := by
  apply Set.Subset.antisymm
  · exact (K.markedEdgeSubdivision point).restrictToSet_support_subset A
  · intro x hx
    obtain ⟨s, hs, hxs, hsA⟩ := hA x hx
    obtain ⟨u, hu, hxu, huSub⟩ :=
      K.exists_markedEdgeSubdivision_face_at point hgraph hs hxs
    rw [PlaneComplex.support]
    simp only [Set.mem_iUnion]
    exact ⟨u, (K.markedEdgeSubdivision point).mem_restrictToSet_simplexes_iff A |>.mpr
      ⟨hu, huSub.trans hsA⟩, hxu⟩

theorem markedEdgeSubdivision_subdivides (point : P → Plane)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2) :
    (K.markedEdgeSubdivision point).Subdivides K :=
  (K.markedEdgeArrangement point).subordinateTo_subdivides K
    (K.markedEdgeSubdivision_support_eq point hgraph)

/-- The `markedEdgeChainMarkIndex` declaration. -/
noncomputable def markedEdgeChainMarkIndex (point : P → Plane) (p : P) :
    Fin ((K.markedEdgeChain point).n + 1) :=
  ⟨2 * Fintype.card K.EdgeFace + (markEquiv p).val, by
    change 2 * Fintype.card K.EdgeFace + (markEquiv p).val <
      2 * Fintype.card K.EdgeFace + Fintype.card P + Fintype.card K.Vertex + 1
    omega⟩

theorem markedEdgeArrangement_monochromatic_vertical (point : P → Plane) (p : P) :
    (K.markedEdgeChain point).arrangementMesh.IsMonochromatic
      (BrokenLineData.verticalLine (point p)) := by
  have h := (K.markedEdgeChain point).arrangementMesh_monochromatic_verticalLine
    (K.markedEdgeChainMarkIndex point p)
  have hj : (K.markedEdgeChain point).vertex (K.markedEdgeChainMarkIndex point p) =
      point p := K.markedEdgeChain_vertex_mark point p
  rwa [hj] at h

theorem markedEdgeArrangement_monochromatic_horizontal (point : P → Plane) (p : P) :
    (K.markedEdgeChain point).arrangementMesh.IsMonochromatic
      (BrokenLineData.horizontalLine (point p)) := by
  have h := (K.markedEdgeChain point).arrangementMesh_monochromatic_horizontalLine
    (K.markedEdgeChainMarkIndex point p)
  have hj : (K.markedEdgeChain point).vertex (K.markedEdgeChainMarkIndex point p) =
      point p := K.markedEdgeChain_vertex_mark point p
  rwa [hj] at h

/-- Every arrangement face lies on one side of a marked affine parameter on an original edge. -/
theorem markedFace_parameter_side (point : P → Plane) (p : P)
    (i : Fin (Fintype.card K.EdgeFace)) (r : ℝ)
    (hpoint : point p = AffineMap.lineMap (K.position (K.edgeFirst i))
      (K.position (K.edgeSecond i)) r)
    {u : Finset (K.markedEdgeChain point).arrangementMesh.Vertex}
    (hu : u ∈ (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.simplexes) :
    (∀ v ∈ u, K.edgeParameter i
        ((K.markedEdgeChain point).arrangementMesh.position v) ≤ r) ∨
      (∀ v ∈ u, r ≤ K.edgeParameter i
        ((K.markedEdgeChain point).arrangementMesh.position v)) := by
  let M := (K.markedEdgeChain point).arrangementMesh
  obtain ⟨-, T, hT, huT⟩ := M.mem_faces_iff.mp hu
  unfold edgeParameter
  split_ifs with hx
  · have hmono := K.markedEdgeArrangement_monochromatic_vertical point p
    rcases hmono T hT with hnonneg | hnonpos
    · by_cases hΔ : 0 < K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0
      · right
        intro v hv
        apply normalized_ge_of_line_nonneg hΔ
        have hline := hnonneg v (huT hv)
        change 0 ≤ M.position v 0 - point p 0 at hline
        rw [hpoint] at hline
        simpa [M, AffineMap.lineMap_apply_module] using hline
      · have hΔ' : K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0 < 0 := by
          exact lt_of_le_of_ne (le_of_not_gt hΔ) (sub_ne_zero.mpr hx.symm)
        left
        intro v hv
        apply normalized_le_of_line_nonneg_of_neg hΔ'
        have hline := hnonneg v (huT hv)
        change 0 ≤ M.position v 0 - point p 0 at hline
        rw [hpoint] at hline
        simpa [M, AffineMap.lineMap_apply_module] using hline
    · by_cases hΔ : 0 < K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0
      · left
        intro v hv
        apply normalized_le_of_line_nonpos hΔ
        have hline := hnonpos v (huT hv)
        change M.position v 0 - point p 0 ≤ 0 at hline
        rw [hpoint] at hline
        simpa [M, AffineMap.lineMap_apply_module] using hline
      · have hΔ' : K.position (K.edgeSecond i) 0 - K.position (K.edgeFirst i) 0 < 0 := by
          exact lt_of_le_of_ne (le_of_not_gt hΔ) (sub_ne_zero.mpr hx.symm)
        right
        intro v hv
        apply normalized_ge_of_line_nonpos_of_neg hΔ'
        have hline := hnonpos v (huT hv)
        change M.position v 0 - point p 0 ≤ 0 at hline
        rw [hpoint] at hline
        simpa [M, AffineMap.lineMap_apply_module] using hline
  · have hxy : K.position (K.edgeFirst i) 1 ≠ K.position (K.edgeSecond i) 1 := by
      intro hy
      apply K.position_injective.ne (K.edgeFirst_ne_edgeSecond i)
      exact plane_ext (not_ne_iff.mp hx) hy
    have hmono := K.markedEdgeArrangement_monochromatic_horizontal point p
    rcases hmono T hT with hnonneg | hnonpos
    · by_cases hΔ : 0 < K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1
      · right
        intro v hv
        apply normalized_ge_of_line_nonneg hΔ
        have hline := hnonneg v (huT hv)
        change 0 ≤ M.position v 1 - point p 1 at hline
        rw [hpoint] at hline
        simpa [M, AffineMap.lineMap_apply_module] using hline
      · have hΔ' : K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1 < 0 := by
          exact lt_of_le_of_ne (le_of_not_gt hΔ) (sub_ne_zero.mpr hxy.symm)
        left
        intro v hv
        apply normalized_le_of_line_nonneg_of_neg hΔ'
        have hline := hnonneg v (huT hv)
        change 0 ≤ M.position v 1 - point p 1 at hline
        rw [hpoint] at hline
        simpa [M, AffineMap.lineMap_apply_module] using hline
    · by_cases hΔ : 0 < K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1
      · left
        intro v hv
        apply normalized_le_of_line_nonpos hΔ
        have hline := hnonpos v (huT hv)
        change M.position v 1 - point p 1 ≤ 0 at hline
        rw [hpoint] at hline
        simpa [M, AffineMap.lineMap_apply_module] using hline
      · have hΔ' : K.position (K.edgeSecond i) 1 - K.position (K.edgeFirst i) 1 < 0 := by
          exact lt_of_le_of_ne (le_of_not_gt hΔ) (sub_ne_zero.mpr hxy.symm)
        right
        intro v hv
        apply normalized_ge_of_line_nonpos_of_neg hΔ'
        have hline := hnonpos v (huT hv)
        change M.position v 1 - point p 1 ≤ 0 at hline
        rw [hpoint] at hline
        simpa [M, AffineMap.lineMap_apply_module] using hline

theorem markedFaceCarrier_parameter_side (point : P → Plane) (p : P)
    (i : Fin (Fintype.card K.EdgeFace)) (r : ℝ)
    (hpoint : point p = AffineMap.lineMap (K.position (K.edgeFirst i))
      (K.position (K.edgeSecond i)) r)
    {u : Finset (K.markedEdgeChain point).arrangementMesh.Vertex}
    (hu : u ∈ (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.simplexes) :
    (∀ x ∈ (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.cellCarrier u,
        K.edgeParameter i x ≤ r) ∨
      (∀ x ∈ (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.cellCarrier u,
        r ≤ K.edgeParameter i x) := by
  rcases K.markedFace_parameter_side point p i r hpoint hu with hle | hge
  · left
    intro x hx
    apply convexHull_min ?_ ((convex_Iic r).affine_preimage (K.edgeParameter i)) hx
    rintro y ⟨v, hv, rfl⟩
    exact hle v hv
  · right
    intro x hx
    apply convexHull_min ?_ ((convex_Ici r).affine_preimage (K.edgeParameter i)) hx
    rintro y ⟨v, hv, rfl⟩
    exact hge v hv

/-- In a finite complex covering an axis segment, a subsegment with no complex vertex in its
relative interior is contained in one face. -/
theorem exists_face_containing_axis_segment_of_no_vertex
    (L : PlaneComplex) {n a b : ℝ}
    (hn : 0 ≤ n) (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ n)
    (hsupport : L.support = segment ℝ (planePoint 0 0) (planePoint n 0))
    (hcard : ∀ s ∈ L.simplexes, s.card ≤ 2)
    (havoid : ∀ v : L.Vertex, L.position v 0 ≤ a ∨ b ≤ L.position v 0) :
    ∃ s ∈ L.simplexes,
      segment ℝ (planePoint a 0) (planePoint b 0) ⊆ L.cellCarrier s := by
  have axis_mem {c d r : ℝ} (hr : r ∈ segment ℝ c d) :
      planePoint r 0 ∈ segment ℝ (planePoint c 0) (planePoint d 0) := by
    rw [segment_eq_image_lineMap] at hr ⊢
    obtain ⟨t, ht, rfl⟩ := hr
    refine ⟨t, ht, ?_⟩
    ext k
    fin_cases k <;> simp [planePoint, AffineMap.lineMap_apply_module]
  let q := (a + b) / 2
  have hq : q ∈ Set.Icc (0 : ℝ) n := by
    constructor <;> dsimp [q] <;> linarith
  have hqReal : q ∈ segment ℝ (0 : ℝ) n := by
    rwa [segment_eq_Icc hn]
  have hqPlane : planePoint q 0 ∈ L.support := by
    rw [hsupport]
    exact axis_mem hqReal
  rw [PlaneComplex.support] at hqPlane
  simp only [Set.mem_iUnion] at hqPlane
  obtain ⟨s, hs, hqs⟩ := hqPlane
  by_cases habEq : a = b
  · subst b
    have hqa : q = a := by simp [q]
    rw [hqa] at hqs
    refine ⟨s, hs, ?_⟩
    intro x hx
    have hxa : x = planePoint a 0 := by simpa using hx
    rwa [hxa]
  have hablt : a < b := lt_of_le_of_ne hab habEq
  have hqne (v : L.Vertex) : planePoint q 0 ≠ L.position v := by
    intro heq
    have hcoord := congrArg (fun z : Plane => z 0) heq
    rcases havoid v with hv | hv <;> dsimp [q] at hcoord <;> linarith
  have hscard : s.card = 2 := by
    have hspos : 0 < s.card := Finset.card_pos.mpr (L.nonempty_of_mem s hs)
    have hsle := hcard s hs
    have : s.card = 1 ∨ s.card = 2 := by omega
    rcases this with hsone | hstwo
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsone
      have : planePoint q 0 = L.position v := by
        simpa [PlaneComplex.cellCarrier] using hqs
      exact (hqne v this).elim
    · exact hstwo
  obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hscard
  have axis_eq (z : L.Vertex) (hz : z ∈ ({v, w} : Finset L.Vertex)) :
      L.position z = planePoint (L.position z 0) 0 := by
    have hzCarrier : L.position z ∈ L.cellCarrier ({v, w} : Finset L.Vertex) :=
      subset_convexHull ℝ _ ⟨z, hz, rfl⟩
    have hzSupport := L.cellCarrier_subset_support hs hzCarrier
    rw [hsupport, segment_eq_image_lineMap] at hzSupport
    obtain ⟨t, ht, hzt⟩ := hzSupport
    rw [← hzt]
    ext k
    fin_cases k <;> simp [planePoint, AffineMap.lineMap_apply_module]
  have hvAxis := axis_eq v (by simp)
  have hwAxis := axis_eq w (by simp)
  have hqSeg : planePoint q 0 ∈
      segment ℝ (planePoint (L.position v 0) 0) (planePoint (L.position w 0) 0) := by
    rw [← hvAxis, ← hwAxis, ← convexHull_pair]
    change planePoint q 0 ∈ convexHull ℝ
      (L.position '' (({v, w} : Finset L.Vertex) : Set L.Vertex)) at hqs
    have himage : L.position '' (({v, w} : Finset L.Vertex) : Set L.Vertex) =
        {L.position v, L.position w} := by
      ext z
      simp [eq_comm]
    rwa [himage] at hqs
  rw [segment_eq_image_lineMap] at hqSeg
  obtain ⟨t, ht, hqt⟩ := hqSeg
  have hqcoord := congrArg (fun z : Plane => z 0) hqt
  simp only [Fin.isValue, planePoint, AffineMap.lineMap_apply_module, PiLp.add_apply,
    PiLp.smul_apply, Matrix.cons_val_zero, smul_eq_mul] at hqcoord
  rcases havoid v with hvLow | hvHigh <;> rcases havoid w with hwLow | hwHigh
  · have hqle : q ≤ a := by
      rw [← hqcoord]
      calc
        (1 - t) * L.position v 0 + t * L.position w 0 ≤ (1 - t) * a + t * a := by
          gcongr <;> linarith [ht.1, ht.2]
        _ = a := by ring
    dsimp [q] at hqle
    linarith
  · have hsub : segment ℝ (planePoint a 0) (planePoint b 0) ⊆
        segment ℝ (planePoint (L.position v 0) 0) (planePoint (L.position w 0) 0) := by
      apply (convex_segment _ _).segment_subset
      · apply axis_mem
        rw [segment_eq_Icc ((hvLow.trans hab).trans hwHigh)]
        exact ⟨hvLow, hab.trans hwHigh⟩
      · apply axis_mem
        rw [segment_eq_Icc ((hvLow.trans hab).trans hwHigh)]
        exact ⟨hvLow.trans hab, hwHigh⟩
    refine ⟨{v, w}, hs, ?_⟩
    rw [PlaneComplex.cellCarrier, show L.position '' (({v, w} : Finset L.Vertex) : Set L.Vertex) =
        {L.position v, L.position w} by ext z; simp [eq_comm], convexHull_pair, hvAxis, hwAxis]
    exact hsub
  · have hsub : segment ℝ (planePoint a 0) (planePoint b 0) ⊆
        segment ℝ (planePoint (L.position w 0) 0) (planePoint (L.position v 0) 0) := by
      apply (convex_segment _ _).segment_subset
      · apply axis_mem
        rw [segment_eq_Icc ((hwLow.trans hab).trans hvHigh)]
        exact ⟨hwLow, hab.trans hvHigh⟩
      · apply axis_mem
        rw [segment_eq_Icc ((hwLow.trans hab).trans hvHigh)]
        exact ⟨hwLow.trans hab, hvHigh⟩
    refine ⟨{v, w}, hs, ?_⟩
    rw [PlaneComplex.cellCarrier, show L.position '' (({v, w} : Finset L.Vertex) : Set L.Vertex) =
        {L.position v, L.position w} by ext z; simp [eq_comm], convexHull_pair,
      hvAxis, hwAxis]
    simpa only [segment_symm] using hsub
  · have hbq : b ≤ q := by
      rw [← hqcoord]
      calc
        b ≤ (1 - t) * b + t * b := by ring_nf; exact le_rfl
        _ ≤ (1 - t) * L.position v 0 + t * L.position w 0 := by
          gcongr <;> linarith [ht.1, ht.2]
    dsimp [q] at hbq
    linarith

/-- A genuine simplex contained in a graph face has at most two vertices. -/
theorem card_le_two_of_cellCarrier_subset_face
    {L K : PlaneComplex} {u : Finset L.Vertex} (hu : u ∈ L.simplexes)
    {t : Finset K.Vertex} (ht : t ∈ K.simplexes) (htcard : t.card ≤ 2)
    (hut : L.cellCarrier u ⊆ K.cellCarrier t) : u.card ≤ 2 := by
  by_contra hnot
  have hucard : u.card = 3 := by
    have := L.card_le_three u hu
    omega
  have hspanU : affineSpan ℝ (Set.range (fun v : u => L.position v)) = ⊤ :=
    ((L.affineIndependent u hu).affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr (by
      simp [hucard, Plane])
  have hsubset : Set.range (fun v : u => L.position v) ⊆
      (affineSpan ℝ (K.position '' (t : Set K.Vertex)) : Set Plane) := by
    rintro x ⟨v, rfl⟩
    apply convexHull_subset_affineSpan (K.position '' (t : Set K.Vertex))
    apply hut
    exact subset_convexHull ℝ _ ⟨v.1, v.2, rfl⟩
  have hle : affineSpan ℝ (Set.range (fun v : u => L.position v)) ≤
      affineSpan ℝ (K.position '' (t : Set K.Vertex)) := affineSpan_le.mpr hsubset
  rw [hspanU] at hle
  have hspanT : affineSpan ℝ (K.position '' (t : Set K.Vertex)) = ⊤ := top_unique hle
  have himage : Set.range (fun v : t => K.position v) =
      K.position '' (t : Set K.Vertex) := by
    ext x
    simp
  rw [← himage] at hspanT
  have htthree :=
    (K.affineIndependent t ht).affineSpan_eq_top_iff_card_eq_finrank_add_one.mp hspanT
  have : t.card = 3 := by simpa [Plane] using htthree
  omega

/-- Every prescribed mark in the graph support becomes a zero-face of the marked subdivision. -/
theorem exists_markedEdgeSubdivision_vertex (point : P → Plane) (p : P)
    (hp : point p ∈ K.support) :
    ∃ w : (K.markedEdgeSubdivision point).Vertex,
      ({w} : Finset (K.markedEdgeSubdivision point).Vertex) ∈
        (K.markedEdgeSubdivision point).simplexes ∧
      (K.markedEdgeSubdivision point).position w = point p := by
  obtain ⟨w, hwpos, hwface⟩ :=
    (K.markedEdgeChain point).exists_arrangementVertex_position_eq
      (K.markedEdgeChainMarkIndex point p)
  have hchain : (K.markedEdgeChain point).vertex
      (K.markedEdgeChainMarkIndex point p) = point p := by
    exact K.markedEdgeChain_vertex_mark point p
  rw [PlaneComplex.support] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨s, hs, hps⟩ := hp
  refine ⟨w, ?_, ?_⟩
  · apply ((K.markedEdgeChain point).arrangementMesh.toPlaneComplex
      |>.mem_subordinateTo_simplexes_iff K).mpr
    refine ⟨hwface, s, hs, ?_⟩
    intro y hy
    have hyw : y = (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position w := by
      change y ∈ convexHull ℝ
        ((K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position ''
          (({w} : Finset (K.markedEdgeChain point).arrangementMesh.Vertex) :
            Set (K.markedEdgeChain point).arrangementMesh.Vertex)) at hy
      have himage : (K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position ''
          (({w} : Finset (K.markedEdgeChain point).arrangementMesh.Vertex) :
            Set (K.markedEdgeChain point).arrangementMesh.Vertex) =
          {(K.markedEdgeChain point).arrangementMesh.toPlaneComplex.position w} := by
        ext z
        constructor
        · rintro ⟨q, hq, rfl⟩
          rw [Finset.mem_singleton.mp hq]
          exact Set.mem_singleton _
        · intro hz
          rw [Set.mem_singleton_iff] at hz
          subst z
          exact ⟨w, Finset.mem_singleton_self _, rfl⟩
      rw [himage, convexHull_singleton] at hy
      exact hy
    rw [hyw, hwpos, hchain]
    exact hps
  · exact hwpos.trans hchain

end PlaneComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification08_block_02
/- END ClassificationOfSurfaces.Moise.GraphRefinement -/

/- BEGIN ClassificationOfSurfaces.Moise.IntrinsicSubdivision | d1def77cfbae9ccfd1ec9156eddde82174301976b3b9d4226b9233d539131dae -/
section schottkyclassification08_block_03
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Plane subdivisions as intrinsic subdivisions

The Rado induction uses intrinsic complexes, while all finite cutting and common-refinement
machinery is geometric and planar.  This file is the bridge between those layers.  A pure plane
complex is regarded as the intrinsic complex of its maximal triangles, and a geometric
subdivision induces a faithful intrinsic subdivision through the barycentric realization
homeomorphisms.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace PlaneComplex

variable (K : PlaneComplex)

/-- Forget the planar placement of a complex, retaining its maximal triangles as an intrinsic
two-complex. -/
@[reducible] def toIntrinsic : IntrinsicTwoComplex where
  Vertex := K.Vertex
  faces := K.cells
  faces_card := fun _ ht => K.card_of_mem_cells ht

@[simp] theorem toIntrinsic_faces : K.toIntrinsic.faces = K.cells := rfl

/-- Barycentric evaluation is an affine map on the ambient coordinate space. -/
noncomputable def baryEvalAffine : (K.Vertex → ℝ) →ᵃ[ℝ] Plane :=
  (∑ v, (LinearMap.proj v).smulRight (K.position v)).toAffineMap

@[simp] theorem baryEvalAffine_apply (x : K.Vertex → ℝ) :
    K.baryEvalAffine x = K.baryEval x := by
  simp [baryEvalAffine, baryEval]

/-- Barycentric coordinates in one maximal triangle, extended by zero to all vertices of the
complex. -/
noncomputable def faceCoords (T : K.toTriangleMesh.Triangle) :
    Plane →ᵃ[ℝ] (K.Vertex → ℝ) := by
  classical
  let b := affineBasisOfTriangle
    (K.toTriangleMesh.position ∘ K.toTriangleMesh.orderedVertex T)
    (K.toTriangleMesh.orderedVertex_affineIndependent T)
  exact AffineMap.pi fun v =>
    if hv : v ∈ T.1 then
      b.coord (K.toTriangleMesh.triangleEquiv T ⟨v, hv⟩)
    else
      AffineMap.const ℝ Plane 0

@[simp] theorem faceCoords_apply_of_mem (T : K.toTriangleMesh.Triangle)
    {v : K.Vertex} (hv : v ∈ T.1) (p : Plane) :
    K.faceCoords T p v =
      (affineBasisOfTriangle
        (K.toTriangleMesh.position ∘ K.toTriangleMesh.orderedVertex T)
        (K.toTriangleMesh.orderedVertex_affineIndependent T)).coord
          (K.toTriangleMesh.triangleEquiv T ⟨v, hv⟩) p := by
  classical
  simp [faceCoords, hv]

@[simp] theorem faceCoords_apply_of_notMem (T : K.toTriangleMesh.Triangle)
    {v : K.Vertex} (hv : v ∉ T.1) (p : Plane) :
    K.faceCoords T p v = 0 := by
  classical
  simp [faceCoords, hv]

theorem faceCoords_support (T : K.toTriangleMesh.Triangle) (p : Plane) :
    ∀ v ∉ T.1, K.faceCoords T p v = 0 :=
  fun _ hv => K.faceCoords_apply_of_notMem T hv p

theorem sum_faceCoords (T : K.toTriangleMesh.Triangle) (p : Plane) :
    ∑ v, K.faceCoords T p v = 1 := by
  classical
  let b := affineBasisOfTriangle
    (K.toTriangleMesh.position ∘ K.toTriangleMesh.orderedVertex T)
    (K.toTriangleMesh.orderedVertex_affineIndependent T)
  rw [K.sum_eq_sum_of_support (K.faceCoords_support T p)]
  erw [← Finset.sum_coe_sort]
  calc
    ∑ v : T.1, K.faceCoords T p v.1 =
        ∑ v : T.1, b.coord (K.toTriangleMesh.triangleEquiv T v) p := by
      apply Finset.sum_congr rfl
      intro v hv
      exact K.faceCoords_apply_of_mem T v.2 p
    _ = ∑ i : Fin 3, b.coord i p :=
      (K.toTriangleMesh.triangleEquiv T).sum_comp (fun i => b.coord i p)
    _ = 1 := b.sum_coord_apply_eq_one p

theorem orderedVertex_triangleEquiv (T : K.toTriangleMesh.Triangle) (v : T.1) :
    K.toTriangleMesh.orderedVertex T (K.toTriangleMesh.triangleEquiv T v) = v.1 := by
  simp [TriangleMesh.orderedVertex]

theorem baryEval_faceCoords (T : K.toTriangleMesh.Triangle) (p : Plane) :
    K.baryEval (K.faceCoords T p) = p := by
  classical
  let b := affineBasisOfTriangle
    (K.toTriangleMesh.position ∘ K.toTriangleMesh.orderedVertex T)
    (K.toTriangleMesh.orderedVertex_affineIndependent T)
  rw [K.baryEval_eq_sum_of_support (K.faceCoords_support T p)]
  erw [← Finset.sum_coe_sort]
  calc
    ∑ v : T.1, K.faceCoords T p v.1 • K.position v.1 =
        ∑ v : T.1, b.coord (K.toTriangleMesh.triangleEquiv T v) p •
          K.position v.1 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [K.faceCoords_apply_of_mem T v.2 p]
    _ = ∑ i : Fin 3, b.coord i p •
          K.position (K.toTriangleMesh.orderedVertex T i) := by
      calc
        _ = ∑ v : T.1, b.coord (K.toTriangleMesh.triangleEquiv T v) p •
            K.position (K.toTriangleMesh.orderedVertex T
              (K.toTriangleMesh.triangleEquiv T v)) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [K.orderedVertex_triangleEquiv T v]
        _ = _ :=
          (K.toTriangleMesh.triangleEquiv T).sum_comp
            (fun i => b.coord i p • K.position (K.toTriangleMesh.orderedVertex T i))
    _ = p := by
      change ∑ i : Fin 3, b.coord i p • b i = p
      exact b.linear_combination_coord_eq_self p

/-- The affine coordinates of a geometric triangle vertex are the corresponding unit
barycentric coordinates. -/
theorem faceCoords_position (T : K.toTriangleMesh.Triangle) {v : K.Vertex}
    (hv : v ∈ T.1) :
    K.faceCoords T (K.position v) = Pi.single v 1 := by
  apply K.baryEval_injOn_face (K.mem_simplexes_of_mem_cells T.2)
  · exact K.faceCoords_support T (K.position v)
  · intro w hw
    have hwv : w ≠ v := by
      intro h
      subst w
      exact hw hv
    simp [hwv]
  · exact K.sum_faceCoords T (K.position v)
  · simp
  · rw [K.baryEval_faceCoords]
    simp [PlaneComplex.baryEval]

/-- The inverse barycentric realization map sends a point of a maximal geometric triangle to
the corresponding intrinsic face. -/
theorem realizationHomeomorph_symm_mem_faceCarrier (hpure : K.IsPure2)
    (T : K.toTriangleMesh.Triangle) (p : K.support)
    (hp : p.1 ∈ K.cellCarrier T.1) :
    (K.realizationHomeomorph hpure).symm p ∈ K.toIntrinsic.faceCarrier T.1 := by
  classical
  obtain ⟨x, hxsupp, hx0, hx1, hxeval⟩ := K.exists_weights_of_mem_cellCarrier hp
  let z : K.toIntrinsic.realization :=
    ⟨x, ⟨hx0, hx1⟩, T.1, T.2, hxsupp⟩
  have hz : (K.realizationHomeomorph hpure).symm p = z := by
    have hzimage : K.realizationHomeomorph hpure z = p := by
      apply Subtype.ext
      exact hxeval
    calc
      (K.realizationHomeomorph hpure).symm p =
          (K.realizationHomeomorph hpure).symm
            (K.realizationHomeomorph hpure z) := congrArg _ hzimage.symm
      _ = z := (K.realizationHomeomorph hpure).symm_apply_apply z
  rw [hz]
  exact hxsupp

/-- On a selected maximal triangle, the inverse realization homeomorphism is given by the
explicit affine barycentric-coordinate map for that triangle. -/
theorem realizationHomeomorph_symm_val_eq_faceCoords (hpure : K.IsPure2)
    (T : K.toTriangleMesh.Triangle) (p : K.support)
    (hp : p.1 ∈ K.cellCarrier T.1) :
    ((K.realizationHomeomorph hpure).symm p).1 = K.faceCoords T p.1 := by
  let z := (K.realizationHomeomorph hpure).symm p
  apply K.baryEval_injOn_face (K.mem_simplexes_of_mem_cells T.2)
  · exact K.realizationHomeomorph_symm_mem_faceCarrier hpure T p hp
  · exact K.faceCoords_support T p.1
  · exact z.2.1.2
  · exact K.sum_faceCoords T p.1
  · calc
      K.baryEval z.1 = (K.realizationHomeomorph hpure z).1 := by
        rw [K.realizationHomeomorph_apply]
      _ = p.1 := congrArg Subtype.val
        ((K.realizationHomeomorph hpure).apply_symm_apply p)
      _ = K.baryEval (K.faceCoords T p.1) := (K.baryEval_faceCoords T p.1).symm

/-- Barycentric realization carries every abstract face carrier exactly onto its geometric
convex hull. -/
theorem realizationHomeomorph_image_faceCarrier (hpure : K.IsPure2)
    {s : Finset K.Vertex} (hs : s ∈ K.simplexes) :
    (fun x : K.toIntrinsic.realization => (K.realizationHomeomorph hpure x).1) ''
        K.toIntrinsic.faceCarrier s = K.cellCarrier s := by
  classical
  apply Set.Subset.antisymm
  · rintro p ⟨x, hx, rfl⟩
    change (K.realizationHomeomorph hpure x).1 ∈ K.cellCarrier s
    rw [K.realizationHomeomorph_apply]
    exact K.baryEval_mem_cellCarrier hx x.2.1.1 x.2.1.2
  · intro p hp
    obtain ⟨t, ht, hst, htcard⟩ := hpure s hs
    have htcell : t ∈ K.cells := Finset.mem_filter.mpr ⟨ht, htcard⟩
    obtain ⟨x, hxsupp, hx0, hx1, hxeval⟩ := K.exists_weights_of_mem_cellCarrier hp
    have hxt : ∀ v ∉ t, x v = 0 := fun v hv => hxsupp v (fun hvs => hv (hst hvs))
    let z : K.toIntrinsic.realization :=
      ⟨x, ⟨hx0, hx1⟩, ⟨t, htcell, hxt⟩⟩
    refine ⟨z, hxsupp, ?_⟩
    change (K.realizationHomeomorph hpure z).1 = p
    rw [K.realizationHomeomorph_apply]
    exact hxeval

end PlaneComplex

namespace IntrinsicTwoComplex

/-- The intrinsic homeomorphism underlying a geometric subdivision of pure plane complexes. -/
noncomputable def subdivisionHomeomorph {L K : PlaneComplex}
    (hLpure : L.IsPure2) (hKpure : K.IsPure2) (hLK : L.Subdivides K) :
    L.toIntrinsic.realization ≃ₜ K.toIntrinsic.realization :=
  (L.realizationHomeomorph hLpure).trans
    ((Homeomorph.setCongr hLK.1).trans (K.realizationHomeomorph hKpure).symm)

theorem baryEval_subdivisionHomeomorph {L K : PlaneComplex}
    (hLpure : L.IsPure2) (hKpure : K.IsPure2) (hLK : L.Subdivides K)
    (x : L.toIntrinsic.realization) :
    K.baryEval ((subdivisionHomeomorph hLpure hKpure hLK x).1) = L.baryEval x.1 := by
  let q : L.support := L.realizationHomeomorph hLpure x
  let p : K.support := Homeomorph.setCongr hLK.1 q
  have h := congrArg Subtype.val
    ((K.realizationHomeomorph hKpure).apply_symm_apply p)
  change K.baryEval ((K.realizationHomeomorph hKpure).symm p).1 = p.1 at h
  change K.baryEval ((subdivisionHomeomorph hLpure hKpure hLK x).1) =
    L.baryEval x.1
  exact h

/-- A geometric subdivision of pure finite plane complexes is a faithful subdivision of their
intrinsic realizations. -/
noncomputable def subdivisionOfPlaneSubdivision {L K : PlaneComplex}
    (hLpure : L.IsPure2) (hKpure : K.IsPure2) (hLK : L.Subdivides K) :
    K.toIntrinsic.Subdivision where
  refined := L.toIntrinsic
  homeo := subdivisionHomeomorph hLpure hKpure hLK
  affineOnFace := by
    intro s hs
    have hsSimplex : s ∈ L.simplexes := L.mem_simplexes_of_mem_cells hs
    obtain ⟨u, hu, hsu⟩ := hLK.2 s hsSimplex
    obtain ⟨t, ht, hut, htcard⟩ := hKpure u hu
    have htCell : t ∈ K.cells := Finset.mem_filter.mpr ⟨ht, htcard⟩
    let T : K.toTriangleMesh.Triangle := ⟨t, htCell⟩
    refine ⟨(K.faceCoords T).comp L.baryEvalAffine, ?_⟩
    intro x hx
    let y := subdivisionHomeomorph hLpure hKpure hLK x
    have hxGeom : L.baryEval x.1 ∈ L.cellCarrier s :=
      L.baryEval_mem_cellCarrier hx x.2.1.1 x.2.1.2
    have hpGeom : L.baryEval x.1 ∈ K.cellCarrier t :=
      convexHull_mono (Set.image_mono hut) (hsu hxGeom)
    let p : K.support := ⟨L.baryEval x.1, by
      rw [← hLK.1]
      exact L.cellCarrier_subset_support hsSimplex hxGeom⟩
    have hyFace : y ∈ K.toIntrinsic.faceCarrier t := by
      change (K.realizationHomeomorph hKpure).symm p ∈ K.toIntrinsic.faceCarrier t
      exact K.realizationHomeomorph_symm_mem_faceCarrier hKpure T p hpGeom
    have hcoord := K.baryEval_injOn_face (K.mem_simplexes_of_mem_cells htCell)
      hyFace (K.faceCoords_support T (L.baryEval x.1)) y.2.1.2
      (K.sum_faceCoords T (L.baryEval x.1))
      (by rw [baryEval_subdivisionHomeomorph hLpure hKpure hLK,
        K.baryEval_faceCoords])
    rw [AffineMap.comp_apply, PlaneComplex.baryEvalAffine_apply]
    exact hcoord
  subordinate := by
    intro s hs
    have hsSimplex : s ∈ L.simplexes := L.mem_simplexes_of_mem_cells hs
    obtain ⟨u, hu, hsu⟩ := hLK.2 s hsSimplex
    obtain ⟨t, ht, hut, htcard⟩ := hKpure u hu
    have htCell : t ∈ K.cells := Finset.mem_filter.mpr ⟨ht, htcard⟩
    let T : K.toTriangleMesh.Triangle := ⟨t, htCell⟩
    refine ⟨t, htCell, ?_⟩
    intro x hx
    have hxGeom : L.baryEval x.1 ∈ L.cellCarrier s :=
      L.baryEval_mem_cellCarrier hx x.2.1.1 x.2.1.2
    have hpGeom : L.baryEval x.1 ∈ K.cellCarrier t :=
      convexHull_mono (Set.image_mono hut) (hsu hxGeom)
    let p : K.support := ⟨L.baryEval x.1, by
      rw [← hLK.1]
      exact L.cellCarrier_subset_support hsSimplex hxGeom⟩
    change (K.realizationHomeomorph hKpure).symm p ∈ K.toIntrinsic.faceCarrier t
    exact K.realizationHomeomorph_symm_mem_faceCarrier hKpure T p hpGeom

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification08_block_03
/- END ClassificationOfSurfaces.Moise.IntrinsicSubdivision -/

/- BEGIN ClassificationOfSurfaces.Moise.PolygonalFamilyPolyhedron | fbe1f485bfca13a7f6075e561a3640b8ed797acb5e2a6c6a3eac7aa65e63ac52 -/
section schottkyclassification08_block_04
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Finite unions of polygonal disks

The cellwise intrinsic approximation produces finitely many polygonal closed disks whose
interiors are compatible.  Independently chosen disk triangulations need not agree on their
common boundary segments.  This file instead cuts one enclosing triangle by every edge line in
the family and retains precisely the chambers lying inside at least one polygon.  The resulting
single triangle mesh has support equal to the union.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace TriangleMesh

/-- The canonical barycentric embedding of a finite plane triangle mesh realization. -/
noncomputable def coordinateEmbed (M : TriangleMesh) :
    GeometricRealization M.Vertex M.triangles → Plane :=
  fun x ↦ M.toPlaneComplex.baryEval x.1

theorem isEmbedding_coordinateEmbed (M : TriangleMesh) :
    _root_.Topology.IsEmbedding M.coordinateEmbed := by
  have hfaces : GeometricRealization M.Vertex M.triangles =
      GeometricRealization M.Vertex M.toPlaneComplex.cells := by
    rw [M.toPlaneComplex_cells]
  let hhomeo := (Homeomorph.setCongr hfaces).trans
    (M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2)
  have hhomeo_apply (x : GeometricRealization M.Vertex M.triangles) :
      (hhomeo x).1 = M.coordinateEmbed x := by
    rfl
  have h := _root_.Topology.IsEmbedding.subtypeVal.comp hhomeo.isEmbedding
  have heq : (Subtype.val ∘ hhomeo) = M.coordinateEmbed := by
    funext x
    exact hhomeo_apply x
  rw [heq] at h
  exact h

theorem range_coordinateEmbed (M : TriangleMesh) :
    Set.range M.coordinateEmbed = M.toPlaneComplex.support := by
  have hfaces : GeometricRealization M.Vertex M.triangles =
      GeometricRealization M.Vertex M.toPlaneComplex.cells := by
    rw [M.toPlaneComplex_cells]
  let hhomeo := (Homeomorph.setCongr hfaces).trans
    (M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2)
  have hhomeo_apply (x : GeometricRealization M.Vertex M.triangles) :
      (hhomeo x).1 = M.coordinateEmbed x := by
    rfl
  apply Set.Subset.antisymm
  · rintro x ⟨y, rfl⟩
    rw [← hhomeo_apply y]
    exact (hhomeo y).2
  · intro x hx
    obtain ⟨y, hy⟩ := hhomeo.surjective ⟨x, hx⟩
    refine ⟨y, ?_⟩
    rw [← hhomeo_apply y]
    exact congrArg Subtype.val hy

/-- Restrict the coordinate embedding to any plane region containing the mesh support. -/
noncomputable def coordinateEmbedInto (M : TriangleMesh) (W : Set Plane)
    (hW : M.toPlaneComplex.support ⊆ W) :
    GeometricRealization M.Vertex M.triangles → W :=
  fun x ↦ ⟨M.coordinateEmbed x, hW (by
    rw [← M.range_coordinateEmbed]
    exact Set.mem_range_self x)⟩

theorem isEmbedding_coordinateEmbedInto (M : TriangleMesh) (W : Set Plane)
    (hW : M.toPlaneComplex.support ⊆ W) :
    _root_.Topology.IsEmbedding (M.coordinateEmbedInto W hW) :=
  M.isEmbedding_coordinateEmbed.codRestrict W _

end TriangleMesh

namespace PolygonalFamily

variable {ι : Type*} [Fintype ι] (J : ι → PolygonalCircle)

/-- The union of the finitely many closed polygonal disks. -/
def closedRegion : Set Plane :=
  ⋃ i, (J i).closedRegion

omit [Fintype ι] in
theorem isCompact_closedRegion [Finite ι] : IsCompact (closedRegion J) := by
  letI := Fintype.ofFinite ι
  exact isCompact_iUnion fun i ↦ (J i).isCompact_closedRegion

/-- A positive radius of a ball containing every disk in the family. -/
noncomputable def enclosingRadius : ℝ :=
  max ((isCompact_closedRegion J).isBounded.subset_closedBall (0 : Plane)).choose 1

theorem enclosingRadius_pos : 0 < enclosingRadius J :=
  lt_of_lt_of_le zero_lt_one (le_max_right _ _)

theorem closedRegion_subset_enclosingBall :
    closedRegion J ⊆ Metric.closedBall (0 : Plane) (enclosingRadius J) := by
  intro x hx
  have h := ((isCompact_closedRegion J).isBounded.subset_closedBall
    (0 : Plane)).choose_spec hx
  exact Metric.closedBall_subset_closedBall (le_max_left _ _) h

/-- The common enclosing triangle. -/
noncomputable def enclosingMesh : TriangleMesh :=
  TriangleMesh.single (PolygonalCircle.enclosingTriangleVertices (enclosingRadius J))
    (PolygonalCircle.enclosingTriangleVertices_affineIndependent (enclosingRadius_pos J))

theorem closedRegion_subset_enclosingMesh_support :
    closedRegion J ⊆ (enclosingMesh J).toPlaneComplex.support := by
  rw [enclosingMesh, TriangleMesh.single_support]
  exact (closedRegion_subset_enclosingBall J).trans
    (PolygonalCircle.closedBall_subset_enclosingTriangle (enclosingRadius_pos J))

/-- Every supporting line of every polygon in the family. -/
noncomputable def edgeLines : List (Plane →ᵃ[ℝ] ℝ) :=
  (Finset.univ : Finset ι).toList.flatMap fun i ↦ (J i).edgeLines

theorem edgeLine_mem_edgeLines (i : ι) (k : ZMod (J i).n) :
    (J i).edgeLine k ∈ edgeLines J := by
  rw [edgeLines, List.mem_flatMap]
  exact ⟨i, by simp, (J i).edgeLine_mem_edgeLines k⟩

/-- The common supporting-line arrangement. -/
noncomputable def arrangementMesh : TriangleMesh :=
  (enclosingMesh J).refineByLines (edgeLines J)

theorem arrangementMesh_support :
    (arrangementMesh J).toPlaneComplex.support =
      (enclosingMesh J).toPlaneComplex.support :=
  (enclosingMesh J).refineByLines_support (edgeLines J)

theorem closedRegion_subset_arrangementMesh_support :
    closedRegion J ⊆ (arrangementMesh J).toPlaneComplex.support := by
  rw [arrangementMesh_support]
  exact closedRegion_subset_enclosingMesh_support J

theorem arrangementMesh_isMonochromatic (i : ι) (k : ZMod (J i).n) :
    (arrangementMesh J).IsMonochromatic ((J i).edgeLine k) :=
  (enclosingMesh J).refineByLines_isMonochromatic_of_mem
    (edgeLines J) (edgeLine_mem_edgeLines J i k)

/-- Carrier of one maximal chamber of the common arrangement. -/
def arrangementTriangleCarrier (t : Finset (arrangementMesh J).Vertex) : Set Plane :=
  convexHull ℝ ((arrangementMesh J).position '' (t : Set _))

theorem convex_arrangementTriangleCarrier
    (t : Finset (arrangementMesh J).Vertex) :
    Convex ℝ (arrangementTriangleCarrier J t) :=
  convex_convexHull ℝ _

theorem isClosed_arrangementTriangleCarrier
    (t : Finset (arrangementMesh J).Vertex) :
    IsClosed (arrangementTriangleCarrier J t) :=
  (t.finite_toSet.image (arrangementMesh J).position).isClosed_convexHull ℝ

theorem arrangementTriangleCarrier_interior_nonempty
    {t : Finset (arrangementMesh J).Vertex} (ht : t ∈ (arrangementMesh J).triangles) :
    (interior (arrangementTriangleCarrier J t)).Nonempty := by
  apply (convex_arrangementTriangleCarrier J t).interior_nonempty_iff_affineSpan_eq_top.mpr
  rw [arrangementTriangleCarrier, affineSpan_convexHull]
  have hrange : Set.range (fun v : t ↦ (arrangementMesh J).position v) =
      (arrangementMesh J).position '' (t : Set _) := by
    ext x
    simp
  rw [← hrange]
  apply
    ((arrangementMesh J).affineIndependent_triangle t ht)
      |>.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  rw [Fintype.card_coe, (arrangementMesh J).card_triangle t ht]
  simp [Plane]

theorem closure_interior_arrangementTriangleCarrier
    {t : Finset (arrangementMesh J).Vertex} (ht : t ∈ (arrangementMesh J).triangles) :
    closure (interior (arrangementTriangleCarrier J t)) =
      arrangementTriangleCarrier J t := by
  calc
    closure (interior (arrangementTriangleCarrier J t)) =
        closure (arrangementTriangleCarrier J t) :=
      (convex_arrangementTriangleCarrier J t).closure_interior_eq_closure_of_nonempty_interior
        (arrangementTriangleCarrier_interior_nonempty J ht)
    _ = arrangementTriangleCarrier J t :=
      (isClosed_arrangementTriangleCarrier J t).closure_eq

/-- Every open arrangement chamber misses every polygon boundary in the family. -/
theorem arrangementTriangle_interior_disjoint_carrier
    (i : ι) {t : Finset (arrangementMesh J).Vertex}
    (ht : t ∈ (arrangementMesh J).triangles) :
    Disjoint (interior (arrangementTriangleCarrier J t)) (J i).carrier := by
  rw [Set.disjoint_left]
  intro x hxint hxcarrier
  obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxcarrier
  have hxzero : (J i).edgeLine k x = 0 :=
    (J i).edgeLine_eq_zero_of_mem_edgeSegment k hxk
  rcases arrangementMesh_isMonochromatic J i k t ht with hpos | hneg
  · have hsubset : arrangementTriangleCarrier J t ⊆
        {y | 0 ≤ (J i).edgeLine k y} := by
      rw [arrangementTriangleCarrier]
      apply convexHull_min
      · rintro y ⟨v, hv, rfl⟩
        exact hpos v hv
      · exact (convex_Ici (0 : ℝ)).affine_preimage ((J i).edgeLine k)
    have hxstrict := interior_mono hsubset hxint
    rw [(J i).interior_edgeLine_nonneg k] at hxstrict
    change 0 < (J i).edgeLine k x at hxstrict
    linarith
  · have hsubset : arrangementTriangleCarrier J t ⊆
        {y | (J i).edgeLine k y ≤ 0} := by
      rw [arrangementTriangleCarrier]
      apply convexHull_min
      · rintro y ⟨v, hv, rfl⟩
        exact hneg v hv
      · exact (convex_Iic (0 : ℝ)).affine_preimage ((J i).edgeLine k)
    have hxstrict := interior_mono hsubset hxint
    rw [(J i).interior_edgeLine_nonpos k] at hxstrict
    change (J i).edgeLine k x < 0 at hxstrict
    linarith

theorem arrangementTriangle_interior_side
    (i : ι) {t : Finset (arrangementMesh J).Vertex}
    (ht : t ∈ (arrangementMesh J).triangles) :
    interior (arrangementTriangleCarrier J t) ⊆ (J i).interiorRegion ∨
      interior (arrangementTriangleCarrier J t) ⊆ (J i).exteriorRegion := by
  let s := interior (arrangementTriangleCarrier J t)
  have hsconn : IsPreconnected s :=
    (convex_arrangementTriangleCarrier J t).interior.isPreconnected
  have hsoff : s ⊆ (J i).carrierᶜ := by
    intro x hx
    exact fun hxcarrier ↦ Set.disjoint_left.mp
      (arrangementTriangle_interior_disjoint_carrier J i ht) hx hxcarrier
  have hsunion : s ⊆ (J i).interiorRegion ∪ (J i).exteriorRegion := by
    rw [(J i).interior_union_exterior]
    exact hsoff
  obtain ⟨x, hx⟩ := arrangementTriangleCarrier_interior_nonempty J ht
  rcases hsunion hx with hxin | hxout
  · exact Or.inl <| hsconn.subset_left_of_subset_union
      (J i).isOpen_interiorRegion (J i).isOpen_exteriorRegion
      (J i).disjoint_interior_exterior hsunion ⟨x, hx, hxin⟩
  · exact Or.inr <| hsconn.subset_right_of_subset_union
      (J i).isOpen_interiorRegion (J i).isOpen_exteriorRegion
      (J i).disjoint_interior_exterior hsunion ⟨x, hx, hxout⟩

/-- A chamber is retained when it lies on the bounded side of at least one polygon. -/
def IsInteriorArrangementTriangle
    (t : Finset (arrangementMesh J).Vertex) : Prop :=
  ∃ i, interior (arrangementTriangleCarrier J t) ⊆ (J i).interiorRegion

/-- The common finite mesh of the union of all closed regions. -/
noncomputable def closedRegionMesh : TriangleMesh := by
  classical
  exact (arrangementMesh J).restrictTriangles (IsInteriorArrangementTriangle J)

theorem closedRegionMesh_triangle_mem
    {t : Finset (closedRegionMesh J).Vertex} :
    t ∈ (closedRegionMesh J).triangles ↔
      t ∈ (arrangementMesh J).triangles ∧ IsInteriorArrangementTriangle J t := by
  classical
  exact (arrangementMesh J).mem_restrictTriangles_triangles
    (IsInteriorArrangementTriangle J)

theorem arrangementTriangleCarrier_subset_closedRegion
    {t : Finset (arrangementMesh J).Vertex} (ht : t ∈ (arrangementMesh J).triangles)
    (hinside : IsInteriorArrangementTriangle J t) :
    arrangementTriangleCarrier J t ⊆ closedRegion J := by
  obtain ⟨i, hi⟩ := hinside
  rw [← closure_interior_arrangementTriangleCarrier J ht]
  exact (closure_mono hi).trans fun x hx ↦ Set.mem_iUnion.mpr
    ⟨i, by simpa only [PolygonalCircle.closedRegion] using hx⟩

theorem closedRegionMesh_support_subset :
    (closedRegionMesh J).toPlaneComplex.support ⊆ closedRegion J := by
  rw [TriangleMesh.toPlaneComplex_support]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  obtain ⟨htarr, htinside⟩ := (closedRegionMesh_triangle_mem J).mp ht
  exact arrangementTriangleCarrier_subset_closedRegion J htarr htinside hxt

theorem interiorRegion_subset_closedRegionMesh_support (i : ι) :
    (J i).interiorRegion ⊆ (closedRegionMesh J).toPlaneComplex.support := by
  intro x hxinside
  have hxclosed : x ∈ closedRegion J := Set.mem_iUnion.mpr
    ⟨i, by rw [(J i).closedRegion_eq_union]; exact Or.inl hxinside⟩
  have hxsupport := closedRegion_subset_arrangementMesh_support J hxclosed
  rw [TriangleMesh.toPlaneComplex_support] at hxsupport
  simp only [Set.mem_iUnion] at hxsupport
  obtain ⟨t, ht, hxt⟩ := hxsupport
  have hxclosure : x ∈ closure (interior (arrangementTriangleCarrier J t)) := by
    rw [closure_interior_arrangementTriangleCarrier J ht]
    exact hxt
  have hxclosureInter : x ∈ closure
      ((J i).interiorRegion ∩ interior (arrangementTriangleCarrier J t)) :=
    (J i).isOpen_interiorRegion.inter_closure ⟨hxinside, hxclosure⟩
  obtain ⟨y, hyinside, hyt⟩ := Set.Nonempty.of_closure ⟨x, hxclosureInter⟩
  have htinside : interior (arrangementTriangleCarrier J t) ⊆
      (J i).interiorRegion := by
    rcases arrangementTriangle_interior_side J i ht with hin | hout
    · exact hin
    · exact False.elim <| Set.disjoint_left.mp (J i).disjoint_interior_exterior
        hyinside (hout hyt)
  rw [TriangleMesh.toPlaneComplex_support]
  simp only [Set.mem_iUnion]
  exact ⟨t, (closedRegionMesh_triangle_mem J).mpr
    ⟨ht, ⟨i, htinside⟩⟩, hxt⟩

theorem closedRegion_subset_closedRegionMesh_support :
    closedRegion J ⊆ (closedRegionMesh J).toPlaneComplex.support := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  rw [PolygonalCircle.closedRegion] at hxi
  exact closure_minimal (interiorRegion_subset_closedRegionMesh_support J i)
    (closedRegionMesh J).toPlaneComplex.isCompact_support.isClosed hxi

/-- Exact support of the common family mesh. -/
theorem closedRegionMesh_support :
    (closedRegionMesh J).toPlaneComplex.support = closedRegion J :=
  Set.Subset.antisymm (closedRegionMesh_support_subset J)
    (closedRegion_subset_closedRegionMesh_support J)

/-! ## Synchronized submeshes of one family arrangement -/

/-- The union of a selected subfamily of polygonal closed disks. -/
def selectedClosedRegion (p : ι → Prop) : Set Plane :=
  ⋃ i, ⋃ (_ : p i), (J i).closedRegion

/-- An arrangement chamber belongs to the selected submesh when its interior lies on the
bounded side of one selected polygon. -/
def IsSelectedInteriorArrangementTriangle (p : ι → Prop)
    (t : Finset (arrangementMesh J).Vertex) : Prop :=
  ∃ i, p i ∧ interior (arrangementTriangleCarrier J t) ⊆ (J i).interiorRegion

/-- Restrict the common arrangement to the chambers belonging to a selected subfamily.
Different predicates therefore produce meshes with definitionally the same ambient vertex
type and position map. -/
noncomputable def selectedClosedRegionMesh (p : ι → Prop) : TriangleMesh := by
  classical
  exact (arrangementMesh J).restrictTriangles
    (IsSelectedInteriorArrangementTriangle J p)

theorem selectedClosedRegionMesh_triangle_mem (p : ι → Prop)
    {t : Finset (selectedClosedRegionMesh J p).Vertex} :
    t ∈ (selectedClosedRegionMesh J p).triangles ↔
      t ∈ (arrangementMesh J).triangles ∧
        IsSelectedInteriorArrangementTriangle J p t := by
  classical
  exact (arrangementMesh J).mem_restrictTriangles_triangles
    (IsSelectedInteriorArrangementTriangle J p)

theorem arrangementTriangleCarrier_subset_selectedClosedRegion
    (p : ι → Prop) {t : Finset (arrangementMesh J).Vertex}
    (ht : t ∈ (arrangementMesh J).triangles)
    (hinside : IsSelectedInteriorArrangementTriangle J p t) :
    arrangementTriangleCarrier J t ⊆ selectedClosedRegion J p := by
  obtain ⟨i, hpi, hi⟩ := hinside
  rw [← closure_interior_arrangementTriangleCarrier J ht]
  exact (closure_mono hi).trans fun x hx ↦ Set.mem_iUnion.mpr
    ⟨i, Set.mem_iUnion.mpr
      ⟨hpi, by simpa only [PolygonalCircle.closedRegion] using hx⟩⟩

theorem selectedClosedRegionMesh_support_subset (p : ι → Prop) :
    (selectedClosedRegionMesh J p).toPlaneComplex.support ⊆
      selectedClosedRegion J p := by
  rw [TriangleMesh.toPlaneComplex_support]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  obtain ⟨htarr, htinside⟩ :=
    (selectedClosedRegionMesh_triangle_mem J p).mp ht
  exact arrangementTriangleCarrier_subset_selectedClosedRegion
    J p htarr htinside hxt

theorem interiorRegion_subset_selectedClosedRegionMesh_support
    (p : ι → Prop) (i : ι) (hpi : p i) :
    (J i).interiorRegion ⊆
      (selectedClosedRegionMesh J p).toPlaneComplex.support := by
  intro x hxinside
  have hxselected : x ∈ selectedClosedRegion J p := Set.mem_iUnion.mpr
    ⟨i, Set.mem_iUnion.mpr
      ⟨hpi, by
        rw [(J i).closedRegion_eq_union]
        exact Or.inl hxinside⟩⟩
  have hxclosed : x ∈ closedRegion J := by
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxselected
    obtain ⟨_, hxi⟩ := Set.mem_iUnion.mp hxi
    exact Set.mem_iUnion.mpr ⟨i, hxi⟩
  have hxsupport := closedRegion_subset_arrangementMesh_support J hxclosed
  rw [TriangleMesh.toPlaneComplex_support] at hxsupport
  simp only [Set.mem_iUnion] at hxsupport
  obtain ⟨t, ht, hxt⟩ := hxsupport
  have hxclosure : x ∈ closure
      (interior (arrangementTriangleCarrier J t)) := by
    rw [closure_interior_arrangementTriangleCarrier J ht]
    exact hxt
  have hxclosureInter : x ∈ closure
      ((J i).interiorRegion ∩ interior (arrangementTriangleCarrier J t)) :=
    (J i).isOpen_interiorRegion.inter_closure ⟨hxinside, hxclosure⟩
  obtain ⟨y, hyinside, hyt⟩ := Set.Nonempty.of_closure ⟨x, hxclosureInter⟩
  have htinside : interior (arrangementTriangleCarrier J t) ⊆
      (J i).interiorRegion := by
    rcases arrangementTriangle_interior_side J i ht with hin | hout
    · exact hin
    · exact False.elim <| Set.disjoint_left.mp
        (J i).disjoint_interior_exterior hyinside (hout hyt)
  rw [TriangleMesh.toPlaneComplex_support]
  simp only [Set.mem_iUnion]
  exact ⟨t, (selectedClosedRegionMesh_triangle_mem J p).mpr
    ⟨ht, ⟨i, hpi, htinside⟩⟩, hxt⟩

theorem selectedClosedRegion_subset_selectedClosedRegionMesh_support
    (p : ι → Prop) :
    selectedClosedRegion J p ⊆
      (selectedClosedRegionMesh J p).toPlaneComplex.support := by
  intro x hx
  obtain ⟨i, hpi, hxi⟩ := Set.mem_iUnion₂.mp hx
  rw [PolygonalCircle.closedRegion] at hxi
  exact closure_minimal
    (interiorRegion_subset_selectedClosedRegionMesh_support J p i hpi)
    (selectedClosedRegionMesh J p).toPlaneComplex.isCompact_support.isClosed hxi

/-- Every selected subfamily is recovered exactly as a face restriction of the one common
arrangement.  This is the conforming old/new submesh interface used by the Radó weld. -/
theorem selectedClosedRegionMesh_support (p : ι → Prop) :
    (selectedClosedRegionMesh J p).toPlaneComplex.support =
      selectedClosedRegion J p :=
  Set.Subset.antisymm (selectedClosedRegionMesh_support_subset J p)
    (selectedClosedRegion_subset_selectedClosedRegionMesh_support J p)

/-- Taking the union of two selected submeshes is literally the selection by the disjunction
of the two predicates.  All three meshes use the same ambient arrangement vertex type. -/
theorem selectedClosedRegionMesh_triangles_union (p q : ι → Prop) :
    (selectedClosedRegionMesh J p).triangles ∪
        (selectedClosedRegionMesh J q).triangles =
      (selectedClosedRegionMesh J fun i ↦ p i ∨ q i).triangles := by
  classical
  change
    ((arrangementMesh J).triangles.filter
        (IsSelectedInteriorArrangementTriangle J p)) ∪
      ((arrangementMesh J).triangles.filter
        (IsSelectedInteriorArrangementTriangle J q)) =
      (arrangementMesh J).triangles.filter
        (IsSelectedInteriorArrangementTriangle J (fun i ↦ p i ∨ q i))
  ext t
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨ht, i, hpi, hi⟩ | ⟨ht, i, hqi, hi⟩)
    · exact ⟨ht, i, Or.inl hpi, hi⟩
    · exact ⟨ht, i, Or.inr hqi, hi⟩
  · rintro ⟨ht, i, hpi | hqi, hi⟩
    · exact Or.inl ⟨ht, i, hpi, hi⟩
    · exact Or.inr ⟨ht, i, hqi, hi⟩

/-- The two synchronized selected submeshes jointly retain the planar surface incidence bound:
every two-vertex edge belongs to at most two triangles.  This is inherited from the single
ambient arrangement, not proved separately for the two selections. -/
theorem selectedClosedRegionMeshes_joint_edge_valence (p q : ι → Prop)
    (e : Finset (arrangementMesh J).Vertex) (he : e.card = 2) :
    (((selectedClosedRegionMesh J p).triangles ∪
        (selectedClosedRegionMesh J q).triangles).filter fun t ↦ e ⊆ t).card ≤ 2 := by
  rw [selectedClosedRegionMesh_triangles_union J p q]
  exact (selectedClosedRegionMesh J fun i ↦ p i ∨ q i).card_incidentTriangles_le_two he

/-! ## Synchronization with an independent finite patch mesh -/

/-- Cut the polygon-family arrangement by all barycentric face lines of a second mesh. -/
noncomputable def synchronizedArrangement (N : TriangleMesh) : TriangleMesh :=
  (arrangementMesh J).refineTo N

/-- A chamber of the synchronized arrangement lies in the selected polygonal region. -/
def IsSelectedSynchronizedTriangle (N : TriangleMesh) (p : ι → Prop)
    (t : Finset (synchronizedArrangement J N).Vertex) : Prop :=
  ∃ i, p i ∧
    interior ((synchronizedArrangement J N).triangleCarrier t) ⊆
      (J i).interiorRegion

/-- The polygonal side of the common old/patch arrangement. -/
noncomputable def selectedSynchronizedMesh (N : TriangleMesh)
    (p : ι → Prop) : TriangleMesh := by
  classical
  exact (synchronizedArrangement J N).restrictTriangles
    (IsSelectedSynchronizedTriangle J N p)

/-- The patch side consists of the synchronized chambers whose interiors meet the patch. -/
def IsTargetSynchronizedTriangle (N : TriangleMesh)
    (t : Finset (synchronizedArrangement J N).Vertex) : Prop :=
  (interior ((synchronizedArrangement J N).triangleCarrier t) ∩
    N.toPlaneComplex.support).Nonempty

/-- The target-mesh side of the common old/patch arrangement. -/
noncomputable def targetSynchronizedMesh (N : TriangleMesh) : TriangleMesh := by
  classical
  exact (synchronizedArrangement J N).restrictTriangles
    (IsTargetSynchronizedTriangle J N)

theorem selectedSynchronizedMesh_triangle_mem (N : TriangleMesh) (p : ι → Prop)
    {t : Finset (selectedSynchronizedMesh J N p).Vertex} :
    t ∈ (selectedSynchronizedMesh J N p).triangles ↔
      t ∈ (synchronizedArrangement J N).triangles ∧
        IsSelectedSynchronizedTriangle J N p t := by
  classical
  exact (synchronizedArrangement J N).mem_restrictTriangles_triangles _

theorem targetSynchronizedMesh_triangle_mem (N : TriangleMesh)
    {t : Finset (targetSynchronizedMesh J N).Vertex} :
    t ∈ (targetSynchronizedMesh J N).triangles ↔
      t ∈ (synchronizedArrangement J N).triangles ∧
        IsTargetSynchronizedTriangle J N t := by
  classical
  exact (synchronizedArrangement J N).mem_restrictTriangles_triangles _

/-- Every synchronized chamber is contained in one chamber of the original polygon-family
arrangement. -/
theorem exists_arrangementTriangle_of_synchronized {N : TriangleMesh}
    {t : Finset (synchronizedArrangement J N).Vertex}
    (ht : t ∈ (synchronizedArrangement J N).triangles) :
    ∃ u ∈ (arrangementMesh J).triangles,
      (synchronizedArrangement J N).triangleCarrier t ⊆
        (arrangementMesh J).triangleCarrier u := by
  let R := synchronizedArrangement J N
  have htFace : t ∈ R.toPlaneComplex.simplexes :=
    R.mem_faces_iff.mpr ⟨by
      have htcard : t.card = 3 := R.card_triangle t ht
      exact Finset.card_pos.mp (by omega), t, ht, subset_rfl⟩
  obtain ⟨s, hs, hts⟩ :=
    ((arrangementMesh J).refineTo_subdivides_left N).2 t htFace
  obtain ⟨-, u, hu, hsu⟩ := (arrangementMesh J).mem_faces_iff.mp hs
  refine ⟨u, hu, ?_⟩
  exact hts.trans (convexHull_mono (Set.image_mono hsu))

/-- Synchronized chambers still lie wholly on one side of every family polygon. -/
theorem synchronizedTriangle_interior_side (N : TriangleMesh) (i : ι)
    {t : Finset (synchronizedArrangement J N).Vertex}
    (ht : t ∈ (synchronizedArrangement J N).triangles) :
    interior ((synchronizedArrangement J N).triangleCarrier t) ⊆
        (J i).interiorRegion ∨
      interior ((synchronizedArrangement J N).triangleCarrier t) ⊆
        (J i).exteriorRegion := by
  obtain ⟨u, hu, htu⟩ := exists_arrangementTriangle_of_synchronized J ht
  have hint := interior_mono htu
  rcases arrangementTriangle_interior_side J i hu with hin | hout
  · exact Or.inl (hint.trans hin)
  · exact Or.inr (hint.trans hout)

/-- Further cutting by the target mesh does not change the selected polygonal support. -/
theorem selectedSynchronizedMesh_support (N : TriangleMesh) (p : ι → Prop) :
    (selectedSynchronizedMesh J N p).toPlaneComplex.support =
      selectedClosedRegion J p := by
  classical
  let R := synchronizedArrangement J N
  let L := selectedSynchronizedMesh J N p
  apply Set.Subset.antisymm
  · rw [TriangleMesh.toPlaneComplex_support]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    obtain ⟨htR, i, hpi, hi⟩ :=
      (selectedSynchronizedMesh_triangle_mem J N p).mp ht
    let T : R.Triangle := ⟨t, htR⟩
    have hxClosure : x ∈ closure (interior (R.triangleCarrier t)) := by
      rw [R.closure_interior_triangleCarrier T]
      exact hxt
    have hxRegion : x ∈ closure (J i).interiorRegion :=
      closure_mono hi hxClosure
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
      ⟨hpi, by simpa only [PolygonalCircle.closedRegion] using hxRegion⟩⟩
  · intro x hx
    obtain ⟨i, hpi, hxi⟩ := Set.mem_iUnion₂.mp hx
    rw [PolygonalCircle.closedRegion] at hxi
    apply closure_minimal _ L.toPlaneComplex.isCompact_support.isClosed hxi
    intro y hy
    have hyFamily : y ∈ closedRegion J := Set.mem_iUnion.mpr
      ⟨i, by rw [(J i).closedRegion_eq_union]; exact Or.inl hy⟩
    have hyArrangement : y ∈ (arrangementMesh J).toPlaneComplex.support :=
      closedRegion_subset_arrangementMesh_support J hyFamily
    have hyR : y ∈ R.toPlaneComplex.support := by
      rw [show R.toPlaneComplex.support =
          (arrangementMesh J).toPlaneComplex.support by
        exact (arrangementMesh J).refineTo_support N]
      exact hyArrangement
    rw [TriangleMesh.toPlaneComplex_support] at hyR
    simp only [Set.mem_iUnion] at hyR
    obtain ⟨t, ht, hyt⟩ := hyR
    let T : R.Triangle := ⟨t, ht⟩
    have hyClosure : y ∈ closure (interior (R.triangleCarrier t)) := by
      rw [R.closure_interior_triangleCarrier T]
      exact hyt
    have hyInterClosure : y ∈ closure
        ((J i).interiorRegion ∩ interior (R.triangleCarrier t)) :=
      (J i).isOpen_interiorRegion.inter_closure ⟨hy, hyClosure⟩
    obtain ⟨z, hzInside, hzT⟩ := Set.Nonempty.of_closure ⟨y, hyInterClosure⟩
    have htInside : interior (R.triangleCarrier t) ⊆
        (J i).interiorRegion := by
      rcases synchronizedTriangle_interior_side J N i ht with hin | hout
      · exact hin
      · exact False.elim <| Set.disjoint_left.mp
          (J i).disjoint_interior_exterior hzInside (hout hzT)
    rw [TriangleMesh.toPlaneComplex_support]
    exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr
      ⟨(selectedSynchronizedMesh_triangle_mem J N p).mpr
        ⟨ht, i, hpi, htInside⟩, hyt⟩⟩

/-- When the target support lies in the family arrangement's enclosing triangle, the target
side of the synchronized arrangement recovers it exactly. -/
theorem targetSynchronizedMesh_support (N : TriangleMesh)
    (hsub : N.toPlaneComplex.support ⊆
      (arrangementMesh J).toPlaneComplex.support) :
    (targetSynchronizedMesh J N).toPlaneComplex.support =
      N.toPlaneComplex.support := by
  change ((arrangementMesh J).refineToSupport N).toPlaneComplex.support =
    N.toPlaneComplex.support
  exact (arrangementMesh J).refineToSupport_support N hsub

/-- The synchronized old and target submeshes jointly satisfy the planar edge-incidence bound. -/
theorem synchronizedMeshes_joint_edge_valence (N : TriangleMesh) (p : ι → Prop)
    (e : Finset (synchronizedArrangement J N).Vertex) (he : e.card = 2) :
    (((selectedSynchronizedMesh J N p).triangles ∪
        (targetSynchronizedMesh J N).triangles).filter fun t ↦ e ⊆ t).card ≤ 2 := by
  apply le_trans (Finset.card_le_card ?_)
    ((synchronizedArrangement J N).card_incidentTriangles_le_two he)
  intro t ht
  replace ht := Finset.mem_filter.mp ht
  apply (synchronizedArrangement J N).mem_incidentTriangles_iff.mpr
  refine ⟨?_, ht.2⟩
  rcases Finset.mem_union.mp ht.1 with htOld | htTarget
  · exact (selectedSynchronizedMesh_triangle_mem J N p).mp htOld |>.1
  · exact (targetSynchronizedMesh_triangle_mem J N).mp htTarget |>.1

omit [Fintype ι] in
/-- A finite union of polygonal closed disks is a finite pure plane polyhedron. -/
theorem closedRegion_is_polyhedron [Finite ι] :
    ∃ K : PlaneComplex, K.support = closedRegion J ∧ K.IsPure2 := by
  letI := Fintype.ofFinite ι
  exact ⟨(closedRegionMesh J).toPlaneComplex, closedRegionMesh_support J,
    (closedRegionMesh J).toPlaneComplex_isPure2⟩

end PolygonalFamily

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification08_block_04
/- END ClassificationOfSurfaces.Moise.PolygonalFamilyPolyhedron -/

/- BEGIN ClassificationOfSurfaces.Moise.FineSubdivision | 1af8733308ee7b794af99023e6a5e1d3c28f31eba9638dff732aa6f63d3df618 -/
section schottkyclassification08_block_05
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Fine subdivisions of finite plane complexes

Moise Chapter 6 repeatedly chooses a subdivision sufficiently fine for a continuous map.  For a
finite plane complex this follows from a concrete finite line arrangement: cover the compact
support by small balls and, around every center, cut by two vertical and two horizontal lines.
Every chamber meeting the corresponding smaller ball is trapped in the resulting rectangle.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace PlaneComplex

variable (K : PlaneComplex)

theorem affine_nonneg_on_cellCarrier {a : Plane →ᵃ[ℝ] ℝ}
    {s : Finset K.Vertex} (hs : ∀ v ∈ s, 0 ≤ a (K.position v)) :
    ∀ x ∈ K.cellCarrier s, 0 ≤ a x := by
  intro x hx
  have hsubset : K.position '' (s : Set K.Vertex) ⊆ {x | 0 ≤ a x} := by
    rintro y ⟨v, hv, rfl⟩
    exact hs v hv
  exact convexHull_min hsubset ((convex_Ici 0).affine_preimage a) hx

theorem affine_nonpos_on_cellCarrier {a : Plane →ᵃ[ℝ] ℝ}
    {s : Finset K.Vertex} (hs : ∀ v ∈ s, a (K.position v) ≤ 0) :
    ∀ x ∈ K.cellCarrier s, a x ≤ 0 := by
  intro x hx
  have hsubset : K.position '' (s : Set K.Vertex) ⊆ {x | a x ≤ 0} := by
    rintro y ⟨v, hv, rfl⟩
    exact hs v hv
  exact convexHull_min hsubset ((convex_Iic 0).affine_preimage a) hx

end PlaneComplex

/-- The vertical line whose zero set is `x = c`. -/
noncomputable def verticalCut (c : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  cartesianX - AffineMap.const ℝ Plane c

/-- The horizontal line whose zero set is `y = c`. -/
noncomputable def horizontalCut (c : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  cartesianY - AffineMap.const ℝ Plane c

@[simp] theorem verticalCut_apply (c : ℝ) (p : Plane) : verticalCut c p = p 0 - c := by
  rfl

@[simp] theorem horizontalCut_apply (c : ℝ) (p : Plane) : horizontalCut c p = p 1 - c := by
  rfl

/-- Four coordinate cuts bounding a square of radius `r` around `p`. -/
noncomputable def boxCuts (p : Plane) (r : ℝ) : List (Plane →ᵃ[ℝ] ℝ) :=
  [verticalCut (p 0 - r), verticalCut (p 0 + r),
    horizontalCut (p 1 - r), horizontalCut (p 1 + r)]

@[simp] theorem mem_boxCuts {p : Plane} {r : ℝ} {a : Plane →ᵃ[ℝ] ℝ} :
    a ∈ boxCuts p r ↔
      a = verticalCut (p 0 - r) ∨ a = verticalCut (p 0 + r) ∨
      a = horizontalCut (p 1 - r) ∨ a = horizontalCut (p 1 + r) := by
  simp [boxCuts]

/-- All box cuts associated to a finite set of centers. -/
noncomputable def coverCuts (centers : Finset Plane) (r : ℝ) :
    List (Plane →ᵃ[ℝ] ℝ) :=
  centers.toList.flatMap fun p => boxCuts p r

theorem boxCut_mem_coverCuts {centers : Finset Plane} {p : Plane} (hp : p ∈ centers)
    (r : ℝ) {a : Plane →ᵃ[ℝ] ℝ} (ha : a ∈ boxCuts p r) :
    a ∈ coverCuts centers r := by
  simp only [coverCuts, List.mem_flatMap]
  exact ⟨p, by simpa using hp, ha⟩

private theorem coordinate_dist_le (x y : Plane) (k : Fin 2) :
    |x k - y k| ≤ dist x y := by
  have h := PiLp.norm_apply_le (x - y) k
  simpa only [PiLp.sub_apply, Real.norm_eq_abs, dist_eq_norm] using h

/-- A chamber cut by the four box lines around `p` is trapped in that box as soon as it meets
the concentric half-radius ball. -/
theorem TriangleMesh.cellCarrier_subset_box_of_monochromatic
    (N : TriangleMesh) {p : Plane} {r : ℝ} (hr : 0 < r)
    (hmono : ∀ a ∈ boxCuts p r, N.IsMonochromatic a)
    {t : Finset N.Vertex} (ht : t ∈ N.triangles) {x : Plane}
    (hx : x ∈ N.toPlaneComplex.cellCarrier t) (hxp : dist x p < r / 2) :
    ∀ y ∈ N.toPlaneComplex.cellCarrier t,
      p 0 - r ≤ y 0 ∧ y 0 ≤ p 0 + r ∧
      p 1 - r ≤ y 1 ∧ y 1 ≤ p 1 + r := by
  have hxcoord (k : Fin 2) : |x k - p k| < r / 2 :=
    (coordinate_dist_le x p k).trans_lt hxp
  have trapLower (a : Plane →ᵃ[ℝ] ℝ) (ha : a ∈ boxCuts p r)
      (hax : 0 < a x) : ∀ y ∈ N.toPlaneComplex.cellCarrier t, 0 ≤ a y := by
    rcases hmono a ha t ht with hnonneg | hnonpos
    · exact N.toPlaneComplex.affine_nonneg_on_cellCarrier hnonneg
    · have := N.toPlaneComplex.affine_nonpos_on_cellCarrier hnonpos x hx
      exact (not_le_of_gt hax this).elim
  have trapUpper (a : Plane →ᵃ[ℝ] ℝ) (ha : a ∈ boxCuts p r)
      (hax : a x < 0) : ∀ y ∈ N.toPlaneComplex.cellCarrier t, a y ≤ 0 := by
    rcases hmono a ha t ht with hnonneg | hnonpos
    · have := N.toPlaneComplex.affine_nonneg_on_cellCarrier hnonneg x hx
      exact (not_le_of_gt hax this).elim
    · exact N.toPlaneComplex.affine_nonpos_on_cellCarrier hnonpos
  have hx0lower : 0 < verticalCut (p 0 - r) x := by
    rw [verticalCut_apply]
    have := hxcoord 0
    rw [abs_lt] at this
    linarith
  have hx0upper : verticalCut (p 0 + r) x < 0 := by
    rw [verticalCut_apply]
    have := hxcoord 0
    rw [abs_lt] at this
    linarith
  have hx1lower : 0 < horizontalCut (p 1 - r) x := by
    rw [horizontalCut_apply]
    have := hxcoord 1
    rw [abs_lt] at this
    linarith
  have hx1upper : horizontalCut (p 1 + r) x < 0 := by
    rw [horizontalCut_apply]
    have := hxcoord 1
    rw [abs_lt] at this
    linarith
  intro y hy
  have h0lower := trapLower (verticalCut (p 0 - r)) (by simp) hx0lower y hy
  have h0upper := trapUpper (verticalCut (p 0 + r)) (by simp) hx0upper y hy
  have h1lower := trapLower (horizontalCut (p 1 - r)) (by simp) hx1lower y hy
  have h1upper := trapUpper (horizontalCut (p 1 + r)) (by simp) hx1upper y hy
  simp only [verticalCut_apply] at h0lower h0upper
  simp only [horizontalCut_apply] at h1lower h1upper
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private theorem dist_lt_four_mul_of_mem_box {p x y : Plane} {r : ℝ} (hr : 0 < r)
    (hx : p 0 - r ≤ x 0 ∧ x 0 ≤ p 0 + r ∧
      p 1 - r ≤ x 1 ∧ x 1 ≤ p 1 + r)
    (hy : p 0 - r ≤ y 0 ∧ y 0 ≤ p 0 + r ∧
      p 1 - r ≤ y 1 ∧ y 1 ≤ p 1 + r) :
    dist x y < 4 * r := by
  have h0 : |x 0 - y 0| ≤ 2 * r := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2.1, hy.1, hy.2.1]
  have h1 : |x 1 - y 1| ≤ 2 * r := by
    rw [abs_le]
    constructor <;> linarith [hx.2.2.1, hx.2.2.2, hy.2.2.1, hy.2.2.2]
  rw [EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_two, Real.dist_eq]
  apply (Real.sqrt_lt' (by positivity : 0 < 4 * r)).2
  have h0sq : |x 0 - y 0| ^ 2 ≤ (2 * r) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 h0
  have h1sq : |x 1 - y 1| ^ 2 ≤ (2 * r) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 h1
  simp only [sq_abs] at h0sq h1sq
  simp only [sq_abs]
  nlinarith [sq_nonneg r]

/-- A finite pure plane complex has a subdivision on whose two-cells a prescribed continuous map
has arbitrarily small oscillation. -/
theorem PlaneComplex.exists_subdivision_image_dist_lt (K : PlaneComplex)
    (hpure : K.IsPure2) {h : Plane → Plane} (hcont : ContinuousOn h K.support)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ L : PlaneComplex, L.IsPure2 ∧ L.Subdivides K ∧
      ∀ t ∈ L.cells, ∀ x ∈ L.cellCarrier t, ∀ y ∈ L.cellCarrier t,
        dist (h x) (h y) < eps := by
  classical
  have huniform : UniformContinuousOn h K.support :=
    K.isCompact_support.uniformContinuousOn_of_continuous hcont
  obtain ⟨delta, hdelta, hcontrol⟩ :=
    (Metric.uniformContinuousOn_iff.mp huniform) eps heps
  let r : ℝ := delta / 8
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨centers, hcentersSub, hcentersFinite, hcover⟩ :=
    K.isCompact_support.finite_cover_balls (show 0 < r / 2 by positivity)
  let centerFinset : Finset Plane := hcentersFinite.toFinset
  let M : TriangleMesh := K.toTriangleMesh
  let lines := coverCuts centerFinset r
  let N : TriangleMesh := M.refineByLines lines
  let L : PlaneComplex := N.toPlaneComplex
  have hMK : M.toPlaneComplex.Subdivides K := by
    constructor
    · exact K.toTriangleMesh_support hpure
    · intro s hs
      obtain ⟨-, t, ht, hst⟩ := M.mem_faces_iff.mp hs
      exact ⟨t, K.mem_simplexes_of_mem_cells ht, convexHull_mono (Set.image_mono hst)⟩
  have hLK : L.Subdivides K :=
    (M.refineByLines_subdivides lines).trans hMK
  refine ⟨L, N.toPlaneComplex_isPure2, hLK, ?_⟩
  intro t ht x hx y hy
  have htSimplex : t ∈ L.simplexes := (Finset.mem_filter.mp ht).1
  have htcard : t.card = 3 := (Finset.mem_filter.mp ht).2
  obtain ⟨-, T, hT, htT⟩ := N.mem_faces_iff.mp htSimplex
  have hteq : t = T := by
    apply Finset.eq_of_subset_of_card_le htT
    have hcardT := N.card_triangle T hT
    exact (hcardT.trans htcard.symm).le
  subst T
  have hxK : x ∈ K.support := hLK.1 ▸ L.cellCarrier_subset_support htSimplex hx
  have hyK : y ∈ K.support := hLK.1 ▸ L.cellCarrier_subset_support htSimplex hy
  have hxCover := hcover hxK
  simp only [Set.mem_iUnion, Metric.mem_ball] at hxCover
  obtain ⟨p, hpCenters, hxp⟩ := hxCover
  have hpFinset : p ∈ centerFinset := by
    simpa only [centerFinset, Set.Finite.mem_toFinset] using hpCenters
  have hmono : ∀ a ∈ boxCuts p r, N.IsMonochromatic a := by
    intro a ha
    exact M.refineByLines_isMonochromatic_of_mem lines
      (boxCut_mem_coverCuts hpFinset r ha)
  have htrap := N.cellCarrier_subset_box_of_monochromatic hr hmono hT hx hxp
  have hxbox := htrap x hx
  have hybox := htrap y hy
  have hxy : dist x y < delta := by
    have hsmall := dist_lt_four_mul_of_mem_box hr hxbox hybox
    dsimp [r] at hsmall
    linarith
  exact hcontrol x hxK y hyK hxy

/-- A sufficiently fine subdivision of a pure finite plane complex is subordinate to any open
cover of its support. -/
theorem PlaneComplex.exists_subdivision_subordinate_openCover
    (K : PlaneComplex) (hpure : K.IsPure2)
    {I : Type*} (U : I → Set Plane) (hU : ∀ i, IsOpen (U i))
    (hcover : K.support ⊆ ⋃ i, U i) :
    ∃ L : PlaneComplex, L.IsPure2 ∧ L.Subdivides K ∧
      ∀ t ∈ L.cells, ∃ i, L.cellCarrier t ⊆ U i := by
  obtain ⟨delta, hdelta, hLebesgue⟩ :=
    lebesgue_number_lemma_of_metric K.isCompact_support hU hcover
  obtain ⟨L, hLpure, hLK, hsmall⟩ :=
    K.exists_subdivision_image_dist_lt hpure continuousOn_id hdelta
  refine ⟨L, hLpure, hLK, ?_⟩
  intro t ht
  have htpos : 0 < t.card := by
    rw [L.card_of_mem_cells ht]
    decide
  obtain ⟨v, hv⟩ := Finset.card_pos.mp htpos
  have hpCarrier : L.position v ∈ L.cellCarrier t := by
    exact subset_convexHull ℝ _ ⟨v, hv, rfl⟩
  have hpSupport : L.position v ∈ K.support := by
    rw [← hLK.1]
    exact L.cellCarrier_subset_support (L.mem_simplexes_of_mem_cells ht) hpCarrier
  obtain ⟨i, hi⟩ := hLebesgue (L.position v) hpSupport
  refine ⟨i, fun x hx => hi ?_⟩
  rw [Metric.mem_ball]
  exact hsmall t ht x hx (L.position v) hpCarrier

/-- A finite triangle submesh selected between a compact set and an ambient open set.  Unlike a
full subdivision, its support is only the retained compact polyhedron; every retained triangle
is nevertheless subordinate to the original plane complex. -/
structure PlaneComplex.OpenSubmesh
    (K : PlaneComplex) (C U : Set Plane) where
  /-- The `mesh` declaration. -/
  mesh : TriangleMesh
  face_subordinate : ∀ t ∈ mesh.triangles,
    ∃ s ∈ K.simplexes, mesh.toPlaneComplex.cellCarrier t ⊆ K.cellCarrier s
  covers : C ⊆ mesh.toPlaneComplex.support
  contained : mesh.toPlaneComplex.support ⊆ U

namespace PlaneComplex.OpenSubmesh

variable {K : PlaneComplex} {C U : Set Plane}

/-- Every retained triangle of an open submesh still lies in the original complex support. -/
theorem support_subset_original (L : K.OpenSubmesh C U) :
    L.mesh.toPlaneComplex.support ⊆ K.support := by
  intro x hx
  rw [L.mesh.toPlaneComplex_support] at hx
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨s, hs, hts⟩ := L.face_subordinate t ht
  exact K.cellCarrier_subset_support hs (hts hxt)

end PlaneComplex.OpenSubmesh

/-- Every compact subset of an open subset of a pure finite plane complex is covered by a finite
triangle submesh lying in that open set. -/
theorem PlaneComplex.exists_openSubmesh
    (K : PlaneComplex) (hpure : K.IsPure2) {C U : Set Plane}
    (hC : IsCompact C) (hCK : C ⊆ K.support)
    (hU : IsOpen U) (hCU : C ⊆ U) :
    Nonempty (K.OpenSubmesh C U) := by
  classical
  let W : Bool → Set Plane := fun b => if b then Cᶜ else U
  have hWopen : ∀ b, IsOpen (W b) := by
    intro b
    cases b <;> simp [W, hU, hC.isClosed]
  have hWcover : K.support ⊆ ⋃ b, W b := by
    intro x hx
    by_cases hxC : x ∈ C
    · exact Set.mem_iUnion.mpr ⟨false, by simpa [W] using hCU hxC⟩
    · exact Set.mem_iUnion.mpr ⟨true, by simpa [W] using hxC⟩
  obtain ⟨L, hLpure, hLK, hsubordinate⟩ :=
    K.exists_subdivision_subordinate_openCover hpure W hWopen hWcover
  let M := L.toTriangleMesh
  let N : TriangleMesh := M.restrictTriangles fun t =>
    L.cellCarrier t ⊆ U
  refine ⟨{
    mesh := N
    face_subordinate := ?_
    covers := ?_
    contained := ?_ }⟩
  · intro t ht
    have htM : t ∈ M.triangles :=
      (M.mem_restrictTriangles_triangles (fun s => L.cellCarrier s ⊆ U)).mp ht |>.1
    have htL : t ∈ L.simplexes := by
      exact L.mem_simplexes_of_mem_cells htM
    obtain ⟨s, hs, hts⟩ := hLK.2 t htL
    exact ⟨s, hs, hts⟩
  · intro z hzC
    have hzK : z ∈ K.support := hCK hzC
    have hzL : z ∈ L.support := by
      rw [hLK.1]
      exact hzK
    rw [PlaneComplex.support] at hzL
    obtain ⟨s, hs, hzs⟩ := Set.mem_iUnion₂.mp hzL
    obtain ⟨t, ht, hst, htcard⟩ := hLpure s hs
    have hzt : z ∈ L.cellCarrier t := by
      exact convexHull_mono (Set.image_mono hst) hzs
    have htCell : t ∈ L.cells := Finset.mem_filter.mpr ⟨ht, htcard⟩
    obtain ⟨b, hb⟩ := hsubordinate t htCell
    have htU : L.cellCarrier t ⊆ U := by
      cases b with
      | false => simpa [W] using hb
      | true =>
          exfalso
          have hzNotC : z ∈ Cᶜ := by simpa [W] using hb hzt
          exact hzNotC hzC
    have htN : t ∈ N.triangles := by
      exact (M.mem_restrictTriangles_triangles
        (fun s => L.cellCarrier s ⊆ U)).mpr ⟨htCell, htU⟩
    rw [N.toPlaneComplex_support]
    exact Set.mem_iUnion₂.mpr ⟨t, htN, hzt⟩
  · intro z hz
    rw [N.toPlaneComplex_support] at hz
    obtain ⟨t, htN, hzt⟩ := Set.mem_iUnion₂.mp hz
    have htU :=
      (M.mem_restrictTriangles_triangles
        (fun s => L.cellCarrier s ⊆ U)).mp htN |>.2
    exact htU hzt

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification08_block_05
/- END ClassificationOfSurfaces.Moise.FineSubdivision -/

/- BEGIN ClassificationOfSurfaces.Moise.FinitePLHomeomorph | f59345232df197d4aef68484023d99af2cabe8bb87bc23f4eeb07e17240c300c -/
section schottkyclassification08_block_06
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Finite PL homeomorphisms on compact plane polyhedra

This is the concrete PL category needed by Moise Chapters 5 and 6.  A witness records a pure
finite source complex on which an ambient homeomorphism is affine facewise.  Common subdivision
and pullback make these witnesses closed under symmetry and composition.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- An ambient homeomorphism is finitely PL on `A`, with an explicit pure source complex. -/
structure FinitePLHomeomorphOn (h : Plane ≃ₜ Plane) (A : Set Plane) where
  /-- The `complex` declaration. -/
  complex : PlaneComplex
  support_eq : complex.support = A
  pure : complex.IsPure2
  affineOn : ∀ s ∈ complex.simplexes, IsAffineOn h (complex.cellCarrier s)

/-- A finite PL homeomorphism between two compact plane polyhedra.

The underlying function need not be meaningful, continuous, or injective away from `A`; all
geometric data is deliberately relative to the source support. -/
structure FinitePLHomeomorphBetween (f : Plane → Plane) (A B : Set Plane) where
  /-- The `complex` declaration. -/
  complex : PlaneComplex
  support_eq : complex.support = A
  pure : complex.IsPure2
  vertex_mem_support : ∀ v : complex.Vertex, complex.position v ∈ complex.support
  affineOn : ∀ s ∈ complex.simplexes, IsAffineOn f (complex.cellCarrier s)
  injOn : Set.InjOn f A
  image_eq : f '' A = B

namespace FinitePLHomeomorphBetween

variable {f g : Plane → Plane} {A B C : Set Plane}

/-- Forget the explicit pure witness. -/
theorem isPLOnSet (F : FinitePLHomeomorphBetween f A B) : IsPLOnSet A f := by
  exact ⟨F.complex, F.support_eq, F.complex, PlaneComplex.Subdivides.refl F.complex,
    F.affineOn⟩

theorem continuousOn (F : FinitePLHomeomorphBetween f A B) : ContinuousOn f A := by
  rw [← F.support_eq]
  exact (show IsPLOn F.complex f from
    ⟨F.complex, PlaneComplex.Subdivides.refl F.complex, F.affineOn⟩).continuousOn

/-- Reindex the certified target along a set equality. -/
def congrTarget (F : FinitePLHomeomorphBetween f A B) {C : Set Plane} (hBC : B = C) :
    FinitePLHomeomorphBetween f A C where
  complex := F.complex
  support_eq := F.support_eq
  pure := F.pure
  vertex_mem_support := F.vertex_mem_support
  affineOn := F.affineOn
  injOn := F.injOn
  image_eq := F.image_eq.trans hBC

/-- The target complex obtained by mapping every source face. -/
noncomputable def targetComplex (F : FinitePLHomeomorphBetween f A B) : PlaneComplex :=
  F.complex.mapComplexOn f F.vertex_mem_support
    (by simpa only [F.support_eq] using F.injOn) F.affineOn

theorem targetComplex_support (F : FinitePLHomeomorphBetween f A B) :
    F.targetComplex.support = B := by
  rw [targetComplex, F.complex.mapComplexOn_support f F.vertex_mem_support
    (by simpa only [F.support_eq] using F.injOn) F.affineOn, F.support_eq, F.image_eq]

theorem targetComplex_pure (F : FinitePLHomeomorphBetween f A B) :
    F.targetComplex.IsPure2 :=
  PlaneComplex.IsPure2.mapComplexOn F.complex F.pure f F.vertex_mem_support
    (by simpa only [F.support_eq] using F.injOn) F.affineOn

theorem targetComplex_vertex_mem_support (F : FinitePLHomeomorphBetween f A B)
    (v : F.targetComplex.Vertex) :
    F.targetComplex.position v ∈ F.targetComplex.support := by
  rw [F.targetComplex_support]
  change f (F.complex.position v) ∈ B
  apply (Set.ext_iff.mp F.image_eq (f (F.complex.position v))).mp
  exact ⟨F.complex.position v,
    (Set.ext_iff.mp F.support_eq (F.complex.position v)).mp
      (F.vertex_mem_support v), rfl⟩

/-- A set-theoretic inverse, used only on the certified target polyhedron. -/
noncomputable def inverseOn (F : FinitePLHomeomorphBetween f A B) : Plane → Plane :=
  by
    classical
    exact fun y => if hy : y ∈ B then
      Classical.choose (show ∃ x ∈ A, f x = y by
        rw [← F.image_eq] at hy
        exact hy)
    else 0

theorem inverseOn_mem (F : FinitePLHomeomorphBetween f A B) {y : Plane} (hy : y ∈ B) :
    F.inverseOn y ∈ A := by
  simp only [inverseOn, dif_pos hy]
  exact (Classical.choose_spec (show ∃ x ∈ A, f x = y by
    rw [← F.image_eq] at hy
    exact hy)).1

theorem apply_inverseOn (F : FinitePLHomeomorphBetween f A B) {y : Plane} (hy : y ∈ B) :
    f (F.inverseOn y) = y := by
  simp only [inverseOn, dif_pos hy]
  exact (Classical.choose_spec (show ∃ x ∈ A, f x = y by
    rw [← F.image_eq] at hy
    exact hy)).2

theorem inverseOn_apply (F : FinitePLHomeomorphBetween f A B) {x : Plane} (hx : x ∈ A) :
    F.inverseOn (f x) = x := by
  have hfx : f x ∈ B := by
    rw [← F.image_eq]
    exact ⟨x, hx, rfl⟩
  apply F.injOn (F.inverseOn_mem hfx) hx
  rw [F.apply_inverseOn hfx]

theorem inverseOn_injOn (F : FinitePLHomeomorphBetween f A B) :
    Set.InjOn F.inverseOn B := by
  intro x hx y hy hxy
  calc
    x = f (F.inverseOn x) := (F.apply_inverseOn hx).symm
    _ = f (F.inverseOn y) := congrArg f hxy
    _ = y := F.apply_inverseOn hy

/-- On a subdivision of the target complex, the certified inverse is affine facewise. -/
theorem inverseOn_affineOn_of_subdivides_targetComplex
    (F : FinitePLHomeomorphBetween f A B) {R : PlaneComplex}
    (hR : R.Subdivides F.targetComplex) :
    ∀ s ∈ R.simplexes, IsAffineOn F.inverseOn (R.cellCarrier s) := by
  intro s hs
  obtain ⟨u, hu, hsu⟩ := hR.2 s hs
  obtain ⟨t, ht, hut, htcard⟩ := F.pure u hu
  have hutCarrier : F.targetComplex.cellCarrier u ⊆
      F.targetComplex.cellCarrier t := convexHull_mono (Set.image_mono hut)
  have hinjSupport : Set.InjOn f F.complex.support := by
    simpa only [F.support_eq] using F.injOn
  have hsTarget : R.cellCarrier s ⊆ f '' F.complex.cellCarrier t := by
    exact hsu.trans (hutCarrier.trans_eq
      (F.complex.mapComplexOn_cellCarrier f F.vertex_mem_support hinjSupport
        F.affineOn ht))
  obtain ⟨a, hfa⟩ := F.affineOn t ht
  have hinterior : (interior (F.complex.cellCarrier t)).Nonempty := by
    rw [PlaneComplex.cellCarrier]
    have hrange : Set.range (fun v : t => F.complex.position v) =
        F.complex.position '' (t : Set F.complex.Vertex) := by
      ext x
      simp
    rw [← hrange]
    apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
    exact ((F.complex.affineIndependent t ht).affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr
      (by simp [htcard, Plane])
  have haInjOn : Set.InjOn a (F.complex.cellCarrier t) := by
    intro x hx y hy hxy
    apply F.injOn
    · rw [← F.support_eq]
      exact F.complex.cellCarrier_subset_support ht hx
    · rw [← F.support_eq]
      exact F.complex.cellCarrier_subset_support ht hy
    · rw [hfa hx, hfa hy]
      exact hxy
  have haInj : Function.Injective a :=
    affineMap_injective_of_injOn_of_interior_nonempty a hinterior haInjOn
  have haLinearInj : Function.Injective a.linear := a.linear_injective_iff.mpr haInj
  have haLinearSurj : Function.Surjective a.linear :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp haLinearInj
  have haBij : Function.Bijective a := a.linear_bijective_iff.mp
    ⟨haLinearInj, haLinearSurj⟩
  let e : Plane ≃ᵃ[ℝ] Plane := AffineEquiv.ofBijective haBij
  refine ⟨e.symm.toAffineMap, fun y hy => ?_⟩
  obtain ⟨x, hxt, rfl⟩ := hsTarget hy
  have hxA : x ∈ A := by
    rw [← F.support_eq]
    exact F.complex.cellCarrier_subset_support ht hxt
  change F.inverseOn (f x) = e.symm (f x)
  rw [F.inverseOn_apply hxA, hfa hxt]
  exact (e.symm_apply_apply x).symm

/-- A common target refinement together with all data needed to pull it back through a finite
PL homeomorphism.  This is the relative-subdivision package used when a prescribed target mesh
introduces new vertices on the boundary of a polygonal face. -/
structure PullbackSubdivision (F : FinitePLHomeomorphBetween f A B)
    (R : PlaneComplex) where
  /-- The `target` declaration. -/
  target : PlaneComplex
  target_support : target.support = B
  target_pure : target.IsPure2
  target_subdivides_certificate : target.Subdivides F.targetComplex
  target_subdivides_given : target.Subdivides R
  target_vertex_mem_support : ∀ v : target.Vertex,
    target.position v ∈ target.support
  inverseAffine : ∀ s ∈ target.simplexes,
    IsAffineOn F.inverseOn (target.cellCarrier s)

/-- Pull a prescribed pure finite target mesh back through a certified finite PL
homeomorphism.  A common refinement is taken first, so no compatibility between the supplied
mesh and the certificate's original target complex is required. -/
noncomputable def pullbackSubdivision
    (F : FinitePLHomeomorphBetween f A B) (R : PlaneComplex)
    (hRpure : R.IsPure2) (hRsupport : R.support = B) :
    PullbackSubdivision F R := by
  let common := PlaneComplex.exists_common_subdivision F.targetComplex_pure hRpure
    (F.targetComplex_support.trans hRsupport.symm)
  let T₀ : PlaneComplex := common.choose.toPlaneComplex
  let T : PlaneComplex := PlaneComplex.active T₀
  have hTcert : T.Subdivides F.targetComplex :=
    PlaneComplex.active_subdivides_left common.choose_spec.1
  have hTgiven : T.Subdivides R :=
    PlaneComplex.active_subdivides_left common.choose_spec.2
  have hTpure : T.IsPure2 :=
    PlaneComplex.IsPure2.active T₀ common.choose.toPlaneComplex_isPure2
  have hTsupport : T.support = B := hTcert.1.trans F.targetComplex_support
  have hTvertex : ∀ v : T.Vertex, T.position v ∈ T.support := by
    intro v
    change T₀.position v.1 ∈ T.support
    rw [T₀.active_support]
    exact v.2
  exact
    { target := T
      target_support := hTsupport
      target_pure := hTpure
      target_subdivides_certificate := hTcert
      target_subdivides_given := hTgiven
      target_vertex_mem_support := hTvertex
      inverseAffine := F.inverseOn_affineOn_of_subdivides_targetComplex hTcert }

namespace PullbackSubdivision

variable {f : Plane → Plane} {A B : Set Plane}
  {F : FinitePLHomeomorphBetween f A B} {R : PlaneComplex}
  (P : PullbackSubdivision F R)

theorem inverseOn_injOn_target : Set.InjOn F.inverseOn P.target.support := by
  rw [P.target_support]
  exact F.inverseOn_injOn

/-- The actual source complex obtained by mapping the common target refinement through the
certified inverse.  It has the same vertex and simplex labels as the target refinement. -/
noncomputable def source : PlaneComplex :=
  P.target.mapComplexOn F.inverseOn P.target_vertex_mem_support
    P.inverseOn_injOn_target P.inverseAffine

@[simp] theorem source_simplexes : P.source.simplexes = P.target.simplexes := rfl

theorem inverseOn_image_target : F.inverseOn '' B = A := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact F.inverseOn_mem hy
  · intro x hx
    refine ⟨f x, ?_, F.inverseOn_apply hx⟩
    rw [← F.image_eq]
    exact ⟨x, hx, rfl⟩

theorem source_support : P.source.support = A := by
  rw [source, P.target.mapComplexOn_support F.inverseOn
    P.target_vertex_mem_support P.inverseOn_injOn_target P.inverseAffine,
    P.target_support, inverseOn_image_target (F := F)]

theorem source_pure : P.source.IsPure2 :=
  PlaneComplex.IsPure2.mapComplexOn P.target P.target_pure F.inverseOn
    P.target_vertex_mem_support P.inverseOn_injOn_target P.inverseAffine

theorem source_cellCarrier (s : Finset P.target.Vertex)
    (hs : s ∈ P.target.simplexes) :
    P.source.cellCarrier s = F.inverseOn '' P.target.cellCarrier s := by
  exact P.target.mapComplexOn_cellCarrier F.inverseOn P.target_vertex_mem_support
    P.inverseOn_injOn_target P.inverseAffine hs

/-- Corresponding source and target faces are carried exactly onto one another by the
original map. -/
theorem image_source_cellCarrier (s : Finset P.target.Vertex)
    (hs : s ∈ P.target.simplexes) :
    f '' P.source.cellCarrier s = P.target.cellCarrier s := by
  rw [P.source_cellCarrier s hs]
  apply Set.Subset.antisymm
  · rintro y ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    have hzB : z ∈ B := by
      rw [← P.target_support]
      exact P.target.cellCarrier_subset_support hs hz
    simpa only [F.apply_inverseOn hzB] using hz
  · intro y hy
    have hyB : y ∈ B := by
      rw [← P.target_support]
      exact P.target.cellCarrier_subset_support hs hy
    exact ⟨F.inverseOn y, ⟨y, hy, rfl⟩, F.apply_inverseOn hyB⟩

end PullbackSubdivision

/-- Postcomposition by an ambient finite PL homeomorphism preserves finite PL cell
homeomorphisms.  A common target subdivision is pulled back through the first map. -/
noncomputable def transAmbient (F : FinitePLHomeomorphBetween f A B)
    {h : Plane ≃ₜ Plane} (G : FinitePLHomeomorphOn h B) :
    FinitePLHomeomorphBetween (h ∘ f) A (h '' B) := by
  let common := PlaneComplex.exists_common_subdivision F.targetComplex_pure G.pure
    (F.targetComplex_support.trans G.support_eq.symm)
  let R₀ : PlaneComplex := common.choose.toPlaneComplex
  let R : PlaneComplex := PlaneComplex.active R₀
  have hRtarget : R.Subdivides F.targetComplex :=
    PlaneComplex.active_subdivides_left common.choose_spec.1
  have hRG : R.Subdivides G.complex :=
    PlaneComplex.active_subdivides_left common.choose_spec.2
  have hRpure : R.IsPure2 :=
    PlaneComplex.IsPure2.active R₀ common.choose.toPlaneComplex_isPure2
  have hRsupport : R.support = B :=
    hRtarget.1.trans F.targetComplex_support
  have hRvertex : ∀ v : R.Vertex, R.position v ∈ R.support := by
    intro v
    change R₀.position v.1 ∈ R.support
    rw [R₀.active_support]
    exact v.2
  have hinverseAffine : ∀ s ∈ R.simplexes,
      IsAffineOn F.inverseOn (R.cellCarrier s) :=
    F.inverseOn_affineOn_of_subdivides_targetComplex hRtarget
  have hinverseInj : Set.InjOn F.inverseOn R.support := by
    rw [hRsupport]
    exact F.inverseOn_injOn
  have hinverseImage : F.inverseOn '' B = A := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact F.inverseOn_mem hy
    · intro x hx
      refine ⟨f x, ?_, F.inverseOn_apply hx⟩
      rw [← F.image_eq]
      exact ⟨x, hx, rfl⟩
  let Finv : FinitePLHomeomorphBetween F.inverseOn B A :=
    { complex := R
      support_eq := hRsupport
      pure := hRpure
      vertex_mem_support := hRvertex
      affineOn := hinverseAffine
      injOn := F.inverseOn_injOn
      image_eq := hinverseImage }
  let S : PlaneComplex := Finv.targetComplex
  have hSsupport : S.support = A := Finv.targetComplex_support
  have hSpure : S.IsPure2 := Finv.targetComplex_pure
  have hfLikeAffine : ∀ s ∈ S.simplexes,
      IsAffineOn Finv.inverseOn (S.cellCarrier s) :=
    Finv.inverseOn_affineOn_of_subdivides_targetComplex
      (PlaneComplex.Subdivides.refl S)
  have hfLike_eq : Set.EqOn Finv.inverseOn f A := by
    intro x hx
    have hfxB : f x ∈ B := by
      rw [← F.image_eq]
      exact ⟨x, hx, rfl⟩
    have hfinvB : Finv.inverseOn x ∈ B := Finv.inverseOn_mem hx
    apply F.inverseOn_injOn hfinvB hfxB
    rw [Finv.apply_inverseOn hx, F.inverseOn_apply hx]
  have hfAffine : ∀ s ∈ S.simplexes, IsAffineOn f (S.cellCarrier s) := by
    intro s hs
    obtain ⟨a, ha⟩ := hfLikeAffine s hs
    refine ⟨a, fun x hx => ?_⟩
    rw [← hfLike_eq (hSsupport ▸ S.cellCarrier_subset_support hs hx)]
    exact ha hx
  have hgAffine : ∀ s ∈ R.simplexes, IsAffineOn h (R.cellCarrier s) := by
    intro s hs
    obtain ⟨u, hu, hsu⟩ := hRG.2 s hs
    exact (G.affineOn u hu).mono hsu
  have hmaps : ∀ s ∈ S.simplexes,
      Set.MapsTo f (S.cellCarrier s) (R.cellCarrier s) := by
    intro s hs x hx
    have hsR : s ∈ R.simplexes := hs
    have hcell : S.cellCarrier s = F.inverseOn '' R.cellCarrier s := by
      exact R.mapComplexOn_cellCarrier F.inverseOn hRvertex hinverseInj
        hinverseAffine hsR
    rw [hcell] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyB : y ∈ B := by
      rw [← hRsupport]
      exact R.cellCarrier_subset_support hsR hy
    rw [F.apply_inverseOn hyB]
    exact hy
  refine {
    complex := S
    support_eq := hSsupport
    pure := hSpure
    vertex_mem_support := ?_
    affineOn := ?_
    injOn := fun x hx y hy hxy => F.injOn hx hy (h.injective hxy)
    image_eq := ?_ }
  · intro v
    exact Finv.targetComplex_vertex_mem_support v
  · intro s hs
    exact (hgAffine s hs).comp (hfAffine s hs) (hmaps s hs)
  · rw [Set.image_comp, F.image_eq]

end FinitePLHomeomorphBetween

namespace FinitePLHomeomorphOn

variable {h g : Plane ≃ₜ Plane} {A : Set Plane}

/-- Reindex a finite PL witness along an equality of its underlying polyhedron. -/
def congrSet (F : FinitePLHomeomorphOn h A) {B : Set Plane} (hAB : A = B) :
    FinitePLHomeomorphOn h B where
  complex := F.complex
  support_eq := F.support_eq.trans hAB
  pure := F.pure
  affineOn := F.affineOn

/-- Reindex a certificate along equality of ambient homeomorphisms. -/
def congrHomeomorph (F : FinitePLHomeomorphOn h A) {g : Plane ≃ₜ Plane} (hg : h = g) :
    FinitePLHomeomorphOn g A := hg ▸ F

/-- Forget the explicit pure witness and retain the ordinary finite PL-on-set predicate. -/
theorem isPLOnSet (F : FinitePLHomeomorphOn h A) : IsPLOnSet A h := by
  exact ⟨F.complex, F.support_eq, F.complex, PlaneComplex.Subdivides.refl F.complex,
    F.affineOn⟩

/-- The geometric target complex obtained by mapping source vertices and faces. -/
noncomputable def targetComplex (F : FinitePLHomeomorphOn h A) : PlaneComplex :=
  F.complex.mapComplex h h.injective F.affineOn

theorem targetComplex_support (F : FinitePLHomeomorphOn h A) :
    F.targetComplex.support = h '' A := by
  rw [targetComplex, F.complex.mapComplex_support h h.injective F.affineOn, F.support_eq]

theorem targetComplex_pure (F : FinitePLHomeomorphOn h A) :
    F.targetComplex.IsPure2 :=
  PlaneComplex.IsPure2.mapComplex F.complex F.pure h h.injective F.affineOn

/-- The inverse homeomorphism is PL on the exact image polyhedron. -/
noncomputable def symm (F : FinitePLHomeomorphOn h A) :
    FinitePLHomeomorphOn h.symm (h '' A) where
  complex := F.targetComplex
  support_eq := F.targetComplex_support
  pure := F.targetComplex_pure
  affineOn := F.complex.inverse_affineOn_of_subdivides_mapComplex F.pure h F.affineOn
    (PlaneComplex.Subdivides.refl F.targetComplex)

/-- Identity is affine on every face of an explicit pure complex. -/
def refl (K : PlaneComplex) (hpure : K.IsPure2) :
    FinitePLHomeomorphOn (Homeomorph.refl Plane) K.support where
  complex := K
  support_eq := rfl
  pure := hpure
  affineOn := by
    intro s hs
    exact ⟨AffineMap.id ℝ Plane, fun _ _ => rfl⟩

/-- Finite PL witnesses compose.  The proof takes a common target subdivision, pulls it back
through the first homeomorphism, and composes the two affine witnesses face by face. -/
noncomputable def trans (F : FinitePLHomeomorphOn h A)
    (G : FinitePLHomeomorphOn g (h '' A)) :
    FinitePLHomeomorphOn (h.trans g) A := by
  let P := F.targetComplex
  have hPG : P.support = G.complex.support :=
    F.targetComplex_support.trans G.support_eq.symm
  let common := PlaneComplex.exists_common_subdivision F.targetComplex_pure G.pure hPG
  let Rmesh := common.choose
  have hRP := common.choose_spec.1
  have hRG := common.choose_spec.2
  let R := Rmesh.toPlaneComplex
  have hRpure : R.IsPure2 := Rmesh.toPlaneComplex_isPure2
  have hinvAffine : ∀ s ∈ R.simplexes, IsAffineOn h.symm (R.cellCarrier s) :=
    F.complex.inverse_affineOn_of_subdivides_mapComplex F.pure h F.affineOn hRP
  let Q : PlaneComplex := R.mapComplex h.symm h.symm.injective hinvAffine
  have hQsupport : Q.support = A := by
    change (R.mapComplex h.symm h.symm.injective hinvAffine).support = A
    rw [R.mapComplex_support h.symm h.symm.injective hinvAffine,
      hRP.1, F.targetComplex_support]
    ext x
    simp
  have hQpure : Q.IsPure2 :=
    PlaneComplex.IsPure2.mapComplex R hRpure h.symm h.symm.injective hinvAffine
  have hhAffine : ∀ s ∈ Q.simplexes, IsAffineOn h (Q.cellCarrier s) := by
    exact R.inverse_affineOn_of_subdivides_mapComplex hRpure h.symm hinvAffine
      (PlaneComplex.Subdivides.refl Q)
  refine {
    complex := Q
    support_eq := hQsupport
    pure := hQpure
    affineOn := ?_ }
  intro s hs
  obtain ⟨u, hu, hsu⟩ := hRG.2 s hs
  have hgAffine : IsAffineOn g (R.cellCarrier s) := (G.affineOn u hu).mono hsu
  have hmaps : Set.MapsTo h (Q.cellCarrier s) (R.cellCarrier s) := by
    intro x hx
    change x ∈ (R.mapComplex h.symm h.symm.injective hinvAffine).cellCarrier s at hx
    rw [R.mapComplex_cellCarrier h.symm h.symm.injective hinvAffine hs] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  exact hgAffine.comp (hhAffine s hs) hmaps

/-- A finite PL homeomorphism supported on a compact patch is finite PL on every finite plane
polyhedron.  The source is cut by all barycentric lines of the patch.  A resulting triangle
which meets the patch interior lies in one patch triangle; on every other triangle continuity
extends the identity from its interior to its closure. -/
noncomputable def extendByIdentity (F : FinitePLHomeomorphOn h A)
    (hfix : Set.EqOn h id Aᶜ) (K : PlaneComplex) (hKpure : K.IsPure2) :
    FinitePLHomeomorphOn h K.support := by
  let source := K.toTriangleMesh
  let target := F.complex.toTriangleMesh
  let R := source.refineTo target
  have htargetSupport : target.toPlaneComplex.support = A := by
    exact (F.complex.toTriangleMesh_support F.pure).trans F.support_eq
  refine {
    complex := R.toPlaneComplex
    support_eq := (source.refineTo_support target).trans (K.toTriangleMesh_support hKpure)
    pure := R.toPlaneComplex_isPure2
    affineOn := ?_ }
  intro s hs
  obtain ⟨-, t, ht, hst⟩ := R.mem_faces_iff.mp hs
  let T : R.Triangle := ⟨t, ht⟩
  by_cases hhit : (interior (R.triangleCarrier T.1) ∩
      target.toPlaneComplex.support).Nonempty
  · obtain ⟨U, hTU⟩ :=
      source.exists_target_triangle_of_refineTo_of_interior_inter_support target T hhit
    have hUcell : U.1 ∈ F.complex.cells := U.2
    have hUsimplex : U.1 ∈ F.complex.simplexes :=
      F.complex.mem_simplexes_of_mem_cells hUcell
    apply (F.affineOn U.1 hUsimplex).mono
    exact (convexHull_mono (Set.image_mono hst)).trans hTU
  · have heqInterior : Set.EqOn h id (interior (R.triangleCarrier T.1)) := by
      intro x hx
      apply hfix
      rw [Set.mem_compl_iff]
      intro hxA
      apply hhit
      exact ⟨x, hx, htargetSupport.symm ▸ hxA⟩
    have heqTriangle : Set.EqOn h id (R.triangleCarrier T.1) := by
      rw [← R.closure_interior_triangleCarrier T]
      exact heqInterior.closure h.continuous continuous_id
    exact ⟨AffineMap.id ℝ Plane,
      heqTriangle.mono (convexHull_mono (Set.image_mono hst))⟩

end FinitePLHomeomorphOn

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification08_block_06
/- END ClassificationOfSurfaces.Moise.FinitePLHomeomorph -/

/- BEGIN ClassificationOfSurfaces.Moise.IntrinsicFaceModel | 3054dffda2bfe032576957c8cd15dc07751112479e8bef021d9448f332b44e8e -/
section schottkyclassification08_block_07
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Standard plane models for intrinsic faces

Every maximal face of an intrinsic complex is a closed barycentric triangle.  This file gives
the explicit coordinate reindexing homeomorphism to the standard plane triangle.  It is the
source-side bridge used to apply the already proved polygonal Schoenflies extension cellwise.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

open scoped BigOperators Topology

theorem standardTrianglePlaneComplex_pure : standardTrianglePlaneComplex.IsPure2 := by
  intro s hs
  refine ⟨Finset.univ, ?_, Finset.subset_univ s, ?_⟩
  · change (Finset.univ : Finset (Fin 3)) ∈
      (Finset.univ.powerset.filter fun t : Finset (Fin 3) => t.Nonempty)
    simp
  · change (Finset.univ : Finset (Fin 3)).card = 3
    decide

theorem standardTriangle_univ_mem_cells :
    (Finset.univ : Finset (Fin 3)) ∈ standardTrianglePlaneComplex.cells := by
  change (Finset.univ : Finset (Fin 3)) ∈
    (Finset.univ.powerset.filter fun t : Finset (Fin 3) => t.Nonempty).filter
      fun t => t.card = 3
  decide

/-- The unique maximal face of the standard triangle mesh. -/
noncomputable def standardTriangleMeshFace :
    standardTrianglePlaneComplex.toTriangleMesh.Triangle :=
  ⟨Finset.univ, standardTriangle_univ_mem_cells⟩

theorem standardTrianglePlaneComplex_support :
    standardTrianglePlaneComplex.support =
      convexHull ℝ (Set.range standardTriangleVertex) := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [PlaneComplex.support] at hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
    rw [PlaneComplex.cellCarrier] at hxs
    apply convexHull_mono _ hxs
    rintro y ⟨i, hi, rfl⟩
    exact ⟨i, rfl⟩
  · intro x hx
    apply standardTrianglePlaneComplex.cellCarrier_subset_support
      (standardTrianglePlaneComplex.mem_simplexes_of_mem_cells
        standardTriangle_univ_mem_cells)
    rw [PlaneComplex.cellCarrier]
    change x ∈ convexHull ℝ
      (standardTriangleVertex '' ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)))
    simpa only [Finset.coe_univ, Set.image_univ] using hx

theorem standardTriangle_cellCarrier_univ :
    standardTrianglePlaneComplex.cellCarrier (Finset.univ : Finset (Fin 3)) =
      standardTrianglePlaneComplex.support := by
  rw [PlaneComplex.cellCarrier, standardTrianglePlaneComplex_position]
  change convexHull ℝ
    (standardTriangleVertex '' ((Finset.univ : Finset (Fin 3)) : Set (Fin 3))) = _
  rw [Finset.coe_univ, Set.image_univ, ← standardTrianglePlaneComplex_support]

theorem standardTrianglePlaneComplex_isTriangle :
    IsTriangle standardTrianglePlaneComplex.support := by
  exact ⟨standardTriangleVertex, standardTriangleVertex_affineIndependent,
    standardTrianglePlaneComplex_support⟩

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex)

@[simp] theorem finEquiv_symm_three (i : ZMod 3) :
    (ZMod.finEquiv 3).symm i = i := rfl

/-- The chosen ordering of one intrinsic face, viewed as an embedding into all vertices. -/
noncomputable def faceVertexEmbedding (t : K.Face) : Fin 3 ↪ K.Vertex where
  toFun i := (K.faceVertexEquiv t i).1
  inj' := fun _ _ hij => (K.faceVertexEquiv t).injective (Subtype.ext hij)

/-- The two standard indices belonging to cyclic side `i`. -/
noncomputable def faceStandardEdge (i : ZMod 3) : Finset (Fin 3) :=
  {(ZMod.finEquiv 3).symm i, (ZMod.finEquiv 3).symm (i + 1)}

theorem faceVertexEmbedding_cyclic (t : K.Face) (i : ZMod 3) :
    K.faceVertexEmbedding t ((ZMod.finEquiv 3).symm i) = K.faceVertex t i := rfl

theorem faceStandardEdge_map (t : K.Face) (i : ZMod 3) :
    (faceStandardEdge i).map (K.faceVertexEmbedding t) = (K.faceEdge t i).1 := by
  simp only [faceStandardEdge, Finset.map_insert, Finset.map_singleton,
    faceVertexEmbedding, K.faceEdge_val]
  rfl

theorem faceStandardEdge_mem_simplexes (i : ZMod 3) :
    faceStandardEdge i ∈ standardTrianglePlaneComplex.simplexes := by
  change faceStandardEdge i ∈
    (Finset.univ.powerset.filter fun t : Finset (Fin 3) => t.Nonempty)
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
  exact ⟨i, Finset.mem_insert_self i {i + 1}⟩

/-- The geometric carrier of a standard cyclic edge is its polygon side. -/
theorem standard_cellCarrier_faceStandardEdge (i : ZMod 3) :
    standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i) =
      standardTriangleCircle.edgeSegment i := by
  change standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i) =
    segment ℝ (standardTriangleVertex ((ZMod.finEquiv 3).symm i))
      (standardTriangleVertex ((ZMod.finEquiv 3).symm (i + 1)))
  rw [PlaneComplex.cellCarrier, ← convexHull_pair]
  congr 1
  ext p
  constructor
  · rintro ⟨j, hj, rfl⟩
    change j ∈ ({(ZMod.finEquiv 3).symm i,
      (ZMod.finEquiv 3).symm (i + 1)} : Finset (Fin 3)) at hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Or.inl rfl
    · have hj' := Finset.mem_singleton.mp hj
      subst j
      exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨(ZMod.finEquiv 3).symm i, Finset.mem_insert_self _ _, rfl⟩
    · exact ⟨(ZMod.finEquiv 3).symm (i + 1),
        Finset.mem_insert_of_mem (Finset.mem_singleton_self _), rfl⟩

/-- The one-skeleton of the standard triangle complex is exactly its polygonal frontier. -/
theorem standardTriangle_oneSkeleton_support :
    standardTrianglePlaneComplex.oneSkeleton.support =
      standardTriangleCircle.carrier := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [PlaneComplex.support] at hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
    have hsData := standardTrianglePlaneComplex.mem_oneSkeleton_simplexes.mp hs
    have hsSide : ∃ i : ZMod 3, s ⊆ faceStandardEdge i := by
      by_cases h0 : (0 : Fin 3) ∈ s
      · by_cases h1 : (1 : Fin 3) ∈ s
        · have h2 : (2 : Fin 3) ∉ s := by
            intro h2
            have hsub : ({0, 1, 2} : Finset (Fin 3)) ⊆ s := by
              intro y hy
              simp only [Finset.mem_insert, Finset.mem_singleton] at hy
              rcases hy with rfl | rfl | rfl
              exacts [h0, h1, h2]
            have hcard := Finset.card_le_card hsub
            have hthree : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
            rw [hthree] at hcard
            exact (by omega : ¬ (3 : ℕ) ≤ 2) (hcard.trans hsData.2)
          refine ⟨0, ?_⟩
          change s ⊆ ({0, 1} : Finset (Fin 3))
          intro j hj
          fin_cases j
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          · exact (h2 hj).elim
        · refine ⟨2, ?_⟩
          change s ⊆ ({2, 0} : Finset (Fin 3))
          intro j hj
          fin_cases j
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          · exact (h1 hj).elim
          · exact Finset.mem_insert_self _ _
      · refine ⟨1, ?_⟩
        change s ⊆ ({1, 2} : Finset (Fin 3))
        intro j hj
        fin_cases j
        · exact (h0 hj).elim
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    obtain ⟨i, hsi⟩ := hsSide
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [← standard_cellCarrier_faceStandardEdge i]
    exact convexHull_mono (Set.image_mono hsi) hxs
  · intro x hx
    change x ∈ ⋃ i : ZMod 3, standardTriangleCircle.edgeSegment i at hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    rw [← standard_cellCarrier_faceStandardEdge i] at hxi
    rw [PlaneComplex.support]
    apply Set.mem_iUnion₂.mpr
    refine ⟨faceStandardEdge i, ?_, hxi⟩
    apply standardTrianglePlaneComplex.mem_oneSkeleton_simplexes.mpr
    refine ⟨faceStandardEdge_mem_simplexes i, ?_⟩
    rw [faceStandardEdge]
    calc
      ({(ZMod.finEquiv 3).symm i,
          (ZMod.finEquiv 3).symm (i + 1)} : Finset (Fin 3)).card ≤
          ({(ZMod.finEquiv 3).symm (i + 1)} : Finset (Fin 3)).card + 1 :=
        Finset.card_insert_le _ _
      _ = 2 := by rw [Finset.card_singleton]

/-- One closed maximal face, as a subtype of the intrinsic realization. -/
abbrev ClosedFace (t : K.Face) := {x : K.realization // x ∈ K.faceCarrier t.1}

/-- Reindex the barycentric coordinates of an intrinsic face by its chosen `Fin 3` ordering. -/
noncomputable def faceReindexToStandard (t : K.Face) (x : K.ClosedFace t) :
    standardTrianglePlaneComplex.toIntrinsic.realization := by
  let z : Fin 3 → ℝ := fun i => x.1.1 (K.faceVertexEquiv t i).1
  refine ⟨z, ⟨?_, ?_⟩, ⟨Finset.univ, standardTriangle_univ_mem_cells, ?_⟩⟩
  · intro i
    exact x.1.2.1.1 _
  · calc
      ∑ i, z i = ∑ v : t.1, x.1.1 v.1 :=
        (K.faceVertexEquiv t).sum_comp (fun v : t.1 => x.1.1 v.1)
      _ = ∑ v ∈ t.1, x.1.1 v := by rw [Finset.sum_coe_sort]
      _ = ∑ v, x.1.1 v :=
        Finset.sum_subset (Finset.subset_univ t.1) fun v _ hv => x.2 v hv
      _ = 1 := x.1.2.1.2
  · intro i hi
    exact (hi (Finset.mem_univ i)).elim

/-- Extend standard barycentric coordinates by zero away from the chosen intrinsic face. -/
noncomputable def faceReindexFromStandard (t : K.Face)
    (z : standardTrianglePlaneComplex.toIntrinsic.realization) : K.ClosedFace t := by
  let x : K.Vertex → ℝ := fun v =>
    if hv : v ∈ t.1 then z.1 ((K.faceVertexEquiv t).symm ⟨v, hv⟩) else 0
  refine ⟨⟨x, ⟨?_, ?_⟩, ⟨t.1, t.2, ?_⟩⟩, ?_⟩
  · intro v
    dsimp [x]
    split_ifs with hv
    · exact z.2.1.1 _
    · exact le_rfl
  · calc
      ∑ v, x v = ∑ v ∈ t.1, x v :=
        (Finset.sum_subset (Finset.subset_univ t.1) fun v _ hv => by
          simp [x, hv]).symm
      _ = ∑ v : t.1, z.1 ((K.faceVertexEquiv t).symm v) := by
        rw [← Finset.sum_coe_sort]
        apply Finset.sum_congr rfl
        intro v hv
        simp [x, v.2]
      _ = ∑ i : Fin 3, z.1 i :=
        (K.faceVertexEquiv t).symm.sum_comp (fun i : Fin 3 => z.1 i)
      _ = 1 := z.2.1.2
  · intro v hv
    simp [x, hv]
  · intro v hv
    simp [x, hv]

@[simp] theorem faceReindexFromStandard_toStandard (t : K.Face) (x : K.ClosedFace t) :
    K.faceReindexFromStandard t (K.faceReindexToStandard t x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  funext v
  by_cases hv : v ∈ t.1
  · simp [faceReindexFromStandard, faceReindexToStandard, hv]
  · simp [faceReindexFromStandard, hv, x.2 v hv]

@[simp] theorem faceReindexToStandard_fromStandard (t : K.Face)
    (z : standardTrianglePlaneComplex.toIntrinsic.realization) :
    K.faceReindexToStandard t (K.faceReindexFromStandard t z) = z := by
  apply Subtype.ext
  funext i
  simp [faceReindexToStandard, faceReindexFromStandard]

theorem continuous_faceReindexToStandard (t : K.Face) :
    Continuous (K.faceReindexToStandard t) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact ((continuous_apply (K.faceVertexEquiv t i).1).comp continuous_subtype_val).comp
    continuous_subtype_val

/-- The canonical barycentric homeomorphism from one intrinsic face to the standard intrinsic
triangle. -/
noncomputable def faceReindexHomeomorph (t : K.Face) :
    K.ClosedFace t ≃ₜ standardTrianglePlaneComplex.toIntrinsic.realization := by
  let e : K.ClosedFace t ≃ standardTrianglePlaneComplex.toIntrinsic.realization := {
    toFun := K.faceReindexToStandard t
    invFun := K.faceReindexFromStandard t
    left_inv := K.faceReindexFromStandard_toStandard t
    right_inv := K.faceReindexToStandard_fromStandard t }
  letI : CompactSpace (K.ClosedFace t) :=
    isCompact_iff_compactSpace.mp (K.faceCarrier_closed t.1).isCompact
  exact Continuous.homeoOfEquivCompactToT2 (f := e)
    (K.continuous_faceReindexToStandard t)

/-- Reindexing carries any selected standard subface exactly to the corresponding intrinsic
vertex set. -/
theorem faceReindexToStandard_mem_faceCarrier (t : K.Face) (s : Finset (Fin 3))
    (x : K.ClosedFace t) :
    K.faceReindexToStandard t x ∈ standardTrianglePlaneComplex.toIntrinsic.faceCarrier s ↔
      x.1 ∈ K.faceCarrier (s.map (K.faceVertexEmbedding t)) := by
  constructor
  · intro hz v hv
    by_cases hvt : v ∈ t.1
    · let j : Fin 3 := (K.faceVertexEquiv t).symm ⟨v, hvt⟩
      have hj : j ∉ s := by
        intro hjs
        apply hv
        apply Finset.mem_map.mpr
        refine ⟨j, hjs, ?_⟩
        exact congrArg Subtype.val ((K.faceVertexEquiv t).apply_symm_apply ⟨v, hvt⟩)
      have := hz j hj
      change x.1.1 (K.faceVertexEmbedding t j) = 0 at this
      have hjv : K.faceVertexEmbedding t j = v :=
        congrArg Subtype.val ((K.faceVertexEquiv t).apply_symm_apply ⟨v, hvt⟩)
      rw [hjv] at this
      exact this
    · exact x.2 v hvt
  · intro hx j hj
    change x.1.1 (K.faceVertexEmbedding t j) = 0
    apply hx
    intro hmem
    obtain ⟨k, hks, hkj⟩ := Finset.mem_map.mp hmem
    have hkj' : k = j := (K.faceVertexEmbedding t).injective hkj
    exact hj (hkj' ▸ hks)

/-- The standard plane realization of one intrinsic closed face. -/
noncomputable def facePlaneHomeomorph (t : K.Face) :
    K.ClosedFace t ≃ₜ standardTrianglePlaneComplex.support :=
  (K.faceReindexHomeomorph t).trans
    (standardTrianglePlaneComplex.realizationHomeomorph
      standardTrianglePlaneComplex_pure)

/-- Restrict ambient intrinsic barycentric coordinates to the ordered vertices of one face. -/
noncomputable def faceCoordRestrictionAffine (t : K.Face) :
    (K.Vertex → ℝ) →ᵃ[ℝ] (Fin 3 → ℝ) :=
  AffineMap.pi fun j =>
    (LinearMap.proj (K.faceVertexEmbedding t j)).toAffineMap

@[simp] theorem faceCoordRestrictionAffine_apply (t : K.Face)
    (x : K.Vertex → ℝ) (j : Fin 3) :
    K.faceCoordRestrictionAffine t x j =
      x (K.faceVertexEmbedding t j) := by
  rfl

/-- The forward standard-plane chart is affine in the ambient intrinsic barycentric
coordinates. -/
noncomputable def facePlaneForwardAffine (t : K.Face) :
    (K.Vertex → ℝ) →ᵃ[ℝ] Plane :=
  standardTrianglePlaneComplex.baryEvalAffine.comp
    (K.faceCoordRestrictionAffine t)

theorem facePlaneHomeomorph_val_eq_forwardAffine (t : K.Face)
    (x : K.ClosedFace t) :
    (K.facePlaneHomeomorph t x).1 =
      K.facePlaneForwardAffine t x.1.1 := by
  change standardTrianglePlaneComplex.baryEval
      (K.faceReindexToStandard t x).1 =
    standardTrianglePlaneComplex.baryEval
      (K.faceCoordRestrictionAffine t x.1.1)
  apply congrArg standardTrianglePlaneComplex.baryEval
  funext j
  rfl

/-- Affinely extend standard face coordinates by zero away from the selected intrinsic face. -/
noncomputable def faceCoordExtensionAffine (t : K.Face) :
    (Fin 3 → ℝ) →ᵃ[ℝ] (K.Vertex → ℝ) :=
  AffineMap.pi fun v =>
    if hv : v ∈ t.1 then
      (LinearMap.proj ((K.faceVertexEquiv t).symm ⟨v, hv⟩)).toAffineMap
    else
      AffineMap.const ℝ (Fin 3 → ℝ) 0

@[simp] theorem faceCoordExtensionAffine_apply_of_mem (t : K.Face)
    (z : Fin 3 → ℝ) {v : K.Vertex} (hv : v ∈ t.1) :
    K.faceCoordExtensionAffine t z v =
      z ((K.faceVertexEquiv t).symm ⟨v, hv⟩) := by
  simp [faceCoordExtensionAffine, hv]

@[simp] theorem faceCoordExtensionAffine_apply_of_notMem (t : K.Face)
    (z : Fin 3 → ℝ) {v : K.Vertex} (hv : v ∉ t.1) :
    K.faceCoordExtensionAffine t z v = 0 := by
  simp [faceCoordExtensionAffine, hv]

/-- The barycentric-coordinate formula for the inverse standard plane chart of one intrinsic
face. -/
noncomputable def facePlaneInverseAffine (t : K.Face) :
    Plane →ᵃ[ℝ] (K.Vertex → ℝ) :=
  (K.faceCoordExtensionAffine t).comp
    (standardTrianglePlaneComplex.faceCoords standardTriangleMeshFace)

/-- The inverse-chart affine formula takes each standard corner to the corresponding intrinsic
unit barycentric coordinate. -/
theorem facePlaneInverseAffine_standardVertex (t : K.Face) (j : Fin 3) :
    K.facePlaneInverseAffine t (standardTriangleVertex j) =
      Pi.single (K.faceVertexEmbedding t j) 1 := by
  have hc := standardTrianglePlaneComplex.faceCoords_position
    standardTriangleMeshFace (v := j) (by
      change j ∈ (Finset.univ : Finset (Fin 3))
      simp)
  rw [standardTrianglePlaneComplex_position] at hc
  funext v
  by_cases hv : v ∈ t.1
  · rw [facePlaneInverseAffine, AffineMap.comp_apply,
      K.faceCoordExtensionAffine_apply_of_mem _ _ hv, hc]
    by_cases hvj : v = K.faceVertexEmbedding t j
    · have hkj : (K.faceVertexEquiv t).symm ⟨v, hv⟩ = j := by
        apply (K.faceVertexEquiv t).injective
        rw [(K.faceVertexEquiv t).apply_symm_apply]
        apply Subtype.ext
        exact hvj
      rw [hkj, hvj]
      simp
    · have hkj : (K.faceVertexEquiv t).symm ⟨v, hv⟩ ≠ j := by
        intro h
        apply hvj
        change v = (K.faceVertexEquiv t j).1
        exact congrArg Subtype.val ((K.faceVertexEquiv t).symm_apply_eq.mp h)
      simp [hkj, hvj]
  · rw [facePlaneInverseAffine, AffineMap.comp_apply,
      K.faceCoordExtensionAffine_apply_of_notMem _ _ hv]
    have hvj : v ≠ K.faceVertexEmbedding t j := by
      intro hvj
      apply hv
      rw [hvj]
      exact (K.faceVertexEquiv t j).2
    simp [hvj]

/-- The first endpoint of a cyclic face edge belongs to the containing face. -/
theorem edgeFirst_faceEdge_mem_face (t : K.Face) (i : ZMod 3) :
    K.edgeFirst (K.faceEdge t i) ∈ t.1 := by
  have h := K.edgeFirst_mem (K.faceEdge t i)
  rw [K.faceEdge_val] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · simpa only [h] using K.faceVertex_mem t i
  · simpa only [h] using K.faceVertex_mem t (i + 1)

/-- The second endpoint of a cyclic face edge belongs to the containing face. -/
theorem edgeSecond_faceEdge_mem_face (t : K.Face) (i : ZMod 3) :
    K.edgeSecond (K.faceEdge t i) ∈ t.1 := by
  have h := K.edgeSecond_mem (K.faceEdge t i)
  rw [K.faceEdge_val] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · simpa only [h] using K.faceVertex_mem t i
  · simpa only [h] using K.faceVertex_mem t (i + 1)

/-- The standard corner corresponding to the globally chosen first endpoint of a face edge. -/
noncomputable def faceEdgeFirstIndex (t : K.Face) (i : ZMod 3) : Fin 3 :=
  (K.faceVertexEquiv t).symm
    ⟨K.edgeFirst (K.faceEdge t i), K.edgeFirst_faceEdge_mem_face t i⟩

/-- The standard corner corresponding to the globally chosen second endpoint of a face edge. -/
noncomputable def faceEdgeSecondIndex (t : K.Face) (i : ZMod 3) : Fin 3 :=
  (K.faceVertexEquiv t).symm
    ⟨K.edgeSecond (K.faceEdge t i), K.edgeSecond_faceEdge_mem_face t i⟩

@[simp] theorem faceVertexEmbedding_faceEdgeFirstIndex (t : K.Face) (i : ZMod 3) :
    K.faceVertexEmbedding t (K.faceEdgeFirstIndex t i) =
      K.edgeFirst (K.faceEdge t i) := by
  change ((K.faceVertexEquiv t) ((K.faceVertexEquiv t).symm _)).1 = _
  rw [(K.faceVertexEquiv t).apply_symm_apply]

@[simp] theorem faceVertexEmbedding_faceEdgeSecondIndex (t : K.Face) (i : ZMod 3) :
    K.faceVertexEmbedding t (K.faceEdgeSecondIndex t i) =
      K.edgeSecond (K.faceEdge t i) := by
  change ((K.faceVertexEquiv t) ((K.faceVertexEquiv t).symm _)).1 = _
  rw [(K.faceVertexEquiv t).apply_symm_apply]

/-- The two standard endpoint indices are exactly the cyclic standard side, with the order
chosen globally by the intrinsic edge. -/
theorem faceStandardEdge_eq_endpointIndices (t : K.Face) (i : ZMod 3) :
    faceStandardEdge i =
      {K.faceEdgeFirstIndex t i, K.faceEdgeSecondIndex t i} := by
  apply Finset.map_injective (K.faceVertexEmbedding t)
  rw [K.faceStandardEdge_map t i, Finset.map_insert, Finset.map_singleton,
    K.faceVertexEmbedding_faceEdgeFirstIndex,
    K.faceVertexEmbedding_faceEdgeSecondIndex, K.edge_eq_pair]

/-- The standard source point on a face side, oriented by the global intrinsic edge ordering. -/
noncomputable def faceEdgeSourcePoint (t : K.Face) (i : ZMod 3) (r : ℝ) : Plane :=
  AffineMap.lineMap
    (standardTriangleVertex (K.faceEdgeFirstIndex t i))
    (standardTriangleVertex (K.faceEdgeSecondIndex t i)) r

/-- The inverse face chart carries the oriented standard side parameter to the corresponding
intrinsic barycentric line parameter. -/
theorem facePlaneInverseAffine_faceEdgeSourcePoint (t : K.Face) (i : ZMod 3) (r : ℝ) :
    K.facePlaneInverseAffine t (K.faceEdgeSourcePoint t i r) =
      (AffineMap.lineMap (k := ℝ)
        (Pi.single (K.edgeFirst (K.faceEdge t i)) (1 : ℝ) : K.Vertex → ℝ)
        (Pi.single (K.edgeSecond (K.faceEdge t i)) (1 : ℝ) : K.Vertex → ℝ)) r := by
  rw [faceEdgeSourcePoint, AffineMap.apply_lineMap,
    K.facePlaneInverseAffine_standardVertex,
    K.facePlaneInverseAffine_standardVertex,
    K.faceVertexEmbedding_faceEdgeFirstIndex,
    K.faceVertexEmbedding_faceEdgeSecondIndex]

/-- On the oriented standard side, the second intrinsic barycentric coordinate is its affine
parameter. -/
theorem facePlaneInverseAffine_faceEdgeSourcePoint_apply_second
    (t : K.Face) (i : ZMod 3) (r : ℝ) :
    K.facePlaneInverseAffine t (K.faceEdgeSourcePoint t i r)
        (K.edgeSecond (K.faceEdge t i)) = r := by
  rw [K.facePlaneInverseAffine_faceEdgeSourcePoint]
  simp [AffineMap.lineMap_apply_module,
    K.edgeFirst_ne_edgeSecond (K.faceEdge t i)]

/-- Every unit-interval source point lies on the corresponding standard side. -/
theorem faceEdgeSourcePoint_mem_standardEdge (t : K.Face) (i : ZMod 3)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    K.faceEdgeSourcePoint t i r ∈
      standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i) := by
  rw [K.faceStandardEdge_eq_endpointIndices t i, PlaneComplex.cellCarrier]
  change AffineMap.lineMap
      (standardTriangleVertex (K.faceEdgeFirstIndex t i))
      (standardTriangleVertex (K.faceEdgeSecondIndex t i)) r ∈
    convexHull ℝ
      (standardTriangleVertex ''
        (({K.faceEdgeFirstIndex t i, K.faceEdgeSecondIndex t i} : Finset (Fin 3)) :
          Set (Fin 3)))
  rw [show standardTriangleVertex ''
      (({K.faceEdgeFirstIndex t i, K.faceEdgeSecondIndex t i} : Finset (Fin 3)) :
        Set (Fin 3)) =
      {standardTriangleVertex (K.faceEdgeFirstIndex t i),
        standardTriangleVertex (K.faceEdgeSecondIndex t i)} by
    ext p
    simp [eq_comm]]
  rw [convexHull_pair, segment_eq_image_lineMap]
  exact ⟨r, hr, rfl⟩

/-- The oriented unit interval covers exactly the corresponding standard side. -/
theorem faceEdgeSourcePoint_image_Icc (t : K.Face) (i : ZMod 3) :
    K.faceEdgeSourcePoint t i '' Set.Icc (0 : ℝ) 1 =
      standardTrianglePlaneComplex.cellCarrier (faceStandardEdge i) := by
  rw [K.faceStandardEdge_eq_endpointIndices t i, PlaneComplex.cellCarrier]
  have himage : standardTriangleVertex ''
      (({K.faceEdgeFirstIndex t i, K.faceEdgeSecondIndex t i} : Finset (Fin 3)) :
        Set (Fin 3)) =
      {standardTriangleVertex (K.faceEdgeFirstIndex t i),
        standardTriangleVertex (K.faceEdgeSecondIndex t i)} := by
    ext p
    simp [eq_comm]
  rw [himage, convexHull_pair, segment_eq_image_lineMap]
  rfl

/-- The inverse face chart is the restriction of `facePlaneInverseAffine` to the closed
standard triangle. -/
theorem facePlaneHomeomorph_symm_val (t : K.Face)
    (p : standardTrianglePlaneComplex.support) :
    ((K.facePlaneHomeomorph t).symm p).1.1 = K.facePlaneInverseAffine t p.1 := by
  let z := (standardTrianglePlaneComplex.realizationHomeomorph
    standardTrianglePlaneComplex_pure).symm p
  have hz : z.1 = standardTrianglePlaneComplex.faceCoords
      standardTriangleMeshFace p.1 := by
    apply standardTrianglePlaneComplex.realizationHomeomorph_symm_val_eq_faceCoords
      standardTrianglePlaneComplex_pure standardTriangleMeshFace p
    change p.1 ∈ standardTrianglePlaneComplex.cellCarrier
      (Finset.univ : Finset (Fin 3))
    rw [standardTriangle_cellCarrier_univ]
    exact p.2
  change (K.faceReindexFromStandard t z).1.1 = K.facePlaneInverseAffine t p.1
  funext v
  by_cases hv : v ∈ t.1
  · simp only [faceReindexFromStandard, dif_pos hv,
      facePlaneInverseAffine, AffineMap.comp_apply,
      K.faceCoordExtensionAffine_apply_of_mem _ _ hv]
    exact congrFun hz ((K.faceVertexEquiv t).symm ⟨v, hv⟩)
  · simp [faceReindexFromStandard, facePlaneInverseAffine, hv]

/-- The standard plane chart sends cyclic intrinsic edge `i` exactly onto cyclic side `i` of
the standard triangle. -/
theorem facePlaneHomeomorph_image_edge (t : K.Face) (i : ZMod 3) :
    (fun x : K.ClosedFace t => (K.facePlaneHomeomorph t x).1) ''
        {x : K.ClosedFace t | x.1 ∈ K.faceCarrier (K.faceEdge t i).1} =
      standardTriangleCircle.edgeSegment i := by
  let s := faceStandardEdge i
  have hs : s ∈ standardTrianglePlaneComplex.simplexes :=
    faceStandardEdge_mem_simplexes i
  have hgeom := standardTrianglePlaneComplex.realizationHomeomorph_image_faceCarrier
    standardTrianglePlaneComplex_pure hs
  rw [standard_cellCarrier_faceStandardEdge i] at hgeom
  apply Set.Subset.antisymm
  · rintro p ⟨x, hx, rfl⟩
    let z := K.faceReindexToStandard t x
    have hz : z ∈ standardTrianglePlaneComplex.toIntrinsic.faceCarrier s := by
      rw [K.faceReindexToStandard_mem_faceCarrier t s x,
        K.faceStandardEdge_map t i]
      exact hx
    rw [← hgeom]
    refine ⟨z, hz, ?_⟩
    rfl
  · intro p hp
    rw [← hgeom] at hp
    obtain ⟨z, hz, hzp⟩ := hp
    let x : K.ClosedFace t := (K.faceReindexHomeomorph t).symm z
    have hxEdge : x.1 ∈ K.faceCarrier (K.faceEdge t i).1 := by
      rw [← K.faceStandardEdge_map t i,
        ← K.faceReindexToStandard_mem_faceCarrier t s x]
      have heq : K.faceReindexToStandard t x = z := by
        change K.faceReindexHomeomorph t x = z
        exact (K.faceReindexHomeomorph t).apply_symm_apply z
      rw [heq]
      exact hz
    refine ⟨x, hxEdge, ?_⟩
    change (standardTrianglePlaneComplex.realizationHomeomorph
      standardTrianglePlaneComplex_pure (K.faceReindexHomeomorph t x)).1 = p
    simpa [x] using hzp

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification08_block_07
/- END ClassificationOfSurfaces.Moise.IntrinsicFaceModel -/

/- BEGIN ClassificationOfSurfaces.Moise.NoRetraction | ae8dc8e70bb6bacc3127e708d0e533ba9c6a59368ad5dbe9448772862ac2fbf0 -/
section schottkyclassification08_block_08
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# The disk has no retraction onto its boundary

This is Moise, Chapter 4, Problem 2 (proved as Theorem 10.10 later in the book).  We use the
covering map `Circle.exp : ℝ → S¹`: a map from the contractible closed disk to the circle
lifts to `ℝ`, whereas its restriction to the boundary cannot be the identity because the
standard boundary loop has lifts whose endpoints differ by `2π`.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

open scoped Pointwise unitInterval

/-- The complex closed unit disk, used only as the standard model for the no-retraction
argument. -/
abbrev ClosedUnitDisk := Metric.closedBall (0 : ℂ) 1

/-- The boundary circle included in the closed unit disk. -/
def circleToClosedUnitDisk (z : Circle) : ClosedUnitDisk :=
  ⟨z, by
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [Circle.norm_coe]⟩

@[simp] theorem circleToClosedUnitDisk_coe (z : Circle) :
    (circleToClosedUnitDisk z : ℂ) = z :=
  rfl

theorem continuous_circleToClosedUnitDisk : Continuous circleToClosedUnitDisk := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

/-- The closed disk does not retract continuously onto its boundary circle. -/
theorem no_retraction_closedUnitDisk :
    ¬ ∃ r : ClosedUnitDisk → Circle,
      Continuous r ∧ ∀ z : Circle, r (circleToClosedUnitDisk z) = z := by
  rintro ⟨r, hr, hretract⟩
  letI : ContractibleSpace ClosedUnitDisk :=
    (convex_closedBall (0 : ℂ) 1).contractibleSpace ⟨0, by simp⟩
  letI : LocallyPathConnectedSpace ClosedUnitDisk :=
    (convex_closedBall (0 : ℂ) 1).locallyPathConnectedSpace
  let f : C(ClosedUnitDisk, Circle) := ⟨r, hr⟩
  let center : ClosedUnitDisk := ⟨0, by simp⟩
  obtain ⟨e₀, he₀⟩ := Circle.exp_surjective (f center)
  obtain ⟨F, hF, -⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f center e₀ he₀
  have hFlifts : Circle.exp ∘ F = f := hF.2
  let γ : C(I, Circle) :=
    ⟨fun t => Circle.exp (2 * Real.pi * (t : ℝ)), by fun_prop⟩
  let Γ : C(I, ℝ) :=
    ⟨fun t => F (circleToClosedUnitDisk (γ t)),
      F.continuous.comp (continuous_circleToClosedUnitDisk.comp γ.continuous)⟩
  let Λ : C(I, ℝ) :=
    ⟨fun t => Γ 0 + 2 * Real.pi * (t : ℝ), by fun_prop⟩
  have hΓlift : Circle.exp ∘ Γ = γ := by
    funext t
    change Circle.exp (F (circleToClosedUnitDisk (γ t))) = γ t
    rw [show Circle.exp (F (circleToClosedUnitDisk (γ t))) =
      f (circleToClosedUnitDisk (γ t)) by exact congrFun hFlifts _]
    exact hretract (γ t)
  have hΛlift : Circle.exp ∘ Λ = γ := by
    funext t
    change Circle.exp (Γ 0 + 2 * Real.pi * (t : ℝ)) =
      Circle.exp (2 * Real.pi * (t : ℝ))
    rw [Circle.exp_add]
    have hΓ0 : Circle.exp (Γ 0) = 1 := by
      have h := congrFun hΓlift 0
      simpa [γ] using h
    rw [hΓ0, one_mul]
  have hΓ0 : Γ 0 = Λ 0 := by simp [Λ]
  have hΓeq : Γ = Circle.isCoveringMap_exp.liftPath γ (Γ 0) (by
      simpa using (congrFun hΓlift 0).symm) :=
    (Circle.isCoveringMap_exp.eq_liftPath_iff' (by
      simpa using (congrFun hΓlift 0).symm)).mpr ⟨hΓlift, rfl⟩
  have hΛeq : Λ = Circle.isCoveringMap_exp.liftPath γ (Γ 0) (by
      simpa using (congrFun hΓlift 0).symm) :=
    (Circle.isCoveringMap_exp.eq_liftPath_iff' (by
      simpa using (congrFun hΓlift 0).symm)).mpr ⟨hΛlift, hΓ0.symm⟩
  have hend : Γ 1 = Λ 1 := by rw [hΓeq, hΛeq]
  have hloop : Γ 1 = Γ 0 := by
    change F (circleToClosedUnitDisk (γ 1)) = F (circleToClosedUnitDisk (γ 0))
    congr 2
    apply Subtype.ext
    simp [γ]
  rw [hloop] at hend
  have hend' : Γ 0 = Γ 0 + 2 * Real.pi := by simp [Λ] at hend
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  apply hpi
  linarith

/-- The Euclidean plane and the complex plane are linearly isometric, using the orthonormal
basis `(1, I)` of `ℂ` over `ℝ`. -/
noncomputable abbrev planeComplexIsometry : Plane ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

/-- A complex unit direction, transported to the Euclidean plane, lies in the plane unit ball. -/
noncomputable def circleToPlaneClosedUnitBall (z : Circle) : Metric.closedBall (0 : Plane) 1 :=
  ⟨planeComplexIsometry.symm z, by
    rw [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map, Circle.norm_coe]⟩

/-- A point on the Euclidean unit sphere, transported to `ℂ`, is a point of `Circle`. -/
noncomputable def planeUnitSphereToCircle (x : Metric.sphere (0 : Plane) 1) : Circle :=
  ⟨planeComplexIsometry x, by
    exact show planeComplexIsometry (x : Plane) ∈ Metric.sphere (0 : ℂ) 1 from
      mem_sphere_zero_iff_norm.mpr (by
        rw [LinearIsometryEquiv.norm_map]
        exact mem_sphere_zero_iff_norm.mp x.2)⟩

@[simp] theorem planeUnitSphereToCircle_circleToPlaneClosedUnitBall (z : Circle) :
    planeUnitSphereToCircle
      ⟨(circleToPlaneClosedUnitBall z : Plane), by
        rw [mem_sphere_zero_iff_norm]
        change ‖planeComplexIsometry.symm (z : ℂ)‖ = 1
        rw [LinearIsometryEquiv.norm_map, Circle.norm_coe]⟩ = z := by
  apply Subtype.ext
  exact planeComplexIsometry.apply_symm_apply z

theorem continuous_circleToPlaneClosedUnitBall : Continuous circleToPlaneClosedUnitBall := by
  apply Continuous.subtype_mk
  exact planeComplexIsometry.symm.continuous.comp continuous_subtype_val

theorem continuous_planeUnitSphereToCircle : Continuous planeUnitSphereToCircle := by
  apply Continuous.subtype_mk
  exact planeComplexIsometry.continuous.comp continuous_subtype_val

/-- The linear isometry sends the complex unit disk to the plane unit ball. -/
noncomputable def complexDiskToPlaneClosedUnitBall
    (z : ClosedUnitDisk) : Metric.closedBall (0 : Plane) 1 :=
  ⟨planeComplexIsometry.symm z.1, by
    rw [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
    simpa [dist_zero_right] using Metric.mem_closedBall.mp z.2⟩

theorem continuous_complexDiskToPlaneClosedUnitBall :
    Continuous complexDiskToPlaneClosedUnitBall := by
  apply Continuous.subtype_mk
  exact planeComplexIsometry.symm.continuous.comp continuous_subtype_val

/-- The closed unit ball in the project's Euclidean plane does not retract onto its sphere. -/
theorem no_retraction_planeClosedUnitBall :
    ¬ ∃ r : Metric.closedBall (0 : Plane) 1 → Metric.sphere (0 : Plane) 1,
      Continuous r ∧
        ∀ z : Metric.sphere (0 : Plane) 1,
          r ⟨z.1, Metric.mem_closedBall.mpr z.2.le⟩ = z := by
  rintro ⟨r, hr, hretract⟩
  apply no_retraction_closedUnitDisk
  let r' : ClosedUnitDisk → Circle := fun z =>
    planeUnitSphereToCircle (r (complexDiskToPlaneClosedUnitBall z))
  refine ⟨r', ?_, ?_⟩
  · exact continuous_planeUnitSphereToCircle.comp
      (hr.comp continuous_complexDiskToPlaneClosedUnitBall)
  · intro z
    let zp : Metric.sphere (0 : Plane) 1 :=
      ⟨planeComplexIsometry.symm z, by
        rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map, Circle.norm_coe]⟩
    change planeUnitSphereToCircle (r ⟨zp.1, Metric.mem_closedBall.mpr zp.2.le⟩) = z
    rw [hretract zp]
    exact planeUnitSphereToCircle_circleToPlaneClosedUnitBall z

/-- Retractions are invariant under an ambient homeomorphism carrying both the disk and its
boundary to the target disk and boundary. -/
theorem no_retraction_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A B : Set X} {A' B' : Set Y} (e : X ≃ₜ Y)
    (hA : e '' A = A') (hB : e '' B = B') (hBA : B ⊆ A) (hB'A' : B' ⊆ A')
    (hno : ¬ ∃ r : A' → B', Continuous r ∧
      ∀ z : B', r ⟨z.1, hB'A' z.2⟩ = z) :
    ¬ ∃ r : A → B, Continuous r ∧
      ∀ z : B, r ⟨z.1, hBA z.2⟩ = z := by
  rintro ⟨r, hr, hretract⟩
  apply hno
  have hApre : A = e ⁻¹' A' := by
    ext x
    constructor
    · intro hx
      exact hA ▸ ⟨x, hx, rfl⟩
    · intro hx
      have hex : e x ∈ e '' A := hA.symm ▸ hx
      obtain ⟨y, hy, hey⟩ := hex
      exact e.injective hey ▸ hy
  have hBpre : B = e ⁻¹' B' := by
    ext x
    constructor
    · intro hx
      exact hB ▸ ⟨x, hx, rfl⟩
    · intro hx
      have hex : e x ∈ e '' B := hB.symm ▸ hx
      obtain ⟨y, hy, hey⟩ := hex
      exact e.injective hey ▸ hy
  let eA : A ≃ₜ A' := e.sets hApre
  let eB : B ≃ₜ B' := e.sets hBpre
  let r' : A' → B' := fun x => eB (r (eA.symm x))
  refine ⟨r', eB.continuous.comp (hr.comp eA.symm.continuous), ?_⟩
  intro z
  apply Subtype.ext
  have hzB : e.symm z.1 ∈ B := by
    rw [hBpre]
    change e (e.symm z.1) ∈ B'
    rw [e.apply_symm_apply]
    exact z.2
  have hzA : e.symm z.1 ∈ A := hBA hzB
  change e (r ⟨e.symm z.1, hzA⟩).1 = z.1
  rw [show (r ⟨e.symm z.1, hzA⟩).1 = e.symm z.1 from
    congrArg Subtype.val (hretract ⟨e.symm z.1, hzB⟩)]
  exact e.apply_symm_apply z.1

/-- A nondegenerate closed plane triangle has no continuous retraction onto its frontier. -/
theorem IsTriangle.no_retraction {C : Set Plane} (hC : IsTriangle C) :
    ¬ ∃ r : C → frontier C,
      Continuous r ∧ ∀ z : frontier C,
        r ⟨z.1, hC.isCompact.isClosed.frontier_subset z.2⟩ = z := by
  obtain ⟨e, -, hclosure, hfrontier⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hC.convex
      hC.infinite_interior.nonempty hC.isCompact.isBounded
  have hclosed : IsClosed C := hC.isCompact.isClosed
  have hCimage : e '' C = Metric.closedBall (0 : Plane) 1 := by
    rw [← hclosed.closure_eq]
    exact hclosure
  exact no_retraction_of_homeomorph e hCimage hfrontier
    hC.isCompact.isClosed.frontier_subset Metric.sphere_subset_closedBall
    no_retraction_planeClosedUnitBall

/-- Radial projection from an interior point of a bounded convex plane set retracts the
punctured plane onto the set's frontier.  The Minkowski gauge supplies the distance to the
frontier along each ray. -/
theorem exists_radial_retraction_to_frontier {C : Set Plane}
    (hconvex : Convex ℝ C) (hbounded : Bornology.IsBounded C)
    {q : Plane} (hq : q ∈ interior C) :
    ∃ R : {x : Plane // x ≠ q} → frontier C,
      Continuous R ∧
        ∀ x : frontier C, R ⟨x.1, fun h =>
          Set.disjoint_left.mp disjoint_interior_frontier hq (h ▸ x.2)⟩ = x := by
  let S : Set Plane := -q +ᵥ C
  have hSconvex : Convex ℝ S := by
    simpa only [S] using hconvex.vadd (-q)
  have hSnhds : S ∈ nhds (0 : Plane) := by
    rw [← mem_interior_iff_mem_nhds]
    change (0 : Plane) ∈ interior (-q +ᵥ C)
    rw [interior_vadd]
    exact ⟨q, hq, by simp [vadd_eq_add]⟩
  have hSbounded : Bornology.IsVonNBounded ℝ S :=
    NormedSpace.isVonNBounded_of_isBounded ℝ (hbounded.vadd (-q))
  have hSabsorbent : Absorbent ℝ S := absorbent_nhds_zero hSnhds
  have hgaugePos (x : {x : Plane // x ≠ q}) :
      0 < gauge S (x.1 - q) := by
    rw [gauge_pos hSabsorbent hSbounded]
    exact sub_ne_zero.mpr x.2
  let radial (x : {x : Plane // x ≠ q}) : Plane :=
    q + (gauge S (x.1 - q))⁻¹ • (x.1 - q)
  have hradialFrontier (x : {x : Plane // x ≠ q}) : radial x ∈ frontier C := by
    have hgauge : gauge S ((gauge S (x.1 - q))⁻¹ • (x.1 - q)) = 1 := by
      rw [gauge_smul_of_nonneg (inv_nonneg.mpr (hgaugePos x).le), smul_eq_mul,
        inv_mul_cancel₀ (hgaugePos x).ne']
    have hfrontierS : (gauge S (x.1 - q))⁻¹ • (x.1 - q) ∈ frontier S :=
      (gauge_eq_one_iff_mem_frontier hSconvex hSnhds).mp hgauge
    let w := (gauge S (x.1 - q))⁻¹ • (x.1 - q)
    have hwFrontier : w ∈ frontier (-q +ᵥ C) := hfrontierS
    rw [frontier, closure_vadd, interior_vadd] at hwFrontier
    rw [frontier]
    constructor
    · rcases hwFrontier.1 with ⟨y, hy, heq⟩
      change q + w ∈ closure C
      have hqy : q + w = y := by
        rw [← heq]
        simp [vadd_eq_add]
      exact hqy ▸ hy
    · intro hqwin
      change q + w ∈ interior C at hqwin
      apply hwFrontier.2
      exact ⟨q + w, hqwin, by simp [vadd_eq_add]⟩
  let R : {x : Plane // x ≠ q} → frontier C :=
    fun x => ⟨radial x, hradialFrontier x⟩
  refine ⟨R, ?_, ?_⟩
  · apply Continuous.subtype_mk
    have hgauge : Continuous fun x : {x : Plane // x ≠ q} => gauge S (x.1 - q) :=
      (continuous_gauge hSconvex hSnhds).comp
        (continuous_subtype_val.sub continuous_const)
    have hginv : Continuous fun x : {x : Plane // x ≠ q} => (gauge S (x.1 - q))⁻¹ :=
      hgauge.inv₀ fun x => (hgaugePos x).ne'
    exact continuous_const.add (hginv.smul (continuous_subtype_val.sub continuous_const))
  · intro x
    apply Subtype.ext
    have hxS : x.1 - q ∈ frontier S := by
      change x.1 - q ∈ frontier (-q +ᵥ C)
      rw [frontier, closure_vadd, interior_vadd]
      constructor
      · exact ⟨x.1, x.2.1, by simp [vadd_eq_add, sub_eq_add_neg, add_comm]⟩
      · rintro ⟨y, hy, heq⟩
        apply x.2.2
        have hyx : y = x.1 := by
          apply_fun (fun z : Plane => q + z) at heq
          simpa [vadd_eq_add, sub_eq_add_neg, add_assoc] using heq
        rwa [← hyx]
    have hgauge : gauge S (x.1 - q) = 1 :=
      (gauge_eq_one_iff_mem_frontier hSconvex hSnhds).mpr hxS
    change radial ⟨x.1, _⟩ = x.1
    simp [radial, hgauge]

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification08_block_08
/- END ClassificationOfSurfaces.Moise.NoRetraction -/

/- BEGIN ClassificationOfSurfaces.Moise.PolygonalArcModel | 121667ae9bf8719a4073de58fde4fdfdda54a0dd582ce9b571800d2b60598e4e -/
section schottkyclassification08_block_09
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-! # PL segment models for polygonal arcs -/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace BrokenLineData

/-- A polygonal arc extracted from a broken line is the endpoint-preserving PL image of a
straight segment. -/
theorem exists_PL_segment_model {U : Set Plane} (B : BrokenLineData U) :
    ∃ (S : PlaneComplex) (F : Plane → Plane),
      S.support = segment ℝ (planePoint 0 0) (planePoint B.resolvedWalk.length 0) ∧
      IsPLOn S F ∧ (∀ s ∈ S.simplexes, s.card ≤ 2) ∧
      Set.InjOn F S.support ∧ F '' S.support = B.resolvedCarrier ∧
      F (planePoint 0 0) = B.start ∧
      F (planePoint B.resolvedWalk.length 0) = B.finish := by
  let A : PlaneComplex := PlaneComplex.active B.resolvedComplex
  have hAvertex : ∀ v, A.position v ∈ A.support := by
    intro v
    change B.resolvedComplex.position v.1 ∈ A.support
    rw [B.resolvedComplex.active_support]
    exact v.2
  have hAgraph : ∀ s ∈ A.simplexes, s.card ≤ 2 := by
    intro s hs
    have hsResolved := B.resolvedComplex.mem_activeSimplexes.mp hs
    calc
      s.card = (s.map B.resolvedComplex.activeEmbedding).card :=
        (Finset.card_map B.resolvedComplex.activeEmbedding).symm
      _ ≤ 2 := B.resolvedComplex_card_le_two hsResolved
  have hAaffine : ∀ s ∈ A.simplexes,
      IsAffineOn B.resolvedStraighten (A.cellCarrier s) := by
    intro s hs
    erw [B.resolvedComplex.active_cellCarrier]
    exact B.resolvedStraighten_affineOn_faces _
      (B.resolvedComplex.mem_activeSimplexes.mp hs)
  have hAinj : Set.InjOn B.resolvedStraighten A.support := by
    rw [B.resolvedComplex.active_support, B.resolvedComplex_support]
    exact B.resolvedStraighten_injectiveOn
  let S : PlaneComplex :=
    A.mapGraph B.resolvedStraighten hAvertex hAinj hAgraph hAaffine
  have hSsupport : S.support =
      segment ℝ (planePoint 0 0) (planePoint B.resolvedWalk.length 0) := by
    change (A.mapGraph B.resolvedStraighten hAvertex hAinj hAgraph hAaffine).support = _
    rw [A.mapGraph_support B.resolvedStraighten hAvertex hAinj hAgraph hAaffine,
      B.resolvedComplex.active_support, B.resolvedComplex_support,
      B.resolvedStraighten_image]
  let qpos : S.Vertex → Plane := A.position
  have qinj : Function.Injective qpos := A.position_injective
  have qaff : ∀ s ∈ S.simplexes, AffineIndependent ℝ fun v : s => qpos v := by
    intro s hs
    exact A.affineIndependent s hs
  have qface : ∀ s ∈ S.simplexes, ∀ t ∈ S.simplexes,
      convexHull ℝ (qpos '' (s : Set S.Vertex)) ∩
          convexHull ℝ (qpos '' (t : Set S.Vertex)) =
        convexHull ℝ (qpos '' ((s ∩ t : Finset S.Vertex) : Set S.Vertex)) := by
    intro s hs t ht
    exact A.face_inter s hs t ht
  let F : Plane → Plane := S.repositionMap qpos qinj qaff qface
  have hRsupport : (S.reposition qpos qinj qaff qface).support = A.support := by
    rfl
  let v0R : B.resolvedComplex.ActiveVertex :=
    ⟨B.resolvedWalk.getVert 0, B.resolvedVertex_mem_support 0⟩
  let vnR : B.resolvedComplex.ActiveVertex :=
    ⟨B.resolvedWalk.getVert B.resolvedWalk.length,
      B.resolvedVertex_mem_support (Fin.last B.resolvedWalk.length)⟩
  let v0A : A.Vertex := v0R
  let vnA : A.Vertex := vnR
  let v0 : S.Vertex := v0A
  let vn : S.Vertex := vnA
  have hv0 : ({v0} : Finset S.Vertex) ∈ S.simplexes := by
    change ({v0R} : Finset B.resolvedComplex.ActiveVertex) ∈
      B.resolvedComplex.activeSimplexes
    apply B.resolvedComplex.mem_activeSimplexes.mpr
    rw [Finset.map_singleton]
    change ({B.resolvedWalk.getVert 0} :
      Finset B.arrangementMesh.toPlaneComplex.Vertex) ∈ B.resolvedComplex.simplexes
    exact B.resolvedVertex_face 0
  have hvn : ({vn} : Finset S.Vertex) ∈ S.simplexes := by
    change ({vnR} : Finset B.resolvedComplex.ActiveVertex) ∈
      B.resolvedComplex.activeSimplexes
    apply B.resolvedComplex.mem_activeSimplexes.mpr
    rw [Finset.map_singleton]
    change ({B.resolvedWalk.getVert B.resolvedWalk.length} :
      Finset B.arrangementMesh.toPlaneComplex.Vertex) ∈ B.resolvedComplex.simplexes
    exact B.resolvedVertex_face (Fin.last B.resolvedWalk.length)
  have hSpos0 : S.position v0 = planePoint 0 0 := B.resolvedStraighten_start
  have hSposn : S.position vn = planePoint B.resolvedWalk.length 0 :=
    B.resolvedStraighten_finish
  have hqpos0 : qpos v0 = B.start := B.resolvedVertex_start
  have hqposn : qpos vn = B.finish := B.resolvedVertex_finish
  refine ⟨S, F, hSsupport, S.repositionMap_isPL qpos qinj qaff qface,
    (fun s hs => hAgraph s hs), ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hxF : F x =
        (S.repositionHomeomorphAll qpos qinj qaff qface ⟨x, hx⟩).1 := by
      simp [F, PlaneComplex.repositionMap, hx]
    have hyF : F y =
        (S.repositionHomeomorphAll qpos qinj qaff qface ⟨y, hy⟩).1 := by
      simp [F, PlaneComplex.repositionMap, hy]
    have heq : S.repositionHomeomorphAll qpos qinj qaff qface ⟨x, hx⟩ =
        S.repositionHomeomorphAll qpos qinj qaff qface ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa [← hxF, ← hyF] using hxy
    exact congrArg Subtype.val
      ((S.repositionHomeomorphAll qpos qinj qaff qface).injective heq)
  · rw [← B.resolvedComplex_support, ← B.resolvedComplex.active_support,
      ← hRsupport]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x ∈ S.support := hx
      have hFx : F x =
          (S.repositionHomeomorphAll qpos qinj qaff qface ⟨x, hx'⟩).1 := by
        simp [F, PlaneComplex.repositionMap, hx']
      rw [hFx]
      exact (S.repositionHomeomorphAll qpos qinj qaff qface ⟨x, hx'⟩).2
    · intro hy
      obtain ⟨x, hx⟩ :=
        (S.repositionHomeomorphAll qpos qinj qaff qface).surjective ⟨y, hy⟩
      refine ⟨x.1, x.2, ?_⟩
      rw [show F x.1 =
        (S.repositionHomeomorphAll qpos qinj qaff qface x).1 by
          simp [F, PlaneComplex.repositionMap, x.2]]
      exact congrArg Subtype.val hx
  · calc
      F (planePoint 0 0) = F (S.position v0) := congrArg F hSpos0.symm
      _ = qpos v0 := S.repositionMap_position qpos qinj qaff qface v0 hv0
      _ = B.start := hqpos0
  · calc
      F (planePoint B.resolvedWalk.length 0) = F (S.position vn) :=
        congrArg F hSposn.symm
      _ = qpos vn := S.repositionMap_position qpos qinj qaff qface vn hvn
      _ = B.finish := hqposn

end BrokenLineData

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification08_block_09
/- END ClassificationOfSurfaces.Moise.PolygonalArcModel -/

/- BEGIN ClassificationOfSurfaces.Moise.RelativeSynchronizedArrangement | 32d6f58f5fc9b20b7f57dc28a5e257b2a9e098d00d0cf8cddd8c5e17b48ba5a1 -/
section schottkyclassification08_block_10
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Synchronized polygonal arrangements with additional finite cuts

The relative Radó weld must cut the common old/new planar arrangement by finitely many
additional lines coming from retained PL face certificates.  Both sides must still be literal
submeshes of one ambient triangle mesh.  This file records that harmless extra-line
generalization of `PolygonalFamily.synchronizedArrangement`.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace PolygonalFamily

variable {ι : Type*} [Fintype ι] (J : ι → PolygonalCircle)

/-- Cut the polygon-family arrangement simultaneously by a target mesh and by an additional
finite list of affine lines. -/
noncomputable def relativeSynchronizedArrangement (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) : TriangleMesh :=
  (arrangementMesh J).refineByLines (N.coordinateLines ++ lines)

theorem relativeSynchronizedArrangement_support (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) :
    (relativeSynchronizedArrangement J N lines).toPlaneComplex.support =
      (arrangementMesh J).toPlaneComplex.support :=
  (arrangementMesh J).refineByLines_support _

/-- A relative synchronized chamber belongs to the selected polygonal side. -/
def IsSelectedRelativeSynchronizedTriangle (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) (p : ι → Prop)
    (t : Finset (relativeSynchronizedArrangement J N lines).Vertex) : Prop :=
  ∃ i, p i ∧
    interior ((relativeSynchronizedArrangement J N lines).triangleCarrier t) ⊆
      (J i).interiorRegion

/-- The selected polygonal member after all additional cuts. -/
noncomputable def selectedRelativeSynchronizedMesh (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) (p : ι → Prop) : TriangleMesh := by
  classical
  exact (relativeSynchronizedArrangement J N lines).restrictTriangles
    (IsSelectedRelativeSynchronizedTriangle J N lines p)

/-- A relative synchronized chamber belongs to the prescribed target side exactly when its
interior meets the target support. -/
def IsTargetRelativeSynchronizedTriangle (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (t : Finset (relativeSynchronizedArrangement J N lines).Vertex) : Prop :=
  (interior ((relativeSynchronizedArrangement J N lines).triangleCarrier t) ∩
    N.toPlaneComplex.support).Nonempty

/-- The target member after all additional cuts. -/
noncomputable def targetRelativeSynchronizedMesh (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) : TriangleMesh := by
  classical
  exact (relativeSynchronizedArrangement J N lines).restrictTriangles
    (IsTargetRelativeSynchronizedTriangle J N lines)

theorem selectedRelativeSynchronizedMesh_triangle_mem
    (N : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ)) (p : ι → Prop)
    {t : Finset (selectedRelativeSynchronizedMesh J N lines p).Vertex} :
    t ∈ (selectedRelativeSynchronizedMesh J N lines p).triangles ↔
      t ∈ (relativeSynchronizedArrangement J N lines).triangles ∧
        IsSelectedRelativeSynchronizedTriangle J N lines p t := by
  classical
  exact (relativeSynchronizedArrangement J N lines).mem_restrictTriangles_triangles _

theorem targetRelativeSynchronizedMesh_triangle_mem
    (N : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ))
    {t : Finset (targetRelativeSynchronizedMesh J N lines).Vertex} :
    t ∈ (targetRelativeSynchronizedMesh J N lines).triangles ↔
      t ∈ (relativeSynchronizedArrangement J N lines).triangles ∧
        IsTargetRelativeSynchronizedTriangle J N lines t := by
  classical
  exact (relativeSynchronizedArrangement J N lines).mem_restrictTriangles_triangles _

/-- Every chamber after the extra cuts remains inside an original polygon-family arrangement
triangle. -/
theorem exists_arrangementTriangle_of_relativeSynchronized
    {N : TriangleMesh} {lines : List (Plane →ᵃ[ℝ] ℝ)}
    {t : Finset (relativeSynchronizedArrangement J N lines).Vertex}
    (ht : t ∈ (relativeSynchronizedArrangement J N lines).triangles) :
    ∃ u ∈ (arrangementMesh J).triangles,
      (relativeSynchronizedArrangement J N lines).triangleCarrier t ⊆
        (arrangementMesh J).triangleCarrier u := by
  let R := relativeSynchronizedArrangement J N lines
  have htFace : t ∈ R.toPlaneComplex.simplexes :=
    R.mem_faces_iff.mpr ⟨by
      have htcard : t.card = 3 := R.card_triangle t ht
      exact Finset.card_pos.mp (by omega), t, ht, subset_rfl⟩
  obtain ⟨s, hs, hts⟩ :=
    ((arrangementMesh J).refineByLines_subdivides
      (N.coordinateLines ++ lines)).2 t htFace
  obtain ⟨-, u, hu, hsu⟩ := (arrangementMesh J).mem_faces_iff.mp hs
  refine ⟨u, hu, ?_⟩
  exact hts.trans (convexHull_mono (Set.image_mono hsu))

/-- Extra cuts preserve the one-sidedness of every chamber with respect to every polygon in
the family. -/
theorem relativeSynchronizedTriangle_interior_side
    (N : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ)) (i : ι)
    {t : Finset (relativeSynchronizedArrangement J N lines).Vertex}
    (ht : t ∈ (relativeSynchronizedArrangement J N lines).triangles) :
    interior ((relativeSynchronizedArrangement J N lines).triangleCarrier t) ⊆
        (J i).interiorRegion ∨
      interior ((relativeSynchronizedArrangement J N lines).triangleCarrier t) ⊆
        (J i).exteriorRegion := by
  obtain ⟨u, hu, htu⟩ :=
    exists_arrangementTriangle_of_relativeSynchronized J ht
  have hint := interior_mono htu
  rcases arrangementTriangle_interior_side J i hu with hin | hout
  · exact Or.inl (hint.trans hin)
  · exact Or.inr (hint.trans hout)

/-- Additional cuts do not alter the selected polygonal support. -/
theorem selectedRelativeSynchronizedMesh_support
    (N : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ)) (p : ι → Prop) :
    (selectedRelativeSynchronizedMesh J N lines p).toPlaneComplex.support =
      selectedClosedRegion J p := by
  classical
  let R := relativeSynchronizedArrangement J N lines
  let L := selectedRelativeSynchronizedMesh J N lines p
  apply Set.Subset.antisymm
  · rw [TriangleMesh.toPlaneComplex_support]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    obtain ⟨htR, i, hpi, hi⟩ :=
      (selectedRelativeSynchronizedMesh_triangle_mem J N lines p).mp ht
    let T : R.Triangle := ⟨t, htR⟩
    have hxClosure : x ∈ closure (interior (R.triangleCarrier t)) := by
      rw [R.closure_interior_triangleCarrier T]
      exact hxt
    have hxRegion : x ∈ closure (J i).interiorRegion :=
      closure_mono hi hxClosure
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
      ⟨hpi, by simpa only [PolygonalCircle.closedRegion] using hxRegion⟩⟩
  · intro x hx
    obtain ⟨i, hpi, hxi⟩ := Set.mem_iUnion₂.mp hx
    rw [PolygonalCircle.closedRegion] at hxi
    apply closure_minimal _ L.toPlaneComplex.isCompact_support.isClosed hxi
    intro y hy
    have hyFamily : y ∈ closedRegion J := Set.mem_iUnion.mpr
      ⟨i, by rw [(J i).closedRegion_eq_union]; exact Or.inl hy⟩
    have hyArrangement : y ∈ (arrangementMesh J).toPlaneComplex.support :=
      closedRegion_subset_arrangementMesh_support J hyFamily
    have hyR : y ∈ R.toPlaneComplex.support := by
      rw [show R.toPlaneComplex.support =
          (arrangementMesh J).toPlaneComplex.support by
        exact relativeSynchronizedArrangement_support J N lines]
      exact hyArrangement
    rw [TriangleMesh.toPlaneComplex_support] at hyR
    simp only [Set.mem_iUnion] at hyR
    obtain ⟨t, ht, hyt⟩ := hyR
    let T : R.Triangle := ⟨t, ht⟩
    have hyClosure : y ∈ closure (interior (R.triangleCarrier t)) := by
      rw [R.closure_interior_triangleCarrier T]
      exact hyt
    have hyInterClosure : y ∈ closure
        ((J i).interiorRegion ∩ interior (R.triangleCarrier t)) :=
      (J i).isOpen_interiorRegion.inter_closure ⟨hy, hyClosure⟩
    obtain ⟨z, hzInside, hzT⟩ := Set.Nonempty.of_closure ⟨y, hyInterClosure⟩
    have htInside : interior (R.triangleCarrier t) ⊆
        (J i).interiorRegion := by
      rcases relativeSynchronizedTriangle_interior_side J N lines i ht with
          hin | hout
      · exact hin
      · exact False.elim <| Set.disjoint_left.mp
          (J i).disjoint_interior_exterior hzInside (hout hzT)
    rw [TriangleMesh.toPlaneComplex_support]
    exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr
      ⟨(selectedRelativeSynchronizedMesh_triangle_mem J N lines p).mpr
        ⟨ht, i, hpi, htInside⟩, hyt⟩⟩

/-- Every retained target chamber lies in a triangle of the prescribed target mesh. -/
theorem exists_targetTriangle_of_targetRelativeSynchronized
    (N : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ))
    {t : Finset (targetRelativeSynchronizedMesh J N lines).Vertex}
    (ht : t ∈ (targetRelativeSynchronizedMesh J N lines).triangles) :
    ∃ u ∈ N.triangles,
      (relativeSynchronizedArrangement J N lines).triangleCarrier t ⊆
        N.triangleCarrier u := by
  have htData :=
    (targetRelativeSynchronizedMesh_triangle_mem J N lines).mp ht
  let T : (relativeSynchronizedArrangement J N lines).Triangle :=
    ⟨t, htData.1⟩
  obtain ⟨U, hTU⟩ :=
    (arrangementMesh J).exists_target_triangle_of_refineByLines_of_interior_inter_support
      N (N.coordinateLines ++ lines)
      (fun a ha ↦ List.mem_append_left _ ha) T htData.2
  exact ⟨U.1, U.2, hTU⟩

/-- If the target lies in the polygon-family arrangement, its relative synchronized member has
exactly the prescribed support. -/
theorem targetRelativeSynchronizedMesh_support
    (N : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (hsub : N.toPlaneComplex.support ⊆
      (arrangementMesh J).toPlaneComplex.support) :
    (targetRelativeSynchronizedMesh J N lines).toPlaneComplex.support =
      N.toPlaneComplex.support := by
  classical
  let R := relativeSynchronizedArrangement J N lines
  let L := targetRelativeSynchronizedMesh J N lines
  apply Set.Subset.antisymm
  · rw [TriangleMesh.toPlaneComplex_support]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    obtain ⟨u, hu, htu⟩ :=
      exists_targetTriangle_of_targetRelativeSynchronized J N lines ht
    rw [TriangleMesh.toPlaneComplex_support]
    exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hu, htu hxt⟩⟩
  · rw [TriangleMesh.toPlaneComplex_support]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨u, hu, hxu⟩ := hx
    let U : N.Triangle := ⟨u, hu⟩
    have hinterior : interior (N.triangleCarrier u) ⊆
        L.toPlaneComplex.support := by
      intro y hy
      have hyN : y ∈ N.toPlaneComplex.support := by
        rw [TriangleMesh.toPlaneComplex_support]
        exact Set.mem_iUnion.mpr
          ⟨u, Set.mem_iUnion.mpr ⟨hu, interior_subset hy⟩⟩
      have hyR : y ∈ R.toPlaneComplex.support := by
        rw [relativeSynchronizedArrangement_support]
        exact hsub hyN
      rw [TriangleMesh.toPlaneComplex_support] at hyR
      simp only [Set.mem_iUnion] at hyR
      obtain ⟨t, ht, hyt⟩ := hyR
      let T : R.Triangle := ⟨t, ht⟩
      have hyClosure : y ∈ closure (interior (R.triangleCarrier t)) := by
        rw [R.closure_interior_triangleCarrier T]
        exact hyt
      have hyInterClosure : y ∈ closure
          (interior (N.triangleCarrier u) ∩
            interior (R.triangleCarrier t)) :=
        isOpen_interior.inter_closure ⟨hy, hyClosure⟩
      obtain ⟨z, hzN, hzR⟩ := Set.Nonempty.of_closure ⟨y, hyInterClosure⟩
      have htKeep : t ∈ L.triangles :=
        (targetRelativeSynchronizedMesh_triangle_mem J N lines).mpr
          ⟨ht, ⟨z, hzR, by
            rw [TriangleMesh.toPlaneComplex_support]
            exact Set.mem_iUnion.mpr
              ⟨u, Set.mem_iUnion.mpr ⟨hu, interior_subset hzN⟩⟩⟩⟩
      rw [TriangleMesh.toPlaneComplex_support]
      exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨htKeep, hyt⟩⟩
    change x ∈ N.triangleCarrier u at hxu
    rw [← N.closure_interior_triangleCarrier U] at hxu
    exact closure_minimal hinterior L.toPlaneComplex.isCompact_support.isClosed hxu

/-- The selected and target members inherit the ambient planar edge-incidence bound. -/
theorem relativeSynchronizedMeshes_joint_edge_valence
    (N : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ)) (p : ι → Prop)
    (e : Finset (relativeSynchronizedArrangement J N lines).Vertex)
    (he : e.card = 2) :
    (((selectedRelativeSynchronizedMesh J N lines p).triangles ∪
        (targetRelativeSynchronizedMesh J N lines).triangles).filter
      fun t ↦ e ⊆ t).card ≤ 2 := by
  apply le_trans (Finset.card_le_card ?_)
    ((relativeSynchronizedArrangement J N lines).card_incidentTriangles_le_two he)
  intro t ht
  replace ht := Finset.mem_filter.mp ht
  apply (relativeSynchronizedArrangement J N lines).mem_incidentTriangles_iff.mpr
  refine ⟨?_, ht.2⟩
  rcases Finset.mem_union.mp ht.1 with htOld | htTarget
  · exact
      (selectedRelativeSynchronizedMesh_triangle_mem J N lines p).mp htOld |>.1
  · exact
      (targetRelativeSynchronizedMesh_triangle_mem J N lines).mp htTarget |>.1

end PolygonalFamily

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification08_block_10
/- END ClassificationOfSurfaces.Moise.RelativeSynchronizedArrangement -/
