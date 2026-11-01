/- Derived from https://github.com/mccorvie/classification-of-surfaces (commit e3c7230fe78d7b056a415d9ecae6f77887046b32),
   Apache License 2.0. Modified for LiZhongQC: bundled with other upstream files, imports renamed,
   local proof repairs. See NOTICE.Classification and LICENSE.Apache-2.0 in this directory. -/
/- SchottkyClassification07: pinned classification sources (upstream e3c7230f); see BUNDLE_MAP.json and licenses/. -/
import LiZhongExternal.Classification.SchottkyClassification04
import LiZhongExternal.Classification.SchottkyClassification05
import LiZhongExternal.Classification.SchottkyClassification06

/- BEGIN ClassificationOfSurfaces.Moise.PolygonalCrosscut | c10b056867affa21641a5ec4d08b84deebfb8d6e334ec3613ca33c68514ac5e7 -/
noncomputable section

section schottkyclassification07_block_01
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Polygonal crosscuts

The set-theoretic part of Moise Chapter 2, Theorems 7 and 8.  Three polygonal arcs with common
endpoints form three polygons.  When the third arc is a chord inside the first polygon, the two
polygons containing the chord lie inside the first polygon.  This is the cutting lemma used in
the free-triangle induction of Chapter 3.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace PolygonalCircle

/-- Splitting a nondegenerate segment at a non-endpoint produces two subsegments meeting only
at the split point. -/
theorem segment_split_inter {a b p : Plane} (hp : p ∈ segment ℝ a b)
    (hpa : p ≠ a) (hpb : p ≠ b) :
    segment ℝ a p ∩ segment ℝ p b = {p} := by
  rw [segment_eq_image_lineMap] at hp
  obtain ⟨c, hc, rfl⟩ := hp
  have hab : a ≠ b := by
    intro hab
    subst b
    rw [AffineMap.lineMap_same_apply] at hpa
    exact hpa rfl
  have hc0 : 0 < c := by
    exact lt_of_le_of_ne hc.1 fun hc0 => hpa <| by
      rw [← hc0, AffineMap.lineMap_apply_zero]
  have hc1 : c < 1 := by
    exact lt_of_le_of_ne hc.2 fun hc1 => hpb <| by
      rw [hc1, AffineMap.lineMap_apply_one]
  apply Set.Subset.antisymm
  · rintro x ⟨hxLeft, hxRight⟩
    rw [segment_eq_image_lineMap] at hxLeft hxRight
    obtain ⟨d, hd, rfl⟩ := hxLeft
    obtain ⟨e, he, heq⟩ := hxRight
    rw [AffineMap.lineMap_lineMap_right, AffineMap.lineMap_lineMap_left] at heq
    have hparam : d * c = 1 - (1 - e) * (1 - c) :=
      (AffineMap.lineMap_eq_lineMap_iff.mp heq.symm).resolve_left hab
    have hle : d * c ≤ c := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hd.2) hc.1]
    have hge : c ≤ 1 - (1 - e) * (1 - c) := by
      nlinarith [mul_nonneg he.1 (sub_nonneg.mpr hc.2)]
    have hdc : d * c = c := le_antisymm hle (hparam ▸ hge)
    rw [AffineMap.lineMap_lineMap_right, hdc]
    exact Set.mem_singleton _
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩

/-- Vertex sequence obtained by inserting `p` in edge zero.  Its cyclic order is
`p, v₁, ..., vₙ₋₁, v₀`. -/
def insertZeroVertex (J : PolygonalCircle) (p : Plane) : ZMod (J.n + 1) → Plane :=
  fun i => if i.val = 0 then p else J.vertex (i.val : ZMod J.n)

@[simp] theorem insertZeroVertex_zero (J : PolygonalCircle) (p : Plane) :
    J.insertZeroVertex p 0 = p := by
  simp [insertZeroVertex]

theorem insertZeroVertex_natCast (J : PolygonalCircle) (p : Plane) {m : ℕ}
    (hm0 : 0 < m) (hm : m < J.n + 1) :
    J.insertZeroVertex p (m : ZMod (J.n + 1)) = J.vertex (m : ZMod J.n) := by
  rw [insertZeroVertex, ZMod.val_natCast_of_lt hm]
  simp only [if_neg hm0.ne']

/-- The prospective edges of `insertZero`, before packaging the simple-polygon proofs. -/
def insertZeroEdgeSegment (J : PolygonalCircle) (p : Plane)
    (i : ZMod (J.n + 1)) : Set Plane :=
  segment ℝ (J.insertZeroVertex p i) (J.insertZeroVertex p (i + 1))

theorem insertZeroEdgeSegment_zero (J : PolygonalCircle) (p : Plane) :
    J.insertZeroEdgeSegment p 0 = segment ℝ p (J.vertex 1) := by
  unfold insertZeroEdgeSegment
  rw [insertZeroVertex_zero]
  have htwo : 1 < J.n + 1 := by
    have := J.three_le
    omega
  rw [show (0 : ZMod (J.n + 1)) + 1 = 1 by simp]
  unfold insertZeroVertex
  rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt htwo]
  simp

theorem insertZeroEdgeSegment_middle (J : PolygonalCircle) (p : Plane) {m : ℕ}
    (hm0 : 0 < m) (hm : m < J.n) :
    J.insertZeroEdgeSegment p (m : ZMod (J.n + 1)) =
      J.edgeSegment (m : ZMod J.n) := by
  unfold insertZeroEdgeSegment edgeSegment
  rw [J.insertZeroVertex_natCast p hm0 (by omega)]
  have hm1 : m + 1 < J.n + 1 := by omega
  have hsucc : (m : ZMod (J.n + 1)) + 1 = (m + 1 : ℕ) := by
    norm_num [Nat.cast_add]
  rw [hsucc, J.insertZeroVertex_natCast p (by omega) hm1]
  congr 2
  norm_num [Nat.cast_add]

theorem insertZeroEdgeSegment_last (J : PolygonalCircle) (p : Plane) :
    J.insertZeroEdgeSegment p (J.n : ZMod (J.n + 1)) =
      segment ℝ (J.vertex 0) p := by
  unfold insertZeroEdgeSegment
  have hn : 0 < J.n := by
    have := J.three_le
    omega
  rw [J.insertZeroVertex_natCast p hn (by omega)]
  have hwrap : (J.n : ZMod (J.n + 1)) + 1 = 0 := by
    calc
      (J.n : ZMod (J.n + 1)) + 1 =
          ((J.n + 1 : ℕ) : ZMod (J.n + 1)) := by
            rw [Nat.cast_add, Nat.cast_one]
      _ = 0 := ZMod.natCast_self (J.n + 1)
  rw [hwrap, J.insertZeroVertex_zero]
  congr 2
  exact ZMod.natCast_self J.n

theorem insertZeroVertex_adjacent_ne (J : PolygonalCircle) {p : Plane}
    (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1)
    (i : ZMod (J.n + 1)) :
    J.insertZeroVertex p i ≠ J.insertZeroVertex p (i + 1) := by
  let m := i.val
  have hi : (m : ZMod (J.n + 1)) = i := ZMod.natCast_zmod_val i
  have hmle : m ≤ J.n := by
    have := i.val_lt
    omega
  rw [← hi]
  by_cases hm0 : m = 0
  · rw [hm0]
    change J.insertZeroVertex p (0 : ZMod (J.n + 1)) ≠
      J.insertZeroVertex p ((0 : ZMod (J.n + 1)) + 1)
    rw [J.insertZeroVertex_zero]
    have htwo : 1 < J.n + 1 := by
      have := J.three_le
      omega
    have hsucc : (0 : ZMod (J.n + 1)) + 1 = (1 : ZMod (J.n + 1)) := by simp
    rw [hsucc]
    unfold insertZeroVertex
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt htwo]
    simp only [if_neg (by omega : (1 : ℕ) ≠ 0)]
    simpa only [Nat.cast_one] using hp1
  by_cases hmn : m = J.n
  · rw [hmn]
    have hn : 0 < J.n := by
      have := J.three_le
      omega
    rw [J.insertZeroVertex_natCast p hn (by omega)]
    have hwrap : (J.n : ZMod (J.n + 1)) + 1 = 0 := by
      calc
        (J.n : ZMod (J.n + 1)) + 1 =
            ((J.n + 1 : ℕ) : ZMod (J.n + 1)) := by
              rw [Nat.cast_add, Nat.cast_one]
        _ = 0 := ZMod.natCast_self (J.n + 1)
    rw [hwrap, J.insertZeroVertex_zero]
    intro h
    apply hp0
    calc
      p = J.vertex (J.n : ZMod J.n) := h.symm
      _ = J.vertex 0 := congrArg J.vertex (ZMod.natCast_self J.n)
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hmlt : m < J.n := lt_of_le_of_ne hmle hmn
    rw [J.insertZeroVertex_natCast p hmpos (by omega)]
    have hsucc : (m : ZMod (J.n + 1)) + 1 = (m + 1 : ℕ) := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [hsucc, J.insertZeroVertex_natCast p (by omega) (by omega)]
    simpa only [Nat.cast_add, Nat.cast_one] using
      J.adjacent_ne (m : ZMod J.n)

theorem insertZero_consecutive_inter (J : PolygonalCircle) {p : Plane}
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1)
    (i : ZMod (J.n + 1)) :
    J.insertZeroEdgeSegment p i ∩ J.insertZeroEdgeSegment p (i + 1) =
      {J.insertZeroVertex p (i + 1)} := by
  have hp' : p ∈ segment ℝ (J.vertex 0) (J.vertex 1) := by
    simpa only [edgeSegment, zero_add] using hp
  let m := i.val
  have hi : (m : ZMod (J.n + 1)) = i := ZMod.natCast_zmod_val i
  have hmle : m ≤ J.n := by
    have := i.val_lt
    omega
  rw [← hi]
  by_cases hm0 : m = 0
  · rw [hm0]
    rw [Nat.cast_zero]
    simp only [zero_add]
    change J.insertZeroEdgeSegment p 0 ∩ J.insertZeroEdgeSegment p 1 =
      {J.insertZeroVertex p 1}
    rw [J.insertZeroEdgeSegment_zero]
    have hn : 1 < J.n := by
      have := J.three_le
      omega
    have hedge1 := J.insertZeroEdgeSegment_middle p (m := 1) (by omega) hn
    have hvertex1 := J.insertZeroVertex_natCast p (m := 1) (by omega) (by omega)
    have hedge1' : J.insertZeroEdgeSegment p (1 : ZMod (J.n + 1)) =
        J.edgeSegment (1 : ZMod J.n) := by
      simpa only [Nat.cast_one] using hedge1
    have hvertex1' : J.insertZeroVertex p (1 : ZMod (J.n + 1)) =
        J.vertex (1 : ZMod J.n) := by
      simpa only [Nat.cast_one] using hvertex1
    rw [hedge1', hvertex1']
    have hbase := J.consecutive_inter 0
    have hsub : segment ℝ p (J.vertex 1) ⊆
        segment ℝ (J.vertex 0) (J.vertex 1) :=
      (convex_segment (J.vertex 0) (J.vertex 1)).segment_subset hp'
        (right_mem_segment ℝ _ _)
    unfold edgeSegment at hbase ⊢
    simp only [zero_add, one_add_one_eq_two] at hbase ⊢
    apply Set.Subset.antisymm
    · intro x hx
      exact hbase ▸ ⟨hsub hx.1, hx.2⟩
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
  by_cases hmn : m = J.n
  · rw [hmn]
    have hwrap : (J.n : ZMod (J.n + 1)) + 1 = 0 := by
      calc
        (J.n : ZMod (J.n + 1)) + 1 =
            ((J.n + 1 : ℕ) : ZMod (J.n + 1)) := by
              rw [Nat.cast_add, Nat.cast_one]
        _ = 0 := ZMod.natCast_self (J.n + 1)
    rw [hwrap, J.insertZeroEdgeSegment_last, J.insertZeroEdgeSegment_zero,
      J.insertZeroVertex_zero]
    exact segment_split_inter hp' hp0 hp1
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hmlt : m < J.n := lt_of_le_of_ne hmle hmn
    by_cases hmlast : m + 1 = J.n
    · have hedgeM := J.insertZeroEdgeSegment_middle p hmpos hmlt
      have hedgeLast := J.insertZeroEdgeSegment_last p
      have hsucc : (m : ZMod (J.n + 1)) + 1 = (J.n : ZMod (J.n + 1)) := by
        calc
          (m : ZMod (J.n + 1)) + 1 = (m + 1 : ℕ) := by
            rw [Nat.cast_add, Nat.cast_one]
          _ = (J.n : ℕ) := by rw [hmlast]
      rw [hedgeM, hsucc, hedgeLast]
      have hvertex : J.insertZeroVertex p (J.n : ZMod (J.n + 1)) = J.vertex 0 := by
        rw [J.insertZeroVertex_natCast p (by omega) (by omega)]
        exact congrArg J.vertex (ZMod.natCast_self J.n)
      rw [hvertex]
      have hprev : (m : ZMod J.n) + 1 = 0 := by
        calc
          (m : ZMod J.n) + 1 = (m + 1 : ℕ) := by
            rw [Nat.cast_add, Nat.cast_one]
          _ = (J.n : ℕ) := by rw [hmlast]
          _ = 0 := ZMod.natCast_self J.n
      have hbase := J.consecutive_inter (m : ZMod J.n)
      have hprev2 : (m : ZMod J.n) + 2 = 1 := by
        calc
          (m : ZMod J.n) + 2 = ((m : ZMod J.n) + 1) + 1 := by
            rw [show (2 : ZMod J.n) = 1 + 1 by norm_num]
            abel
          _ = 0 + 1 := by rw [hprev]
          _ = 1 := zero_add 1
      unfold edgeSegment at hbase ⊢
      rw [hprev, hprev2] at hbase
      rw [hprev]
      have hsub : segment ℝ (J.vertex 0) p ⊆
          segment ℝ (J.vertex 0) (J.vertex 1) :=
        (convex_segment (J.vertex 0) (J.vertex 1)).segment_subset
          (left_mem_segment ℝ _ _) hp'
      apply Set.Subset.antisymm
      · intro x hx
        exact hbase ▸ ⟨hx.1, hsub hx.2⟩
      · intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
    · have hm1lt : m + 1 < J.n := by omega
      have hedgeM := J.insertZeroEdgeSegment_middle p hmpos hmlt
      have hedgeM1 := J.insertZeroEdgeSegment_middle p (m := m + 1) (by omega) hm1lt
      have hsucc : (m : ZMod (J.n + 1)) + 1 = (m + 1 : ℕ) := by
        rw [Nat.cast_add, Nat.cast_one]
      rw [hedgeM, hsucc, hedgeM1]
      have hvertex := J.insertZeroVertex_natCast p (m := m + 1) (by omega) (by omega)
      rw [hvertex]
      simpa only [edgeSegment, Nat.cast_add, Nat.cast_one, add_assoc,
        one_add_one_eq_two] using
        J.consecutive_inter (m : ZMod J.n)

theorem vertex_zero_not_mem_insertZero_first (J : PolygonalCircle) {p : Plane}
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1) :
    J.vertex 0 ∉ segment ℝ p (J.vertex 1) := by
  have hp' : p ∈ segment ℝ (J.vertex 0) (J.vertex 1) := by
    simpa only [edgeSegment, zero_add] using hp
  intro hmem
  have hinter := segment_split_inter hp' hp0 hp1
  have hboth : J.vertex 0 ∈
      segment ℝ (J.vertex 0) p ∩ segment ℝ p (J.vertex 1) :=
    ⟨left_mem_segment ℝ _ _, hmem⟩
  rw [hinter, Set.mem_singleton_iff] at hboth
  exact hp0 hboth.symm

theorem vertex_one_not_mem_insertZero_last (J : PolygonalCircle) {p : Plane}
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1) :
    J.vertex 1 ∉ segment ℝ (J.vertex 0) p := by
  have hp' : p ∈ segment ℝ (J.vertex 0) (J.vertex 1) := by
    simpa only [edgeSegment, zero_add] using hp
  intro hmem
  have hinter := segment_split_inter hp' hp0 hp1
  have hboth : J.vertex 1 ∈
      segment ℝ (J.vertex 0) p ∩ segment ℝ p (J.vertex 1) :=
    ⟨hmem, right_mem_segment ℝ _ _⟩
  rw [hinter, Set.mem_singleton_iff] at hboth
  exact hp1 hboth.symm

theorem disjoint_insertZero_first_previous (J : PolygonalCircle) {p : Plane}
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1) :
    Disjoint (segment ℝ p (J.vertex 1))
      (J.edgeSegment ((J.n - 1 : ℕ) : ZMod J.n)) := by
  have hn : 0 < J.n := by
    have := J.three_le
    omega
  have hp' : p ∈ segment ℝ (J.vertex 0) (J.vertex 1) := by
    simpa only [edgeSegment, zero_add] using hp
  have hprev : ((J.n - 1 : ℕ) : ZMod J.n) + 1 = 0 := by
    calc
      ((J.n - 1 : ℕ) : ZMod J.n) + 1 = ((J.n - 1 + 1 : ℕ) : ZMod J.n) := by
        rw [Nat.cast_add, Nat.cast_one]
      _ = (J.n : ℕ) := congrArg (fun q : ℕ => (q : ZMod J.n))
        (Nat.sub_add_cancel (by omega))
      _ = 0 := ZMod.natCast_self J.n
  have hprev2 : ((J.n - 1 : ℕ) : ZMod J.n) + 2 = 1 := by
    calc
      ((J.n - 1 : ℕ) : ZMod J.n) + 2 =
          (((J.n - 1 : ℕ) : ZMod J.n) + 1) + 1 := by
            rw [show (2 : ZMod J.n) = 1 + 1 by norm_num]
            abel
      _ = 0 + 1 := by rw [hprev]
      _ = 1 := zero_add 1
  have hbase := J.consecutive_inter ((J.n - 1 : ℕ) : ZMod J.n)
  rw [hprev, hprev2] at hbase
  rw [Set.disjoint_left]
  intro x hxFirst hxPrev
  have hxEdge0 : x ∈ J.edgeSegment 0 := by
    simpa only [edgeSegment, zero_add] using
      (convex_segment (J.vertex 0) (J.vertex 1)).segment_subset hp'
        (right_mem_segment ℝ _ _) hxFirst
  have hxBase : x ∈ J.edgeSegment ((J.n - 1 : ℕ) : ZMod J.n) ∩
      J.edgeSegment 0 := ⟨hxPrev, hxEdge0⟩
  unfold edgeSegment at hxBase
  rw [hprev] at hxBase
  have hxBase' : x = J.vertex 0 := by
    simpa only [zero_add, hbase, Set.mem_singleton_iff] using hxBase
  exact J.vertex_zero_not_mem_insertZero_first hp hp0 hp1 (hxBase' ▸ hxFirst)

theorem disjoint_insertZero_last_next (J : PolygonalCircle) {p : Plane}
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1) :
    Disjoint (segment ℝ (J.vertex 0) p) (J.edgeSegment 1) := by
  have hp' : p ∈ segment ℝ (J.vertex 0) (J.vertex 1) := by
    simpa only [edgeSegment, zero_add] using hp
  have hbase := J.consecutive_inter 0
  simp only [zero_add] at hbase
  rw [Set.disjoint_left]
  intro x hxLast hxNext
  have hxEdge0 : x ∈ J.edgeSegment 0 := by
    simpa only [edgeSegment, zero_add] using
      (convex_segment (J.vertex 0) (J.vertex 1)).segment_subset
        (left_mem_segment ℝ _ _) hp' hxLast
  have hxBase : x ∈ J.edgeSegment 0 ∩ J.edgeSegment 1 := by
    exact ⟨hxEdge0, hxNext⟩
  unfold edgeSegment at hxBase
  simp only [zero_add, one_add_one_eq_two, hbase, Set.mem_singleton_iff] at hxBase
  exact J.vertex_one_not_mem_insertZero_last hp hp0 hp1 (hxBase ▸ hxLast)

private theorem natCast_eq_natCast_of_lt {n m l : ℕ} [NeZero n]
    (hm : m < n) (hl : l < n) (h : (m : ZMod n) = (l : ZMod n)) : m = l := by
  have hv := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt hm, ZMod.val_natCast_of_lt hl] at hv

private theorem natCast_eq_succ_of_pos_lt {n m l : ℕ} [NeZero n] [Fact (1 < n)]
    (hm0 : 0 < m) (hm : m < n) (hl : l < n)
    (h : (m : ZMod n) = (l : ZMod n) + 1) : m = l + 1 := by
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt hm, ZMod.val_add,
    ZMod.val_natCast_of_lt hl, ZMod.val_one] at hv
  by_cases hln : l + 1 < n
  · rwa [Nat.mod_eq_of_lt hln] at hv
  · have hle : n ≤ l + 1 := Nat.le_of_not_gt hln
    have heq : l + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega

theorem insertZero_first_subset_edge_zero (J : PolygonalCircle) {p : Plane}
    (hp : p ∈ J.edgeSegment 0) :
    segment ℝ p (J.vertex 1) ⊆ J.edgeSegment 0 := by
  have hp' : p ∈ segment ℝ (J.vertex 0) (J.vertex 1) := by
    simpa only [edgeSegment, zero_add] using hp
  intro x hx
  simpa only [edgeSegment, zero_add] using
    (convex_segment (J.vertex 0) (J.vertex 1)).segment_subset hp'
      (right_mem_segment ℝ _ _) hx

theorem insertZero_last_subset_edge_zero (J : PolygonalCircle) {p : Plane}
    (hp : p ∈ J.edgeSegment 0) :
    segment ℝ (J.vertex 0) p ⊆ J.edgeSegment 0 := by
  have hp' : p ∈ segment ℝ (J.vertex 0) (J.vertex 1) := by
    simpa only [edgeSegment, zero_add] using hp
  intro x hx
  simpa only [edgeSegment, zero_add] using
    (convex_segment (J.vertex 0) (J.vertex 1)).segment_subset
      (left_mem_segment ℝ _ _) hp' hx

/-- Splitting edge zero preserves disjointness of every pair of non-adjacent edges. -/
theorem insertZero_nonadjacent_disjoint (J : PolygonalCircle) {p : Plane}
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1)
    (i j : ZMod (J.n + 1)) (hij : i ≠ j) (hprev : i ≠ j + 1)
    (hnext : j ≠ i + 1) :
    J.insertZeroEdgeSegment p i ∩ J.insertZeroEdgeSegment p j = ∅ := by
  letI : Fact (1 < J.n) := ⟨by have := J.three_le; omega⟩
  let m := i.val
  let l := j.val
  have hm : m < J.n + 1 := i.val_lt
  have hl : l < J.n + 1 := j.val_lt
  have hi : (m : ZMod (J.n + 1)) = i := ZMod.natCast_zmod_val i
  have hj : (l : ZMod (J.n + 1)) = j := ZMod.natCast_zmod_val j
  rw [← hi, ← hj] at hij hprev hnext ⊢
  have hmle : m ≤ J.n := by omega
  have hlle : l ≤ J.n := by omega
  have hwrap : (J.n : ZMod (J.n + 1)) + 1 = 0 := by
    calc
      (J.n : ZMod (J.n + 1)) + 1 = ((J.n + 1 : ℕ) : ZMod (J.n + 1)) := by
        rw [Nat.cast_add, Nat.cast_one]
      _ = 0 := ZMod.natCast_self (J.n + 1)
  by_cases hm0 : m = 0
  · rw [hm0] at hij hprev hnext ⊢
    simp only [Nat.cast_zero] at hij hprev hnext ⊢
    by_cases hl0 : l = 0
    · rw [hl0] at hij hprev hnext ⊢
      simp only [Nat.cast_zero] at hij hprev hnext ⊢
      exact (hij rfl).elim
    by_cases hln : l = J.n
    · rw [hln] at hij hprev hnext ⊢
      exact (hprev hwrap.symm).elim
    have hlpos : 0 < l := Nat.pos_of_ne_zero hl0
    have hllt : l < J.n := lt_of_le_of_ne hlle hln
    rw [J.insertZeroEdgeSegment_zero,
      J.insertZeroEdgeSegment_middle p hlpos hllt]
    by_cases hl1 : l = 1
    · rw [hl1] at hnext ⊢
      exact (hnext (by norm_num)).elim
    by_cases hllast : l = J.n - 1
    · rw [hllast]
      exact Set.disjoint_iff_inter_eq_empty.mp
        (J.disjoint_insertZero_first_previous hp hp0 hp1)
    have hOld : J.edgeSegment 0 ∩ J.edgeSegment (l : ZMod J.n) = ∅ := by
      apply J.nonadjacent_disjoint
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_zero, ZMod.val_natCast_of_lt hllt] at hv
        omega
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_zero, ZMod.val_add, ZMod.val_natCast_of_lt hllt,
          ZMod.val_one] at hv
        have hsum : l + 1 < J.n := by omega
        rw [Nat.mod_eq_of_lt hsum] at hv
        omega
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast_of_lt hllt, ZMod.val_add, ZMod.val_zero,
          ZMod.val_one, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < J.n)] at hv
        exact hl1 hv
    rw [Set.eq_empty_iff_forall_notMem]; rintro x ⟨hxFirst, hxOld⟩
    exact Set.eq_empty_iff_forall_notMem.mp hOld x
      ⟨J.insertZero_first_subset_edge_zero hp hxFirst, hxOld⟩
  by_cases hmn : m = J.n
  · rw [hmn] at hij hprev hnext ⊢
    by_cases hl0 : l = 0
    · rw [hl0] at hij hprev hnext ⊢
      simp only [Nat.cast_zero] at hij hprev hnext ⊢
      exact (hnext hwrap.symm).elim
    by_cases hln : l = J.n
    · rw [hln] at hij hprev hnext ⊢
      exact (hij rfl).elim
    have hlpos : 0 < l := Nat.pos_of_ne_zero hl0
    have hllt : l < J.n := lt_of_le_of_ne hlle hln
    rw [J.insertZeroEdgeSegment_last,
      J.insertZeroEdgeSegment_middle p hlpos hllt]
    by_cases hl1 : l = 1
    · rw [hl1]
      rw [Set.inter_comm]
      simpa only [Nat.cast_one] using Set.disjoint_iff_inter_eq_empty.mp
        (J.disjoint_insertZero_last_next hp hp0 hp1).symm
    by_cases hllast : l = J.n - 1
    · have hcast : (l : ZMod (J.n + 1)) + 1 =
          (J.n : ZMod (J.n + 1)) := by
        rw [hllast]
        calc
          ((J.n - 1 : ℕ) : ZMod (J.n + 1)) + 1 =
              ((J.n - 1 + 1 : ℕ) : ZMod (J.n + 1)) := by
                rw [Nat.cast_add, Nat.cast_one]
          _ = (J.n : ℕ) := congrArg (fun q : ℕ => (q : ZMod (J.n + 1)))
            (Nat.sub_add_cancel (by have := J.three_le; omega))
      exact (hprev hcast.symm).elim
    have hOld : J.edgeSegment 0 ∩ J.edgeSegment (l : ZMod J.n) = ∅ := by
      apply J.nonadjacent_disjoint
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_zero, ZMod.val_natCast_of_lt hllt] at hv
        omega
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_zero, ZMod.val_add, ZMod.val_natCast_of_lt hllt,
          ZMod.val_one] at hv
        have hsum : l + 1 < J.n := by omega
        rw [Nat.mod_eq_of_lt hsum] at hv
        omega
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast_of_lt hllt, ZMod.val_add, ZMod.val_zero,
          ZMod.val_one, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < J.n)] at hv
        exact hl1 hv
    rw [Set.eq_empty_iff_forall_notMem]; rintro x ⟨hxLast, hxOld⟩
    exact Set.eq_empty_iff_forall_notMem.mp hOld x
      ⟨J.insertZero_last_subset_edge_zero hp hxLast, hxOld⟩
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hmlt : m < J.n := lt_of_le_of_ne hmle hmn
  rw [J.insertZeroEdgeSegment_middle p hmpos hmlt]
  by_cases hl0 : l = 0
  · rw [hl0] at hij hprev hnext ⊢
    simp only [Nat.cast_zero] at hij hprev hnext ⊢
    rw [J.insertZeroEdgeSegment_zero]
    by_cases hm1 : m = 1
    · rw [hm1] at hprev
      exact (hprev (by norm_num)).elim
    by_cases hmlast : m = J.n - 1
    · rw [hmlast]
      rw [Set.inter_comm]
      exact Set.disjoint_iff_inter_eq_empty.mp
        (J.disjoint_insertZero_first_previous hp hp0 hp1)
    have hOld : J.edgeSegment (m : ZMod J.n) ∩ J.edgeSegment 0 = ∅ := by
      apply J.nonadjacent_disjoint
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast_of_lt hmlt, ZMod.val_zero] at hv
        omega
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast_of_lt hmlt, ZMod.val_add, ZMod.val_zero,
          ZMod.val_one, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < J.n)] at hv
        exact hm1 hv
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_zero, ZMod.val_add, ZMod.val_natCast_of_lt hmlt,
          ZMod.val_one] at hv
        have hsum : m + 1 < J.n := by omega
        rw [Nat.mod_eq_of_lt hsum] at hv
        omega
    rw [Set.eq_empty_iff_forall_notMem]; rintro x ⟨hxOld, hxFirst⟩
    exact Set.eq_empty_iff_forall_notMem.mp hOld x
      ⟨hxOld, J.insertZero_first_subset_edge_zero hp hxFirst⟩
  by_cases hln : l = J.n
  · rw [hln] at hij hprev hnext ⊢
    rw [J.insertZeroEdgeSegment_last]
    by_cases hm1 : m = 1
    · rw [hm1]
      simpa only [Nat.cast_one] using Set.disjoint_iff_inter_eq_empty.mp
        (J.disjoint_insertZero_last_next hp hp0 hp1).symm
    by_cases hmlast : m = J.n - 1
    · have hcast : (m : ZMod (J.n + 1)) + 1 =
          (J.n : ZMod (J.n + 1)) := by
        rw [hmlast]
        calc
          ((J.n - 1 : ℕ) : ZMod (J.n + 1)) + 1 =
              ((J.n - 1 + 1 : ℕ) : ZMod (J.n + 1)) := by
                rw [Nat.cast_add, Nat.cast_one]
          _ = (J.n : ℕ) := congrArg (fun q : ℕ => (q : ZMod (J.n + 1)))
            (Nat.sub_add_cancel (by have := J.three_le; omega))
      exact (hnext hcast.symm).elim
    have hOld : J.edgeSegment (m : ZMod J.n) ∩ J.edgeSegment 0 = ∅ := by
      apply J.nonadjacent_disjoint
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast_of_lt hmlt, ZMod.val_zero] at hv
        omega
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_natCast_of_lt hmlt, ZMod.val_add, ZMod.val_zero,
          ZMod.val_one, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < J.n)] at hv
        exact hm1 hv
      · intro h
        have hv := congrArg ZMod.val h
        rw [ZMod.val_zero, ZMod.val_add, ZMod.val_natCast_of_lt hmlt,
          ZMod.val_one] at hv
        have hsum : m + 1 < J.n := by omega
        rw [Nat.mod_eq_of_lt hsum] at hv
        omega
    rw [Set.eq_empty_iff_forall_notMem]; rintro x ⟨hxOld, hxLast⟩
    exact Set.eq_empty_iff_forall_notMem.mp hOld x
      ⟨hxOld, J.insertZero_last_subset_edge_zero hp hxLast⟩
  have hlpos : 0 < l := Nat.pos_of_ne_zero hl0
  have hllt : l < J.n := lt_of_le_of_ne hlle hln
  rw [J.insertZeroEdgeSegment_middle p hlpos hllt]
  apply J.nonadjacent_disjoint
  · intro h
    have hml := natCast_eq_natCast_of_lt hmlt hllt h
    apply hij
    rw [hml]
  · intro h
    have hml := natCast_eq_succ_of_pos_lt hmpos hmlt hllt h
    apply hprev
    rw [hml, Nat.cast_add, Nat.cast_one]
  · intro h
    have hlm := natCast_eq_succ_of_pos_lt hlpos hllt hmlt h
    apply hnext
    rw [hlm, Nat.cast_add, Nat.cast_one]

/-- A point on a segment splits it into two subsegments whose union is the original segment. -/
theorem segment_split_union {a b p : Plane} (hp : p ∈ segment ℝ a b) :
    segment ℝ a p ∪ segment ℝ p b = segment ℝ a b := by
  apply Set.Subset.antisymm
  · rintro x (hx | hx)
    · exact (convex_segment a b).segment_subset (left_mem_segment ℝ _ _) hp hx
    · exact (convex_segment a b).segment_subset hp (right_mem_segment ℝ _ _) hx
  · intro x hx
    rw [← insert_endpoints_openSegment] at hx
    rcases hx with rfl | rfl | hx
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inr (right_mem_segment ℝ _ _)
    · have hpRange : p ∈ Set.range (AffineMap.lineMap a b : ℝ → Plane) := by
        rw [segment_eq_image_lineMap] at hp
        obtain ⟨c, -, hc⟩ := hp
        exact ⟨c, hc⟩
      rcases openSegment_subset_union a b hpRange hx with rfl | hx | hx
      · exact Or.inl (right_mem_segment ℝ _ _)
      · exact Or.inl (openSegment_subset_segment ℝ _ _ hx)
      · exact Or.inr (openSegment_subset_segment ℝ _ _ hx)

/-- Subdivide edge zero at a non-endpoint.  The cyclic order is
`p, v₁, ..., vₙ₋₁, v₀`. -/
def insertZero (J : PolygonalCircle) (p : Plane) (hp : p ∈ J.edgeSegment 0)
    (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1) : PolygonalCircle where
  n := J.n + 1
  three_le := by have := J.three_le; omega
  vertex := J.insertZeroVertex p
  adjacent_ne := J.insertZeroVertex_adjacent_ne hp0 hp1
  consecutive_inter := by
    intro i
    simpa only [insertZeroEdgeSegment, add_assoc, one_add_one_eq_two] using
      J.insertZero_consecutive_inter hp hp0 hp1 i
  nonadjacent_disjoint := by
    intro i j hij hprev hnext
    simpa only [insertZeroEdgeSegment] using
      J.insertZero_nonadjacent_disjoint hp hp0 hp1 i j hij hprev hnext

@[simp] theorem insertZero_n (J : PolygonalCircle) (p : Plane)
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1) :
    (J.insertZero p hp hp0 hp1).n = J.n + 1 := rfl

@[simp] theorem insertZero_vertex_zero (J : PolygonalCircle) (p : Plane)
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1) :
    (J.insertZero p hp hp0 hp1).vertex 0 = p := by
  exact J.insertZeroVertex_zero p

/-- Inserting a vertex into an edge does not change the polygon carrier. -/
theorem insertZero_carrier (J : PolygonalCircle) (p : Plane) (hp : p ∈ J.edgeSegment 0)
    (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1) :
    (J.insertZero p hp hp0 hp1).carrier = J.carrier := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hi⟩ : ∃ i : ZMod (J.n + 1), x ∈ J.insertZeroEdgeSegment p i :=
      Set.mem_iUnion.mp hx
    let m := i.val
    have hm : m < J.n + 1 := i.val_lt
    have hcast : (m : ZMod (J.n + 1)) = i := ZMod.natCast_zmod_val i
    rw [← hcast] at hi
    change x ∈ J.insertZeroEdgeSegment p (m : ZMod (J.n + 1)) at hi
    by_cases hm0 : m = 0
    · rw [hm0, Nat.cast_zero, J.insertZeroEdgeSegment_zero] at hi
      exact Set.mem_iUnion.mpr ⟨0, J.insertZero_first_subset_edge_zero hp hi⟩
    by_cases hmn : m = J.n
    · rw [hmn, J.insertZeroEdgeSegment_last] at hi
      exact Set.mem_iUnion.mpr ⟨0, J.insertZero_last_subset_edge_zero hp hi⟩
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hmlt : m < J.n := by omega
    rw [J.insertZeroEdgeSegment_middle p hmpos hmlt] at hi
    exact Set.mem_iUnion.mpr ⟨(m : ZMod J.n), hi⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    by_cases hi0 : i = 0
    · subst i
      have hp' : p ∈ segment ℝ (J.vertex 0) (J.vertex 1) := by
        simpa only [edgeSegment, zero_add] using hp
      have hsplit := segment_split_union hp'
      have hi' : x ∈ segment ℝ (J.vertex 0) (J.vertex 1) := by
        simpa only [edgeSegment, zero_add] using hi
      rw [← hsplit] at hi'
      rcases hi' with hi' | hi'
      · refine Set.mem_iUnion.mpr ⟨(J.n : ZMod (J.n + 1)), ?_⟩
        change x ∈ J.insertZeroEdgeSegment p (J.n : ZMod (J.n + 1))
        rwa [J.insertZeroEdgeSegment_last]
      · refine Set.mem_iUnion.mpr ⟨0, ?_⟩
        change x ∈ J.insertZeroEdgeSegment p 0
        rwa [J.insertZeroEdgeSegment_zero]
    · let m := i.val
      have hmpos : 0 < m := Nat.pos_of_ne_zero fun hm0 =>
        hi0 ((ZMod.val_eq_zero i).mp hm0)
      have hmlt : m < J.n := i.val_lt
      refine Set.mem_iUnion.mpr ⟨(m : ZMod (J.n + 1)), ?_⟩
      change x ∈ J.insertZeroEdgeSegment p (m : ZMod (J.n + 1))
      rw [J.insertZeroEdgeSegment_middle p hmpos hmlt]
      rwa [ZMod.natCast_zmod_val i]

/-- Cyclically reindex a polygon so that the old index `a` becomes the new index zero. -/
def rotate (J : PolygonalCircle) (a : ZMod J.n) : PolygonalCircle where
  n := J.n
  three_le := J.three_le
  vertex i := J.vertex (i + a)
  adjacent_ne i := by
    convert J.adjacent_ne (i + a) using 1; ring
  consecutive_inter i := by
    convert J.consecutive_inter (i + a) using 1 <;> ring
  nonadjacent_disjoint i j hij hprev hnext := by
    have h := J.nonadjacent_disjoint (i + a) (j + a)
      (fun h => hij (add_right_cancel h))
      (fun h => hprev (add_right_cancel (by calc
        i + a = j + a + 1 := h
        _ = (j + 1) + a := by ring)))
      (fun h => hnext (add_right_cancel (by calc
        j + a = i + a + 1 := h
        _ = (i + 1) + a := by ring)))
    convert h using 1; ring

@[simp] theorem rotate_n (J : PolygonalCircle) (a : ZMod J.n) :
    (J.rotate a).n = J.n := rfl

@[simp] theorem rotate_vertex (J : PolygonalCircle) (a i : ZMod J.n) :
    (J.rotate a).vertex i = J.vertex (i + a) := rfl

theorem rotate_edgeSegment (J : PolygonalCircle) (a i : ZMod J.n) :
    (J.rotate a).edgeSegment i = J.edgeSegment (i + a) := by
  unfold edgeSegment
  show segment ℝ (J.vertex (i + a)) (J.vertex (i + 1 + a)) =
    segment ℝ (J.vertex (i + a)) (J.vertex (i + a + 1))
  congr 2
  exact add_right_comm i (1 : ZMod J.n) a

theorem rotate_carrier (J : PolygonalCircle) (a : ZMod J.n) :
    (J.rotate a).carrier = J.carrier := by
  change (⋃ i : ZMod J.n, (J.rotate a).edgeSegment i) =
    ⋃ i : ZMod J.n, J.edgeSegment i
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    exact Set.mem_iUnion.mpr ⟨i + a, by rwa [J.rotate_edgeSegment a i] at hi⟩
  · intro p hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    refine Set.mem_iUnion.mpr ⟨i - a, ?_⟩
    rw [J.rotate_edgeSegment]
    simpa using hi

/-- The bounded and unbounded complementary components depend only on the polygon carrier, not
on its cyclic indexing. -/
theorem regions_eq_of_carrier_eq {J J' : PolygonalCircle}
    (hcarrier : J.carrier = J'.carrier) :
    J.interiorRegion = J'.interiorRegion ∧ J.exteriorRegion = J'.exteriorRegion := by
  have hsplitJ' : J'.exteriorRegion ⊆ J.interiorRegion ∪ J.exteriorRegion := by
    intro p hp
    have hpCompl : p ∈ J'.carrierᶜ := by
      rw [← J'.interior_union_exterior]
      exact Or.inr hp
    have hpCompl' : p ∈ J.carrierᶜ := by rwa [hcarrier]
    rwa [← J.interior_union_exterior] at hpCompl'
  have hmeetExterior : (J'.exteriorRegion ∩ J.exteriorRegion).Nonempty := by
    by_contra h
    have hsubsetInterior : J'.exteriorRegion ⊆ J.interiorRegion := by
      intro p hp
      rcases hsplitJ' hp with hpInt | hpExt
      · exact hpInt
      · exact False.elim <| h ⟨p, hp, hpExt⟩
    exact J'.not_isBounded_exteriorRegion
      (J.isBounded_interiorRegion.subset hsubsetInterior)
  have hExteriorSub : J'.exteriorRegion ⊆ J.exteriorRegion :=
    J'.isConnected_exteriorRegion.isPreconnected.subset_right_of_subset_union
      J.isOpen_interiorRegion J.isOpen_exteriorRegion J.disjoint_interior_exterior
      hsplitJ' hmeetExterior
  have hsplitJ : J.exteriorRegion ⊆ J'.interiorRegion ∪ J'.exteriorRegion := by
    intro p hp
    have hpCompl : p ∈ J.carrierᶜ := by
      rw [← J.interior_union_exterior]
      exact Or.inr hp
    have hpCompl' : p ∈ J'.carrierᶜ := by rwa [← hcarrier]
    rwa [← J'.interior_union_exterior] at hpCompl'
  have hmeetExterior' : (J.exteriorRegion ∩ J'.exteriorRegion).Nonempty := by
    obtain ⟨p, hpJ', hpJ⟩ := hmeetExterior
    exact ⟨p, hpJ, hpJ'⟩
  have hExteriorSub' : J.exteriorRegion ⊆ J'.exteriorRegion :=
    J.isConnected_exteriorRegion.isPreconnected.subset_right_of_subset_union
      J'.isOpen_interiorRegion J'.isOpen_exteriorRegion J'.disjoint_interior_exterior
      hsplitJ hmeetExterior'
  have hExterior : J.exteriorRegion = J'.exteriorRegion :=
    Set.Subset.antisymm hExteriorSub' hExteriorSub
  refine ⟨?_, hExterior⟩
  have hcomplements : J.interiorRegion ∪ J.exteriorRegion =
      J'.interiorRegion ∪ J'.exteriorRegion := by
    rw [J.interior_union_exterior, J'.interior_union_exterior, hcarrier]
  apply Set.Subset.antisymm
  · intro p hp
    have hpUnion : p ∈ J'.interiorRegion ∪ J'.exteriorRegion := by
      rw [← hcomplements]
      exact Or.inl hp
    rcases hpUnion with hpInt | hpExt
    · exact hpInt
    · exact False.elim <| Set.disjoint_left.mp J.disjoint_interior_exterior
        hp (hExterior ▸ hpExt)
  · intro p hp
    have hpUnion : p ∈ J.interiorRegion ∪ J.exteriorRegion := by
      rw [hcomplements]
      exact Or.inl hp
    rcases hpUnion with hpInt | hpExt
    · exact hpInt
    · exact False.elim <| Set.disjoint_left.mp J'.disjoint_interior_exterior
        hp (hExterior ▸ hpExt)

theorem rotate_interiorRegion (J : PolygonalCircle) (a : ZMod J.n) :
    (J.rotate a).interiorRegion = J.interiorRegion :=
  (regions_eq_of_carrier_eq (J.rotate_carrier a)).1

theorem rotate_exteriorRegion (J : PolygonalCircle) (a : ZMod J.n) :
    (J.rotate a).exteriorRegion = J.exteriorRegion :=
  (regions_eq_of_carrier_eq (J.rotate_carrier a)).2

theorem insertZero_interiorRegion (J : PolygonalCircle) (p : Plane)
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1) :
    (J.insertZero p hp hp0 hp1).interiorRegion = J.interiorRegion :=
  (regions_eq_of_carrier_eq (J.insertZero_carrier p hp hp0 hp1)).1

theorem insertZero_exteriorRegion (J : PolygonalCircle) (p : Plane)
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1) :
    (J.insertZero p hp hp0 hp1).exteriorRegion = J.exteriorRegion :=
  (regions_eq_of_carrier_eq (J.insertZero_carrier p hp hp0 hp1)).2

/-- A point is a vertex of one of the cyclic presentations of a polygon. -/
def IsVertexPoint (J : PolygonalCircle) (p : Plane) : Prop :=
  ∃ i, J.vertex i = p

/-- A point known to be a polygon vertex lies on an edge exactly when it is one of that edge's
two endpoints. -/
theorem IsVertexPoint.mem_edgeSegment_iff {J : PolygonalCircle} {p : Plane}
    (hp : J.IsVertexPoint p) (i : ZMod J.n) :
    p ∈ J.edgeSegment i ↔ p = J.vertex i ∨ p = J.vertex (i + 1) := by
  obtain ⟨j, rfl⟩ := hp
  rw [J.vertex_mem_edgeSegment_iff j i]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (h | h)
    · exact Or.inl (J.vertex_injective h)
    · exact Or.inr (J.vertex_injective h)

theorem isVertexPoint_rotate_iff (J : PolygonalCircle) (a : ZMod J.n) (p : Plane) :
    (J.rotate a).IsVertexPoint p ↔ J.IsVertexPoint p := by
  change (∃ i : ZMod J.n, J.vertex (i + a) = p) ↔
    ∃ i : ZMod J.n, J.vertex i = p
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i + a, hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨i - a, ?_⟩
    simpa only [rotate_vertex, sub_add_cancel] using hi

theorem isVertexPoint_insertZero (J : PolygonalCircle) (p : Plane)
    (hp : p ∈ J.edgeSegment 0) (hp0 : p ≠ J.vertex 0) (hp1 : p ≠ J.vertex 1)
    {q : Plane} (hq : J.IsVertexPoint q) :
    (J.insertZero p hp hp0 hp1).IsVertexPoint q := by
  obtain ⟨i, rfl⟩ := hq
  by_cases hi0 : i = 0
  · subst i
    refine ⟨(J.n : ZMod (J.n + 1)), ?_⟩
    change J.insertZeroVertex p (J.n : ZMod (J.n + 1)) = J.vertex 0
    rw [J.insertZeroVertex_natCast p (by have := J.three_le; omega) (by omega)]
    exact congrArg J.vertex (ZMod.natCast_self J.n)
  · let m := i.val
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun hm =>
      hi0 ((ZMod.val_eq_zero i).mp hm)
    have hmlt : m < J.n := i.val_lt
    refine ⟨(m : ZMod (J.n + 1)), ?_⟩
    change J.insertZeroVertex p (m : ZMod (J.n + 1)) = J.vertex i
    rw [J.insertZeroVertex_natCast p hm0 (by omega), ZMod.natCast_zmod_val i]

/-- Insert a boundary point as vertex zero without changing the carrier, while retaining every
old vertex.  Endpoint cases need only a cyclic reindexing; an interior edge point uses
`insertZero`. -/
theorem exists_refinement_vertex_zero (J : PolygonalCircle) {p : Plane}
    (hp : p ∈ J.carrier) :
    ∃ J' : PolygonalCircle,
      J'.carrier = J.carrier ∧ J'.vertex 0 = p ∧
        ∀ q, J.IsVertexPoint q → J'.IsVertexPoint q := by
  simp only [carrier, Set.mem_iUnion] at hp
  obtain ⟨i, hi⟩ := hp
  let R := J.rotate i
  have hiR : p ∈ R.edgeSegment 0 := by
    change p ∈ (J.rotate i).edgeSegment (0 : ZMod J.n)
    rw [J.rotate_edgeSegment]
    simpa only [zero_add] using hi
  by_cases hp0 : p = R.vertex 0
  · refine ⟨R, J.rotate_carrier i, hp0.symm, ?_⟩
    intro q hq
    exact (J.isVertexPoint_rotate_iff i q).mpr hq
  by_cases hp1 : p = R.vertex 1
  · let R' := R.rotate 1
    refine ⟨R', ?_, ?_, ?_⟩
    · exact (R.rotate_carrier 1).trans (J.rotate_carrier i)
    · dsimp [R']
      change R.vertex ((0 : ZMod R.n) + 1) = p
      rw [zero_add]
      exact hp1.symm
    · intro q hq
      exact (R.isVertexPoint_rotate_iff 1 q).mpr
        ((J.isVertexPoint_rotate_iff i q).mpr hq)
  · let J' := R.insertZero p hiR hp0 hp1
    refine ⟨J', (R.insertZero_carrier p hiR hp0 hp1).trans (J.rotate_carrier i), ?_, ?_⟩
    · exact R.insertZero_vertex_zero p hiR hp0 hp1
    · intro q hq
      exact R.isVertexPoint_insertZero p hiR hp0 hp1
        ((J.isVertexPoint_rotate_iff i q).mpr hq)

/-- Refine a polygonal presentation so that every point of a prescribed finite subset of its
carrier is a polygon vertex, without changing the carrier. -/
theorem exists_refinement_vertices (J : PolygonalCircle) (F : Finset Plane)
    (hF : ∀ p ∈ F, p ∈ J.carrier) :
    ∃ J' : PolygonalCircle, J'.carrier = J.carrier ∧
      ∀ p ∈ F, J'.IsVertexPoint p := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      exact ⟨J, rfl, by simp⟩
  | @insert p F hpF ih =>
      obtain ⟨K, hKcarrier, hKF⟩ := ih (fun q hq => hF q (Finset.mem_insert_of_mem hq))
      have hpK : p ∈ K.carrier := by
        rw [hKcarrier]
        exact hF p (Finset.mem_insert_self p F)
      obtain ⟨K', hK'carrier, hK'p, hkeep⟩ := K.exists_refinement_vertex_zero hpK
      refine ⟨K', hK'carrier.trans hKcarrier, ?_⟩
      intro q hq
      rw [Finset.mem_insert] at hq
      rcases hq with rfl | hq
      · exact ⟨0, hK'p⟩
      · exact hkeep q (hKF q hq)

/-- A straight crosscut of a polygonal disk: its endpoints lie on the polygon, while every
other point of the segment lies in the polygon interior. -/
structure ProperChord (J : PolygonalCircle) where
  /-- The `P` declaration. -/
  P : Plane
  /-- The `Q` declaration. -/
  Q : Plane
  ne : P ≠ Q
  P_mem : P ∈ J.carrier
  Q_mem : Q ∈ J.carrier
  interior_subset : segment ℝ P Q \ {P, Q} ⊆ J.interiorRegion

namespace ProperChord

variable {J : PolygonalCircle} (C : J.ProperChord)

/-- Transport a proper chord across a different cyclic polygon presentation with the same
carrier. -/
def congrCarrier {J' : PolygonalCircle} (hcarrier : J'.carrier = J.carrier) :
    J'.ProperChord where
  P := C.P
  Q := C.Q
  ne := C.ne
  P_mem := by rw [hcarrier]; exact C.P_mem
  Q_mem := by rw [hcarrier]; exact C.Q_mem
  interior_subset := by
    rw [(regions_eq_of_carrier_eq hcarrier).1]
    exact C.interior_subset

/-- Reindexing the boundary polygon does not change a proper chord. -/
def rotate (a : ZMod J.n) : (J.rotate a).ProperChord where
  P := C.P
  Q := C.Q
  ne := C.ne
  P_mem := by rw [J.rotate_carrier]; exact C.P_mem
  Q_mem := by rw [J.rotate_carrier]; exact C.Q_mem
  interior_subset := by
    rw [J.rotate_interiorRegion]
    exact C.interior_subset

/-- The chord meets the original polygon precisely at its endpoints. -/
theorem segment_inter_carrier :
    segment ℝ C.P C.Q ∩ J.carrier = {C.P, C.Q} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxSegment, hxCarrier⟩
    by_contra hxEndpoints
    have hxInterior := C.interior_subset ⟨hxSegment, hxEndpoints⟩
    have hxCompl : x ∈ J.carrierᶜ := by
      rw [← J.interior_union_exterior]
      exact Or.inl hxInterior
    exact hxCompl hxCarrier
  · intro x hx
    rcases hx with rfl | rfl
    · exact ⟨left_mem_segment ℝ _ _, C.P_mem⟩
    · exact ⟨right_mem_segment ℝ _ _, C.Q_mem⟩

theorem interior_nonempty :
    (segment ℝ C.P C.Q \ {C.P, C.Q}).Nonempty := by
  refine ⟨midpoint ℝ C.P C.Q, midpoint_mem_segment C.P C.Q, ?_⟩
  intro h
  rcases h with h | h
  · exact C.ne ((midpoint_eq_left_iff (R := ℝ)).mp h)
  · exact C.ne ((midpoint_eq_right_iff (R := ℝ)).mp h)

/-- Each endpoint of a proper chord lies on a concrete polygon edge. -/
theorem exists_endpoint_edges :
    ∃ i j : ZMod J.n, C.P ∈ J.edgeSegment i ∧ C.Q ∈ J.edgeSegment j := by
  have hP := C.P_mem
  have hQ := C.Q_mem
  unfold PolygonalCircle.carrier at hP hQ
  simp only [Set.mem_iUnion] at hP hQ
  obtain ⟨i, hi⟩ := hP
  obtain ⟨j, hj⟩ := hQ
  exact ⟨i, j, hi, hj⟩

/-- The endpoints of a proper chord cannot lie on one polygon edge. -/
theorem endpoint_edges_ne {i j : ZMod J.n} (hi : C.P ∈ J.edgeSegment i)
    (hj : C.Q ∈ J.edgeSegment j) : i ≠ j := by
  intro hij
  subst j
  let m := midpoint ℝ C.P C.Q
  have hmSegment : m ∈ segment ℝ C.P C.Q := midpoint_mem_segment C.P C.Q
  have hmEndpoints : m ∉ ({C.P, C.Q} : Set Plane) := by
    intro hm
    rcases hm with hm | hm
    · exact C.ne ((midpoint_eq_left_iff (R := ℝ)).mp hm)
    · exact C.ne ((midpoint_eq_right_iff (R := ℝ)).mp hm)
  have hmInterior : m ∈ J.interiorRegion :=
    C.interior_subset ⟨hmSegment, hmEndpoints⟩
  have hmEdge : m ∈ J.edgeSegment i := by
    exact (convex_segment (𝕜 := ℝ) (J.vertex i) (J.vertex (i + 1))).segment_subset
      hi hj hmSegment
  have hmCarrier : m ∈ J.carrier := J.edgeSegment_subset_carrier i hmEdge
  have hmCompl : m ∈ J.carrierᶜ := by
    rw [← J.interior_union_exterior]
    exact Or.inl hmInterior
  exact hmCompl hmCarrier

/-- Normalize a proper chord so that its first endpoint lies on edge zero and its second
endpoint lies on an edge with a positive ordinary index. -/
theorem exists_rotated_endpoint_edges :
    ∃ a : ZMod J.n, ∃ k : ℕ, 0 < k ∧ k < J.n ∧
      C.P ∈ (J.rotate a).edgeSegment 0 ∧
      C.Q ∈ (J.rotate a).edgeSegment (k : ZMod J.n) := by
  obtain ⟨i, j, hi, hj⟩ := C.exists_endpoint_edges
  let d : ZMod J.n := j - i
  have hd : d ≠ 0 := by
    intro hd
    apply C.endpoint_edges_ne hi hj
    have : j = i := sub_eq_zero.mp hd
    exact this.symm
  refine ⟨i, d.val, ?_, d.val_lt, ?_, ?_⟩
  · exact Nat.pos_of_ne_zero fun h => hd (d.val_eq_zero.mp h)
  · erw [J.rotate_edgeSegment]
    convert hi using 1
    exact congrArg J.edgeSegment (zero_add i)
  · erw [J.rotate_edgeSegment]
    have hcast : (d.val : ZMod J.n) = d := ZMod.natCast_zmod_val d
    rw [hcast]
    simpa [d] using hj

/-- After subdividing boundary edges and cyclically reindexing, both chord endpoints are
vertices, with the first at index zero and the second at a strictly positive ordinary index. -/
theorem exists_vertex_normalization :
    ∃ J' : PolygonalCircle, ∃ k : ℕ,
      2 ≤ k ∧ k + 1 < J'.n ∧ J'.carrier = J.carrier ∧
        J'.vertex 0 = C.P ∧ J'.vertex (k : ZMod J'.n) = C.Q ∧
          ∃ C' : J'.ProperChord, C'.P = C.P ∧ C'.Q = C.Q := by
  obtain ⟨JP, hJPcarrier, hJPP, -⟩ :=
    J.exists_refinement_vertex_zero C.P_mem
  let CP : JP.ProperChord := C.congrCarrier hJPcarrier
  obtain ⟨JQ, hJQcarrier, hJQQ, hkeep⟩ :=
    JP.exists_refinement_vertex_zero CP.Q_mem
  have hPVertex : JQ.IsVertexPoint C.P := by
    apply hkeep C.P
    exact ⟨0, hJPP⟩
  obtain ⟨i, hiP⟩ := hPVertex
  have hi0 : i ≠ 0 := by
    intro hi0
    subst i
    apply C.ne
    calc
      C.P = JQ.vertex 0 := hiP.symm
      _ = C.Q := hJQQ
  let R := JQ.rotate i
  let d : ZMod JQ.n := -i
  have hd0 : d ≠ 0 := by
    intro hd
    apply hi0
    have : -d = i := by simp [d]
    rw [hd] at this
    simpa using this.symm
  have hRcarrier : R.carrier = J.carrier := by
    exact (JQ.rotate_carrier i).trans (hJQcarrier.trans hJPcarrier)
  have hRzero : R.vertex 0 = C.P := by
    change JQ.vertex ((0 : ZMod JQ.n) + i) = C.P
    simpa only [zero_add] using hiP
  have hRk : R.vertex (d.val : ZMod R.n) = C.Q := by
    have hdcast : (d.val : ZMod JQ.n) = d := ZMod.natCast_zmod_val d
    change JQ.vertex ((d.val : ZMod JQ.n) + i) = C.Q
    rw [hdcast]
    simp only [d, neg_add_cancel]
    exact hJQQ
  let CR : R.ProperChord := C.congrCarrier hRcarrier
  have hk1 : d.val ≠ 1 := by
    intro hk1
    have hPedge : CR.P ∈ R.edgeSegment 0 := by
      change C.P ∈ R.edgeSegment 0
      rw [← hRzero]
      exact left_mem_segment ℝ _ _
    have hQedge : CR.Q ∈ R.edgeSegment 0 := by
      change C.Q ∈ R.edgeSegment 0
      rw [← hRk, hk1]
      unfold edgeSegment
      simpa only [Nat.cast_one, zero_add] using
        right_mem_segment ℝ (R.vertex 0) (R.vertex 1)
    exact (CR.endpoint_edges_ne hPedge hQedge) rfl
  have hklast : d.val + 1 ≠ JQ.n := by
    intro hlast
    change d.val + 1 = R.n at hlast
    have hQedge : CR.Q ∈ R.edgeSegment (d.val : ZMod R.n) := by
      change C.Q ∈ R.edgeSegment (d.val : ZMod R.n)
      rw [← hRk]
      exact left_mem_segment ℝ _ _
    have hsucc : (d.val : ZMod R.n) + 1 = 0 := by
      calc
        (d.val : ZMod R.n) + 1 = ((d.val + 1 : ℕ) : ZMod R.n) := by
          rw [Nat.cast_add, Nat.cast_one]
        _ = (R.n : ℕ) := by rw [hlast]
        _ = 0 := ZMod.natCast_self R.n
    have hPedge : CR.P ∈ R.edgeSegment (d.val : ZMod R.n) := by
      change C.P ∈ R.edgeSegment (d.val : ZMod R.n)
      rw [← hRzero]
      unfold edgeSegment
      rw [hsucc]
      exact right_mem_segment ℝ _ _
    exact (CR.endpoint_edges_ne hPedge hQedge) rfl
  refine ⟨R, d.val, ?_, ?_, hRcarrier, hRzero, hRk, CR, rfl, rfl⟩
  · have hdpos := Nat.pos_of_ne_zero fun hdval => hd0 ((ZMod.val_eq_zero d).mp hdval)
    omega
  · have := d.val_lt
    change d.val + 1 < JQ.n
    omega

/-- Reverse the orientation of a proper chord. -/
def symm : J.ProperChord where
  P := C.Q
  Q := C.P
  ne := C.ne.symm
  P_mem := C.Q_mem
  Q_mem := C.P_mem
  interior_subset := by
    rw [segment_symm]
    simpa only [Set.pair_comm] using C.interior_subset

/-- Vertex sequence for the polygon consisting of vertices `0,...,k` and the closing chord. -/
def forwardCutVertex (k : ℕ) : ZMod (k + 1) → Plane :=
  fun i => J.vertex (i.val : ZMod J.n)

theorem forwardCutVertex_natCast {k m : ℕ} (hm : m < k + 1) :
    forwardCutVertex (J := J) k (m : ZMod (k + 1)) = J.vertex (m : ZMod J.n) := by
  unfold forwardCutVertex
  rw [ZMod.val_natCast_of_lt hm]

theorem edgeBeforeChord_inter_chord {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    J.edgeSegment ((k - 1 : ℕ) : ZMod J.n) ∩ segment ℝ C.Q C.P = {C.Q} := by
  letI : Fact (1 < J.n) := ⟨by omega⟩
  have hkpos : 0 < k := by omega
  have hkmem : C.Q ∈ J.edgeSegment ((k - 1 : ℕ) : ZMod J.n) := by
    rw [← hQ]
    apply (J.vertex_mem_edgeSegment_iff (k : ZMod J.n)
      ((k - 1 : ℕ) : ZMod J.n)).mpr
    right
    calc
      (k : ZMod J.n) = ((k - 1 + 1 : ℕ) : ZMod J.n) :=
        congrArg (fun q : ℕ => (q : ZMod J.n)) (by omega)
      _ = ((k - 1 : ℕ) : ZMod J.n) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]
  have hPnot : C.P ∉ J.edgeSegment ((k - 1 : ℕ) : ZMod J.n) := by
    rw [← hP]
    intro hmem
    rcases (J.vertex_mem_edgeSegment_iff (0 : ZMod J.n)
      ((k - 1 : ℕ) : ZMod J.n)).mp hmem with h | h
    · have hv := congrArg ZMod.val h
      rw [ZMod.val_zero, ZMod.val_natCast_of_lt (by omega : k - 1 < J.n)] at hv
      omega
    · have hv := congrArg ZMod.val h
      rw [ZMod.val_zero, ZMod.val_add,
        ZMod.val_natCast_of_lt (by omega : k - 1 < J.n), ZMod.val_one] at hv
      rw [Nat.mod_eq_of_lt (by omega : k - 1 + 1 < J.n)] at hv
      omega
  apply Set.Subset.antisymm
  · rintro x ⟨hxEdge, hxChord⟩
    have hxCarrier : x ∈ J.carrier := J.edgeSegment_subset_carrier _ hxEdge
    have hx : x ∈ segment ℝ C.P C.Q ∩ J.carrier := by
      rw [segment_symm]
      exact ⟨hxChord, hxCarrier⟩
    rw [C.segment_inter_carrier] at hx
    rcases hx with rfl | rfl
    · exact (hPnot hxEdge).elim
    · exact Set.mem_singleton _
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨hkmem, left_mem_segment ℝ _ _⟩

theorem chord_inter_firstEdge {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    segment ℝ C.Q C.P ∩ J.edgeSegment 0 = {C.P} := by
  letI : Fact (1 < J.n) := ⟨by omega⟩
  have hQnot : C.Q ∉ J.edgeSegment 0 := by
    rw [← hQ]
    intro hmem
    rcases (J.vertex_mem_edgeSegment_iff (k : ZMod J.n) 0).mp hmem with h | h
    · have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt (by omega : k < J.n), ZMod.val_zero] at hv
      omega
    · have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt (by omega : k < J.n), ZMod.val_add,
        ZMod.val_zero, ZMod.val_one, Nat.zero_add,
        Nat.mod_eq_of_lt (by omega : 1 < J.n)] at hv
      omega
  have hPmem : C.P ∈ J.edgeSegment 0 := by
    rw [← hP]
    exact left_mem_segment ℝ _ _
  apply Set.Subset.antisymm
  · rintro x ⟨hxChord, hxEdge⟩
    have hxCarrier : x ∈ J.carrier := J.edgeSegment_subset_carrier _ hxEdge
    have hx : x ∈ segment ℝ C.P C.Q ∩ J.carrier := by
      rw [segment_symm]
      exact ⟨hxChord, hxCarrier⟩
    rw [C.segment_inter_carrier] at hx
    rcases hx with rfl | rfl
    · exact Set.mem_singleton _
    · exact (hQnot hxEdge).elim
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨right_mem_segment ℝ _ _, hPmem⟩

theorem chord_disjoint_middleEdge {k m : ℕ} (hm0 : 0 < m) (hmk : m + 1 < k)
    (hk : k < J.n) (hP : J.vertex 0 = C.P)
    (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    Disjoint (segment ℝ C.Q C.P) (J.edgeSegment (m : ZMod J.n)) := by
  letI : Fact (1 < J.n) := ⟨by omega⟩
  have hPnot : C.P ∉ J.edgeSegment (m : ZMod J.n) := by
    rw [← hP]
    intro hmem
    rcases (J.vertex_mem_edgeSegment_iff (0 : ZMod J.n) (m : ZMod J.n)).mp hmem with h | h
    · have hv := congrArg ZMod.val h
      rw [ZMod.val_zero, ZMod.val_natCast_of_lt (by omega : m < J.n)] at hv
      omega
    · have hv := congrArg ZMod.val h
      rw [ZMod.val_zero, ZMod.val_add, ZMod.val_natCast_of_lt (by omega : m < J.n),
        ZMod.val_one, Nat.mod_eq_of_lt (by omega : m + 1 < J.n)] at hv
      omega
  have hQnot : C.Q ∉ J.edgeSegment (m : ZMod J.n) := by
    rw [← hQ]
    intro hmem
    rcases (J.vertex_mem_edgeSegment_iff (k : ZMod J.n) (m : ZMod J.n)).mp hmem with h | h
    · have := natCast_eq_natCast_of_lt hk (by omega : m < J.n) h
      omega
    · have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt hk, ZMod.val_add,
        ZMod.val_natCast_of_lt (by omega : m < J.n), ZMod.val_one,
        Nat.mod_eq_of_lt (by omega : m + 1 < J.n)] at hv
      omega
  rw [Set.disjoint_left]
  intro x hxChord hxEdge
  have hxCarrier : x ∈ J.carrier := J.edgeSegment_subset_carrier _ hxEdge
  have hx : x ∈ segment ℝ C.P C.Q ∩ J.carrier := by
    rw [segment_symm]
    exact ⟨hxChord, hxCarrier⟩
  rw [C.segment_inter_carrier] at hx
  exact hx.elim (fun h => hPnot (h ▸ hxEdge)) (fun h => hQnot (h ▸ hxEdge))

/-- The `forwardCutEdgeSegment` declaration. -/
def forwardCutEdgeSegment (k : ℕ) (i : ZMod (k + 1)) : Set Plane :=
  segment ℝ (forwardCutVertex (J := J) k i)
    (forwardCutVertex (J := J) k (i + 1))

theorem forwardCutEdgeSegment_of_lt {k m : ℕ} (hm : m < k) :
    forwardCutEdgeSegment (J := J) k (m : ZMod (k + 1)) =
      J.edgeSegment (m : ZMod J.n) := by
  unfold forwardCutEdgeSegment edgeSegment
  rw [forwardCutVertex_natCast (J := J) (by omega)]
  have hsucc : (m : ZMod (k + 1)) + 1 = (m + 1 : ℕ) := by
    rw [Nat.cast_add, Nat.cast_one]
  rw [hsucc, forwardCutVertex_natCast (J := J) (by omega)]
  congr 2
  rw [Nat.cast_add, Nat.cast_one]

theorem forwardCutEdgeSegment_last {k : ℕ} (_ : k < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    forwardCutEdgeSegment (J := J) k (k : ZMod (k + 1)) = segment ℝ C.Q C.P := by
  unfold forwardCutEdgeSegment
  rw [forwardCutVertex_natCast (J := J) (by omega), hQ]
  have hwrap : (k : ZMod (k + 1)) + 1 = 0 := by
    calc
      (k : ZMod (k + 1)) + 1 = ((k + 1 : ℕ) : ZMod (k + 1)) := by
        rw [Nat.cast_add, Nat.cast_one]
      _ = 0 := ZMod.natCast_self (k + 1)
  rw [hwrap]
  unfold forwardCutVertex
  rw [ZMod.val_zero]
  simp only [Nat.cast_zero]
  rw [hP]

theorem forwardCutVertex_adjacent_ne {k : ℕ} (_ : 2 ≤ k) (_ : k < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q)
    (i : ZMod (k + 1)) :
    forwardCutVertex (J := J) k i ≠ forwardCutVertex (J := J) k (i + 1) := by
  let m := i.val
  have hm : m < k + 1 := i.val_lt
  have hcast : (m : ZMod (k + 1)) = i := ZMod.natCast_zmod_val i
  rw [← hcast]
  by_cases hmk : m = k
  · rw [hmk, forwardCutVertex_natCast (J := J) (by omega), hQ]
    have hwrap : (k : ZMod (k + 1)) + 1 = 0 := by
      calc
        (k : ZMod (k + 1)) + 1 = ((k + 1 : ℕ) : ZMod (k + 1)) := by
          rw [Nat.cast_add, Nat.cast_one]
        _ = 0 := ZMod.natCast_self (k + 1)
    rw [hwrap]
    unfold forwardCutVertex
    rw [ZMod.val_zero]
    simp only [Nat.cast_zero]
    rw [hP]
    exact C.ne.symm
  · have hmlt : m < k := by omega
    rw [forwardCutVertex_natCast (J := J) (by omega)]
    have hsucc : (m : ZMod (k + 1)) + 1 = (m + 1 : ℕ) := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [hsucc, forwardCutVertex_natCast (J := J) (by omega)]
    simpa only [Nat.cast_add, Nat.cast_one] using J.adjacent_ne (m : ZMod J.n)

theorem forwardCut_consecutive_inter {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q)
    (i : ZMod (k + 1)) :
    forwardCutEdgeSegment (J := J) k i ∩
      forwardCutEdgeSegment (J := J) k (i + 1) =
        {forwardCutVertex (J := J) k (i + 1)} := by
  letI : Fact (1 < k + 1) := ⟨by omega⟩
  let m := i.val
  have hm : m < k + 1 := i.val_lt
  have hcast : (m : ZMod (k + 1)) = i := ZMod.natCast_zmod_val i
  rw [← hcast]
  by_cases hmk : m = k
  · rw [hmk, C.forwardCutEdgeSegment_last (by omega) hP hQ]
    have hwrap : (k : ZMod (k + 1)) + 1 = 0 := by
      calc
        (k : ZMod (k + 1)) + 1 = ((k + 1 : ℕ) : ZMod (k + 1)) := by
          rw [Nat.cast_add, Nat.cast_one]
        _ = 0 := ZMod.natCast_self (k + 1)
    rw [hwrap]
    unfold forwardCutEdgeSegment forwardCutVertex
    simp only [zero_add, ZMod.val_zero, ZMod.val_one]
    simp only [Nat.cast_zero, Nat.cast_one]
    rw [hP]
    have hfirst := C.chord_inter_firstEdge hk2 hk hP hQ
    unfold edgeSegment at hfirst
    simp only [zero_add] at hfirst
    rw [hP] at hfirst
    exact hfirst
  have hmlt : m < k := by omega
  by_cases hmnext : m + 1 = k
  · rw [forwardCutEdgeSegment_of_lt (J := J) hmlt]
    have hsucc : (m : ZMod (k + 1)) + 1 = (k : ZMod (k + 1)) := by
      calc
        (m : ZMod (k + 1)) + 1 = (m + 1 : ℕ) := by
          rw [Nat.cast_add, Nat.cast_one]
        _ = (k : ℕ) := by rw [hmnext]
    rw [hsucc, C.forwardCutEdgeSegment_last (by omega) hP hQ]
    rw [forwardCutVertex_natCast (J := J) (by omega), hQ]
    have hmEq : m = k - 1 := by omega
    rw [hmEq]
    exact C.edgeBeforeChord_inter_chord hk2 hk hP hQ
  · have hm2 : m + 1 < k := by omega
    rw [forwardCutEdgeSegment_of_lt (J := J) hmlt]
    have hsucc : (m : ZMod (k + 1)) + 1 = (m + 1 : ℕ) := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [hsucc, forwardCutEdgeSegment_of_lt (J := J) hm2]
    rw [forwardCutVertex_natCast (J := J) (by omega)]
    simpa only [edgeSegment, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using J.consecutive_inter (m : ZMod J.n)

theorem forwardCut_nonadjacent_disjoint {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q)
    (i j : ZMod (k + 1)) (hij : i ≠ j) (hprev : i ≠ j + 1)
    (hnext : j ≠ i + 1) :
    forwardCutEdgeSegment (J := J) k i ∩
      forwardCutEdgeSegment (J := J) k j = ∅ := by
  letI : Fact (1 < J.n) := ⟨by omega⟩
  let m := i.val
  let l := j.val
  have hm : m < k + 1 := i.val_lt
  have hl : l < k + 1 := j.val_lt
  have hi : (m : ZMod (k + 1)) = i := ZMod.natCast_zmod_val i
  have hj : (l : ZMod (k + 1)) = j := ZMod.natCast_zmod_val j
  rw [← hi, ← hj] at hij hprev hnext ⊢
  have hmle : m ≤ k := by omega
  have hlle : l ≤ k := by omega
  have hwrap : (k : ZMod (k + 1)) + 1 = 0 := by
    calc
      (k : ZMod (k + 1)) + 1 = ((k + 1 : ℕ) : ZMod (k + 1)) := by
        rw [Nat.cast_add, Nat.cast_one]
      _ = 0 := ZMod.natCast_self (k + 1)
  by_cases hmk : m = k
  · rw [hmk] at hij hprev hnext ⊢
    by_cases hlk : l = k
    · rw [hlk] at hij
      exact (hij rfl).elim
    have hllt : l < k := by omega
    by_cases hl0 : l = 0
    · rw [hl0, Nat.cast_zero] at hnext
      exact (hnext hwrap.symm).elim
    by_cases hlsucc : l + 1 = k
    · apply False.elim
      apply hprev
      calc
        (k : ZMod (k + 1)) = (l + 1 : ℕ) := by rw [hlsucc]
        _ = (l : ZMod (k + 1)) + 1 := by rw [Nat.cast_add, Nat.cast_one]
    rw [C.forwardCutEdgeSegment_last (by omega) hP hQ,
      forwardCutEdgeSegment_of_lt (J := J) hllt]
    exact Set.disjoint_iff_inter_eq_empty.mp
      (C.chord_disjoint_middleEdge (Nat.pos_of_ne_zero hl0) (by omega)
        (by omega) hP hQ)
  have hmlt : m < k := by omega
  by_cases hlk : l = k
  · rw [hlk] at hij hprev hnext ⊢
    by_cases hm0 : m = 0
    · rw [hm0, Nat.cast_zero] at hprev
      exact (hprev hwrap.symm).elim
    by_cases hmsucc : m + 1 = k
    · apply False.elim
      apply hnext
      calc
        (k : ZMod (k + 1)) = (m + 1 : ℕ) := by rw [hmsucc]
        _ = (m : ZMod (k + 1)) + 1 := by rw [Nat.cast_add, Nat.cast_one]
    rw [forwardCutEdgeSegment_of_lt (J := J) hmlt,
      C.forwardCutEdgeSegment_last (by omega) hP hQ]
    exact Set.disjoint_iff_inter_eq_empty.mp
      (C.chord_disjoint_middleEdge (Nat.pos_of_ne_zero hm0) (by omega)
        (by omega) hP hQ).symm
  have hllt : l < k := by omega
  rw [forwardCutEdgeSegment_of_lt (J := J) hmlt,
    forwardCutEdgeSegment_of_lt (J := J) hllt]
  apply J.nonadjacent_disjoint
  · intro h
    have hml := natCast_eq_natCast_of_lt (by omega : m < J.n) (by omega : l < J.n) h
    apply hij
    rw [hml]
  · intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (by omega : m < J.n), ZMod.val_add,
      ZMod.val_natCast_of_lt (by omega : l < J.n)] at hv
    have hone : (1 : ZMod J.n).val = 1 := by
      rw [ZMod.val_one]
    rw [hone, Nat.mod_eq_of_lt (by omega : l + 1 < J.n)] at hv
    apply hprev
    rw [hv, Nat.cast_add, Nat.cast_one]
  · intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (by omega : l < J.n), ZMod.val_add,
      ZMod.val_natCast_of_lt (by omega : m < J.n)] at hv
    have hone : (1 : ZMod J.n).val = 1 := by
      rw [ZMod.val_one]
    rw [hone, Nat.mod_eq_of_lt (by omega : m + 1 < J.n)] at hv
    apply hnext
    rw [hv, Nat.cast_add, Nat.cast_one]

/-- Close the forward boundary arc from vertex `0` to vertex `k` by a proper chord. -/
def forwardCutCircle {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    PolygonalCircle where
  n := k + 1
  three_le := by omega
  vertex := forwardCutVertex (J := J) k
  adjacent_ne := C.forwardCutVertex_adjacent_ne hk2 (by omega) hP hQ
  consecutive_inter := by
    intro i
    simpa only [forwardCutEdgeSegment, add_assoc, one_add_one_eq_two] using
      C.forwardCut_consecutive_inter hk2 hk hP hQ i
  nonadjacent_disjoint := by
    intro i j hij hprev hnext
    simpa only [forwardCutEdgeSegment] using
      C.forwardCut_nonadjacent_disjoint hk2 hk hP hQ i j hij hprev hnext

/-- The forward boundary arc consisting of old edges `0,...,k-1`. -/
def forwardArc (k : ℕ) : Set Plane :=
  ⋃ m : Fin k, J.edgeSegment (m.val : ZMod J.n)

theorem forwardCutCircle_carrier {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    (C.forwardCutCircle hk2 hk hP hQ).carrier =
      forwardArc (J := J) k ∪ segment ℝ C.Q C.P := by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [PolygonalCircle.carrier, Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    let m := i.val
    have hm : m < k + 1 := i.val_lt
    have hcast : (m : ZMod (k + 1)) = i := ZMod.natCast_zmod_val i
    rw [← hcast] at hi
    change x ∈ forwardCutEdgeSegment (J := J) k (m : ZMod (k + 1)) at hi
    by_cases hmk : m = k
    · right
      rwa [hmk, C.forwardCutEdgeSegment_last (by omega) hP hQ] at hi
    · left
      have hmlt : m < k := by omega
      simp only [forwardArc, Set.mem_iUnion]
      refine ⟨⟨m, hmlt⟩, ?_⟩
      rwa [forwardCutEdgeSegment_of_lt (J := J) hmlt] at hi
  · rintro x (hx | hx)
    · simp only [forwardArc, Set.mem_iUnion] at hx
      obtain ⟨m, hm⟩ := hx
      simp only [PolygonalCircle.carrier, Set.mem_iUnion]
      refine ⟨(m.val : ZMod (k + 1)), ?_⟩
      change x ∈ forwardCutEdgeSegment (J := J) k (m.val : ZMod (k + 1))
      rwa [forwardCutEdgeSegment_of_lt (J := J) m.isLt]
    · simp only [PolygonalCircle.carrier, Set.mem_iUnion]
      refine ⟨(k : ZMod (k + 1)), ?_⟩
      change x ∈ forwardCutEdgeSegment (J := J) k (k : ZMod (k + 1))
      rwa [C.forwardCutEdgeSegment_last (by omega) hP hQ]

theorem endpoints_mem_forwardArc {k : ℕ} (hk2 : 2 ≤ k) (_ : k < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    C.P ∈ forwardArc (J := J) k ∧ C.Q ∈ forwardArc (J := J) k := by
  constructor
  · simp only [forwardArc, Set.mem_iUnion]
    refine ⟨⟨0, by omega⟩, ?_⟩
    have hmem : C.P ∈ J.edgeSegment 0 := by
      rw [← hP]
      exact left_mem_segment ℝ _ _
    simpa using hmem
  · simp only [forwardArc, Set.mem_iUnion]
    refine ⟨⟨k - 1, by omega⟩, ?_⟩
    change C.Q ∈ J.edgeSegment ((k - 1 : ℕ) : ZMod J.n)
    rw [← hQ]
    apply (J.vertex_mem_edgeSegment_iff (k : ZMod J.n)
      ((k - 1 : ℕ) : ZMod J.n)).mpr
    right
    calc
      (k : ZMod J.n) = ((k - 1 + 1 : ℕ) : ZMod J.n) :=
        congrArg (fun q : ℕ => (q : ZMod J.n)) (by omega)
      _ = ((k - 1 : ℕ) : ZMod J.n) + 1 := by rw [Nat.cast_add, Nat.cast_one]

theorem forwardArc_interior_nonempty {k : ℕ} (hk2 : 2 ≤ k) (_ : k < J.n)
    (hP : J.vertex 0 = C.P) (_ : J.vertex (k : ZMod J.n) = C.Q) :
    (forwardArc (J := J) k \ {C.P, C.Q}).Nonempty := by
  refine ⟨J.vertex 1, ?_, ?_⟩
  · simp only [forwardArc, Set.mem_iUnion]
    refine ⟨⟨0, by omega⟩, ?_⟩
    have hmem : J.vertex 1 ∈ J.edgeSegment 0 := by
      unfold edgeSegment
      simpa only [zero_add] using right_mem_segment ℝ (J.vertex 0) (J.vertex 1)
    simpa using hmem
  · intro hendpoint
    rcases hendpoint with h | h
    · apply J.adjacent_ne 0
      simpa only [zero_add, hP] using h.symm
    · have hPedge : C.P ∈ J.edgeSegment 0 := by
        rw [← hP]
        exact left_mem_segment ℝ _ _
      have hQedge : C.Q ∈ J.edgeSegment 0 := by
        rw [← h]
        unfold edgeSegment
        simpa only [zero_add] using right_mem_segment ℝ (J.vertex 0) (J.vertex 1)
      exact (C.endpoint_edges_ne hPedge hQedge) rfl

theorem forwardArc_subset_carrier {k : ℕ} :
    forwardArc (J := J) k ⊆ J.carrier := by
  intro x hx
  simp only [forwardArc, Set.mem_iUnion] at hx
  obtain ⟨m, hm⟩ := hx
  exact J.edgeSegment_subset_carrier _ hm

/-- The complementary boundary arc, expressed as a forward arc after rotating vertex `k` to
index zero. -/
def backwardArc (k : ℕ) : Set Plane :=
  forwardArc (J := J.rotate (k : ZMod J.n)) (J.n - k)

theorem backwardArc_subset_carrier {k : ℕ} :
    backwardArc (J := J) k ⊆ J.carrier := by
  intro x hx
  have hx' := forwardArc_subset_carrier (J := J.rotate (k : ZMod J.n)) hx
  rwa [J.rotate_carrier] at hx'

theorem rotate_edgeSegment_nat {k m : ℕ} (_ : k < J.n) (_ : m + k < J.n) :
    (J.rotate (k : ZMod J.n)).edgeSegment (m : ZMod J.n) =
      J.edgeSegment (m + k : ZMod J.n) := by
  rw [J.rotate_edgeSegment]

/-- The two cyclic boundary arcs cover the original polygon carrier. -/
theorem forwardArc_union_backwardArc {k : ℕ} (hk : k < J.n) :
    forwardArc (J := J) k ∪ backwardArc (J := J) k = J.carrier := by
  apply Set.Subset.antisymm
  · rintro x (hx | hx)
    · exact forwardArc_subset_carrier (J := J) hx
    · exact backwardArc_subset_carrier (J := J) hx
  · intro x hx
    simp only [PolygonalCircle.carrier, Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    let m := i.val
    have hm : m < J.n := i.val_lt
    have hcast : (m : ZMod J.n) = i := ZMod.natCast_zmod_val i
    rw [← hcast] at hi
    by_cases hmk : m < k
    · left
      simp only [forwardArc, Set.mem_iUnion]
      exact ⟨⟨m, hmk⟩, hi⟩
    · right
      let l := m - k
      have hl : l < J.n - k := by omega
      simp only [backwardArc, forwardArc, Set.mem_iUnion]
      refine ⟨⟨l, hl⟩, ?_⟩
      change x ∈ (J.rotate (k : ZMod J.n)).edgeSegment (l : ZMod J.n)
      have hlk : l + k = m := Nat.sub_add_cancel (Nat.le_of_not_gt hmk)
      have hedge := rotate_edgeSegment_nat (J := J) hk (by omega : l + k < J.n)
      rw [hedge]
      have hidx : (l : ZMod J.n) + (k : ZMod J.n) = (m : ZMod J.n) := by
        rw [← Nat.cast_add, hlk]
      rw [hidx]
      exact hi

/-- The complementary arc has the same two endpoints as the forward arc. -/
theorem endpoints_mem_backwardArc {k : ℕ} (hkpos : 0 < k) (hk2 : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    C.P ∈ backwardArc (J := J) k ∧ C.Q ∈ backwardArc (J := J) k := by
  let R := J.rotate (k : ZMod J.n)
  let CR : R.ProperChord := C.symm.rotate (k : ZMod J.n)
  have hlen : 2 ≤ J.n - k := by omega
  have hRzero : R.vertex 0 = CR.P := by
    change J.vertex ((0 : ZMod J.n) + k) = C.Q
    simpa only [zero_add] using hQ
  have hRlast' : (J.rotate (k : ZMod J.n)).vertex
      ((J.n - k : ℕ) : ZMod J.n) = C.P := by
    change J.vertex (((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n)) = C.P
    have hsum : ((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n) = 0 := by
      calc
        ((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n) =
            ((J.n - k + k : ℕ) : ZMod J.n) := by rw [Nat.cast_add]
        _ = (J.n : ℕ) := by rw [Nat.sub_add_cancel (by omega)]
        _ = 0 := ZMod.natCast_self J.n
    rw [hsum]
    exact hP
  have hRlast : R.vertex ((J.n - k : ℕ) : ZMod R.n) = CR.Q := by
    exact hRlast'
  have hlenlt : J.n - k < R.n := by
    change J.n - k < J.n
    omega
  have hends := CR.endpoints_mem_forwardArc hlen hlenlt hRzero hRlast
  exact ⟨hends.2, hends.1⟩

theorem forwardArc_inter_chord {k : ℕ} (hk2 : 2 ≤ k) (hk : k < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    forwardArc (J := J) k ∩ segment ℝ C.P C.Q = {C.P, C.Q} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxArc, hxChord⟩
    have hxCarrier := forwardArc_subset_carrier (J := J) hxArc
    exact C.segment_inter_carrier ▸ ⟨hxChord, hxCarrier⟩
  · intro x hx
    rcases hx with rfl | rfl
    · exact ⟨(C.endpoints_mem_forwardArc hk2 hk hP hQ).1,
        left_mem_segment ℝ _ _⟩
    · exact ⟨(C.endpoints_mem_forwardArc hk2 hk hP hQ).2,
        right_mem_segment ℝ _ _⟩

theorem backwardArc_inter_chord {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    backwardArc (J := J) k ∩ segment ℝ C.P C.Q = {C.P, C.Q} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxArc, hxChord⟩
    have hxCarrier := backwardArc_subset_carrier (J := J) hxArc
    exact C.segment_inter_carrier ▸ ⟨hxChord, hxCarrier⟩
  · intro x hx
    rcases hx with rfl | rfl
    · exact ⟨(C.endpoints_mem_backwardArc (by omega) hk hP hQ).1,
        left_mem_segment ℝ _ _⟩
    · exact ⟨(C.endpoints_mem_backwardArc (by omega) hk hP hQ).2,
        right_mem_segment ℝ _ _⟩

/-- The two complementary cyclic boundary arcs meet only at their endpoints. -/
theorem forwardArc_inter_backwardArc {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    forwardArc (J := J) k ∩ backwardArc (J := J) k = {C.P, C.Q} := by
  letI : Fact (1 < J.n) := ⟨by omega⟩
  apply Set.Subset.antisymm
  · rintro x ⟨hxF, hxB⟩
    simp only [forwardArc, Set.mem_iUnion] at hxF
    simp only [backwardArc, forwardArc, Set.mem_iUnion] at hxB
    obtain ⟨m, hm⟩ := hxF
    obtain ⟨l, hl⟩ := hxB
    let a := m.val
    let b := l.val + k
    have ha : a < k := m.isLt
    have hb0 : k ≤ b := by dsimp [b]; omega
    have hbn : b < J.n := by dsimp [b]; omega
    have hm' : x ∈ J.edgeSegment (a : ZMod J.n) := by
      simpa [a] using hm
    have hrot := rotate_edgeSegment_nat (J := J) (k := k) (m := l.val)
      (by omega) (by omega)
    have hlOld : x ∈ J.edgeSegment (b : ZMod J.n) := by
      have hl' : x ∈ (J.rotate (k : ZMod J.n)).edgeSegment (l.val : ZMod J.n) := by
        exact hl
      rw [hrot] at hl'
      have hidx : (l.val : ZMod J.n) + (k : ZMod J.n) = (b : ZMod J.n) := by
        dsimp [b]
        rw [Nat.cast_add]
      rwa [hidx] at hl'
    have hab : (a : ZMod J.n) ≠ (b : ZMod J.n) := by
      intro heq
      have := natCast_eq_natCast_of_lt (by omega : a < J.n) hbn heq
      omega
    have hxEnds := J.edgeSegment_inter_subset_endpoints hab ⟨hm', hlOld⟩
    rcases hxEnds with hxa | hxa
    · have hvertexB : J.vertex (a : ZMod J.n) ∈ J.edgeSegment (b : ZMod J.n) := by
        rwa [hxa] at hlOld
      rcases (J.vertex_mem_edgeSegment_iff (a : ZMod J.n)
        (b : ZMod J.n)).mp hvertexB with heq | hsucc
      · exact (hab heq).elim
      · have hv := congrArg ZMod.val hsucc
        rw [ZMod.val_natCast_of_lt (by omega : a < J.n), ZMod.val_add,
          ZMod.val_natCast_of_lt hbn, ZMod.val_one] at hv
        by_cases hblt : b + 1 < J.n
        · rw [Nat.mod_eq_of_lt hblt] at hv
          omega
        · have hblast : b + 1 = J.n := by omega
          rw [hblast, Nat.mod_self] at hv
          have ha0 : a = 0 := by omega
          left
          calc
            x = J.vertex (a : ZMod J.n) := hxa
            _ = J.vertex (0 : ZMod J.n) := by rw [ha0]; simp only [Nat.cast_zero]
            _ = C.P := hP
    · have ha1 : a + 1 < J.n := by omega
      rw [Set.mem_singleton_iff] at hxa
      have hcast : (a : ZMod J.n) + 1 = (a + 1 : ℕ) := by
        rw [Nat.cast_add, Nat.cast_one]
      rw [hcast] at hxa
      have hvertexB : J.vertex ((a + 1 : ℕ) : ZMod J.n) ∈
          J.edgeSegment (b : ZMod J.n) := by
        rwa [hxa] at hlOld
      rcases (J.vertex_mem_edgeSegment_iff ((a + 1 : ℕ) : ZMod J.n)
        (b : ZMod J.n)).mp hvertexB with heq | hsucc
      · have habNat := natCast_eq_natCast_of_lt ha1 hbn heq
        have haLast : a + 1 = k := by omega
        right
        calc
          x = J.vertex ((a + 1 : ℕ) : ZMod J.n) := hxa
          _ = J.vertex (k : ZMod J.n) := by rw [haLast]
          _ = C.Q := hQ
      · have hv := congrArg ZMod.val hsucc
        rw [ZMod.val_natCast_of_lt ha1, ZMod.val_add,
          ZMod.val_natCast_of_lt hbn, ZMod.val_one] at hv
        by_cases hblt : b + 1 < J.n
        · rw [Nat.mod_eq_of_lt hblt] at hv
          omega
        · have hblast : b + 1 = J.n := by omega
          rw [hblast, Nat.mod_self] at hv
          omega
  · intro x hx
    rcases hx with rfl | rfl
    · exact ⟨(C.endpoints_mem_forwardArc hk2 (by omega) hP hQ).1,
        (C.endpoints_mem_backwardArc (by omega) hk hP hQ).1⟩
    · exact ⟨(C.endpoints_mem_forwardArc hk2 (by omega) hP hQ).2,
        (C.endpoints_mem_backwardArc (by omega) hk hP hQ).2⟩

/-- Close the complementary boundary arc by the same chord, using a cyclic rotation. -/
def backwardCutCircle {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    PolygonalCircle := by
  let R := J.rotate (k : ZMod J.n)
  let CR : R.ProperChord := C.symm.rotate (k : ZMod J.n)
  have hlen : 2 ≤ J.n - k := by omega
  have hcut : J.n - k + 1 < R.n := by
    change J.n - k + 1 < J.n
    omega
  have hRzero : R.vertex 0 = CR.P := by
    change J.vertex ((0 : ZMod J.n) + k) = C.Q
    simpa only [zero_add] using hQ
  have hRlast : R.vertex ((J.n - k : ℕ) : ZMod R.n) = CR.Q := by
    change J.vertex (((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n)) = C.P
    have hsum : ((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n) = 0 := by
      calc
        ((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n) =
            ((J.n - k + k : ℕ) : ZMod J.n) := by rw [Nat.cast_add]
        _ = (J.n : ℕ) := by rw [Nat.sub_add_cancel (by omega)]
        _ = 0 := ZMod.natCast_self J.n
    rw [hsum]
    exact hP
  exact CR.forwardCutCircle hlen hcut hRzero hRlast

theorem backwardCutCircle_carrier {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    (C.backwardCutCircle hk2 hk hP hQ).carrier =
      backwardArc (J := J) k ∪ segment ℝ C.P C.Q := by
  classical
  unfold backwardCutCircle
  dsimp only
  rw [PolygonalCircle.ProperChord.forwardCutCircle_carrier]
  simp only [backwardArc, ProperChord.symm, ProperChord.rotate]

theorem backwardArc_interior_nonempty {k : ℕ} (hk2 : 2 ≤ k) (hk : k + 1 < J.n)
    (hP : J.vertex 0 = C.P) (hQ : J.vertex (k : ZMod J.n) = C.Q) :
    (backwardArc (J := J) k \ {C.P, C.Q}).Nonempty := by
  let R := J.rotate (k : ZMod J.n)
  let CR : R.ProperChord := C.symm.rotate (k : ZMod J.n)
  have hlen : 2 ≤ J.n - k := by omega
  have hRzero : R.vertex 0 = CR.P := by
    change J.vertex ((0 : ZMod J.n) + k) = C.Q
    simpa only [zero_add] using hQ
  have hRlast : R.vertex ((J.n - k : ℕ) : ZMod R.n) = CR.Q := by
    change J.vertex (((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n)) = C.P
    have hsum : ((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n) = 0 := by
      calc
        ((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n) =
            ((J.n - k + k : ℕ) : ZMod J.n) := by rw [Nat.cast_add]
        _ = (J.n : ℕ) := by rw [Nat.sub_add_cancel (by omega)]
        _ = 0 := ZMod.natCast_self J.n
    rw [hsum]
    exact hP
  have hnonempty := CR.forwardArc_interior_nonempty hlen (by
    change J.n - k < J.n
    omega) hRzero hRlast
  have hCRP : CR.P = C.Q := rfl
  have hCRQ : CR.Q = C.P := rfl
  rw [hCRP, hCRQ] at hnonempty
  simpa only [backwardArc, Set.pair_comm] using hnonempty

end ProperChord

/-- Crossing predicate for one oriented segment, separated from cyclic indexing. -/
def SegmentCrossed (v w P : Plane) : Prop :=
  (v 1 ≤ P 1 ∧ P 1 < w 1 ∨ w 1 ≤ P 1 ∧ P 1 < v 1) ∧
    crossingX v w (P 1) < P 0

theorem edgeCrossed_iff_segmentCrossed (J : PolygonalCircle) (i : ZMod J.n) (P : Plane) :
    J.EdgeCrossed i P ↔ SegmentCrossed (J.vertex i) (J.vertex (i + 1)) P :=
  Iff.rfl

theorem crossingX_comm {v w : Plane} {y : ℝ} (h : v 1 ≠ w 1) :
    crossingX v w y = crossingX w v y := by
  unfold crossingX
  field_simp
  ring

theorem segmentCrossed_comm (v w P : Plane) :
    SegmentCrossed v w P ↔ SegmentCrossed w v P := by
  by_cases hheight : v 1 = w 1
  · unfold SegmentCrossed
    rw [hheight]
    constructor <;> rintro ⟨hband, -⟩ <;>
      rcases hband with hband | hband <;>
      exact (not_lt_of_ge hband.1 hband.2).elim
  · unfold SegmentCrossed
    rw [crossingX_comm hheight]
    tauto

open scoped Classical in
/-- Number of crossed polygon edges before reducing modulo two, indexed by ordinary naturals. -/
noncomputable def crossingCount (J : PolygonalCircle) (P : Plane) : ℕ :=
  ∑ m ∈ Finset.range J.n, if J.EdgeCrossed (m : ZMod J.n) P then 1 else 0

theorem index_eq_crossingCount_mod (J : PolygonalCircle) (P : Plane) :
    J.index P = J.crossingCount P % 2 := by
  classical
  unfold index crossingCount
  rw [Finset.card_filter]
  simp only [Finset.sum_const_zero, Finset.sum_ite, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  congr 2
  apply Finset.card_bij (fun z _ => z.val)
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨z.val_lt, by rwa [ZMod.natCast_zmod_val z]⟩
  · intro z _ w _ h
    exact ZMod.val_injective J.n h
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    refine ⟨(m : ZMod J.n), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [ZMod.val_natCast_of_lt hm.1] using hm.2
    · exact ZMod.val_natCast_of_lt hm.1

theorem rotate_edgeCrossed_iff (J : PolygonalCircle) (a i : ZMod J.n) (P : Plane) :
    (J.rotate a).EdgeCrossed i P ↔ J.EdgeCrossed (i + a) P := by
  change SegmentCrossed (J.vertex (i + a)) (J.vertex ((i + 1) + a)) P ↔
    SegmentCrossed (J.vertex (i + a)) (J.vertex (i + a + 1)) P
  abel

namespace ProperChord

variable {J : PolygonalCircle} (C : J.ProperChord)

theorem forwardCutCircle_edgeCrossed_of_lt {k m : ℕ} (hk2 : 2 ≤ k)
    (hk : k + 1 < J.n) (hP : J.vertex 0 = C.P)
    (hQ : J.vertex (k : ZMod J.n) = C.Q) (hm : m < k) (P : Plane) :
    (C.forwardCutCircle hk2 hk hP hQ).EdgeCrossed (m : ZMod (k + 1)) P ↔
      J.EdgeCrossed (m : ZMod J.n) P := by
  change SegmentCrossed (forwardCutVertex (J := J) k (m : ZMod (k + 1)))
      (forwardCutVertex (J := J) k ((m : ZMod (k + 1)) + 1)) P ↔
    SegmentCrossed (J.vertex (m : ZMod J.n)) (J.vertex ((m : ZMod J.n) + 1)) P
  rw [forwardCutVertex_natCast (J := J) (by omega)]
  have hsucc : (m : ZMod (k + 1)) + 1 = (m + 1 : ℕ) := by
    rw [Nat.cast_add, Nat.cast_one]
  rw [hsucc, forwardCutVertex_natCast (J := J) (by omega)]
  rw [Nat.cast_add, Nat.cast_one]

theorem forwardCutCircle_edgeCrossed_last {k : ℕ} (hk2 : 2 ≤ k)
    (hk : k + 1 < J.n) (hP : J.vertex 0 = C.P)
    (hQ : J.vertex (k : ZMod J.n) = C.Q) (P : Plane) :
    (C.forwardCutCircle hk2 hk hP hQ).EdgeCrossed (k : ZMod (k + 1)) P ↔
      SegmentCrossed C.P C.Q P := by
  change SegmentCrossed (forwardCutVertex (J := J) k (k : ZMod (k + 1)))
      (forwardCutVertex (J := J) k ((k : ZMod (k + 1)) + 1)) P ↔
    SegmentCrossed C.P C.Q P
  rw [forwardCutVertex_natCast (J := J) (by omega), hQ]
  have hwrap : (k : ZMod (k + 1)) + 1 = 0 := by
    calc
      (k : ZMod (k + 1)) + 1 = ((k + 1 : ℕ) : ZMod (k + 1)) := by
        rw [Nat.cast_add, Nat.cast_one]
      _ = 0 := ZMod.natCast_self (k + 1)
  have hnext : forwardCutVertex (J := J) k ((k : ZMod (k + 1)) + 1) = C.P := by
    rw [hwrap]
    unfold forwardCutVertex
    rw [ZMod.val_zero]
    simpa only [Nat.cast_zero] using hP
  have hnextEq : SegmentCrossed C.Q
      (forwardCutVertex (J := J) k ((k : ZMod (k + 1)) + 1)) P =
        SegmentCrossed C.Q C.P P :=
    congrArg (fun q => SegmentCrossed C.Q q P) hnext
  constructor
  · intro h
    have h' : SegmentCrossed C.Q
        (forwardCutVertex (J := J) k ((k : ZMod (k + 1)) + 1)) P := h
    exact (segmentCrossed_comm C.Q C.P P).mp (hnextEq.mp h')
  · intro h
    have h' := (segmentCrossed_comm C.Q C.P P).mpr h
    have h'' : SegmentCrossed C.Q
        (forwardCutVertex (J := J) k ((k : ZMod (k + 1)) + 1)) P :=
      hnextEq.mpr h'
    exact h''

open scoped Classical in
theorem crossingCount_forwardCutCircle {k : ℕ} (hk2 : 2 ≤ k)
    (hk : k + 1 < J.n) (hP : J.vertex 0 = C.P)
    (hQ : J.vertex (k : ZMod J.n) = C.Q) (P : Plane) :
    (C.forwardCutCircle hk2 hk hP hQ).crossingCount P =
      (∑ m ∈ Finset.range k, if J.EdgeCrossed (m : ZMod J.n) P then 1 else 0) +
        if SegmentCrossed C.P C.Q P then 1 else 0 := by
  unfold crossingCount
  change (∑ m ∈ Finset.range (k + 1),
    if (C.forwardCutCircle hk2 hk hP hQ).EdgeCrossed (m : ZMod (k + 1)) P
      then 1 else 0) = _
  rw [Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro m hm
    have hmlt := Finset.mem_range.mp hm
    rw [C.forwardCutCircle_edgeCrossed_of_lt hk2 hk hP hQ hmlt]
  · rw [C.forwardCutCircle_edgeCrossed_last hk2 hk hP hQ]

open scoped Classical in
theorem crossingCount_backwardCutCircle {k : ℕ} (hk2 : 2 ≤ k)
    (hk : k + 1 < J.n) (hP : J.vertex 0 = C.P)
    (hQ : J.vertex (k : ZMod J.n) = C.Q) (P : Plane) :
    (C.backwardCutCircle hk2 hk hP hQ).crossingCount P =
      (∑ m ∈ Finset.range (J.n - k),
        if J.EdgeCrossed ((m + k : ℕ) : ZMod J.n) P then 1 else 0) +
          if SegmentCrossed C.P C.Q P then 1 else 0 := by
  let R := J.rotate (k : ZMod J.n)
  let CR : R.ProperChord := C.symm.rotate (k : ZMod J.n)
  have hlen : 2 ≤ J.n - k := by omega
  have hcut : J.n - k + 1 < R.n := by
    change J.n - k + 1 < J.n
    omega
  have hRzero : R.vertex 0 = CR.P := by
    change J.vertex ((0 : ZMod J.n) + k) = C.Q
    simpa only [zero_add] using hQ
  have hRlast : R.vertex ((J.n - k : ℕ) : ZMod R.n) = CR.Q := by
    change J.vertex (((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n)) = C.P
    have hsum : ((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n) = 0 := by
      calc
        ((J.n - k : ℕ) : ZMod J.n) + (k : ZMod J.n) =
            ((J.n - k + k : ℕ) : ZMod J.n) := by rw [Nat.cast_add]
        _ = (J.n : ℕ) := by rw [Nat.sub_add_cancel (by omega)]
        _ = 0 := ZMod.natCast_self J.n
    rw [hsum]
    exact hP
  have hcount := CR.crossingCount_forwardCutCircle hlen hcut hRzero hRlast P
  change (CR.forwardCutCircle hlen hcut hRzero hRlast).crossingCount P = _
  rw [hcount]
  congr 1
  · apply Finset.sum_congr rfl
    intro m hm
    have hmlt := Finset.mem_range.mp hm
    have hrotate := J.rotate_edgeCrossed_iff (k : ZMod J.n)
      (m : ZMod J.n) P
    have hidx : (m : ZMod J.n) + (k : ZMod J.n) = (m + k : ℕ) := by
      rw [Nat.cast_add]
    rw [hidx] at hrotate
    have hrotate' : R.EdgeCrossed (m : ZMod R.n) P ↔
        J.EdgeCrossed ((m + k : ℕ) : ZMod J.n) P := hrotate
    exact if_congr hrotate' rfl rfl
  · have hcomm := segmentCrossed_comm C.Q C.P P
    change (if SegmentCrossed C.Q C.P P then 1 else 0) = _
    exact if_congr hcomm rfl rfl

theorem index_parity_cutCircles {k : ℕ} (hk2 : 2 ≤ k)
    (hk : k + 1 < J.n) (hP : J.vertex 0 = C.P)
    (hQ : J.vertex (k : ZMod J.n) = C.Q) (P : Plane) :
    J.index P = ((C.forwardCutCircle hk2 hk hP hQ).index P +
      (C.backwardCutCircle hk2 hk hP hQ).index P) % 2 := by
  classical
  let A := ∑ m ∈ Finset.range k,
    if J.EdgeCrossed (m : ZMod J.n) P then 1 else 0
  let B := ∑ m ∈ Finset.range (J.n - k),
    if J.EdgeCrossed ((m + k : ℕ) : ZMod J.n) P then 1 else 0
  let e := if SegmentCrossed C.P C.Q P then 1 else 0
  have hcountJ : J.crossingCount P = A + B := by
    unfold crossingCount A B
    have hkn : k + (J.n - k) = J.n := Nat.add_sub_of_le (by omega)
    calc
      (∑ m ∈ Finset.range J.n,
          if J.EdgeCrossed (m : ZMod J.n) P then 1 else 0) =
          ∑ m ∈ Finset.range (k + (J.n - k)),
            if J.EdgeCrossed (m : ZMod J.n) P then 1 else 0 := by rw [hkn]
      _ = (∑ m ∈ Finset.range k,
          if J.EdgeCrossed (m : ZMod J.n) P then 1 else 0) +
          ∑ m ∈ Finset.range (J.n - k),
            if J.EdgeCrossed ((k + m : ℕ) : ZMod J.n) P then 1 else 0 := by
              exact Finset.sum_range_add _ _ _
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro m hm
        rw [Nat.add_comm]
  have hcountF := C.crossingCount_forwardCutCircle hk2 hk hP hQ P
  have hcountB := C.crossingCount_backwardCutCircle hk2 hk hP hQ P
  rw [J.index_eq_crossingCount_mod,
    (C.forwardCutCircle hk2 hk hP hQ).index_eq_crossingCount_mod,
    (C.backwardCutCircle hk2 hk hP hQ).index_eq_crossingCount_mod,
    hcountJ, hcountF, hcountB]
  change (A + B) % 2 = ((A + e) % 2 + (B + e) % 2) % 2
  dsimp [e]
  by_cases hcross : SegmentCrossed C.P C.Q P <;> simp [hcross] ; omega

end ProperChord

end PolygonalCircle

/-- The carrier data of a polygonal theta graph.  `J12`, `J13`, and `J23` are the polygons
formed by the indicated pairs of arcs. -/
structure PolygonalTheta where
  /-- The `P` declaration. -/
  P : Plane
  /-- The `Q` declaration. -/
  Q : Plane
  /-- The `B1` declaration. -/
  B1 : Set Plane
  /-- The `B2` declaration. -/
  B2 : Set Plane
  /-- The `B3` declaration. -/
  B3 : Set Plane
  /-- The `J12` declaration. -/
  J12 : PolygonalCircle
  /-- The `J13` declaration. -/
  J13 : PolygonalCircle
  /-- The `J23` declaration. -/
  J23 : PolygonalCircle
  P_mem_B1 : P ∈ B1
  Q_mem_B1 : Q ∈ B1
  P_mem_B2 : P ∈ B2
  Q_mem_B2 : Q ∈ B2
  P_mem_B3 : P ∈ B3
  Q_mem_B3 : Q ∈ B3
  B1_inter_B2 : B1 ∩ B2 = {P, Q}
  B1_inter_B3 : B1 ∩ B3 = {P, Q}
  B2_inter_B3 : B2 ∩ B3 = {P, Q}
  carrier12 : J12.carrier = B1 ∪ B2
  carrier13 : J13.carrier = B1 ∪ B3
  carrier23 : J23.carrier = B2 ∪ B3
  chord_subset : B3 ⊆ {P, Q} ∪ J12.interiorRegion
  B1_interior_nonempty : (B1 \ {P, Q}).Nonempty
  B2_interior_nonempty : (B2 \ {P, Q}).Nonempty
  chord_interior_nonempty : (B3 \ {P, Q}).Nonempty
  index_parity : ∀ x, x ∉ J12.carrier → x ∉ J13.carrier → x ∉ J23.carrier →
    J12.index x = (J13.index x + J23.index x) % 2

namespace PolygonalCircle.ProperChord

variable {J : PolygonalCircle} (C : J.ProperChord)

/-- Every proper straight chord of a polygon determines the finite polygonal theta graph used
in Moise Chapter 2, Theorems 7 and 8. -/
theorem exists_polygonalTheta :
    ∃ G : PolygonalTheta,
      G.J12.carrier = J.carrier ∧ G.P = C.P ∧ G.Q = C.Q ∧ G.B3 = segment ℝ C.P C.Q := by
  obtain ⟨J', k, hk2, hk, hcarrier, hP, hQ, C', hC'P, hC'Q⟩ :=
    C.exists_vertex_normalization
  have hP' : J'.vertex 0 = C'.P := hP.trans hC'P.symm
  have hQ' : J'.vertex (k : ZMod J'.n) = C'.Q := hQ.trans hC'Q.symm
  let J13 := C'.forwardCutCircle hk2 hk hP' hQ'
  let J23 := C'.backwardCutCircle hk2 hk hP' hQ'
  let B1 := forwardArc (J := J') k
  let B2 := backwardArc (J := J') k
  let B3 := segment ℝ C'.P C'.Q
  let G : PolygonalTheta :=
    { P := C'.P
      Q := C'.Q
      B1 := B1
      B2 := B2
      B3 := B3
      J12 := J'
      J13 := J13
      J23 := J23
      P_mem_B1 := (C'.endpoints_mem_forwardArc hk2 (by omega) hP' hQ').1
      Q_mem_B1 := (C'.endpoints_mem_forwardArc hk2 (by omega) hP' hQ').2
      P_mem_B2 := (C'.endpoints_mem_backwardArc (by omega) hk hP' hQ').1
      Q_mem_B2 := (C'.endpoints_mem_backwardArc (by omega) hk hP' hQ').2
      P_mem_B3 := left_mem_segment ℝ _ _
      Q_mem_B3 := right_mem_segment ℝ _ _
      B1_inter_B2 := C'.forwardArc_inter_backwardArc hk2 hk hP' hQ'
      B1_inter_B3 := C'.forwardArc_inter_chord hk2 (by omega) hP' hQ'
      B2_inter_B3 := C'.backwardArc_inter_chord hk2 hk hP' hQ'
      carrier12 := by
        dsimp [B1, B2]
        exact (forwardArc_union_backwardArc (J := J') (by omega)).symm
      carrier13 := by
        dsimp [J13, B1, B3]
        rw [C'.forwardCutCircle_carrier hk2 hk hP' hQ', segment_symm]
      carrier23 := by
        dsimp [J23, B2, B3]
        exact C'.backwardCutCircle_carrier hk2 hk hP' hQ'
      chord_subset := by
        intro x hx
        by_cases hxEnds : x ∈ ({C'.P, C'.Q} : Set Plane)
        · exact Or.inl hxEnds
        · exact Or.inr (C'.interior_subset ⟨hx, hxEnds⟩)
      B1_interior_nonempty := C'.forwardArc_interior_nonempty hk2 (by omega) hP' hQ'
      B2_interior_nonempty := C'.backwardArc_interior_nonempty hk2 hk hP' hQ'
      chord_interior_nonempty := C'.interior_nonempty
      index_parity := by
        intro x _ _ _
        exact C'.index_parity_cutCircles hk2 hk hP' hQ' x }
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · exact hcarrier
  · exact hC'P
  · exact hC'Q
  · dsimp [G, B3]
    rw [hC'P, hC'Q]

end PolygonalCircle.ProperChord

/-- A theta crosscut realized by an edge of a triangle mesh of the original polygonal disk.
This is the exact interface between the separation theorem of Chapter 2 and the cutting
induction of Chapter 3. -/
structure PolygonalTheta.MeshCrosscut (G : PolygonalTheta) (M : TriangleMesh) where
  support_eq : M.toPlaneComplex.support = G.J12.closedRegion
  /-- The `chordEdge` declaration. -/
  chordEdge : Finset M.Vertex
  chordEdge_mem : chordEdge ∈ M.edges
  chordVertices : M.position '' (chordEdge : Set M.Vertex) = {G.P, G.Q}
  chordCarrier : convexHull ℝ (M.position '' (chordEdge : Set M.Vertex)) = G.B3

namespace PolygonalTheta

variable (G : PolygonalTheta)

theorem endpoints_subset_carrier12 : ({G.P, G.Q} : Set Plane) ⊆ G.J12.carrier := by
  rw [G.carrier12]
  intro x hx
  rcases hx with (rfl | rfl) <;> simp [G.P_mem_B1, G.Q_mem_B1]

theorem exterior12_disjoint_B3 : Disjoint G.J12.exteriorRegion G.B3 := by
  rw [Set.disjoint_left]
  intro x hxExterior hxB3
  rcases G.chord_subset hxB3 with hxEndpoint | hxInterior
  · have hxCarrier := G.endpoints_subset_carrier12 hxEndpoint
    have hxCompl : x ∈ G.J12.carrierᶜ := by
      rw [← G.J12.interior_union_exterior]
      exact Or.inr hxExterior
    exact hxCompl hxCarrier
  · exact Set.disjoint_left.mp G.J12.disjoint_interior_exterior hxInterior hxExterior

theorem exterior12_subset_exterior13 :
    G.J12.exteriorRegion ⊆ G.J13.exteriorRegion := by
  have hsubsetCompl : G.J12.exteriorRegion ⊆ G.J13.carrierᶜ := by
    intro x hx
    rw [G.carrier13]
    intro hxCarrier
    rcases hxCarrier with hxB1 | hxB3
    · have hxJ12 : x ∈ G.J12.carrier := by rw [G.carrier12]; exact Or.inl hxB1
      have hxCompl : x ∈ G.J12.carrierᶜ := by
        rw [← G.J12.interior_union_exterior]
        exact Or.inr hx
      exact hxCompl hxJ12
    · exact Set.disjoint_left.mp G.exterior12_disjoint_B3 hx hxB3
  have hsubsetUnion : G.J12.exteriorRegion ⊆
      G.J13.interiorRegion ∪ G.J13.exteriorRegion := by
    rw [G.J13.interior_union_exterior]
    exact hsubsetCompl
  by_contra hnot
  have hwitness : ∃ x ∈ G.J12.exteriorRegion, x ∈ G.J13.interiorRegion := by
    obtain ⟨x, hx12, hxNot13⟩ := Set.not_subset.mp hnot
    rcases hsubsetUnion hx12 with hx13 | hx13
    · exact ⟨x, hx12, hx13⟩
    · exact (hxNot13 hx13).elim
  have hallInterior : G.J12.exteriorRegion ⊆ G.J13.interiorRegion :=
    G.J12.isConnected_exteriorRegion.isPreconnected.subset_left_of_subset_union
      G.J13.isOpen_interiorRegion G.J13.isOpen_exteriorRegion
      G.J13.disjoint_interior_exterior hsubsetUnion hwitness
  exact G.J12.not_isBounded_exteriorRegion
    (G.J13.isBounded_interiorRegion.subset hallInterior)

theorem B2_diff_endpoints_subset_exterior13 :
    G.B2 \ {G.P, G.Q} ⊆ G.J13.exteriorRegion := by
  intro x hx
  have hxFrontier12 : x ∈ frontier G.J12.exteriorRegion := by
    rw [G.J12.frontier_exteriorRegion, G.carrier12]
    exact Or.inr hx.1
  have hxClosure12 : x ∈ closure G.J12.exteriorRegion := frontier_subset_closure hxFrontier12
  have hxClosure13 : x ∈ closure G.J13.exteriorRegion :=
    closure_mono G.exterior12_subset_exterior13 hxClosure12
  have hxNotCarrier13 : x ∉ G.J13.carrier := by
    rw [G.carrier13]
    rintro (hxB1 | hxB3)
    · have : x ∈ G.B1 ∩ G.B2 := ⟨hxB1, hx.1⟩
      rw [G.B1_inter_B2] at this
      exact hx.2 this
    · have : x ∈ G.B2 ∩ G.B3 := ⟨hx.1, hxB3⟩
      rw [G.B2_inter_B3] at this
      exact hx.2 this
  rw [closure_eq_self_union_frontier, G.J13.frontier_exteriorRegion] at hxClosure13
  exact hxClosure13.resolve_right hxNotCarrier13

theorem interior13_subset_interior12 :
    G.J13.interiorRegion ⊆ G.J12.interiorRegion := by
  have hsubsetCompl : G.J13.interiorRegion ⊆ G.J12.carrierᶜ := by
    intro x hx13
    rw [G.carrier12]
    rintro (hxB1 | hxB2)
    · have hxCarrier13 : x ∈ G.J13.carrier := by rw [G.carrier13]; exact Or.inl hxB1
      have hxCompl13 : x ∈ G.J13.carrierᶜ := by
        rw [← G.J13.interior_union_exterior]
        exact Or.inl hx13
      exact hxCompl13 hxCarrier13
    · by_cases hxEndpoint : x ∈ ({G.P, G.Q} : Set Plane)
      · have hxB1 : x ∈ G.B1 := by
          rcases hxEndpoint with (rfl | rfl)
          · exact G.P_mem_B1
          · exact G.Q_mem_B1
        have hxCarrier13 : x ∈ G.J13.carrier := by rw [G.carrier13]; exact Or.inl hxB1
        have hxCompl13 : x ∈ G.J13.carrierᶜ := by
          rw [← G.J13.interior_union_exterior]
          exact Or.inl hx13
        exact hxCompl13 hxCarrier13
      · have hxExterior13 := G.B2_diff_endpoints_subset_exterior13 ⟨hxB2, hxEndpoint⟩
        exact Set.disjoint_left.mp G.J13.disjoint_interior_exterior hx13 hxExterior13
  have hsubsetUnion : G.J13.interiorRegion ⊆
      G.J12.interiorRegion ∪ G.J12.exteriorRegion := by
    rw [G.J12.interior_union_exterior]
    exact hsubsetCompl
  obtain ⟨y, hyB3, hyEndpoint⟩ := G.chord_interior_nonempty
  have hyInside12 : y ∈ G.J12.interiorRegion :=
    (G.chord_subset hyB3).resolve_left hyEndpoint
  have hyFrontier13 : y ∈ frontier G.J13.interiorRegion := by
    rw [G.J13.frontier_interiorRegion, G.carrier13]
    exact Or.inr hyB3
  have hyClosure : y ∈ closure
      (G.J12.interiorRegion ∩ G.J13.interiorRegion) :=
    G.J12.isOpen_interiorRegion.inter_closure
      ⟨hyInside12, frontier_subset_closure hyFrontier13⟩
  obtain ⟨z, hz12, hz13⟩ := Set.Nonempty.of_closure ⟨y, hyClosure⟩
  exact G.J13.isConnected_interiorRegion.isPreconnected.subset_left_of_subset_union
    G.J12.isOpen_interiorRegion G.J12.isOpen_exteriorRegion
    G.J12.disjoint_interior_exterior hsubsetUnion ⟨z, hz13, hz12⟩

/-- Exchange the two boundary arcs of a theta graph. -/
def swap12 : PolygonalTheta where
  P := G.P
  Q := G.Q
  B1 := G.B2
  B2 := G.B1
  B3 := G.B3
  J12 := G.J12
  J13 := G.J23
  J23 := G.J13
  P_mem_B1 := G.P_mem_B2
  Q_mem_B1 := G.Q_mem_B2
  P_mem_B2 := G.P_mem_B1
  Q_mem_B2 := G.Q_mem_B1
  P_mem_B3 := G.P_mem_B3
  Q_mem_B3 := G.Q_mem_B3
  B1_inter_B2 := by rw [Set.inter_comm, G.B1_inter_B2]
  B1_inter_B3 := G.B2_inter_B3
  B2_inter_B3 := G.B1_inter_B3
  carrier12 := by rw [G.carrier12, Set.union_comm]
  carrier13 := G.carrier23
  carrier23 := G.carrier13
  chord_subset := G.chord_subset
  B1_interior_nonempty := G.B2_interior_nonempty
  B2_interior_nonempty := G.B1_interior_nonempty
  chord_interior_nonempty := G.chord_interior_nonempty
  index_parity := by
    intro x hx12 hx23 hx13
    rw [Nat.add_comm]
    exact G.index_parity x hx12 hx13 hx23

theorem exterior12_subset_exterior23 :
    G.J12.exteriorRegion ⊆ G.J23.exteriorRegion :=
  (G.swap12).exterior12_subset_exterior13

theorem B1_diff_endpoints_subset_exterior23 :
    G.B1 \ {G.P, G.Q} ⊆ G.J23.exteriorRegion :=
  (G.swap12).B2_diff_endpoints_subset_exterior13

theorem interior23_subset_interior12 :
    G.J23.interiorRegion ⊆ G.J12.interiorRegion :=
  (G.swap12).interior13_subset_interior12

/-- The interior of one cut-off polygon lies in the exterior of the other. -/
theorem interior13_subset_exterior23 :
    G.J13.interiorRegion ⊆ G.J23.exteriorRegion := by
  have hsubsetCompl : G.J13.interiorRegion ⊆ G.J23.carrierᶜ := by
    intro x hx13
    rw [G.carrier23]
    rintro (hxB2 | hxB3)
    · by_cases hxEndpoint : x ∈ ({G.P, G.Q} : Set Plane)
      · have hxB1 : x ∈ G.B1 := by
          rcases hxEndpoint with (rfl | rfl)
          · exact G.P_mem_B1
          · exact G.Q_mem_B1
        have hxCarrier13 : x ∈ G.J13.carrier := by rw [G.carrier13]; exact Or.inl hxB1
        have hxCompl13 : x ∈ G.J13.carrierᶜ := by
          rw [← G.J13.interior_union_exterior]
          exact Or.inl hx13
        exact hxCompl13 hxCarrier13
      · have hxExterior13 := G.B2_diff_endpoints_subset_exterior13 ⟨hxB2, hxEndpoint⟩
        exact Set.disjoint_left.mp G.J13.disjoint_interior_exterior hx13 hxExterior13
    · have hxCarrier13 : x ∈ G.J13.carrier := by rw [G.carrier13]; exact Or.inr hxB3
      have hxCompl13 : x ∈ G.J13.carrierᶜ := by
        rw [← G.J13.interior_union_exterior]
        exact Or.inl hx13
      exact hxCompl13 hxCarrier13
  have hsubsetUnion : G.J13.interiorRegion ⊆
      G.J23.interiorRegion ∪ G.J23.exteriorRegion := by
    rw [G.J23.interior_union_exterior]
    exact hsubsetCompl
  obtain ⟨y, hyB1, hyEndpoint⟩ := G.B1_interior_nonempty
  have hyExterior23 := G.B1_diff_endpoints_subset_exterior23 ⟨hyB1, hyEndpoint⟩
  have hyFrontier13 : y ∈ frontier G.J13.interiorRegion := by
    rw [G.J13.frontier_interiorRegion, G.carrier13]
    exact Or.inl hyB1
  have hyClosure : y ∈ closure
      (G.J23.exteriorRegion ∩ G.J13.interiorRegion) :=
    G.J23.isOpen_exteriorRegion.inter_closure
      ⟨hyExterior23, frontier_subset_closure hyFrontier13⟩
  obtain ⟨z, hz23, hz13⟩ := Set.Nonempty.of_closure ⟨y, hyClosure⟩
  exact G.J13.isConnected_interiorRegion.isPreconnected.subset_right_of_subset_union
    G.J23.isOpen_interiorRegion G.J23.isOpen_exteriorRegion
    G.J23.disjoint_interior_exterior hsubsetUnion ⟨z, hz13, hz23⟩

theorem interior23_subset_exterior13 :
    G.J23.interiorRegion ⊆ G.J13.exteriorRegion :=
  (G.swap12).interior13_subset_exterior23

/-- The two polygons cut off by the chord have disjoint interiors. -/
theorem disjoint_interior13_interior23 :
    Disjoint G.J13.interiorRegion G.J23.interiorRegion := by
  have hsubsetCompl : G.J13.interiorRegion ⊆ G.J23.carrierᶜ := by
    intro x hx13
    rw [G.carrier23]
    rintro (hxB2 | hxB3)
    · by_cases hxEndpoint : x ∈ ({G.P, G.Q} : Set Plane)
      · have hxB1 : x ∈ G.B1 := by
          rcases hxEndpoint with (rfl | rfl)
          · exact G.P_mem_B1
          · exact G.Q_mem_B1
        have hxCarrier13 : x ∈ G.J13.carrier := by rw [G.carrier13]; exact Or.inl hxB1
        have hxCompl13 : x ∈ G.J13.carrierᶜ := by
          rw [← G.J13.interior_union_exterior]
          exact Or.inl hx13
        exact hxCompl13 hxCarrier13
      · have hxExterior13 := G.B2_diff_endpoints_subset_exterior13 ⟨hxB2, hxEndpoint⟩
        exact Set.disjoint_left.mp G.J13.disjoint_interior_exterior hx13 hxExterior13
    · have hxCarrier13 : x ∈ G.J13.carrier := by rw [G.carrier13]; exact Or.inr hxB3
      have hxCompl13 : x ∈ G.J13.carrierᶜ := by
        rw [← G.J13.interior_union_exterior]
        exact Or.inl hx13
      exact hxCompl13 hxCarrier13
  have hsubsetUnion : G.J13.interiorRegion ⊆
      G.J23.interiorRegion ∪ G.J23.exteriorRegion := by
    rw [G.J23.interior_union_exterior]
    exact hsubsetCompl
  obtain ⟨y, hyB1, hyEndpoint⟩ := G.B1_interior_nonempty
  have hyExterior23 := G.B1_diff_endpoints_subset_exterior23 ⟨hyB1, hyEndpoint⟩
  have hyFrontier13 : y ∈ frontier G.J13.interiorRegion := by
    rw [G.J13.frontier_interiorRegion, G.carrier13]
    exact Or.inl hyB1
  have hyClosure : y ∈ closure
      (G.J23.exteriorRegion ∩ G.J13.interiorRegion) :=
    G.J23.isOpen_exteriorRegion.inter_closure
      ⟨hyExterior23, frontier_subset_closure hyFrontier13⟩
  obtain ⟨z, hz23, hz13⟩ := Set.Nonempty.of_closure ⟨y, hyClosure⟩
  have hallExterior : G.J13.interiorRegion ⊆ G.J23.exteriorRegion :=
    G.J13.isConnected_interiorRegion.isPreconnected.subset_right_of_subset_union
      G.J23.isOpen_interiorRegion G.J23.isOpen_exteriorRegion
      G.J23.disjoint_interior_exterior hsubsetUnion ⟨z, hz13, hz23⟩
  exact Set.disjoint_left.mpr fun x hx13 hx23 =>
    Set.disjoint_left.mp G.J23.disjoint_interior_exterior hx23 (hallExterior hx13)

/-- The two closed subdisks cut off by a proper chord meet exactly in that chord. -/
theorem closedRegion13_inter_closedRegion23 :
    G.J13.closedRegion ∩ G.J23.closedRegion = G.B3 := by
  rw [G.J13.closedRegion_eq_union, G.J23.closedRegion_eq_union,
    G.carrier13, G.carrier23]
  ext x
  constructor
  · rintro ⟨hx13, hx23⟩
    rcases hx13 with hxInt13 | hxB1 | hxB3
    · have hxExt23 := G.interior13_subset_exterior23 hxInt13
      rcases hx23 with hxInt23 | hxCarrier23
      · exact False.elim <|
          Set.disjoint_left.mp G.J23.disjoint_interior_exterior hxInt23 hxExt23
      · have hxCompl : x ∈ G.J23.carrierᶜ := by
          rw [← G.J23.interior_union_exterior]
          exact Or.inr hxExt23
        have hxCarrier23' : x ∈ G.J23.carrier := by
          rw [G.carrier23]
          exact hxCarrier23
        exact False.elim (hxCompl hxCarrier23')
    · rcases hx23 with hxInt23 | hxB2 | hxB3
      · have hxExt13 := G.interior23_subset_exterior13 hxInt23
        have hxCarrier13 : x ∈ G.J13.carrier := by rw [G.carrier13]; exact Or.inl hxB1
        have hxCompl : x ∈ G.J13.carrierᶜ := by
          rw [← G.J13.interior_union_exterior]
          exact Or.inr hxExt13
        exact False.elim (hxCompl hxCarrier13)
      · have hxEndpoint : x ∈ ({G.P, G.Q} : Set Plane) := by
          rw [← G.B1_inter_B2]
          exact ⟨hxB1, hxB2⟩
        rcases hxEndpoint with (rfl | rfl)
        · exact G.P_mem_B3
        · exact G.Q_mem_B3
      · exact hxB3
    · exact hxB3
  · intro hxB3
    exact ⟨Or.inr (Or.inr hxB3), Or.inr (Or.inr hxB3)⟩

theorem interior12_diff_chord_subset :
    G.J12.interiorRegion \ G.B3 ⊆ G.J13.interiorRegion ∪ G.J23.interiorRegion := by
  intro x hx
  have hxNotB1 : x ∉ G.B1 := by
    intro hxB1
    have hxCarrier : x ∈ G.J12.carrier := by rw [G.carrier12]; exact Or.inl hxB1
    have hxCompl : x ∈ G.J12.carrierᶜ := by
      rw [← G.J12.interior_union_exterior]
      exact Or.inl hx.1
    exact hxCompl hxCarrier
  have hxNotB2 : x ∉ G.B2 := by
    intro hxB2
    have hxCarrier : x ∈ G.J12.carrier := by rw [G.carrier12]; exact Or.inr hxB2
    have hxCompl : x ∈ G.J12.carrierᶜ := by
      rw [← G.J12.interior_union_exterior]
      exact Or.inl hx.1
    exact hxCompl hxCarrier
  have hxNot13 : x ∉ G.J13.carrier := by
    rw [G.carrier13]
    rintro (hxB1 | hxB3)
    · exact hxNotB1 hxB1
    · exact hx.2 hxB3
  have hxNot23 : x ∉ G.J23.carrier := by
    rw [G.carrier23]
    rintro (hxB2 | hxB3)
    · exact hxNotB2 hxB2
    · exact hx.2 hxB3
  have hxNot12 : x ∉ G.J12.carrier := by
    rw [G.carrier12]
    rintro (hxB1 | hxB2)
    · exact hxNotB1 hxB1
    · exact hxNotB2 hxB2
  have hxSplit13 : x ∈ G.J13.interiorRegion ∪ G.J13.exteriorRegion := by
    rw [G.J13.interior_union_exterior]
    exact hxNot13
  have hxSplit23 : x ∈ G.J23.interiorRegion ∪ G.J23.exteriorRegion := by
    rw [G.J23.interior_union_exterior]
    exact hxNot23
  rcases hxSplit13 with hx13 | hx13
  · exact Or.inl hx13
  rcases hxSplit23 with hx23 | hx23
  · exact Or.inr hx23
  exfalso
  have hindex12 : G.J12.index x = 1 := by
    have hm : x ∈ G.J12.indexRegion 1 := by
      rw [← G.J12.interiorRegion_eq_indexRegion_one]
      exact hx.1
    exact hm.2
  have hindex13 : G.J13.index x = 0 := by
    have hm : x ∈ G.J13.indexRegion 0 := by
      rw [← G.J13.exteriorRegion_eq_indexRegion_zero]
      exact hx13
    exact hm.2
  have hindex23 : G.J23.index x = 0 := by
    have hm : x ∈ G.J23.indexRegion 0 := by
      rw [← G.J23.exteriorRegion_eq_indexRegion_zero]
      exact hx23
    exact hm.2
  have hparity := G.index_parity x hxNot12 hxNot13 hxNot23
  rw [hindex12, hindex13, hindex23] at hparity
  norm_num at hparity

/-- Moise Chapter 2, Theorem 8(2): the two chord polygons exactly fill the original closed
polygonal disk. -/
theorem closedRegion_eq_union :
    G.J12.closedRegion = G.J13.closedRegion ∪ G.J23.closedRegion := by
  rw [G.J12.closedRegion_eq_union, G.J13.closedRegion_eq_union,
    G.J23.closedRegion_eq_union]
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with hxInterior | hxCarrier
    · by_cases hxB3 : x ∈ G.B3
      · left
        exact Or.inr (by rw [G.carrier13]; exact Or.inr hxB3)
      · rcases G.interior12_diff_chord_subset ⟨hxInterior, hxB3⟩ with hx13 | hx23
        · exact Or.inl (Or.inl hx13)
        · exact Or.inr (Or.inl hx23)
    · rw [G.carrier12] at hxCarrier
      rcases hxCarrier with hxB1 | hxB2
      · exact Or.inl (Or.inr (by rw [G.carrier13]; exact Or.inl hxB1))
      · exact Or.inr (Or.inr (by rw [G.carrier23]; exact Or.inl hxB2))
  · intro x
    rintro (hx13 | hx23)
    · rcases hx13 with hxInterior | hxCarrier
      · exact Or.inl (G.interior13_subset_interior12 hxInterior)
      · rw [G.carrier13] at hxCarrier
        rcases hxCarrier with hxB1 | hxB3
        · exact Or.inr (by rw [G.carrier12]; exact Or.inl hxB1)
        · rcases G.chord_subset hxB3 with hxEndpoint | hxInterior
          · exact Or.inr (G.endpoints_subset_carrier12 hxEndpoint)
          · exact Or.inl hxInterior
    · rcases hx23 with hxInterior | hxCarrier
      · exact Or.inl (G.interior23_subset_interior12 hxInterior)
      · rw [G.carrier23] at hxCarrier
        rcases hxCarrier with hxB2 | hxB3
        · exact Or.inr (by rw [G.carrier12]; exact Or.inr hxB2)
        · rcases G.chord_subset hxB3 with hxEndpoint | hxInterior
          · exact Or.inr (G.endpoints_subset_carrier12 hxEndpoint)
          · exact Or.inl hxInterior

namespace MeshCrosscut

variable {G : PolygonalTheta} {M : TriangleMesh} (C : G.MeshCrosscut M)

/-- Exchange the two sides of a realized mesh crosscut. -/
noncomputable def swap12 (C : G.MeshCrosscut M) : G.swap12.MeshCrosscut M where
  support_eq := C.support_eq
  chordEdge := C.chordEdge
  chordEdge_mem := C.chordEdge_mem
  chordVertices := C.chordVertices
  chordCarrier := C.chordCarrier

/-- A mesh triangle lies wholly on one side of a realized crosscut. -/
theorem triangle_interior_side (C : G.MeshCrosscut M) (T : M.Triangle) :
    interior (M.triangleCarrier T.1) ⊆ G.J13.interiorRegion ∨
      interior (M.triangleCarrier T.1) ⊆ G.J23.interiorRegion := by
  have htriangleSupport : M.triangleCarrier T.1 ⊆ M.toPlaneComplex.support := by
    rw [M.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset T.1
      (Set.subset_iUnion_of_subset T.2 subset_rfl)
  have hinside12 : interior (M.triangleCarrier T.1) ⊆ G.J12.interiorRegion := by
    rw [← G.J12.interior_closedRegion,
      ← PolygonalTheta.MeshCrosscut.support_eq C]
    exact interior_mono htriangleSupport
  have hdisjointChord :
      Disjoint (interior (M.triangleCarrier T.1)) G.B3 := by
    rw [← PolygonalTheta.MeshCrosscut.chordCarrier C]
    exact M.disjoint_interior_triangleCarrier_edgeCarrier T
      (PolygonalTheta.MeshCrosscut.chordEdge_mem C)
  have hsplit : interior (M.triangleCarrier T.1) ⊆
      G.J13.interiorRegion ∪ G.J23.interiorRegion := by
    intro p hp
    exact G.interior12_diff_chord_subset
      ⟨hinside12 hp, fun hpChord => Set.disjoint_left.mp hdisjointChord hp hpChord⟩
  obtain ⟨p, hp⟩ := M.interior_triangleCarrier_nonempty T
  rcases hsplit hp with hp13 | hp23
  · exact Or.inl <|
      (convex_convexHull ℝ _).interior.isPreconnected.subset_left_of_subset_union
        G.J13.isOpen_interiorRegion G.J23.isOpen_interiorRegion
        G.disjoint_interior13_interior23 hsplit ⟨p, hp, hp13⟩
  · exact Or.inr <|
      (convex_convexHull ℝ _).interior.isPreconnected.subset_right_of_subset_union
        G.J13.isOpen_interiorRegion G.J23.isOpen_interiorRegion
        G.disjoint_interior13_interior23 hsplit ⟨p, hp, hp23⟩

/-- Select the maximal triangles lying on the `J13` side of the crosscut. -/
noncomputable def side13Mesh (_ : G.MeshCrosscut M) : TriangleMesh := by
  classical
  exact M.restrictTriangles fun t =>
    (interior (M.triangleCarrier t) ∩ G.J13.interiorRegion).Nonempty

/-- Select the maximal triangles lying on the `J23` side of the crosscut. -/
noncomputable def side23Mesh (_ : G.MeshCrosscut M) : TriangleMesh := by
  classical
  exact M.restrictTriangles fun t =>
    (interior (M.triangleCarrier t) ∩ G.J23.interiorRegion).Nonempty

@[simp] theorem swap12_side13Mesh : C.swap12.side13Mesh = C.side23Mesh := rfl

@[simp] theorem swap12_side23Mesh : C.swap12.side23Mesh = C.side13Mesh := rfl

private theorem triangleCarrier_subset_side13 {t : Finset M.Vertex}
    (ht : t ∈ C.side13Mesh.triangles) :
    M.triangleCarrier t ⊆ G.J13.closedRegion := by
  classical
  have htM : t ∈ M.triangles :=
    (M.mem_restrictTriangles_triangles fun u =>
      (interior (M.triangleCarrier u) ∩ G.J13.interiorRegion).Nonempty).mp ht |>.1
  have hmeet : (interior (M.triangleCarrier t) ∩ G.J13.interiorRegion).Nonempty :=
    (M.mem_restrictTriangles_triangles fun u =>
      (interior (M.triangleCarrier u) ∩ G.J13.interiorRegion).Nonempty).mp ht |>.2
  let T : M.Triangle := ⟨t, htM⟩
  have hside : interior (M.triangleCarrier t) ⊆ G.J13.interiorRegion := by
    rcases triangle_interior_side C T with h13 | h23
    · exact h13
    · obtain ⟨p, hpT, hp13⟩ := hmeet
      exact False.elim <| Set.disjoint_left.mp G.disjoint_interior13_interior23
        hp13 (h23 hpT)
  rw [← M.closure_interior_triangleCarrier T, PolygonalCircle.closedRegion]
  exact closure_mono hside

private theorem triangleCarrier_subset_side23 {t : Finset M.Vertex}
    (ht : t ∈ C.side23Mesh.triangles) :
    M.triangleCarrier t ⊆ G.J23.closedRegion := by
  classical
  have htM : t ∈ M.triangles :=
    (M.mem_restrictTriangles_triangles fun u =>
      (interior (M.triangleCarrier u) ∩ G.J23.interiorRegion).Nonempty).mp ht |>.1
  have hmeet : (interior (M.triangleCarrier t) ∩ G.J23.interiorRegion).Nonempty :=
    (M.mem_restrictTriangles_triangles fun u =>
      (interior (M.triangleCarrier u) ∩ G.J23.interiorRegion).Nonempty).mp ht |>.2
  let T : M.Triangle := ⟨t, htM⟩
  have hside : interior (M.triangleCarrier t) ⊆ G.J23.interiorRegion := by
    rcases triangle_interior_side C T with h13 | h23
    · obtain ⟨p, hpT, hp23⟩ := hmeet
      exact False.elim <| Set.disjoint_left.mp G.disjoint_interior13_interior23
        (h13 hpT) hp23
    · exact h23
  rw [← M.closure_interior_triangleCarrier T, PolygonalCircle.closedRegion]
  exact closure_mono hside

/-- Restricting along a realized crosscut gives exactly the first closed polygonal subdisk. -/
theorem side13Mesh_support :
    C.side13Mesh.toPlaneComplex.support = G.J13.closedRegion := by
  classical
  apply Set.Subset.antisymm
  · rw [TriangleMesh.toPlaneComplex_support]
    intro p hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨t, ht, hpt⟩ := hp
    exact C.triangleCarrier_subset_side13 ht hpt
  · rw [PolygonalCircle.closedRegion]
    apply closure_minimal _ C.side13Mesh.toPlaneComplex.isCompact_support.isClosed
    intro p hp13
    have hp12 : p ∈ G.J12.closedRegion := by
      rw [G.closedRegion_eq_union]
      exact Or.inl (by rw [G.J13.closedRegion_eq_union]; exact Or.inl hp13)
    have hpSupport : p ∈ M.toPlaneComplex.support := by
      rwa [PolygonalTheta.MeshCrosscut.support_eq C]
    rw [M.toPlaneComplex_support] at hpSupport
    simp only [Set.mem_iUnion] at hpSupport
    obtain ⟨t, ht, hpt⟩ := hpSupport
    let T : M.Triangle := ⟨t, ht⟩
    have hpClosure : p ∈ closure (interior (M.triangleCarrier t)) := by
      rw [M.closure_interior_triangleCarrier T]
      exact hpt
    have hpInterClosure : p ∈ closure
        (G.J13.interiorRegion ∩ interior (M.triangleCarrier t)) :=
      G.J13.isOpen_interiorRegion.inter_closure ⟨hp13, hpClosure⟩
    have hmeet :
        (interior (M.triangleCarrier t) ∩ G.J13.interiorRegion).Nonempty := by
      obtain ⟨q, hq13, hqt⟩ := Set.Nonempty.of_closure ⟨p, hpInterClosure⟩
      exact ⟨q, hqt, hq13⟩
    rw [TriangleMesh.toPlaneComplex_support]
    exact Set.mem_iUnion_of_mem t <| Set.mem_iUnion_of_mem
      ((M.mem_restrictTriangles_triangles fun u =>
        (interior (M.triangleCarrier u) ∩ G.J13.interiorRegion).Nonempty).mpr
          ⟨ht, hmeet⟩) hpt

/-- Restricting along a realized crosscut gives exactly the second closed polygonal subdisk. -/
theorem side23Mesh_support :
    C.side23Mesh.toPlaneComplex.support = G.J23.closedRegion := by
  classical
  apply Set.Subset.antisymm
  · rw [TriangleMesh.toPlaneComplex_support]
    intro p hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨t, ht, hpt⟩ := hp
    exact C.triangleCarrier_subset_side23 ht hpt
  · rw [PolygonalCircle.closedRegion]
    apply closure_minimal _ C.side23Mesh.toPlaneComplex.isCompact_support.isClosed
    intro p hp23
    have hp12 : p ∈ G.J12.closedRegion := by
      rw [G.closedRegion_eq_union]
      exact Or.inr (by rw [G.J23.closedRegion_eq_union]; exact Or.inl hp23)
    have hpSupport : p ∈ M.toPlaneComplex.support := by
      rwa [PolygonalTheta.MeshCrosscut.support_eq C]
    rw [M.toPlaneComplex_support] at hpSupport
    simp only [Set.mem_iUnion] at hpSupport
    obtain ⟨t, ht, hpt⟩ := hpSupport
    let T : M.Triangle := ⟨t, ht⟩
    have hpClosure : p ∈ closure (interior (M.triangleCarrier t)) := by
      rw [M.closure_interior_triangleCarrier T]
      exact hpt
    have hpInterClosure : p ∈ closure
        (G.J23.interiorRegion ∩ interior (M.triangleCarrier t)) :=
      G.J23.isOpen_interiorRegion.inter_closure ⟨hp23, hpClosure⟩
    have hmeet :
        (interior (M.triangleCarrier t) ∩ G.J23.interiorRegion).Nonempty := by
      obtain ⟨q, hq23, hqt⟩ := Set.Nonempty.of_closure ⟨p, hpInterClosure⟩
      exact ⟨q, hqt, hq23⟩
    rw [TriangleMesh.toPlaneComplex_support]
    exact Set.mem_iUnion_of_mem t <| Set.mem_iUnion_of_mem
      ((M.mem_restrictTriangles_triangles fun u =>
        (interior (M.triangleCarrier u) ∩ G.J23.interiorRegion).Nonempty).mpr
          ⟨ht, hmeet⟩) hpt

theorem mem_side13Mesh_triangles_iff {t : Finset M.Vertex} :
    t ∈ C.side13Mesh.triangles ↔ t ∈ M.triangles ∧
      interior (M.triangleCarrier t) ⊆ G.J13.interiorRegion := by
  classical
  change t ∈ (M.restrictTriangles fun u =>
    (interior (M.triangleCarrier u) ∩ G.J13.interiorRegion).Nonempty).triangles ↔ _
  rw [M.mem_restrictTriangles_triangles]
  constructor
  · rintro ⟨ht, hmeet⟩
    let T : M.Triangle := ⟨t, ht⟩
    refine ⟨ht, ?_⟩
    rcases triangle_interior_side C T with h13 | h23
    · exact h13
    · obtain ⟨p, hpT, hp13⟩ := hmeet
      exact False.elim <| Set.disjoint_left.mp G.disjoint_interior13_interior23
        hp13 (h23 hpT)
  · rintro ⟨ht, hside⟩
    obtain ⟨p, hp⟩ := M.interior_triangleCarrier_nonempty ⟨t, ht⟩
    exact ⟨ht, p, hp, hside hp⟩

theorem mem_side23Mesh_triangles_iff {t : Finset M.Vertex} :
    t ∈ C.side23Mesh.triangles ↔ t ∈ M.triangles ∧
      interior (M.triangleCarrier t) ⊆ G.J23.interiorRegion := by
  classical
  change t ∈ (M.restrictTriangles fun u =>
    (interior (M.triangleCarrier u) ∩ G.J23.interiorRegion).Nonempty).triangles ↔ _
  rw [M.mem_restrictTriangles_triangles]
  constructor
  · rintro ⟨ht, hmeet⟩
    let T : M.Triangle := ⟨t, ht⟩
    refine ⟨ht, ?_⟩
    rcases triangle_interior_side C T with h13 | h23
    · obtain ⟨p, hpT, hp23⟩ := hmeet
      exact False.elim <| Set.disjoint_left.mp G.disjoint_interior13_interior23
        (h13 hpT) hp23
    · exact h23
  · rintro ⟨ht, hside⟩
    obtain ⟨p, hp⟩ := M.interior_triangleCarrier_nonempty ⟨t, ht⟩
    exact ⟨ht, p, hp, hside hp⟩

/-- The two restricted triangle sets partition the original mesh. -/
theorem side_triangles_union :
    C.side13Mesh.triangles ∪ C.side23Mesh.triangles = M.triangles := by
  classical
  ext t
  constructor
  · intro ht
    rcases Finset.mem_union.mp ht with ht13 | ht23
    · exact (C.mem_side13Mesh_triangles_iff.mp ht13).1
    · exact (C.mem_side23Mesh_triangles_iff.mp ht23).1
  · intro ht
    let T : M.Triangle := ⟨t, ht⟩
    rcases triangle_interior_side C T with h13 | h23
    · exact Finset.mem_union_left _ <| C.mem_side13Mesh_triangles_iff.mpr ⟨ht, h13⟩
    · exact Finset.mem_union_right _ <| C.mem_side23Mesh_triangles_iff.mpr ⟨ht, h23⟩

/-- No maximal triangle occurs on both sides of the crosscut. -/
theorem disjoint_side_triangles :
    Disjoint C.side13Mesh.triangles C.side23Mesh.triangles := by
  classical
  apply Finset.disjoint_left.mpr
  intro t ht13 ht23
  have h13 := (C.mem_side13Mesh_triangles_iff.mp ht13).2
  have h23 := (C.mem_side23Mesh_triangles_iff.mp ht23).2
  obtain ⟨p, hp⟩ := M.interior_triangleCarrier_nonempty
    ⟨t, (C.mem_side13Mesh_triangles_iff.mp ht13).1⟩
  exact Set.disjoint_left.mp G.disjoint_interior13_interior23 (h13 hp) (h23 hp)

theorem side13_triangles_nonempty : C.side13Mesh.triangles.Nonempty := by
  obtain ⟨p, hp⟩ := G.J13.isConnected_interiorRegion.nonempty
  have hpSupport : p ∈ C.side13Mesh.toPlaneComplex.support := by
    rw [C.side13Mesh_support, G.J13.closedRegion_eq_union]
    exact Or.inl hp
  rw [TriangleMesh.toPlaneComplex_support] at hpSupport
  simp only [Set.mem_iUnion] at hpSupport
  obtain ⟨t, ht, -⟩ := hpSupport
  exact ⟨t, ht⟩

theorem side23_triangles_nonempty : C.side23Mesh.triangles.Nonempty := by
  obtain ⟨p, hp⟩ := G.J23.isConnected_interiorRegion.nonempty
  have hpSupport : p ∈ C.side23Mesh.toPlaneComplex.support := by
    rw [C.side23Mesh_support, G.J23.closedRegion_eq_union]
    exact Or.inl hp
  rw [TriangleMesh.toPlaneComplex_support] at hpSupport
  simp only [Set.mem_iUnion] at hpSupport
  obtain ⟨t, ht, -⟩ := hpSupport
  exact ⟨t, ht⟩

/-- Each side of a proper realized crosscut has strictly fewer maximal triangles. -/
theorem card_side13_triangles_lt :
    C.side13Mesh.triangles.card < M.triangles.card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro t ht
    exact (C.mem_side13Mesh_triangles_iff.mp ht).1
  · intro heq
    obtain ⟨t, ht23⟩ := C.side23_triangles_nonempty
    have htM := (C.mem_side23Mesh_triangles_iff.mp ht23).1
    have ht13 : t ∈ C.side13Mesh.triangles := by rwa [heq]
    exact Finset.disjoint_left.mp C.disjoint_side_triangles ht13 ht23

theorem card_side23_triangles_lt :
    C.side23Mesh.triangles.card < M.triangles.card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro t ht
    exact (C.mem_side23Mesh_triangles_iff.mp ht).1
  · intro heq
    obtain ⟨t, ht13⟩ := C.side13_triangles_nonempty
    have htM := (C.mem_side13Mesh_triangles_iff.mp ht13).1
    have ht23 : t ∈ C.side23Mesh.triangles := by rwa [heq]
    exact Finset.disjoint_left.mp C.disjoint_side_triangles ht13 ht23

end MeshCrosscut

end PolygonalTheta

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification07_block_01
/- END ClassificationOfSurfaces.Moise.PolygonalCrosscut -/

/- BEGIN ClassificationOfSurfaces.Moise.AdaptiveOpenComplex | eb74dc0567f77b312364a70cb9d050bdfeb718965b17152080a9396eee2ee3d2 -/
section schottkyclassification07_block_02
/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/

/-!
# Adaptive midpoint tiles in an open polyhedron

Select the first triangle in each midpoint-descendant chain whose complete carrier lies in an
open set.  These triangles cover the open set and form a locally finite hierarchical tiling.
Their edges need not yet form a conforming simplicial complex: a coarse edge may contain several
edges of finer adjacent tiles.  The next layer resolves precisely those hanging vertices.
-/

open scoped BigOperators

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex) (U : Set K.realization)

/-- A maximal face at midpoint level `n`. -/
abbrev LevelFace (n : ℕ) := (K.safeSubdivision n).refined.Face

/-- The carrier of a level face, transported back to the original realization. -/
def levelFaceCarrier {n : ℕ} (t : K.LevelFace n) : Set K.realization :=
  (K.safeSubdivision n).homeo ''
    (K.safeSubdivision n).refined.faceCarrier t.1

theorem isCompact_levelFaceCarrier {n : ℕ} (t : K.LevelFace n) :
    IsCompact (K.levelFaceCarrier t) :=
  ((K.safeSubdivision n).refined.faceCarrier_closed t.1).isCompact.image
    (K.safeSubdivision n).homeo.continuous

/-- A hereditary rule selecting sufficiently small level faces inside `U`.

The default rule is simple containment in `U`.  A stricter local rule can be installed as a
local instance, allowing the conforming adaptive fan construction to be reused for open-cover,
oscillation, separation, and boundary-control requirements. -/
class AdaptiveSafety (K : IntrinsicTwoComplex) (U : Set K.realization) where
  /-- The `safe` declaration. -/
  safe : {n : ℕ} → K.LevelFace n → Prop
  carrier_subset : ∀ {n : ℕ} {t : K.LevelFace n}, safe t →
    K.levelFaceCarrier t ⊆ U
  hereditary : ∀ {n m : ℕ} {s : K.LevelFace n} {t : K.LevelFace m},
    K.levelFaceCarrier t ⊆ K.levelFaceCarrier s → safe s → safe t

/-- The original safety rule: a face is safe exactly when its carrier lies in `U`.  Its low
priority lets a quantitative chart-control rule override it locally without changing any of the
adaptive combinatorial APIs. -/
instance (priority := 100) defaultAdaptiveSafety : AdaptiveSafety K U where
  safe t := K.levelFaceCarrier t ⊆ U
  carrier_subset ht := ht
  hereditary hts hs := hts.trans hs

/-- The active safety predicate. -/
def LevelFace.IsSafe [AdaptiveSafety K U] {n : ℕ} (t : K.LevelFace n) : Prop :=
  AdaptiveSafety.safe (K := K) (U := U) t

theorem levelFace_isSafe_iff {n : ℕ} (t : K.LevelFace n) :
    @LevelFace.IsSafe K U (defaultAdaptiveSafety K U) n t ↔
      t.1 ∈ K.safeFaces U n := by
  classical
  change (K.levelFaceCarrier t ⊆ U) ↔ _
  rw [safeFaces, Finset.mem_filter]
  constructor
  · intro ht
    refine ⟨t.2, ?_⟩
    intro x hx
    exact ht ⟨x, hx, rfl⟩
  · rintro ⟨-, ht⟩
    rintro z ⟨x, hx, rfl⟩
    exact ht x hx

/-- The chosen parent one level above an iterated midpoint face. -/
noncomputable def levelParentFace (n : ℕ) (t : K.LevelFace (n + 1)) : K.LevelFace n := by
  let R := K.safeSubdivision n
  change R.refined.midpointComplex.Face at t
  exact R.refined.midpointParentFace t

/-- Local attainability hypotheses for an adaptive safety rule.  The first field guarantees
coverage.  The second says that sufficiently fine children meeting a fixed neighborhood have a
safe parent; this is exactly the condition that makes first-safe faces locally finite. -/
class AdaptiveSafety.IsAdmissible [AdaptiveSafety K U] : Prop where
  exists_safe : IsOpen U → ∀ {p : K.realization}, p ∈ U →
    ∃ (n : ℕ) (t : K.LevelFace n),
      LevelFace.IsSafe K U t ∧ p ∈ K.levelFaceCarrier t
  locally_parent_safe : IsOpen U → ∀ p : U,
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → ∀ t : K.LevelFace (n + 1),
        (K.levelFaceCarrier t ∩ Metric.ball p.1 (ε / 2)).Nonempty →
          LevelFace.IsSafe K U (K.levelParentFace n t)

theorem levelFaceCarrier_subset_parent (n : ℕ) (t : K.LevelFace (n + 1)) :
    K.levelFaceCarrier t ⊆ K.levelFaceCarrier (K.levelParentFace n t) := by
  let R := K.safeSubdivision n
  change R.refined.midpointComplex.Face at t
  rintro z ⟨x, hx, rfl⟩
  let p : R.refined.realization := R.refined.midpointHomeomorph x
  refine ⟨p, ?_, rfl⟩
  exact R.refined.midpointEval_mem_parentFace
    (R.refined.midpointParentFace t) (R.refined.midpointFace_mem_parent t) x hx

/-- Every point of a level face lies in a child face at the next midpoint level whose entire
transported carrier remains in the parent carrier. -/
theorem exists_levelFace_succ_containing {n : ℕ} (t : K.LevelFace n)
    {p : K.realization} (hp : p ∈ K.levelFaceCarrier t) :
    ∃ u : K.LevelFace (n + 1),
      p ∈ K.levelFaceCarrier u ∧
        K.levelFaceCarrier u ⊆ K.levelFaceCarrier t := by
  let R := K.safeSubdivision n
  obtain ⟨x, hxt, hxp⟩ := hp
  obtain ⟨y, s, hsOver, hys, heval⟩ :=
    R.refined.exists_midpoint_preimage_in_face t x hxt
  have hsFace : s ∈ R.refined.midpointComplex.faces := by
    change s ∈ R.refined.midpointFaces
    rw [IntrinsicTwoComplex.midpointFaces]
    exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, hsOver⟩
  let u : K.LevelFace (n + 1) := by
    change R.refined.midpointComplex.Face
    exact ⟨s, hsFace⟩
  refine ⟨u, ?_, ?_⟩
  · refine ⟨y, hys, ?_⟩
    change R.homeo (R.refined.midpointHomeomorph y) = p
    rw [R.refined.midpointHomeomorph_apply]
    have hxy : R.refined.midpointEval y = x := Subtype.ext heval
    rw [hxy]
    exact hxp
  · rintro q ⟨z, hzu, rfl⟩
    let w : R.refined.realization := R.refined.midpointEval z
    refine ⟨w, ?_, rfl⟩
    exact R.refined.midpointEval_mem_parentFace t hsOver z hzu

/-- Containment in an open set is an admissible adaptive safety rule. -/
instance (priority := 100) defaultAdaptiveSafety_admissible :
    @AdaptiveSafety.IsAdmissible K U (defaultAdaptiveSafety K U) := by
  refine { exists_safe := ?_, locally_parent_safe := ?_ }
  · intro hU p hp
    classical
    obtain ⟨n, hn⟩ := K.mem_safeStageSupport_of_mem U hU hp
    obtain ⟨x, hx⟩ := hn
    rcases x.2.2 with ⟨t, ht, hxt⟩
    let q : (K.safeSubdivision n).refined.realization :=
      (K.safeSubdivision n).refined.restrictFacesInclusion
        (fun s ↦ s ∈ K.safeFaces U n) x
    let T : K.LevelFace n := ⟨t, ((Finset.mem_filter (p := fun t => t ∈ K.safeFaces U n)).mp ht).1⟩
    refine ⟨n, T, ?_, q, hxt, hx⟩
    change K.levelFaceCarrier T ⊆ U
    rintro z ⟨y, hy, rfl⟩
    exact (Finset.mem_filter.mp ((Finset.mem_filter (p := fun t => t ∈ K.safeFaces U n)).mp ht).2).2 y hy
  · intro hU p
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU p.1 p.2
    have hε2 : 0 < ε / 2 := half_pos hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε2
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨ε, hε, N, ?_⟩
    intro n hNn t hinter
    change K.levelFaceCarrier (K.levelParentFace n t) ⊆ U
    obtain ⟨z, hzFace, hzBall⟩ := hinter
    have hzParent : z ∈ K.levelFaceCarrier (K.levelParentFace n t) :=
      K.levelFaceCarrier_subset_parent n t hzFace
    have hpow : (1 / 2 : ℝ) ^ n < ε / 2 := by
      exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hNn).trans_lt hN
    intro y hy
    apply hball
    rw [Metric.mem_ball]
    calc
      dist y p.1 ≤ dist y z + dist z p.1 := dist_triangle _ _ _
      _ ≤ (1 / 2 : ℝ) ^ n + dist z p.1 := by
        gcongr
        obtain ⟨y', hy', rfl⟩ := hy
        obtain ⟨z', hz', hz'eq⟩ := hzParent
        have hz'eq' : (K.safeSubdivision n).homeo z' = z := hz'eq
        rw [← hz'eq']
        exact K.iteratedMidpointSubdivision_meshLE n
          (K.levelParentFace n t).1 (K.levelParentFace n t).2 y' hy' z' hz'
      _ < ε / 2 + ε / 2 := add_lt_add hpow hzBall
      _ = ε := by ring

variable [AdaptiveSafety K U]

/-- Iterating the preceding child-cover lemma gives a face at every later level through a
chosen point, with carrier contained in the original face. -/
theorem exists_levelFace_add_containing (n k : ℕ) (t : K.LevelFace n)
    {p : K.realization} (hp : p ∈ K.levelFaceCarrier t) :
    ∃ u : K.LevelFace (n + k),
      p ∈ K.levelFaceCarrier u ∧
        K.levelFaceCarrier u ⊆ K.levelFaceCarrier t := by
  induction k with
  | zero => exact ⟨t, hp, Set.Subset.rfl⟩
  | succ k ih =>
      obtain ⟨s, hps, hst⟩ := ih
      obtain ⟨u, hpu, hus⟩ := K.exists_levelFace_succ_containing s hps
      have hcarrier : K.levelFaceCarrier u ⊆ K.levelFaceCarrier t := hus.trans hst
      simpa only [Nat.add_assoc] using ⟨u, hpu, hcarrier⟩

/-- A level face is exactly the union of its faces at any prescribed later midpoint level.
The descendant condition is stated geometrically, which avoids choosing a combinatorial parent
for faces meeting an old edge. -/
theorem levelFaceCarrier_eq_iUnion_descendants (n k : ℕ) (t : K.LevelFace n) :
    K.levelFaceCarrier t =
      ⋃ u : K.LevelFace (n + k),
        ⋃ (_ : K.levelFaceCarrier u ⊆ K.levelFaceCarrier t),
          K.levelFaceCarrier u := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨u, hpu, hut⟩ := K.exists_levelFace_add_containing n k t hp
    exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hut, hpu⟩⟩
  · intro p hp
    obtain ⟨u, hp⟩ := Set.mem_iUnion.mp hp
    obtain ⟨hut, hpu⟩ := Set.mem_iUnion.mp hp
    exact hut hpu

/-- Exact intersection formula for two transported faces at the same midpoint level. -/
theorem levelFaceCarrier_inter {n : ℕ} (s t : K.LevelFace n) :
    K.levelFaceCarrier s ∩ K.levelFaceCarrier t =
      (K.safeSubdivision n).homeo ''
        (K.safeSubdivision n).refined.faceCarrier (s.1 ∩ t.1) := by
  rw [levelFaceCarrier, levelFaceCarrier,
    ← Set.image_inter (K.safeSubdivision n).homeo.injective,
    (K.safeSubdivision n).refined.faceCarrier_inter]

/-- Distinct maximal faces at one level share at most two vertices. -/
theorem card_inter_levelFace_le_two {n : ℕ} {s t : K.LevelFace n}
    (hst : s ≠ t) : (s.1 ∩ t.1).card ≤ 2 := by
  by_contra hcard
  have hthree : (s.1 ∩ t.1).card = 3 := by
    have hle : (s.1 ∩ t.1).card ≤ s.1.card := Finset.card_le_card Finset.inter_subset_left
    rw [(K.safeSubdivision n).refined.faces_card s.1 s.2] at hle
    omega
  have hstSets : s.1 = t.1 := by
    have hleft : s.1 ∩ t.1 = s.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
        rw [(K.safeSubdivision n).refined.faces_card s.1 s.2, hthree])
    have hright : s.1 ∩ t.1 = t.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
        rw [(K.safeSubdivision n).refined.faces_card t.1 t.2, hthree])
    exact hleft.symm.trans hright
  exact hst (Subtype.ext hstSets)

/-- A barycentric realization point supported on one face vertex is that face's canonical
vertex point. -/
theorem eq_facePoint_of_mem_faceCarrier_singleton (t : K.Face)
    (v : {v // v ∈ t.1}) (x : K.realization)
    (hx : x ∈ K.faceCarrier ({v.1} : Finset K.Vertex)) :
    x = K.facePoint t v := by
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
    rw [K.facePoint_val]
    simp [hxv]
  · rw [K.facePoint_val]
    simp [hwv, hx w (by simp [hwv])]

/-- Two two-vertex subfaces of a triangle which share a nonvertex point are equal. -/
theorem eq_of_card_two_of_mem_faceCarriers_not_vertex (t : K.Face)
    {e d : Finset K.Vertex} (het : e ⊆ t.1) (_ : d ⊆ t.1)
    (hecard : e.card = 2) (hdcard : d.card = 2)
    {x : K.realization} (hxe : x ∈ K.faceCarrier e)
    (hxd : x ∈ K.faceCarrier d)
    (hxNot : ∀ v : {v // v ∈ t.1}, x ≠ K.facePoint t v) :
    e = d := by
  by_contra hed
  have hinterLe : (e ∩ d).card ≤ 1 := by
    by_contra hnot
    have hinterTwo : (e ∩ d).card = 2 := by
      have hle : (e ∩ d).card ≤ e.card :=
        Finset.card_le_card Finset.inter_subset_left
      omega
    have hinterE : e ∩ d = e :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
        rw [hecard, hinterTwo])
    have hinterD : e ∩ d = d :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
        rw [hdcard, hinterTwo])
    exact hed (hinterE.symm.trans hinterD)
  have hxinter : x ∈ K.faceCarrier (e ∩ d) := by
    rw [← K.faceCarrier_inter e d]
    exact ⟨hxe, hxd⟩
  have hinterNonempty : (e ∩ d).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, K.faceCarrier_empty] at hxinter
    exact hxinter
  have hinterOne : (e ∩ d).card = 1 := by
    have := Finset.card_pos.mpr hinterNonempty
    omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hinterOne
  have hvt : v ∈ t.1 := het (Finset.inter_subset_left (by
    rw [hv]
    exact Finset.mem_singleton_self v))
  apply hxNot ⟨v, hvt⟩
  apply K.eq_facePoint_of_mem_faceCarrier_singleton t ⟨v, hvt⟩ x
  rwa [hv] at hxinter

theorem LevelFace.IsSafe.child {n : ℕ} {t : K.LevelFace (n + 1)}
    (ht : LevelFace.IsSafe K U (K.levelParentFace n t)) :
    LevelFace.IsSafe K U t := by
  exact AdaptiveSafety.hereditary (K := K) (U := U)
    (K.levelFaceCarrier_subset_parent n t) ht

/-- Relative interior of a transported level face, expressed by positive barycentric
coordinates on all three face vertices. -/
def levelFaceRelInterior {n : ℕ} (t : K.LevelFace n) : Set K.realization :=
  (K.safeSubdivision n).homeo ''
    {x : (K.safeSubdivision n).refined.realization |
      x ∈ (K.safeSubdivision n).refined.faceCarrier t.1 ∧
        ∀ v ∈ t.1, 0 < x.1 v}

theorem levelFaceRelInterior_subset_carrier {n : ℕ} (t : K.LevelFace n) :
    K.levelFaceRelInterior t ⊆ K.levelFaceCarrier t := by
  rintro z ⟨x, hx, rfl⟩
  exact ⟨x, hx.1, rfl⟩

/-- Midpoint subdivision sends a child's relative interior into its parent's relative
interior. -/
theorem levelFaceRelInterior_subset_parent (n : ℕ) (t : K.LevelFace (n + 1)) :
    K.levelFaceRelInterior t ⊆
      K.levelFaceRelInterior (K.levelParentFace n t) := by
  let R := K.safeSubdivision n
  change R.refined.midpointComplex.Face at t
  rintro z ⟨x, hx, rfl⟩
  let p : R.refined.realization := R.refined.midpointHomeomorph x
  refine ⟨p, ⟨?_, ?_⟩, rfl⟩
  · exact R.refined.midpointEval_mem_parentFace
      (R.refined.midpointParentFace t) (R.refined.midpointFace_mem_parent t) x hx.1
  · intro v hv
    exact R.refined.midpointEvalAffine_pos_on_parent
      (R.refined.midpointParentFace t) (R.refined.midpointFace_mem_parent t)
      hx.1 x.2.1.1 hx.2 hv

/-- At a fixed midpoint level, the relative interior of one maximal face misses the carrier of
every distinct maximal face. -/
theorem disjoint_levelFaceRelInterior_levelFaceCarrier {n : ℕ}
    {t u : K.LevelFace n} (htu : t ≠ u) :
    Disjoint (K.levelFaceRelInterior t) (K.levelFaceCarrier u) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
  have hxy : x = y := (K.safeSubdivision n).homeo.injective hyx.symm
  have hnsub : ¬t.1 ⊆ u.1 := by
    intro hsub
    apply htu
    apply Subtype.ext
    exact Finset.eq_of_subset_of_card_le hsub (by
      rw [(K.safeSubdivision n).refined.faces_card t.1 t.2,
        (K.safeSubdivision n).refined.faces_card u.1 u.2])
  obtain ⟨v, hvt, hvu⟩ := Finset.not_subset.mp hnsub
  have hyzero : y.1 v = 0 := hy v hvu
  have hcoord : x.1 v = y.1 v := congrFun (congrArg Subtype.val hxy) v
  linarith [hx.2 v hvt]

/-- The ancestor at level `n` of a face at level `n + k`. -/
noncomputable def levelAncestor (n : ℕ) :
    (k : ℕ) → K.LevelFace (n + k) → K.LevelFace n
  | 0, t => t
  | k + 1, t => levelAncestor n k (K.levelParentFace (n + k) t)

@[simp] theorem levelAncestor_zero (n : ℕ) (t : K.LevelFace n) :
    K.levelAncestor n 0 t = t := rfl

@[simp] theorem levelAncestor_succ (n k : ℕ) (t : K.LevelFace (n + (k + 1))) :
    K.levelAncestor n (k + 1) t =
      K.levelAncestor n k (K.levelParentFace (n + k) t) := rfl

theorem levelFaceCarrier_subset_ancestor (n k : ℕ)
    (t : K.LevelFace (n + k)) :
    K.levelFaceCarrier t ⊆ K.levelFaceCarrier (K.levelAncestor n k t) := by
  induction k with
  | zero => exact Set.Subset.rfl
  | succ k ih =>
      exact (K.levelFaceCarrier_subset_parent (n + k) t).trans
        (ih (K.levelParentFace (n + k) t))

theorem levelFaceRelInterior_subset_ancestor (n k : ℕ)
    (t : K.LevelFace (n + k)) :
    K.levelFaceRelInterior t ⊆ K.levelFaceRelInterior (K.levelAncestor n k t) := by
  induction k with
  | zero => exact Set.Subset.rfl
  | succ k ih =>
      exact (K.levelFaceRelInterior_subset_parent (n + k) t).trans
        (ih (K.levelParentFace (n + k) t))

theorem LevelFace.IsSafe.ancestor_child {n k : ℕ} {t : K.LevelFace (n + k)}
    (ht : LevelFace.IsSafe K U (K.levelAncestor n k t)) :
    LevelFace.IsSafe K U t := by
  exact AdaptiveSafety.hereditary (K := K) (U := U)
    (K.levelFaceCarrier_subset_ancestor n k t) ht

/-- A first-safe face is safe, but at a positive level its chosen parent is not safe. -/
def LevelFace.IsFirstSafe : {n : ℕ} → K.LevelFace n → Prop
  | 0, t => LevelFace.IsSafe K U t
  | n + 1, t => LevelFace.IsSafe K U t ∧
      ¬LevelFace.IsSafe K U (K.levelParentFace n t)

theorem LevelFace.IsFirstSafe.safe {n : ℕ} {t : K.LevelFace n}
    (ht : LevelFace.IsFirstSafe K U t) : LevelFace.IsSafe K U t := by
  cases n with
  | zero => exact ht
  | succ _ => exact ht.1

/-- A later first-safe face cannot meet the relative interior of an earlier first-safe face.
If its ancestor were the earlier face, that safe ancestor would make its immediate parent safe;
otherwise the fixed-level face-to-face property separates them. -/
theorem disjoint_firstSafeRelInterior_laterCarrier {n k : ℕ}
    {t : K.LevelFace n} {u : K.LevelFace (n + (k + 1))}
    (ht : LevelFace.IsFirstSafe K U t)
    (hu : LevelFace.IsFirstSafe K U u) :
    Disjoint (K.levelFaceRelInterior t) (K.levelFaceCarrier u) := by
  let p := K.levelParentFace (n + k) u
  by_cases hancestor : K.levelAncestor n k p = t
  · have hpSafe : LevelFace.IsSafe K U p := by
      apply LevelFace.IsSafe.ancestor_child K U
      rw [hancestor]
      exact ht.safe
    exact False.elim (hu.2 hpSafe)
  · exact (K.disjoint_levelFaceRelInterior_levelFaceCarrier
      (fun h ↦ hancestor h.symm)).mono_right
      (K.levelFaceCarrier_subset_ancestor n (k + 1) u)

/-- The relative interior of a later first-safe face also misses the entire earlier carrier. -/
theorem disjoint_laterFirstSafeRelInterior_firstSafeCarrier {n k : ℕ}
    {t : K.LevelFace n} {u : K.LevelFace (n + (k + 1))}
    (ht : LevelFace.IsFirstSafe K U t)
    (hu : LevelFace.IsFirstSafe K U u) :
    Disjoint (K.levelFaceRelInterior u) (K.levelFaceCarrier t) := by
  let p := K.levelParentFace (n + k) u
  by_cases hancestor : K.levelAncestor n k p = t
  · have hpSafe : LevelFace.IsSafe K U p := by
      apply LevelFace.IsSafe.ancestor_child K U
      rw [hancestor]
      exact ht.safe
    exact False.elim (hu.2 hpSafe)
  · exact (K.disjoint_levelFaceRelInterior_levelFaceCarrier hancestor).mono_left
      (K.levelFaceRelInterior_subset_ancestor n (k + 1) u)

theorem LevelFace.isFirstSafe_of_minimal {n : ℕ} (t : K.LevelFace n)
    {p : K.realization} (hsafe : LevelFace.IsSafe K U t)
    (hp : p ∈ K.levelFaceCarrier t)
    (hminimal : ∀ m < n, ¬∃ u : K.LevelFace m,
      LevelFace.IsSafe K U u ∧ p ∈ K.levelFaceCarrier u) :
    LevelFace.IsFirstSafe K U t := by
  cases n with
  | zero => exact hsafe
  | succ m =>
      refine ⟨hsafe, ?_⟩
      intro hparent
      apply hminimal m (Nat.lt_succ_self m)
      exact ⟨K.levelParentFace m t, hparent,
        K.levelFaceCarrier_subset_parent m t hp⟩

/-- The countable type of first-safe adaptive triangles. -/
abbrev AdaptiveFace (K : IntrinsicTwoComplex) (U : Set K.realization)
    [AdaptiveSafety K U] :=
  Σ n : ℕ, {t : K.LevelFace n // LevelFace.IsFirstSafe K U t}

/-- One common midpoint level dominating a finite family of adaptive tiles. -/
noncomputable def adaptiveFaceCommonLevel
    (F : Finset (K.AdaptiveFace U)) : ℕ :=
  F.sup fun t ↦ t.1

theorem adaptiveFace_level_le_commonLevel
    (F : Finset (K.AdaptiveFace U)) {t : K.AdaptiveFace U} (ht : t ∈ F) :
    t.1 ≤ K.adaptiveFaceCommonLevel U F := by
  exact Finset.le_sup (f := fun u : K.AdaptiveFace U ↦ u.1) ht

/-- Carrier of one adaptive triangle in the original realization. -/
def adaptiveFaceCarrier (t : K.AdaptiveFace U) : Set K.realization :=
  K.levelFaceCarrier t.2.1

/-- Every tile in a finite adaptive family is a union of faces of the family's common midpoint
level.  This is the finite source-subcomplex reduction used in the Radó crossing weld. -/
theorem adaptiveFaceCarrier_eq_iUnion_commonLevel_descendants
    (F : Finset (K.AdaptiveFace U)) {t : K.AdaptiveFace U} (ht : t ∈ F) :
    K.adaptiveFaceCarrier U t =
      ⋃ u : K.LevelFace (K.adaptiveFaceCommonLevel U F),
        ⋃ (_ : K.levelFaceCarrier u ⊆ K.adaptiveFaceCarrier U t),
          K.levelFaceCarrier u := by
  have hle := K.adaptiveFace_level_le_commonLevel U F ht
  have h := K.levelFaceCarrier_eq_iUnion_descendants t.1
    (K.adaptiveFaceCommonLevel U F - t.1) t.2.1
  rw [Nat.add_sub_of_le hle] at h
  exact h

theorem adaptiveFaceCarrier_subset (t : K.AdaptiveFace U) :
    K.adaptiveFaceCarrier U t ⊆ U := by
  rcases t with ⟨(_ | n), t⟩
  · exact AdaptiveSafety.carrier_subset (K := K) (U := U) t.2
  · exact AdaptiveSafety.carrier_subset (K := K) (U := U) t.2.1

/-- Relative interior of one adaptive face. -/
def adaptiveFaceRelInterior (t : K.AdaptiveFace U) : Set K.realization :=
  K.levelFaceRelInterior t.2.1

/-- Distinct first-safe adaptive faces meet only on their relative boundaries. -/
theorem disjoint_adaptiveFaceRelInterior_carrier
    {s t : K.AdaptiveFace U} (hst : s ≠ t) :
    Disjoint (K.adaptiveFaceRelInterior U s) (K.adaptiveFaceCarrier U t) := by
  rcases s with ⟨n, s⟩
  rcases t with ⟨m, t⟩
  rcases lt_trichotomy n m with hnm | hnm | hmn
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hnm
    have hmk : m = n + (k + 1) := by omega
    subst m
    exact K.disjoint_firstSafeRelInterior_laterCarrier U s.2 t.2
  · subst m
    have hfaces : s.1 ≠ t.1 := by
      intro hfaces
      apply hst
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (Subtype.ext hfaces)
    exact K.disjoint_levelFaceRelInterior_levelFaceCarrier hfaces
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hmn
    have hnk : n = m + (k + 1) := by omega
    subst n
    exact K.disjoint_laterFirstSafeRelInterior_firstSafeCarrier U t.2 s.2

variable [AdaptiveSafety.IsAdmissible (K := K) (U := U)]

/-- Some safe level face contains every point of the open set. -/
theorem exists_safeLevelFace_containing (hU : IsOpen U)
    {p : K.realization} (hp : p ∈ U) :
    ∃ (n : ℕ) (t : K.LevelFace n),
      LevelFace.IsSafe K U t ∧ p ∈ K.levelFaceCarrier t := by
  exact AdaptiveSafety.IsAdmissible.exists_safe (K := K) (U := U) hU hp

/-- The least midpoint level at which a safe face carries `p`. -/
noncomputable def firstSafeLevel (hU : IsOpen U) (p : U) : ℕ :=
  by
    classical
    exact Nat.find (K.exists_safeLevelFace_containing U hU p.2)

theorem exists_firstSafeLevelFace (hU : IsOpen U) (p : U) :
    ∃ t : K.LevelFace (K.firstSafeLevel U hU p),
      LevelFace.IsSafe K U t ∧ p.1 ∈ K.levelFaceCarrier t :=
  by
    classical
    exact Nat.find_spec (K.exists_safeLevelFace_containing U hU p.2)

/-- A chosen least-level safe face through `p`. -/
noncomputable def firstSafeFace (hU : IsOpen U) (p : U) :
    K.LevelFace (K.firstSafeLevel U hU p) :=
  Classical.choose (K.exists_firstSafeLevelFace U hU p)

theorem firstSafeFace_isSafe (hU : IsOpen U) (p : U) :
    LevelFace.IsSafe K U (K.firstSafeFace U hU p) :=
  (Classical.choose_spec (K.exists_firstSafeLevelFace U hU p)).1

theorem mem_firstSafeFaceCarrier (hU : IsOpen U) (p : U) :
    p.1 ∈ K.levelFaceCarrier (K.firstSafeFace U hU p) :=
  (Classical.choose_spec (K.exists_firstSafeLevelFace U hU p)).2

theorem firstSafeFace_isFirstSafe (hU : IsOpen U) (p : U) :
    LevelFace.IsFirstSafe K U (K.firstSafeFace U hU p) := by
  classical
  have hsafe := K.firstSafeFace_isSafe U hU p
  have hpface := K.mem_firstSafeFaceCarrier U hU p
  apply LevelFace.isFirstSafe_of_minimal K U _ hsafe hpface
  intro m hm
  exact Nat.find_min (K.exists_safeLevelFace_containing U hU p.2) hm

/-- The first-safe adaptive triangles cover the whole open set. -/
theorem iUnion_adaptiveFaceCarrier (hU : IsOpen U) :
    (⋃ t : K.AdaptiveFace U, K.adaptiveFaceCarrier U t) = U := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hp
    exact K.adaptiveFaceCarrier_subset U t ht
  · intro p hp
    let q : U := ⟨p, hp⟩
    let t : K.AdaptiveFace U :=
      ⟨K.firstSafeLevel U hU q,
        ⟨K.firstSafeFace U hU q, K.firstSafeFace_isFirstSafe U hU q⟩⟩
    exact Set.mem_iUnion.mpr ⟨t, K.mem_firstSafeFaceCarrier U hU q⟩

/-- The transported diameter of every level-`n` face is at most `2⁻ⁿ`. -/
theorem dist_le_pow_of_mem_levelFaceCarrier {n : ℕ} (t : K.LevelFace n)
    {x y : K.realization} (hx : x ∈ K.levelFaceCarrier t)
    (hy : y ∈ K.levelFaceCarrier t) :
    dist x y ≤ (1 / 2 : ℝ) ^ n := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  exact K.iteratedMidpointSubdivision_meshLE n t.1 t.2 x' hx' y' hy'

omit [AdaptiveSafety K U] in
/-- If a child face meets a half-radius ball and its parent mesh is below that half-radius,
then the parent is already safe. -/
theorem parent_isSafe_of_inter_ball {n : ℕ} (t : K.LevelFace (n + 1))
    {p : K.realization} {ε : ℝ} (_ : 0 < ε)
    (hball : Metric.ball p ε ⊆ U)
    (hmesh : (1 / 2 : ℝ) ^ n < ε / 2)
    (hinter : (K.levelFaceCarrier t ∩ Metric.ball p (ε / 2)).Nonempty) :
    @LevelFace.IsSafe K U (defaultAdaptiveSafety K U) n
      (K.levelParentFace n t) := by
  obtain ⟨z, hzFace, hzBall⟩ := hinter
  have hzParent : z ∈ K.levelFaceCarrier (K.levelParentFace n t) :=
    K.levelFaceCarrier_subset_parent n t hzFace
  intro y hy
  apply hball
  rw [Metric.mem_ball]
  calc
    dist y p ≤ dist y z + dist z p := dist_triangle _ _ _
    _ ≤ (1 / 2 : ℝ) ^ n + dist z p :=
      add_le_add (K.dist_le_pow_of_mem_levelFaceCarrier
        (K.levelParentFace n t) hy hzParent) le_rfl
    _ < ε / 2 + ε / 2 := add_lt_add hmesh hzBall
    _ = ε := by ring

omit [AdaptiveSafety.IsAdmissible K U] in
/-- Only finitely many adaptive faces occur below a fixed midpoint level. -/
theorem finite_adaptiveFace_level_lt (N : ℕ) :
    {t : K.AdaptiveFace U | t.1 < N}.Finite := by
  classical
  let encode : {t : K.AdaptiveFace U // t.1 < N} →
      Σ i : Fin N, K.LevelFace i.1 :=
    fun t ↦ ⟨⟨t.1.1, t.2⟩, t.1.2.1⟩
  have hencode : Function.Injective encode := by
    rintro ⟨⟨sn, s⟩, hs⟩ ⟨⟨tn, t⟩, ht⟩ hst
    dsimp only [encode] at hst
    have hnFin : (⟨sn, hs⟩ : Fin N) = ⟨tn, ht⟩ :=
      (Sigma.mk.inj_iff.mp hst).1
    have hn : sn = tn := congrArg (fun i : Fin N ↦ (i : ℕ)) hnFin
    subst tn
    have hface : s = t := Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp hst).2)
    subst t
    rfl
  letI : Finite {t : K.AdaptiveFace U // t.1 < N} :=
    Finite.of_injective encode hencode
  exact Set.finite_coe_iff.mp
    (show Finite {t : K.AdaptiveFace U // t.1 < N} from inferInstance)

/-- Carrier of an adaptive face in the open subspace itself. -/
def adaptiveFaceCarrierInOpen (t : K.AdaptiveFace U) : Set U :=
  Subtype.val ⁻¹' K.adaptiveFaceCarrier U t

/-- The first-safe adaptive triangle family is locally finite in the open set. -/
theorem locallyFinite_adaptiveFaceCarrierInOpen (hU : IsOpen U) :
    LocallyFinite (K.adaptiveFaceCarrierInOpen U) := by
  classical
  intro p
  obtain ⟨ε, hε, N, hparent⟩ :=
    AdaptiveSafety.IsAdmissible.locally_parent_safe (K := K) (U := U) hU p
  have hε2 : 0 < ε / 2 := half_pos hε
  let V : Set U := Subtype.val ⁻¹' Metric.ball p.1 (ε / 2)
  refine ⟨V, ?_, ?_⟩
  · exact (Metric.isOpen_ball.preimage continuous_subtype_val).mem_nhds
      (Metric.mem_ball_self hε2)
  · apply (K.finite_adaptiveFace_level_lt U (N + 1)).subset
    intro t ht
    simp only [Set.mem_setOf_eq]
    by_contra hlevel
    have hNlevel : N + 1 ≤ t.1 := Nat.le_of_not_gt hlevel
    rcases t with ⟨(_ | n), t⟩
    · change N + 1 ≤ 0 at hNlevel
      omega
    · change N + 1 ≤ n + 1 at hNlevel
      have hNn : N ≤ n := by omega
      obtain ⟨q, hqFace, hqV⟩ := ht
      have hinter :
          (K.levelFaceCarrier t.1 ∩ Metric.ball p.1 (ε / 2)).Nonempty :=
        ⟨q.1, hqFace, hqV⟩
      exact t.2.2 (hparent n hNn t.1 hinter)

/-! ## Finite boundary data on each adaptive tile -/

/-- The geometric point represented by one vertex of a level face. -/
noncomputable def levelFaceVertexPoint {n : ℕ} (t : K.LevelFace n)
    (v : {v // v ∈ t.1}) : K.realization :=
  (K.safeSubdivision n).homeo
    ((K.safeSubdivision n).refined.facePoint t v)

theorem levelFaceVertexPoint_mem_carrier {n : ℕ} (t : K.LevelFace n)
    (v : {v // v ∈ t.1}) :
    K.levelFaceVertexPoint t v ∈ K.levelFaceCarrier t :=
  ⟨(K.safeSubdivision n).refined.facePoint t v,
    (K.safeSubdivision n).refined.facePoint_mem_faceCarrier t v, rfl⟩

/-- A vertex occurrence on an adaptive tile.  Geometrically equal occurrences on adjacent
tiles are deliberately not quotiented here; `boundaryVertices` takes their finite image as
actual points. -/
abbrev AdaptiveVertexOccurrence (t : K.AdaptiveFace U) :=
  {v // v ∈ t.2.1.1}

/-- The `adaptiveVertexPoint` declaration. -/
noncomputable def adaptiveVertexPoint (t : K.AdaptiveFace U)
    (v : K.AdaptiveVertexOccurrence U t) : K.realization :=
  K.levelFaceVertexPoint t.2.1 v

omit [AdaptiveSafety.IsAdmissible K U] in
theorem adaptiveVertexPoint_mem_carrier (t : K.AdaptiveFace U)
    (v : K.AdaptiveVertexOccurrence U t) :
    K.adaptiveVertexPoint U t v ∈ K.adaptiveFaceCarrier U t :=
  K.levelFaceVertexPoint_mem_carrier t.2.1 v

omit [AdaptiveSafety.IsAdmissible K U] in
theorem isCompact_adaptiveFaceCarrierInOpen (t : K.AdaptiveFace U) :
    IsCompact (K.adaptiveFaceCarrierInOpen U t) := by
  let e : {x // x ∈ K.adaptiveFaceCarrier U t} → U :=
    fun x ↦ ⟨x.1, K.adaptiveFaceCarrier_subset U t x.2⟩
  have he : Continuous e := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have hrange : Set.range e = K.adaptiveFaceCarrierInOpen U t := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x.1, hx⟩, Subtype.ext rfl⟩
  rw [← hrange]
  letI : CompactSpace {x // x ∈ K.adaptiveFaceCarrier U t} :=
    isCompact_iff_compactSpace.mp (K.isCompact_levelFaceCarrier t.2.1)
  exact isCompact_range he

/-- Adaptive tiles touching a fixed tile. -/
def TouchingFace (t : K.AdaptiveFace U) :=
  {u : K.AdaptiveFace U //
    (K.adaptiveFaceCarrierInOpen U u ∩ K.adaptiveFaceCarrierInOpen U t).Nonempty}

theorem finite_touchingFace (hU : IsOpen U) (t : K.AdaptiveFace U) :
    Finite (K.TouchingFace U t) := by
  exact Set.finite_coe_iff.mpr
    ((K.locallyFinite_adaptiveFaceCarrierInOpen U hU).finite_nonempty_inter_compact
      (K.isCompact_adaptiveFaceCarrierInOpen U t))

/-- Every tile touches itself. -/
noncomputable def selfTouchingFace (t : K.AdaptiveFace U) : K.TouchingFace U t := by
  refine ⟨t, ?_⟩
  obtain ⟨v, hv⟩ : t.2.1.1.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have := (K.safeSubdivision t.1).refined.faces_card t.2.1.1 t.2.1.2
    rw [hempty] at this
    simp at this
  let p := K.adaptiveVertexPoint U t ⟨v, hv⟩
  have hp : p ∈ K.adaptiveFaceCarrier U t :=
    K.adaptiveVertexPoint_mem_carrier U t ⟨v, hv⟩
  exact ⟨⟨p, K.adaptiveFaceCarrier_subset U t hp⟩, hp, hp⟩

/-- All vertex occurrences belonging to tiles which touch `t`. -/
abbrev TouchingVertexOccurrence (t : K.AdaptiveFace U) :=
  Σ u : K.TouchingFace U t, K.AdaptiveVertexOccurrence U u.1

/-- The finite set of all touching-tile vertices which lie in `t`.  It contains the original
three corners of `t` and every hanging midpoint introduced by a finer neighboring tile. -/
noncomputable def boundaryVertices (hU : IsOpen U) (t : K.AdaptiveFace U) :
    Finset K.realization := by
  classical
  letI : Finite (K.TouchingFace U t) := K.finite_touchingFace U hU t
  letI : Fintype (K.TouchingFace U t) := Fintype.ofFinite _
  let point : K.TouchingVertexOccurrence U t → K.realization :=
    fun v ↦ K.adaptiveVertexPoint U v.1.1 v.2
  exact (Finset.univ.image point).filter fun p ↦ p ∈ K.adaptiveFaceCarrier U t

theorem mem_boundaryVertices_iff (hU : IsOpen U) (t : K.AdaptiveFace U)
    (p : K.realization) :
    p ∈ K.boundaryVertices U hU t ↔
      p ∈ K.adaptiveFaceCarrier U t ∧
        ∃ (u : K.TouchingFace U t) (v : K.AdaptiveVertexOccurrence U u.1),
          K.adaptiveVertexPoint U u.1 v = p := by
  classical
  letI : Finite (K.TouchingFace U t) := K.finite_touchingFace U hU t
  letI : Fintype (K.TouchingFace U t) := Fintype.ofFinite _
  simp only [boundaryVertices, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨⟨v, rfl⟩, hp⟩
    exact ⟨hp, v.1, v.2, rfl⟩
  · rintro ⟨hp, u, v, rfl⟩
    exact ⟨⟨⟨u, v⟩, rfl⟩, hp⟩

/-- On the overlap of two adaptive tiles, their finite sets of collected boundary marks agree
pointwise.  Indeed a vertex occurrence whose tile touches one of the two tiles at the shared
point also touches the other there. -/
theorem mem_boundaryVertices_iff_of_mem_adaptiveFaceCarrier_inter
    (hU : IsOpen U) (s t : K.AdaptiveFace U) {p : K.realization}
    (hps : p ∈ K.adaptiveFaceCarrier U s)
    (hpt : p ∈ K.adaptiveFaceCarrier U t) :
    p ∈ K.boundaryVertices U hU s ↔
      p ∈ K.boundaryVertices U hU t := by
  constructor
  · intro hp
    obtain ⟨-, u, v, huv⟩ := (K.mem_boundaryVertices_iff U hU s p).mp hp
    rw [K.mem_boundaryVertices_iff U hU t p]
    refine ⟨hpt, ⟨u.1, ?_⟩, v, huv⟩
    let q : U := ⟨p, K.adaptiveFaceCarrier_subset U t hpt⟩
    refine ⟨q, ?_, hpt⟩
    change p ∈ K.adaptiveFaceCarrier U u.1
    rw [← huv]
    exact K.adaptiveVertexPoint_mem_carrier U u.1 v
  · intro hp
    obtain ⟨-, u, v, huv⟩ := (K.mem_boundaryVertices_iff U hU t p).mp hp
    rw [K.mem_boundaryVertices_iff U hU s p]
    refine ⟨hps, ⟨u.1, ?_⟩, v, huv⟩
    let q : U := ⟨p, K.adaptiveFaceCarrier_subset U s hps⟩
    refine ⟨q, ?_, hps⟩
    change p ∈ K.adaptiveFaceCarrier U u.1
    rw [← huv]
    exact K.adaptiveVertexPoint_mem_carrier U u.1 v

omit [AdaptiveSafety.IsAdmissible K U] in
/-- Distinct first-safe tiles meet only in the relative boundary of each tile. -/
theorem adaptiveFaceCarrier_inter_subset_relativeBoundaries
    {s t : K.AdaptiveFace U} (hst : s ≠ t) :
    K.adaptiveFaceCarrier U s ∩ K.adaptiveFaceCarrier U t ⊆
      (K.adaptiveFaceCarrier U s \ K.adaptiveFaceRelInterior U s) ∩
        (K.adaptiveFaceCarrier U t \ K.adaptiveFaceRelInterior U t) := by
  rintro p ⟨hps, hpt⟩
  refine ⟨⟨hps, ?_⟩, hpt, ?_⟩
  · exact fun hpInt ↦ Set.disjoint_left.mp
      (K.disjoint_adaptiveFaceRelInterior_carrier U hst) hpInt hpt
  · exact fun hpInt ↦ Set.disjoint_left.mp
      (K.disjoint_adaptiveFaceRelInterior_carrier U (fun h ↦ hst h.symm)) hpInt hps

theorem levelFaceVertexPoint_not_mem_relInterior {n : ℕ} (t : K.LevelFace n)
    (v : {v // v ∈ t.1}) :
    K.levelFaceVertexPoint t v ∉ K.levelFaceRelInterior t := by
  intro hvInt
  obtain ⟨x, hx, heq⟩ := hvInt
  have hsource : (K.safeSubdivision n).refined.facePoint t v = x :=
    (K.safeSubdivision n).homeo.injective heq.symm
  have hone : 1 < t.1.card := by
    rw [(K.safeSubdivision n).refined.faces_card t.1 t.2]
    omega
  obtain ⟨w, hwt, hwv⟩ := Finset.exists_mem_ne hone v.1
  have hzero : ((K.safeSubdivision n).refined.facePoint t v).1 w = 0 := by
    rw [(K.safeSubdivision n).refined.facePoint_val t v]
    simp [hwv]
  have hcoord := congrFun (congrArg Subtype.val hsource) w
  linarith [hx.2 w hwt]

omit [AdaptiveSafety.IsAdmissible K U] in
theorem adaptiveVertexPoint_not_mem_relInterior (t : K.AdaptiveFace U)
    (v : K.AdaptiveVertexOccurrence U t) :
    K.adaptiveVertexPoint U t v ∉ K.adaptiveFaceRelInterior U t :=
  K.levelFaceVertexPoint_not_mem_relInterior t.2.1 v

/-- Every collected touching vertex lies on the relative boundary of the fixed tile. -/
theorem boundaryVertices_not_mem_relInterior (hU : IsOpen U)
    (t : K.AdaptiveFace U) {p : K.realization}
    (hp : p ∈ K.boundaryVertices U hU t) :
    p ∉ K.adaptiveFaceRelInterior U t := by
  obtain ⟨-, u, v, huv⟩ := (K.mem_boundaryVertices_iff U hU t p).mp hp
  by_cases hut : u.1 = t
  · have hvNot := K.adaptiveVertexPoint_not_mem_relInterior U u.1 v
    intro hpInt
    apply hvNot
    have hsets : K.adaptiveFaceRelInterior U u.1 =
        K.adaptiveFaceRelInterior U t := congrArg (K.adaptiveFaceRelInterior U) hut
    have hpIntU : p ∈ K.adaptiveFaceRelInterior U u.1 := by
      rw [hsets]
      exact hpInt
    rw [huv]
    exact hpIntU
  · have hdisjoint := K.disjoint_adaptiveFaceRelInterior_carrier U
      (s := t) (t := u.1) (fun h ↦ hut h.symm)
    intro hpInt
    exact Set.disjoint_left.mp hdisjoint hpInt
      (huv ▸ K.adaptiveVertexPoint_mem_carrier U u.1 v)

/-- All three original corners of a tile occur in its resolved boundary vertex set. -/
theorem adaptiveVertexPoint_mem_boundaryVertices (hU : IsOpen U)
    (t : K.AdaptiveFace U) (v : K.AdaptiveVertexOccurrence U t) :
    K.adaptiveVertexPoint U t v ∈ K.boundaryVertices U hU t := by
  rw [K.mem_boundaryVertices_iff U hU t]
  refine ⟨K.adaptiveVertexPoint_mem_carrier U t v,
    K.selfTouchingFace U t, ?_⟩
  exact ⟨v, rfl⟩

/-- Carrier of one cyclic edge of a level face. -/
def levelFaceEdgeCarrier {n : ℕ} (t : K.LevelFace n) (i : ZMod 3) :
    Set K.realization :=
  (K.safeSubdivision n).homeo ''
    (K.safeSubdivision n).refined.faceCarrier
      ((K.safeSubdivision n).refined.faceEdge t i).1

theorem levelFaceEdgeCarrier_subset {n : ℕ} (t : K.LevelFace n) (i : ZMod 3) :
    K.levelFaceEdgeCarrier t i ⊆ K.levelFaceCarrier t := by
  rintro p ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  intro v hvt
  exact hx v (fun hve ↦ hvt
    ((K.safeSubdivision n).refined.faceEdge_subset_face t i hve))

/-- Every point of a closed level face outside its relative interior lies on a cyclic edge. -/
theorem exists_levelFaceEdge_of_mem_not_relInterior {n : ℕ} (t : K.LevelFace n)
    {p : K.realization} (hp : p ∈ K.levelFaceCarrier t)
    (hpInt : p ∉ K.levelFaceRelInterior t) :
    ∃ i : ZMod 3, p ∈ K.levelFaceEdgeCarrier t i := by
  classical
  obtain ⟨x, hxt, rfl⟩ := hp
  have hzero : ∃ v ∈ t.1, x.1 v = 0 := by
    by_contra h
    have hpos : ∀ v ∈ t.1, 0 < x.1 v := by
      intro v hv
      exact lt_of_le_of_ne (x.2.1.1 v) (fun hz ↦ h ⟨v, hv, hz.symm⟩)
    exact hpInt ⟨x, ⟨hxt, hpos⟩, rfl⟩
  obtain ⟨v, hvt, hxv⟩ := hzero
  let e0 : Finset (K.safeSubdivision n).refined.Vertex := t.1.erase v
  have heCard : e0.card = 2 := by
    dsimp only [e0]
    rw [Finset.card_erase_of_mem hvt,
      (K.safeSubdivision n).refined.faces_card t.1 t.2]
  have heMem : e0 ∈ (K.safeSubdivision n).refined.edges := by
    change e0 ∈ (K.safeSubdivision n).refined.faces.biUnion
      (fun s ↦ s.powersetCard 2)
    exact Finset.mem_biUnion.mpr
      ⟨t.1, t.2, Finset.mem_powersetCard.mpr ⟨Finset.erase_subset _ _, heCard⟩⟩
  let e : (K.safeSubdivision n).refined.Edge := ⟨e0, heMem⟩
  obtain ⟨i, hi⟩ := (K.safeSubdivision n).refined.exists_faceEdge_eq_of_subset
    t e (Finset.erase_subset _ _)
  refine ⟨i, x, ?_, rfl⟩
  rw [hi]
  intro w hw
  by_cases hwt : w ∈ t.1
  · have hwv : w = v := by
      by_contra hne
      exact hw (Finset.mem_erase.mpr ⟨hne, hwt⟩)
    simpa only [hwv] using hxv
  · exact hxt w hwt

/-- Resolved boundary vertices lying on one cyclic edge. -/
noncomputable def boundaryEdgeVertices (hU : IsOpen U) (t : K.AdaptiveFace U)
    (i : ZMod 3) : Finset K.realization := by
  classical
  exact (K.boundaryVertices U hU t).filter fun p ↦
    p ∈ K.levelFaceEdgeCarrier t.2.1 i

theorem mem_boundaryEdgeVertices_iff (hU : IsOpen U) (t : K.AdaptiveFace U)
    (i : ZMod 3) (p : K.realization) :
    p ∈ K.boundaryEdgeVertices U hU t i ↔
      p ∈ K.boundaryVertices U hU t ∧
        p ∈ K.levelFaceEdgeCarrier t.2.1 i := by
  classical
  exact Finset.mem_filter

/-- Barycentric parameter along a cyclic level-face edge, from vertex `i` to vertex `i+1`. -/
noncomputable def levelFaceEdgeParameter {n : ℕ} (t : K.LevelFace n)
    (i : ZMod 3) (p : K.realization) : ℝ :=
  ((K.safeSubdivision n).homeo.symm p).1
    ((K.safeSubdivision n).refined.faceVertex t (i + 1))

theorem levelFaceEdgeParameter_injOn {n : ℕ} (t : K.LevelFace n) (i : ZMod 3) :
    Set.InjOn (K.levelFaceEdgeParameter t i) (K.levelFaceEdgeCarrier t i) := by
  intro p hp q hq hpq
  obtain ⟨x, hx, hxp⟩ := hp
  obtain ⟨y, hy, hyq⟩ := hq
  have hxEq : (K.safeSubdivision n).homeo.symm p = x := by
    rw [← hxp]
    exact (K.safeSubdivision n).homeo.symm_apply_apply x
  have hyEq : (K.safeSubdivision n).homeo.symm q = y := by
    rw [← hyq]
    exact (K.safeSubdivision n).homeo.symm_apply_apply y
  have hsecond : x.1 ((K.safeSubdivision n).refined.faceVertex t (i + 1)) =
      y.1 ((K.safeSubdivision n).refined.faceVertex t (i + 1)) := by
    simpa only [levelFaceEdgeParameter, hxEq, hyEq] using hpq
  have hfirst : x.1 ((K.safeSubdivision n).refined.faceVertex t i) =
      y.1 ((K.safeSubdivision n).refined.faceVertex t i) := by
    have hxsum : (∑ v ∈ ((K.safeSubdivision n).refined.faceEdge t i).1, x.1 v) = 1 := by
      calc
        _ = ∑ v, x.1 v := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro v _ hv
          exact hx v hv
        _ = 1 := x.2.1.2
    have hysum : (∑ v ∈ ((K.safeSubdivision n).refined.faceEdge t i).1, y.1 v) = 1 := by
      calc
        _ = ∑ v, y.1 v := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro v _ hv
          exact hy v hv
        _ = 1 := y.2.1.2
    simp only [(K.safeSubdivision n).refined.faceEdge_val,
      Finset.sum_insert,
      Finset.mem_singleton,
      (K.safeSubdivision n).refined.faceVertex_ne_next t i,
      not_false_eq_true,
      Finset.sum_singleton] at hxsum hysum
    linarith
  have hxy : x = y := by
    apply Subtype.ext
    funext v
    by_cases hvi : v = (K.safeSubdivision n).refined.faceVertex t i
    · simpa only [hvi] using hfirst
    by_cases hvj : v = (K.safeSubdivision n).refined.faceVertex t (i + 1)
    · simpa only [hvj] using hsecond
    have hvEdge : v ∉ ((K.safeSubdivision n).refined.faceEdge t i).1 := by
      simp only [(K.safeSubdivision n).refined.faceEdge_val, Finset.mem_insert,
        Finset.mem_singleton]
      exact fun h ↦ h.elim hvi hvj
    rw [hx v hvEdge, hy v hvEdge]
  apply (K.safeSubdivision n).homeo.symm.injective
  calc
    (K.safeSubdivision n).homeo.symm p = x := hxEq
    _ = y := hxy
    _ = (K.safeSubdivision n).homeo.symm q := hyEq.symm

/-- A resolved vertex on one adaptive edge. -/
abbrev BoundaryEdgeVertex (hU : IsOpen U) (t : K.AdaptiveFace U) (i : ZMod 3) :=
  {p // p ∈ K.boundaryEdgeVertices U hU t i}

theorem boundaryEdgeParameter_injective (hU : IsOpen U) (t : K.AdaptiveFace U)
    (i : ZMod 3) : Function.Injective
      (fun p : K.BoundaryEdgeVertex U hU t i ↦
        K.levelFaceEdgeParameter t.2.1 i p.1) := by
  intro p q hpq
  apply Subtype.ext
  apply K.levelFaceEdgeParameter_injOn t.2.1 i
  · exact (K.mem_boundaryEdgeVertices_iff U hU t i p.1).mp p.2 |>.2
  · exact (K.mem_boundaryEdgeVertices_iff U hU t i q.1).mp q.2 |>.2
  · exact hpq

/-- The parameter order on the finite set of vertices of one resolved edge. -/
def boundaryEdgeVertexLE (hU : IsOpen U) (t : K.AdaptiveFace U) (i : ZMod 3)
    (p q : K.BoundaryEdgeVertex U hU t i) : Prop :=
  K.levelFaceEdgeParameter t.2.1 i p.1 ≤
    K.levelFaceEdgeParameter t.2.1 i q.1

noncomputable instance boundaryEdgeVertexLEDecidable (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    DecidableRel (K.boundaryEdgeVertexLE U hU t i) :=
  fun p q ↦ inferInstanceAs (Decidable
    (K.levelFaceEdgeParameter t.2.1 i p.1 ≤
      K.levelFaceEdgeParameter t.2.1 i q.1))

instance boundaryEdgeVertexLE_total (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    Std.Total (K.boundaryEdgeVertexLE U hU t i) :=
  ⟨fun p q ↦ le_total
    (K.levelFaceEdgeParameter t.2.1 i p.1)
    (K.levelFaceEdgeParameter t.2.1 i q.1)⟩

instance boundaryEdgeVertexLE_antisymm (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    Std.Antisymm (K.boundaryEdgeVertexLE U hU t i) :=
  ⟨fun _ _ hpq hqp ↦ K.boundaryEdgeParameter_injective U hU t i
    (le_antisymm hpq hqp)⟩

instance boundaryEdgeVertexLE_isTrans (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    IsTrans (K.BoundaryEdgeVertex U hU t i)
      (K.boundaryEdgeVertexLE U hU t i) :=
  ⟨fun _ _ _ hpq hqr ↦ hpq.trans hqr⟩

/-- Canonically ordered vertices on one resolved adaptive edge. -/
noncomputable def boundaryEdgeVertexList (hU : IsOpen U) (t : K.AdaptiveFace U)
    (i : ZMod 3) : List K.realization := by
  classical
  exact ((K.boundaryEdgeVertices U hU t i).attach.sort
    (K.boundaryEdgeVertexLE U hU t i)).map Subtype.val

theorem mem_boundaryEdgeVertexList_iff (hU : IsOpen U) (t : K.AdaptiveFace U)
    (i : ZMod 3) (p : K.realization) :
    p ∈ K.boundaryEdgeVertexList U hU t i ↔
      p ∈ K.boundaryEdgeVertices U hU t i := by
  classical
  simp only [boundaryEdgeVertexList, List.mem_map, Finset.mem_sort,
    Finset.mem_attach]
  constructor
  · rintro ⟨q, -, rfl⟩
    exact q.2
  · intro hp
    exact ⟨⟨p, hp⟩, trivial, rfl⟩

theorem boundaryEdgeVertexList_nodup (hU : IsOpen U) (t : K.AdaptiveFace U)
    (i : ZMod 3) : (K.boundaryEdgeVertexList U hU t i).Nodup := by
  classical
  unfold boundaryEdgeVertexList
  exact (Finset.sort_nodup _ (K.boundaryEdgeVertexLE U hU t i)).map
    Subtype.val_injective

theorem boundaryEdgeVertexList_pairwise_parameter_le (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    (K.boundaryEdgeVertexList U hU t i).Pairwise
      (fun p q ↦ K.levelFaceEdgeParameter t.2.1 i p ≤
        K.levelFaceEdgeParameter t.2.1 i q) := by
  classical
  unfold boundaryEdgeVertexList
  simp only [List.pairwise_map]
  apply (Finset.pairwise_sort
    (K.boundaryEdgeVertices U hU t i).attach
    (K.boundaryEdgeVertexLE U hU t i)).imp
  intro p q hpq
  exact hpq

/-- A monotone finite list with at least two entries covers every parameter between its
endpoints by one of its consecutive intervals. -/
theorem exists_adjacent_get_of_pairwise_le {α : Type*} (L : List α) (f : α → ℝ)
    (hlength : 2 ≤ L.length)
    (hpair : L.Pairwise fun a b ↦ f a ≤ f b) {r : ℝ}
    (hfirst : f (L.get ⟨0, by omega⟩) ≤ r)
    (hlast : r ≤ f (L.get ⟨L.length - 1, by omega⟩)) :
    ∃ j : Fin (L.length - 1),
      f (L.get ⟨j.1, by omega⟩) ≤ r ∧
        r ≤ f (L.get ⟨j.1 + 1, by omega⟩) := by
  classical
  let A : Finset (Fin L.length) :=
    Finset.univ.filter fun k ↦ f (L.get k) ≤ r
  have hA : A.Nonempty := by
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hfirst
  let k : Fin L.length := A.max' hA
  have hkA : k ∈ A := Finset.max'_mem A hA
  have hkLower : f (L.get k) ≤ r := by
    simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hkA
  by_cases hkLast : k.1 = L.length - 1
  · let prev : Fin L.length := ⟨L.length - 2, by omega⟩
    let last : Fin L.length := ⟨L.length - 1, by omega⟩
    have hklastFin : k = last := Fin.ext hkLast
    rw [hklastFin] at hkLower
    let j : Fin (L.length - 1) := ⟨L.length - 2, by omega⟩
    refine ⟨j, ?_, ?_⟩
    · have hprev : f (L.get prev) ≤ f (L.get last) := by
        apply hpair.rel_get_of_lt
        exact Fin.mk_lt_mk.mpr (by omega)
      simpa only [j, prev, last] using hprev.trans hkLower
    · have hjNext : (⟨j.1 + 1, by omega⟩ : Fin L.length) = last := by
        apply Fin.ext
        dsimp only [j, last]
        omega
      rw [hjNext]
      simpa only [last] using hlast
  · have hkBeforeLast : k.1 < L.length - 1 := by omega
    let j : Fin (L.length - 1) := ⟨k.1, hkBeforeLast⟩
    let kNext : Fin L.length := ⟨k.1 + 1, by omega⟩
    have hkNextUpper : r ≤ f (L.get kNext) := by
      apply le_of_not_ge
      intro hkNextLower
      have hkNextA : kNext ∈ A := by
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hkNextLower
      have hle : kNext ≤ k := Finset.le_max' A kNext hkNextA
      change k.1 + 1 ≤ k.1 at hle
      omega
    refine ⟨j, ?_, ?_⟩
    · simpa only [j] using hkLower
    · simpa only [j, kNext] using hkNextUpper

/-- The first corner of a cyclic adaptive edge. -/
noncomputable def adaptiveEdgeFirstCorner (t : K.AdaptiveFace U) (i : ZMod 3) :
    K.realization :=
  K.levelFaceVertexPoint t.2.1
    ⟨(K.safeSubdivision t.1).refined.faceVertex t.2.1 i,
      (K.safeSubdivision t.1).refined.faceVertex_mem t.2.1 i⟩

/-- The second corner of a cyclic adaptive edge. -/
noncomputable def adaptiveEdgeSecondCorner (t : K.AdaptiveFace U) (i : ZMod 3) :
    K.realization :=
  K.levelFaceVertexPoint t.2.1
    ⟨(K.safeSubdivision t.1).refined.faceVertex t.2.1 (i + 1),
      (K.safeSubdivision t.1).refined.faceVertex_mem t.2.1 (i + 1)⟩

theorem adaptiveEdgeFirstCorner_mem_boundaryEdgeVertices (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    K.adaptiveEdgeFirstCorner U t i ∈ K.boundaryEdgeVertices U hU t i := by
  rw [K.mem_boundaryEdgeVertices_iff U hU t i]
  constructor
  · exact K.adaptiveVertexPoint_mem_boundaryVertices U hU t
      ⟨(K.safeSubdivision t.1).refined.faceVertex t.2.1 i,
        (K.safeSubdivision t.1).refined.faceVertex_mem t.2.1 i⟩
  · refine ⟨(K.safeSubdivision t.1).refined.facePoint t.2.1
      ⟨(K.safeSubdivision t.1).refined.faceVertex t.2.1 i,
        (K.safeSubdivision t.1).refined.faceVertex_mem t.2.1 i⟩, ?_, rfl⟩
    exact ((K.safeSubdivision t.1).refined.vertexPoint_mem_faceCarrier_iff
      ⟨(K.safeSubdivision t.1).refined.faceVertex t.2.1 i,
        t.2.1.1, t.2.1.2,
        (K.safeSubdivision t.1).refined.faceVertex_mem t.2.1 i⟩
      ((K.safeSubdivision t.1).refined.faceEdge t.2.1 i).1).mpr (by
      rw [(K.safeSubdivision t.1).refined.faceEdge_val]
      simp)

theorem adaptiveEdgeSecondCorner_mem_boundaryEdgeVertices (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    K.adaptiveEdgeSecondCorner U t i ∈ K.boundaryEdgeVertices U hU t i := by
  rw [K.mem_boundaryEdgeVertices_iff U hU t i]
  constructor
  · exact K.adaptiveVertexPoint_mem_boundaryVertices U hU t
      ⟨(K.safeSubdivision t.1).refined.faceVertex t.2.1 (i + 1),
        (K.safeSubdivision t.1).refined.faceVertex_mem t.2.1 (i + 1)⟩
  · refine ⟨(K.safeSubdivision t.1).refined.facePoint t.2.1
      ⟨(K.safeSubdivision t.1).refined.faceVertex t.2.1 (i + 1),
        (K.safeSubdivision t.1).refined.faceVertex_mem t.2.1 (i + 1)⟩, ?_, rfl⟩
    exact ((K.safeSubdivision t.1).refined.vertexPoint_mem_faceCarrier_iff
      ⟨(K.safeSubdivision t.1).refined.faceVertex t.2.1 (i + 1),
        t.2.1.1, t.2.1.2,
        (K.safeSubdivision t.1).refined.faceVertex_mem t.2.1 (i + 1)⟩
      ((K.safeSubdivision t.1).refined.faceEdge t.2.1 i).1).mpr (by
      rw [(K.safeSubdivision t.1).refined.faceEdge_val]
      simp)

omit [AdaptiveSafety.IsAdmissible K U] in
theorem adaptiveEdgeFirstCorner_ne_second (t : K.AdaptiveFace U) (i : ZMod 3) :
    K.adaptiveEdgeFirstCorner U t i ≠ K.adaptiveEdgeSecondCorner U t i := by
  intro h
  have hvne := (K.safeSubdivision t.1).refined.faceVertex_ne_next t.2.1 i
  have hsource := (K.safeSubdivision t.1).homeo.injective h
  have hcoord := congrArg (fun x : (K.safeSubdivision t.1).refined.realization ↦
    x.1 ((K.safeSubdivision t.1).refined.faceVertex t.2.1 i)) hsource
  simp only [(K.safeSubdivision t.1).refined.facePoint_val,
    Pi.single_apply, if_neg hvne] at hcoord
  norm_num at hcoord

theorem two_le_boundaryEdgeVertices_card (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    2 ≤ (K.boundaryEdgeVertices U hU t i).card := by
  rw [Nat.succ_le_iff]
  apply Finset.one_lt_card.mpr
  exact ⟨K.adaptiveEdgeFirstCorner U t i,
    K.adaptiveEdgeFirstCorner_mem_boundaryEdgeVertices U hU t i,
    K.adaptiveEdgeSecondCorner U t i,
    K.adaptiveEdgeSecondCorner_mem_boundaryEdgeVertices U hU t i,
    K.adaptiveEdgeFirstCorner_ne_second U t i⟩

theorem two_le_boundaryEdgeVertexList_length (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    2 ≤ (K.boundaryEdgeVertexList U hU t i).length := by
  rw [← List.toFinset_card_of_nodup
    (K.boundaryEdgeVertexList_nodup U hU t i)]
  rw [show (K.boundaryEdgeVertexList U hU t i).toFinset =
      K.boundaryEdgeVertices U hU t i by
    ext p
    simp only [List.mem_toFinset, K.mem_boundaryEdgeVertexList_iff U hU t i]]
  exact K.two_le_boundaryEdgeVertices_card U hU t i

omit [AdaptiveSafety.IsAdmissible K U] in
@[simp] theorem levelFaceEdgeParameter_adaptiveEdgeFirstCorner
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    K.levelFaceEdgeParameter t.2.1 i
      (K.adaptiveEdgeFirstCorner U t i) = 0 := by
  simp [levelFaceEdgeParameter, adaptiveEdgeFirstCorner, levelFaceVertexPoint,
    (K.safeSubdivision t.1).refined.faceVertex_ne_next t.2.1 i]

omit [AdaptiveSafety.IsAdmissible K U] in
@[simp] theorem levelFaceEdgeParameter_adaptiveEdgeSecondCorner
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    K.levelFaceEdgeParameter t.2.1 i
      (K.adaptiveEdgeSecondCorner U t i) = 1 := by
  simp [levelFaceEdgeParameter, adaptiveEdgeSecondCorner, levelFaceVertexPoint]

theorem levelFaceEdgeParameter_mem_Icc {n : ℕ} (t : K.LevelFace n)
    (i : ZMod 3) {p : K.realization}
    (hp : p ∈ K.levelFaceEdgeCarrier t i) :
    K.levelFaceEdgeParameter t i p ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨x, hx, rfl⟩ := hp
  rw [levelFaceEdgeParameter, (K.safeSubdivision n).homeo.symm_apply_apply]
  exact mem_Icc_of_mem_stdSimplex x.2.1 _

theorem boundaryEdgeVertexList_first_parameter (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    K.levelFaceEdgeParameter t.2.1 i
      ((K.boundaryEdgeVertexList U hU t i).get ⟨0, by
        have := K.two_le_boundaryEdgeVertexList_length U hU t i
        omega⟩) = 0 := by
  let L := K.boundaryEdgeVertexList U hU t i
  let first : Fin L.length := ⟨0, by
    dsimp only [L]
    have := K.two_le_boundaryEdgeVertexList_length U hU t i
    omega⟩
  have hfirstEdge : L.get first ∈ K.levelFaceEdgeCarrier t.2.1 i :=
    ((K.mem_boundaryEdgeVertices_iff U hU t i _).mp
      ((K.mem_boundaryEdgeVertexList_iff U hU t i _).mp
        (List.get_mem L first))).2
  have hnonneg := (K.levelFaceEdgeParameter_mem_Icc t.2.1 i hfirstEdge).1
  have hcornerL : K.adaptiveEdgeFirstCorner U t i ∈ L :=
    (K.mem_boundaryEdgeVertexList_iff U hU t i _).mpr
      (K.adaptiveEdgeFirstCorner_mem_boundaryEdgeVertices U hU t i)
  obtain ⟨k, hk⟩ := List.get_of_mem hcornerL
  have hle : K.levelFaceEdgeParameter t.2.1 i (L.get first) ≤ 0 := by
    by_cases hkfirst : k = first
    · subst k
      simpa only [L, first, hk] using
        K.levelFaceEdgeParameter_adaptiveEdgeFirstCorner U t i |>.le
    · have hlt : first < k := by
        have hk0 : k.1 ≠ 0 := by
          intro hk0
          apply hkfirst
          apply Fin.ext
          simpa only [first] using hk0
        change 0 < k.1
        omega
      have hpair := K.boundaryEdgeVertexList_pairwise_parameter_le U hU t i
      have := hpair.rel_get_of_lt hlt
      rw [hk, K.levelFaceEdgeParameter_adaptiveEdgeFirstCorner U t i] at this
      exact this
  apply le_antisymm hle hnonneg

theorem boundaryEdgeVertexList_last_parameter (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    K.levelFaceEdgeParameter t.2.1 i
      ((K.boundaryEdgeVertexList U hU t i).get
        ⟨(K.boundaryEdgeVertexList U hU t i).length - 1, by
          have := K.two_le_boundaryEdgeVertexList_length U hU t i
          omega⟩) = 1 := by
  let L := K.boundaryEdgeVertexList U hU t i
  let last : Fin L.length := ⟨L.length - 1, by
    dsimp only [L]
    have := K.two_le_boundaryEdgeVertexList_length U hU t i
    omega⟩
  have hlastEdge : L.get last ∈ K.levelFaceEdgeCarrier t.2.1 i :=
    ((K.mem_boundaryEdgeVertices_iff U hU t i _).mp
      ((K.mem_boundaryEdgeVertexList_iff U hU t i _).mp
        (List.get_mem L last))).2
  have hupper := (K.levelFaceEdgeParameter_mem_Icc t.2.1 i hlastEdge).2
  have hcornerL : K.adaptiveEdgeSecondCorner U t i ∈ L :=
    (K.mem_boundaryEdgeVertexList_iff U hU t i _).mpr
      (K.adaptiveEdgeSecondCorner_mem_boundaryEdgeVertices U hU t i)
  obtain ⟨k, hk⟩ := List.get_of_mem hcornerL
  have hle : 1 ≤ K.levelFaceEdgeParameter t.2.1 i (L.get last) := by
    by_cases hklast : k = last
    · subst k
      simpa only [L, last, hk] using
        K.levelFaceEdgeParameter_adaptiveEdgeSecondCorner U t i |>.ge
    · have hlt : k < last := by
        have hkne : k.1 ≠ L.length - 1 := by
          intro hkne
          apply hklast
          apply Fin.ext
          simpa only [last] using hkne
        change k.1 < L.length - 1
        omega
      have hpair := K.boundaryEdgeVertexList_pairwise_parameter_le U hU t i
      have := hpair.rel_get_of_lt hlt
      rw [hk, K.levelFaceEdgeParameter_adaptiveEdgeSecondCorner U t i] at this
      exact this
  apply le_antisymm hupper hle

/-- The equal-weight point of the standard simplex on an intrinsic face. -/
noncomputable def faceCenterSimplex (t : K.Face) :
    stdSimplex ℝ {v // v ∈ t.1} := by
  let x : {v // v ∈ t.1} → ℝ := fun _ ↦ 1 / 3
  refine ⟨x, ?_, ?_⟩
  · intro v
    dsimp only [x]
    norm_num
  · change ∑ _ : {v // v ∈ t.1}, (1 / 3 : ℝ) = 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      K.faces_card t.1 t.2]
    norm_num

@[simp] theorem faceCenterSimplex_apply (t : K.Face) (v : {v // v ∈ t.1}) :
    K.faceCenterSimplex t v = 1 / 3 := rfl

/-- The barycentric center of an arbitrary level face, transported to the original
realization. -/
noncomputable def levelFaceCenter {n : ℕ} (t : K.LevelFace n) : K.realization :=
  (K.safeSubdivision n).homeo
    ((K.safeSubdivision n).refined.faceStandardMap t
      ((K.safeSubdivision n).refined.faceCenterSimplex t))

theorem levelFaceCenter_mem_relInterior {n : ℕ} (t : K.LevelFace n) :
    K.levelFaceCenter t ∈ K.levelFaceRelInterior t := by
  refine ⟨(K.safeSubdivision n).refined.faceStandardMap t
      ((K.safeSubdivision n).refined.faceCenterSimplex t), ?_, rfl⟩
  constructor
  · intro v hv
    rw [(K.safeSubdivision n).refined.faceStandardMap_val]
    exact extendFaceCoordinates_of_notMem t.1 _ hv
  · intro v hv
    rw [(K.safeSubdivision n).refined.faceStandardMap_val,
      extendFaceCoordinates_of_mem t.1 _ hv]
    norm_num

theorem levelFaceCenter_mem_carrier {n : ℕ} (t : K.LevelFace n) :
    K.levelFaceCenter t ∈ K.levelFaceCarrier t :=
  K.levelFaceRelInterior_subset_carrier t
    (K.levelFaceCenter_mem_relInterior t)

/-- If a later-level edge meets an earlier face at a point which is not a later-level vertex,
and the two face interiors are disjoint, then the whole later edge lies in the earlier face.
This is the no-crossing fact for nested midpoint subdivisions. -/
theorem levelFaceEdgeCarrier_subset_of_common_not_vertex (n k : ℕ)
    (s : K.LevelFace n) (t : K.LevelFace (n + k)) (i : ZMod 3)
    {p : K.realization}
    (hdisjoint : Disjoint (K.levelFaceRelInterior t) (K.levelFaceCarrier s))
    (hps : p ∈ K.levelFaceCarrier s)
    (hpt : p ∈ K.levelFaceEdgeCarrier t i)
    (hpNot : ∀ v : {v // v ∈ t.1},
      p ≠ K.levelFaceVertexPoint t v) :
    K.levelFaceEdgeCarrier t i ⊆ K.levelFaceCarrier s := by
  obtain ⟨r, hpr, hrs⟩ := K.exists_levelFace_add_containing n k s hps
  have hrt : r ≠ t := by
    intro hrt
    subst r
    exact Set.disjoint_left.mp hdisjoint
      (K.levelFaceCenter_mem_relInterior t)
      (hrs (K.levelFaceCenter_mem_carrier t))
  have hptCarrier : p ∈ K.levelFaceCarrier t :=
    K.levelFaceEdgeCarrier_subset t i hpt
  have hpBoth : p ∈ K.levelFaceCarrier r ∩ K.levelFaceCarrier t :=
    ⟨hpr, hptCarrier⟩
  rw [K.levelFaceCarrier_inter r t] at hpBoth
  obtain ⟨q, hqe, hqp⟩ := hpBoth
  let R := K.safeSubdivision (n + k)
  let e : Finset R.refined.Vertex := r.1 ∩ t.1
  let d : Finset R.refined.Vertex := (R.refined.faceEdge t i).1
  have hecardLe : e.card ≤ 2 := K.card_inter_levelFace_le_two hrt
  have heNonempty : e.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have : q ∈ R.refined.faceCarrier (∅ : Finset R.refined.Vertex) := by
      simpa only [e, he] using hqe
    rw [R.refined.faceCarrier_empty] at this
    exact this
  have hecard : e.card = 2 := by
    have hepos : 0 < e.card := Finset.card_pos.mpr heNonempty
    have hcases : e.card = 1 ∨ e.card = 2 := by omega
    rcases hcases with hone | htwo
    · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hone
      have hvt : v ∈ t.1 := Finset.inter_subset_right (by
        change v ∈ e
        rw [hv]
        exact Finset.mem_singleton_self v)
      have hqSingle : q ∈ R.refined.faceCarrier ({v} : Finset R.refined.Vertex) := by
        simpa only [e, hv] using hqe
      have hqv := R.refined.eq_facePoint_of_mem_faceCarrier_singleton t ⟨v, hvt⟩ q hqSingle
      exact False.elim (hpNot ⟨v, hvt⟩ (by
        calc
          p = R.homeo q := hqp.symm
          _ = R.homeo (R.refined.facePoint t ⟨v, hvt⟩) := congrArg R.homeo hqv
          _ = K.levelFaceVertexPoint t ⟨v, hvt⟩ := rfl))
    · exact htwo
  obtain ⟨y, hyd, hyp⟩ := hpt
  have hqy : q = y := R.homeo.injective (hqp.trans hyp.symm)
  have hqd : q ∈ R.refined.faceCarrier d := by
    simpa only [d, hqy] using hyd
  have hdcard : d.card = 2 := R.refined.card_of_mem_edges (R.refined.faceEdge t i).2
  have hed : e = d := by
    apply R.refined.eq_of_card_two_of_mem_faceCarriers_not_vertex t
      Finset.inter_subset_right (R.refined.faceEdge_subset_face t i)
      hecard hdcard hqe hqd
    intro v hqv
    apply hpNot v
    calc
      p = R.homeo q := hqp.symm
      _ = R.homeo (R.refined.facePoint t v) := congrArg R.homeo hqv
      _ = K.levelFaceVertexPoint t v := rfl
  rintro z ⟨x, hxd, rfl⟩
  apply hrs
  refine ⟨x, ?_, rfl⟩
  have hxe : x ∈ R.refined.faceCarrier e := by
    rw [hed]
    exact hxd
  intro v hvr
  exact hxe v (fun hve ↦ hvr (Finset.inter_subset_left hve))

/-- Adaptive-tile specialization of nested-edge no crossing.  At a common point which is not a
resolved vertex of the later tile, the later edge is contained in the earlier tile. -/
theorem adaptiveFace_edgeCarrier_subset_of_level_le_of_common_not_boundaryVertex
    (hU : IsOpen U) {s t : K.AdaptiveFace U} (hst : s ≠ t)
    (hlevel : s.1 ≤ t.1) (i : ZMod 3) {p : K.realization}
    (hps : p ∈ K.adaptiveFaceCarrier U s)
    (hpt : p ∈ K.levelFaceEdgeCarrier t.2.1 i)
    (hpNot : p ∉ K.boundaryVertices U hU t) :
    K.levelFaceEdgeCarrier t.2.1 i ⊆ K.adaptiveFaceCarrier U s := by
  rcases s with ⟨n, s⟩
  rcases t with ⟨m, t⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hlevel
  apply K.levelFaceEdgeCarrier_subset_of_common_not_vertex n k s.1 t.1 i
  · exact K.disjoint_adaptiveFaceRelInterior_carrier U
      (s := ⟨n + k, t⟩) (t := ⟨n, s⟩) (fun h ↦ hst h.symm)
  · exact hps
  · exact hpt
  · intro v hpv
    apply hpNot
    rw [hpv]
    exact K.adaptiveVertexPoint_mem_boundaryVertices U hU ⟨n + k, t⟩ v

/-- The barycentric center of one adaptive tile, transported to the original realization. -/
noncomputable def adaptiveFaceCenter (t : K.AdaptiveFace U) : K.realization :=
  (K.safeSubdivision t.1).homeo
    ((K.safeSubdivision t.1).refined.faceStandardMap t.2.1
      ((K.safeSubdivision t.1).refined.faceCenterSimplex t.2.1))

omit [AdaptiveSafety.IsAdmissible K U] in
theorem adaptiveFaceCenter_mem_relInterior (t : K.AdaptiveFace U) :
    K.adaptiveFaceCenter U t ∈ K.adaptiveFaceRelInterior U t := by
  refine ⟨(K.safeSubdivision t.1).refined.faceStandardMap t.2.1
      ((K.safeSubdivision t.1).refined.faceCenterSimplex t.2.1), ?_, rfl⟩
  constructor
  · intro v hv
    rw [(K.safeSubdivision t.1).refined.faceStandardMap_val]
    exact extendFaceCoordinates_of_notMem t.2.1.1 _ hv
  · intro v hv
    rw [(K.safeSubdivision t.1).refined.faceStandardMap_val,
      extendFaceCoordinates_of_mem t.2.1.1 _ hv]
    norm_num

omit [AdaptiveSafety.IsAdmissible K U] in
theorem adaptiveFaceCenter_mem_carrier (t : K.AdaptiveFace U) :
    K.adaptiveFaceCenter U t ∈ K.adaptiveFaceCarrier U t :=
  K.levelFaceRelInterior_subset_carrier t.2.1
    (K.adaptiveFaceCenter_mem_relInterior U t)

theorem adaptiveFaceCenter_ne_boundaryVertex (hU : IsOpen U)
    (t : K.AdaptiveFace U) {p : K.realization}
    (hp : p ∈ K.boundaryVertices U hU t) :
    K.adaptiveFaceCenter U t ≠ p := by
  intro h
  exact K.boundaryVertices_not_mem_relInterior U hU t hp
    (h ▸ K.adaptiveFaceCenter_mem_relInterior U t)

/-- One of the consecutive intervals in the ordered subdivision of an adaptive edge. -/
abbrev AdaptiveEdgeInterval (hU : IsOpen U) (t : K.AdaptiveFace U) (i : ZMod 3) :=
  Fin ((K.boundaryEdgeVertexList U hU t i).length - 1)

/-- First endpoint of a resolved adaptive-edge interval. -/
noncomputable def adaptiveEdgeIntervalFirst (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3)
    (j : K.AdaptiveEdgeInterval U hU t i) : K.realization :=
  (K.boundaryEdgeVertexList U hU t i).get
    ⟨j.1, by
      have hj := j.2
      omega⟩

/-- Second endpoint of a resolved adaptive-edge interval. -/
noncomputable def adaptiveEdgeIntervalSecond (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3)
    (j : K.AdaptiveEdgeInterval U hU t i) : K.realization :=
  (K.boundaryEdgeVertexList U hU t i).get
    ⟨j.1 + 1, by
      have hj := j.2
      omega⟩

theorem adaptiveEdgeIntervalFirst_mem_boundaryEdgeVertices (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3)
    (j : K.AdaptiveEdgeInterval U hU t i) :
    K.adaptiveEdgeIntervalFirst U hU t i j ∈
      K.boundaryEdgeVertices U hU t i := by
  rw [← K.mem_boundaryEdgeVertexList_iff U hU t i]
  exact List.get_mem _ _

theorem adaptiveEdgeIntervalSecond_mem_boundaryEdgeVertices (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3)
    (j : K.AdaptiveEdgeInterval U hU t i) :
    K.adaptiveEdgeIntervalSecond U hU t i j ∈
      K.boundaryEdgeVertices U hU t i := by
  rw [← K.mem_boundaryEdgeVertexList_iff U hU t i]
  exact List.get_mem _ _

theorem adaptiveEdgeIntervalFirst_ne_second (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3)
    (j : K.AdaptiveEdgeInterval U hU t i) :
    K.adaptiveEdgeIntervalFirst U hU t i j ≠
      K.adaptiveEdgeIntervalSecond U hU t i j := by
  intro h
  have hn := K.boundaryEdgeVertexList_nodup U hU t i
  have hij := hn.injective_get h
  have hval := congrArg Fin.val hij
  simp only at hval
  omega

/-- Consecutive vertices in the resolved edge order have strictly increasing edge parameter. -/
theorem adaptiveEdgeInterval_parameter_lt (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3)
    (j : K.AdaptiveEdgeInterval U hU t i) :
    K.levelFaceEdgeParameter t.2.1 i
        (K.adaptiveEdgeIntervalFirst U hU t i j) <
      K.levelFaceEdgeParameter t.2.1 i
        (K.adaptiveEdgeIntervalSecond U hU t i j) := by
  let a : Fin (K.boundaryEdgeVertexList U hU t i).length :=
    ⟨j.1, by
      have hj := j.2
      omega⟩
  let b : Fin (K.boundaryEdgeVertexList U hU t i).length :=
    ⟨j.1 + 1, by
      have hj := j.2
      omega⟩
  have hab : a < b := by
    exact Nat.lt_succ_self j.1
  have hle := (K.boundaryEdgeVertexList_pairwise_parameter_le U hU t i).rel_get_of_lt hab
  have hne : K.levelFaceEdgeParameter t.2.1 i
        (K.adaptiveEdgeIntervalFirst U hU t i j) ≠
      K.levelFaceEdgeParameter t.2.1 i
        (K.adaptiveEdgeIntervalSecond U hU t i j) := by
    intro heq
    exact K.adaptiveEdgeIntervalFirst_ne_second U hU t i j
      (K.levelFaceEdgeParameter_injOn t.2.1 i
        ((K.mem_boundaryEdgeVertices_iff U hU t i _).mp
          (K.adaptiveEdgeIntervalFirst_mem_boundaryEdgeVertices U hU t i j)).2
        ((K.mem_boundaryEdgeVertices_iff U hU t i _).mp
          (K.adaptiveEdgeIntervalSecond_mem_boundaryEdgeVertices U hU t i j)).2
        heq)
  exact lt_of_le_of_ne hle hne

/-- Every parameter on an adaptive edge lies between the parameters of two consecutive
resolved boundary vertices. -/
theorem exists_adaptiveEdgeInterval_parameter_mem_Icc (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ∃ j : K.AdaptiveEdgeInterval U hU t i,
      r ∈ Set.Icc
        (K.levelFaceEdgeParameter t.2.1 i
          (K.adaptiveEdgeIntervalFirst U hU t i j))
        (K.levelFaceEdgeParameter t.2.1 i
          (K.adaptiveEdgeIntervalSecond U hU t i j)) := by
  let L := K.boundaryEdgeVertexList U hU t i
  have hlength : 2 ≤ L.length :=
    K.two_le_boundaryEdgeVertexList_length U hU t i
  have hfirst : K.levelFaceEdgeParameter t.2.1 i
      (L.get ⟨0, by omega⟩) ≤ r := by
    change K.levelFaceEdgeParameter t.2.1 i
      ((K.boundaryEdgeVertexList U hU t i).get ⟨0, by
        have := K.two_le_boundaryEdgeVertexList_length U hU t i
        omega⟩) ≤ r
    rw [K.boundaryEdgeVertexList_first_parameter U hU t i]
    exact hr.1
  have hlast : r ≤ K.levelFaceEdgeParameter t.2.1 i
      (L.get ⟨L.length - 1, by omega⟩) := by
    change r ≤ K.levelFaceEdgeParameter t.2.1 i
      ((K.boundaryEdgeVertexList U hU t i).get
        ⟨(K.boundaryEdgeVertexList U hU t i).length - 1, by
          have := K.two_le_boundaryEdgeVertexList_length U hU t i
          omega⟩)
    rw [K.boundaryEdgeVertexList_last_parameter U hU t i]
    exact hr.2
  obtain ⟨j, hj⟩ := exists_adjacent_get_of_pairwise_le (r := r) L
    (K.levelFaceEdgeParameter t.2.1 i)
    hlength
    (K.boundaryEdgeVertexList_pairwise_parameter_le U hU t i)
    hfirst hlast
  refine ⟨j, ?_⟩
  have hjlt : j.1 < (K.boundaryEdgeVertexList U hU t i).length - 1 := by
    simpa only [L] using j.2
  change K.levelFaceEdgeParameter t.2.1 i
      ((K.boundaryEdgeVertexList U hU t i).get ⟨j.1, by
        omega⟩) ≤ r ∧
    r ≤ K.levelFaceEdgeParameter t.2.1 i
      ((K.boundaryEdgeVertexList U hU t i).get ⟨j.1 + 1, by
        omega⟩)
  exact hj

/-- No resolved boundary mark lies strictly between the two consecutive marks of an adaptive
edge interval. -/
theorem not_parameter_mem_Ioo_adaptiveEdgeInterval (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3)
    (j : K.AdaptiveEdgeInterval U hU t i)
    {p : K.realization} (hp : p ∈ K.boundaryEdgeVertices U hU t i) :
    K.levelFaceEdgeParameter t.2.1 i p ∉ Set.Ioo
      (K.levelFaceEdgeParameter t.2.1 i
        (K.adaptiveEdgeIntervalFirst U hU t i j))
      (K.levelFaceEdgeParameter t.2.1 i
        (K.adaptiveEdgeIntervalSecond U hU t i j)) := by
  let L := K.boundaryEdgeVertexList U hU t i
  let a : Fin L.length := ⟨j.1, by
    have hj := j.2
    dsimp only [L]
    omega⟩
  let b : Fin L.length := ⟨j.1 + 1, by
    have hj := j.2
    dsimp only [L]
    omega⟩
  have hab : a < b := by
    exact Nat.lt_succ_self j.1
  have hpL : p ∈ L :=
    (K.mem_boundaryEdgeVertexList_iff U hU t i p).mpr hp
  obtain ⟨k, hk⟩ := List.get_of_mem hpL
  have hpair := K.boundaryEdgeVertexList_pairwise_parameter_le U hU t i
  intro hpBetween
  by_cases hka : k ≤ a
  · have hle : K.levelFaceEdgeParameter t.2.1 i (L.get k) ≤
        K.levelFaceEdgeParameter t.2.1 i (L.get a) := by
      rcases hka.eq_or_lt with hka | hka
      · rw [hka]
      · exact hpair.rel_get_of_lt hka
    have hpa : K.levelFaceEdgeParameter t.2.1 i p ≤
        K.levelFaceEdgeParameter t.2.1 i
          (K.adaptiveEdgeIntervalFirst U hU t i j) := by
      simpa only [hk, adaptiveEdgeIntervalFirst, L, a] using hle
    exact (not_lt_of_ge hpa) hpBetween.1
  · have hbk : b ≤ k := by
      have : a.1 < k.1 := Nat.lt_of_not_ge hka
      change j.1 < k.1 at this
      change j.1 + 1 ≤ k.1
      omega
    have hle : K.levelFaceEdgeParameter t.2.1 i (L.get b) ≤
        K.levelFaceEdgeParameter t.2.1 i (L.get k) := by
      rcases hbk.eq_or_lt with hbk | hbk
      · rw [hbk]
      · exact hpair.rel_get_of_lt hbk
    have hbp : K.levelFaceEdgeParameter t.2.1 i
          (K.adaptiveEdgeIntervalSecond U hU t i j) ≤
        K.levelFaceEdgeParameter t.2.1 i p := by
      simpa only [hk, adaptiveEdgeIntervalSecond, L, b] using hle
    exact (not_lt_of_ge hbp) hpBetween.2

/-- The countable family of fan triangles before identifying their shared geometric edges. -/
abbrev AdaptiveFanFace (hU : IsOpen U) :=
  Σ t : K.AdaptiveFace U, Σ i : ZMod 3, K.AdaptiveEdgeInterval U hU t i

/-- The finite family of all resolved fan triangles over one adaptive tile. -/
noncomputable def adaptiveFanFacesOver (hU : IsOpen U)
    (t : K.AdaptiveFace U) : Finset (K.AdaptiveFanFace U hU) :=
  ((Finset.univ : Finset (ZMod 3)).sigma fun i ↦
      (Finset.univ : Finset (K.AdaptiveEdgeInterval U hU t i))).map
    ⟨fun p ↦ ⟨t, p⟩, by
      intro p q hpq
      exact eq_of_heq (Sigma.mk.inj_iff.mp hpq).2⟩

theorem mem_adaptiveFanFacesOver_iff (hU : IsOpen U)
    (t : K.AdaptiveFace U) (f : K.AdaptiveFanFace U hU) :
    f ∈ K.adaptiveFanFacesOver U hU t ↔ f.1 = t := by
  classical
  constructor
  · intro hf
    obtain ⟨p, -, hp⟩ := Finset.mem_map.mp hf
    exact (congrArg Sigma.fst hp).symm
  · intro hft
    subst t
    apply Finset.mem_map.mpr
    exact ⟨f.2, by simp, rfl⟩

/-- The `adaptiveFanFaceVertices` declaration. -/
noncomputable def adaptiveFanFaceVertices (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) : Finset K.realization :=
  {K.adaptiveFaceCenter U f.1,
    K.adaptiveEdgeIntervalFirst U hU f.1 f.2.1 f.2.2,
    K.adaptiveEdgeIntervalSecond U hU f.1 f.2.1 f.2.2}

theorem adaptiveFanFaceVertices_card (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    (K.adaptiveFanFaceVertices U hU f).card = 3 := by
  have hp := K.adaptiveEdgeIntervalFirst_mem_boundaryEdgeVertices U hU
    f.1 f.2.1 f.2.2
  have hq := K.adaptiveEdgeIntervalSecond_mem_boundaryEdgeVertices U hU
    f.1 f.2.1 f.2.2
  have hcp : K.adaptiveFaceCenter U f.1 ≠
      K.adaptiveEdgeIntervalFirst U hU f.1 f.2.1 f.2.2 :=
    K.adaptiveFaceCenter_ne_boundaryVertex U hU f.1
      ((K.mem_boundaryEdgeVertices_iff U hU f.1 f.2.1 _).mp hp).1
  have hcq : K.adaptiveFaceCenter U f.1 ≠
      K.adaptiveEdgeIntervalSecond U hU f.1 f.2.1 f.2.2 :=
    K.adaptiveFaceCenter_ne_boundaryVertex U hU f.1
      ((K.mem_boundaryEdgeVertices_iff U hU f.1 f.2.1 _).mp hq).1
  have hpq := K.adaptiveEdgeIntervalFirst_ne_second U hU
    f.1 f.2.1 f.2.2
  simp [adaptiveFanFaceVertices, hcp, hcq, hpq]

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end schottkyclassification07_block_02
/- END ClassificationOfSurfaces.Moise.AdaptiveOpenComplex -/
