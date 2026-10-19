import LiZhongQC.Lemmas.SchottkyDoubleCarrier

open Set Topology Filter
noncomputable section
namespace LiZhongQC
universe u

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
  {g n m : ℕ} (F : FiniteTypeStructure S g n m)

/-- Disjointness prevents two closed holes from jointly creating new interior. -/
theorem s31dt_disc_union_interior :
    interior (⋃ j, F.D j) = ⋃ j, interior (F.D j) := by
  classical
  apply Subset.antisymm
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (interior_subset hx)
    let E : Set F.X.carrier := ⋃ k, if k = j then ∅ else F.D k
    have hEc : IsClosed E := by
      apply isClosed_iUnion_of_finite
      intro k
      split_ifs
      · exact isClosed_empty
      · exact (s31eg_disc_compact (F.disc k)).isClosed
    have hxE : x ∉ E := by
      intro h
      obtain ⟨k, hk⟩ := mem_iUnion.mp h
      by_cases hkj : k = j
      · simpa only [if_pos hkj, mem_empty_iff_false] using hk
      · have hkD : x ∈ F.D k := by simpa only [if_neg hkj] using hk
        exact Set.disjoint_left.mp (F.disjoint (Ne.symm hkj)) hj hkD
    have hsub : interior (⋃ k, F.D k) ∩ Eᶜ ⊆ F.D j := by
      intro y hy
      obtain ⟨k, hk⟩ := mem_iUnion.mp (interior_subset hy.1)
      by_cases hkj : k = j
      · simpa only [hkj] using hk
      · exact False.elim (hy.2 (mem_iUnion.mpr ⟨k, by
          simpa only [if_neg hkj] using hk⟩))
    exact mem_iUnion.mpr ⟨j,
      interior_maximal hsub (isOpen_interior.inter hEc.isOpen_compl) ⟨hx, hxE⟩⟩
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact interior_mono (subset_iUnion F.D j) hj

/-- The core is exactly the closure of the original embedded surface. -/
theorem s31dt_closure_original : closure (range F.ι) = s31dt_coreSet F := by
  letI : ∀ x : F.X.carrier, NeBot (𝓝[≠] x) := s31cg_punctured_nhds_neBot
  have hP : interior (↑F.P : Set F.X.carrier) = ∅ := by
    apply interior_eq_empty_iff_dense_compl.mpr
    simpa only [sdiff_eq, univ_inter] using (dense_univ.sdiff_finset F.P)
  have hD : IsClosed (⋃ j, F.D j) :=
    isClosed_iUnion_of_finite (fun j => (s31eg_disc_compact (F.disc j)).isClosed)
  rw [F.range_ι, closure_compl, union_comm (↑F.P : Set F.X.carrier),
    interior_union_isClosed_of_interior_empty hD hP, s31dt_disc_union_interior]
  rfl

theorem s31dt_originalCore_dense : DenseRange (s31dt_originalCore F) := by
  change Dense (range (s31dt_originalCore F))
  rw [dense_iff_closure_eq,
    Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have him : (Subtype.val : s31dt_Core F → F.X.carrier) ''
      range (s31dt_originalCore F) = range F.ι := by
    rw [← range_comp]
    rfl
  rw [him, s31dt_closure_original]
  ext x
  exact iff_true_intro x.property

theorem s31dt_core_connected [ConnectedSpace S] : ConnectedSpace (s31dt_Core F) := by
  letI : PreconnectedSpace (s31dt_Core F) := (s31dt_originalCore_dense F).preconnectedSpace
    (s31dt_originalCore_openEmbedding F).continuous
  exact ⟨⟨s31dt_originalCore F (Classical.choice inferInstance)⟩⟩

theorem s31dt_frontier_mem_core {j : Fin m} {x : F.X.carrier}
    (hx : x ∈ frontier (F.D j)) : x ∈ s31dt_coreSet F := by
  have hxD : x ∈ F.D j := by
    have hc := frontier_subset_closure hx
    rwa [(s31eg_disc_compact (F.disc j)).isClosed.closure_eq] at hc
  intro hi
  obtain ⟨k, hk⟩ := mem_iUnion.mp hi
  by_cases hjk : j = k
  · subst k
    exact (mem_frontier_iff_notMem_interior hxD).mp hx hk
  · exact Set.disjoint_left.mp (F.disjoint hjk) hxD (interior_subset hk)

/-- An actual hole supplies an actual seam point; nonemptiness is not assumed. -/
theorem s31dt_boundary_nonempty [Nonempty S] (hm : m ≠ 0) :
    (s31dt_boundary F).Nonempty := by
  let j : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
  obtain ⟨a, ha, J, hJ, hJb, hJt, hJeq, hrest⟩ := F.disc j
  obtain ⟨z, hz⟩ := hJ.2.1.nonempty
  have hz' : z ∈ chartAt ℂ a '' F.D j := hJeq.symm ▸ subset_closure hz
  obtain ⟨d, hd, hdz⟩ := hz'
  have hproper : F.D j ≠ univ := by
    intro he
    have hs := s31dt_original_avoids_disc F (Classical.choice inferInstance) j
    exact hs (he.symm ▸ mem_univ _)
  obtain ⟨x, hx⟩ := nonempty_frontier_iff.mpr ⟨⟨d, hd⟩, hproper⟩
  exact ⟨⟨x, s31dt_frontier_mem_core F hx⟩, j, hx⟩

theorem s31dt_double_connected [ConnectedSpace S] (hm : m ≠ 0) :
    ConnectedSpace (s31dt_Double F) := by
  letI := s31dt_core_connected F
  obtain ⟨x, hx⟩ := s31dt_boundary_nonempty F hm
  have hi : (range (s31dt_side F false) ∩ range (s31dt_side F true)).Nonempty := by
    refine ⟨s31dt_side F false x, ⟨x, rfl⟩, x, ?_⟩
    exact ((s31dt_opposite_eq_iff F x x).mpr ⟨rfl, hx⟩).symm
  have hc := IsConnected.union hi (isConnected_range (s31dt_continuous_side F false))
    (isConnected_range (s31dt_continuous_side F true))
  rw [s31dt_side_cover] at hc
  exact connectedSpace_iff_univ.mpr hc

theorem s31dt_side_closedEmbedding (b : Bool) :
    Topology.IsClosedEmbedding (s31dt_side F b) := by
  letI := s31dt_core_compact F
  letI := s31dt_double_t2 F
  exact (s31dt_continuous_side F b).isClosedEmbedding (s31dt_side_injective F b)

/-- The closure of each copy of S is exactly its filled, closed half. -/
theorem s31dt_closure_embed (b : Bool) :
    closure (range (s31dt_embed F b)) = range (s31dt_side F b) := by
  change closure (range (s31dt_side F b ∘ s31dt_originalCore F)) = _
  rw [range_comp, (s31dt_side_closedEmbedding F b).closure_image_eq,
    (s31dt_originalCore_dense F).closure_eq, image_univ]

end LiZhongQC
end


open Set Topology
noncomputable section
namespace LiZhongQC
universe u

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
  {g n m : ℕ} (F : FiniteTypeStructure S g n m)

/-- The precise fixed-curves condition for the concrete carrier. The only
parameter identifying Pd is its explicit set of original and mirror punctures,
as produced by s31sd_concrete_marked_points; no topological conclusion is assumed. -/
theorem s31dt_fixed_curves (Pd : Finset (s31dt_Double F))
    (hPd : (↑Pd : Set (s31dt_Double F)) =
      s31dt_side F false '' {x : s31dt_Core F | x.val ∈ F.P} ∪
      s31dt_side F true '' {x : s31dt_Core F | x.val ∈ F.P}) :
    {q | s31dt_flipHomeomorph F q = q} =
      frontier (range (s31dt_embed F false)) \ ↑Pd := by
  change {q | s31dt_flip F q = q} = _
  rw [s31dt_fixed_set,
    (s31dt_embed_openEmbedding F false).isOpen_range.frontier_eq,
    s31dt_closure_embed]
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨⟨x, rfl⟩, ?_⟩, ?_⟩
    · rintro ⟨s, hs⟩
      have he : s31dt_originalCore F s = x := s31dt_side_injective F false hs
      exact s31dt_originalCore_not_boundary F s (he.symm ▸ hx)
    · intro hq
      rw [hPd] at hq
      have hPx : x.val ∈ F.P := by
        rcases hq with hq | hq
        · obtain ⟨y, hy, he⟩ := hq
          have hey : y = x := congrArg (s31dt_project F) he
          exact hey ▸ hy
        · obtain ⟨y, hy, he⟩ := hq
          have hey : y = x := congrArg (s31dt_project F) he
          exact hey ▸ hy
      obtain ⟨j, hj⟩ := hx
      have hxD : x.val ∈ F.D j := by
        have hc := frontier_subset_closure hj
        rwa [(s31eg_disc_compact (F.disc j)).isClosed.closure_eq] at hc
      exact Set.disjoint_left.mp (F.disjoint_P j) hxD hPx
  · rintro ⟨⟨⟨x, rfl⟩, hnotS⟩, hnotP⟩
    refine ⟨x, ?_, rfl⟩
    have hxP : x.val ∉ F.P := by
      intro hp
      apply hnotP
      rw [hPd]
      exact Or.inl ⟨x, hp, rfl⟩
    have hxS : x.val ∉ range F.ι := by
      rintro ⟨s, hs⟩
      apply hnotS
      refine ⟨s, ?_⟩
      apply congrArg (s31dt_side F false)
      exact Subtype.ext hs
    have hxD : x.val ∈ ⋃ j, F.D j := by
      by_contra h
      apply hxS
      rw [F.range_ι]
      exact fun hh => hh.elim hxP h
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxD
    refine ⟨j, (mem_frontier_iff_notMem_interior hj).mpr ?_⟩
    intro hi
    exact x.property (mem_iUnion.mpr ⟨j, hi⟩)

end LiZhongQC
end
