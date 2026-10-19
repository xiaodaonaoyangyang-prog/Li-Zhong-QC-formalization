import LiZhongQC.Lemmas.FinitePunctureCompactification

open Complex Set Metric Filter Topology
open scoped Manifold ContDiff
noncomputable section
namespace LiZhongQC
universe u

/-- Compact deleted chart discs are genuinely compact in the surface. -/
theorem s31eg_disc_compact {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {D : Set X} (hD : IsClosedDiscIn D) : IsCompact D := by
  obtain ⟨x, hDs, J, _hJ, hJb, hJt, hDJ, _hc⟩ := hD
  have heq : D = (chartAt ℂ x).symm '' closure J := by
    rw [← hDJ]
    ext y
    constructor
    · intro hy
      exact ⟨chartAt ℂ x y, ⟨y, hy, rfl⟩, (chartAt ℂ x).left_inv (hDs hy)⟩
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
      simpa only [(chartAt ℂ x).left_inv (hDs hw)] using hw
  rw [heq]
  exact hJb.isCompact_closure.image_of_continuousOn
    ((chartAt ℂ x).continuousOn_symm.mono hJt)

/-- Open embeddings into compact Hausdorff spaces have no interior cluster
point at a missing source point. No finiteness of the complement is needed. -/
theorem s31eg_cluster_missing {A X Y : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [CompactSpace Y]
    (i : A → X) (j : A → Y) (hi : Continuous i) (hj : Topology.IsOpenEmbedding j)
    {x : X} (hx : x ∉ range i)
    {y : Y} (hy : ClusterPt y (map j (comap i (𝓝 x)))) : y ∉ range j := by
  intro hyr
  have hclosed : IsClosed (range j)ᶜ := hj.isOpen_range.isClosed_compl
  have hd : Disjoint (range j)ᶜ ({y} : Set Y) :=
    disjoint_singleton_right.2 (fun h => h hyr)
  obtain ⟨U, V, hU, hV, hmiss, hyV, hdisj⟩ :=
    normal_separation hclosed isClosed_singleton hd
  obtain ⟨W, hW, himage⟩ :=
    s31fe_near_missing i j hi hj.isEmbedding hx hU hmiss
  have hmem : U ∈ map j (comap i (𝓝 x)) := by
    apply mem_map.2
    exact mem_of_superset (preimage_mem_comap hW) (fun a ha => himage a ha)
  obtain ⟨z, hzV, hzU⟩ := (clusterPt_iff_nonempty.1 hy)
    (hV.mem_nhds (hyV (mem_singleton y))) hmem
  exact disjoint_left.1 hdisj hzU hzV

/-- A connected end trace converges to one member of a finite disjoint compact
deletion family. The component and all its eventual neighborhoods are proved,
not supplied as an endpoint assignment or trapping hypothesis. -/
theorem s31eg_component_trapping {A X Y I : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [CompactSpace Y] [Finite I]
    (i : A → X) (j : A → Y) (hi : Continuous i) (hj : Topology.IsOpenEmbedding j)
    (B : I → Set Y) (hB : ∀ k, IsCompact (B k))
    (hdis : Pairwise fun k l => Disjoint (B k) (B l))
    (hcover : (range j)ᶜ = ⋃ k, B k)
    {x : X} (hx : x ∉ range i) [NeBot (comap i (𝓝 x))]
    (hconn : ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsPreconnected (i ⁻¹' V)) :
    ∃ k, ∀ W : Set Y, IsOpen W → B k ⊆ W →
      ∃ U ∈ 𝓝 x, ∀ a, i a ∈ U → j a ∈ W := by
  classical
  obtain ⟨y, hy⟩ := exists_clusterPt_of_compactSpace (map j (comap i (𝓝 x)))
  have hym := s31eg_cluster_missing i j hi hj hx hy
  change y ∈ (range j)ᶜ at hym
  rw [hcover] at hym
  obtain ⟨k, hyk⟩ := mem_iUnion.1 hym
  refine ⟨k, ?_⟩
  intro W hW hBW
  let R : Set Y := ⋃ l : {l : I // l ≠ k}, B l.1
  have hR : IsClosed R := (isCompact_iUnion (fun l : {l : I // l ≠ k} => hB l.1)).isClosed
  have hd : Disjoint (B k) R := by
    apply disjoint_left.2
    intro z hzk hzR
    obtain ⟨l, hzl⟩ := mem_iUnion.1 hzR
    exact disjoint_left.1 (hdis (Ne.symm l.2)) hzk hzl
  obtain ⟨O, V, hO, hV, hBO, hRV, hOV⟩ :=
    normal_separation (hB k).isClosed hR hd
  have hcov : (range j)ᶜ ⊆ (O ∩ W) ∪ V := by
    intro z hz
    rw [hcover] at hz
    obtain ⟨l, hzl⟩ := mem_iUnion.1 hz
    by_cases hl : l = k
    · subst l
      exact Or.inl ⟨hBO hzl, hBW hzl⟩
    · exact Or.inr (hRV (mem_iUnion.2 ⟨⟨l, hl⟩, hzl⟩))
  obtain ⟨N, hN, hnear⟩ := s31fe_near_missing i j hi hj.isEmbedding hx
    ((hO.inter hW).union hV) hcov
  obtain ⟨T, hT, hTN, hTc⟩ := hconn N hN
  have hC : IsPreconnected (j '' (i ⁻¹' T)) :=
    hTc.image j hj.continuous.continuousOn
  have hCs : j '' (i ⁻¹' T) ⊆ (O ∩ W) ∪ V := by
    rintro z ⟨a, ha, rfl⟩
    exact hnear a (hTN ha)
  have hCe : (j '' (i ⁻¹' T)) ∩ ((O ∩ W) ∩ V) = ∅ := by
    apply eq_empty_iff_forall_notMem.2
    rintro z ⟨_, ⟨hzO, _⟩, hzV⟩
    exact disjoint_left.1 hOV hzO hzV
  rcases (isPreconnected_iff_subset_of_disjoint.1 hC)
      (O ∩ W) V (hO.inter hW) hV hCs hCe with hleft | hright
  · exact ⟨T, hT, fun a ha => (hleft ⟨a, ha, rfl⟩).2⟩
  · have hCm : j '' (i ⁻¹' T) ∈ map j (comap i (𝓝 x)) :=
      image_mem_map (preimage_mem_comap hT)
    obtain ⟨z, hzO, hzC⟩ := (clusterPt_iff_nonempty.1 hy)
      (hO.mem_nhds (hBO hyk)) hCm
    exact (disjoint_left.1 hOV hzO (hright hzC)).elim

/-- Actual punctures have connected traces even when other deleted components
are closed discs: first shrink away from their compact union. -/
theorem s31eg_puncture_connected_traces {S : Type u} [TopologicalSpace S]
    [ChartedSpace ℂ S] {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    {x : F.X.carrier} (hx : x ∈ F.P) :
    ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsPreconnected (F.ι ⁻¹' V) := by
  intro U hU
  let H : Set F.X.carrier := ⋃ j, F.D j
  have hH : IsClosed H := (isCompact_iUnion (fun j => s31eg_disc_compact (F.disc j))).isClosed
  have hxH : x ∉ H := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.1 h
    exact disjoint_left.1 (F.disjoint_P j) hj hx
  obtain ⟨V, hV, hVU, hc⟩ := s31cg_punctured_chart_basis
    (↑F.P) F.P.finite_toSet hx (U ∩ Hᶜ)
    (Filter.inter_mem hU (hH.isOpen_compl.mem_nhds hxH))
  refine ⟨V, hV, fun z hz => (hVU hz).1, ?_⟩
  apply F.embedding.isEmbedding.toIsInducing.isPreconnected_image.1
  rw [image_preimage_eq_inter_range, F.range_ι]
  have heq : V ∩ (↑F.P ∪ ⋃ j, F.D j)ᶜ = V \ ↑F.P := by
    ext z
    constructor
    · rintro ⟨hzV, hz⟩
      exact ⟨hzV, fun hp => hz (Or.inl hp)⟩
    · rintro ⟨hzV, hzP⟩
      refine ⟨hzV, ?_⟩
      rintro (hp | hD)
      · exact hzP hp
      · exact (hVU hzV).2 hD
  rw [heq]
  exact hc

/-- The source puncture filter is nontrivial despite the presence of holes. -/
theorem s31eg_puncture_neBot {S : Type u} [TopologicalSpace S]
    [ChartedSpace ℂ S] {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    {x : F.X.carrier} (hx : x ∈ F.P) : NeBot (comap F.ι (𝓝 x)) := by
  letI : ∀ y : F.X.carrier, NeBot (𝓝[≠] y) := s31cg_punctured_nhds_neBot
  have hdense : Dense ((↑F.P : Set F.X.carrier)ᶜ) := by
    simpa only [sdiff_eq, univ_inter] using
      (dense_univ : Dense (univ : Set F.X.carrier)).sdiff_finite F.P.finite_toSet
  let H : Set F.X.carrier := ⋃ j, F.D j
  have hH : IsClosed H := (isCompact_iUnion (fun j => s31eg_disc_compact (F.disc j))).isClosed
  have hxH : x ∉ H := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.1 h
    exact disjoint_left.1 (F.disjoint_P j) hj hx
  apply comap_neBot_iff.2
  intro U hU
  obtain ⟨y, hyU, hyP⟩ := (mem_closure_iff_nhds.1 (hdense x))
    (U ∩ Hᶜ) (Filter.inter_mem hU (hH.isOpen_compl.mem_nhds hxH))
  have hyr : y ∈ range F.ι := by
    rw [F.range_ι]
    rintro (hp | hD)
    · exact hyP hp
    · exact hyU.2 hD
  obtain ⟨a, rfl⟩ := hyr
  exact ⟨a, hyU.1⟩

/-- The actual finite deletion family, with separate indices for punctures and
closed discs. This definition contains only the given geometric sets. -/
def s31eg_component {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {g n m : ℕ} (F : FiniteTypeStructure S g n m) :
    (↥F.P ⊕ Fin m) → Set F.X.carrier :=
  Sum.elim (fun p => {p.1}) F.D

theorem s31eg_components_compact {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {g n m : ℕ} (F : FiniteTypeStructure S g n m) :
    ∀ k, IsCompact (s31eg_component F k) := by
  intro k
  cases k with
  | inl p => exact isCompact_singleton
  | inr j => exact s31eg_disc_compact (F.disc j)

theorem s31eg_components_disjoint {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {g n m : ℕ} (F : FiniteTypeStructure S g n m) :
    Pairwise fun k l => Disjoint (s31eg_component F k) (s31eg_component F l) := by
  intro k l hkl
  cases k with
  | inl p =>
    cases l with
    | inl q =>
      apply disjoint_singleton_right.2
      intro he
      apply hkl
      have hpq : p = q := Subtype.ext (mem_singleton_iff.1 he).symm
      exact congrArg Sum.inl hpq
    | inr j =>
      apply disjoint_left.2
      intro z hz hzD
      have hzp : z = p.1 := hz
      exact disjoint_left.1 (F.disjoint_P j) hzD (hzp.symm ▸ p.2)
  | inr j =>
    cases l with
    | inl p =>
      apply disjoint_left.2
      intro z hzD hz
      have hzp : z = p.1 := hz
      exact disjoint_left.1 (F.disjoint_P j) hzD (hzp.symm ▸ p.2)
    | inr k =>
      exact F.disjoint (fun he => hkl (congrArg Sum.inr he))

theorem s31eg_components_cover {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {g n m : ℕ} (F : FiniteTypeStructure S g n m) :
    (range F.ι)ᶜ = ⋃ k, s31eg_component F k := by
  rw [F.range_ι, compl_compl]
  ext x
  constructor
  · rintro (hp | hD)
    · exact mem_iUnion.2 ⟨Sum.inl ⟨x, hp⟩, rfl⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hD
      exact mem_iUnion.2 ⟨Sum.inr j, hj⟩
  · intro h
    obtain ⟨k, hk⟩ := mem_iUnion.1 h
    cases k with
    | inl p =>
      have hxp : x = p.1 := hk
      exact Or.inl (hxp.symm ▸ p.2)
    | inr j => exact Or.inr (mem_iUnion.2 ⟨j, hk⟩)

/-- Global trapping for two actual finite-type presentations. No finite-cover,
local connectedness, nontrivial-filter, or endpoint assignment is assumed. -/
theorem s31eg_puncture_component {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {g n m g' n' m' : ℕ} (F : FiniteTypeStructure S g n m)
    (G : FiniteTypeStructure S g' n' m') {p : F.X.carrier} (hp : p ∈ F.P) :
    ∃ k : ↥G.P ⊕ Fin m', ∀ W : Set G.X.carrier, IsOpen W →
      s31eg_component G k ⊆ W →
      ∃ U ∈ 𝓝 p, ∀ a, F.ι a ∈ U → G.ι a ∈ W := by
  letI := s31eg_puncture_neBot F hp
  have hpr : p ∉ range F.ι := by
    rw [F.range_ι]
    exact fun h => h (Or.inl hp)
  exact s31eg_component_trapping F.ι G.ι F.embedding.continuous G.embedding
    (s31eg_component G) (s31eg_components_compact G) (s31eg_components_disjoint G)
    (s31eg_components_cover G) hpr (s31eg_puncture_connected_traces F hp)

end LiZhongQC

