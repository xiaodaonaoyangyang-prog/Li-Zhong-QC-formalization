import LiZhongQC.Ch09.S31_FiniteType

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

/-- Near a missing source point, a change of embedded model escapes every compact
set lying in the target image. -/
theorem s31fe_escape_compact {A X Y : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    (i : A → X) (j : A → Y) (hi : Continuous i) (hj : Topology.IsEmbedding j)
    {x : X} (hx : x ∉ range i) {K : Set Y} (hK : IsCompact K) (hKr : K ⊆ range j) :
    ∃ U ∈ 𝓝 x, ∀ a, i a ∈ U → j a ∉ K := by
  have hpre : IsCompact (j ⁻¹' K) := hj.isCompact_iff.2 (by
    rw [image_preimage_eq_of_subset hKr]
    exact hK)
  have hc : IsClosed (i '' (j ⁻¹' K)) := (hpre.image hi).isClosed
  have hxi : x ∉ i '' (j ⁻¹' K) := by
    rintro ⟨a, _, ha⟩
    exact hx ⟨a, ha⟩
  refine ⟨(i '' (j ⁻¹' K))ᶜ, hc.isOpen_compl.mem_nhds hxi, ?_⟩
  intro a ha hja
  exact ha ⟨a, hja, rfl⟩

/-- Every open neighborhood of all missing target points eventually contains
the image of a neighborhood trace at a missing source point. -/
theorem s31fe_near_missing {A X Y : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [CompactSpace Y]
    (i : A → X) (j : A → Y) (hi : Continuous i) (hj : Topology.IsEmbedding j)
    {x : X} (hx : x ∉ range i) {W : Set Y} (hW : IsOpen W)
    (hmissing : (range j)ᶜ ⊆ W) :
    ∃ U ∈ 𝓝 x, ∀ a, i a ∈ U → j a ∈ W := by
  classical
  have hsub : Wᶜ ⊆ range j := by
    intro y hy
    by_contra hyr
    exact hy (hmissing hyr)
  obtain ⟨U, hU, hescape⟩ := s31fe_escape_compact i j hi hj hx hW.isClosed_compl.isCompact hsub
  exact ⟨U, hU, fun a ha => by simpa using hescape a ha⟩

/-- A cluster point at a missing source point cannot be an interior target point.
Finiteness separates the missing set from that alleged interior cluster point. -/
theorem s31fe_cluster_missing {A X Y : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [CompactSpace Y]
    (i : A → X) (j : A → Y) (hi : Continuous i) (hj : Topology.IsEmbedding j)
    (hfinite : ((range j)ᶜ).Finite) {x : X} (hx : x ∉ range i)
    {y : Y} (hy : ClusterPt y (map j (comap i (𝓝 x)))) : y ∉ range j := by
  intro hyr
  have hd : Disjoint ((range j)ᶜ) ({y} : Set Y) := by
    apply disjoint_singleton_right.2
    exact fun h => h hyr
  obtain ⟨U, V, hU, hV, hmiss, hyV, hdisj⟩ :=
    SeparatedNhds.of_finite hfinite (finite_singleton y) hd
  obtain ⟨W, hW, himage⟩ := s31fe_near_missing i j hi hj hx hU hmiss
  have hmem : U ∈ map j (comap i (𝓝 x)) := by
    apply mem_map.2
    exact mem_of_superset (preimage_mem_comap hW) (fun a ha => himage a ha)
  obtain ⟨z, hzV, hzU⟩ := (clusterPt_iff_nonempty.1 hy)
    (hV.mem_nhds (hyV (mem_singleton y))) hmem
  exact disjoint_left.1 hdisj hzU hzV

/-- Connected neighborhood traces prevent two distinct missing target cluster
points. The local trace hypothesis contains no endpoint assignment or extension. -/
theorem s31fe_cluster_unique {A X Y : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [CompactSpace Y]
    (i : A → X) (j : A → Y) (hi : Continuous i) (hj : Topology.IsEmbedding j)
    (hfinite : ((range j)ᶜ).Finite) {x : X} (hx : x ∉ range i)
    (hconn : ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsPreconnected (i ⁻¹' V))
    {y z : Y} (hy : ClusterPt y (map j (comap i (𝓝 x))))
    (hz : ClusterPt z (map j (comap i (𝓝 x)))) : y = z := by
  classical
  have hym := s31fe_cluster_missing i j hi hj hfinite hx hy
  have hzm := s31fe_cluster_missing i j hi hj hfinite hx hz
  by_contra hyz
  have hd : Disjoint ({y} : Set Y) ((range j)ᶜ \ {y}) := by simp
  obtain ⟨U, V, hU, hV, hyU, hrestV, hdisj⟩ :=
    SeparatedNhds.of_finite (finite_singleton y) (hfinite.subset sdiff_subset) hd
  have hcover : (range j)ᶜ ⊆ U ∪ V := by
    intro w hw
    by_cases hwy : w = y
    · subst w
      exact Or.inl (hyU (mem_singleton y))
    · exact Or.inr (hrestV ⟨hw, hwy⟩)
  obtain ⟨W, hW, hnear⟩ := s31fe_near_missing i j hi hj hx (hU.union hV) hcover
  obtain ⟨B, hB, hBW, hBc⟩ := hconn W hW
  have hC : IsPreconnected (j '' (i ⁻¹' B)) := hBc.image j hj.continuous.continuousOn
  have hCs : j '' (i ⁻¹' B) ⊆ U ∪ V := by
    rintro w ⟨a, ha, rfl⟩
    exact hnear a (hBW ha)
  have hCe : (j '' (i ⁻¹' B)) ∩ (U ∩ V) = ∅ := by
    apply eq_empty_iff_forall_notMem.2
    rintro w ⟨_, hwU, hwV⟩
    exact disjoint_left.1 hdisj hwU hwV
  have hCmem : j '' (i ⁻¹' B) ∈ map j (comap i (𝓝 x)) :=
    image_mem_map (preimage_mem_comap hB)
  rcases (isPreconnected_iff_subset_of_disjoint.1 hC) U V hU hV hCs hCe with hCU | hCV
  · obtain ⟨w, hwV, hwC⟩ := (clusterPt_iff_nonempty.1 hz)
      (hV.mem_nhds (hrestV ⟨hzm, Ne.symm hyz⟩)) hCmem
    exact disjoint_left.1 hdisj (hCU hwC) hwV
  · obtain ⟨w, hwU, hwC⟩ := (clusterPt_iff_nonempty.1 hy)
      (hU.mem_nhds (hyU (mem_singleton y))) hCmem
    exact disjoint_left.1 hdisj hwU (hCV hwC)

/-- Each nontrivial connected end trace has one actual limiting missing point. -/
theorem s31fe_exists_unique_endpoint {A X Y : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [CompactSpace Y]
    (i : A → X) (j : A → Y) (hi : Continuous i) (hj : Topology.IsEmbedding j)
    (hfinite : ((range j)ᶜ).Finite) {x : X} (hx : x ∉ range i)
    [NeBot (comap i (𝓝 x))]
    (hconn : ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsPreconnected (i ⁻¹' V)) :
    ∃! y : Y, y ∉ range j ∧ Tendsto j (comap i (𝓝 x)) (𝓝 y) := by
  obtain ⟨y, hy⟩ := exists_clusterPt_of_compactSpace (map j (comap i (𝓝 x)))
  have ht : Tendsto j (comap i (𝓝 x)) (𝓝 y) :=
    tendsto_nhds_of_unique_mapClusterPt (fun z hz => s31fe_cluster_unique i j hi hj hfinite hx hconn hz hy)
  refine ⟨y, ⟨s31fe_cluster_missing i j hi hj hfinite hx hy, ht⟩, ?_⟩
  intro z hz
  exact tendsto_nhds_unique hz.2 ht

/-- Limits at missing points, together with continuity on the embedded space,
provide the full hypothesis of Mathlib's dense extension theorem. -/
theorem s31fe_limits_everywhere {A X Y : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [CompactSpace Y]
    (i : A → X) (j : A → Y) (hi : Topology.IsEmbedding i) (hj : Topology.IsEmbedding j)
    (hdi : DenseRange i) (hfinite : ((range j)ᶜ).Finite)
    (hconn : ∀ x ∉ range i, ∀ U ∈ 𝓝 x,
      ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsPreconnected (i ⁻¹' V)) :
    ∀ x, ∃ y, Tendsto j (comap i (𝓝 x)) (𝓝 y) := by
  let di : IsDenseInducing i := ⟨hi.toIsInducing, hdi⟩
  intro x
  by_cases hx : x ∈ range i
  · obtain ⟨a, rfl⟩ := hx
    refine ⟨j a, ?_⟩
    rw [← di.nhds_eq_comap a]
    exact hj.continuous.tendsto a
  · letI : NeBot (comap i (𝓝 x)) := di.comap_nhds_neBot x
    obtain ⟨y, hy, _⟩ := s31fe_exists_unique_endpoint i j hi.continuous hj hfinite hx (hconn x hx)
    exact ⟨y, hy.2⟩

/-- Finite missing sets with locally connected traces determine the same compact
space. Both maps and their inverse laws are constructed; no global extension
or matching of missing points is assumed. -/
theorem s31fe_extend_finite_missing {A X Y : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [CompactSpace X] [CompactSpace Y]
    (i : A → X) (j : A → Y) (hi : Topology.IsEmbedding i) (hj : Topology.IsEmbedding j)
    (hdi : DenseRange i) (hdj : DenseRange j)
    (hfi : ((range i)ᶜ).Finite) (hfj : ((range j)ᶜ).Finite)
    (hci : ∀ x ∉ range i, ∀ U ∈ 𝓝 x,
      ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsPreconnected (i ⁻¹' V))
    (hcj : ∀ y ∉ range j, ∀ U ∈ 𝓝 y,
      ∃ V ∈ 𝓝 y, V ⊆ U ∧ IsPreconnected (j ⁻¹' V)) :
    ∃! H : X ≃ₜ Y, ∀ a, H (i a) = j a := by
  let di : IsDenseInducing i := ⟨hi.toIsInducing, hdi⟩
  let dj : IsDenseInducing j := ⟨hj.toIsInducing, hdj⟩
  let F : X → Y := di.extend j
  let G : Y → X := dj.extend i
  have hF : Continuous F := di.continuous_extend (s31fe_limits_everywhere i j hi hj hdi hfj hci)
  have hG : Continuous G := dj.continuous_extend (s31fe_limits_everywhere j i hj hi hdj hfi hcj)
  have hFi : ∀ a, F (i a) = j a := di.extend_eq hj.continuous
  have hGj : ∀ a, G (j a) = i a := dj.extend_eq hi.continuous
  have hGF : G ∘ F = id := hdi.equalizer (hG.comp hF) continuous_id (by
    funext a
    change G (F (i a)) = i a
    rw [hFi, hGj])
  have hFG : F ∘ G = id := hdj.equalizer (hF.comp hG) continuous_id (by
    funext a
    change F (G (j a)) = j a
    rw [hGj, hFi])
  let H : X ≃ₜ Y :=
    { toFun := F
      invFun := G
      left_inv := fun x => congrFun hGF x
      right_inv := fun y => congrFun hFG y
      continuous_toFun := hF
      continuous_invFun := hG }
  refine ⟨H, hFi, ?_⟩
  intro H' hH'
  apply Homeomorph.ext
  have heq : (H' : X → Y) = H := hdi.equalizer H'.continuous H.continuous (by
    funext a
    exact (hH' a).trans (hFi a).symm)
  exact congrFun heq

/-- The constructed compactification homeomorphism restricts to a bijection of
the missing sets, so their cardinalities agree. -/
theorem s31fe_missing_equiv {A X Y : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    (i : A → X) (j : A → Y) (H : X ≃ₜ Y) (hH : ∀ a, H (i a) = j a) :
    Nonempty (((range i)ᶜ : Set X) ≃ ((range j)ᶜ : Set Y)) ∧
      ((range i)ᶜ).ncard = ((range j)ᶜ).ncard := by
  have hr : ∀ x, H x ∈ range j ↔ x ∈ range i := by
    intro x
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, H.injective ((hH a).trans ha)⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, (hH a).symm⟩
  let E : ((range i)ᶜ : Set X) ≃ ((range j)ᶜ : Set Y) :=
    { toFun := fun x => ⟨H x.val, fun hx => x.property ((hr x.val).1 hx)⟩
      invFun := fun y => ⟨H.symm y.val, fun hy => y.property (by
        have h := (hr (H.symm y.val)).2 hy
        simpa only [H.apply_symm_apply] using h)⟩
      left_inv := fun x => Subtype.ext (H.symm_apply_apply x.val)
      right_inv := fun y => Subtype.ext (H.apply_symm_apply y.val) }
  exact ⟨⟨E⟩, Set.ncard_congr' E⟩

/-- Finite complements are dense when the ambient space has no isolated points. -/
theorem s31fe_denseRange_of_finite_compl {A X : Type*} [TopologicalSpace X] [T1Space X]
    [∀ x : X, NeBot (𝓝[≠] x)] (i : A → X) (hfinite : ((range i)ᶜ).Finite) :
    DenseRange i := by
  show Dense (range i)
  simpa using (dense_univ : Dense (univ : Set X)).sdiff_finite hfinite

/-- The no-hole finite-type conclusion now reduces only to density and the
local connected-trace geometry of the supplied open embeddings. The end
matching, global extension, cardinality comparison, and genus transport are
proved here, rather than included among the hypotheses. -/
theorem s31fe_no_holes_unique_of_connected_traces {S : Type u}
    [TopologicalSpace S] [ChartedSpace ℂ S] {g n g' n' : ℕ}
    (F : FiniteTypeStructure S g n 0) (F' : FiniteTypeStructure S g' n' 0)
    (hd : DenseRange F.ι) (hd' : DenseRange F'.ι)
    (hc : ∀ x ∉ range F.ι, ∀ U ∈ 𝓝 x,
      ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsPreconnected (F.ι ⁻¹' V))
    (hc' : ∀ y ∉ range F'.ι, ∀ U ∈ 𝓝 y,
      ∃ V ∈ 𝓝 y, V ⊆ U ∧ IsPreconnected (F'.ι ⁻¹' V)) :
    g = g' ∧ n = n' := by
  have hr : (range F.ι)ᶜ = (↑F.P : Set F.X.carrier) := by rw [F.range_ι]; simp
  have hr' : (range F'.ι)ᶜ = (↑F'.P : Set F'.X.carrier) := by rw [F'.range_ι]; simp
  have hf : ((range F.ι)ᶜ).Finite := hr.symm ▸ F.P.finite_toSet
  have hf' : ((range F'.ι)ᶜ).Finite := hr'.symm ▸ F'.P.finite_toSet
  obtain ⟨H, hH, _⟩ := s31fe_extend_finite_missing F.ι F'.ι
    F.embedding.isEmbedding F'.embedding.isEmbedding hd hd' hf hf' hc hc'
  have hcard := (s31fe_missing_equiv F.ι F'.ι H hH).2
  rw [hr, hr'] at hcard
  have hcard' : F.P.card = F'.P.card := by simpa using hcard
  exact ⟨closed_surface_genus_unique (hasGenus_of_homeomorph F.genus H) F'.genus,
    F.card_P.symm.trans (hcard'.trans F'.card_P)⟩

end LiZhongQC

