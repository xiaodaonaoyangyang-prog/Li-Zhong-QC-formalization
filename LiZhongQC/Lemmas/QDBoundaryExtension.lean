import LiZhongQC.Lemmas.QDReflectionAfterHalves
import LiZhongQC.Lemmas.QDReflectionPuncturePoles
import LiZhongQC.Lemmas.QDTransportZero
import LiZhongQC.Lemmas.QDSeamFill
import LiZhongQC.Lemmas.SchottkyCollarFromDouble
import LiZhongQC.Lemmas.QDDecompBoundaryJet
import LiZhongQC.Lemmas.QDBoundaryLimit
import LiZhongQC.Lemmas.S6bBoundaryTangent
import LiZhongQC.Lemmas.QDCollarCenterReal
import LiZhongQC.Lemmas.QDCollarPullbackRel
open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u


/-- (G1) Every point of the frontier of a hole is an end of `ι(S)` approaching a `J`-fixed point of the double: there is
a filter on `S` along which `F.ι` tends to `ζ` and `ιd` tends to a fixed point of `J`. -/
theorem s31qe_hole_to_seam {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    (j : Fin m) {ζ : F.X.carrier} (hζ : ζ ∈ frontier (F.D j)) :
    ∃ p₀ : Xd.carrier, J p₀ = p₀ ∧ ∃ ℓ : Filter S, ℓ.NeBot ∧ Tendsto F.ι ℓ (𝓝 ζ) ∧ Tendsto ιd ℓ (𝓝 p₀) := by
  classical
  haveI : Nonempty S := inferInstance
  have hDc : ∀ i, IsCompact (F.D i) := fun i => s31eg_disc_compact (F.disc i)
  have hζD : ζ ∈ F.D j := by
    have := frontier_subset_closure hζ
    rwa [(hDc j).isClosed.closure_eq] at this
  have hζout : ζ ∉ range F.ι := by
    rw [F.range_ι]
    exact fun h => h (Or.inr (mem_iUnion.2 ⟨j, hζD⟩))
  -- the filter of approaches to `ζ` from the open surface
  have hne : (comap F.ι (𝓝 ζ)).NeBot := by
    rw [comap_neBot_iff]
    intro N hN
    let C : Set F.X.carrier := ↑F.P ∪ ⋃ i : {i // i ≠ j}, F.D i.1
    have hCc : IsClosed C :=
      F.P.finite_toSet.isClosed.union (isClosed_iUnion_of_finite fun i => (hDc i.1).isClosed)
    have hζC : ζ ∉ C := by
      rintro (h | h)
      · exact Set.disjoint_left.1 (F.disjoint_P j) hζD h
      · obtain ⟨i, hi⟩ := mem_iUnion.1 h
        exact Set.disjoint_left.1 (F.disjoint i.2) hi hζD
    have hN' : N ∩ Cᶜ ∈ 𝓝 ζ := inter_mem hN (hCc.isOpen_compl.mem_nhds hζC)
    obtain ⟨y, hyN, hyD⟩ : ∃ y ∈ N ∩ Cᶜ, y ∉ F.D j := by
      by_contra hcon
      push_neg at hcon
      exact hζ.2 (mem_interior_iff_mem_nhds.2 (mem_of_superset hN' hcon))
    have hy : y ∈ range F.ι := by
      rw [F.range_ι]
      rintro (h | h)
      · exact hyN.2 (Or.inl h)
      · obtain ⟨i, hi⟩ := mem_iUnion.1 h
        by_cases hij : i = j
        · subst hij; exact hyD hi
        · exact hyN.2 (Or.inr (mem_iUnion.2 ⟨⟨i, hij⟩, hi⟩))
    obtain ⟨a, rfl⟩ := hy
    exact ⟨a, hyN.1⟩
  set ℓ : Filter S := comap F.ι (𝓝 ζ) with hℓ
  haveI hmapne : (map ιd ℓ).NeBot := map_neBot
  obtain ⟨p, hp⟩ := exists_clusterPt_of_compactSpace (map ιd ℓ)
  -- the cluster point is not in the open half
  have hpR : p ∉ range ιd :=
    s31eg_cluster_missing F.ι ιd F.embedding.continuous hd.embedding hζout hp
  -- the refined filter
  have hℓ'ne : (ℓ ⊓ comap ιd (𝓝 p)).NeBot := by
    rw [inf_neBot_iff]
    intro s hs t ht
    obtain ⟨u, hu, hut⟩ := mem_comap.1 ht
    obtain ⟨x, hxu, hxs⟩ := (clusterPt_iff_nonempty.1 hp) hu (image_mem_map hs)
    obtain ⟨a, has, rfl⟩ := hxs
    exact ⟨a, has, hut hxu⟩
  have hF : Tendsto F.ι (ℓ ⊓ comap ιd (𝓝 p)) (𝓝 ζ) :=
    tendsto_inf_left (tendsto_comap)
  have hI : Tendsto ιd (ℓ ⊓ comap ιd (𝓝 p)) (𝓝 p) :=
    tendsto_inf_right (tendsto_comap)
  have hpne : Tendsto ιd (ℓ ⊓ comap ιd (𝓝 p)) (𝓝[≠] p) :=
    tendsto_nhdsWithin_iff.2 ⟨hI, Eventually.of_forall fun s h => hpR (h ▸ mem_range_self s)⟩
  -- the cluster point is not in the mirror half
  have hMo : IsOpen (range (J ∘ ιd)) := (J.isOpenMap.comp hd.embedding.isOpenMap).isOpen_range
  have hpM : p ∉ range (J ∘ ιd) := by
    intro h
    obtain ⟨a, ha⟩ := (hI.eventually (hMo.mem_nhds h)).exists
    exact Set.disjoint_left.1 hd.disjoint (mem_range_self a) ha
  refine ⟨p, ?_, ℓ ⊓ comap ιd (𝓝 p), hℓ'ne, hF, hI⟩
  rcases s31qr_outside_halves F hd hpR hpM with h | h
  · exact h
  · exfalso
    obtain ⟨e, he_mem, he_tend, hinj, hsep, hexh⟩ := s31pp_endpoints_exhaust F hd
    have hp' := h
    have hp'' : p ∈ (↑Pd : Set Xd.carrier) := h
    rw [hexh] at hp'
    rcases Finset.mem_union.1 hp' with h1 | h1
    · -- an endpoint of an original puncture: `F.ι` tends to that puncture
      obtain ⟨p₁, _, rfl⟩ := Finset.mem_image.1 h1
      obtain ⟨-, hret⟩ := s31pp_endpoint_half F hd (Finset.mem_coe.1 p₁.2) (he_tend p₁)
      have h2 : Tendsto F.ι (ℓ ⊓ comap ιd (𝓝 (e p₁))) (𝓝 p₁.1) := by
        refine (hret.comp hpne).congr fun s => ?_
        exact s31qr_halfReturn_image F hd s
      have h3 : ζ = p₁.1 := tendsto_nhds_unique hF h2
      exact Set.disjoint_left.1 (F.disjoint_P j) hζD (h3 ▸ Finset.mem_coe.1 p₁.2)
    · -- the mirror of an endpoint: the open half does not accumulate there
      obtain ⟨p₁, _, rfl⟩ := Finset.mem_image.1 h1
      have hJJ : ∀ x, J (J x) = x := hd.involution.1
      obtain ⟨hhalf, -⟩ := s31pp_endpoint_half F hd (Finset.mem_coe.1 p₁.2) (he_tend p₁)
      have hJt : Tendsto J (𝓝[≠] (J (e p₁))) (𝓝[≠] (e p₁)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have h' := (J.continuous.continuousAt (x := J (e p₁))).tendsto
          rw [hJJ] at h'
          exact h'.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with x hx h''
          apply hx
          have := congrArg J h''
          rw [hJJ] at this
          exact this
      have h3 : ∀ᶠ x in 𝓝[≠] (J (e p₁)), x ∈ range (J ∘ ιd) := by
        filter_upwards [hJt.eventually hhalf] with x hx
        exact (s31qr_mirror_membership F hd x).1 hx
      obtain ⟨a, ha⟩ := (hpne.eventually h3).exists
      exact Set.disjoint_left.1 hd.disjoint (mem_range_self a) ha



section Assemble
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}

/-- A point of the frontier of a hole is a limit of points of the open surface. -/
theorem s31qe_frontier_mem_closure (F : FiniteTypeStructure S g n m) (j : Fin m)
    {ζ : F.X.carrier} (hζ : ζ ∈ frontier (F.D j)) : ζ ∈ closure (range F.ι) := by
  classical
  have hDc : ∀ i, IsCompact (F.D i) := fun i => s31eg_disc_compact (F.disc i)
  have hζD : ζ ∈ F.D j := by
    have := frontier_subset_closure hζ
    rwa [(hDc j).isClosed.closure_eq] at this
  rw [mem_closure_iff_nhds]
  intro N hN
  let C : Set F.X.carrier := ↑F.P ∪ ⋃ i : {i // i ≠ j}, F.D i.1
  have hCc : IsClosed C :=
    F.P.finite_toSet.isClosed.union (isClosed_iUnion_of_finite fun i => (hDc i.1).isClosed)
  have hζC : ζ ∉ C := by
    rintro (h | h)
    · exact Set.disjoint_left.1 (F.disjoint_P j) hζD h
    · obtain ⟨i, hi⟩ := mem_iUnion.1 h
      exact Set.disjoint_left.1 (F.disjoint i.2) hi hζD
  have hN' : N ∩ Cᶜ ∈ 𝓝 ζ := inter_mem hN (hCc.isOpen_compl.mem_nhds hζC)
  obtain ⟨y, hyN, hyD⟩ : ∃ y ∈ N ∩ Cᶜ, y ∉ F.D j := by
    by_contra hcon
    push_neg at hcon
    exact hζ.2 (mem_interior_iff_mem_nhds.2 (mem_of_superset hN' hcon))
  have hy : y ∈ range F.ι := by
    rw [F.range_ι]
    rintro (h | h)
    · exact hyN.2 (Or.inl h)
    · obtain ⟨i, hi⟩ := mem_iUnion.1 h
      by_cases hij : i = j
      · subst hij; exact hyD hi
      · exact hyN.2 (Or.inr (mem_iUnion.2 ⟨⟨i, hij⟩, hi⟩))
  exact ⟨y, hyN.1, hy⟩

/-- The open surface accumulates at every chart point over the frontier of a hole. -/
theorem s31qe_chart_nebot (F : FiniteTypeStructure S g n m) {x : F.X.carrier} {j : Fin m} {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) (hf : (chartAt ℂ x).symm z ∈ frontier (F.D j)) :
    (𝓝[{w | w ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm w ∈ range F.ι}] z).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhds]
  intro N hN
  have h1 : (chartAt ℂ x).symm '' (N ∩ (chartAt ℂ x).target) ∈ 𝓝 ((chartAt ℂ x).symm z) :=
    (chartAt ℂ x).symm.image_mem_nhds (by simpa using hz)
      (inter_mem hN ((chartAt ℂ x).open_target.mem_nhds hz))
  obtain ⟨u, ⟨w, hw, rfl⟩, hu⟩ := mem_closure_iff_nhds.1 (s31qe_frontier_mem_closure F j hf) _ h1
  exact ⟨w, hw.1, hw.2, hu⟩

/-- Transfer of a boundary limit between two charts, through the tensor law. -/
theorem s31qe_limit_transfer {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] {q : M → ℂ → ℂ} (hq : IsDiffFamily 2 0 q) (U : Set M) (x y : M) {z : ℂ}
    (hz : z ∈ (chartAt ℂ y).target) (hs : (chartAt ℂ y).symm z ∈ (chartAt ℂ x).source) {b : ℂ}
    (hb : Tendsto (q x) (𝓝[{w | w ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm w ∈ U}]
      (chartTransition x y z)) (𝓝 b)) :
    Tendsto (q y) (𝓝[{w | w ∈ (chartAt ℂ y).target ∧ (chartAt ℂ y).symm w ∈ U}] z)
      (𝓝 (b * deriv (chartTransition x y) z ^ 2)) := by
  have hOo : IsOpen ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source) :=
    (chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ x).open_source
  have hzO : z ∈ (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source := ⟨hz, hs⟩
  have hτd : DifferentiableOn ℂ (chartTransition x y)
      ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source) :=
    fun w hw => (s23_transition_differentiableAt x y hw.1 hw.2).differentiableWithinAt
  have hτc : ContinuousAt (chartTransition x y) z :=
    (hτd.differentiableAt (hOo.mem_nhds hzO)).continuousAt
  have hdτc : ContinuousAt (deriv (chartTransition x y)) z :=
    ((hτd.deriv hOo).differentiableAt (hOo.mem_nhds hzO)).continuousAt
  have hmap : Tendsto (chartTransition x y)
      (𝓝[{w | w ∈ (chartAt ℂ y).target ∧ (chartAt ℂ y).symm w ∈ U}] z)
      (𝓝[{w | w ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm w ∈ U}] (chartTransition x y z)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hτc.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [nhdsWithin_le_nhds (hOo.mem_nhds hzO), self_mem_nhdsWithin] with w hwO hwA
    obtain ⟨hxt, _, hpoint⟩ := s23_transition_mem hwO.1 hwO.2
    refine ⟨hxt, ?_⟩
    rw [hpoint]
    exact hwA.2
  have h1 : Tendsto (fun w => q x (chartTransition x y w) * deriv (chartTransition x y) w ^ 2)
      (𝓝[{w | w ∈ (chartAt ℂ y).target ∧ (chartAt ℂ y).symm w ∈ U}] z)
      (𝓝 (b * deriv (chartTransition x y) z ^ 2)) :=
    (hb.comp hmap).mul ((hdτc.pow 2).tendsto.mono_left nhdsWithin_le_nhds)
  refine h1.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (hOo.mem_nhds hzO)] with w hwO
  have hlaw := hq.2 x y w hwO.1 hwO.2
  rw [zpow_zero, mul_one, zpow_two] at hlaw
  rw [hlaw]
  ring

/-- The assembly of the boundary extension from a differential family on the open surface having
boundary limits along every hole frontier, with the reality of limits along `C¹` boundary curves. -/
theorem s31qe_assemble (F : FiniteTypeStructure S g n m) {q0 : F.X.carrier → ℂ → ℂ}
    (hq0 : IsDiffFamily 2 0 q0)
    (hhol : ∀ x : F.X.carrier, DifferentiableOn ℂ (q0 x)
      ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' range F.ι))
    (hlim : ∀ (x : F.X.carrier) (j : Fin m) (z : ℂ), z ∈ (chartAt ℂ x).target →
      (chartAt ℂ x).symm z ∈ frontier (F.D j) →
      ∃ b : ℂ, Tendsto (q0 x)
        (𝓝[{w | w ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm w ∈ range F.ι}] z) (𝓝 b))
    (hreal : ∀ (x : F.X.carrier) (j : Fin m) (c : ℝ → ℂ) (a b : ℝ), ContDiffOn ℝ 1 c (Icc a b) →
      c '' Icc a b ⊆ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' frontier (F.D j) →
      ∀ t ∈ Ioo a b, ∀ b₀ : ℂ, Tendsto (q0 x)
        (𝓝[{w | w ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm w ∈ range F.ι}] (c t)) (𝓝 b₀) →
        (b₀ * deriv c t ^ 2).im = 0) :
    ∃ q : F.X.carrier → ℂ → ℂ, IsDiffFamily 2 0 q ∧
      (∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ range F.ι → q x z = q0 x z) ∧
      (∀ (x : F.X.carrier) (j : Fin m), ∀ z ∈ (chartAt ℂ x).target,
        (chartAt ℂ x).symm z ∈ interior (F.D j) → q x z = 0) ∧
      (∀ (x : F.X.carrier), ∀ p ∈ F.P, p ∈ (chartAt ℂ x).source → q x (chartAt ℂ x p) = 0) ∧
      (∀ (x : F.X.carrier) (j : Fin m),
        ContinuousOn (q x) ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (range F.ι ∪ frontier (F.D j)))) ∧
      (∀ (x : F.X.carrier) (j : Fin m) (c : ℝ → ℂ) (a b : ℝ), ContDiffOn ℝ 1 c (Icc a b) →
        c '' Icc a b ⊆ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' frontier (F.D j) →
        ∀ t ∈ Ioo a b, (q x (c t) * deriv c t ^ 2).im = 0) := by
  classical
  have hD : ∀ i, IsClosed (F.D i) := fun i => (s31eg_disc_compact (F.disc i)).isClosed
  -- the pieces of the surface
  have hfr_sub : ∀ i, frontier (F.D i) ⊆ F.D i := fun i => by
    have := frontier_subset_closure (s := F.D i)
    rwa [(hD i).closure_eq] at this
  have hD_out : ∀ i {u : F.X.carrier}, u ∈ F.D i → u ∉ range F.ι := by
    intro i u hu hr
    rw [F.range_ι] at hr
    exact hr (Or.inr (mem_iUnion.2 ⟨i, hu⟩))
  have hP_out : ∀ {u : F.X.carrier}, u ∈ F.P → u ∉ range F.ι := by
    intro u hu hr
    rw [F.range_ι] at hr
    exact hr (Or.inl hu)
  have hcover : ∀ u : F.X.carrier, u ∈ range F.ι ∨ u ∈ (↑F.P : Set F.X.carrier) ∨
      (∃ j, u ∈ frontier (F.D j)) ∨ (∃ j, u ∈ interior (F.D j)) := by
    intro u
    by_cases hr : u ∈ range F.ι
    · exact Or.inl hr
    · rw [F.range_ι, mem_compl_iff, not_not] at hr
      rcases hr with hP | hD'
      · exact Or.inr (Or.inl hP)
      · obtain ⟨j, hj⟩ := mem_iUnion.1 hD'
        by_cases hi : u ∈ interior (F.D j)
        · exact Or.inr (Or.inr (Or.inr ⟨j, hi⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨j, subset_closure hj, hi⟩))
  have hnotfr_of_interior : ∀ {u : F.X.carrier} {i : Fin m}, u ∈ interior (F.D i) →
      ∀ j, u ∉ frontier (F.D j) := by
    intro u i hu j hf
    by_cases hij : i = j
    · subst hij; exact hf.2 hu
    · exact Set.disjoint_left.1 (F.disjoint hij) (interior_subset hu) (hfr_sub j hf)
  have hnotfr_of_P : ∀ {u : F.X.carrier}, u ∈ (↑F.P : Set F.X.carrier) → ∀ j, u ∉ frontier (F.D j) :=
    fun hu j hf => Set.disjoint_left.1 (F.disjoint_P j) (hfr_sub j hf) hu
  have hfr_out : ∀ {u : F.X.carrier} {j : Fin m}, u ∈ frontier (F.D j) → u ∉ range F.ι :=
    fun hf => hD_out _ (hfr_sub _ hf)
  let A : F.X.carrier → Set ℂ := fun x =>
    {w | w ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm w ∈ range F.ι}
  let q : F.X.carrier → ℂ → ℂ := fun x z =>
    if z ∈ A x then q0 x z
    else if z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm z ∈ ⋃ j, frontier (F.D j) then
      limUnder (𝓝[A x] z) (q0 x)
    else 0
  have hqA : ∀ x z, z ∈ A x → q x z = q0 x z := fun x z h => by
    simp only [q, h, if_true]
  have hqF : ∀ (x : F.X.carrier) (j : Fin m) (z : ℂ), z ∈ (chartAt ℂ x).target →
      (chartAt ℂ x).symm z ∈ frontier (F.D j) → q x z = limUnder (𝓝[A x] z) (q0 x) := by
    intro x j z hz hf
    have hnot : z ∉ A x := fun h => hfr_out hf h.2
    have hin : z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm z ∈ ⋃ j, frontier (F.D j) :=
      ⟨hz, mem_iUnion.2 ⟨j, hf⟩⟩
    change (if z ∈ A x then q0 x z else if z ∈ (chartAt ℂ x).target ∧
      (chartAt ℂ x).symm z ∈ ⋃ j, frontier (F.D j) then limUnder (𝓝[A x] z) (q0 x) else 0) = _
    rw [if_neg hnot, if_pos hin]
  have hqz1 : ∀ x z, z ∉ (chartAt ℂ x).target → q x z = 0 := fun x z hz => by
    have h1 : z ∉ A x := fun h => hz h.1
    have h2 : ¬ (z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm z ∈ ⋃ j, frontier (F.D j)) :=
      fun h => hz h.1
    simp only [q, h1, h2, if_false]
  have hqz2 : ∀ (x : F.X.carrier) (z : ℂ), z ∈ (chartAt ℂ x).target →
      (chartAt ℂ x).symm z ∉ range F.ι → (∀ j, (chartAt ℂ x).symm z ∉ frontier (F.D j)) →
      q x z = 0 := by
    intro x z hz hr hf
    have h1 : z ∉ A x := fun h => hr h.2
    have h2 : ¬ (z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm z ∈ ⋃ j, frontier (F.D j)) := by
      rintro ⟨-, h⟩
      obtain ⟨j, hj⟩ := mem_iUnion.1 h
      exact hf j hj
    simp only [q, h1, h2, if_false]
  have hlimT : ∀ (x : F.X.carrier) (j : Fin m) (z : ℂ), z ∈ (chartAt ℂ x).target →
      (chartAt ℂ x).symm z ∈ frontier (F.D j) → Tendsto (q0 x) (𝓝[A x] z) (𝓝 (q x z)) := by
    intro x j z hz hf
    obtain ⟨b, hb⟩ := hlim x j z hz hf
    haveI := s31qe_chart_nebot F hz hf
    rw [hqF x j z hz hf]
    exact tendsto_nhds_limUnder ⟨b, hb⟩
  have hAo : ∀ x, IsOpen (A x) := fun x =>
    (chartAt ℂ x).isOpen_inter_preimage_symm F.embedding.isOpenMap.isOpen_range
  refine ⟨q, ⟨fun x z hz => hqz1 x z hz, fun x y z hz hs => ?_⟩,
    fun x z h1 h2 => hqA x z ⟨h1, h2⟩, ?_, ?_, ?_, ?_⟩
  · -- the tensor law
    rw [zpow_zero, mul_one, zpow_two]
    obtain ⟨hxt, _, hpoint⟩ := s23_transition_mem hz hs
    rcases hcover ((chartAt ℂ y).symm z) with hr | hP | ⟨j, hf⟩ | ⟨j, hi⟩
    · rw [hqA y z ⟨hz, hr⟩, hqA x _ ⟨hxt, by rw [hpoint]; exact hr⟩]
      have hlaw := hq0.2 x y z hz hs
      rw [zpow_zero, mul_one, zpow_two] at hlaw
      exact hlaw
    · rw [hqz2 y z hz (hP_out hP) (hnotfr_of_P hP),
        hqz2 x _ hxt (by rw [hpoint]; exact hP_out hP) (by rw [hpoint]; exact hnotfr_of_P hP),
        zero_mul]
    · have hfx : (chartAt ℂ x).symm (chartTransition x y z) ∈ frontier (F.D j) := by
        rw [hpoint]; exact hf
      obtain ⟨b, hb⟩ := hlim x j _ hxt hfx
      have hT := s31qe_limit_transfer hq0 (range F.ι) x y hz hs hb
      haveI := s31qe_chart_nebot F hz hf
      haveI := s31qe_chart_nebot F hxt hfx
      rw [hqF y j z hz hf, hqF x j _ hxt hfx, hT.limUnder_eq, hb.limUnder_eq]
      ring
    · rw [hqz2 y z hz (hD_out j (interior_subset hi)) (hnotfr_of_interior hi),
        hqz2 x _ hxt (by rw [hpoint]; exact hD_out j (interior_subset hi))
          (by rw [hpoint]; exact hnotfr_of_interior hi), zero_mul]
  · intro x j z hz hi
    exact hqz2 x z hz (hD_out j (interior_subset hi)) (hnotfr_of_interior hi)
  · intro x p hp hs
    have hzt : chartAt ℂ x p ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hs
    have hpp : (chartAt ℂ x).symm (chartAt ℂ x p) = p := (chartAt ℂ x).left_inv hs
    exact hqz2 x _ hzt (by rw [hpp]; exact hP_out (Finset.mem_coe.2 hp))
      (by rw [hpp]; exact hnotfr_of_P (Finset.mem_coe.2 hp))
  · intro x j z hz
    rcases hz.2 with hr | hf
    · have hzA : z ∈ A x := ⟨hz.1, hr⟩
      have hd : DifferentiableAt ℂ (q0 x) z := (hhol x).differentiableAt ((hAo x).mem_nhds hzA)
      have hc : ContinuousAt (q x) z := by
        refine hd.continuousAt.congr ?_
        filter_upwards [(hAo x).mem_nhds hzA] with w hw using (hqA x w hw).symm
      exact hc.continuousWithinAt
    · rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨δ, hδ, hδ'⟩ := (Metric.tendsto_nhdsWithin_nhds.1 (hlimT x j z hz.1 hf)) (ε / 2)
        (half_pos hε)
      refine ⟨δ, hδ, fun {y} hy hyd => ?_⟩
      rcases hy.2 with hyr | hyf
      · rw [hqA x y ⟨hy.1, hyr⟩]
        have := hδ' (x := y) ⟨hy.1, hyr⟩ hyd
        linarith
      · haveI hnb : (𝓝[A x] y).NeBot := s31qe_chart_nebot F hy.1 hyf
        have hlimy := hlimT x j y hy.1 hyf
        have hev : ∀ᶠ w in 𝓝[A x] y, dist (q0 x w) (q x z) ≤ ε / 2 := by
          filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball.2 hyd)),
            self_mem_nhdsWithin] with w hw hwA
          exact (hδ' hwA (mem_ball.1 hw)).le
        have := le_of_tendsto (hlimy.dist tendsto_const_nhds) hev
        linarith
  · intro x j c a b hc hsub t ht
    have hz := hsub (mem_image_of_mem c (Ioo_subset_Icc_self ht))
    exact hreal x j c a b hc hsub t ht (q x (c t)) (hlimT x j (c t) hz.1 hz.2)

end Assemble



section Collar
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}

/-- Along a filter on which `ιd` tends to the centre `p₀` of a collar, the chart images of `F.ι` tend to `κ 0`. -/
theorem s31qe_collar_tendsto (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
    (hd : IsSchottkyDouble F Xd J ιd Pd) {p₀ : Xd.carrier} {wc : OpenPartialHomeomorph Xd.carrier ℂ}
    (hp₀ : p₀ ∈ wc.source) (hwc0 : wc p₀ = 0)
    (hup : ∀ p ∈ wc.source, (0 < (wc p).im ↔ p ∈ range ιd))
    {x : F.X.carrier} {r' : ℝ} (hr'0 : 0 < r') {κ : ℂ → ℂ}
    (hcont : ContinuousOn κ {z : ℂ | ‖z‖ < r' ∧ 0 ≤ z.im})
    (hlink : ∀ z : ℂ, ‖z‖ < r' → 0 < z.im → ∃ s : S, ιd s = wc.symm z ∧
      F.ι s ∈ (chartAt ℂ x).source ∧ κ z = chartAt ℂ x (F.ι s))
    {ℓ : Filter S} [ℓ.NeBot] (hℓ : Tendsto ιd ℓ (𝓝 p₀)) :
    (∀ᶠ s in ℓ, F.ι s ∈ (chartAt ℂ x).source) ∧
      Tendsto (fun s => chartAt ℂ x (F.ι s)) ℓ (𝓝 (κ 0)) := by
  have hinj : Function.Injective ιd := hd.embedding.injective
  have hw : Tendsto (fun s => wc (ιd s)) ℓ (𝓝 0) := by
    have := (wc.continuousAt hp₀).tendsto.comp hℓ
    rwa [hwc0] at this
  have hsrc : ∀ᶠ s in ℓ, ιd s ∈ wc.source := hℓ.eventually (wc.open_source.mem_nhds hp₀)
  have hnorm : ∀ᶠ s in ℓ, ‖wc (ιd s)‖ < r' :=
    hw.eventually (ball_mem_nhds (0 : ℂ) hr'0) |>.mono fun s hs => by simpa using hs
  have hgood : ∀ᶠ s in ℓ, ιd s ∈ wc.source ∧ ‖wc (ιd s)‖ < r' ∧ 0 < (wc (ιd s)).im ∧
      F.ι s ∈ (chartAt ℂ x).source ∧ κ (wc (ιd s)) = chartAt ℂ x (F.ι s) := by
    filter_upwards [hsrc, hnorm] with s hs1 hs2
    have him : 0 < (wc (ιd s)).im := (hup _ hs1).2 (mem_range_self s)
    obtain ⟨s', h1, h2, h3⟩ := hlink _ hs2 him
    rw [wc.left_inv hs1] at h1
    have : s' = s := hinj h1
    subst this
    exact ⟨hs1, hs2, him, h2, h3⟩
  refine ⟨hgood.mono fun s hs => hs.2.2.2.1, ?_⟩
  have hk : Tendsto (fun s => κ (wc (ιd s))) ℓ (𝓝 (κ 0)) := by
    have hc0 : ContinuousWithinAt κ {z : ℂ | ‖z‖ < r' ∧ 0 ≤ z.im} 0 :=
      hcont 0 ⟨by simpa using hr'0, le_refl _⟩
    refine hc0.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hw, ?_⟩)
    filter_upwards [hgood] with s hs
    exact ⟨hs.2.1, hs.2.2.1.le⟩
  refine hk.congr' ?_
  filter_upwards [hgood] with s hs
  exact hs.2.2.2.2

end Collar


section Pdata

/-- The coefficient of `Q` in the coordinate `wc` is continuous at the centre, and the chart `a = E p₀` contains the image of a small disc. -/
theorem s31qe_P_data {Xd : ClosedRS.{u}} {Y : ClosedRS.{u}} (E : Xd.carrier ≃ₜ Y.carrier)
    (hE : IsBiholomorphic (E : Xd.carrier → Y.carrier)) {Q : Y.carrier → ℂ → ℂ}
    {p₀ : Xd.carrier} {wc : OpenPartialHomeomorph Xd.carrier ℂ} {r : ℝ} (hr : 0 < r)
    (hp₀s : p₀ ∈ wc.source) (hwc0 : wc p₀ = 0) (hwt : wc.target = ball 0 r)
    (hmds : ∀ z ∈ wc.target, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) wc.symm z)
    (hQa : DifferentiableAt ℂ (Q (E p₀)) (chartAt ℂ (E p₀) (E p₀))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ (∀ w : ℂ, ‖w‖ < ρ → E (wc.symm w) ∈ (chartAt ℂ (E p₀)).source) ∧
      ContinuousAt (fun w : ℂ => Q (E p₀) (chartAt ℂ (E p₀) (E (wc.symm w))) *
        deriv (fun v : ℂ => chartAt ℂ (E p₀) (E (wc.symm v))) w ^ 2) 0 := by
  set a := E p₀ with ha
  let φ : ℂ → ℂ := fun v => chartAt ℂ a (E (wc.symm v))
  let O : Set ℂ := ball (0 : ℂ) r ∩ (fun v => E (wc.symm v)) ⁻¹' (chartAt ℂ a).source
  have hcE : ContinuousOn (fun v => E (wc.symm v)) (ball (0 : ℂ) r) := by
    rw [← hwt]
    exact E.continuous.comp_continuousOn wc.continuousOn_symm
  have hOo : IsOpen O := hcE.isOpen_inter_preimage isOpen_ball (chartAt ℂ a).open_source
  have hw0 : wc.symm 0 = p₀ := by
    rw [← hwc0]
    exact wc.left_inv hp₀s
  have h0O : (0 : ℂ) ∈ O :=
    ⟨mem_ball_self hr, by simp only [mem_preimage, hw0]; exact mem_chart_source ℂ a⟩
  have hφd : DifferentiableOn ℂ φ O := by
    intro v hv
    have hvt : v ∈ wc.target := by rw [hwt]; exact hv.1
    have hm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun v => E (wc.symm v)) v :=
      (hE.1 _).comp v (hmds v hvt)
    exact (((mdifferentiableAt_atlas (chart_mem_atlas ℂ a) hv.2).comp v hm).differentiableAt).differentiableWithinAt
  have hdd : DifferentiableOn ℂ (deriv φ) O := hφd.deriv hOo
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.1 hOo 0 h0O
  refine ⟨min ρ₀ r, lt_min hρ₀ hr, min_le_right _ _, fun w hw => ?_, ?_⟩
  · have : w ∈ O := hball (mem_ball_zero_iff.2 (lt_of_lt_of_le hw (min_le_left _ _)))
    exact this.2
  · have hφc : ContinuousAt φ 0 := (hφd.differentiableAt (hOo.mem_nhds h0O)).continuousAt
    have hφ0 : φ 0 = chartAt ℂ a a := by
      show chartAt ℂ a (E (wc.symm 0)) = _
      rw [hw0]
    have hQc : ContinuousAt (Q a) (φ 0) := by rw [hφ0]; exact hQa.continuousAt
    exact (hQc.comp hφc).mul (((hdd.differentiableAt (hOo.mem_nhds h0O)).continuousAt).pow 2)

end Pdata

section CollarData
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}

/-- The collar data at a point `ζ` of the frontier of the hole `D j`, in the witness chart `xF` of `D j`: a collar map `κ`
with `κ 0 = chart ζ`, a nonzero boundary limit `L` of `κ'`, a continuous function `P` (the pull-back of `Q` to the collar
coordinate) with `q0 (κ w) κ'(w)² = P w` near `0`, real at `0`, and the open surface fills a neighbourhood of `chart ζ`
inside `κ(upper half disc)`. -/
theorem s31qe_collar_data [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {gd nd : ℕ} (Fd : FiniteTypeStructure (puncturedOpens Pd) gd nd 0)
    (E : Xd.carrier ≃ₜ Fd.X.carrier) (hE : IsBiholomorphic (E : Xd.carrier → Fd.X.carrier))
    (hP : ∀ p : Xd.carrier, p ∈ Pd ↔ E p ∈ Fd.P)
    {Q : Fd.X.carrier → ℂ → ℂ} (hQ : IsAdmissibleQD Fd Q)
    (hfix : s31qr_transportOn univ (fun y : Fd.X.carrier => E (J (E.symm y)))
      Complex.conjCLE.toLinearMap Q = Q)
    {j : Fin m} {xF : F.X.carrier} (hDs : F.D j ⊆ (chartAt ℂ xF).source) {Jd : Set ℂ}
    (hJd : IsJordanDomain Jd) (hbd : Bornology.IsBounded Jd) (hclt : closure Jd ⊆ (chartAt ℂ xF).target)
    (hcl : chartAt ℂ xF '' F.D j = closure Jd)
    {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hc' : ∀ t, deriv c t ≠ 0) (hper : ∀ t, c (t + 1) = c t)
    (hinj : InjOn c (Ico 0 1)) (hcf : c '' Ico 0 1 = frontier Jd)
    {ζ : F.X.carrier} (hζ : ζ ∈ frontier (F.D j)) :
    ∃ (r' : ℝ) (κ : ℂ → ℂ) (L P0 : ℂ), 0 < r' ∧
      DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r' ∧ 0 < z.im} ∧
      ContinuousOn κ {z : ℂ | ‖z‖ < r' ∧ 0 ≤ z.im} ∧
      InjOn κ {z : ℂ | ‖z‖ < r' ∧ 0 ≤ z.im} ∧
      MapsTo κ {z : ℂ | ‖z‖ < r' ∧ 0 < z.im} (closure Jd)ᶜ ∧
      MapsTo κ {z : ℂ | ‖z‖ < r' ∧ z.im = 0} (frontier Jd) ∧
      (∃ V : Set ℂ, IsOpen V ∧ κ '' {z : ℂ | ‖z‖ < r' ∧ 0 ≤ z.im} = V ∩ Jdᶜ) ∧
      κ ((0 : ℝ) : ℂ) = chartAt ℂ xF ζ ∧ L ≠ 0 ∧
      Tendsto (deriv κ) (𝓝[{z : ℂ | ‖z‖ < r' ∧ 0 < z.im}] ((0 : ℝ) : ℂ)) (𝓝 L) ∧
      P0.im = 0 ∧
      (∃ (P : ℂ → ℂ) (ρ : ℝ), 0 < ρ ∧ ContinuousAt P ((0 : ℝ) : ℂ) ∧ P ((0 : ℝ) : ℂ) = P0 ∧
        ∀ w : ℂ, ‖w‖ < r' → 0 < w.im → ‖w - ((0 : ℝ) : ℂ)‖ < ρ →
          s31qr_transportOn (range F.ι)
            (fun y : F.X.carrier => E (ιd ((F.embedding.toOpenPartialHomeomorph F.ι).symm y)))
            (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q xF (κ w) * deriv κ w ^ 2 = P w) ∧
      (∃ N ∈ 𝓝 (chartAt ℂ xF ζ), ∀ z ∈ N, z ∈ (chartAt ℂ xF).target →
        (chartAt ℂ xF).symm z ∈ range F.ι → z ∈ κ '' {z : ℂ | ‖z‖ < r' ∧ 0 < z.im}) := by
  classical
  haveI : Nonempty S := inferInstance
  have hDc : ∀ i, IsCompact (F.D i) := fun i => s31eg_disc_compact (F.disc i)
  have hDcl : ∀ i, IsClosed (F.D i) := fun i => (hDc i).isClosed
  have hζD : ζ ∈ F.D j := by
    have := frontier_subset_closure hζ
    rwa [(hDcl j).closure_eq] at this
  have hfr_sub : ∀ i, frontier (F.D i) ⊆ F.D i := fun i => (hDcl i).frontier_subset
  -- an end approaching the seam
  obtain ⟨p₀, hp₀J, ℓ, hℓne, hℓF, hℓι⟩ := s31qe_hole_to_seam F hm hd j hζ
  haveI := hℓne
  obtain ⟨j', wc, r, hr, hp₀s, hwc0, hwt, hmd, hmds, hJw, hup, hrealw, hcol⟩ :=
    s31qi_collar_from_hd F hm hd hp₀J
  -- the collar belongs to the hole `j`
  have hjj : j' = j := by
    obtain ⟨xF', hDs', Jd', hJd', hbd', hclt', hcl', c', hc₁, hc₁', hper', hinj', hcf'⟩ := F.disc j'
    obtain ⟨r1, hr10, hr1r, κ1, hκd1, hκc1, hκi1, hκu1, hκr1, hκV1, hlink1⟩ :=
      hcol xF' Jd' hDs' hJd' hbd' hcl' hclt'
    obtain ⟨hsrc, hten⟩ := s31qe_collar_tendsto F hd hp₀s hwc0 hup hr10 hκc1 hlink1 hℓι
    have hy₀F : κ1 0 ∈ frontier Jd' := hκr1 ⟨by simpa using hr10, by simp⟩
    obtain ⟨hyt, hyf⟩ := s31qi_hole_frontier_back hDs' hJd' hbd' hcl' (hDc j') hclt' hy₀F
    have h1 : Tendsto (fun s => (chartAt ℂ xF').symm (chartAt ℂ xF' (F.ι s))) ℓ
        (𝓝 ((chartAt ℂ xF').symm (κ1 0))) :=
      ((chartAt ℂ xF').continuousAt_symm hyt).tendsto.comp hten
    have h2 : Tendsto F.ι ℓ (𝓝 ((chartAt ℂ xF').symm (κ1 0))) := by
      refine h1.congr' ?_
      filter_upwards [hsrc] with s hs
      exact (chartAt ℂ xF').left_inv hs
    have h3 : ζ = (chartAt ℂ xF').symm (κ1 0) := tendsto_nhds_unique hℓF h2
    by_contra hne
    exact Set.disjoint_left.1 (F.disjoint hne) (hfr_sub j' hyf) (h3 ▸ hζD)
  subst hjj
  obtain ⟨r', hr'0, hr'r, κ, hκd, hκc, hκi, hκu, hκr, hκV, hlink⟩ :=
    hcol xF Jd hDs hJd hbd hcl hclt
  obtain ⟨-, hten⟩ := s31qe_collar_tendsto F hd hp₀s hwc0 hup hr'0 hκc hlink hℓι
  have hζs : ζ ∈ (chartAt ℂ xF).source := hDs hζD
  have hten' : Tendsto (fun s => chartAt ℂ xF (F.ι s)) ℓ (𝓝 (chartAt ℂ xF ζ)) :=
    ((chartAt ℂ xF).continuousAt hζs).tendsto.comp hℓF
  have hκ0 : κ 0 = chartAt ℂ xF ζ := tendsto_nhds_unique hten hten'
  have hκ0' : κ ((0 : ℝ) : ℂ) = chartAt ℂ xF ζ := by rw [Complex.ofReal_zero]; exact hκ0
  -- the boundary jet
  obtain ⟨L, hL0, hL⟩ := s31qd_boundary_jet hJd hbd hc hc' hper hinj hcf hr'0 hκd hκc hκi hκu hκr hκV
    0 (by simpa using hr'0)
  -- the coefficient in the collar coordinate
  have hpd : p₀ ∉ Pd := by
    have h : p₀ ∈ {x | J x = x} := hp₀J
    rw [hd.fixed_curves] at h
    exact h.2
  have hRange : range Fd.ι = (↑Fd.P : Set Fd.X.carrier)ᶜ := by simpa using Fd.range_ι
  have hy₁ : E p₀ ∈ range Fd.ι := by
    rw [hRange]
    exact fun h => hpd ((hP p₀).2 (Finset.mem_coe.1 h))
  have hQa : DifferentiableAt ℂ (Q (E p₀)) (chartAt ℂ (E p₀) (E p₀)) := by
    have hO : IsOpen ((chartAt ℂ (E p₀)).target ∩ (chartAt ℂ (E p₀)).symm ⁻¹' range Fd.ι) :=
      (chartAt ℂ (E p₀)).isOpen_inter_preimage_symm Fd.embedding.isOpenMap.isOpen_range
    refine (hQ.2.1 (E p₀)).differentiableAt (hO.mem_nhds ⟨(chartAt ℂ (E p₀)).map_source
      (mem_chart_source ℂ (E p₀)), ?_⟩)
    change (chartAt ℂ (E p₀)).symm (chartAt ℂ (E p₀) (E p₀)) ∈ range Fd.ι
    rw [(chartAt ℂ (E p₀)).left_inv (mem_chart_source ℂ (E p₀))]
    exact hy₁
  obtain ⟨ρ, hρ0, hρr, hρs, hPc⟩ := s31qe_P_data E hE hr hp₀s hwc0 hwt hmds hQa
  have hw0 : wc.symm 0 = p₀ := by
    rw [← hwc0]
    exact wc.left_inv hp₀s
  have hreal0 := s31qe_center_real hd.involution E hE hQ.1 hfix hp₀J hr hp₀s hwc0 hwt hmds hJw
  refine ⟨r', κ, L, Q (E p₀) (chartAt ℂ (E p₀) (E p₀)) *
      deriv (fun v : ℂ => chartAt ℂ (E p₀) (E (wc.symm v))) 0 ^ 2, hr'0, hκd, hκc, hκi, hκu, hκr, hκV,
    hκ0', hL0, hL, hreal0, ?_, ?_⟩
  · refine ⟨fun w : ℂ => Q (E p₀) (chartAt ℂ (E p₀) (E (wc.symm w))) *
      deriv (fun v : ℂ => chartAt ℂ (E p₀) (E (wc.symm v))) w ^ 2, ρ, hρ0, ?_, ?_, ?_⟩
    · simpa using hPc
    · simp only [Complex.ofReal_zero, hw0]
    · intro w hw hwi hwρ
      have hwρ' : ‖w‖ < ρ := by simpa using hwρ
      exact s31qe_pullback_rel F hd E hE hQ.1 hwt hmds hr'r hκd hlink (E p₀) hρs hw hwi hwρ'
  · obtain ⟨V, hVo, hVeq⟩ := hκV
    have h0V : κ 0 ∈ V ∩ Jdᶜ := by
      rw [← hVeq]
      exact mem_image_of_mem κ ⟨by simpa using hr'0, le_refl _⟩
    refine ⟨V, by rw [← hκ0]; exact hVo.mem_nhds h0V.1, fun z hzV hzt hzr => ?_⟩
    have hzcl : z ∉ closure Jd := by
      intro hz
      rw [← hcl] at hz
      obtain ⟨d, hdD, rfl⟩ := hz
      have hsymm : (chartAt ℂ xF).symm (chartAt ℂ xF d) = d := (chartAt ℂ xF).left_inv (hDs hdD)
      rw [hsymm] at hzr
      rw [F.range_ι] at hzr
      exact hzr (Or.inr (mem_iUnion.2 ⟨_, hdD⟩))
    have hzJ : z ∈ V ∩ Jdᶜ := ⟨hzV, fun h => hzcl (subset_closure h)⟩
    rw [← hVeq] at hzJ
    obtain ⟨w, hw, rfl⟩ := hzJ
    refine ⟨w, ⟨hw.1, lt_of_le_of_ne hw.2 ?_⟩, rfl⟩
    intro him
    exact hzcl (frontier_subset_closure (hκr ⟨hw.1, him.symm⟩))

end CollarData

section Glue
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}

/-- The transported family `q0` on the open surface is a differential family, holomorphic there. -/
theorem s31qe_q0_props [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [Nonempty S]
    (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {gd nd : ℕ} (Fd : FiniteTypeStructure (puncturedOpens Pd) gd nd 0)
    (E : Xd.carrier ≃ₜ Fd.X.carrier) (hE : IsBiholomorphic (E : Xd.carrier → Fd.X.carrier))
    (hP : ∀ p : Xd.carrier, p ∈ Pd ↔ E p ∈ Fd.P)
    {Q : Fd.X.carrier → ℂ → ℂ} (hQ : IsAdmissibleQD Fd Q) :
    IsDiffFamily 2 0 (s31qr_transportOn (range F.ι)
        (fun y : F.X.carrier => E (ιd ((F.embedding.toOpenPartialHomeomorph F.ι).symm y)))
        (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q) ∧
      ∀ x : F.X.carrier, DifferentiableOn ℂ (s31qr_transportOn (range F.ι)
        (fun y : F.X.carrier => E (ιd ((F.embedding.toOpenPartialHomeomorph F.ι).symm y)))
        (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q x)
        ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' range F.ι) := by
  classical
  set G : F.X.carrier → Fd.X.carrier :=
    fun y => E (ιd ((F.embedding.toOpenPartialHomeomorph F.ι).symm y)) with hG
  have hGh : ∀ p ∈ range F.ι, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) G p := fun p hp =>
    (hE.1 _).comp p ((hd.holomorphic _).comp p
      (s31qr_open_embedding_inverse F.embedding F.holomorphic hp))
  have hGι : ∀ s : S, G (F.ι s) = E (ιd s) := fun s => by
    simp only [hG]
    rw [F.embedding.toOpenPartialHomeomorph_left_inv F.ι]
  refine ⟨s31qr_holomorphic_transport_family (range F.ι) G hGh Q, fun x => ?_⟩
  have hRange : range Fd.ι = (↑Fd.P : Set Fd.X.carrier)ᶜ := by simpa using Fd.range_ι
  have himage : MapsTo G (range F.ι) (range Fd.ι) := by
    rintro _ ⟨s, rfl⟩
    rw [hGι, hRange]
    intro h
    exact (s31qi_Pd_off_halves F hm hd _ ((hP _).2 h)).1 (mem_range_self s)
  exact s31qr_transport_holomorphic F.embedding.isOpenMap.isOpen_range
    Fd.embedding.isOpenMap.isOpen_range hGh himage hQ.1 hQ.2.1 x

/-- Boundary value at a frontier point of a hole: the limit exists and is real along every `C¹` boundary curve through
the point. -/
theorem s31qe_boundary_value [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [Nonempty S]
    (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {gd nd : ℕ} (Fd : FiniteTypeStructure (puncturedOpens Pd) gd nd 0)
    (E : Xd.carrier ≃ₜ Fd.X.carrier) (hE : IsBiholomorphic (E : Xd.carrier → Fd.X.carrier))
    (hP : ∀ p : Xd.carrier, p ∈ Pd ↔ E p ∈ Fd.P)
    {Q : Fd.X.carrier → ℂ → ℂ} (hQ : IsAdmissibleQD Fd Q)
    (hfix : s31qr_transportOn univ (fun y : Fd.X.carrier => E (J (E.symm y)))
      Complex.conjCLE.toLinearMap Q = Q)
    (x : F.X.carrier) (j : Fin m) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target)
    (hf : (chartAt ℂ x).symm z ∈ frontier (F.D j)) :
    ∃ b : ℂ, Tendsto (s31qr_transportOn (range F.ι)
        (fun y : F.X.carrier => E (ιd ((F.embedding.toOpenPartialHomeomorph F.ι).symm y)))
        (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q x)
        (𝓝[{w | w ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm w ∈ range F.ι}] z) (𝓝 b) ∧
      ∀ (c : ℝ → ℂ) (a b' t : ℝ), ContDiffOn ℝ 1 c (Icc a b') →
        c '' Icc a b' ⊆ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' frontier (F.D j) →
        t ∈ Ioo a b' → c t = z → (b * deriv c t ^ 2).im = 0 := by
  classical
  obtain ⟨hq0, -⟩ := s31qe_q0_props F hm hd Fd E hE hP hQ
  set q0 := s31qr_transportOn (range F.ι)
    (fun y : F.X.carrier => E (ιd ((F.embedding.toOpenPartialHomeomorph F.ι).symm y)))
    (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q with hq0def
  obtain ⟨xF, hDs, Jd, hJd, hbd, hclt, hcl, c₀, hc₀, hc₀', hper, hinj, hcf⟩ := F.disc j
  have hDcl : IsClosed (F.D j) := (s31eg_disc_compact (F.disc j)).isClosed
  obtain ⟨r', κ, L, P0, hr'0, hκd, hκc, hκi, hκu, hκr, hκV, hκ0, hL0, hL, hP0, ⟨P, ρ, hρ0, hPc, hP0e, hg⟩,
    ⟨N, hN, hNA⟩⟩ := s31qe_collar_data F hm hd Fd E hE hP hQ hfix hDs hJd hbd hclt hcl hc₀ hc₀' hper
      hinj hcf hf
  have hsF : (chartAt ℂ x).symm z ∈ (chartAt ℂ xF).source := hDs (hDcl.frontier_subset hf)
  -- the limit in the witness chart
  have hT := s31qe_boundary_limit hJd hbd hr'0 hκd hκc hκi hκu hκr hκV (t := 0)
    (by simpa using hr'0) hL0 hL (g := q0 xF) (P := P) hρ0 hPc hg
  rw [hκ0, hP0e] at hT
  have hmono : Tendsto id
      (𝓝[{w | w ∈ (chartAt ℂ xF).target ∧ (chartAt ℂ xF).symm w ∈ range F.ι}]
        (chartAt ℂ xF ((chartAt ℂ x).symm z)))
      (𝓝[κ '' {z : ℂ | ‖z‖ < r' ∧ 0 < z.im}] (chartAt ℂ xF ((chartAt ℂ x).symm z))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_id.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [nhdsWithin_le_nhds hN, self_mem_nhdsWithin] with w hwN hwA
    exact hNA w hwN hwA.1 hwA.2
  have hbF : Tendsto (q0 xF)
      (𝓝[{w | w ∈ (chartAt ℂ xF).target ∧ (chartAt ℂ xF).symm w ∈ range F.ι}]
        (chartAt ℂ xF ((chartAt ℂ x).symm z))) (𝓝 (P0 / L ^ 2)) := hT.comp hmono
  have hTL := s31qe_limit_transfer hq0 (range F.ι) xF x hz hsF hbF
  refine ⟨P0 / L ^ 2 * deriv (chartTransition xF x) z ^ 2, hTL, ?_⟩
  intro c a b' t hc hsub ht hct
  have hcs : ∀ s ∈ Icc a b', c s ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm (c s) ∈ frontier (F.D j) :=
    fun s hs => hsub (mem_image_of_mem c hs)
  have hOo : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (chartAt ℂ xF).source) :=
    (chartAt ℂ x).isOpen_inter_preimage_symm (chartAt ℂ xF).open_source
  have hτd : DifferentiableOn ℂ (chartTransition xF x)
      ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (chartAt ℂ xF).source) :=
    fun w hw => (s23_transition_differentiableAt xF x hw.1 hw.2).differentiableWithinAt
  have hmaps : MapsTo c (Icc a b')
      ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (chartAt ℂ xF).source) :=
    fun s hs => ⟨(hcs s hs).1, hDs (hDcl.frontier_subset (hcs s hs).2)⟩
  have hτcd : ContDiffOn ℝ 1 (chartTransition xF x)
      ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (chartAt ℂ xF).source) :=
    ((hτd.analyticOnNhd hOo).contDiffOn (n := 1) hOo.uniqueDiffOn).restrict_scalars ℝ
  have hcd : ContDiffOn ℝ 1 (chartTransition xF x ∘ c) (Icc a b') := hτcd.comp hc hmaps
  have himg : (chartTransition xF x ∘ c) '' Icc a b' ⊆ frontier Jd := by
    rintro _ ⟨s, hs, rfl⟩
    exact s31qc_chart_frontier_image hDcl hDs hJd.1 hcl ⟨_, (hcs s hs).2, rfl⟩
  have hγt : (chartTransition xF x ∘ c) t = κ ((0 : ℝ) : ℂ) := by
    rw [hκ0]
    change chartAt ℂ xF ((chartAt ℂ x).symm (c t)) = _
    rw [hct]
  obtain ⟨μ, hμ⟩ := s31qe_curve_tangent hJd hbd hr'0 hκd hκc hκi hκu hκr hκV (τ₀ := 0)
    (by simpa using hr'0) hL0 hL hcd himg ht hγt
  have hct' : DifferentiableAt ℝ c t := (hc.differentiableOn (by norm_num)).differentiableAt (Icc_mem_nhds ht.1 ht.2)
  have hτt : DifferentiableAt ℂ (chartTransition xF x) (c t) := by
    rw [hct]
    exact s23_transition_differentiableAt xF x hz hsF
  have hder : deriv (chartTransition xF x ∘ c) t = deriv c t * deriv (chartTransition xF x) z := by
    have := hτt.hasDerivAt.scomp t hct'.hasDerivAt
    rw [this.deriv, smul_eq_mul, hct]
  have h2 : deriv c t * deriv (chartTransition xF x) z = μ * L := by rw [← hder]; exact hμ
  have hmain : P0 / L ^ 2 * deriv (chartTransition xF x) z ^ 2 * deriv c t ^ 2 = P0 * (μ : ℂ) ^ 2 := by
    calc P0 / L ^ 2 * deriv (chartTransition xF x) z ^ 2 * deriv c t ^ 2
        = P0 / L ^ 2 * (deriv c t * deriv (chartTransition xF x) z) ^ 2 := by ring
      _ = P0 / L ^ 2 * (μ * L) ^ 2 := by rw [h2]
      _ = P0 * (μ : ℂ) ^ 2 := by field_simp
  rw [hmain]
  have hμ2 : ((μ : ℂ) ^ 2) = ((μ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hμ2, Complex.mul_im, hP0]
  simp only [Complex.ofReal_im, mul_zero, zero_mul, add_zero]

end Glue

section Final

/-- (S6b-ext) Boundary extension.  Let `Q` be an admissible differential of `Fd` fixed by the conjugate transport
along `E ∘ J ∘ E⁻¹`.  Its pull-back `q0` to the open surface `ι(S)` (through `ι⁻¹` followed by `E ∘ ιd`) extends to a
differential family `q` of `F.X`: equal to `q0` on the open surface, zero on the interiors of the holes and at the
punctures, continuous up to every boundary curve `frontier (D j)` and real along it (`q(c) c'^2 ∈ ℝ`). -/
theorem s31qd_boundary_extension {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [Nonempty S]
    (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {gd nd : ℕ} (Fd : FiniteTypeStructure (puncturedOpens Pd) gd nd 0)
    (E : Xd.carrier ≃ₜ Fd.X.carrier) (hE : IsBiholomorphic (E : Xd.carrier → Fd.X.carrier))
    (hP : ∀ p : Xd.carrier, p ∈ Pd ↔ E p ∈ Fd.P)
    {Q : Fd.X.carrier → ℂ → ℂ} (hQ : IsAdmissibleQD Fd Q)
    (hfix : s31qr_transportOn univ (fun y : Fd.X.carrier => E (J (E.symm y)))
      Complex.conjCLE.toLinearMap Q = Q) :
    ∃ q : F.X.carrier → ℂ → ℂ, IsDiffFamily 2 0 q ∧
      (∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ range F.ι →
        q x z = s31qr_transportOn (range F.ι)
          (fun y : F.X.carrier => E (ιd ((F.embedding.toOpenPartialHomeomorph F.ι).symm y)))
          (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q x z) ∧
      (∀ (x : F.X.carrier) (j : Fin m), ∀ z ∈ (chartAt ℂ x).target,
        (chartAt ℂ x).symm z ∈ interior (F.D j) → q x z = 0) ∧
      (∀ (x : F.X.carrier), ∀ p ∈ F.P, p ∈ (chartAt ℂ x).source → q x (chartAt ℂ x p) = 0) ∧
      (∀ (x : F.X.carrier) (j : Fin m),
        ContinuousOn (q x) ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (range F.ι ∪ frontier (F.D j)))) ∧
      (∀ (x : F.X.carrier) (j : Fin m) (c : ℝ → ℂ) (a b : ℝ), ContDiffOn ℝ 1 c (Icc a b) →
        c '' Icc a b ⊆ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' frontier (F.D j) →
        ∀ t ∈ Ioo a b, (q x (c t) * deriv c t ^ 2).im = 0) := by
  classical
  obtain ⟨hq0, hhol⟩ := s31qe_q0_props F hm hd Fd E hE hP hQ
  refine s31qe_assemble F hq0 hhol ?_ ?_
  · intro x j z hz hf
    obtain ⟨b, hb, -⟩ := s31qe_boundary_value F hm hd Fd E hE hP hQ hfix x j hz hf
    exact ⟨b, hb⟩
  · intro x j c a b hc hsub t ht b₀ hb₀
    have hz := hsub (mem_image_of_mem c (Ioo_subset_Icc_self ht))
    obtain ⟨b, hb, hreal⟩ := s31qe_boundary_value F hm hd Fd E hE hP hQ hfix x j hz.1 hz.2
    haveI := s31qe_chart_nebot F hz.1 hz.2
    have hbb : b₀ = b := tendsto_nhds_unique hb₀ hb
    subst hbb
    exact hreal c a b t hc hsub ht rfl

end Final


end LiZhongQC
