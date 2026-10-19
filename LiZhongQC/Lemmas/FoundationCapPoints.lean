import LiZhongQC.Ch11.S36_Hamilton
import LiZhongQC.Lemmas.FinitePunctureCompactification
import LiZhongQC.Lemmas.SchottkyBranchedCover5
import LiZhongQC.Lemmas.SchottkyClosedGenus

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC
universe u
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- A holomorphic map on an open set is analytic there (holomorphic charts). -/
theorem ft3_contMDiffOn_of_mdiffOn {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]
    [TopologicalSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N] {f : M → N} {s : Set M} (hs : IsOpen s)
    (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f s) : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f s := by
  rw [contMDiffOn_iff]
  refine ⟨hf.continuousOn, fun x y => ?_⟩
  refine ((mdifferentiableOn_iff.mp hf).2 x y).contDiffOn ?_
  exact (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x)
    (hf.continuousOn.isOpen_inter_preimage hs (isOpen_extChartAt_source y))

/-- The inverse of an injective, open, holomorphic map `ℂ ⊇ U → S` is holomorphic on the image. -/
theorem ft3_inv_mdiffOn {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    {φ : ℂ → S} {U : Set ℂ} (hU : IsOpen U) (hinj : InjOn φ U) (hd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) φ U)
    (ho : ∀ V : Set ℂ, IsOpen V → V ⊆ U → IsOpen (φ '' V)) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (Function.invFunOn φ U) (φ '' U) := by
  rintro _ ⟨w₀, hw₀, rfl⟩
  refine MDifferentiableAt.mdifferentiableWithinAt ?_
  let c := chartAt ℂ (φ w₀)
  let U' : Set ℂ := U ∩ φ ⁻¹' c.source
  have hU' : IsOpen U' := hd.continuousOn.isOpen_inter_preimage hU c.open_source
  have hw₀' : w₀ ∈ U' := ⟨hw₀, mem_chart_source ℂ _⟩
  let h : ℂ → ℂ := fun w => c (φ w)
  have hhd : DifferentiableOn ℂ h U' := fun w hw =>
    (tor_h_differentiableAt_chart_comp ((hd w hw.1).mdifferentiableAt (hU.mem_nhds hw.1)) hw.2).differentiableWithinAt
  have hhinj : InjOn h U' := fun a ha b hb hab => hinj ha.1 hb.1 (c.injOn ha.2 hb.2 hab)
  obtain ⟨hopen, hgd⟩ := RMT.differentiableOn_invFunOn_of_injOn hU' hhd hhinj
  have hmem : c (φ w₀) ∈ h '' U' := ⟨w₀, hw₀', rfl⟩
  have hgD : DifferentiableAt ℂ (Function.invFunOn h U') (c (φ w₀)) := hgd.differentiableAt (hopen.mem_nhds hmem)
  have hm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Function.invFunOn h U' ∘ c) (φ w₀) :=
    hgD.mdifferentiableAt.comp (φ w₀) (mdifferentiableAt_atlas (chart_mem_atlas ℂ (φ w₀)) (mem_chart_source ℂ _))
  refine hm.congr_of_eventuallyEq ?_
  have hnhds : φ '' U' ∈ 𝓝 (φ w₀) := (ho U' hU' inter_subset_left).mem_nhds ⟨w₀, hw₀', rfl⟩
  filter_upwards [hnhds] with s hs
  obtain ⟨w, hw, rfl⟩ := hs
  show Function.invFunOn φ U (φ w) = Function.invFunOn h U' (c (φ w))
  rw [hinj.leftInvOn_invFunOn hw.1]
  exact (hhinj.leftInvOn_invFunOn hw).symm

/-- **F3p (filling in the punctures).**  A Riemann surface with cusp end data is of finite type `(g, n, 0)`: glue a
disc to each end (inside the proof, as a quotient of `S ⊕ Fin n × ball 0 1`); the punctures are the centres; the genus
is that of the closed surface (`closed_surface_has_genus`). -/
theorem ft3_cap_points {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {n : ℕ} (φ : Fin n → ℂ → S) (K : Set S) (r : ℝ) (hK : IsCompact K) (hr : r < 1)
    (hφ : ∀ i, InjOn (φ i) {w | w ≠ 0 ∧ ‖w‖ < 1} ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (φ i) {w | w ≠ 0 ∧ ‖w‖ < 1} ∧
        ∀ V : Set ℂ, IsOpen V → V ⊆ {w | w ≠ 0 ∧ ‖w‖ < 1} → IsOpen (φ i '' V))
    (hφφ : ∀ i i', i ≠ i' → Disjoint (φ i '' {w | w ≠ 0 ∧ ‖w‖ < 1}) (φ i' '' {w | w ≠ 0 ∧ ‖w‖ < 1}))
    (hcov : ∀ x : S, x ∈ K ∨ ∃ i w, w ≠ 0 ∧ ‖w‖ ≤ r ∧ φ i w = x)
    (hend : ∀ x : S, ∃ N ∈ 𝓝 x, ∃ δ > (0 : ℝ), ∀ i w, w ≠ 0 → ‖w‖ < 1 → φ i w ∈ N → δ ≤ ‖w‖) :
    ∃ g : ℕ, IsFiniteType S g n 0 := by
  classical
  -- the punctured disc
  set D : Set ℂ := {w | w ≠ 0 ∧ ‖w‖ < 1} with hDdef
  have hDo : IsOpen D := isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)
  have hDeq : D = {v : ℂ | 0 < ‖v‖ ∧ ‖v‖ < 1} := by
    ext v
    simp [hDdef, norm_pos_iff]
  -- the end charts `W i = (φ i)⁻¹`
  have hEx : ∀ i, ∃ E : OpenPartialHomeomorph ℂ S, E.source = D ∧ (∀ w, E w = φ i w) ∧
      E.target = φ i '' D ∧ ∀ s, E.symm s = Function.invFunOn (φ i) D s := by
    intro i
    obtain ⟨hinj, hd, ho⟩ := hφ i
    let e : PartialEquiv ℂ S := hinj.toPartialEquiv
    have hes : e.source = D := rfl
    refine ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict e (hes ▸ hd.continuousOn) ?_ (hes ▸ hDo),
      rfl, fun w => rfl, rfl, fun s => rfl⟩
    intro V hV
    obtain ⟨V', hV', hVe⟩ := isOpen_induced_iff.mp hV
    have himage : (fun w : e.source => e w) '' V = φ i '' (V' ∩ D) := by
      ext s
      constructor
      · rintro ⟨v, hv, hvs⟩
        have hv' : v ∈ (Subtype.val : e.source → ℂ) ⁻¹' V' := hVe.symm ▸ hv
        have hvD : v.val ∈ D := hes ▸ v.property
        refine ⟨v.val, ⟨hv', hvD⟩, ?_⟩
        change φ i v.val = s at hvs
        exact hvs
      · rintro ⟨w, hw, rfl⟩
        let v : e.source := ⟨w, hes.symm ▸ hw.2⟩
        refine ⟨v, ?_, rfl⟩
        rw [← hVe]
        exact hw.1
    change IsOpen ((fun w : e.source => e w) '' V)
    rw [himage]
    exact ho _ (hV'.inter hDo) inter_subset_right
  choose E hEs hEapp hEt hEsymm using hEx
  let W : Fin n → OpenPartialHomeomorph S ℂ := fun i => (E i).symm
  have hWt : ∀ i, (W i).target = {v : ℂ | 0 < ‖v‖ ∧ ‖v‖ < (fun _ => (1 : ℝ)) i} := fun i => by
    show (E i).source = _
    rw [hEs, hDeq]
  have hR : ∀ i : Fin n, 0 < (fun _ => (1 : ℝ)) i := fun _ => one_pos
  have hWs : ∀ i, (W i).source = φ i '' D := fun i => hEt i
  have hWφ : ∀ i w, w ∈ D → W i (φ i w) = w := by
    intro i w hw
    show (E i).symm (φ i w) = w
    rw [← hEapp, (E i).left_inv (by rw [hEs]; exact hw)]
  have hWm : ∀ i, W i ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω S := by
    intro i
    obtain ⟨hinj, hd, ho⟩ := hφ i
    refine (W i).mem_maximalAtlas_of_contMDiffOn ?_ ?_
    · show ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (E i).symm (E i).target
      rw [hEt]
      refine (ft3_contMDiffOn_of_mdiffOn (ho D hDo subset_rfl) (ft3_inv_mdiffOn hDo hinj hd ho)).congr ?_
      intro s _
      exact hEsymm i s
    · show ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (E i) (E i).source
      rw [hEs]
      exact (ft3_contMDiffOn_of_mdiffOn hDo hd).congr fun w _ => hEapp i w
  -- the topology on `S ⊕ Fin n`
  let τ0 : TopologicalSpace (S ⊕ Fin n) :=
    { IsOpen := fun V => IsOpen (Sum.inl ⁻¹' V) ∧ ∀ i, Sum.inr i ∈ V →
        ∃ s > 0, ∀ y ∈ (W i).source, ‖W i y‖ < s → Sum.inl y ∈ V
      isOpen_univ := ⟨isOpen_univ, fun i _ => ⟨1, one_pos, fun _ _ _ => mem_univ _⟩⟩
      isOpen_inter := by
        rintro s t ⟨hs1, hs2⟩ ⟨ht1, ht2⟩
        refine ⟨hs1.inter ht1, fun i hi => ?_⟩
        obtain ⟨s1, hs1p, h1⟩ := hs2 i hi.1
        obtain ⟨s2, hs2p, h2⟩ := ht2 i hi.2
        exact ⟨min s1 s2, lt_min hs1p hs2p, fun y hy hys =>
          ⟨h1 y hy (lt_of_lt_of_le hys (min_le_left _ _)),
            h2 y hy (lt_of_lt_of_le hys (min_le_right _ _))⟩⟩
      isOpen_sUnion := by
        intro 𝒮 h𝒮
        refine ⟨?_, fun i hi => ?_⟩
        · rw [Set.preimage_sUnion]
          exact isOpen_biUnion fun t ht => (h𝒮 t ht).1
        · obtain ⟨t, ht, hit⟩ := hi
          obtain ⟨s, hsp, hs⟩ := (h𝒮 t ht).2 i hit
          exact ⟨s, hsp, fun y hy hys => ⟨t, ht, hs y hy hys⟩⟩ }
  have hT : ∀ V : Set (S ⊕ Fin n), IsOpen[τ0] V ↔ (IsOpen (Sum.inl ⁻¹' V) ∧ ∀ i, Sum.inr i ∈ V →
      ∃ s > 0, ∀ y ∈ (W i).source, ‖W i y‖ < s → Sum.inl y ∈ V) := fun V => Iff.rfl
  letI : TopologicalSpace (S ⊕ Fin n) := τ0
  have hinl := s82bc_inl_openEmbedding W hT
  -- a point of the `i`-th tail is `φ i w` with `‖w‖` small
  have htail : ∀ i y, y ∈ (W i).source → ∃ w ∈ D, φ i w = y ∧ W i y = w := by
    intro i y hy
    rw [hWs] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    exact ⟨w, hw, rfl, hWφ i w hw⟩
  -- Hausdorff
  have hT2 : T2Space (S ⊕ Fin n) := by
    refine ⟨fun a b hab => ?_⟩
    have hsep : ∀ (y : S) (i : Fin n), ∃ u v : Set (S ⊕ Fin n), IsOpen u ∧ IsOpen v ∧ Sum.inl y ∈ u ∧
        Sum.inr i ∈ v ∧ Disjoint u v := by
      intro y i
      obtain ⟨N, hN, δ, hδ, hNδ⟩ := hend y
      refine ⟨Sum.inl '' interior N, insert (Sum.inr i) (Sum.inl '' {y : S | y ∈ (W i).source ∧ ‖W i y‖ < δ}),
        hinl.isOpenMap _ isOpen_interior, s82bc_end_nhd_open W hT i δ hδ,
        ⟨y, mem_interior_iff_mem_nhds.2 hN, rfl⟩, mem_insert _ _, ?_⟩
      rw [Set.disjoint_left]
      rintro _ ⟨z, hz, rfl⟩ (h | ⟨z', ⟨hz's, hz'δ⟩, hz'⟩)
      · exact absurd h (by simp)
      · obtain rfl := Sum.inl_injective hz'
        obtain ⟨w, hw, rfl, hWw⟩ := htail i z' hz's
        rw [hWw] at hz'δ
        exact absurd (hNδ i w hw.1 hw.2 (interior_subset hz)) (not_le.2 hz'δ)
    rcases a with y | i <;> rcases b with y' | j
    · obtain ⟨u, v, hu, hv, hyu, hyv, huv⟩ := t2_separation (fun h : y = y' => hab (by rw [h]))
      exact ⟨Sum.inl '' u, Sum.inl '' v, hinl.isOpenMap _ hu, hinl.isOpenMap _ hv, ⟨y, hyu, rfl⟩,
        ⟨y', hyv, rfl⟩, (huv.image hinl.injective.injOn (subset_univ _) (subset_univ _))⟩
    · exact hsep y j
    · obtain ⟨u, v, hu, hv, hyu, hyv, huv⟩ := hsep y' i
      exact ⟨v, u, hv, hu, hyv, hyu, huv.symm⟩
    · have hij : i ≠ j := fun h => hab (by rw [h])
      refine ⟨_, _, s82bc_end_nhd_open W hT i 1 one_pos, s82bc_end_nhd_open W hT j 1 one_pos,
        mem_insert _ _, mem_insert _ _, ?_⟩
      rw [Set.disjoint_left]
      rintro t (rfl | ⟨z, ⟨hz, -⟩, rfl⟩) (h | ⟨z', ⟨hz', -⟩, h⟩)
      · exact hij (Sum.inr_injective h)
      · exact absurd h (by simp)
      · exact absurd h (by simp)
      · obtain rfl := Sum.inl_injective h
        rw [hWs] at hz hz'
        exact Set.disjoint_left.1 (hφφ i j hij) hz hz'
  -- compact
  set s₀ : ℝ := (max r 0 + 1) / 2 with hs₀
  have hs₀0 : 0 < s₀ := by rw [hs₀]; have := le_max_right r 0; linarith
  have hs₀1 : s₀ < 1 := by rw [hs₀]; have := max_lt hr one_pos; linarith
  have hrs₀ : r ≤ s₀ := by rw [hs₀]; have := le_max_left r 0; have := max_lt hr one_pos; linarith
  have hcpt : CompactSpace (S ⊕ Fin n) := by
    refine ⟨?_⟩
    have hU : (univ : Set (S ⊕ Fin n)) ⊆ Sum.inl '' K ∪ ⋃ i, insert (Sum.inr i : S ⊕ Fin n)
        (Sum.inl '' {y : S | y ∈ (W i).source ∧ ‖W i y‖ ≤ s₀}) := by
      rintro (y | i) -
      · rcases hcov y with hy | ⟨i, w, hw0, hwr, rfl⟩
        · exact Or.inl ⟨y, hy, rfl⟩
        · have hwD : w ∈ D := ⟨hw0, lt_of_le_of_lt hwr hr⟩
          refine Or.inr (mem_iUnion.2 ⟨i, Or.inr ⟨φ i w, ⟨by rw [hWs]; exact ⟨w, hwD, rfl⟩, ?_⟩, rfl⟩⟩)
          rw [hWφ i w hwD]
          exact hwr.trans hrs₀
      · exact Or.inr (mem_iUnion.2 ⟨i, mem_insert _ _⟩)
    exact ((hK.image hinl.continuous).union (isCompact_iUnion fun i =>
      s82bc_end_compact W hT i 1 s₀ hs₀0 hs₀1 (hWt i))).of_isClosed_subset isClosed_univ hU
  -- connected
  have hconn : ConnectedSpace (S ⊕ Fin n) := by
    refine s82bc_connected_of_dense (Sum.inl : S → S ⊕ Fin n) hinl.continuous ?_
    intro t
    rcases t with y | i
    · exact subset_closure ⟨y, rfl⟩
    · rw [mem_closure_iff_nhds]
      intro A hA
      obtain ⟨s, hs, hsub⟩ := (s82bc_end_nhds_iff W hT i A).mp hA
      set m := min s 1 / 2 with hm
      have hm0 : 0 < m := by rw [hm]; have := lt_min hs one_pos; positivity
      have hmlt : m < min s 1 := by rw [hm]; have := lt_min hs one_pos; linarith
      have hmD : (m : ℂ) ∈ D := by
        refine ⟨by exact_mod_cast hm0.ne', ?_⟩
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
        exact lt_of_lt_of_le hmlt (min_le_right _ _)
      refine ⟨Sum.inl (φ i m), hsub (Or.inr ⟨_, ⟨by rw [hWs]; exact ⟨_, hmD, rfl⟩, ?_⟩, rfl⟩), _, rfl⟩
      rw [hWφ i _ hmD, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
      exact lt_of_lt_of_le hmlt (min_le_left _ _)
  -- the complex structure
  obtain ⟨Wend, -, -, -, -, -, -, csT, hmanT, hchl, -⟩ :=
    s82bc_T_manifold W (fun _ => (1 : ℝ)) hWt hR hWm hT
  let X : ClosedRS.{u} :=
    { carrier := S ⊕ Fin n
      topologicalSpace := τ0
      t2Space := hT2
      connectedSpace := hconn
      compactSpace := hcpt
      chartedSpace := csT
      isManifold := hmanT }
  obtain ⟨g, hg⟩ := closed_surface_has_genus (S := X.carrier)
  -- `inl` is holomorphic: it reads as the identity in the charts
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Sum.inl : S → X.carrier) := by
    intro y
    refine s82bc_mdiffAt_of_charts (A := S) (B := X.carrier) Sum.inl y hinl.continuous.continuousAt id
      differentiableAt_id ?_
    have hchart : chartAt ℂ (Sum.inl y : X.carrier) = (chartAt ℂ y).lift_openEmbedding hinl := hchl y
    filter_upwards [(chartAt ℂ y).open_target.mem_nhds ((chartAt ℂ y).map_source (mem_chart_source ℂ y))]
      with z hz
    rw [hchart, OpenPartialHomeomorph.lift_openEmbedding_apply, (chartAt ℂ y).right_inv hz]
    rfl
  refine ⟨g, ⟨{
    X := X
    P := Finset.univ.image (Sum.inr : Fin n → S ⊕ Fin n)
    D := fun j => j.elim0
    ι := Sum.inl
    genus := hg
    card_P := by rw [Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ, Fintype.card_fin]
    disc := fun j => j.elim0
    disjoint := fun j => j.elim0
    disjoint_P := fun j => j.elim0
    embedding := hinl
    holomorphic := hhol
    range_ι := ?_ }⟩⟩
  ext t
  rcases t with y | i
  · simp
  · simp

end LiZhongQC
