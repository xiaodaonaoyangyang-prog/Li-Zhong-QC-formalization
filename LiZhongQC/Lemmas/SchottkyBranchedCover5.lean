import LiZhongQC.Lemmas.SchottkyBranchedCover2
import LiZhongQC.Lemmas.SchottkyBranchedCover3
import LiZhongQC.Lemmas.SchottkyBranchedCover4
import LiZhongQC.Ch06.S22_RiemannSurfaces
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

open Set Topology Filter
open scoped Manifold ContDiff

noncomputable section
namespace LiZhongQC
universe u

/-- An open embedding of an open subset `N` into `ℂ` gives a chart of the ambient space. -/
theorem s82bc_W0_exists {Y : Type*} [TopologicalSpace Y] {N : Set Y} (hN : IsOpen N)
    (w : ↥N → ℂ) (hw : Topology.IsOpenEmbedding w) [Nonempty ↥N] :
    ∃ W0 : OpenPartialHomeomorph Y ℂ, W0.source = N ∧ W0.target = range w ∧
      ∀ (y : Y) (hy : y ∈ N), W0 y = w ⟨y, hy⟩ := by
  let ew := hw.toOpenPartialHomeomorph w
  refine ⟨ew.lift_openEmbedding hN.isOpenEmbedding_subtypeVal, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.lift_openEmbedding_source]
    simp [ew]
  · rw [OpenPartialHomeomorph.lift_openEmbedding_target]
    simp [ew]
  · intro y hy
    have := OpenPartialHomeomorph.lift_openEmbedding_apply ew hN.isOpenEmbedding_subtypeVal
      (x := ⟨y, hy⟩)
    simpa [ew] using this

/-- Local compactness criterion for a space mapping to a compact space. -/
theorem s82bc_compact_of_local {T X : Type*} [TopologicalSpace T] [TopologicalSpace X]
    [CompactSpace X] (f : T → X)
    (hK : ∀ x : X, ∃ A ∈ 𝓝 x, ∃ K : Set T, IsCompact K ∧ f ⁻¹' A ⊆ K) : CompactSpace T := by
  choose A hA K hKc hsub using hK
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => interior (A x))
    (fun _ => isOpen_interior) (fun x _ => mem_iUnion.mpr ⟨x, mem_interior_iff_mem_nhds.mpr (hA x)⟩)
  refine ⟨?_⟩
  have hcov : (univ : Set T) ⊆ ⋃ x ∈ t, K x := by
    intro z _
    have : f z ∈ ⋃ x ∈ t, interior (A x) := ht (mem_univ _)
    obtain ⟨x, hx, hz⟩ := mem_iUnion₂.mp this
    have hz' : f z ∈ A x := interior_subset hz
    exact mem_iUnion₂.mpr ⟨x, hx, hsub x hz'⟩
  exact (t.isCompact_biUnion fun x _ => hKc x).of_isClosed_subset isClosed_univ hcov

theorem s82bc_connected_of_dense {T Y : Type*} [TopologicalSpace T] [TopologicalSpace Y]
    [ConnectedSpace Y] (j : Y → T) (hj : Continuous j) (hd : DenseRange j) :
    ConnectedSpace T :=
  { toPreconnectedSpace := hd.preconnectedSpace hj
    toNonempty := ⟨j (Classical.arbitrary Y)⟩ }

/-- Restricting a chart of the maximal atlas to an open subset stays in the maximal atlas. -/
theorem s82bc_subtypeRestr_mem_maximalAtlas {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) {U : TopologicalSpace.Opens X}
    (hU : Nonempty U) : e.subtypeRestr hU ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω U := by
  intro e' he'
  obtain ⟨x, rfl⟩ := TopologicalSpace.Opens.chart_eq hU he'
  have hx := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := ω) (x : X)
  refine ⟨?_, ?_⟩
  · exact (contDiffGroupoid ω 𝓘(ℂ)).mem_of_eqOnSource
      (closedUnderRestriction' (IsManifold.compatible_of_mem_maximalAtlas he hx)
        (e.isOpen_inter_preimage_symm U.2))
      (e.subtypeRestr_symm_trans_subtypeRestr hU (chartAt ℂ (x : X)))
  · exact (contDiffGroupoid ω 𝓘(ℂ)).mem_of_eqOnSource
      (closedUnderRestriction' (IsManifold.compatible_of_mem_maximalAtlas hx he)
        ((chartAt ℂ (x : X)).isOpen_inter_preimage_symm U.2))
      ((chartAt ℂ (x : X)).subtypeRestr_symm_trans_subtypeRestr hU e)

section EndCompactificationMain

variable {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X] {ι : Type*}

/-- **The end compactification** `Y ⊕ ι`: topology, Hausdorff, compact, connected. -/
theorem s82bc_end_compactification [T2Space X] [CompactSpace X] [T2Space Y] [ConnectedSpace Y]
    (W : ι → OpenPartialHomeomorph Y ℂ) (R : ι → ℝ)
    (hWt : ∀ i, (W i).target = {v : ℂ | 0 < ‖v‖ ∧ ‖v‖ < R i}) (hR : ∀ i, 0 < R i)
    (ψ : Y → X) (hψ : Continuous ψ) (e : ι → X) (he : Function.Injective e)
    (hne : ∀ y i, ψ y ≠ e i)
    (hlim : ∀ i, ∀ A ∈ 𝓝 (e i), ∃ s > 0, ∀ y ∈ (W i).source, ‖W i y‖ < s → ψ y ∈ A)
    (hKS : ∀ x : X, x ∉ range e → ∃ A ∈ 𝓝 x, (∀ j, e j ∉ A) ∧
      ∃ C : Set Y, IsCompact C ∧ ∀ y, ψ y ∈ A → y ∈ C)
    (hKE : ∀ i, ∃ A ∈ 𝓝 (e i), (∀ j, e j ∈ A → j = i) ∧ ∃ s : ℝ, 0 < s ∧ s < R i ∧
      ∀ y, ψ y ∈ A → y ∈ (W i).source ∧ ‖W i y‖ ≤ s) :
    ∃ τT : TopologicalSpace (Y ⊕ ι),
      (∀ V : Set (Y ⊕ ι), IsOpen[τT] V ↔ (IsOpen (Sum.inl ⁻¹' V) ∧ ∀ i, Sum.inr i ∈ V →
        ∃ s > 0, ∀ y ∈ (W i).source, ‖W i y‖ < s → Sum.inl y ∈ V)) ∧
      @T2Space (Y ⊕ ι) τT ∧ @CompactSpace (Y ⊕ ι) τT ∧ @ConnectedSpace (Y ⊕ ι) τT ∧
      @Continuous (Y ⊕ ι) X τT _ (Sum.elim ψ e) := by
  classical
  let τ0 : TopologicalSpace (Y ⊕ ι) :=
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
  have hT : ∀ V : Set (Y ⊕ ι), IsOpen[τ0] V ↔ (IsOpen (Sum.inl ⁻¹' V) ∧ ∀ i, Sum.inr i ∈ V →
      ∃ s > 0, ∀ y ∈ (W i).source, ‖W i y‖ < s → Sum.inl y ∈ V) := fun V => Iff.rfl
  letI : TopologicalSpace (Y ⊕ ι) := τ0
  have hpr : Continuous (Sum.elim ψ e) := s82bc_pr_continuous W hT ψ e hψ hlim
  have hinl := s82bc_inl_openEmbedding W hT
  refine ⟨τ0, hT, s82bc_t2 W hT ψ e hpr he hne, ?_, ?_, hpr⟩
  · -- compactness
    refine s82bc_compact_of_local (Sum.elim ψ e) fun x => ?_
    by_cases hx : x ∈ range e
    · obtain ⟨i, rfl⟩ := hx
      obtain ⟨A, hA, hAe, s, hs0, hsR, hAy⟩ := hKE i
      refine ⟨A, hA, _, s82bc_end_compact W hT i (R i) s hs0 hsR (hWt i), ?_⟩
      rintro (y | j) hy
      · exact Or.inr ⟨y, hAy y hy, rfl⟩
      · have : j = i := hAe j hy
        subst this
        exact Or.inl rfl
    · obtain ⟨A, hA, hAe, C, hC, hAC⟩ := hKS x hx
      refine ⟨A, hA, Sum.inl '' C, hC.image hinl.continuous, ?_⟩
      rintro (y | j) hy
      · exact ⟨y, hAC y hy, rfl⟩
      · exact absurd hy (hAe j)
  · -- connectedness
    refine s82bc_connected_of_dense (Sum.inl : Y → Y ⊕ ι) hinl.continuous ?_
    intro t
    rcases t with y | i
    · exact subset_closure ⟨y, rfl⟩
    · rw [mem_closure_iff_nhds]
      intro A hA
      obtain ⟨s, hs, hsub⟩ := (s82bc_end_nhds_iff W hT i A).mp hA
      have hRi := hR i
      have hmin : 0 < min s (R i) := lt_min hs hRi
      set m := min s (R i) / 2 with hm
      have hm0 : 0 < m := by rw [hm]; positivity
      have hmlt : m < min s (R i) := by rw [hm]; linarith
      have hmv : (m : ℂ) ∈ (W i).target := by
        rw [hWt i]
        refine ⟨?_, ?_⟩
        · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]; exact hm0
        · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
          exact lt_of_lt_of_le hmlt (min_le_right _ _)
      refine ⟨Sum.inl ((W i).symm (m : ℂ)), hsub (Or.inr ⟨_, ⟨(W i).map_target hmv, ?_⟩, rfl⟩), _, rfl⟩
      rw [(W i).right_inv hmv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
      exact lt_of_lt_of_le hmlt (min_le_left _ _)

end EndCompactificationMain

/-- A two-sheeted covering with a continuous free deck involution has compact preimages of
compact sets. -/
theorem s82bc_preimage_compact {Y S : Type*} [TopologicalSpace Y] [TopologicalSpace S]
    (q : Y → S) (τ : Y → Y) (hqlh : IsLocalHomeomorph q) (hqs : Function.Surjective q)
    (hτ : Continuous τ) (hτ2 : ∀ y, τ (τ y) = y) (hqτ : ∀ y, q (τ y) = q y)
    (hfibτ : ∀ y y', q y = q y' → y' = y ∨ y' = τ y) {B : Set S} (hB : IsCompact B) :
    IsCompact (q ⁻¹' B) := by
  have hqopen : IsOpenMap q := hqlh.isOpenMap
  have hclosed : IsClosedMap q := by
    intro C hC
    have hcomp : (q '' C)ᶜ = q '' (C ∪ τ ⁻¹' C)ᶜ := by
      ext s
      constructor
      · intro hs
        obtain ⟨y, rfl⟩ := hqs s
        refine ⟨y, ?_, rfl⟩
        rintro (hy | hy)
        · exact hs ⟨y, hy, rfl⟩
        · exact hs ⟨τ y, hy, hqτ y⟩
      · rintro ⟨y, hy, rfl⟩ ⟨c, hc, hcy⟩
        rcases hfibτ c y hcy with h | h
        · exact hy (Or.inl (h ▸ hc))
        · refine hy (Or.inr ?_)
          rw [h]; show τ (τ c) ∈ C; rw [hτ2]; exact hc
    rw [← isOpen_compl_iff, hcomp]
    exact hqopen _ ((hC.union (hC.preimage hτ)).isOpen_compl)
  have hfin : ∀ s, (q ⁻¹' {s}).Finite := by
    intro s
    obtain ⟨y, hy⟩ := hqs s
    refine ((Set.finite_singleton (τ y)).insert y).subset ?_
    intro y' hy'
    rcases hfibτ y y' (hy.trans hy'.symm) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hproper : IsProperMap q := by
    rw [isProperMap_iff_isClosedMap_and_compact_fibers]
    exact ⟨hqlh.continuous, hclosed, fun s => (hfin s).isCompact⟩
  exact hproper.isCompact_preimage hB

theorem s82bc_fibre_pair {Y S : Type*} (q : Y → S) (τ : Y → Y)
    (hfib : ∀ s, (q ⁻¹' {s}).ncard = 2) (hqτ : ∀ y, q (τ y) = q y) (hfree : ∀ y, τ y ≠ y) :
    ∀ y y', q y = q y' → y' = y ∨ y' = τ y := by
  intro y y' h
  by_cases hyy : y' = y
  · exact Or.inl hyy
  · refine Or.inr (s82bc_two_pts (hfib (q y)) (a := y') (b := y) (c := τ y) ?_ rfl ?_
      (Ne.symm hyy) (hfree y).symm)
    · exact h.symm
    · exact hqτ y

theorem s82bc_fibre_surj {Y S : Type*} (q : Y → S) (hfib : ∀ s, (q ⁻¹' {s}).ncard = 2) :
    Function.Surjective q := by
  intro s
  obtain ⟨y, hy⟩ : (q ⁻¹' {s}).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [hfib]; norm_num)
  exact ⟨y, hy⟩

section EndAnalysis

variable {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]

/-- Near an end, the base point is the chart-inverse of the square of the end coordinate. -/
theorem s82bc_end_lim (ψ : Y → X) (E : OpenPartialHomeomorph X ℂ) (W0 : OpenPartialHomeomorph Y ℂ)
    (r : ℝ) (hr : 0 < r) (hball : Metric.ball (0 : ℂ) r ⊆ E.target) {p : X} (hp : p ∈ E.source)
    (hEp : E p = 0)
    (hsrcW : ∀ y ∈ W0.source, ψ y ∈ E.source ∧ W0 y ^ 2 = E (ψ y)) :
    ∀ A ∈ 𝓝 p, ∃ s > 0, ∀ y ∈ W0.source, ‖W0 y‖ < s → ψ y ∈ A := by
  intro A hA
  have h0 : (0 : ℂ) ∈ E.target := hball (Metric.mem_ball_self hr)
  have hsymm0 : E.symm 0 = p := by rw [← hEp]; exact E.left_inv hp
  have hc : ContinuousAt E.symm 0 := E.continuousAt_symm h0
  have hpre : E.symm ⁻¹' A ∈ 𝓝 (0 : ℂ) := hc.preimage_mem_nhds (by rw [hsymm0]; exact hA)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨Real.sqrt δ, Real.sqrt_pos.mpr hδ, fun y hy hys => ?_⟩
  obtain ⟨hψ, hsq⟩ := hsrcW y hy
  have : ψ y = E.symm (W0 y ^ 2) := by rw [hsq, E.left_inv hψ]
  rw [this]
  apply hδsub
  rw [Metric.mem_ball, dist_zero_right, norm_pow]
  have := (Real.lt_sqrt (norm_nonneg _)).mp hys
  exact this

/-- A small neighbourhood of an end point is contained in a small tail. -/
theorem s82bc_end_tail (ψ : Y → X) (E : OpenPartialHomeomorph X ℂ) (W0 : OpenPartialHomeomorph Y ℂ)
    (r : ℝ) (hr : 0 < r) (hball : Metric.ball (0 : ℂ) r ⊆ E.target) {p : X} (hp : p ∈ E.source)
    (hEp : E p = 0)
    (hsrcW : ∀ y ∈ W0.source, ψ y ∈ E.source ∧ W0 y ^ 2 = E (ψ y))
    (hback : ∀ y, ψ y ∈ E.source → E (ψ y) ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} → y ∈ W0.source) :
    ∃ A ∈ 𝓝 p, (∀ x ∈ A, x = p ∨ ∃ z : ℂ, z ≠ 0 ∧ ‖z‖ < r ∧ x = E.symm z) ∧
      ∃ s : ℝ, 0 < s ∧ s < Real.sqrt r ∧
        ∀ y, ψ y ∈ A → ψ y ≠ p → y ∈ W0.source ∧ ‖W0 y‖ ≤ s := by
  have h0 : (0 : ℂ) ∈ E.target := hball (Metric.mem_ball_self hr)
  have hsymm0 : E.symm 0 = p := by rw [← hEp]; exact E.left_inv hp
  have hσ : 0 < r / 4 := by positivity
  refine ⟨E.symm '' Metric.ball (0 : ℂ) (r / 4), ?_, ?_, Real.sqrt (r / 4), Real.sqrt_pos.mpr hσ,
    Real.sqrt_lt_sqrt hσ.le (by linarith), ?_⟩
  · have := E.symm.image_mem_nhds (x := (0 : ℂ)) (by simpa using h0) (Metric.ball_mem_nhds _ hσ)
    rwa [hsymm0] at this
  · rintro _ ⟨z, hz, rfl⟩
    by_cases hz0 : z = 0
    · left; rw [hz0, hsymm0]
    · right
      refine ⟨z, hz0, ?_, rfl⟩
      rw [Metric.mem_ball, dist_zero_right] at hz
      linarith
  · intro y hy hyp
    obtain ⟨z, hz, hzy⟩ := hy
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hyp (by rw [← hzy, hsymm0])
    rw [Metric.mem_ball, dist_zero_right] at hz
    have hzt : z ∈ E.target := hball (by rw [Metric.mem_ball, dist_zero_right]; linarith)
    have hψ : ψ y ∈ E.source := by rw [← hzy]; exact E.map_target hzt
    have hEψ : E (ψ y) = z := by rw [← hzy]; exact E.right_inv hzt
    have hyW : y ∈ W0.source :=
      hback y hψ (by rw [hEψ]; exact ⟨norm_pos_iff.mpr hz0, by linarith⟩)
    refine ⟨hyW, ?_⟩
    have hsq := (hsrcW y hyW).2
    rw [hEψ] at hsq
    have : ‖W0 y‖ ^ 2 < r / 4 := by
      rw [← norm_pow, hsq]; exact hz
    exact (Real.lt_sqrt (norm_nonneg _)).mpr this |>.le

end EndAnalysis

section Main

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X] [ConnectedSpace X]
  [CompactSpace X] [IsManifold 𝓘(ℂ) ω X]

/-- **Per-end construction.**  For a chart `E` of `X` centred at a puncture, and the covering
`q : Y → U` over the complement of the punctures: a chart `W0` of `Y` onto a punctured disc whose
square is `E ∘ q`. -/
theorem s82bc_end_chart {Y : Type u} [TopologicalSpace Y] (U : TopologicalSpace.Opens X)
    (hUne : Nonempty U) (q : Y → U) (hcov : IsCoveringMap q) (hfib : ∀ s, (q ⁻¹' {s}).ncard = 2)
    (E : OpenPartialHomeomorph X ℂ) (r ρ : ℝ) (hρ0 : 0 < ρ) (hρr : ρ < r)
    (hball : Metric.ball (0 : ℂ) r ⊆ E.target) (hU : ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → E.symm z ∈ U)
    (hmono : ∀ Γ : C(unitInterval, Y), (∀ t : unitInterval,
      ((q (Γ t) : U) : X) = E.symm ((ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)))) →
      Γ 1 ≠ Γ 0) :
    ∃ W0 : OpenPartialHomeomorph Y ℂ,
      W0.target = {v : ℂ | 0 < ‖v‖ ∧ ‖v‖ < Real.sqrt r} ∧
      (∀ y ∈ W0.source, ((q y : U) : X) ∈ E.source ∧ W0 y ^ 2 = E ((q y : U) : X)) ∧
      (∀ y, ((q y : U) : X) ∈ E.source → E ((q y : U) : X) ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} →
        y ∈ W0.source) := by
  classical
  have hr : 0 < r := hρ0.trans hρr
  set ES := E.subtypeRestr hUne with hES
  have hESt : ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → z ∈ ES.target := by
    intro z hz0 hz
    refine ⟨hball (by rw [Metric.mem_ball, dist_zero_right]; exact hz), ?_⟩
    rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
    exact hU z hz0 hz
  have hESsymm : ∀ z, z ∈ ES.target → ((ES.symm z : U) : X) = E.symm z := fun z hz =>
    (E.subtypeRestr_symm_apply hUne hz)
  have hdst : {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} ⊆ ES.target := fun z hz =>
    hESt z (norm_pos_iff.mp hz.1) hz.2
  have hmono' : ∀ Γ : C(unitInterval, Y), (∀ t : unitInterval,
      q (Γ t) = ES.symm ((ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)))) →
      Γ 1 ≠ Γ 0 := by
    intro Γ hΓ
    refine hmono Γ fun t => ?_
    have hn : ‖(ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ))‖ = ρ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
      have : ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℝ))‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [this, mul_one]
    have hz0 : (ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) ≠ 0 := by
      intro h; rw [h, norm_zero] at hn; linarith
    rw [hΓ t, hESsymm _ (hESt _ hz0 (by rw [hn]; exact hρr))]
  obtain ⟨w, hwemb, hwrange, hwsq⟩ := s82bc_puncture_model q hcov hfib ES r hr hdst ρ hρ0 hρr hmono'
  have hsrc' : ES.source = Subtype.val ⁻¹' E.source := E.subtypeRestr_source hUne
  have hNo : IsOpen (q ⁻¹' {s : U | s ∈ ES.source ∧ ES s ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r}}) :=
    (s82bc_disc_open ES r).preimage hcov.continuous
  have hNne : Nonempty ↥(q ⁻¹' {s : U | s ∈ ES.source ∧ ES s ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r}}) := by
    have : ((Real.sqrt r / 2 : ℝ) : ℂ) ∈ range w := by
      rw [hwrange]
      have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
      refine ⟨?_, ?_⟩
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; positivity
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith
    obtain ⟨y, _⟩ := this
    exact ⟨y⟩
  obtain ⟨W0, hsrc, htgt, happ⟩ := s82bc_W0_exists hNo w hwemb
  refine ⟨W0, by rw [htgt, hwrange], ?_, ?_⟩
  · intro y hy
    rw [hsrc] at hy
    refine ⟨by have := hy.1; rwa [hsrc'] at this, ?_⟩
    rw [happ y hy]
    exact hwsq ⟨y, hy⟩
  · intro y h1 h2
    rw [hsrc]
    exact ⟨by rw [hsrc']; exact h1, h2⟩

end Main

section Wrapper

/-- The index-two cover with the atlas replaced by the set of canonical charts. -/
theorem s82bc_index_two_cover' {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [IsManifold 𝓘(ℂ) ω S] [ConnectedSpace S] (x₀ : S) (K : Subgroup (FundamentalGroup S x₀))
    (hK : K.index = 2) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace ℂ Y) (q : Y → S) (τ : Y → Y),
      T2Space Y ∧ IsManifold 𝓘(ℂ) ω Y ∧ PathConnectedSpace Y ∧ IsCoveringMap q ∧
      (∀ y y', y' ∈ (chartAt ℂ y).source → q y' ∈ (chartAt ℂ (q y)).source ∧
        chartAt ℂ (q y) (q y') = chartAt ℂ y y') ∧
      (∀ s, (q ⁻¹' {s}).ncard = 2) ∧ Continuous τ ∧ (∀ y, τ (τ y) = y) ∧ (∀ y, q (τ y) = q y) ∧
      (∀ y, τ y ≠ y) ∧
      (∀ (z : S) (a : Path x₀ z) (β : Path z z),
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((a.trans β).trans a.symm)) ∉ K →
        ∀ Γ : C(unitInterval, Y), (∀ t, q (Γ t) = β t) → Γ 1 ≠ Γ 0) ∧
      (∀ e' ∈ atlas ℂ Y, ∃ y : Y, e' = chartAt ℂ y) := by
  obtain ⟨Y, tY, cs0, q, τ, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11⟩ :=
    s82bc_index_two_cover x₀ K hK
  have hcompat : ∀ y y' : Y, (chartAt ℂ y).symm ≫ₕ chartAt ℂ y' ∈ contDiffGroupoid ω 𝓘(ℂ) :=
    fun y y' => (contDiffGroupoid ω 𝓘(ℂ)).compatible (chart_mem_atlas ℂ y) (chart_mem_atlas ℂ y')
  let cs : ChartedSpace ℂ Y :=
    { atlas := range (fun y : Y => cs0.chartAt y)
      chartAt := fun y => cs0.chartAt y
      mem_chart_source := fun y => cs0.mem_chart_source y
      chart_mem_atlas := fun y => ⟨y, rfl⟩ }
  have hman : @IsManifold ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ) ω Y _ cs := by
    refine @IsManifold.mk ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ) ω Y _ cs ⟨?_⟩
    rintro e e' ⟨y, rfl⟩ ⟨y', rfl⟩
    exact hcompat y y'
  refine ⟨Y, tY, cs, q, τ, H1, hman, H3, H4, H5, H6, H7, H8, H9, H10, H11, ?_⟩
  rintro e' ⟨y, rfl⟩
  exact ⟨y, rfl⟩

end Wrapper

section MainTheorem

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X] [ConnectedSpace X]
  [CompactSpace X] [IsManifold 𝓘(ℂ) ω X]

/-- **The branched double cover** attached to an index-two subgroup `K` of `π₁(X ∖ P)` which
changes sheets around each puncture. -/
theorem s82bc_branched_main {ι : Type u} (e : ι → X) (he : Function.Injective e)
    (U : TopologicalSpace.Opens X) (hrange : range e = (U : Set X)ᶜ) (x₀ : U)
    [ConnectedSpace U] (K : Subgroup (FundamentalGroup U x₀)) (hK : K.index = 2)
    (hpunct : ∀ i : ι, ∃ (E : OpenPartialHomeomorph X ℂ) (r ρ : ℝ),
      E ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X ∧ e i ∈ E.source ∧ E (e i) = 0 ∧ 0 < ρ ∧ ρ < r ∧
      Metric.ball (0 : ℂ) r ⊆ E.target ∧ (∀ z : ℂ, z ≠ 0 → ‖z‖ < r → E.symm z ∈ U) ∧
      ∃ (z₀ : U) (a : Path x₀ z₀) (β : Path z₀ z₀), (z₀ : X) = E.symm ρ ∧
        (∀ t : unitInterval, (β t : X) =
          E.symm ((ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)))) ∧
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((a.trans β).trans a.symm)) ∉ K) :
    ∃ (T : Type u) (_ : TopologicalSpace T) (_ : ChartedSpace ℂ T),
      T2Space T ∧ ConnectedSpace T ∧ CompactSpace T ∧ IsManifold 𝓘(ℂ) ω T ∧
      ∃ pr : T → X, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr ∧ Function.Surjective pr ∧
        (∀ x : X, x ∈ U → (pr ⁻¹' {x}).ncard = 2) ∧ (∀ x : X, x ∉ U → (pr ⁻¹' {x}).ncard = 1) ∧
        ∃ h : T ≃ₜ T, IsBiholomorphic h ∧ (∀ y, h (h y) = y) ∧ (∀ y, pr (h y) = pr y) ∧
          ∀ y, h y = y ↔ pr y ∉ U := by
  classical
  have hUne : Nonempty U := ⟨x₀⟩
  obtain ⟨Y, tY, csY, q, τ, hT2Y, hmanY, hpcY, hcov, hchart, hfib, hτc, hτ2, hqτ, hfree, hmono,
    hatlas⟩ := s82bc_index_two_cover' x₀ K hK
  haveI : ConnectedSpace Y := inferInstance
  choose E r ρ hEm hEsrc hEp hρ0 hρr hball hU hloop using hpunct
  have hr : ∀ i, 0 < r i := fun i => (hρ0 i).trans (hρr i)
  -- the end charts
  have hend : ∀ i, ∃ W0 : OpenPartialHomeomorph Y ℂ,
      W0.target = {v : ℂ | 0 < ‖v‖ ∧ ‖v‖ < Real.sqrt (r i)} ∧
      (∀ y ∈ W0.source, ((q y : U) : X) ∈ (E i).source ∧ W0 y ^ 2 = E i ((q y : U) : X)) ∧
      (∀ y, ((q y : U) : X) ∈ (E i).source → E i ((q y : U) : X) ∈
        {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r i} → y ∈ W0.source) := by
    intro i
    obtain ⟨z₀, a, β, hz0, hβ, hKn⟩ := hloop i
    refine s82bc_end_chart U hUne q hcov hfib (E i) (r i) (ρ i) (hρ0 i) (hρr i) (hball i) (hU i) ?_
    intro Γ hΓ
    refine hmono z₀ a β hKn Γ fun t => Subtype.ext ?_
    rw [hΓ t, hβ t]
  choose W0 hW0t hW0sq hW0back using hend
  have hqs : Function.Surjective q := s82bc_fibre_surj q hfib
  have hfibτ := s82bc_fibre_pair q τ hfib hqτ hfree
  let R : ι → ℝ := fun i => Real.sqrt (r i)
  have hR : ∀ i, 0 < R i := fun i => Real.sqrt_pos.mpr (hr i)
  let ψ : Y → X := fun y => ((q y : U) : X)
  have hψ : Continuous ψ := continuous_subtype_val.comp hcov.continuous
  have hψU : ∀ y, ψ y ∈ U := fun y => (q y).2
  have heU : ∀ i, e i ∉ U := by
    intro i hi
    have : e i ∈ (U : Set X)ᶜ := by rw [← hrange]; exact mem_range_self i
    exact this hi
  have hne : ∀ y i, ψ y ≠ e i := fun y i h => heU i (h ▸ hψU y)
  have hWm : ∀ i, W0 i ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y := by
    intro i
    refine s82bc_endchart_mem_maximalAtlas hatlas q hchart ((E i).subtypeRestr hUne)
      (s82bc_subtypeRestr_mem_maximalAtlas (hEm i) hUne) (W0 i) ?_ ?_
    · intro y hy
      exact ⟨by rw [(E i).subtypeRestr_source hUne]; exact (hW0sq i y hy).1, (hW0sq i y hy).2⟩
    · intro y hy h
      have hv : W0 i y ∈ (W0 i).target := (W0 i).map_source hy
      rw [hW0t i] at hv
      exact (norm_pos_iff.mp hv.1) h
  have hlim : ∀ i, ∀ A ∈ 𝓝 (e i), ∃ s > 0, ∀ y ∈ (W0 i).source, ‖W0 i y‖ < s → ψ y ∈ A :=
    fun i => s82bc_end_lim ψ (E i) (W0 i) (r i) (hr i) (hball i) (hEsrc i) (hEp i) (hW0sq i)
  have hKE : ∀ i, ∃ A ∈ 𝓝 (e i), (∀ j, e j ∈ A → j = i) ∧ ∃ s : ℝ, 0 < s ∧ s < R i ∧
      ∀ y, ψ y ∈ A → y ∈ (W0 i).source ∧ ‖W0 i y‖ ≤ s := by
    intro i
    obtain ⟨A, hA, hdesc, s, hs0, hsR, hsub⟩ :=
      s82bc_end_tail ψ (E i) (W0 i) (r i) (hr i) (hball i) (hEsrc i) (hEp i) (hW0sq i) (hW0back i)
    refine ⟨A, hA, ?_, s, hs0, hsR, fun y hy => hsub y hy (hne y i)⟩
    intro j hj
    rcases hdesc _ hj with h | ⟨z, hz0, hz, hjz⟩
    · exact he h
    · exfalso
      exact heU j (hjz ▸ hU i z hz0 hz)
  have hKS : ∀ x : X, x ∉ range e → ∃ A ∈ 𝓝 x, (∀ j, e j ∉ A) ∧
      ∃ C : Set Y, IsCompact C ∧ ∀ y, ψ y ∈ A → y ∈ C := by
    intro x hx
    have hxU : x ∈ U := by
      by_contra h
      exact hx (by rw [hrange]; exact h)
    obtain ⟨Kc, hKc, hxK, hKU⟩ := exists_compact_subset U.isOpen hxU
    refine ⟨Kc, mem_interior_iff_mem_nhds.mp hxK, fun j hj => heU j (hKU hj),
      q ⁻¹' {s : U | (s : X) ∈ Kc}, ?_, fun y hy => hy⟩
    refine s82bc_preimage_compact q τ hcov.isLocalHomeomorph hqs hτc hτ2 hqτ hfibτ ?_
    rw [Subtype.isCompact_iff]
    have : (Subtype.val : U → X) '' {s : U | (s : X) ∈ Kc} = Kc := by
      ext z
      constructor
      · rintro ⟨s, hs, rfl⟩; exact hs
      · intro hz; exact ⟨⟨z, hKU hz⟩, hz, rfl⟩
    rw [this]; exact hKc
  -- the deck involution preserves the end charts and acts by `-1`
  have hWτ : ∀ i, ∀ y ∈ (W0 i).source, τ y ∈ (W0 i).source ∧ W0 i (τ y) = - W0 i y := by
    intro i y hy
    obtain ⟨hψy, hsq⟩ := hW0sq i y hy
    have hv : W0 i y ∈ (W0 i).target := (W0 i).map_source hy
    rw [hW0t i] at hv
    have hEψ : E i (ψ y) ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r i} := by
      show E i (ψ y) ∈ _
      rw [← hsq]
      show 0 < ‖W0 i y ^ 2‖ ∧ ‖W0 i y ^ 2‖ < r i
      rw [norm_pow]
      refine ⟨pow_pos hv.1 2, ?_⟩
      have := (Real.lt_sqrt (norm_nonneg _)).mp hv.2
      exact this
    have hψτ : ψ (τ y) = ψ y := by
      show ((q (τ y) : U) : X) = ((q y : U) : X)
      rw [hqτ]
    have hτs : τ y ∈ (W0 i).source := by
      refine hW0back i (τ y) ?_ ?_
      · show ψ (τ y) ∈ (E i).source
        rw [hψτ]; exact hψy
      · show E i (ψ (τ y)) ∈ _
        rw [hψτ]; exact hEψ
    refine ⟨hτs, ?_⟩
    obtain ⟨_, hsq'⟩ := hW0sq i (τ y) hτs
    have hsq2 : W0 i (τ y) ^ 2 = W0 i y ^ 2 := by
      rw [hsq', hsq]
      show E i (ψ (τ y)) = E i (ψ y)
      rw [hψτ]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq2 with h | h
    · exfalso
      exact hfree y ((W0 i).injOn hτs hy h)
    · exact h
  obtain ⟨τT, hT, hT2, hcpt, hconn, hprc⟩ :=
    s82bc_end_compactification W0 R hW0t hR ψ hψ e he hne hlim hKS hKE
  letI : TopologicalSpace (Y ⊕ ι) := τT
  obtain ⟨Wend, hsrc, htgt, happ_l, happ_r, hsymm, hsymm0, csT, hmanT, hchl, hchr⟩ :=
    s82bc_T_manifold W0 R hW0t hR hWm hT
  have hinl := s82bc_inl_openEmbedding W0 hT
  -- the involution on `T`
  let τ' : Y ⊕ ι → Y ⊕ ι := Sum.map τ id
  have hτ'2 : ∀ t, τ' (τ' t) = t := by
    rintro (y | i)
    · show Sum.inl (τ (τ y)) = Sum.inl y
      rw [hτ2]
    · rfl
  have hτ'c : Continuous τ' := by
    refine continuous_def.mpr fun V hV => (hT _).mpr ⟨?_, ?_⟩
    · exact ((hT V).mp hV).1.preimage hτc
    · intro i hi
      obtain ⟨s, hs, hsV⟩ := ((hT V).mp hV).2 i hi
      refine ⟨s, hs, fun y hy hys => ?_⟩
      obtain ⟨hτy, hneg⟩ := hWτ i y hy
      exact hsV (τ y) hτy (by rw [hneg, norm_neg]; exact hys)
  let hom : (Y ⊕ ι) ≃ₜ (Y ⊕ ι) :=
    { toFun := τ'
      invFun := τ'
      left_inv := hτ'2
      right_inv := hτ'2
      continuous_toFun := hτ'c
      continuous_invFun := hτ'c }
  have hprτ : ∀ t, Sum.elim ψ e (τ' t) = Sum.elim ψ e t := by
    rintro (y | i)
    · show ψ (τ y) = ψ y
      show ((q (τ y) : U) : X) = ((q y : U) : X)
      rw [hqτ]
    · rfl
  haveI : IsManifold 𝓘(ℂ) 1 (Y ⊕ ι) := IsManifold.of_le (n := ω) (by simp)
  haveI : IsManifold 𝓘(ℂ) 1 X := IsManifold.of_le (n := ω) (by simp)
  have hpr_eq : ∀ i, ∀ y ∈ (W0 i).source, ψ y = (E i).symm (W0 i y ^ 2) := by
    intro i y hy
    obtain ⟨hψy, hsq⟩ := hW0sq i y hy
    rw [hsq, (E i).left_inv hψy]
  -- holomorphy of the involution
  have hτ'md : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ' := by
    rintro (y | i)
    · refine s82bc_mdiffAt_of_charts τ' (Sum.inl y) hτ'c.continuousAt id differentiableAt_id ?_
      show ∀ᶠ z in 𝓝 (chartAt ℂ (Sum.inl y : Y ⊕ ι) (Sum.inl y)),
        chartAt ℂ (Sum.inl (τ y) : Y ⊕ ι) (τ' ((chartAt ℂ (Sum.inl y : Y ⊕ ι)).symm z)) = id z
      rw [hchl y, hchl (τ y)]
      have hpt : ((chartAt ℂ y).lift_openEmbedding hinl) (Sum.inl y) = chartAt ℂ y y :=
        OpenPartialHomeomorph.lift_openEmbedding_apply _ _
      rw [hpt]
      have hyt : chartAt ℂ y y ∈ (chartAt ℂ y).target :=
        (chartAt ℂ y).map_source (mem_chart_source ℂ y)
      have hsrcτ : (chartAt ℂ (τ y)).source ∈ 𝓝 (τ y) :=
        (chartAt ℂ (τ y)).open_source.mem_nhds (mem_chart_source ℂ _)
      have hnhd : (chartAt ℂ y).target ∩
          (chartAt ℂ y).symm ⁻¹' (τ ⁻¹' (chartAt ℂ (τ y)).source) ∈ 𝓝 (chartAt ℂ y y) := by
        refine Filter.inter_mem ((chartAt ℂ y).open_target.mem_nhds hyt) ?_
        have hc : ContinuousAt (chartAt ℂ y).symm (chartAt ℂ y y) :=
          (chartAt ℂ y).continuousAt_symm hyt
        refine hc.preimage_mem_nhds ?_
        rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
        exact hτc.continuousAt.preimage_mem_nhds hsrcτ
      filter_upwards [hnhd] with z hz
      obtain ⟨hzt, hzs⟩ := hz
      show ((chartAt ℂ (τ y)).lift_openEmbedding hinl)
        (Sum.inl (τ ((chartAt ℂ y).symm z))) = z
      rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
      have hy' : (chartAt ℂ y).symm z ∈ (chartAt ℂ y).source := (chartAt ℂ y).map_target hzt
      have hz' : chartAt ℂ y ((chartAt ℂ y).symm z) = z := (chartAt ℂ y).right_inv hzt
      have h1 := (hchart y _ hy').2
      have h2 := (hchart (τ y) (τ ((chartAt ℂ y).symm z)) hzs).2
      rw [hqτ, hqτ] at h2
      rw [← h2, h1, hz']
    · refine s82bc_mdiffAt_of_charts τ' (Sum.inr i) hτ'c.continuousAt (fun z => -z)
        differentiableAt_id.neg ?_
      show ∀ᶠ z in 𝓝 (chartAt ℂ (Sum.inr i : Y ⊕ ι) (Sum.inr i)),
        chartAt ℂ (Sum.inr i : Y ⊕ ι) (τ' ((chartAt ℂ (Sum.inr i : Y ⊕ ι)).symm z)) = -z
      rw [hchr i]
      have hmem : Sum.inr i ∈ (Wend i).source := by rw [hsrc]; exact Or.inl rfl
      filter_upwards [(Wend i).open_target.mem_nhds ((Wend i).map_source hmem)] with z hz
      by_cases hz0 : z = 0
      · subst hz0
        rw [hsymm0]
        show Wend i (Sum.inr i) = -0
        rw [happ_r, neg_zero]
      · have hzb : z ∈ Metric.ball (0 : ℂ) (R i) := by rw [← htgt]; exact hz
        have hzt : z ∈ (W0 i).target := by
          rw [hW0t i]
          rw [Metric.mem_ball, dist_zero_right] at hzb
          exact ⟨norm_pos_iff.mpr hz0, hzb⟩
        rw [hsymm i z hzt]
        show Wend i (Sum.inl (τ ((W0 i).symm z))) = -z
        rw [happ_l, (hWτ i _ ((W0 i).map_target hzt)).2, (W0 i).right_inv hzt]
  have hpr_md : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Sum.elim ψ e) := by
    rintro (y | i)
    · refine s82bc_mdiffAt_of_charts (Sum.elim ψ e) (Sum.inl y) hprc.continuousAt id
        differentiableAt_id ?_
      show ∀ᶠ z in 𝓝 (chartAt ℂ (Sum.inl y : Y ⊕ ι) (Sum.inl y)),
        chartAt ℂ (ψ y) (Sum.elim ψ e ((chartAt ℂ (Sum.inl y : Y ⊕ ι)).symm z)) = id z
      rw [hchl y]
      have hpt : ((chartAt ℂ y).lift_openEmbedding hinl) (Sum.inl y) = chartAt ℂ y y :=
        OpenPartialHomeomorph.lift_openEmbedding_apply _ _
      rw [hpt]
      have hyt : chartAt ℂ y y ∈ (chartAt ℂ y).target :=
        (chartAt ℂ y).map_source (mem_chart_source ℂ y)
      filter_upwards [(chartAt ℂ y).open_target.mem_nhds hyt] with z hzt
      show chartAt ℂ ((q y : U) : X) ((q ((chartAt ℂ y).symm z) : U) : X) = z
      have hy' : (chartAt ℂ y).symm z ∈ (chartAt ℂ y).source := (chartAt ℂ y).map_target hzt
      have hz' : chartAt ℂ y ((chartAt ℂ y).symm z) = z := (chartAt ℂ y).right_inv hzt
      exact ((hchart y _ hy').2).trans hz'
    · have hmem : Sum.inr i ∈ (Wend i).source := by rw [hsrc]; exact Or.inl rfl
      have hcd : ContDiffOn ℂ ω ((E i).symm ≫ₕ chartAt ℂ (e i))
          ((E i).symm ≫ₕ chartAt ℂ (e i)).source :=
        ((s82bc_mem_groupoid_iff _).mp (IsManifold.compatible_of_mem_maximalAtlas (hEm i)
          (IsManifold.chart_mem_maximalAtlas (e i)))).1
      have hsymm0' : (E i).symm 0 = e i := by
        have := (E i).left_inv (hEsrc i)
        rwa [hEp i] at this
      have h0t : (0 : ℂ) ∈ (E i).target := hball i (Metric.mem_ball_self (hr i))
      have h0src : (0 : ℂ) ∈ ((E i).symm ≫ₕ chartAt ℂ (e i)).source :=
        ⟨h0t, by show (E i).symm 0 ∈ (chartAt ℂ (e i)).source; rw [hsymm0']; exact mem_chart_source ℂ _⟩
      have hdiff : DifferentiableAt ℂ ((E i).symm ≫ₕ chartAt ℂ (e i)) 0 :=
        (hcd.contDiffAt (((E i).symm ≫ₕ chartAt ℂ (e i)).open_source.mem_nhds h0src)).differentiableAt
          (by simp)
      refine s82bc_mdiffAt_of_charts (Sum.elim ψ e) (Sum.inr i) hprc.continuousAt
        (fun z => chartAt ℂ (e i) ((E i).symm (z ^ 2))) ?_ ?_
      · show DifferentiableAt ℂ (fun z : ℂ => chartAt ℂ (e i) ((E i).symm (z ^ 2)))
          (chartAt ℂ (Sum.inr i : Y ⊕ ι) (Sum.inr i))
        rw [hchr i, happ_r]
        have h2 : DifferentiableAt ℂ (fun z : ℂ => z ^ 2) 0 := (differentiableAt_id.pow 2)
        have h3 : DifferentiableAt ℂ (fun w : ℂ => chartAt ℂ (e i) ((E i).symm w))
            ((fun z : ℂ => z ^ 2) 0) := by
          have h0 : ((fun z : ℂ => z ^ 2) 0) = 0 := by norm_num
          rw [h0]; exact hdiff
        have h4 := DifferentiableAt.comp (g := fun w : ℂ => chartAt ℂ (e i) ((E i).symm w))
          (f := fun z : ℂ => z ^ 2) (0 : ℂ) h3 h2
        exact h4
      · show ∀ᶠ z in 𝓝 (chartAt ℂ (Sum.inr i : Y ⊕ ι) (Sum.inr i)),
          chartAt ℂ (e i) (Sum.elim ψ e ((chartAt ℂ (Sum.inr i : Y ⊕ ι)).symm z)) =
            chartAt ℂ (e i) ((E i).symm (z ^ 2))
        rw [hchr i]
        filter_upwards [(Wend i).open_target.mem_nhds ((Wend i).map_source hmem)] with z hz
        by_cases hz0 : z = 0
        · subst hz0
          rw [hsymm0]
          show chartAt ℂ (e i) (e i) = chartAt ℂ (e i) ((E i).symm ((0 : ℂ) ^ 2))
          rw [show ((0 : ℂ) ^ 2) = 0 by norm_num, hsymm0']
        · have hzb : z ∈ Metric.ball (0 : ℂ) (R i) := by rw [← htgt]; exact hz
          have hzt : z ∈ (W0 i).target := by
            rw [hW0t i]
            rw [Metric.mem_ball, dist_zero_right] at hzb
            exact ⟨norm_pos_iff.mpr hz0, hzb⟩
          rw [hsymm i z hzt]
          show chartAt ℂ (e i) (ψ ((W0 i).symm z)) = chartAt ℂ (e i) ((E i).symm (z ^ 2))
          rw [hpr_eq i _ ((W0 i).map_target hzt), (W0 i).right_inv hzt]
  refine ⟨Y ⊕ ι, τT, csT, hT2, hconn, hcpt, hmanT, Sum.elim ψ e, hpr_md, ?_, ?_, ?_, ?_⟩
  · rintro x
    by_cases hx : x ∈ U
    · obtain ⟨y, hy⟩ := hqs ⟨x, hx⟩
      exact ⟨Sum.inl y, by show ((q y : U) : X) = x; rw [hy]⟩
    · have : x ∈ range e := by rw [hrange]; exact hx
      obtain ⟨i, rfl⟩ := this
      exact ⟨Sum.inr i, rfl⟩
  · intro x hx
    have : Sum.elim ψ e ⁻¹' {x} = Sum.inl '' (q ⁻¹' {⟨x, hx⟩}) := by
      ext t
      rcases t with y | i
      · constructor
        · intro h
          refine ⟨y, ?_, rfl⟩
          exact Subtype.ext h
        · rintro ⟨y', hy', hyy⟩
          rw [Sum.inl_injective hyy] at hy'
          exact congrArg Subtype.val hy'
      · constructor
        · intro h
          exact absurd (by rw [show e i = x from h]; exact hx) (heU i)
        · rintro ⟨y', _, h⟩
          exact absurd h (by simp)
    rw [this, Set.ncard_image_of_injective _ Sum.inl_injective, hfib]
  · intro x hx
    have hxr : x ∈ range e := by rw [hrange]; exact hx
    obtain ⟨i₀, rfl⟩ := hxr
    have : Sum.elim ψ e ⁻¹' {e i₀} = {Sum.inr i₀} := by
      ext t
      rcases t with y | i
      · constructor
        · intro h
          exact absurd (show ψ y = e i₀ from h) (hne y i₀)
        · intro h; exact absurd h (by simp)
      · constructor
        · intro h
          exact congrArg Sum.inr (he h)
        · intro h
          exact congrArg e (Sum.inr_injective h)
    rw [this, Set.ncard_singleton]
  · refine ⟨hom, ⟨hτ'md, τ', hτ'md, hτ'2, hτ'2⟩, hτ'2, hprτ, ?_⟩
    rintro (y | i)
    · constructor
      · intro h
        exact absurd (Sum.inl_injective h) (hfree y)
      · intro h
        exact absurd (hψU y) h
    · exact ⟨fun _ => heU i, fun _ => rfl⟩

end MainTheorem

end LiZhongQC
