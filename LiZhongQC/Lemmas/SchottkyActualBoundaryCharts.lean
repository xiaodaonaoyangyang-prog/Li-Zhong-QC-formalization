import LiZhongQC.Lemmas.FiniteTypeUniqueness
import LiZhongQC.Lemmas.SchottkyDoubleCarrier
import LiZhongQC.Lemmas.SchottkyReflectionCoordinates
import LiZhongQC.Lemmas.SchottkyHalfPlaneGluing

section SchottkySurfaceBoundaryGeometryBlock

/-! Actual surface-chart geometry of a hole in the shared Schottky core.
The chart and Jordan domain are extracted from F.disc, not assumed collars. -/

open Complex Set Topology

noncomputable section
namespace LiZhongQC

/-- A chart presenting an actual closed Jordan disc also presents its
interior and frontier. Regular openness of the Jordan domain is essential. -/
theorem s78ra_disc_chart_loci {X : Type*} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X ℂ) {D : Set X} {J : Set ℂ}
    (hDs : D ⊆ c.source) (hDJ : c '' D = closure J)
    (hJ : IsJordanDomain J) (hb : Bornology.IsBounded J) :
    c.IsImage D (closure J) ∧ c.IsImage (interior D) J ∧
      c.IsImage (frontier D) (frontier J) := by
  have himage : c.IsImage D (closure J) := by
    intro x hx
    constructor
    · intro h
      obtain ⟨y, hy, he⟩ := hDJ.symm ▸ h
      exact c.injOn (hDs hy) hx he ▸ hy
    · intro h
      rw [← hDJ]
      exact mem_image_of_mem c h
  have hcurve : IsJordanCurve (toExt (frontier J)) := by
    rw [← frontier_toExt_of_isBounded' hb hJ.1]
    exact hJ.2.2
  have hreg : interior (closure J) = J := by
    apply subset_antisymm
    · exact interior_closure_subset_of_isJordanCurve_frontier hJ.1 hJ.2.1 hb hcurve
    · calc
        J = interior J := hJ.1.interior_eq.symm
        _ ⊆ interior (closure J) := interior_mono subset_closure
  have hi : c.IsImage (interior D) J := by
    simpa only [hreg] using himage.interior
  have hf : c.IsImage (frontier D) (frontier J) := by
    simpa only [frontier, closure_closure, hreg, hJ.1.interior_eq] using himage.frontier
  exact ⟨himage, hi, hf⟩

/-- At every actual hole-boundary point, the shared core is locally the
closed exterior of the Jordan domain in F.disc's surface chart. The open
neighborhood excludes punctures and every other hole. -/
theorem s78ra_actual_hole_chart_neighborhood
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) (j : Fin m) (p : F.X.carrier)
    (hp : p ∈ frontier (F.D j)) :
    ∃ (x : F.X.carrier) (J : Set ℂ) (N : Set F.X.carrier),
      IsJordanDomain J ∧ Bornology.IsBounded J ∧
      IsOpen N ∧ p ∈ N ∧ N ⊆ (chartAt ℂ x).source ∧
      closure J ⊆ (chartAt ℂ x).target ∧
      (chartAt ℂ x) '' F.D j = closure J ∧
      (∀ y ∈ N, y ∉ (↑F.P : Set F.X.carrier)) ∧
      (∀ y ∈ N, ∀ k : Fin m, k ≠ j → y ∉ F.D k) ∧
      (∀ y ∈ N, y ∈ s31dt_coreSet F ↔ (chartAt ℂ x) y ∉ J) ∧
      (∀ y : s31dt_Core F, y.val ∈ N →
        (y ∈ s31dt_boundary F ↔ (chartAt ℂ x) y.val ∈ frontier J)) := by
  obtain ⟨x, hDs, J, hJ, hb, hJt, hDJ, _⟩ := F.disc j
  let c := chartAt ℂ x
  obtain ⟨hDloc, hIloc, hFloc⟩ := s78ra_disc_chart_loci c hDs hDJ hJ hb
  have hclosed : ∀ k, IsClosed (F.D k) :=
    fun k => (s31eg_disc_compact (F.disc k)).isClosed
  have hpD : p ∈ F.D j := (hclosed j).closure_eq ▸ hp.1
  let A : Set F.X.carrier := (↑F.P : Set F.X.carrier) ∪
    ⋃ k : {k : Fin m // k ≠ j}, F.D k.val
  have hAc : IsClosed A := F.P.finite_toSet.isClosed.union
    (isClosed_iUnion_of_finite (fun k : {k : Fin m // k ≠ j} => hclosed k.val))
  have hpA : p ∉ A := by
    rintro (hP | hother)
    · exact Set.disjoint_left.1 (F.disjoint_P j) hpD hP
    · obtain ⟨k, hk⟩ := mem_iUnion.1 hother
      exact Set.disjoint_left.1 (F.disjoint k.property) hk hpD
  let N : Set F.X.carrier := c.source ∩ Aᶜ
  have hNo : IsOpen N := c.open_source.inter hAc.isOpen_compl
  have hpN : p ∈ N := ⟨hDs hpD, hpA⟩
  have hNP : ∀ y ∈ N, y ∉ (↑F.P : Set F.X.carrier) :=
    fun y hy hP => hy.2 (Or.inl hP)
  have hND : ∀ y ∈ N, ∀ k : Fin m, k ≠ j → y ∉ F.D k := by
    intro y hy k hkj hk
    exact hy.2 (Or.inr (mem_iUnion.2 ⟨⟨k, hkj⟩, hk⟩))
  refine ⟨x, J, N, hJ, hb, hNo, hpN, inter_subset_left,
    hJt, hDJ, hNP, hND, ?_, ?_⟩
  · intro y hy
    have hlocal : c y ∈ J ↔ y ∈ interior (F.D j) := hIloc hy.1
    constructor
    · intro hcore hJmem
      exact hcore (mem_iUnion.2 ⟨j, hlocal.1 hJmem⟩)
    · intro hnot hdeleted
      obtain ⟨k, hk⟩ := mem_iUnion.1 hdeleted
      by_cases hkj : k = j
      · subst k
        exact hnot (hlocal.2 hk)
      · exact hND y hy k hkj (interior_subset hk)
  · intro y hy
    constructor
    · intro hboundary
      obtain ⟨k, hk⟩ := hboundary
      have hkj : k = j := by
        by_contra hne
        exact hND y.val hy k hne ((hclosed k).closure_eq ▸ hk.1)
      subst k
      exact (hFloc hy.1).2 hk
    · intro hboundary
      exact ⟨j, (hFloc hy.1).1 hboundary⟩

end LiZhongQC
end -- close original anonymous noncomputable section
end SchottkySurfaceBoundaryGeometryBlock

section SchottkyCoreExteriorTransportBlock

/-! Transport the actual core, through its original surface chart, into
the closed exterior used by the analytic uniformizer. -/

open Complex Set Topology

noncomputable section
namespace LiZhongQC

/-- A surface chart that identifies core membership with the closed Jordan
exterior induces a genuine relative homeomorphism, with the original chart
as its exact coordinate function. -/
theorem s78ra_core_exterior_transport
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) (c : OpenPartialHomeomorph F.X.carrier ℂ)
    (J : Set ℂ) (N : Set F.X.carrier) (hNo : IsOpen N) (hNs : N ⊆ c.source)
    (hcore : ∀ y ∈ N, y ∈ s31dt_coreSet F ↔ c y ∉ J) :
    IsOpen {z : ↥((toExt J)ᶜ) | z.val ∈ toExt (c '' N)} ∧
      ∃ E : {y : s31dt_Core F | y.val ∈ N} ≃ₜ
        {z : ↥((toExt J)ᶜ) | z.val ∈ toExt (c '' N)},
        ∀ y, (E y).val.val = (c y.val.val : ExtPlane) := by
  have htarget : IsOpen {z : ↥((toExt J)ᶜ) | z.val ∈ toExt (c '' N)} :=
    (isOpen_toExt_iff.2 (c.isOpen_image_of_subset_source hNo hNs)).preimage
      continuous_subtype_val
  let A : Set F.X.carrier := N ∩ s31dt_coreSet F
  let B : Set ℂ := (c '' N) ∩ Jᶜ
  have hAB : c '' A = B := by
    apply subset_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨mem_image_of_mem c hy.1, (hcore y hy.1).1 hy.2⟩
    · rintro z ⟨⟨y, hy, rfl⟩, hz⟩
      exact ⟨y, ⟨hy, (hcore y hy).2 hz⟩, rfl⟩
  let E₀ : ↥A ≃ₜ ↥B := c.toPartialHomeomorph.homeomorphOfImageSubsetSource
    (fun y hy => hNs hy.1) hAB
  let E₁ : {y : s31dt_Core F | y.val ∈ N} ≃ₜ ↥A := {
    toFun := fun y => ⟨y.val.val, ⟨y.property, y.val.property⟩⟩
    invFun := fun y => ⟨⟨y.val, y.property.2⟩, y.property.1⟩
    left_inv := by intro y; rfl
    right_inv := by intro y; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hBext : toExt B = (toExt J)ᶜ ∩ toExt (c '' N) := by
    apply subset_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨fun h => hz.2 (coe_mem_toExt_iff.1 h),
        coe_mem_toExt_iff.2 hz.1⟩
    · rintro p ⟨hpJ, z, hz, rfl⟩
      exact ⟨z, ⟨hz, fun h => hpJ (coe_mem_toExt_iff.2 h)⟩, rfl⟩
  let E₂ : ↥B ≃ₜ ↥(toExt B) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage B
  have hBmem : ∀ z : ↥(toExt B),
      z.val ∈ (toExt J)ᶜ ∧ z.val ∈ toExt (c '' N) := by
    intro z
    change z.val ∈ (toExt J)ᶜ ∩ toExt (c '' N)
    rw [← hBext]
    exact z.property
  let E₃ : ↥(toExt B) ≃ₜ {z : ↥((toExt J)ᶜ) | z.val ∈ toExt (c '' N)} := {
    toFun := fun z => ⟨⟨z.val, (hBmem z).1⟩, (hBmem z).2⟩
    invFun := fun z => ⟨z.val.val, by
      rw [hBext]
      exact ⟨z.val.property, z.property⟩⟩
    left_inv := by intro z; rfl
    right_inv := by intro z; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  exact ⟨htarget, E₁.trans (E₀.trans (E₂.trans E₃)), fun _ => rfl⟩

/-- At every actual hole-boundary point, produce the finite surface-chart
transport to a relatively open part of the spherical closed exterior.
All coordinate and membership data come from F, with no assumed collar. -/
theorem s78ra_actual_core_exterior_model
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) (j : Fin m) (p : F.X.carrier)
    (hp : p ∈ frontier (F.D j)) :
    ∃ (x : F.X.carrier) (J : Set ℂ) (N : Set F.X.carrier),
      IsJordanDomain J ∧ Bornology.IsBounded J ∧ IsOpen N ∧ p ∈ N ∧
      N ⊆ (chartAt ℂ x).source ∧
      (∀ y : s31dt_Core F, y.val ∈ N →
        (y ∈ s31dt_boundary F ↔ (chartAt ℂ x) y.val ∈ frontier J)) ∧
      IsOpen {z : ↥((toExt J)ᶜ) | z.val ∈ toExt ((chartAt ℂ x) '' N)} ∧
      ∃ E : {y : s31dt_Core F | y.val ∈ N} ≃ₜ
        {z : ↥((toExt J)ᶜ) | z.val ∈ toExt ((chartAt ℂ x) '' N)},
        ∀ y, (E y).val.val = ((chartAt ℂ x) y.val.val : ExtPlane) := by
  obtain ⟨x, J, N, hJ, hb, hN, hpN, hNs, _, _, _, _, hcore, hboundary⟩ :=
    s78ra_actual_hole_chart_neighborhood F j p hp
  obtain ⟨hO, E, hE⟩ := s78ra_core_exterior_transport F (chartAt ℂ x) J N hN hNs hcore
  exact ⟨x, J, N, hJ, hb, hN, hpN, hNs, hboundary, hO, E, hE⟩

end LiZhongQC
end -- close original anonymous noncomputable section
end SchottkyCoreExteriorTransportBlock

section SchottkyHalfDiscRestrictionBlock

/-! Restrict a genuine relative half-plane coordinate inside a prescribed
open neighborhood. This is the step excluding infinity and other holes. -/

open Complex Set Metric Topology

noncomputable section
namespace LiZhongQC

/-- A relative half-plane chart centered at p can be restricted inside any
prescribed open neighborhood of p, with an actual half-disc as its target
and without changing its coordinate function. -/
theorem s78ra_halfplane_restrict_halfdisc
    {A : Type*} [TopologicalSpace A]
    (h : A ≃ₜ {z : ℂ | 0 ≤ z.im}) (p : A) (hp : (h p).val = 0)
    (U : Set A) (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ (r : ℝ) (V : Set A), 0 < r ∧ IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
      ∃ e : ↥V ≃ₜ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im},
        ∀ x : ↥V, (e x).val = (h x.val).val := by
  have hO : IsOpen (h '' U) := h.isOpenMap U hU
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO (h p) ⟨p, hpU, rfl⟩
  let V : Set A := {x | ‖(h x).val‖ < r}
  have hV : IsOpen V :=
    isOpen_lt ((continuous_subtype_val.comp h.continuous).norm) continuous_const
  have hpV : p ∈ V := by
    change ‖(h p).val‖ < r
    rwa [hp, norm_zero]
  have hVU : V ⊆ U := by
    intro x hx
    have hxball : h x ∈ ball (h p) r := by
      apply mem_ball.2
      change dist (h x).val (h p).val < r
      rw [hp, dist_zero_right]
      exact hx
    obtain ⟨y, hy, he⟩ := hball hxball
    exact h.injective he ▸ hy
  let E : ↥V ≃ₜ {z : {z : ℂ | 0 ≤ z.im} | ‖z.val‖ < r} :=
    h.subtype (fun _ => Iff.rfl)
  let K : {z : {z : ℂ | 0 ≤ z.im} | ‖z.val‖ < r} ≃ₜ
      {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} := {
    toFun := fun z => ⟨z.val.val, ⟨z.property, z.val.property⟩⟩
    invFun := fun z => ⟨⟨z.val, z.property.2⟩, z.property.1⟩
    left_inv := by intro z; rfl
    right_inv := by intro z; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  exact ⟨r, V, hr, hV, hpV, hVU, E.trans K, fun _ => rfl⟩

end LiZhongQC
end -- close original anonymous noncomputable section
end SchottkyHalfDiscRestrictionBlock

section SchottkyRelativeHalfChartBlock

open Complex Set Metric Topology

noncomputable section
namespace LiZhongQC

/-- Pull a relative half-plane chart through an actual homeomorphism onto
an open subspace, restricting to a half-disc without changing its formula. -/
theorem s78ra_relative_halfchart_transfer
    {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (O V : Set X) (hO : IsOpen O) (hV : IsOpen V)
    (E : A ≃ₜ ↥O) (H : ↥V ≃ₜ {z : ℂ | 0 ≤ z.im})
    (p : A) (hpV : (E p).val ∈ V)
    (hp0 : (H ⟨(E p).val, hpV⟩).val = 0) :
    ∃ (r : ℝ) (W : Set A), 0 < r ∧ IsOpen W ∧ p ∈ W ∧
      ∃ K : ↥W ≃ₜ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im},
        (∀ y : ↥W, ∃ hy : (E y.val).val ∈ V,
          (K y).val = (H ⟨(E y.val).val, hy⟩).val) ∧
        (∀ hpW : p ∈ W, (K ⟨p, hpW⟩).val = 0) := by
  let pV : ↥V := ⟨(E p).val, hpV⟩
  let U : Set ↥V := {z | z.val ∈ O}
  have hU : IsOpen U := hO.preimage continuous_subtype_val
  have hpU : pV ∈ U := (E p).property
  obtain ⟨r, hr, hro, hrr, hpR, hRU, H₀, hH₀⟩ :=
    s78ra_halfplane_restrict_halfdisc H pV hp0 U hU hpU
  let val₂ : ↥hr → X := fun z => z.val.val
  have hv₂ : Topology.IsOpenEmbedding val₂ :=
    hV.isOpenEmbedding_subtypeVal.comp hrr.isOpenEmbedding_subtypeVal
  have hm : ∀ z : ↥hr, val₂ z ∈ O := fun z => hRU z.property
  let j : ↥hr → ↥O := fun z => ⟨val₂ z, hm z⟩
  have hj : Topology.IsOpenEmbedding j :=
    (Topology.isOpenEmbedding_iff_isEmbedding_isOpenMap).2
      ⟨hv₂.isEmbedding.codRestrict O hm, hv₂.isOpenMap.subtype_mk hm⟩
  let k : ↥hr → A := E.symm ∘ j
  have hk : Topology.IsOpenEmbedding k := E.symm.isOpenEmbedding.comp hj
  let W : Set A := range k
  let K₀ : ↥hr ≃ₜ ↥W := hk.isEmbedding.toHomeomorph
  let K : ↥W ≃ₜ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} := K₀.symm.trans H₀
  have hpW : p ∈ W := by
    refine ⟨⟨pV, hpR⟩, ?_⟩
    change E.symm (E p) = p
    exact E.symm_apply_apply p
  have hformula : ∀ y : ↥W, ∃ hy : (E y.val).val ∈ V,
      (K y).val = (H ⟨(E y.val).val, hy⟩).val := by
    intro y
    let z : ↥hr := K₀.symm y
    have hkz : k z = y.val := congrArg Subtype.val (K₀.apply_symm_apply y)
    have hEz : (E y.val).val = z.val.val := by
      rw [← hkz]
      change (E (E.symm (j z))).val = z.val.val
      rw [E.apply_symm_apply]
    have hy : (E y.val).val ∈ V := hEz.symm ▸ z.val.property
    refine ⟨hy, ?_⟩
    change (H₀ z).val = _
    rw [hH₀ z]
    have harg : z.val = (⟨(E y.val).val, hy⟩ : ↥V) := Subtype.ext hEz.symm
    exact congrArg (fun w : ↥V => (H w).val) harg
  refine ⟨r, W, hro, hk.isOpen_range, hpW, K, hformula, ?_⟩
  intro hpW'
  obtain ⟨hy, he⟩ := hformula ⟨p, hpW'⟩
  exact he.trans hp0

end LiZhongQC
end -- close original anonymous noncomputable section
end SchottkyRelativeHalfChartBlock

section SchottkyFixedHoleModelBlock

/-! Choose the original chart and exterior uniformizer once per hole,
before any boundary point or Cayley anchor is chosen. -/

open Complex Set Metric Topology

noncomputable section
namespace LiZhongQC

/-- One open support for the entire actual closed hole, avoiding all other
holes and punctures. Its preferred chart and Jordan domain are fixed once. -/
theorem s78ra_fixed_hole_support
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) (j : Fin m) :
    ∃ (x : F.X.carrier) (J : Set ℂ) (N : Set F.X.carrier),
      IsJordanDomain J ∧ Bornology.IsBounded J ∧ IsOpen N ∧ F.D j ⊆ N ∧
      N ⊆ (chartAt ℂ x).source ∧ closure J ⊆ (chartAt ℂ x).target ∧
      (chartAt ℂ x) '' F.D j = closure J ∧
      (∀ y ∈ N, y ∉ (↑F.P : Set F.X.carrier)) ∧
      (∀ y ∈ N, ∀ k : Fin m, k ≠ j → y ∉ F.D k) ∧
      (∀ y ∈ N, y ∈ s31dt_coreSet F ↔ (chartAt ℂ x) y ∉ J) ∧
      (∀ y : s31dt_Core F, y.val ∈ N →
        (y ∈ s31dt_boundary F ↔ (chartAt ℂ x) y.val ∈ frontier J)) := by
  obtain ⟨x, hDs, J, hJ, hb, hJt, hDJ, _⟩ := F.disc j
  let c := chartAt ℂ x
  obtain ⟨hDloc, hIloc, hFloc⟩ := s78ra_disc_chart_loci c hDs hDJ hJ hb
  have hclosed : ∀ k, IsClosed (F.D k) :=
    fun k => (s31eg_disc_compact (F.disc k)).isClosed
  let A : Set F.X.carrier := (↑F.P : Set F.X.carrier) ∪
    ⋃ k : {k : Fin m // k ≠ j}, F.D k.val
  have hAc : IsClosed A := F.P.finite_toSet.isClosed.union
    (isClosed_iUnion_of_finite (fun k : {k : Fin m // k ≠ j} => hclosed k.val))
  let N : Set F.X.carrier := c.source ∩ Aᶜ
  have hNo : IsOpen N := c.open_source.inter hAc.isOpen_compl
  have hDN : F.D j ⊆ N := by
    intro y hy
    refine ⟨hDs hy, ?_⟩
    rintro (hP | hother)
    · exact Set.disjoint_left.1 (F.disjoint_P j) hy hP
    · obtain ⟨k, hk⟩ := mem_iUnion.1 hother
      exact Set.disjoint_left.1 (F.disjoint k.property) hk hy
  have hNP : ∀ y ∈ N, y ∉ (↑F.P : Set F.X.carrier) :=
    fun y hy hP => hy.2 (Or.inl hP)
  have hND : ∀ y ∈ N, ∀ k : Fin m, k ≠ j → y ∉ F.D k := by
    intro y hy k hkj hk
    exact hy.2 (Or.inr (mem_iUnion.2 ⟨⟨k, hkj⟩, hk⟩))
  refine ⟨x, J, N, hJ, hb, hNo, hDN, inter_subset_left,
    hJt, hDJ, hNP, hND, ?_, ?_⟩
  · intro y hy
    have hlocal : c y ∈ J ↔ y ∈ interior (F.D j) := hIloc hy.1
    constructor
    · intro hcore hJmem
      exact hcore (mem_iUnion.2 ⟨j, hlocal.1 hJmem⟩)
    · intro hnot hdeleted
      obtain ⟨k, hk⟩ := mem_iUnion.1 hdeleted
      by_cases hkj : k = j
      · subst k
        exact hnot (hlocal.2 hk)
      · exact hND y hy k hkj (interior_subset hk)
  · intro y hy
    constructor
    · intro hboundary
      obtain ⟨k, hk⟩ := hboundary
      have hkj : k = j := by
        by_contra hne
        exact hND y.val hy k hne ((hclosed k).closure_eq ▸ hk.1)
      subst k
      exact (hFloc hy.1).2 hk
    · intro hboundary
      exact ⟨j, (hFloc hy.1).1 hboundary⟩

/-- Fix an actual conformal exterior coordinate for one hole, independently
of the later boundary point. Its full closed-disc coordinate is retained so
different Cayley anchors act on this same map. -/
theorem s78ra_fixed_hole_uniformizer
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) (j : Fin m) :
    ∃ (x : F.X.carrier) (J : Set ℂ) (N : Set F.X.carrier),
      IsJordanDomain J ∧ Bornology.IsBounded J ∧ IsOpen N ∧ F.D j ⊆ N ∧
      N ⊆ (chartAt ℂ x).source ∧ closure J ⊆ (chartAt ℂ x).target ∧
      (chartAt ℂ x) '' F.D j = closure J ∧
      (∀ y ∈ N, y ∉ (↑F.P : Set F.X.carrier)) ∧
      (∀ y ∈ N, ∀ k : Fin m, k ≠ j → y ∉ F.D k) ∧
      (∀ y ∈ N, y ∈ s31dt_coreSet F ↔ (chartAt ℂ x) y ∉ J) ∧
      (∀ y : s31dt_Core F, y.val ∈ N →
        (y ∈ s31dt_boundary F ↔ (chartAt ℂ x) y.val ∈ frontier J)) ∧
      ∃ (f : ℂ → ℂ) (e : ↥((toExt J)ᶜ) ≃ₜ closedBall (0 : ℂ) 1),
        DifferentiableOn ℂ f (closure J)ᶜ ∧ InjOn f (closure J)ᶜ ∧
        (∀ z ∈ (closure J)ᶜ, ∀ hz : (z : ExtPlane) ∈ (toExt J)ᶜ,
          (e ⟨(z : ExtPlane), hz⟩).val = f z) ∧
        (∀ z : ↥((toExt J)ᶜ),
          ‖(e z).val‖ < 1 ↔ z.val ∈ (closure (toExt J))ᶜ) ∧
        (∀ z : ↥((toExt J)ᶜ),
          ‖(e z).val‖ = 1 ↔ z.val ∈ frontier (toExt J)) := by
  obtain ⟨x, J, N, hJ, hb, hN, hDN, hNs, hJt, hDJ, hNP, hND, hcore, hboundary⟩ :=
    s78ra_fixed_hole_support F j
  obtain ⟨f, e, hf, hfi, hef, hei, heb⟩ := s78ra_exterior_closed_coordinate hJ hb
  exact ⟨x, J, N, hJ, hb, hN, hDN, hNs, hJt, hDJ, hNP, hND,
    hcore, hboundary, f, e, hf, hfi, hef, hei, heb⟩

end LiZhongQC
end -- close original anonymous noncomputable section
end SchottkyFixedHoleModelBlock

section SchottkyCoreHalfDiscBlock

open Complex Set Metric Topology
open scoped ComplexConjugate

noncomputable section
namespace LiZhongQC

/-- Restrict one fixed closed-exterior coordinate to a genuine half-disc
chart of the actual core. The universal formula, including the seam, is
the Cayley transform of that same fixed coordinate. -/
theorem s78ra_core_halfdisc_from_closed_coordinate
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) (x : F.X.carrier)
    (J : Set ℂ) (hJ : IsJordanDomain J) (hb : Bornology.IsBounded J)
    (N : Set F.X.carrier) (hN : IsOpen N) (hNs : N ⊆ (chartAt ℂ x).source)
    (hcore : ∀ y ∈ N, y ∈ s31dt_coreSet F ↔ (chartAt ℂ x) y ∉ J)
    (hboundary : ∀ y : s31dt_Core F, y.val ∈ N →
      (y ∈ s31dt_boundary F ↔ (chartAt ℂ x) y.val ∈ frontier J))
    (e : ↥((toExt J)ᶜ) ≃ₜ closedBall (0 : ℂ) 1)
    (heb : ∀ z : ↥((toExt J)ᶜ), ‖(e z).val‖ = 1 ↔ z.val ∈ frontier (toExt J))
    (p : s31dt_Core F) (hpN : p.val ∈ N) (hpB : p ∈ s31dt_boundary F) :
    ∃ (r : ℝ) (U : Set (s31dt_Core F)) (a : ℂ),
      0 < r ∧ IsOpen U ∧ p ∈ U ∧ U ⊆ {y | y.val ∈ N} ∧ ‖a‖ = 1 ∧
      ∃ K : ↥U ≃ₜ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im},
        (∀ hpU : p ∈ U, (K ⟨p, hpU⟩).val = 0) ∧
        (∀ y : ↥U, y.val ∈ s31dt_boundary F ↔ (K y).val.im = 0) ∧
        (∀ y : ↥U, ∃ hy : ((chartAt ℂ x) y.val.val : ExtPlane) ∈ (toExt J)ᶜ,
          (K y).val = I * (a - (e ⟨((chartAt ℂ x) y.val.val : ExtPlane), hy⟩).val) /
            (a + (e ⟨((chartAt ℂ x) y.val.val : ExtPlane), hy⟩).val)) := by
  let c := chartAt ℂ x
  let A : Set (s31dt_Core F) := {y | y.val ∈ N}
  let O : Set ↥((toExt J)ᶜ) := {z | z.val ∈ toExt (c '' N)}
  have hA : IsOpen A := hN.preimage continuous_subtype_val
  obtain ⟨hO, E, hE⟩ := s78ra_core_exterior_transport F c J N hN hNs hcore
  let pA : ↥A := ⟨p, hpN⟩
  let q : ↥((toExt J)ᶜ) := (E pA).val
  have hqfr : q.val ∈ frontier (toExt J) := by
    change (E pA).val.val ∈ frontier (toExt J)
    rw [hE pA, frontier_toExt_of_isBounded' hb hJ.1]
    exact coe_mem_toExt_iff.2 ((hboundary p hpN).1 hpB)
  have hqe : ‖(e q).val‖ = 1 := (heb q).2 hqfr
  obtain ⟨V, hV, hqV, H, hH, hHp, _⟩ := s78ra_closed_coordinate_halfchart e q hqe
  obtain ⟨r, W, hr, hW, hpW, K₁, hK₁, _⟩ :=
    s78ra_relative_halfchart_transfer O V hO hV E H pA hqV (hHp hqV)
  let k : ↥W → s31dt_Core F := fun z => z.val.val
  have hk : Topology.IsOpenEmbedding k :=
    hA.isOpenEmbedding_subtypeVal.comp hW.isOpenEmbedding_subtypeVal
  let U : Set (s31dt_Core F) := range k
  let E₀ : ↥W ≃ₜ ↥U := hk.isEmbedding.toHomeomorph
  let K : ↥U ≃ₜ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} := E₀.symm.trans K₁
  let a : ℂ := (e q).val
  have hpU : p ∈ U := ⟨⟨pA, hpW⟩, rfl⟩
  have hUN : U ⊆ A := by
    rintro y ⟨z, rfl⟩
    exact z.val.property
  have hformula : ∀ y : ↥U, ∃ hy : (c y.val.val : ExtPlane) ∈ (toExt J)ᶜ,
      (K y).val = I * (a - (e ⟨(c y.val.val : ExtPlane), hy⟩).val) /
        (a + (e ⟨(c y.val.val : ExtPlane), hy⟩).val) := by
    intro y
    let z : ↥W := E₀.symm y
    have hzy : z.val.val = y.val := congrArg Subtype.val (E₀.apply_symm_apply y)
    have hEz : (E z.val).val.val = (c y.val.val : ExtPlane) := by
      rw [hE z.val, hzy]
    have hy : (c y.val.val : ExtPlane) ∈ (toExt J)ᶜ :=
      hEz ▸ (E z.val).val.property
    have hpoint : (E z.val).val = (⟨(c y.val.val : ExtPlane), hy⟩ : ↥((toExt J)ᶜ)) :=
      Subtype.ext hEz
    obtain ⟨hzV, hzformula⟩ := hK₁ z
    refine ⟨hy, ?_⟩
    change (K₁ z).val = _
    rw [hzformula, hH ⟨(E z.val).val, hzV⟩, hpoint]
  have hbnd : ∀ y : ↥U, y.val ∈ s31dt_boundary F ↔ (K y).val.im = 0 := by
    intro y
    obtain ⟨hy, hfy⟩ := hformula y
    let t : ↥((toExt J)ᶜ) := ⟨(c y.val.val : ExtPlane), hy⟩
    have htb : ‖(e t).val‖ = 1 ↔ y.val ∈ s31dt_boundary F := by
      rw [heb t, frontier_toExt_of_isBounded' hb hJ.1]
      change ((c y.val.val : ExtPlane) ∈ toExt (frontier J)) ↔ _
      rw [coe_mem_toExt_iff]
      exact (hboundary y.val (hUN y.property)).symm
    constructor
    · intro hyB
      rw [hfy]
      exact s78ra_cayley_real hqe (htb.2 hyB)
    · intro hy0
      by_contra hyB
      have hne : ‖(e t).val‖ ≠ 1 := fun he => hyB (htb.1 he)
      have hle : ‖(e t).val‖ ≤ 1 := mem_closedBall_zero_iff.1 (e t).property
      have hlt : ‖(e t).val‖ < 1 := lt_of_le_of_ne hle hne
      have hpos := (s78ra_cayley_upper hqe hlt).2
      rw [hfy] at hy0
      change 0 < (I * (a - (e t).val) / (a + (e t).val)).im at hpos
      linarith
  refine ⟨r, U, a, hr, hk.isOpen_range, hpU, hUN, hqe, K, ?_, hbnd, hformula⟩
  intro hpU'
  obtain ⟨hy, hfy⟩ := hformula ⟨p, hpU'⟩
  have hpoint : (⟨(c p.val : ExtPlane), hy⟩ : ↥((toExt J)ᶜ)) = q :=
    Subtype.ext (hE pA).symm
  rw [hfy, hpoint]
  exact s78ra_cayley_center a

end LiZhongQC
end -- close original anonymous noncomputable section
end SchottkyCoreHalfDiscBlock

section SchottkyHalfDiscGluingBlock

/-! Restrict the already constructed fold to an open disc. This produces
actual quotient boundary charts with exactly the original half-disc formula. -/

open Complex Set Metric Topology
open scoped ComplexConjugate

noncomputable section
namespace LiZhongQC

/-- The two-half-disc fold is the open-target restriction of the proved
two-half-plane quotient map. -/
theorem s78ra_halfdisc_fold_quotient (r : ℝ) :
    IsQuotientMap (fun x : Bool × {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} =>
      (⟨if x.1 then conj x.2.val else x.2.val, by
        rcases x with ⟨b, z⟩
        cases b <;> simpa [mem_ball_zero_iff] using z.property.1⟩ : ball (0 : ℂ) r)) := by
  let H := {z : ℂ | 0 ≤ z.im}
  let B := {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im}
  let f : Bool × H → ℂ := fun x => if x.1 then conj x.2.val else x.2.val
  have hmem : ∀ x : Bool × H, f x ∈ ball (0 : ℂ) r ↔ ‖x.2.val‖ < r := by
    intro x
    rcases x with ⟨b, z⟩
    cases b <;> simp [f, mem_ball_zero_iff]
  let R : Bool × B ≃ₜ ↥(f ⁻¹' ball (0 : ℂ) r) := {
    toFun := fun x => ⟨(x.1, ⟨x.2.val, x.2.property.2⟩),
      (hmem _).2 x.2.property.1⟩
    invFun := fun x => (x.val.1,
      ⟨x.val.2.val, ⟨(hmem x.val).1 x.property, x.val.2.property⟩⟩)
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  exact (s78ra_halfplane_fold_quotient.restrictPreimage_isOpen isOpen_ball).comp
    R.isQuotientMap

/-- A genuine half-disc coordinate on an open part of the actual core
sews to a chart on s31dt_Double F with target precisely ball 0 r. -/
theorem s78ra_actual_quotient_halfdisc_chart
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {r : ℝ} (hr : 0 < r)
    (V : Set (s31dt_Core F)) (hV : IsOpen V)
    (h : ↥V ≃ₜ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hboundary : ∀ x : ↥V, x.val ∈ s31dt_boundary F ↔ (h x).val.im = 0) :
    ∃ u : OpenPartialHomeomorph (s31dt_Double F) ℂ,
      u.source = s31dt_project F ⁻¹' V ∧ u.target = ball 0 r ∧
      (∀ b (x : ↥V), u (s31dt_side F b x.val) =
        if b then conj (h x).val else (h x).val) ∧
      (∀ q ∈ u.source, s31dt_flip F q ∈ u.source ∧
        u (s31dt_flip F q) = conj (u q)) := by
  let W : Set (s31dt_Double F) := s31dt_project F ⁻¹' V
  have hW : IsOpen W := hV.preimage (s31dt_continuous_project F)
  let R : Bool × ↥V ≃ₜ ↥(s31dt_mk F ⁻¹' W) := {
    toFun := fun x => ⟨(x.1, x.2.val), x.2.property⟩
    invFun := fun x => (x.val.1, ⟨x.val.2, x.property⟩)
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let q : Bool × ↥V → ↥W := fun x => ⟨s31dt_side F x.1 x.2.val, x.2.property⟩
  have hmk : IsQuotientMap (s31dt_mk F) := isQuotientMap_quotient_mk'
  have hq : IsQuotientMap q := (hmk.restrictPreimage_isOpen hW).comp R.isQuotientMap
  let T : Bool × ↥V ≃ₜ Bool × {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} :=
    (Homeomorph.refl Bool).prodCongr h
  let f : Bool × ↥V → ball (0 : ℂ) r := fun x =>
    ⟨if x.1 then conj (h x.2).val else (h x.2).val, by
      rcases x with ⟨b, z⟩
      cases b <;> simpa [mem_ball_zero_iff] using (h z).property.1⟩
  have hf : IsQuotientMap f := (s78ra_halfdisc_fold_quotient r).comp T.isQuotientMap
  have hker : ∀ x y, q x = q y ↔ f x = f y := by
    intro x y
    have hqeq : q x = q y ↔
        x.2 = y.2 ∧ (x.1 = y.1 ∨ x.2.val ∈ s31dt_boundary F) := by
      rw [Subtype.ext_iff]
      change s31dt_side F x.1 x.2.val = s31dt_side F y.1 y.2.val ↔ _
      rw [s31dt_side_eq_iff]
      exact and_congr_left (fun _ => Subtype.val_injective.eq_iff)
    rw [hqeq]
    have hfeq : f x = f y ↔ (f x).val = (f y).val := Subtype.ext_iff
    rw [hfeq]
    change _ ↔ (if x.1 then conj (h x.2).val else (h x.2).val) =
      (if y.1 then conj (h y.2).val else (h y.2).val)
    have hk := s78ra_halfplane_fold_fibers
      (x.1, ⟨(h x.2).val, (h x.2).property.2⟩)
      (y.1, ⟨(h y.2).val, (h y.2).property.2⟩)
    change (if x.1 then conj (h x.2).val else (h x.2).val) =
      (if y.1 then conj (h y.2).val else (h y.2).val) ↔
      (⟨(h x.2).val, (h x.2).property.2⟩ : {z : ℂ | 0 ≤ z.im}) =
        ⟨(h y.2).val, (h y.2).property.2⟩ ∧
      (x.1 = y.1 ∨ (h x.2).val.im = 0) at hk
    rw [hk]
    have he : (⟨(h x.2).val, (h x.2).property.2⟩ : {z : ℂ | 0 ≤ z.im}) =
        ⟨(h y.2).val, (h y.2).property.2⟩ ↔ x.2 = y.2 := by
      constructor
      · intro heq
        have hval : (h x.2).val = (h y.2).val :=
          congrArg (fun z : {z : ℂ | 0 ≤ z.im} => z.val) heq
        exact h.injective (Subtype.ext hval)
      · intro heq
        exact Subtype.ext (congrArg (fun z : ↥V => (h z).val) heq)
    rw [he, hboundary x.2]
  obtain ⟨E, hE⟩ := h84g_homeomorph_of_same_fibers q f hq hf hker
  have hWne : W.Nonempty := by
    let x : ↥V := h.symm ⟨0, by simpa using And.intro hr (le_refl (0 : ℝ))⟩
    exact ⟨s31dt_side F false x.val, x.property⟩
  obtain ⟨u, huS, huT, hu⟩ := h84g_open_subspaces_chart W (ball 0 r) hW isOpen_ball
    hWne ⟨0, by simpa using hr⟩ E
  have hside : ∀ b (x : ↥V), u (s31dt_side F b x.val) =
      if b then conj (h x).val else (h x).val := by
    intro b x
    exact (hu ⟨s31dt_side F b x.val, x.property⟩).trans
      (congrArg Subtype.val (hE (b, x)))
  refine ⟨u, huS, huT, hside, ?_⟩
  intro q
  refine Quotient.inductionOn q ?_
  intro x hx
  rcases x with ⟨b, x⟩
  have hxV : x ∈ V := by rw [huS] at hx; exact hx
  change s31dt_flip F (s31dt_side F b x) ∈ u.source ∧
    u (s31dt_flip F (s31dt_side F b x)) = conj (u (s31dt_side F b x))
  rw [s31dt_flip_side]
  constructor
  · rw [huS]
    exact hxV
  · rw [hside (!b) ⟨x, hxV⟩, hside b ⟨x, hxV⟩]
    cases b <;> simp

end LiZhongQC
end -- close original anonymous noncomputable section
end SchottkyHalfDiscGluingBlock

section SchottkyActualBoundaryChartsBlock

open Complex Set Metric Topology
open scoped ComplexConjugate

noncomputable section
namespace LiZhongQC

/-- Produce actual boundary charts on the shared quotient for a whole hole.
The exterior uniformizer and original surface chart are chosen before the
boundary point; all subsequent charts use that same closed-disc coordinate.
There is no assumed collar, double atlas, or analytic extension across the
original smooth boundary in this producer. -/
theorem s78ra_actual_boundary_chart_family
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) (j : Fin m) :
    ∃ (x : F.X.carrier) (J : Set ℂ) (N : Set F.X.carrier)
      (f : ℂ → ℂ) (e : ↥((toExt J)ᶜ) ≃ₜ closedBall (0 : ℂ) 1),
      IsJordanDomain J ∧ Bornology.IsBounded J ∧ IsOpen N ∧ F.D j ⊆ N ∧
      N ⊆ (chartAt ℂ x).source ∧
      (∀ y ∈ N, y ∉ (↑F.P : Set F.X.carrier)) ∧
      (∀ y ∈ N, ∀ k : Fin m, k ≠ j → y ∉ F.D k) ∧
      DifferentiableOn ℂ f (closure J)ᶜ ∧ InjOn f (closure J)ᶜ ∧
      (∀ z ∈ (closure J)ᶜ, ∀ hz : (z : ExtPlane) ∈ (toExt J)ᶜ,
        (e ⟨(z : ExtPlane), hz⟩).val = f z) ∧
      (∀ z : ↥((toExt J)ᶜ), ‖(e z).val‖ < 1 ↔ z.val ∈ (closure (toExt J))ᶜ) ∧
      (∀ z : ↥((toExt J)ᶜ), ‖(e z).val‖ = 1 ↔ z.val ∈ frontier (toExt J)) ∧
      ∀ p : s31dt_Core F, p.val ∈ frontier (F.D j) →
        ∃ (r : ℝ) (U : Set (s31dt_Core F)) (a : ℂ)
          (K : ↥U ≃ₜ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
          (u : OpenPartialHomeomorph (s31dt_Double F) ℂ),
          0 < r ∧ IsOpen U ∧ p ∈ U ∧ U ⊆ {y | y.val ∈ N} ∧ ‖a‖ = 1 ∧
          u.source = s31dt_project F ⁻¹' U ∧ u.target = ball 0 r ∧
          s31dt_side F false p ∈ u.source ∧ u (s31dt_side F false p) = 0 ∧
          (∀ y : ↥U, y.val ∈ s31dt_boundary F ↔ (K y).val.im = 0) ∧
          (∀ y : ↥U, ∃ hy : ((chartAt ℂ x) y.val.val : ExtPlane) ∈ (toExt J)ᶜ,
            (K y).val = I * (a - (e ⟨((chartAt ℂ x) y.val.val : ExtPlane), hy⟩).val) /
              (a + (e ⟨((chartAt ℂ x) y.val.val : ExtPlane), hy⟩).val)) ∧
          (∀ b (y : ↥U), u (s31dt_side F b y.val) =
            if b then conj (K y).val else (K y).val) ∧
          (∀ q ∈ u.source, s31dt_flip F q ∈ u.source ∧
            u (s31dt_flip F q) = conj (u q)) := by
  obtain ⟨x, J, N, hJ, hb, hN, hDN, hNs, hJt, hDJ, hNP, hND, hcore, hboundary,
      f, e, hf, hfi, hef, hei, heb⟩ := s78ra_fixed_hole_uniformizer F j
  refine ⟨x, J, N, f, e, hJ, hb, hN, hDN, hNs, hNP, hND,
    hf, hfi, hef, hei, heb, ?_⟩
  intro p hp
  have hpD : p.val ∈ F.D j :=
    (s31eg_disc_compact (F.disc j)).isClosed.closure_eq ▸ hp.1
  have hpN : p.val ∈ N := hDN hpD
  have hpB : p ∈ s31dt_boundary F := ⟨j, hp⟩
  obtain ⟨r, U, a, hr, hU, hpU, hUN, ha, K, hKp, hKb, hKformula⟩ :=
    s78ra_core_halfdisc_from_closed_coordinate F x J hJ hb N hN hNs
      hcore hboundary e heb p hpN hpB
  obtain ⟨u, huS, huT, hside, hflip⟩ :=
    s78ra_actual_quotient_halfdisc_chart F hr U hU K hKb
  have hpu : s31dt_side F false p ∈ u.source := by
    rw [huS]
    exact hpU
  have hpzero : u (s31dt_side F false p) = 0 := by
    rw [hside false ⟨p, hpU⟩]
    exact hKp hpU
  exact ⟨r, U, a, K, u, hr, hU, hpU, hUN, ha, huS, huT,
    hpu, hpzero, hKb, hKformula, hside, hflip⟩

end LiZhongQC
end -- close original anonymous noncomputable section
end SchottkyActualBoundaryChartsBlock
