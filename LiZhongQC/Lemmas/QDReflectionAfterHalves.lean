import LiZhongQC.Lemmas.QDReflectionTwoHalves
import LiZhongQC.Lemmas.FiniteTypeComponentTrapping
import Mathlib.Analysis.Complex.RemovableSingularity

section HalfRegularityBlock

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u v

section LocalTransport
variable {A : Type u} {B : Type v} [TopologicalSpace A] [ChartedSpace ℂ A]
  [TopologicalSpace B] [ChartedSpace ℂ B]
  [IsManifold 𝓘(ℂ) ω A] [IsManifold 𝓘(ℂ) ω B]

theorem s31qr_coordinate_differentiable {H : B → A} (x : B) (a : A)
    {z : ℂ} (hz : z ∈ (chartAt ℂ x).target)
    (ha : H ((chartAt ℂ x).symm z) ∈ (chartAt ℂ a).source)
    (hH : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H ((chartAt ℂ x).symm z)) :
    DifferentiableAt ℂ (fun w => chartAt ℂ a (H ((chartAt ℂ x).symm w))) z := by
  have hh := ((s23_mdifferentiableAt_iff ((chartAt ℂ x).map_target hz) ha).1 hH).2
  rwa [(chartAt ℂ x).right_inv hz] at hh

/-- A differential family's canonical-point transport has its usual formula in
any fixed target chart. This is what removes the point-dependent chart from
the regularity argument. -/
theorem s31qr_transport_local {U : Set B} {H : B → A}
    {q : A → ℂ → ℂ} (hq : IsDiffFamily 2 0 q) (x : B) (a : A)
    {z : ℂ} (hz : z ∈ (chartAt ℂ x).target)
    (hp : (chartAt ℂ x).symm z ∈ U)
    (ha : H ((chartAt ℂ x).symm z) ∈ (chartAt ℂ a).source)
    (hH : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H ((chartAt ℂ x).symm z)) :
    s31qr_transportOn U H (LinearMap.id : ℂ →ₗ[ℝ] ℂ) q x z =
      q a (chartAt ℂ a (H ((chartAt ℂ x).symm z))) *
        deriv (fun w => chartAt ℂ a (H ((chartAt ℂ x).symm w))) z ^ 2 := by
  let b := H ((chartAt ℂ x).symm z)
  have hbt : chartAt ℂ b b ∈ (chartAt ℂ b).target :=
    (chartAt ℂ b).map_source (mem_chart_source ℂ b)
  have hbi : (chartAt ℂ b).symm (chartAt ℂ b b) = b :=
    (chartAt ℂ b).left_inv (mem_chart_source ℂ b)
  have hl : q b (chartAt ℂ b b) =
      q a (chartAt ℂ a b) * deriv (chartTransition a b) (chartAt ℂ b b) ^ 2 := by
    have hh := hq.2 a b (chartAt ℂ b b) hbt (by rw [hbi]; exact ha)
    have he : chartTransition a b (chartAt ℂ b b) = chartAt ℂ a b := by
      change chartAt ℂ a ((chartAt ℂ b).symm (chartAt ℂ b b)) = _
      rw [hbi]
    simpa only [he, zpow_zero, mul_one, zpow_two, pow_two] using hh
  have hbD := s31qr_coordinate_differentiable x b hz (mem_chart_source ℂ b) hH
  have hτD := s23_transition_differentiableAt a b hbt (by rw [hbi]; exact ha)
  have hc : ContinuousAt (fun w => H ((chartAt ℂ x).symm w)) z :=
    hH.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz)
  have he :
      (fun w => chartAt ℂ a (H ((chartAt ℂ x).symm w))) =ᶠ[𝓝 z]
      chartTransition a b ∘ (fun w => chartAt ℂ b (H ((chartAt ℂ x).symm w))) := by
    filter_upwards [hc.preimage_mem_nhds ((chartAt ℂ b).open_source.mem_nhds
      (mem_chart_source ℂ b))] with w hw
    change chartAt ℂ a (H ((chartAt ℂ x).symm w)) =
      chartAt ℂ a ((chartAt ℂ b).symm (chartAt ℂ b (H ((chartAt ℂ x).symm w))))
    rw [(chartAt ℂ b).left_inv hw]
  have hd : deriv (fun w => chartAt ℂ a (H ((chartAt ℂ x).symm w))) z =
      deriv (chartTransition a b) (chartAt ℂ b b) *
        deriv (fun w => chartAt ℂ b (H ((chartAt ℂ x).symm w))) z := by
    rw [he.deriv_eq]
    exact (hτD.hasDerivAt.comp z hbD.hasDerivAt).deriv
  classical
  change (if z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm z ∈ U then
    q b (chartAt ℂ b b) *
      deriv (fun w => chartAt ℂ b (H ((chartAt ℂ x).symm w))) z ^ 2 else 0) = _
  rw [if_pos ⟨hz, hp⟩, hl, hd]
  ring

/-- Holomorphic regularity on the transported open piece is proved from the
original local coefficients and tensor law, not assumed of the new family. -/
theorem s31qr_transport_holomorphic {U : Set B} (hU : IsOpen U)
    {V : Set A} (hV : IsOpen V) {H : B → A}
    (hH : ∀ p ∈ U, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H p)
    (himage : MapsTo H U V) {q : A → ℂ → ℂ} (hq : IsDiffFamily 2 0 q)
    (hqd : ∀ a : A, DifferentiableOn ℂ (q a)
      ((chartAt ℂ a).target ∩ (chartAt ℂ a).symm ⁻¹' V))
    (x : B) :
    DifferentiableOn ℂ (s31qr_transportOn U H (LinearMap.id : ℂ →ₗ[ℝ] ℂ) q x)
      ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' U) := by
  intro z hz
  let a := H ((chartAt ℂ x).symm z)
  let W : Set ℂ := (chartAt ℂ x).target ∩
    (chartAt ℂ x).symm ⁻¹' (U ∩ H ⁻¹' (chartAt ℂ a).source)
  have hHc : ContinuousOn H U := fun p hp => (hH p hp).continuousAt.continuousWithinAt
  have hWo : IsOpen W := (chartAt ℂ x).isOpen_inter_preimage_symm
    (hHc.isOpen_inter_preimage hU (chartAt ℂ a).open_source)
  have hzW : z ∈ W := ⟨hz.1, hz.2, mem_chart_source ℂ a⟩
  have hTd : DifferentiableOn ℂ
      (fun w => chartAt ℂ a (H ((chartAt ℂ x).symm w))) W := by
    intro w hw
    exact (s31qr_coordinate_differentiable x a hw.1 hw.2.2
      (hH _ hw.2.1)).differentiableWithinAt
  have hdd := hTd.deriv hWo
  have haV : (chartAt ℂ a).symm (chartAt ℂ a a) ∈ V := by
    rw [(chartAt ℂ a).left_inv (mem_chart_source ℂ a)]
    exact himage hz.2
  have hnb : (chartAt ℂ a).target ∩ (chartAt ℂ a).symm ⁻¹' V ∈ 𝓝 (chartAt ℂ a a) :=
    ((chartAt ℂ a).isOpen_inter_preimage_symm hV).mem_nhds
      ⟨(chartAt ℂ a).map_source (mem_chart_source ℂ a), haV⟩
  have hqAt : DifferentiableAt ℂ (q a) (chartAt ℂ a a) :=
    (hqd a).differentiableAt hnb
  have hmodel : DifferentiableAt ℂ
      (fun w => q a (chartAt ℂ a (H ((chartAt ℂ x).symm w))) *
        deriv (fun v => chartAt ℂ a (H ((chartAt ℂ x).symm v))) w ^ 2) z :=
    (hqAt.comp z (hTd.differentiableAt (hWo.mem_nhds hzW))).mul
      ((hdd.differentiableAt (hWo.mem_nhds hzW)).pow 2)
  have he :
      s31qr_transportOn U H (LinearMap.id : ℂ →ₗ[ℝ] ℂ) q x =ᶠ[𝓝 z]
      (fun w => q a (chartAt ℂ a (H ((chartAt ℂ x).symm w))) *
        deriv (fun v => chartAt ℂ a (H ((chartAt ℂ x).symm v))) w ^ 2) := by
    filter_upwards [hWo.mem_nhds hzW] with w hw
    exact s31qr_transport_local hq x a hw.1 hw.2.1 hw.2.2 (hH _ hw.2.1)
  exact (hmodel.congr_of_eventuallyEq he).differentiableWithinAt

end LocalTransport

/-- On the genuine positive half, the newly constructed data are holomorphic
for every ORIGINAL admissible q. -/
theorem s31qr_positive_holomorphic
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [Nonempty S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
    (hd : IsSchottkyDouble F Xd J ιd Pd)
    {q : F.X.carrier → ℂ → ℂ} (hq : IsAdmissibleQD F q) (x : Xd.carrier) :
    DifferentiableOn ℂ (s31qr_positiveData F hd q x)
      ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' range ιd) := by
  apply s31qr_transport_holomorphic hd.embedding.isOpenMap.isOpen_range
    F.embedding.isOpenMap.isOpen_range
    (fun p hp => s31qr_halfReturn_holomorphic F hd hp) _ hq.1 hq.2.1
  intro p hp
  exact ⟨(hd.embedding.toOpenPartialHomeomorph ιd).symm p, rfl⟩

end LiZhongQC


end
end HalfRegularityBlock

section GlobalContinuationBlock

section CompactificationBlock

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u v

/-- A continuous surface map holomorphic away from finitely many points is
holomorphic everywhere. This uses planar removable singularities in actual
preferred charts. -/
theorem s31qr_remove_finite
    {A : Type u} {B : Type v} [TopologicalSpace A] [ChartedSpace ℂ A] [T1Space A]
    [TopologicalSpace B] [ChartedSpace ℂ B]
    [IsManifold 𝓘(ℂ) ω A] [IsManifold 𝓘(ℂ) ω B]
    (P : Finset A) {f : A → B} (hc : Continuous f)
    (hf : ∀ p ∉ P, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f p) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  classical
  intro p
  apply (s23_mdifferentiableAt_iff (mem_chart_source ℂ p)
    (mem_chart_source ℂ (f p))).2
  refine ⟨hc.continuousAt, ?_⟩
  let χ := chartAt ℂ p
  let η := chartAt ℂ (f p)
  let g : ℂ → ℂ := fun z => η (f (χ.symm z))
  have hleft : χ.symm (χ p) = p := χ.left_inv (mem_chart_source ℂ p)
  have htarget : χ p ∈ χ.target := χ.map_source (mem_chart_source ℂ p)
  have hgC : ContinuousAt g (χ p) := by
    have hη : ContinuousAt η (f (χ.symm (χ p))) := by
      rw [hleft]
      exact η.continuousAt (mem_chart_source ℂ (f p))
    have hfc : ContinuousAt (fun z => f (χ.symm z)) (χ p) :=
      hc.continuousAt.comp (χ.continuousAt_symm htarget)
    exact ContinuousAt.comp (g := η) (f := fun z => f (χ.symm z)) (x := χ p) hη hfc
  have hOpen : IsOpen (f ⁻¹' η.source ∩ (↑(P.erase p) : Set A)ᶜ) :=
    (η.open_source.preimage hc).inter (P.erase p).finite_toSet.isClosed.isOpen_compl
  have hnb : χ.target ∩ χ.symm ⁻¹' (f ⁻¹' η.source ∩ (↑(P.erase p) : Set A)ᶜ) ∈ 𝓝 (χ p) := by
    apply (χ.isOpen_inter_preimage_symm hOpen).mem_nhds
    refine ⟨htarget, ?_, ?_⟩
    · change f (χ.symm (χ p)) ∈ η.source
      rw [hleft]
      exact mem_chart_source ℂ (f p)
    · rw [hleft]
      simp
  have hgD : ∀ᶠ z in 𝓝[≠] (χ p), DifferentiableAt ℂ g z := by
    filter_upwards [nhdsWithin_le_nhds (s := {χ p}ᶜ) hnb, self_mem_nhdsWithin] with z hz hne
    have hnot : χ.symm z ∉ P := by
      intro hP
      have hpne : χ.symm z ≠ p := by
        intro he
        apply hne
        change z = χ p
        rw [← χ.right_inv hz.1, he]
      exact hz.2.2 (Finset.mem_erase.2 ⟨hpne, hP⟩)
    have hd := ((s23_mdifferentiableAt_iff (χ.map_target hz.1) hz.2.1).1
      (hf (χ.symm z) hnot)).2
    rw [χ.right_inv hz.1] at hd
    exact hd
  exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hgD hgC).differentiableAt

section Compactification
variable (Xd : ClosedRS.{u}) (Pd : Finset Xd.carrier)
  {gd nd : ℕ} (Fd : FiniteTypeStructure (puncturedOpens Pd) gd nd 0)

/-- The literal inclusion has precisely Pd as its missing set. -/
theorem s31qr_punctured_range :
    range (Subtype.val : puncturedOpens Pd → Xd.carrier) = (↑Pd : Set Xd.carrier)ᶜ := by
  ext p
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro hp
    exact ⟨⟨p, hp⟩, rfl⟩

/-- Topological compactification transport to an arbitrary Fd, constructed from
the installed finite-puncture theorem. No supplied compactification equivalence
or puncture matching is assumed. -/
theorem s31qr_fd_homeomorph :
    ∃! E : Xd.carrier ≃ₜ Fd.X.carrier,
      ∀ a : puncturedOpens Pd, E a.val = Fd.ι a := by
  let i : puncturedOpens Pd → Xd.carrier := Subtype.val
  have hi := (puncturedOpens Pd).isOpenEmbedding'.isEmbedding
  have hfi : ((range i)ᶜ).Finite := by
    change ((range (Subtype.val : puncturedOpens Pd → Xd.carrier))ᶜ).Finite
    rw [s31qr_punctured_range Xd Pd, compl_compl]
    exact Pd.finite_toSet
  have hfj : ((range Fd.ι)ᶜ).Finite := by
    have he : (range Fd.ι)ᶜ = (↑Fd.P : Set Fd.X.carrier) := by rw [Fd.range_ι]; simp
    rw [he]
    exact Fd.P.finite_toSet
  exact s31fe_extend_finite_missing i Fd.ι hi Fd.embedding.isEmbedding
    (s31cg_denseRange i hfi) (s31cg_denseRange Fd.ι hfj) hfi hfj
    (s31cg_connected_traces i hi hfi)
    (s31cg_connected_traces Fd.ι Fd.embedding.isEmbedding hfj)

/-- The constructed compactification equivalence maps precisely the puncture
sets to each other, derived from its agreement on the common open surface. -/
theorem s31qr_fd_puncture_membership
    (E : Xd.carrier ≃ₜ Fd.X.carrier)
    (hE : ∀ a : puncturedOpens Pd, E a.val = Fd.ι a) (p : Xd.carrier) :
    p ∈ Pd ↔ E p ∈ Fd.P := by
  have hr : E p ∈ range Fd.ι ↔ p ∉ Pd := by
    constructor
    · rintro ⟨a, ha⟩
      have he : a.val = p := E.injective ((hE a).trans ha)
      exact he ▸ a.property
    · intro hp
      exact ⟨⟨p, hp⟩, (hE ⟨p, hp⟩).symm⟩
  rw [Fd.range_ι] at hr
  simpa using (not_congr hr).symm

/-- Arbitrary finite-puncture compactification transport is actually biholomorphic,
including at the filled punctures. -/
theorem s31qr_fd_biholomorphic
    (E : Xd.carrier ≃ₜ Fd.X.carrier)
    (hE : ∀ a : puncturedOpens Pd, E a.val = Fd.ι a) :
    IsBiholomorphic (E : Xd.carrier → Fd.X.carrier) := by
  let i : puncturedOpens Pd → Xd.carrier := Subtype.val
  have hi := (puncturedOpens Pd).isOpenEmbedding'
  have hir : range i = (↑Pd : Set Xd.carrier)ᶜ := s31qr_punctured_range Xd Pd
  have hfi : ((range i)ᶜ).Finite := by
    rw [hir, compl_compl]
    exact Pd.finite_toSet
  letI : Nonempty (puncturedOpens Pd) := (s31cg_denseRange i hfi).nonempty
  have him : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) i :=
    (contMDiff_subtype_val (n := ω)).mdifferentiable (by simp)
  have hEhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) E := by
    apply s31qr_remove_finite Pd E.continuous
    intro p hp
    have hpR : p ∈ range i := by rw [hir]; exact hp
    have hinv := s31qr_open_embedding_inverse hi him hpR
    have hcomp := (Fd.holomorphic _).comp p hinv
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [hi.isOpenMap.isOpen_range.mem_nhds hpR] with y hy
    have he := hi.toOpenPartialHomeomorph_right_inv i hy
    change E y = Fd.ι ((hi.toOpenPartialHomeomorph i).symm y)
    calc
      E y = E (i ((hi.toOpenPartialHomeomorph i).symm y)) := by rw [he]
      _ = Fd.ι ((hi.toOpenPartialHomeomorph i).symm y) := hE _
  have hEinv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) E.symm := by
    apply s31qr_remove_finite Fd.P E.symm.continuous
    intro p hp
    have hpR : p ∈ range Fd.ι := by
      rw [Fd.range_ι]
      simpa using hp
    have hinv := s31qr_open_embedding_inverse Fd.embedding Fd.holomorphic hpR
    have hcomp := (him _).comp p hinv
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [Fd.embedding.isOpenMap.isOpen_range.mem_nhds hpR] with y hy
    change E.symm y = i ((Fd.embedding.toOpenPartialHomeomorph Fd.ι).symm y)
    apply E.injective
    rw [E.apply_symm_apply, hE]
    exact (Fd.embedding.toOpenPartialHomeomorph_right_inv Fd.ι hy).symm
  exact ⟨hEhol, E.symm, hEinv, E.symm_apply_apply, E.apply_symm_apply⟩

/-- The precise geometric interface for the later quadratic-differential
transport to arbitrary Fd, with both holomorphic directions and puncture
correspondence proved. -/
theorem s31qr_fd_compactification :
    ∃ E : Xd.carrier ≃ₜ Fd.X.carrier,
      IsBiholomorphic (E : Xd.carrier → Fd.X.carrier) ∧
      (∀ a : puncturedOpens Pd, E a.val = Fd.ι a) ∧
      (∀ p : Xd.carrier, p ∈ Pd ↔ E p ∈ Fd.P) := by
  obtain ⟨E, hE, _⟩ := s31qr_fd_homeomorph Xd Pd Fd
  exact ⟨E, s31qr_fd_biholomorphic Xd Pd Fd E hE, hE,
    s31qr_fd_puncture_membership Xd Pd Fd E hE⟩

end Compactification
open Classical in
/-- Once the genuine original puncture endpoints have been constructed and
separated from their mirrors, the original cardinality clauses force them to
exhaust Pd. This isolates the remaining geometric endpoint-existence problem. -/
theorem s31qr_Pd_exhaustion
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
    (hd : IsSchottkyDouble F Xd J ιd Pd)
    (e : (↑F.P : Set F.X.carrier) ↪ Xd.carrier)
    (he : ∀ p, e p ∈ Pd)
    (hsep : ∀ p r, e p ≠ J (e r)) :
    Pd = (Finset.univ.image e) ∪ (Finset.univ.image (fun p => J (e p))) := by
  classical
  let A : Finset Xd.carrier := Finset.univ.image e
  let B : Finset Xd.carrier := Finset.univ.image (fun p => J (e p))
  have hA : A.card = n := by
    rw [Finset.card_image_of_injective _ e.injective]
    simpa using F.card_P
  have hB : B.card = n := by
    rw [Finset.card_image_of_injective _
      (show Function.Injective (fun p => J (e p)) from J.injective.comp e.injective)]
    simpa using F.card_P
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.2
    intro p hpA hpB
    obtain ⟨a, _, ha⟩ := Finset.mem_image.1 hpA
    obtain ⟨b, _, hb⟩ := Finset.mem_image.1 hpB
    exact hsep a b (ha.trans hb.symm)
  have hsub : A ∪ B ⊆ Pd := by
    intro p hp
    rcases Finset.mem_union.1 hp with ha | hb
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 ha
      exact he a
    · obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hb
      have hm : J (e b) ∈ J '' (↑Pd : Set Xd.carrier) := mem_image_of_mem J (he b)
      rwa [hd.Pd_invariant] at hm
  have hc : Pd.card ≤ (A ∪ B).card := by
    rw [hd.card_Pd, Finset.card_union_of_disjoint hAB, hA, hB]
    omega
  exact (Finset.eq_of_subset_of_card_le hsub hc).symm

end LiZhongQC


end
end CompactificationBlock

section RestrictionBlock

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u v

/-- Original admissibility determines every coefficient from its restriction to
the original open surface: poles are normalized, holes are zero, and boundary
values are limits from the open surface. This generalizes the range-recovery
step of s32p_pullbackQD_eq_zero without importing downstream S32. -/
theorem s31qr_admissible_zero_of_range
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {q : F.X.carrier → ℂ → ℂ}
    (hq : IsAdmissibleQD F q)
    (hrange : ∀ x z, z ∈ (chartAt ℂ x).target →
      (chartAt ℂ x).symm z ∈ range F.ι → q x z = 0) : q = 0 := by
  classical
  funext x z
  show q x z = 0
  by_cases hz : z ∈ (chartAt ℂ x).target
  · let p := (chartAt ℂ x).symm z
    have hp : p ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
    have hpz : chartAt ℂ x p = z := (chartAt ℂ x).right_inv hz
    by_cases hι : p ∈ range F.ι
    · exact hrange x z hz hι
    by_cases hP : p ∈ F.P
    · have h := (hq.2.2.1 x p hP hp).1
      rwa [hpz] at h
    have hD : p ∈ ⋃ j, F.D j := by
      rw [F.range_ι] at hι
      simp only [mem_compl_iff, not_not, mem_union, Finset.mem_coe] at hι
      exact hι.resolve_left hP
    obtain ⟨j, hj⟩ := mem_iUnion.1 hD
    by_cases hint : p ∈ interior (F.D j)
    · exact hq.2.2.2.2.2 x j z hz hint
    have hfr : p ∈ frontier (F.D j) := ⟨subset_closure hj, hint⟩
    have hC : IsClosed ((↑F.P : Set F.X.carrier) ∪ ⋃ i ∈ {i | i ≠ j}, F.D i) :=
      F.P.finite_toSet.isClosed.union
        ((Set.toFinite _).isClosed_biUnion fun i _ => (s31eg_disc_compact (F.disc i)).isClosed)
    have hpC : p ∉ (↑F.P : Set F.X.carrier) ∪ ⋃ i ∈ {i | i ≠ j}, F.D i := by
      rintro (h | h)
      · exact Set.disjoint_left.1 (F.disjoint_P j) hj h
      · obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.1 h
        exact Set.disjoint_left.1 (F.disjoint hi) hpi hj
    have hcl : p ∈ closure (range F.ι) := by
      rw [mem_closure_iff_nhds]
      intro t ht
      have ht' : t ∩ ((↑F.P : Set F.X.carrier) ∪ ⋃ i ∈ {i | i ≠ j}, F.D i)ᶜ ∈ 𝓝 p :=
        Filter.inter_mem ht (hC.isOpen_compl.mem_nhds hpC)
      have hfr' : p ∈ closure (F.D j)ᶜ :=
        frontier_subset_closure (by rw [frontier_compl]; exact hfr)
      obtain ⟨y, ⟨hyt, hyC⟩, hyD⟩ := mem_closure_iff_nhds.1 hfr' _ ht'
      refine ⟨y, hyt, ?_⟩
      rw [F.range_ι]
      rintro (hyP | hyU)
      · exact hyC (Or.inl hyP)
      · obtain ⟨i, hi⟩ := mem_iUnion.1 hyU
        by_cases hij : i = j
        · exact hyD (hij ▸ hi)
        · exact hyC (Or.inr (mem_iUnion₂.2 ⟨i, hij, hi⟩))
    have hzA : z ∈ closure ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' range F.ι) := by
      have hp' : p ∈ closure ((chartAt ℂ x).source ∩ range F.ι) := by
        rw [mem_closure_iff_nhds] at hcl ⊢
        intro t ht
        obtain ⟨y, ⟨hyt, hys⟩, hyr⟩ :=
          hcl _ (Filter.inter_mem ht ((chartAt ℂ x).open_source.mem_nhds hp))
        exact ⟨y, hyt, hys, hyr⟩
      have himg := ((chartAt ℂ x).continuousAt hp).continuousWithinAt.mem_closure_image hp'
      rw [hpz] at himg
      refine closure_mono ?_ himg
      rintro _ ⟨y, ⟨hys, hyr⟩, rfl⟩
      refine ⟨(chartAt ℂ x).map_source hys, ?_⟩
      show (chartAt ℂ x).symm (chartAt ℂ x y) ∈ range F.ι
      rw [(chartAt ℂ x).left_inv hys]
      exact hyr
    have hcontq : ContinuousWithinAt (q x)
        ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' range F.ι) z :=
      ((hq.2.2.2.1 x j) z ⟨hz, Or.inr hfr⟩).mono
        (inter_subset_inter_right _ (preimage_mono subset_union_left))
    have hsub : q x '' ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' range F.ι) ⊆ {0} := by
      rintro _ ⟨w, ⟨hw, hwr⟩, rfl⟩
      exact hrange x w hw hwr
    have h0 := closure_mono hsub (hcontq.mem_closure_image hzA)
    rwa [closure_singleton, mem_singleton_iff] at h0
  · exact hq.1.1 x z hz

/-- A holomorphic map injective on its actual open domain has a nonzero
coordinate derivative at every point of that domain. -/
theorem s31qr_coordinate_deriv_ne_zero
    {A : Type u} {B : Type v} [TopologicalSpace A] [ChartedSpace ℂ A]
    [TopologicalSpace B] [ChartedSpace ℂ B]
    [IsManifold 𝓘(ℂ) ω A] [IsManifold 𝓘(ℂ) ω B]
    {U : Set B} (hU : IsOpen U) {H : B → A}
    (hH : ∀ p ∈ U, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H p) (hi : InjOn H U)
    (x : B) (a : A) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target)
    (hp : (chartAt ℂ x).symm z ∈ U)
    (ha : H ((chartAt ℂ x).symm z) ∈ (chartAt ℂ a).source) :
    deriv (fun w => chartAt ℂ a (H ((chartAt ℂ x).symm w))) z ≠ 0 := by
  let W := (chartAt ℂ x).target ∩
    (chartAt ℂ x).symm ⁻¹' (U ∩ H ⁻¹' (chartAt ℂ a).source)
  have hHc : ContinuousOn H U := fun p hp => (hH p hp).continuousAt.continuousWithinAt
  have hWo : IsOpen W := (chartAt ℂ x).isOpen_inter_preimage_symm
    (hHc.isOpen_inter_preimage hU (chartAt ℂ a).open_source)
  have hd : DifferentiableOn ℂ (fun w => chartAt ℂ a (H ((chartAt ℂ x).symm w))) W := by
    intro w hw
    exact (s31qr_coordinate_differentiable x a hw.1 hw.2.2
      (hH _ hw.2.1)).differentiableWithinAt
  have hinj : InjOn (fun w => chartAt ℂ a (H ((chartAt ℂ x).symm w))) W := by
    intro w hw v hv he
    have hh := hi hw.2.1 hv.2.1 ((chartAt ℂ a).injOn hw.2.2 hv.2.2 he)
    rw [← (chartAt ℂ x).right_inv hw.1, ← (chartAt ℂ x).right_inv hv.1, hh]
  exact deriv_ne_zero_of_injOn hWo hd hinj ⟨hz, hp, ha⟩

section Recovery
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
  [Nonempty S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ}
  (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
  {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
  (hd : IsSchottkyDouble F Xd J ιd Pd)

theorem s31qr_halfReturn_injOn : InjOn (s31qr_halfReturn F hd) (range ιd) := by
  intro p hp r hr he
  change F.ι ((hd.embedding.toOpenPartialHomeomorph ιd).symm p) =
    F.ι ((hd.embedding.toOpenPartialHomeomorph ιd).symm r) at he
  have hh := congrArg ιd (F.embedding.injective he)
  rwa [hd.embedding.toOpenPartialHomeomorph_right_inv ιd hp,
    hd.embedding.toOpenPartialHomeomorph_right_inv ιd hr] at hh

/-- Vanishing of the actual pushed-forward coefficients just on the positive
half forces the ORIGINAL admissible differential to vanish everywhere. -/
theorem s31qr_positive_restriction_recover
    {q : F.X.carrier → ℂ → ℂ} (hq : IsAdmissibleQD F q)
    (hzero : ∀ x z, z ∈ (chartAt ℂ x).target →
      (chartAt ℂ x).symm z ∈ range ιd → s31qr_positiveData F hd q x z = 0) : q = 0 := by
  have hcenter : ∀ s : S, q (F.ι s) (chartAt ℂ (F.ι s) (F.ι s)) = 0 := by
    intro s
    let p := ιd s
    let z := chartAt ℂ p p
    have hz : z ∈ (chartAt ℂ p).target :=
      (chartAt ℂ p).map_source (mem_chart_source ℂ p)
    have hleft : (chartAt ℂ p).symm z = p :=
      (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
    have hp : (chartAt ℂ p).symm z ∈ range ιd := by rw [hleft]; exact ⟨s, rfl⟩
    have hR : s31qr_halfReturn F hd p = F.ι s := s31qr_halfReturn_image F hd s
    have ha : s31qr_halfReturn F hd ((chartAt ℂ p).symm z) ∈
        (chartAt ℂ (F.ι s)).source := by rw [hleft, hR]; exact mem_chart_source ℂ _
    have hder := s31qr_coordinate_deriv_ne_zero hd.embedding.isOpenMap.isOpen_range
      (fun y hy => s31qr_halfReturn_holomorphic F hd hy)
      (s31qr_halfReturn_injOn F hd) p (F.ι s) hz hp ha
    have hval := hzero p z hz hp
    classical
    change (if z ∈ (chartAt ℂ p).target ∧ (chartAt ℂ p).symm z ∈ range ιd then
      q (s31qr_halfReturn F hd ((chartAt ℂ p).symm z))
        (chartAt ℂ (s31qr_halfReturn F hd ((chartAt ℂ p).symm z))
          (s31qr_halfReturn F hd ((chartAt ℂ p).symm z))) *
        deriv (fun w => chartAt ℂ (s31qr_halfReturn F hd ((chartAt ℂ p).symm z))
          (s31qr_halfReturn F hd ((chartAt ℂ p).symm w))) z ^ 2 else 0) = 0 at hval
    rw [if_pos ⟨hz, hp⟩, hleft, hR] at hval
    exact (mul_eq_zero.1 hval).resolve_right (pow_ne_zero 2 hder)
  apply s31qr_admissible_zero_of_range F hq
  rintro x z hz ⟨s, hs⟩
  have hsrc : (chartAt ℂ x).symm z ∈ (chartAt ℂ (F.ι s)).source := by
    rw [← hs]
    exact mem_chart_source ℂ _
  have hT : chartTransition (F.ι s) x z = chartAt ℂ (F.ι s) (F.ι s) := by
    change chartAt ℂ (F.ι s) ((chartAt ℂ x).symm z) = _
    rw [← hs]
  rw [hq.1.2 (F.ι s) x z hz hsrc, hT, hcenter s]
  simp

/-- The two-half construction is injective on the original admissible space,
before the seam values are filled. -/
theorem s31qr_twoHalf_injective :
    InjOn (s31qr_twoHalfData F hd) (admissibleQDSpace F) := by
  intro q hq r hr he
  obtain ⟨T, hT⟩ := s31qr_twoHalf_linear F hd
  have hsub : IsAdmissibleQD F (q - r) := (admissibleQDSpace F).sub_mem hq hr
  have hz : s31qr_twoHalfData F hd (q - r) = 0 := by
    rw [← hT, map_sub, hT, hT, he, sub_self]
  have hqr : q - r = 0 := by
    apply s31qr_positive_restriction_recover F hd hsub
    intro x z hzt hp
    rw [← s31qr_twoHalf_on_positive F hd (q - r) x z hp, hz]
    rfl
  exact sub_eq_zero.1 hqr

end Recovery
end LiZhongQC


end
end RestrictionBlock


end GlobalContinuationBlock

section PointwiseTransferBlock

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

/-- Actual pointwise equality on the original open surface determines the
entire original admissible coefficient family, including boundary and junk-free
normalizations. No global extension is supplied. -/
theorem s31qr_admissible_eq_of_range
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {q r : F.X.carrier → ℂ → ℂ}
    (hq : IsAdmissibleQD F q) (hr : IsAdmissibleQD F r)
    (he : ∀ x z, z ∈ (chartAt ℂ x).target →
      (chartAt ℂ x).symm z ∈ range F.ι → q x z = r x z) : q = r := by
  have hs : IsAdmissibleQD F (q - r) := (admissibleQDSpace F).sub_mem hq hr
  apply sub_eq_zero.1
  apply s31qr_admissible_zero_of_range F hs
  intro x z hz hp
  change q x z - r x z = 0
  exact sub_eq_zero.2 (he x z hz hp)

/-- Equality only at the preferred chart centre of every point of range F.ι
already determines an admissible family: its original tensor law gives all
other chart values. -/
theorem s31qr_admissible_eq_of_centers
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {q r : F.X.carrier → ℂ → ℂ}
    (hq : IsAdmissibleQD F q) (hr : IsAdmissibleQD F r)
    (he : ∀ s : S, q (F.ι s) (chartAt ℂ (F.ι s) (F.ι s)) =
      r (F.ι s) (chartAt ℂ (F.ι s) (F.ι s))) : q = r := by
  apply s31qr_admissible_eq_of_range F hq hr
  rintro x z hz ⟨s, hs⟩
  have hsrc : (chartAt ℂ x).symm z ∈ (chartAt ℂ (F.ι s)).source := by
    rw [← hs]
    exact mem_chart_source ℂ _
  have hT : chartTransition (F.ι s) x z = chartAt ℂ (F.ι s) (F.ι s) := by
    change chartAt ℂ (F.ι s) ((chartAt ℂ x).symm z) = _
    rw [← hs]
  rw [hq.1.2 (F.ι s) x z hz hsrc, hr.1.2 (F.ι s) x z hz hsrc, hT, he s]

/-- Pointwise equality of genuine quadratic coordinate transports recovers the
original family. d is the nonzero first derivative of the coordinate map at
the comparison point; neither a global extended family nor its existence is
an input. -/
theorem s31qr_admissible_eq_of_transport_values
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {q r : F.X.carrier → ℂ → ℂ}
    (hq : IsAdmissibleQD F q) (hr : IsAdmissibleQD F r)
    (he : ∀ s : S, ∃ d : ℂ, d ≠ 0 ∧
      q (F.ι s) (chartAt ℂ (F.ι s) (F.ι s)) * d ^ 2 =
      r (F.ι s) (chartAt ℂ (F.ι s) (F.ι s)) * d ^ 2) : q = r := by
  apply s31qr_admissible_eq_of_centers F hq hr
  intro s
  obtain ⟨d, hd, heq⟩ := he s
  exact mul_right_cancel₀ (pow_ne_zero 2 hd) heq

/-- Equality of the actual positive-half coefficient data, point by point on
that half, is enough for equality of the entire original admissible families. -/
theorem s31qr_positive_restriction_eq
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [Nonempty S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
    (hd : IsSchottkyDouble F Xd J ιd Pd)
    {q r : F.X.carrier → ℂ → ℂ}
    (hq : IsAdmissibleQD F q) (hr : IsAdmissibleQD F r)
    (he : ∀ x z, z ∈ (chartAt ℂ x).target →
      (chartAt ℂ x).symm z ∈ range ιd →
        s31qr_positiveData F hd q x z = s31qr_positiveData F hd r x z) : q = r := by
  let T : (F.X.carrier → ℂ → ℂ) →ₗ[ℝ] (Xd.carrier → ℂ → ℂ) :=
    { toFun := s31qr_positiveData F hd
      map_add' := s31qr_transport_add _ _ _
      map_smul' := s31qr_transport_real_smul _ _ _ }
  have hsub : s31qr_positiveData F hd (q - r) =
      s31qr_positiveData F hd q - s31qr_positiveData F hd r := T.map_sub q r
  have hs : IsAdmissibleQD F (q - r) := (admissibleQDSpace F).sub_mem hq hr
  apply sub_eq_zero.1
  apply s31qr_positive_restriction_recover F hd hs
  intro x z hz hp
  rw [hsub]
  change s31qr_positiveData F hd q x z - s31qr_positiveData F hd r x z = 0
  exact sub_eq_zero.2 (he x z hz hp)

/-- An actual simple-principal-part expansion is meromorphic; this is not
inferred from a default value of meromorphicOrderAt. -/
theorem s31qr_meromorphic_of_simple_expansion {f r : ℂ → ℂ} {a c : ℂ}
    (hr : AnalyticAt ℂ r a)
    (he : f =ᶠ[𝓝[≠] a] (fun z => c / (z - a) + r z)) :
    MeromorphicAt f a := by
  have hlin : AnalyticAt ℂ (fun z : ℂ => z - a) a := analyticAt_id.sub analyticAt_const
  have hm : MeromorphicAt (fun z => c / (z - a) + r z) a :=
    ((MeromorphicAt.const c a).div hlin.meromorphicAt).add hr.meromorphicAt
  exact hm.congr he.symm

/-- A nonramified analytic coordinate change preserves the order of an actual
quadratic pullback, because its derivative square is an analytic unit. -/
theorem s31qr_quadratic_pullback_order {f τ : ℂ → ℂ} {p : ℂ}
    (hτ : AnalyticAt ℂ τ p) (hd : deriv τ p ≠ 0) :
    meromorphicOrderAt (fun z => f (τ z) * deriv τ z ^ 2) p =
      meromorphicOrderAt f (τ p) := by
  have he : (fun z => f (τ z) * deriv τ z ^ 2) =
      (deriv τ ^ 2) * (f ∘ τ) := by
    funext z
    change f (τ z) * deriv τ z ^ 2 = deriv τ z ^ 2 * f (τ z)
    exact mul_comm _ _
  rw [he, meromorphicOrderAt_mul_of_ne_zero (hτ.deriv.pow 2) (pow_ne_zero 2 hd),
    meromorphicOrderAt_comp_of_deriv_ne_zero hτ hd]

/-- The original normalized simple-pole condition survives an actual
nonramified quadratic coordinate pullback. This supplies the local pole
interface for the proved arbitrary-Fd biholomorphic compactification. -/
theorem s31qr_simple_pole_pullback {f r τ : ℂ → ℂ} {p c : ℂ}
    (hτ : AnalyticAt ℂ τ p) (hd : deriv τ p ≠ 0)
    (hz : f (τ p) = 0) (hr : AnalyticAt ℂ r (τ p))
    (he : f =ᶠ[𝓝[≠] (τ p)] (fun z => c / (z - τ p) + r z)) :
    f (τ p) * deriv τ p ^ 2 = 0 ∧
      ∃ (c' : ℂ) (r' : ℂ → ℂ), AnalyticAt ℂ r' p ∧
        (fun z => f (τ z) * deriv τ z ^ 2) =ᶠ[𝓝[≠] p]
          (fun z => c' / (z - p) + r' z) := by
  have hf : MeromorphicAt f (τ p) := s31qr_meromorphic_of_simple_expansion hr he
  have hfo : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f (τ p) :=
    (k31p_simple_pole_normal_form hf).2 ⟨c, r, hr, he⟩
  have hprod : MeromorphicAt (fun z => f (τ z) * deriv τ z ^ 2) p :=
    (hf.comp_analyticAt hτ).mul (hτ.deriv.pow 2).meromorphicAt
  refine ⟨by rw [hz, zero_mul], (k31p_simple_pole_normal_form hprod).1 ?_⟩
  rwa [s31qr_quadratic_pullback_order hτ hd]

/-- Transport of an actual punctured quadratic coefficient family from Xd to
an arbitrary Fd. All input conditions concern the supplied q on Xd; existence
of a reflection extension of an original differential is not assumed here. -/
theorem s31qr_fd_transport_admissible
    (Xd : ClosedRS.{u}) (Pd : Finset Xd.carrier) {gd nd : ℕ}
    (Fd : FiniteTypeStructure (puncturedOpens Pd) gd nd 0)
    (E : Xd.carrier ≃ₜ Fd.X.carrier)
    (hE : IsBiholomorphic (E : Xd.carrier → Fd.X.carrier))
    (hP : ∀ p : Xd.carrier, p ∈ Pd ↔ E p ∈ Fd.P)
    {q : Xd.carrier → ℂ → ℂ} (hq : IsDiffFamily 2 0 q)
    (hregular : ∀ a : Xd.carrier, DifferentiableOn ℂ (q a)
      ((chartAt ℂ a).target ∩ (chartAt ℂ a).symm ⁻¹' (↑Pd : Set Xd.carrier)ᶜ))
    (hpoles : ∀ a : Xd.carrier, ∀ p ∈ Pd, p ∈ (chartAt ℂ a).source →
      q a (chartAt ℂ a p) = 0 ∧
        ∃ (c : ℂ) (r : ℂ → ℂ), AnalyticAt ℂ r (chartAt ℂ a p) ∧
          ∀ᶠ z in 𝓝[≠] (chartAt ℂ a p), q a z = c / (z - chartAt ℂ a p) + r z) :
    IsAdmissibleQD Fd
      (s31qr_transportOn univ E.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ) q) := by
  let H : Fd.X.carrier → Xd.carrier := E.symm
  have hH : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H := hE.homeomorph_symm.1
  have hRange : range Fd.ι = (↑Fd.P : Set Fd.X.carrier)ᶜ := by simpa using Fd.range_ι
  have hmatch : ∀ p : Fd.X.carrier, H p ∈ Pd ↔ p ∈ Fd.P := by
    intro p
    simpa only [H, E.apply_symm_apply] using hP (E.symm p)
  refine ⟨s31qr_holomorphic_transport_family univ H (fun p _ => hH p) q,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hRange]
    have himage : MapsTo H (↑Fd.P : Set Fd.X.carrier)ᶜ (↑Pd : Set Xd.carrier)ᶜ := by
      intro p hp hbad
      exact hp ((hmatch p).1 hbad)
    have hb := s31qr_transport_holomorphic Fd.P.finite_toSet.isClosed.isOpen_compl
      Pd.finite_toSet.isClosed.isOpen_compl
      (fun p _ => hH p) himage hq hregular x
    apply hb.congr
    intro z hz
    have h2 : (chartAt ℂ x).symm z ∈ (↑Fd.P : Set Fd.X.carrier)ᶜ := hz.2
    simp [H, s31qr_transportOn, hz.1, h2]
  · intro x p hp hs
    let a := H p
    let w := chartAt ℂ x p
    let τ : ℂ → ℂ := fun z => chartAt ℂ a (H ((chartAt ℂ x).symm z))
    have hw : w ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hs
    have hleft : (chartAt ℂ x).symm w = p := (chartAt ℂ x).left_inv hs
    have hcenter : τ w = chartAt ℂ a a := by
      change chartAt ℂ a (H ((chartAt ℂ x).symm w)) = chartAt ℂ a a
      rw [hleft]
    have haPd : a ∈ Pd := (hmatch p).2 hp
    obtain ⟨hzero, c, r, hr, he⟩ := hpoles a a haPd (mem_chart_source ℂ a)
    let W : Set ℂ := (chartAt ℂ x).target ∩
      (chartAt ℂ x).symm ⁻¹' (H ⁻¹' (chartAt ℂ a).source)
    have hWo : IsOpen W := (chartAt ℂ x).isOpen_inter_preimage_symm
      ((chartAt ℂ a).open_source.preimage E.symm.continuous)
    have hwW : w ∈ W := by
      refine ⟨hw, ?_⟩
      change H ((chartAt ℂ x).symm w) ∈ (chartAt ℂ a).source
      rw [hleft]
      exact mem_chart_source ℂ a
    have hTd : DifferentiableOn ℂ τ W := by
      intro z hz
      exact (s31qr_coordinate_differentiable x a hz.1 hz.2 (hH _)).differentiableWithinAt
    have hτ : AnalyticAt ℂ τ w := hTd.analyticOnNhd hWo w hwW
    have hd : deriv τ w ≠ 0 :=
      s31qr_coordinate_deriv_ne_zero isOpen_univ (fun z _ => hH z)
        E.symm.injective.injOn x a hw (mem_univ _) hwW.2
    have hzero' : q a (τ w) = 0 := by rwa [hcenter]
    have hr' : AnalyticAt ℂ r (τ w) := by rwa [hcenter]
    have he' : q a =ᶠ[𝓝[≠] (τ w)] (fun z => c / (z - τ w) + r z) := by
      rwa [hcenter]
    obtain ⟨hval, c', r', hr'', hexp⟩ := s31qr_simple_pole_pullback hτ hd hzero' hr' he'
    have hloc : ∀ z ∈ W,
        s31qr_transportOn univ H (LinearMap.id : ℂ →ₗ[ℝ] ℂ) q x z =
          q a (τ z) * deriv τ z ^ 2 := by
      intro z hz
      exact s31qr_transport_local hq x a hz.1 (mem_univ _) hz.2 (hH _)
    refine ⟨(hloc w hwW).trans hval, c', r', hr'', ?_⟩
    filter_upwards [nhdsWithin_le_nhds (s := {w}ᶜ) (hWo.mem_nhds hwW), hexp] with z hz hez
    exact (hloc z hz).trans hez
  · intro x j
    exact Fin.elim0 j
  · intro x j
    exact Fin.elim0 j
  · intro x j
    exact Fin.elim0 j

end LiZhongQC


end
end PointwiseTransferBlock
