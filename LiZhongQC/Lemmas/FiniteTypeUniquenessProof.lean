/- Mechanically assembled round77 proof; see BUNDLE_MAP.json. -/
import LiZhongQC.Lemmas.PunctureMatching
import LiZhongQC.Lemmas.FiniteDiscShrinking
import LiZhongQC.Lemmas.FinitePunctureCompactification
import LiZhongQC.Lemmas.UnitDiscJordan
import LiZhongQC.Lemmas.FiniteTypePunctureEndpoint

/- BEGIN FiniteTypeAssembly | SHA256 5086f681c3055985d1501c92c821d01c67d66d7dbb084bd28e2e4aaac41ac135 -/
section round77_block_01

open Set Filter Topology
open scoped Manifold ContDiff

noncomputable section
namespace LiZhongQC

universe u

/-- A concrete homeomorphism of complements transports an embedded surface
to an embedding with exactly the displayed finite complement. -/
theorem s31fu_embedding_of_complement_homeomorph {S X : Type*}
    [TopologicalSpace S] [TopologicalSpace X]
    (i : S → X) (hi : Topology.IsEmbedding i) {A : Set X}
    (hr : range i = Aᶜ) (Q : Finset X) (e : ↥(Aᶜ) ≃ₜ ↥((↑Q : Set X)ᶜ)) :
    ∃ k : S → X, Topology.IsEmbedding k ∧
      (range k)ᶜ = (↑Q : Set X) := by
  let E : S ≃ₜ ↥((↑Q : Set X)ᶜ) :=
    hi.toHomeomorph.trans ((Homeomorph.setCongr hr).trans e)
  let k : S → X := fun s => (E s).val
  have hk : Topology.IsEmbedding k := Topology.IsEmbedding.subtypeVal.comp E.isEmbedding
  have hkr : range k = (↑Q : Set X)ᶜ := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact (E s).property
    · intro hx
      obtain ⟨s, hs⟩ := E.surjective ⟨x, hx⟩
      exact ⟨s, congrArg Subtype.val hs⟩
  exact ⟨k, hk, by rw [hkr, compl_compl]⟩

/-- Actual local shrinkings of all the deleted discs produce a topological
finite-point embedding into the original compact surface, preserving its
genus without imposing any holomorphic condition on the new embedding. -/
theorem s31fu_filled_embedding {S : Type u} [TopologicalSpace S]
    [ChartedSpace ℂ S] {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    (hclosed : ∀ j, IsClosed (F.D j))
    (hshrink : ∀ j, ∀ A : Set F.X.carrier, IsClosed A → Disjoint (F.D j) A →
      ∃ c ∈ F.D j, ∃ e : ↥((F.D j)ᶜ) ≃ₜ ({c}ᶜ : Set F.X.carrier),
        ∀ x : ↥((F.D j)ᶜ), x.val ∈ A → (e x).val = x.val) :
    ∃ k : S → F.X.carrier, Topology.IsEmbedding k ∧
      ((range k)ᶜ).Finite ∧ ((range k)ᶜ).ncard = n + m := by
  classical
  obtain ⟨Q, hQ, e⟩ := s31fu_shrink_finite F.D Finset.univ
    (fun j _ => hclosed j)
    (fun i _ j _ hij => F.disjoint hij)
    (fun j _ => hshrink j) F.P (fun j _ => F.disjoint_P j)
  have he : Nonempty (↥(((↑F.P : Set F.X.carrier) ∪ ⋃ j, F.D j)ᶜ) ≃ₜ
      ↥((↑Q : Set F.X.carrier)ᶜ)) := by
    have hindex : (⋃ j ∈ (Finset.univ : Finset (Fin m)), F.D j) = ⋃ j, F.D j := by
      ext x
      constructor
      · intro hx
        obtain ⟨j, _, hj⟩ := mem_iUnion₂.1 hx
        exact mem_iUnion.2 ⟨j, hj⟩
      · intro hx
        obtain ⟨j, hj⟩ := mem_iUnion.1 hx
        exact mem_iUnion₂.2 ⟨j, Finset.mem_univ j, hj⟩
    rw [hindex] at e
    exact e
  obtain ⟨E⟩ := he
  obtain ⟨k, hk, hkr⟩ := s31fu_embedding_of_complement_homeomorph
    F.ι F.embedding.isEmbedding F.range_ι Q E
  refine ⟨k, hk, hkr.symm ▸ Q.finite_toSet, ?_⟩
  rw [hkr]
  simpa only [Set.ncard_coe_finset, F.card_P, Finset.card_univ, Fintype.card_fin]
    using hQ

/-- The geometric assembly step. Its inputs are exactly the two local tasks:
supported shrinking of individual discs and actual puncture limits. It proves
all three type equalities; the terminal book theorem must discharge these
local inputs from the original structures. -/
theorem s31fu_type_unique_of_local_geometry {S : Type u}
    [TopologicalSpace S] [ChartedSpace ℂ S] {g n m g' n' m' : ℕ}
    (F : FiniteTypeStructure S g n m) (F' : FiniteTypeStructure S g' n' m')
    (hclosed : ∀ j, IsClosed (F.D j)) (hclosed' : ∀ j, IsClosed (F'.D j))
    (hshrink : ∀ j, ∀ A : Set F.X.carrier, IsClosed A → Disjoint (F.D j) A →
      ∃ c ∈ F.D j, ∃ e : ↥((F.D j)ᶜ) ≃ₜ ({c}ᶜ : Set F.X.carrier),
        ∀ x : ↥((F.D j)ᶜ), x.val ∈ A → (e x).val = x.val)
    (hshrink' : ∀ j, ∀ A : Set F'.X.carrier, IsClosed A → Disjoint (F'.D j) A →
      ∃ c ∈ F'.D j, ∃ e : ↥((F'.D j)ᶜ) ≃ₜ ({c}ᶜ : Set F'.X.carrier),
        ∀ x : ↥((F'.D j)ᶜ), x.val ∈ A → (e x).val = x.val)
    (hend : ∀ p ∈ F.P, ∃ q ∈ F'.P,
      Tendsto F'.ι (comap F.ι (𝓝 p)) (𝓝 q))
    (hend' : ∀ q ∈ F'.P, ∃ p ∈ F.P,
      Tendsto F.ι (comap F'.ι (𝓝 q)) (𝓝 p)) :
    g = g' ∧ n = n' ∧ m = m' := by
  have htrace : ∀ p ∈ F.P, NeBot (comap F.ι (𝓝 p)) := by
    intro p hp
    apply s31fu_puncture_trace_neBot F.ι F.P
      (isClosed_iUnion_of_finite hclosed) F.range_ι
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.1 h
    exact disjoint_left.1 (F.disjoint_P j) hj hp
  have htrace' : ∀ q ∈ F'.P, NeBot (comap F'.ι (𝓝 q)) := by
    intro q hq
    apply s31fu_puncture_trace_neBot F'.ι F'.P
      (isClosed_iUnion_of_finite hclosed') F'.range_ι
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.1 h
    exact disjoint_left.1 (F'.disjoint_P j) hj hq
  have hcard := (s31fu_endpoint_equiv F.ι F'.ι F.P F'.P
    htrace htrace' hend hend').2
  have hn : n = n' := F.card_P.symm.trans (hcard.trans F'.card_P)
  obtain ⟨i, hi, hfi, hci⟩ := s31fu_filled_embedding F hclosed hshrink
  obtain ⟨j, hj, hfj, hcj⟩ := s31fu_filled_embedding F' hclosed' hshrink'
  obtain ⟨hg, ht⟩ := s31fu_finite_complement_comparison F.genus F'.genus
    i j hi hj hfi hfj
  rw [hci, hcj] at ht
  exact ⟨hg, hn, by omega⟩

end LiZhongQC
end -- close original anonymous noncomputable section
end round77_block_01
/- END FiniteTypeAssembly -/

/- BEGIN SphereRadialExtension | SHA256 65b90fe561bcac9b9174cc73b9f1f30dc523fe4e43f264c752fff4cc8bd21e9e -/
section round77_block_02

open Set Metric Filter Topology

noncomputable section
namespace LiZhongQC

/-- A norm-preserving map continuous away from zero is continuous at the
filled-in origin. This supplies the continuity missing from polar coordinates. -/
theorem s31sh_continuous_of_norm {f : ℂ → ℂ} (hf0 : f 0 = 0)
    (hn : ∀ z, ‖f z‖ = ‖z‖) (hc : ContinuousOn f ({0}ᶜ : Set ℂ)) :
    Continuous f := by
  apply continuous_iff_continuousAt.2
  intro z
  by_cases hz : z = 0
  · subst z
    apply Metric.continuousAt_iff.2
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro x hx
    simpa only [hf0, dist_zero_right, hn] using hx
  · exact hc.continuousAt (isOpen_compl_singleton.mem_nhds hz)

/-- A norm-preserving homeomorphism of the punctured plane extends over zero.
Both inverse laws and both continuities are constructed explicitly. -/
theorem s31sh_fill_zero
    (e : ({0}ᶜ : Set ℂ) ≃ₜ ({0}ᶜ : Set ℂ))
    (hn : ∀ z : ({0}ᶜ : Set ℂ), ‖(e z).val‖ = ‖z.val‖) :
    ∃ E : ℂ ≃ₜ ℂ, E 0 = 0 ∧ (∀ z, ‖E z‖ = ‖z‖) ∧
      ∀ z : ({0}ᶜ : Set ℂ), E z.val = (e z).val := by
  classical
  let f : ℂ → ℂ := fun z => if hz : z = 0 then 0 else (e ⟨z, hz⟩).val
  let g : ℂ → ℂ := fun z => if hz : z = 0 then 0 else (e.symm ⟨z, hz⟩).val
  have hf0 : f 0 = 0 := by simp only [f, dif_pos rfl]
  have hg0 : g 0 = 0 := by simp only [g, dif_pos rfl]
  have hfe : ∀ z : ({0}ᶜ : Set ℂ), f z.val = (e z).val := by
    intro z
    exact dif_neg z.property
  have hge : ∀ z : ({0}ᶜ : Set ℂ), g z.val = (e.symm z).val := by
    intro z
    exact dif_neg z.property
  have hfn : ∀ z, ‖f z‖ = ‖z‖ := by
    intro z
    by_cases hz : z = 0
    · rw [hz, hf0]
    · exact (congrArg norm (hfe ⟨z, hz⟩)).trans (hn ⟨z, hz⟩)
  have hgn : ∀ z, ‖g z‖ = ‖z‖ := by
    intro z
    by_cases hz : z = 0
    · rw [hz, hg0]
    · rw [hge ⟨z, hz⟩]
      have h := hn (e.symm ⟨z, hz⟩)
      simpa only [e.apply_symm_apply] using h.symm
  have hfc : Continuous f := by
    apply s31sh_continuous_of_norm hf0 hfn
    apply continuousOn_iff_continuous_domRestrict.2
    have heq : ({0}ᶜ : Set ℂ).domRestrict f = fun z => (e z).val := funext hfe
    rw [heq]
    exact continuous_subtype_val.comp e.continuous
  have hgc : Continuous g := by
    apply s31sh_continuous_of_norm hg0 hgn
    apply continuousOn_iff_continuous_domRestrict.2
    have heq : ({0}ᶜ : Set ℂ).domRestrict g = fun z => (e.symm z).val := funext hge
    rw [heq]
    exact continuous_subtype_val.comp e.symm.continuous
  have hgf : Function.LeftInverse g f := by
    intro z
    by_cases hz : z = 0
    · rw [hz, hf0, hg0]
    · rw [hfe ⟨z, hz⟩, hge (e ⟨z, hz⟩), e.symm_apply_apply]
  have hfg : Function.RightInverse g f := by
    intro z
    by_cases hz : z = 0
    · rw [hz, hg0, hf0]
    · rw [hge ⟨z, hz⟩, hfe (e.symm ⟨z, hz⟩), e.apply_symm_apply]
  exact ⟨{
    toFun := f
    invFun := g
    left_inv := hgf
    right_inv := hfg
    continuous_toFun := hfc
    continuous_invFun := hgc }, hf0, hfn, hfe⟩

/-- Every unit-circle homeomorphism extends radially to a plane homeomorphism
preserving every radius. This is the boundary-alignment step for gluing the
two Caratheodory closed discs; it uses no Schoenflies theorem. -/
theorem s31sh_sphere_radial_extension
    (e : sphere (0 : ℂ) 1 ≃ₜ sphere (0 : ℂ) 1) :
    ∃ E : ℂ ≃ₜ ℂ, E 0 = 0 ∧ (∀ z, ‖E z‖ = ‖z‖) ∧
      ∀ z : sphere (0 : ℂ) 1, E z.val = (e z).val := by
  let H := homeomorphUnitSphereProd ℂ
  let h : ({0}ᶜ : Set ℂ) ≃ₜ ({0}ᶜ : Set ℂ) :=
    H.trans ((e.prodCongr (Homeomorph.refl (Ioi (0 : ℝ)))).trans H.symm)
  have hn : ∀ z : ({0}ᶜ : Set ℂ), ‖(h z).val‖ = ‖z.val‖ := by
    intro z
    have hu : ‖(e (H z).1).val‖ = 1 := mem_sphere_zero_iff_norm.1 (e (H z).1).property
    change ‖(H z).2.val • (e (H z).1).val‖ = ‖z.val‖
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs,
      abs_of_pos (show 0 < (H z).2.val from (H z).2.property)]
    simp only [H, homeomorphUnitSphereProd_apply_snd_coe]
  obtain ⟨E, hE0, hEn, hEh⟩ := s31sh_fill_zero h hn
  refine ⟨E, hE0, hEn, ?_⟩
  intro z
  have hzn : ‖z.val‖ = 1 := mem_sphere_zero_iff_norm.1 z.property
  have hz : z.val ≠ 0 := by
    intro hz0
    have hnorm := hzn
    rw [hz0, norm_zero] at hnorm
    exact zero_ne_one hnorm
  rw [hEh ⟨z.val, hz⟩]
  have hdir : (H ⟨z.val, hz⟩).1 = z := by
    apply Subtype.ext
    simp only [H, homeomorphUnitSphereProd_apply_fst_coe, hzn, inv_one, one_smul]
  change (H ⟨z.val, hz⟩).2.val • (e (H ⟨z.val, hz⟩).1).val = (e z).val
  rw [hdir]
  simp only [H, homeomorphUnitSphereProd_apply_snd_coe, hzn, one_smul]

end LiZhongQC
end -- close original anonymous noncomputable section
end round77_block_02
/- END SphereRadialExtension -/

/- BEGIN JordanExterior | SHA256 cc5236281cecbe25857f82af884630b8a19bb18a25cd489fbd9951e2b7b8baf1 -/
section round77_block_03

open Set Metric Filter Topology

noncomputable section
namespace LiZhongQC

/-- A bounded Jordan domain is regular open also in the one-point plane.
This identifies the closure of its exterior with the complement of its interior. -/
theorem s31sh_jordan_regular_open {J : Set ℂ} (hJ : IsJordanDomain J)
    (hb : Bornology.IsBounded J) : interior (closure (toExt J)) = toExt J := by
  have hJo : IsOpen (toExt J) := isOpen_toExt_iff.2 hJ.1
  apply subset_antisymm
  · intro p hp
    have hpc : p ∈ toExt (closure J) := by
      rw [← closure_toExt_of_isBounded' hb]
      exact interior_subset hp
    obtain ⟨z, hz, rfl⟩ := hpc
    have hi : z ∈ interior (((↑) : ℂ → ExtPlane) ⁻¹' closure (toExt J)) :=
      preimage_interior_subset_interior_preimage OnePoint.continuous_coe hp
    have hpre : ((↑) : ℂ → ExtPlane) ⁻¹' closure (toExt J) = closure J := by
      rw [closure_toExt_of_isBounded' hb]
      ext z
      exact coe_mem_toExt_iff
    rw [hpre] at hi
    have hjplane : IsJordanCurve (toExt (frontier J)) := by
      rw [← frontier_toExt_of_isBounded' hb hJ.1]
      exact hJ.2.2
    exact coe_mem_toExt_iff.2
      (interior_closure_subset_of_isJordanCurve_frontier hJ.1 hJ.2.1 hb hjplane hi)
  · calc
      toExt J = interior (toExt J) := hJo.interior_eq.symm
      _ ⊆ interior (closure (toExt J)) := interior_mono subset_closure

/-- The exterior of a bounded Jordan disc, including infinity, is a connected
open spherical Jordan domain with the same frontier. -/
theorem s31sh_jordan_exterior {J : Set ℂ} (hJ : IsJordanDomain J)
    (hb : Bornology.IsBounded J) :
    IsOpen (closure (toExt J))ᶜ ∧ IsConnected (closure (toExt J))ᶜ ∧
      frontier (closure (toExt J))ᶜ = frontier (toExt J) ∧
      closure (closure (toExt J))ᶜ = (toExt J)ᶜ := by
  have hjplane : IsJordanCurve (toExt (frontier J)) := by
    rw [← frontier_toExt_of_isBounded' hb hJ.1]
    exact hJ.2.2
  obtain ⟨hEc, hEu⟩ :=
    isConnected_compl_closure_of_isJordanCurve_frontier hJ.1 hJ.2.1 hb hjplane
  have heq : (closure (toExt J))ᶜ = toExt (closure J)ᶜ ∪ {extInf} := by
    rw [closure_toExt_of_isBounded' hb, compl_toExt]
  have hconn : IsConnected (closure (toExt J))ᶜ := by
    rw [heq]
    exact ⟨⟨extInf, Or.inr rfl⟩,
      isPreconnected_toExt_union_extInf_of_unbounded hEc.isPreconnected hEu⟩
  have hreg := s31sh_jordan_regular_open hJ hb
  refine ⟨isClosed_closure.isOpen_compl, hconn, ?_, ?_⟩
  · rw [frontier_compl, frontier, closure_closure, hreg,
      frontier, (isOpen_toExt_iff.2 hJ.1).interior_eq]
  · rw [closure_compl, hreg]

/-- Moving an interior point of J to infinity turns the spherical exterior
into a bounded planar Jordan domain. Its closed disc parametrization can
therefore be obtained from the installed Caratheodory theorem. -/
theorem s31sh_bounded_exterior_model {J : Set ℂ} (hJ : IsJordanDomain J)
    (hb : Bornology.IsBounded J) :
    ∃ (W : Set ℂ) (M : ExtPlane ≃ₜ ExtPlane), IsJordanDomain W ∧
      Bornology.IsBounded W ∧
      M '' toExt W = (closure (toExt J))ᶜ ∧
      M '' closure (toExt W) = (toExt J)ᶜ ∧
      M '' frontier (toExt W) = frontier (toExt J) := by
  obtain ⟨c, hc⟩ := hJ.2.1.nonempty
  let T := mobiusHomeomorph 0 1 1 (-c) (uq_j_inv_det c)
  have hTc : T (c : ExtPlane) = extInf := uq_j_mobiusInv_apply_self c
  let B : Set ExtPlane := (closure (toExt J))ᶜ
  let C : Set ExtPlane := (toExt J)ᶜ
  obtain ⟨hBo, hBc, hBfr, hBcl⟩ := s31sh_jordan_exterior hJ hb
  have hCo : IsClosed C := (isOpen_toExt_iff.2 hJ.1).isClosed_compl
  have hBC : B ⊆ C := compl_subset_compl.2 subset_closure
  have hTC : extInf ∉ T '' C := by
    rintro ⟨p, hp, hpe⟩
    have hpc : p = (c : ExtPlane) := T.injective (hpe.trans hTc.symm)
    exact hp (hpc.symm ▸ coe_mem_toExt_iff.2 hc)
  let W : Set ℂ := ((↑) : ℂ → ExtPlane) ⁻¹' (T '' B)
  let K : Set ℂ := ((↑) : ℂ → ExtPlane) ⁻¹' (T '' C)
  have hWeq : toExt W = T '' B :=
    uq_j_toExt_preimage_coe (fun h => hTC (image_mono hBC h))
  have hKeq : toExt K = T '' C := uq_j_toExt_preimage_coe hTC
  have hKc : IsCompact K := by
    have h : IsClosed (toExt K) := by
      rw [hKeq]
      exact T.isClosedMap C hCo
    exact (OnePoint.isClosed_image_coe.1 h).2
  have hWK : W ⊆ K := preimage_mono (image_mono hBC)
  have hWb : Bornology.IsBounded W := hKc.isBounded.subset hWK
  have hWo : IsOpen W := by
    apply isOpen_toExt_iff.1
    rw [hWeq]
    exact T.isOpenMap B hBo
  have hWc : IsConnected W := by
    have h : IsConnected (toExt W) := by
      rw [hWeq]
      exact hBc.image T T.continuous.continuousOn
    refine ⟨?_, OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image.1 h.2⟩
    obtain ⟨p, hp⟩ := h.nonempty
    obtain ⟨z, hz, _⟩ := hp
    exact ⟨z, hz⟩
  have hWj : IsJordanCurve (frontier (toExt W)) := by
    rw [hWeq, ← T.image_frontier, hBfr]
    exact uq_isJordanCurve_image T hJ.2.2
  have himg : T.symm '' toExt W = B := by
    rw [hWeq]
    exact T.toEquiv.symm_image_image B
  refine ⟨W, T.symm, ⟨hWo, hWc, hWj⟩, hWb, himg, ?_, ?_⟩
  · rw [T.symm.image_closure, himg]
    exact hBcl
  · rw [T.symm.image_frontier, himg]
    exact hBfr

end LiZhongQC
end -- close original anonymous noncomputable section
end round77_block_03
/- END JordanExterior -/

/- BEGIN JordanClosedDisc | SHA256 987b594ac25f27a766b4a2ed9c78cbd40345e3fceff6757a67a9039ccda55370 -/
section round77_block_04

open Set Metric Filter Topology

noncomputable section
namespace LiZhongQC

/-- A Caratheodory extension gives an actual homeomorphism of the closed
unit disc onto the spherical domain closure, with the open-disc locus retained. -/
theorem s31sh_closed_disc_of_extension {J : Set ℂ} {f : ℂ → ℂ}
    {F : ExtPlane → ExtPlane} (hf : IsConformalOnto f unitDisc J)
    (hF : IsHomeoExtension f unitDisc J F) :
    ∃ e : closedBall (0 : ℂ) 1 ≃ₜ closure (toExt J),
      ∀ z : closedBall (0 : ℂ) 1, ‖z.val‖ < 1 ↔ (e z).val ∈ toExt J := by
  have hcl : closure (toExt unitDisc) = toExt (closedBall (0 : ℂ) 1) :=
    abN_closure_toExt_unitDisc
  have hsrc : ∀ z : closedBall (0 : ℂ) 1,
      (z.val : ExtPlane) ∈ closure (toExt unitDisc) := by
    intro z
    rw [hcl]
    exact ⟨z.val, z.property, rfl⟩
  let k : closedBall (0 : ℂ) 1 → closure (toExt J) := fun z =>
    ⟨F z.val, hF.2.2.2 ▸ mem_image_of_mem F (hsrc z)⟩
  have hk : Continuous k := by
    apply Continuous.subtype_mk
    exact hF.2.1.comp_continuous
      (OnePoint.continuous_coe.comp continuous_subtype_val) hsrc
  have hki : Function.Injective k := by
    intro z w hzw
    apply Subtype.ext
    apply OnePoint.coe_injective
    exact hF.2.2.1 (hsrc z) (hsrc w) (congrArg Subtype.val hzw)
  have hks : Function.Surjective k := by
    intro y
    have hy : y.val ∈ F '' closure (toExt unitDisc) := hF.2.2.2.symm ▸ y.property
    obtain ⟨p, hp, hpy⟩ := hy
    rw [hcl] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    exact ⟨⟨z, hz⟩, Subtype.ext hpy⟩
  letI : CompactSpace (closedBall (0 : ℂ) 1) := isCompact_iff_compactSpace.1 (isCompact_closedBall (0 : ℂ) 1)
  let e := (hk.isClosedEmbedding hki).isEmbedding.toHomeomorphOfSurjective hks
  refine ⟨e, ?_⟩
  intro z
  change ‖z.val‖ < 1 ↔ F z.val ∈ toExt J
  constructor
  · intro hz
    have hzD : z.val ∈ unitDisc := mem_ball_zero_iff.2 hz
    rw [hF.1 z.val hzD]
    exact coe_mem_toExt_iff.2 (hf.mapsTo hzD)
  · rintro ⟨w, hw, hwe⟩
    obtain ⟨v, hv, hvw⟩ := hf.2.2.symm ▸ hw
    have hFv : F (v : ExtPlane) = F (z.val : ExtPlane) := by
      rw [hF.1 v hv, hvw]
      exact hwe
    have hvz : v = z.val := OnePoint.coe_injective
      (hF.2.2.1 (subset_closure ⟨v, hv, rfl⟩) (hsrc z) hFv)
    exact mem_ball_zero_iff.1 (hvz ▸ hv)

/-- Every planar Jordan domain has a closed-disc parametrization with its
interior distinguished. This directly reuses the installed uniformizer and
Caratheodory extension, rather than reproving boundary correspondence. -/
theorem s31sh_jordan_closed_disc {J : Set ℂ} (hJ : IsJordanDomain J) :
    ∃ e : closedBall (0 : ℂ) 1 ≃ₜ closure (toExt J),
      ∀ z : closedBall (0 : ℂ) 1, ‖z.val‖ < 1 ↔ (e z).val ∈ toExt J := by
  obtain ⟨φ, hφ, Φ, hΦ⟩ := s13x_th_exists_disc_uniformizer hJ
  exact s31sh_closed_disc_of_extension (hφ.symm hJ.1)
    (isHomeoExtension_invFunOn hφ hΦ)

end LiZhongQC
end -- close original anonymous noncomputable section
end round77_block_04
/- END JordanClosedDisc -/

/- BEGIN ClosedCoverHomeomorph | SHA256 361a3d45cf2d0de1bad84b00adbc616fd67d548277f9b6684e188d1b644b7c42 -/
section round77_block_05

open Set Topology

noncomputable section
namespace LiZhongQC

/-- Glue homeomorphisms on a closed two-piece cover. The overlap condition
on the second map prevents two different source pieces from acquiring an
extra intersection. This constructs the global map and proves bijectivity. -/
theorem s31sh_glue_closed_cover {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space Y]
    {P Q : Set X} {P' Q' : Set Y}
    (hP : IsClosed P) (hQ : IsClosed Q) (hcover : P ∪ Q = univ)
    (hcover' : P' ∪ Q' = univ) (p : P ≃ₜ P') (q : Q ≃ₜ Q')
    (hagree : ∀ x (hxP : x ∈ P) (hxQ : x ∈ Q),
      (p ⟨x, hxP⟩).val = (q ⟨x, hxQ⟩).val)
    (hinter : ∀ x : Q, (q x).val ∈ P' ↔ x.val ∈ P) :
    ∃ E : X ≃ₜ Y,
      (∀ x : P, E x.val = (p x).val) ∧
      (∀ x : Q, E x.val = (q x).val) := by
  classical
  have hQof : ∀ x, x ∉ P → x ∈ Q := by
    intro x hx
    have h : x ∈ P ∪ Q := hcover.symm ▸ mem_univ x
    exact h.resolve_left hx
  have hQof' : ∀ y, y ∉ P' → y ∈ Q' := by
    intro y hy
    have h : y ∈ P' ∪ Q' := hcover'.symm ▸ mem_univ y
    exact h.resolve_left hy
  let f : X → Y := fun x => if hx : x ∈ P then (p ⟨x, hx⟩).val
    else (q ⟨x, hQof x hx⟩).val
  have hfP : ∀ x : P, f x.val = (p x).val := by
    intro x
    exact dif_pos x.property
  have hfQ : ∀ x : Q, f x.val = (q x).val := by
    intro x
    by_cases hx : x.val ∈ P
    · rw [show f x.val = (p ⟨x.val, hx⟩).val from dif_pos hx]
      exact hagree x.val hx x.property
    · exact dif_neg hx
  have hfcP : ContinuousOn f P := by
    apply continuousOn_iff_continuous_domRestrict.2
    have heq : P.domRestrict f = fun x => (p x).val := funext hfP
    rw [heq]
    exact continuous_subtype_val.comp p.continuous
  have hfcQ : ContinuousOn f Q := by
    apply continuousOn_iff_continuous_domRestrict.2
    have heq : Q.domRestrict f = fun x => (q x).val := funext hfQ
    rw [heq]
    exact continuous_subtype_val.comp q.continuous
  have hfc : Continuous f := by
    rw [← continuousOn_univ, ← hcover]
    exact hfcP.union_of_isClosed hfcQ hP hQ
  have hseparate : ∀ x y, x ∈ P → y ∉ P → f x ≠ f y := by
    intro x y hx hy hxy
    have hp : f x ∈ P' := by rw [hfP ⟨x, hx⟩]; exact (p ⟨x, hx⟩).property
    have hq : f y ∉ P' := by
      rw [hfQ ⟨y, hQof y hy⟩]
      exact fun h => hy ((hinter ⟨y, hQof y hy⟩).1 h)
    exact hq (hxy ▸ hp)
  have hfi : Function.Injective f := by
    intro x y hxy
    by_cases hx : x ∈ P <;> by_cases hy : y ∈ P
    · rw [hfP ⟨x, hx⟩, hfP ⟨y, hy⟩] at hxy
      exact congrArg Subtype.val (p.injective (Subtype.ext hxy))
    · exact (hseparate x y hx hy hxy).elim
    · exact (hseparate y x hy hx hxy.symm).elim
    · rw [hfQ ⟨x, hQof x hx⟩, hfQ ⟨y, hQof y hy⟩] at hxy
      exact congrArg Subtype.val (q.injective (Subtype.ext hxy))
  have hfs : Function.Surjective f := by
    intro y
    by_cases hy : y ∈ P'
    · refine ⟨(p.symm ⟨y, hy⟩).val, ?_⟩
      rw [hfP (p.symm ⟨y, hy⟩), p.apply_symm_apply]
    · refine ⟨(q.symm ⟨y, hQof' y hy⟩).val, ?_⟩
      rw [hfQ (q.symm ⟨y, hQof' y hy⟩), q.apply_symm_apply]
  exact ⟨(hfc.isClosedEmbedding hfi).isEmbedding.toHomeomorphOfSurjective hfs, hfP, hfQ⟩

end LiZhongQC
end -- close original anonymous noncomputable section
end round77_block_05
/- END ClosedCoverHomeomorph -/

/- BEGIN DiscBoundary | SHA256 6fcecea7f99ec6237936d6e2fd4e7246c192b5bd61a4fdb85c3d45cc69c27687 -/
section round77_block_06

open Set Metric Filter Topology

noncomputable section
namespace LiZhongQC

/-- A closed-disc parametrization that identifies the interior restricts to
an actual homeomorphism of its boundary circle onto the domain frontier. -/
theorem s31sh_disc_boundary {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {A : Set Y} (hA : IsOpen A) (e : closedBall (0 : ℂ) 1 ≃ₜ closure A)
    (hint : ∀ z : closedBall (0 : ℂ) 1, ‖z.val‖ < 1 ↔ (e z).val ∈ A) :
    ∃ b : sphere (0 : ℂ) 1 ≃ₜ frontier A,
      ∀ z : sphere (0 : ℂ) 1,
        (b z).val = (e ⟨z.val, sphere_subset_closedBall z.property⟩).val := by
  let k : sphere (0 : ℂ) 1 → frontier A := fun z =>
    ⟨(e ⟨z.val, sphere_subset_closedBall z.property⟩).val, by
      rw [hA.frontier_eq]
      refine ⟨(e _).property, ?_⟩
      intro hzA
      have hn := (hint ⟨z.val, sphere_subset_closedBall z.property⟩).2 hzA
      have hz : ‖z.val‖ = 1 := mem_sphere_zero_iff_norm.1 z.property
      linarith⟩
  have hk : Continuous k := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      (e.continuous.comp (continuous_subtype_val.subtype_mk _))
  have hki : Function.Injective k := by
    intro z w hzw
    apply Subtype.ext
    have hv : (k z).val = (k w).val :=
      congrArg (fun t : frontier A => t.val) hzw
    have he : e ⟨z.val, sphere_subset_closedBall z.property⟩ =
        e ⟨w.val, sphere_subset_closedBall w.property⟩ := Subtype.ext hv
    exact congrArg (fun t : closedBall (0 : ℂ) 1 => t.val) (e.injective he)
  have hks : Function.Surjective k := by
    intro y
    have hyc : y.val ∈ closure A := frontier_subset_closure y.property
    let z := e.symm ⟨y.val, hyc⟩
    have hle : ‖z.val‖ ≤ 1 := mem_closedBall_zero_iff.1 z.property
    have hnlt : ¬ ‖z.val‖ < 1 := by
      intro hzlt
      have h := (hint z).1 hzlt
      change (e (e.symm ⟨y.val, hyc⟩)).val ∈ A at h
      rw [e.apply_symm_apply] at h
      exact disjoint_left.1 (disjoint_frontier_iff_isOpen.2 hA) y.property h
    have hz : z.val ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.2 (le_antisymm hle (le_of_not_gt hnlt))
    refine ⟨⟨z.val, hz⟩, ?_⟩
    apply Subtype.ext
    change (e z).val = y.val
    exact congrArg Subtype.val (e.apply_symm_apply ⟨y.val, hyc⟩)
  letI : CompactSpace (sphere (0 : ℂ) 1) := isCompact_iff_compactSpace.1 (isCompact_sphere (0 : ℂ) 1)
  exact ⟨(hk.isClosedEmbedding hki).isEmbedding.toHomeomorphOfSurjective hks,
    fun _ => rfl⟩

end LiZhongQC
end -- close original anonymous noncomputable section
end round77_block_06
/- END DiscBoundary -/

/- BEGIN DiscAlignment | SHA256 6510bb2da854da90214c12346e3ae3f30583d9252ab3e7b58e9df249b45aeb78 -/
section round77_block_07

open Set Metric Filter Topology

noncomputable section
namespace LiZhongQC

/-- A homeomorphism of the closed exteriors preserving their boundary loci
restricts to the two frontiers. No extension of a boundary map is assumed. -/
theorem s31sh_exterior_boundary {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (q : ↥(Aᶜ) ≃ₜ ↥(Bᶜ))
    (hq : ∀ x : ↥(Aᶜ), (q x).val ∈ closure B ↔ x.val ∈ closure A) :
    ∃ b : frontier A ≃ₜ frontier B,
      ∀ x : frontier A,
        (b x).val = (q ⟨x.val, disjoint_left.1 (disjoint_frontier_iff_isOpen.2 hA) x.property⟩).val := by
  let f : frontier A → frontier B := fun x =>
    ⟨(q ⟨x.val, disjoint_left.1 (disjoint_frontier_iff_isOpen.2 hA) x.property⟩).val, by
      rw [hB.frontier_eq]
      exact ⟨(hq _).2 (frontier_subset_closure x.property), (q _).property⟩⟩
  let g : frontier B → frontier A := fun y =>
    ⟨(q.symm ⟨y.val, disjoint_left.1 (disjoint_frontier_iff_isOpen.2 hB) y.property⟩).val, by
      rw [hA.frontier_eq]
      refine ⟨(hq _).1 ?_, (q.symm _).property⟩
      rw [q.apply_symm_apply]
      exact frontier_subset_closure y.property⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      (q.continuous.comp (continuous_subtype_val.subtype_mk _))
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      (q.symm.continuous.comp (continuous_subtype_val.subtype_mk _))
  refine ⟨{
    toFun := f
    invFun := g
    continuous_toFun := hf
    continuous_invFun := hg
    left_inv := ?_
    right_inv := ?_ }, fun _ => rfl⟩
  · intro x
    apply Subtype.ext
    change (q.symm (q ⟨x.val, _⟩)).val = x.val
    rw [q.symm_apply_apply]
  · intro y
    apply Subtype.ext
    change (q (q.symm ⟨y.val, _⟩)).val = y.val
    rw [q.apply_symm_apply]

/-- Two closed-disc parametrizations can be aligned to any already supplied
homeomorphism of their exteriors. The correction is the proved radial
extension of the induced circle homeomorphism. -/
theorem s31sh_align_discs {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
    {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (e : closedBall (0 : ℂ) 1 ≃ₜ closure A)
    (e' : closedBall (0 : ℂ) 1 ≃ₜ closure B)
    (hi : ∀ z : closedBall (0 : ℂ) 1, ‖z.val‖ < 1 ↔ (e z).val ∈ A)
    (hi' : ∀ z : closedBall (0 : ℂ) 1, ‖z.val‖ < 1 ↔ (e' z).val ∈ B)
    (q : ↥(Aᶜ) ≃ₜ ↥(Bᶜ))
    (hq : ∀ x : ↥(Aᶜ), (q x).val ∈ closure B ↔ x.val ∈ closure A) :
    ∃ p : closure A ≃ₜ closure B,
      ∀ x (hx : x ∈ closure A) (hx' : x ∉ A),
        (p ⟨x, hx⟩).val = (q ⟨x, hx'⟩).val := by
  obtain ⟨b, hb⟩ := s31sh_disc_boundary hA e hi
  obtain ⟨b', hb'⟩ := s31sh_disc_boundary hB e' hi'
  obtain ⟨bq, hbq⟩ := s31sh_exterior_boundary hA hB q hq
  let a : sphere (0 : ℂ) 1 ≃ₜ sphere (0 : ℂ) 1 := b.trans (bq.trans b'.symm)
  obtain ⟨R, _, hRn, hRb⟩ := s31sh_sphere_radial_extension a
  let Rd : closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1 :=
    R.subtype (fun z => by
      simp only [mem_closedBall_zero_iff, hRn])
  let p : closure A ≃ₜ closure B := e.symm.trans (Rd.trans e')
  refine ⟨p, ?_⟩
  intro x hx hx'
  let z := e.symm ⟨x, hx⟩
  have hzn : ‖z.val‖ = 1 := by
    have hle : ‖z.val‖ ≤ 1 := mem_closedBall_zero_iff.1 z.property
    have hnlt : ¬ ‖z.val‖ < 1 := by
      intro hlt
      have h := (hi z).1 hlt
      change (e (e.symm ⟨x, hx⟩)).val ∈ A at h
      rw [e.apply_symm_apply] at h
      exact hx' h
    exact le_antisymm hle (le_of_not_gt hnlt)
  let zs : sphere (0 : ℂ) 1 := ⟨z.val, mem_sphere_zero_iff_norm.2 hzn⟩
  have hbz : (b zs).val = x := by
    rw [hb zs]
    change (e (e.symm ⟨x, hx⟩)).val = x
    rw [e.apply_symm_apply]
  calc
    (p ⟨x, hx⟩).val =
        (e' ⟨(a zs).val, sphere_subset_closedBall (a zs).property⟩).val := by
      change (e' (Rd z)).val = _
      apply congrArg (fun w : closedBall (0 : ℂ) 1 => (e' w).val)
      apply Subtype.ext
      exact hRb zs
    _ = (b' (a zs)).val := (hb' (a zs)).symm
    _ = (bq (b zs)).val := by
      change (b' (b'.symm (bq (b zs)))).val = _
      rw [b'.apply_symm_apply]
    _ = (q ⟨x, hx'⟩).val := by
      rw [hbq (b zs)]
      apply congrArg (fun w : ↥(Aᶜ) => (q w).val)
      exact Subtype.ext hbz

end LiZhongQC
end -- close original anonymous noncomputable section
end round77_block_07
/- END DiscAlignment -/

/- BEGIN JordanDiscCoordinates | SHA256 230c12afdae3ae6716bcf05913cbd924386616c84b10cb893dd5c6e99294fb3c -/
section round77_block_08

open Set Metric Filter Topology

noncomputable section
namespace LiZhongQC

/-- The closed exterior of a bounded Jordan domain is an actual closed disc;
the puncture at spherical infinity is included in this construction. -/
theorem s31sh_exterior_closed_disc {J : Set ℂ} (hJ : IsJordanDomain J)
    (hb : Bornology.IsBounded J) :
    ∃ e : closedBall (0 : ℂ) 1 ≃ₜ ↥((toExt J)ᶜ),
      ∀ z : closedBall (0 : ℂ) 1,
        ‖z.val‖ < 1 ↔ (e z).val ∉ closure (toExt J) := by
  obtain ⟨W, M, hW, _, himg, hcl, _⟩ := s31sh_bounded_exterior_model hJ hb
  obtain ⟨e, he⟩ := s31sh_jordan_closed_disc hW
  let eM : closure (toExt W) ≃ₜ ↥((toExt J)ᶜ) :=
    (M.isEmbedding.homeomorphImage (closure (toExt W))).trans (Homeomorph.setCongr hcl)
  refine ⟨e.trans eM, ?_⟩
  intro z
  change ‖z.val‖ < 1 ↔ M (e z).val ∈ (closure (toExt J))ᶜ
  rw [he z, ← himg]
  constructor
  · intro hz
    exact ⟨(e z).val, hz, rfl⟩
  · rintro ⟨w, hw, heq⟩
    exact (M.injective heq) ▸ hw

/-- A bounded Jordan disc has spherical coordinates taking the standard
closed unit disc exactly onto its closure. The proof constructs both closed
disc parametrizations, aligns their boundary circles radially, and glues.
It does not invoke the unproved Schoenflies statement in References. -/
theorem s31sh_jordan_disc_coordinates {J : Set ℂ} (hJ : IsJordanDomain J)
    (hb : Bornology.IsBounded J) :
    ∃ H : ExtPlane ≃ₜ ExtPlane,
      H '' closure (toExt unitDisc) = closure (toExt J) := by
  let A : Set ExtPlane := toExt unitDisc
  let B : Set ExtPlane := toExt J
  have hA : IsOpen A := isOpen_toExt_iff.2 isOpen_ball
  have hB : IsOpen B := isOpen_toExt_iff.2 hJ.1
  obtain ⟨e, hi⟩ := s31sh_jordan_closed_disc isJordanDomain_unitDisc
  obtain ⟨e', hi'⟩ := s31sh_jordan_closed_disc hJ
  obtain ⟨f, hf⟩ := s31sh_exterior_closed_disc isJordanDomain_unitDisc isBounded_ball
  obtain ⟨f', hf'⟩ := s31sh_exterior_closed_disc hJ hb
  let q : ↥(Aᶜ) ≃ₜ ↥(Bᶜ) := f.symm.trans f'
  have hq : ∀ x : ↥(Aᶜ), (q x).val ∈ closure B ↔ x.val ∈ closure A := by
    intro x
    have hn : (q x).val ∉ closure B ↔ x.val ∉ closure A := by
      change (f' (f.symm x)).val ∉ closure (toExt J) ↔
        x.val ∉ closure (toExt unitDisc)
      rw [← hf' (f.symm x)]
      simpa only [f.apply_symm_apply] using hf (f.symm x)
    simpa only [not_not] using not_congr hn
  obtain ⟨p, hp⟩ := s31sh_align_discs hA hB e e' hi hi' q hq
  have hcover : closure A ∪ Aᶜ = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ A
    · exact Or.inl (subset_closure hx)
    · exact Or.inr hx
  have hcover' : closure B ∪ Bᶜ = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ B
    · exact Or.inl (subset_closure hx)
    · exact Or.inr hx
  obtain ⟨H, hHP, _⟩ := s31sh_glue_closed_cover isClosed_closure hA.isClosed_compl
    hcover hcover' p q hp hq
  refine ⟨H, ?_⟩
  change H '' closure A = closure B
  apply subset_antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [hHP ⟨x, hx⟩]
    exact (p ⟨x, hx⟩).property
  · intro y hy
    refine ⟨(p.symm ⟨y, hy⟩).val, (p.symm ⟨y, hy⟩).property, ?_⟩
    rw [hHP (p.symm ⟨y, hy⟩), p.apply_symm_apply]

end LiZhongQC
end -- close original anonymous noncomputable section
end round77_block_08
/- END JordanDiscCoordinates -/

/- BEGIN RadialDiscShrinking | SHA256 64b07852db6e14607d530d00d2351e64fa62c614be34ce15190af9261dfdc889 -/
section round77_block_09

open Set Metric Filter Topology

noncomputable section
namespace LiZhongQC

/-- An explicit radius homeomorphism from (1,infinity) to (0,infinity).
The min/max formulas are continuous and become the identity at large radius. -/
theorem s31sh_radius_homeomorph {a : ℝ} (ha : 0 < a) :
    ∃ e : Ioi (1 : ℝ) ≃ₜ Ioi (0 : ℝ),
      (∀ t, (e t).val = min t.val ((t.val - 1) / a)) ∧
      (∀ u, (e.symm u).val = max u.val (1 + a * u.val)) := by
  let f : Ioi (1 : ℝ) → Ioi (0 : ℝ) := fun t =>
    ⟨min t.val ((t.val - 1) / a), lt_min (lt_trans zero_lt_one t.property)
      (div_pos (sub_pos.2 t.property) ha)⟩
  let g : Ioi (0 : ℝ) → Ioi (1 : ℝ) := fun u =>
    ⟨max u.val (1 + a * u.val), lt_of_lt_of_le
      (show (1 : ℝ) < 1 + a * u.val by
        have hp : 0 < a * u.val := mul_pos ha u.property
        linarith) (le_max_right _ _)⟩
  have hgf : Function.LeftInverse g f := by
    intro t
    apply Subtype.ext
    change max (min t.val ((t.val - 1) / a))
      (1 + a * min t.val ((t.val - 1) / a)) = t.val
    by_cases ht : t.val ≤ (t.val - 1) / a
    · rw [min_eq_left ht]
      apply max_eq_left
      have h := (le_div_iff₀ ha).1 ht
      nlinarith
    · have ht' := le_of_not_ge ht
      rw [min_eq_right ht']
      have he : 1 + a * ((t.val - 1) / a) = t.val := by field_simp [ha.ne']; ring
      rw [he, max_eq_right ht']
  have hfg : Function.RightInverse g f := by
    intro u
    apply Subtype.ext
    change min (max u.val (1 + a * u.val))
      ((max u.val (1 + a * u.val) - 1) / a) = u.val
    by_cases hu : 1 + a * u.val ≤ u.val
    · rw [max_eq_left hu]
      apply min_eq_left
      apply (le_div_iff₀ ha).2
      nlinarith
    · have hu' := le_of_not_ge hu
      rw [max_eq_right hu']
      have he : (1 + a * u.val - 1) / a = u.val := by field_simp [ha.ne']; ring
      rw [he, min_eq_right hu']
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.min
      ((continuous_subtype_val.sub continuous_const).div_const a)
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.max
      (continuous_const.add (continuous_const.mul continuous_subtype_val))
  exact ⟨{
    toFun := f
    invFun := g
    left_inv := hgf
    right_inv := hfg
    continuous_toFun := hf
    continuous_invFun := hg }, fun _ => rfl, fun _ => rfl⟩

/-- Polar coordinates on the complement of a closed disc, including radius
zero. The radial factor is strictly positive throughout the domain. -/
theorem s31sh_exterior_polar {r : ℝ} (hr : 0 ≤ r) :
    ∃ e : ↥((closedBall (0 : ℂ) r)ᶜ) ≃ₜ (sphere (0 : ℂ) 1 × Ioi r),
      (∀ z, (e z).1.val = ‖z.val‖⁻¹ • z.val) ∧
      (∀ z, (e z).2.val = ‖z.val‖) ∧
      (∀ p, (e.symm p).val = p.2.val • p.1.val) := by
  have hn : ∀ z : ↥((closedBall (0 : ℂ) r)ᶜ), r < ‖z.val‖ := by
    intro z
    exact lt_of_not_ge (fun h => z.property (mem_closedBall_zero_iff.2 h))
  have hn0 : ∀ z : ↥((closedBall (0 : ℂ) r)ᶜ), 0 < ‖z.val‖ :=
    fun z => lt_of_le_of_lt hr (hn z)
  let f : ↥((closedBall (0 : ℂ) r)ᶜ) → sphere (0 : ℂ) 1 × Ioi r := fun z =>
    (⟨‖z.val‖⁻¹ • z.val, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 (hn0 z)), inv_mul_cancel₀ (hn0 z).ne']⟩,
      ⟨‖z.val‖, hn z⟩)
  let g : sphere (0 : ℂ) 1 × Ioi r → ↥((closedBall (0 : ℂ) r)ᶜ) := fun p =>
    ⟨p.2.val • p.1.val, by
      have hp : 0 < p.2.val := lt_of_le_of_lt hr p.2.property
      have hn : ‖p.1.val‖ = 1 := mem_sphere_zero_iff_norm.1 p.1.property
      intro h
      have hle := mem_closedBall_zero_iff.1 h
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp, hn, mul_one] at hle
      exact not_le_of_gt p.2.property hle⟩
  have hgf : Function.LeftInverse g f := by
    intro z
    apply Subtype.ext
    change ‖z.val‖ • (‖z.val‖⁻¹ • z.val) = z.val
    rw [smul_smul, mul_inv_cancel₀ (hn0 z).ne', one_smul]
  have hfg : Function.RightInverse g f := by
    intro p
    have hp : 0 < p.2.val := lt_of_le_of_lt hr p.2.property
    have hn : ‖p.1.val‖ = 1 := mem_sphere_zero_iff_norm.1 p.1.property
    apply Prod.ext <;> apply Subtype.ext
    · change ‖p.2.val • p.1.val‖⁻¹ • (p.2.val • p.1.val) = p.1.val
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp, hn, mul_one,
        smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
    · change ‖p.2.val • p.1.val‖ = p.2.val
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp, hn, mul_one]
  have hf : Continuous f := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact (continuous_subtype_val.norm.inv₀ (fun z => (hn0 z).ne')).smul continuous_subtype_val
    · exact continuous_subtype_val.norm.subtype_mk _
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)
  exact ⟨{
    toFun := f
    invFun := g
    left_inv := hgf
    right_inv := hfg
    continuous_toFun := hf
    continuous_invFun := hg }, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The standard closed unit disc can be shrunk to its centre by a genuine
homeomorphism of complements, equal to the identity at every radius at least R.
The inverse has the same support bound. -/
theorem s31sh_standard_disc_shrink {R : ℝ} (hR : 1 < R) :
    ∃ e : ↥((closedBall (0 : ℂ) 1)ᶜ) ≃ₜ ({0}ᶜ : Set ℂ),
      (∀ z, R ≤ ‖z.val‖ → (e z).val = z.val) ∧
      (∀ w, R ≤ ‖w.val‖ → (e.symm w).val = w.val) := by
  have hRp : 0 < R := lt_trans zero_lt_one hR
  let a : ℝ := (R - 1) / R
  have ha : 0 < a := div_pos (sub_pos.2 hR) hRp
  have haR : a * R = R - 1 := div_mul_cancel₀ _ hRp.ne'
  obtain ⟨er, her, _⟩ := s31sh_radius_homeomorph ha
  obtain ⟨e1, he1a, he1r, he1i⟩ := s31sh_exterior_polar (r := 1) zero_le_one
  obtain ⟨e0, _, _, he0i⟩ := s31sh_exterior_polar (r := 0) le_rfl
  have hzero : (closedBall (0 : ℂ) 0)ᶜ = ({0}ᶜ : Set ℂ) := by simp
  let e : ↥((closedBall (0 : ℂ) 1)ᶜ) ≃ₜ ({0}ᶜ : Set ℂ) :=
    e1.trans (((Homeomorph.refl (sphere (0 : ℂ) 1)).prodCongr er).trans
      (e0.symm.trans (Homeomorph.setCongr hzero)))
  have he : ∀ z : ↥((closedBall (0 : ℂ) 1)ᶜ),
      (e z).val = min ‖z.val‖ ((‖z.val‖ - 1) / a) • (‖z.val‖⁻¹ • z.val) := by
    intro z
    change (e0.symm ((e1 z).1, er (e1 z).2)).val = _
    rw [he0i, her, he1a, he1r]
  have hfix : ∀ z : ↥((closedBall (0 : ℂ) 1)ᶜ),
      R ≤ ‖z.val‖ → (e z).val = z.val := by
    intro z hz
    have hn : 0 < ‖z.val‖ := lt_of_lt_of_le hRp hz
    have hmin : ‖z.val‖ ≤ (‖z.val‖ - 1) / a := by
      apply (le_div_iff₀ ha).2
      apply (mul_le_mul_iff_right₀ hRp).1
      have heq : ‖z.val‖ * a * R = ‖z.val‖ * (R - 1) := by rw [mul_assoc, haR]
      nlinarith [heq]
    rw [he, min_eq_left hmin, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  refine ⟨e, hfix, ?_⟩
  intro w hw
  have hwu : w.val ∉ closedBall (0 : ℂ) 1 := by
    intro h
    have hn := mem_closedBall_zero_iff.1 h
    linarith
  have hew : e ⟨w.val, hwu⟩ = w := Subtype.ext (hfix ⟨w.val, hwu⟩ hw)
  have h := congrArg (fun y => (e.symm y).val) hew
  simpa only [e.symm_apply_apply] using h.symm

end LiZhongQC
end -- close original anonymous noncomputable section
end round77_block_09
/- END RadialDiscShrinking -/

/- BEGIN OpenSetHomeomorph | SHA256 0f7329cdd09c0a457659bc45ae61355904412175e7660ee85dbcd06f9e620b8d -/
section round77_block_10

open Set Topology

noncomputable section
namespace LiZhongQC

/-- Realize a homeomorphism of two open subsets as an ambient partial
homeomorphism, retaining explicit formulas in both directions. -/
theorem s31sh_open_set_partial {X : Type*} [TopologicalSpace X]
    {s t : Set X} (hs : IsOpen s) (ht : IsOpen t) (h : s ≃ₜ t) :
    ∃ e : OpenPartialHomeomorph X X, e.source = s ∧ e.target = t ∧
      (∀ x : s, e x.val = (h x).val) ∧
      (∀ y : t, e.symm y.val = (h.symm y).val) := by
  classical
  let f : X → X := fun x => if hx : x ∈ s then (h ⟨x, hx⟩).val else x
  let g : X → X := fun y => if hy : y ∈ t then (h.symm ⟨y, hy⟩).val else y
  have hf : ∀ x : s, f x.val = (h x).val := fun x => dif_pos x.property
  have hg : ∀ y : t, g y.val = (h.symm y).val := fun y => dif_pos y.property
  have hfc : ContinuousOn f s := by
    apply continuousOn_iff_continuous_domRestrict.2
    have he : s.domRestrict f = fun x => (h x).val := funext hf
    rw [he]
    exact continuous_subtype_val.comp h.continuous
  have hgc : ContinuousOn g t := by
    apply continuousOn_iff_continuous_domRestrict.2
    have he : t.domRestrict g = fun y => (h.symm y).val := funext hg
    rw [he]
    exact continuous_subtype_val.comp h.symm.continuous
  let e : OpenPartialHomeomorph X X := {
    toFun := f
    invFun := g
    source := s
    target := t
    map_source' := by
      intro x hx
      rw [hf ⟨x, hx⟩]
      exact (h ⟨x, hx⟩).property
    map_target' := by
      intro y hy
      rw [hg ⟨y, hy⟩]
      exact (h.symm ⟨y, hy⟩).property
    left_inv' := by
      intro x hx
      rw [hf ⟨x, hx⟩, hg (h ⟨x, hx⟩), h.symm_apply_apply]
    right_inv' := by
      intro y hy
      rw [hg ⟨y, hy⟩, hf (h.symm ⟨y, hy⟩), h.apply_symm_apply]
    open_source := hs
    open_target := ht
    continuousOn_toFun := hfc
    continuousOn_invFun := hgc }
  exact ⟨e, rfl, rfl, hf, hg⟩

end LiZhongQC
end -- close original anonymous noncomputable section
end round77_block_10
/- END OpenSetHomeomorph -/

/- BEGIN PartialShrinkingPatch | SHA256 7374007708ea197145e5fcde8b55a2b53b5723a63504ac22e40674f4d254306f -/
section round77_block_11

open Set Topology

noncomputable section
namespace LiZhongQC

/-- Patch a local shrinking by the identity outside a closed support set.
Mathlib's partial-homeomorphism pasting theorem supplies both continuities. -/
theorem s31sh_patch_local_shrinking {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X X) {K D : Set X} {c : X}
    (hDK : D ⊆ K) (hcK : c ∈ K)
    (hs : e.source ∩ K = K \ D) (ht : e.target ∩ K = K \ {c})
    (himage : e.IsImage K K) (hfront : frontier K ⊆ e.source)
    (hfix : EqOn e id (frontier K)) :
    ∃ H : ↥(Dᶜ) ≃ₜ ({c}ᶜ : Set X),
      ∀ x : ↥(Dᶜ), x.val ∉ K → (H x).val = x.val := by
  classical
  let i := OpenPartialHomeomorph.refl X
  have hi : i.IsImage K K := by
    intro x hx
    exact Iff.rfl
  have hboundary : e.source ∩ frontier K = i.source ∩ frontier K := by
    change e.source ∩ frontier K = univ ∩ frontier K
    rw [univ_inter, inter_eq_right.2 hfront]
  have hagree : EqOn e i (e.source ∩ frontier K) := fun x hx => hfix hx.2
  let E := e.piecewise i K K himage hi hboundary hagree
  have hEs : E.source = Dᶜ := by
    change (e.source ∩ K ∪ i.source \ K) = Dᶜ
    rw [hs]
    change (K \ D ∪ univ \ K) = Dᶜ
    ext x
    simp only [mem_union, mem_diff, mem_univ, true_and, mem_compl_iff]
    constructor
    · rintro (h | h)
      · exact h.2
      · exact fun hD => h (hDK hD)
    · intro hx
      by_cases hxK : x ∈ K
      · exact Or.inl ⟨hxK, hx⟩
      · exact Or.inr hxK
  have hEt : E.target = ({c}ᶜ : Set X) := by
    change (e.target ∩ K ∪ i.target \ K) = ({c}ᶜ : Set X)
    rw [ht]
    change (K \ {c} ∪ univ \ K) = ({c}ᶜ : Set X)
    ext x
    simp only [mem_union, mem_diff, mem_univ, true_and, mem_compl_iff, mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact h.2
      · intro hxc
        exact h (hxc.symm ▸ hcK)
    · intro hx
      by_cases hxK : x ∈ K
      · exact Or.inl ⟨hxK, hx⟩
      · exact Or.inr hxK
  let H : ↥(Dᶜ) ≃ₜ ({c}ᶜ : Set X) := (Homeomorph.setCongr hEs.symm).trans
    (E.toPartialHomeomorph.toHomeomorphSourceTarget.trans (Homeomorph.setCongr hEt))
  refine ⟨H, ?_⟩
  intro x hx
  change K.piecewise e i x.val = x.val
  rw [piecewise_eq_of_notMem K e i hx]
  rfl

end LiZhongQC
end -- close original anonymous noncomputable section
end round77_block_11
/- END PartialShrinkingPatch -/

/- BEGIN ChartDiscShrinking | SHA256 fa317d298d2ebacf612c1c40d2b0da488540d574d161e265537b0980d4c5d9f3 -/
section round77_block_12

open Set Metric Filter Topology

noncomputable section
namespace LiZhongQC

/-- A standard disc in a genuine topological chart can be shrunk inside any
larger closed coordinate disc. The ambient map is patched by the identity. -/
theorem s31sh_chart_disc_shrink {X : Type*} [TopologicalSpace X] [T2Space X]
    (u : OpenPartialHomeomorph ℂ X) {D U : Set X} {R : ℝ} (hR : 1 < R)
    (hRs : closedBall (0 : ℂ) R ⊆ u.source)
    (hD : u '' closedBall (0 : ℂ) 1 = D)
    (hU : u '' closedBall (0 : ℂ) R ⊆ U) :
    ∃ c ∈ D, ∃ H : ↥(Dᶜ) ≃ₜ ({c}ᶜ : Set X),
      ∀ x : ↥(Dᶜ), x.val ∉ U → (H x).val = x.val := by
  obtain ⟨rH, hrfix, hrifix⟩ := s31sh_standard_disc_shrink hR
  obtain ⟨r, hrs, hrt, hre, hri⟩ := s31sh_open_set_partial
    isClosed_closedBall.isOpen_compl isOpen_compl_singleton rH
  have hrfix' : ∀ z ∈ r.source, R ≤ ‖z‖ → r z = z := by
    intro z hz hzn
    rw [hrs] at hz
    exact (hre ⟨z, hz⟩).trans (hrfix ⟨z, hz⟩ hzn)
  have hrifix' : ∀ z ∈ r.target, R ≤ ‖z‖ → r.symm z = z := by
    intro z hz hzn
    rw [hrt] at hz
    exact (hri ⟨z, hz⟩).trans (hrifix ⟨z, hz⟩ hzn)
  have hrball : ∀ z ∈ r.source, ‖r z‖ ≤ R ↔ ‖z‖ ≤ R := by
    intro z hz
    constructor
    · intro hout
      by_contra hin
      rw [hrfix' z hz (le_of_lt (lt_of_not_ge hin))] at hout
      exact hin hout
    · intro hin
      by_contra hout
      have heq : r z = z :=
        (hrifix' (r z) (r.map_source hz) (le_of_lt (lt_of_not_ge hout))).symm.trans
          (r.left_inv hz)
      rw [heq] at hout
      exact hout hin
  have hriball : ∀ z ∈ r.target, ‖r.symm z‖ ≤ R ↔ ‖z‖ ≤ R := by
    intro z hz
    simpa only [r.right_inv hz] using (hrball (r.symm z) (r.map_target hz)).symm
  let K : Set X := u '' closedBall (0 : ℂ) R
  let c := u 0
  have hunit : closedBall (0 : ℂ) 1 ⊆ closedBall (0 : ℂ) R := closedBall_subset_closedBall hR.le
  have hzero : (0 : ℂ) ∈ closedBall (0 : ℂ) 1 := mem_closedBall_self zero_le_one
  have hcD : c ∈ D := hD ▸ mem_image_of_mem u hzero
  have hDK : D ⊆ K := hD ▸ image_mono hunit
  have hcK : c ∈ K := hDK hcD
  have hKc : IsClosed K :=
    ((isCompact_closedBall 0 R).image_of_continuousOn (u.continuousOn.mono hRs)).isClosed
  have hKt : K ⊆ u.target := by
    rintro x ⟨z, hz, rfl⟩
    exact u.map_source (hRs hz)
  have hcoord : ∀ x ∈ K, u.symm x ∈ closedBall (0 : ℂ) R := by
    rintro x ⟨z, hz, rfl⟩
    rwa [u.left_inv (hRs hz)]
  have hDcoord : ∀ x ∈ K, x ∈ D ↔ u.symm x ∈ closedBall (0 : ℂ) 1 := by
    intro x hx
    constructor
    · intro hxd
      rw [← hD] at hxd
      obtain ⟨z, hz, rfl⟩ := hxd
      rwa [u.left_inv (hRs (hunit hz))]
    · intro hz
      rw [← hD]
      exact ⟨u.symm x, hz, u.right_inv (hKt hx)⟩
  have hcCoord : ∀ x ∈ K, u.symm x = 0 ↔ x = c := by
    intro x hx
    constructor
    · intro h
      rw [← u.right_inv (hKt hx), h]
    · intro h
      rw [h]
      exact u.left_inv (hRs (hunit hzero))
  let e := u.symm.trans (r.trans u)
  have hes : ∀ x ∈ K, x ∈ e.source ↔ x ∉ D := by
    intro x hx
    change (x ∈ u.target ∧ u.symm x ∈ r.source ∧ r (u.symm x) ∈ u.source) ↔ x ∉ D
    constructor
    · intro h hxd
      have hn := h.2.1
      rw [hrs] at hn
      exact hn ((hDcoord x hx).1 hxd)
    · intro hxd
      have hz : u.symm x ∈ r.source := by
        rw [hrs]
        exact fun h => hxd ((hDcoord x hx).2 h)
      refine ⟨hKt hx, hz, hRs (mem_closedBall_zero_iff.2 ?_)⟩
      exact (hrball _ hz).2 (mem_closedBall_zero_iff.1 (hcoord x hx))
  have het : ∀ x ∈ K, x ∈ e.target ↔ x ≠ c := by
    intro x hx
    change ((x ∈ u.target ∧ u.symm x ∈ r.target) ∧ r.symm (u.symm x) ∈ u.source) ↔ x ≠ c
    constructor
    · intro h hxc
      have hn := h.1.2
      rw [hrt] at hn
      exact hn ((hcCoord x hx).2 hxc)
    · intro hxc
      have hz : u.symm x ∈ r.target := by
        rw [hrt]
        exact fun h => hxc ((hcCoord x hx).1 h)
      refine ⟨⟨hKt hx, hz⟩, hRs (mem_closedBall_zero_iff.2 ?_)⟩
      exact (hriball _ hz).2 (mem_closedBall_zero_iff.1 (hcoord x hx))
  have hmaps : ∀ x ∈ e.source, x ∈ K → e x ∈ K := by
    intro x hx hxK
    have hz : u.symm x ∈ r.source := hx.2.1
    refine ⟨r (u.symm x), mem_closedBall_zero_iff.2 ?_, rfl⟩
    exact (hrball _ hz).2 (mem_closedBall_zero_iff.1 (hcoord x hxK))
  have himaps : ∀ x ∈ e.target, x ∈ K → e.symm x ∈ K := by
    intro x hx hxK
    have hz : u.symm x ∈ r.target := hx.1.2
    refine ⟨r.symm (u.symm x), mem_closedBall_zero_iff.2 ?_, rfl⟩
    exact (hriball _ hz).2 (mem_closedBall_zero_iff.1 (hcoord x hxK))
  have himage : e.IsImage K K := by
    intro x hx
    constructor
    · intro hK
      have h := himaps (e x) (e.map_source hx) hK
      rwa [e.left_inv hx] at h
    · exact hmaps x hx
  have hfrontnorm : ∀ x ∈ frontier K, x ∈ K ∧ ‖u.symm x‖ = R := by
    intro x hx
    have hxK : x ∈ K := hKc.closure_eq ▸ frontier_subset_closure hx
    have hle := mem_closedBall_zero_iff.1 (hcoord x hxK)
    refine ⟨hxK, le_antisymm hle (le_of_not_gt ?_)⟩
    intro hlt
    let L := u '' ball (0 : ℂ) R
    have hLo : IsOpen L := u.isOpen_image_of_subset_source isOpen_ball
      (fun z hz => hRs (ball_subset_closedBall hz))
    have hLK : L ⊆ K := image_mono ball_subset_closedBall
    have hxL : x ∈ L := ⟨u.symm x, mem_ball_zero_iff.2 hlt, u.right_inv (hKt hxK)⟩
    have hxint : x ∈ interior K := interior_mono hLK (hLo.interior_eq.symm ▸ hxL)
    exact hx.2 hxint
  have hfront : frontier K ⊆ e.source := by
    intro x hx
    obtain ⟨hxK, hnorm⟩ := hfrontnorm x hx
    apply (hes x hxK).2
    intro hxd
    have hn := mem_closedBall_zero_iff.1 ((hDcoord x hxK).1 hxd)
    rw [hnorm] at hn
    exact not_le_of_gt hR hn
  have hfix : EqOn e id (frontier K) := by
    intro x hx
    obtain ⟨hxK, hnorm⟩ := hfrontnorm x hx
    have hs := hfront hx
    change u (r (u.symm x)) = x
    have hz : u.symm x ∈ r.source := hs.2.1
    have hrad : r (u.symm x) = u.symm x := hrfix' (u.symm x) hz hnorm.ge
    rw [hrad, u.right_inv (hKt hxK)]
  have hs : e.source ∩ K = K \ D := by
    ext x
    exact ⟨fun h => ⟨h.2, (hes x h.2).1 h.1⟩,
      fun h => ⟨(hes x h.1).2 h.2, h.1⟩⟩
  have ht : e.target ∩ K = K \ {c} := by
    ext x
    exact ⟨fun h => ⟨h.2, (het x h.2).1 h.1⟩,
      fun h => ⟨(het x h.1).2 h.2, h.1⟩⟩
  obtain ⟨H, hH⟩ := s31sh_patch_local_shrinking e hDK hcK hs ht himage hfront hfix
  exact ⟨c, hcD, H, fun x hx => hH x (fun hK => hx (hU hK))⟩

end LiZhongQC
end -- close original anonymous noncomputable section
end round77_block_12
/- END ChartDiscShrinking -/

/- BEGIN JordanChartCoordinates | SHA256 1b443496f098933df5446553a0e278d02bf73b5072795e73799bd9c17af123a4 -/
section round77_block_13

open Set Metric Filter Topology

noncomputable section
namespace LiZhongQC

/-- The spherical Jordan-disc coordinates and the given surface chart
compose to a genuine open partial homeomorphism around the deleted disc. -/
theorem s31sh_surface_disc_coordinates {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] {D : Set X} (hD : IsClosedDiscIn D) :
    ∃ u : OpenPartialHomeomorph ℂ X,
      closedBall (0 : ℂ) 1 ⊆ u.source ∧ u '' closedBall (0 : ℂ) 1 = D := by
  obtain ⟨x, hDs, J, hJ, hJb, hJt, hDJ, _⟩ := hD
  let v := chartAt ℂ x
  obtain ⟨H, hH0⟩ := s31sh_jordan_disc_coordinates hJ hJb
  have hH : H '' toExt (closedBall (0 : ℂ) 1) = toExt (closure J) := by
    rw [← abN_closure_toExt_unitDisc, hH0, closure_toExt_of_isBounded' hJb]
  let C : OpenPartialHomeomorph ℂ ExtPlane :=
    OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph ((↑) : ℂ → ExtPlane)
  have hCs : C.source = univ := rfl
  have hCt : C.target = range ((↑) : ℂ → ExtPlane) := by
    exact OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_target ((↑) : ℂ → ExtPlane)
  have hCv : ∀ z : ℂ, C z = (z : ExtPlane) := fun _ => rfl
  have hCi : ∀ z : ℂ, C.symm (z : ExtPlane) = z := by
    intro z
    exact C.left_inv (hCs.symm ▸ mem_univ z)
  let u := (C.trans H.toOpenPartialHomeomorph).trans (C.symm.trans v.symm)
  have hcoords : ∀ z ∈ closedBall (0 : ℂ) 1,
      ∃ w ∈ closure J, H (z : ExtPlane) = (w : ExtPlane) := by
    intro z hz
    have hm : H (z : ExtPlane) ∈ toExt (closure J) :=
      hH ▸ mem_image_of_mem H (coe_mem_toExt_iff.2 hz)
    obtain ⟨w, hw, hwe⟩ := hm
    exact ⟨w, hw, hwe.symm⟩
  have hu : closedBall (0 : ℂ) 1 ⊆ u.source := by
    intro z hz
    obtain ⟨w, hw, hzw⟩ := hcoords z hz
    change (z ∈ C.source ∧ C z ∈ univ) ∧
      H (C z) ∈ C.target ∧ C.symm (H (C z)) ∈ v.target
    refine ⟨⟨hCs.symm ▸ mem_univ z, mem_univ _⟩, ?_, ?_⟩
    · rw [hCv, hzw, hCt]
      exact mem_range_self w
    · rw [hCv, hzw, hCi]
      exact hJt hw
  have huval : ∀ z w : ℂ, H (z : ExtPlane) = (w : ExtPlane) →
      u z = v.symm w := by
    intro z w hzw
    change v.symm (C.symm (H (C z))) = v.symm w
    rw [hCv, hzw, hCi]
  refine ⟨u, hu, ?_⟩
  apply subset_antisymm
  · rintro y ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hzw⟩ := hcoords z hz
    rw [huval z w hzw]
    rw [← hDJ] at hw
    obtain ⟨d, hd, hed⟩ := hw
    rw [← hed, v.left_inv (hDs hd)]
    exact hd
  · intro d hd
    have hm : (v d : ExtPlane) ∈ H '' toExt (closedBall (0 : ℂ) 1) := by
      rw [hH]
      exact coe_mem_toExt_iff.2 (hDJ ▸ mem_image_of_mem v hd)
    obtain ⟨p, hp, hpd⟩ := hm
    obtain ⟨z, hz, rfl⟩ := hp
    refine ⟨z, hz, ?_⟩
    rw [huval z (v d) hpd, v.left_inv (hDs hd)]

/-- A neighborhood of the closed unit disc contains a strictly larger closed
concentric disc. Compact thickening supplies the radius uniformly. -/
theorem s31sh_larger_closed_disc {V : Set ℂ} (hV : IsOpen V)
    (hunit : closedBall (0 : ℂ) 1 ⊆ V) :
    ∃ R : ℝ, 1 < R ∧ closedBall (0 : ℂ) R ⊆ V := by
  obtain ⟨δ, hδ, hδV⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_cthickening_subset_open hV hunit
  let R : ℝ := 1 + δ
  have hRp : 0 < R := by dsimp [R]; linarith
  refine ⟨R, by dsimp [R]; linarith, ?_⟩
  intro z hz
  have hzn : ‖z‖ ≤ R := mem_closedBall_zero_iff.1 hz
  let w : ℂ := R⁻¹ • z
  have hwn : ‖w‖ ≤ 1 := by
    change ‖R⁻¹ • z‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hRp)]
    calc R⁻¹ * ‖z‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hzn (inv_nonneg.2 hRp.le)
      _ = 1 := inv_mul_cancel₀ hRp.ne'
  have hw : R • w = z := by
    change R • (R⁻¹ • z) = z
    rw [smul_smul, mul_inv_cancel₀ hRp.ne', one_smul]
  have hdiff : z - w = δ • w := by
    calc z - w = R • w - (1 : ℝ) • w := by rw [hw, one_smul]
      _ = (R - 1) • w := (sub_smul R 1 w).symm
      _ = δ • w := by congr 1; dsimp [R]; ring
  apply hδV
  apply mem_cthickening_of_dist_le z w δ (closedBall (0 : ℂ) 1)
    (mem_closedBall_zero_iff.2 hwn)
  rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
  nlinarith

/-- Localize the constructed disc coordinates inside any requested open
neighborhood of the actual deleted disc. -/
theorem s31sh_surface_disc_coordinates_in {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] {D U : Set X} (hD : IsClosedDiscIn D)
    (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ (u : OpenPartialHomeomorph ℂ X) (R : ℝ), 1 < R ∧
      closedBall (0 : ℂ) R ⊆ u.source ∧
      u '' closedBall (0 : ℂ) 1 = D ∧ u '' closedBall (0 : ℂ) R ⊆ U := by
  obtain ⟨u, hus, huD⟩ := s31sh_surface_disc_coordinates hD
  have hunit : closedBall (0 : ℂ) 1 ⊆ u.source ∩ u ⁻¹' U := by
    intro z hz
    exact ⟨hus hz, hDU (huD ▸ mem_image_of_mem u hz)⟩
  obtain ⟨R, hR, hRV⟩ := s31sh_larger_closed_disc (u.isOpen_inter_preimage hU) hunit
  refine ⟨u, R, hR, fun z hz => (hRV hz).1, huD, ?_⟩
  rintro x ⟨z, hz, rfl⟩
  exact (hRV hz).2

end LiZhongQC
end -- close original anonymous noncomputable section
end round77_block_13
/- END JordanChartCoordinates -/

/- BEGIN SurfaceDiscShrinking | SHA256 ab738deb2440cd6ae4bdb4206061a787f171e469caf2a51a14904cf27eb6ab0b -/
section round77_block_14

open Set Filter Topology

noncomputable section
namespace LiZhongQC

/-- An actual closed smooth Jordan disc in a surface can be shrunk to an
interior point, with support in any prescribed open neighborhood. All local
coordinates and the homeomorphism are constructed from IsClosedDiscIn. -/
theorem s31sh_surface_disc_shrink {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [T2Space X] {D U : Set X}
    (hD : IsClosedDiscIn D) (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ c ∈ D, ∃ e : ↥(Dᶜ) ≃ₜ ({c}ᶜ : Set X),
      ∀ x : ↥(Dᶜ), x.val ∉ U → (e x).val = x.val := by
  obtain ⟨u, R, hR, hRs, huD, huU⟩ := s31sh_surface_disc_coordinates_in hD hU hDU
  exact s31sh_chart_disc_shrink u hR hRs huD huU

/-- Protected-set form used by finite induction: the shrinking fixes every
point of a closed set disjoint from the given actual disc. -/
theorem s31sh_surface_disc_shrink_away {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [T2Space X] {D A : Set X}
    (hD : IsClosedDiscIn D) (hA : IsClosed A) (hDA : Disjoint D A) :
    ∃ c ∈ D, ∃ e : ↥(Dᶜ) ≃ₜ ({c}ᶜ : Set X),
      ∀ x : ↥(Dᶜ), x.val ∈ A → (e x).val = x.val := by
  obtain ⟨c, hc, e, he⟩ := s31sh_surface_disc_shrink hD hA.isOpen_compl
    (fun x hx hxa => disjoint_left.1 hDA hx hxa)
  exact ⟨c, hc, e, fun x hx => he x (by simpa only [mem_compl_iff, not_not] using hx)⟩

end LiZhongQC
end -- close original anonymous noncomputable section
end round77_block_14
/- END SurfaceDiscShrinking -/

/- BEGIN FiniteTypeUnique | SHA256 2f7845a4eedc72cd46d99d8b10ee46daddfa9f2f59dca5c844b7d3c9c5be4b70 -/
section round77_block_15

open Complex Set Metric Filter Topology
open scoped Manifold ContDiff

noncomputable section
namespace LiZhongQC

universe u


end LiZhongQC
end -- close original anonymous noncomputable section
end round77_block_15
/- END FiniteTypeUnique -/


