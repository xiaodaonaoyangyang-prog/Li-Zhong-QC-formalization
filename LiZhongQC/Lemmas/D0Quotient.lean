import LiZhongQC.Lemmas.FoundationQuotient
import LiZhongQC.Lemmas.S36BersOrdinary
import LiZhongQC.Lemmas.StrebelDoubleDomain

/-! D0-Q standalone source candidate, 2026-10-18.
Frozen contract from iface_v2. No new top-level definitions, structures or instances.
The effective action and analytic quotient follow installed F0's construction,
with affine-domain pole exclusions explicit. No compiler has been invoked. -/
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- D0-Q. The analytic quotient constructor for an open connected ordinary domain.
The domain assumptions are supplied by the preceding producers, not added to D0.
Construct the effective permutation image of the restricted action inside the
proof (as in installed ft0_quotient), then use Mathlib's quotient covering/charts.
The total P outside Ω is irrelevant; only its restriction is asserted continuous
and holomorphic through the local sheet conclusion. -/
theorem s36d0_quotient_of_domain (hΓ : IsFuchsian Γ) {Ω : Set ℂ}
    (hopen : IsOpen Ω) (hconn : IsConnected Ω)
    (hord : ∀ z ∈ Ω, (z : ExtPlane) ∉ fuchsianLimitSet Γ)
    (hinv : ∀ γ ∈ Γ, ∀ z ∈ Ω,
      (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 ∧ h36p_m γ z ∈ Ω)
    (hfix : ∀ γ ∈ Γ, ∀ z ∈ Ω, h36p_m γ z = z → γ = 1 ∨ γ = -1) :
    ∃ (S : Type) (_ : TopologicalSpace S) (_ : ChartedSpace ℂ S) (_ : T2Space S)
      (_ : ConnectedSpace S) (_ : IsManifold 𝓘(ℂ) ω S) (P : ℂ → S),
      P '' Ω = univ ∧
      (∀ z ∈ Ω, ∀ w ∈ Ω, (P z = P w ↔ ∃ γ ∈ Γ, w = h36p_m γ z)) ∧
      ∀ z ∈ Ω, ∃ e : OpenPartialHomeomorph ℂ S, z ∈ e.source ∧ e.source ⊆ Ω ∧ EqOn P e e.source ∧
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target := by
  classical
  -- Source candidate for the approved contract; no compiler has checked it.
  let U : TopologicalSpace.Opens ℂ := ⟨Ω, hopen⟩
  have hcomp : ∀ γ ∈ Γ, ∀ δ ∈ Γ, ∀ z ∈ Ω,
      h36p_m (γ * δ) z = h36p_m γ (h36p_m δ z) := by
    intro γ hγ δ hδ z hz
    apply OnePoint.coe_injective
    rw [← s36x_msl_coe (γ * δ) (hinv _ (mul_mem hγ hδ) z hz).1,
      map_mul, k22_t_mobiusSL_mul,
      s36x_msl_coe δ (hinv δ hδ z hz).1,
      s36x_msl_coe γ (hinv γ hγ _ (hinv δ hδ z hz).2).1]
  have hinverse : ∀ γ ∈ Γ, ∀ z ∈ Ω,
      h36p_m γ⁻¹ (h36p_m γ z) = z := by
    intro γ hγ z hz
    rw [← hcomp γ⁻¹ (inv_mem hγ) γ hγ z hz, inv_mul_cancel, h36p_a_m_one]
  let φ : Γ →* Equiv.Perm U :=
    { toFun := fun γ =>
        { toFun := fun z => ⟨h36p_m γ.1 z.val, (hinv γ.1 γ.2 z.val z.property).2⟩
          invFun := fun z => ⟨h36p_m γ.1⁻¹ z.val, (hinv γ.1⁻¹ (inv_mem γ.2) z.val z.property).2⟩
          left_inv := fun z => Subtype.ext (hinverse γ.1 γ.2 z.val z.property)
          right_inv := fun z => by
            apply Subtype.ext
            simpa only [inv_inv] using hinverse γ.1⁻¹ (inv_mem γ.2) z.val z.property }
      map_one' := by
        apply Equiv.ext
        intro z
        apply Subtype.ext
        exact h36p_a_m_one z.val
      map_mul' := by
        intro γ δ
        apply Equiv.ext
        intro z
        apply Subtype.ext
        exact hcomp γ.1 γ.2 δ.1 δ.2 z.val z.property }
  let G := φ.range
  have hσ : ∀ σ : G, ∃ γ ∈ Γ, ∀ z : U,
      ((σ • z : U) : ℂ) = h36p_m γ z.val := by
    rintro ⟨σ, γ, rfl⟩
    exact ⟨γ.1, γ.2, fun z => rfl⟩
  have hγσ : ∀ γ ∈ Γ, ∃ σ : G, ∀ z : U,
      ((σ • z : U) : ℂ) = h36p_m γ z.val := by
    intro γ hγ
    exact ⟨φ.rangeRestrict ⟨γ, hγ⟩, fun z => rfl⟩
  have hcancel : IsCancelSMul G U := by
    refine isCancelSMul_iff_eq_one_of_smul_eq.2 ?_
    intro σ z he
    obtain ⟨γ, hγ, hσγ⟩ := hσ σ
    have hγz : h36p_m γ z.val = z.val := by
      rw [← hσγ z, he]
    have htriv : ∀ w : U, σ • w = w := by
      intro w
      apply Subtype.ext
      rw [hσγ w]
      rcases hfix γ hγ z.val z.property hγz with h1 | hm1
      · rw [h1, h36p_a_m_one]
      · rw [hm1, h36p_a_m_neg, h36p_a_m_one]
    exact Subtype.ext (Equiv.ext htriv)
  have hcont : ContinuousConstSMul G U := by
    refine ⟨fun σ => ?_⟩
    obtain ⟨γ, hγ, hσγ⟩ := hσ σ
    have he : (fun z : U => ((σ • z : U) : ℂ)) =
        fun z : U => h36p_m γ z.val := funext hσγ
    have hc : Continuous (fun z : U => ((σ • z : U) : ℂ)) := by
      rw [he]
      refine continuous_iff_continuousAt.2 ?_
      intro z
      exact (s36x_m_hasDerivAt γ (hinv γ hγ z.val z.property).1).continuousAt.comp
        continuous_subtype_val.continuousAt
    exact hc.subtype_mk (fun z => (σ • z).property)
  have hpd : ProperlyDiscontinuousSMul G U := by
    refine ⟨fun {K L} hK hL => ?_⟩
    have hKL : IsCompact (((↑) : U → ℂ) '' (K ∪ L)) :=
      (hK.union hL).image continuous_subtype_val
    have hfinite := s36x_fin hΓ (hKL.image OnePoint.continuous_coe) (by
      rintro p ⟨w, ⟨z, hz, rfl⟩, rfl⟩
      exact hord z.val z.property)
    refine (hfinite.image φ.rangeRestrict).subset ?_
    rintro ⟨σ, γ, rfl⟩ ⟨w, ⟨z, hz, rfl⟩, hw⟩
    refine ⟨γ, ?_, rfl⟩
    refine ⟨(((φ γ) z).val : ExtPlane), ?_, ?_⟩
    · refine ⟨(z.val : ExtPlane), ⟨z.val, ⟨z, Or.inl hz, rfl⟩, rfl⟩, ?_⟩
      exact s36x_msl_coe γ.1 (hinv γ.1 γ.2 z.val z.property).1
    · exact ⟨((φ γ) z).val, ⟨(φ γ) z, Or.inr hw, rfl⟩, rfl⟩
  letI : ConnectedSpace U := isConnected_iff_connectedSpace.1 hconn
  letI : LocallyCompactSpace U := hopen.locallyCompactSpace
  let p : U → MulAction.orbitRel.Quotient G U := Quotient.mk _
  have hcov : IsCoveringMap p :=
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap
  have hloc : IsLocalHomeomorph p := hcov.isLocalHomeomorph
  have hporb : ∀ (σ : G) (z : U), p (σ • z) = p z :=
    fun σ z => Quotient.sound ⟨σ, rfl⟩
  have hporbfib : ∀ z w : U, p z = p w ↔
      ∃ γ ∈ Γ, w.val = h36p_m γ z.val := by
    intro z w
    constructor
    · intro he
      obtain ⟨σ, hσz⟩ := Quotient.exact he
      obtain ⟨γ, hγ, hσγ⟩ := hσ σ
      refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
      have hσz' : σ • w = z := hσz
      have hz : z.val = h36p_m γ w.val := by
        rw [← hσγ w, hσz']
      rw [hz, hinverse γ hγ w.val w.property]
    · rintro ⟨γ, hγ, he⟩
      obtain ⟨σ, hσγ⟩ := hγσ γ hγ
      have hw : w = σ • z := Subtype.ext (he.trans (hσγ z).symm)
      rw [hw, hporb]
  let S := MulAction.orbitRel.Quotient G U
  have hcsource : ∀ x : U, (chartAt ℂ x).source = univ := by
    intro x
    simp only [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq,
      OpenPartialHomeomorph.subtypeRestr_source, OpenPartialHomeomorph.refl_source,
      Set.preimage_univ]
  have hccoe : ∀ x y : U, chartAt ℂ x y = y.val := fun x y => rfl
  have hctarget : ∀ x : U, (chartAt ℂ x).target = Ω := by
    intro x
    ext z
    constructor
    · intro hz
      have he : ((chartAt ℂ x).symm z).val = z := (chartAt ℂ x).right_inv hz
      rw [← he]
      exact ((chartAt ℂ x).symm z).property
    · intro hz
      have he := (chartAt ℂ x).map_source (show (⟨z, hz⟩ : U) ∈ (chartAt ℂ x).source by
        rw [hcsource]
        trivial)
      simpa only [hccoe] using he
  let xbase : U := Classical.choice (inferInstance : Nonempty U)
  let i : ℂ → U := (chartAt ℂ xbase).symm
  have hiv : ∀ z ∈ Ω, (i z).val = z := by
    intro z hz
    exact (chartAt ℂ xbase).right_inv (by rwa [hctarget])
  have hic : ∀ z ∈ Ω, ContinuousAt i z := by
    intro z hz
    exact (chartAt ℂ xbase).symm.continuousAt (by rwa [OpenPartialHomeomorph.symm_source, hctarget])
  let P : ℂ → S := fun z => p (i z)
  have hPval : ∀ (z : ℂ) (hz : z ∈ Ω), P z = p (⟨z, hz⟩ : U) := by
    intro z hz
    apply congrArg p
    exact Subtype.ext (hiv z hz)
  have hPc : ∀ z ∈ Ω, ContinuousAt P z := fun z hz =>
    hcov.continuous.continuousAt.comp (hic z hz)
  let eAt : U → OpenPartialHomeomorph S ℂ :=
    fun x => (hloc.localInverseAt x).trans (chartAt ℂ x)
  have hEsource : ∀ x : U, (eAt x).source = (hloc.localInverseAt x).source := by
    intro x
    simp only [eAt, OpenPartialHomeomorph.trans_source, hcsource,
      Set.preimage_univ, Set.inter_univ]
  have hEcoe : ∀ (x : U) (q : S), eAt x q = ((hloc.localInverseAt x) q).val :=
    fun x q => rfl
  have hEtarg : ∀ (x : U) (z : ℂ), z ∈ (eAt x).target → z ∈ Ω := by
    intro x z hz
    rw [OpenPartialHomeomorph.trans_target] at hz
    exact (hctarget x) ▸ hz.1
  have hEsymm : ∀ (x : U) (z : ℂ), z ∈ Ω → (eAt x).symm z = P z := by
    intro x z hz
    show ((hloc.localInverseAt x).trans (chartAt ℂ x)).symm z = P z
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.coe_trans,
      Function.comp_apply, IsLocalHomeomorph.localInverseAt_symm]
    change p ((chartAt ℂ x).symm z) = p (i z)
    apply congrArg p
    apply Subtype.ext
    exact ((chartAt ℂ x).right_inv (by rwa [hctarget])).trans (hiv z hz).symm
  -- A local inverse of the quotient, expressed in the affine coordinate,
  -- agrees near each point with one fixed group element.
  have key : ∀ (x : U) (z : ℂ), z ∈ Ω →
      P z ∈ (hloc.localInverseAt x).source →
      ContDiffAt ℂ ω (fun w => ((hloc.localInverseAt x) (P w)).val) z := by
    intro x z hz hs
    let L := hloc.localInverseAt x
    have he : p (L (P z)) = p (i z) := hloc.apply_localInverseAt_of_mem hs
    obtain ⟨σ, hσz⟩ := Quotient.exact he
    obtain ⟨γ, hγ, hσγ⟩ := hσ σ
    have hf1 : ContinuousAt (fun w => L (P w)) z :=
      (L.continuousAt hs).comp (hPc z hz)
    have hf2 : ContinuousAt (fun w => σ • i w) z :=
      (continuous_const_smul σ).continuousAt.comp (hic z hz)
    have hmem : L (P z) ∈ L.target := L.map_source hs
    have hσz' : σ • i z = L (P z) := hσz
    have h2mem : σ • i z ∈ L.target := by
      rw [hσz']
      exact hmem
    have hev : (fun w => (L (P w)).val) =ᶠ[𝓝 z] h36p_m γ := by
      filter_upwards [hf1.preimage_mem_nhds (L.open_target.mem_nhds hmem),
        hf2.preimage_mem_nhds (L.open_target.mem_nhds h2mem),
        (hPc z hz).preimage_mem_nhds (L.open_source.mem_nhds hs),
        hopen.mem_nhds hz] with w h1 h2 h3 hw
      have heq : L (P w) = σ • i w := by
        apply hloc.injOn_localInverseAt_target h1 h2
        rw [hloc.apply_localInverseAt_of_mem h3, hporb]
      rw [heq, hσγ, hiv w hw]
    have hm : ContDiffAt ℂ ω (h36p_m γ) z := by
      change ContDiffAt ℂ ω (fun w : ℂ =>
        ((γ 0 0 : ℂ) * w + γ 0 1) / ((γ 1 0 : ℂ) * w + γ 1 1)) z
      exact ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const).div
        ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const) (hinv γ hγ z hz).1
    exact hm.congr_of_eventuallyEq hev
  have hatlas : ∀ e ∈ atlas ℂ S, ∃ x : U, e = eAt x := by
    rintro e ⟨q, rfl⟩
    exact ⟨_, rfl⟩
  have hchart : ∀ q : S, ∃ x : U, chartAt ℂ q = eAt x :=
    fun q => ⟨_, rfl⟩
  -- Construct the analytic manifold instance; a topological quotient alone
  -- does not supply this instance.
  have hman : IsManifold 𝓘(ℂ) ω S := by
    refine isManifold_of_contDiffOn _ _ _ ?_
    intro e e' he he'
    obtain ⟨a, rfl⟩ := hatlas e he
    obtain ⟨b, rfl⟩ := hatlas e' he'
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Set.range_id, Set.inter_univ, Set.preimage_id_eq, Function.id_comp, Function.comp_id]
    intro z hz
    rw [OpenPartialHomeomorph.trans_source] at hz
    have hzΩ := hEtarg a z hz.1
    have hs : P z ∈ (hloc.localInverseAt b).source := by
      have hs' := hz.2
      change (eAt a).symm z ∈ (eAt b).source at hs'
      rwa [hEsymm a z hzΩ, hEsource b] at hs'
    have hev : (fun w => ((eAt a).symm.trans (eAt b)) w) =ᶠ[𝓝 z]
        fun w => ((hloc.localInverseAt b) (P w)).val := by
      filter_upwards [hopen.mem_nhds hzΩ] with w hw
      simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
      rw [hEsymm a w hw, hEcoe]
    exact ((key b z hzΩ hs).congr_of_eventuallyEq hev).contDiffWithinAt
  have hMDP : ∀ z ∈ Ω, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) P z := by
    intro z hz
    refine ContMDiffAt.mdifferentiableAt (n := ω) ?_ (by simp)
    rw [contMDiffAt_iff]
    refine ⟨hPc z hz, ?_⟩
    obtain ⟨a, ha⟩ := hchart (P z)
    have hs : P z ∈ (hloc.localInverseAt a).source := by
      have hs' := mem_chart_source ℂ (P z)
      rwa [ha, hEsource a] at hs'
    have hfun : (extChartAt 𝓘(ℂ) (P z) ∘ P ∘ (extChartAt 𝓘(ℂ) z).symm) =
        fun w => ((hloc.localInverseAt a) (P w)).val := by
      funext w
      simp only [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
        PartialEquiv.trans_refl, OpenPartialHomeomorph.toFun_eq_coe,
        OpenPartialHomeomorph.coe_toPartialEquiv_symm, Function.comp_apply, ha, chartAt_self_eq]
      rfl
    rw [hfun]
    simpa [chartAt_self_eq] using (key a z hz hs).contDiffWithinAt
  have hMDE : ∀ (x : U) (q : S), q ∈ (eAt x).source →
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (eAt x) q := by
    intro x q hq
    have hqL : q ∈ (hloc.localInverseAt x).source := (hEsource x) ▸ hq
    obtain ⟨a, ha⟩ := hchart q
    let w₀ : ℂ := chartAt ℂ q q
    have hw₀ : w₀ ∈ (eAt a).target := by
      rw [← ha]
      exact mem_chart_target ℂ q
    have hwΩ := hEtarg a w₀ hw₀
    have hPw : P w₀ = q := by
      rw [← hEsymm a w₀ hwΩ, ← ha]
      exact (chartAt ℂ q).left_inv (mem_chart_source ℂ q)
    have hs : P w₀ ∈ (hloc.localInverseAt x).source := by rwa [hPw]
    have hev : (fun w => eAt x ((chartAt ℂ q).symm w)) =ᶠ[𝓝 w₀]
        fun w => ((hloc.localInverseAt x) (P w)).val := by
      filter_upwards [hopen.mem_nhds hwΩ] with w hw
      rw [ha, hEsymm a w hw, hEcoe]
    have hk : ContDiffAt ℂ ω (fun w => eAt x ((chartAt ℂ q).symm w)) w₀ :=
      (key x w₀ hwΩ hs).congr_of_eventuallyEq hev
    refine ContMDiffAt.mdifferentiableAt (n := ω) ?_ (by simp)
    rw [contMDiffAt_iff]
    refine ⟨(eAt x).continuousAt hq, ?_⟩
    have hfun : (extChartAt 𝓘(ℂ) (eAt x q) ∘ eAt x ∘ (extChartAt 𝓘(ℂ) q).symm) =
        fun w => eAt x ((chartAt ℂ q).symm w) := by
      funext w
      simp only [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
        PartialEquiv.trans_refl, OpenPartialHomeomorph.toFun_eq_coe,
        OpenPartialHomeomorph.coe_toPartialEquiv_symm, Function.comp_apply, chartAt_self_eq]
      rfl
    rw [hfun]
    simpa using hk.contDiffWithinAt
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, hman, P, ?_, ?_, ?_⟩
  · apply Set.eq_univ_of_forall
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    exact ⟨x.val, x.property, hPval x.val x.property⟩
  · intro z hz w hw
    rw [hPval z hz, hPval w hw]
    exact hporbfib ⟨z, hz⟩ ⟨w, hw⟩
  · intro z hz
    let x : U := ⟨z, hz⟩
    have hpx : p x ∈ (eAt x).source := by
      rw [hEsource]
      exact hloc.apply_self_mem_localInverseAt_source
    have hez : eAt x (p x) = z := by
      rw [hEcoe, hloc.localInverseAt_apply_self]
      all_goals rfl
    have hzT : z ∈ (eAt x).target := by
      have ht := (eAt x).map_source hpx
      rwa [hez] at ht
    refine ⟨(eAt x).symm, hzT, fun w hw => hEtarg x w hw,
      fun w hw => (hEsymm x w (hEtarg x w hw)).symm, ?_, ?_⟩
    · intro w hw
      have hev : (eAt x).symm =ᶠ[𝓝 w] P :=
        Filter.eventually_of_mem ((eAt x).open_target.mem_nhds hw)
          (fun y hy => hEsymm x y (hEtarg x y hy))
      exact ((hMDP w (hEtarg x w hw)).congr_of_eventuallyEq hev).mdifferentiableWithinAt
    · intro q hq
      exact (hMDE x q hq).mdifferentiableWithinAt


end LiZhongQC
