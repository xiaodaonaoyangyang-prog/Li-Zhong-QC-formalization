import LiZhongQC.Ch10.S34_BersFiberSpace
import LiZhongQC.Lemmas.UniformizedUniqueness
import LiZhongQC.Lemmas.S34mCore
import LiZhongQC.Lemmas.S34mManifold

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

/-! R83 S34 (下属2): the fibre of the Bers fibre space.  `s34f_uniformize` (`D_φ/G_φ` is a closed Riemann surface of
genus `g` covered holomorphically by `D_φ`), `s34f_embed`, `s34f_j_hol`, the universe transport `s34f_transport`
and `s34f_fibre` (the fibre clauses of `thm34_1_bers`, `X : ClosedRS.{v}`). -/

noncomputable section

namespace LiZhongQC

universe u v

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}


/-- `f_μ|ℍ` and `f^μ|ℍ` have the same complex dilatation, so `c = f^μ ∘ (f_μ|ℍ)⁻¹` is a conformal map of
`D = f_μ(ℍ)` onto `f^μ(ℍ) = ℍ`. -/
theorem s34f_conf (μ : BeltramiH) :
    IsConformalOnto (fMuSym μ.1 ∘ Function.invFunOn (normalizedSolution μ.1) upperHalf)
      (normalizedSolution μ.1 '' upperHalf) upperHalf := by
  obtain ⟨k, hk0, hk1, hμ⟩ := bg_beltramiH_upper μ
  obtain ⟨⟨K, hK⟩, -, -, -, hd⟩ := ut_spec μ
  have hf : IsKQC (normalizedSolution μ.1) upperHalf K := ac_t_isKQC_restrict hK isOpen_upperHalf (subset_univ _)
  obtain ⟨himg, -, -, hKq, hdil⟩ := fMuSym_upperHalf hk0 hk1 hμ
  have hdf : ∀ᵐ z ∂(volume.restrict upperHalf), complexDilatation (fMuSym μ.1) z =
      complexDilatation (normalizedSolution μ.1) z := by
    filter_upwards [hdil, ae_restrict_of_ae hd] with z h1 h2
    rw [h1, h2]
  have := bg_conformal_of_dilatation_eq hf hKq hdf
  rwa [himg] at this




/-- A conformal map of an open set `U` onto `V` is a partial homeomorphism of `ℂ` with source `U`, target `V` and
inverse `invFunOn f U`. -/
theorem s34f_oph_of_conformal {f : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U) (hf : IsConformalOnto f U V) :
    ∃ E : OpenPartialHomeomorph ℂ ℂ, E.source = U ∧ E.target = V ∧ (∀ z ∈ U, E z = f z) ∧
      ∀ w ∈ V, E.symm w = Function.invFunOn f U w := by
  have hV : IsOpen V := hf.isOpen hU
  have hs : IsConformalOnto (Function.invFunOn f U) V U := hf.symm hU
  have hleft : ∀ z ∈ U, Function.invFunOn f U (f z) = z := fun z hz => hf.2.1.leftInvOn_invFunOn hz
  have hright : ∀ w ∈ V, Function.invFunOn f U w ∈ U ∧ f (Function.invFunOn f U w) = w := by
    intro w hw
    rw [← hf.2.2] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    rw [hleft z hz]
    exact ⟨hz, rfl⟩
  refine ⟨{ toFun := f
            invFun := Function.invFunOn f U
            source := U
            target := V
            map_source' := fun z hz => hf.2.2 ▸ mem_image_of_mem f hz
            map_target' := fun w hw => (hright w hw).1
            left_inv' := hleft
            right_inv' := fun w hw => (hright w hw).2
            open_source := hU
            open_target := hV
            continuousOn_toFun := hf.1.continuousOn
            continuousOn_invFun := hs.1.continuousOn }, rfl, rfl, fun z hz => rfl, fun w hw => rfl⟩

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X] [IsManifold 𝓘(ℂ) ω X]

/-- **A local holomorphic sheet of a uniformization.**  Around every `τ ∈ ℍ`, `utm_pext p` is, on an open set
`⊆ ℍ`, a partial homeomorphism `ℂ → X` with holomorphic inverse. -/
theorem s34f_sheet {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hp : IsUniformization Γ' p) (τ : UpperHalfPlane) :
    ∃ e : OpenPartialHomeomorph ℂ X, (τ : ℂ) ∈ e.source ∧ e.source ⊆ upperHalf ∧
      EqOn (utm_pext p) e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source := by
  have hq0 : IsHolQuadDiff (0 : X → ℂ → ℂ) := (holQuadDiffSubmodule X).zero_mem
  obtain ⟨U, hUo, hτU, hUH, hinj, hU⟩ := utm_liftQD_local hq0 hp τ (p τ) (mem_chart_source ℂ (p τ))
  set x : X := p τ with hx
  set H : ℂ → ℂ := fun w => chartAt ℂ x (utm_pext p w) with hH
  have hconf : IsConformalOnto H U (H '' U) :=
    ⟨fun w hw => (hU w hw).2.1.differentiableAt.differentiableWithinAt, hinj, rfl⟩
  obtain ⟨E, hEs, hEt, hEf, hEinv⟩ := s34f_oph_of_conformal hUo hconf
  have hHt : ∀ w ∈ U, H w ∈ (chartAt ℂ x).target := fun w hw =>
    (chartAt ℂ x).map_source (hU w hw).1
  have hsrc : (E.trans (chartAt ℂ x).symm).source = U := by
    ext w
    simp only [OpenPartialHomeomorph.trans_source, hEs, OpenPartialHomeomorph.symm_source, mem_inter_iff,
      mem_preimage]
    constructor
    · exact fun h => h.1
    · intro hw
      exact ⟨hw, by rw [hEf w hw]; exact hHt w hw⟩
  refine ⟨E.trans (chartAt ℂ x).symm, by rw [hsrc]; exact hτU, by rw [hsrc]; exact hUH, ?_, ?_, ?_⟩
  · intro w hw
    rw [hsrc] at hw
    simp only [OpenPartialHomeomorph.trans_apply, hEf w hw]
    exact ((chartAt ℂ x).left_inv (hU w hw).1).symm
  · intro y hy
    have hy' : y ∈ (chartAt ℂ x).source ∧ chartAt ℂ x y ∈ E.target := by
      simpa [OpenPartialHomeomorph.trans_target] using hy
    obtain ⟨hyc, hyE⟩ := hy'
    rw [hEt] at hyE
    obtain ⟨z, hz, hzy⟩ := hyE
    have hsymm : (E.trans (chartAt ℂ x).symm).symm = fun w => E.symm (chartAt ℂ x w) := by
      funext w
      simp [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    rw [hsymm]
    refine MDifferentiableAt.mdifferentiableWithinAt ?_
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x) y :=
      ((contMDiffOn_chart (I := 𝓘(ℂ)) (n := ω)).mdifferentiableOn (by simp) y hyc).mdifferentiableAt
        ((chartAt ℂ x).open_source.mem_nhds hyc)
    have hVo : IsOpen (H '' U) := hconf.isOpen hUo
    have h2 : DifferentiableAt ℂ E.symm (chartAt ℂ x y) := by
      rw [← hzy]
      refine (hconf.differentiableAt_invFunOn hUo hz).congr_of_eventuallyEq ?_
      filter_upwards [hVo.mem_nhds (mem_image_of_mem H hz)] with w hw
      exact hEinv w hw
    exact h2.mdifferentiableAt.comp y h1
  · intro w hw
    rw [hsrc] at hw
    have hE : DifferentiableAt ℂ E w := by
      refine ((hU w hw).2.1.differentiableAt).congr_of_eventuallyEq ?_
      filter_upwards [hUo.mem_nhds hw] with v hv
      rw [hEf v hv]
    have hcs : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x).symm (E w) := by
      rw [hEf w hw]
      exact ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ω)).mdifferentiableOn (by simp) (H w)
        (hHt w hw)).mdifferentiableAt ((chartAt ℂ x).open_target.mem_nhds (hHt w hw))
    exact (hcs.comp w hE.mdifferentiableAt).mdifferentiableWithinAt



/-- **The fibre surface `D_φ/G_φ`.**  For `μ ∈ M(Γ)` there is a closed Riemann surface `X` of genus `g` and a
map `cov : ℂ → X` which on `D_φ = f_μ(ℍ)` is a holomorphic local homeomorphism onto `X` whose fibres are the
`G_φ`-orbits. -/
theorem s34f_uniformize {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) (μ : BeltramiGamma Γ) :
    ∃ (X : ClosedRS.{u}) (cov : ℂ → X.carrier), HasGenus X.carrier g ∧
      (∀ z ∈ bersDisc Γ (bersFunctionGamma μ), ∃ e : OpenPartialHomeomorph ℂ X.carrier, z ∈ e.source ∧
        e.source ⊆ bersDisc Γ (bersFunctionGamma μ) ∧ EqOn cov e e.source ∧
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target) ∧
      cov '' bersDisc Γ (bersFunctionGamma μ) = univ ∧
      (∀ z ∈ bersDisc Γ (bersFunctionGamma μ), ∀ w ∈ bersDisc Γ (bersFunctionGamma μ),
        (cov z = cov w ↔ ∃ γ ∈ Γ, w = bersFiberAction Γ γ (bersFunctionGamma μ) z)) ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) cov (bersDisc Γ (bersFunctionGamma μ)) := by
  classical
  have _ := hg
  have _ := hfree
  haveI : CompactSpace S := hS.1
  obtain ⟨m, hm⟩ := s33v_marked hp μ
  obtain ⟨Γ', p', F, G, hp', hN, hFeq, -⟩ := s27u_exists_uniformization hp m
  set f : ℂ → ℂ := normalizedSolution μ.1.1 with hf
  have hFμ : ∀ τ : UpperHalfPlane, (F τ : ℂ) = fMuSym μ.1.1 τ := fun τ => by
    rw [hFeq τ, hm]; rfl
  have hD : bersDisc Γ (bersFunctionGamma μ) = f '' upperHalf := (bersDisc_wellDefined rfl).2
  have hconf := s34f_conf μ.1
  have hfinj : Function.Injective f := s34_h_injective μ.1
  set c : ℂ → ℂ := fMuSym μ.1.1 ∘ Function.invFunOn f upperHalf with hc
  have hcf : ∀ τ : UpperHalfPlane, c (f τ) = (F τ : ℂ) := fun τ => by
    simp only [hc, Function.comp_apply]
    rw [hfinj.injOn.leftInvOn_invFunOn τ.2, hFμ τ]
  have hp'ext : ∀ τ : UpperHalfPlane, utm_pext p' (F τ : ℂ) = p' (F τ) := fun τ => by
    rw [utm_a_pext_eq p' (F τ).im_pos]
    exact congrArg p' (UpperHalfPlane.ofComplex_apply (F τ))
  set cov : ℂ → m.X.carrier := fun z => utm_pext p' (c z) with hcov
  have hkey : ∀ τ : UpperHalfPlane, cov (f τ) = p' (F τ) := fun τ => by
    simp only [hcov]
    rw [hcf τ, hp'ext τ]
  have hDmem : ∀ z ∈ bersDisc Γ (bersFunctionGamma μ), ∃ τ : UpperHalfPlane, f τ = z := fun z hz => by
    rw [hD] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨⟨w, hw⟩, rfl⟩
  have hDo : IsOpen (f '' upperHalf) := by
    obtain ⟨e, he⟩ := b34_b_homeo μ.1
    have hfe : f = e := he.symm
    rw [hfe]
    exact e.isOpenMap _ isOpen_upperHalf
  have hlift := hN.1
  refine ⟨m.X, cov, hasGenus_of_homeomorph hS m.marking, ?_, ?_, ?_, ?_⟩
  · -- local sheets
    intro z hz
    obtain ⟨τ, rfl⟩ := hDmem z hz
    obtain ⟨Ec, hEs, hEt, hEf, hEinv⟩ := s34f_oph_of_conformal hDo hconf
    obtain ⟨e', hτ'e, he'H, he'eq, he'd, he'f⟩ := s34f_sheet hp' (F τ)
    have hfτ : f τ ∈ f '' upperHalf := ⟨τ, τ.2, rfl⟩
    have hmem : f τ ∈ (Ec.trans e').source := by
      refine ⟨by show f τ ∈ Ec.source; rw [hEs]; exact hfτ, ?_⟩
      show Ec (f τ) ∈ e'.source
      rw [hEf _ hfτ, hcf τ]
      exact hτ'e
    refine ⟨Ec.trans e', hmem, ?_, ?_, ?_⟩
    · intro w hw
      have : w ∈ Ec.source := hw.1
      rw [hEs] at this
      rw [hD]; exact this
    · intro w hw
      have hwD : w ∈ f '' upperHalf := by rw [← hEs]; exact hw.1
      have hw' : Ec w ∈ e'.source := hw.2
      rw [hEf w hwD] at hw'
      show utm_pext p' (c w) = e' (Ec w)
      rw [hEf w hwD]
      exact he'eq hw'
    · intro y hy
      have hy1 : y ∈ e'.target := hy.1
      have hy2 : e'.symm y ∈ Ec.target := hy.2
      have hsymm : ⇑(Ec.trans e').symm = fun y => Ec.symm (e'.symm y) := by
        funext y
        simp [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
      rw [hsymm]
      refine MDifferentiableAt.mdifferentiableWithinAt ?_
      have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e'.symm y :=
        (he'd y hy1).mdifferentiableAt (e'.open_target.mem_nhds hy1)
      have hyH : (e'.symm y) ∈ upperHalf := he'H (e'.map_target hy1)
      have h2 : DifferentiableAt ℂ Ec.symm (e'.symm y) := by
        refine ((hconf.symm hDo).1.differentiableAt (isOpen_upperHalf.mem_nhds hyH)).congr_of_eventuallyEq ?_
        filter_upwards [isOpen_upperHalf.mem_nhds hyH] with w hw
        exact hEinv w hw
      exact h2.mdifferentiableAt.comp y h1
  · apply eq_univ_of_forall
    intro x
    obtain ⟨τ', rfl⟩ := hp'.2.2.1 x
    obtain ⟨τ, rfl⟩ := F.surjective τ'
    exact ⟨f τ, by rw [hD]; exact ⟨τ, τ.2, rfl⟩, hkey τ⟩
  · intro z hz w hw
    obtain ⟨τz, rfl⟩ := hDmem z hz
    obtain ⟨τw, rfl⟩ := hDmem w hw
    rw [hkey, hkey, hlift τz, hlift τw, m.marking.injective.eq_iff, hp.2.2.2 τz τw]
    constructor
    · rintro ⟨γ, hγ, h⟩
      refine ⟨γ, hγ, ?_⟩
      rw [s34m_act_spec hΓ μ hγ τz, h]
    · rintro ⟨γ, hγ, h⟩
      refine ⟨γ, hγ, ?_⟩
      rw [s34m_act_spec hΓ μ hγ τz] at h
      exact UpperHalfPlane.ext (hfinj h).symm
  · intro z hz
    rw [hD] at hz ⊢
    obtain ⟨τ, hτ, rfl⟩ := hz
    obtain ⟨Ec, hEs, hEt, hEf, hEinv⟩ := s34f_oph_of_conformal hDo hconf
    obtain ⟨e', hτ'e, he'H, he'eq, he'd, he'f⟩ := s34f_sheet hp' (F ⟨τ, hτ⟩)
    have hfτ : f τ ∈ f '' upperHalf := ⟨τ, hτ, rfl⟩
    have hcz : c (f τ) = (F ⟨τ, hτ⟩ : ℂ) := hcf ⟨τ, hτ⟩
    have hcd : DifferentiableAt ℂ c (f τ) := hconf.1.differentiableAt (hDo.mem_nhds hfτ)
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e' (c (f τ)) :=
      (he'f _ (by rw [hcz]; exact hτ'e)).mdifferentiableAt (e'.open_source.mem_nhds (by rw [hcz]; exact hτ'e))
    have hev : (fun w => e' (c w)) =ᶠ[𝓝 (f τ)] cov := by
      have hco : ContinuousAt c (f τ) := hcd.continuousAt
      have hmem : ∀ᶠ w in 𝓝 (f τ), c w ∈ e'.source :=
        hco.preimage_mem_nhds (e'.open_source.mem_nhds (by rw [hcz]; exact hτ'e))
      filter_upwards [hmem] with w hw
      exact (he'eq hw).symm
    exact ((h1.comp (f τ) hcd.mdifferentiableAt).congr_of_eventuallyEq hev.symm).mdifferentiableWithinAt



/-- **Transport of a closed Riemann surface along an equivalence** `T ≃ X`, in any universe: the pull-back topology
and the charts `h ≫ chart_{h t}` make `T` a closed Riemann surface and `h : T ≃ₜ X` an isomorphism. -/
theorem s34f_transport {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [T2Space X] [ConnectedSpace X] [CompactSpace X] {T : Type v} (ψ : T ≃ X) :
    ∃ (_ : TopologicalSpace T) (_ : ChartedSpace ℂ T) (_ : T2Space T) (_ : ConnectedSpace T)
      (_ : CompactSpace T) (_ : IsManifold 𝓘(ℂ) ω T) (h : T ≃ₜ X),
      (∀ t, h t = ψ t) ∧ (∀ t, chartAt ℂ t = h.toOpenPartialHomeomorph.trans (chartAt ℂ (ψ t))) ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h.symm := by
  classical
  letI tT : TopologicalSpace T := TopologicalSpace.induced ψ inferInstance
  let h : T ≃ₜ X := ψ.toHomeomorphOfIsInducing ⟨rfl⟩
  have hh : ∀ t, h t = ψ t := fun t => rfl
  let C : T → OpenPartialHomeomorph T ℂ := fun t => h.toOpenPartialHomeomorph.trans (chartAt ℂ (ψ t))
  letI cs : ChartedSpace ℂ T :=
    { atlas := range C
      chartAt := C
      mem_chart_source := fun t => ⟨trivial, mem_chart_source ℂ (ψ t)⟩
      chart_mem_atlas := fun t => ⟨t, rfl⟩ }
  have hA : ∀ e ∈ atlas ℂ T, ∃ c ∈ atlas ℂ X, e = h.toOpenPartialHomeomorph.trans c := by
    rintro e ⟨t, rfl⟩
    exact ⟨chartAt ℂ (ψ t), chart_mem_atlas ℂ _, rfl⟩
  have hman : IsManifold 𝓘(ℂ) ω T := by
    refine isManifold_of_contDiffOn 𝓘(ℂ) ω T fun e e' he he' => ?_
    obtain ⟨c, hc, rfl⟩ := hA e he
    obtain ⟨c', hc', rfl⟩ := hA e' he'
    have hcc := (mem_groupoid_of_pregroupoid.mp
      (HasGroupoid.compatible (G := contDiffGroupoid ω 𝓘(ℂ)) hc hc')).1
    have hfun : (⇑((h.toOpenPartialHomeomorph.trans c).symm.trans (h.toOpenPartialHomeomorph.trans c')) : ℂ → ℂ) =
        ⇑(c.symm.trans c') := by
      funext z
      simp [OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.coe_trans_symm]
    have hsrc : ((h.toOpenPartialHomeomorph.trans c).symm.trans (h.toOpenPartialHomeomorph.trans c')).source =
        (c.symm.trans c').source := by
      ext z
      simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
        Homeomorph.toOpenPartialHomeomorph_source, mem_inter_iff, mem_preimage, mem_univ, true_and, and_true,
        OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply]
      simp
    rw [hfun, hsrc]
    exact hcc
  have hd1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
    intro t
    have hc := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) (M := T) t
    have hc' := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) (M := X) (h t)
    rw [← mdifferentiableWithinAt_univ,
      mdifferentiableWithinAt_iff_of_mem_maximalAtlas hc hc' (mem_chart_source ℂ t) (mem_chart_source ℂ (h t))]
    refine ⟨h.continuous.continuousWithinAt, ?_⟩
    simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp, preimage_univ, range_id, inter_univ]
    have hev : (chartAt ℂ (h t) ∘ h ∘ (chartAt ℂ t).symm) =ᶠ[𝓝 (chartAt ℂ t t)] id := by
      have hmem : (chartAt ℂ (ψ t)).target ∈ 𝓝 (chartAt ℂ t t) := by
        refine (chartAt ℂ (ψ t)).open_target.mem_nhds ?_
        exact (chartAt ℂ (ψ t)).map_source (mem_chart_source ℂ (ψ t))
      filter_upwards [hmem] with w hw
      show chartAt ℂ (h t) (h (h.symm ((chartAt ℂ (ψ t)).symm w))) = w
      rw [Homeomorph.apply_symm_apply]
      exact (chartAt ℂ (ψ t)).right_inv hw
    exact differentiableWithinAt_id.congr_of_eventuallyEq (hev.filter_mono nhdsWithin_le_nhds)
      (hev.self_of_nhds)
  have hd2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h.symm := by
    intro x
    obtain ⟨t, rfl⟩ := h.surjective x
    have hc := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) (M := X) (h t)
    have hc' := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) (M := T) (h.symm (h t))
    rw [← mdifferentiableWithinAt_univ,
      mdifferentiableWithinAt_iff_of_mem_maximalAtlas hc hc' (mem_chart_source ℂ (h t))
        (mem_chart_source ℂ (h.symm (h t)))]
    refine ⟨h.symm.continuous.continuousWithinAt, ?_⟩
    simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp, preimage_univ, range_id, inter_univ]
    have hev : (chartAt ℂ (h.symm (h t)) ∘ h.symm ∘ (chartAt ℂ (h t)).symm) =ᶠ[𝓝 (chartAt ℂ (h t) (h t))] id := by
      have hmem : (chartAt ℂ (h t)).target ∈ 𝓝 (chartAt ℂ (h t) (h t)) :=
        (chartAt ℂ (h t)).open_target.mem_nhds ((chartAt ℂ (h t)).map_source (mem_chart_source ℂ (h t)))
      filter_upwards [hmem] with w hw
      show chartAt ℂ (h.symm (h t)) (h.symm ((chartAt ℂ (h t)).symm w)) = w
      rw [Homeomorph.symm_apply_apply]
      show (h.toOpenPartialHomeomorph.trans (chartAt ℂ (ψ t))) (h.symm ((chartAt ℂ (h t)).symm w)) = w
      simp [OpenPartialHomeomorph.trans_apply, hh]
      have hpsi : ψ (h.symm ((chartAt ℂ (ψ t)).symm w)) = (chartAt ℂ (ψ t)).symm w := by
        rw [← hh]; exact h.apply_symm_apply _
      rw [hpsi]
      exact (chartAt ℂ (ψ t)).right_inv hw
    exact differentiableWithinAt_id.congr_of_eventuallyEq (hev.filter_mono nhdsWithin_le_nhds)
      (hev.self_of_nhds)
  exact ⟨tT, cs, h.isEmbedding.t2Space, h.symm.surjective.connectedSpace h.symm.continuous,
    h.symm.compactSpace, hman, h, hh, fun t => rfl, hd1, hd2⟩


/-- **The fibre embeds.**  Given a surjection `cov : D_φ → X¹` which is a topological local homeomorphism (local
sheets with open sources in `D_φ`) and whose fibres are the `G_φ`-orbits, the map `j₁ : X¹ → V(G₀)`,
`j₁(cov z) = [φ, z]`, is an embedding onto the fibre `pr⁻¹(φ)` (for the quotient topology). -/
theorem s34f_embed (hΓ : IsFuchsian Γ) {m : ℕ} (e : automorphicQD Γ ≃L[ℂ] (Fin m → ℂ))
    (hfin : ∀ φ : automorphicQD Γ, bersNormL (φ : ℂ → ℂ) < ⊤) [τ : TopologicalSpace (BersQuotient Γ)]
    (hτ : τ = TopologicalSpace.coinduced (Quot.mk (bersFiberRel Γ)) inferInstance)
    (q : TeichGamma Γ) {X1 : Type u} [TopologicalSpace X1] (cov : ℂ → X1)
    (hsheet : ∀ z ∈ bersDisc Γ (bersMapGamma Γ q), ∃ E : OpenPartialHomeomorph ℂ X1, z ∈ E.source ∧
      E.source ⊆ bersDisc Γ (bersMapGamma Γ q) ∧ EqOn cov E E.source)
    (hsurj : cov '' bersDisc Γ (bersMapGamma Γ q) = univ)
    (horb : ∀ z ∈ bersDisc Γ (bersMapGamma Γ q), ∀ w ∈ bersDisc Γ (bersMapGamma Γ q),
      (cov z = cov w ↔ ∃ γ ∈ Γ, w = bersFiberAction Γ γ (bersMapGamma Γ q) z)) :
    ∃ j₁ : X1 → BersQuotient Γ, Topology.IsEmbedding j₁ ∧
      range j₁ = bersProjection Γ ⁻¹' {bersMapGamma Γ q} ∧
      ∀ z (hz : z ∈ bersDisc Γ (bersMapGamma Γ q)),
        j₁ (cov z) = Quot.mk _ ⟨(bersMapGamma Γ q, z), ⟨q, rfl⟩, hz⟩ := by
  classical
  set φ : ℂ → ℂ := bersMapGamma Γ q with hφdef
  have hφ : φ ∈ bersImage Γ := ⟨q, rfl⟩
  set D : Set ℂ := bersDisc Γ φ with hD
  set mk : BersFiberSpace Γ → BersQuotient Γ := Quot.mk (bersFiberRel Γ) with hmk
  have hmkc : Continuous mk := by
    rw [hτ]
    exact continuous_coinduced_rng
  have hmko : IsOpenMap mk := by
    rw [hτ]
    exact s34m_mk_isOpenMap hΓ e hfin
  -- the slice
  let ι : D → BersFiberSpace Γ := fun z => ⟨(φ, z), hφ, z.2⟩
  have hιc : Continuous ι :=
    Continuous.subtype_mk (Continuous.prodMk continuous_const continuous_subtype_val) _
  have hDo : IsOpen D := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨E, hzE, hED, -⟩ := hsheet z hz
    exact Filter.mem_of_superset (E.open_source.mem_nhds hzE) hED
  -- relation between slice points and orbits
  have hrel_iff : ∀ z w : D, bersFiberRel Γ (ι z) (ι w) ↔ cov z = cov w := fun z w => by
    rw [horb z z.2 w w.2]
    constructor
    · rintro ⟨γ, hγ, h⟩
      refine ⟨γ, hγ, ?_⟩
      have := congrArg Prod.snd h
      exact this.symm
    · rintro ⟨γ, hγ, h⟩
      exact ⟨γ, hγ, Prod.ext rfl h.symm⟩
  have hcovD : Function.Surjective (fun z : D => cov z) := fun x => by
    have : x ∈ cov '' D := by rw [hsurj]; trivial
    obtain ⟨z, hz, rfl⟩ := this
    exact ⟨⟨z, hz⟩, rfl⟩
  set sec : X1 → D := Function.surjInv hcovD with hsec
  have hsec' : ∀ x, cov (sec x) = x := Function.surjInv_eq hcovD
  set j₁ : X1 → BersQuotient Γ := fun x => mk (ι (sec x)) with hj₁
  have hj₁cov : ∀ z (hz : z ∈ D), j₁ (cov z) = mk (ι ⟨z, hz⟩) := fun z hz => by
    simp only [hj₁]
    have h1 : cov (sec (cov z)) = cov z := hsec' _
    exact Quot.sound ((hrel_iff _ ⟨z, hz⟩).2 h1)
  have hinj : Function.Injective j₁ := fun x y hxy => by
    have h := (s34m_mk_eq_iff hΓ _ _).1 hxy
    have := (hrel_iff _ _).1 h
    rwa [hsec', hsec'] at this
  have hlocj : ∀ (E : OpenPartialHomeomorph ℂ X1) (hEs : E.source ⊆ D), EqOn cov E E.source →
      ∀ y (hy : y ∈ E.target), j₁ y = mk (ι ⟨E.symm y, hEs (E.map_target hy)⟩) := by
    intro E hEs hEq y hy
    have hw := E.map_target hy
    have h1 : cov (E.symm y) = y := by rw [hEq hw, E.right_inv hy]
    have := hj₁cov (E.symm y) (hEs hw)
    rw [h1] at this
    exact this
  have hcont : Continuous j₁ := by
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨E, hxE, hED, hEq⟩ := hsheet (sec x) (sec x).2
    have hxt : x ∈ E.target := by
      have : (sec x : ℂ) ∈ E.source := hxE
      have h2 := E.map_source this
      rwa [← hEq this, hsec'] at h2
    have hg : Continuous (fun y : E.target => mk (ι ⟨E.symm y, hED (E.map_target y.2)⟩)) := by
      refine hmkc.comp (hιc.comp (Continuous.subtype_mk ?_ _))
      exact E.continuousOn_symm.comp_continuous continuous_subtype_val (fun y => y.2)
    have hcon : ContinuousOn j₁ E.target := by
      rw [continuousOn_iff_continuous_restrict]
      have : E.target.domRestrict j₁ = fun y : E.target => mk (ι ⟨E.symm y, hED (E.map_target y.2)⟩) := by
        funext y
        exact hlocj E hED hEq y y.2
      rw [this]
      exact hg
    exact hcon.continuousAt (E.open_target.mem_nhds hxt)
  have hind : Topology.IsInducing j₁ := by
    refine ⟨le_antisymm (continuous_iff_le_induced.1 hcont) ?_⟩
    intro U hU
    rw [isOpen_induced_iff]
    choose E hxE hED hEq using fun x : X1 => hsheet (sec x) (sec x).2
    let W : X1 → Set ℂ := fun x => (E x).source ∩ E x ⁻¹' U
    have hWo : ∀ x, IsOpen (W x) := fun x =>
      (E x).continuousOn.isOpen_inter_preimage (E x).open_source hU
    let P : X1 → Set (BersFiberSpace Γ) := fun x => {y | y.1.2 ∈ W x}
    have hPo : ∀ x, IsOpen (P x) := fun x =>
      (hWo x).preimage (continuous_snd.comp continuous_subtype_val)
    let O : Set (BersQuotient Γ) := ⋃ x ∈ U, mk '' P x
    have hOo : IsOpen O := isOpen_biUnion fun x _ => hmko _ (hPo x)
    refine ⟨O, hOo, ?_⟩
    ext y
    constructor
    · intro hy
      obtain ⟨x, hxU, y', hy'P, hy'⟩ := mem_iUnion₂.1 (show j₁ y ∈ O from hy)
      have hrel := (s34m_mk_eq_iff hΓ y' (ι (sec y))).1 (hy'.trans rfl)
      obtain ⟨γ, hγ, hγe⟩ := hrel
      have h1 : y'.1.1 = φ := by
        have := congrArg Prod.fst hγe
        exact this
      have hw'D : y'.1.2 ∈ D := hED x hy'P.1
      have hy'eq : y' = ι ⟨y'.1.2, hw'D⟩ := Subtype.ext (Prod.ext h1 rfl)
      have hrel2 : bersFiberRel Γ (ι ⟨y'.1.2, hw'D⟩) (ι (sec y)) := by
        rw [← hy'eq]; exact ⟨γ, hγ, hγe⟩
      have hc := (hrel_iff _ _).1 hrel2
      rw [hsec'] at hc
      have hyU : cov y'.1.2 ∈ U := by
        rw [hEq x hy'P.1]; exact hy'P.2
      show y ∈ U
      rw [← hc]
      exact hyU
    · intro hyU
      refine mem_iUnion₂.2 ⟨y, hyU, ι (sec y), ?_, rfl⟩
      refine ⟨hxE y, ?_⟩
      show E y (sec y) ∈ U
      rw [← hEq y (hxE y), hsec']
      exact hyU
  refine ⟨j₁, ⟨hind, hinj⟩, ?_, hj₁cov⟩
  ext v
  rw [bersProjection_fiber φ hφ]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨sec x, (sec x).2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨cov z, hj₁cov z hz⟩


/-- `w ↦ (c, w)` is differentiable. -/
theorem s34f_snoc_diff {n : ℕ} (c : Fin n → ℂ) (z : ℂ) :
    DifferentiableAt ℂ (fun w : ℂ => (Fin.snoc (α := fun _ => ℂ) c w : Fin (n + 1) → ℂ)) z := by
  rw [differentiableAt_pi]
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using differentiableAt_id
  · simpa using differentiableAt_const (c j)

/-- **`j₁` is holomorphic** for the charts of `V(G₀)` given by `bersQuotient_manifold`. -/
theorem s34f_j_hol {g : ℕ} (coords : TeichGamma Γ → Fin (3 * g - 3) → ℂ)
    [τ : TopologicalSpace (BersQuotient Γ)] [cs : ChartedSpace (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ)]
    [hM : IsManifold 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) ω (BersQuotient Γ)]
    (hchart : ∀ x₀ : BersFiberSpace Γ, ∃ e ∈ atlas (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ),
        ∃ N : Set (BersFiberSpace Γ), IsOpen N ∧ x₀ ∈ N ∧
          (Quot.mk (bersFiberRel Γ) '' N : Set (BersQuotient Γ)) = e.source ∧
          ∀ x ∈ N, ∀ q : TeichGamma Γ, x.1.1 = bersMapGamma Γ q →
            e (Quot.mk (bersFiberRel Γ) x) = Fin.snoc (α := fun _ => ℂ) (coords q) x.1.2)
    (q : TeichGamma Γ) {X1 : Type u} [TopologicalSpace X1] [ChartedSpace ℂ X1] (cov : ℂ → X1)
    (hsh : ∀ z ∈ bersDisc Γ (bersMapGamma Γ q), ∃ E : OpenPartialHomeomorph ℂ X1, z ∈ E.source ∧
      E.source ⊆ bersDisc Γ (bersMapGamma Γ q) ∧ EqOn cov E E.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) E.symm E.target)
    (hsurj : cov '' bersDisc Γ (bersMapGamma Γ q) = univ)
    (j₁ : X1 → BersQuotient Γ) (hj₁c : Continuous j₁)
    (hj₁cov : ∀ z (hz : z ∈ bersDisc Γ (bersMapGamma Γ q)),
      j₁ (cov z) = Quot.mk _ ⟨(bersMapGamma Γ q, z), ⟨q, rfl⟩, hz⟩) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) j₁ := by
  classical
  intro x
  obtain ⟨z, hz, rfl⟩ : x ∈ cov '' bersDisc Γ (bersMapGamma Γ q) := by rw [hsurj]; trivial
  obtain ⟨E, hzE, hED, hEq, hEd⟩ := hsh z hz
  set φ : ℂ → ℂ := bersMapGamma Γ q with hφ
  let x₀ : BersFiberSpace Γ := ⟨(φ, z), ⟨q, rfl⟩, hz⟩
  obtain ⟨ε, hε, N, hNo, hx₀N, hNε, hNsnoc⟩ := hchart x₀
  obtain ⟨N', hN'o, hNN'⟩ := isOpen_induced_iff.1 hNo
  have hgz : j₁ (E z) = Quot.mk _ x₀ := by rw [← hEq hzE]; exact hj₁cov z hz
  have hmem : j₁ (E z) ∈ ε.source := by
    rw [hgz, ← hNε]; exact ⟨x₀, hx₀N, rfl⟩
  -- the neighbourhood on which `ε ∘ j₁ ∘ E = (coords q, w)`
  set W0 : Set ℂ := {w | (φ, w) ∈ N'} ∩ E.source with hW0
  have hW0o : IsOpen W0 :=
    (hN'o.preimage (Continuous.prodMk continuous_const continuous_id)).inter E.open_source
  have hzW0 : z ∈ W0 := ⟨by
    have : x₀ ∈ N := hx₀N
    rw [← hNN'] at this
    exact this, hzE⟩
  have hεg : ∀ w ∈ W0, ε (j₁ (E w)) = Fin.snoc (α := fun _ => ℂ) (coords q) w := by
    intro w hw
    have hwD : w ∈ bersDisc Γ φ := hED hw.2
    have hwN : (⟨(φ, w), ⟨q, rfl⟩, hwD⟩ : BersFiberSpace Γ) ∈ N := by
      rw [← hNN']; exact hw.1
    rw [← hEq hw.2, hj₁cov w hwD]
    exact hNsnoc _ hwN q rfl
  have hg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) (fun w => j₁ (E w)) z := by
    have hc := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) (M := ℂ) z
    have hε' : ε ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) 1 (BersQuotient Γ) :=
      IsManifold.subset_maximalAtlas hε
    rw [← mdifferentiableWithinAt_univ,
      mdifferentiableWithinAt_iff_of_mem_maximalAtlas hc hε' (mem_chart_source ℂ z) hmem]
    refine ⟨((hj₁c.continuousAt).comp (E.continuousAt hzE)).continuousWithinAt, ?_⟩
    simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp,
      preimage_univ, range_id, inter_univ, chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
      OpenPartialHomeomorph.refl_symm, id]
    refine (s34f_snoc_diff (coords q) z).differentiableWithinAt.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [nhdsWithin_le_nhds (hW0o.mem_nhds hzW0)] with w hw
      exact hεg w hw
    · exact hεg z hzW0
  have hEs : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) E.symm (E z) := by
    have hzt : E z ∈ E.target := E.map_source hzE
    exact (hEd (E z) hzt).mdifferentiableAt (E.open_target.mem_nhds hzt)
  have hg' : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) (fun w => j₁ (E w)) (E.symm (E z)) := by
    rw [E.left_inv hzE]; exact hg
  have hcomp := hg'.comp (E z) hEs
  rw [hEq hzE]
  refine hcomp.congr_of_eventuallyEq ?_
  have hzt : E z ∈ E.target := E.map_source hzE
  filter_upwards [E.open_target.mem_nhds hzt] with y hy
  show j₁ y = j₁ (E (E.symm y))
  rw [E.right_inv hy]


/-- **The fibre is a holomorphic embedded copy of `D_φ/G_φ`**, in any universe `v`. -/
theorem s34f_fibre {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p)
    (coords : TeichGamma Γ → Fin (3 * g - 3) → ℂ) (hinj : Function.Injective coords)
    (hopen : IsOpen (range coords)) (τ : TopologicalSpace (BersQuotient Γ))
    (hτ : τ = TopologicalSpace.coinduced (Quot.mk (bersFiberRel Γ)) inferInstance)
    (cs : ChartedSpace (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ))
    (hM : IsManifold 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) ω (BersQuotient Γ))
    (hchart : ∀ x₀ : BersFiberSpace Γ, ∃ e ∈ atlas (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ),
        ∃ N : Set (BersFiberSpace Γ), IsOpen N ∧ x₀ ∈ N ∧
          (Quot.mk (bersFiberRel Γ) '' N : Set (BersQuotient Γ)) = e.source ∧
          ∀ x ∈ N, ∀ q : TeichGamma Γ, x.1.1 = bersMapGamma Γ q →
            e (Quot.mk (bersFiberRel Γ) x) = Fin.snoc (α := fun _ => ℂ) (coords q) x.1.2)
    (q : TeichGamma Γ) :
    ∃ (X : ClosedRS.{v}) (j : X.carrier → BersQuotient Γ) (cov : ℂ → X.carrier),
      HasGenus X.carrier g ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) j ∧ Topology.IsEmbedding j ∧
      range j = bersProjection Γ ⁻¹' {bersMapGamma Γ q} ∧
      (∀ z (hz : z ∈ bersDisc Γ (bersMapGamma Γ q)),
        j (cov z) = Quot.mk _ ⟨(bersMapGamma Γ q, z), ⟨q, rfl⟩, hz⟩) ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) cov (bersDisc Γ (bersMapGamma Γ q)) ∧
      ∀ z ∈ bersDisc Γ (bersMapGamma Γ q), ∀ w ∈ bersDisc Γ (bersMapGamma Γ q),
        (cov z = cov w ↔ ∃ γ ∈ Γ, w = bersFiberAction Γ γ (bersMapGamma Γ q) z) := by
  classical
  obtain ⟨e, hfin, -, -⟩ := s34m_coords hg hS hΓ hp
  obtain ⟨X1, cov, hgen, hsheet, hsurj, horb, hhol⟩ := s34f_uniformize hg hS hΓ hfree hp (Quotient.out q)
  have hb : bersMapGamma Γ q = bersFunctionGamma (Quotient.out q) := rfl
  rw [← hb] at hsheet hsurj horb hhol
  have hsh : ∀ z ∈ bersDisc Γ (bersMapGamma Γ q), ∃ E : OpenPartialHomeomorph ℂ X1.carrier, z ∈ E.source ∧
      E.source ⊆ bersDisc Γ (bersMapGamma Γ q) ∧ EqOn cov E E.source := fun z hz => by
    obtain ⟨E, h1, h2, h3, -⟩ := hsheet z hz
    exact ⟨E, h1, h2, h3⟩
  obtain ⟨j₁, hemb, hrange, hj₁cov⟩ := s34f_embed hΓ e hfin hτ q cov hsh hsurj horb
  have hj₁hol := s34f_j_hol coords hchart q cov hsheet hsurj j₁ hemb.continuous hj₁cov
  let ψ : ULift.{v} (range j₁) ≃ X1.carrier :=
    Equiv.ulift.trans (Equiv.ofInjective j₁ hemb.injective).symm
  obtain ⟨tT, cs', t2, cn, cp, hman, h, hh, hch, hd1, hd2⟩ := s34f_transport ψ
  have hjh : ∀ t, (t.down : BersQuotient Γ) = j₁ (h t) := fun t => by
    rw [hh t]
    exact (Equiv.apply_ofInjective_symm hemb.injective t.down).symm
  have hhs : ∀ x, h.symm x = ψ.symm x := fun x => by
    apply ψ.injective
    rw [← hh, h.apply_symm_apply, ψ.apply_symm_apply]
  have hjj : (fun t : ULift.{v} (range j₁) => (t.down : BersQuotient Γ)) = j₁ ∘ h := funext hjh
  refine ⟨⟨ULift.{v} (range j₁)⟩, fun t => (t.down : BersQuotient Γ), fun z => ψ.symm (cov z), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨cp, fun x => ?_⟩
    obtain ⟨e'⟩ := hgen.2 (h x)
    exact ⟨(fundamentalGroupMulEquivOfHomeomorph h rfl).trans e'⟩
  · rw [hjj]
    exact hj₁hol.comp hd1
  · rw [hjj]
    exact hemb.comp h.isEmbedding
  · rw [hjj, Function.Surjective.range_comp h.surjective, hrange]
  · intro z hz
    have h1 : ((ψ.symm (cov z)).down : BersQuotient Γ) = j₁ (cov z) := by
      rw [hjh, hh, ψ.apply_symm_apply]
    exact h1.trans (hj₁cov z hz)
  · have : (fun z => ψ.symm (cov z)) = h.symm ∘ cov := funext fun z => (hhs (cov z)).symm
    rw [this]
    exact hd2.comp_mdifferentiableOn hhol
  · intro z hz w hw
    rw [ψ.symm.injective.eq_iff]
    exact horb z hz w hw


end LiZhongQC
