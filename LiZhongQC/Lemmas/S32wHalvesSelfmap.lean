import LiZhongQC.Lemmas.S32wSideConstant
import LiZhongQC.Lemmas.S32wSidesPreserved
import LiZhongQC.Lemmas.S32wSeamElement
import LiZhongQC.Lemmas.S32wBdryFixedPoints
import LiZhongQC.Ch09.S31_FiniteType

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u

/-- Local-homeomorphism version of `h23l_chart_proj`: `ψ ∘ P` is conformal near `τ`. -/
theorem s32w_chart_proj_loc {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {P : UpperHalfPlane → X} (hloc : IsLocalHomeomorph P) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) P)
    (x : X) {τ : UpperHalfPlane} (hτ : P τ ∈ (chartAt ℂ x).source) :
    ∃ U : Set ℂ, IsOpen U ∧ (τ : ℂ) ∈ U ∧ U ⊆ upperHalf ∧
      (∀ z ∈ U, P (UpperHalfPlane.ofComplex z) ∈ (chartAt ℂ x).source) ∧
      IsKQC (fun z => chartAt ℂ x (P (UpperHalfPlane.ofComplex z))) U 1 := by
  obtain ⟨e, hτe, hpe⟩ := hloc τ
  set W : Set UpperHalfPlane := e.source ∩ P ⁻¹' (chartAt ℂ x).source
  have hWo : IsOpen W := e.open_source.inter
    (hloc.continuous.isOpen_preimage _ (chartAt ℂ x).open_source)
  set U : Set ℂ := upperHalf ∩ UpperHalfPlane.ofComplex ⁻¹' W
  have hsrc : UpperHalfPlane.ofComplex.source = upperHalf := by
    ext z
    simp [UpperHalfPlane.ofComplex, upperHalf]
  have hUo : IsOpen U := by
    have h := UpperHalfPlane.ofComplex.isOpen_inter_preimage hWo
    rwa [hsrc] at h
  have hτU : (τ : ℂ) ∈ U := by
    refine ⟨τ.coe_im_pos, ?_⟩
    show UpperHalfPlane.ofComplex (τ : ℂ) ∈ W
    rw [UpperHalfPlane.ofComplex_apply]
    exact ⟨hτe, hτ⟩
  refine ⟨U, hUo, hτU, fun z hz => hz.1, fun z hz => hz.2.2, ?_⟩
  refine isKQC_one_of_conformal hUo ⟨fun z hz => ?_, fun z hz w hw hzw => ?_, rfl⟩
  · have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun z => chartAt ℂ x (P (UpperHalfPlane.ofComplex z))) z :=
      (mdifferentiableAt_atlas (chart_mem_atlas ℂ x) hz.2.2).comp z
        ((hhol _).comp z (UpperHalfPlane.mdifferentiableAt_ofComplex hz.1))
    exact (mdifferentiableAt_iff_differentiableAt.1 h1).differentiableWithinAt
  · have h1 : P (UpperHalfPlane.ofComplex z) = P (UpperHalfPlane.ofComplex w) :=
      (chartAt ℂ x).injOn hz.2.2 hw.2.2 hzw
    rw [hpe] at h1
    have h2 := e.injOn hz.2.1 hw.2.1 h1
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz.1, UpperHalfPlane.ofComplex_apply_of_im_pos hw.1] at h2
    exact congrArg UpperHalfPlane.coe h2

/-- **L0'.**  Lifts of an anti-conformal map through a holomorphic local homeomorphism `ℍ → X` are anti-holomorphic. -/
theorem s32w_lift_antiholo_loc {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {P : UpperHalfPlane → X} (hloc : IsLocalHomeomorph P) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) P)
    {J : X ≃ₜ X} (hJ : IsAnticonformalInvolution J)
    {Jt : UpperHalfPlane ≃ₜ UpperHalfPlane} (hlift : ∀ τ, P (Jt τ) = J (P τ)) :
    DifferentiableOn ℂ (fun z => conj (liftToC Jt z)) upperHalf := by
  intro z₀ hz₀
  have hz₀' : 0 < z₀.im := hz₀
  set τ₀ : UpperHalfPlane := ⟨z₀, hz₀'⟩ with hτ₀
  obtain ⟨U₀, hU₀o, hτU₀, hU₀H, hU₀s, hψ₀⟩ :=
    s32w_chart_proj_loc (τ := τ₀) hloc hhol (P τ₀) (mem_chart_source ℂ _)
  obtain ⟨U₁, hU₁o, hτU₁, -, -, hψ₁⟩ :=
    s32w_chart_proj_loc (τ := Jt τ₀) hloc hhol (P (Jt τ₀)) (mem_chart_source ℂ _)
  have hc₀ := thm7_3_one_qc_conformal hψ₀
  have hc₁ := thm7_3_one_qc_conformal hψ₁
  have hFx : P (Jt τ₀) = J (P τ₀) := hlift _
  have hkey : ∀ z ∈ U₀, chartAt ℂ (P (Jt τ₀)) (P (UpperHalfPlane.ofComplex (liftToC Jt z))) =
      localMapExpr J (P τ₀) (chartAt ℂ (P τ₀) (P (UpperHalfPlane.ofComplex z))) := by
    intro z hz
    rw [h23l_liftToC_eq Jt (hU₀H hz), UpperHalfPlane.ofComplex_apply, hFx,
      hlift (UpperHalfPlane.ofComplex z)]
    unfold localMapExpr
    rw [(chartAt ℂ (P τ₀)).left_inv (hU₀s z hz)]
  have hl₀ : liftToC Jt z₀ = ((Jt τ₀ : UpperHalfPlane) : ℂ) := h23l_liftToC_coe Jt τ₀
  have hfa : AnalyticAt ℂ (fun z => chartAt ℂ (P (Jt τ₀)) (P (UpperHalfPlane.ofComplex z)))
      ((Jt τ₀ : UpperHalfPlane) : ℂ) := hc₁.1.analyticAt (hU₁o.mem_nhds hτU₁)
  have hder := deriv_ne_zero_of_injOn hU₁o hc₁.1 hc₁.2.1 hτU₁
  have hs := hfa.hasStrictDerivAt
  have hinv := hs.to_localInverse hder
  have hleft := hs.eventually_left_inverse hder
  have h1 : DifferentiableAt ℂ (fun z => chartAt ℂ (P τ₀) (P (UpperHalfPlane.ofComplex z))) z₀ :=
    hc₀.1.differentiableAt (hU₀o.mem_nhds hτU₀)
  have hDo : IsOpen (localMapDomain J (P τ₀)) :=
    (chartAt ℂ (P τ₀)).isOpen_inter_preimage_symm
      ((chartAt ℂ (J (P τ₀))).open_source.preimage J.continuous)
  have hz₀D : chartAt ℂ (P τ₀) (P (UpperHalfPlane.ofComplex z₀)) ∈ localMapDomain J (P τ₀) := by
    have e : UpperHalfPlane.ofComplex z₀ = τ₀ := UpperHalfPlane.ofComplex_apply_of_im_pos hz₀'
    rw [e]
    exact (s23_h_center J _).1
  have h2 : DifferentiableAt ℂ (fun w => conj (localMapExpr J (P τ₀) w))
      (chartAt ℂ (P τ₀) (P (UpperHalfPlane.ofComplex z₀))) :=
    (hJ.2 (P τ₀)).differentiableAt (hDo.mem_nhds hz₀D)
  have hpt : localMapExpr J (P τ₀) (chartAt ℂ (P τ₀) (P (UpperHalfPlane.ofComplex z₀))) =
      chartAt ℂ (P (Jt τ₀)) (P (UpperHalfPlane.ofComplex ((Jt τ₀ : UpperHalfPlane) : ℂ))) := by
    rw [← hkey z₀ hτU₀, hl₀]
  have h3 : DifferentiableAt ℂ (fun u => conj ((hs.localInverse _ _ _ hder) (conj u)))
      (conj (localMapExpr J (P τ₀) (chartAt ℂ (P τ₀) (P (UpperHalfPlane.ofComplex z₀))))) := by
    have := hinv.hasDerivAt.differentiableAt
    rw [hpt]
    exact (this.hasDerivAt.conj_conj).differentiableAt
  have hcomp := h3.comp z₀ (h2.comp z₀ h1)
  have hcont : ContinuousAt (liftToC Jt) z₀ :=
    (h23l_liftToC_continuousOn Jt.continuous).continuousAt (isOpen_upperHalf.mem_nhds hz₀)
  have hev : ∀ᶠ z in 𝓝 z₀, liftToC Jt z ∈ {y | hs.localInverse _ _ _ hder
      ((fun z => chartAt ℂ (P (Jt τ₀)) (P (UpperHalfPlane.ofComplex z))) y) = y} := by
    have : Tendsto (liftToC Jt) (𝓝 z₀) (𝓝 ((Jt τ₀ : UpperHalfPlane) : ℂ)) := by
      rw [← hl₀]; exact hcont
    exact this.eventually hleft
  apply DifferentiableAt.differentiableWithinAt
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hU₀o.mem_nhds hτU₀, hev] with z hz hzev
  simp only [Function.comp_apply, conj_conj]
  rw [← hkey z hz]
  exact congrArg conj hzev.symm

/-- Facts on the punctured double used by the orientation argument: the half `A = ιd(S) ∖ Pd` is
connected, the reflection has a fixed point off `Pd`, and the fixed set is compact in `puncturedOpens Pd`. -/
theorem s32w_punctured_facts {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd) :
    IsConnected {y : puncturedOpens Pd | (y : Xd.carrier) ∈ range ιd} ∧
    (∃ y : puncturedOpens Pd, J (y : Xd.carrier) = y) ∧
    IsCompact {y : puncturedOpens Pd | J (y : Xd.carrier) = y} := by
  classical
  letI : Infinite S := Jacobians.Discharge.ContMDiff.Degree.infinite_of_chartedSpace_complex
  letI : Infinite Xd.carrier := Jacobians.Discharge.ContMDiff.Degree.infinite_of_chartedSpace_complex
  have hinj : Function.Injective ιd := hd.embedding.injective
  set C : Set S := ιd ⁻¹' (↑Pd : Set Xd.carrier) with hC
  have hCfin : C.Finite := Pd.finite_toSet.preimage hinj.injOn
  have hCne : Cᶜ.Nonempty := by
    obtain ⟨s, hs⟩ := hCfin.infinite_compl.nonempty
    exact ⟨s, hs⟩
  have hCconn : IsConnected Cᶜ :=
    (Jacobians.Discharge.Manifold.isPathConnected_compl_finite_of_connected_chartedSpace_complex
      hCfin hCne).isConnected
  haveI : ConnectedSpace ↥Cᶜ := Subtype.connectedSpace hCconn
  let G : ↥Cᶜ → puncturedOpens Pd := fun s => ⟨ιd s, s.2⟩
  have hGc : Continuous G :=
    Continuous.subtype_mk (hd.embedding.continuous.comp continuous_subtype_val) _
  have hArange : {y : puncturedOpens Pd | (y : Xd.carrier) ∈ range ιd} = range G := by
    ext y
    constructor
    · rintro ⟨s, hs⟩
      have hsC : s ∈ Cᶜ := by
        intro h
        exact y.2 (hs ▸ h)
      exact ⟨⟨s, hsC⟩, Subtype.ext hs⟩
    · rintro ⟨s, rfl⟩
      exact ⟨s, rfl⟩
  have hAconn : IsConnected {y : puncturedOpens Pd | (y : Xd.carrier) ∈ range ιd} := by
    rw [hArange]; exact isConnected_range hGc
  have hJinv : ∀ x, J (J x) = x := hd.involution.1
  have hFixPd : ∀ x : Xd.carrier, J x = x → x ∉ (↑Pd : Set Xd.carrier) := fun x hx => by
    have : x ∈ {x | J x = x} := hx
    rw [hd.fixed_curves] at this
    exact this.2
  refine ⟨hAconn, ?_, ?_⟩
  · by_contra hno
    push_neg at hno
    -- no fixed point: `D = A ∪ J A`, contradicting connectedness
    have hcoverD : ∀ y : puncturedOpens Pd, (y : Xd.carrier) ∈ range ιd ∨ (y : Xd.carrier) ∈ range (J ∘ ιd) := by
      intro y
      have hall : (y : Xd.carrier) ∈ (univ : Set Xd.carrier) := mem_univ _
      rw [← hd.cover] at hall
      rcases hall with ((h | h) | h) | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h (hno y)
      · exact absurd h y.2
    have hc : IsConnected (univ : Set (puncturedOpens Pd)) := by
      have hne : ((↑Pd : Set Xd.carrier)ᶜ).Nonempty := by
        obtain ⟨x, hx⟩ := (Pd.finite_toSet.infinite_compl).nonempty
        exact ⟨x, hx⟩
      have hcc : IsConnected ((↑Pd : Set Xd.carrier)ᶜ) :=
        (Jacobians.Discharge.Manifold.isPathConnected_compl_finite_of_connected_chartedSpace_complex
          Pd.finite_toSet hne).isConnected
      haveI : ConnectedSpace (puncturedOpens Pd) := Subtype.connectedSpace hcc
      exact isConnected_univ
    have hA1 : IsOpen {y : puncturedOpens Pd | (y : Xd.carrier) ∈ range ιd} :=
      hd.embedding.isOpen_range.preimage continuous_subtype_val
    have hA2 : IsOpen {y : puncturedOpens Pd | (y : Xd.carrier) ∈ range (J ∘ ιd)} :=
      (J.isOpenEmbedding.comp hd.embedding).isOpen_range.preimage continuous_subtype_val
    rcases hc.isPreconnected.subset_or_subset hA1 hA2
      (Set.disjoint_left.2 fun y h1 h2 => (Set.disjoint_left.1 hd.disjoint) h1 h2)
      (fun y _ => hcoverD y) with h | h
    · -- everything lies in `A`, but `J A` is non-empty in `D`
      obtain ⟨y, hy⟩ := hAconn.nonempty
      have hJy : J (y : Xd.carrier) ∉ (↑Pd : Set Xd.carrier) := by
        intro hP
        apply y.2
        have : (y : Xd.carrier) ∈ J '' (↑Pd : Set Xd.carrier) := ⟨_, hP, hJinv _⟩
        rwa [hd.Pd_invariant] at this
      have hmem : (⟨J (y : Xd.carrier), hJy⟩ : puncturedOpens Pd) ∈
          {y : puncturedOpens Pd | (y : Xd.carrier) ∈ range ιd} := h (mem_univ _)
      obtain ⟨s, hs⟩ := hmem
      obtain ⟨s', hs'⟩ := hy
      have : (y : Xd.carrier) ∈ range ιd ∩ range (J ∘ ιd) := by
        refine ⟨⟨s', hs'⟩, ⟨s, ?_⟩⟩
        show J (ιd s) = y
        rw [show ιd s = J y from hs, hJinv]
      exact (Set.disjoint_left.1 hd.disjoint) this.1 this.2
    · obtain ⟨y, hy⟩ := hAconn.nonempty
      have := h (mem_univ y)
      exact (Set.disjoint_left.1 hd.disjoint) hy this
  · -- compactness of the fixed set
    have hFixc : IsCompact {x : Xd.carrier | J x = x} :=
      (isClosed_eq J.continuous continuous_id).isCompact
    have himg : (Subtype.val : puncturedOpens Pd → Xd.carrier) '' {y : puncturedOpens Pd | J (y : Xd.carrier) = y} =
        {x : Xd.carrier | J x = x} := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hFixPd x hx⟩, hx, rfl⟩
    exact (Topology.IsEmbedding.subtypeVal.isCompact_iff).2 (by rw [himg]; exact hFixc)

/-- The punctured double is connected. -/
theorem s32w_punctured_connectedSpace {Xd : ClosedRS.{u}} (Pd : Finset Xd.carrier) :
    ConnectedSpace (puncturedOpens Pd) := by
  letI : Infinite Xd.carrier := Jacobians.Discharge.ContMDiff.Degree.infinite_of_chartedSpace_complex
  have hne : ((↑Pd : Set Xd.carrier)ᶜ).Nonempty := by
    obtain ⟨x, hx⟩ := (Pd.finite_toSet.infinite_compl).nonempty
    exact ⟨x, hx⟩
  have hcc : IsConnected ((↑Pd : Set Xd.carrier)ᶜ) :=
    (Jacobians.Discharge.Manifold.isPathConnected_compl_finite_of_connected_chartedSpace_complex
      Pd.finite_toSet hne).isConnected
  exact Subtype.connectedSpace hcc

/-- **L5 (core).**  A quasiconformal self-map `ψ` of the punctured double, homotopic to the identity and
commuting with the reflection, maps the half `ιd(S)` into itself. -/
theorem s32w_halves_selfmap {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ} (hm : m ≠ 0) (hex : ¬ IsExceptionalType g n m)
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {ψ : puncturedOpens Pd ≃ₜ puncturedOpens Pd} (hψ : IsQCRS ψ)
    (hψ1 : ContinuousMap.Homotopic (ψ : C(puncturedOpens Pd, puncturedOpens Pd))
      ((Homeomorph.refl (puncturedOpens Pd) : puncturedOpens Pd ≃ₜ puncturedOpens Pd) :
        C(puncturedOpens Pd, puncturedOpens Pd)))
    (hψJ : ∀ y y' : puncturedOpens Pd, (y' : Xd.carrier) = J y → (ψ y' : Xd.carrier) = J (ψ y)) :
    ∀ y : puncturedOpens Pd, (y : Xd.carrier) ∈ range ιd → (ψ y : Xd.carrier) ∈ range ιd := by
  classical
  obtain ⟨hAc, ⟨y₀, hy₀⟩, hFixc⟩ := s32w_punctured_facts F hd
  haveI : ConnectedSpace (puncturedOpens Pd) := s32w_punctured_connectedSpace Pd
  obtain ⟨Γ, p, hΓ, hfree, hp⟩ := ((finiteType_hyperbolic F hex).2 hm Xd J ιd Pd hd)
  have hJinv : ∀ x, J (J x) = x := hd.involution.1
  have hJPd : ∀ y : puncturedOpens Pd, J (y : Xd.carrier) ∉ (↑Pd : Set Xd.carrier) := by
    intro y hP
    apply y.2
    have : (y : Xd.carrier) ∈ J '' (↑Pd : Set Xd.carrier) := ⟨_, hP, hJinv _⟩
    rwa [hd.Pd_invariant] at this
  -- the restricted reflection
  obtain ⟨Jd, hJd⟩ : ∃ Jd : puncturedOpens Pd ≃ₜ puncturedOpens Pd, ∀ y, (Jd y : Xd.carrier) = J y :=
    ⟨{ toFun := fun y => ⟨J y, hJPd y⟩
       invFun := fun y => ⟨J y, hJPd y⟩
       left_inv := fun y => Subtype.ext (hJinv _)
       right_inv := fun y => Subtype.ext (hJinv _)
       continuous_toFun := Continuous.subtype_mk (J.continuous.comp continuous_subtype_val) _
       continuous_invFun := Continuous.subtype_mk (J.continuous.comp continuous_subtype_val) _ },
      fun _ => rfl⟩
  have hψJd : ∀ y, ψ (Jd y) = Jd (ψ y) := fun y =>
    Subtype.ext (by rw [hJd, hψJ y (Jd y) (hJd y)])
  have hFixD : {y : puncturedOpens Pd | Jd y = y} = {y : puncturedOpens Pd | J (y : Xd.carrier) = y} := by
    ext y
    simp only [mem_setOf_eq, Subtype.ext_iff, hJd]
  have hFixDc : IsCompact {y : puncturedOpens Pd | Jd y = y} := by rw [hFixD]; exact hFixc
  -- the uniformization and the lift of the reflection
  obtain ⟨τ₀, hτ₀⟩ := hp.2.2.1 y₀
  have hy₀' : Jd y₀ = y₀ := Subtype.ext (by rw [hJd]; exact hy₀)
  obtain ⟨Jt, hJt, hJt0⟩ := exists_lift hp hp Jd τ₀ τ₀ (by rw [hτ₀, hy₀'])
  have hJt' : ∀ τ, p (Jt τ) = Jd (p τ) := hJt
  set P : UpperHalfPlane → Xd.carrier := fun τ => ((p τ : puncturedOpens Pd) : Xd.carrier) with hPdef
  have hPloc : IsLocalHomeomorph P :=
    (Topology.IsOpenEmbedding.isLocalHomeomorph (puncturedOpens Pd).isOpen.isOpenEmbedding_subtypeVal).comp
      hp.1.isLocalHomeomorph
  have hPhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) P :=
    (contMDiff_subtype_val (n := ω) (U := puncturedOpens Pd)).mdifferentiable (by simp) |>.comp hp.2.1
  have hPlift : ∀ τ, P (Jt τ) = J (P τ) := fun τ => by
    show ((p (Jt τ) : puncturedOpens Pd) : Xd.carrier) = J ((p τ : puncturedOpens Pd) : Xd.carrier)
    rw [hJt', hJd]
  have hfib : ∀ τ τ', P τ = P τ' → ∃ γ ∈ Γ, γ • τ = τ' := fun τ τ' h =>
    (hp.2.2.2 τ τ').1 (Subtype.ext h)
  have hanti := s32w_lift_antiholo_loc hPloc hPhol hd.involution hPlift
  obtain ⟨a, ha, δ, hδΓ, hδcomm, hδnt, d1, d2, d3⟩ :=
    s32w_seam_element hΓ hfree hp hFixDc hJt' hanti hJt0
  -- the lift of `ψ` with trivial deck homomorphism
  obtain ⟨τ₁, hτ₁⟩ := hp.2.2.1 (ψ (p τ₀))
  obtain ⟨Ψ, hΨ, -⟩ := exists_lift hp hp ψ τ₀ τ₁ hτ₁
  have hΨ' : ∀ τ, p (Ψ τ) = ψ (p τ) := hΨ
  have hidlift : IsLift p p (Homeomorph.refl (puncturedOpens Pd)) (Homeomorph.refl UpperHalfPlane) :=
    fun τ => rfl
  obtain ⟨γ₁, hγ₁Γ, hγ₁⟩ := (thm23_1_homotopy_iff hp hp ψ (Homeomorph.refl _) hΨ hidlift).1 hψ1
  set Ψ' : UpperHalfPlane ≃ₜ UpperHalfPlane := Ψ.trans (Homeomorph.smul γ₁⁻¹) with hΨ'def
  have hΨ'app : ∀ τ, Ψ' τ = γ₁⁻¹ • Ψ τ := fun τ => rfl
  have hΨ'p : ∀ τ, p (Ψ' τ) = ψ (p τ) := by
    intro τ
    rw [hΨ'app, ← hΨ' τ]
    exact ((hp.2.2.2 (Ψ τ) (γ₁⁻¹ • Ψ τ)).2 ⟨γ₁⁻¹, Γ.inv_mem hγ₁Γ, rfl⟩).symm
  have hΨ'comm : ∀ γ ∈ Γ, ∀ τ, Ψ' (γ • τ) = γ • Ψ' τ := by
    intro γ hγ τ
    have h := hγ₁ γ hγ (Ψ τ)
    simp only [Homeomorph.symm_apply_apply, Homeomorph.refl_apply, Homeomorph.refl_symm] at h
    rw [hΨ'app, hΨ'app, h]
    simp [smul_smul]
  have hΨ'symm_comm : ∀ γ ∈ Γ, ∀ τ, Ψ'.symm (γ • τ) = γ • Ψ'.symm τ := by
    intro γ hγ τ
    apply Ψ'.injective
    rw [Homeomorph.apply_symm_apply, hΨ'comm γ hγ, Homeomorph.apply_symm_apply]
  -- the conjugated reflection `R = Ψ' Jt Ψ'⁻¹`
  set R : UpperHalfPlane ≃ₜ UpperHalfPlane := (Ψ'.symm.trans Jt).trans Ψ' with hRdef
  have hRapp : ∀ τ, R τ = Ψ' (Jt (Ψ'.symm τ)) := fun τ => rfl
  have hRp : ∀ τ, P (R τ) = J (P τ) := by
    intro τ
    rw [hRapp]
    show ((p (Ψ' (Jt (Ψ'.symm τ))) : puncturedOpens Pd) : Xd.carrier) = J ((p τ : puncturedOpens Pd) : Xd.carrier)
    rw [hΨ'p, hJt', hψJd, hJd, ← hΨ'p, Homeomorph.apply_symm_apply]
  have hRfix : R (Ψ' τ₀) = Ψ' τ₀ := by
    rw [hRapp, Homeomorph.symm_apply_apply, hJt0]
  have hantiR := s32w_lift_antiholo_loc hPloc hPhol hd.involution (Jt := R) hRp
  obtain ⟨a', ha'⟩ := s32w_reflection_form R hantiR hRfix
  have hRδ : ∀ τ, R (δ • τ) = δ • R τ := by
    intro τ
    rw [hRapp, hRapp, hΨ'symm_comm δ hδΓ, hδcomm, hΨ'comm δ hδΓ]
  have hfree' : ∀ τ : UpperHalfPlane, δ • τ = τ → δ = 1 ∨ δ = -1 := fun τ h => hfree δ hδΓ τ h
  have hagree := s32w_reflections_agree Jt R δ hfree' hδnt hδcomm hRδ a a' ha ha'
  have hΨJ : ∀ τ, Ψ' (Jt τ) = Jt (Ψ' τ) := by
    intro τ
    rw [hagree (Ψ' τ), hRapp, Homeomorph.symm_apply_apply]
  have hΨ'fix : Jt (Ψ' τ₀) = Ψ' τ₀ := by rw [← hΨJ, hJt0]
  -- the conjugate `f = a Ψ' a⁻¹`
  obtain ⟨K, hK⟩ := hψ
  have hKQC := (lift_isKQC_automorphic hp hp hK hΨ).1
  set f : UpperHalfPlane ≃ₜ UpperHalfPlane :=
    ((Homeomorph.smul a⁻¹).trans Ψ).trans (Homeomorph.smul (a * γ₁⁻¹)) with hfdef
  have hfQC : IsKQC (liftToC f) upperHalf K := s30w_isKQC_conj hKQC a⁻¹ (a * γ₁⁻¹)
  have hfapp : ∀ τ, f τ = a • Ψ' (a⁻¹ • τ) := by
    intro τ
    show (a * γ₁⁻¹) • Ψ (a⁻¹ • τ) = a • γ₁⁻¹ • Ψ (a⁻¹ • τ)
    rw [mul_smul]
  have hMcomm : ∀ τ, f ((a * δ * a⁻¹) • τ) = (a * δ * a⁻¹) • f τ := by
    intro τ
    have e1 : a⁻¹ • (a * δ * a⁻¹) • τ = δ • a⁻¹ • τ := by simp [mul_smul]
    rw [hfapp, hfapp, e1, hΨ'comm δ hδΓ]
    simp [mul_smul]
  have key : ∀ τ : UpperHalfPlane, (τ : ℂ).re = 0 ↔ Jt (a⁻¹ • τ) = a⁻¹ • τ := by
    intro τ
    rw [s32w_fix_iff ha, smul_inv_smul]
  have hax : ∀ τ : UpperHalfPlane, (τ : ℂ).re = 0 ↔ ((f τ : UpperHalfPlane) : ℂ).re = 0 := by
    intro τ
    rw [key τ, key (f τ), hfapp, inv_smul_smul, ← hΨJ]
    exact Ψ'.injective.eq_iff.symm
  have hside := s32w_sides_preserved f hfQC (a * δ * a⁻¹) d1 d2 d3 hMcomm hax
  have hside' : ∀ σ : UpperHalfPlane, 0 < ((a • σ : UpperHalfPlane) : ℂ).re →
      0 < ((a • Ψ' σ : UpperHalfPlane) : ℂ).re := by
    intro σ hσ
    have := hside (a • σ) hσ
    rwa [hfapp, inv_smul_smul] at this
  -- a point of `ιd(S)` whose image is again in `ιd(S)`
  have hRe0 : ((a • τ₀ : UpperHalfPlane) : ℂ).re = 0 := (s32w_fix_iff ha τ₀).1 hJt0
  have hex2 : ∃ τ, P τ ∈ range ιd ∧ P (Ψ' τ) ∈ range ιd := by
    rcases s32w_side_constant F hd hΓ hfree hPloc hfib hPlift a ha with hL | hRt
    · obtain ⟨W₁, hW₁o, hq1, h11, -⟩ := hL τ₀ hJt0
      obtain ⟨W₂, hW₂o, hq2, h21, -⟩ := hL (Ψ' τ₀) hΨ'fix
      have hWn : W₁ ∩ Ψ' ⁻¹' W₂ ∈ 𝓝 τ₀ :=
        (hW₁o.inter (hW₂o.preimage Ψ'.continuous)).mem_nhds ⟨hq1, hq2⟩
      obtain ⟨⟨τ, hτW, hτpos⟩, -⟩ := s32w_near_sides a hRe0 hWn
      exact ⟨τ, h11 τ hτW.1 hτpos, h21 _ hτW.2 (hside' τ hτpos)⟩
    · obtain ⟨W₁, hW₁o, hq1, h11, -⟩ := hRt τ₀ hJt0
      obtain ⟨W₂, hW₂o, hq2, h21, -⟩ := hRt (Ψ' τ₀) hΨ'fix
      have hWn : W₁ ∩ Ψ' ⁻¹' W₂ ∈ 𝓝 τ₀ :=
        (hW₁o.inter (hW₂o.preimage Ψ'.continuous)).mem_nhds ⟨hq1, hq2⟩
      obtain ⟨⟨τ, hτW, hτpos⟩, -⟩ := s32w_near_sides a hRe0 hWn
      have h1 := h11 τ hτW.1 hτpos
      have h2 := h21 _ hτW.2 (hside' τ hτpos)
      refine ⟨Jt τ, ?_, ?_⟩
      · obtain ⟨s, hs⟩ := h1
        exact ⟨s, by rw [hPlift, ← hs]; exact (hJinv _).symm⟩
      · obtain ⟨s, hs⟩ := h2
        exact ⟨s, by rw [hΨJ, hPlift, ← hs]; exact (hJinv _).symm⟩
  obtain ⟨τ, hτ1, hτ2⟩ := hex2
  -- the halves of `D`
  have hA1 : IsOpen {y : puncturedOpens Pd | (y : Xd.carrier) ∈ range ιd} :=
    hd.embedding.isOpen_range.preimage continuous_subtype_val
  have hA2 : IsOpen {y : puncturedOpens Pd | (y : Xd.carrier) ∈ range (J ∘ ιd)} :=
    (J.isOpenEmbedding.comp hd.embedding).isOpen_range.preimage continuous_subtype_val
  have hAFix : ∀ y : puncturedOpens Pd, (y : Xd.carrier) ∈ range ιd → Jd y ≠ y := by
    intro y hy hJy
    have hJ' : J (y : Xd.carrier) = y := by rw [← hJd, hJy]
    have hmem : (y : Xd.carrier) ∈ {x | J x = x} := hJ'
    rw [hd.fixed_curves, hd.embedding.isOpen_range.frontier_eq] at hmem
    exact hmem.1.2 hy
  have hψcover : ∀ y : puncturedOpens Pd, (y : Xd.carrier) ∈ range ιd →
      (ψ y : Xd.carrier) ∈ range ιd ∪ range (J ∘ ιd) := by
    intro y hy
    have hall : (ψ y : Xd.carrier) ∈ (univ : Set Xd.carrier) := mem_univ _
    rw [← hd.cover] at hall
    rcases hall with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have hψy : Jd (ψ y) = ψ y := Subtype.ext (by rw [hJd]; exact h)
      have : ψ (Jd y) = ψ y := by rw [hψJd, hψy]
      exact hAFix y hy (ψ.injective this)
    · exact absurd h (ψ y).2
  have hmeet : (ψ (p τ) : Xd.carrier) ∈ range ιd := by
    rw [← hΨ'p]; exact hτ2
  have hsub := (hAc.isPreconnected.image ψ ψ.continuous.continuousOn).subset_or_subset hA1 hA2
    (Set.disjoint_left.2 fun y h1 h2 => (Set.disjoint_left.1 hd.disjoint) h1 h2)
    (by
      rintro _ ⟨y, hy, rfl⟩
      exact hψcover y hy)
  intro y hy
  rcases hsub with h | h
  · exact h ⟨y, hy, rfl⟩
  · exfalso
    have h' : ψ (p τ) ∈ {y : puncturedOpens Pd | (y : Xd.carrier) ∈ range (J ∘ ιd)} := h ⟨p τ, hτ1, rfl⟩
    exact (Set.disjoint_left.1 hd.disjoint) hmeet h'

/-- **W3 (frozen, with `hvJ`).**  Homotopic quasiconformal maps `v, h` of the punctured doubles commuting with the
reflections, with `v(A₀) ⊆ A₁`, satisfy `h(A₀) ⊆ A₁`. -/
theorem s32w_orientation_halves
    {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀] [ConnectedSpace S₀]
    [IsManifold 𝓘(ℂ) ω S₀]
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ} (hm : m ≠ 0) (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    {Xd₀ Xd₁ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier}
    {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier}
    {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    {v h : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₁} (hv : IsQCRS v) (hh : IsQCRS h)
    (hvh : ContinuousMap.Homotopic (v : C(puncturedOpens Pd₀, puncturedOpens Pd₁))
      (h : C(puncturedOpens Pd₀, puncturedOpens Pd₁)))
    (hvA : ∀ y : puncturedOpens Pd₀, (y : Xd₀.carrier) ∈ range ιd₀ → (v y : Xd₁.carrier) ∈ range ιd₁)
    (hvJ : ∀ y y' : puncturedOpens Pd₀, (y' : Xd₀.carrier) = J₀ y → (v y' : Xd₁.carrier) = J₁ (v y))
    (hhJ : ∀ y y' : puncturedOpens Pd₀, (y' : Xd₀.carrier) = J₀ y → (h y' : Xd₁.carrier) = J₁ (h y)) :
    ∀ y : puncturedOpens Pd₀, (y : Xd₀.carrier) ∈ range ιd₀ → (h y : Xd₁.carrier) ∈ range ιd₁ := by
  classical
  have _hd₁ := hd₁
  have _F₁ := F₁
  have hJPd : ∀ y : puncturedOpens Pd₀, J₀ (y : Xd₀.carrier) ∉ (↑Pd₀ : Set Xd₀.carrier) := by
    intro y hP
    apply y.2
    have : (y : Xd₀.carrier) ∈ J₀ '' (↑Pd₀ : Set Xd₀.carrier) := ⟨_, hP, hd₀.involution.1 _⟩
    rwa [hd₀.Pd_invariant] at this
  set ψ : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₀ := h.trans v.symm with hψdef
  have hψ : IsQCRS ψ := s28q_isQCRS_trans hh (s28q_isQCRS_symm hv)
  have hψ1 : ContinuousMap.Homotopic (ψ : C(puncturedOpens Pd₀, puncturedOpens Pd₀))
      ((Homeomorph.refl (puncturedOpens Pd₀) : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₀) :
        C(puncturedOpens Pd₀, puncturedOpens Pd₀)) := by
    have h1 := (ContinuousMap.Homotopic.refl (v.symm : C(puncturedOpens Pd₁, puncturedOpens Pd₀))).comp hvh.symm
    have e1 : (ψ : C(puncturedOpens Pd₀, puncturedOpens Pd₀)) =
        (v.symm : C(puncturedOpens Pd₁, puncturedOpens Pd₀)).comp (h : C(puncturedOpens Pd₀, puncturedOpens Pd₁)) :=
      rfl
    have e2 : (v.symm : C(puncturedOpens Pd₁, puncturedOpens Pd₀)).comp
        (v : C(puncturedOpens Pd₀, puncturedOpens Pd₁)) =
        ((Homeomorph.refl (puncturedOpens Pd₀) : puncturedOpens Pd₀ ≃ₜ puncturedOpens Pd₀) :
          C(puncturedOpens Pd₀, puncturedOpens Pd₀)) :=
      ContinuousMap.ext fun x => v.symm_apply_apply x
    rw [e1]
    rw [e2] at h1
    exact h1
  have hψJ : ∀ y y' : puncturedOpens Pd₀, (y' : Xd₀.carrier) = J₀ y →
      (ψ y' : Xd₀.carrier) = J₀ (ψ y) := by
    intro y y' hy
    set w : puncturedOpens Pd₀ := v.symm (h y) with hw
    set w' : puncturedOpens Pd₀ := ⟨J₀ (w : Xd₀.carrier), hJPd w⟩ with hw'
    have h1 : (v w' : Xd₁.carrier) = J₁ (v w) := hvJ w w' rfl
    have h2 : (h y' : Xd₁.carrier) = J₁ (h y) := hhJ y y' hy
    have hvw : v w = h y := v.apply_symm_apply _
    have h3 : v w' = h y' := Subtype.ext (by rw [h1, hvw, h2])
    have h4 : v.symm (h y') = w' := by rw [← h3]; exact v.symm_apply_apply _
    show ((v.symm (h y') : puncturedOpens Pd₀) : Xd₀.carrier) = J₀ ((v.symm (h y) : puncturedOpens Pd₀) : Xd₀.carrier)
    rw [h4]
  intro y hy
  have hψy := s32w_halves_selfmap hm hex F₀ hd₀ hψ hψ1 hψJ y hy
  have := hvA (ψ y) hψy
  have e : v (ψ y) = h y := v.apply_symm_apply _
  rwa [e] at this

end LiZhongQC
