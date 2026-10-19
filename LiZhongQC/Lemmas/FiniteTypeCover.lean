import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller
import LiZhongQC.Lemmas.UniformizedUniqueness
import LiZhongQC.Ch08.S29_TeichmullerMetric
import LiZhongQC.Lemmas.UniformizedTeichmuller

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]


/-- Chart partitions on a second countable charted space subordinate to a neighbourhood system
(the non-compact analogue of `s26_exists_chartPartition`). -/
theorem s82cmp_exists_chartPartition {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    [SecondCountableTopology S] [Nonempty S] (V : S → Set S) (hVo : ∀ p, IsOpen (V p))
    (hVp : ∀ p, p ∈ V p) (hVs : ∀ p, V p ⊆ (chartAt ℂ p).source) :
    ∃ (x : ℕ → S) (P : ℕ → Set S), IsChartPartition S x P ∧ ∀ i, P i ⊆ V (x i) := by
  classical
  obtain ⟨t, htc, ht⟩ := (isLindelof_univ (X := S)).elim_countable_subcover V hVo
    (fun p _ => mem_iUnion.2 ⟨p, hVp p⟩)
  obtain ⟨p₀⟩ := (inferInstance : Nonempty S)
  have htne : (t ∪ {p₀}).Nonempty := ⟨p₀, Or.inr rfl⟩
  obtain ⟨x, hx⟩ := (htc.union (countable_singleton p₀)).exists_eq_range htne
  set W : ℕ → Set S := fun i => V (x i) with hW
  have hWo : ∀ i, IsOpen (W i) := fun i => hVo _
  refine ⟨x, disjointed W, ⟨fun i => ⟨?_, ?_⟩, disjoint_disjointed W, ?_⟩, fun i => ?_⟩
  · exact (disjointed_subset W i).trans (hVs _)
  · rw [disjointed_eq_inter_compl]
    exact s26_measurableSet_chart_image (x i) W hWo i (hVs _)
  · rw [iUnion_disjointed, eq_univ_iff_forall]
    intro p
    obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.1 (ht (mem_univ p))
    have hq' : q ∈ range x := hx ▸ Or.inl hq
    obtain ⟨i, rfl⟩ := hq'
    exact mem_iUnion.2 ⟨i, hpq⟩
  · exact disjointed_subset W i



/-- Two holomorphic sections of a two-sheeted cover over a small neighbourhood of a point off the branch
set: `pr⁻¹ V = σ₁ V ⊔ σ₂ V`, `pr ∘ σₖ = id` on `V`. The data are the outputs of `s82lc_local_form` (local
holomorphic inverses). -/
theorem s82cmp_sections {Y X : ClosedRS.{u}} {P : Finset X.carrier} {pr : Y.carrier → X.carrier}
    (hcont : Continuous pr) (hfib : ∀ x ∉ P, (pr ⁻¹' {x}).ncard = 2)
    (hloc : ∀ y, pr y ∉ P → ∃ e : OpenPartialHomeomorph Y.carrier X.carrier, y ∈ e.source ∧
      EqOn pr e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    {p : X.carrier} (hp : p ∉ P) {W : Set X.carrier} (hW : W ∈ 𝓝 p)
    (T : Y.carrier → Set Y.carrier) (hT : ∀ y, T y ∈ 𝓝 y) :
    ∃ (V : Set X.carrier) (σ₁ σ₂ : OpenPartialHomeomorph X.carrier Y.carrier) (y₁ y₂ : Y.carrier),
      σ₁ p = y₁ ∧ σ₂ p = y₂ ∧ σ₁ '' V ⊆ T y₁ ∧ σ₂ '' V ⊆ T y₂ ∧
      IsOpen V ∧ p ∈ V ∧ V ⊆ W ∧ V ⊆ σ₁.source ∧ V ⊆ σ₂.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) σ₁ V ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) σ₂ V ∧
      (∀ v ∈ V, pr (σ₁ v) = v) ∧ (∀ v ∈ V, pr (σ₂ v) = v) ∧
      Disjoint (σ₁ '' V) (σ₂ '' V) ∧ pr ⁻¹' V = σ₁ '' V ∪ σ₂ '' V ∧
      IsOpen (σ₁ '' V) ∧ IsOpen (σ₂ '' V) := by
  classical
  obtain ⟨y₁, y₂, hne, hfibre⟩ := Set.ncard_eq_two.1 (hfib p hp)
  have hy₁ : pr y₁ = p := by
    have : y₁ ∈ pr ⁻¹' {p} := by rw [hfibre]; simp
    exact this
  have hy₂ : pr y₂ = p := by
    have : y₂ ∈ pr ⁻¹' {p} := by rw [hfibre]; simp
    exact this
  obtain ⟨e₁, he₁s, he₁eq, he₁d⟩ := hloc y₁ (by rw [hy₁]; exact hp)
  obtain ⟨e₂, he₂s, he₂eq, he₂d⟩ := hloc y₂ (by rw [hy₂]; exact hp)
  -- disjoint open neighbourhoods of the two fibre points inside the sources
  obtain ⟨B₁, B₂, hB₁, hB₂, hy₁B, hy₂B, hdis⟩ := t2_separation hne
  set A₁ := B₁ ∩ e₁.source ∩ interior (T y₁) with hA₁
  set A₂ := B₂ ∩ e₂.source ∩ interior (T y₂) with hA₂
  have hA₁o : IsOpen A₁ := (hB₁.inter e₁.open_source).inter isOpen_interior
  have hA₂o : IsOpen A₂ := (hB₂.inter e₂.open_source).inter isOpen_interior
  have hA₁s : A₁ ⊆ e₁.source := fun y hy => hy.1.2
  have hA₂s : A₂ ⊆ e₂.source := fun y hy => hy.1.2
  have hy₁A : y₁ ∈ A₁ := ⟨⟨hy₁B, he₁s⟩, mem_interior_iff_mem_nhds.2 (hT y₁)⟩
  have hy₂A : y₂ ∈ A₂ := ⟨⟨hy₂B, he₂s⟩, mem_interior_iff_mem_nhds.2 (hT y₂)⟩
  have hAdis : Disjoint A₁ A₂ := hdis.mono (fun y hy => hy.1.1) (fun y hy => hy.1.1)
  -- the closed set of points not in `A₁ ∪ A₂` has compact image avoiding `p`
  have hC : IsClosed (pr '' (A₁ ∪ A₂)ᶜ) :=
    ((hA₁o.union hA₂o).isClosed_compl.isCompact.image hcont).isClosed
  have hpC : p ∉ pr '' (A₁ ∪ A₂)ᶜ := by
    rintro ⟨y, hy, hyp⟩
    have : y ∈ pr ⁻¹' {p} := hyp
    rw [hfibre] at this
    rcases this with rfl | rfl
    · exact hy (Or.inl hy₁A)
    · exact hy (Or.inr hy₂A)
  set V : Set X.carrier := e₁ '' A₁ ∩ e₂ '' A₂ ∩ (pr '' (A₁ ∪ A₂)ᶜ)ᶜ ∩ interior W with hV
  have hVo : IsOpen V :=
    (((e₁.isOpen_image_of_subset_source hA₁o hA₁s).inter
      (e₂.isOpen_image_of_subset_source hA₂o hA₂s)).inter hC.isOpen_compl).inter isOpen_interior
  have hpV : p ∈ V := by
    refine ⟨⟨⟨?_, ?_⟩, hpC⟩, mem_interior_iff_mem_nhds.2 hW⟩
    · exact ⟨y₁, hy₁A, by rw [← he₁eq he₁s, hy₁]⟩
    · exact ⟨y₂, hy₂A, by rw [← he₂eq he₂s, hy₂]⟩
  have hV1 : V ⊆ e₁ '' A₁ := fun v hv => hv.1.1.1
  have hV2 : V ⊆ e₂ '' A₂ := fun v hv => hv.1.1.2
  have hVC : ∀ v ∈ V, v ∉ pr '' (A₁ ∪ A₂)ᶜ := fun v hv => hv.1.2
  have hVW : V ⊆ W := fun v hv => interior_subset hv.2
  have hs1 : ∀ v ∈ V, e₁.symm v ∈ A₁ := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := hV1 hv
    rw [e₁.left_inv (hA₁s ha)]
    exact ha
  have hs2 : ∀ v ∈ V, e₂.symm v ∈ A₂ := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := hV2 hv
    rw [e₂.left_inv (hA₂s ha)]
    exact ha
  have ht1 : ∀ v ∈ V, v ∈ e₁.target := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := hV1 hv
    exact e₁.map_source (hA₁s ha)
  have ht2 : ∀ v ∈ V, v ∈ e₂.target := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := hV2 hv
    exact e₂.map_source (hA₂s ha)
  have hpr1 : ∀ v ∈ V, pr (e₁.symm v) = v := by
    intro v hv
    rw [he₁eq (e₁.map_target (ht1 v hv)), e₁.right_inv (ht1 v hv)]
  have hpr2 : ∀ v ∈ V, pr (e₂.symm v) = v := by
    intro v hv
    rw [he₂eq (e₂.map_target (ht2 v hv)), e₂.right_inv (ht2 v hv)]
  have himg1 : e₁.symm '' V = A₁ ∩ pr ⁻¹' V := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨hs1 v hv, by simpa [hpr1 v hv] using hv⟩
    · rintro ⟨hyA, hyV⟩
      refine ⟨pr y, hyV, ?_⟩
      rw [he₁eq (hA₁s hyA), e₁.left_inv (hA₁s hyA)]
  have himg2 : e₂.symm '' V = A₂ ∩ pr ⁻¹' V := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨hs2 v hv, by simpa [hpr2 v hv] using hv⟩
    · rintro ⟨hyA, hyV⟩
      refine ⟨pr y, hyV, ?_⟩
      rw [he₂eq (hA₂s hyA), e₂.left_inv (hA₂s hyA)]
  have hσ1p : e₁.symm p = y₁ := by
    have h : e₁ y₁ = p := (he₁eq he₁s).symm.trans hy₁
    rw [← h]; exact e₁.left_inv he₁s
  have hσ2p : e₂.symm p = y₂ := by
    have h : e₂ y₂ = p := (he₂eq he₂s).symm.trans hy₂
    rw [← h]; exact e₂.left_inv he₂s
  refine ⟨V, e₁.symm, e₂.symm, y₁, y₂, hσ1p, hσ2p, ?_, ?_, hVo, hpV, hVW, ?_, ?_, he₁d.mono ?_, he₂d.mono ?_, hpr1, hpr2, ?_, ?_, ?_, ?_⟩
  · rw [himg1]; exact fun y hy => interior_subset hy.1.2
  · rw [himg2]; exact fun y hy => interior_subset hy.1.2
  · intro v hv; rw [OpenPartialHomeomorph.symm_source]; exact ht1 v hv
  · intro v hv; rw [OpenPartialHomeomorph.symm_source]; exact ht2 v hv
  · exact ht1
  · exact ht2
  · rw [himg1, himg2]
    exact hAdis.mono inter_subset_left inter_subset_left
  · ext y
    constructor
    · intro hyV
      have hyA : y ∈ A₁ ∪ A₂ := by
        by_contra hy
        exact hVC _ hyV ⟨y, hy, rfl⟩
      rcases hyA with hyA | hyA
      · left; rw [himg1]; exact ⟨hyA, hyV⟩
      · right; rw [himg2]; exact ⟨hyA, hyV⟩
    · rintro (h | h)
      · rw [himg1] at h; exact h.2
      · rw [himg2] at h; exact h.2
  · rw [himg1]; exact hA₁o.inter (hVo.preimage hcont)
  · rw [himg2]; exact hA₂o.inter (hVo.preimage hcont)



/-- **Pointwise pull-back relation, abstract form.**  `Φ : S → Y` is injective and holomorphic on an open
set `U` with a local inverse `G`; if `q` and `r` are holomorphic quadratic differentials and
`q = Φ_* r` is known at the centre of the chart at `Φ a` (in the form `hrel`, with the chart at `a` on the source
side), then `r_x(φ_x a) = q_ŷ(φ_ŷ (Φ a)) · (deriv (φ_ŷ ∘ Φ ∘ φ_x⁻¹) (φ_x a))²` for **any** charts `x ∋ a`,
`ŷ ∋ Φ a`. -/
theorem s82cmp_pullback_pointwise {S Y : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {r : S → ℂ → ℂ} {q : Y → ℂ → ℂ} (hr : IsHolQuadDiff r) (hq : IsHolQuadDiff q)
    {Φ : S → Y} {G : Y → S} {a : S} {U : Set S} (hU : IsOpen U) (haU : a ∈ U)
    (hUs : U ⊆ (chartAt ℂ a).source)
    (hΦd : ∀ b ∈ U, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) Φ b) (hinj : InjOn Φ U)
    (hGΦ : ∀ b ∈ U, G (Φ b) = b) (hΦG : ∀ᶠ y in 𝓝 (Φ a), Φ (G y) = y ∧ G y ∈ U)
    (hGc : ContinuousAt G (Φ a))
    (hrel : q (Φ a) (chartAt ℂ (Φ a) (Φ a)) =
      r a (chartAt ℂ a (G ((chartAt ℂ (Φ a)).symm (chartAt ℂ (Φ a) (Φ a))))) *
        deriv (fun v => chartAt ℂ a (G ((chartAt ℂ (Φ a)).symm v))) (chartAt ℂ (Φ a) (Φ a)) ^ 2)
    {x : S} {ŷ : Y} (hax : a ∈ (chartAt ℂ x).source) (hŷ : Φ a ∈ (chartAt ℂ ŷ).source) :
    r x (chartAt ℂ x a) = q ŷ (chartAt ℂ ŷ (Φ a)) *
      deriv (fun w => chartAt ℂ ŷ (Φ ((chartAt ℂ x).symm w))) (chartAt ℂ x a) ^ 2 := by
  classical
  set y' := Φ a with hy'
  set c' := chartAt ℂ y' y' with hc'
  set ca := chartAt ℂ a a with hca
  set w := chartAt ℂ x a with hw
  set z := chartAt ℂ ŷ y' with hz
  let Ta : ℂ → ℂ := fun v => chartAt ℂ y' (Φ ((chartAt ℂ a).symm v))
  let Tx : ℂ → ℂ := fun v => chartAt ℂ ŷ (Φ ((chartAt ℂ x).symm v))
  let Ψ : ℂ → ℂ := fun v => chartAt ℂ a (G ((chartAt ℂ y').symm v))
  have hy'mem : y' ∈ (chartAt ℂ y').source := mem_chart_source ℂ y'
  have ha_mem : a ∈ (chartAt ℂ a).source := mem_chart_source ℂ a
  have hΦc : ∀ b ∈ U, ContinuousAt Φ b := fun b hb => (hΦd b hb).continuousAt
  have hTa_d : DifferentiableAt ℂ Ta ca :=
    ((s23_mdifferentiableAt_iff ha_mem hy'mem).1 (hΦd a haU)).2
  have hTx_d : DifferentiableAt ℂ Tx w := ((s23_mdifferentiableAt_iff hax hŷ).1 (hΦd a haU)).2
  -- the open set where `Ta` is defined, injective, differentiable
  have hU' : IsOpen (U ∩ Φ ⁻¹' (chartAt ℂ y').source) :=
    (continuousOn_of_forall_continuousAt hΦc).isOpen_inter_preimage hU (chartAt ℂ y').open_source
  set Ω : Set ℂ := (chartAt ℂ a).target ∩ (chartAt ℂ a).symm ⁻¹' (U ∩ Φ ⁻¹' (chartAt ℂ y').source) with hΩ
  have hΩo : IsOpen Ω := (chartAt ℂ a).isOpen_inter_preimage_symm hU'
  have hcaΩ : ca ∈ Ω := by
    refine ⟨(chartAt ℂ a).map_source ha_mem, ?_⟩
    simp only [mem_preimage, hca, (chartAt ℂ a).left_inv ha_mem]
    exact ⟨haU, hy'mem⟩
  have hΩd : DifferentiableOn ℂ Ta Ω := by
    intro v hv
    have hb : (chartAt ℂ a).symm v ∈ U := hv.2.1
    have hbs : (chartAt ℂ a).symm v ∈ (chartAt ℂ a).source := (chartAt ℂ a).map_target hv.1
    have h := ((s23_mdifferentiableAt_iff hbs hv.2.2).1 (hΦd _ hb)).2
    rw [(chartAt ℂ a).right_inv hv.1] at h
    exact h.differentiableWithinAt
  have hΩi : InjOn Ta Ω := by
    intro v₁ hv₁ v₂ hv₂ h
    have h1 : Φ ((chartAt ℂ a).symm v₁) = Φ ((chartAt ℂ a).symm v₂) := by
      have := (chartAt ℂ y').injOn hv₁.2.2 hv₂.2.2 h
      exact this
    have h2 := hinj hv₁.2.1 hv₂.2.1 h1
    rw [← (chartAt ℂ a).right_inv hv₁.1, ← (chartAt ℂ a).right_inv hv₂.1, h2]
  have hTa'ne : deriv Ta ca ≠ 0 := deriv_ne_zero_of_injOn hΩo hΩd hΩi hcaΩ
  -- the local inverse `Ψ`
  have hc'tgt : c' ∈ (chartAt ℂ y').target := (chartAt ℂ y').map_source hy'mem
  have hsymm_c' : (chartAt ℂ y').symm c' = y' := (chartAt ℂ y').left_inv hy'mem
  have hΨc' : Ψ c' = ca := by
    simp only [Ψ, hsymm_c']
    rw [hy', hGΦ a haU]
  have hΨcont : ContinuousAt Ψ c' := by
    have h1 : ContinuousAt (chartAt ℂ y').symm c' := (chartAt ℂ y').continuousAt_symm hc'tgt
    have h2 : ContinuousAt G ((chartAt ℂ y').symm c') := by rw [hsymm_c']; exact hGc
    have h3 : ContinuousAt (chartAt ℂ a) (G ((chartAt ℂ y').symm c')) := by
      rw [hsymm_c', hy', hGΦ a haU]
      exact (chartAt ℂ a).continuousAt ha_mem
    exact h3.comp_of_eq (h2.comp h1) rfl
  have hev : ∀ᶠ v in 𝓝 c', Ta (Ψ v) = v := by
    have h1 : ContinuousAt (chartAt ℂ y').symm c' := (chartAt ℂ y').continuousAt_symm hc'tgt
    have h2 : ∀ᶠ v in 𝓝 c', Φ (G ((chartAt ℂ y').symm v)) = (chartAt ℂ y').symm v ∧
        G ((chartAt ℂ y').symm v) ∈ U := by
      exact h1.eventually (p := fun y => Φ (G y) = y ∧ G y ∈ U) (by rw [hsymm_c']; exact hΦG)
    filter_upwards [h2, (chartAt ℂ y').open_target.mem_nhds hc'tgt] with v hv hvt
    simp only [Ta, Ψ]
    rw [(chartAt ℂ a).left_inv (hUs hv.2), hv.1, (chartAt ℂ y').right_inv hvt]
  have hTa_has : HasDerivAt Ta (deriv Ta ca) (Ψ c') := by rw [hΨc']; exact hTa_d.hasDerivAt
  have hΨhas : HasDerivAt Ψ (deriv Ta ca)⁻¹ c' :=
    HasDerivAt.of_local_left_inverse hΨcont hTa_has hTa'ne hev
  have hΨderiv : deriv Ψ c' = (deriv Ta ca)⁻¹ := hΨhas.deriv
  -- the relation at the centre
  have hrel' : q y' c' = r a ca * (deriv Ta ca)⁻¹ ^ 2 := by
    have h := hrel
    simp only [hsymm_c'] at h
    rw [hy', hGΦ a haU] at h
    rw [h]
    congr 2
  have hrel'' : r a ca = q y' c' * deriv Ta ca ^ 2 := by
    rw [hrel']
    field_simp
  -- transformation laws
  have hwt : w ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hax
  have hwsymm : (chartAt ℂ x).symm w = a := (chartAt ℂ x).left_inv hax
  have hzt : z ∈ (chartAt ℂ ŷ).target := (chartAt ℂ ŷ).map_source hŷ
  have hzsymm : (chartAt ℂ ŷ).symm z = y' := (chartAt ℂ ŷ).left_inv hŷ
  have hlawr : r x w = r a (chartTransition a x w) * deriv (chartTransition a x) w ^ 2 :=
    s26u_law hr x a hwt (by rw [hwsymm]; exact ha_mem)
  have hlawq : q ŷ z = q y' (chartTransition y' ŷ z) * deriv (chartTransition y' ŷ) z ^ 2 :=
    s26u_law hq ŷ y' hzt (by rw [hzsymm]; exact hy'mem)
  have hτw : chartTransition a x w = ca := by
    simp only [chartTransition, hwsymm]; rfl
  have hτz : chartTransition y' ŷ z = c' := by
    simp only [chartTransition, hzsymm]; rfl
  have hτd : DifferentiableAt ℂ (chartTransition a x) w :=
    s23_transition_differentiableAt a x hwt (by rw [hwsymm]; exact ha_mem)
  have hτzd : DifferentiableAt ℂ (chartTransition y' ŷ) z :=
    s23_transition_differentiableAt y' ŷ hzt (by rw [hzsymm]; exact hy'mem)
  have hTxw : Tx w = z := by simp only [Tx, hwsymm]; rfl
  -- chain rule: `Ta ∘ τ = τ̂ ∘ Tx` near `w`
  have hchain_ev : (Ta ∘ chartTransition a x) =ᶠ[𝓝 w] (chartTransition y' ŷ ∘ Tx) := by
    have h1 : ContinuousAt (chartAt ℂ x).symm w := (chartAt ℂ x).continuousAt_symm hwt
    have h2 : ContinuousAt (fun v => Φ ((chartAt ℂ x).symm v)) w := by
      have : ContinuousAt Φ ((chartAt ℂ x).symm w) := by rw [hwsymm]; exact hΦc a haU
      exact this.comp h1
    have h3 : ∀ᶠ v in 𝓝 w, Φ ((chartAt ℂ x).symm v) ∈ (chartAt ℂ ŷ).source := by
      refine h2.eventually ?_
      have : Φ ((chartAt ℂ x).symm w) ∈ (chartAt ℂ ŷ).source := by rw [hwsymm]; exact hŷ
      exact (chartAt ℂ ŷ).open_source.mem_nhds this
    have h4 : ∀ᶠ v in 𝓝 w, (chartAt ℂ x).symm v ∈ (chartAt ℂ a).source := by
      refine h1.eventually ?_
      rw [hwsymm]
      exact (chartAt ℂ a).open_source.mem_nhds ha_mem
    filter_upwards [h3, h4] with v hv3 hv4
    simp only [Function.comp, chartTransition, Ta, Tx]
    rw [(chartAt ℂ a).left_inv hv4, (chartAt ℂ ŷ).left_inv hv3]
  have hd1 : HasDerivAt (Ta ∘ chartTransition a x) (deriv Ta ca * deriv (chartTransition a x) w) w := by
    have hTa_h : HasDerivAt Ta (deriv Ta ca) (chartTransition a x w) := by
      rw [hτw]; exact hTa_d.hasDerivAt
    exact hTa_h.comp w hτd.hasDerivAt
  have hd2 : HasDerivAt (chartTransition y' ŷ ∘ Tx) (deriv (chartTransition y' ŷ) z * deriv Tx w) w := by
    have hτ_h : HasDerivAt (chartTransition y' ŷ) (deriv (chartTransition y' ŷ) z) (Tx w) := by
      rw [hTxw]; exact hτzd.hasDerivAt
    exact hτ_h.comp w hTx_d.hasDerivAt
  have hd1' : HasDerivAt (chartTransition y' ŷ ∘ Tx) (deriv Ta ca * deriv (chartTransition a x) w) w :=
    hd1.congr_of_eventuallyEq hchain_ev.symm
  have hchain : deriv Ta ca * deriv (chartTransition a x) w =
      deriv (chartTransition y' ŷ) z * deriv Tx w := hd1'.unique hd2
  calc r x w = r a ca * deriv (chartTransition a x) w ^ 2 := by rw [hlawr, hτw]
    _ = q y' c' * deriv Ta ca ^ 2 * deriv (chartTransition a x) w ^ 2 := by rw [hrel'']
    _ = q y' c' * (deriv Ta ca * deriv (chartTransition a x) w) ^ 2 := by ring
    _ = q y' c' * (deriv (chartTransition y' ŷ) z * deriv Tx w) ^ 2 := by rw [hchain]
    _ = (q y' c' * deriv (chartTransition y' ŷ) z ^ 2) * deriv Tx w ^ 2 := by ring
    _ = q ŷ z * deriv Tx w ^ 2 := by rw [hlawq, hτz]



/-- Change of variables for the area integral through an injective holomorphic map: if `rr = T^* qq` on `M`
(`rr w = qq (T w) · (T' w)²`), then `∫_{T(M)} F |qq| = ∫_M (F ∘ T) |rr|`. -/
theorem s82cmp_lintegral_pullback {M : Set ℂ} (hM : MeasurableSet M) {T : ℂ → ℂ}
    (hd : ∀ w ∈ M, DifferentiableAt ℂ T w) (hinj : InjOn T M) {F : ℂ → ℝ≥0∞} {rr qq : ℂ → ℂ}
    (hrel : ∀ w ∈ M, rr w = qq (T w) * deriv T w ^ 2) :
    ∫⁻ z in T '' M, F z * ENNReal.ofReal ‖qq z‖ = ∫⁻ w in M, F (T w) * ENNReal.ofReal ‖rr w‖ := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hM
    (fun w hw => ((hd w hw).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt) hinj]
  refine setLIntegral_congr_fun hM fun w hw => ?_
  have hdw := hd w hw
  have hdet : (fderiv ℝ T w).det = ‖deriv T w‖ ^ 2 := by
    have e := det_fderiv_eq_jacobian (hdw.restrictScalars ℝ)
    rw [show (fderiv ℝ T w).det = LinearMap.det (fderiv ℝ T w : ℂ →ₗ[ℝ] ℂ) from rfl, e,
      jacobian, dz_eq_deriv hdw, (cauchyRiemann_iff.1 hdw).2, norm_zero]
    ring
  rw [hdet, abs_of_nonneg (by positivity), hrel w hw, norm_mul, norm_pow,
    ENNReal.ofReal_mul (norm_nonneg _)]
  ring


/-- `Function.invFun` of an open embedding is continuous at points of the range. -/
theorem s82cmp_invFun_continuousAt {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [Nonempty A]
    {f : A → B} (hf : Topology.IsOpenEmbedding f) {b : B} (hb : b ∈ Set.range f) :
    ContinuousAt (Function.invFun f) b := by
  obtain ⟨a, rfl⟩ := hb
  have hia : Function.invFun f (f a) = a := Function.leftInverse_invFun hf.isEmbedding.injective a
  rw [ContinuousAt, hia]
  intro N hN
  rw [Filter.mem_map]
  obtain ⟨O, hON, hOo, haO⟩ := mem_nhds_iff.1 hN
  refine Filter.mem_of_superset ((hf.isOpenMap O hOo).mem_nhds ⟨a, haO, rfl⟩) ?_
  rintro _ ⟨c, hc, rfl⟩
  show Function.invFun f (f c) ∈ N
  rw [Function.leftInverse_invFun hf.isEmbedding.injective c]
  exact hON hc

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

/-- **Sheet relation.**  On a sheet `σ` of a two-sheeted cover over `V`, with `ι⁻¹ V` inside a chart of `S₀` and
`σ V` inside a chart of `Y`, the lifted differential is the pull-back of `r` through `σ ∘ ι`, in any pair of charts
`x ∋ a`, `ŷ ∋ σ(ι a)`. -/
theorem s82cmp_sheet_relation {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) {Y : ClosedRS.{u}}
    {pr : Y.carrier → F₀.X.carrier} (hcont : Continuous pr)
    {r : S₀ → ℂ → ℂ} {qh : Y.carrier → ℂ → ℂ} (hr : IsHolQuadDiff r) (hq : IsHolQuadDiff qh)
    (hrel : ∀ (y : Y.carrier) (s : S₀), pr y = F₀.ι s → ∀ᶠ z in 𝓝 (chartAt ℂ y y),
      qh y z = r s (chartAt ℂ s (Function.invFun F₀.ι (pr ((chartAt ℂ y).symm z)))) *
        deriv (fun w => chartAt ℂ s (Function.invFun F₀.ι (pr ((chartAt ℂ y).symm w)))) z ^ 2)
    {V : Set F₀.X.carrier} (hVo : IsOpen V) (hVr : V ⊆ Set.range F₀.ι)
    {σ : OpenPartialHomeomorph F₀.X.carrier Y.carrier} (hVσ : V ⊆ σ.source)
    (hσd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) σ V) (hσpr : ∀ v ∈ V, pr (σ v) = v)
    (hσo : IsOpen (σ '' V))
    {a : S₀} (haV : F₀.ι a ∈ V) {x : S₀} {ŷ : Y.carrier} (hax : a ∈ (chartAt ℂ x).source)
    (hŷ : σ (F₀.ι a) ∈ (chartAt ℂ ŷ).source) :
    r x (chartAt ℂ x a) = qh ŷ (chartAt ℂ ŷ (σ (F₀.ι a))) *
      deriv (fun w => chartAt ℂ ŷ (σ (F₀.ι ((chartAt ℂ x).symm w)))) (chartAt ℂ x a) ^ 2 := by
  classical
  haveI : Nonempty S₀ := ⟨a⟩
  have hemb := F₀.embedding
  set Φ : S₀ → Y.carrier := fun b => σ (F₀.ι b) with hΦ
  set G : Y.carrier → S₀ := fun y => Function.invFun F₀.ι (pr y) with hG
  set U' : Set S₀ := F₀.ι ⁻¹' V ∩ (chartAt ℂ a).source with hU'
  have hU'o : IsOpen U' := (hVo.preimage hemb.continuous).inter (chartAt ℂ a).open_source
  have haU' : a ∈ U' := ⟨haV, mem_chart_source ℂ a⟩
  have hΦd : ∀ b ∈ U', MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) Φ b := by
    intro b hb
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F₀.ι b := F₀.holomorphic b
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) σ (F₀.ι b) :=
      (hσd (F₀.ι b) hb.1).mdifferentiableAt (hVo.mem_nhds hb.1)
    exact h2.comp b h1
  have hinj : InjOn Φ U' := by
    intro b₁ hb₁ b₂ hb₂ h
    exact hemb.isEmbedding.injective (σ.injOn (hVσ hb₁.1) (hVσ hb₂.1) h)
  have hGΦ : ∀ b ∈ U', G (Φ b) = b := by
    intro b hb
    simp only [hG, hΦ]
    rw [hσpr _ hb.1]
    exact Function.leftInverse_invFun hemb.isEmbedding.injective b
  have hy0 : Φ a ∈ σ '' V := ⟨F₀.ι a, haV, rfl⟩
  have hGc : ContinuousAt G (Φ a) := by
    have h1 : pr (Φ a) = F₀.ι a := hσpr _ haV
    have h2 : ContinuousAt (Function.invFun F₀.ι) (pr (Φ a)) := by
      rw [h1]; exact s82cmp_invFun_continuousAt hemb ⟨a, rfl⟩
    exact h2.comp hcont.continuousAt
  have hΦG : ∀ᶠ y in 𝓝 (Φ a), Φ (G y) = y ∧ G y ∈ U' := by
    have h1 : ∀ᶠ y in 𝓝 (Φ a), G y ∈ (chartAt ℂ a).source := by
      refine hGc.eventually ?_
      have : G (Φ a) = a := hGΦ a haU'
      rw [this]
      exact (chartAt ℂ a).open_source.mem_nhds (mem_chart_source ℂ a)
    filter_upwards [hσo.mem_nhds hy0, h1] with y hy hys
    obtain ⟨v, hv, rfl⟩ := hy
    have hpv : pr (σ v) = v := hσpr v hv
    obtain ⟨c, hc⟩ := hVr hv
    have hGv : G (σ v) = c := by
      simp only [hG]
      rw [hpv, ← hc]
      exact Function.leftInverse_invFun hemb.isEmbedding.injective c
    refine ⟨?_, ?_, hys⟩
    · simp only [hΦ, hGv, hc]
    · show F₀.ι (G (σ v)) ∈ V
      rw [hGv, hc]; exact hv
  have hrel0 : qh (Φ a) (chartAt ℂ (Φ a) (Φ a)) =
      r a (chartAt ℂ a (G ((chartAt ℂ (Φ a)).symm (chartAt ℂ (Φ a) (Φ a))))) *
        deriv (fun v => chartAt ℂ a (G ((chartAt ℂ (Φ a)).symm v))) (chartAt ℂ (Φ a) (Φ a)) ^ 2 := by
    have h := (hrel (Φ a) a (hσpr _ haV)).self_of_nhds
    exact h
  exact s82cmp_pullback_pointwise hr hq hU'o haU' (fun b hb => hb.2) hΦd hinj hGΦ hΦG hGc hrel0 hax hŷ

end

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

/-- Per-point sheet data of a two-sheeted cover: a neighbourhood `V` of `ι s` in the range of `ι`, two sections
`sh false`, `sh true` over `V` with images inside chart sources, covering `pr⁻¹ V`. -/
theorem s82cmp_sheet_data {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) {Y : ClosedRS.{u}}
    {pr : Y.carrier → F₀.X.carrier} (hcont : Continuous pr)
    (hfib : ∀ x ∉ F₀.P, (pr ⁻¹' {x}).ncard = 2)
    (hloc : ∀ y, pr y ∉ F₀.P → ∃ e : OpenPartialHomeomorph Y.carrier F₀.X.carrier, y ∈ e.source ∧
      EqOn pr e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target) (s : S₀) :
    ∃ (V : Set F₀.X.carrier) (sh : Bool → OpenPartialHomeomorph F₀.X.carrier Y.carrier)
      (ŷ : Bool → Y.carrier),
      IsOpen V ∧ F₀.ι s ∈ V ∧ V ⊆ Set.range F₀.ι ∧ (∀ k, V ⊆ (sh k).source) ∧
      (∀ k, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (sh k) V) ∧ (∀ k, ∀ v ∈ V, pr (sh k v) = v) ∧
      (∀ k, IsOpen (sh k '' V)) ∧ (∀ k, sh k (F₀.ι s) = ŷ k) ∧
      (∀ k, sh k '' V ⊆ (chartAt ℂ (ŷ k)).source) ∧
      Disjoint (sh false '' V) (sh true '' V) ∧ pr ⁻¹' V = sh false '' V ∪ sh true '' V := by
  have hP0 : F₀.P = F₀.P := rfl
  have hrange : Set.range F₀.ι = (↑F₀.P : Set F₀.X.carrier)ᶜ := by
    rw [F₀.range_ι]; simp
  have hp : F₀.ι s ∉ F₀.P := by
    have : F₀.ι s ∈ Set.range F₀.ι := ⟨s, rfl⟩
    rw [hrange] at this
    exact this
  have hW : Set.range F₀.ι ∈ 𝓝 (F₀.ι s) := F₀.embedding.isOpen_range.mem_nhds ⟨s, rfl⟩
  obtain ⟨V, σ₁, σ₂, y₁, y₂, h1, h2, hT1, hT2, hVo, hpV, hVW, hV1, hV2, hd1, hd2, hp1, hp2, hdis, hpre,
    hio1, hio2⟩ := s82cmp_sections hcont hfib hloc hp hW (fun y => (chartAt ℂ y).source)
      (fun y => (chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y))
  refine ⟨V, fun k => cond k σ₂ σ₁, fun k => cond k y₂ y₁, hVo, hpV, hVW, ?_, ?_, ?_, ?_, ?_, ?_, hdis, hpre⟩
  · intro k; cases k
    · exact hV1
    · exact hV2
  · intro k; cases k
    · exact hd1
    · exact hd2
  · intro k; cases k
    · exact hp1
    · exact hp2
  · intro k; cases k
    · exact hio1
    · exact hio2
  · intro k; cases k
    · exact h1
    · exact h2
  · intro k; cases k
    · exact hT1
    · exact hT2

end

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

/-- The chart expression `T = φ_ŷ ∘ σ ∘ ι ∘ φ_x⁻¹` of a sheet: it maps `φ_x(A)` onto `φ_ŷ(σ ι A)`, is holomorphic
and injective there. -/
theorem s82cmp_sheet_T {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) {Y : ClosedRS.{u}}
    {V : Set F₀.X.carrier} (hVo : IsOpen V)
    {σ : OpenPartialHomeomorph F₀.X.carrier Y.carrier} (hVσ : V ⊆ σ.source)
    (hσd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) σ V) {x : S₀} {ŷ : Y.carrier}
    (hŷ : σ '' V ⊆ (chartAt ℂ ŷ).source)
    {A : Set S₀} (hA : A ⊆ F₀.ι ⁻¹' V) (hAx : A ⊆ (chartAt ℂ x).source) :
    (fun w => chartAt ℂ ŷ (σ (F₀.ι ((chartAt ℂ x).symm w)))) '' (chartAt ℂ x '' A) =
        chartAt ℂ ŷ '' (σ '' (F₀.ι '' A)) ∧
      (∀ w ∈ chartAt ℂ x '' A,
        DifferentiableAt ℂ (fun w => chartAt ℂ ŷ (σ (F₀.ι ((chartAt ℂ x).symm w)))) w) ∧
      InjOn (fun w => chartAt ℂ ŷ (σ (F₀.ι ((chartAt ℂ x).symm w)))) (chartAt ℂ x '' A) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨w, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨σ (F₀.ι a), ⟨F₀.ι a, ⟨a, ha, rfl⟩, rfl⟩, ?_⟩
      simp only [(chartAt ℂ x).left_inv (hAx ha)]
    · rintro ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, rfl⟩
      refine ⟨chartAt ℂ x a, ⟨a, ha, rfl⟩, ?_⟩
      simp only [(chartAt ℂ x).left_inv (hAx ha)]
  · rintro w ⟨a, ha, rfl⟩
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F₀.ι a := F₀.holomorphic a
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) σ (F₀.ι a) :=
      (hσd (F₀.ι a) (hA ha)).mdifferentiableAt (hVo.mem_nhds (hA ha))
    have h3 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun b => σ (F₀.ι b)) a := h2.comp a h1
    exact ((s23_mdifferentiableAt_iff (hAx ha) (hŷ ⟨F₀.ι a, hA ha, rfl⟩)).1 h3).2
  · rintro w₁ ⟨a₁, ha₁, rfl⟩ w₂ ⟨a₂, ha₂, rfl⟩ h
    simp only [(chartAt ℂ x).left_inv (hAx ha₁), (chartAt ℂ x).left_inv (hAx ha₂)] at h
    have h1 := (chartAt ℂ ŷ).injOn (hŷ ⟨F₀.ι a₁, hA ha₁, rfl⟩) (hŷ ⟨F₀.ι a₂, hA ha₂, rfl⟩) h
    have h2 := σ.injOn (hVσ (hA ha₁)) (hVσ (hA ha₂)) h1
    rw [F₀.embedding.isEmbedding.injective h2]

/-- Measurability of the chart image of a sheet piece (Lusin–Souslin). -/
theorem s82cmp_sheet_measurable {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) {Y : ClosedRS.{u}}
    {V : Set F₀.X.carrier} (hVo : IsOpen V)
    {σ : OpenPartialHomeomorph F₀.X.carrier Y.carrier} (hVσ : V ⊆ σ.source)
    (hσd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) σ V) {x : S₀} {ŷ : Y.carrier}
    (hŷ : σ '' V ⊆ (chartAt ℂ ŷ).source)
    {A : Set S₀} (hA : A ⊆ F₀.ι ⁻¹' V) (hAx : A ⊆ (chartAt ℂ x).source)
    (hAm : MeasurableSet (chartAt ℂ x '' A)) :
    MeasurableSet (chartAt ℂ ŷ '' (σ '' (F₀.ι '' A))) := by
  obtain ⟨himg, hd, hinj⟩ := s82cmp_sheet_T F₀ hVo hVσ hσd hŷ hA hAx
  rw [← himg]
  exact hAm.image_of_continuousOn_injOn
    (continuousOn_of_forall_continuousAt fun w hw => (hd w hw).continuousAt) hinj

/-- **Integral over one sheet.**  The area integral of the lifted differential over the image of a piece `A`
of `S₀` along a sheet equals the integral of `r` over `A`. -/
theorem s82cmp_sheet_integral {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) {Y : ClosedRS.{u}}
    {pr : Y.carrier → F₀.X.carrier} (hcont : Continuous pr)
    {r : S₀ → ℂ → ℂ} {qh : Y.carrier → ℂ → ℂ} (hr : IsHolQuadDiff r) (hq : IsHolQuadDiff qh)
    (hrel : ∀ (y : Y.carrier) (s : S₀), pr y = F₀.ι s → ∀ᶠ z in 𝓝 (chartAt ℂ y y),
      qh y z = r s (chartAt ℂ s (Function.invFun F₀.ι (pr ((chartAt ℂ y).symm z)))) *
        deriv (fun w => chartAt ℂ s (Function.invFun F₀.ι (pr ((chartAt ℂ y).symm w)))) z ^ 2)
    (U : S₀ → ℝ≥0∞) (Uh : Y.carrier → ℝ≥0∞) (hU : ∀ y s, pr y = F₀.ι s → Uh y = U s)
    {V : Set F₀.X.carrier} (hVo : IsOpen V) (hVr : V ⊆ Set.range F₀.ι)
    {σ : OpenPartialHomeomorph F₀.X.carrier Y.carrier} (hVσ : V ⊆ σ.source)
    (hσd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) σ V) (hσpr : ∀ v ∈ V, pr (σ v) = v)
    (hσo : IsOpen (σ '' V)) {x : S₀} {ŷ : Y.carrier} (hŷ : σ '' V ⊆ (chartAt ℂ ŷ).source)
    {A : Set S₀} (hA : A ⊆ F₀.ι ⁻¹' V) (hAx : A ⊆ (chartAt ℂ x).source)
    (hAm : MeasurableSet (chartAt ℂ x '' A)) :
    ∫⁻ z in chartAt ℂ ŷ '' (σ '' (F₀.ι '' A)), Uh ((chartAt ℂ ŷ).symm z) * ENNReal.ofReal ‖qh ŷ z‖ =
      ∫⁻ w in chartAt ℂ x '' A, U ((chartAt ℂ x).symm w) * ENNReal.ofReal ‖r x w‖ := by
  classical
  obtain ⟨himg, hd, hinj⟩ := s82cmp_sheet_T F₀ hVo hVσ hσd hŷ hA hAx
  have hrel' : ∀ w ∈ chartAt ℂ x '' A, r x w = qh ŷ (chartAt ℂ ŷ (σ (F₀.ι ((chartAt ℂ x).symm w)))) *
      deriv (fun w => chartAt ℂ ŷ (σ (F₀.ι ((chartAt ℂ x).symm w)))) w ^ 2 := by
    rintro w ⟨a, ha, rfl⟩
    have h := s82cmp_sheet_relation F₀ hcont hr hq hrel hVo hVr hVσ hσd hσpr hσo (hA ha) (hAx ha)
      (hŷ ⟨F₀.ι a, hA ha, rfl⟩)
    simp only [(chartAt ℂ x).left_inv (hAx ha)]
    exact h
  rw [← himg]
  have key := s82cmp_lintegral_pullback (F := fun z => Uh ((chartAt ℂ ŷ).symm z)) hAm hd hinj hrel'
  rw [key]
  refine setLIntegral_congr_fun hAm fun w hw => ?_
  obtain ⟨a, ha, rfl⟩ := hw
  have hp : pr (σ (F₀.ι a)) = F₀.ι a := hσpr _ (hA ha)
  simp only [(chartAt ℂ x).left_inv (hAx ha)]
  rw [(chartAt ℂ ŷ).left_inv (hŷ ⟨F₀.ι a, hA ha, rfl⟩), hU _ _ hp]

end

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

/-- **Change of variables for a two-sheeted branched cover (C3).**  If the differential `qh` on the cover
`Y` is the chart-wise pull-back of the differential `r` on `S₀ = X ∖ P` (`hrel`), and `Uh` is the pull-back of the
point function `U`, then the area integrals satisfy `∫_Y Uh dA_qh = 2 ∫_{S₀} U dA_r`. -/
theorem s82cmp_cover_integral {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) {Y : ClosedRS.{u}}
    {pr : Y.carrier → F₀.X.carrier} (hcont : Continuous pr)
    (hfib : ∀ x ∉ F₀.P, (pr ⁻¹' {x}).ncard = 2) (hfibP : ∀ x ∈ F₀.P, (pr ⁻¹' {x}).ncard = 1)
    (hloc : ∀ y, pr y ∉ F₀.P → ∃ e : OpenPartialHomeomorph Y.carrier F₀.X.carrier, y ∈ e.source ∧
      EqOn pr e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    {r : S₀ → ℂ → ℂ} {qh : Y.carrier → ℂ → ℂ} (hr : IsHolQuadDiff r) (hq : IsHolQuadDiff qh)
    (hrel : ∀ (y : Y.carrier) (s : S₀), pr y = F₀.ι s → ∀ᶠ z in 𝓝 (chartAt ℂ y y),
      qh y z = r s (chartAt ℂ s (Function.invFun F₀.ι (pr ((chartAt ℂ y).symm z)))) *
        deriv (fun w => chartAt ℂ s (Function.invFun F₀.ι (pr ((chartAt ℂ y).symm w)))) z ^ 2)
    (U : S₀ → ℝ≥0∞) (Uh : Y.carrier → ℝ≥0∞) (hU : ∀ y s, pr y = F₀.ι s → Uh y = U s) :
    surfaceIntegral qh (fun y z => Uh ((chartAt ℂ y).symm z)) =
      2 * surfaceIntegral r (fun x z => U ((chartAt ℂ x).symm z)) := by
  classical
  haveI : Nonempty S₀ := ConnectedSpace.toNonempty
  haveI : SecondCountableTopology F₀.X.carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ℂ F₀.X.carrier
  haveI : SecondCountableTopology S₀ := F₀.embedding.isEmbedding.secondCountableTopology
  have hrange : Set.range F₀.ι = (↑F₀.P : Set F₀.X.carrier)ᶜ := by
    rw [F₀.range_ι]; simp
  choose V sh ŷ hVo hpV hVr hVs hsd hspr hso hshy hshs hdis hpre using
    s82cmp_sheet_data F₀ hcont hfib hloc
  obtain ⟨x, P, hP, hPV⟩ := s82cmp_exists_chartPartition
    (fun s => F₀.ι ⁻¹' V s ∩ (chartAt ℂ s).source)
    (fun s => ((hVo s).preimage F₀.embedding.continuous).inter (chartAt ℂ s).open_source)
    (fun s => ⟨hpV s, mem_chart_source ℂ s⟩) (fun s => inter_subset_right)
  have hS := s26v_surfaceIntegral_eq_tsum hr U hP
  -- the pieces of `S₀`
  have hPι : ∀ i, P i ⊆ F₀.ι ⁻¹' V (x i) := fun i => (hPV i).trans inter_subset_left
  have hPx : ∀ i, P i ⊆ (chartAt ℂ (x i)).source := fun i => (hP.1 i).1
  have hPm : ∀ i, MeasurableSet (chartAt ℂ (x i) '' P i) := fun i => (hP.1 i).2
  -- the exceptional fibre
  set B : Set Y.carrier := pr ⁻¹' (↑F₀.P : Set F₀.X.carrier) with hB
  have hBfin : B.Finite := by
    have : B = ⋃ p ∈ F₀.P, pr ⁻¹' {p} := by
      ext y; simp [hB]
    rw [this]
    exact F₀.P.finite_toSet.biUnion fun p hp =>
      Set.finite_of_ncard_pos (by rw [hfibP p hp]; norm_num)
  haveI : Finite B := hBfin.to_subtype
  -- the index type of the lifted partition
  obtain ⟨hden⟩ := nonempty_denumerable ((ℕ × Bool) ⊕ ↥B)
  letI := hden
  let e : ((ℕ × Bool) ⊕ ↥B) ≃ ℕ := Denumerable.eqv _
  let xh : ((ℕ × Bool) ⊕ ↥B) → Y.carrier :=
    Sum.elim (fun ik => sh (x ik.1) ik.2 (F₀.ι (x ik.1))) (fun b => (b : Y.carrier))
  let Ph : ((ℕ × Bool) ⊕ ↥B) → Set Y.carrier :=
    Sum.elim (fun ik => sh (x ik.1) ik.2 '' (F₀.ι '' P ik.1)) (fun b => {(b : Y.carrier)})
  have hPhV : ∀ i k, sh (x i) k '' (F₀.ι '' P i) ⊆ sh (x i) k '' V (x i) := fun i k =>
    image_mono (by rintro _ ⟨a, ha, rfl⟩; exact hPι i ha)
  have hPh_sub : ∀ j, Ph j ⊆ (chartAt ℂ (xh j)).source := by
    rintro (⟨i, k⟩ | b)
    · show sh (x i) k '' (F₀.ι '' P i) ⊆ (chartAt ℂ (sh (x i) k (F₀.ι (x i)))).source
      rw [hshy (x i) k]
      exact (hPhV i k).trans (hshs (x i) k)
    · show {(b : Y.carrier)} ⊆ (chartAt ℂ (b : Y.carrier)).source
      simpa using mem_chart_source ℂ (b : Y.carrier)
  have hPh_meas : ∀ j, MeasurableSet (chartAt ℂ (xh j) '' Ph j) := by
    rintro (⟨i, k⟩ | b)
    · show MeasurableSet (chartAt ℂ (sh (x i) k (F₀.ι (x i))) ''
        (sh (x i) k '' (F₀.ι '' P i)))
      rw [hshy (x i) k]
      exact s82cmp_sheet_measurable F₀ (hVo (x i)) (hVs (x i) k) (hsd (x i) k) (hshs (x i) k)
        (hPι i) (hPx i) (hPm i)
    · show MeasurableSet (chartAt ℂ (b : Y.carrier) '' {(b : Y.carrier)})
      rw [Set.image_singleton]
      exact measurableSet_singleton _
  have hpr_Ph : ∀ i k, ∀ y ∈ sh (x i) k '' (F₀.ι '' P i), ∃ a ∈ P i, pr y = F₀.ι a ∧
      y = sh (x i) k (F₀.ι a) := by
    rintro i k _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, hspr (x i) k _ (hPι i ha), rfl⟩
  have hPh_disj : Pairwise (fun j j' => Disjoint (Ph j) (Ph j')) := by
    rintro (⟨i, k⟩ | b) (⟨i', k'⟩ | b') hne
    · -- two sheet pieces
      rw [Set.disjoint_left]
      intro y hy hy'
      obtain ⟨a, ha, hpa, hya⟩ := hpr_Ph i k y hy
      obtain ⟨a', ha', hpa', hya'⟩ := hpr_Ph i' k' y hy'
      by_cases hii : i = i'
      · subst hii
        have hkk : k ≠ k' := fun h => hne (by rw [h])
        have hV1 := hPhV i k hy
        have hV2 := hPhV i k' hy'
        cases k <;> cases k'
        · exact hkk rfl
        · exact (Set.disjoint_left.1 (hdis (x i))) hV1 hV2
        · exact (Set.disjoint_left.1 (hdis (x i))) hV2 hV1
        · exact hkk rfl
      · have : F₀.ι a = F₀.ι a' := hpa.symm.trans hpa'
        have haa : a = a' := F₀.embedding.isEmbedding.injective this
        exact (Set.disjoint_left.1 (hP.2.1 hii)) ha (haa ▸ ha')
    · rw [Set.disjoint_left]
      intro y hy hy'
      obtain ⟨a, ha, hpa, hya⟩ := hpr_Ph i k y hy
      have hyb : y = (b' : Y.carrier) := hy'
      have hb : pr (b' : Y.carrier) ∈ (↑F₀.P : Set F₀.X.carrier) := b'.2
      rw [← hyb, hpa] at hb
      have : F₀.ι a ∈ Set.range F₀.ι := ⟨a, rfl⟩
      rw [hrange] at this
      exact this hb
    · rw [Set.disjoint_left]
      intro y hy hy'
      obtain ⟨a, ha, hpa, hya⟩ := hpr_Ph i' k' y hy'
      have hyb : y = (b : Y.carrier) := hy
      have hb : pr (b : Y.carrier) ∈ (↑F₀.P : Set F₀.X.carrier) := b.2
      rw [← hyb, hpa] at hb
      have : F₀.ι a ∈ Set.range F₀.ι := ⟨a, rfl⟩
      rw [hrange] at this
      exact this hb
    · rw [Set.disjoint_left]
      intro y hy hy'
      have h1 : y = (b : Y.carrier) := hy
      have h2 : y = (b' : Y.carrier) := hy'
      exact hne (congrArg Sum.inr (Subtype.ext (h1.symm.trans h2)))
  have hPh_cover : (⋃ j, Ph j) = Set.univ := by
    rw [eq_univ_iff_forall]
    intro y
    by_cases hy : pr y ∈ (↑F₀.P : Set F₀.X.carrier)
    · exact mem_iUnion.2 ⟨Sum.inr ⟨y, hy⟩, rfl⟩
    · have hyr : pr y ∈ Set.range F₀.ι := by rw [hrange]; exact hy
      obtain ⟨s, hs⟩ := hyr
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hP.2.2.symm ▸ mem_univ s : s ∈ ⋃ i, P i)
      have hsV : pr y ∈ V (x i) := by rw [← hs]; exact hPι i hi
      have hy2 : y ∈ pr ⁻¹' V (x i) := hsV
      rw [hpre (x i)] at hy2
      rcases hy2 with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
      · refine mem_iUnion.2 ⟨Sum.inl (i, false), ?_⟩
        have hpv : pr (sh (x i) false v) = v := hspr (x i) false v hv
        have : v = F₀.ι s := hpv.symm.trans hs.symm
        subst this
        exact ⟨F₀.ι s, ⟨s, hi, rfl⟩, rfl⟩
      · refine mem_iUnion.2 ⟨Sum.inl (i, true), ?_⟩
        have hpv : pr (sh (x i) true v) = v := hspr (x i) true v hv
        have : v = F₀.ι s := hpv.symm.trans hs.symm
        subst this
        exact ⟨F₀.ι s, ⟨s, hi, rfl⟩, rfl⟩
  have hPart : IsChartPartition Y.carrier (fun n => xh (e.symm n)) (fun n => Ph (e.symm n)) := by
    refine ⟨fun n => ⟨hPh_sub _, hPh_meas _⟩, fun n m hnm => hPh_disj ?_, ?_⟩
    · intro h; exact hnm (e.symm.injective h)
    · rw [← hPh_cover]
      ext y
      simp only [mem_iUnion]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨e.symm n, hn⟩
      · rintro ⟨j, hj⟩
        exact ⟨e j, by simpa using hj⟩
  rw [hS, s26v_surfaceIntegral_eq_tsum hq Uh hPart]
  -- evaluate the cover sum
  set G : ((ℕ × Bool) ⊕ ↥B) → ℝ≥0∞ := fun j =>
    ∫⁻ z in chartAt ℂ (xh j) '' Ph j, Uh ((chartAt ℂ (xh j)).symm z) *
      ENNReal.ofReal ‖qh (xh j) z‖ with hG
  have hre : ∑' n, G (e.symm n) = ∑' j, G j := e.symm.tsum_eq G
  have hGn : (∑' n, ∫⁻ z in chartAt ℂ (xh (e.symm n)) '' Ph (e.symm n),
      Uh ((chartAt ℂ (xh (e.symm n))).symm z) * ENNReal.ofReal ‖qh (xh (e.symm n)) z‖) =
      ∑' n, G (e.symm n) := rfl
  rw [hGn, hre]
  have hsplit : ∑' j, G j = ∑' ik : ℕ × Bool, G (Sum.inl ik) + ∑' b : ↥B, G (Sum.inr b) :=
    (ENNReal.summable.hasSum (f := fun ik => G (Sum.inl ik))).sum
      (ENNReal.summable.hasSum (f := fun b : ↥B => G (Sum.inr b))) |>.tsum_eq
  have hzero : ∑' b : ↥B, G (Sum.inr b) = 0 := by
    refine ENNReal.tsum_eq_zero.2 fun b => ?_
    show ∫⁻ z in chartAt ℂ (b : Y.carrier) '' {(b : Y.carrier)}, _ = 0
    rw [Set.image_singleton]
    exact setLIntegral_measure_zero _ _ (measure_singleton _)
  have hsheet : ∀ i k, G (Sum.inl (i, k)) =
      ∫⁻ w in chartAt ℂ (x i) '' P i, U ((chartAt ℂ (x i)).symm w) * ENNReal.ofReal ‖r (x i) w‖ := by
    intro i k
    show ∫⁻ z in chartAt ℂ (sh (x i) k (F₀.ι (x i))) '' (sh (x i) k '' (F₀.ι '' P i)),
      Uh ((chartAt ℂ (sh (x i) k (F₀.ι (x i)))).symm z) *
        ENNReal.ofReal ‖qh (sh (x i) k (F₀.ι (x i))) z‖ = _
    rw [hshy (x i) k]
    exact s82cmp_sheet_integral F₀ hcont hr hq hrel U Uh hU (hVo (x i)) (hVr (x i)) (hVs (x i) k)
      (hsd (x i) k) (hspr (x i) k) (hso (x i) k) (hshs (x i) k) (hPι i) (hPx i) (hPm i)
  rw [hsplit, hzero, add_zero]
  have hprod : ∑' ik : ℕ × Bool, G (Sum.inl ik) = ∑' i, ∑' k : Bool, G (Sum.inl (i, k)) :=
    ENNReal.tsum_prod (f := fun i k => G (Sum.inl (i, k)))
  rw [hprod]
  have h2 : ∀ i, ∑' k : Bool, G (Sum.inl (i, k)) = 2 * ∫⁻ w in chartAt ℂ (x i) '' P i,
      U ((chartAt ℂ (x i)).symm w) * ENNReal.ofReal ‖r (x i) w‖ := by
    intro i
    rw [tsum_fintype, Fintype.sum_bool, hsheet, hsheet, two_mul]
  simp_rw [h2]
  rw [ENNReal.tsum_mul_left]

end

/-- **Local biholomorphic chart pair of a cover.**  For an open holomorphic embedding `ι : S → X`, a continuous map
`pr : Y → X` with a local holomorphic inverse `e.symm` at `y`, `pr y = ι s`: the chart expressions
`B = φ_s ∘ (ι⁻¹ ∘ pr) ∘ φ_y⁻¹` and `B' = φ_y ∘ e⁻¹ ∘ ι ∘ φ_s⁻¹` are holomorphic local inverses of each other
near the chart centres. -/
theorem s82cmp_chart_pair {S X Y : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [Nonempty S]
    {ι : S → X} (hι : Topology.IsOpenEmbedding ι) (hιd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ι)
    {pr : Y → X} (hpr : Continuous pr) {y : Y} {s : S} (hs : pr y = ι s)
    (e : OpenPartialHomeomorph Y X) (hye : y ∈ e.source) (heq : EqOn pr e e.source)
    (hed : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target) :
    DifferentiableAt ℂ (fun z => chartAt ℂ s (Function.invFun ι (pr ((chartAt ℂ y).symm z))))
        (chartAt ℂ y y) ∧
      DifferentiableAt ℂ (fun u => chartAt ℂ y (e.symm (ι ((chartAt ℂ s).symm u)))) (chartAt ℂ s s) ∧
      chartAt ℂ s (Function.invFun ι (pr ((chartAt ℂ y).symm (chartAt ℂ y y)))) = chartAt ℂ s s ∧
      (∀ᶠ z in 𝓝 (chartAt ℂ y y),
        chartAt ℂ y (e.symm (ι ((chartAt ℂ s).symm
          (chartAt ℂ s (Function.invFun ι (pr ((chartAt ℂ y).symm z))))))) = z) ∧
      (∀ᶠ u in 𝓝 (chartAt ℂ s s),
        chartAt ℂ s (Function.invFun ι (pr ((chartAt ℂ y).symm
          (chartAt ℂ y (e.symm (ι ((chartAt ℂ s).symm u))))))) = u) := by
  classical
  set c := chartAt ℂ y y with hc
  set cs := chartAt ℂ s s with hcs
  have hy_src : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  have hs_src : s ∈ (chartAt ℂ s).source := mem_chart_source ℂ s
  have hct : c ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hy_src
  have hcst : cs ∈ (chartAt ℂ s).target := (chartAt ℂ s).map_source hs_src
  have hsymm_c : (chartAt ℂ y).symm c = y := (chartAt ℂ y).left_inv hy_src
  have hsymm_cs : (chartAt ℂ s).symm cs = s := (chartAt ℂ s).left_inv hs_src
  have hGy : Function.invFun ι (pr y) = s := by
    rw [hs]
    exact Function.leftInverse_invFun hι.isEmbedding.injective s
  have hιs_tgt : ι s ∈ e.target := by
    rw [← hs, heq hye]
    exact e.map_source hye
  have hesymm : e.symm (ι s) = y := by
    rw [← hs, heq hye]
    exact e.left_inv hye
  -- the open set `U''` of points `b` of `S` with `ι b ∈ e.target` and `e.symm (ι b) ∈ source y`
  set U'' : Set S := (chartAt ℂ s).source ∩ (ι ⁻¹' e.target ∩ {b | e.symm (ι b) ∈ (chartAt ℂ y).source})
    with hU''
  have hU''o : IsOpen U'' := by
    have h1 : IsOpen (ι ⁻¹' e.target) := e.open_target.preimage hι.continuous
    have hc2 : ContinuousOn (fun b => e.symm (ι b)) (ι ⁻¹' e.target) :=
      e.continuousOn_symm.comp hι.continuous.continuousOn (fun b hb => hb)
    have h2 := hc2.isOpen_inter_preimage h1 (chartAt ℂ y).open_source
    exact (chartAt ℂ s).open_source.inter h2
  have hsU : s ∈ U'' := ⟨hs_src, hιs_tgt, by simp only [mem_setOf_eq, hesymm]; exact hy_src⟩
  let B' : ℂ → ℂ := fun u => chartAt ℂ y (e.symm (ι ((chartAt ℂ s).symm u)))
  set Ω : Set ℂ := (chartAt ℂ s).target ∩ (chartAt ℂ s).symm ⁻¹' U'' with hΩ
  have hΩo : IsOpen Ω := (chartAt ℂ s).isOpen_inter_preimage_symm hU''o
  have hcsΩ : cs ∈ Ω := ⟨hcst, by simpa [hsymm_cs] using hsU⟩
  have hBd : ∀ u ∈ Ω, DifferentiableAt ℂ B' u := by
    intro u hu
    have hb : (chartAt ℂ s).symm u ∈ U'' := hu.2
    have hbs : (chartAt ℂ s).symm u ∈ (chartAt ℂ s).source := (chartAt ℂ s).map_target hu.1
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ι ((chartAt ℂ s).symm u) := hιd _
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e.symm (ι ((chartAt ℂ s).symm u)) :=
      (hed _ hb.2.1).mdifferentiableAt (e.open_target.mem_nhds hb.2.1)
    have h3 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun b => e.symm (ι b)) ((chartAt ℂ s).symm u) :=
      h2.comp _ h1
    have h4 := ((s23_mdifferentiableAt_iff hbs hb.2.2).1 h3).2
    rw [(chartAt ℂ s).right_inv hu.1] at h4
    exact h4
  have hBinj : InjOn B' Ω := by
    intro u₁ hu₁ u₂ hu₂ h
    have h1 : e.symm (ι ((chartAt ℂ s).symm u₁)) = e.symm (ι ((chartAt ℂ s).symm u₂)) :=
      (chartAt ℂ y).injOn hu₁.2.2.2 hu₂.2.2.2 h
    have h2 : ι ((chartAt ℂ s).symm u₁) = ι ((chartAt ℂ s).symm u₂) := by
      have := congrArg e h1
      rwa [e.right_inv hu₁.2.2.1, e.right_inv hu₂.2.2.1] at this
    have h3 := hι.isEmbedding.injective h2
    rw [← (chartAt ℂ s).right_inv hu₁.1, ← (chartAt ℂ s).right_inv hu₂.1, h3]
  have hB'ne : deriv B' cs ≠ 0 :=
    deriv_ne_zero_of_injOn hΩo (fun u hu => (hBd u hu).differentiableWithinAt) hBinj hcsΩ
  have hB'd : DifferentiableAt ℂ B' cs := hBd cs hcsΩ
  -- `B`
  let B : ℂ → ℂ := fun z => chartAt ℂ s (Function.invFun ι (pr ((chartAt ℂ y).symm z)))
  have hBc : B c = cs := by
    simp only [B, hsymm_c, hGy]
    rfl
  have hGcont : ContinuousAt (fun y' => Function.invFun ι (pr y')) y := by
    have h2 : ContinuousAt (Function.invFun ι) (pr y) := by
      rw [hs]; exact s82cmp_invFun_continuousAt hι ⟨s, rfl⟩
    exact h2.comp hpr.continuousAt
  have hsymm_cont : ContinuousAt (chartAt ℂ y).symm c := (chartAt ℂ y).continuousAt_symm hct
  have hGcont' : ContinuousAt (fun z => Function.invFun ι (pr ((chartAt ℂ y).symm z))) c :=
    hGcont.comp_of_eq hsymm_cont hsymm_c
  have hBcont : ContinuousAt B c := by
    have h3 : ContinuousAt (chartAt ℂ s) (Function.invFun ι (pr ((chartAt ℂ y).symm c))) := by
      rw [hsymm_c, hGy]; exact (chartAt ℂ s).continuousAt hs_src
    exact h3.comp_of_eq hGcont' rfl
  -- eventual facts near `c`
  have ha : ∀ᶠ z in 𝓝 c, z ∈ (chartAt ℂ y).target := (chartAt ℂ y).open_target.mem_nhds hct
  have hb : ∀ᶠ z in 𝓝 c, (chartAt ℂ y).symm z ∈ e.source :=
    hsymm_cont.eventually_mem (e.open_source.mem_nhds (by rw [hsymm_c]; exact hye))
  have hr : ∀ᶠ z in 𝓝 c, pr ((chartAt ℂ y).symm z) ∈ Set.range ι := by
    have hcomp : ContinuousAt (fun z => pr ((chartAt ℂ y).symm z)) c :=
      hpr.continuousAt.comp_of_eq hsymm_cont hsymm_c
    refine hcomp.eventually_mem ?_
    show Set.range ι ∈ 𝓝 (pr ((chartAt ℂ y).symm c))
    rw [hsymm_c, hs]
    exact hι.isOpen_range.mem_nhds ⟨s, rfl⟩
  have hd : ∀ᶠ z in 𝓝 c, Function.invFun ι (pr ((chartAt ℂ y).symm z)) ∈ (chartAt ℂ s).source := by
    refine hGcont'.eventually_mem ?_
    show (chartAt ℂ s).source ∈ 𝓝 (Function.invFun ι (pr ((chartAt ℂ y).symm c)))
    rw [hsymm_c, hGy]
    exact (chartAt ℂ s).open_source.mem_nhds hs_src
  have hBB' : ∀ᶠ z in 𝓝 c, B' (B z) = z := by
    filter_upwards [ha, hb, hr, hd] with z hz hy' hr' hGs
    simp only [B, B']
    rw [(chartAt ℂ s).left_inv hGs]
    have h1 : ι (Function.invFun ι (pr ((chartAt ℂ y).symm z))) = pr ((chartAt ℂ y).symm z) :=
      Function.invFun_eq hr'
    rw [h1, heq hy', e.left_inv hy', (chartAt ℂ y).right_inv hz]
  have hev2 : ∀ᶠ u in 𝓝 cs, u ∈ (chartAt ℂ s).target ∧ (chartAt ℂ s).symm u ∈ U'' := by
    refine Filter.Eventually.and ((chartAt ℂ s).open_target.mem_nhds hcst) ?_
    refine ((chartAt ℂ s).continuousAt_symm hcst).eventually_mem ?_
    rw [hsymm_cs]
    exact hU''o.mem_nhds hsU
  have hB'B : ∀ᶠ u in 𝓝 cs, B (B' u) = u := by
    filter_upwards [hev2] with u hu
    obtain ⟨hut, hbU⟩ := hu
    simp only [B, B']
    rw [(chartAt ℂ y).left_inv hbU.2.2]
    have h1 : pr (e.symm (ι ((chartAt ℂ s).symm u))) = ι ((chartAt ℂ s).symm u) := by
      rw [heq (e.map_target hbU.2.1), e.right_inv hbU.2.1]
    rw [h1, Function.leftInverse_invFun hι.isEmbedding.injective, (chartAt ℂ s).right_inv hut]
  have hB'has : HasDerivAt B' (deriv B' cs) (B c) := by rw [hBc]; exact hB'd.hasDerivAt
  have hBhas : HasDerivAt B (deriv B' cs)⁻¹ c :=
    HasDerivAt.of_local_left_inverse hBcont hB'has hB'ne hBB'
  refine ⟨hBhas.differentiableAt, hB'd, hBc, hBB', ?_⟩
  exact hB'B

/-- **The dilatation quotient is unchanged by lifting through a cover.**  If `f' : Y₀ → Y₁` covers `a : S₀ → S₁`
(`pr₁ (f' y) = ι₁ (a s)` whenever `pr₀ y = ι₀ s`), then `D_{f'}(y) = D_a(s)` at every `y` over `ι₀ s`. -/
theorem s82cmp_D_lift {S₀' S₁' X₀ X₁ Y₀ Y₁ : Type*} [TopologicalSpace S₀'] [ChartedSpace ℂ S₀']
    [IsManifold 𝓘(ℂ) ω S₀'] [Nonempty S₀'] [TopologicalSpace S₁'] [ChartedSpace ℂ S₁']
    [IsManifold 𝓘(ℂ) ω S₁'] [Nonempty S₁'] [TopologicalSpace X₀] [ChartedSpace ℂ X₀]
    [IsManifold 𝓘(ℂ) ω X₀] [TopologicalSpace X₁] [ChartedSpace ℂ X₁] [IsManifold 𝓘(ℂ) ω X₁]
    [TopologicalSpace Y₀] [ChartedSpace ℂ Y₀] [IsManifold 𝓘(ℂ) ω Y₀] [TopologicalSpace Y₁]
    [ChartedSpace ℂ Y₁] [IsManifold 𝓘(ℂ) ω Y₁]
    {ι₀ : S₀' → X₀} (hι₀ : Topology.IsOpenEmbedding ι₀) (hι₀d : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ι₀)
    {ι₁ : S₁' → X₁} (hι₁ : Topology.IsOpenEmbedding ι₁) (hι₁d : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ι₁)
    {pr₀ : Y₀ → X₀} (hpr₀ : Continuous pr₀) {pr₁ : Y₁ → X₁} (hpr₁ : Continuous pr₁)
    (hloc₀ : ∀ y, pr₀ y ∈ Set.range ι₀ → ∃ e : OpenPartialHomeomorph Y₀ X₀, y ∈ e.source ∧
      EqOn pr₀ e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    (hloc₁ : ∀ y, pr₁ y ∈ Set.range ι₁ → ∃ e : OpenPartialHomeomorph Y₁ X₁, y ∈ e.source ∧
      EqOn pr₁ e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    {a : S₀' → S₁'} {f' : Y₀ → Y₁} (hf' : Continuous f')
    (hrelf : ∀ y s, pr₀ y = ι₀ s → pr₁ (f' y) = ι₁ (a s)) {y : Y₀} {s : S₀'} (hs : pr₀ y = ι₀ s) :
    dilatationQuotient (localMapExpr f' y) (chartAt ℂ y y) =
      dilatationQuotient (localMapExpr a s) (chartAt ℂ s s) := by
  classical
  have hs₁ : pr₁ (f' y) = ι₁ (a s) := hrelf y s hs
  obtain ⟨e₀, he₀s, he₀eq, he₀d⟩ := hloc₀ y ⟨s, hs.symm⟩
  obtain ⟨e₁, he₁s, he₁eq, he₁d⟩ := hloc₁ (f' y) ⟨a s, hs₁.symm⟩
  obtain ⟨hBd, hB'd, hBc, hBB', hB'B⟩ := s82cmp_chart_pair hι₀ hι₀d hpr₀ hs e₀ he₀s he₀eq he₀d
  obtain ⟨hAd, hA'd, hAc, hAA', hA'A⟩ := s82cmp_chart_pair hι₁ hι₁d hpr₁ hs₁ e₁ he₁s he₁eq he₁d
  set c := chartAt ℂ y y with hc
  set cs := chartAt ℂ s s with hcs
  set c₁ := chartAt ℂ (f' y) (f' y) with hc₁
  set B : ℂ → ℂ := fun z => chartAt ℂ s (Function.invFun ι₀ (pr₀ ((chartAt ℂ y).symm z))) with hB
  set B' : ℂ → ℂ := fun u => chartAt ℂ y (e₀.symm (ι₀ ((chartAt ℂ s).symm u))) with hB'
  set A : ℂ → ℂ := fun w => chartAt ℂ (a s) (Function.invFun ι₁ (pr₁ ((chartAt ℂ (f' y)).symm w)))
    with hA
  set A' : ℂ → ℂ := fun u => chartAt ℂ (f' y) (e₁.symm (ι₁ ((chartAt ℂ (a s)).symm u))) with hA'
  set L' : ℂ → ℂ := localMapExpr f' y with hL'
  set L : ℂ → ℂ := localMapExpr a s with hL
  have hy_src : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  have hct : c ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hy_src
  have hsymm_c : (chartAt ℂ y).symm c = y := (chartAt ℂ y).left_inv hy_src
  have hs_src : s ∈ (chartAt ℂ s).source := mem_chart_source ℂ s
  have hL'c : L' c = c₁ := by
    simp only [hL', localMapExpr, hsymm_c]
    rfl
  have hBcs : B c = cs := hBc
  -- `L' = φ_{f' y} ∘ f' ∘ φ_y⁻¹` is continuous at `c`
  have hL'cont : ContinuousAt L' c := by
    have h1 : ContinuousAt (chartAt ℂ y).symm c := (chartAt ℂ y).continuousAt_symm hct
    have h2 : ContinuousAt f' ((chartAt ℂ y).symm c) := hf'.continuousAt
    have h3 : ContinuousAt (chartAt ℂ (f' y)) (f' ((chartAt ℂ y).symm c)) := by
      rw [hsymm_c]; exact (chartAt ℂ (f' y)).continuousAt (mem_chart_source ℂ (f' y))
    exact h3.comp_of_eq (h2.comp h1) rfl
  -- eventual facts near `c`
  have hsymm_cont : ContinuousAt (chartAt ℂ y).symm c := (chartAt ℂ y).continuousAt_symm hct
  have ha : ∀ᶠ z in 𝓝 c, z ∈ (chartAt ℂ y).target := (chartAt ℂ y).open_target.mem_nhds hct
  have hr : ∀ᶠ z in 𝓝 c, pr₀ ((chartAt ℂ y).symm z) ∈ Set.range ι₀ := by
    have hcomp : ContinuousAt (fun z => pr₀ ((chartAt ℂ y).symm z)) c :=
      hpr₀.continuousAt.comp_of_eq hsymm_cont hsymm_c
    refine hcomp.eventually_mem ?_
    show Set.range ι₀ ∈ 𝓝 (pr₀ ((chartAt ℂ y).symm c))
    rw [hsymm_c, hs]
    exact hι₀.isOpen_range.mem_nhds ⟨s, rfl⟩
  have hd : ∀ᶠ z in 𝓝 c, Function.invFun ι₀ (pr₀ ((chartAt ℂ y).symm z)) ∈ (chartAt ℂ s).source := by
    have hGcont : ContinuousAt (fun y' => Function.invFun ι₀ (pr₀ y')) y := by
      have h2 : ContinuousAt (Function.invFun ι₀) (pr₀ y) := by
        rw [hs]; exact s82cmp_invFun_continuousAt hι₀ ⟨s, rfl⟩
      exact h2.comp hpr₀.continuousAt
    have hG' : ContinuousAt (fun z => Function.invFun ι₀ (pr₀ ((chartAt ℂ y).symm z))) c :=
      hGcont.comp_of_eq hsymm_cont hsymm_c
    refine hG'.eventually_mem ?_
    show (chartAt ℂ s).source ∈ 𝓝 (Function.invFun ι₀ (pr₀ ((chartAt ℂ y).symm c)))
    rw [hsymm_c, hs, Function.leftInverse_invFun hι₀.isEmbedding.injective s]
    exact (chartAt ℂ s).open_source.mem_nhds hs_src
  have hf : ∀ᶠ z in 𝓝 c, f' ((chartAt ℂ y).symm z) ∈ (chartAt ℂ (f' y)).source := by
    have hcomp : ContinuousAt (fun z => f' ((chartAt ℂ y).symm z)) c :=
      hf'.continuousAt.comp_of_eq hsymm_cont hsymm_c
    refine hcomp.eventually_mem ?_
    show (chartAt ℂ (f' y)).source ∈ 𝓝 (f' ((chartAt ℂ y).symm c))
    rw [hsymm_c]
    exact (chartAt ℂ (f' y)).open_source.mem_nhds (mem_chart_source ℂ (f' y))
  have hev : (L ∘ B) =ᶠ[𝓝 c] (A ∘ L') := by
    filter_upwards [ha, hr, hd, hf] with z hz hr' hGs hfs
    simp only [Function.comp, hL, hL', hA, hB, localMapExpr]
    set y' := (chartAt ℂ y).symm z with hy'
    set s' := Function.invFun ι₀ (pr₀ y') with hs'
    have h1 : ι₀ s' = pr₀ y' := Function.invFun_eq hr'
    have h2 : pr₁ (f' y') = ι₁ (a s') := hrelf y' s' h1.symm
    rw [(chartAt ℂ s).left_inv hGs, (chartAt ℂ (f' y)).left_inv hfs, h2]
    rw [Function.leftInverse_invFun hι₁.isEmbedding.injective (a s')]
  -- the complex dilatations agree
  have hμ : complexDilatation (L ∘ B) c = complexDilatation (A ∘ L') c := by
    simp only [complexDilatation, dz, dzbar, hev.fderiv_eq (𝕜 := ℝ)]
  have hLc : B c = cs := hBc
  have h1 : complexDilatation (A ∘ L') c = complexDilatation L' c := by
    refine s23_dilatation_comp_left (k := A') hL'cont ?_ ?_ ?_
    · rw [hL'c]; exact hAd
    · rw [hL'c]
      have : A c₁ = chartAt ℂ (a s) (a s) := by
        simpa [hA, hc₁] using hAc
      rw [this]; exact hA'd
    · rw [hL'c]; exact hAA'
  have h2 : complexDilatation (L ∘ B) c = complexDilatation L (B c) * (conj (deriv B c) / deriv B c) := by
    refine s23_dilatation_comp_right (S := B') hBd ?_ hBB' ?_
    · rw [hBcs]; exact hB'd
    · rw [hBcs]; exact hB'B
  have hBne : deriv B c ≠ 0 := s23_deriv_ne_zero hBd (by rw [hBcs]; exact hB'd) hBB'
  have hnorm : ‖complexDilatation L' c‖ = ‖complexDilatation L cs‖ := by
    rw [← h1, ← hμ, h2, hBcs, norm_mul, norm_div, Complex.norm_conj,
      div_self (norm_ne_zero_iff.2 hBne), mul_one]
  unfold dilatationQuotient
  rw [hnorm]




variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]

/-- `surfaceIntegral` is homogeneous for positive real scalars (no compactness needed). -/
theorem s82cmp_surfaceIntegral_smul {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    (q : S → ℂ → ℂ) (u : S → ℂ → ℝ≥0∞) {c : ℝ} (hc : 0 < c) :
    surfaceIntegral ((c : ℂ) • q) u = ENNReal.ofReal c * surfaceIntegral q u := by
  have h0 : ENNReal.ofReal c ≠ 0 := by simpa using hc
  have h1 : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold surfaceIntegral
  simp only [ENNReal.mul_iInf_of_ne h0 h1]
  refine iInf_congr fun x => iInf_congr fun P => iInf_congr fun hP => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [← lintegral_const_mul' _ _ h1]
  refine lintegral_congr fun z => ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  rw [ENNReal.ofReal_mul hc.le]
  ring

theorem s82cmp_quadDiffNorm_smul {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    (q : S → ℂ → ℂ) {c : ℝ} (hc : 0 < c) :
    quadDiffNorm ((c : ℂ) • q) = ENNReal.ofReal c * quadDiffNorm q :=
  s82cmp_surfaceIntegral_smul q _ hc


/-- **The comparison inequality for closed surfaces** (Teichmüller's main inequality, `eq29_7` applied to the
inverse): `h : A → B` a Teichmüller map between closed surfaces of the same genus `> 1` with initial
differential `q` of area `1`, `a ≃ h` quasiconformal: `K[h] ≤ ∬_A D[a] dA_q`. -/
theorem s82cmp_closed_core {g : ℕ} (hg : 1 < g) {A B : ClosedRS.{u}} (hA : HasGenus A.carrier g)
    (hB : HasGenus B.carrier g) {h : A.carrier ≃ₜ B.carrier} {q : A.carrier → ℂ → ℂ}
    {q' : B.carrier → ℂ → ℂ} {k : ℝ} (hh : IsTeichmullerMap h q q' k)
    (a : A.carrier ≃ₜ B.carrier) (ha : IsQCRS a)
    (hhom : ContinuousMap.Homotopic (h : C(A.carrier, B.carrier)) (a : C(A.carrier, B.carrier)))
    (hnorm : quadDiffNorm q = 1) :
    ENNReal.ofReal ((1 + k) / (1 - k)) ≤ surfaceIntegral q
      (fun x z => ENNReal.ofReal (dilatationQuotient (localMapExprAt a x z) z)) := by
  classical
  haveI : Nonempty A.carrier := ConnectedSpace.toNonempty
  set K : ℝ := (1 + k) / (1 - k) with hK
  have hk1 : k < 1 := hh.k_lt_one
  have hk0 : 0 ≤ k := hh.k_nonneg
  have hKpos : 0 < K := div_pos (by linarith) (by linarith)
  have hG := utm_x_teichmullerMap_symm hh
  have hc : 0 < (K ^ 2)⁻¹ := inv_pos.2 (pow_pos hKpos 2)
  have hG' := s29_e12_teichMap_smul hG hc
  have e1 : ((((K ^ 2)⁻¹ : ℝ) : ℂ) • ((((-(K ^ 2) : ℝ)) : ℂ) • q)) = -q := by
    funext x z
    have hK2 : (K ^ 2 : ℝ) ≠ 0 := (pow_pos hKpos 2).ne'
    have hK2c : ((K ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hK2
    have hKc : (K : ℂ) ≠ 0 := by exact_mod_cast hKpos.ne'
    simp only [Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
    push_cast
    field_simp
  rw [e1] at hG'
  have hsm : ∀ u : A.carrier → ℂ → ℝ≥0∞, surfaceIntegral (-q) u = surfaceIntegral q u := by
    intro u
    have := s26_surfaceIntegral_smul q u (-1)
    rwa [neg_one_smul, norm_neg, norm_one, ENNReal.ofReal_one, one_mul] at this
  have hnorm' : quadDiffNorm (-q) = 1 := by
    rw [quadDiffNorm, hsm]
    exact hnorm
  have hhom'' := s29_e7_homotopic_symm hhom
  have hhom3 : ContinuousMap.Homotopic (h.symm : C(B.carrier, A.carrier))
      (((a.symm.trans (Homeomorph.refl A.carrier) : B.carrier ≃ₜ A.carrier)) : C(B.carrier, A.carrier)) := by
    have e : ((a.symm.trans (Homeomorph.refl A.carrier) : B.carrier ≃ₜ A.carrier) :
        C(B.carrier, A.carrier)) = (a.symm : C(B.carrier, A.carrier)) := rfl
    rw [e]
    exact hhom''
  have key := eq29_7 hg hA (S := A.carrier) (Sn := B.carrier) hA hB (f := Homeomorph.refl A.carrier)
    (fn := a) isQCRS_refl ha hG' hhom3 hnorm'
  have hfun : ⇑((Homeomorph.refl A.carrier).symm.trans a) = ⇑a := rfl
  rw [hfun, hsm] at key
  exact key


/-- The area integral of the dilatation density read in the chart at the image point equals the point-function
form `p ↦ D_f(p)` (chart independence of `D`, `s29_e7_D_inv`). -/
theorem s82cmp_surfaceIntegral_Dil {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [TopologicalSpace Y] [ChartedSpace ℂ Y] (f : X → Y) (q : X → ℂ → ℂ) :
    surfaceIntegral q (fun y z => ENNReal.ofReal (dilatationQuotient (localMapExprAt f y z) z)) =
      surfaceIntegral q (fun y z => ENNReal.ofReal (dilatationQuotient
        (localMapExpr f ((chartAt ℂ y).symm z))
        (chartAt ℂ ((chartAt ℂ y).symm z) ((chartAt ℂ y).symm z)))) := by
  unfold surfaceIntegral
  refine iInf_congr fun x => iInf_congr fun P => iInf_congr fun hP => tsum_congr fun i => ?_
  refine setLIntegral_congr_fun (hP.1 i).2 fun z hz => ?_
  obtain ⟨a, ha, rfl⟩ := hz
  have hzt : chartAt ℂ (x i) a ∈ (chartAt ℂ (x i)).target :=
    (chartAt ℂ (x i)).map_source ((hP.1 i).1 ha)
  beta_reduce
  rw [s29_e7_D_inv f (x i) hzt]

/-- For a finite-type structure of type `(g, 0, 0)` the surface `S₀` is compact (`ι` is a homeomorphism onto `X`). -/
theorem s82cmp_type_zero {g : ℕ} (F₀ : FiniteTypeStructure S₀ g 0 0) :
    CompactSpace S₀ ∧ Nonempty (F₀.X.carrier ≃ₜ S₀) := by
  have hP : F₀.P = ∅ := Finset.card_eq_zero.1 F₀.card_P
  have hrange : Set.range F₀.ι = Set.univ := by
    rw [F₀.range_ι, hP]
    simp
  have hemb : Topology.IsEmbedding F₀.ι := F₀.embedding.isEmbedding
  have hcl : IsClosed (Set.range F₀.ι) := by rw [hrange]; exact isClosed_univ
  refine ⟨(Topology.IsClosedEmbedding.mk hemb hcl).compactSpace, ⟨?_⟩⟩
  exact (Equiv.ofBijective F₀.ι ⟨hemb.injective, Set.range_eq_univ.1 hrange⟩).toHomeomorphOfIsInducing
    hemb.isInducing |>.symm

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

/-- The comparison inequality for surfaces of type `(g, 0, 0)` (closed surfaces): `eq29_7` applied to `h⁻¹`. -/
theorem s82cmp_core_closed {g : ℕ} (hex : ¬ IsExceptionalType g 0 0) (F₀ : FiniteTypeStructure S₀ g 0 0)
    (Y : FiniteTypeRS.{u} g 0 0) (a : S₀ ≃ₜ Y.carrier) (ha : IsQCRS a) {h : S₀ ≃ₜ Y.carrier}
    {r : S₀ → ℂ → ℂ} {r' : Y.carrier → ℂ → ℂ} {k : ℝ} (hh : IsAdmissibleTeichmullerMap F₀ h r r' k)
    (hk : 0 < k) (hhom : ContinuousMap.Homotopic (h : C(S₀, Y.carrier)) (a : C(S₀, Y.carrier)))
    (hnorm : quadDiffNorm r = 1) :
    maxDilatationRS h ≤ surfaceIntegral r
      (fun x z => ENNReal.ofReal (dilatationQuotient (localMapExprAt a x z) z)) := by
  classical
  obtain ⟨hcS, ⟨eS⟩⟩ := s82cmp_type_zero F₀
  obtain ⟨hcY, ⟨eY⟩⟩ := s82cmp_type_zero Y.structure'
  haveI : CompactSpace S₀ := hcS
  haveI : CompactSpace Y.carrier := hcY
  haveI : Nonempty S₀ := ConnectedSpace.toNonempty
  have hg : 1 < g := by
    by_contra hg'
    have : g = 0 ∨ g = 1 := by omega
    rcases this with rfl | rfl <;> exact hex (by simp [IsExceptionalType])
  let XS : ClosedRS.{u} := ⟨S₀⟩
  let XY : ClosedRS.{u} := ⟨Y.carrier⟩
  have hSg : HasGenus S₀ g :=
    hasGenus_of_homeomorph (X := XS) F₀.genus (eS : F₀.X.carrier ≃ₜ XS.carrier)
  have hYg : HasGenus Y.carrier g :=
    hasGenus_of_homeomorph (X := XY) Y.structure'.genus (eY : Y.structure'.X.carrier ≃ₜ XY.carrier)
  set K : ℝ := (1 + k) / (1 - k) with hK
  have hk1 : k < 1 := hh.2.k_lt_one
  have hKpos : 0 < K := div_pos (by linarith) (by linarith)
  have hG := utm_x_teichmullerMap_symm hh.2
  have hc : 0 < (K ^ 2)⁻¹ := inv_pos.2 (pow_pos hKpos 2)
  have hG' := s29_e12_teichMap_smul hG hc
  have e1 : ((((K ^ 2)⁻¹ : ℝ) : ℂ) • ((((-(K ^ 2) : ℝ)) : ℂ) • r)) = -r := by
    funext x z
    have hK2 : (K ^ 2 : ℝ) ≠ 0 := (pow_pos hKpos 2).ne'
    have hK2c : ((K ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hK2
    have hKc : (K : ℂ) ≠ 0 := by exact_mod_cast hKpos.ne'
    simp only [Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
    push_cast
    field_simp
  rw [e1] at hG'
  have hsm : ∀ u : S₀ → ℂ → ℝ≥0∞, surfaceIntegral (-r) u = surfaceIntegral r u := by
    intro u
    have := s26_surfaceIntegral_smul r u (-1)
    rwa [neg_one_smul, norm_neg, norm_one, ENNReal.ofReal_one, one_mul] at this
  have hnorm' : quadDiffNorm (-r) = 1 := by
    rw [quadDiffNorm, hsm]
    exact hnorm
  have hhom'' := s29_e7_homotopic_symm hhom
  have hhom3 : ContinuousMap.Homotopic (h.symm : C(Y.carrier, S₀))
      (((a.symm.trans (Homeomorph.refl S₀) : Y.carrier ≃ₜ S₀)) : C(Y.carrier, S₀)) := by
    have e : ((a.symm.trans (Homeomorph.refl S₀) : Y.carrier ≃ₜ S₀) : C(Y.carrier, S₀)) =
        (a.symm : C(Y.carrier, S₀)) := rfl
    rw [e]
    exact hhom''
  have key := eq29_7 hg hSg (S := S₀) (Sn := Y.carrier) hSg hYg (f := Homeomorph.refl S₀) (fn := a)
    isQCRS_refl ha hG' hhom3 hnorm'
  have hfun : ⇑((Homeomorph.refl S₀).symm.trans a) = ⇑a := rfl
  rw [hfun, hsm] at key
  have hmax : maxDilatationRS h = ENNReal.ofReal K := (teichmullerMap_beltrami hh.2).2
  rw [hmax]
  exact key

end

end LiZhongQC
