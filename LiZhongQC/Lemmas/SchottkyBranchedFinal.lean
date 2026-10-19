import LiZhongQC.Lemmas.SchottkyBranchedCover5
import LiZhongQC.Lemmas.SchottkyBranchedPunctureData
import LiZhongQC.Lemmas.HurwitzProofChain
import LiZhongQC.Lemmas.SchottkyClosedGenus

/-!
# The branched double cover and its genus (R82, §32.1)

Final assembly of the relocated book theorem `exists_branched_double_cover`
(helper `s82bc_exists_branched_double_cover`): the puncture data (`s82bc_puncture_data`), the cover
with its local multiplicities (`s82bc_branched_main2`), and the genus `2g + n - 1` by the installed
Riemann–Hurwitz formula `h77d_riemann_hurwitz_of_quotient_multiplicity`.
-/

open Set Topology Filter
open scoped Manifold ContDiff

noncomputable section
namespace LiZhongQC
universe u


section MainTheorem

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X] [ConnectedSpace X]
  [CompactSpace X] [IsManifold 𝓘(ℂ) ω X]

/-- **The branched double cover** attached to an index-two subgroup `K` of `π₁(X ∖ P)` which
changes sheets around each puncture. -/
theorem s82bc_branched_main2 {ι : Type u} (e : ι → X) (he : Function.Injective e)
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
      ∃ pr : T → X, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr ∧ ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω pr ∧
        (∀ y : T, pr y ∈ U → analyticOrderAt (fun z =>
          (chartAt ℂ (pr y) ∘ pr ∘ (chartAt ℂ y).symm) z - chartAt ℂ (pr y) (pr y))
          (chartAt ℂ y y) = 1) ∧
        (∀ y : T, pr y ∉ U → analyticOrderAt (fun z =>
          (chartAt ℂ (pr y) ∘ pr ∘ (chartAt ℂ y).symm) z - chartAt ℂ (pr y) (pr y))
          (chartAt ℂ y y) = 2) ∧ Function.Surjective pr ∧
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
  have hinl_ev : ∀ y : Y, ∀ᶠ z in 𝓝 (chartAt ℂ (Sum.inl y : Y ⊕ ι) (Sum.inl y)),
      chartAt ℂ (ψ y) (Sum.elim ψ e ((chartAt ℂ (Sum.inl y : Y ⊕ ι)).symm z)) = z := by
    intro y
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
  have hpr_md : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Sum.elim ψ e) := by
    rintro (y | i)
    · refine s82bc_mdiffAt_of_charts (Sum.elim ψ e) (Sum.inl y) hprc.continuousAt id
        differentiableAt_id (hinl_ev y)
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
  have hpr_cm : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (Sum.elim ψ e) := k22u_mdifferentiable_contMDiff hpr_md
  have hord1 : ∀ y : Y, analyticOrderAt (fun z =>
      (chartAt ℂ (Sum.elim ψ e (Sum.inl y)) ∘ Sum.elim ψ e ∘
        (chartAt ℂ (Sum.inl y : Y ⊕ ι)).symm) z -
        chartAt ℂ (Sum.elim ψ e (Sum.inl y)) (Sum.elim ψ e (Sum.inl y)))
      (chartAt ℂ (Sum.inl y : Y ⊕ ι) (Sum.inl y)) = 1 := by
    intro y
    have hev := hinl_ev y
    have hself := hev.self_of_nhds
    rw [(chartAt ℂ (Sum.inl y : Y ⊕ ι)).left_inv (mem_chart_source ℂ _)] at hself
    have hcongr : (fun z => (chartAt ℂ (Sum.elim ψ e (Sum.inl y)) ∘ Sum.elim ψ e ∘
        (chartAt ℂ (Sum.inl y : Y ⊕ ι)).symm) z -
        chartAt ℂ (Sum.elim ψ e (Sum.inl y)) (Sum.elim ψ e (Sum.inl y))) =ᶠ[𝓝 (chartAt ℂ
          (Sum.inl y : Y ⊕ ι) (Sum.inl y))]
        (fun z => z - chartAt ℂ (Sum.inl y : Y ⊕ ι) (Sum.inl y)) := by
      filter_upwards [hev] with z hz
      show chartAt ℂ (ψ y) (Sum.elim ψ e ((chartAt ℂ (Sum.inl y : Y ⊕ ι)).symm z)) -
        chartAt ℂ (ψ y) (ψ y) = _
      rw [hz]
      show _ - chartAt ℂ (ψ y) (Sum.elim ψ e (Sum.inl y)) = _
      rw [hself]
    rw [analyticOrderAt_congr hcongr]
    exact analyticOrderAt_id_sub_const_self
  have hord2 : ∀ i : ι, analyticOrderAt (fun z =>
      (chartAt ℂ (Sum.elim ψ e (Sum.inr i)) ∘ Sum.elim ψ e ∘
        (chartAt ℂ (Sum.inr i : Y ⊕ ι)).symm) z -
        chartAt ℂ (Sum.elim ψ e (Sum.inr i)) (Sum.elim ψ e (Sum.inr i)))
      (chartAt ℂ (Sum.inr i : Y ⊕ ι) (Sum.inr i)) = 2 := by
    intro i
    have hmem : Sum.inr i ∈ (Wend i).source := by rw [hsrc]; exact Or.inl rfl
    have hWm' : Wend i ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω (Y ⊕ ι) := by
      rw [← hchr i]; exact IsManifold.chart_mem_maximalAtlas (Sum.inr i)
    have h := h77d_chart_multiplicity_of_power_model (Sum.elim ψ e) hpr_cm (Sum.inr i) 2
      (by norm_num) (Wend i) (E i) hmem (by rw [happ_r]) (hEsrc i)
      (contMDiffOn_of_mem_maximalAtlas hWm') (contMDiffOn_symm_of_mem_maximalAtlas hWm')
      (contMDiffOn_of_mem_maximalAtlas (hEm i)) (contMDiffOn_symm_of_mem_maximalAtlas (hEm i))
      (by
        intro x hx
        rw [hsrc] at hx
        rcases hx with rfl | ⟨y, hy, rfl⟩
        · show E i (e i) = (Wend i (Sum.inr i)) ^ 2
          rw [happ_r, hEp i]; norm_num
        · show E i (ψ y) = (Wend i (Sum.inl y)) ^ 2
          rw [happ_l]
          exact (hW0sq i y hy).2.symm)
    exact_mod_cast h
  refine ⟨Y ⊕ ι, τT, csT, hT2, hconn, hcpt, hmanT, Sum.elim ψ e, hpr_md, hpr_cm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (y | i) hy
    · exact hord1 y
    · exact absurd hy (heU i)
  · rintro (y | i) hy
    · exact absurd (hψU y) hy
    · exact hord2 i
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

/-- Any Riemann surface has two distinct points. -/
theorem s82bc_exists_ne (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] [Nonempty X] :
    ∃ a b : X, a ≠ b := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hxt : chartAt ℂ x x ∈ (chartAt ℂ x).target :=
    (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp (chartAt ℂ x).open_target _ hxt
  have hw : chartAt ℂ x x + ((ε / 2 : ℝ) : ℂ) ∈ (chartAt ℂ x).target := by
    apply hsub
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ ε / 2)]
    linarith
  refine ⟨x, (chartAt ℂ x).symm (chartAt ℂ x x + ((ε / 2 : ℝ) : ℂ)), fun hxy => ?_⟩
  have := congrArg (chartAt ℂ x) hxy
  rw [(chartAt ℂ x).right_inv hw] at this
  have h2 : ((ε / 2 : ℝ) : ℂ) = 0 :=
    add_left_cancel (a := chartAt ℂ x x) (this.symm.trans (add_zero _).symm)
  have h3 : (ε / 2 : ℝ) = 0 := by exact_mod_cast h2
  linarith

/-- §32.1 (the two-sheeted covering): a closed surface `X` with an even number `2n` of marked points
`P` has a two-sheeted covering `X̃ → X` (a closed surface of genus `2g + n - 1`) branched exactly
at `P` (branching order `1`); it is obtained by cutting along `n` disjoint arcs joining the points
of `P` in pairs and gluing two copies crosswise.

**Correction (2026-09-27).**  The hypothesis `hgn : g ≠ 0 ∨ n ≠ 0` was added: for `(g, n) = (0, 0)` the
conclusion asks for a connected unbranched two-sheeted cover of the sphere, which does not exist (refuted in
Lean, s31t). -/
theorem s82bc_exists_branched_double_cover {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] [CompactSpace X] {g n : ℕ} (hgn : g ≠ 0 ∨ n ≠ 0)
    (hX : HasGenus X g) (P : Finset X) (hP : P.card = 2 * n) :
    ∃ (X' : ClosedRS.{u}) (pr : X'.carrier → X), HasGenus X'.carrier (2 * g + n - 1) ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr ∧ Function.Surjective pr ∧
      (∀ x ∉ P, (pr ⁻¹' {x}).ncard = 2) ∧ (∀ x ∈ P, (pr ⁻¹' {x}).ncard = 1) ∧
      ∃ h : X'.carrier ≃ₜ X'.carrier, IsBiholomorphic h ∧ (∀ y, h (h y) = y) ∧ (∀ y, pr (h y) = pr y) ∧
        ∀ y, h y = y ↔ pr y ∈ P := by
  classical
  have hPe : Even P.card := ⟨n, by omega⟩
  have hgn' : g ≠ 0 ∨ P.card ≠ 0 := by
    rcases hgn with h | h
    · exact Or.inl h
    · right; omega
  obtain ⟨U, hUc, hUconn, x₀, K, hK, hloc⟩ := s82bc_puncture_data hX P hPe hgn'
  have hrange : range (Subtype.val : ↥P → X) = (U : Set X)ᶜ := by
    rw [hUc, Subtype.range_coe]
  have hU : ∀ x : X, x ∈ U ↔ x ∉ P := by
    intro x
    have : x ∈ (U : Set X)ᶜ ↔ x ∈ (↑P : Set X) := by rw [hUc]
    simpa using this.not
  obtain ⟨T, tT, cT, hT2, hconn, hcpt, hman, pr, hmd, hcm, hord1, hord2, hsurj, hfib2, hfib1, h,
    hbih, hinv, hprh, hfix⟩ := s82bc_branched_main2 (Subtype.val : ↥P → X) Subtype.val_injective U
      hrange x₀ K hK hloc
  haveI : ConnectedSpace U := hUconn
  have hprU : ∀ y : T, pr y ∈ U ↔ h y ≠ y := by
    intro y
    rw [Ne, hfix y]
    exact not_not.symm
  have hnt : ∃ a b : X, a ≠ b := s82bc_exists_ne X
  have hnc : ¬ Jacobians.Discharge.IsConstantMap pr := by
    rintro ⟨c, hc⟩
    obtain ⟨a, b, hab⟩ := hnt
    obtain ⟨ya, rfl⟩ := hsurj a
    obtain ⟨yb, rfl⟩ := hsurj b
    exact hab ((hc ya).trans (hc yb).symm)
  have hcases : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
  have hsq : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide
  have hone : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  let σ : Equiv.Perm T := h.toEquiv
  let φ : Multiplicative (ZMod 2) →* Equiv.Perm T :=
    { toFun := fun g => if g = 1 then 1 else σ
      map_one' := by simp
      map_mul' := by
        intro a b
        rcases hcases a with rfl | rfl <;> rcases hcases b with rfl | rfl
        · simp
        · simp
        · simp
        · rw [hsq]
          ext y
          simp only [if_true, if_neg hone]
          exact (hinv y).symm }
  letI : MulAction (Multiplicative (ZMod 2)) T := MulAction.compHom T φ
  have hsmul : ∀ (g : Multiplicative (ZMod 2)) (y : T), g • y = if g = 1 then y else h y := by
    intro g y
    show (φ g) y = _
    by_cases hg : g = 1
    · simp [φ, hg]
    · simp [φ, hg, σ]
  have hfiber : ∀ x y : T, pr x = pr y ↔ ∃ g : Multiplicative (ZMod 2), g • x = y := by
    intro x y
    constructor
    · intro hxy
      by_cases hfx : h x = x
      · have hP : pr x ∈ (P : Set X) := by
          have := (hfix x).mp hfx
          rwa [← hUc]
        have h1 := hfib1 (pr x) (fun hU' => (hU _).mp hU' hP)
        obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
        have hx : x ∈ pr ⁻¹' {pr x} := rfl
        have hy : y ∈ pr ⁻¹' {pr x} := hxy.symm
        rw [ha] at hx hy
        exact ⟨1, by rw [hsmul, if_pos rfl, mem_singleton_iff.mp hx, mem_singleton_iff.mp hy]⟩
      · have hU' : pr x ∈ U := (hprU x).mpr hfx
        have h2 := hfib2 (pr x) hU'
        have hfin : (pr ⁻¹' {pr x}).Finite := Set.finite_of_ncard_ne_zero (by rw [h2]; norm_num)
        have hpair : ({x, h x} : Set T) = pr ⁻¹' {pr x} := by
          apply Set.eq_of_subset_of_ncard_le
          · intro z hz
            rcases hz with rfl | rfl
            · rfl
            · exact (hprh x)
          · rw [h2, Set.ncard_pair (Ne.symm hfx)]
          · exact hfin
        have hy : y ∈ ({x, h x} : Set T) := by rw [hpair]; exact hxy.symm
        rcases hy with rfl | rfl
        · exact ⟨1, by rw [hsmul, if_pos rfl]⟩
        · exact ⟨Multiplicative.ofAdd 1, by rw [hsmul, if_neg hone]⟩
    · rintro ⟨g, rfl⟩
      rw [hsmul]
      split_ifs
      · rfl
      · exact (hprh x).symm
  have hcard : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    simp [Nat.card_eq_fintype_card]
  have hstab : ∀ y : T, Nat.card (MulAction.stabilizer (Multiplicative (ZMod 2)) y) =
      if h y = y then 2 else 1 := by
    intro y
    by_cases hy : h y = y
    · rw [if_pos hy]
      have : MulAction.stabilizer (Multiplicative (ZMod 2)) y = ⊤ := by
        rw [Subgroup.eq_top_iff']
        intro g
        rw [MulAction.mem_stabilizer_iff, hsmul]
        split_ifs
        · rfl
        · exact hy
      rw [this, Subgroup.card_top, hcard]
    · rw [if_neg hy]
      have : MulAction.stabilizer (Multiplicative (ZMod 2)) y = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro g hg
        rw [MulAction.mem_stabilizer_iff, hsmul] at hg
        by_contra hg1
        rw [if_neg hg1] at hg
        exact hy hg
      rw [this, Subgroup.card_bot]
  have hloc' : ∀ y : T, analyticOrderAt (fun z =>
      (chartAt ℂ (pr y) ∘ pr ∘ (chartAt ℂ y).symm) z - chartAt ℂ (pr y) (pr y))
      (chartAt ℂ y y) =
      (Nat.card (MulAction.stabilizer (Multiplicative (ZMod 2)) y) : ℕ∞) := by
    intro y
    rw [hstab y]
    by_cases hy : pr y ∈ U
    · rw [hord1 y hy, if_neg ((hprU y).mp hy)]; rfl
    · have hfy : h y = y := by
        by_contra hne; exact hy ((hprU y).mpr hne)
      rw [hord2 y hy, if_pos hfy]; rfl
  obtain ⟨R, hR, hRfin, hRH⟩ := h77d_riemann_hurwitz_of_quotient_multiplicity
    (G := Multiplicative (ZMod 2)) pr hcm hnc hsurj hfiber hloc'
  obtain ⟨gT, hgT⟩ := closed_surface_has_genus (S := T)
  have e1 := k22rr_genus_eq hgT
  have e2 := k22rr_genus_eq hX
  have hRval : ∀ y, R y = if h y = y then 1 else 0 := by
    intro y
    rw [hR y, hstab y]
    split_ifs <;> simp
  have hsupp : (R.support : Set T) = {y | h y = y} := by
    ext y
    simp only [Finset.mem_coe, Finsupp.mem_support_iff, mem_setOf_eq, hRval]
    split_ifs with hy <;> simp [hy]
  have hdeg : Finsupp.degree R = (P.card : ℤ) := by
    have h1 : Finsupp.degree R = (R.support.card : ℤ) := by
      rw [Finsupp.degree, Finset.card_eq_sum_ones, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro y hy
      have hy' : h y = y := by
        have : y ∈ (R.support : Set T) := hy
        rw [hsupp] at this; exact this
      rw [hRval, if_pos hy']; rfl
    rw [h1]
    have h2 : R.support.card = ({y | h y = y} : Set T).ncard := by
      rw [← hsupp, Set.ncard_coe_finset]
    have h3 : ({y | h y = y} : Set T).ncard = (P : Set X).ncard := by
      apply Set.ncard_congr (fun y _ => pr y)
      · intro y hy
        have := (hfix y).mp hy
        rwa [← hUc]
      · intro y1 y2 hy1 hy2 hpr
        have hP : pr y1 ∈ (P : Set X) := by
          have := (hfix y1).mp hy1
          rwa [← hUc]
        have h1 := hfib1 (pr y1) (fun hU' => (hU _).mp hU' hP)
        obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
        have m1 : y1 ∈ pr ⁻¹' {pr y1} := rfl
        have m2 : y2 ∈ pr ⁻¹' {pr y1} := hpr.symm
        rw [ha] at m1 m2
        rw [mem_singleton_iff.mp m1, mem_singleton_iff.mp m2]
      · intro x hx
        obtain ⟨y, rfl⟩ := hsurj x
        refine ⟨y, ?_, rfl⟩
        show h y = y
        rw [hfix]
        rw [← hUc] at hx
        exact fun hU' => hx hU'
    rw [h2, h3, Set.ncard_coe_finset]
  rw [hcard, hdeg, e1, e2, hP] at hRH
  have hgTeq : gT = 2 * g + n - 1 := by
    push_cast at hRH
    omega
  refine ⟨{ carrier := T }, pr, ?_, hmd, hsurj, ?_, ?_, h, hbih, hinv, hprh, ?_⟩
  · show HasGenus T (2 * g + n - 1)
    rw [← hgTeq]; exact hgT
  · intro x hx
    exact hfib2 x ((hU x).mpr hx)
  · intro x hx
    exact hfib1 x (fun hxU => (hU x).mp hxU hx)
  · intro y
    rw [hfix y]
    have := hU (pr y)
    tauto

section RelocatedS32

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- §32.1 (the two-sheeted covering): a closed surface `X` with an even number `2n` of marked points
`P` has a two-sheeted covering `X̃ → X` (a closed surface of genus `2g + n - 1`) branched exactly
at `P` (branching order `1`); it is obtained by cutting along `n` disjoint arcs joining the points
of `P` in pairs and gluing two copies crosswise.

**Correction (2026-09-27).**  The hypothesis `hgn : g ≠ 0 ∨ n ≠ 0` was added: for `(g, n) = (0, 0)` the
conclusion asks for a connected unbranched two-sheeted cover of the sphere, which does not exist (refuted in
Lean, s31t). -/
theorem exists_branched_double_cover {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] [CompactSpace X] {g n : ℕ} (hgn : g ≠ 0 ∨ n ≠ 0)
    (hX : HasGenus X g) (P : Finset X) (hP : P.card = 2 * n) :
    ∃ (X' : ClosedRS.{u}) (pr : X'.carrier → X), HasGenus X'.carrier (2 * g + n - 1) ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr ∧ Function.Surjective pr ∧
      (∀ x ∉ P, (pr ⁻¹' {x}).ncard = 2) ∧ (∀ x ∈ P, (pr ⁻¹' {x}).ncard = 1) ∧
      ∃ h : X'.carrier ≃ₜ X'.carrier, IsBiholomorphic h ∧ (∀ y, h (h y) = y) ∧ (∀ y, pr (h y) = pr y) ∧
        ∀ y, h y = y ↔ pr y ∈ P := by
  exact s82bc_exists_branched_double_cover hgn hX P hP

end RelocatedS32

end LiZhongQC
