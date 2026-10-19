import LiZhongQC.Lemmas.S32wDTQ

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u v w

section Biholo

variable {Y : Type u} {Z : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y] [TopologicalSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Y] [IsManifold 𝓘(ℂ) ω Z]

/-- The coordinate expression of a holomorphic map is analytic at the chart centre. -/
theorem s32w_dt_coord_analytic {H : Y → Z} (hH : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H) (p : Y) {a : Z}
    (ha : H p = a) :
    AnalyticAt ℂ (fun w => chartAt ℂ a (H ((chartAt ℂ p).symm w))) (chartAt ℂ p p) := by
  subst ha
  have hl : (chartAt ℂ p).symm (chartAt ℂ p p) = p := (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  set W : Set ℂ := (chartAt ℂ p).target ∩ (chartAt ℂ p).symm ⁻¹' (H ⁻¹' (chartAt ℂ (H p)).source) with hW
  have hWo : IsOpen W :=
    (chartAt ℂ p).isOpen_inter_preimage_symm (hH.continuous.isOpen_preimage _ (chartAt ℂ (H p)).open_source)
  have hcW : chartAt ℂ p p ∈ W :=
    ⟨(chartAt ℂ p).map_source (mem_chart_source ℂ p), by
      show H ((chartAt ℂ p).symm (chartAt ℂ p p)) ∈ (chartAt ℂ (H p)).source
      rw [hl]; exact mem_chart_source ℂ _⟩
  have hd : DifferentiableOn ℂ (fun w => chartAt ℂ (H p) (H ((chartAt ℂ p).symm w))) W := by
    intro w hw
    exact (s31qr_coordinate_differentiable p (H p) hw.1 hw.2 (hH _)).differentiableWithinAt
  exact hd.analyticAt (hWo.mem_nhds hcW)

/-- The inverse coordinate expression of a biholomorphic map has nonzero derivative at the chart centre. -/
theorem s32w_dt_biholo_deriv_ne {c : Y ≃ₜ Z} (hc : IsBiholomorphic c) (y : Y) :
    deriv (fun v => chartAt ℂ y (c.symm ((chartAt ℂ (c y)).symm v))) (chartAt ℂ (c y) (c y)) ≠ 0 := by
  have h := s32w_dt_chain (H := (c : Y → Z)) (K := (c.symm : Z → Y)) (p := y) (hc.1 y)
    (hc.homeomorph_symm.1 (c y))
  simp only [Homeomorph.symm_apply_apply] at h
  have hid : (fun w => chartAt ℂ y ((chartAt ℂ y).symm w)) =ᶠ[𝓝 (chartAt ℂ y y)] id := by
    filter_upwards [(chartAt ℂ y).open_target.mem_nhds ((chartAt ℂ y).map_source (mem_chart_source ℂ y))]
      with w hw
    exact (chartAt ℂ y).right_inv hw
  rw [hid.deriv_eq, deriv_id] at h
  exact left_ne_zero_of_mul_eq_one h.symm

end Biholo

section TeichComp

variable {S₀ : Type u} {Y : Type v} {Z : Type w} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [TopologicalSpace Z] [ChartedSpace ℂ Z]
  [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω Y] [IsManifold 𝓘(ℂ) ω Z]

/-- The facts about the coordinate expression `τ_y = φ_y ∘ c⁻¹ ∘ φ_{c y}⁻¹` of a biholomorphic map. -/
theorem s32w_dt_tilde_facts {c : Y ≃ₜ Z} (hc : IsBiholomorphic c) (y : Y) :
    AnalyticAt ℂ (fun w => chartAt ℂ y (c.symm ((chartAt ℂ (c y)).symm w))) (chartAt ℂ (c y) (c y)) ∧
    (fun w => chartAt ℂ y (c.symm ((chartAt ℂ (c y)).symm w))) (chartAt ℂ (c y) (c y)) = chartAt ℂ y y ∧
    deriv (fun w => chartAt ℂ y (c.symm ((chartAt ℂ (c y)).symm w))) (chartAt ℂ (c y) (c y)) ≠ 0 := by
  refine ⟨s32w_dt_coord_analytic hc.homeomorph_symm.1 (c y) (c.symm_apply_apply y), ?_,
    s32w_dt_biholo_deriv_ne hc y⟩
  show chartAt ℂ y (c.symm ((chartAt ℂ (c y)).symm (chartAt ℂ (c y) (c y)))) = _
  rw [(chartAt ℂ (c y)).left_inv (mem_chart_source ℂ _), c.symm_apply_apply]

/-- The local formula of the transported differential. -/
theorem s32w_dt_transport_formula {c : Y ≃ₜ Z} (hc : IsBiholomorphic c) {q' : Y → ℂ → ℂ}
    (hq : IsDiffFamily 2 0 q') (y : Y) :
    ∀ᶠ z in 𝓝 (chartAt ℂ (c y) (c y)),
      s31qr_transportOn univ c.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ) q' (c y) z =
        q' y (chartAt ℂ y (c.symm ((chartAt ℂ (c y)).symm z))) *
          deriv (fun w => chartAt ℂ y (c.symm ((chartAt ℂ (c y)).symm w))) z ^ 2 := by
  have hcs : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c.symm : Z → Y) := hc.homeomorph_symm.1
  have hz0 : chartAt ℂ (c y) (c y) ∈ (chartAt ℂ (c y)).target :=
    (chartAt ℂ (c y)).map_source (mem_chart_source ℂ _)
  have hcont : ContinuousAt (fun z => c.symm ((chartAt ℂ (c y)).symm z)) (chartAt ℂ (c y) (c y)) :=
    c.symm.continuous.continuousAt.comp ((chartAt ℂ (c y)).continuousAt_symm hz0)
  have hval : c.symm ((chartAt ℂ (c y)).symm (chartAt ℂ (c y) (c y))) = y := by
    rw [(chartAt ℂ (c y)).left_inv (mem_chart_source ℂ _), c.symm_apply_apply]
  have hsrc : ∀ᶠ z in 𝓝 (chartAt ℂ (c y) (c y)),
      c.symm ((chartAt ℂ (c y)).symm z) ∈ (chartAt ℂ y).source := by
    apply hcont.preimage_mem_nhds
    show (chartAt ℂ y).source ∈ 𝓝 (c.symm ((chartAt ℂ (c y)).symm (chartAt ℂ (c y) (c y))))
    rw [hval]
    exact (chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y)
  filter_upwards [(chartAt ℂ (c y)).open_target.mem_nhds hz0, hsrc] with z hz hz2
  exact s31qr_transport_local hq (c y) y hz (mem_univ _) hz2 (hcs _)

/-- **(D4)** A biholomorphic map composed with a Teichmüller map is a Teichmüller map. -/
theorem s32w_dt_teich_comp (ι : S₀ ≃ₜ Y) (c : Y ≃ₜ Z) (hc : IsBiholomorphic c) {Q : S₀ → ℂ → ℂ}
    {q' : Y → ℂ → ℂ} {k : ℝ} (hι : IsTeichmullerMap ι Q q' k) :
    ∃ Q' : Z → ℂ → ℂ, IsTeichmullerMap (ι.trans c) Q Q' k := by
  classical
  have hcs : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c.symm : Z → Y) := hc.homeomorph_symm.1
  have hq' : IsDiffFamily 2 0 q' ∧ ∀ x, DifferentiableOn ℂ (q' x) (chartAt ℂ x).target := hι.terminal
  have hqfam := hq'.1
  have hqdiff := hq'.2
  obtain ⟨Q', hQ'⟩ : ∃ Q' : Z → ℂ → ℂ,
      Q' = s31qr_transportOn univ c.symm (LinearMap.id : ℂ →ₗ[ℝ] ℂ) q' := ⟨_, rfl⟩
  have hform : ∀ y, ∀ᶠ z in 𝓝 (chartAt ℂ (c y) (c y)),
      Q' (c y) z = q' y (chartAt ℂ y (c.symm ((chartAt ℂ (c y)).symm z))) *
        deriv (fun w => chartAt ℂ y (c.symm ((chartAt ℂ (c y)).symm w))) z ^ 2 := by
    intro y
    rw [hQ']
    exact s32w_dt_transport_formula hc hqfam y
  refine ⟨Q', ?_⟩
  have hqc : IsQCRS (ι.trans c) := s28q_isQCRS_trans hι.qc ⟨1, (isKQCRS_one_iff c).2 hc⟩
  have hterm : IsHolQuadDiff Q' := by
    rw [hQ']
    refine ⟨?_, fun x => ?_⟩
    · exact s31qr_holomorphic_transport_family univ c.symm (fun p _ => hcs p) q'
    have h := s31qr_transport_holomorphic (U := univ) isOpen_univ (V := univ) isOpen_univ (H := c.symm)
      (fun p _ => hcs p) (mapsTo_univ _ _) hqfam
      (fun a => (hqdiff a).mono (fun z hz => hz.1)) x
    simpa only [preimage_univ, inter_univ] using h
  refine ⟨hqc, hι.initial, hι.initial_ne, hterm, hι.k_nonneg, hι.k_lt_one, ?_, ?_⟩
  · -- regular points
    intro p hp
    obtain ⟨hreg', ζ, ζ₁, hζ, hζ₁, hrel⟩ := hι.regular p hp
    obtain ⟨hz₁an, hz₁0, hz₁d, hz₁nat⟩ := hζ₁
    obtain ⟨hτan, hτc, hτd⟩ := s32w_dt_tilde_facts hc (ι p)
    set τ : ℂ → ℂ := fun w => chartAt ℂ (ι p) (c.symm ((chartAt ℂ (c (ι p))).symm w)) with hτ
    set c' : ℂ := chartAt ℂ (c (ι p)) (c (ι p)) with hc'
    have hτt : Tendsto τ (𝓝 c') (𝓝 (chartAt ℂ (ι p) (ι p))) := by
      have := hτan.continuousAt.tendsto
      rwa [hτc] at this
    have hd1 : DifferentiableAt ℂ ζ₁ (τ c') := by rw [hτc]; exact hz₁an.differentiableAt
    have hd2 : DifferentiableAt ℂ τ c' := hτan.differentiableAt
    have hcomp : AnalyticAt ℂ (fun w => ζ₁ (τ w)) c' := hz₁an.comp_of_eq hτan hτc
    refine ⟨?_, ζ, fun w => ζ₁ (τ w), hζ, ⟨hcomp, ?_, ?_, ?_⟩, ?_⟩
    · -- regularity
      show Q' (c (ι p)) (chartAt ℂ (c (ι p)) (c (ι p))) ≠ 0
      have h1 := (hform (ι p)).self_of_nhds
      rw [h1]
      have h2 : q' (ι p) (τ c') ≠ 0 := by rw [hτc]; exact hreg'
      exact mul_ne_zero h2 (pow_ne_zero 2 hτd)
    · show ζ₁ (τ c') = 0
      rw [hτc]; exact hz₁0
    · show deriv (fun w => ζ₁ (τ w)) c' ≠ 0
      have : deriv (fun w => ζ₁ (τ w)) c' = deriv ζ₁ (τ c') * deriv τ c' := deriv_comp c' hd1 hd2
      rw [this, hτc]
      exact mul_ne_zero hz₁d hτd
    · have hev1 : ∀ᶠ z in 𝓝 c', DifferentiableAt ℂ τ z :=
        hτan.eventually_analyticAt.mono fun z hz => hz.differentiableAt
      have hev2 : ∀ᶠ z in 𝓝 c', DifferentiableAt ℂ ζ₁ (τ z) :=
        hτt.eventually (hz₁an.eventually_analyticAt.mono fun z hz => hz.differentiableAt)
      have hev3 : ∀ᶠ z in 𝓝 c', deriv ζ₁ (τ z) ^ 2 = q' (ι p) (τ z) := hτt.eventually hz₁nat
      filter_upwards [hform (ι p), hev1, hev2, hev3] with z h1 h2 h3 h4
      have h5 : deriv (fun w => ζ₁ (τ w)) z = deriv ζ₁ (τ z) * deriv τ z := deriv_comp z h3 h2
      show deriv (fun w => ζ₁ (τ w)) z ^ 2 = Q' (c (ι p)) z
      rw [h1, h5, mul_pow, h4]
    · -- the stretch relation
      have hc0 : ContinuousAt (fun z => c (ι ((chartAt ℂ p).symm z))) (chartAt ℂ p p) := by
        have hz : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
        exact (c.continuous.comp ι.continuous).continuousAt.comp ((chartAt ℂ p).continuousAt_symm hz)
      have hsrc : ∀ᶠ z in 𝓝 (chartAt ℂ p p),
          c (ι ((chartAt ℂ p).symm z)) ∈ (chartAt ℂ (c (ι p))).source := by
        apply hc0.preimage_mem_nhds
        show (chartAt ℂ (c (ι p))).source ∈ 𝓝 (c (ι ((chartAt ℂ p).symm (chartAt ℂ p p))))
        rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
        exact (chartAt ℂ _).open_source.mem_nhds (mem_chart_source ℂ _)
      filter_upwards [hrel, hsrc] with z h1 h2
      show ζ₁ (τ (localMapExpr (ι.trans c) p z)) = _
      have h3 : τ (localMapExpr (ι.trans c) p z) = localMapExpr ι p z := by
        show chartAt ℂ (ι p) (c.symm ((chartAt ℂ (c (ι p))).symm
          (chartAt ℂ (c (ι p)) (c (ι ((chartAt ℂ p).symm z)))))) = _
        rw [(chartAt ℂ (c (ι p))).left_inv h2, c.symm_apply_apply]
        try rfl
      rw [h3]
      exact h1
  · -- zeros
    intro p n hp
    have h0 := hι.zero p n hp
    obtain ⟨hτan, hτc, hτd⟩ := s32w_dt_tilde_facts hc (ι p)
    set τ : ℂ → ℂ := fun w => chartAt ℂ (ι p) (c.symm ((chartAt ℂ (c (ι p))).symm w)) with hτ
    set c' : ℂ := chartAt ℂ (c (ι p)) (c (ι p)) with hc'
    unfold IsZeroOfOrder at h0 ⊢
    change meromorphicOrderAt (Q' (c (ι p))) c' = _
    have hQeq : Q' (c (ι p)) =ᶠ[𝓝[≠] c'] (fun z => deriv τ z ^ 2) * ((q' (ι p)) ∘ τ) := by
      refine ((hform (ι p)).filter_mono nhdsWithin_le_nhds).mono fun z hz => ?_
      rw [hz]
      simp only [Pi.mul_apply, Function.comp_apply]
      ring
    have hga : AnalyticAt ℂ (fun z => deriv τ z ^ 2) c' := (hτan.deriv).pow 2
    rw [meromorphicOrderAt_congr hQeq, meromorphicOrderAt_mul_of_ne_zero hga (pow_ne_zero 2 hτd),
      meromorphicOrderAt_comp_of_deriv_ne_zero hτan hτd, hτc]
    exact h0

end TeichComp

end LiZhongQC
