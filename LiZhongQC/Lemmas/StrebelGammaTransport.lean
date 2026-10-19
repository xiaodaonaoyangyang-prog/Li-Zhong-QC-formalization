import LiZhongQC.Lemmas.HyperbolicSurfaceArea
import LiZhongQC.Lemmas.UniformizedUniqueness

/-!
# Transport of the Γ-model to a surface `S = ℍ/Γ` (R83, `StrebelGammaTransport`)

Helpers for the Γ-version of the Reich–Strebel inequality (`strebel_hamilton_sufficient`):
`str_surfaceIntegral_eq` (T3: `surfaceIntegral` of a chart-invariant integrand against `|q|` is the `F`-integral
of its lift against `|φ|`), `str_descend` (T1: a q.c. self-map of `ℍ` commuting with `Γ` descends to a q.c.
homeomorphism of `S` homotopic to the identity), `str_lambda` (T4: the stretching function is the lifted
one).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold UpperHalfPlane

noncomputable section

namespace LiZhongQC

universe u



/-- `ℍ.indicator |φ|` is measurable for `φ` holomorphic on `ℍ`. -/
theorem str_meas {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ upperHalf) :
    Measurable (upperHalf.indicator (fun z => ENNReal.ofReal ‖φ z‖)) := by
  classical
  have h : upperHalf.indicator (fun z => ENNReal.ofReal ‖φ z‖) =
      upperHalf.piecewise (fun z => ENNReal.ofReal ‖φ z‖) (fun _ => 0) := by
    ext z
    by_cases hz : z ∈ upperHalf <;> simp [hz, Set.indicator, Set.piecewise]
  rw [h]
  exact ContinuousOn.measurable_piecewise
    (ENNReal.continuous_ofReal.comp_continuousOn hφ.continuousOn.norm) continuousOn_const
    isOpen_upperHalf.measurableSet

/-- A chart partition subordinate to open sets `V p ∋ p` (`V p` inside the chart source at `p`) on a
Lindelöf charted space, with Borel pieces. -/
theorem str_exists_partition {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [MeasurableSpace S]
    [BorelSpace S] [Nonempty S] (hL : IsLindelof (univ : Set S)) (V : S → Set S)
    (hVo : ∀ p, IsOpen (V p)) (hVp : ∀ p, p ∈ V p) (hVs : ∀ p, V p ⊆ (chartAt ℂ p).source) :
    ∃ (x : ℕ → S) (P : ℕ → Set S), IsChartPartition S x P ∧ (∀ i, P i ⊆ V (x i)) ∧
      ∀ i, MeasurableSet (P i) := by
  obtain ⟨t, htc, htU⟩ := hL.elim_countable_subcover V hVo
    (fun p _ => mem_iUnion.2 ⟨p, hVp p⟩)
  have htne : t.Nonempty := by
    obtain ⟨p⟩ := ‹Nonempty S›
    obtain ⟨q, hq, -⟩ := mem_iUnion₂.1 (htU (mem_univ p))
    exact ⟨q, hq⟩
  obtain ⟨x, hx⟩ := htc.exists_eq_range htne
  set W : ℕ → Set S := fun i => V (x i) with hW
  have hWo : ∀ i, IsOpen (W i) := fun i => hVo _
  have hWs : ∀ i, W i ⊆ (chartAt ℂ (x i)).source := fun i => hVs _
  refine ⟨x, disjointed W, ⟨fun i => ⟨?_, ?_⟩, disjoint_disjointed W, ?_⟩, fun i => ?_, fun i => ?_⟩
  · exact (disjointed_subset W i).trans (hWs i)
  · rw [disjointed_eq_inter_compl]
    exact s26_measurableSet_chart_image (x i) W hWo i (hWs i)
  · rw [iUnion_disjointed, eq_univ_iff_forall]
    intro p
    obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.1 (htU (mem_univ p))
    rw [hx] at hq
    obtain ⟨i, rfl⟩ := hq
    exact mem_iUnion.2 ⟨i, hpq⟩
  · exact disjointed_subset W i
  · rw [disjointed_eq_inter_compl]
    exact (hWo i).measurableSet.inter
      (MeasurableSet.biInter (to_countable _) fun j _ => (hWo j).measurableSet.compl)

/-- Change of variables for a holomorphic injective `H` on a measurable set `E`. -/
theorem str_cov_local {E : Set ℂ} {H : ℂ → ℂ} (hEm : MeasurableSet E)
    (hd : ∀ z ∈ E, HasDerivAt H (deriv H z) z) (hinj : InjOn H E) (G : ℂ → ℝ≥0∞) :
    ∫⁻ w in H '' E, G w = ∫⁻ z in E, ENNReal.ofReal (‖deriv H z‖ ^ 2) * G (H z) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hEm
    (fun z hz => ((hd z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hinj G]
  refine setLIntegral_congr_fun hEm fun z _ => ?_
  simp only [det_restrictScalars_toSpanSingleton]
  rw [abs_of_nonneg (sq_nonneg _)]


section T3

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [IsManifold 𝓘(ℂ) ω S]
  [MeasurableSpace S] [BorelSpace S]

/-- The invariance of `|φ|` under the weight `|γ'|²`, for a holomorphic automorphic `φ`. -/
theorem str_inv' {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {φ : ℂ → ℂ}
    (hφd : DifferentiableOn ℂ φ upperHalf)
    (hφΓ : ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
      φ ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = φ z)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) {z : ℂ} (hz : z ∈ upperHalf) :
    (upperHalf.indicator (fun z => ENNReal.ofReal ‖φ z‖)) (h36p_m γ z) *
        ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4) =
      (upperHalf.indicator (fun z => ENNReal.ofReal ‖φ z‖)) z := by
  have _ := hφd
  have hdet := b33_d_det γ
  have hden := k24_d_den_ne_zero hdet (ne_of_gt (show 0 < z.im from hz))
  have hA := hφΓ γ hγ z hz
  have hφm : φ (h36p_m γ z) = φ z * ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 := by
    rw [← hA, div_mul_cancel₀ _ (pow_ne_zero _ hden)]
    rfl
  rw [indicator_of_mem (h36p_m_mem γ hz), indicator_of_mem hz, hφm, norm_mul, norm_pow,
    ENNReal.ofReal_mul (norm_nonneg _), mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hq : ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ≠ 0 := norm_ne_zero_iff.2 hden
  rw [show ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ^ 4 * ‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4 = 1 by
    rw [← mul_pow, mul_inv_cancel₀ hq, one_pow], ENNReal.ofReal_one, mul_one]

/-- **T3.**  For a chart-invariant integrand `U ∘ (chart⁻¹)` the surface integral against `|q|` is the
`F`-integral of `U ∘ p̂ · |φ|`, where `φ` is the lift of `q`. -/
theorem str_surfaceIntegral_eq
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) (hΓ : IsFuchsian Γ) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) {φ : ℂ → ℂ} (hφd : DifferentiableOn ℂ φ upperHalf)
    (hφΓ : ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
      φ ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = φ z)
    (hqφ : ∀ τ ∈ upperHalf, utm_liftQD q p τ = φ τ) {U : S → ℝ≥0∞} (hU : Measurable U) :
    surfaceIntegral q (fun y z => U ((chartAt ℂ y).symm z)) =
      ∫⁻ z in F, U (s22gm_projectionExtension p z) * ENNReal.ofReal ‖φ z‖ := by
  classical
  have hF' := hF
  obtain ⟨hFH, hFm, -, -, -⟩ := hF
  have hΔ : MeasurableSet upperHalf := isOpen_upperHalf.measurableSet
  have hpc : Continuous p := hp.1.continuous
  have hpmeas := s22gm_projectionExtension_measurable hpc
  have : Nonempty S := ⟨p UpperHalfPlane.I⟩
  have hsurj : Function.Surjective p := hp.2.2.1
  choose τ hτ using hsurj
  have hdisc : ∀ s : S, ∃ r : ℝ, 0 < r ∧ r < (τ s).im ∧
      InjOn p (UpperHalfPlane.coe ⁻¹' ball ((τ s : UpperHalfPlane) : ℂ) r) := fun s => utm_x2_disc hp (τ s)
  choose r hr0 hrim hrinj using hdisc
  set B : S → Set UpperHalfPlane := fun s =>
    UpperHalfPlane.coe ⁻¹' ball ((τ s : UpperHalfPlane) : ℂ) (r s) with hBdef
  set V : S → Set S := fun s => (chartAt ℂ s).source ∩ p '' B s with hVdef
  have hBo : ∀ s, IsOpen (B s) := fun s => isOpen_ball.preimage UpperHalfPlane.continuous_coe
  have hVo : ∀ s, IsOpen (V s) := fun s =>
    (chartAt ℂ s).open_source.inter (hp.1.isOpenMap _ (hBo s))
  have hVp : ∀ s, s ∈ V s := fun s =>
    ⟨mem_chart_source ℂ s, ⟨τ s, mem_preimage.2 (mem_ball_self (hr0 s)), hτ s⟩⟩
  have hL : IsLindelof (univ : Set S) := by
    have h1 := (isLindelof_univ (X := UpperHalfPlane)).image hpc
    rwa [image_univ, Function.Surjective.range_eq (fun s => ⟨τ s, hτ s⟩)] at h1
  obtain ⟨x, P, hP, hPV, hPm⟩ := str_exists_partition hL V hVo hVp (fun s => inter_subset_left)
  -- the weight on `ℍ`
  set w : ℂ → ℝ≥0∞ := fun z => U (s22gm_projectionExtension p z) *
    upperHalf.indicator (fun z => ENNReal.ofReal ‖φ z‖) z with hw
  have hwm : Measurable w :=
    (hU.comp hpmeas).mul (str_meas hφd)
  have hcov : ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
      w (h36p_m γ z) * ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4) = w z := by
    intro γ hγ z hz
    simp only [hw]
    rw [s22gm_projectionExtension_invariant hp hγ hz, mul_assoc, str_inv' hφd hφΓ hγ hz]
  have hFw : ∀ z ∈ F, w z = U (s22gm_projectionExtension p z) * ENNReal.ofReal ‖φ z‖ := by
    intro z hz
    simp only [hw]
    rw [indicator_of_mem (hFH hz)]
  rw [s26v_surfaceIntegral_eq_tsum hq U hP]
  have hterm : ∀ i, ∫⁻ z in chartAt ℂ (x i) '' P i,
      U ((chartAt ℂ (x i)).symm z) * ENNReal.ofReal ‖q (x i) z‖ =
      ∫⁻ z in F, (s22gm_projectionExtension p ⁻¹' P i).indicator w z := by
    intro i
    set s := x i with hs
    set Bc : Set ℂ := ball ((τ s : UpperHalfPlane) : ℂ) (r s) with hBc
    have hBcH : Bc ⊆ upperHalf := by
      intro z hz
      have h1 := Complex.abs_im_le_norm (z - ((τ s : UpperHalfPlane) : ℂ))
      rw [Complex.sub_im] at h1
      have hd : ‖z - ((τ s : UpperHalfPlane) : ℂ)‖ < r s := by
        have hz' : z ∈ ball ((τ s : UpperHalfPlane) : ℂ) (r s) := hz
        rw [mem_ball, dist_eq_norm] at hz'
        exact hz'
      have h2 := (abs_lt.1 (lt_of_le_of_lt h1 hd)).1
      have h3 : 0 < ((τ s : UpperHalfPlane) : ℂ).im := (τ s).im_pos
      have h4 := hrim s
      show 0 < z.im
      have : ((τ s : UpperHalfPlane) : ℂ).im = (τ s).im := rfl
      linarith
    have hinjB : InjOn (s22gm_projectionExtension p) Bc := by
      intro z hz w hw hzw
      have hz' := hBcH hz
      have hw' := hBcH hw
      have e : p ⟨z, hz'⟩ = p ⟨w, hw'⟩ := by
        have := hzw
        simp only [s22gm_projectionExtension, UpperHalfPlane.ofComplex_apply_of_im_pos hz',
          UpperHalfPlane.ofComplex_apply_of_im_pos hw'] at this
        exact this
      have := hrinj s (show (⟨z, hz'⟩ : UpperHalfPlane) ∈ UpperHalfPlane.coe ⁻¹'
        ball ((τ s : UpperHalfPlane) : ℂ) (r s) from hz) (show (⟨w, hw'⟩ : UpperHalfPlane) ∈
        UpperHalfPlane.coe ⁻¹' ball ((τ s : UpperHalfPlane) : ℂ) (r s) from hw) e
      exact congrArg UpperHalfPlane.coe this
    set L : Set ℂ := Bc ∩ s22gm_projectionExtension p ⁻¹' P i with hLdef
    have hLm : MeasurableSet L := measurableSet_ball.inter (hpmeas (hPm i))
    have hLH : L ⊆ upperHalf := inter_subset_left.trans hBcH
    have hPs : P i ⊆ (chartAt ℂ s).source := (hP.1 i).1
    have hPimg : s22gm_projectionExtension p '' L = P i := by
      ext y
      constructor
      · rintro ⟨z, ⟨_, hz⟩, rfl⟩
        exact hz
      · intro hy
        obtain ⟨β, hβ, rfl⟩ := (hPV i hy).2
        refine ⟨(β : ℂ), ⟨hβ, ?_⟩, s22gm_projectionExtension_coe p β⟩
        show s22gm_projectionExtension p (β : ℂ) ∈ P i
        rw [s22gm_projectionExtension_coe]
        exact hy
    set H : ℂ → ℂ := fun v => chartAt ℂ s (utm_pext p v) with hH
    have hphat : ∀ z ∈ upperHalf, utm_pext p z = s22gm_projectionExtension p z := fun z hz =>
      utm_a_pext_eq p hz
    have hHz : ∀ z ∈ L, H z = chartAt ℂ s (s22gm_projectionExtension p z) := fun z hz => by
      simp only [hH]
      rw [hphat z (hLH hz)]
    have hHinj : InjOn H L := by
      intro z hz w hw hzw
      rw [hHz z hz, hHz w hw] at hzw
      have h1 := (chartAt ℂ s).injOn (hPs hz.2) (hPs hw.2) hzw
      exact hinjB hz.1 hw.1 h1
    have hlaw : ∀ z ∈ L, HasDerivAt H (deriv H z) z ∧
        ‖φ z‖ = ‖q s (H z)‖ * ‖deriv H z‖ ^ 2 := by
      intro z hz
      have hzH := hLH hz
      have hx : p ⟨z, hzH⟩ ∈ (chartAt ℂ s).source := by
        have := hPs hz.2
        simpa [s22gm_projectionExtension, UpperHalfPlane.ofComplex_apply_of_im_pos hzH] using this
      obtain ⟨U0, hU0o, hzU0, hU0H, -, hU0⟩ := utm_liftQD_local hq hp ⟨z, hzH⟩ s hx
      obtain ⟨-, hd, -, hlaw⟩ := hU0 z hzU0
      refine ⟨hd, ?_⟩
      have h1 := hqφ z hzH
      rw [hlaw] at h1
      rw [← h1, norm_mul, norm_pow]
    have himg : chartAt ℂ s '' P i = H '' L := by
      ext y
      constructor
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨z, hz, rfl⟩ : a ∈ s22gm_projectionExtension p '' L := by rw [hPimg]; exact ha
        exact ⟨z, hz, hHz z hz⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨_, hz.2, (hHz z hz).symm⟩
    calc ∫⁻ z in chartAt ℂ s '' P i, U ((chartAt ℂ s).symm z) * ENNReal.ofReal ‖q s z‖
        = ∫⁻ z in H '' L, U ((chartAt ℂ s).symm z) * ENNReal.ofReal ‖q s z‖ := by rw [himg]
      _ = ∫⁻ z in L, ENNReal.ofReal (‖deriv H z‖ ^ 2) *
            (U ((chartAt ℂ s).symm (H z)) * ENNReal.ofReal ‖q s (H z)‖) :=
          str_cov_local hLm (fun z hz => (hlaw z hz).1) hHinj _
      _ = ∫⁻ z in L, w z := by
          refine setLIntegral_congr_fun hLm fun z hz => ?_
          have hzH := hLH hz
          rw [hHz z hz, (chartAt ℂ s).left_inv (hPs hz.2)]
          simp only [hw]
          rw [indicator_of_mem hzH, (hlaw z hz).2, ENNReal.ofReal_mul (norm_nonneg _), ← hHz z hz]
          ring
      _ = ∫⁻ z in F, (s22gm_projectionExtension p ⁻¹' (s22gm_projectionExtension p '' L)).indicator w z :=
          (s22gm_lintegral_partial_sheet hp hΓ hF' hLm hLH (hinjB.mono inter_subset_left) hwm hcov).symm
      _ = ∫⁻ z in F, (s22gm_projectionExtension p ⁻¹' P i).indicator w z := by rw [hPimg]
  rw [tsum_congr hterm, ← lintegral_tsum (fun i => (hwm.indicator (hpmeas (hPm i))).aemeasurable)]
  refine setLIntegral_congr_fun hFm fun z hz => ?_
  obtain ⟨i₀, hi₀⟩ := mem_iUnion.1 (hP.2.2.symm ▸ mem_univ (s22gm_projectionExtension p z) :
    s22gm_projectionExtension p z ∈ ⋃ i, P i)
  rw [tsum_eq_single i₀ (fun j hj => indicator_of_notMem (fun h => ?_) _)]
  · rw [indicator_of_mem (show z ∈ s22gm_projectionExtension p ⁻¹' P i₀ from hi₀), hFw z hz]
  · exact Set.disjoint_left.1 (hP.2.1 hj) h hi₀

end T3



/-- A `K`-q.c. self-map of `ℍ` onto `ℍ` is a homeomorphism of `ℍ`. -/
theorem str_homeoH {g : ℂ → ℂ} {K : ℝ} (hgK : IsKQC g upperHalf K) (hgimg : g '' upperHalf = upperHalf) :
    ∃ F : UpperHalfPlane ≃ₜ UpperHalfPlane, ∀ τ : UpperHalfPlane, (F τ : ℂ) = g τ := by
  obtain ⟨hc, hi, himg, hic⟩ := hgK.2.2.1
  have hmem : ∀ τ : UpperHalfPlane, g (τ : ℂ) ∈ upperHalf := fun τ =>
    hgimg ▸ mem_image_of_mem g τ.2
  have hex : ∀ σ : UpperHalfPlane, ∃ a ∈ upperHalf, g a = (σ : ℂ) := fun σ => by
    have : (σ : ℂ) ∈ g '' upperHalf := by rw [hgimg]; exact σ.2
    exact this
  have hinvmem : ∀ σ : UpperHalfPlane, Function.invFunOn g upperHalf (σ : ℂ) ∈ upperHalf :=
    fun σ => Function.invFunOn_mem (hex σ)
  refine ⟨⟨⟨fun τ => ⟨g τ, hmem τ⟩, fun σ => ⟨Function.invFunOn g upperHalf σ, hinvmem σ⟩, ?_, ?_⟩,
    ?_, ?_⟩, fun τ => rfl⟩
  · intro τ
    apply UpperHalfPlane.ext
    exact hi.leftInvOn_invFunOn τ.2
  · intro σ
    apply UpperHalfPlane.ext
    exact Function.invFunOn_eq (hex σ)
  · exact UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff.2
      (hc.comp_continuous UpperHalfPlane.continuous_coe (fun τ => τ.2))
  · exact UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff.2
      (hic.comp_continuous UpperHalfPlane.continuous_coe (fun σ => by rw [hgimg]; exact σ.2))

/-- **T1.**  A `K`-q.c. self-map `g` of `ℍ` commuting with `Γ` descends to a `K`-q.c. homeomorphism `h` of
`S = ℍ/Γ` homotopic to the identity, with `h ∘ p̂ = p̂ ∘ g` on `ℍ`. -/
theorem str_descend {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] [MeasurableSpace S] [BorelSpace S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) {g : ℂ → ℂ} {K : ℝ} (hgK : IsKQC g upperHalf K)
    (hgimg : g '' upperHalf = upperHalf)
    (hcomm : ∀ γ ∈ Γ, ∀ z ∈ upperHalf, g (h36p_m γ z) = h36p_m γ (g z)) :
    ∃ h : S ≃ₜ S, IsKQCRS h K ∧ ContinuousMap.Homotopic (h : C(S, S)) (ContinuousMap.id S) ∧
      ∀ z ∈ upperHalf, h (s22gm_projectionExtension p z) = s22gm_projectionExtension p (g z) := by
  obtain ⟨F, hF⟩ := str_homeoH hgK hgimg
  have hFγ : ∀ γ ∈ Γ, ∀ τ : UpperHalfPlane, F (γ • τ) = γ • F τ := by
    intro γ hγ τ
    apply UpperHalfPlane.ext
    show ((F (γ • τ) : UpperHalfPlane) : ℂ) = ((γ • F τ : UpperHalfPlane) : ℂ)
    rw [hF, ← h36p_m_coe γ τ, hcomm γ hγ _ τ.2, ← hF τ, h36p_m_coe γ (F τ)]
  obtain ⟨h, hh⟩ := s24q_descend hp hp F (fun γ hγ => ⟨γ, hγ, hFγ γ hγ⟩)
    (fun δ hδ => ⟨δ, hδ, hFγ δ hδ⟩)
  have hKlift : IsKQC (liftToC F) upperHalf K := by
    refine ad_isKQC_congr hgK (fun z hz => ?_)
    have := h23l_liftToC_coe F ⟨z, hz⟩
    simpa [hF] using this
  refine ⟨h, s27v_isKQCRS_of_lift hp hp hh hKlift, ?_, ?_⟩
  · have := (thm23_1_homotopy_iff hp hp h (Homeomorph.refl S) (F := F) (G := Homeomorph.refl _) hh
      (fun τ => rfl)).2 ⟨1, Γ.one_mem, fun γ hγ τ => by simp [hFγ γ hγ]⟩
    exact this
  · intro z hz
    set τ : UpperHalfPlane := ⟨z, hz⟩ with hτ
    have e1 := s22gm_projectionExtension_coe p τ
    have e2 := s22gm_projectionExtension_coe p (F τ)
    rw [hF τ] at e2
    show h (s22gm_projectionExtension p (τ : ℂ)) = s22gm_projectionExtension p (g (τ : ℂ))
    rw [e1, e2, hh τ]



section T4

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [IsManifold 𝓘(ℂ) ω S]
  [MeasurableSpace S] [BorelSpace S]

/-- A local conformal chart `H = φ_x ∘ p̂` around `τ ∈ ℍ`, with a holomorphic local inverse. -/
theorem str_localchart {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (τ : UpperHalfPlane) (x : S)
    (hx : p τ ∈ (chartAt ℂ x).source) :
    ∃ k : ℂ → ℂ, DifferentiableAt ℂ (fun v => chartAt ℂ x (utm_pext p v)) (τ : ℂ) ∧
      DifferentiableAt ℂ k (chartAt ℂ x (utm_pext p (τ : ℂ))) ∧
      (∀ᶠ w in 𝓝 (τ : ℂ), k (chartAt ℂ x (utm_pext p w)) = w) ∧
      (∀ᶠ u in 𝓝 (chartAt ℂ x (utm_pext p (τ : ℂ))), chartAt ℂ x (utm_pext p (k u)) = u) ∧
      deriv (fun v => chartAt ℂ x (utm_pext p v)) (τ : ℂ) ≠ 0 ∧
      utm_liftQD q p (τ : ℂ) = q x (chartAt ℂ x (utm_pext p (τ : ℂ))) *
        deriv (fun v => chartAt ℂ x (utm_pext p v)) (τ : ℂ) ^ 2 := by
  obtain ⟨U, hUo, hτU, hUH, hinj, hU⟩ := utm_liftQD_local hq hp τ x hx
  set H : ℂ → ℂ := fun v => chartAt ℂ x (utm_pext p v) with hH
  have hconf : IsConformalOnto H U (H '' U) :=
    ⟨fun w hw => (hU w hw).2.1.differentiableAt.differentiableWithinAt, hinj, rfl⟩
  refine ⟨Function.invFunOn H U, (hU _ hτU).2.1.differentiableAt,
    hconf.differentiableAt_invFunOn hUo hτU, ?_, ?_, (hU _ hτU).2.2.1, (hU _ hτU).2.2.2⟩
  · filter_upwards [hUo.mem_nhds hτU] with w hw
    exact hinj.leftInvOn_invFunOn hw
  · filter_upwards [hconf.image_mem_nhds hUo hτU (hUo.mem_nhds hτU)] with u hu
    obtain ⟨w, hw, rfl⟩ := hu
    show H (Function.invFunOn H U (H w)) = H w
    rw [hinj.leftInvOn_invFunOn hw]

/-- **T4.**  The stretching function `λ_{h,q}` of the descended map at `p̂ z` is the lifted
`lambdaStretchPlane φ φ g z`. -/
theorem str_lambda {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) {φ : ℂ → ℂ}
    (hqφ : ∀ τ ∈ upperHalf, utm_liftQD q p τ = φ τ) {g : ℂ → ℂ} {K : ℝ}
    (hgK : IsKQC g upperHalf K) (hgimg : g '' upperHalf = upperHalf) (h : S ≃ₜ S)
    (hh : ∀ z ∈ upperHalf, h (s22gm_projectionExtension p z) = s22gm_projectionExtension p (g z))
    {z : ℂ} (hz : z ∈ upperHalf) :
    s26v_lam q h (s22gm_projectionExtension p z) = ENNReal.ofReal (lambdaStretchPlane φ φ g z) := by
  have hgz : g z ∈ upperHalf := hgimg ▸ mem_image_of_mem g hz
  set s := s22gm_projectionExtension p z with hs
  set τ : UpperHalfPlane := ⟨z, hz⟩ with hτ
  set τ' : UpperHalfPlane := ⟨g z, hgz⟩ with hτ'
  have hpτ : p τ = s := (s22gm_projectionExtension_coe p τ).symm
  have hpτ' : p τ' = h s := by
    rw [hs, hh z hz]
    exact (s22gm_projectionExtension_coe p τ').symm
  obtain ⟨k0, hd0, hk0, hk0H, hHk0, ha0, hlaw0⟩ :=
    str_localchart hp hq τ s (by rw [hpτ]; exact mem_chart_source ℂ s)
  obtain ⟨k1, hd1, hk1, hk1H, -, hb0, hlaw1⟩ :=
    str_localchart hp hq τ' (h s) (by rw [hpτ']; exact mem_chart_source ℂ (h s))
  set H : ℂ → ℂ := fun v => chartAt ℂ s (utm_pext p v) with hH
  set ψ : ℂ → ℂ := fun v => chartAt ℂ (h s) (utm_pext p v) with hψ
  have hpe : utm_pext p z = s := utm_a_pext_eq p hz
  have hph : ∀ w ∈ upperHalf, utm_pext p w = s22gm_projectionExtension p w :=
    fun w hw => utm_a_pext_eq p hw
  have hpe' : utm_pext p (g z) = h s := by
    rw [hph (g z) hgz]
    exact (hh z hz).symm
  have hτc : (τ : ℂ) = z := rfl
  have hτc' : (τ' : ℂ) = g z := rfl
  rw [hτc] at hd0 hk0 hk0H hHk0 hlaw0 ha0
  rw [hτc'] at hd1 hk1 hk1H hlaw1 hb0
  have hHz : H z = chartAt ℂ s s := by simp only [hH, hpe]
  have hψz : ψ (g z) = chartAt ℂ (h s) (h s) := by simp only [hψ, hpe']
  set a : ℂ := deriv H z with ha
  set b : ℂ := deriv ψ (g z) with hb
  set L : ℂ → ℂ := localMapExprAt h s (chartAt ℂ s s) with hL
  have hev : (L ∘ H) =ᶠ[𝓝 z] (ψ ∘ g) := by
    have hc1 : ContinuousAt (utm_pext p) z := utm_a_continuousAt hp.1.continuous hz
    have hmem : ∀ᶠ v in 𝓝 z, utm_pext p v ∈ (chartAt ℂ s).source :=
      hc1.preimage_mem_nhds ((chartAt ℂ s).open_source.mem_nhds (by rw [hpe]; exact mem_chart_source ℂ s))
    filter_upwards [hmem, isOpen_upperHalf.mem_nhds hz] with v hv hvH
    have hgv : g v ∈ upperHalf := hgimg ▸ mem_image_of_mem g hvH
    simp only [Function.comp_apply, hL, localMapExprAt, hH, hψ]
    rw [(chartAt ℂ s).left_inv (mem_chart_source ℂ s), (chartAt ℂ s).left_inv hv,
      hph v hvH, hph (g v) hgv, hh v hvH]
  have hLz : L (chartAt ℂ s s) = chartAt ℂ (h s) (h s) := by
    have := hev.self_of_nhds
    simp only [Function.comp_apply] at this
    rw [← hHz, this, hψz]
  have hgc : ContinuousAt g z := hgK.2.2.1.1.continuousAt (isOpen_upperHalf.mem_nhds hz)
  obtain ⟨hdzR, hdzbarR⟩ := s23_wirtinger_comp_right (g := L) (T := H) (S := k0) hd0 hk0 hk0H hHk0
  obtain ⟨hdzL, hdzbarL⟩ := s23_wirtinger_comp_left (g := g) (h := ψ) (k := k1) hgc hd1 hk1 hk1H
  have e1 : dz L (chartAt ℂ s s) * a = b * dz g z := by
    have h1 : dz (L ∘ H) z = dz (ψ ∘ g) z := by simp only [dz, hev.fderiv_eq]
    rw [hdzR, hdzL, hHz] at h1
    exact h1
  have e2 : dzbar L (chartAt ℂ s s) * conj a = b * dzbar g z := by
    have h1 : dzbar (L ∘ H) z = dzbar (ψ ∘ g) z := by simp only [dzbar, hev.fderiv_eq]
    rw [hdzbarR, hdzbarL, hHz] at h1
    exact h1
  rw [hpe] at hlaw0
  rw [hpe'] at hlaw1
  have hQ : φ z = q s (chartAt ℂ s s) * a ^ 2 := by rw [← hqφ z hz, hlaw0]
  have hQ' : φ (g z) = q (h s) (chartAt ℂ (h s) (h s)) * b ^ 2 := by rw [← hqφ (g z) hgz, hlaw1]
  have hlam : lambdaStretch q q h s (chartAt ℂ s s) =
      lambdaStretchPlane (q s) (q (h s)) L (chartAt ℂ s s) := by
    simp only [lambdaStretch, hL, (chartAt ℂ s).left_inv (mem_chart_source ℂ s)]
  show ENNReal.ofReal (lambdaStretch q q h s (chartAt ℂ s s)) = _
  congr 1
  rw [hlam]
  unfold lambdaStretchPlane
  rw [hLz]
  have halg := s26v_b_lambdaPlane_alg (dz L (chartAt ℂ s s)) (dzbar L (chartAt ℂ s s))
    (q s (chartAt ℂ s s)) a ha0 (Real.sqrt ‖q (h s) (chartAt ℂ (h s) (h s))‖)
  rw [← halg, ← hQ, e1, e2]
  have hfac : b * dz g z + b * dzbar g z * (φ z / ((‖φ z‖ : ℝ) : ℂ)) =
      b * (dz g z + dzbar g z * (φ z / ((‖φ z‖ : ℝ) : ℂ))) := by ring
  rw [hfac, norm_mul]
  have hsq : Real.sqrt ‖φ (g z)‖ =
      Real.sqrt ‖q (h s) (chartAt ℂ (h s) (h s))‖ * ‖b‖ := by
    rw [hQ', norm_mul, norm_pow, Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  rw [hsq]
  ring

end T4


end LiZhongQC
