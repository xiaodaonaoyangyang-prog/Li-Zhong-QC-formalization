import LiZhongQC.Ch02.S13_Representation

/-!
# Removability of an isolated puncture for quasiconformal maps (Lehto–Virtanen I.8.1, planar form)

`lv81_puncture_removable`: a `K`-quasiconformal map `f` of an open set `G ⊆ ℂ` that omits an isolated point `z₀`
(a punctured disc around `z₀` lies in `G`), with bounded image near `z₀`, has a limit `w₀` at `z₀`, `w₀ ∉ f(G)`, and
`f` extended by `w₀` is `K`-quasiconformal on `G ∪ {z₀}`.  (Lehto–Virtanen 1973, Theorem I.8.1, for a puncture whose
image is finite; the case `w₀ = ∞` reduces to this one by a Möbius conjugation.)

Route (instead of the book's ring-modulus argument): the normalized solution `χ` of the Beltrami equation for the
dilatation of `f` on the punctured disc (`thm13_7_normalized_existence`) factors `f = φ ∘ χ` there with `φ` conformal
(`same_dilatation_conformal`); `φ` is bounded and holomorphic on a punctured disc, so it extends holomorphically
(Riemann's removable singularity theorem, Mathlib); the open mapping theorem makes the inverse continuous at `w₀`;
`K`-quasiconformality at `z₀` is the removability of a point (`s13x_removable`).  Helpers carry the prefix `lv81_`.
-/

open Complex Set Metric Filter Topology MeasureTheory Function
open scoped ComplexConjugate

noncomputable section

namespace LiZhongQC

/-- **Lehto–Virtanen I.8.1** (planar form, finite image of the puncture): an isolated boundary point `z₀` of the
domain of a `K`-quasiconformal map `f` with bounded image near `z₀` is a removable singularity: `f` has a limit `w₀`
at `z₀`, `w₀` is not a value of `f`, and `f` extended by `w₀` is `K`-quasiconformal on `G ∪ {z₀}`. -/
theorem lv81_puncture_removable {f : ℂ → ℂ} {G : Set ℂ} {K : ℝ} (hf : IsKQC f G K) {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hsub : ball z₀ r \ {z₀} ⊆ G) (hz₀ : z₀ ∉ G)
    (hbdd : Bornology.IsBounded (f '' (ball z₀ r \ {z₀}))) :
    ∃ w₀ : ℂ, Tendsto f (𝓝[≠] z₀) (𝓝 w₀) ∧ w₀ ∉ f '' G ∧ IsKQC (Function.update f z₀ w₀) (insert z₀ G) K := by
  classical
  have hGo : IsOpen G := hf.1
  have hK1 : 1 ≤ K := hf.2.1
  have hfH := hf.2.2.1
  set D₀ : Set ℂ := ball z₀ r \ {z₀} with hD₀
  have hD₀o : IsOpen D₀ := isOpen_ball.sdiff isClosed_singleton
  have hD₀m : MeasurableSet D₀ := hD₀o.measurableSet
  have hfD : IsKQC f D₀ K := ac_t_isKQC_restrict hf hD₀o hsub
  -- the Beltrami coefficient of `f` on the punctured disc, extended by `0`
  obtain ⟨⟨hμm, hμb⟩, -⟩ := thm10_2_genHomeoSolution_of_isKQC hfD
  set k : ℝ := (K - 1) / (K + 1) with hk
  have hk0 : 0 ≤ k := div_nonneg (by linarith) (by linarith)
  have hk1 : k < 1 := (div_lt_one (by linarith)).2 (by linarith)
  set μ : ℂ → ℂ := D₀.indicator (complexDilatation f) with hμ
  have hμB : IsBeltramiCoeff μ univ k := by
    refine ⟨?_, ?_⟩
    · rw [Measure.restrict_univ]
      exact (aestronglyMeasurable_indicator_iff hD₀m).2 hμm
    · rw [Measure.restrict_univ]
      have h1 := (ae_restrict_iff' hD₀m).1 hμb
      filter_upwards [h1] with z hz
      by_cases h : z ∈ D₀
      · rw [hμ, indicator_of_mem h]
        exact hz h
      · rw [hμ, indicator_of_notMem h, norm_zero]
        exact hk0
  -- the normalized solution `χ`, a homeomorphism of the plane
  obtain ⟨χ, hχN, hχK, -⟩ := thm13_7_normalized_existence hk0 hk1 hμB
  obtain ⟨-, hχs, -, -, hχd⟩ := hχN
  have hχH := hχK.2.2.1
  rw [hχs] at hχH
  let χe : ℂ ≃ₜ ℂ :=
    { toFun := χ
      invFun := Function.invFunOn χ univ
      left_inv := fun z => hχH.2.1.leftInvOn_invFunOn (mem_univ z)
      right_inv := fun y => Function.invFunOn_eq (by
        have : y ∈ χ '' univ := by rw [hχs]; exact mem_univ y
        obtain ⟨a, ha, hay⟩ := this
        exact ⟨a, ha, hay⟩)
      continuous_toFun := continuousOn_univ.1 hχH.1
      continuous_invFun := continuousOn_univ.1 hχH.2.2.2 }
  have hχe : ∀ z, χe z = χ z := fun z => rfl
  -- `f = φ ∘ χ` on the punctured disc with `φ` conformal
  have hχD : IsKQC χ D₀ ((1 + k) / (1 - k)) := ac_t_isKQC_restrict hχK hD₀o (subset_univ _)
  have hae : ∀ᵐ z ∂(volume.restrict D₀), complexDilatation f z = complexDilatation χ z := by
    have h1 : ∀ᵐ z ∂(volume.restrict D₀), complexDilatation χ z = μ z := ae_restrict_of_ae hχd
    filter_upwards [h1, ae_restrict_mem hD₀m] with z h1 h2
    rw [h1, hμ, indicator_of_mem h2]
  obtain ⟨hμχ, hχsol⟩ := thm10_2_genHomeoSolution_of_isKQC hχD
  have hfsol := nxS_genHomeoSolution_congr (thm10_2_genHomeoSolution_of_isKQC hfD).2 hae
  have hK' : 1 ≤ (1 + k) / (1 - k) := hχD.2.1
  have hk' : ((1 + k) / (1 - k) - 1) / ((1 + k) / (1 - k) + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  obtain ⟨φ, hφ, hfφ⟩ := same_dilatation_conformal hD₀o hk' hμχ hχsol hfsol
  -- a punctured disc around `c = χ z₀` inside `χ(D₀)`
  set c := χ z₀ with hc
  have hball : IsOpen (χe '' ball z₀ r) := χe.isOpenMap _ isOpen_ball
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 hball c (mem_image_of_mem χe (mem_ball_self hr))
  have hpunct : ball c ρ \ {c} ⊆ χ '' D₀ := by
    rintro u ⟨hu, huc⟩
    obtain ⟨z, hz, rfl⟩ := hρsub hu
    refine ⟨z, ⟨hz, fun h => huc ?_⟩, rfl⟩
    rw [mem_singleton_iff] at h ⊢
    rw [h, hχe]
  have hφd : DifferentiableOn ℂ φ (ball c ρ \ {c}) := hφ.1.mono hpunct
  have hφb : BddAbove (norm ∘ φ '' (ball c ρ \ {c})) := by
    obtain ⟨C, hC⟩ := hbdd.exists_norm_le
    refine ⟨C, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hpunct hu
    show ‖φ (χ z)‖ ≤ C
    rw [← hfφ z hz]
    exact hC _ (mem_image_of_mem f hz)
  set w₀ := limUnder (𝓝[≠] c) φ with hw₀
  set ψ := Function.update φ c w₀ with hψ
  have hψd : DifferentiableOn ℂ ψ (ball c ρ) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds c hρ) hφd hφb
  have hψc : ψ c = w₀ := Function.update_self c w₀ φ
  have hψφ : ∀ u, u ≠ c → ψ u = φ u := fun u hu => Function.update_of_ne hu w₀ φ
  have hψa : AnalyticAt ℂ ψ c := hψd.analyticAt (ball_mem_nhds c hρ)
  have hφlim : Tendsto φ (𝓝[≠] c) (𝓝 w₀) := by
    have h1 : Tendsto ψ (𝓝[≠] c) (𝓝 w₀) := by
      rw [← hψc]
      exact hψa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hψφ u hu
  -- `f → w₀` at `z₀`
  have hχt : Tendsto χ (𝓝[≠] z₀) (𝓝[≠] c) := by
    refine tendsto_nhdsWithin_iff.2 ⟨χe.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    intro h
    exact hz (χe.injective h)
  have hD₀ev : ∀ᶠ z in 𝓝[≠] z₀, z ∈ D₀ := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds z₀ hr), self_mem_nhdsWithin] with z h1 h2
    exact ⟨h1, h2⟩
  have htend : Tendsto f (𝓝[≠] z₀) (𝓝 w₀) := by
    refine (hφlim.comp hχt).congr' ?_
    filter_upwards [hD₀ev] with z hz
    exact (hfφ z hz).symm
  -- `w₀` is not a value of `f`
  have hw₀G : w₀ ∉ f '' G := by
    rintro ⟨z₁, hz₁, hfz₁⟩
    have hcw : ContinuousWithinAt (Function.invFunOn f G) (f '' G) w₀ :=
      hfH.2.2.2 w₀ ⟨z₁, hz₁, hfz₁⟩
    have h1 : Tendsto f (𝓝[≠] z₀) (𝓝[f '' G] w₀) := by
      refine tendsto_nhdsWithin_iff.2 ⟨htend, ?_⟩
      filter_upwards [hD₀ev] with z hz
      exact mem_image_of_mem f (hsub hz)
    have h2 := hcw.tendsto.comp h1
    have h3 : Function.invFunOn f G w₀ = z₁ := by
      rw [← hfz₁]
      exact hfH.2.1.leftInvOn_invFunOn hz₁
    rw [h3] at h2
    have h4 : Tendsto (fun z => z) (𝓝[≠] z₀) (𝓝 z₁) := by
      refine h2.congr' ?_
      filter_upwards [hD₀ev] with z hz
      exact hfH.2.1.leftInvOn_invFunOn (hsub hz)
    have h5 : Tendsto (fun z => z) (𝓝[≠] z₀) (𝓝 z₀) := tendsto_id.mono_left nhdsWithin_le_nhds
    have h6 : z₁ = z₀ := tendsto_nhds_unique h4 h5
    exact hz₀ (h6 ▸ hz₁)
  -- the extension `F`
  set F := Function.update f z₀ w₀ with hF
  have hFz₀ : F z₀ = w₀ := Function.update_self z₀ w₀ f
  have hFG : EqOn F f G := fun z hz => Function.update_of_ne (by rintro rfl; exact hz₀ hz) w₀ f
  have hΩeq : insert z₀ G = G ∪ ball z₀ r := by
    ext z
    constructor
    · rintro (rfl | hz)
      · exact Or.inr (mem_ball_self hr)
      · exact Or.inl hz
    · rintro (hz | hz)
      · exact Or.inr hz
      · by_cases h : z = z₀
        · exact Or.inl h
        · exact Or.inr (hsub ⟨hz, h⟩)
  have hΩo : IsOpen (insert z₀ G) := by
    rw [hΩeq]
    exact hGo.union isOpen_ball
  have hFc : ContinuousOn F (insert z₀ G) := by
    intro z hz
    refine ContinuousAt.continuousWithinAt ?_
    rcases hz with rfl | hz
    · exact continuousAt_update_same.2 htend
    · have hev : f =ᶠ[𝓝 z] F := by
        filter_upwards [hGo.mem_nhds hz] with y hy
        exact (hFG hy).symm
      exact ((hfH.1 z hz).continuousAt (hGo.mem_nhds hz)).congr hev
  have hFi : InjOn F (insert z₀ G) := by
    rintro x (rfl | hx) y (rfl | hy) h
    · rfl
    · rw [hFz₀, hFG hy] at h
      exact absurd ⟨y, hy, h.symm⟩ hw₀G
    · rw [hFz₀, hFG hx] at h
      exact absurd ⟨x, hx, h⟩ hw₀G
    · rw [hFG hx, hFG hy] at h
      exact hfH.2.1 hx hy h
  have hFimg : F '' insert z₀ G = insert w₀ (f '' G) := by
    rw [image_insert_eq, hFz₀, hFG.image_eq]
  have hinvG : ∀ z ∈ G, Function.invFunOn F (insert z₀ G) (f z) = z := by
    intro z hz
    have h1 : F z = f z := hFG hz
    rw [← h1]
    exact hFi.leftInvOn_invFunOn (mem_insert_of_mem z₀ hz)
  have hinv₀ : Function.invFunOn F (insert z₀ G) w₀ = z₀ := by
    rw [← hFz₀]
    exact hFi.leftInvOn_invFunOn (mem_insert z₀ G)
  -- `ψ` is not constant near `c` (`φ` is injective), so it is open there
  have hopen : 𝓝 w₀ ≤ map ψ (𝓝 c) := by
    rcases hψa.eventually_constant_or_nhds_le_map_nhds with h | h
    · exfalso
      obtain ⟨ε, hε, hεsub⟩ := Metric.eventually_nhds_iff.1 h
      set ε' := min ε ρ / 2 with hε'
      have hε'0 : 0 < ε' := by positivity
      have hu1 : c + ε' ∈ ball c ρ \ {c} := by
        refine ⟨?_, ?_⟩
        · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hε'0.le]
          have : min ε ρ ≤ ρ := min_le_right _ _
          linarith
        · rw [mem_singleton_iff, add_eq_left]
          exact_mod_cast hε'0.ne'
      have hu2 : c + ε' / 2 ∈ ball c ρ \ {c} := by
        refine ⟨?_, ?_⟩
        · rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
          rw [show (ε' / 2 : ℂ) = ((ε' / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
            Real.norm_of_nonneg (by positivity)]
          have : min ε ρ ≤ ρ := min_le_right _ _
          linarith
        · rw [mem_singleton_iff, add_eq_left]
          exact div_ne_zero (by exact_mod_cast hε'0.ne') two_ne_zero
      have hd1 : dist (c + ε') c < ε := by
        rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hε'0.le]
        have : min ε ρ ≤ ε := min_le_left _ _
        linarith
      have hd2 : dist (c + ε' / 2) c < ε := by
        rw [dist_eq_norm, add_sub_cancel_left]
        rw [show (ε' / 2 : ℂ) = ((ε' / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
        have : min ε ρ ≤ ε := min_le_left _ _
        linarith
      have he1 := hεsub hd1
      have he2 := hεsub hd2
      rw [hψφ _ hu1.2] at he1
      rw [hψφ _ hu2.2] at he2
      have heq := hφ.2.1 (hpunct hu1) (hpunct hu2) (he1.trans he2.symm)
      have : (ε' : ℂ) = ε' / 2 := add_left_cancel heq
      have h0 : (ε' : ℂ) = 0 := by linear_combination 2 * this
      exact hε'0.ne' (by exact_mod_cast h0)
    · rwa [hψc] at h
  have hFinv : ContinuousOn (Function.invFunOn F (insert z₀ G)) (F '' insert z₀ G) := by
    rw [hFimg]
    rintro w (rfl | ⟨z, hz, rfl⟩)
    · -- at `w₀`
      rw [ContinuousWithinAt, hinv₀]
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hχsc : ContinuousAt χe.symm c := χe.symm.continuous.continuousAt
      have hχs0 : χe.symm c = z₀ := by rw [hc, ← hχe, χe.symm_apply_apply]
      obtain ⟨δ, hδ, hδsub⟩ := Metric.continuousAt_iff.1 hχsc ε hε
      set δ' := min δ ρ with hδ'
      have hδ'0 : 0 < δ' := lt_min hδ hρ
      have himg : ψ '' ball c δ' ∈ 𝓝 w₀ := hopen (image_mem_map (ball_mem_nhds c hδ'0))
      filter_upwards [nhdsWithin_le_nhds himg, self_mem_nhdsWithin] with w hw1 hw2
      obtain ⟨u, hu, rfl⟩ := hw1
      by_cases huc : u = c
      · rw [huc, hψc, hinv₀, dist_self]
        exact hε
      · have hu' : u ∈ ball c ρ \ {c} := ⟨ball_subset_ball (min_le_right _ _) hu, huc⟩
        obtain ⟨z, hz, hzu⟩ := hpunct hu'
        have hψu : ψ u = f z := by rw [hψφ u huc, ← hzu, hfφ z hz]
        rw [hψu, hinvG z (hsub hz)]
        have h1 : χe.symm u = z := by rw [← hzu, ← hχe, χe.symm_apply_apply]
        have h2 := hδsub (lt_of_lt_of_le (mem_ball.1 hu) (min_le_left _ _))
        rw [h1, hχs0] at h2
        exact h2
    · -- at a value `f z`, `z ∈ G`
      rw [continuousWithinAt_insert]
      have h1 : ContinuousWithinAt (Function.invFunOn f G) (f '' G) (f z) :=
        hfH.2.2.2 (f z) (mem_image_of_mem f hz)
      refine h1.congr ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        rw [hinvG y hy, hfH.2.1.leftInvOn_invFunOn hy]
      · rw [hinvG z hz, hfH.2.1.leftInvOn_invFunOn hz]
  have hhom : IsHomeomorphOnto F (insert z₀ G) (F '' insert z₀ G) := ⟨hFc, hFi, rfl, hFinv⟩
  refine ⟨w₀, htend, hw₀G, ?_⟩
  refine s13x_removable (L := {z₀}) hΩo hK1 hhom (measure_singleton z₀) ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun x => (Set.countable_singleton z₀.im).mono ?_
    intro y hy
    have h := congrArg Complex.im (mem_singleton_iff.1 hy)
    simp at h
    exact h
  · refine Filter.Eventually.of_forall fun y => (Set.countable_singleton z₀.re).mono ?_
    intro x hx
    have h := congrArg Complex.re (mem_singleton_iff.1 hx)
    simp at h
    exact h
  · intro z hz
    have hzG : z ∈ G := by
      rcases hz.1 with h | h
      · exact absurd h hz.2
      · exact h
    exact ⟨G, hGo, hzG, subset_insert z₀ G, ad_isKQC_congr hf hFG⟩

end LiZhongQC
