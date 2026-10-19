import LiZhongQC.Lemmas.GeodesicContacts
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC

/-- One phi-arclength parameter covers an entire zero-free open gap, even if
its endpoints are zeros. It is C1 and regular throughout the open gap, and
the quadratic velocity is one nonzero constant throughout that gap.
The increasing parameter preserves the full closed trace and both endpoints. -/
theorem s25ep_gap_arclength {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {γ : LRCurve}
    (hγ : IsPhiGeodesic φ unitDisc γ)
    (hγp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hnz : ∀ t ∈ Ioo a b, φ (γ.toFun t) ≠ 0) :
    ∃ (h : ℝ → ℝ) (k : ℝ), 0 < k ∧ StrictMonoOn h (Icc a b) ∧ h '' Icc a b = Icc a b ∧
      ContinuousOn h (Icc a b) ∧ h a = a ∧ h b = b ∧
      (∀ τ ∈ Icc a b, (phiSegmentLength φ γ a (h τ)).toReal = k * (τ - a)) ∧
      ContDiffOn ℝ 1 (γ.toFun ∘ h) (Ioo a b) ∧ IsPhiStraightArc φ (γ.toFun ∘ h) a b ∧
      ∃ C : ℂ, C ≠ 0 ∧ ∀ τ ∈ Ioo a b,
        φ ((γ.toFun ∘ h) τ) * deriv (γ.toFun ∘ h) τ ^ 2 = C := by
  classical
  have hI : ∀ x ∈ Icc a b, x ∈ Icc (0 : ℝ) 1 := fun x hx => ⟨ha.trans hx.1, hx.2.trans hb⟩
  obtain ⟨M, hM0, hM⟩ := s25g_segLen_bound hφ hγ
  have hfin : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → phiSegmentLength φ γ s t ≠ ⊤ :=
    fun s hs t ht hst => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hM s (hI s hs) t (hI t ht) hst)
  set S : ℝ → ℝ := fun x => (phiSegmentLength φ γ a x).toReal with hS
  have hSa : S a = 0 := by simp [hS, phiSegmentLength]
  have hSadd : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      S t - S s = (phiSegmentLength φ γ s t).toReal := by
    intro s hs t ht hst
    simp only [hS]
    rw [s25g_segLen_add φ γ hs.1 hst,
      ENNReal.toReal_add (hfin a ⟨le_rfl, hab.le⟩ s hs hs.1) (hfin s hs t ht hst)]
    ring
  have hSmo : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → S s ≤ S t := fun s hs t ht hst => by
    have := hSadd s hs t ht hst
    have h0 := ENNReal.toReal_nonneg (a := phiSegmentLength φ γ s t)
    linarith
  have hSlip : LipschitzOnWith M.toNNReal S (Icc a b) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    wlog hxy : x ≤ y generalizing x y
    · rw [dist_comm, dist_comm x y]
      exact this y hy x hx (not_le.1 hxy).le
    rw [Real.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hSmo x hx y hy hxy)),
      abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hxy), hSadd x hx y hy hxy]
    have := hM x (hI x hx) y (hI y hy) hxy
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top this
    rw [ENNReal.toReal_ofReal (mul_nonneg hM0 (sub_nonneg.2 hxy))] at h2
    rwa [Real.coe_toNNReal _ hM0]
  have hSstrict : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s < t → S s < S t := by
    intro s hs t ht hst
    have hp := s25fc_segment_pos hφ hne hγ hγp (hI s hs).1 hst (hI t ht).2
    have hpos := ENNReal.toReal_pos (ne_of_gt hp) (hfin s hs t ht hst.le)
    have hadd := hSadd s hs t ht hst.le
    linarith
  have hSmono : StrictMonoOn S (Icc a b) := fun s hs t ht hst => hSstrict s hs t ht hst
  obtain ⟨h, hmono, himg, hhS, hcont⟩ :=
    s25g_arclength_inv hab hSlip.continuousOn hSmono hSa
  have hha : h a = a := by
    have haI : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
    obtain ⟨x, hx, he⟩ := (show a ∈ h '' Icc a b by rw [himg]; exact haI)
    exact le_antisymm ((hmono.monotoneOn haI hx hx.1).trans_eq he) (hhS a haI).1.1
  have hhb : h b = b := by
    have hbI : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
    obtain ⟨x, hx, he⟩ := (show b ∈ h '' Icc a b by rw [himg]; exact hbI)
    exact le_antisymm (hhS b hbI).1.2 (he.symm.trans_le (hmono.monotoneOn hx hbI hx.2))
  have hinto : ∀ τ ∈ Ioo a b, h τ ∈ Ioo a b := by
    intro τ hτ
    have hl := hmono ⟨le_rfl, hab.le⟩ (Ioo_subset_Icc_self hτ) hτ.1
    have hr := hmono (Ioo_subset_Icc_self hτ) ⟨hab.le, le_rfl⟩ hτ.2
    rw [hha] at hl
    rw [hhb] at hr
    exact ⟨hl, hr⟩
  have hhc : ContinuousOn h (Icc a b) := by
    let H : Icc a b → Icc a b := fun x => ⟨h x, (hhS x x.property).1⟩
    have hHm : StrictMono H := fun x y hxy => hmono x.property y.property hxy
    have hHs : Function.Surjective H := by
      intro y
      obtain ⟨x, hx, he⟩ := (show y.val ∈ h '' Icc a b by rw [himg]; exact y.property)
      exact ⟨⟨x, hx⟩, Subtype.ext he⟩
    have hHc : Continuous H := (hHm.orderIsoOfSurjective H hHs).continuous
    exact continuousOn_iff_continuous_domRestrict.2 (continuous_subtype_val.comp hHc)
  set k : ℝ := S b / (b - a) with hk
  have hk0 : 0 < k := by
    have : 0 < S b := by
      have := hSmono (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hab
      rwa [hSa] at this
    exact div_pos this (sub_pos.2 hab)
  -- local structure of `γ ∘ h`
  have hloc2 : ∀ τ' ∈ Ioo a b, ∃ c : ℂ, ∀ᶠ τ in 𝓝 τ', ContDiffAt ℝ 1 (γ.toFun ∘ h) τ ∧
      deriv (γ.toFun ∘ h) τ ≠ 0 ∧ φ ((γ.toFun ∘ h) τ) * deriv (γ.toFun ∘ h) τ ^ 2 = c := by
    intro τ' hτ'
    have hτ'I : τ' ∈ Icc a b := Ioo_subset_Icc_self hτ'
    obtain ⟨ht'I, hSt'⟩ := hhS τ' hτ'I
    set t' := h τ' with ht'
    obtain ⟨δ, hδ, ζ, ψ, W, u, hu1, hWo, hWD, han, hinj, hopen, hψ, hwin, hrel⟩ :=
      s25g_local isOpen_ball hφ hγ hγp (hI t' ht'I) (hnz t' (hinto τ' hτ'))
    obtain ⟨η, hη, hηh⟩ := hcont τ' hτ' δ hδ
    set N : Set ℝ := Ioo (max a (τ' - η)) (min b (τ' + η)) with hN
    have hNo : IsOpen N := isOpen_Ioo
    have hNn : N ∈ 𝓝 τ' :=
      hNo.mem_nhds ⟨max_lt hτ'.1 (by linarith), lt_min hτ'.2 (by linarith)⟩
    have hNI : ∀ τ ∈ N, τ ∈ Icc a b ∧ |τ - τ'| < η := by
      intro τ hτ
      refine ⟨⟨(le_max_left _ _).trans hτ.1.le, hτ.2.le.trans (min_le_left _ _)⟩, ?_⟩
      rw [abs_lt]
      constructor
      · linarith [le_max_right a (τ' - η), hτ.1]
      · linarith [min_le_right b (τ' + η), hτ.2]
    have hxd : ∀ τ ∈ N, h τ ∈ Icc a b ∧ |h τ - t'| < δ := fun τ hτ =>
      ⟨(hhS τ (hNI τ hτ).1).1, hηh τ (hNI τ hτ).1 (hNI τ hτ).2⟩
    have hψζ : ∀ x ∈ W, ψ (ζ x) = x := fun x hx =>
      hinj (hψ (ζ x) ⟨x, hx, rfl⟩).1 hx (hψ (ζ x) ⟨x, hx, rfl⟩).2.1
    have hGW : ∀ τ ∈ N, γ.toFun (h τ) ∈ W := by
      intro τ hτ
      obtain ⟨hxI, hxd'⟩ := hxd τ hτ
      rw [abs_lt] at hxd'
      exact hwin (h τ) (hI _ hxI) (by linarith [hxd'.1]) (by linarith [hxd'.2])
    have hlin : ∀ τ ∈ N, ζ (γ.toFun (h τ)) = ζ (γ.toFun t') + u * ((k * (τ - τ') : ℝ) : ℂ) := by
      intro τ hτ
      obtain ⟨hxI, hxd'⟩ := hxd τ hτ
      rw [abs_lt] at hxd'
      have hdiff : S (h τ) - S t' = k * (τ - τ') := by
        rw [(hhS τ (hNI τ hτ).1).2, hSt']; ring
      rcases le_total t' (h τ) with hle | hle
      · have := hrel t' (hI t' ht'I) (h τ) (hI _ hxI) (by linarith) hle (by linarith [hxd'.2])
        rw [← hSadd t' ht'I (h τ) hxI hle, hdiff] at this
        linear_combination this
      · have := hrel (h τ) (hI _ hxI) t' (hI t' ht'I) (by linarith [hxd'.1]) hle (by linarith)
        rw [← hSadd (h τ) hxI t' ht'I hle, show S t' - S (h τ) = -(k * (τ - τ')) by linarith] at this
        push_cast at this ⊢
        linear_combination -this
    have hGd : ∀ τ ∈ N, ContDiffAt ℝ 1 (γ.toFun ∘ h) τ ∧ HasDerivAt (γ.toFun ∘ h)
        (u * (k : ℂ) * (deriv ζ (γ.toFun (h τ)))⁻¹) τ := by
      intro τ hτ
      set A : ℝ → ℂ := fun σ => ζ (γ.toFun t') + u * ((k * (σ - τ') : ℝ) : ℂ) with hA
      have hA' : HasDerivAt A (u * (k : ℂ)) τ := by
        have h1 : HasDerivAt (fun σ : ℝ => k * (σ - τ')) (k * 1) τ :=
          ((hasDerivAt_id τ).sub_const τ').const_mul k
        have h2 := (h1.ofReal_comp).const_mul u
        have h3 := h2.const_add (ζ (γ.toFun t'))
        exact h3.congr_deriv (by push_cast; ring)
      have hAτ : A τ = ζ (γ.toFun (h τ)) := (hlin τ hτ).symm
      have hAmem : A τ ∈ ζ '' W := ⟨_, hGW τ hτ, hAτ.symm⟩
      have hψd := (hψ (A τ) hAmem).2.2
      have hcomp := hψd.scomp τ hA'
      have hψA : ψ (A τ) = γ.toFun (h τ) := by rw [hAτ]; exact hψζ _ (hGW τ hτ)
      have hev : (γ.toFun ∘ h) =ᶠ[𝓝 τ] ψ ∘ A := by
        filter_upwards [hNo.mem_nhds hτ] with σ hσ
        show γ.toFun (h σ) = ψ (A σ)
        rw [show A σ = ζ (γ.toFun (h σ)) from (hlin σ hσ).symm, hψζ _ (hGW σ hσ)]
      have hψan : AnalyticOnNhd ℂ ψ (ζ '' W) := by
        apply DifferentiableOn.analyticOnNhd _ hopen
        intro w hw
        exact (hψ w hw).2.2.differentiableAt.differentiableWithinAt
      have hAc : ContDiff ℝ 1 A := by
        have hreal : ContDiff ℝ 1 (fun σ : ℝ => k * (σ - τ')) :=
          contDiff_const.mul (contDiff_id.sub contDiff_const)
        have hcast : ContDiff ℝ 1 (fun σ : ℝ => ((k * (σ - τ') : ℝ) : ℂ)) :=
          Complex.ofRealCLM.contDiff.comp hreal
        exact contDiff_const.add (contDiff_const.mul hcast)
      have hCc : ContDiffAt ℝ 1 (ψ ∘ A) τ :=
        ((hψan (A τ) hAmem).contDiffAt.restrict_scalars ℝ).comp τ hAc.contDiffAt
      refine ⟨hCc.congr_of_eventuallyEq hev, ?_⟩
      rw [hψA] at hcomp
      simpa [smul_eq_mul] using hcomp.congr_of_eventuallyEq hev
    refine ⟨(u * (k : ℂ)) ^ 2, ?_⟩
    filter_upwards [hNn] with τ hτ
    obtain ⟨hζa, hζφ, hζne⟩ := han _ (hGW τ hτ)
    have hu0 : u ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hu1; exact zero_ne_one hu1
    have hk0' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
    obtain ⟨hC, hd⟩ := hGd τ hτ
    refine ⟨hC, ?_, ?_⟩
    · rw [hd.deriv]
      exact mul_ne_zero (mul_ne_zero hu0 hk0') (inv_ne_zero hζne)
    · rw [hd.deriv]
      show φ (γ.toFun (h τ)) * _ = _
      rw [← hζφ]
      field_simp
  -- `φ (γ ∘ h) (γ ∘ h)'²` is locally constant, hence constant
  set Wf : ℝ → ℂ := fun τ => φ ((γ.toFun ∘ h) τ) * deriv (γ.toFun ∘ h) τ ^ 2 with hWf
  have hlcl : IsLocallyConstant (fun x : Ioo a b => Wf x.1) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨c, hc⟩ := hloc2 x.1 x.2
    have hx := hc.self_of_nhds
    have h1 : ∀ᶠ τ in 𝓝 x.1, Wf τ = Wf x.1 := by
      filter_upwards [hc] with τ hτ
      rw [show Wf τ = c from hτ.2.2, show Wf x.1 = c from hx.2.2]
    exact (continuous_subtype_val.tendsto x).eventually h1
  haveI : PreconnectedSpace (Ioo a b) := Subtype.preconnectedSpace isPreconnected_Ioo
  have hτ₀ : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hconst : ∀ τ ∈ Ioo a b, Wf τ = Wf ((a + b) / 2) := fun τ hτ =>
    hlcl.apply_eq_of_isPreconnected isPreconnected_univ (x := ⟨τ, hτ⟩) (y := ⟨(a + b) / 2, hτ₀⟩)
      (mem_univ _) (mem_univ _)
  have hdiff : ∀ τ ∈ Ioo a b, DifferentiableAt ℝ (γ.toFun ∘ h) τ ∧ deriv (γ.toFun ∘ h) τ ≠ 0 := by
    intro τ hτ
    obtain ⟨c, hc⟩ := hloc2 τ hτ
    have := hc.self_of_nhds
    exact ⟨this.1.differentiableAt_one, this.2.1⟩
  have hc0 : Wf ((a + b) / 2) ≠ 0 := by
    have hτ := hτ₀
    have hmem := (hhS _ (Ioo_subset_Icc_self hτ)).1
    exact mul_ne_zero (hnz _ (hinto _ hτ)) (pow_ne_zero 2 (hdiff _ hτ).2)
  have hC : ContDiffOn ℝ 1 (γ.toFun ∘ h) (Ioo a b) := by
    intro τ hτ
    obtain ⟨c, hc⟩ := hloc2 τ hτ
    exact hc.self_of_nhds.1.contDiffWithinAt
  refine ⟨h, k, hk0, hmono, himg, hhc, hha, hhb, ?_, hC, ?_,
    Wf ((a + b) / 2), hc0, hconst⟩
  · intro τ hτ
    exact (hhS τ hτ).2
  · refine ⟨arg (Wf ((a + b) / 2)), fun τ hτ => ⟨(hdiff τ hτ).1, (hdiff τ hτ).2, ?_, ?_⟩⟩
    · have := hconst τ hτ
      rw [show φ ((γ.toFun ∘ h) τ) * deriv (γ.toFun ∘ h) τ ^ 2 = Wf τ from rfl, this]
      exact hc0
    · have := hconst τ hτ
      rw [show φ ((γ.toFun ∘ h) τ) * deriv (γ.toFun ∘ h) τ ^ 2 = Wf τ from rfl, this]
      have hexp : Wf ((a + b) / 2) = ((‖Wf ((a + b) / 2)‖ : ℝ) : ℂ) * exp (arg (Wf ((a + b) / 2)) * I) :=
        (Complex.norm_mul_exp_arg_mul_I _).symm
      have e : Wf ((a + b) / 2) * exp (-(arg (Wf ((a + b) / 2)) : ℂ) * I) =
          ((‖Wf ((a + b) / 2)‖ : ℝ) : ℂ) := by
        conv_lhs => arg 1; rw [hexp]
        rw [mul_assoc, ← Complex.exp_add, show (arg (Wf ((a + b) / 2)) : ℂ) * I +
          -(arg (Wf ((a + b) / 2)) : ℂ) * I = 0 by ring, Complex.exp_zero, mul_one]
      rw [e]
      exact Complex.arg_ofReal_of_nonneg (norm_nonneg _)
  
  
/-- A nondegenerate real change of parameter multiplies the quadratic
velocity by the positive square of its derivative. -/
theorem s25ep_quadratic_velocity_comp {φ : ℂ → ℂ} {f : ℝ → ℂ} {h : ℝ → ℝ}
    {t d : ℝ} (hf : DifferentiableAt ℝ f (h t)) (hh : HasDerivAt h d t) :
    φ ((f ∘ h) t) * deriv (f ∘ h) t ^ 2 =
      ((d ^ 2 : ℝ) : ℂ) * (φ (f (h t)) * deriv f (h t) ^ 2) := by
  have hd := hf.hasDerivAt.scomp t hh
  rw [hd.deriv]
  simp only [Function.comp_apply, Complex.real_smul]
  push_cast
  ring

/-- A regular scalar reparametrization preserves the single straight-arc
direction on a whole gap. This also covers orientation reversal, since the
quadratic velocity acquires the positive square of the scalar derivative. -/
theorem s25ep_straight_reparam {φ : ℂ → ℂ} {f : ℝ → ℂ} {h : ℝ → ℝ}
    {a b s t : ℝ} (hf : IsPhiStraightArc φ f a b)
    (hmap : MapsTo h (Ioo s t) (Ioo a b))
    (hh : ∀ u ∈ Ioo s t, DifferentiableAt ℝ h u ∧ deriv h u ≠ 0) :
    IsPhiStraightArc φ (f ∘ h) s t := by
  obtain ⟨θ, hθ⟩ := hf
  refine ⟨θ, ?_⟩
  intro u hu
  obtain ⟨hfd, hfne, hqne, harg⟩ := hθ (h u) (hmap hu)
  obtain ⟨hhd, hhne⟩ := hh u hu
  have hd := hfd.hasDerivAt.scomp u hhd.hasDerivAt
  have hvel := s25ep_quadratic_velocity_comp (φ := φ) hfd hhd.hasDerivAt
  have hpos : 0 < deriv h u ^ 2 := sq_pos_of_ne_zero hhne
  have hcast : ((deriv h u ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hpos)
  refine ⟨hd.differentiableAt, ?_, ?_, ?_⟩
  · rw [hd.deriv]
    exact smul_ne_zero hhne hfne
  · rw [hvel]
    exact mul_ne_zero hcast hqne
  · rw [hvel, mul_assoc, Complex.arg_real_mul _ hpos]
    exact harg

/-- A scalar bijection preserving the parameter interval preserves the
entire curve trace, including both endpoints. -/
theorem s25ep_reparam_trace {f : ℝ → ℂ} {h : ℝ → ℝ} {a b s t : ℝ}
    (himage : h '' Icc s t = Icc a b) : (f ∘ h) '' Icc s t = f '' Icc a b := by
  exact (Set.image_image f h (Icc s t)).symm.trans
    (congrArg (fun A : Set ℝ => f '' A) himage)

end LiZhongQC

