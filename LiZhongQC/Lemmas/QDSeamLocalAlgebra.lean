import LiZhongQC.Lemmas.QDReflectionAfterHalves
open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

/-- A holomorphic coordinate `wc` of the double, read through a preferred chart `x`, is complex
differentiable. -/
theorem s31qi_coord_diff {Xd : ClosedRS.{u}} (wc : OpenPartialHomeomorph Xd.carrier ℂ)
    (hmd : ∀ p ∈ wc.source, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) wc p) (x : Xd.carrier) {w : ℂ}
    (hw : w ∈ (chartAt ℂ x).target) (hs : (chartAt ℂ x).symm w ∈ wc.source) :
    DifferentiableAt ℂ (fun w' => wc ((chartAt ℂ x).symm w')) w := by
  have h := ((s23_mdifferentiableAt_iff (x := x) (p := (chartAt ℂ x).symm w)
    (y := wc ((chartAt ℂ x).symm w)) ((chartAt ℂ x).map_target hw)
    (by simp [chartAt_self_eq])).1 (hmd _ hs)).2
  rw [(chartAt ℂ x).right_inv hw] at h
  simpa [chartAt_self_eq] using h

section SeamLocalAlgebra
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
  [Nonempty S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ}
  (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
  {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
  (hd : IsSchottkyDouble F Xd J ιd Pd)

/-- The actual mirror coefficient, read in any chart `a` of `F.X` containing the returned point. -/
theorem s31qi_mirror_local {qF : F.X.carrier → ℂ → ℂ} (hq : IsDiffFamily 2 0 qF)
    (x : Xd.carrier) (a : F.X.carrier) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target)
    (hp : (chartAt ℂ x).symm z ∈ range (J ∘ ιd))
    (ha : s31qr_halfReturn F hd (J ((chartAt ℂ x).symm z)) ∈ (chartAt ℂ a).source) :
    s31qr_mirrorData F hd qF x z =
      conj (qF a (chartAt ℂ a (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm z))))) *
        deriv (fun w => conj (chartAt ℂ a
          (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))) z ^ 2 := by
  classical
  have htr : J ((chartAt ℂ x).symm z) ∈ range ιd :=
    (s31qr_mirror_membership F hd ((chartAt ℂ x).symm z)).2 hp
  have hRt : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (s31qr_halfReturn F hd)
      (J ((chartAt ℂ x).symm z)) := s31qr_halfReturn_holomorphic F hd htr
  obtain ⟨b, hb⟩ : ∃ b, b = s31qr_halfReturn F hd (J ((chartAt ℂ x).symm z)) := ⟨_, rfl⟩
  rw [← hb] at ha ⊢
  have hbt : chartAt ℂ b b ∈ (chartAt ℂ b).target :=
    (chartAt ℂ b).map_source (mem_chart_source ℂ b)
  have hbi : (chartAt ℂ b).symm (chartAt ℂ b b) = b := (chartAt ℂ b).left_inv (mem_chart_source ℂ b)
  have hl : qF b (chartAt ℂ b b) =
      qF a (chartAt ℂ a b) * deriv (chartTransition a b) (chartAt ℂ b b) ^ 2 := by
    have hh := hq.2 a b (chartAt ℂ b b) hbt (by rw [hbi]; exact ha)
    have he : chartTransition a b (chartAt ℂ b b) = chartAt ℂ a b := by
      change chartAt ℂ a ((chartAt ℂ b).symm (chartAt ℂ b b)) = _
      rw [hbi]
    simpa only [he, zpow_zero, mul_one, zpow_two, pow_two] using hh
  have hτD : DifferentiableAt ℂ (chartTransition a b) (chartAt ℂ b b) :=
    s23_transition_differentiableAt a b hbt (by rw [hbi]; exact ha)
  have hψ : DifferentiableAt ℂ
      (fun w => conj (chartAt ℂ b (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))) z := by
    rw [hb]
    exact s31qr_return_after_involution J hd.involution (s31qr_halfReturn F hd) x hz hRt
  have hJs : ContinuousAt (fun w => J ((chartAt ℂ x).symm w)) z :=
    ContinuousAt.comp (g := J) (f := (chartAt ℂ x).symm) (x := z)
      J.continuous.continuousAt ((chartAt ℂ x).continuousAt_symm hz)
  have hRc : ContinuousAt (fun w => s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))) z :=
    ContinuousAt.comp (g := s31qr_halfReturn F hd) (f := fun w => J ((chartAt ℂ x).symm w))
      (x := z) hRt.continuousAt hJs
  have hbs : b ∈ (chartAt ℂ b).source := mem_chart_source ℂ b
  have he : (fun w => conj (chartAt ℂ a (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))) =ᶠ[𝓝 z]
      (conj ∘ chartTransition a b ∘ conj) ∘
        (fun w => conj (chartAt ℂ b (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))) := by
    have hsrc : (chartAt ℂ b).source ∈ 𝓝 (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm z))) := by
      rw [← hb]
      exact (chartAt ℂ b).open_source.mem_nhds hbs
    filter_upwards [hRc.preimage_mem_nhds hsrc] with w hw
    change conj (chartAt ℂ a (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w)))) =
      conj (chartAt ℂ a ((chartAt ℂ b).symm
        (conj (conj (chartAt ℂ b (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))))))
    rw [Complex.conj_conj, (chartAt ℂ b).left_inv hw]
  have hτc : HasDerivAt (conj ∘ chartTransition a b ∘ conj)
      (conj (deriv (chartTransition a b) (chartAt ℂ b b))) (conj (chartAt ℂ b b)) :=
    hτD.hasDerivAt.conj_conj
  have hψz : conj (chartAt ℂ b (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm z)))) =
      conj (chartAt ℂ b b) := by rw [← hb]
  have hcomp := hτc.comp_of_eq z hψ.hasDerivAt hψz.symm
  have hderiv : deriv (fun w => conj (chartAt ℂ a
      (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))) z =
      conj (deriv (chartTransition a b) (chartAt ℂ b b)) *
        deriv (fun w => conj (chartAt ℂ b
          (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))) z := by
    rw [he.deriv_eq]
    exact hcomp.deriv
  have hval : s31qr_mirrorData F hd qF x z =
      conj (qF b (chartAt ℂ b b)) * deriv (fun w => conj (chartAt ℂ b
        (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))) z ^ 2 := by
    change (if z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm z ∈ range (J ∘ ιd) then
      Complex.conjCLE.toLinearMap
        (qF ((s31qr_halfReturn F hd ∘ J) ((chartAt ℂ x).symm z))
          (chartAt ℂ ((s31qr_halfReturn F hd ∘ J) ((chartAt ℂ x).symm z))
            ((s31qr_halfReturn F hd ∘ J) ((chartAt ℂ x).symm z)))) *
        deriv (fun w => Complex.conjCLE.toLinearMap
          (chartAt ℂ ((s31qr_halfReturn F hd ∘ J) ((chartAt ℂ x).symm z))
            ((s31qr_halfReturn F hd ∘ J) ((chartAt ℂ x).symm w)))) z ^ 2 else 0) = _
    rw [if_pos ⟨hz, hp⟩]
    rw [hb]
    rfl
  rw [hval, hl, hderiv]
  simp only [map_mul, map_pow]
  ring

/-- Chart-form local analytic germ at a fixed point, from the collar data: the statement of the
algebraic half of the seam germ (stub C1), with the collar objects as hypotheses. -/
theorem s31qi_seam_local_algebra
    {qF : F.X.carrier → ℂ → ℂ} (hq : IsDiffFamily 2 0 qF)
    (x : Xd.carrier) {z₀ : ℂ} (hz₀ : z₀ ∈ (chartAt ℂ x).target)
    (wc : OpenPartialHomeomorph Xd.carrier ℂ) {r' : ℝ} (hr' : 0 < r')
    (hp₀ : (chartAt ℂ x).symm z₀ ∈ wc.source) (hwc0 : wc ((chartAt ℂ x).symm z₀) = 0)
    (hmd : ∀ p ∈ wc.source, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) wc p)
    (hJw : ∀ p ∈ wc.source, J p ∈ wc.source ∧ wc (J p) = conj (wc p))
    (hup : ∀ p ∈ wc.source, (0 < (wc p).im ↔ p ∈ range ιd))
    (xF : F.X.carrier) {κ G : ℂ → ℂ}
    (hκd : DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r' ∧ 0 < z.im})
    (hlink : ∀ z : ℂ, ‖z‖ < r' → 0 < z.im → ∃ s : S, ιd s = wc.symm z ∧
      F.ι s ∈ (chartAt ℂ xF).source ∧ κ z = chartAt ℂ xF (F.ι s))
    (hGa : AnalyticOnNhd ℂ G (ball 0 r'))
    (hGs : ∀ z : ℂ, ‖z‖ < r' → G (conj z) = conj (G z))
    (hGe : ∀ z : ℂ, ‖z‖ < r' → 0 < z.im → G z = qF xF (κ z) * deriv κ z ^ 2) :
    ∃ ε : ℝ, 0 < ε ∧ ball z₀ ε ⊆ (chartAt ℂ x).target ∧
      ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball z₀ ε) ∧
        ∀ z ∈ ball z₀ ε,
          ((chartAt ℂ x).symm z ∈ range ιd ∨ (chartAt ℂ x).symm z ∈ range (J ∘ ιd)) →
          H z = s31qr_twoHalfData F hd qF x z := by
  classical
  let τ : ℂ → ℂ := fun w => wc ((chartAt ℂ x).symm w)
  let O : Set Xd.carrier := wc.source ∩ wc ⁻¹' ball 0 r'
  have hO : IsOpen O := wc.isOpen_inter_preimage isOpen_ball
  let W : Set ℂ := (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' O
  have hW : IsOpen W := (chartAt ℂ x).isOpen_inter_preimage_symm hO
  have hz₀W : z₀ ∈ W := by
    refine ⟨hz₀, hp₀, ?_⟩
    rw [Set.mem_preimage, hwc0]
    simpa using hr'
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW z₀ hz₀W
  have hτd : DifferentiableOn ℂ τ W := fun w hw =>
    (s31qi_coord_diff wc hmd x hw.1 hw.2.1).differentiableWithinAt
  have hτa : AnalyticOnNhd ℂ τ W := hτd.analyticOnNhd hW
  have hopenUp : IsOpen {z : ℂ | ‖z‖ < r' ∧ 0 < z.im} :=
    (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const continuous_im)
  have hRopen : IsOpen (range ιd) := hd.embedding.isOpenMap.isOpen_range
  refine ⟨ε, hε, fun z hz => (hεW hz).1, fun w => G (τ w) * deriv τ w ^ 2, ?_, ?_⟩
  · intro w hw
    have hwW := hεW hw
    exact ((hGa (τ w) (mem_ball_zero_iff.2 (mem_ball_zero_iff.1 hwW.2.2))).comp (hτa w hwW)).mul
      ((hτa w hwW).deriv.pow 2)
  · intro z hz hhalf
    have hzW := hεW hz
    have hzt : z ∈ (chartAt ℂ x).target := hzW.1
    have hpw : (chartAt ℂ x).symm z ∈ wc.source := hzW.2.1
    have hu : ‖τ z‖ < r' := mem_ball_zero_iff.1 hzW.2.2
    have hτdz : DifferentiableAt ℂ τ z := s31qi_coord_diff wc hmd x hzt hpw
    show G (τ z) * deriv τ z ^ 2 = _
    rcases hhalf with hpos | hmir
    · -- positive half
      have hupper : 0 < (τ z).im := (hup _ hpw).2 hpos
      obtain ⟨s, hs1, hs2, hs3⟩ := hlink (τ z) hu hupper
      have hs1' : ιd s = (chartAt ℂ x).symm z := hs1.trans (wc.left_inv hpw)
      have hRs : s31qr_halfReturn F hd ((chartAt ℂ x).symm z) = F.ι s := by
        rw [← hs1']
        exact s31qr_halfReturn_image F hd s
      rw [s31qr_twoHalf_on_positive F hd qF x z hpos]
      have hpd : s31qr_positiveData F hd qF x z =
          qF xF (chartAt ℂ xF (s31qr_halfReturn F hd ((chartAt ℂ x).symm z))) *
            deriv (fun w => chartAt ℂ xF
              (s31qr_halfReturn F hd ((chartAt ℂ x).symm w))) z ^ 2 :=
        s31qr_transport_local hq x xF hzt hpos (by rw [hRs]; exact hs2)
          (s31qr_halfReturn_holomorphic F hd hpos)
      let W' : Set ℂ := (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (O ∩ range ιd)
      have hW' : IsOpen W' := (chartAt ℂ x).isOpen_inter_preimage_symm (hO.inter hRopen)
      have hzW' : z ∈ W' := ⟨hzt, hzW.2, hpos⟩
      have hloc : (fun w => chartAt ℂ xF (s31qr_halfReturn F hd ((chartAt ℂ x).symm w))) =ᶠ[𝓝 z]
          fun w => κ (τ w) := by
        filter_upwards [hW'.mem_nhds hzW'] with w hw
        have hwsrc : (chartAt ℂ x).symm w ∈ wc.source := hw.2.1.1
        have hu' : ‖τ w‖ < r' := mem_ball_zero_iff.1 hw.2.1.2
        have hup' : 0 < (τ w).im := (hup _ hwsrc).2 hw.2.2
        obtain ⟨s', hs1', _, hs3'⟩ := hlink (τ w) hu' hup'
        have hs1'' : ιd s' = (chartAt ℂ x).symm w := hs1'.trans (wc.left_inv hwsrc)
        have hR' : s31qr_halfReturn F hd ((chartAt ℂ x).symm w) = F.ι s' := by
          rw [← hs1'']
          exact s31qr_halfReturn_image F hd s'
        change chartAt ℂ xF (s31qr_halfReturn F hd ((chartAt ℂ x).symm w)) = κ (τ w)
        rw [hR', hs3']
      have hκdiff : DifferentiableAt ℂ κ (τ z) :=
        hκd.differentiableAt (hopenUp.mem_nhds ⟨hu, hupper⟩)
      have hderiv : deriv (fun w => chartAt ℂ xF
          (s31qr_halfReturn F hd ((chartAt ℂ x).symm w))) z = deriv κ (τ z) * deriv τ z := by
        rw [hloc.deriv_eq]
        exact (hκdiff.hasDerivAt.comp z hτdz.hasDerivAt).deriv
      have hval : chartAt ℂ xF (s31qr_halfReturn F hd ((chartAt ℂ x).symm z)) = κ (τ z) := by
        rw [hRs, hs3]
      rw [hpd, hval, hderiv, hGe _ hu hupper]
      ring
    · -- mirror half
      have hJp : J ((chartAt ℂ x).symm z) ∈ range ιd :=
        (s31qr_mirror_membership F hd ((chartAt ℂ x).symm z)).2 hmir
      obtain ⟨hJs, hJc⟩ := hJw _ hpw
      have hupp : 0 < (conj (τ z)).im := by
        have h := (hup _ hJs).2 hJp
        rw [hJc] at h
        exact h
      have hu'' : ‖conj (τ z)‖ < r' := by simpa using hu
      obtain ⟨s, hs1, hs2, hs3⟩ := hlink (conj (τ z)) hu'' hupp
      have hs1' : ιd s = J ((chartAt ℂ x).symm z) := by
        rw [hs1]
        have : conj (τ z) = wc (J ((chartAt ℂ x).symm z)) := hJc.symm
        rw [this]
        exact wc.left_inv hJs
      have hRs : s31qr_halfReturn F hd (J ((chartAt ℂ x).symm z)) = F.ι s := by
        rw [← hs1']
        exact s31qr_halfReturn_image F hd s
      rw [s31qr_twoHalf_on_mirror F hd qF x z hmir]
      rw [s31qi_mirror_local F hd hq x xF hzt hmir (by rw [hRs]; exact hs2)]
      let W'' : Set ℂ := (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (O ∩ J ⁻¹' range ιd)
      have hW'' : IsOpen W'' :=
        (chartAt ℂ x).isOpen_inter_preimage_symm (hO.inter (hRopen.preimage J.continuous))
      have hzW'' : z ∈ W'' := ⟨hzt, hzW.2, hJp⟩
      have hloc : (fun w => conj (chartAt ℂ xF
          (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))) =ᶠ[𝓝 z]
          fun w => (conj ∘ κ ∘ conj) (τ w) := by
        filter_upwards [hW''.mem_nhds hzW''] with w hw
        have hwsrc : (chartAt ℂ x).symm w ∈ wc.source := hw.2.1.1
        obtain ⟨hJws, hJwc⟩ := hJw _ hwsrc
        have hu' : ‖conj (τ w)‖ < r' := by simpa using mem_ball_zero_iff.1 hw.2.1.2
        have hup' : 0 < (conj (τ w)).im := by
          have h := (hup _ hJws).2 hw.2.2
          rw [hJwc] at h
          exact h
        obtain ⟨s', hs1', _, hs3'⟩ := hlink (conj (τ w)) hu' hup'
        have hs1'' : ιd s' = J ((chartAt ℂ x).symm w) := by
          rw [hs1']
          have : conj (τ w) = wc (J ((chartAt ℂ x).symm w)) := hJwc.symm
          rw [this]
          exact wc.left_inv hJws
        have hR' : s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w)) = F.ι s' := by
          rw [← hs1'']
          exact s31qr_halfReturn_image F hd s'
        change conj (chartAt ℂ xF (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w)))) =
          conj (κ (conj (τ w)))
        rw [hR', hs3']
      have hκdiff : DifferentiableAt ℂ κ (conj (τ z)) :=
        hκd.differentiableAt (hopenUp.mem_nhds ⟨hu'', hupp⟩)
      have h1 := hκdiff.hasDerivAt.conj_conj
      rw [Complex.conj_conj] at h1
      have h2 := h1.comp z hτdz.hasDerivAt
      have hderiv : deriv (fun w => conj (chartAt ℂ xF
          (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))) z =
          conj (deriv κ (conj (τ z))) * deriv τ z := by
        rw [hloc.deriv_eq]
        exact h2.deriv
      have hval : chartAt ℂ xF (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm z))) =
          κ (conj (τ z)) := by
        rw [hRs, hs3]
      have hGu : G (τ z) = conj (qF xF (κ (conj (τ z)))) * conj (deriv κ (conj (τ z))) ^ 2 := by
        have h := hGs (conj (τ z)) hu''
        rw [Complex.conj_conj] at h
        rw [h, hGe _ hu'' hupp, map_mul, map_pow]
      rw [hval, hderiv, hGu]
      ring

end SeamLocalAlgebra

end LiZhongQC
