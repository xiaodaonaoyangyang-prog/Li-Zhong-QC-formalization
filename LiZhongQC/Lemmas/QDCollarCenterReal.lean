import LiZhongQC.Lemmas.QDReflectionAfterHalves
import LiZhongQC.Lemmas.QDReflectionPuncturePoles
import LiZhongQC.Lemmas.QDTransportZero
import LiZhongQC.Lemmas.QDSeamFill
import LiZhongQC.Lemmas.SchottkyCollarFromDouble

/-!
# (R) Reality at the centre of a collar (round78 S6b, helpers `s31qf_`)

`s31qe_center_real` is proved by unfolding the fixed-point hypothesis at the centre of the chart at `y = E p₀`.  In the
coordinate `φ = chart_y ∘ E ∘ wc⁻¹`, the map `E J E⁻¹` becomes `conj ∘ φ ∘ conj`, so the derivative `μ` of the conjugated
coordinate satisfies `μ φ'(0) = conj φ'(0)`; with `λ = conj λ μ²` this gives `λ φ'(0)² = conj (λ φ'(0)²)`.
-/

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

/-- A number equal to its own conjugate is real. -/
theorem s31qf_im_eq_zero_of_eq_conj {z : ℂ} (h : z = conj z) : z.im = 0 :=
  Complex.conj_eq_iff_im.1 h.symm

/-- The algebra of the centre: from `λ = conj λ · μ²` and `μ φ' = conj φ'`, the number `λ φ'²` is real. -/
theorem s31qf_center_algebra {lam μ φ' : ℂ} (h1 : lam = conj lam * μ ^ 2) (h2 : μ * φ' = conj φ') :
    (lam * φ' ^ 2).im = 0 := by
  apply s31qf_im_eq_zero_of_eq_conj
  calc lam * φ' ^ 2 = conj lam * (μ * φ') ^ 2 := by
        conv_lhs => rw [h1]
        ring
    _ = conj lam * conj φ' ^ 2 := by rw [h2]
    _ = conj (lam * φ' ^ 2) := by simp [map_mul, map_pow]

/-- (R) Reality at the centre of a collar.  `Q` is a differential family of `Fd.X` fixed by the conjugate transport
along `E ∘ J ∘ E⁻¹`; `wc` is a holomorphic chart of `Xd` at the `J`-fixed point `p₀` in which `J` is complex
conjugation.  The coefficient of `Q` at `E p₀`, pulled back to the coordinate `wc`, is real at the centre:
with `y = E p₀`, `φ v = chart_y (E (wc⁻¹ v))`, the number `Q y (chart_y y) * (φ'(0))^2` is real.
(Proof: unfold the fixed-point hypothesis at the centre of the chart at `y`; `H(symm w)` for `H = E J E⁻¹` is, in the
coordinate `φ`, the conjugate coordinate `conj ∘ φ ∘ conj`, so the derivative `μ` of the conjugated coordinate at the centre
satisfies `μ φ'(0) = conj φ'(0)`, and `λ = conj λ μ²` gives `λ φ'(0)² = conj (λ φ'(0)²)`.) -/
theorem s31qe_center_real {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    (hJ : IsAnticonformalInvolution J)
    {Y : ClosedRS.{u}} (E : Xd.carrier ≃ₜ Y.carrier) (hE : IsBiholomorphic (E : Xd.carrier → Y.carrier))
    {Q : Y.carrier → ℂ → ℂ} (hQ : IsDiffFamily 2 0 Q)
    (hfix : s31qr_transportOn univ (fun y : Y.carrier => E (J (E.symm y)))
      Complex.conjCLE.toLinearMap Q = Q)
    {p₀ : Xd.carrier} (hp₀ : J p₀ = p₀)
    {wc : OpenPartialHomeomorph Xd.carrier ℂ} {r : ℝ} (hr : 0 < r)
    (hp₀s : p₀ ∈ wc.source) (hwc0 : wc p₀ = 0) (hwt : wc.target = ball 0 r)
    (hmds : ∀ z ∈ wc.target, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) wc.symm z)
    (hJw : ∀ p ∈ wc.source, J p ∈ wc.source ∧ wc (J p) = conj (wc p)) :
    (Q (E p₀) (chartAt ℂ (E p₀) (E p₀)) *
      deriv (fun v : ℂ => chartAt ℂ (E p₀) (E (wc.symm v))) 0 ^ 2).im = 0 := by
  have _hQ := hQ
  set y : Y.carrier := E p₀ with hy
  set c₁ : ℂ := chartAt ℂ y y with hc₁
  have hc₁t : c₁ ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source (mem_chart_source ℂ y)
  have hsym : (chartAt ℂ y).symm c₁ = y := (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  have hEs : E.symm y = p₀ := E.symm_apply_apply p₀
  have hHy : E (J (E.symm y)) = y := by rw [hEs, hp₀]
  set g : ℂ → ℂ := fun w => conj (chartAt ℂ y (E (J (E.symm ((chartAt ℂ y).symm w))))) with hg
  -- the fixed-point equation at the centre
  have hlam : Q y c₁ = conj (Q y c₁) * deriv g c₁ ^ 2 := by
    have h := congrFun (congrFun hfix y) c₁
    simp only [s31qr_transportOn] at h
    rw [if_pos ⟨hc₁t, mem_univ _⟩] at h
    rw [hsym, hHy] at h
    simpa [hg] using h.symm
  -- the coordinate `φ`
  set φ : ℂ → ℂ := fun v => chartAt ℂ y (E (wc.symm v)) with hφ
  have h0t : (0 : ℂ) ∈ wc.target := by rw [hwt]; exact mem_ball_self hr
  have hwc0' : wc.symm 0 = p₀ := by rw [← hwc0]; exact wc.left_inv hp₀s
  have hφ0 : φ 0 = c₁ := by
    show chartAt ℂ y (E (wc.symm 0)) = c₁
    rw [hwc0']
  -- `E.symm` is holomorphic
  have hEsm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E.symm : Y.carrier → Xd.carrier) := by
    obtain ⟨g', hg', hl, -⟩ := hE.2
    have : (g' : Y.carrier → Xd.carrier) = E.symm := by
      funext z
      have := hl (E.symm z)
      rw [E.apply_symm_apply] at this
      exact this
    rw [← this]; exact hg'
  have hφd : DifferentiableAt ℂ φ 0 := by
    have hm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun v : ℂ => E (wc.symm v)) 0 :=
      (hE.1 (wc.symm 0)).comp 0 (hmds 0 h0t)
    have hsrc : E (wc.symm 0) ∈ (chartAt ℂ y).source := by rw [hwc0']; exact mem_chart_source ℂ y
    have := ((s23_mdifferentiableAt_iff (x := (0 : ℂ)) (p := (0 : ℂ)) (y := y)
      (by simp) hsrc).1 hm).2
    simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, id] at this
    exact this
  -- `g` is holomorphic at the centre: `g = h ∘ σ` near `c₁`
  have hgd : DifferentiableAt ℂ g c₁ := by
    set σ : ℂ → ℂ := fun w => chartAt ℂ p₀ (E.symm ((chartAt ℂ y).symm w)) with hσ
    set h : ℂ → ℂ := fun u => conj (chartAt ℂ y (E (J ((chartAt ℂ p₀).symm u)))) with hh
    have hσd : DifferentiableAt ℂ σ c₁ :=
      s31qr_coordinate_differentiable (H := (E.symm : Y.carrier → Xd.carrier)) y p₀ hc₁t
        (by rw [hsym, hEs]; exact mem_chart_source ℂ p₀) (hEsm _)
    have hp₀t : chartAt ℂ p₀ p₀ ∈ (chartAt ℂ p₀).target := (chartAt ℂ p₀).map_source (mem_chart_source ℂ p₀)
    have hp₀sym : (chartAt ℂ p₀).symm (chartAt ℂ p₀ p₀) = p₀ := (chartAt ℂ p₀).left_inv (mem_chart_source ℂ p₀)
    have hhd : DifferentiableAt ℂ h (chartAt ℂ p₀ p₀) :=
      s31q2_return_after_involution_chart J hJ (E : Xd.carrier → Y.carrier) p₀ y hp₀t
        (by rw [hp₀sym, hp₀]; exact mem_chart_source ℂ y) (hE.1 _)
    have hσc : σ c₁ = chartAt ℂ p₀ p₀ := by simp only [hσ, hsym, hEs]
    have hcomp : DifferentiableAt ℂ (h ∘ σ) c₁ := by
      rw [← hσc] at hhd; exact hhd.comp c₁ hσd
    apply hcomp.congr_of_eventuallyEq
    have hcont : ContinuousAt (fun w => E.symm ((chartAt ℂ y).symm w)) c₁ :=
      E.symm.continuous.continuousAt.comp ((chartAt ℂ y).continuousAt_symm hc₁t)
    have hsrc : (chartAt ℂ p₀).source ∈ 𝓝 (E.symm ((chartAt ℂ y).symm c₁)) := by
      rw [hsym, hEs]; exact (chartAt ℂ p₀).open_source.mem_nhds (mem_chart_source ℂ p₀)
    filter_upwards [hcont.preimage_mem_nhds hsrc] with w hw
    simp only [Function.comp, hσ, hh, hg]
    rw [(chartAt ℂ p₀).left_inv hw]
  -- `g ∘ φ = conj ∘ φ ∘ conj` near `0`
  have hev : (g ∘ φ) =ᶠ[𝓝 0] fun v => conj (φ (conj v)) := by
    have hcont : ContinuousAt (fun v => E (wc.symm v)) 0 :=
      E.continuous.continuousAt.comp (wc.continuousAt_symm h0t)
    have hsrc : (chartAt ℂ y).source ∈ 𝓝 (E (wc.symm 0)) := by
      rw [hwc0']; exact (chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y)
    have hball : ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := ball_mem_nhds _ hr
    filter_upwards [hcont.preimage_mem_nhds hsrc, hball] with v hv hvb
    have hvt : v ∈ wc.target := by rw [hwt]; exact hvb
    have hcv : conj v ∈ wc.target := by
      rw [hwt, mem_ball_zero_iff, Complex.norm_conj]; rwa [mem_ball_zero_iff] at hvb
    obtain ⟨hJs, hJe⟩ := hJw (wc.symm v) (wc.map_target hvt)
    have hJv : J (wc.symm v) = wc.symm (conj v) := by
      rw [wc.right_inv hvt] at hJe
      rw [← hJe, wc.left_inv hJs]
    simp only [Function.comp, hg, hφ]
    rw [(chartAt ℂ y).left_inv hv, E.symm_apply_apply, hJv]
  -- derivatives at `0`
  have h1 : HasDerivAt (g ∘ φ) (deriv g c₁ * deriv φ 0) 0 := by
    have hg' : HasDerivAt g (deriv g c₁) (φ 0) := by rw [hφ0]; exact hgd.hasDerivAt
    exact hg'.comp 0 hφd.hasDerivAt
  have h2 : HasDerivAt (fun v => conj (φ (conj v))) (conj (deriv φ 0)) 0 := by
    have := hφd.hasDerivAt.conj_conj
    rw [map_zero] at this
    exact this
  have hμ : deriv g c₁ * deriv φ 0 = conj (deriv φ 0) := (h1.congr_of_eventuallyEq hev.symm).unique h2
  exact s31qf_center_algebra hlam hμ

end LiZhongQC
