import LiZhongQC.Lemmas.QDReflectionAfterHalves
import LiZhongQC.Lemmas.QDReflectionPuncturePoles
import LiZhongQC.Lemmas.QDTransportZero
import LiZhongQC.Lemmas.QDSeamFill
import LiZhongQC.Lemmas.SchottkyCollarFromDouble
import LiZhongQC.Lemmas.QDBoundaryInverseContinuity
open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

/-- (E5) At a real point `t` of the segment the real derivative of `κ|ℝ` is the boundary limit `L` of `κ'`
(mean value inequality on the convex half disc). -/
theorem s31qe_boundary_deriv
    {r : ℝ} (hr : 0 < r) {κ : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    (hcont : ContinuousOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    {t : ℝ} (ht : |t| < r) {L : ℂ}
    (hL : Tendsto (deriv κ) (𝓝[{z : ℂ | ‖z‖ < r ∧ 0 < z.im}] (t : ℂ)) (𝓝 L)) :
    HasDerivAt (fun s : ℝ => κ (s : ℂ)) L t := by
  have hU : IsOpen {z : ℂ | ‖z‖ < r ∧ 0 < z.im} :=
    (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const Complex.continuous_im)
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.1 (hL (Metric.ball_mem_nhds L hc))
  have hδ' : 0 < min δ (r - |t|) := lt_min hδ (by linarith)
  have hδ'δ : min δ (r - |t|) ≤ δ := min_le_left _ _
  have hδ'r : min δ (r - |t|) ≤ r - |t| := min_le_right _ _
  -- the convex open half ball `D` around `t`, inside the open half disc
  have hDU : ∀ z ∈ ball (t : ℂ) (min δ (r - |t|)) ∩ {z : ℂ | 0 < z.im}, ‖z‖ < r ∧ 0 < z.im := by
    intro z hz
    refine ⟨?_, hz.2⟩
    have h1 : ‖z - t‖ < min δ (r - |t|) := by
      have := hz.1
      rwa [mem_ball, dist_eq_norm] at this
    have h2 : ‖z‖ ≤ ‖z - t‖ + ‖(t : ℂ)‖ := by
      calc ‖z‖ = ‖(z - t) + t‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs] at h2
    linarith
  have hDconv : Convex ℝ (ball (t : ℂ) (min δ (r - |t|)) ∩ {z : ℂ | 0 < z.im}) :=
    (convex_ball _ _).inter (convex_halfSpace_im_gt 0)
  have hderiv : ∀ z ∈ ball (t : ℂ) (min δ (r - |t|)) ∩ {z : ℂ | 0 < z.im},
      HasDerivWithinAt (fun w => κ w - L * w) (deriv κ z - L * 1)
        (ball (t : ℂ) (min δ (r - |t|)) ∩ {z : ℂ | 0 < z.im}) z := by
    intro z hz
    have hk : DifferentiableAt ℂ κ z := (hhol z (hDU z hz)).differentiableAt (hU.mem_nhds (hDU z hz))
    exact (hk.hasDerivAt.sub ((hasDerivAt_id' z).const_mul L)).hasDerivWithinAt
  have hbound : ∀ z ∈ ball (t : ℂ) (min δ (r - |t|)) ∩ {z : ℂ | 0 < z.im}, ‖deriv κ z - L * 1‖ ≤ c := by
    intro z hz
    have hz' : z ∈ ball (t : ℂ) δ ∩ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} :=
      ⟨ball_subset_ball hδ'δ hz.1, hDU z hz⟩
    have h0 : deriv κ z ∈ ball L c := hδs hz'
    rw [mul_one, ← dist_eq_norm]
    exact (mem_ball.1 h0).le
  -- approximation of real points from the open half disc
  have hC : ∀ x : ℝ, |x| < r →
      Tendsto (fun η : ℝ => κ ((x : ℂ) + (η : ℂ) * I)) (𝓝[>] 0) (𝓝 (κ x)) := by
    intro x hx
    have hxC : (x : ℂ) ∈ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} :=
      ⟨by rw [Complex.norm_real, Real.norm_eq_abs]; exact hx, by simp⟩
    have hcts : ContinuousAt (fun η : ℝ => (x : ℂ) + (η : ℂ) * I) 0 := by fun_prop
    have hball : {z : ℂ | ‖z‖ < r} ∈ 𝓝 ((fun η : ℝ => (x : ℂ) + (η : ℂ) * I) 0) := by
      apply (isOpen_lt continuous_norm continuous_const).mem_nhds
      show ‖(x : ℂ) + ((0 : ℝ) : ℂ) * I‖ < r
      simpa [Real.norm_eq_abs] using hx
    have hpath : Tendsto (fun η : ℝ => (x : ℂ) + (η : ℂ) * I) (𝓝[>] 0)
        (𝓝[{z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im}] (x : ℂ)) := by
      apply tendsto_nhdsWithin_iff.2
      constructor
      · have h0 := hcts.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        simpa using h0
      · filter_upwards [nhdsWithin_le_nhds (hcts.preimage_mem_nhds hball), self_mem_nhdsWithin]
          with η h1 h2
        refine ⟨h1, ?_⟩
        show 0 ≤ ((x : ℂ) + (η : ℂ) * I).im
        have h2' : 0 < η := h2
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
          Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
        exact h2'.le
    exact (hcont x hxC).tendsto.comp hpath
  filter_upwards [Metric.ball_mem_nhds t hδ'] with s hs
  have hst : |s - t| < min δ (r - |t|) := by
    rw [mem_ball, Real.dist_eq] at hs
    exact hs
  have hsr : |s| < r := by
    have := abs_sub_abs_le_abs_sub s t
    linarith
  have hmvt : ∀ η : ℝ, 0 < η → η < min δ (r - |t|) - |s - t| →
      ‖κ ((s : ℂ) + (η : ℂ) * I) - κ ((t : ℂ) + (η : ℂ) * I) - ((s - t : ℝ) : ℂ) * L‖ ≤
        c * |s - t| := by
    intro η hη hη'
    have hIm : ∀ x : ℝ, 0 < ((x : ℂ) + (η : ℂ) * I).im := by
      intro x
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
      exact hη
    have hnI : ‖(η : ℂ) * I‖ = η := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hη.le]
    have ha : (s : ℂ) + (η : ℂ) * I ∈ ball (t : ℂ) (min δ (r - |t|)) ∩ {z : ℂ | 0 < z.im} := by
      refine ⟨?_, hIm s⟩
      rw [mem_ball, dist_eq_norm]
      have he : (s : ℂ) + (η : ℂ) * I - t = ((s - t : ℝ) : ℂ) + (η : ℂ) * I := by push_cast; ring
      rw [he]
      calc ‖((s - t : ℝ) : ℂ) + (η : ℂ) * I‖ ≤ ‖((s - t : ℝ) : ℂ)‖ + ‖(η : ℂ) * I‖ := norm_add_le _ _
        _ = |s - t| + η := by rw [hnI, Complex.norm_real, Real.norm_eq_abs]
        _ < min δ (r - |t|) := by linarith
    have hb : (t : ℂ) + (η : ℂ) * I ∈ ball (t : ℂ) (min δ (r - |t|)) ∩ {z : ℂ | 0 < z.im} := by
      refine ⟨?_, hIm t⟩
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hnI]
      have := abs_nonneg (s - t)
      linarith
    have h := hDconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hb ha
    have hab : (s : ℂ) + (η : ℂ) * I - ((t : ℂ) + (η : ℂ) * I) = ((s - t : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hab, Complex.norm_real, Real.norm_eq_abs] at h
    calc ‖κ ((s : ℂ) + (η : ℂ) * I) - κ ((t : ℂ) + (η : ℂ) * I) - ((s - t : ℝ) : ℂ) * L‖ =
        ‖(κ ((s : ℂ) + (η : ℂ) * I) - L * ((s : ℂ) + (η : ℂ) * I)) -
          (κ ((t : ℂ) + (η : ℂ) * I) - L * ((t : ℂ) + (η : ℂ) * I))‖ := by
          congr 1
          push_cast
          ring
      _ ≤ c * |s - t| := h
  have hlim : Tendsto (fun η : ℝ =>
      ‖κ ((s : ℂ) + (η : ℂ) * I) - κ ((t : ℂ) + (η : ℂ) * I) - ((s - t : ℝ) : ℂ) * L‖) (𝓝[>] 0)
      (𝓝 ‖κ (s : ℂ) - κ (t : ℂ) - ((s - t : ℝ) : ℂ) * L‖) :=
    (((hC s hsr).sub (hC t ht)).sub tendsto_const_nhds).norm
  have hle : ‖κ (s : ℂ) - κ (t : ℂ) - ((s - t : ℝ) : ℂ) * L‖ ≤ c * |s - t| := by
    apply le_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min δ (r - |t|) - |s - t| by linarith)] with η hη
    exact hmvt η hη.1 hη.2
  show ‖κ (s : ℂ) - κ (t : ℂ) - (s - t) • L‖ ≤ c * ‖s - t‖
  rw [Real.norm_eq_abs, Complex.real_smul]
  exact hle

/-- (E4) A `C¹` curve in the frontier through a point `κ τ₀` of the boundary arc has tangent in `ℝ · L`, where `L` is the
boundary limit of `κ'`. -/
theorem s31qe_curve_tangent
    {Jd : Set ℂ} (hJd : IsJordanDomain Jd) (hbd : Bornology.IsBounded Jd)
    {r : ℝ} (hr : 0 < r) {κ : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    (hcont : ContinuousOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hκinj : InjOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hup : MapsTo κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} (closure Jd)ᶜ)
    (hreal : MapsTo κ {z : ℂ | ‖z‖ < r ∧ z.im = 0} (frontier Jd))
    (hlocal : ∃ V : Set ℂ, IsOpen V ∧ κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} = V ∩ Jdᶜ)
    {τ₀ : ℝ} (hτ₀ : |τ₀| < r) {L : ℂ} (hL0 : L ≠ 0)
    (hL : Tendsto (deriv κ) (𝓝[{z : ℂ | ‖z‖ < r ∧ 0 < z.im}] (τ₀ : ℂ)) (𝓝 L))
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : ContDiffOn ℝ 1 γ (Icc a b)) (hγF : γ '' Icc a b ⊆ frontier Jd)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (hγt : γ t₀ = κ (τ₀ : ℂ)) :
    ∃ μ : ℝ, deriv γ t₀ = (μ : ℂ) * L := by
  have hJo : IsOpen Jd := hJd.1
  have hκd := s31qe_boundary_deriv hr hhol hcont hτ₀ hL
  have hIcc : Icc a b ∈ 𝓝 t₀ := Icc_mem_nhds ht₀.1 ht₀.2
  have hγd : HasDerivAt γ (deriv γ t₀) t₀ :=
    ((hγ.differentiableOn one_ne_zero t₀ (Ioo_subset_Icc_self ht₀)).differentiableAt hIcc).hasDerivAt
  have hγc : ContinuousAt γ t₀ := hγd.continuousAt
  have hLn : 0 < ‖L‖ := norm_pos_iff.2 hL0
  have hLne : ‖L‖ ≠ 0 := hLn.ne'
  -- along the segment, `(κ s - κ τ₀) / L` is real up to a small multiple of `‖κ s - κ τ₀‖`
  have hkey : ∀ ε > 0, ∀ᶠ s : ℝ in 𝓝 τ₀,
      |((κ (s : ℂ) - κ (τ₀ : ℂ)) / L).im| ≤ ε * ‖κ (s : ℂ) - κ (τ₀ : ℂ)‖ := by
    intro ε hε
    have hc : 0 < min (‖L‖ / 2) (ε * ‖L‖ ^ 2 / 2) := lt_min (by positivity) (by positivity)
    have hc1 : min (‖L‖ / 2) (ε * ‖L‖ ^ 2 / 2) ≤ ‖L‖ / 2 := min_le_left _ _
    have hc2 : min (‖L‖ / 2) (ε * ‖L‖ ^ 2 / 2) ≤ ε * ‖L‖ ^ 2 / 2 := min_le_right _ _
    filter_upwards [(hasDerivAt_iff_isLittleO.1 hκd).def hc] with s hs
    have hs' : ‖κ (s : ℂ) - κ (τ₀ : ℂ) - ((s - τ₀ : ℝ) : ℂ) * L‖ ≤
        min (‖L‖ / 2) (ε * ‖L‖ ^ 2 / 2) * |s - τ₀| := by
      rw [Complex.real_smul, Real.norm_eq_abs] at hs
      exact hs
    have hDL : (κ (s : ℂ) - κ (τ₀ : ℂ)) / L =
        (κ (s : ℂ) - κ (τ₀ : ℂ) - ((s - τ₀ : ℝ) : ℂ) * L) / L + ((s - τ₀ : ℝ) : ℂ) := by
      rw [sub_div (κ (s : ℂ) - κ (τ₀ : ℂ)), mul_div_assoc, div_self hL0, mul_one]
      ring
    have him : ((κ (s : ℂ) - κ (τ₀ : ℂ)) / L).im =
        ((κ (s : ℂ) - κ (τ₀ : ℂ) - ((s - τ₀ : ℝ) : ℂ) * L) / L).im := by
      rw [hDL, Complex.add_im, Complex.ofReal_im, add_zero]
    have h1 : |((κ (s : ℂ) - κ (τ₀ : ℂ) - ((s - τ₀ : ℝ) : ℂ) * L) / L).im| ≤
        min (‖L‖ / 2) (ε * ‖L‖ ^ 2 / 2) * |s - τ₀| / ‖L‖ := by
      calc _ ≤ ‖(κ (s : ℂ) - κ (τ₀ : ℂ) - ((s - τ₀ : ℝ) : ℂ) * L) / L‖ := Complex.abs_im_le_norm _
        _ = ‖κ (s : ℂ) - κ (τ₀ : ℂ) - ((s - τ₀ : ℝ) : ℂ) * L‖ / ‖L‖ := norm_div _ _
        _ ≤ _ := div_le_div_of_nonneg_right hs' hLn.le
    have h2 : |s - τ₀| * ‖L‖ / 2 ≤ ‖κ (s : ℂ) - κ (τ₀ : ℂ)‖ := by
      have h3 : ‖((s - τ₀ : ℝ) : ℂ) * L‖ ≤
          ‖κ (s : ℂ) - κ (τ₀ : ℂ)‖ + ‖κ (s : ℂ) - κ (τ₀ : ℂ) - ((s - τ₀ : ℝ) : ℂ) * L‖ := by
        calc ‖((s - τ₀ : ℝ) : ℂ) * L‖ =
            ‖(κ (s : ℂ) - κ (τ₀ : ℂ)) - (κ (s : ℂ) - κ (τ₀ : ℂ) - ((s - τ₀ : ℝ) : ℂ) * L)‖ := by
              congr 1
              ring
          _ ≤ _ := norm_sub_le _ _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h3
      have h4 : min (‖L‖ / 2) (ε * ‖L‖ ^ 2 / 2) * |s - τ₀| ≤ ‖L‖ / 2 * |s - τ₀| :=
        mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)
      linarith
    rw [him]
    calc _ ≤ min (‖L‖ / 2) (ε * ‖L‖ ^ 2 / 2) * |s - τ₀| / ‖L‖ := h1
      _ ≤ ε * ‖L‖ ^ 2 / 2 * |s - τ₀| / ‖L‖ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc2 (abs_nonneg _)) hLn.le
      _ = ε * (|s - τ₀| * ‖L‖ / 2) := by
          field_simp
      _ ≤ ε * ‖κ (s : ℂ) - κ (τ₀ : ℂ)‖ := mul_le_mul_of_nonneg_left h2 hε.le
  -- near `t₀`, `γ t` is `κ` of a real point close to `τ₀` (inverse continuity, E2)
  obtain ⟨V, hVo, hVeq⟩ := hlocal
  have hτC : (τ₀ : ℂ) ∈ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} :=
    ⟨by rw [Complex.norm_real, Real.norm_eq_abs]; exact hτ₀, by simp⟩
  have hκV : κ (τ₀ : ℂ) ∈ V := by
    have h0 : κ (τ₀ : ℂ) ∈ κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} := mem_image_of_mem κ hτC
    rw [hVeq] at h0
    exact h0.1
  have hrep : ∀ y ∈ V, y ∈ frontier Jd →
      ∃ w : ℂ, (‖w‖ < r ∧ 0 ≤ w.im) ∧ w.im = 0 ∧ κ w = y := by
    intro y hyV hyF
    have hyJ : y ∈ Jdᶜ := by
      have hyF' := hyF
      rw [hJo.frontier_eq] at hyF'
      exact hyF'.2
    have hy : y ∈ κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} := by
      rw [hVeq]
      exact ⟨hyV, hyJ⟩
    obtain ⟨w, hw, rfl⟩ := hy
    refine ⟨w, hw, ?_, rfl⟩
    by_contra hne
    have hpos : 0 < w.im := lt_of_le_of_ne hw.2 (Ne.symm hne)
    exact hup ⟨hw.1, hpos⟩ (frontier_subset_closure hyF)
  have hE2 := s31qe_inverse_continuity hJd hbd hr hhol hcont hκinj hup hreal ⟨V, hVo, hVeq⟩ hτ₀
  have hβ : ∀ ρ > 0, ∀ᶠ t in 𝓝 t₀, ∃ s : ℝ, |s - τ₀| < ρ ∧ κ (s : ℂ) = γ t := by
    intro ρ hρ
    obtain ⟨δ, hδ, hδw⟩ := hE2 ρ hρ
    have hγV : ∀ᶠ t in 𝓝 t₀, γ t ∈ V :=
      hγc.preimage_mem_nhds (hVo.mem_nhds (by rw [hγt]; exact hκV))
    have hγδ : ∀ᶠ t in 𝓝 t₀, ‖γ t - κ (τ₀ : ℂ)‖ < δ := by
      have h0 := hγc.tendsto
      rw [hγt] at h0
      filter_upwards [h0 (Metric.ball_mem_nhds _ hδ)] with t ht
      have ht' : γ t ∈ ball (κ (τ₀ : ℂ)) δ := ht
      rwa [mem_ball, dist_eq_norm] at ht'
    filter_upwards [hγV, hγδ, hIcc] with t h1 h2 h3
    have hF : γ t ∈ frontier Jd := hγF (mem_image_of_mem γ h3)
    obtain ⟨w, hw, hw0, hwe⟩ := hrep (γ t) h1 hF
    have hwr : ((w.re : ℝ) : ℂ) = w := Complex.ext (by rw [Complex.ofReal_re])
      (by rw [Complex.ofReal_im, hw0])
    refine ⟨w.re, ?_, by rw [hwr, hwe]⟩
    have h4 := hδw w hw.1 hw.2 (by rw [hwe]; exact h2)
    rw [← hwr, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h4
    exact h4
  -- `Im (γ' / L) = 0`
  have hslope := hasDerivAt_iff_tendsto_slope.1 hγd
  have hall : ∀ ε > 0, |(deriv γ t₀ / L).im| ≤ ε * ‖deriv γ t₀‖ := by
    intro ε hε
    obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff.1 (hkey ε hε)
    have hev : ∀ᶠ t in 𝓝[≠] t₀, |(slope γ t₀ t / L).im| ≤ ε * ‖slope γ t₀ t‖ := by
      filter_upwards [nhdsWithin_le_nhds (hβ ρ hρ)] with t ht
      obtain ⟨s, hs, hse⟩ := ht
      have hP := hρs (show dist s τ₀ < ρ by rw [Real.dist_eq]; exact hs)
      rw [hse, ← hγt] at hP
      rw [slope_def_module, Complex.real_smul, mul_div_assoc, Complex.im_ofReal_mul, abs_mul, norm_mul,
        Complex.norm_real, Real.norm_eq_abs]
      calc |(t - t₀)⁻¹| * |((γ t - γ t₀) / L).im| ≤ |(t - t₀)⁻¹| * (ε * ‖γ t - γ t₀‖) :=
            mul_le_mul_of_nonneg_left hP (abs_nonneg _)
        _ = ε * (|(t - t₀)⁻¹| * ‖γ t - γ t₀‖) := by ring
    have hT1 : Tendsto (fun t => |(slope γ t₀ t / L).im|) (𝓝[≠] t₀) (𝓝 |(deriv γ t₀ / L).im|) :=
      ((Complex.continuous_im.tendsto _).comp (hslope.div_const L)).abs
    have hT2 : Tendsto (fun t => ε * ‖slope γ t₀ t‖) (𝓝[≠] t₀) (𝓝 (ε * ‖deriv γ t₀‖)) :=
      hslope.norm.const_mul ε
    exact le_of_tendsto_of_tendsto hT1 hT2 hev
  have himz : (deriv γ t₀ / L).im = 0 := by
    by_contra hne
    have hx : 0 < |(deriv γ t₀ / L).im| := abs_pos.2 hne
    have hN := norm_nonneg (deriv γ t₀)
    have h := hall (|(deriv γ t₀ / L).im| / (‖deriv γ t₀‖ + 1)) (by positivity)
    have h' : |(deriv γ t₀ / L).im| / (‖deriv γ t₀‖ + 1) * ‖deriv γ t₀‖ < |(deriv γ t₀ / L).im| := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  refine ⟨(deriv γ t₀ / L).re, ?_⟩
  have h1 : (((deriv γ t₀ / L).re : ℝ) : ℂ) = deriv γ t₀ / L :=
    Complex.ext (by rw [Complex.ofReal_re]) (by rw [Complex.ofReal_im, himz])
  rw [h1, div_mul_cancel₀ _ hL0]

end LiZhongQC
