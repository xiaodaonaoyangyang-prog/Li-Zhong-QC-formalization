import LiZhongQC.Lemmas.GeodesicEndpoints
import LiZhongQC.Lemmas.GeodesicZeroCorner
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
/- Uses ZeroCorner (candidate until the leader reports acceptance). -/

/-- Equality in the triangle inequality with the positive real unit endpoint
forces the other endpoint onto the positive real axis. -/
theorem s25ep_norm_triangle_equality {z : ℂ} (h : 1 + ‖z - 1‖ ≤ ‖z‖) :
    z = (‖z‖ : ℂ) := by
  have hs : ‖z - 1‖ ^ 2 = ‖z‖ ^ 2 - 2 * z.re + 1 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    ring
  have hn : 0 ≤ ‖z‖ - 1 := by linarith [norm_nonneg (z - 1)]
  have hs' : ‖z - 1‖ ^ 2 ≤ (‖z‖ - 1) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hn).2 (by linarith)
  have hre : z.re = ‖z‖ := by nlinarith [Complex.re_le_norm z]
  have him : z.im = 0 := by
    have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [hre] at hz
    nlinarith [sq_nonneg z.im]
  apply Complex.ext
  · simpa using hre
  · simpa using him

/-- The equality case of the explicit cone potential is radial. This is an
algebraic conclusion, not an additional geometric hypothesis on the curve. -/
theorem s25ep_cone_equality {c : ℝ} (hc : 1 < c) {a b : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ‖a‖ ^ c +
      (if Real.cos (Real.pi / c) * ‖b / a‖ ≤ (b / a).re then
        ‖a‖ ^ c * ‖(b / a) ^ (c : ℂ) - 1‖ else ‖a‖ ^ c + ‖b‖ ^ c) ≤ ‖b‖ ^ c) :
    b / a = (‖b / a‖ : ℂ) ∧ ‖a‖ ≤ ‖b‖ := by
  have hc0 : 0 < c := by linarith
  have haN : 0 < ‖a‖ := norm_pos_iff.2 ha
  have haP : 0 < ‖a‖ ^ c := Real.rpow_pos_of_pos haN c
  have hsector : Real.cos (Real.pi / c) * ‖b / a‖ ≤ (b / a).re := by
    by_contra hn
    rw [if_neg hn] at h
    linarith
  rw [if_pos hsector] at h
  have hstrict : Real.cos (Real.pi / c) * ‖b / a‖ < (b / a).re := by
    by_contra hn
    have he := le_antisymm hsector (not_lt.1 hn)
    rw [s25e_cone_boundary_val hc ha hb he] at h
    linarith
  have hnorm : ‖a‖ ^ c * ‖(b / a) ^ (c : ℂ)‖ = ‖b‖ ^ c := by
    rw [Complex.norm_cpow_real, norm_div,
      Real.div_rpow (norm_nonneg b) haN.le, mul_div_cancel₀ _ haP.ne']
  have htriangle : 1 + ‖(b / a) ^ (c : ℂ) - 1‖ ≤ ‖(b / a) ^ (c : ℂ)‖ := by
    apply (mul_le_mul_iff_right₀ haP).1
    nlinarith [hnorm]
  have hreal := s25ep_norm_triangle_equality htriangle
  have hinv := (s25e_cpow_cpow_inv hc (div_ne_zero hb ha)
    (s25e_sector_strict hc (div_ne_zero hb ha) hstrict)).2
  have hq : b / a = ((‖(b / a) ^ (c : ℂ)‖ ^ (1 / c) : ℝ) : ℂ) := by
    rw [hreal, ← Complex.ofReal_cpow (norm_nonneg _)] at hinv
    exact hinv.symm
  have hqnorm : ‖b / a‖ = ‖(b / a) ^ (c : ℂ)‖ ^ (1 / c) := by
    simpa only [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using
      congrArg (fun z : ℂ => ‖z‖) hq
  refine ⟨hq.trans (congrArg (fun x : ℝ => (x : ℂ)) hqnorm.symm), ?_⟩
  have hp : ‖a‖ ^ c ≤ ‖b‖ ^ c := by
    have hn : 0 ≤ ‖a‖ ^ c * ‖(b / a) ^ (c : ℂ) - 1‖ := by positivity
    linarith
  exact (Real.rpow_le_rpow_iff (norm_nonneg a) (norm_nonneg b) hc0).1 hp

/-- A radial comparison curve bounds the length of an actual minimizing
segment whose initial point is the zero of a natural coordinate. -/
theorem s25ep_minimizing_apex_upper (m : ℕ) (hm : 1 ≤ m)
    {φ ζ : ℂ → ℂ} {D W : Set ℂ} {r : ℝ}
    (hW : IsOpen W) (hWD : W ⊆ D) (hζ : IsConformalOnto ζ W (ball (0 : ℂ) r))
    (hq : ∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    (γ : LRCurve) {s t : ℝ} (hs : γ.toFun s ∈ W) (ht : γ.toFun t ∈ W)
    (hz : ζ (γ.toFun s) = 0)
    (hmin : phiSegmentLength φ γ s t = metricDist D (phiDensity φ) (γ.toFun s) (γ.toFun t)) :
    phiSegmentLength φ γ s t ≤ ENNReal.ofReal (‖ζ (γ.toFun t)‖ ^ (((m : ℝ) + 2) / 2)) := by
  obtain ⟨σ, hσ, hlen⟩ := s25e_apex_curve m hm (hζ.mapsTo hs) (hζ.mapsTo ht)
  have hupper : phiSegmentLength φ γ s t ≤
      phiLength (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) σ := by
    rw [hmin]
    apply (s25za_dist_mono hWD (phiDensity φ) (γ.toFun s) (γ.toFun t)).trans
    rw [s25za_chart_distance m hW isOpen_ball hζ hq hs ht]
    exact iInf₂_le σ hσ
  rw [hlen, hz, norm_zero, Real.zero_rpow (by positivity : ((m : ℝ) + 2) / 2 ≠ 0),
    zero_add] at hupper
  exact hupper

/-- Every point of a minimizing segment issuing from a zero lies on the
radial segment to its endpoint. Neither radiality nor any equality case is
assumed: both follow from the actual length comparison. -/
theorem s25ep_minimizing_radial (m : ℕ) (hm : 1 ≤ m)
    {φ ζ : ℂ → ℂ} {D W : Set ℂ} {r : ℝ}
    (hW : IsOpen W) (hWD : W ⊆ D) (hζ : IsConformalOnto ζ W (ball (0 : ℂ) r))
    (hq : ∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    (γ : LRCurve) {K : ℝ≥0} {s t : ℝ} (hst : s ≤ t)
    (hK : LipschitzOnWith K γ.toFun (Icc s t)) (hmap : MapsTo γ.toFun (Icc s t) W)
    (hz : ζ (γ.toFun s) = 0) (hb : ζ (γ.toFun t) ≠ 0)
    (hmin : phiSegmentLength φ γ s t = metricDist D (phiDensity φ) (γ.toFun s) (γ.toFun t)) :
    ∀ u ∈ Icc s t, ∃ lam ∈ Icc (0 : ℝ) 1, ζ (γ.toFun u) = lam • ζ (γ.toFun t) := by
  let c : ℝ := ((m : ℝ) + 2) / 2
  have hc : 1 < c := by
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    dsimp only [c]
    linarith
  have hc0 : c ≠ 0 := by linarith
  have hupper := s25ep_minimizing_apex_upper m hm hW hWD hζ hq γ
    (hmap ⟨le_rfl, hst⟩) (hmap ⟨hst, le_rfl⟩) hz hmin
  intro u hu
  let a : ℂ := ζ (γ.toFun u)
  let b : ℂ := ζ (γ.toFun t)
  by_cases ha : a = 0
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simpa only [zero_smul] using ha⟩
  let G : ℂ → ℝ := fun w => if Real.cos (Real.pi / c) * ‖w / a‖ ≤ (w / a).re then
    ‖a‖ ^ c * ‖(w / a) ^ (c : ℂ) - 1‖ else ‖a‖ ^ c + ‖w‖ ^ c
  have hGa : G a = 0 := by
    have hsec : Real.cos (Real.pi / c) * ‖a / a‖ ≤ (a / a).re := by
      rw [div_self ha]
      simpa using Real.cos_le_one (Real.pi / c)
    simp only [G, if_pos hsec, div_self ha, Complex.one_cpow, sub_self, norm_zero, mul_zero]
  have hGb : 0 ≤ G b := by
    dsimp only [G]
    split_ifs <;> positivity
  have hL := s25za_potential_segment m hW hζ hq (s25e_radial_hG m) γ hu.1
    (hK.mono (Icc_subset_Icc le_rfl hu.2)) (hmap.mono (Icc_subset_Icc le_rfl hu.2) (Subset.refl _))
  have hR := s25za_potential_segment m hW hζ hq
    (G := G) (fun x ε hε => s25e_cone_pt hc ha (fun w => rfl) x hε) γ hu.2
    (hK.mono (Icc_subset_Icc hu.1 le_rfl)) (hmap.mono (Icc_subset_Icc hu.1 le_rfl) (Subset.refl _))
  change ENNReal.ofReal (‖a‖ ^ c - ‖ζ (γ.toFun s)‖ ^ c) ≤ _ at hL
  change ENNReal.ofReal (G b - G a) ≤ _ at hR
  rw [hz, norm_zero, Real.zero_rpow hc0, sub_zero] at hL
  rw [hGa, sub_zero] at hR
  have hsum : ENNReal.ofReal (‖a‖ ^ c + G b) ≤ ENNReal.ofReal (‖b‖ ^ c) := by
    rw [ENNReal.ofReal_add (by positivity) hGb]
    exact (add_le_add hL hR).trans (by rwa [← s25g_segLen_add φ γ hu.1 hu.2])
  have hreal : ‖a‖ ^ c + G b ≤ ‖b‖ ^ c :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hsum
  obtain ⟨hray, hnorm⟩ := s25ep_cone_equality hc ha hb hreal
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hnb : 0 < ‖b‖ := norm_pos_iff.2 hb
  refine ⟨‖a‖ / ‖b‖, ⟨by positivity, (div_le_one hnb).2 hnorm⟩, ?_⟩
  have hba : b = ((‖b‖ / ‖a‖ : ℝ) : ℂ) * a := by
    apply (div_eq_iff ha).1
    simpa only [norm_div] using hray
  change a = (‖a‖ / ‖b‖) • b
  have hcancel : (‖a‖ / ‖b‖) • (((‖b‖ / ‖a‖ : ℝ) : ℂ) * a) = a := by
    rw [← Complex.real_smul, smul_smul]
    have hquot : (‖a‖ / ‖b‖) * (‖b‖ / ‖a‖) = 1 := by
      field_simp [hna.ne', hnb.ne']
    rw [hquot, one_smul]
  exact ((congrArg (fun z : ℂ => (‖a‖ / ‖b‖) • z) hba).trans hcancel).symm

/-- Restrict the closed inverse-chart data to an open source mapping exactly
onto the coordinate ball. This supplies the distance-comparison interface. -/
theorem s25ep_open_chart {ζ ψ : ℂ → ℂ} {z₀ : ℂ} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hζ0 : ζ z₀ = 0)
    (hinj : InjOn ζ (closedBall z₀ r))
    (han : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ ζ z)
    (hψ : ∀ w ∈ closedBall (0 : ℂ) R, ψ w ∈ ball z₀ r ∧ ζ (ψ w) = w) :
    ∃ W : Set ℂ, IsOpen W ∧ z₀ ∈ W ∧ W ⊆ ball z₀ r ∧
      IsConformalOnto ζ W (ball (0 : ℂ) R) ∧
      ∀ z ∈ W, ψ (ζ z) = z := by
  let W : Set ℂ := ball z₀ r ∩ ζ ⁻¹' ball (0 : ℂ) R
  have hWsub : W ⊆ ball z₀ r := inter_subset_left
  have hcont : ContinuousOn ζ (ball z₀ r) := by
    intro z hz
    exact (han z (ball_subset_closedBall hz)).continuousAt.continuousWithinAt
  have hW : IsOpen W := hcont.isOpen_inter_preimage isOpen_ball isOpen_ball
  have hW0 : z₀ ∈ W := ⟨mem_ball_self hr, by simpa only [mem_preimage, hζ0] using mem_ball_self hR⟩
  have himage : ζ '' W = ball (0 : ℂ) R := by
    apply Subset.antisymm
    · rintro w ⟨z, hz, rfl⟩
      exact hz.2
    · intro w hw
      have hi := hψ w (ball_subset_closedBall hw)
      exact ⟨ψ w, ⟨hi.1, by simpa only [mem_preimage, hi.2] using hw⟩, hi.2⟩
  refine ⟨W, hW, hW0, hWsub, ⟨?_, hinj.mono (hWsub.trans ball_subset_closedBall), himage⟩, ?_⟩
  · intro z hz
    exact (han z (ball_subset_closedBall hz.1)).differentiableAt.differentiableWithinAt
  · intro z hz
    have hi := hψ (ζ z) (ball_subset_closedBall hz.2)
    exact hinj (ball_subset_closedBall hi.1) (ball_subset_closedBall hz.1) hi.2

/-- A radial segment of the actual curve has a regular C1 inverse-chart
parametrization. The radius gives a continuous, strictly increasing bijection
of parameter intervals, so the parametrization covers the whole trace. -/
theorem s25ep_right_reparam {ζ ψ : ℂ → ℂ} {z₀ : ℂ} {r R : ℝ}
    (hR : 0 < R) (hψ0 : ψ 0 = z₀)
    (hinj : InjOn ζ (closedBall z₀ r))
    (han : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ ζ z)
    (hψ : ∀ w ∈ closedBall (0 : ℂ) R, ψ w ∈ ball z₀ r ∧ ζ (ψ w) = w ∧
      AnalyticAt ℂ ψ w ∧ HasDerivAt ψ (deriv ζ (ψ w))⁻¹ w)
    (hd : ∀ w ∈ closedBall (0 : ℂ) R, deriv ζ (ψ w) ≠ 0)
    {f : ℝ → ℂ} {s t : ℝ} (hst : s < t)
    (hf : ContinuousOn f (Icc s t)) (hfi : InjOn f (Icc s t))
    (hmap : MapsTo f (Icc s t) (closedBall z₀ r))
    (hz : ζ (f s) = 0) (hb : ζ (f t) ≠ 0) (hbR : ‖ζ (f t)‖ ≤ R)
    (hrad : ∀ u ∈ Icc s t, ∃ lam ∈ Icc (0 : ℝ) 1, ζ (f u) = lam • ζ (f t)) :
    ∃ (v : ℂ) (B : ℝ) (σ : ℝ → ℂ) (θ : ℝ → ℝ),
      ‖v‖ = 1 ∧ 0 < B ∧ B ≤ R ∧ σ 0 = z₀ ∧ σ B = f t ∧
      ContDiffOn ℝ 1 σ (Icc 0 B) ∧ InjOn σ (Icc 0 B) ∧
      (∀ q ∈ Icc 0 B, HasDerivAt σ (v * (deriv ζ (σ q))⁻¹) q ∧ deriv σ q ≠ 0) ∧
      ContinuousOn θ (Icc s t) ∧ StrictMonoOn θ (Icc s t) ∧
      BijOn θ (Icc s t) (Icc 0 B) ∧ θ s = 0 ∧ θ t = B ∧
      (∀ u ∈ Icc s t, f u = σ (θ u)) ∧ f '' Icc s t = σ '' Icc 0 B := by
  let b : ℂ := ζ (f t)
  let B : ℝ := ‖b‖
  let v : ℂ := B⁻¹ • b
  let θ : ℝ → ℝ := fun u => ‖ζ (f u)‖
  let σ : ℝ → ℂ := fun q => ψ (q • v)
  have hB : 0 < B := norm_pos_iff.2 hb
  have hv : ‖v‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hB.le)]
    exact inv_mul_cancel₀ hB.ne'
  have hθs : θ s = 0 := by simp only [θ, hz, norm_zero]
  have hθt : θ t = B := rfl
  have hθc : ContinuousOn θ (Icc s t) := by
    apply ContinuousOn.norm
    apply ContinuousOn.comp _ hf hmap
    intro z hz'
    exact (han z hz').continuousAt.continuousWithinAt
  have hcoord : ∀ u ∈ Icc s t, ζ (f u) = θ u • v := by
    intro u hu
    obtain ⟨lam, hlam, he⟩ := hrad u hu
    have hθ : θ u = lam * B := by
      change ‖ζ (f u)‖ = lam * B
      rw [he, norm_smul, Real.norm_of_nonneg hlam.1]
    rw [hθ]
    change ζ (f u) = (lam * B) • (B⁻¹ • b)
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hB.ne', mul_one]
    exact he
  have hθmap : MapsTo θ (Icc s t) (Icc 0 B) := by
    intro u hu
    obtain ⟨lam, hlam, he⟩ := hrad u hu
    refine ⟨norm_nonneg _, ?_⟩
    change ‖ζ (f u)‖ ≤ B
    rw [he, norm_smul, Real.norm_of_nonneg hlam.1]
    exact mul_le_of_le_one_left hB.le hlam.2
  have hθi : InjOn θ (Icc s t) := by
    intro u hu w hw he
    apply hfi hu hw
    apply hinj (hmap hu) (hmap hw)
    rw [hcoord u hu, hcoord w hw, he]
  have hθmono : StrictMonoOn θ (Icc s t) :=
    hθc.strictMonoOn_of_injOn_Icc hst.le (by rw [hθs, hθt]; exact hB.le) hθi
  have hθsurj : SurjOn θ (Icc s t) (Icc 0 B) := by
    have hi := intermediate_value_Icc hst.le hθc
    rw [hθs, hθt] at hi
    exact hi
  have harc := s25ep_inverse_radial_arc hR hψ0 hψ hd hv
  have hsub : Icc (0 : ℝ) B ⊆ Icc 0 R := Icc_subset_Icc le_rfl hbR
  have hfun : ∀ u ∈ Icc s t, f u = σ (θ u) := by
    intro u hu
    have hq := hsub (hθmap hu)
    have hi := harc.2.2.2.1 (θ u) hq
    apply hinj (hmap hu) (ball_subset_closedBall hi.1)
    exact (hcoord u hu).trans hi.2.1.symm
  refine ⟨v, B, σ, θ, hv, hB, hbR, harc.1, ?_, harc.2.1.mono hsub,
    harc.2.2.1.mono hsub, ?_, hθc, hθmono, ⟨hθmap, hθi, hθsurj⟩,
    hθs, hθt, hfun, ?_⟩
  · exact (hfun t ⟨hst.le, le_rfl⟩).symm
  · intro q hq
    exact (harc.2.2.2.1 q (hsub hq)).2.2
  · apply Subset.antisymm
    · rintro z ⟨u, hu, rfl⟩
      exact ⟨θ u, hθmap hu, (hfun u hu).symm⟩
    · rintro z ⟨q, hq, rfl⟩
      obtain ⟨u, hu, he⟩ := hθsurj hq
      exact ⟨u, hu, by rw [hfun u hu, he]⟩

/-- A common injective minimizing window lies in any prescribed open
neighborhood of an actual point of the non-pausing geodesic. -/
theorem s25ep_minimizing_window {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) {W : Set ℂ}
    (hW : IsOpen W) (hW0 : γ.toFun t₀ ∈ W) :
    ∃ δ > 0, InjOn γ.toFun (Icc (0 : ℝ) 1 ∩ Ioo (t₀ - δ) (t₀ + δ)) ∧
      MapsTo γ.toFun (Icc (0 : ℝ) 1 ∩ Ioo (t₀ - δ) (t₀ + δ)) W ∧
      ∀ s ∈ Icc (0 : ℝ) 1 ∩ Ioo (t₀ - δ) (t₀ + δ),
      ∀ t ∈ Icc (0 : ℝ) 1 ∩ Ioo (t₀ - δ) (t₀ + δ), s < t →
        phiSegmentLength φ γ s t = metricDist unitDisc (phiDensity φ) (γ.toFun s) (γ.toFun t) := by
  obtain ⟨δi, hδi, hi⟩ := s25fc_locally_injective hφ hne hγ hp ht₀
  obtain ⟨δm, hδm, hm⟩ := hγ.2.2 t₀ ht₀
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hW (γ.toFun t₀) hW0
  obtain ⟨K, hK⟩ := hγ.1
  obtain ⟨η, hη, hclose⟩ := Metric.continuousWithinAt_iff.1 (hK.continuousOn t₀ ht₀) r hr
  let δ := min δi (min δm η)
  have hδ : 0 < δ := lt_min hδi (lt_min hδm hη)
  have hdi : δ ≤ δi := min_le_left _ _
  have hdm : δ ≤ δm := (min_le_right _ _).trans (min_le_left _ _)
  have hdη : δ ≤ η := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ, hi.mono ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨ht.1, ⟨by linarith [ht.2.1], by linarith [ht.2.2]⟩⟩
  · intro t ht
    apply hrW
    apply mem_ball.2
    apply hclose ht.1
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.2.1], by linarith [ht.2.2]⟩
  · intro s hs t ht hst
    exact hm s hs.1 t ht.1 (by linarith [hs.2.1]) hst (by linarith [ht.2.2])

/-- The actual right arm at a zero admits a regular C1 parametrization, with
a continuous increasing change of parameter and the same complete trace.
In particular its endpoint tangent is nonzero. -/
theorem s25ep_actual_right_endpoint {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (ht₁ : t₀ < 1) (hzero : φ (γ.toFun t₀) = 0) :
    ∃ (ε B : ℝ) (σ : ℝ → ℂ) (θ : ℝ → ℝ),
      0 < ε ∧ t₀ + ε < 1 ∧ 0 < B ∧ σ 0 = γ.toFun t₀ ∧ σ B = γ.toFun (t₀ + ε) ∧
      ContDiffOn ℝ 1 σ (Icc 0 B) ∧ InjOn σ (Icc 0 B) ∧
      (∀ q ∈ Icc 0 B, DifferentiableAt ℝ σ q ∧ deriv σ q ≠ 0) ∧
      ContinuousOn θ (Icc t₀ (t₀ + ε)) ∧ StrictMonoOn θ (Icc t₀ (t₀ + ε)) ∧
      BijOn θ (Icc t₀ (t₀ + ε)) (Icc 0 B) ∧ θ t₀ = 0 ∧ θ (t₀ + ε) = B ∧
      (∀ u ∈ Icc t₀ (t₀ + ε), γ.toFun u = σ (θ u)) ∧
      γ.toFun '' Icc t₀ (t₀ + ε) = σ '' Icc 0 B := by
  have hz₀ : γ.toFun t₀ ∈ unitDisc := hγ.2.1 ⟨t₀, ht₀, rfl⟩
  obtain ⟨m, ζ, ψ, r, R, hm, hr, hR, hrD, hζ0, hψ0, hinj, hchart, hψ⟩ :=
    s25ep_chart_at_zero hφ hne hz₀ hzero
  obtain ⟨W, hW, hW0, hWr, hζ, -⟩ := s25ep_open_chart hr hR hζ0 hinj
    (fun z hz => (hchart z hz).1) (fun w hw => ⟨(hψ w hw).1, (hψ w hw).2.1⟩)
  have hWD : W ⊆ unitDisc := hWr.trans (ball_subset_closedBall.trans hrD)
  have hq : ∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2 :=
    fun z hz => (hchart z (ball_subset_closedBall (hWr hz))).2.2
  obtain ⟨δ, hδ, hγi, hγW, hmin⟩ := s25ep_minimizing_window hφ hne hγ hp ht₀ hW hW0
  obtain ⟨ε, hε, hεmax⟩ := exists_between (lt_min hδ (sub_pos.2 ht₁))
  have heδ : ε < δ := hεmax.trans_le (min_le_left _ _)
  have he1 : ε < 1 - t₀ := hεmax.trans_le (min_le_right _ _)
  have hsub : Icc t₀ (t₀ + ε) ⊆ Icc (0 : ℝ) 1 ∩ Ioo (t₀ - δ) (t₀ + δ) := by
    intro u hu
    exact ⟨⟨ht₀.1.trans hu.1, by linarith [hu.2]⟩,
      ⟨by linarith [hu.1], by linarith [hu.2]⟩⟩
  have hst : t₀ < t₀ + ε := by linarith
  have hsI : t₀ ∈ Icc t₀ (t₀ + ε) := ⟨le_rfl, hst.le⟩
  have htI : t₀ + ε ∈ Icc t₀ (t₀ + ε) := ⟨hst.le, le_rfl⟩
  have hmap : MapsTo γ.toFun (Icc t₀ (t₀ + ε)) W := hγW.mono hsub (Subset.refl _)
  have hfi : InjOn γ.toFun (Icc t₀ (t₀ + ε)) := hγi.mono hsub
  have hb : ζ (γ.toFun (t₀ + ε)) ≠ 0 := by
    intro he
    have hf := hζ.2.1 (hmap htI) (hmap hsI) (he.trans hζ0.symm)
    exact (ne_of_gt hst) (hfi htI hsI hf)
  obtain ⟨K, hK⟩ := hγ.1
  have hKs := hK.mono (hsub.trans inter_subset_left)
  have hrad := s25ep_minimizing_radial m hm hW hWD hζ hq γ hst.le hKs hmap hζ0 hb
    (hmin t₀ (hsub hsI) (t₀ + ε) (hsub htI) hst)
  have hbR : ‖ζ (γ.toFun (t₀ + ε))‖ ≤ R := (mem_ball_zero_iff.1 (hζ.mapsTo (hmap htI))).le
  have hd : ∀ w ∈ closedBall (0 : ℂ) R, deriv ζ (ψ w) ≠ 0 :=
    fun w hw => (hchart _ (ball_subset_closedBall (hψ w hw).1)).2.1
  obtain ⟨v, B, σ, θ, hv, hB, hBR, hσ0, hσB, hσc, hσi, hσd,
    hθc, hθm, hθb, hθ0, hθB, hfun, himage⟩ :=
    s25ep_right_reparam hR hψ0 hinj (fun z hz => (hchart z hz).1) hψ hd
      hst hKs.continuousOn hfi (fun u hu => ball_subset_closedBall (hWr (hmap hu)))
      hζ0 hb hbR hrad
  exact ⟨ε, B, σ, θ, hε, by linarith, hB, hσ0, hσB, hσc, hσi,
    fun q hq => ⟨(hσd q hq).1.differentiableAt, (hσd q hq).2⟩,
    hθc, hθm, hθb, hθ0, hθB, hfun, himage⟩
end LiZhongQC

