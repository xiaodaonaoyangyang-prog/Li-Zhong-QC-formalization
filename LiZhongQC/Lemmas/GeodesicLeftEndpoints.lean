import LiZhongQC.Lemmas.GeodesicRadialEndpoints
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC

/-- Negating a real potential preserves its pointwise slope bound. -/
theorem s25ep_neg_potential {ρ G : ℂ → ℝ}
    (hG : ∀ x : ℂ, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ →
      |G y - G x| ≤ (ρ x + ε) * ‖y - x‖) :
    ∀ x : ℂ, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ →
      |(-G y) - (-G x)| ≤ (ρ x + ε) * ‖y - x‖ := by
  intro x ε hε
  obtain ⟨δ, hδ, hb⟩ := hG x ε hε
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  simpa only [neg_sub_neg, abs_sub_comm] using hb y hy

/-- A minimizing segment ending at the apex pays at most the radial cost
of its initial point, by an actual comparison curve in the natural chart. -/
theorem s25ep_minimizing_apex_upper_left (m : ℕ) (hm : 1 ≤ m)
    {φ ζ : ℂ → ℂ} {D W : Set ℂ} {r : ℝ}
    (hW : IsOpen W) (hWD : W ⊆ D) (hζ : IsConformalOnto ζ W (ball (0 : ℂ) r))
    (hq : ∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    (γ : LRCurve) {s t : ℝ} (hs : γ.toFun s ∈ W) (ht : γ.toFun t ∈ W)
    (hz : ζ (γ.toFun t) = 0)
    (hmin : phiSegmentLength φ γ s t = metricDist D (phiDensity φ) (γ.toFun s) (γ.toFun t)) :
    phiSegmentLength φ γ s t ≤ ENNReal.ofReal (‖ζ (γ.toFun s)‖ ^ (((m : ℝ) + 2) / 2)) := by
  obtain ⟨σ, hσ, hlen⟩ := s25e_apex_curve m hm (hζ.mapsTo hs) (hζ.mapsTo ht)
  have hupper : phiSegmentLength φ γ s t ≤
      phiLength (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) σ := by
    rw [hmin]
    apply (s25za_dist_mono hWD (phiDensity φ) (γ.toFun s) (γ.toFun t)).trans
    rw [s25za_chart_distance m hW isOpen_ball hζ hq hs ht]
    exact iInf₂_le σ hσ
  rw [hlen, hz, norm_zero, Real.zero_rpow (by positivity : ((m : ℝ) + 2) / 2 ≠ 0),
    add_zero] at hupper
  exact hupper

/-- Radiality for an actual minimizing segment ending at a zero, obtained
from the same cone equality using negatively oriented potentials. -/
theorem s25ep_minimizing_radial_left (m : ℕ) (hm : 1 ≤ m)
    {φ ζ : ℂ → ℂ} {D W : Set ℂ} {r : ℝ}
    (hW : IsOpen W) (hWD : W ⊆ D) (hζ : IsConformalOnto ζ W (ball (0 : ℂ) r))
    (hq : ∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    (γ : LRCurve) {K : ℝ≥0} {s t : ℝ} (hst : s ≤ t)
    (hK : LipschitzOnWith K γ.toFun (Icc s t)) (hmap : MapsTo γ.toFun (Icc s t) W)
    (hz : ζ (γ.toFun t) = 0) (hb : ζ (γ.toFun s) ≠ 0)
    (hmin : phiSegmentLength φ γ s t = metricDist D (phiDensity φ) (γ.toFun s) (γ.toFun t)) :
    ∀ u ∈ Icc s t, ∃ lam ∈ Icc (0 : ℝ) 1, ζ (γ.toFun u) = lam • ζ (γ.toFun s) := by
  let c : ℝ := ((m : ℝ) + 2) / 2
  have hc : 1 < c := by
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    dsimp only [c]
    linarith
  have hc0 : c ≠ 0 := by linarith
  have hupper := s25ep_minimizing_apex_upper_left m hm hW hWD hζ hq γ
    (hmap ⟨le_rfl, hst⟩) (hmap ⟨hst, le_rfl⟩) hz hmin
  intro u hu
  let a : ℂ := ζ (γ.toFun u)
  let b : ℂ := ζ (γ.toFun s)
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
  have hL := s25za_potential_segment m hW hζ hq
    (G := fun w => -G w)
    (s25ep_neg_potential (fun x ε hε => s25e_cone_pt hc ha (fun w => rfl) x hε)) γ hu.1
    (hK.mono (Icc_subset_Icc le_rfl hu.2)) (hmap.mono (Icc_subset_Icc le_rfl hu.2) (Subset.refl _))
  have hR := s25za_potential_segment m hW hζ hq
    (G := fun w => -‖w‖ ^ c) (s25ep_neg_potential (s25e_radial_hG m)) γ hu.2
    (hK.mono (Icc_subset_Icc hu.1 le_rfl)) (hmap.mono (Icc_subset_Icc hu.1 le_rfl) (Subset.refl _))
  change ENNReal.ofReal (-G a - (-G b)) ≤ _ at hL
  change ENNReal.ofReal (-‖ζ (γ.toFun t)‖ ^ c - (-‖a‖ ^ c)) ≤ _ at hR
  rw [hGa, neg_zero, zero_sub, neg_neg] at hL
  rw [hz, norm_zero, Real.zero_rpow hc0, neg_zero, zero_sub, neg_neg] at hR
  have hsum : ENNReal.ofReal (‖a‖ ^ c + G b) ≤ ENNReal.ofReal (‖b‖ ^ c) := by
    rw [ENNReal.ofReal_add (by positivity) hGb, add_comm]
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

/-- The left radial arm has a C1 parametrization directed outwards from its
zero endpoint. The original increasing time is a continuous decreasing
bijection to radial distance; the tangent at radial parameter zero is nonzero. -/
theorem s25ep_left_reparam {ζ ψ : ℂ → ℂ} {z₀ : ℂ} {r R : ℝ}
    (hR : 0 < R) (hψ0 : ψ 0 = z₀)
    (hinj : InjOn ζ (closedBall z₀ r))
    (han : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ ζ z)
    (hψ : ∀ w ∈ closedBall (0 : ℂ) R, ψ w ∈ ball z₀ r ∧ ζ (ψ w) = w ∧
      AnalyticAt ℂ ψ w ∧ HasDerivAt ψ (deriv ζ (ψ w))⁻¹ w)
    (hd : ∀ w ∈ closedBall (0 : ℂ) R, deriv ζ (ψ w) ≠ 0)
    {f : ℝ → ℂ} {s t : ℝ} (hst : s < t)
    (hf : ContinuousOn f (Icc s t)) (hfi : InjOn f (Icc s t))
    (hmap : MapsTo f (Icc s t) (closedBall z₀ r))
    (hz : ζ (f t) = 0) (hb : ζ (f s) ≠ 0) (hbR : ‖ζ (f s)‖ ≤ R)
    (hrad : ∀ u ∈ Icc s t, ∃ lam ∈ Icc (0 : ℝ) 1, ζ (f u) = lam • ζ (f s)) :
    ∃ (v : ℂ) (B : ℝ) (σ : ℝ → ℂ) (θ : ℝ → ℝ),
      ‖v‖ = 1 ∧ 0 < B ∧ B ≤ R ∧ σ 0 = z₀ ∧ σ B = f s ∧
      ContDiffOn ℝ 1 σ (Icc 0 B) ∧ InjOn σ (Icc 0 B) ∧
      (∀ q ∈ Icc 0 B, HasDerivAt σ (v * (deriv ζ (σ q))⁻¹) q ∧ deriv σ q ≠ 0) ∧
      ContinuousOn θ (Icc s t) ∧ StrictAntiOn θ (Icc s t) ∧
      BijOn θ (Icc s t) (Icc 0 B) ∧ θ s = B ∧ θ t = 0 ∧
      (∀ u ∈ Icc s t, f u = σ (θ u)) ∧ f '' Icc s t = σ '' Icc 0 B := by
  let b : ℂ := ζ (f s)
  let B : ℝ := ‖b‖
  let v : ℂ := B⁻¹ • b
  let θ : ℝ → ℝ := fun u => ‖ζ (f u)‖
  let σ : ℝ → ℂ := fun q => ψ (q • v)
  have hB : 0 < B := norm_pos_iff.2 hb
  have hv : ‖v‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hB.le)]
    exact inv_mul_cancel₀ hB.ne'
  have hθs : θ s = B := rfl
  have hθt : θ t = 0 := by simp only [θ, hz, norm_zero]
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
  have hθmono : StrictAntiOn θ (Icc s t) :=
    hθc.strictAntiOn_of_injOn_Icc hst.le (by rw [hθs, hθt]; exact hB.le) hθi
  have hθsurj : SurjOn θ (Icc s t) (Icc 0 B) := by
    have hi := intermediate_value_Icc' hst.le hθc
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
  · exact (hfun s ⟨le_rfl, hst.le⟩).symm
  · intro q hq
    exact (harc.2.2.2.1 q (hsub hq)).2.2
  · apply Subset.antisymm
    · rintro z ⟨u, hu, rfl⟩
      exact ⟨θ u, hθmap hu, (hfun u hu).symm⟩
    · rintro z ⟨q, hq, rfl⟩
      obtain ⟨u, hu, he⟩ := hθsurj hq
      exact ⟨u, hu, by rw [hfun u hu, he]⟩

/-- The actual left arm at a zero has the same regular C1 endpoint geometry.
The parametrization starts at the zero and runs outwards; its change from the
original parameter is strictly decreasing, and its endpoint derivative is nonzero. -/
theorem s25ep_actual_left_endpoint {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (ht₁ : 0 < t₀) (hzero : φ (γ.toFun t₀) = 0) :
    ∃ (ε B : ℝ) (σ : ℝ → ℂ) (θ : ℝ → ℝ),
      0 < ε ∧ 0 < t₀ - ε ∧ 0 < B ∧ σ 0 = γ.toFun t₀ ∧ σ B = γ.toFun (t₀ - ε) ∧
      ContDiffOn ℝ 1 σ (Icc 0 B) ∧ InjOn σ (Icc 0 B) ∧
      (∀ q ∈ Icc 0 B, DifferentiableAt ℝ σ q ∧ deriv σ q ≠ 0) ∧
      ContinuousOn θ (Icc (t₀ - ε) t₀) ∧ StrictAntiOn θ (Icc (t₀ - ε) t₀) ∧
      BijOn θ (Icc (t₀ - ε) t₀) (Icc 0 B) ∧ θ t₀ = 0 ∧ θ (t₀ - ε) = B ∧
      (∀ u ∈ Icc (t₀ - ε) t₀, γ.toFun u = σ (θ u)) ∧
      γ.toFun '' Icc (t₀ - ε) t₀ = σ '' Icc 0 B := by
  have hz₀ : γ.toFun t₀ ∈ unitDisc := hγ.2.1 ⟨t₀, ht₀, rfl⟩
  obtain ⟨m, ζ, ψ, r, R, hm, hr, hR, hrD, hζ0, hψ0, hinj, hchart, hψ⟩ :=
    s25ep_chart_at_zero hφ hne hz₀ hzero
  obtain ⟨W, hW, hW0, hWr, hζ, -⟩ := s25ep_open_chart hr hR hζ0 hinj
    (fun z hz => (hchart z hz).1) (fun w hw => ⟨(hψ w hw).1, (hψ w hw).2.1⟩)
  have hWD : W ⊆ unitDisc := hWr.trans (ball_subset_closedBall.trans hrD)
  have hq : ∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2 :=
    fun z hz => (hchart z (ball_subset_closedBall (hWr hz))).2.2
  obtain ⟨δ, hδ, hγi, hγW, hmin⟩ := s25ep_minimizing_window hφ hne hγ hp ht₀ hW hW0
  obtain ⟨ε, hε, hεmax⟩ := exists_between (lt_min hδ ht₁)
  have heδ : ε < δ := hεmax.trans_le (min_le_left _ _)
  have he0 : ε < t₀ := hεmax.trans_le (min_le_right _ _)
  have hsub : Icc (t₀ - ε) t₀ ⊆ Icc (0 : ℝ) 1 ∩ Ioo (t₀ - δ) (t₀ + δ) := by
    intro u hu
    exact ⟨⟨by linarith [hu.1], hu.2.trans ht₀.2⟩,
      ⟨by linarith [hu.1], by linarith [hu.2]⟩⟩
  have hst : t₀ - ε < t₀ := by linarith
  have hsI : t₀ - ε ∈ Icc (t₀ - ε) t₀ := ⟨le_rfl, hst.le⟩
  have htI : t₀ ∈ Icc (t₀ - ε) t₀ := ⟨hst.le, le_rfl⟩
  have hmap : MapsTo γ.toFun (Icc (t₀ - ε) t₀) W := hγW.mono hsub (Subset.refl _)
  have hfi : InjOn γ.toFun (Icc (t₀ - ε) t₀) := hγi.mono hsub
  have hb : ζ (γ.toFun (t₀ - ε)) ≠ 0 := by
    intro he
    have hf := hζ.2.1 (hmap hsI) (hmap htI) (he.trans hζ0.symm)
    exact (ne_of_lt hst) (hfi hsI htI hf)
  obtain ⟨K, hK⟩ := hγ.1
  have hKs := hK.mono (hsub.trans inter_subset_left)
  have hrad := s25ep_minimizing_radial_left m hm hW hWD hζ hq γ hst.le hKs hmap hζ0 hb
    (hmin (t₀ - ε) (hsub hsI) t₀ (hsub htI) hst)
  have hbR : ‖ζ (γ.toFun (t₀ - ε))‖ ≤ R := (mem_ball_zero_iff.1 (hζ.mapsTo (hmap hsI))).le
  have hd : ∀ w ∈ closedBall (0 : ℂ) R, deriv ζ (ψ w) ≠ 0 :=
    fun w hw => (hchart _ (ball_subset_closedBall (hψ w hw).1)).2.1
  obtain ⟨v, B, σ, θ, hv, hB, hBR, hσ0, hσB, hσc, hσi, hσd,
    hθc, hθm, hθb, hθB, hθ0, hfun, himage⟩ :=
    s25ep_left_reparam hR hψ0 hinj (fun z hz => (hchart z hz).1) hψ hd
      hst hKs.continuousOn hfi (fun u hu => ball_subset_closedBall (hWr (hmap hu)))
      hζ0 hb hbR hrad
  exact ⟨ε, B, σ, θ, hε, by linarith, hB, hσ0, hσB, hσc, hσi,
    fun q hq => ⟨(hσd q hq).1.differentiableAt, (hσd q hq).2⟩,
    hθc, hθm, hθb, hθ0, hθB, hfun, himage⟩

end LiZhongQC

