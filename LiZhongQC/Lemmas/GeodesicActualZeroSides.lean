import LiZhongQC.Lemmas.GeodesicZeroTangentOrder
import LiZhongQC.Lemmas.GeodesicLeftEndpoints
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC

/-- An injective continuous radial trace determines a continuous injective
nonnegative scalar coordinate. Its value at the apex is zero. -/
theorem s25ep_radial_scalar {F : ℝ → ℂ} {a b : ℝ} {v : ℂ} (hv : v ≠ 0)
    (hF : ContinuousOn F (Icc a b)) (hi : InjOn F (Icc a b))
    (hrad : ∀ x ∈ Icc a b, ∃ lam ∈ Icc (0 : ℝ) 1, F x = lam • v) :
    ∃ ρ : ℝ → ℝ, ContinuousOn ρ (Icc a b) ∧ InjOn ρ (Icc a b) ∧
      (∀ x ∈ Icc a b, 0 ≤ ρ x ∧ F x = (ρ x : ℂ) * v) ∧
      ∀ x ∈ Icc a b, F x = 0 → ρ x = 0 := by
  let ρ : ℝ → ℝ := fun x => ‖F x‖ / ‖v‖
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have he : ∀ x ∈ Icc a b, F x = (ρ x : ℂ) * v := by
    intro x hx
    obtain ⟨lam, hlam, h⟩ := hrad x hx
    have hr : ρ x = lam := by
      dsimp only [ρ]
      rw [h, norm_smul, Real.norm_of_nonneg hlam.1, mul_div_cancel_right₀ _ hvn.ne']
    rw [hr]
    simpa only [Complex.real_smul] using h
  refine ⟨ρ, hF.norm.div_const _, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    apply hi hx hy
    rw [he x hx, he y hy, hxy]
  · intro x hx
    exact ⟨div_nonneg (norm_nonneg _) hvn.le, he x hx⟩
  · intro x hx hz
    change ‖F x‖ / ‖v‖ = 0
    rw [hz, norm_zero, zero_div]

/-- Actual increasing original-time representatives on the two sides of a
minimizing zero contact have the physical corner bounds. Radial chart-line
identities and their scalar monotonicity are derived from the actual traces. -/
theorem s25ep_zero_sides_in_chart {φ ζ : ℂ → ℂ} {z₀ : ℂ} {r R : ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hr : 0 < r) (hζ0 : ζ z₀ = 0)
    (hchart : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 ∧
      φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    {D W : Set ℂ} (hW : IsOpen W) (hWD : W ⊆ D) (hWr : W ⊆ closedBall z₀ r)
    (hζ : IsConformalOnto ζ W (ball (0 : ℂ) R))
    (γ : LRCurve) {K : ℝ≥0} {s t₀ t : ℝ} (hs : s < t₀) (ht : t₀ < t)
    (hK : LipschitzOnWith K γ.toFun (Icc s t)) (hmap : MapsTo γ.toFun (Icc s t) W)
    (hi : InjOn γ.toFun (Icc s t)) (hzero : γ.toFun t₀ = z₀)
    (hmin : ∀ a ∈ Icc s t, ∀ b ∈ Icc s t, a < b →
      phiSegmentLength φ γ a b = metricDist D (phiDensity φ) (γ.toFun a) (γ.toFun b))
    {f g : ℝ → ℂ} {p q : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc 0 1)) (hg : ContDiffOn ℝ 1 g (Icc 0 1))
    (hp : StrictMonoOn p (Icc (0 : ℝ) 1)) (hq : StrictMonoOn q (Icc (0 : ℝ) 1))
    (hpm : MapsTo p (Icc (0 : ℝ) 1) (Icc s t₀)) (hqm : MapsTo q (Icc (0 : ℝ) 1) (Icc t₀ t))
    (hp1 : p 1 = t₀) (hq0 : q 0 = t₀)
    (hfeq : ∀ x ∈ Icc (0 : ℝ) 1, f x = γ.toFun (p x))
    (hgeq : ∀ x ∈ Icc (0 : ℝ) 1, g x = γ.toFun (q x))
    (hfn : derivWithin f (Icc 0 1) 1 ≠ 0) (hgn : derivWithin g (Icc 0 1) 0 ≠ 0) :
    meromorphicOrderAt φ z₀ = (m : ℤ) ∧
      2 * Real.pi / ((m : ℝ) + 2) ≤ |arg (-derivWithin f (Icc 0 1) 1 / derivWithin g (Icc 0 1) 0)| ∧
      2 * Real.pi / ((m : ℝ) + 2) ≤ 2 * Real.pi -
        |arg (-derivWithin f (Icc 0 1) 1 / derivWithin g (Icc 0 1) 0)| ∧
      arg (-derivWithin f (Icc 0 1) 1 / derivWithin g (Icc 0 1) 0) ≠ 0 := by
  have hsI : s ∈ Icc s t := ⟨le_rfl, (hs.trans ht).le⟩
  have h0I : t₀ ∈ Icc s t := ⟨hs.le, ht.le⟩
  have htI : t ∈ Icc s t := ⟨(hs.trans ht).le, le_rfl⟩
  have hsubL : Icc s t₀ ⊆ Icc s t := Icc_subset_Icc le_rfl ht.le
  have hsubR : Icc t₀ t ⊆ Icc s t := Icc_subset_Icc hs.le le_rfl
  have hz : ζ (γ.toFun t₀) = 0 := by rw [hzero]; exact hζ0
  have hu : ζ (γ.toFun s) ≠ 0 := by
    intro he
    have h := hi hsI h0I (hζ.2.1 (hmap hsI) (hmap h0I) (he.trans hz.symm))
    exact (ne_of_lt hs) h
  have hv : ζ (γ.toFun t) ≠ 0 := by
    intro he
    have h := hi htI h0I (hζ.2.1 (hmap htI) (hmap h0I) (he.trans hz.symm))
    exact (ne_of_gt ht) h
  have hcoef : ∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2 :=
    fun z hz' => (hchart z (hWr hz')).2.2
  have hradL := s25ep_minimizing_radial_left m hm hW hWD hζ hcoef γ hs.le
    (hK.mono hsubL) (hmap.mono hsubL (Subset.refl _)) hz hu (hmin s hsI t₀ h0I hs)
  have hradR := s25ep_minimizing_radial m hm hW hWD hζ hcoef γ ht.le
    (hK.mono hsubR) (hmap.mono hsubR (Subset.refl _)) hz hv (hmin t₀ h0I t htI ht)
  have hfW : MapsTo f (Icc (0 : ℝ) 1) W := by
    intro x hx
    rw [hfeq x hx]
    exact hmap (hsubL (hpm hx))
  have hgW : MapsTo g (Icc (0 : ℝ) 1) W := by
    intro x hx
    rw [hgeq x hx]
    exact hmap (hsubR (hqm hx))
  have hζc : ContinuousOn ζ W := hζ.1.continuousOn
  have hfci : InjOn (ζ ∘ f) (Icc (0 : ℝ) 1) := by
    intro x hx y hy he
    have hxy := hζ.2.1 (hfW hx) (hfW hy) he
    rw [hfeq x hx, hfeq y hy] at hxy
    exact hp.injOn hx hy (hi (hsubL (hpm hx)) (hsubL (hpm hy)) hxy)
  have hgci : InjOn (ζ ∘ g) (Icc (0 : ℝ) 1) := by
    intro x hx y hy he
    have hxy := hζ.2.1 (hgW hx) (hgW hy) he
    rw [hgeq x hx, hgeq y hy] at hxy
    exact hq.injOn hx hy (hi (hsubR (hqm hx)) (hsubR (hqm hy)) hxy)
  have hfRad : ∀ x ∈ Icc (0 : ℝ) 1, ∃ lam ∈ Icc (0 : ℝ) 1,
      (ζ ∘ f) x = lam • ζ (γ.toFun s) := by
    intro x hx
    simpa only [Function.comp_apply, hfeq x hx] using hradL (p x) (hpm hx)
  have hgRad : ∀ x ∈ Icc (0 : ℝ) 1, ∃ lam ∈ Icc (0 : ℝ) 1,
      (ζ ∘ g) x = lam • ζ (γ.toFun t) := by
    intro x hx
    simpa only [Function.comp_apply, hgeq x hx] using hradR (q x) (hqm hx)
  obtain ⟨ρ, hρc, hρi, hρline, hρzero⟩ :=
    s25ep_radial_scalar hu (hζc.comp hf.continuousOn hfW) hfci hfRad
  obtain ⟨τ, hτc, hτi, hτline, hτzero⟩ :=
    s25ep_radial_scalar hv (hζc.comp hg.continuousOn hgW) hgci hgRad
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hf1 : f 1 = z₀ := by rw [hfeq 1 h11, hp1, hzero]
  have hg0 : g 0 = z₀ := by rw [hgeq 0 h01, hq0, hzero]
  have hρ1 : ρ 1 = 0 := hρzero 1 h11 (by simp only [Function.comp_apply, hf1, hζ0])
  have hτ0 : τ 0 = 0 := hτzero 0 h01 (by simp only [Function.comp_apply, hg0, hζ0])
  have hρanti : StrictAntiOn ρ (Icc (0 : ℝ) 1) :=
    hρc.strictAntiOn_of_injOn_Icc zero_le_one (by rw [hρ1]; exact (hρline 0 h01).1) hρi
  have hτmono : StrictMonoOn τ (Icc (0 : ℝ) 1) :=
    hτc.strictMonoOn_of_injOn_Icc zero_le_one (by rw [hτ0]; exact (hτline 1 h11).1) hτi
  have hneg : MonotoneOn (fun x => -ρ x) (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    exact neg_le_neg (hρanti.antitoneOn hx hy hxy)
  apply s25ep_actual_zero_corner hm hr hζ0 hchart hW hWD hWr hζ γ hs.le ht.le hK hmap hzero
    hu hv zero_lt_one zero_lt_one (by simp) (by simp) (hmin s hsI t htI (hs.trans ht))
    zero_lt_one zero_lt_one hf1 hg0
    (hf.differentiableOn one_ne_zero 1 h11) (hg.differentiableOn one_ne_zero 0 h01)
    hfn hgn hneg hτmono.monotoneOn (qf := 0) (qg := 0)
  · intro x hx
    simpa only [Function.comp_def, zero_add, Complex.ofReal_neg, neg_mul_neg] using (hρline x hx).2
  · intro x hx
    simpa only [Function.comp_def, zero_add] using (hτline x hx).2

/-- Every genuine interior zero contact has a window in which any two
adjacent regular sides preserving the actual original-time order form a
blunt non-cuspidal corner. The chart, radial traces, scalar monotonicity,
physical tangent angles, and zero order are all supplied by the proof. -/
theorem s25ep_actual_zero_blunt_window {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hpause : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hz : φ (γ.toFun t₀) = 0) :
    ∃ δ > 0, ∃ m : ℕ, 1 ≤ m ∧ meromorphicOrderAt φ (γ.toFun t₀) = (m : ℤ) ∧
      ∀ s ∈ Ioo (t₀ - δ) t₀, ∀ t ∈ Ioo t₀ (t₀ + δ),
      ∀ (n : ℕ) [NeZero n] (side : Fin n → ℝ → ℂ) (j : Fin n) (p q : ℝ → ℝ),
        ContDiffOn ℝ 1 (side (j - 1)) (Icc 0 1) → ContDiffOn ℝ 1 (side j) (Icc 0 1) →
        StrictMonoOn p (Icc (0 : ℝ) 1) → StrictMonoOn q (Icc (0 : ℝ) 1) →
        MapsTo p (Icc (0 : ℝ) 1) (Icc s t₀) → MapsTo q (Icc (0 : ℝ) 1) (Icc t₀ t) →
        p 1 = t₀ → q 0 = t₀ →
        (∀ x ∈ Icc (0 : ℝ) 1, side (j - 1) x = γ.toFun (p x)) →
        (∀ x ∈ Icc (0 : ℝ) 1, side j x = γ.toFun (q x)) →
        derivWithin (side (j - 1)) (Icc 0 1) 1 ≠ 0 → derivWithin (side j) (Icc 0 1) 0 ≠ 0 →
        fx_IsBlunt φ side j ∧
          arg (-derivWithin (side (j - 1)) (Icc 0 1) 1 / derivWithin (side j) (Icc 0 1) 0) ≠ 0 := by
  have htI : t₀ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht₀
  have hzD : γ.toFun t₀ ∈ unitDisc := hγ.2.1 ⟨t₀, htI, rfl⟩
  obtain ⟨m, ζ, ψ, r, R, hm, hr, hR, hrD, hζ0, hψ0, hinj, hchart, hψ⟩ :=
    s25ep_chart_at_zero hφ hne hzD hz
  obtain ⟨W, hW, hW0, hWr, hζ, -⟩ := s25ep_open_chart hr hR hζ0 hinj
    (fun z hz' => (hchart z hz').1) (fun w hw => ⟨(hψ w hw).1, (hψ w hw).2.1⟩)
  have hWcl : W ⊆ closedBall (γ.toFun t₀) r := hWr.trans ball_subset_closedBall
  have hWD : W ⊆ unitDisc := hWcl.trans hrD
  obtain ⟨η, hη, hi, hmap, hmin⟩ := s25ep_minimizing_window hφ hne hγ hpause htI hW hW0
  let δ : ℝ := min η (min t₀ (1 - t₀))
  have hδ : 0 < δ := lt_min hη (lt_min ht₀.1 (sub_pos.2 ht₀.2))
  have hδη : δ ≤ η := min_le_left _ _
  have hδ0 : δ ≤ t₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 - t₀ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ, m, hm, s25ep_natural_chart_order hr hζ0 hchart, ?_⟩
  intro s hs t ht n inst side j p q hf hg hp hq hpm hqm hp1 hq0 hfeq hgeq hfn hgn
  have hst : s < t := hs.2.trans ht.1
  have hsub : Icc s t ⊆ Icc (0 : ℝ) 1 ∩ Ioo (t₀ - η) (t₀ + η) := by
    intro x hx
    exact ⟨⟨by linarith [hs.1, hx.1], by linarith [ht.2, hx.2]⟩,
      ⟨by linarith [hs.1, hx.1], by linarith [ht.2, hx.2]⟩⟩
  obtain ⟨K, hK⟩ := hγ.1
  have hmins : ∀ a ∈ Icc s t, ∀ b ∈ Icc s t, a < b →
      phiSegmentLength φ γ a b = metricDist unitDisc (phiDensity φ) (γ.toFun a) (γ.toFun b) := by
    intro a ha b hb hab
    exact hmin a (hsub ha) b (hsub hb) hab
  obtain ⟨hord, hlo, hhi, hnc⟩ := s25ep_zero_sides_in_chart hm hr hζ0 hchart hW hWD hWcl hζ
    γ hs.2 ht.1 (hK.mono (hsub.trans inter_subset_left)) (hmap.mono hsub (Subset.refl _))
    (hi.mono hsub) rfl hmins hf hg hp hq hpm hqm hp1 hq0 hfeq hgeq hfn hgn
  have hstart : side j 0 = γ.toFun t₀ := by
    rw [hgeq 0 ⟨le_rfl, zero_le_one⟩, hq0]
  refine ⟨s25gb_blunt_of_angle j m ?_ hlo hhi, hnc⟩
  rwa [hstart]

end LiZhongQC

