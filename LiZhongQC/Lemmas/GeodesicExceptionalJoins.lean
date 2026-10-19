import LiZhongQC.Lemmas.GeodesicRadialRepresentative
import LiZhongQC.Lemmas.GeodesicRegularJoins
import LiZhongQC.Lemmas.GeodesicFlatRadial
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real
noncomputable section
namespace LiZhongQC

/-- Every disc point has one common natural chart of a nonnegative degree.
At a regular point the degree is zero; at a zero it is the actual positive
order. No coordinate choices are tied to either of the two geodesics. -/
theorem s25gb_point_chart {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ unitDisc) :
    ∃ (m : ℕ) (ζ : ℂ → ℂ) (W : Set ℂ) (R : ℝ),
      IsOpen W ∧ z₀ ∈ W ∧ W ⊆ unitDisc ∧
      IsConformalOnto ζ W (ball (0 : ℂ) R) ∧
      (∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2) ∧
      ζ z₀ = 0 ∧ deriv ζ z₀ ≠ 0 := by
  by_cases hz : φ z₀ = 0
  · obtain ⟨m, ζ, ψ, r, R, hm, hr, hR, hrD, hζ0, hψ0, hinj, hchart, hψ⟩ :=
      s25ep_chart_at_zero hφ hne hz₀ hz
    obtain ⟨W, hW, hW0, hWr, hζ, _⟩ := s25ep_open_chart hr hR hζ0 hinj
      (fun z hz' => (hchart z hz').1) (fun w hw => ⟨(hψ w hw).1, (hψ w hw).2.1⟩)
    exact ⟨m, ζ, W, R, hW, hW0, hWr.trans (ball_subset_closedBall.trans hrD),
      hζ, fun z hz' => (hchart z (ball_subset_closedBall (hWr hz'))).2.2,
      hζ0, (hchart z₀ (mem_closedBall_self hr.le)).2.1⟩
  · obtain ⟨ζ, r, hr, hrD, hζ0, hinj, han⟩ := psa_chart isOpen_ball hφ hz₀ hz
    obtain ⟨hopen, hψ⟩ := psa_inverse hr hinj (fun z hz' => ⟨(han z hz').1, (han z hz').2.2⟩)
    have h0 : (0 : ℂ) ∈ ζ '' ball z₀ r := ⟨z₀, mem_ball_self hr, hζ0⟩
    obtain ⟨ρ, hρ, hρB⟩ := Metric.isOpen_iff.1 hopen 0 h0
    have hR : 0 < ρ / 2 := by positivity
    have hclosed : closedBall (0 : ℂ) (ρ / 2) ⊆ ζ '' ball z₀ r :=
      (closedBall_subset_ball (by linarith)).trans hρB
    obtain ⟨W, hW, hW0, hWr, hζ, _⟩ :=
      s25ep_open_chart (ψ := Function.invFunOn ζ (ball z₀ r)) hr hR hζ0 hinj
        (fun z hz' => (han z hz').1)
        (fun w hw => ⟨(hψ w (hclosed hw)).1, (hψ w (hclosed hw)).2.1⟩)
    refine ⟨0, ζ, W, ρ / 2, hW, hW0, hWr.trans (ball_subset_closedBall.trans hrD),
      hζ, ?_, hζ0, (han z₀ (mem_closedBall_self hr.le)).2.2⟩
    intro z hz'
    simpa using (han z (ball_subset_closedBall (hWr hz'))).2.1.symm

/-- Common-chart outgoing data at a model center for any regular representative of
an actual geodesic arm. Both original-time orientations are allowed. The
common chart is supplied once and can be used for two different geodesics. -/
theorem s25gb_actual_model_arm {φ ζ : ℂ → ℂ} {W : Set ℂ} {R : ℝ} {m : ℕ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    (hW : IsOpen W) (hWD : W ⊆ unitDisc)
    (hζ : IsConformalOnto ζ W (ball (0 : ℂ) R))
    (hq : ∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hpause : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (htW : γ.toFun t₀ ∈ W)
    (hz : ζ (γ.toFun t₀) = 0) (hζd : deriv ζ (γ.toFun t₀) ≠ 0)
    {σ : ℝ → ℂ} {p : ℝ → ℝ}
    (hσ : ContDiffOn ℝ 1 σ (Icc 0 1))
    (hpc : ContinuousOn p (Icc (0 : ℝ) 1))
    (hpm : StrictMonoOn p (Icc (0 : ℝ) 1) ∨ StrictAntiOn p (Icc (0 : ℝ) 1))
    (hpi : MapsTo p (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)) (hp0 : p 0 = t₀)
    (heq : ∀ t ∈ Icc (0 : ℝ) 1, σ t = γ.toFun (p t))
    (hd : derivWithin σ (Icc 0 1) 0 ≠ 0) :
    ∃ (v : ℂ) (k B : ℝ), ‖v‖ = 1 ∧ 0 < k ∧ 0 < B ∧
      deriv ζ (γ.toFun t₀) * derivWithin σ (Icc 0 1) 0 = (k : ℂ) * v ∧
      ∀ q ∈ Ioo (0 : ℝ) B, ∃ t ∈ Ioo (0 : ℝ) 1,
        σ t ∈ W ∧ ζ (σ t) = (q : ℂ) * v := by
  obtain ⟨δ, hδ, hγi, hγW, hmin⟩ := s25ep_minimizing_window hφ hne hγ hpause ht₀ hW htW
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨e, he, he1, heshape, henear⟩ := s25gb_parameter_shrink hpc h0 hδ
  have hem : ∀ t ∈ Icc (0 : ℝ) 1, e * t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    simpa only [mul_zero, zero_add] using heshape t ht
  let τ : ℝ → ℂ := fun t => σ (e * t)
  let q : ℝ → ℝ := fun t => p (e * t)
  have hqi : ∀ t ∈ Icc (0 : ℝ) 1,
      q t ∈ Icc (0 : ℝ) 1 ∩ Ioo (t₀ - δ) (t₀ + δ) := by
    intro t ht
    have hn := henear t ht
    simp only [mul_zero, zero_add, hp0, abs_lt] at hn
    exact ⟨hpi (hem t ht), ⟨by dsimp [q]; linarith [hn.1], by dsimp [q]; linarith [hn.2]⟩⟩
  have hq0 : q 0 = t₀ := by simpa only [q, mul_zero] using hp0
  have hτeq : ∀ t ∈ Icc (0 : ℝ) 1, τ t = γ.toFun (q t) := fun t ht => heq _ (hem t ht)
  have hτ0 : τ 0 = γ.toFun t₀ := by rw [hτeq 0 h0, hq0]
  have hτW : MapsTo τ (Icc (0 : ℝ) 1) W := by
    intro t ht
    rw [hτeq t ht]
    exact hγW (hqi t ht)
  have hqm : StrictMonoOn q (Icc (0 : ℝ) 1) ∨ StrictAntiOn q (Icc (0 : ℝ) 1) := by
    rcases hpm with hm | hm
    · left
      intro s hs t ht hst
      exact hm (hem s hs) (hem t ht) (mul_lt_mul_of_pos_left hst he)
    · right
      intro s hs t ht hst
      exact hm (hem s hs) (hem t ht) (mul_lt_mul_of_pos_left hst he)
  have hqinj : InjOn q (Icc (0 : ℝ) 1) := hqm.elim StrictMonoOn.injOn StrictAntiOn.injOn
  have hτi : InjOn τ (Icc (0 : ℝ) 1) := by
    intro s hs t ht heq'
    apply hqinj hs ht
    apply hγi (hqi s hs) (hqi t ht)
    rw [← hτeq s hs, ← hτeq t ht]
    exact heq'
  have hτz : ζ (τ 0) = 0 := by rw [hτ0]; exact hz
  have hτb : ζ (τ 1) ≠ 0 := by
    intro heq'
    have heq'' := hζ.2.1 (hτW h1) (hτW h0) (heq'.trans hτz.symm)
    exact one_ne_zero (hτi h1 h0 heq'')
  have hτsmooth : ContDiffOn ℝ 1 τ (Icc 0 1) := by
    simpa only [zero_add] using fx_p2_contDiffOn_affine hσ
      (show ∀ t ∈ Icc (0 : ℝ) 1, 0 + e * t ∈ Icc (0 : ℝ) 1 from fun t ht => by simpa using hem t ht)
  have hder : derivWithin τ (Icc 0 1) 0 = (e : ℂ) * derivWithin σ (Icc 0 1) 0 := by
    simpa only [zero_add, mul_zero] using
      fx_p2_derivWithin_affine (fx_p2_hasDerivWithinAt_of_contDiffOn hσ) zero_lt_one
        (show ∀ t ∈ Icc (0 : ℝ) 1, 0 + e * t ∈ Icc (0 : ℝ) 1 from fun t ht => by simpa using hem t ht) h0
  have hec : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  have hτd : derivWithin τ (Icc 0 1) 0 ≠ 0 := by rw [hder]; exact mul_ne_zero hec hd
  obtain ⟨K, hK⟩ := hγ.1
  have hrad : ∀ t ∈ Icc (0 : ℝ) 1, ∃ c ∈ Icc (0 : ℝ) 1, ζ (τ t) = c • ζ (τ 1) := by
    rcases hqm with hmono | hanti
    · have h01 : q 0 < q 1 := hmono h0 h1 zero_lt_one
      have hsub : Icc (q 0) (q 1) ⊆ Icc (0 : ℝ) 1 ∩ Ioo (t₀ - δ) (t₀ + δ) := by
        intro s hs
        exact ⟨⟨(hqi 0 h0).1.1.trans hs.1, hs.2.trans (hqi 1 h1).1.2⟩,
          ⟨(hqi 0 h0).2.1.trans_le hs.1, hs.2.trans_lt (hqi 1 h1).2.2⟩⟩
      have hr := s25gb_model_minimizing_radial m hW hWD hζ hq γ h01.le
        (hK.mono (hsub.trans inter_subset_left)) (fun s hs => hγW (hsub hs))
        (by rw [← hτeq 0 h0]; exact hτz) (by rw [← hτeq 1 h1]; exact hτb)
        (hmin _ (hqi 0 h0) _ (hqi 1 h1) h01)
      intro t ht
      obtain ⟨c, hc, heq'⟩ := hr (q t) ⟨hmono.monotoneOn h0 ht ht.1, hmono.monotoneOn ht h1 ht.2⟩
      exact ⟨c, hc, by rw [hτeq t ht, hτeq 1 h1]; exact heq'⟩
    · have h10 : q 1 < q 0 := hanti h0 h1 zero_lt_one
      have hsub : Icc (q 1) (q 0) ⊆ Icc (0 : ℝ) 1 ∩ Ioo (t₀ - δ) (t₀ + δ) := by
        intro s hs
        exact ⟨⟨(hqi 1 h1).1.1.trans hs.1, hs.2.trans (hqi 0 h0).1.2⟩,
          ⟨(hqi 1 h1).2.1.trans_le hs.1, hs.2.trans_lt (hqi 0 h0).2.2⟩⟩
      have hr := s25gb_model_minimizing_radial_left m hW hWD hζ hq γ h10.le
        (hK.mono (hsub.trans inter_subset_left)) (fun s hs => hγW (hsub hs))
        (by rw [← hτeq 0 h0]; exact hτz) (by rw [← hτeq 1 h1]; exact hτb)
        (hmin _ (hqi 1 h1) _ (hqi 0 h0) h10)
      intro t ht
      obtain ⟨c, hc, heq'⟩ := hr (q t) ⟨hanti.antitoneOn ht h1 ht.2, hanti.antitoneOn h0 ht ht.1⟩
      exact ⟨c, hc, by rw [hτeq t ht, hτeq 1 h1]; exact heq'⟩
  obtain ⟨v, k, B, hv, hk, hB, hkd, hfill⟩ := s25gb_radial_representative hW hζ.1 hζ.2.1
    hτsmooth hτi hτW hτz hτb (by rw [hτ0]; exact hζd) hτd hrad
  rw [hτ0, hder] at hkd
  refine ⟨v, k / e, B, hv, div_pos hk he, hB, ?_, ?_⟩
  · push_cast
    apply mul_left_cancel₀ hec
    calc
      (e : ℂ) * (deriv ζ (γ.toFun t₀) * derivWithin σ (Icc 0 1) 0)
          = deriv ζ (γ.toFun t₀) * ((e : ℂ) * derivWithin σ (Icc 0 1) 0) := by ring
      _ = (k : ℂ) * v := hkd
      _ = (e : ℂ) * ((k : ℂ) / e * v) := by field_simp <;> ring
  · intro r hr
    obtain ⟨t, ht, htW, hcoord⟩ := hfill r hr
    refine ⟨e * t, ⟨mul_pos he ht.1, ?_⟩, htW, hcoord⟩
    nlinarith [mul_pos he (sub_pos.2 ht.2)]

/-- Actual exceptional-join exclusion at ANY common spatial point,
regular or zero. Common-chart existence and radiality are proved internally.
The only geometric input is the interior-disjointness already produced by
the simple-loop or simple-bigon extractor. Both original-time orientations
are allowed for the outgoing representatives. -/
theorem s25gb_actual_exceptional_join {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ₁ γ₂ : LRCurve} (hγ₁ : IsPhiGeodesic φ unitDisc γ₁)
    (hγ₂ : IsPhiGeodesic φ unitDisc γ₂)
    (hp₁ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ₁.toFun u ≠ γ₁.toFun s)
    (hp₂ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ₂.toFun u ≠ γ₂.toFun s)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (ht₂ : t₂ ∈ Icc (0 : ℝ) 1)
    (hpoint : γ₁.toFun t₁ = γ₂.toFun t₂)
    {F G : ℝ → ℂ} {pF pG : ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (Icc 0 1)) (hG : ContDiffOn ℝ 1 G (Icc 0 1))
    (hcF : ContinuousOn pF (Icc (0 : ℝ) 1)) (hcG : ContinuousOn pG (Icc (0 : ℝ) 1))
    (hmF : StrictMonoOn pF (Icc (0 : ℝ) 1) ∨ StrictAntiOn pF (Icc (0 : ℝ) 1))
    (hmG : StrictMonoOn pG (Icc (0 : ℝ) 1) ∨ StrictAntiOn pG (Icc (0 : ℝ) 1))
    (hiF : MapsTo pF (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hiG : MapsTo pG (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hpF : pF 0 = t₁) (hpG : pG 0 = t₂)
    (heF : ∀ t ∈ Icc (0 : ℝ) 1, F t = γ₁.toFun (pF t))
    (heG : ∀ t ∈ Icc (0 : ℝ) 1, G t = γ₂.toFun (pG t))
    (hdF : derivWithin F (Icc 0 1) 0 ≠ 0)
    (hdG : derivWithin G (Icc 0 1) 0 ≠ 0)
    (hdisj : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Ioo (0 : ℝ) 1, F s ≠ G t) :
    arg (derivWithin F (Icc 0 1) 0 / derivWithin G (Icc 0 1) 0) ≠ 0 := by
  have hzD : γ₁.toFun t₁ ∈ unitDisc := hγ₁.2.1 ⟨t₁, ht₁, rfl⟩
  obtain ⟨m, ζ, W, R, hW, hW0, hWD, hζ, hq, hζ0, hdζ⟩ :=
    s25gb_point_chart hφ hne hzD
  obtain ⟨u, k, A, hu, hk, hA, hvelF, hfillF⟩ :=
    s25gb_actual_model_arm hφ hne hW hWD hζ hq hγ₁ hp₁ ht₁ hW0 hζ0 hdζ
      hF hcF hmF hiF hpF heF hdF
  obtain ⟨v, l, B, hv, hl, hB, hvelG, hfillG⟩ :=
    s25gb_actual_model_arm hφ hne hW hWD hζ hq hγ₂ hp₂ ht₂
      (by rwa [← hpoint]) (by rwa [← hpoint]) (by rwa [← hpoint])
      hG hcG hmG hiG hpG heG hdG
  rw [← hpoint] at hvelG
  have hlc : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hv0 : v ≠ 0 := by intro he; simpa [he] using hv
  have hevel : derivWithin F (Icc 0 1) 0 / derivWithin G (Icc 0 1) 0 =
      ((k / l : ℝ) : ℂ) * (u / v) := by
    have heF' : derivWithin F (Icc 0 1) 0 = (k : ℂ) * u / deriv ζ (γ₁.toFun t₁) :=
      (eq_div_iff hdζ).2 (by simpa only [mul_comm] using hvelF)
    have heG' : derivWithin G (Icc 0 1) 0 = (l : ℂ) * v / deriv ζ (γ₁.toFun t₁) :=
      (eq_div_iff hdζ).2 (by simpa only [mul_comm] using hvelG)
    rw [heF', heG']
    push_cast
    field_simp <;> ring
  rw [hevel, Complex.arg_real_mul _ (div_pos hk hl)]
  intro harg
  have huv : u = v := s25gb_unit_direction_of_arg hu hv harg
  let q : ℝ := min A B / 2
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hqA : q < A := by dsimp [q]; linarith [min_le_left A B]
  have hqB : q < B := by dsimp [q]; linarith [min_le_right A B]
  obtain ⟨s, hs, hsW, hes⟩ := hfillF q ⟨hq0, hqA⟩
  obtain ⟨t, ht, htW, het⟩ := hfillG q ⟨hq0, hqB⟩
  apply hdisj s hs t ht
  apply hζ.2.1 hsW htW
  rw [hes, het, huv]


end LiZhongQC




