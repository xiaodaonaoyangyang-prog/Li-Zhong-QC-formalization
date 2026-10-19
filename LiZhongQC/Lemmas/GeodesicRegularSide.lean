import LiZhongQC.Lemmas.GeodesicSmoothSide
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC

/-- Every actual regular time has a natural-coordinate window in which each
nondegenerate closed subinterval has a smooth straight representative, including
both endpoint derivatives. This is constructed from the local geodesic theorem. -/
theorem s25cv_regular_window {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hz : φ (γ.toFun x) ≠ 0) :
    ∃ δ > 0, ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      x - δ < a → b < x + δ → Nonempty (s25cv_Side φ γ.toFun a b) := by
  obtain ⟨δ, hδ, ζ, ψ, W, u, hu, hW, hWD, han, hinj, hopen, hψ, hwin, hrel⟩ :=
    s25g_local isOpen_ball hφ hγ hp hx hz
  have hu0 : u ≠ 0 := by
    intro he; rw [he, norm_zero] at hu; exact zero_ne_one hu
  refine ⟨δ, hδ, ?_⟩
  intro a b ha hab hb hleft hright
  have hI : ∀ t ∈ Icc a b, t ∈ Icc (0 : ℝ) 1 :=
    fun t ht => ⟨ha.trans ht.1, ht.2.trans hb⟩
  have hγW : ∀ t ∈ Icc a b, γ.toFun t ∈ W := fun t ht =>
    hwin t (hI t ht) (hleft.trans_le ht.1) (ht.2.trans_lt hright)
  have haI : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hbI : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  let θ : ℝ → ℝ := fun t => ((ζ (γ.toFun t) - ζ (γ.toFun a)) / u).re
  have hθa : θ a = 0 := by simp [θ]
  have hdiff : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      θ t - θ s = (phiSegmentLength φ γ s t).toReal := by
    intro s hs t ht hst
    have he := hrel s (hI s hs) t (hI t ht) (hleft.trans_le hs.1) hst
      (ht.2.trans_lt hright)
    have he' : θ t - θ s = ((ζ (γ.toFun t) - ζ (γ.toFun s)) / u).re := by
      dsimp [θ]
      rw [← Complex.sub_re, ← sub_div]
      congr 2
      ring
    rw [he] at he'
    simpa [hu0] using he'
  obtain ⟨M, hM0, hM⟩ := s25g_segLen_bound hφ hγ
  have hθm : StrictMonoOn θ (Icc a b) := by
    intro s hs t ht hst
    have hpos := s25fc_segment_pos hφ hne hγ hp (hI s hs).1 hst (hI t ht).2
    have hfin : phiSegmentLength φ γ s t ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hM s (hI s hs) t (hI t ht) hst.le)
    have h := ENNReal.toReal_pos (ne_of_gt hpos) hfin
    have he := hdiff s hs t ht hst.le
    linarith
  obtain ⟨K, hK⟩ := hγ.1
  have hζγ : ContinuousOn (fun t => ζ (γ.toFun t)) (Icc a b) :=
    (show ContinuousOn ζ W from fun z hz => (han z hz).1.continuousAt.continuousWithinAt).comp
      (hK.continuousOn.mono hI) hγW
  have hθc : ContinuousOn θ (Icc a b) := by
    exact Complex.continuous_re.comp_continuousOn
      ((hζγ.sub continuousOn_const).div_const u)
  let B := θ b
  have hB : 0 < B := by
    have h := hθm haI hbI hab
    simpa only [hθa] using h
  have hθmap : MapsTo θ (Icc a b) (Icc 0 B) := by
    intro t ht
    have hl := hθm.monotoneOn haI ht ht.1
    have hr := hθm.monotoneOn ht hbI ht.2
    constructor
    · simpa only [hθa] using hl
    · exact hr
  have hθsurj : SurjOn θ (Icc a b) (Icc 0 B) := by
    have h := intermediate_value_Icc hab.le hθc
    change Icc 0 (θ b) ⊆ θ '' Icc a b
    simpa only [hθa] using h
  have hline : ∀ t ∈ Icc a b,
      ζ (γ.toFun t) = ζ (γ.toFun a) + (θ t : ℂ) * u := by
    intro t ht
    have he := hrel a (hI a haI) t (hI t ht) hleft ht.1 (ht.2.trans_lt hright)
    have hθt := hdiff a haI t ht ht.1
    rw [hθa, sub_zero] at hθt
    rw [hθt]
    linear_combination he
  let A : ℝ → ℂ := fun q => ζ (γ.toFun a) + (q : ℂ) * u
  let σ : ℝ → ℂ := ψ ∘ A
  have hAimage : ∀ q ∈ Icc (0 : ℝ) B, A q ∈ ζ '' W := by
    intro q hq
    obtain ⟨t, ht, he⟩ := hθsurj hq
    refine ⟨γ.toFun t, hγW t ht, ?_⟩
    dsimp [A]
    rw [← he]
    exact hline t ht
  have hψζ : ∀ z ∈ W, ψ (ζ z) = z := by
    intro z hz
    exact hinj (hψ (ζ z) ⟨z, hz, rfl⟩).1 hz (hψ (ζ z) ⟨z, hz, rfl⟩).2.1
  have htrace : ∀ t ∈ Icc a b, γ.toFun t = σ (θ t) := by
    intro t ht
    change γ.toFun t = ψ (ζ (γ.toFun a) + (θ t : ℂ) * u)
    rw [← hline t ht, hψζ _ (hγW t ht)]
  have hσW : ∀ q ∈ Icc (0 : ℝ) B, σ q ∈ W :=
    fun q hq => (hψ (A q) (hAimage q hq)).1
  have hψan : AnalyticOnNhd ℂ ψ (ζ '' W) := by
    apply DifferentiableOn.analyticOnNhd _ hopen
    intro w hw
    exact (hψ w hw).2.2.differentiableAt.differentiableWithinAt
  have hAc : ContDiff ℝ 1 A := by
    exact contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have hσc : ContDiffOn ℝ 1 σ (Icc 0 B) := by
    intro q hq
    exact (((hψan (A q) (hAimage q hq)).contDiffAt.restrict_scalars ℝ).comp q
      hAc.contDiffAt).contDiffWithinAt
  have hσder : ∀ q ∈ Icc (0 : ℝ) B,
      HasDerivAt σ (u * (deriv ζ (σ q))⁻¹) q := by
    intro q hq
    have hAd : HasDerivAt A u q := by
      simpa only [A, id_eq, Complex.ofReal_one, one_mul] using
        ((hasDerivAt_id q).ofReal_comp.mul_const u).const_add (ζ (γ.toFun a))
    simpa only [σ, Function.comp_def, smul_eq_mul] using (hψ (A q) (hAimage q hq)).2.2.scomp q hAd
  have hσd : ∀ q ∈ Icc (0 : ℝ) B, DifferentiableAt ℝ σ q ∧ deriv σ q ≠ 0 := by
    intro q hq
    exact ⟨(hσder q hq).differentiableAt, by
      rw [(hσder q hq).deriv]
      exact mul_ne_zero hu0 (inv_ne_zero (han _ (hσW q hq)).2.2)⟩
  have hvel : ∀ q ∈ Icc (0 : ℝ) B, φ (σ q) * deriv σ q ^ 2 = u ^ 2 := by
    intro q hq
    have hζ := han _ (hσW q hq)
    rw [(hσder q hq).deriv, ← hζ.2.1]
    field_simp [hζ.2.2]
    <;> ring
  have hrot : u ^ 2 * exp (-(arg (u ^ 2) : ℂ) * I) = (‖u ^ 2‖ : ℂ) := by
    conv_lhs => arg 1; rw [← Complex.norm_mul_exp_arg_mul_I (u ^ 2)]
    rw [mul_assoc, ← Complex.exp_add,
      show (arg (u ^ 2) : ℂ) * I + -(arg (u ^ 2) : ℂ) * I = 0 by ring,
      Complex.exp_zero, mul_one]
  have hstr : IsPhiStraightArc φ σ 0 B := by
    refine ⟨arg (u ^ 2), ?_⟩
    intro q hq
    have hq' := Ioo_subset_Icc_self hq
    refine ⟨(hσd q hq').1, (hσd q hq').2, ?_, ?_⟩
    · rw [hvel q hq']; exact pow_ne_zero 2 hu0
    · rw [hvel q hq', hrot]
      exact Complex.arg_ofReal_of_nonneg (norm_nonneg _)
  exact s25cv_of_model hab hB hstr hσc hσd hθm
    ⟨hθmap, hθm.injOn, hθsurj⟩ hθa rfl htrace

end LiZhongQC

