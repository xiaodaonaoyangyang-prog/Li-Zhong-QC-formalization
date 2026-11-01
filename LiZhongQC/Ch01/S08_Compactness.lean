import LiZhongQC.Ch01.S07_GeometricDefinition

/-!
# §8 K 拟共形映射族的紧致性 — Compactness of families of `K`-quasiconformal mappings

* estimate (8.4) (uniform modulus of continuity)        — `eq8_4_equicontinuity_estimate`
* Theorem 8.1 (normality)                               — `thm8_1_normal_family`
* Theorem 8.2 (limits of `K`-q.c. mappings)             — `thm8_2_limit`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real

noncomputable section

namespace LiZhongQC

/-! ### Theorem 8.1 — helpers of piece A -/


/-- **A1.** Area of the off-centre annulus `{r < |z − ζ| < R}` for `0 ≤ r < R`
(`Complex.volume_ball`, `Complex.volume_closedBall`, `measure_diff`). -/
theorem nf_a_volume_annulusAt (ζ : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    volume (annulusAt ζ r R) = ENNReal.ofReal (π * (R ^ 2 - r ^ 2)) := by
  have hRpos : 0 < R := lt_of_le_of_lt hr hrR
  have hset : annulusAt ζ r R = Metric.ball ζ R \ Metric.closedBall ζ r := by
    ext z
    simp only [annulusAt, mem_setOf_eq, Metric.mem_ball, Metric.mem_closedBall, mem_diff,
      dist_eq_norm, not_le]
    tauto
  rw [hset]
  have hsub : Metric.closedBall ζ r ⊆ Metric.ball ζ R := Metric.closedBall_subset_ball hrR
  have hmeas : MeasurableSet (Metric.closedBall ζ r) := Metric.isClosed_closedBall.measurableSet
  have hfin : volume (Metric.closedBall ζ r) ≠ ⊤ := by
    rw [Complex.volume_closedBall]
    finiteness
  rw [measure_diff hsub hmeas.nullMeasurableSet hfin, Complex.volume_ball, Complex.volume_closedBall,
    ← ENNReal.sub_mul (fun _ _ => ENNReal.coe_ne_top),
    ← ENNReal.ofReal_pow hRpos.le, ← ENNReal.ofReal_pow hr,
    ← ENNReal.ofReal_sub _ (sq_nonneg r)]
  have hpi : (↑NNReal.pi : ℝ≥0∞) = ENNReal.ofReal π := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  rw [hpi, ← ENNReal.ofReal_mul (by nlinarith [sq_nonneg r, hrR, hr]), mul_comm]

/-- **A2.** The `ρ`-area over ANY set `B` of the density `1/(2ε)` on `A = annulusAt ζ Δ (ε + Δ)`
is at most `(π/4)(1 + 2Δ/ε)`. -/
theorem nf_a_rhoArea_le (B : Set ℂ) (ζ : ℂ) {Δ ε : ℝ} (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    rhoArea (fun z => (annulusAt ζ Δ (ε + Δ)).indicator
      (fun _ => ENNReal.ofReal (1 / (2 * ε))) z) B ≤
        ENNReal.ofReal (π / 4 * (1 + 2 * Δ / ε)) := by
  set A : Set ℂ := annulusAt ζ Δ (ε + Δ) with hAdef
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / (2 * ε)) with hcdef
  have hAopen : IsOpen A := by
    have heq : A = (fun z : ℂ => ‖z - ζ‖) ⁻¹' Ioo Δ (ε + Δ) := by
      ext z; simp [hAdef, annulusAt, Ioo]
    rw [heq]
    exact (continuous_norm.comp (continuous_id.sub continuous_const)).isOpen_preimage _ isOpen_Ioo
  have hAmeas : MeasurableSet A := hAopen.measurableSet
  unfold rhoArea
  have hpt : ∀ z, (A.indicator (fun _ => c) z) ^ 2 = A.indicator (fun _ => c ^ 2) z := by
    intro z
    by_cases hz : z ∈ A
    · simp [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz]
  calc ∫⁻ z in B, (A.indicator (fun _ => c) z) ^ 2
      = ∫⁻ z in B, A.indicator (fun _ => c ^ 2) z := lintegral_congr hpt
    _ ≤ ∫⁻ z in univ, A.indicator (fun _ => c ^ 2) z := lintegral_mono_set (subset_univ B)
    _ = ∫⁻ z, A.indicator (fun _ => c ^ 2) z := by rw [Measure.restrict_univ]
    _ = ∫⁻ z in A, (c ^ 2 : ℝ≥0∞) := lintegral_indicator hAmeas (fun _ => c ^ 2)
    _ = (c ^ 2) * volume A := setLIntegral_const A (c ^ 2)
    _ = ENNReal.ofReal (π / 4 * (1 + 2 * Δ / ε)) := by
        rw [hcdef, hAdef, nf_a_volume_annulusAt ζ hΔ (by linarith)]
        rw [← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring


/-! ### Theorem 8.1 — helpers of piece B -/

theorem nf_b_hasDerivAt_re_of_hasDerivAt {γ : ℝ → ℂ} {γ' : ℂ} {u : ℝ} (h : HasDerivAt γ γ' u) :
    HasDerivAt (fun v => (γ v).re) γ'.re u := by
  rw [hasDerivAt_iff_isLittleO] at h ⊢
  refine Asymptotics.IsBigO.trans_isLittleO
    (Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun v => ?_)) h
  have e : (γ v).re - (γ u).re - (v - u) • γ'.re = (γ v - γ u - (v - u) • γ').re := by simp
  simp only [one_mul]
  rw [e, Real.norm_eq_abs]
  exact abs_re_le_norm _

theorem nf_b_enorm_sub_le_lintegral {γ : LRCurve} (hγ : γ.IsClosedCurve) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ‖γ.toFun b - γ.toFun a‖ₑ ≤ ∫⁻ t in Ioo a b, ‖deriv γ.toFun t‖ₑ := by
  obtain ⟨K, hKLip, -⟩ := hγ
  rcases eq_or_ne (γ.toFun b) (γ.toFun a) with heq | hne
  · simp [heq]
  set v : ℂ := (γ.toFun b - γ.toFun a) / (‖γ.toFun b - γ.toFun a‖ : ℂ) with hvdef
  have hdne : γ.toFun b - γ.toFun a ≠ 0 := sub_ne_zero.2 hne
  have hnormne : (‖γ.toFun b - γ.toFun a‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.2 hdne
  have hvmul : v * (‖γ.toFun b - γ.toFun a‖ : ℂ) = γ.toFun b - γ.toFun a :=
    div_mul_cancel₀ _ hnormne
  have hvnorm : ‖v‖ = 1 := by
    rw [hvdef, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.2 hdne)
  have hvnormsq : (starRingEnd ℂ) v * v = 1 := by
    rw [mul_comm, mul_conj', hvnorm]; norm_num
  set g : ℝ → ℝ := fun t => ((starRingEnd ℂ) v * γ.toFun t).re with hgdef
  have hgba : g b - g a = ‖γ.toFun b - γ.toFun a‖ := by
    have hthis : (starRingEnd ℂ) v * (γ.toFun b - γ.toFun a) = (‖γ.toFun b - γ.toFun a‖ : ℂ) := by
      conv_lhs => rw [← hvmul]
      rw [← mul_assoc, hvnormsq, one_mul]
    show ((starRingEnd ℂ) v * γ.toFun b).re - ((starRingEnd ℂ) v * γ.toFun a).re = _
    rw [← Complex.sub_re, ← mul_sub, hthis, Complex.ofReal_re]
  have hKIcc : LipschitzOnWith K γ.toFun (Icc (0:ℝ) 1) := hKLip
  have hsub : Icc a b ⊆ Icc (0:ℝ) 1 := Icc_subset_Icc ha hb
  have hKab : LipschitzOnWith K γ.toFun (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact hKIcc.mono hsub
  have hgLip : LipschitzOnWith K g (uIcc a b) := by
    rw [lipschitzOnWith_iff_dist_le_mul] at hKab ⊢
    intro x hx y hy
    calc dist (g x) (g y) ≤ dist (γ.toFun x) (γ.toFun y) := by
          rw [hgdef]
          simp only [Real.dist_eq]
          calc |((starRingEnd ℂ) v * γ.toFun x).re - ((starRingEnd ℂ) v * γ.toFun y).re|
              = |((starRingEnd ℂ) v * (γ.toFun x - γ.toFun y)).re| := by
                rw [← Complex.sub_re, ← mul_sub]
            _ ≤ ‖(starRingEnd ℂ) v * (γ.toFun x - γ.toFun y)‖ := abs_re_le_norm _
            _ = ‖γ.toFun x - γ.toFun y‖ := by
                rw [norm_mul, Complex.norm_conj, hvnorm, one_mul]
            _ = dist (γ.toFun x) (γ.toFun y) := (Complex.dist_eq _ _).symm
      _ ≤ K * dist x y := hKab x hx y hy
  have hftc : ∫ t in a..b, deriv g t = g b - g a :=
    hgLip.absolutelyContinuousOnInterval.integral_deriv_eq_sub
  have hA := LocallyLipschitzOn.ae_differentiableAt_Ioo γ.locallyLipschitzOn
  have hnn : 0 ≤ g b - g a := hgba ▸ norm_nonneg _
  conv_lhs => rw [← ofReal_norm]
  rw [← hgba, ← Real.norm_of_nonneg hnn, ofReal_norm, ← hftc,
    intervalIntegral.integral_of_le hab]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← setLIntegral_congr Ioo_ae_eq_Ioc]
  refine setLIntegral_mono_ae' measurableSet_Ioo ?_
  filter_upwards [hA] with u hu huI
  have hu01 : u ∈ Ioo (0:ℝ) 1 := ⟨ha.trans_lt huI.1, huI.2.trans_le hb⟩
  have hd : HasDerivAt g ((starRingEnd ℂ) v * deriv γ.toFun u).re u :=
    nf_b_hasDerivAt_re_of_hasDerivAt ((hu hu01).hasDerivAt.const_mul ((starRingEnd ℂ) v))
  rw [hd.deriv, ← ofReal_norm]
  calc ENNReal.ofReal |((starRingEnd ℂ) v * deriv γ.toFun u).re|
      ≤ ENNReal.ofReal ‖(starRingEnd ℂ) v * deriv γ.toFun u‖ :=
        ENNReal.ofReal_le_ofReal (abs_re_le_norm _)
    _ = ENNReal.ofReal ‖deriv γ.toFun u‖ := by
        rw [norm_mul, Complex.norm_conj, hvnorm, one_mul]
    _ = ‖deriv γ.toFun u‖ₑ := ofReal_norm _

theorem nf_b_clamp_le_lintegral {γ : LRCurve} (hγ : γ.IsClosedCurve) (ζ : ℂ) {Δ ε : ℝ}
    (hΔ : 0 ≤ Δ) (hε : 0 < ε) {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) :
    ENNReal.ofReal |max Δ (min (ε + Δ) ‖γ.toFun d - ζ‖) - max Δ (min (ε + Δ) ‖γ.toFun c - ζ‖)| ≤
      ∫⁻ t in Ioo c d, (annulusAt ζ Δ (ε + Δ)).indicator (fun _ => (1 : ℝ≥0∞)) (γ.toFun t) *
        ‖deriv γ.toFun t‖ₑ := by
  have hγ' := hγ
  obtain ⟨K, hKLip, -⟩ := hγ
  set r : ℝ → ℝ := fun t => ‖γ.toFun t - ζ‖ with hrdef
  set clamp : ℝ → ℝ := fun x => max Δ (min (ε + Δ) x) with hclampdef
  set α := clamp (r c) with hαdef
  set β := clamp (r d) with hβdef
  have hclampge : ∀ x, Δ ≤ clamp x := fun x => le_max_left _ _
  have hclampleΔε : ∀ x, clamp x ≤ ε + Δ := fun x => by
    rw [hclampdef]
    exact max_le (by linarith) (min_le_left _ _)
  have hrcont : ContinuousOn r (Icc (0:ℝ) 1) := (hKLip.continuousOn.sub continuousOn_const).norm
  -- the key one-sided construction, used for both `α < β` and `β < α`
  have key : ∀ p q : ℝ, p ∈ Icc c d → q ∈ Icc c d → p ≤ q → clamp (r p) < clamp (r q) →
      ENNReal.ofReal (clamp (r q) - clamp (r p)) ≤
        ∫⁻ t in Ioo c d, (annulusAt ζ Δ (ε + Δ)).indicator (fun _ => (1 : ℝ≥0∞)) (γ.toFun t) *
          ‖deriv γ.toFun t‖ₑ := by
    intro p q hp hq hpq hlt
    set αq := clamp (r p) with hαqdef
    set βq := clamp (r q) with hβqdef
    have hrq_ge : βq ≤ r q := by
      rcases le_or_gt (r q) Δ with h | h
      · exfalso
        have hβq_eq : βq = Δ := by
          show max Δ (min (ε + Δ) (r q)) = Δ
          rw [min_eq_right (by linarith : r q ≤ ε + Δ)]
          exact max_eq_left h
        linarith [hclampge (r p), hβq_eq]
      · rcases le_or_gt (r q) (ε + Δ) with h2 | h2
        · show max Δ (min (ε + Δ) (r q)) ≤ r q
          rw [min_eq_right h2]
          exact max_le h.le le_rfl
        · show max Δ (min (ε + Δ) (r q)) ≤ r q
          rw [min_eq_left h2.le]
          exact max_le h.le h2.le
    have hrp_le : r p ≤ αq := by
      rcases le_or_gt (r p) Δ with h | h
      · show r p ≤ max Δ (min (ε + Δ) (r p))
        rw [min_eq_right (by linarith : r p ≤ ε + Δ)]
        rw [max_eq_left h]
        exact h
      · rcases le_or_gt (r p) (ε + Δ) with h2 | h2
        · show r p ≤ max Δ (min (ε + Δ) (r p))
          rw [min_eq_right h2]
          exact le_max_right _ _
        · exfalso
          have hαq_eq : αq = ε + Δ := by
            show max Δ (min (ε + Δ) (r p)) = ε + Δ
            rw [min_eq_left h2.le]
            exact max_eq_right (by linarith)
          linarith [hclampleΔε (r q), hαq_eq]
    -- find `b`: the least point of `[p,q]` reaching up to `βq`
    have hpq01 : Icc p q ⊆ Icc (0:ℝ) 1 := Icc_subset_Icc (hc.trans hp.1) (hq.2.trans hd)
    have hrcontpq : ContinuousOn r (Icc p q) := hrcont.mono hpq01
    set Sb : Set ℝ := Icc p q ∩ r ⁻¹' (Ici βq) with hSbdef
    have hSbne : Sb.Nonempty := ⟨q, ⟨right_mem_Icc.2 hpq, hrq_ge⟩⟩
    have hSbclosed : IsClosed Sb :=
      hrcontpq.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hSbcompact : IsCompact Sb :=
      IsCompact.of_isClosed_subset isCompact_Icc hSbclosed inter_subset_left
    obtain ⟨b, ⟨hbSb, hblb⟩⟩ := hSbcompact.exists_isLeast hSbne
    obtain ⟨hbIcc, hbr⟩ := hbSb
    rw [Set.mem_preimage, Set.mem_Ici] at hbr
    -- find `a`: the greatest point of `[p,b]` staying down to `αq`
    have hpb : p ≤ b := hbIcc.1
    have hab01 : Icc p b ⊆ Icc (0:ℝ) 1 :=
      Icc_subset_Icc (hc.trans hp.1) (hbIcc.2.trans (hq.2.trans hd))
    have hrcontab : ContinuousOn r (Icc p b) := hrcont.mono hab01
    set Sa : Set ℝ := Icc p b ∩ r ⁻¹' (Iic αq) with hSadef
    have hSane : Sa.Nonempty := ⟨p, ⟨left_mem_Icc.2 hpb, hrp_le⟩⟩
    have hSaclosed : IsClosed Sa :=
      hrcontab.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hSacompact : IsCompact Sa :=
      IsCompact.of_isClosed_subset isCompact_Icc hSaclosed inter_subset_left
    obtain ⟨a, ⟨haSa, haub⟩⟩ := hSacompact.exists_isGreatest hSane
    obtain ⟨haIcc, har⟩ := haSa
    rw [Set.mem_preimage, Set.mem_Iic] at har
    have hab_le : a ≤ b := haIcc.2
    have hane : a ≠ b := by
      rintro rfl
      linarith [hbr, har]
    have hab_lt : a < b := lt_of_le_of_ne hab_le hane
    have hmid : ∀ t ∈ Ioo a b, αq < r t ∧ r t < βq := by
      intro t ht
      have htp : p ≤ t := haIcc.1.trans ht.1.le
      have htq : t ≤ q := ht.2.le.trans hbIcc.2
      have htb : t ≤ b := ht.2.le
      refine ⟨?_, ?_⟩
      · by_contra hle
        push Not at hle
        exact absurd (haub ⟨⟨htp, htb⟩, hle⟩) (not_le.2 ht.1)
      · by_contra hge
        push Not at hge
        exact absurd (hblb ⟨⟨htp, htq⟩, hge⟩) (not_le.2 ht.2)
    have hindic : ∀ t ∈ Ioo a b, γ.toFun t ∈ annulusAt ζ Δ (ε + Δ) := by
      intro t ht
      obtain ⟨h1, h2⟩ := hmid t ht
      exact ⟨lt_of_le_of_lt (hclampge (r p)) h1, lt_of_lt_of_le h2 (hclampleΔε (r q))⟩
    have ha0 : 0 ≤ a := hc.trans (hp.1.trans haIcc.1)
    have hb1 : b ≤ 1 := hbIcc.2.trans (hq.2.trans hd)
    have hB1 := nf_b_enorm_sub_le_lintegral hγ' ha0 hab_le hb1
    have hlen : ENNReal.ofReal (r b - r a) ≤ ‖γ.toFun b - γ.toFun a‖ₑ := by
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      have hrw : ‖(γ.toFun b - ζ) - (γ.toFun a - ζ)‖ = ‖γ.toFun b - γ.toFun a‖ := by
        congr 1; ring
      calc r b - r a ≤ |r b - r a| := le_abs_self _
        _ ≤ ‖(γ.toFun b - ζ) - (γ.toFun a - ζ)‖ := abs_norm_sub_norm_le _ _
        _ = ‖γ.toFun b - γ.toFun a‖ := hrw
    have hβα_le : ENNReal.ofReal (βq - αq) ≤ ENNReal.ofReal (r b - r a) :=
      ENNReal.ofReal_le_ofReal (by linarith [hbr, har])
    have hintAB : ∫⁻ t in Ioo a b, ‖deriv γ.toFun t‖ₑ ≤
        ∫⁻ t in Ioo c d, (annulusAt ζ Δ (ε + Δ)).indicator (fun _ => (1 : ℝ≥0∞))
          (γ.toFun t) * ‖deriv γ.toFun t‖ₑ := by
      have heqon : ∀ t ∈ Ioo a b, ‖deriv γ.toFun t‖ₑ =
          (annulusAt ζ Δ (ε + Δ)).indicator (fun _ => (1 : ℝ≥0∞)) (γ.toFun t) *
            ‖deriv γ.toFun t‖ₑ := by
        intro t ht
        rw [indicator_of_mem (hindic t ht), one_mul]
      rw [setLIntegral_congr_fun measurableSet_Ioo heqon]
      apply lintegral_mono_set
      intro t ht
      exact ⟨lt_of_le_of_lt (hp.1.trans haIcc.1) ht.1, lt_of_lt_of_le ht.2 (hbIcc.2.trans hq.2)⟩
    calc ENNReal.ofReal (βq - αq) ≤ ENNReal.ofReal (r b - r a) := hβα_le
      _ ≤ ‖γ.toFun b - γ.toFun a‖ₑ := hlen
      _ ≤ ∫⁻ t in Ioo a b, ‖deriv γ.toFun t‖ₑ := hB1
      _ ≤ _ := hintAB
  -- mirrored construction for the decreasing case (`β < α`)
  have key' : ∀ p q : ℝ, p ∈ Icc c d → q ∈ Icc c d → p ≤ q → clamp (r q) < clamp (r p) →
      ENNReal.ofReal (clamp (r p) - clamp (r q)) ≤
        ∫⁻ t in Ioo c d, (annulusAt ζ Δ (ε + Δ)).indicator (fun _ => (1 : ℝ≥0∞)) (γ.toFun t) *
          ‖deriv γ.toFun t‖ₑ := by
    intro p q hp hq hpq hgt'
    set αq := clamp (r p) with hαqdef
    set βq := clamp (r q) with hβqdef
    have hrp_ge : αq ≤ r p := by
      rcases le_or_gt (r p) Δ with h | h
      · exfalso
        have hαq_eq : αq = Δ := by
          show max Δ (min (ε + Δ) (r p)) = Δ
          rw [min_eq_right (by linarith : r p ≤ ε + Δ)]
          exact max_eq_left h
        linarith [hclampge (r q), hαq_eq]
      · rcases le_or_gt (r p) (ε + Δ) with h2 | h2
        · show max Δ (min (ε + Δ) (r p)) ≤ r p
          rw [min_eq_right h2]
          exact max_le h.le le_rfl
        · show max Δ (min (ε + Δ) (r p)) ≤ r p
          rw [min_eq_left h2.le]
          exact max_le h.le h2.le
    have hrq_le : r q ≤ βq := by
      rcases le_or_gt (r q) Δ with h | h
      · show r q ≤ max Δ (min (ε + Δ) (r q))
        rw [min_eq_right (by linarith : r q ≤ ε + Δ)]
        rw [max_eq_left h]
        exact h
      · rcases le_or_gt (r q) (ε + Δ) with h2 | h2
        · show r q ≤ max Δ (min (ε + Δ) (r q))
          rw [min_eq_right h2]
          exact le_max_right _ _
        · exfalso
          have hβq_eq : βq = ε + Δ := by
            show max Δ (min (ε + Δ) (r q)) = ε + Δ
            rw [min_eq_left h2.le]
            exact max_eq_right (by linarith)
          linarith [hclampleΔε (r p), hβq_eq]
    -- find `a`: the greatest point of `[p,q]` still up at `αq`
    have hpq01 : Icc p q ⊆ Icc (0:ℝ) 1 := Icc_subset_Icc (hc.trans hp.1) (hq.2.trans hd)
    have hrcontpq : ContinuousOn r (Icc p q) := hrcont.mono hpq01
    set Sa : Set ℝ := Icc p q ∩ r ⁻¹' (Ici αq) with hSadef
    have hSane : Sa.Nonempty := ⟨p, ⟨left_mem_Icc.2 hpq, hrp_ge⟩⟩
    have hSaclosed : IsClosed Sa :=
      hrcontpq.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hSacompact : IsCompact Sa :=
      IsCompact.of_isClosed_subset isCompact_Icc hSaclosed inter_subset_left
    obtain ⟨a, ⟨haSa, haub⟩⟩ := hSacompact.exists_isGreatest hSane
    obtain ⟨haIcc, har⟩ := haSa
    rw [Set.mem_preimage, Set.mem_Ici] at har
    -- find `b`: the least point of `[a,q]` dropping to `βq`
    have haq : a ≤ q := haIcc.2
    have hab01 : Icc a q ⊆ Icc (0:ℝ) 1 :=
      Icc_subset_Icc (hc.trans (hp.1.trans haIcc.1)) (hq.2.trans hd)
    have hrcontaq : ContinuousOn r (Icc a q) := hrcont.mono hab01
    set Sb : Set ℝ := Icc a q ∩ r ⁻¹' (Iic βq) with hSbdef
    have hSbne : Sb.Nonempty := ⟨q, ⟨right_mem_Icc.2 haq, hrq_le⟩⟩
    have hSbclosed : IsClosed Sb :=
      hrcontaq.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hSbcompact : IsCompact Sb :=
      IsCompact.of_isClosed_subset isCompact_Icc hSbclosed inter_subset_left
    obtain ⟨b, ⟨hbSb, hblb⟩⟩ := hSbcompact.exists_isLeast hSbne
    obtain ⟨hbIcc, hbr⟩ := hbSb
    rw [Set.mem_preimage, Set.mem_Iic] at hbr
    have hab_le : a ≤ b := hbIcc.1
    have hane : a ≠ b := by
      rintro rfl
      linarith [hbr, har]
    have hab_lt : a < b := lt_of_le_of_ne hab_le hane
    have hmid : ∀ t ∈ Ioo a b, βq < r t ∧ r t < αq := by
      intro t ht
      have hta : a ≤ t := ht.1.le
      have htq : t ≤ q := ht.2.le.trans hbIcc.2
      refine ⟨?_, ?_⟩
      · by_contra hle
        push Not at hle
        exact absurd (hblb ⟨⟨hta, htq⟩, hle⟩) (not_le.2 ht.2)
      · by_contra hge
        push Not at hge
        have htp' : p ≤ t := haIcc.1.trans ht.1.le
        exact absurd (haub ⟨⟨htp', htq⟩, hge⟩) (not_le.2 ht.1)
    have hindic : ∀ t ∈ Ioo a b, γ.toFun t ∈ annulusAt ζ Δ (ε + Δ) := by
      intro t ht
      obtain ⟨h1, h2⟩ := hmid t ht
      exact ⟨lt_of_le_of_lt (hclampge (r q)) h1, lt_of_lt_of_le h2 (hclampleΔε (r p))⟩
    have ha0 : 0 ≤ a := hc.trans (hp.1.trans haIcc.1)
    have hb1 : b ≤ 1 := hbIcc.2.trans (hq.2.trans hd)
    have hB1 := nf_b_enorm_sub_le_lintegral hγ' ha0 hab_le hb1
    have hlen : ENNReal.ofReal (r a - r b) ≤ ‖γ.toFun b - γ.toFun a‖ₑ := by
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      have hrw : ‖(γ.toFun b - ζ) - (γ.toFun a - ζ)‖ = ‖γ.toFun b - γ.toFun a‖ := by
        congr 1; ring
      calc r a - r b ≤ |r a - r b| := le_abs_self _
        _ = |r b - r a| := abs_sub_comm _ _
        _ ≤ ‖(γ.toFun b - ζ) - (γ.toFun a - ζ)‖ := abs_norm_sub_norm_le _ _
        _ = ‖γ.toFun b - γ.toFun a‖ := hrw
    have hβα_le : ENNReal.ofReal (αq - βq) ≤ ENNReal.ofReal (r a - r b) :=
      ENNReal.ofReal_le_ofReal (by linarith [hbr, har])
    have hintAB : ∫⁻ t in Ioo a b, ‖deriv γ.toFun t‖ₑ ≤
        ∫⁻ t in Ioo c d, (annulusAt ζ Δ (ε + Δ)).indicator (fun _ => (1 : ℝ≥0∞))
          (γ.toFun t) * ‖deriv γ.toFun t‖ₑ := by
      have heqon : ∀ t ∈ Ioo a b, ‖deriv γ.toFun t‖ₑ =
          (annulusAt ζ Δ (ε + Δ)).indicator (fun _ => (1 : ℝ≥0∞)) (γ.toFun t) *
            ‖deriv γ.toFun t‖ₑ := by
        intro t ht
        rw [indicator_of_mem (hindic t ht), one_mul]
      rw [setLIntegral_congr_fun measurableSet_Ioo heqon]
      apply lintegral_mono_set
      intro t ht
      exact ⟨lt_of_le_of_lt (hp.1.trans haIcc.1) ht.1, lt_of_lt_of_le ht.2 (hbIcc.2.trans hq.2)⟩
    calc ENNReal.ofReal (αq - βq) ≤ ENNReal.ofReal (r a - r b) := hβα_le
      _ ≤ ‖γ.toFun b - γ.toFun a‖ₑ := hlen
      _ ≤ ∫⁻ t in Ioo a b, ‖deriv γ.toFun t‖ₑ := hB1
      _ ≤ _ := hintAB
  show ENNReal.ofReal |β - α| ≤
      ∫⁻ t in Ioo c d, (annulusAt ζ Δ (ε + Δ)).indicator (fun _ => (1 : ℝ≥0∞)) (γ.toFun t) *
        ‖deriv γ.toFun t‖ₑ
  rcases lt_trichotomy α β with hlt | heq | hgt
  · rw [abs_of_pos (by linarith : (0:ℝ) < β - α)]
    exact key c d (left_mem_Icc.2 hcd) (right_mem_Icc.2 hcd) hcd hlt
  · rw [heq, sub_self, abs_zero, ENNReal.ofReal_zero]
    exact bot_le
  · rw [abs_of_neg (by linarith : β - α < 0), neg_sub]
    exact key' c d (left_mem_Icc.2 hcd) (right_mem_Icc.2 hcd) hcd hgt

theorem nf_b_one_le_rhoLength {γ : LRCurve} (hγ : γ.IsClosedCurve) (ζ : ℂ) {Δ ε : ℝ}
    (hΔ : 0 ≤ Δ) (hε : 0 < ε) {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Icc (0 : ℝ) 1) (hs₂ : s₂ ∈ Icc (0 : ℝ) 1)
    (hin : ‖γ.toFun s₁ - ζ‖ < Δ) (hout : ε + Δ < ‖γ.toFun s₂ - ζ‖) :
    1 ≤ γ.rhoLength (fun z => (annulusAt ζ Δ (ε + Δ)).indicator
      (fun _ => ENNReal.ofReal (1 / (2 * ε))) z) := by
  have hγ' := hγ
  obtain ⟨K, hKLip, hclosed⟩ := hγ
  set r : ℝ → ℝ := fun t => ‖γ.toFun t - ζ‖ with hrdef
  set clamp : ℝ → ℝ := fun x => max Δ (min (ε + Δ) x) with hclampdef
  have hclamp_s1 : clamp (r s₁) = Δ := by
    show max Δ (min (ε + Δ) (r s₁)) = Δ
    rw [min_eq_right (by linarith : r s₁ ≤ ε + Δ)]
    exact max_eq_left hin.le
  have hclamp_s2 : clamp (r s₂) = ε + Δ := by
    show max Δ (min (ε + Δ) (r s₂)) = ε + Δ
    rw [min_eq_left hout.le]
    exact max_eq_right (by linarith)
  have hr01 : r 0 = r 1 := by
    show ‖γ.toFun 0 - ζ‖ = ‖γ.toFun 1 - ζ‖
    rw [hclosed]
  have hκ : clamp (r 1) = clamp (r 0) := by rw [hr01]
  set X : ℝ≥0∞ := ∫⁻ t in Ioo (0:ℝ) 1, (annulusAt ζ Δ (ε + Δ)).indicator (fun _ => (1:ℝ≥0∞))
    (γ.toFun t) * ‖deriv γ.toFun t‖ₑ with hXdef
  have hmain : ∀ u v x y : ℝ, u ∈ Icc (0:ℝ) 1 → v ∈ Icc (0:ℝ) 1 → u ≤ v →
      clamp (r u) = x → clamp (r v) = y → |y - x| = ε → ENNReal.ofReal (2 * ε) ≤ X := by
    intro u v x y hu hv huv hcu hcv hxy
    have hseg1 := nf_b_clamp_le_lintegral hγ' ζ hΔ hε (le_refl (0:ℝ)) hu.1 hu.2
    have hseg2 := nf_b_clamp_le_lintegral hγ' ζ hΔ hε hu.1 huv hv.2
    have hseg3 := nf_b_clamp_le_lintegral hγ' ζ hΔ hε hv.1 hv.2 (le_refl (1:ℝ))
    have hcu' : max Δ (min (ε + Δ) ‖γ.toFun u - ζ‖) = x := hcu
    have hcv' : max Δ (min (ε + Δ) ‖γ.toFun v - ζ‖) = y := hcv
    have hκ' : max Δ (min (ε + Δ) ‖γ.toFun 1 - ζ‖) =
        max Δ (min (ε + Δ) ‖γ.toFun 0 - ζ‖) := hκ
    rw [hcu', hcv', hxy] at hseg2
    rw [hcu'] at hseg1
    rw [hκ', hcv'] at hseg3
    have hxy' : |x - y| = ε := by rw [abs_sub_comm]; exact hxy
    have htri0 : |x - y| ≤ |x - clamp (r 0)| + |clamp (r 0) - y| := abs_sub_le x (clamp (r 0)) y
    rw [hxy'] at htri0
    have hsum : ENNReal.ofReal (2 * ε) ≤
        ENNReal.ofReal |x - clamp (r 0)| + ENNReal.ofReal ε + ENNReal.ofReal |clamp (r 0) - y| := by
      rw [← ENNReal.ofReal_add (abs_nonneg _) hε.le,
        ← ENNReal.ofReal_add (add_nonneg (abs_nonneg _) hε.le) (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (by linarith [htri0])
    have hstep : ENNReal.ofReal |x - clamp (r 0)| + ENNReal.ofReal ε +
        ENNReal.ofReal |clamp (r 0) - y| ≤
        (∫⁻ t in Ioo (0:ℝ) u, (annulusAt ζ Δ (ε + Δ)).indicator (fun _ => (1:ℝ≥0∞))
            (γ.toFun t) * ‖deriv γ.toFun t‖ₑ) +
        (∫⁻ t in Ioo u v, (annulusAt ζ Δ (ε + Δ)).indicator (fun _ => (1:ℝ≥0∞))
            (γ.toFun t) * ‖deriv γ.toFun t‖ₑ) +
        (∫⁻ t in Ioo v 1, (annulusAt ζ Δ (ε + Δ)).indicator (fun _ => (1:ℝ≥0∞))
            (γ.toFun t) * ‖deriv γ.toFun t‖ₑ) := by
      gcongr
    have hd1 : Disjoint (Ioo (0:ℝ) u) (Ioo u v) := by
      apply Set.disjoint_left.mpr
      intro x0 hx1 hx2
      exact absurd hx1.2 (not_lt.2 hx2.1.le)
    have hd2 : Disjoint (Ioo (0:ℝ) u ∪ Ioo u v) (Ioo v 1) := by
      apply Set.disjoint_left.mpr
      intro x0 hx1 hx2
      rcases hx1 with hx1 | hx1
      · exact absurd hx1.2 (not_lt.2 (huv.trans hx2.1.le))
      · exact absurd hx1.2 (not_lt.2 hx2.1.le)
    have hsub : (∫⁻ t in Ioo (0:ℝ) u, (annulusAt ζ Δ (ε + Δ)).indicator (fun _ => (1:ℝ≥0∞))
          (γ.toFun t) * ‖deriv γ.toFun t‖ₑ) +
        (∫⁻ t in Ioo u v, (annulusAt ζ Δ (ε + Δ)).indicator (fun _ => (1:ℝ≥0∞))
            (γ.toFun t) * ‖deriv γ.toFun t‖ₑ) +
        (∫⁻ t in Ioo v 1, (annulusAt ζ Δ (ε + Δ)).indicator (fun _ => (1:ℝ≥0∞))
            (γ.toFun t) * ‖deriv γ.toFun t‖ₑ) ≤ X := by
      rw [hXdef, ← lintegral_union measurableSet_Ioo hd1, ← lintegral_union measurableSet_Ioo hd2]
      apply lintegral_mono_set
      intro t ht
      rcases ht with (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩
      · exact ⟨h1, h2.trans_le (huv.trans hv.2)⟩
      · exact ⟨hu.1.trans_lt h1, h2.trans_le hv.2⟩
      · exact ⟨hu.1.trans_lt (huv.trans_lt h1), h2⟩
    exact hsum.trans (hstep.trans hsub)
  have hbound : ENNReal.ofReal (2 * ε) ≤ X := by
    rcases le_total s₁ s₂ with hle | hle
    · exact hmain s₁ s₂ Δ (ε + Δ) hs₁ hs₂ hle hclamp_s1 hclamp_s2
        (by rw [show (ε + Δ) - Δ = ε by ring]; exact abs_of_pos hε)
    · exact hmain s₂ s₁ (ε + Δ) Δ hs₂ hs₁ hle hclamp_s2 hclamp_s1
        (by rw [show Δ - (ε + Δ) = -ε by ring, abs_neg]; exact abs_of_pos hε)
  have hρeq : ∀ t, (annulusAt ζ Δ (ε + Δ)).indicator
      (fun _ => ENNReal.ofReal (1 / (2 * ε))) (γ.toFun t) =
      ENNReal.ofReal (1 / (2 * ε)) *
        (annulusAt ζ Δ (ε + Δ)).indicator (fun _ => (1:ℝ≥0∞)) (γ.toFun t) := by
    intro t
    by_cases h : γ.toFun t ∈ annulusAt ζ Δ (ε + Δ)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  have hρ : γ.rhoLength (fun z => (annulusAt ζ Δ (ε + Δ)).indicator
      (fun _ => ENNReal.ofReal (1 / (2 * ε))) z) = ENNReal.ofReal (1 / (2 * ε)) * X := by
    show ∫⁻ t in Ioo (0:ℝ) 1, (annulusAt ζ Δ (ε + Δ)).indicator
        (fun _ => ENNReal.ofReal (1 / (2 * ε))) (γ.toFun t) * ‖deriv γ.toFun t‖ₑ = _
    have heq2 : ∀ t, (annulusAt ζ Δ (ε + Δ)).indicator
        (fun _ => ENNReal.ofReal (1 / (2 * ε))) (γ.toFun t) * ‖deriv γ.toFun t‖ₑ =
        ENNReal.ofReal (1 / (2 * ε)) * ((annulusAt ζ Δ (ε + Δ)).indicator
          (fun _ => (1:ℝ≥0∞)) (γ.toFun t) * ‖deriv γ.toFun t‖ₑ) := by
      intro t
      rw [hρeq t, mul_assoc]
    rw [setLIntegral_congr_fun measurableSet_Ioo (fun t _ => heq2 t),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hXdef]
  rw [hρ]
  have hne : ENNReal.ofReal (1 / (2 * ε)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmul : ENNReal.ofReal (1 / (2 * ε)) * ENNReal.ofReal (2 * ε) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [show 1 / (2 * ε) * (2 * ε) = 1 by field_simp]
    exact ENNReal.ofReal_one
  calc (1:ℝ≥0∞) = ENNReal.ofReal (1 / (2 * ε)) * ENNReal.ofReal (2 * ε) := hmul.symm
    _ ≤ ENNReal.ofReal (1 / (2 * ε)) * X := by
        gcongr

/-! ### Theorem 8.1 — helpers of piece C -/


theorem nf_c_exists_mem_ray_of_separates {γ : LRCurve} (hγ : γ.IsClosedCurve) {p : ℂ}
    (hp : p ∉ γ.closedTrace)
    (hne : connectedComponentIn (toExt γ.closedTrace)ᶜ (p : ExtPlane) ≠
      connectedComponentIn (toExt γ.closedTrace)ᶜ extInf) {u : ℂ} (hu : ‖u‖ = 1) :
    ∃ t ∈ Icc (0 : ℝ) 1, ∃ ρ : ℝ, 0 < ρ ∧ γ.toFun t = p + ρ * u := by
  set γ' := gsep_z_translateCurve (-p) γ with hγ'def
  have hγ'closed : γ'.IsClosedCurve := gsep_z_translateCurve_isClosedCurve (-p) hγ
  have hγ'trace : γ'.closedTrace = (· + -p) '' γ.closedTrace :=
    gsep_z_translateCurve_closedTrace (-p) γ
  have h0notin : (0 : ℂ) ∉ γ'.closedTrace := by
    rw [hγ'trace]
    rintro ⟨z, hz, hz0⟩
    apply hp
    have hzp : z = p := by
      have h : z + -p = 0 := hz0
      linear_combination h
    rwa [hzp] at hz
  set Φ := gsep_z_translateHomeomorph (-p) with hΦdef
  have hΦcoe : ∀ z : ℂ, Φ (z : ExtPlane) = ((z + -p : ℂ) : ExtPlane) :=
    gsep_z_translateHomeomorph_coe (-p)
  have hΦinfty : Φ extInf = extInf := gsep_z_translateHomeomorph_infty (-p)
  have hΦtoExt : Φ '' toExt γ.closedTrace = toExt γ'.closedTrace := by
    rw [gsep_z_translateHomeomorph_toExt, hγ'trace]
  have hΦcompl : (toExt γ'.closedTrace)ᶜ = Φ '' (toExt γ.closedTrace)ᶜ := by
    rw [← hΦtoExt, gsep_z_image_compl_of_homeomorph]
  have hp_mem : (p : ExtPlane) ∈ (toExt γ.closedTrace)ᶜ := coe_mem_compl_toExt_iff.mpr hp
  have hinf_mem : (extInf : ExtPlane) ∈ (toExt γ.closedTrace)ᶜ := extInf_notMem_toExt _
  have hcc0 : connectedComponentIn (toExt γ'.closedTrace)ᶜ ((0 : ℂ) : ExtPlane) =
      Φ '' connectedComponentIn (toExt γ.closedTrace)ᶜ (p : ExtPlane) := by
    rw [hΦcompl]
    have h0eq : ((0 : ℂ) : ExtPlane) = Φ (p : ExtPlane) := by rw [hΦcoe]; norm_num
    rw [h0eq]
    exact (gsep_z_connectedComponentIn_image_homeomorph Φ hp_mem).symm
  have hccinf : connectedComponentIn (toExt γ'.closedTrace)ᶜ extInf =
      Φ '' connectedComponentIn (toExt γ.closedTrace)ᶜ extInf := by
    rw [hΦcompl]
    conv_lhs => rw [← hΦinfty]
    exact (gsep_z_connectedComponentIn_image_homeomorph Φ hinf_mem).symm
  have hne' : connectedComponentIn (toExt γ'.closedTrace)ᶜ ((0 : ℂ) : ExtPlane) ≠
      connectedComponentIn (toExt γ'.closedTrace)ᶜ extInf := by
    rw [hcc0, hccinf]
    intro heq
    exact hne (Set.image_injective.mpr Φ.injective heq)
  obtain ⟨t, ht, hEq⟩ := cor_exists_mem_ray_of_separates hγ'closed h0notin hne' (Complex.arg u)
  have hγ't : γ'.toFun t = γ.toFun t + -p := by
    rw [hγ'def, gsep_z_translateCurve_toFun]; rfl
  refine ⟨t, ht, ‖γ'.toFun t‖, ?_, ?_⟩
  · rw [norm_pos_iff]
    intro h0eq
    exact h0notin ⟨t, ht, h0eq⟩
  · have hexpu : Complex.exp (Complex.arg u * I) = u := by
      have h := Complex.norm_mul_exp_arg_mul_I u
      rw [hu, Complex.ofReal_one, one_mul] at h
      exact h
    rw [hexpu] at hEq
    linear_combination hEq - hγ't

theorem nf_c_exists_inside_outside {γ : LRCurve} (hγ : γ.IsClosedCurve) {M : ℝ}
    (htrace : γ.closedTrace ⊆ ball (0 : ℂ) M) {w' w'' : ℂ} (hw'' : ‖w''‖ < M) (hne : w' ≠ w'')
    (hw'tr : w' ∉ γ.closedTrace) (hw''tr : w'' ∉ γ.closedTrace)
    (hsep' : connectedComponentIn (toExt γ.closedTrace)ᶜ (w' : ExtPlane) ≠
      connectedComponentIn (toExt γ.closedTrace)ᶜ extInf)
    (hsep'' : connectedComponentIn (toExt γ.closedTrace)ᶜ (w'' : ExtPlane) ≠
      connectedComponentIn (toExt γ.closedTrace)ᶜ extInf) :
    (∃ s₁ ∈ Icc (0 : ℝ) 1,
        ‖γ.toFun s₁ - (w'' + (M : ℂ) * ((w'' - w') / (‖w'' - w'‖ : ℂ)))‖ < M) ∧
      ∃ s₂ ∈ Icc (0 : ℝ) 1,
        ‖w'' - w'‖ + M < ‖γ.toFun s₂ - (w'' + (M : ℂ) * ((w'' - w') / (‖w'' - w'‖ : ℂ)))‖ := by
  set ε : ℝ := ‖w'' - w'‖ with hεdef
  have hεpos : 0 < ε := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne))
  set u : ℂ := (w'' - w') / (ε : ℂ) with hudef
  have hunorm : ‖u‖ = 1 := by
    rw [hudef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hεpos, hεdef,
      div_self hεpos.ne']
  set ζ : ℂ := w'' + (M : ℂ) * u with hζdef
  constructor
  · obtain ⟨t, ht, ρ, hρpos, hEq⟩ :=
      nf_c_exists_mem_ray_of_separates hγ hw''tr hsep'' hunorm
    refine ⟨t, ht, ?_⟩
    have hργ : γ.toFun t = w'' + (ρ : ℂ) * u := hEq
    have hball : γ.toFun t ∈ ball (0 : ℂ) M := htrace ⟨t, ht, rfl⟩
    have hnormlt : ‖γ.toFun t‖ < M := by rwa [mem_ball, dist_zero_right] at hball
    have hkey : ‖(ρ : ℂ) * u‖ - ‖w''‖ ≤ ‖w'' + (ρ : ℂ) * u‖ := by
      have h := norm_sub_le (w'' + (ρ : ℂ) * u) w''
      rw [add_sub_cancel_left] at h
      linarith [h]
    have h2 : ‖(ρ : ℂ) * u‖ = ρ := by
      rw [norm_mul, hunorm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos]
    rw [h2] at hkey
    have hρbound : ρ - ‖w''‖ < M := by rw [← hργ] at hkey; linarith [hkey, hnormlt]
    have hρlt2M : ρ < 2 * M := by linarith [hρbound, hw'']
    have heq2 : γ.toFun t - ζ = ((ρ - M : ℝ) : ℂ) * u := by
      rw [hργ, hζdef]; push_cast; ring
    rw [heq2, norm_mul, Complex.norm_real, Real.norm_eq_abs, hunorm, mul_one, abs_lt]
    constructor <;> linarith [hρpos, hρlt2M, hw'']
  · obtain ⟨t, ht, ρ, hρpos, hEq⟩ :=
      nf_c_exists_mem_ray_of_separates hγ hw'tr hsep' (u := -u) (by rwa [norm_neg])
    refine ⟨t, ht, ?_⟩
    have hργ : γ.toFun t = w' + (ρ : ℂ) * (-u) := hEq
    have huw : (ε : ℂ) * u = w'' - w' := by
      rw [hudef, mul_comm, div_mul_cancel₀]
      exact_mod_cast hεpos.ne'
    have hw'eq : w' = w'' - (ε : ℂ) * u := by linear_combination huw
    have heq2 : γ.toFun t - ζ = (-(ε + ρ + M) : ℝ) * u := by
      rw [hργ, hζdef, hw'eq]; push_cast; ring
    rw [heq2, norm_mul, Complex.norm_real, Real.norm_eq_abs, hunorm, mul_one, abs_neg,
      abs_of_pos (by linarith [hεpos, hρpos, hw'', norm_nonneg w''] : (0 : ℝ) < ε + ρ + M)]
    linarith [hρpos]


/-! ### Theorem 8.1 — helpers of piece D -/


theorem nf_d_component_ne_extInf {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) {z₀ : ℂ}
    {δ δ₁ : ℝ} (hδ : 0 < δ) (hδδ₁ : δ < δ₁) (hD₁ : closedBall z₀ δ₁ ⊆ D) {w : ℂ}
    (hw : w ∈ f '' closedBall z₀ δ) :
    (w : ExtPlane) ∈ (toExt (f '' annulusAt z₀ δ δ₁))ᶜ ∧
      connectedComponentIn (toExt (f '' annulusAt z₀ δ δ₁))ᶜ (w : ExtPlane) ≠
        connectedComponentIn (toExt (f '' annulusAt z₀ δ δ₁))ᶜ extInf := by
  set B' := f '' annulusAt z₀ δ δ₁ with hB'def
  set E := f '' closedBall z₀ δ with hEdef
  have hDopen : IsOpen D := hf.1
  have hcont : ContinuousOn f D := hf.2.2.1.1
  have hinj : InjOn f D := hf.2.2.1.2.1
  have hcballδ : closedBall z₀ δ ⊆ D := (closedBall_subset_closedBall hδδ₁.le).trans hD₁
  have hunion : closedBall z₀ δ ∪ annulusAt z₀ δ δ₁ = ball z₀ δ₁ := by
    ext z
    constructor
    · rintro (h1 | ⟨h1, h2⟩)
      · rw [mem_closedBall, dist_eq_norm] at h1
        rw [mem_ball, dist_eq_norm]
        linarith [h1, hδδ₁]
      · rw [mem_ball, dist_eq_norm]
        exact h2
    · intro h
      rw [mem_ball, dist_eq_norm] at h
      by_cases h1 : ‖z - z₀‖ ≤ δ
      · exact Or.inl (by rw [mem_closedBall, dist_eq_norm]; exact h1)
      · exact Or.inr ⟨not_le.mp h1, h⟩
  have hballD : ball z₀ δ₁ ⊆ D := ball_subset_closedBall.trans hD₁
  have hannsub : annulusAt z₀ δ δ₁ ⊆ D := (subset_union_right.trans hunion.le).trans hballD
  have hUeq : f '' ball z₀ δ₁ = E ∪ B' := by
    rw [hEdef, hB'def, ← hunion, Set.image_union]
  have hUopen : IsOpen (f '' ball z₀ δ₁) :=
    isOpen_image_of_continuousOn_injOn isOpen_ball (hcont.mono hballD) (hinj.mono hballD)
  rw [hUeq] at hUopen
  have hEcompact : IsCompact E := by
    rw [hEdef]
    exact (isCompact_closedBall z₀ δ).image_of_continuousOn (hcont.mono hcballδ)
  have hcballann : closedBall z₀ δ ∩ annulusAt z₀ δ δ₁ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    obtain ⟨h1, h2⟩ := hz
    rw [mem_closedBall, dist_eq_norm] at h1
    exact absurd h1 (not_le.mpr h2.1)
  have hEdisjB' : Disjoint E B' := by
    rw [hEdef, hB'def, Set.disjoint_iff_inter_eq_empty,
      ← Set.InjOn.image_inter hinj hcballδ hannsub, hcballann, Set.image_empty]
  have hwnotB' : w ∉ B' := fun hwB' => hEdisjB'.le_bot ⟨hw, hwB'⟩
  have hw_mem : (w : ExtPlane) ∈ (toExt B')ᶜ := coe_mem_compl_toExt_iff.mpr hwnotB'
  refine ⟨hw_mem, ?_⟩
  intro heqcc
  set C := connectedComponentIn (toExt B')ᶜ (w : ExtPlane) with hCdef
  have hwC : (w : ExtPlane) ∈ C := mem_connectedComponentIn hw_mem
  have hinfmem : (extInf : ExtPlane) ∈ (toExt B')ᶜ := extInf_notMem_toExt B'
  have hinfC : (extInf : ExtPlane) ∈ C := by
    rw [heqcc]
    exact mem_connectedComponentIn hinfmem
  have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have htoExtEclosed : IsClosed (toExt E) :=
    (hEcompact.image OnePoint.continuous_coe).isClosed
  have htoExtEB'open : IsOpen (toExt (E ∪ B')) := isOpen_toExt_iff.mpr hUopen
  have htoExtunion : toExt (E ∪ B') = toExt E ∪ toExt B' := Set.image_union _ E B'
  have htoExtEsub : toExt E ⊆ toExt (E ∪ B') := image_mono subset_union_left
  have hCsubset : C ⊆ toExt E ∪ (toExt (E ∪ B'))ᶜ := by
    intro x hx
    by_cases hxU : x ∈ toExt (E ∪ B')
    · rw [htoExtunion] at hxU
      rcases hxU with hxE | hxB'
      · exact Or.inl hxE
      · exact absurd hxB' (connectedComponentIn_subset _ _ hx)
    · exact Or.inr hxU
  have hCdisj : C ∩ (toExt E ∩ (toExt (E ∪ B'))ᶜ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨-, hxE, hxUc⟩
    exact hxUc (htoExtEsub hxE)
  have hsplit := isPreconnected_iff_subset_of_disjoint_closed.mp hCpre (toExt E)
    (toExt (E ∪ B'))ᶜ htoExtEclosed htoExtEB'open.isClosed_compl hCsubset hCdisj
  have hwEB' : w ∈ E ∪ B' := Or.inl hw
  have hwtoExt : (w : ExtPlane) ∈ toExt (E ∪ B') := coe_mem_toExt_iff.mpr hwEB'
  rcases hsplit with hCE | hCUc
  · exact extInf_notMem_toExt E (hCE hinfC)
  · exact hCUc hwC hwtoExt


/-! ### Theorem 8.1 — helpers of piece G -/


theorem nf_g_isDoublyConnected_annulusAt (z₀ : ℂ) {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) :
    IsDoublyConnected (annulusAt z₀ r₁ r₂) := by
  have hr2pos : 0 < r₂ := h₁.trans h₂
  set B := annulusAt z₀ r₁ r₂ with hBdef
  have hBopen : IsOpen B := by
    have heq : B = (fun z => ‖z - z₀‖) ⁻¹' Ioo r₁ r₂ := by
      ext z; simp [hBdef, annulusAt, mem_Ioo]
    rw [heq]
    exact (continuous_norm.comp (continuous_id.sub continuous_const)).isOpen_preimage _ isOpen_Ioo
  have hBeqimg : B = (· + z₀) '' annulus r₁ r₂ := by
    have h1 := gsep_z_annulusAt_eq_image 0 z₀ r₁ r₂
    rw [zero_add] at h1
    rw [hBdef, h1, gsep_z_annulusAt_zero]
  have hmid : (((r₁ + r₂) / 2 : ℝ) : ℂ) ∈ annulus r₁ r₂ := by
    show r₁ < ‖(((r₁ + r₂) / 2 : ℝ) : ℂ)‖ ∧ ‖(((r₁ + r₂) / 2 : ℝ) : ℂ)‖ < r₂
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < (r₁ + r₂) / 2)]
    constructor <;> linarith
  have hBconn : IsConnected B := by
    rw [hBeqimg]
    exact ⟨⟨(((r₁ + r₂) / 2 : ℝ) : ℂ) + z₀, (((r₁ + r₂) / 2 : ℝ) : ℂ), hmid, rfl⟩,
      (isPreconnected_annulus h₁.le).image _ (continuous_id.add continuous_const).continuousOn⟩
  set P := toExt (closedBall z₀ r₁) with hPdef
  set Q := (toExt (ball z₀ r₂))ᶜ with hQdef
  have hQclosed : IsClosed Q := (isOpen_toExt_iff.mpr isOpen_ball).isClosed_compl
  have hPcompact : IsCompact P := (isCompact_closedBall z₀ r₁).image OnePoint.continuous_coe
  have hPclosed : IsClosed P := hPcompact.isClosed
  -- the general complement fact for `toExt`
  have htoExtScompl : ∀ S : Set ℂ, (toExt S)ᶜ = toExt Sᶜ ∪ {extInf} := by
    intro S
    ext x
    induction x using OnePoint.rec with
    | infty =>
      simp only [mem_compl_iff, mem_union, mem_singleton_iff, or_true, iff_true]
      exact extInf_notMem_toExt S
    | coe z =>
      simp only [mem_compl_iff, coe_mem_toExt_iff, mem_union, mem_singleton_iff,
        OnePoint.coe_ne_infty, or_false]
  have hQeq : Q = toExt {z : ℂ | r₂ ≤ ‖z - z₀‖} ∪ {extInf} := by
    rw [hQdef]
    ext x
    induction x using OnePoint.rec with
    | infty =>
      simp only [mem_compl_iff, mem_union, mem_singleton_iff, or_true, iff_true]
      exact extInf_notMem_toExt (ball z₀ r₂)
    | coe z =>
      simp only [mem_compl_iff, mem_ball, coe_mem_toExt_iff, mem_setOf_eq, mem_union,
        mem_singleton_iff, OnePoint.coe_ne_infty, or_false, not_lt, dist_eq_norm]
  have hPQunion : (toExt B)ᶜ = P ∪ Q := by
    rw [htoExtScompl, hQeq, hPdef]
    have hcompl : Bᶜ = closedBall z₀ r₁ ∪ {z : ℂ | r₂ ≤ ‖z - z₀‖} := by
      ext z
      simp only [hBdef, annulusAt, mem_compl_iff, mem_setOf_eq, mem_union, mem_closedBall,
        dist_eq_norm]
      constructor
      · intro h
        by_contra hcon
        push Not at hcon
        exact h ⟨hcon.1, hcon.2⟩
      · rintro (h | h)
        · intro hh; linarith [hh.1]
        · intro hh; linarith [hh.2]
    rw [hcompl]
    have himgunion : toExt (closedBall z₀ r₁ ∪ {z : ℂ | r₂ ≤ ‖z - z₀‖}) =
        toExt (closedBall z₀ r₁) ∪ toExt {z : ℂ | r₂ ≤ ‖z - z₀‖} := Set.image_union _ _ _
    rw [himgunion]
    ac_rfl
  have hPQdisj : Disjoint P Q := by
    rw [hPdef, hQeq, Set.disjoint_union_right]
    refine ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      rintro x hxP hxQ
      obtain ⟨z, hz, rfl⟩ := hxP
      obtain ⟨z', hz', hzz'⟩ := hxQ
      rw [OnePoint.coe_injective hzz'] at hz'
      rw [mem_closedBall, dist_eq_norm] at hz
      simp only [mem_setOf_eq] at hz'
      linarith
    · rw [Set.disjoint_left]
      rintro x hxP hxQ
      obtain ⟨z, -, hz0⟩ := hxP
      rw [mem_singleton_iff] at hxQ
      exact OnePoint.coe_ne_infty z (hz0.trans hxQ)
  have hPpre : IsPreconnected P :=
    (convex_closedBall z₀ r₁).isPreconnected.image _ OnePoint.continuous_coe.continuousOn
  have hz₀mem : (z₀ : ExtPlane) ∈ P := ⟨z₀, mem_closedBall_self h₁.le, rfl⟩
  have hinfmemQ : (extInf : ExtPlane) ∈ Q := extInf_notMem_toExt (ball z₀ r₂)
  have hunbdd : ¬ Bornology.IsBounded {z : ℂ | r₂ < ‖z - z₀‖} := by
    intro hbdd
    obtain ⟨r, hr⟩ := hbdd.subset_closedBall (0 : ℂ)
    set t : ℝ := max r₂ (r + ‖z₀‖) + 1 with htdef
    set w : ℂ := z₀ + (t : ℂ) with hwdef
    have ht1 : r₂ < t := by
      have := le_max_left r₂ (r + ‖z₀‖); rw [htdef]; linarith
    have ht2 : r + ‖z₀‖ < t := by
      have := le_max_right r₂ (r + ‖z₀‖); rw [htdef]; linarith
    have hwmem : w ∈ {z : ℂ | r₂ < ‖z - z₀‖} := by
      show r₂ < ‖w - z₀‖
      have heq0 : w - z₀ = (t : ℂ) := by rw [hwdef]; ring
      rw [heq0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < t)]
      exact ht1
    have hwr : w ∈ closedBall (0 : ℂ) r := hr hwmem
    rw [mem_closedBall, dist_zero_right] at hwr
    have hwnorm : t - ‖z₀‖ ≤ ‖w‖ := by
      have hkey := norm_sub_le w z₀
      have heq1 : w - z₀ = (t : ℂ) := by rw [hwdef]; ring
      rw [heq1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < t)] at hkey
      linarith [hkey]
    linarith [hwnorm, hwr, ht2]
  have hQpre : IsPreconnected Q := by
    have hclosureeq : closure {z : ℂ | r₂ < ‖z - z₀‖} = {z : ℂ | r₂ ≤ ‖z - z₀‖} := by
      have heq1 : {z : ℂ | r₂ < ‖z - z₀‖} = (closedBall z₀ r₂)ᶜ := by
        ext z; simp [mem_closedBall, dist_eq_norm, not_le]
      rw [heq1, closure_compl, interior_closedBall z₀ hr2pos.ne']
      ext z; simp [mem_ball, dist_eq_norm, not_lt]
    have hQeq2 : Q = toExt (closure {z : ℂ | r₂ < ‖z - z₀‖}) ∪ {extInf} := by
      rw [hclosureeq]; exact hQeq
    rw [hQeq2]
    have h2 : (fun z : ℂ => z + z₀) '' {z : ℂ | r₂ < ‖z‖} = {z : ℂ | r₂ < ‖z - z₀‖} := by
      ext y
      simp only [mem_image, mem_setOf_eq]
      constructor
      · rintro ⟨x, hx, rfl⟩; simpa using hx
      · intro hy; exact ⟨y - z₀, by simpa using hy, by ring⟩
    have hK : IsPreconnected (toExt {z : ℂ | r₂ < ‖z - z₀‖}) := by
      have h1 : IsPreconnected {z : ℂ | r₂ < ‖z‖} := isPreconnected_setOf_lt_norm hr2pos.le
      have h3 := gsep_z_translateHomeomorph_toExt z₀ {z : ℂ | r₂ < ‖z‖}
      rw [h2] at h3
      rw [← h3]
      exact h1.image _ OnePoint.continuous_coe.continuousOn |>.image
        (gsep_z_translateHomeomorph z₀) (gsep_z_translateHomeomorph z₀).continuous.continuousOn
    refine hK.subset_closure ((image_mono subset_closure).trans subset_union_left) ?_
    apply union_subset
    · exact image_closure_subset_closure_image OnePoint.continuous_coe
    · exact singleton_subset_iff.2 (extInf_mem_closure_toExt_of_not_isBounded hunbdd)
  have hsplit : ∀ x ∈ (toExt B)ᶜ,
      connectedComponentIn (toExt B)ᶜ x ⊆ P ∨ connectedComponentIn (toExt B)ᶜ x ⊆ Q := by
    intro x hx
    have hCpre : IsPreconnected (connectedComponentIn (toExt B)ᶜ x) :=
      isPreconnected_connectedComponentIn
    have hCsub : connectedComponentIn (toExt B)ᶜ x ⊆ P ∪ Q :=
      hPQunion ▸ connectedComponentIn_subset _ _
    have hCdisj : connectedComponentIn (toExt B)ᶜ x ∩ (P ∩ Q) = ∅ := by
      rw [hPQdisj.inter_eq, inter_empty]
    exact isPreconnected_iff_subset_of_disjoint_closed.mp hCpre P Q hPclosed hQclosed hCsub hCdisj
  have hsplitEq : ∀ x ∈ (toExt B)ᶜ,
      connectedComponentIn (toExt B)ᶜ x = P ∨ connectedComponentIn (toExt B)ᶜ x = Q := by
    intro x hx
    rcases hsplit x hx with h | h
    · left
      have hxP : x ∈ P := h (mem_connectedComponentIn hx)
      exact le_antisymm h (hPpre.subset_connectedComponentIn hxP (hPQunion ▸ subset_union_left))
    · right
      have hxQ : x ∈ Q := h (mem_connectedComponentIn hx)
      exact le_antisymm h (hQpre.subset_connectedComponentIn hxQ (hPQunion ▸ subset_union_right))
  have hz₀X : (z₀ : ExtPlane) ∈ (toExt B)ᶜ := hPQunion ▸ Or.inl hz₀mem
  have hinfX : (extInf : ExtPlane) ∈ (toExt B)ᶜ := hPQunion ▸ Or.inr hinfmemQ
  have hCz₀ : connectedComponentIn (toExt B)ᶜ (z₀ : ExtPlane) = P := by
    rcases hsplitEq (z₀ : ExtPlane) hz₀X with h | h
    · exact h
    · exfalso
      have hzQ : (z₀ : ExtPlane) ∈ Q := h ▸ mem_connectedComponentIn hz₀X
      exact hPQdisj.le_bot ⟨hz₀mem, hzQ⟩
  have hCinf : connectedComponentIn (toExt B)ᶜ extInf = Q := by
    rcases hsplitEq extInf hinfX with h | h
    · exfalso
      have hzP : (extInf : ExtPlane) ∈ P := h ▸ mem_connectedComponentIn hinfX
      exact hPQdisj.le_bot ⟨hzP, hinfmemQ⟩
    · exact h
  have hne : connectedComponentIn (toExt B)ᶜ (z₀ : ExtPlane) ≠
      connectedComponentIn (toExt B)ᶜ extInf := by
    rw [hCz₀, hCinf]
    intro heq
    have hzQ2 : (z₀ : ExtPlane) ∈ Q := heq ▸ hz₀mem
    exact hPQdisj.le_bot ⟨hz₀mem, hzQ2⟩
  refine ⟨hBopen, hBconn, ?_⟩
  rw [Nat.card_eq_two_iff]
  refine ⟨ConnectedComponents.mk ⟨(z₀ : ExtPlane), hz₀X⟩,
    ConnectedComponents.mk ⟨(extInf : ExtPlane), hinfX⟩, ?_, ?_⟩
  · intro hmk
    rw [ConnectedComponents.coe_eq_coe] at hmk
    apply hne
    rw [connectedComponentIn_eq_image hz₀X, connectedComponentIn_eq_image hinfX, hmk]
  · ext c
    simp only [mem_insert_iff, mem_singleton_iff, mem_univ, iff_true]
    obtain ⟨⟨x, hx⟩, rfl⟩ := ConnectedComponents.surjective_coe c
    rcases hsplitEq x hx with h | h
    · left
      rw [ConnectedComponents.coe_eq_coe]
      apply Set.image_injective.2 Subtype.val_injective
      rw [← connectedComponentIn_eq_image hx, ← connectedComponentIn_eq_image hz₀X, h, hCz₀]
    · right
      rw [ConnectedComponents.coe_eq_coe]
      apply Set.image_injective.2 Subtype.val_injective
      rw [← connectedComponentIn_eq_image hx, ← connectedComponentIn_eq_image hinfX, h, hCinf]


/-! ### Theorem 8.1 — helpers of piece E -/



theorem nf_e_closure_toExt_subset {s C : Set ℂ} (hC : IsCompact C) (hsC : s ⊆ C) :
    closure (toExt s) ⊆ toExt C := by
  have hCclosed : IsClosed (toExt C) := (hC.image OnePoint.continuous_coe).isClosed
  calc closure (toExt s) ⊆ closure (toExt C) := closure_mono (image_mono hsC)
    _ = toExt C := hCclosed.closure_eq

theorem nf_e_dcModulus_annulusAt (z₀ : ℂ) {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) :
    dcModulus (annulusAt z₀ r₁ r₂) = ENNReal.ofReal (Real.log (r₂ / r₁)) := by
  have hBopen : IsOpen (annulusAt z₀ r₁ r₂) := by
    have heq : annulusAt z₀ r₁ r₂ = (fun z => ‖z - z₀‖) ⁻¹' Ioo r₁ r₂ := by
      ext z; simp [annulusAt, mem_Ioo]
    rw [heq]
    exact (continuous_norm.comp (continuous_id.sub continuous_const)).isOpen_preimage _ isOpen_Ioo
  refine dcModulus_eq_of_equiv hBopen h₁ h₂ ⟨fun z => z - z₀,
    (differentiable_id.sub_const z₀).differentiableOn, fun a _ b _ h => by simpa using h, ?_⟩
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hw
    exact ⟨w + z₀, by simpa [annulusAt, annulus] using hw, by ring⟩

theorem nf_e_log_le {f : ℂ → ℂ} {D : Set ℂ} {K M : ℝ} (hf : IsKQC f D K)
    (hM : ∀ z ∈ D, ‖f z‖ ≤ M) {z₀ : ℂ} {δ δ₁ : ℝ} (hδ : 0 < δ) (hδδ₁ : δ < δ₁)
    (hD₁ : closedBall z₀ δ₁ ⊆ D) :
    Real.log (δ₁ / δ) ≤ K * (π ^ 2 / 2 + π ^ 2 * M / diam (f '' closedBall z₀ δ)) := by
  have hDopen : IsOpen D := hf.1
  have hKge1 : (1 : ℝ) ≤ K := hf.2.1
  have hcont : ContinuousOn f D := hf.2.2.1.1
  have hinj : InjOn f D := hf.2.2.1.2.1
  set E := f '' closedBall z₀ δ with hEdef
  have hcballδD : closedBall z₀ δ ⊆ D := (closedBall_subset_closedBall hδδ₁.le).trans hD₁
  have hEcompact : IsCompact E :=
    (isCompact_closedBall z₀ δ).image_of_continuousOn (hcont.mono hcballδD)
  have hEbdd : Bornology.IsBounded E := hEcompact.isBounded
  have hz₀mem : z₀ ∈ closedBall z₀ δ := mem_closedBall_self hδ.le
  have hz₀δmem : z₀ + (δ : ℂ) ∈ closedBall z₀ δ := by
    rw [mem_closedBall, dist_eq_norm]
    simp [abs_of_pos hδ]
  have hEne : E.Nonempty := ⟨f z₀, z₀, hz₀mem, rfl⟩
  have hExEne : (E ×ˢ E).Nonempty := hEne.prod hEne
  obtain ⟨p, hpmem, hpmax⟩ :=
    (hEcompact.prod hEcompact).exists_isMaxOn hExEne (continuous_dist.continuousOn (s := E ×ˢ E))
  obtain ⟨w', w''⟩ := p
  simp only [mem_prod] at hpmem
  obtain ⟨hw'E, hw''E⟩ := hpmem
  set ε := diam E with hεdef
  have hdiam_eq : ε = dist w' w'' := by
    apply le_antisymm
    · refine Metric.diam_le_of_forall_dist_le dist_nonneg (fun x hx y hy => ?_)
      have hmem : (x, y) ∈ E ×ˢ E := mem_prod.2 ⟨hx, hy⟩
      exact hpmax hmem
    · exact Metric.dist_le_diam_of_mem hEbdd hw'E hw''E
  have hfne : f z₀ ≠ f (z₀ + (δ : ℂ)) := by
    intro heq
    have heq2 := hinj (hcballδD hz₀mem) (hcballδD hz₀δmem) heq
    have hδ0 : (δ : ℂ) = 0 := by linear_combination -heq2
    exact hδ.ne' (by exact_mod_cast hδ0)
  have hdistpos : 0 < dist (f z₀) (f (z₀ + (δ : ℂ))) := dist_pos.2 hfne
  have hdistle : dist (f z₀) (f (z₀ + (δ : ℂ))) ≤ ε :=
    Metric.dist_le_diam_of_mem hEbdd ⟨z₀, hz₀mem, rfl⟩ ⟨z₀ + (δ : ℂ), hz₀δmem, rfl⟩
  have hεpos : 0 < ε := lt_of_lt_of_le hdistpos hdistle
  have hw'ne'' : w' ≠ w'' := by
    intro heq
    have h0 : ε = 0 := by rw [hdiam_eq, heq, dist_self]
    linarith [hεpos, h0]
  have hεeq : ‖w'' - w'‖ = ε := by
    rw [hdiam_eq, dist_eq_norm, norm_sub_rev]
  have hw'Mle : ‖w'‖ ≤ M := by
    obtain ⟨a, haD, rfl⟩ := hw'E
    exact hM a (hcballδD haD)
  have hw''Mle : ‖w''‖ ≤ M := by
    obtain ⟨a, haD, rfl⟩ := hw''E
    exact hM a (hcballδD haD)
  have hεleM2 : ε ≤ ‖w'‖ + ‖w''‖ := by
    rw [hdiam_eq, dist_eq_norm]
    exact norm_sub_le w' w''
  have hMpos : 0 < M := by linarith [hεleM2, hw'Mle, hw''Mle, hεpos]
  set u : ℂ := (w'' - w') / (ε : ℂ) with hudef
  have hunorm : ‖u‖ = 1 := by
    rw [hudef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hεpos, hεeq,
      div_self hεpos.ne']
  set ζ : ℂ := w'' + (M : ℂ) * u with hζdef
  have hfDopen : IsOpen (f '' D) := isOpen_image_of_isKQC hf
  have hfDsubcball : f '' D ⊆ closedBall (0 : ℂ) M := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    exact hM z hz
  have hfDsubball : f '' D ⊆ ball (0 : ℂ) M := by
    rw [← interior_closedBall (0 : ℂ) hMpos.ne']
    exact interior_maximal hfDsubcball hfDopen
  have hw'Mlt : ‖w'‖ < M := by
    have hmem : w' ∈ f '' D := ⟨_, hcballδD hw'E.choose_spec.1, hw'E.choose_spec.2⟩
    have hb := hfDsubball hmem
    rwa [mem_ball, dist_zero_right] at hb
  have hw''Mlt : ‖w''‖ < M := by
    have hmem : w'' ∈ f '' D := ⟨_, hcballδD hw''E.choose_spec.1, hw''E.choose_spec.2⟩
    have hb := hfDsubball hmem
    rwa [mem_ball, dist_zero_right] at hb
  set B := annulusAt z₀ δ δ₁ with hBdef2
  have hBdc : IsDoublyConnected B := nf_g_isDoublyConnected_annulusAt z₀ hδ hδδ₁
  have hBsubcball : B ⊆ closedBall z₀ δ₁ := fun z hz => by
    rw [mem_closedBall, dist_eq_norm]; exact hz.2.le
  have hBsubD : B ⊆ D := hBsubcball.trans hD₁
  have hBD : closure (toExt B) ⊆ toExt D :=
    (nf_e_closure_toExt_subset (isCompact_closedBall z₀ δ₁) hBsubcball).trans (image_mono hD₁)
  obtain ⟨hB'dc, hratio, -⟩ := thm7_4_dcModulus_quasi_invariance hf hBdc hBD
  have hBmod : dcModulus B = ENNReal.ofReal (Real.log (δ₁ / δ)) :=
    nf_e_dcModulus_annulusAt z₀ hδ hδδ₁
  have hcballann_disj : closedBall z₀ δ ∩ B = ∅ := by
    ext z
    simp only [hBdef2, annulusAt, mem_inter_iff, mem_closedBall, mem_setOf_eq,
      mem_empty_iff_false, iff_false, not_and, not_lt, dist_eq_norm]
    intro h1 h2
    linarith [h1, h2]
  have hEfBdisj : Disjoint E (f '' B) := by
    rw [hEdef, Set.disjoint_iff_inter_eq_empty,
      ← Set.InjOn.image_inter hinj hcballδD hBsubD, hcballann_disj, Set.image_empty]
  have hw'notfB : w' ∉ f '' B := Set.disjoint_left.mp hEfBdisj hw'E
  have hw''notfB : w'' ∉ f '' B := Set.disjoint_left.mp hEfBdisj hw''E
  have hannopen : IsOpen (annulusAt ζ M (ε + M)) := by
    have heq : annulusAt ζ M (ε + M) = (fun z => ‖z - ζ‖) ⁻¹' Ioo M (ε + M) := by
      ext z; simp [annulusAt, mem_Ioo]
    rw [heq]
    exact (continuous_norm.comp (continuous_id.sub continuous_const)).isOpen_preimage _ isOpen_Ioo
  set ρ : ℂ → ℝ≥0∞ := fun z => (annulusAt ζ M (ε + M)).indicator
    (fun _ => ENNReal.ofReal (1 / (2 * ε))) z with hρdef
  have hρmeas : Measurable ρ := Measurable.indicator measurable_const hannopen.measurableSet
  have hζmatch : w'' + (M : ℂ) * ((w'' - w') / (‖w'' - w'‖ : ℂ)) = ζ := by
    have hcast : (‖w'' - w'‖ : ℂ) = (ε : ℂ) := by exact_mod_cast hεeq
    rw [hζdef, hudef, hcast]
  have hadm : ∀ γ ∈ separatingCurves (f '' B), 1 ≤ γ.rhoLength ρ := by
    intro γ hγ
    obtain ⟨hclosed, htrsub, hsegclause⟩ := hγ
    have hw'd1 := nf_d_component_ne_extInf hf hδ hδδ₁ hD₁ hw'E
    have hw''d1 := nf_d_component_ne_extInf hf hδ hδδ₁ hD₁ hw''E
    have hinfmem : (extInf : ExtPlane) ∈ (toExt (f '' B))ᶜ := extInf_notMem_toExt (f '' B)
    have hsep' := hsegclause (w' : ExtPlane) hw'd1.1 extInf hinfmem hw'd1.2
    have hsep'' := hsegclause (w'' : ExtPlane) hw''d1.1 extInf hinfmem hw''d1.2
    have hw'tr : w' ∉ γ.closedTrace := fun h => hw'notfB (htrsub h)
    have hw''tr : w'' ∉ γ.closedTrace := fun h => hw''notfB (htrsub h)
    have htrace : γ.closedTrace ⊆ ball (0 : ℂ) M :=
      htrsub.trans ((image_mono hBsubD).trans hfDsubball)
    obtain ⟨⟨s₁, hs₁, hin⟩, s₂, hs₂, hout⟩ :=
      nf_c_exists_inside_outside hclosed htrace hw''Mlt hw'ne'' hw'tr hw''tr hsep' hsep''
    rw [hζmatch] at hin hout
    rw [hεeq] at hout
    exact nf_b_one_le_rhoLength hclosed ζ hMpos.le hεpos hs₁ hs₂ hin hout
  have hstep1 : dcModulus (f '' B) ≤
      ENNReal.ofReal (2 * π) * ENNReal.ofReal (π / 4 * (1 + 2 * M / ε)) := by
    calc dcModulus (f '' B) ≤ ENNReal.ofReal (2 * π) * rhoArea ρ (f '' B) :=
          dcModulus_le_rhoArea hB'dc hρmeas hadm
      _ ≤ ENNReal.ofReal (2 * π) * ENNReal.ofReal (π / 4 * (1 + 2 * M / ε)) :=
          mul_le_mul_right (nf_a_rhoArea_le (f '' B) ζ hMpos.le hεpos) _
  have hfinal_ennreal :
      ENNReal.ofReal (Real.log (δ₁ / δ)) ≤ ENNReal.ofReal (K * (π ^ 2 / 2 + π ^ 2 * M / ε)) := by
    calc ENNReal.ofReal (Real.log (δ₁ / δ)) = dcModulus B := hBmod.symm
      _ ≤ ENNReal.ofReal K * dcModulus (f '' B) := hratio
      _ ≤ ENNReal.ofReal K *
            (ENNReal.ofReal (2 * π) * ENNReal.ofReal (π / 4 * (1 + 2 * M / ε))) :=
          mul_le_mul_right hstep1 _
      _ = ENNReal.ofReal (K * (2 * π * (π / 4 * (1 + 2 * M / ε)))) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by linarith)]
      _ = ENNReal.ofReal (K * (π ^ 2 / 2 + π ^ 2 * M / ε)) := by
          congr 1; ring
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hfinal_ennreal

/-- (8.4): if `f` is `K`-q.c. on `D`, `|f| ≤ M` on `D`, and `{|z - z₀| < δ₀} ⊆ D`, then for
`δ` so small that `(1/K) ln(δ₀/δ) > π²/2`, the diameter of `f({|z - z₀| ≤ δ})` is at most
`π² M ((1/K) ln(δ₀/δ) - π²/2)⁻¹`.

Proved (2026-09-21) from Theorem 7.4 and `dcModulus_le_rhoArea` with the book's density `1/(2ε)` on an
off-centre annulus (the `nf_` helpers above: length bound (8.3) `nf_b_one_le_rhoLength`, ray geometry
`nf_c_exists_inside_outside`, end correspondence `nf_d_component_ne_extInf`); no `G_n`, no monotonicity. -/
theorem eq8_4_equicontinuity_estimate {f : ℂ → ℂ} {D : Set ℂ} {K M : ℝ} (hf : IsKQC f D K)
    (hM : ∀ z ∈ D, ‖f z‖ ≤ M) {z₀ : ℂ} {δ₀ δ : ℝ} (hδ₀ : ball z₀ δ₀ ⊆ D) (hδ : 0 < δ)
    (hδδ₀ : δ < δ₀) (hsmall : π ^ 2 / 2 < (1 / K) * Real.log (δ₀ / δ)) :
    diam (f '' closedBall z₀ δ) ≤ π ^ 2 * M * ((1 / K) * Real.log (δ₀ / δ) - π ^ 2 / 2)⁻¹ := by
  set ε := diam (f '' closedBall z₀ δ) with hεdef
  have hKge1 : (1 : ℝ) ≤ K := hf.2.1
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hKge1
  have hbound : ∀ δ₁ ∈ Ioo δ δ₀, Real.log (δ₁ / δ) ≤ K * (π ^ 2 / 2 + π ^ 2 * M / ε) := by
    intro δ₁ hδ₁
    have hD₁ : closedBall z₀ δ₁ ⊆ D := (closedBall_subset_ball hδ₁.2).trans hδ₀
    exact nf_e_log_le hf hM hδ hδ₁.1 hD₁
  have hδ₀pos : 0 < δ₀ := hδ.trans hδδ₀
  have hδ₀δne : δ₀ / δ ≠ 0 := div_ne_zero hδ₀pos.ne' hδ.ne'
  have hf1 : ContinuousAt (fun δ₁ : ℝ => δ₁ / δ) δ₀ := (continuous_id.div_const δ).continuousAt
  have hcont : ContinuousAt (fun δ₁ : ℝ => Real.log (δ₁ / δ)) δ₀ := hf1.log hδ₀δne
  have htendsto : Tendsto (fun δ₁ : ℝ => Real.log (δ₁ / δ)) (𝓝[<] δ₀) (𝓝 (Real.log (δ₀ / δ))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ δ₁ in 𝓝[<] δ₀, Real.log (δ₁ / δ) ≤ K * (π ^ 2 / 2 + π ^ 2 * M / ε) := by
    have h1 : Ioi δ ∈ 𝓝 δ₀ := isOpen_Ioi.mem_nhds hδδ₀
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h1] with δ₁ hδ₁lt hδ₁gt
    exact hbound δ₁ ⟨hδ₁gt, hδ₁lt⟩
  have hlim : Real.log (δ₀ / δ) ≤ K * (π ^ 2 / 2 + π ^ 2 * M / ε) :=
    le_of_tendsto htendsto hev
  set L : ℝ := (1 / K) * Real.log (δ₀ / δ) - π ^ 2 / 2 with hLdef
  have hLpos : 0 < L := by rw [hLdef]; linarith [hsmall]
  have hεnonneg : 0 ≤ ε := diam_nonneg
  rcases eq_or_lt_of_le hεnonneg with hε0 | hεpos
  · rw [← hε0]
    have hMnonneg : 0 ≤ M :=
      (norm_nonneg (f z₀)).trans (hM z₀ (hδ₀ (mem_ball_self hδ₀pos)))
    positivity
  · have h1 : (1 / K) * Real.log (δ₀ / δ) ≤ π ^ 2 / 2 + π ^ 2 * M / ε := by
      rw [show (1 / K) * Real.log (δ₀ / δ) = Real.log (δ₀ / δ) / K by ring, div_le_iff₀ hKpos,
        mul_comm]
      exact hlim
    have hLε : L * ε ≤ π ^ 2 * M := by
      have h2 : L ≤ π ^ 2 * M / ε := by rw [hLdef]; linarith [h1]
      rw [le_div_iff₀ hεpos] at h2
      linarith [h2]
    have hfinal : ε ≤ π ^ 2 * M / L := by
      rw [le_div_iff₀ hLpos, mul_comm]
      exact hLε
    calc diam (f '' closedBall z₀ δ) = ε := hεdef
      _ ≤ π ^ 2 * M / L := hfinal
      _ = π ^ 2 * M * L⁻¹ := div_eq_mul_inv _ _

/-! ### Theorem 8.1 — helpers of piece F -/


/-- **F1.** Arzelà–Ascoli in normal-family form on an open `D ⊆ ℂ`: functions continuous on `D`,
uniformly bounded on `D` and equicontinuous at every point of `D` have a subsequence converging
locally uniformly on `D`. -/
theorem nf_f_exists_subseq_tendstoLocallyUniformlyOn {D : Set ℂ} (hD : IsOpen D) {M : ℝ}
    {gn : ℕ → ℂ → ℂ} (hcont : ∀ n, ContinuousOn (gn n) D) (hM : ∀ n, ∀ z ∈ D, ‖gn n z‖ ≤ M)
    (heq : ∀ z₀ ∈ D, ∀ η : ℝ, 0 < η → ∃ θ : ℝ, 0 < θ ∧ ∀ n, ∀ z ∈ D, dist z z₀ < θ →
      dist (gn n z) (gn n z₀) < η) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℂ → ℂ,
      TendstoLocallyUniformlyOn (fun n => gn (φ n)) f atTop D := by
  classical
  haveI := hD.locallyCompactSpace
  choose θ hθpos hθ using heq
  set g : ℕ → C(↥D, ℂ) := fun n => ⟨D.restrict (gn n), continuousOn_iff_continuous_restrict.1 (hcont n)⟩
    with hgdef
  set S : Set C(↥D, ℂ) := {h : C(↥D, ℂ) | (∀ z, ‖h z‖ ≤ M) ∧
      ∀ (z₀ : ↥D) (η : ℝ) (hη : 0 < η) (z : ↥D),
        dist (z : ℂ) (z₀ : ℂ) < θ (z₀ : ℂ) z₀.2 η hη → dist (h z) (h z₀) ≤ η} with hSdef
  have hgS : ∀ n, g n ∈ S := by
    intro n
    refine ⟨fun z => hM n z.1 z.2, fun z₀ η hη z hz => ?_⟩
    exact (hθ (z₀ : ℂ) z₀.2 η hη n z.1 z.2 hz).le
  -- The set `T` of (not a priori continuous) functions satisfying the same two conditions.
  set T : Set (↥D → ℂ) := {u : ↥D → ℂ | (∀ z, ‖u z‖ ≤ M) ∧
      ∀ (z₀ : ↥D) (η : ℝ) (hη : 0 < η) (z : ↥D),
        dist (z : ℂ) (z₀ : ℂ) < θ (z₀ : ℂ) z₀.2 η hη → dist (u z) (u z₀) ≤ η} with hTdef
  have himage : ContinuousMap.toFun '' S = T := by
    apply Subset.antisymm
    · rintro u ⟨h, hhS, rfl⟩
      exact hhS
    · rintro u ⟨huA, huB⟩
      have hucont : Continuous u := by
        rw [Metric.continuous_iff]
        intro z₀ ε hε
        exact ⟨θ (z₀ : ℂ) z₀.2 (ε / 2) (half_pos hε), hθpos (z₀ : ℂ) z₀.2 (ε / 2) (half_pos hε),
          fun z hz => lt_of_le_of_lt (huB z₀ (ε / 2) (half_pos hε) z hz) (half_lt_self hε)⟩
      exact ⟨⟨u, hucont⟩, ⟨huA, huB⟩, rfl⟩
  have hTclosed : IsClosed T := by
    have hA : IsClosed {u : ↥D → ℂ | ∀ z, ‖u z‖ ≤ M} := by
      rw [setOf_forall]
      exact isClosed_iInter fun z => isClosed_le (continuous_apply z).norm continuous_const
    have hB : IsClosed {u : ↥D → ℂ | ∀ (z₀ : ↥D) (η : ℝ) (hη : 0 < η) (z : ↥D),
        dist (z : ℂ) (z₀ : ℂ) < θ (z₀ : ℂ) z₀.2 η hη → dist (u z) (u z₀) ≤ η} := by
      simp only [setOf_forall]
      refine isClosed_iInter fun z₀ => isClosed_iInter fun η => isClosed_iInter fun hη =>
        isClosed_iInter fun z => ?_
      by_cases hp : dist (z : ℂ) (z₀ : ℂ) < θ (z₀ : ℂ) z₀.2 η hη
      · simpa [hp] using isClosed_le ((continuous_apply z).dist (continuous_apply z₀))
          continuous_const
      · simp [hp]
    exact hA.inter hB
  have hTsub : T ⊆ Set.pi univ fun _ : ↥D => closedBall (0 : ℂ) M := by
    intro u hu i _
    simpa using hu.1 i
  have hS1 : IsCompact (ContinuousMap.toFun '' S) := by
    rw [himage]
    exact IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
      hTclosed hTsub
  have hS2 : Equicontinuous ((↑) : S → ↥D → ℂ) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    filter_upwards [Metric.ball_mem_nhds x₀ (hθpos (x₀ : ℂ) x₀.2 (ε / 2) (half_pos hε))] with x hx s
    have hxd : dist (x : ℂ) (x₀ : ℂ) < θ (x₀ : ℂ) x₀.2 (ε / 2) (half_pos hε) := hx
    have hb := s.2.2 x₀ (ε / 2) (half_pos hε) x hxd
    calc dist ((s : C(↥D, ℂ)) x₀) ((s : C(↥D, ℂ)) x) = dist ((s : C(↥D, ℂ)) x) ((s : C(↥D, ℂ)) x₀) :=
          dist_comm _ _
      _ ≤ ε / 2 := hb
      _ < ε := half_lt_self hε
  have hScompact : IsCompact S := ArzelaAscoli.isCompact_of_equicontinuous S hS1 hS2
  obtain ⟨h, hhS, φ, hφmono, hφtend⟩ := hScompact.tendsto_subseq hgS
  have hloc : TendstoLocallyUniformly (fun n (a : ↥D) => g (φ n) a) h atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.1 hφtend
  refine ⟨φ, hφmono, fun z => if hz : z ∈ D then h ⟨z, hz⟩ else 0, ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  have hfeq : (fun z => if hz : z ∈ D then h ⟨z, hz⟩ else 0) ∘ ((↑) : ↥D → ℂ) = ⇑h := by
    funext a
    simp only [Function.comp_apply, dif_pos a.2]
  rw [hfeq]
  convert hloc using 1
  rfl

/-- **F2.** Equicontinuity of a uniformly bounded `K`-q.c. family from the estimate (8.4). -/
theorem nf_f_equicontinuous_of_isKQC {D : Set ℂ} {K M : ℝ} {fn : ℕ → ℂ → ℂ}
    (hqc : ∀ n, IsKQC (fn n) D K) (hM : ∀ n, ∀ z ∈ D, ‖fn n z‖ ≤ M) {z₀ : ℂ} (hz₀ : z₀ ∈ D)
    {η : ℝ} (hη : 0 < η) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ n, ∀ z ∈ D, dist z z₀ < θ → dist (fn n z) (fn n z₀) < η := by
  have hK1 : 1 ≤ K := (hqc 0).2.1
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK1
  have hDopen : IsOpen D := (hqc 0).1
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ := Metric.isOpen_iff.1 hDopen z₀ hz₀
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 z₀ hz₀)
  set δ : ℝ := δ₀ * Real.exp (-(K * (π ^ 2 / 2 + π ^ 2 * M / η + 1))) with hδdef
  have hδpos : 0 < δ := by positivity
  refine ⟨δ, hδpos, fun n z hz hdist => ?_⟩
  have hexplt1 : Real.exp (-(K * (π ^ 2 / 2 + π ^ 2 * M / η + 1))) < 1 := by
    apply Real.exp_lt_one_iff.2
    have : 0 < K * (π ^ 2 / 2 + π ^ 2 * M / η + 1) := by positivity
    linarith
  have hδδ₀ : δ < δ₀ := by
    rw [hδdef]
    calc δ₀ * Real.exp (-(K * (π ^ 2 / 2 + π ^ 2 * M / η + 1))) < δ₀ * 1 :=
          mul_lt_mul_of_pos_left hexplt1 hδ₀pos
      _ = δ₀ := mul_one δ₀
  have hlogeq : Real.log (δ₀ / δ) = K * (π ^ 2 / 2 + π ^ 2 * M / η + 1) := by
    have hexppos : (0:ℝ) < Real.exp (-(K * (π ^ 2 / 2 + π ^ 2 * M / η + 1))) := Real.exp_pos _
    rw [hδdef, show δ₀ / (δ₀ * Real.exp (-(K * (π ^ 2 / 2 + π ^ 2 * M / η + 1)))) =
        (Real.exp (-(K * (π ^ 2 / 2 + π ^ 2 * M / η + 1))))⁻¹ by
      field_simp,
      ← Real.exp_neg, neg_neg, Real.log_exp]
  have hcancel : (1 / K) * (K * (π ^ 2 / 2 + π ^ 2 * M / η + 1)) = π ^ 2 / 2 + π ^ 2 * M / η + 1 := by
    rw [one_div, inv_mul_cancel_left₀ hKpos.ne']
  have hsmall : π ^ 2 / 2 < (1 / K) * Real.log (δ₀ / δ) := by
    rw [hlogeq, hcancel]
    have : 0 < π ^ 2 * M / η + 1 := by positivity
    linarith
  have hclD : closedBall z₀ δ ⊆ D := (Metric.closedBall_subset_ball hδδ₀).trans hδ₀sub
  have hdiam := eq8_4_equicontinuity_estimate (hqc n) (hM n) hδ₀sub hδpos hδδ₀ hsmall
  rw [hlogeq, hcancel] at hdiam
  have hval : π ^ 2 * M * (π ^ 2 / 2 + π ^ 2 * M / η + 1 - π ^ 2 / 2)⁻¹ < η := by
    have heq2 : π ^ 2 / 2 + π ^ 2 * M / η + 1 - π ^ 2 / 2 = π ^ 2 * M / η + 1 := by ring
    rw [heq2, ← div_eq_mul_inv, div_lt_iff₀ (by positivity)]
    have hsum : η * (π ^ 2 * M / η + 1) = π ^ 2 * M + η := by
      field_simp [hη.ne']
    rw [hsum]
    linarith
  have hdiamlt : diam (fn n '' closedBall z₀ δ) < η := lt_of_le_of_lt hdiam hval
  have hbdd : Bornology.IsBounded (fn n '' closedBall z₀ δ) := by
    apply Bornology.IsBounded.subset (isBounded_closedBall (x := (0:ℂ)) (r := M))
    rintro w ⟨y, hy, rfl⟩
    simpa using hM n y (hclD hy)
  have hzmem : z ∈ closedBall z₀ δ := hdist.le
  have hz₀mem : z₀ ∈ closedBall z₀ δ := mem_closedBall_self hδpos.le
  have hle := Metric.dist_le_diam_of_mem hbdd (mem_image_of_mem (fn n) hzmem)
    (mem_image_of_mem (fn n) hz₀mem)
  exact lt_of_le_of_lt hle hdiamlt

/-- **Theorem 8.1**: a uniformly bounded family of `K`-q.c. maps on a bounded domain is a normal
family: every sequence has a subsequence converging locally uniformly on `D`.

Proved (2026-09-21): the estimate (8.4) gives equicontinuity (`nf_f_equicontinuous_of_isKQC`) and
Mathlib's `ArzelaAscoli.isCompact_of_equicontinuous` on `C(D, ℂ)` gives the locally uniformly convergent
subsequence (`nf_f_exists_subseq_tendstoLocallyUniformlyOn`). -/
theorem thm8_1_normal_family {D : Set ℂ} (hD : Bornology.IsBounded D) (hDc : IsConnected D)
    {K M : ℝ} {fn : ℕ → ℂ → ℂ} (hqc : ∀ n, IsKQC (fn n) D K) (hM : ∀ n, ∀ z ∈ D, ‖fn n z‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℂ → ℂ,
      TendstoLocallyUniformlyOn (fun n => fn (φ n)) f atTop D := by
  have hDopen : IsOpen D := (hqc 0).1
  have hcont : ∀ n, ContinuousOn (fn n) D := fun n => (hqc n).2.2.1.1
  have heq : ∀ z₀ ∈ D, ∀ η : ℝ, 0 < η → ∃ θ : ℝ, 0 < θ ∧ ∀ n, ∀ z ∈ D, dist z z₀ < θ →
      dist (fn n z) (fn n z₀) < η :=
    fun z₀ hz₀ η hη => nf_f_equicontinuous_of_isKQC hqc hM hz₀ hη
  exact nf_f_exists_subseq_tendstoLocallyUniformlyOn hDopen hcont hM heq

/-! ### Theorem 8.2 — helpers of piece P -/


theorem qcl_p_exists_pair {D : Set ℂ} (hDo : IsOpen D) (hDc : IsConnected D) {f : ℂ → ℂ}
    (hf : ContinuousOn f D) (hnc : ¬ ∃ c : ℂ, ∀ z ∈ D, f z = c) (hni : ¬ InjOn f D) :
    ∃ z₂ ∈ D, ∃ z₃ ∈ D, z₂ ≠ z₃ ∧ f z₂ = f z₃ ∧
      ∀ ε : ℝ, 0 < ε → ∃ z₁ ∈ D, dist z₁ z₂ < ε ∧ f z₁ ≠ f z₂ := by
  unfold InjOn at hni
  push Not at hni
  obtain ⟨x, hxD, y, hyD, hfxy, hxy⟩ := hni
  set c := f x with hcdef
  set L := D ∩ interior (f ⁻¹' {c}) with hLdef
  have hLopen : IsOpen L := hDo.inter isOpen_interior
  have hLsubD : L ⊆ D := inter_subset_left
  have hnlc : ∀ z₂ ∈ D, z₂ ∉ interior (f ⁻¹' {c}) →
      ∀ ε : ℝ, 0 < ε → ∃ z₁ ∈ D, dist z₁ z₂ < ε ∧ f z₁ ≠ c := by
    intro z₂ hz₂D hz₂ni ε hε
    obtain ⟨ε', hε'0, hε'D⟩ := Metric.isOpen_iff.mp hDo z₂ hz₂D
    set ε₀ := min ε ε' with hε₀def
    have hε₀0 : 0 < ε₀ := lt_min hε hε'0
    have hnotsub : ¬ ball z₂ ε₀ ⊆ f ⁻¹' {c} := fun hsub =>
      hz₂ni (mem_interior.2 ⟨ball z₂ ε₀, hsub, isOpen_ball, mem_ball_self hε₀0⟩)
    rw [not_subset] at hnotsub
    obtain ⟨z₁, hz₁ball, hz₁nmem⟩ := hnotsub
    exact ⟨z₁, hε'D (Metric.ball_subset_ball (min_le_right ε ε') hz₁ball),
      Metric.ball_subset_ball (min_le_left ε ε') hz₁ball, by simpa using hz₁nmem⟩
  by_cases hLe : L = ∅
  · refine ⟨x, hxD, y, hyD, hxy, hfxy, ?_⟩
    have hxni : x ∉ interior (f ⁻¹' {c}) := fun hmem => by
      have hxL : x ∈ L := ⟨hxD, hmem⟩
      rw [hLe] at hxL
      exact hxL
    exact hnlc x hxD hxni
  · have hLne : L.Nonempty := nonempty_iff_ne_empty.2 hLe
    have hLneD : L ≠ D := by
      intro hLD
      apply hnc
      refine ⟨c, fun z hz => ?_⟩
      have hzL : z ∈ L := hLD ▸ hz
      have hmem : z ∈ f ⁻¹' {c} := interior_subset hzL.2
      exact hmem
    have hLdisjcl : L ∩ closure (D \ L) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzL, hzcl⟩
      obtain ⟨w, hwL, hwDL⟩ := mem_closure_iff.1 hzcl L hLopen hzL
      exact hwDL.2 hwL
    have hex : ∃ z₂ ∈ D, z₂ ∈ closure L ∧ z₂ ∉ L := by
      by_contra hcon
      push Not at hcon
      have hLclosedD : D ∩ closure L = L := by
        apply Subset.antisymm
        · intro z hz
          exact hcon z hz.1 hz.2
        · exact fun z hz => ⟨hLsubD hz, subset_closure hz⟩
      have hcover : D ⊆ closure L ∪ closure (D \ L) := by
        intro z hz
        by_cases h : z ∈ L
        · exact Or.inl (subset_closure h)
        · exact Or.inr (subset_closure (mem_diff_of_mem hz h))
      have hdisjeq : D ∩ (closure L ∩ closure (D \ L)) = ∅ := by
        rw [← Set.inter_assoc, hLclosedD]; exact hLdisjcl
      rcases isPreconnected_iff_subset_of_disjoint_closed.mp hDc.2 (closure L) (closure (D \ L))
        isClosed_closure isClosed_closure hcover hdisjeq with h | h
      · apply hLneD
        rw [← hLclosedD]
        exact Subset.antisymm inter_subset_left (fun z hz => ⟨hz, h hz⟩)
      · obtain ⟨z₀, hz₀L⟩ := hLne
        have hz₀D : z₀ ∈ D := hLsubD hz₀L
        have : z₀ ∈ L ∩ closure (D \ L) := ⟨hz₀L, h hz₀D⟩
        rw [hLdisjcl] at this
        exact this
    obtain ⟨z₂, hz₂D, hz₂cl, hz₂nL⟩ := hex
    have hz₂ni : z₂ ∉ interior (f ⁻¹' {c}) := fun hmem => hz₂nL ⟨hz₂D, hmem⟩
    have hfz₂ : f z₂ = c := by
      have hcAt : ContinuousAt f z₂ := hf.continuousAt (hDo.mem_nhds hz₂D)
      have h1 : Tendsto f (𝓝[L] z₂) (𝓝 (f z₂)) := hcAt.continuousWithinAt.tendsto
      have h2 : Tendsto f (𝓝[L] z₂) (𝓝 c) := by
        have heq : ∀ᶠ z in 𝓝[L] z₂, f z = c := by
          filter_upwards [self_mem_nhdsWithin] with z hz
          have hmem : z ∈ f ⁻¹' {c} := interior_subset hz.2
          exact hmem
        exact tendsto_const_nhds.congr' (heq.mono fun z hz => hz.symm)
      have hzcl2 : (𝓝[L] z₂).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hz₂cl
      exact tendsto_nhds_unique h1 h2
    obtain ⟨z₃, hz₃L⟩ := hLne
    refine ⟨z₂, hz₂D, z₃, hLsubD hz₃L, ?_, ?_, ?_⟩
    · intro heq
      exact hz₂nL (heq ▸ hz₃L)
    · rw [hfz₂]
      exact (interior_subset hz₃L.2).symm
    · rw [hfz₂]
      exact hnlc z₂ hz₂D hz₂ni



/-! ### Theorem 8.2 — helpers of piece O -/


theorem qcl_o_outer_end {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) {z₀ : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hD : closedBall z₀ R ⊆ D) {q : ℂ} (hq : ‖q - z₀‖ = R) :
    (f q : ExtPlane) ∈ (toExt (f '' annulusAt z₀ r R))ᶜ ∧
      connectedComponentIn (toExt (f '' annulusAt z₀ r R))ᶜ (f q : ExtPlane) =
        connectedComponentIn (toExt (f '' annulusAt z₀ r R))ᶜ extInf := by
  have hRpos : 0 < R := hr.trans hrR
  have hDopen : IsOpen D := hf.1
  have hcont : ContinuousOn f D := hf.2.2.1.1
  have hinj : InjOn f D := hf.2.2.1.2.1
  set B := f '' annulusAt z₀ r R with hBdef
  have hannopen : IsOpen (annulusAt z₀ r R) := by
    have heq : annulusAt z₀ r R = (fun z => ‖z - z₀‖) ⁻¹' Ioo r R := by
      ext z; simp [annulusAt, mem_Ioo]
    rw [heq]
    exact (continuous_norm.comp (continuous_id.sub continuous_const)).isOpen_preimage _ isOpen_Ioo
  have hannsubcball : annulusAt z₀ r R ⊆ closedBall z₀ R := fun z hz => by
    rw [mem_closedBall, dist_eq_norm]; exact hz.2.le
  have hannsubD : annulusAt z₀ r R ⊆ D := hannsubcball.trans hD
  have hBdc : IsDoublyConnected B := by
    have hBD : closure (toExt (annulusAt z₀ r R)) ⊆ toExt D :=
      (nf_e_closure_toExt_subset (isCompact_closedBall z₀ R) hannsubcball).trans (image_mono hD)
    exact (thm7_4_dcModulus_quasi_invariance hf (nf_g_isDoublyConnected_annulusAt z₀ hr hrR) hBD).1
  have himgeq : annulusAt z₀ r R = (fun z : ℂ => z + z₀) '' annulus r R := by
    have h1 := gsep_z_annulusAt_eq_image 0 z₀ r R
    rw [zero_add] at h1
    rw [h1, gsep_z_annulusAt_zero]
  have htrans : IsHomeomorphOnto (fun z : ℂ => z + z₀) (annulus r R) (annulusAt z₀ r R) := by
    refine ⟨(continuous_id.add continuous_const).continuousOn,
      fun a _ b _ h => by simpa using h, himgeq.symm, ?_⟩
    have heqfun : EqOn (Function.invFunOn (fun z : ℂ => z + z₀) (annulus r R)) (fun w => w - z₀)
        (annulusAt z₀ r R) := by
      intro w hw
      have hwmem : w ∈ (fun z : ℂ => z + z₀) '' annulus r R := himgeq ▸ hw
      have hkey := Function.invFunOn_eq hwmem
      linear_combination hkey
    exact ContinuousOn.congr (continuous_id.sub continuous_const).continuousOn heqfun
  have hf' : IsHomeomorphOnto (fun z => f (z + z₀)) (annulus r R) B := by
    have hrestrict : IsHomeomorphOnto f (annulusAt z₀ r R) B :=
      aqc_isHomeomorphOnto_restrict hf.2.2.1 (isOpen_image_of_isKQC hf) hannsubD hannopen
    exact aqc_isHomeomorphOnto_comp htrans hrestrict
  have hfz₀mem : f z₀ ∈ f '' closedBall z₀ r := ⟨z₀, mem_closedBall_self hr.le, rfl⟩
  obtain ⟨hxmem, hxne⟩ := nf_d_component_ne_extInf hf hr hrR hD hfz₀mem
  set x : ExtPlane := (f z₀ : ExtPlane) with hxdef
  -- `f` sends the whole closed inner disc into `Comp x`
  have hcballrD : closedBall z₀ r ⊆ D := (closedBall_subset_closedBall hrR.le).trans hD
  have hcballrsub : closedBall z₀ r ⊆ D := hcballrD
  have hcballdisjann : closedBall z₀ r ∩ annulusAt z₀ r R = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_closedBall, annulusAt, mem_setOf_eq, mem_empty_iff_false,
      iff_false, not_and, not_lt, dist_eq_norm]
    intro h1 h2
    linarith [h1, h2]
  have hEBdisj : Disjoint (f '' closedBall z₀ r) B := by
    rw [hBdef, Set.disjoint_iff_inter_eq_empty,
      ← Set.InjOn.image_inter hinj hcballrsub hannsubD, hcballdisjann, Set.image_empty]
  have hEconn : IsPreconnected (f '' closedBall z₀ r) :=
    (convex_closedBall z₀ r).isPreconnected.image f (hcont.mono hcballrD)
  have hEsub : toExt (f '' closedBall z₀ r) ⊆ (toExt B)ᶜ := by
    rintro _ ⟨z, hz, rfl⟩ hzB
    exact Set.disjoint_left.mp hEBdisj hz (coe_mem_toExt_iff.mp hzB)
  have hEsubCompx : toExt (f '' closedBall z₀ r) ⊆ connectedComponentIn (toExt B)ᶜ x :=
    (hEconn.image _ OnePoint.continuous_coe.continuousOn).subset_connectedComponentIn
      (coe_mem_toExt_iff.mpr hfz₀mem) hEsub
  have hCompxfun : ∀ p ∈ closedBall z₀ r, (f p : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ x :=
    fun p hp => hEsubCompx (coe_mem_toExt_iff.mpr (mem_image_of_mem f hp))
  -- points approaching the outer/inner boundary of the annulus, along the segment from `z₀` to `q`
  have hrR1 : r / R < 1 := (div_lt_one hRpos).2 hrR
  set g : ℝ → ℂ := fun t => (t : ℂ) * (q - z₀) + z₀ with hgdef
  have hgcont : Continuous g := by fun_prop
  have hgnorm : ∀ t : ℝ, ‖g t - z₀‖ = |t| * R := by
    intro t
    have heq0 : g t - z₀ = (t : ℂ) * (q - z₀) := by rw [hgdef]; ring
    rw [heq0, norm_mul, Complex.norm_real, Real.norm_eq_abs, hq]
  set S : Set ℂ := g '' Ioo (r / R) (1 : ℝ) with hSdef
  have hSsubann : S ⊆ annulusAt z₀ r R := by
    rintro _ ⟨t, ⟨ht1, ht2⟩, rfl⟩
    have htpos : 0 < t := lt_trans (div_pos hr hRpos) ht1
    show r < ‖g t - z₀‖ ∧ ‖g t - z₀‖ < R
    rw [hgnorm, abs_of_pos htpos]
    exact ⟨(div_lt_iff₀ hRpos).1 ht1, by
      have hh := mul_lt_mul_of_pos_right ht2 hRpos; rwa [one_mul] at hh⟩
  have hSsubD : S ⊆ D := hSsubann.trans hannsubD
  set S₀ : Set ℂ := (fun z : ℂ => z - z₀) '' S with hS0def
  have hS0eq : S₀ = (fun t : ℝ => (t : ℂ) * (q - z₀)) '' Ioo (r / R) (1 : ℝ) := by
    rw [hS0def, hSdef, ← image_comp]
    congr 1
    funext t
    show g t - z₀ = (t : ℂ) * (q - z₀)
    rw [hgdef]; ring
  have hS0sub : S₀ ⊆ annulus r R := by
    rw [hS0eq]
    rintro _ ⟨t, ⟨ht1, ht2⟩, rfl⟩
    have htpos : 0 < t := lt_trans (div_pos hr hRpos) ht1
    show r < ‖(t : ℂ) * (q - z₀)‖ ∧ ‖(t : ℂ) * (q - z₀)‖ < R
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos, hq]
    exact ⟨(div_lt_iff₀ hRpos).1 ht1, by
      have hh := mul_lt_mul_of_pos_right ht2 hRpos; rwa [one_mul] at hh⟩
  have hfSeq : (fun z => f (z + z₀)) '' S₀ = f '' S := by
    rw [hS0def, ← image_comp]
    congr 1
    funext z
    show f (z - z₀ + z₀) = f z
    congr 1; ring
  have hScoverOuter : ∀ ε : ℝ, 0 < ε → ∃ t ∈ Ioo (r / R) (1 : ℝ), R - ε < t * R := by
    intro ε hε
    set δ := min (ε / (2 * R)) ((1 - r / R) / 2) with hδdef
    have hδpos : 0 < δ := lt_min (by positivity) (by linarith)
    have hδ1 : δ ≤ (1 - r / R) / 2 := min_le_right _ _
    have hδ2 : δ ≤ ε / (2 * R) := min_le_left _ _
    refine ⟨1 - δ, ⟨by linarith, by linarith⟩, ?_⟩
    have hb : δ * R ≤ ε / 2 := by
      have hh := mul_le_mul_of_nonneg_right hδ2 hRpos.le
      have heqb : ε / (2 * R) * R = ε / 2 := by field_simp
      rwa [heqb] at hh
    have hexpand : (1 - δ) * R = R - δ * R := by ring
    rw [hexpand]; linarith [hb, hε]
  have hScoverInner : ∀ ε : ℝ, 0 < ε → ∃ t ∈ Ioo (r / R) (1 : ℝ), t * R < r + ε := by
    intro ε hε
    set δ := min (ε / (2 * R)) ((1 - r / R) / 2) with hδdef
    have hδpos : 0 < δ := lt_min (by positivity) (by linarith)
    have hδ1 : δ ≤ (1 - r / R) / 2 := min_le_right _ _
    have hδ2 : δ ≤ ε / (2 * R) := min_le_left _ _
    refine ⟨r / R + δ, ⟨by linarith, by linarith⟩, ?_⟩
    have hb : δ * R ≤ ε / 2 := by
      have hh := mul_le_mul_of_nonneg_right hδ2 hRpos.le
      have heqb : ε / (2 * R) * R = ε / 2 := by field_simp
      rwa [heqb] at hh
    have hexpand : (r / R + δ) * R = r + δ * R := by field_simp
    rw [hexpand]; linarith [hb, hε]
  have hScondOuter : ∀ ε > (0 : ℝ), ∃ z ∈ S₀, R - ε < ‖z‖ := by
    intro ε hε
    obtain ⟨t, ht, htR⟩ := hScoverOuter ε hε
    have htpos : 0 < t := lt_trans (div_pos hr hRpos) ht.1
    rw [hS0eq]
    refine ⟨(t : ℂ) * (q - z₀), ⟨t, ht, rfl⟩, ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos, hq]
    exact htR
  have hScondInner : ∀ ε > (0 : ℝ), ∃ z ∈ S₀, ‖z‖ < r + ε := by
    intro ε hε
    obtain ⟨t, ht, htr⟩ := hScoverInner ε hε
    have htpos : 0 < t := lt_trans (div_pos hr hRpos) ht.1
    rw [hS0eq]
    refine ⟨(t : ℂ) * (q - z₀), ⟨t, ht, rfl⟩, ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos, hq]
    exact htr
  -- `q` and `p₀ := g (r/R)` are the only closure points beyond `S`
  have hqD : q ∈ D := hD (by rw [mem_closedBall, dist_eq_norm, hq])
  have hqclS : q ∈ closure S := by
    have h1cl : (1 : ℝ) ∈ closure (Ioo (r / R) (1 : ℝ)) := by
      rw [closure_Ioo hrR1.ne]; exact right_mem_Icc.2 hrR1.le
    have himg := image_closure_subset_closure_image hgcont (s := Ioo (r / R) (1 : ℝ))
    have hgqmem : g 1 ∈ g '' closure (Ioo (r / R) (1 : ℝ)) := mem_image_of_mem g h1cl
    have hgq1 : g 1 = q := by rw [hgdef]; simp
    rw [← hgq1]; exact himg hgqmem
  have hfqcl : f q ∈ closure (f '' S) := by
    rw [mem_closure_iff_nhds]
    intro U hU
    have hcontAtq : ContinuousAt f q := hcont.continuousAt (hDopen.mem_nhds hqD)
    have hpre : f ⁻¹' U ∈ 𝓝 q := hcontAtq.preimage_mem_nhds hU
    obtain ⟨z', hz'pre, hz'S⟩ := mem_closure_iff_nhds.1 hqclS (f ⁻¹' U) hpre
    exact ⟨f z', hz'pre, mem_image_of_mem f hz'S⟩
  set p₀ : ℂ := g (r / R) with hp₀def
  have hp₀mem : p₀ ∈ closedBall z₀ r := by
    rw [mem_closedBall, dist_eq_norm, hgnorm, abs_of_pos (div_pos hr hRpos),
      div_mul_cancel₀ r hRpos.ne']
  have hIccval : Icc (r / R) (1 : ℝ) = Ioo (r / R) 1 ∪ {r / R, 1} := by
    ext y
    simp only [mem_Icc, mem_union, mem_Ioo, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h1 with h1' | h1'
      · exact Or.inr (Or.inl h1'.symm)
      · rcases eq_or_lt_of_le h2 with h2' | h2'
        · exact Or.inr (Or.inr h2')
        · exact Or.inl ⟨h1', h2'⟩
    · rintro (⟨h1, h2⟩ | h1 | h1)
      · exact ⟨h1.le, h2.le⟩
      · exact ⟨h1.ge, h1 ▸ hrR1.le⟩
      · exact ⟨h1 ▸ hrR1.le, h1.le⟩
  have hclSicc : closure S ⊆ g '' Icc (r / R) (1 : ℝ) := by
    have hgIcc : IsCompact (g '' Icc (r / R) (1 : ℝ)) := isCompact_Icc.image hgcont
    have hSsubIcc : S ⊆ g '' Icc (r / R) (1 : ℝ) := hSdef ▸ image_mono Ioo_subset_Icc_self
    exact hgIcc.isClosed.closure_subset_iff.2 hSsubIcc
  have hclSval : g '' Icc (r / R) (1 : ℝ) = S ∪ {p₀, q} := by
    rw [hIccval, Set.image_union, hSdef]
    congr 1
    have hg1 : g 1 = q := by rw [hgdef]; simp
    rw [show ({r / R, (1:ℝ)} : Set ℝ) = insert (r / R) {(1:ℝ)} from rfl, Set.image_insert_eq,
      Set.image_singleton, hp₀def, hg1]
  have hclSub : closure S ⊆ S ∪ {p₀, q} := hclSval ▸ hclSicc
  have hclScompact : IsCompact (closure S) := by
    have hgIcc : IsCompact (g '' Icc (r / R) (1 : ℝ)) := isCompact_Icc.image hgcont
    rw [hclSval] at hgIcc
    exact hgIcc.of_isClosed_subset isClosed_closure (hclSval ▸ hclSicc)
  have hclSsubD : closure S ⊆ D := by
    refine hclSub.trans (union_subset hSsubD ?_)
    rw [show ({p₀, q} : Set ℂ) = insert p₀ {q} from rfl]
    exact insert_subset_iff.2 ⟨hcballrD hp₀mem, singleton_subset_iff.2 hqD⟩
  have hfclScompact : IsCompact (f '' closure S) :=
    hclScompact.image_of_continuousOn (hcont.mono hclSsubD)
  have hclosurebound : closure (toExt (f '' S)) ⊆
      toExt (f '' S) ∪ {(f p₀ : ExtPlane), (f q : ExtPlane)} := by
    have hstep1 : toExt (f '' S) ⊆ toExt (f '' closure S) :=
      image_mono (image_mono subset_closure)
    have hstep2 : IsClosed (toExt (f '' closure S)) :=
      (hfclScompact.image OnePoint.continuous_coe).isClosed
    have hstep3 : closure (toExt (f '' S)) ⊆ toExt (f '' closure S) :=
      hstep2.closure_subset_iff.2 hstep1
    have hstep4 : f '' closure S ⊆ f '' S ∪ {f p₀, f q} := by
      have heq : f '' S ∪ f '' ({p₀, q} : Set ℂ) = f '' S ∪ {f p₀, f q} := by
        congr 1
        rw [show ({p₀, q} : Set ℂ) = insert p₀ {q} from rfl, Set.image_insert_eq,
          Set.image_singleton]
      rw [← heq, ← Set.image_union]
      exact image_mono hclSub
    have hstep5 : toExt (f '' closure S) ⊆ toExt (f '' S ∪ {f p₀, f q}) := image_mono hstep4
    have hstep6 : toExt (f '' S ∪ {f p₀, f q}) =
        toExt (f '' S) ∪ {(f p₀ : ExtPlane), (f q : ExtPlane)} := by
      have himg : toExt (f '' S ∪ {f p₀, f q}) = toExt (f '' S) ∪ toExt ({f p₀, f q} : Set ℂ) :=
        Set.image_union _ _ _
      rw [himg]
      congr 1
      show ((↑) : ℂ → ExtPlane) '' ({f p₀, f q} : Set ℂ) =
        ({(f p₀ : ExtPlane), (f q : ExtPlane)} : Set ExtPlane)
      rw [Set.image_insert_eq, Set.image_singleton]
    exact hstep3.trans (hstep5.trans hstep6.le)
  have hSsubtoExtB : toExt (f '' S) ⊆ toExt B := image_mono (image_mono hSsubann)
  have hp₀notinf : (f p₀ : ExtPlane) ∉ connectedComponentIn (toExt B)ᶜ extInf := by
    intro hmem
    have h1 : connectedComponentIn (toExt B)ᶜ extInf = connectedComponentIn (toExt B)ᶜ x :=
      (connectedComponentIn_eq hmem).trans (connectedComponentIn_eq (hCompxfun p₀ hp₀mem)).symm
    exact hxne h1.symm
  have hSdisjInf : ∀ y : ExtPlane, y ∈ toExt (f '' S) →
      y ∈ connectedComponentIn (toExt B)ᶜ extInf → False := by
    intro y hyS hyInf
    exact (connectedComponentIn_subset _ _ hyInf) (hSsubtoExtB hyS)
  have hextract : ∀ y : ExtPlane, y ∈ toExt (f '' S) ∪ {(f p₀ : ExtPlane), (f q : ExtPlane)} →
      y ∈ connectedComponentIn (toExt B)ᶜ extInf → y = (f q : ExtPlane) := by
    intro y hy2 hyInf
    rcases hy2 with hy2 | hy2
    · exact (hSdisjInf y hy2 hyInf).elim
    · rcases hy2 with hy2 | hy2
      · exact absurd (hy2 ▸ hyInf) hp₀notinf
      · exact hy2
  have hne1 : (f q : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ extInf := by
    rcases gsep_end_correspondence hr hrR hBdc hf' hxmem hxne with hem | hem
    · have h := hem.2.1 S₀ hS0sub hScondOuter
      rw [hfSeq] at h
      obtain ⟨y, hycl, hyInf⟩ := h
      rw [← hextract y (hclosurebound hycl) hyInf]
      exact hyInf
    · have h := hem.1 S₀ hS0sub hScondInner
      rw [hfSeq] at h
      obtain ⟨y, hycl, hyInf⟩ := h
      rw [← hextract y (hclosurebound hycl) hyInf]
      exact hyInf
  have hfqmem : (f q : ExtPlane) ∈ (toExt B)ᶜ := connectedComponentIn_subset _ _ hne1
  exact ⟨hfqmem, (connectedComponentIn_eq hne1).symm⟩

theorem qcl_o_component_eq_extInf {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K)
    (hDc : IsConnected D) {z₀ : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hD : closedBall z₀ R ⊆ D) {z₃ : ℂ} (hz₃ : z₃ ∈ D) (hfar : R < ‖z₃ - z₀‖) :
    (f z₃ : ExtPlane) ∈ (toExt (f '' annulusAt z₀ r R))ᶜ ∧
      connectedComponentIn (toExt (f '' annulusAt z₀ r R))ᶜ (f z₃ : ExtPlane) =
        connectedComponentIn (toExt (f '' annulusAt z₀ r R))ᶜ extInf := by
  have hDopen : IsOpen D := hf.1
  have hcont : ContinuousOn f D := hf.2.2.1.1
  have hinj : InjOn f D := hf.2.2.1.2.1
  set B := f '' annulusAt z₀ r R with hBdef
  have hz₀D : z₀ ∈ D := hD (mem_closedBall_self (hr.trans hrR).le)
  have hpc : IsPathConnected D := hDopen.isConnected_iff_isPathConnected.1 hDc
  set γp := (hpc.joinedIn z₃ hz₃ z₀ hz₀D).somePath with hγpdef
  set φ : ℝ → ℂ := fun t => γp (projIcc 0 1 zero_le_one t) with hφdef
  have hφc : Continuous φ := γp.continuous.comp continuous_projIcc
  have hφD : ∀ t, φ t ∈ D := fun t => (hpc.joinedIn z₃ hz₃ z₀ hz₀D).somePath_mem _
  have hφ0 : φ 0 = z₃ := by simp only [hφdef, projIcc_left]; exact γp.source
  have hφ1 : φ 1 = z₀ := by simp only [hφdef, projIcc_right]; exact γp.target
  set T : Set ℝ := {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ ‖φ t - z₀‖ ≤ R} with hTdef
  have hTclosed : IsClosed T :=
    isClosed_Icc.inter (isClosed_le (hφc.sub continuous_const).norm continuous_const)
  have hTne : T.Nonempty := ⟨1, ⟨zero_le_one, le_refl 1⟩, by
    rw [hφ1, sub_self, norm_zero]; exact (hr.trans hrR).le⟩
  have hTbdd : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
  set t' := sInf T with ht'def
  have ht'T : t' ∈ T := hTclosed.csInf_mem hTne hTbdd
  have ht'Icc : t' ∈ Icc (0 : ℝ) 1 := ht'T.1
  have ht'le : ‖φ t' - z₀‖ ≤ R := ht'T.2
  have h0notT : (0 : ℝ) ∉ T := by
    rintro ⟨-, h2⟩
    rw [hφ0] at h2
    linarith [hfar]
  have ht'pos : 0 < t' := by
    rcases lt_or_eq_of_le ht'Icc.1 with h | h
    · exact h
    · exact absurd (h ▸ ht'T) h0notT
  have hbelow : ∀ t : ℝ, 0 ≤ t → t < t' → R < ‖φ t - z₀‖ := by
    intro t ht0 htt'
    by_contra hcon
    push Not at hcon
    have htT : t ∈ T := ⟨⟨ht0, htt'.le.trans ht'Icc.2⟩, hcon⟩
    have hle := csInf_le hTbdd htT
    linarith [hle, htt']
  have ht'eq : ‖φ t' - z₀‖ = R := by
    apply le_antisymm ht'le
    have hcont2 : ContinuousAt (fun t => ‖φ t - z₀‖) t' := (hφc.sub continuous_const).norm.continuousAt
    have htendsto : Tendsto (fun t => ‖φ t - z₀‖) (𝓝[<] t') (𝓝 (‖φ t' - z₀‖)) :=
      hcont2.tendsto.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[<] t', R ≤ ‖φ t - z₀‖ := by
      have h1 : Ioi (0 : ℝ) ∈ 𝓝 t' := isOpen_Ioi.mem_nhds ht'pos
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h1] with t htlt htpos
      exact (hbelow t htpos.le htlt).le
    exact ge_of_tendsto htendsto hev
  set q : ℂ := φ t' with hqdef
  obtain ⟨hqmem, hqeq⟩ := qcl_o_outer_end hf hr hrR hD ht'eq
  have hPconn : IsPreconnected (φ '' Icc (0 : ℝ) t') :=
    isPreconnected_Icc.image φ hφc.continuousOn
  have hPsubD : φ '' Icc (0 : ℝ) t' ⊆ D := by
    rintro _ ⟨t, -, rfl⟩; exact hφD t
  have hPsubext : φ '' Icc (0 : ℝ) t' ⊆ {z : ℂ | R ≤ ‖z - z₀‖} := by
    rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
    rcases eq_or_lt_of_le ht1 with h | h
    · rw [h]; exact ht'eq.ge
    · exact (hbelow t ht0 h).le
  have hPdisjann : φ '' Icc (0 : ℝ) t' ∩ annulusAt z₀ r R = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz1, hz2⟩
    have h1 := hPsubext hz1
    exact absurd hz2.2 (not_lt.2 h1)
  have hEfBdisj : Disjoint (f '' (φ '' Icc (0 : ℝ) t')) B := by
    rw [hBdef, Set.disjoint_iff_inter_eq_empty,
      ← Set.InjOn.image_inter hinj hPsubD (fun z hz => hD (by
        rw [mem_closedBall, dist_eq_norm]; exact hz.2.le)), hPdisjann, Set.image_empty]
  have hPconnf : IsPreconnected (f '' (φ '' Icc (0 : ℝ) t')) :=
    hPconn.image f (hcont.mono hPsubD)
  have hPsub : toExt (f '' (φ '' Icc (0 : ℝ) t')) ⊆ (toExt B)ᶜ := by
    rintro _ ⟨z, hz, rfl⟩ hzB
    exact Set.disjoint_left.mp hEfBdisj hz (coe_mem_toExt_iff.mp hzB)
  have hqmemset : q ∈ φ '' Icc (0 : ℝ) t' := ⟨t', ⟨ht'pos.le, le_refl t'⟩, rfl⟩
  have hPsubCompFq :
      toExt (f '' (φ '' Icc (0 : ℝ) t')) ⊆ connectedComponentIn (toExt B)ᶜ (f q : ExtPlane) :=
    (hPconnf.image _ OnePoint.continuous_coe.continuousOn).subset_connectedComponentIn
      (coe_mem_toExt_iff.mpr (mem_image_of_mem f hqmemset)) hPsub
  have hPsubComp : toExt (f '' (φ '' Icc (0 : ℝ) t')) ⊆ connectedComponentIn (toExt B)ᶜ extInf := by
    rw [← hqeq]; exact hPsubCompFq
  have hz₃memset : z₃ ∈ φ '' Icc (0 : ℝ) t' := ⟨0, ⟨le_refl 0, ht'pos.le⟩, hφ0⟩
  have hfz₃mem : (f z₃ : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ extInf :=
    hPsubComp (coe_mem_toExt_iff.mpr (mem_image_of_mem f hz₃memset))
  exact ⟨connectedComponentIn_subset _ _ hfz₃mem, (connectedComponentIn_eq hfz₃mem).symm⟩



/-! ### Theorem 8.2 — helpers of piece G -/


theorem qcl_g_exists_inside_outside {γ : LRCurve} (hγ : γ.IsClosedCurve) {a b c : ℂ}
    (hab : a ≠ b) (ha : a ∉ γ.closedTrace) (hb : b ∉ γ.closedTrace) (hc : c ∉ γ.closedTrace)
    (hcw : c ≠ (a + b) / 2)
    (hsepab : connectedComponentIn (toExt γ.closedTrace)ᶜ (a : ExtPlane) ≠
      connectedComponentIn (toExt γ.closedTrace)ᶜ (b : ExtPlane))
    (hsepc : connectedComponentIn (toExt γ.closedTrace)ᶜ (c : ExtPlane) ≠
      connectedComponentIn (toExt γ.closedTrace)ᶜ extInf) :
    (∃ s₁ ∈ Icc (0 : ℝ) 1, ‖γ.toFun s₁ - (a + b) / 2‖ < ‖a - b‖ / 2) ∧
      ∃ s₂ ∈ Icc (0 : ℝ) 1, ‖c - (a + b) / 2‖ < ‖γ.toFun s₂ - (a + b) / 2‖ := by
  constructor
  · have haXc : (a : ExtPlane) ∈ (toExt γ.closedTrace)ᶜ := coe_mem_compl_toExt_iff.mpr ha
    have hseg_conn : IsPreconnected (toExt (segment ℝ a b)) :=
      (convex_segment a b).isPreconnected.image _ OnePoint.continuous_coe.continuousOn
    have haseg : a ∈ segment ℝ a b := left_mem_segment ℝ a b
    have hbseg : b ∈ segment ℝ a b := right_mem_segment ℝ a b
    have hmeets : (toExt (segment ℝ a b) ∩ toExt γ.closedTrace).Nonempty := by
      by_contra hdisj
      rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] at hdisj
      have hsub : toExt (segment ℝ a b) ⊆ (toExt γ.closedTrace)ᶜ := Set.disjoint_left.mp hdisj
      have hsubComp :
          toExt (segment ℝ a b) ⊆ connectedComponentIn (toExt γ.closedTrace)ᶜ (a : ExtPlane) :=
        hseg_conn.subset_connectedComponentIn (mem_image_of_mem _ haseg) hsub
      have hbComp : (b : ExtPlane) ∈ connectedComponentIn (toExt γ.closedTrace)ᶜ (a : ExtPlane) :=
        hsubComp (mem_image_of_mem _ hbseg)
      exact hsepab (connectedComponentIn_eq hbComp)
    obtain ⟨w0, hw1, hw2⟩ := hmeets
    obtain ⟨z, hzseg, hzw0⟩ := hw1
    rw [← hzw0] at hw2
    have hzc0 : z ∈ γ.closedTrace := coe_mem_toExt_iff.mp hw2
    obtain ⟨s₁, hs₁, hzeq⟩ := hzc0
    refine ⟨s₁, hs₁, ?_⟩
    rw [hzeq]
    obtain ⟨t1, t2, ht10, ht20, ht12, hzform⟩ := hzseg
    have hzc : z ∈ γ.closedTrace := ⟨s₁, hs₁, hzeq⟩
    have hzne_a : z ≠ a := fun heq => ha (heq ▸ hzc)
    have hzne_b : z ≠ b := fun heq => hb (heq ▸ hzc)
    have ht2le1 : t2 ≤ 1 := by linarith [ht10, ht12]
    have ht2ne0 : t2 ≠ 0 := by
      intro h0
      apply hzne_a
      have ht1eq : t1 = 1 := by linarith [ht12, h0]
      rw [← hzform, ht1eq, h0]
      simp
    have ht2ne1 : t2 ≠ 1 := by
      intro h1
      apply hzne_b
      have ht1eq : t1 = 0 := by linarith [ht12, h1]
      rw [← hzform, ht1eq, h1]
      simp
    have ht2pos : 0 < t2 := lt_of_le_of_ne ht20 (Ne.symm ht2ne0)
    have ht2lt1 : t2 < 1 := lt_of_le_of_ne ht2le1 ht2ne1
    have hzval : z = a + (t2 : ℂ) * (b - a) := by
      have ht1eq : t1 = 1 - t2 := by linarith [ht12]
      rw [← hzform, ht1eq]
      simp only [Complex.real_smul]
      push_cast
      ring
    rw [hzval]
    have hcomp : a + (t2 : ℂ) * (b - a) - (a + b) / 2 = ((t2 - 1/2 : ℝ) : ℂ) * (b - a) := by
      push_cast
      ring
    rw [hcomp, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have habs : |t2 - 1/2| < 1/2 := by rw [abs_lt]; constructor <;> linarith
    have hnormba : ‖b - a‖ = ‖a - b‖ := norm_sub_rev b a
    rw [hnormba]
    calc |t2 - 1/2| * ‖a - b‖ < (1/2) * ‖a - b‖ := by
          rcases eq_or_lt_of_le (norm_nonneg (a - b)) with h0 | h0
          · exfalso; apply hab; rw [← sub_eq_zero]; exact norm_eq_zero.mp h0.symm
          · exact mul_lt_mul_of_pos_right habs h0
      _ = ‖a - b‖ / 2 := by ring
  · set w := (a + b) / 2 with hwdef
    have hcw' : c - w ≠ 0 := sub_ne_zero.2 hcw
    have hcwnorm : 0 < ‖c - w‖ := norm_pos_iff.2 hcw'
    set u : ℂ := (c - w) / (‖c - w‖ : ℂ) with hudef
    have hunorm : ‖u‖ = 1 := by
      rw [hudef, norm_div]
      have hcast : ‖(‖c - w‖ : ℂ)‖ = ‖c - w‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcwnorm]
      rw [hcast]
      exact div_self hcwnorm.ne'
    obtain ⟨t, ht, ρ, hρpos, hEq⟩ := nf_c_exists_mem_ray_of_separates hγ hc hsepc hunorm
    refine ⟨t, ht, ?_⟩
    have hcweq : c - w = (‖c - w‖ : ℂ) * u := by
      rw [hudef]
      have hne : (‖c - w‖ : ℂ) ≠ 0 := by exact_mod_cast hcwnorm.ne'
      field_simp
    have heq2 : γ.toFun t - w = ((‖c - w‖ + ρ : ℝ) : ℂ) * u := by
      rw [hEq]
      push_cast
      rw [add_mul, ← hcweq]
      ring
    rw [heq2, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [hcwnorm, hρpos] : (0:ℝ) < ‖c - w‖ + ρ), hunorm, mul_one]
    linarith [hρpos]



/-! ### Theorem 8.2 — helpers of piece L -/

theorem qcl_l_log_sub_le_lintegral {γ : LRCurve} (hγ : γ.IsClosedCurve) (ζ : ℂ) {c d : ℝ}
    (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) (hne : ∀ t ∈ Icc c d, γ.toFun t ≠ ζ) :
    ENNReal.ofReal |Real.log ‖γ.toFun d - ζ‖ - Real.log ‖γ.toFun c - ζ‖| ≤
      ∫⁻ t in Ioo c d, ENNReal.ofReal (1 / ‖γ.toFun t - ζ‖) * ‖deriv γ.toFun t‖ₑ := by
  obtain ⟨K, hKLip, -⟩ := hγ
  have hKIcc : LipschitzOnWith K γ.toFun (Icc (0:ℝ) 1) := hKLip
  have hsub : Icc c d ⊆ Icc (0:ℝ) 1 := Icc_subset_Icc hc hd
  have hKcd : LipschitzOnWith K γ.toFun (Icc c d) := hKIcc.mono hsub
  have hcont : ContinuousOn (fun u => γ.toFun u - ζ) (Icc c d) :=
    hKcd.continuousOn.sub continuousOn_const
  obtain ⟨a, ha, hamin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hcd) hcont.norm
  set m := ‖γ.toFun a - ζ‖ with hmdef
  have hm0 : 0 < m := norm_pos_iff.2 (sub_ne_zero.2 (hne a ha))
  have hmb : ∀ u ∈ Icc c d, m ≤ ‖γ.toFun u - ζ‖ := fun u hu => isMinOn_iff.1 hamin u hu
  have hnormLip : LipschitzOnWith K (fun u => ‖γ.toFun u - ζ‖) (Icc c d) := by
    rw [lipschitzOnWith_iff_dist_le_mul] at hKcd ⊢
    intro x hx y hy
    calc dist ‖γ.toFun x - ζ‖ ‖γ.toFun y - ζ‖ ≤ dist (γ.toFun x - ζ) (γ.toFun y - ζ) := by
          rw [Real.dist_eq, Complex.dist_eq]; exact abs_norm_sub_norm_le _ _
      _ = dist (γ.toFun x) (γ.toFun y) := by
          rw [Complex.dist_eq, Complex.dist_eq, sub_sub_sub_cancel_right]
      _ ≤ K * dist x y := hKcd x hx y hy
  have hmaps : Set.MapsTo (fun u => ‖γ.toFun u - ζ‖) (Icc c d) (Set.Ici m) := fun u hu => hmb u hu
  have hKL : LipschitzOnWith ((1/m).toNNReal * K) (fun u => Real.log ‖γ.toFun u - ζ‖) (uIcc c d) := by
    rw [uIcc_of_le hcd]
    exact (aqc_log_lipschitzOnWith m hm0).comp hnormLip hmaps
  have hftc : ∫ u in c..d, deriv (fun u => Real.log ‖γ.toFun u - ζ‖) u =
      Real.log ‖γ.toFun d - ζ‖ - Real.log ‖γ.toFun c - ζ‖ :=
    hKL.absolutelyContinuousOnInterval.integral_deriv_eq_sub
  have hA := LocallyLipschitzOn.ae_differentiableAt_Ioo γ.locallyLipschitzOn
  rw [← hftc, intervalIntegral.integral_of_le hcd, ← Real.norm_eq_abs, ofReal_norm]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← setLIntegral_congr Ioo_ae_eq_Ioc]
  refine setLIntegral_mono_ae' measurableSet_Ioo ?_
  filter_upwards [hA] with u hu huI
  have hu01 : u ∈ Ioo (0:ℝ) 1 := ⟨hc.trans_lt huI.1, huI.2.trans_le hd⟩
  have hune : γ.toFun u ≠ ζ := hne u ⟨huI.1.le, huI.2.le⟩
  have hshift : HasDerivAt (fun s => γ.toFun s - ζ) (deriv γ.toFun u) u :=
    (hu hu01).hasDerivAt.sub_const ζ
  have hderiv : HasDerivAt (fun s => Real.log ‖γ.toFun s - ζ‖)
      (deriv γ.toFun u / (γ.toFun u - ζ)).re u :=
    aqc_hasDerivAt_log_norm (sub_ne_zero.2 hune) hshift
  rw [hderiv.deriv, ← ofReal_norm]
  have hbound : |(deriv γ.toFun u / (γ.toFun u - ζ)).re| ≤
      ‖deriv γ.toFun u‖ / ‖γ.toFun u - ζ‖ := by
    rw [← norm_div]; exact Complex.abs_re_le_norm _
  calc ENNReal.ofReal |(deriv γ.toFun u / (γ.toFun u - ζ)).re|
      ≤ ENNReal.ofReal (‖deriv γ.toFun u‖ / ‖γ.toFun u - ζ‖) := ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal (1 / ‖γ.toFun u - ζ‖) * ‖deriv γ.toFun u‖ₑ := by
        rw [← ofReal_norm (deriv γ.toFun u), div_eq_mul_one_div, mul_comm,
          ENNReal.ofReal_mul (by positivity)]

theorem qcl_l_clamp_le_lintegral {γ : LRCurve} (hγ : γ.IsClosedCurve) (ζ : ℂ) {Δ Δ' : ℝ}
    (hΔ : 0 < Δ) (hΔΔ' : Δ < Δ') {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) :
    ENNReal.ofReal |Real.log (max Δ (min Δ' ‖γ.toFun d - ζ‖)) -
        Real.log (max Δ (min Δ' ‖γ.toFun c - ζ‖))| ≤
      ∫⁻ t in Ioo c d, (annulusAt ζ Δ Δ').indicator (fun w => ENNReal.ofReal (1 / ‖w - ζ‖))
        (γ.toFun t) * ‖deriv γ.toFun t‖ₑ := by
  have hγ' := hγ
  obtain ⟨K, hKLip, -⟩ := hγ
  set r : ℝ → ℝ := fun t => ‖γ.toFun t - ζ‖ with hrdef
  set clamp : ℝ → ℝ := fun x => max Δ (min Δ' x) with hclampdef
  set α := clamp (r c) with hαdef
  set β := clamp (r d) with hβdef
  have hclampge : ∀ x, Δ ≤ clamp x := fun x => le_max_left _ _
  have hclampleΔ' : ∀ x, clamp x ≤ Δ' := fun x => by
    rw [hclampdef]; exact max_le hΔΔ'.le (min_le_left _ _)
  have hrcont : ContinuousOn r (Icc (0:ℝ) 1) := (hKLip.continuousOn.sub continuousOn_const).norm
  have key : ∀ p q : ℝ, p ∈ Icc c d → q ∈ Icc c d → p ≤ q → clamp (r p) < clamp (r q) →
      ENNReal.ofReal (Real.log (clamp (r q)) - Real.log (clamp (r p))) ≤
        ∫⁻ t in Ioo c d, (annulusAt ζ Δ Δ').indicator (fun w => ENNReal.ofReal (1 / ‖w - ζ‖))
          (γ.toFun t) * ‖deriv γ.toFun t‖ₑ := by
    intro p q hp hq hpq hlt
    set αq := clamp (r p) with hαqdef
    set βq := clamp (r q) with hβqdef
    have hrq_ge : βq ≤ r q := by
      rcases le_or_gt (r q) Δ with h | h
      · exfalso
        have hβq_eq : βq = Δ := by
          show max Δ (min Δ' (r q)) = Δ
          rw [min_eq_right (h.trans hΔΔ'.le)]
          exact max_eq_left h
        linarith [hclampge (r p), hβq_eq]
      · rcases le_or_gt (r q) Δ' with h2 | h2
        · show max Δ (min Δ' (r q)) ≤ r q
          rw [min_eq_right h2]
          exact max_le h.le le_rfl
        · show max Δ (min Δ' (r q)) ≤ r q
          rw [min_eq_left h2.le]
          exact max_le h.le h2.le
    have hrp_le : r p ≤ αq := by
      rcases le_or_gt (r p) Δ with h | h
      · show r p ≤ max Δ (min Δ' (r p))
        rw [min_eq_right (h.trans hΔΔ'.le)]
        rw [max_eq_left h]
        exact h
      · rcases le_or_gt (r p) Δ' with h2 | h2
        · show r p ≤ max Δ (min Δ' (r p))
          rw [min_eq_right h2]
          exact le_max_right _ _
        · exfalso
          have hαq_eq : αq = Δ' := by
            show max Δ (min Δ' (r p)) = Δ'
            rw [min_eq_left h2.le]
            exact max_eq_right hΔΔ'.le
          linarith [hclampleΔ' (r q), hαq_eq]
    have hpq01 : Icc p q ⊆ Icc (0:ℝ) 1 := Icc_subset_Icc (hc.trans hp.1) (hq.2.trans hd)
    have hrcontpq : ContinuousOn r (Icc p q) := hrcont.mono hpq01
    set Sb : Set ℝ := Icc p q ∩ r ⁻¹' (Ici βq) with hSbdef
    have hSbne : Sb.Nonempty := ⟨q, ⟨right_mem_Icc.2 hpq, hrq_ge⟩⟩
    have hSbclosed : IsClosed Sb :=
      hrcontpq.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hSbcompact : IsCompact Sb :=
      IsCompact.of_isClosed_subset isCompact_Icc hSbclosed inter_subset_left
    obtain ⟨b, ⟨hbSb, hblb⟩⟩ := hSbcompact.exists_isLeast hSbne
    obtain ⟨hbIcc, hbr⟩ := hbSb
    rw [Set.mem_preimage, Set.mem_Ici] at hbr
    have hpb : p ≤ b := hbIcc.1
    have hab01 : Icc p b ⊆ Icc (0:ℝ) 1 :=
      Icc_subset_Icc (hc.trans hp.1) (hbIcc.2.trans (hq.2.trans hd))
    have hrcontab : ContinuousOn r (Icc p b) := hrcont.mono hab01
    set Sa : Set ℝ := Icc p b ∩ r ⁻¹' (Iic αq) with hSadef
    have hSane : Sa.Nonempty := ⟨p, ⟨left_mem_Icc.2 hpb, hrp_le⟩⟩
    have hSaclosed : IsClosed Sa :=
      hrcontab.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hSacompact : IsCompact Sa :=
      IsCompact.of_isClosed_subset isCompact_Icc hSaclosed inter_subset_left
    obtain ⟨a, ⟨haSa, haub⟩⟩ := hSacompact.exists_isGreatest hSane
    obtain ⟨haIcc, har⟩ := haSa
    rw [Set.mem_preimage, Set.mem_Iic] at har
    have hab_le : a ≤ b := haIcc.2
    have hane : a ≠ b := by
      rintro rfl
      linarith [hbr, har]
    have hab_lt : a < b := lt_of_le_of_ne hab_le hane
    have hmid : ∀ t ∈ Ioo a b, αq < r t ∧ r t < βq := by
      intro t ht
      have htp : p ≤ t := haIcc.1.trans ht.1.le
      have htq : t ≤ q := ht.2.le.trans hbIcc.2
      have htb : t ≤ b := ht.2.le
      refine ⟨?_, ?_⟩
      · by_contra hle
        push Not at hle
        exact absurd (haub ⟨⟨htp, htb⟩, hle⟩) (not_le.2 ht.1)
      · by_contra hge
        push Not at hge
        exact absurd (hblb ⟨⟨htp, htq⟩, hge⟩) (not_le.2 ht.2)
    have hab01' : Icc a b ⊆ Icc (0:ℝ) 1 :=
      Icc_subset_Icc (hc.trans (hp.1.trans haIcc.1)) (hbIcc.2.trans (hq.2.trans hd))
    have hareq_ge : αq ≤ r a := by
      have hclosedSet : IsClosed (Icc a b ∩ r ⁻¹' (Ici αq)) :=
        (hrcont.mono hab01').preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
      have hsub : Ioo a b ⊆ Icc a b ∩ r ⁻¹' (Ici αq) := fun t ht =>
        ⟨Ioo_subset_Icc_self ht, (hmid t ht).1.le⟩
      have hmem : a ∈ closure (Ioo a b) := by
        rw [closure_Ioo hab_lt.ne]; exact left_mem_Icc.2 hab_lt.le
      exact (hclosedSet.closure_subset_iff.2 hsub hmem).2
    have hareq : r a = αq := le_antisymm har hareq_ge
    have hΔr : ∀ t ∈ Icc a b, Δ ≤ r t := by
      intro t ht
      rcases ht.1.eq_or_lt with h1 | h1
      · rw [← h1, hareq]; exact hclampge (r p)
      · rcases ht.2.eq_or_lt with h2 | h2
        · rw [h2]; exact (hclampge (r q)).trans hbr
        · exact (hclampge (r p)).trans (hmid t ⟨h1, h2⟩).1.le
    have hne_ab : ∀ t ∈ Icc a b, γ.toFun t ≠ ζ := fun t ht =>
      sub_ne_zero.1 (norm_pos_iff.1 (hΔ.trans_le (hΔr t ht)))
    have ha0 : 0 ≤ a := hc.trans (hp.1.trans haIcc.1)
    have hb1 : b ≤ 1 := hbIcc.2.trans (hq.2.trans hd)
    have hL1 := qcl_l_log_sub_le_lintegral hγ' ζ ha0 hab_le hb1 hne_ab
    have hβqpos : 0 < βq := hΔ.trans_le (hclampge (r q))
    have hαqpos : 0 < αq := hΔ.trans_le (hclampge (r p))
    have hlogmono : Real.log βq ≤ Real.log (r b) := Real.log_le_log hβqpos hbr
    have hlogstrict : Real.log αq < Real.log βq := Real.log_lt_log hαqpos hlt
    have hdiffnn : 0 ≤ Real.log (r b) - Real.log (r a) := by rw [hareq]; linarith
    have habs : |Real.log (r b) - Real.log (r a)| = Real.log (r b) - Real.log (r a) :=
      abs_of_nonneg hdiffnn
    rw [habs] at hL1
    have hfinal_le : ENNReal.ofReal (Real.log βq - Real.log αq) ≤
        ENNReal.ofReal (Real.log (r b) - Real.log (r a)) :=
      ENNReal.ofReal_le_ofReal (by rw [hareq]; linarith)
    have hkey_bound := hfinal_le.trans hL1
    have hindic : ∀ t ∈ Ioo a b, γ.toFun t ∈ annulusAt ζ Δ Δ' := by
      intro t ht
      obtain ⟨h1, h2⟩ := hmid t ht
      exact ⟨lt_of_le_of_lt (hclampge (r p)) h1, lt_of_lt_of_le h2 (hclampleΔ' (r q))⟩
    have heqon : ∀ t ∈ Ioo a b, ENNReal.ofReal (1 / ‖γ.toFun t - ζ‖) * ‖deriv γ.toFun t‖ₑ =
        (annulusAt ζ Δ Δ').indicator (fun w => ENNReal.ofReal (1 / ‖w - ζ‖)) (γ.toFun t) *
          ‖deriv γ.toFun t‖ₑ := by
      intro t ht
      rw [indicator_of_mem (hindic t ht)]
    have hintAB : ∫⁻ t in Ioo a b, ENNReal.ofReal (1 / ‖γ.toFun t - ζ‖) * ‖deriv γ.toFun t‖ₑ ≤
        ∫⁻ t in Ioo c d, (annulusAt ζ Δ Δ').indicator (fun w => ENNReal.ofReal (1 / ‖w - ζ‖))
          (γ.toFun t) * ‖deriv γ.toFun t‖ₑ := by
      rw [setLIntegral_congr_fun measurableSet_Ioo heqon]
      apply lintegral_mono_set
      intro t ht
      exact ⟨lt_of_le_of_lt (hp.1.trans haIcc.1) ht.1, lt_of_lt_of_le ht.2 (hbIcc.2.trans hq.2)⟩
    exact hkey_bound.trans hintAB
  have key' : ∀ p q : ℝ, p ∈ Icc c d → q ∈ Icc c d → p ≤ q → clamp (r q) < clamp (r p) →
      ENNReal.ofReal (Real.log (clamp (r p)) - Real.log (clamp (r q))) ≤
        ∫⁻ t in Ioo c d, (annulusAt ζ Δ Δ').indicator (fun w => ENNReal.ofReal (1 / ‖w - ζ‖))
          (γ.toFun t) * ‖deriv γ.toFun t‖ₑ := by
    intro p q hp hq hpq hgt'
    set αq := clamp (r p) with hαqdef
    set βq := clamp (r q) with hβqdef
    have hrp_ge : αq ≤ r p := by
      rcases le_or_gt (r p) Δ with h | h
      · exfalso
        have hαq_eq : αq = Δ := by
          show max Δ (min Δ' (r p)) = Δ
          rw [min_eq_right (h.trans hΔΔ'.le)]
          exact max_eq_left h
        linarith [hclampge (r q), hαq_eq]
      · rcases le_or_gt (r p) Δ' with h2 | h2
        · show max Δ (min Δ' (r p)) ≤ r p
          rw [min_eq_right h2]
          exact max_le h.le le_rfl
        · show max Δ (min Δ' (r p)) ≤ r p
          rw [min_eq_left h2.le]
          exact max_le h.le h2.le
    have hrq_le : r q ≤ βq := by
      rcases le_or_gt (r q) Δ with h | h
      · show r q ≤ max Δ (min Δ' (r q))
        rw [min_eq_right (h.trans hΔΔ'.le)]
        rw [max_eq_left h]
        exact h
      · rcases le_or_gt (r q) Δ' with h2 | h2
        · show r q ≤ max Δ (min Δ' (r q))
          rw [min_eq_right h2]
          exact le_max_right _ _
        · exfalso
          have hβq_eq : βq = Δ' := by
            show max Δ (min Δ' (r q)) = Δ'
            rw [min_eq_left h2.le]
            exact max_eq_right hΔΔ'.le
          linarith [hclampleΔ' (r p), hβq_eq]
    have hpq01 : Icc p q ⊆ Icc (0:ℝ) 1 := Icc_subset_Icc (hc.trans hp.1) (hq.2.trans hd)
    have hrcontpq : ContinuousOn r (Icc p q) := hrcont.mono hpq01
    set Sa : Set ℝ := Icc p q ∩ r ⁻¹' (Ici αq) with hSadef
    have hSane : Sa.Nonempty := ⟨p, ⟨left_mem_Icc.2 hpq, hrp_ge⟩⟩
    have hSaclosed : IsClosed Sa :=
      hrcontpq.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hSacompact : IsCompact Sa :=
      IsCompact.of_isClosed_subset isCompact_Icc hSaclosed inter_subset_left
    obtain ⟨a, ⟨haSa, haub⟩⟩ := hSacompact.exists_isGreatest hSane
    obtain ⟨haIcc, har⟩ := haSa
    rw [Set.mem_preimage, Set.mem_Ici] at har
    have haq : a ≤ q := haIcc.2
    have hab01 : Icc a q ⊆ Icc (0:ℝ) 1 :=
      Icc_subset_Icc (hc.trans (hp.1.trans haIcc.1)) (hq.2.trans hd)
    have hrcontaq : ContinuousOn r (Icc a q) := hrcont.mono hab01
    set Sb : Set ℝ := Icc a q ∩ r ⁻¹' (Iic βq) with hSbdef
    have hSbne : Sb.Nonempty := ⟨q, ⟨right_mem_Icc.2 haq, hrq_le⟩⟩
    have hSbclosed : IsClosed Sb :=
      hrcontaq.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hSbcompact : IsCompact Sb :=
      IsCompact.of_isClosed_subset isCompact_Icc hSbclosed inter_subset_left
    obtain ⟨b, ⟨hbSb, hblb⟩⟩ := hSbcompact.exists_isLeast hSbne
    obtain ⟨hbIcc, hbr⟩ := hbSb
    rw [Set.mem_preimage, Set.mem_Iic] at hbr
    have hab_le : a ≤ b := hbIcc.1
    have hane : a ≠ b := by
      rintro rfl
      linarith [hbr, har]
    have hab_lt : a < b := lt_of_le_of_ne hab_le hane
    have hmid : ∀ t ∈ Ioo a b, βq < r t ∧ r t < αq := by
      intro t ht
      have hta : a ≤ t := ht.1.le
      have htq : t ≤ q := ht.2.le.trans hbIcc.2
      refine ⟨?_, ?_⟩
      · by_contra hle
        push Not at hle
        exact absurd (hblb ⟨⟨hta, htq⟩, hle⟩) (not_le.2 ht.2)
      · by_contra hge
        push Not at hge
        have htp' : p ≤ t := haIcc.1.trans ht.1.le
        exact absurd (haub ⟨⟨htp', htq⟩, hge⟩) (not_le.2 ht.1)
    have hab01' : Icc a b ⊆ Icc (0:ℝ) 1 :=
      Icc_subset_Icc (hc.trans (hp.1.trans haIcc.1)) (hbIcc.2.trans (hq.2.trans hd))
    have hbreq_ge : βq ≤ r b := by
      have hclosedSet : IsClosed (Icc a b ∩ r ⁻¹' (Ici βq)) :=
        (hrcont.mono hab01').preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
      have hsub : Ioo a b ⊆ Icc a b ∩ r ⁻¹' (Ici βq) := fun t ht =>
        ⟨Ioo_subset_Icc_self ht, (hmid t ht).1.le⟩
      have hmem : b ∈ closure (Ioo a b) := by
        rw [closure_Ioo hab_lt.ne]; exact right_mem_Icc.2 hab_lt.le
      exact (hclosedSet.closure_subset_iff.2 hsub hmem).2
    have hbreq : r b = βq := le_antisymm hbr hbreq_ge
    have hΔr : ∀ t ∈ Icc a b, Δ ≤ r t := by
      intro t ht
      rcases ht.2.eq_or_lt with h1 | h1
      · rw [h1, hbreq]; exact hclampge (r q)
      · rcases ht.1.eq_or_lt with h2 | h2
        · rw [← h2]; exact (hclampge (r p)).trans har
        · exact (hclampge (r q)).trans (hmid t ⟨h2, h1⟩).1.le
    have hne_ab : ∀ t ∈ Icc a b, γ.toFun t ≠ ζ := fun t ht =>
      sub_ne_zero.1 (norm_pos_iff.1 (hΔ.trans_le (hΔr t ht)))
    have ha0 : 0 ≤ a := hc.trans (hp.1.trans haIcc.1)
    have hb1 : b ≤ 1 := hbIcc.2.trans (hq.2.trans hd)
    have hL1 := qcl_l_log_sub_le_lintegral hγ' ζ ha0 hab_le hb1 hne_ab
    have hαqpos : 0 < αq := hΔ.trans_le (hclampge (r p))
    have hβqpos : 0 < βq := hΔ.trans_le (hclampge (r q))
    have hlogmono : Real.log αq ≤ Real.log (r a) := Real.log_le_log hαqpos har
    have hlogstrict : Real.log βq < Real.log αq := Real.log_lt_log hβqpos hgt'
    have hdiffnn : 0 ≤ Real.log (r a) - Real.log (r b) := by rw [hbreq]; linarith
    have habs : |Real.log (r b) - Real.log (r a)| = Real.log (r a) - Real.log (r b) := by
      rw [abs_sub_comm]; exact abs_of_nonneg hdiffnn
    rw [habs] at hL1
    have hfinal_le : ENNReal.ofReal (Real.log αq - Real.log βq) ≤
        ENNReal.ofReal (Real.log (r a) - Real.log (r b)) :=
      ENNReal.ofReal_le_ofReal (by rw [hbreq]; linarith)
    have hkey_bound := hfinal_le.trans hL1
    have hindic : ∀ t ∈ Ioo a b, γ.toFun t ∈ annulusAt ζ Δ Δ' := by
      intro t ht
      obtain ⟨h1, h2⟩ := hmid t ht
      exact ⟨lt_of_le_of_lt (hclampge (r q)) h1, lt_of_lt_of_le h2 (hclampleΔ' (r p))⟩
    have heqon : ∀ t ∈ Ioo a b, ENNReal.ofReal (1 / ‖γ.toFun t - ζ‖) * ‖deriv γ.toFun t‖ₑ =
        (annulusAt ζ Δ Δ').indicator (fun w => ENNReal.ofReal (1 / ‖w - ζ‖)) (γ.toFun t) *
          ‖deriv γ.toFun t‖ₑ := by
      intro t ht
      rw [indicator_of_mem (hindic t ht)]
    have hintAB : ∫⁻ t in Ioo a b, ENNReal.ofReal (1 / ‖γ.toFun t - ζ‖) * ‖deriv γ.toFun t‖ₑ ≤
        ∫⁻ t in Ioo c d, (annulusAt ζ Δ Δ').indicator (fun w => ENNReal.ofReal (1 / ‖w - ζ‖))
          (γ.toFun t) * ‖deriv γ.toFun t‖ₑ := by
      rw [setLIntegral_congr_fun measurableSet_Ioo heqon]
      apply lintegral_mono_set
      intro t ht
      exact ⟨lt_of_le_of_lt (hp.1.trans haIcc.1) ht.1, lt_of_lt_of_le ht.2 (hbIcc.2.trans hq.2)⟩
    exact hkey_bound.trans hintAB
  show ENNReal.ofReal |Real.log β - Real.log α| ≤
      ∫⁻ t in Ioo c d, (annulusAt ζ Δ Δ').indicator (fun w => ENNReal.ofReal (1 / ‖w - ζ‖))
        (γ.toFun t) * ‖deriv γ.toFun t‖ₑ
  have hαpos : 0 < α := hΔ.trans_le (hclampge (r c))
  have hβpos : 0 < β := hΔ.trans_le (hclampge (r d))
  rcases lt_trichotomy α β with hlt | heq | hgt
  · have hloglt : Real.log α < Real.log β := Real.log_lt_log hαpos hlt
    rw [abs_of_pos (by linarith : (0:ℝ) < Real.log β - Real.log α)]
    exact key c d (left_mem_Icc.2 hcd) (right_mem_Icc.2 hcd) hcd hlt
  · rw [heq, sub_self, abs_zero, ENNReal.ofReal_zero]
    exact bot_le
  · have hloggt : Real.log β < Real.log α := Real.log_lt_log hβpos hgt
    rw [abs_of_neg (by linarith : Real.log β - Real.log α < 0), neg_sub]
    exact key' c d (left_mem_Icc.2 hcd) (right_mem_Icc.2 hcd) hcd hgt

theorem qcl_l_one_le_rhoLength {γ : LRCurve} (hγ : γ.IsClosedCurve) (ζ : ℂ) {Δ Δ' : ℝ}
    (hΔ : 0 < Δ) (hΔΔ' : Δ < Δ') {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Icc (0 : ℝ) 1)
    (hs₂ : s₂ ∈ Icc (0 : ℝ) 1) (hin : ‖γ.toFun s₁ - ζ‖ < Δ) (hout : Δ' < ‖γ.toFun s₂ - ζ‖) :
    1 ≤ γ.rhoLength (fun w => (annulusAt ζ Δ Δ').indicator
      (fun w => ENNReal.ofReal (1 / (2 * Real.log (Δ' / Δ) * ‖w - ζ‖))) w) := by
  have hγ' := hγ
  obtain ⟨K, hKLip, hclosed⟩ := hγ
  set r : ℝ → ℝ := fun t => ‖γ.toFun t - ζ‖ with hrdef
  set clamp : ℝ → ℝ := fun x => max Δ (min Δ' x) with hclampdef
  have hclampge : ∀ x, Δ ≤ clamp x := fun x => le_max_left _ _
  set L := Real.log (Δ' / Δ) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]; exact Real.log_pos ((one_lt_div hΔ).2 hΔΔ')
  have hclamp_s1 : clamp (r s₁) = Δ := by
    show max Δ (min Δ' (r s₁)) = Δ
    rw [min_eq_right (hin.le.trans hΔΔ'.le)]
    exact max_eq_left hin.le
  have hclamp_s2 : clamp (r s₂) = Δ' := by
    show max Δ (min Δ' (r s₂)) = Δ'
    rw [min_eq_left hout.le]
    exact max_eq_right hΔΔ'.le
  have hr01 : r 0 = r 1 := by
    show ‖γ.toFun 0 - ζ‖ = ‖γ.toFun 1 - ζ‖
    rw [hclosed]
  have hκ : clamp (r 1) = clamp (r 0) := by rw [hr01]
  set X : ℝ≥0∞ := ∫⁻ t in Ioo (0:ℝ) 1, (annulusAt ζ Δ Δ').indicator
    (fun w => ENNReal.ofReal (1 / ‖w - ζ‖)) (γ.toFun t) * ‖deriv γ.toFun t‖ₑ with hXdef
  have hmain : ∀ u v x y : ℝ, u ∈ Icc (0:ℝ) 1 → v ∈ Icc (0:ℝ) 1 → u ≤ v →
      clamp (r u) = x → clamp (r v) = y → |Real.log y - Real.log x| = L →
      ENNReal.ofReal (2 * L) ≤ X := by
    intro u v x y hu hv huv hcu hcv hxy
    have hseg1 := qcl_l_clamp_le_lintegral hγ' ζ hΔ hΔΔ' (le_refl (0:ℝ)) hu.1 hu.2
    have hseg2 := qcl_l_clamp_le_lintegral hγ' ζ hΔ hΔΔ' hu.1 huv hv.2
    have hseg3 := qcl_l_clamp_le_lintegral hγ' ζ hΔ hΔΔ' hv.1 hv.2 (le_refl (1:ℝ))
    have hcu' : max Δ (min Δ' ‖γ.toFun u - ζ‖) = x := hcu
    have hcv' : max Δ (min Δ' ‖γ.toFun v - ζ‖) = y := hcv
    have hκ' : max Δ (min Δ' ‖γ.toFun 1 - ζ‖) =
        max Δ (min Δ' ‖γ.toFun 0 - ζ‖) := hκ
    rw [hcu', hcv', hxy] at hseg2
    rw [hcu'] at hseg1
    rw [hκ', hcv'] at hseg3
    have hxy' : |Real.log x - Real.log y| = L := by rw [abs_sub_comm]; exact hxy
    have htri0 : |Real.log x - Real.log y| ≤
        |Real.log x - Real.log (clamp (r 0))| + |Real.log (clamp (r 0)) - Real.log y| :=
      abs_sub_le (Real.log x) (Real.log (clamp (r 0))) (Real.log y)
    rw [hxy'] at htri0
    have hsum : ENNReal.ofReal (2 * L) ≤
        ENNReal.ofReal |Real.log x - Real.log (clamp (r 0))| + ENNReal.ofReal L +
          ENNReal.ofReal |Real.log (clamp (r 0)) - Real.log y| := by
      rw [← ENNReal.ofReal_add (abs_nonneg _) hLpos.le,
        ← ENNReal.ofReal_add (add_nonneg (abs_nonneg _) hLpos.le) (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (by linarith [htri0])
    have hstep : ENNReal.ofReal |Real.log x - Real.log (clamp (r 0))| + ENNReal.ofReal L +
        ENNReal.ofReal |Real.log (clamp (r 0)) - Real.log y| ≤
        (∫⁻ t in Ioo (0:ℝ) u, (annulusAt ζ Δ Δ').indicator
            (fun w => ENNReal.ofReal (1 / ‖w - ζ‖)) (γ.toFun t) * ‖deriv γ.toFun t‖ₑ) +
        (∫⁻ t in Ioo u v, (annulusAt ζ Δ Δ').indicator
            (fun w => ENNReal.ofReal (1 / ‖w - ζ‖)) (γ.toFun t) * ‖deriv γ.toFun t‖ₑ) +
        (∫⁻ t in Ioo v 1, (annulusAt ζ Δ Δ').indicator
            (fun w => ENNReal.ofReal (1 / ‖w - ζ‖)) (γ.toFun t) * ‖deriv γ.toFun t‖ₑ) := by
      gcongr
    have hd1 : Disjoint (Ioo (0:ℝ) u) (Ioo u v) := by
      apply Set.disjoint_left.mpr
      intro x0 hx1 hx2
      exact absurd hx1.2 (not_lt.2 hx2.1.le)
    have hd2 : Disjoint (Ioo (0:ℝ) u ∪ Ioo u v) (Ioo v 1) := by
      apply Set.disjoint_left.mpr
      intro x0 hx1 hx2
      rcases hx1 with hx1 | hx1
      · exact absurd hx1.2 (not_lt.2 (huv.trans hx2.1.le))
      · exact absurd hx1.2 (not_lt.2 hx2.1.le)
    have hsub : (∫⁻ t in Ioo (0:ℝ) u, (annulusAt ζ Δ Δ').indicator
          (fun w => ENNReal.ofReal (1 / ‖w - ζ‖)) (γ.toFun t) * ‖deriv γ.toFun t‖ₑ) +
        (∫⁻ t in Ioo u v, (annulusAt ζ Δ Δ').indicator
            (fun w => ENNReal.ofReal (1 / ‖w - ζ‖)) (γ.toFun t) * ‖deriv γ.toFun t‖ₑ) +
        (∫⁻ t in Ioo v 1, (annulusAt ζ Δ Δ').indicator
            (fun w => ENNReal.ofReal (1 / ‖w - ζ‖)) (γ.toFun t) * ‖deriv γ.toFun t‖ₑ) ≤ X := by
      rw [hXdef, ← lintegral_union measurableSet_Ioo hd1, ← lintegral_union measurableSet_Ioo hd2]
      apply lintegral_mono_set
      intro t ht
      rcases ht with (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩
      · exact ⟨h1, h2.trans_le (huv.trans hv.2)⟩
      · exact ⟨hu.1.trans_lt h1, h2.trans_le hv.2⟩
      · exact ⟨hu.1.trans_lt (huv.trans_lt h1), h2⟩
    exact hsum.trans (hstep.trans hsub)
  have hΔ'pos : 0 < Δ' := hΔ.trans hΔΔ'
  have hLeq : Real.log Δ' - Real.log Δ = L := by
    rw [hLdef, Real.log_div hΔ'pos.ne' hΔ.ne']
  have hbound : ENNReal.ofReal (2 * L) ≤ X := by
    rcases le_total s₁ s₂ with hle | hle
    · refine hmain s₁ s₂ Δ Δ' hs₁ hs₂ hle hclamp_s1 hclamp_s2 ?_
      rw [hLeq]; exact abs_of_pos hLpos
    · refine hmain s₂ s₁ Δ' Δ hs₂ hs₁ hle hclamp_s2 hclamp_s1 ?_
      rw [show Real.log Δ - Real.log Δ' = -(Real.log Δ' - Real.log Δ) by ring, hLeq, abs_neg]
      exact abs_of_pos hLpos
  have hρeq : ∀ t, (annulusAt ζ Δ Δ').indicator
      (fun w => ENNReal.ofReal (1 / (2 * L * ‖w - ζ‖))) (γ.toFun t) =
      ENNReal.ofReal (1 / (2 * L)) *
        (annulusAt ζ Δ Δ').indicator (fun w => ENNReal.ofReal (1 / ‖w - ζ‖)) (γ.toFun t) := by
    intro t
    by_cases h : γ.toFun t ∈ annulusAt ζ Δ Δ'
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h,
        show (1:ℝ) / (2 * L * ‖γ.toFun t - ζ‖) = (1 / (2 * L)) * (1 / ‖γ.toFun t - ζ‖) by
          rw [one_div_mul_one_div],
        ENNReal.ofReal_mul (by positivity)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  have hρ : γ.rhoLength (fun w => (annulusAt ζ Δ Δ').indicator
      (fun w => ENNReal.ofReal (1 / (2 * L * ‖w - ζ‖))) w) =
      ENNReal.ofReal (1 / (2 * L)) * X := by
    show ∫⁻ t in Ioo (0:ℝ) 1, (annulusAt ζ Δ Δ').indicator
        (fun w => ENNReal.ofReal (1 / (2 * L * ‖w - ζ‖))) (γ.toFun t) * ‖deriv γ.toFun t‖ₑ = _
    have heq2 : ∀ t, (annulusAt ζ Δ Δ').indicator
        (fun w => ENNReal.ofReal (1 / (2 * L * ‖w - ζ‖))) (γ.toFun t) * ‖deriv γ.toFun t‖ₑ =
        ENNReal.ofReal (1 / (2 * L)) * ((annulusAt ζ Δ Δ').indicator
          (fun w => ENNReal.ofReal (1 / ‖w - ζ‖)) (γ.toFun t) * ‖deriv γ.toFun t‖ₑ) := by
      intro t
      rw [hρeq t, mul_assoc]
    rw [setLIntegral_congr_fun measurableSet_Ioo (fun t _ => heq2 t),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hXdef]
  rw [hρ]
  have hmul : ENNReal.ofReal (1 / (2 * L)) * ENNReal.ofReal (2 * L) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [show 1 / (2 * L) * (2 * L) = 1 by field_simp]
    exact ENNReal.ofReal_one
  calc (1:ℝ≥0∞) = ENNReal.ofReal (1 / (2 * L)) * ENNReal.ofReal (2 * L) := hmul.symm
    _ ≤ ENNReal.ofReal (1 / (2 * L)) * X := by
        gcongr


/-! ### Theorem 8.2 — helpers of piece A -/

theorem qcl_a_rhoArea_le (B : Set ℂ) (ζ : ℂ) {Δ Δ' : ℝ} (hΔ : 0 < Δ) (hΔΔ' : Δ < Δ') :
    rhoArea (fun w => (annulusAt ζ Δ Δ').indicator
      (fun w => ENNReal.ofReal (1 / (2 * Real.log (Δ' / Δ) * ‖w - ζ‖))) w) B ≤
      ENNReal.ofReal (π / (2 * Real.log (Δ' / Δ))) := by
  set L := Real.log (Δ' / Δ) with hLdef
  have hLpos : 0 < L := Real.log_pos ((one_lt_div hΔ).2 hΔΔ')
  have harea : rhoArea (fun w => (annulusAt ζ Δ Δ').indicator
      (fun w => ENNReal.ofReal (1 / (2 * L * ‖w - ζ‖))) w) B ≤
      rhoArea (fun w => (annulusAt ζ Δ Δ').indicator
        (fun w => ENNReal.ofReal (1 / (2 * L * ‖w - ζ‖))) w) univ :=
    lintegral_mono_set (subset_univ _)
  refine harea.trans ?_
  have hpointwise : ∀ z : ℂ, ((annulusAt ζ Δ Δ').indicator
      (fun w => ENNReal.ofReal (1 / (2 * L * ‖w - ζ‖))) z) ^ 2 =
      (annulusAt ζ Δ Δ').indicator
        (fun w => ENNReal.ofReal (1 / (2 * L)) ^ 2 * ENNReal.ofReal (1 / ‖w - ζ‖) ^ 2) z := by
    intro z
    by_cases h : z ∈ annulusAt ζ Δ Δ'
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h,
        show (1:ℝ) / (2 * L * ‖z - ζ‖) = (1 / (2 * L)) * (1 / ‖z - ζ‖) by
          rw [one_div_mul_one_div],
        ENNReal.ofReal_mul (by positivity), mul_pow]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; ring
  have hAmeas : MeasurableSet (annulusAt ζ Δ Δ') := by
    have heq : annulusAt ζ Δ Δ' = (fun z => ‖z - ζ‖) ⁻¹' Ioo Δ Δ' := by
      ext z; simp [annulusAt, mem_Ioo]
    rw [heq]
    exact ((continuous_norm.comp (continuous_id.sub continuous_const)).isOpen_preimage
      _ isOpen_Ioo).measurableSet
  have hunivint : rhoArea (fun w => (annulusAt ζ Δ Δ').indicator
      (fun w => ENNReal.ofReal (1 / (2 * L * ‖w - ζ‖))) w) univ =
      ENNReal.ofReal (1 / (2 * L)) ^ 2 *
        ∫⁻ z in annulusAt ζ Δ Δ', ENNReal.ofReal (1 / ‖z - ζ‖) ^ 2 := by
    show ∫⁻ z in (univ : Set ℂ), ((annulusAt ζ Δ Δ').indicator
        (fun w => ENNReal.ofReal (1 / (2 * L * ‖w - ζ‖))) z) ^ 2 = _
    rw [setLIntegral_congr_fun MeasurableSet.univ (fun z _ => hpointwise z),
      Measure.restrict_univ, MeasureTheory.lintegral_indicator hAmeas,
      lintegral_const_mul' _ _ (by finiteness)]
  rw [hunivint]
  have htranslate : ∫⁻ z in annulusAt ζ Δ Δ', ENNReal.ofReal (1 / ‖z - ζ‖) ^ 2 =
      ∫⁻ w in annulus Δ Δ', ENNReal.ofReal (1 / ‖w‖) ^ 2 := by
    have hemb : MeasurableEmbedding (fun w : ℂ => w + ζ) :=
      (Homeomorph.addRight ζ).isClosedEmbedding.measurableEmbedding
    have hpre : (fun w : ℂ => w + ζ) ⁻¹' (annulusAt ζ Δ Δ') = annulus Δ Δ' := by
      ext w
      simp only [Set.mem_preimage, annulusAt, annulus, Set.mem_setOf_eq, add_sub_cancel_right]
    have h := (measurePreserving_add_right volume ζ).setLIntegral_comp_preimage_emb hemb
      (fun z => ENNReal.ofReal (1 / ‖z - ζ‖) ^ 2) (annulusAt ζ Δ Δ')
    rw [hpre] at h
    simp only [add_sub_cancel_right] at h
    exact h.symm
  rw [htranslate]
  have hg2 : ∫⁻ z in annulus Δ Δ', ENNReal.ofReal (1 / ‖z‖) ^ 2 =
      ENNReal.ofReal (2 * π) * ENNReal.ofReal L := by
    rw [hLdef, ← lintegral_annulus_inv_normSq hΔ hΔΔ']
    refine setLIntegral_congr_fun (isOpen_annulus Δ Δ').measurableSet fun z _ => ?_
    rw [← ENNReal.ofReal_pow (show (0:ℝ) ≤ 1 / ‖z‖ by positivity), one_div_pow]
  rw [hg2, ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 * π by positivity),
    ← ENNReal.ofReal_pow (show (0:ℝ) ≤ 1 / (2 * L) by positivity),
    ← ENNReal.ofReal_mul (show (0:ℝ) ≤ (1 / (2 * L)) ^ 2 by positivity)]
  apply le_of_eq
  congr 1
  field_simp


/-! ### Theorem 8.2 — helpers of piece S -/

theorem qcl_s_injOn {D : Set ℂ} (hDc : IsConnected D) {K : ℝ} {fn : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hqc : ∀ n, IsKQC (fn n) D K) (hlim : TendstoLocallyUniformlyOn fn f atTop D)
    (hfc : ContinuousOn f D) (hnc : ¬ ∃ c : ℂ, ∀ z ∈ D, f z = c) : InjOn f D := by
  by_contra hni
  have hDo : IsOpen D := (hqc 0).1
  obtain ⟨z₂, hz₂, z₃, hz₃, hne23, heq23, hP⟩ := qcl_p_exists_pair hDo hDc hfc hnc hni
  obtain ⟨ε, hε0, hεsub⟩ := Metric.isOpen_iff.1 hDo z₂ hz₂
  have hz23pos : 0 < ‖z₃ - z₂‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne23))
  set R := min (ε / 2) (‖z₃ - z₂‖ / 2) with hRdef
  have hRpos : 0 < R := lt_min (by linarith) (by linarith)
  have hRεlt : R < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hR23 : R < ‖z₃ - z₂‖ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hRD : closedBall z₂ R ⊆ D := (closedBall_subset_ball hRεlt).trans hεsub
  set r := R / 2 with hrdef
  have hrpos : 0 < r := by positivity
  have hrR : r < R := by rw [hrdef]; linarith
  obtain ⟨z₁, hz₁D, hz₁dist, hz₁ne⟩ := hP r hrpos
  have hz₁ball : z₁ ∈ ball z₂ r := hz₁dist
  have hz₁cball : z₁ ∈ closedBall z₂ r := mem_closedBall.2 hz₁dist.le
  set B := annulusAt z₂ r R with hBdef
  have hB : IsDoublyConnected B := nf_g_isDoublyConnected_annulusAt z₂ hrpos hrR
  have hz₂not : z₂ ∉ B := by
    show ¬ (r < ‖z₂ - z₂‖ ∧ ‖z₂ - z₂‖ < R)
    rw [sub_self, norm_zero]
    exact fun h => absurd h.1 (not_lt.2 hrpos.le)
  have hz₃notC : z₃ ∉ closedBall z₂ R := by
    rw [mem_closedBall, not_le, dist_eq_norm]; exact hR23
  have hz₁notB : z₁ ∉ B := by
    show ¬ (r < ‖z₁ - z₂‖ ∧ ‖z₁ - z₂‖ < R)
    rw [mem_ball, dist_eq_norm] at hz₁ball
    exact fun h => absurd h.1 (not_lt.2 hz₁ball.le)
  have hBsubC : B ⊆ closedBall z₂ R := by
    intro z hz
    obtain ⟨-, hz2⟩ := hz
    rw [mem_closedBall, dist_eq_norm]; exact hz2.le
  have hBD : closure (toExt B) ⊆ toExt D :=
    (nf_e_closure_toExt_subset (isCompact_closedBall z₂ R) hBsubC).trans (image_mono hRD)
  have hlogRr : dcModulus B = ENNReal.ofReal (Real.log (R / r)) :=
    nf_e_dcModulus_annulusAt z₂ hrpos hrR
  have hquasi : ∀ n, IsDoublyConnected (fn n '' B) ∧
      dcModulus B ≤ ENNReal.ofReal K * dcModulus (fn n '' B) := fun n =>
    ⟨(thm7_4_dcModulus_quasi_invariance (hqc n) hB hBD).1,
      (thm7_4_dcModulus_quasi_invariance (hqc n) hB hBD).2.1⟩
  have hcore : ∀ n : ℕ, fn n z₂ ≠ fn n z₃ →
      ‖fn n z₂ - fn n z₃‖ / 2 < ‖fn n z₁ - (fn n z₂ + fn n z₃) / 2‖ →
      Real.log (R / r) ≤
        K * (π ^ 2 / Real.log (‖fn n z₁ - (fn n z₂ + fn n z₃) / 2‖ /
          (‖fn n z₂ - fn n z₃‖ / 2))) := by
    intro n hab_ne hlt
    have hfni : InjOn (fn n) D := (hqc n).2.2.1.2.1
    set a := fn n z₂ with hadef
    set b := fn n z₃ with hbdef
    set c := fn n z₁ with hcdef
    set w := (a + b) / 2 with hwdef
    set Δ := ‖a - b‖ / 2 with hΔdef
    set Δ' := ‖c - w‖ with hΔ'def
    have hΔpos : 0 < Δ := by
      rw [hΔdef]; exact half_pos (norm_pos_iff.2 (sub_ne_zero.2 hab_ne))
    have hΔΔ' : Δ < Δ' := hlt
    set L := Real.log (Δ' / Δ) with hLdef
    have hLpos : 0 < L := Real.log_pos ((one_lt_div hΔpos).2 hΔΔ')
    have hanotB : a ∉ fn n '' B := by
      rintro ⟨z', hz'B, heq⟩
      exact hz₂not (hfni (hBsubC.trans hRD hz'B) hz₂ heq ▸ hz'B)
    have hbnotB : b ∉ fn n '' B := by
      rintro ⟨z', hz'B, heq⟩
      exact hz₃notC (hBsubC (hfni (hBsubC.trans hRD hz'B) hz₃ heq ▸ hz'B))
    have hcnotB : c ∉ fn n '' B := by
      rintro ⟨z', hz'B, heq⟩
      exact hz₁notB (hfni (hBsubC.trans hRD hz'B) hz₁D heq ▸ hz'B)
    have haextcompl := nf_d_component_ne_extInf (hqc n) hrpos hrR hRD
      (w := a) ⟨z₂, mem_closedBall_self hrpos.le, rfl⟩
    have hcextcompl := nf_d_component_ne_extInf (hqc n) hrpos hrR hRD
      (w := c) ⟨z₁, hz₁cball, rfl⟩
    have hbexteq := qcl_o_component_eq_extInf (hqc n) hDc hrpos hrR hRD hz₃ hR23
    have habsep : connectedComponentIn (toExt (fn n '' B))ᶜ (a : ExtPlane) ≠
        connectedComponentIn (toExt (fn n '' B))ᶜ (b : ExtPlane) := fun heq =>
      haextcompl.2 (heq.trans hbexteq.2)
    have hquasin := hquasi n
    have hAmeas : MeasurableSet (annulusAt w Δ Δ') := by
      have heq : annulusAt w Δ Δ' = (fun z => ‖z - w‖) ⁻¹' Ioo Δ Δ' := by
        ext z; simp [annulusAt, mem_Ioo]
      rw [heq]
      exact ((continuous_norm.comp (continuous_id.sub continuous_const)).isOpen_preimage
        _ isOpen_Ioo).measurableSet
    have hadm : ∀ γ ∈ separatingCurves (fn n '' B), 1 ≤ γ.rhoLength
        (fun w' => (annulusAt w Δ Δ').indicator
          (fun w' => ENNReal.ofReal (1 / (2 * L * ‖w' - w‖))) w') := by
      intro γ hγ
      obtain ⟨hγclosed, hγtrace, hγsep⟩ := hγ
      have hsepab := hγsep a haextcompl.1 b hbexteq.1 habsep
      have hsepc := hγsep c hcextcompl.1 extInf (extInf_mem_compl_toExt _) hcextcompl.2
      have haγ : a ∉ γ.closedTrace := fun h => hanotB (hγtrace h)
      have hbγ : b ∉ γ.closedTrace := fun h => hbnotB (hγtrace h)
      have hcγ : c ∉ γ.closedTrace := fun h => hcnotB (hγtrace h)
      have hcw : c ≠ w := by
        intro heq
        have hΔ'0 : Δ' = 0 := by rw [hΔ'def, heq, sub_self, norm_zero]
        linarith [hΔΔ', hΔpos, hΔ'0]
      obtain ⟨⟨s₁, hs₁mem, hs₁lt⟩, ⟨s₂, hs₂mem, hs₂lt⟩⟩ :=
        qcl_g_exists_inside_outside hγclosed hab_ne haγ hbγ hcγ hcw hsepab hsepc
      rw [← hwdef] at hs₁lt hs₂lt
      exact qcl_l_one_le_rhoLength hγclosed w hΔpos hΔΔ' hs₁mem hs₂mem
        (by rwa [← hΔdef] at hs₁lt) (by rwa [← hΔ'def] at hs₂lt)
    have hρmeas : Measurable (fun w' : ℂ => (annulusAt w Δ Δ').indicator
        (fun w' => ENNReal.ofReal (1 / (2 * L * ‖w' - w‖))) w') := by
      apply Measurable.indicator _ hAmeas
      exact (measurable_const.div
        (((measurable_id.sub measurable_const).norm.const_mul (2 * L)))).ennreal_ofReal
    have hdcle := dcModulus_le_rhoArea hquasin.1 hρmeas hadm
    have hAle := qcl_a_rhoArea_le (fn n '' B) w hΔpos hΔΔ'
    have heq1 : ENNReal.ofReal (2 * π) * ENNReal.ofReal (π / (2 * L)) =
        ENNReal.ofReal (π ^ 2 / L) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    have hstep1 : dcModulus (fn n '' B) ≤ ENNReal.ofReal (π ^ 2 / L) :=
      calc dcModulus (fn n '' B) ≤ ENNReal.ofReal (2 * π) *
            rhoArea (fun w' => (annulusAt w Δ Δ').indicator
              (fun w' => ENNReal.ofReal (1 / (2 * L * ‖w' - w‖))) w') (fn n '' B) := hdcle
        _ ≤ ENNReal.ofReal (2 * π) * ENNReal.ofReal (π / (2 * L)) := by gcongr
        _ = ENNReal.ofReal (π ^ 2 / L) := heq1
    have hKnn : 0 ≤ K := zero_le_one.trans (hqc n).2.1
    have heq2 : ENNReal.ofReal K * ENNReal.ofReal (π ^ 2 / L) =
        ENNReal.ofReal (K * (π ^ 2 / L)) := (ENNReal.ofReal_mul hKnn).symm
    have hstep2 : dcModulus B ≤ ENNReal.ofReal (K * (π ^ 2 / L)) := by
      calc dcModulus B ≤ ENNReal.ofReal K * dcModulus (fn n '' B) := hquasin.2
        _ ≤ ENNReal.ofReal K * ENNReal.ofReal (π ^ 2 / L) := by gcongr
        _ = ENNReal.ofReal (K * (π ^ 2 / L)) := heq2
    rw [hlogRr] at hstep2
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hstep2
  -- limiting argument: derive a contradiction from `Lₙ → ∞`
  have hL0pos : 0 < ‖f z₁ - f z₂‖ := norm_pos_iff.2 (sub_ne_zero.2 hz₁ne)
  have htendA : Tendsto (fun n => fn n z₂ - fn n z₃) atTop (𝓝 (f z₂ - f z₃)) :=
    (hlim.tendsto_at hz₂).sub (hlim.tendsto_at hz₃)
  have htendΔ : Tendsto (fun n => ‖fn n z₂ - fn n z₃‖) atTop (𝓝 0) := by
    have : f z₂ - f z₃ = 0 := by rw [heq23, sub_self]
    simpa [this] using htendA.norm
  have htendC : Tendsto (fun n => fn n z₁ - (fn n z₂ + fn n z₃) / 2) atTop
      (𝓝 (f z₁ - (f z₂ + f z₃) / 2)) :=
    (hlim.tendsto_at hz₁D).sub (((hlim.tendsto_at hz₂).add (hlim.tendsto_at hz₃)).div_const 2)
  have htendΔ' : Tendsto (fun n => ‖fn n z₁ - (fn n z₂ + fn n z₃) / 2‖) atTop
      (𝓝 ‖f z₁ - f z₂‖) := by
    have heq : f z₁ - (f z₂ + f z₃) / 2 = f z₁ - f z₂ := by rw [← heq23]; ring
    simpa [heq] using htendC.norm
  have hKnn0 : 0 ≤ K := zero_le_one.trans (hqc 0).2.1
  have hKpos : 0 < K := lt_of_lt_of_le one_pos (hqc 0).2.1
  have hRrpos : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hrpos).2 hrR)
  have hKπ2pos : 0 < K * π ^ 2 := by positivity
  set M₀ := K * π ^ 2 / Real.log (R / r) with hM₀def
  have hM₀pos : 0 < M₀ := by rw [hM₀def]; positivity
  have hab_ne_all : ∀ n, fn n z₂ ≠ fn n z₃ := fun n heq =>
    hne23 ((hqc n).2.2.1.2.1 hz₂ hz₃ heq)
  have hΔnpos_all : ∀ n, 0 < ‖fn n z₂ - fn n z₃‖ / 2 := fun n => by
    have := norm_pos_iff.2 (sub_ne_zero.2 (hab_ne_all n)); linarith
  have hexpM₀gt1 : 1 < Real.exp M₀ := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 hM₀pos
  have hev1 : ∀ᶠ n in atTop, (‖fn n z₂ - fn n z₃‖ / 2) * Real.exp M₀ < ‖f z₁ - f z₂‖ / 2 := by
    have h0 : Tendsto (fun n => (‖fn n z₂ - fn n z₃‖ / 2) * Real.exp M₀) atTop (𝓝 0) := by
      have := (htendΔ.div_const 2).mul_const (Real.exp M₀)
      simpa using this
    exact h0.eventually_lt_const (by positivity)
  have hev2 : ∀ᶠ n in atTop, ‖f z₁ - f z₂‖ / 2 < ‖fn n z₁ - (fn n z₂ + fn n z₃) / 2‖ :=
    htendΔ'.eventually_const_lt (by linarith)
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  have hchain : (‖fn n z₂ - fn n z₃‖ / 2) * Real.exp M₀ <
      ‖fn n z₁ - (fn n z₂ + fn n z₃) / 2‖ := hn1.trans hn2
  have hΔnpos := hΔnpos_all n
  have hlt : ‖fn n z₂ - fn n z₃‖ / 2 < ‖fn n z₁ - (fn n z₂ + fn n z₃) / 2‖ := by
    calc ‖fn n z₂ - fn n z₃‖ / 2 < (‖fn n z₂ - fn n z₃‖ / 2) * Real.exp M₀ := by
          nlinarith [hΔnpos, hexpM₀gt1]
      _ < ‖fn n z₁ - (fn n z₂ + fn n z₃) / 2‖ := hchain
  have hM₀ltLn : M₀ < Real.log (‖fn n z₁ - (fn n z₂ + fn n z₃) / 2‖ /
      (‖fn n z₂ - fn n z₃‖ / 2)) := by
    rw [Real.lt_log_iff_exp_lt (div_pos (hΔnpos.trans hlt) hΔnpos), lt_div_iff₀ hΔnpos]
    linarith [hchain]
  have hLnpos : 0 < Real.log (‖fn n z₁ - (fn n z₂ + fn n z₃) / 2‖ /
      (‖fn n z₂ - fn n z₃‖ / 2)) := hM₀pos.trans hM₀ltLn
  have hcoreN := hcore n (hab_ne_all n) hlt
  rw [hM₀def, div_lt_iff₀ hRrpos] at hM₀ltLn
  -- hM₀ltLn : K * π ^ 2 < Real.log (...) * Real.log (R / r)
  have hfinal : K * (π ^ 2 / Real.log (‖fn n z₁ - (fn n z₂ + fn n z₃) / 2‖ /
      (‖fn n z₂ - fn n z₃‖ / 2))) < Real.log (R / r) := by
    rw [← mul_div_assoc, div_lt_iff₀ hLnpos]
    nlinarith [hM₀ltLn]
  linarith [hcoreN, hfinal]



/-! ### Theorem 8.2 — helpers of piece W -/

theorem qcl_w_lift_change_eq_of_conformal {A : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) {p : ℂ}
    (hp : p ∈ U) (hA : DifferentiableOn ℂ A U) (hA' : deriv A p ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ closedBall p r ⊆ U ∧ ∀ α : ℝ → ℂ, ContinuousOn α (Icc 0 1) → α 1 = α 0 →
      (∀ t ∈ Icc (0 : ℝ) 1, α t ∈ closedBall p r) → (∀ t ∈ Icc (0 : ℝ) 1, α t ≠ p) →
      ∀ L M : ℝ → ℂ, ContinuousOn L (Icc 0 1) → ContinuousOn M (Icc 0 1) →
        (∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L t) = α t - p) →
        (∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (M t) = A (α t) - A p) →
        M 1 - M 0 = L 1 - L 0 := by
  have hAd : DifferentiableAt ℂ A p := hA.differentiableAt (hU.mem_nhds hp)
  have hAderiv : HasDerivAt A (deriv A p) p := hAd.hasDerivAt
  rw [hasDerivAt_iff_isLittleO] at hAderiv
  have hc : (0:ℝ) < ‖deriv A p‖ / 2 := by positivity
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.1 (hAderiv.def hc)
  obtain ⟨ε', hε'pos, hε'sub⟩ := Metric.isOpen_iff.1 hU p hp
  set r := min ε ε' / 2 with hrdef
  have hrpos : 0 < r := by positivity
  have hrε : r < ε := by rw [hrdef]; have := min_le_left ε ε'; linarith
  have hrε' : r < ε' := by rw [hrdef]; have := min_le_right ε ε'; linarith
  have hrU : closedBall p r ⊆ U := (closedBall_subset_ball hrε').trans hε'sub
  refine ⟨r, hrpos, hrU, ?_⟩
  intro α hαcont hα1 hαr hαne L M hLcont hMcont hLe hMe
  have hbound : ∀ w : ℂ, w ∈ closedBall p r → ‖A w - A p - deriv A p * (w - p)‖ ≤
      ‖deriv A p‖ / 2 * ‖w - p‖ := by
    intro w hw
    have hwdist : dist w p < ε := lt_of_le_of_lt (mem_closedBall.1 hw) hrε
    have hwdist' : dist w p < ε := hwdist
    have := hε hwdist'
    simpa [smul_eq_mul, mul_comm] using this
  have hαmapsto : MapsTo α (Icc (0:ℝ) 1) U := fun t ht => hrU (hαr t ht)
  have hAαcont : ContinuousOn (fun t => A (α t)) (Icc (0:ℝ) 1) := hA.continuousOn.comp hαcont hαmapsto
  set H : ℝ → ℝ → ℂ := fun s t => (1 - s) * (A (α t) - A p) + s * (deriv A p * (α t - p)) with hHdef
  have hHcont : ContinuousOn (Function.uncurry H) (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := by
    have hpart1 : ContinuousOn (fun q : ℝ × ℝ => (1 - (q.1:ℂ)) * (A (α q.2) - A p))
        (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) :=
      (continuousOn_const.sub (Complex.continuous_ofReal.comp continuous_fst).continuousOn).mul
        ((hAαcont.comp continuousOn_snd (fun q hq => by exact hq.2)).sub continuousOn_const)
    have hpart2 : ContinuousOn (fun q : ℝ × ℝ => (q.1 : ℂ) * (deriv A p * (α q.2 - p)))
        (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) :=
      (Complex.continuous_ofReal.comp continuous_fst).continuousOn.mul
        (continuousOn_const.mul ((hαcont.comp continuousOn_snd (fun q hq => by exact hq.2)).sub continuousOn_const))
    have hHeq : (Function.uncurry H) = fun q : ℝ × ℝ =>
        (1 - (q.1:ℂ)) * (A (α q.2) - A p) + (q.1 : ℂ) * (deriv A p * (α q.2 - p)) := by
      funext ⟨s, t⟩
      show H s t = _
      rw [hHdef]
    rw [hHeq]
    exact hpart1.add hpart2
  have hHper : ∀ s ∈ Icc (0:ℝ) 1, H s 1 = H s 0 := fun s _ => by rw [hHdef]; simp [hα1]
  have hHne : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, H s t ≠ 0 := by
    intro s hs t ht
    have hant : α t - p ≠ 0 := sub_ne_zero.2 (hαne t ht)
    have hantpos : 0 < ‖α t - p‖ := norm_pos_iff.2 hant
    have hEbound : ‖A (α t) - A p - deriv A p * (α t - p)‖ ≤ ‖deriv A p‖ / 2 * ‖α t - p‖ :=
      hbound (α t) (hαr t ht)
    have hHeqt : H s t = deriv A p * (α t - p) +
        ((1:ℂ) - (s:ℂ)) * (A (α t) - A p - deriv A p * (α t - p)) := by
      rw [hHdef]; push_cast; ring
    rw [hHeqt]
    intro heq0
    have hnormeq : deriv A p * (α t - p) =
        -(((1:ℂ) - (s:ℂ)) * (A (α t) - A p - deriv A p * (α t - p))) := by
      linear_combination heq0
    have h1s_le : ‖(1:ℂ) - (s:ℂ)‖ ≤ 1 := by
      rw [show (1:ℂ) - (s:ℂ) = ((1 - s : ℝ):ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])]
      linarith [hs.1]
    have hnormbound : ‖deriv A p * (α t - p)‖ ≤ ‖deriv A p‖ / 2 * ‖α t - p‖ := by
      rw [hnormeq, norm_neg, norm_mul]
      calc ‖(1:ℂ) - (s:ℂ)‖ * ‖A (α t) - A p - deriv A p * (α t - p)‖ ≤
          1 * (‖deriv A p‖ / 2 * ‖α t - p‖) :=
            mul_le_mul h1s_le hEbound (norm_nonneg _) zero_le_one
        _ = ‖deriv A p‖ / 2 * ‖α t - p‖ := one_mul _
    rw [norm_mul] at hnormbound
    have hApnorm : 0 < ‖deriv A p‖ := norm_pos_iff.2 hA'
    nlinarith [hnormbound, mul_pos hApnorm hantpos]
  have hL1cont : ContinuousOn (fun t => L t + Complex.log (deriv A p)) (Icc (0:ℝ) 1) :=
    hLcont.add continuousOn_const
  have hL1e : ∀ t ∈ Icc (0:ℝ) 1,
      Complex.exp (L t + Complex.log (deriv A p)) = H 1 t - 0 := by
    intro t ht
    rw [Complex.exp_add, hLe t ht, Complex.exp_log hA', hHdef]
    push_cast; ring
  have hL0e : ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (M t) = H 0 t - 0 := by
    intro t ht
    rw [hMe t ht, hHdef]
    push_cast; ring
  have hkey := lift_change_eq_of_homotopy hHcont hHper hHne hMcont hL1cont hL0e hL1e
  linear_combination hkey

theorem qcl_w_lift_change_eq_of_injOn {k : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V) {p : ℂ} {r : ℝ}
    (hr : 0 < r) (hrV : closedBall p r ⊆ V) (hk : ContinuousOn k V) (hki : InjOn k V)
    (hloc : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (L t) = k (p + ρ * Complex.exp (2 * π * I * t)) - k p) →
      L 1 - L 0 = 2 * π * I)
    {α : ℝ → ℂ} (hα : ContinuousOn α (Icc 0 1)) (hα1 : α 1 = α 0)
    (hαr : ∀ t ∈ Icc (0 : ℝ) 1, α t ∈ closedBall p r) (hαp : ∀ t ∈ Icc (0 : ℝ) 1, α t ≠ p)
    {L M : ℝ → ℂ} (hL : ContinuousOn L (Icc 0 1)) (hM : ContinuousOn M (Icc 0 1))
    (hLe : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L t) = α t - p)
    (hMe : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (M t) = k (α t) - k p)
    (hL1 : L 1 - L 0 = 2 * π * I) :
    M 1 - M 0 = 2 * π * I := by
  have hL1e : L 1 = L 0 + 2 * π * I := by linear_combination hL1
  have hLtre : ∀ t ∈ Icc (0:ℝ) 1, (L t).re = Real.log ‖α t - p‖ := by
    intro t ht
    have h1 : ‖Complex.exp (L t)‖ = ‖α t - p‖ := by rw [hLe t ht]
    rw [Complex.norm_exp] at h1
    rw [← h1, Real.log_exp]
  have hL0re : (L 0).re = Real.log ‖α 0 - p‖ := hLtre 0 (left_mem_Icc.2 zero_le_one)
  have hα0r : α 0 ∈ closedBall p r := hαr 0 (left_mem_Icc.2 zero_le_one)
  have hα0p : α 0 ≠ p := hαp 0 (left_mem_Icc.2 zero_le_one)
  set ρ₀ := ‖α 0 - p‖ with hρ₀def
  have hρ₀pos : 0 < ρ₀ := norm_pos_iff.2 (sub_ne_zero.2 hα0p)
  have hρ₀r : ρ₀ ≤ r := by rw [hρ₀def]; rwa [mem_closedBall, dist_eq_norm] at hα0r
  set θ₀ := Complex.arg (α 0 - p) with hθ₀def
  have hpolar : (ρ₀ : ℂ) * Complex.exp ((θ₀ : ℂ) * I) = α 0 - p := Complex.norm_mul_exp_arg_mul_I _
  -- First homotopy: `H` deforms `α` to the `θ₀`-rotated standard circle
  set H : ℝ → ℝ → ℂ := fun s t => p + Complex.exp ((1 - (s:ℂ)) * L t + (s:ℂ) * (L 0 + 2 * π * I * t))
    with hHdef
  have hH0 : ∀ t, H 0 t = p + Complex.exp (L t) := by
    intro t; rw [hHdef]; norm_num
  have hH0' : ∀ t ∈ Icc (0:ℝ) 1, H 0 t = α t := by
    intro t ht; rw [hH0, hLe t ht]; ring
  have hH1 : ∀ t, H 1 t = p + Complex.exp (L 0 + 2 * π * I * t) := by
    intro t; rw [hHdef]; norm_num
  have hHper : ∀ s ∈ Icc (0:ℝ) 1, H s 1 = H s 0 := by
    intro s hs
    rw [hHdef]
    show p + Complex.exp ((1 - (s:ℂ)) * L 1 + (s:ℂ) * (L 0 + 2 * π * I * 1)) =
      p + Complex.exp ((1 - (s:ℂ)) * L 0 + (s:ℂ) * (L 0 + 2 * π * I * 0))
    congr 1
    rw [hL1e, show (1 - (s:ℂ)) * (L 0 + 2 * π * I) + (s:ℂ) * (L 0 + 2 * π * I * 1) =
      ((1 - (s:ℂ)) * L 0 + (s:ℂ) * (L 0 + 2 * π * I * 0)) + 2 * π * I by ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hzre : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1,
      ((1 - (s:ℂ)) * L t + (s:ℂ) * (L 0 + 2 * π * I * (t:ℂ))).re =
      (1 - s) * (L t).re + s * (L 0).re := by
    intro s hs t ht
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.im_ofNat, Complex.re_ofNat]
    ring
  have hHbound : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, H s t ∈ closedBall p r := by
    intro s hs t ht
    rw [mem_closedBall, dist_eq_norm, hHdef]
    show ‖p + Complex.exp ((1-(s:ℂ)) * L t + (s:ℂ) * (L 0 + 2*π*I*(t:ℂ))) - p‖ ≤ r
    rw [show p + Complex.exp ((1-(s:ℂ)) * L t + (s:ℂ) * (L 0 + 2*π*I*(t:ℂ))) - p =
      Complex.exp ((1-(s:ℂ)) * L t + (s:ℂ) * (L 0 + 2*π*I*(t:ℂ))) by ring, Complex.norm_exp,
      hzre s hs t ht, hLtre t ht, hL0re]
    calc Real.exp ((1 - s) * Real.log ‖α t - p‖ + s * Real.log ‖α 0 - p‖) ≤
        Real.exp ((1 - s) * Real.log r + s * Real.log r) := by
          apply Real.exp_le_exp.2
          have hlogt : Real.log ‖α t - p‖ ≤ Real.log r := by
            apply Real.log_le_log (norm_pos_iff.2 (sub_ne_zero.2 (hαp t ht)))
            have hh := hαr t ht
            rwa [mem_closedBall, dist_eq_norm] at hh
          have hlog0 : Real.log ‖α 0 - p‖ ≤ Real.log r := by
            apply Real.log_le_log (norm_pos_iff.2 (sub_ne_zero.2 hα0p))
            rwa [mem_closedBall, dist_eq_norm] at hα0r
          nlinarith [hlogt, hlog0, hs.1, hs.2]
      _ = r := by rw [show (1 - s) * Real.log r + s * Real.log r = Real.log r by ring,
          Real.exp_log hr]
  have hHne : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, H s t ≠ p := by
    intro s hs t ht heq
    rw [hHdef] at heq
    have : Complex.exp ((1-(s:ℂ)) * L t + (s:ℂ) * (L 0 + 2*π*I*(t:ℂ))) = 0 := by linear_combination heq
    exact Complex.exp_ne_zero _ this
  have hLcont' : ContinuousOn (fun q : ℝ × ℝ => L q.2) (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) :=
    hL.comp continuousOn_snd (fun q hq => hq.2)
  have hHuncurry : (Function.uncurry H) = fun q : ℝ × ℝ =>
      p + Complex.exp ((1 - (q.1:ℂ)) * L q.2 + (q.1:ℂ) * (L 0 + 2 * π * I * (q.2:ℂ))) := by
    funext ⟨s, t⟩; show H s t = _; rw [hHdef]
  have hHcont : ContinuousOn (Function.uncurry H) (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := by
    rw [hHuncurry]
    refine continuousOn_const.add (Complex.continuous_exp.comp_continuousOn ?_)
    refine ContinuousOn.add ?_ ?_
    · exact (continuousOn_const.sub
        (Complex.continuous_ofReal.comp continuous_fst).continuousOn).mul hLcont'
    · exact (Complex.continuous_ofReal.comp continuous_fst).continuousOn.mul
        (continuousOn_const.add (continuousOn_const.mul
          (Complex.continuous_ofReal.comp continuous_snd).continuousOn))
  have hpV : p ∈ V := hrV (mem_closedBall_self hr.le)
  have hHmapsto : MapsTo (Function.uncurry H) (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) V :=
    fun q hq => hrV (hHbound q.1 hq.1 q.2 hq.2)
  have hkHcont : ContinuousOn (Function.uncurry (fun s t => k (H s t)))
      (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := hk.comp hHcont hHmapsto
  have hkHper : ∀ s ∈ Icc (0:ℝ) 1, k (H s 1) = k (H s 0) := fun s hs => by
    rw [hHper s hs]
  have hkHne : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, k (H s t) ≠ k p := by
    intro s hs t ht heq
    exact hHne s hs t ht (hki (hrV (hHbound s hs t ht)) hpV heq)
  have hH1cont : ContinuousOn (fun t => H 1 t) (Icc (0:ℝ) 1) := by
    have heq : (fun t : ℝ => H 1 t) = fun t : ℝ => p + Complex.exp (L 0 + 2 * π * I * (t:ℂ)) :=
      funext hH1
    rw [heq]
    exact continuousOn_const.add (Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.add (continuousOn_const.mul
        (Complex.continuous_ofReal.comp continuous_id).continuousOn)))
  have hkH1cont : ContinuousOn (fun t => k (H 1 t)) (Icc (0:ℝ) 1) :=
    hk.comp hH1cont (fun t ht => hrV (hHbound 1 (right_mem_Icc.2 zero_le_one) t ht))
  have hkH1ne : ∀ t ∈ Icc (0:ℝ) 1, k (H 1 t) ≠ k p := by
    intro t ht heq
    exact hHne 1 (right_mem_Icc.2 zero_le_one) t ht
      (hki (hrV (hHbound 1 (right_mem_Icc.2 zero_le_one) t ht)) hpV heq)
  obtain ⟨N₁, hN₁cont, hN₁e⟩ := exists_continuousOn_log_lift hkH1cont hkH1ne
  have hMe' : ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (M t) = k (H 0 t) - k p := by
    intro t ht; rw [hH0' t ht]; exact hMe t ht
  have hkey1 := lift_change_eq_of_homotopy hkHcont hkHper hkHne hM hN₁cont hMe' hN₁e
  -- second homotopy: rotates the `θ₀`-shifted circle to the standard one
  set R : ℝ → ℝ → ℂ := fun s t =>
    p + (ρ₀:ℂ) * Complex.exp ((θ₀:ℂ) * I * (1 - (s:ℂ)) + 2 * π * I * (t:ℂ)) with hRdef
  have hR0 : ∀ t, R 0 t = H 1 t := by
    intro t
    rw [hRdef, hH1]
    show p + (ρ₀:ℂ) * Complex.exp ((θ₀:ℂ) * I * (1 - 0) + 2*π*I*(t:ℂ)) =
      p + Complex.exp (L 0 + 2*π*I*(t:ℂ))
    have hL0exp : Complex.exp (L 0) = α 0 - p := hLe 0 (left_mem_Icc.2 zero_le_one)
    congr 1
    rw [show (θ₀:ℂ) * I * (1 - (0:ℂ)) + 2*π*I*(t:ℂ) = (θ₀:ℂ)*I + 2*π*I*(t:ℂ) by ring,
      Complex.exp_add, Complex.exp_add, ← mul_assoc, hpolar, hL0exp]
  have hR1 : ∀ t, R 1 t = p + (ρ₀:ℂ) * Complex.exp (2 * π * I * (t:ℂ)) := by
    intro t; rw [hRdef]; norm_num
  have hRper : ∀ s ∈ Icc (0:ℝ) 1, R s 1 = R s 0 := by
    intro s hs
    rw [hRdef]
    show p + (ρ₀:ℂ) * Complex.exp ((θ₀:ℂ)*I*(1-(s:ℂ)) + 2*π*I*(1:ℂ)) =
      p + (ρ₀:ℂ) * Complex.exp ((θ₀:ℂ)*I*(1-(s:ℂ)) + 2*π*I*(0:ℂ))
    congr 2
    rw [show (θ₀:ℂ)*I*(1-(s:ℂ)) + 2*π*I*(1:ℂ) =
      ((θ₀:ℂ)*I*(1-(s:ℂ)) + 2*π*I*(0:ℂ)) + 2*π*I by ring, Complex.exp_add,
      Complex.exp_two_pi_mul_I, mul_one]
  have hRbound : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, R s t ∈ closedBall p r := by
    intro s hs t ht
    rw [mem_closedBall, dist_eq_norm, hRdef]
    show ‖p + (ρ₀:ℂ) * Complex.exp ((θ₀:ℂ)*I*(1-(s:ℂ)) + 2*π*I*(t:ℂ)) - p‖ ≤ r
    rw [show p + (ρ₀:ℂ) * Complex.exp ((θ₀:ℂ)*I*(1-(s:ℂ)) + 2*π*I*(t:ℂ)) - p =
      (ρ₀:ℂ) * Complex.exp ((θ₀:ℂ)*I*(1-(s:ℂ)) + 2*π*I*(t:ℂ)) by ring,
      norm_mul, Complex.norm_exp]
    have hre0 : ((θ₀:ℂ)*I*(1-(s:ℂ)) + 2*π*I*(t:ℂ)).re = 0 := by
      simp only [Complex.add_re, Complex.mul_re, Complex.mul_im,
        Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.im_ofNat, Complex.re_ofNat]
      ring
    rw [hre0, Real.exp_zero, mul_one, Complex.norm_real, Real.norm_of_nonneg hρ₀pos.le]
    exact hρ₀r
  have hRne : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, R s t ≠ p := by
    intro s hs t ht heq
    rw [hRdef] at heq
    have h0 : (ρ₀:ℂ) * Complex.exp ((θ₀:ℂ)*I*(1-(s:ℂ)) + 2*π*I*(t:ℂ)) = 0 := by
      linear_combination heq
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact absurd (Complex.ofReal_eq_zero.1 h1) hρ₀pos.ne'
    · exact Complex.exp_ne_zero _ h1
  have hRcont : ContinuousOn (Function.uncurry R) (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := by
    have hRuncurry : (Function.uncurry R) = fun q : ℝ × ℝ =>
        p + (ρ₀:ℂ) * Complex.exp ((θ₀:ℂ) * I * (1 - (q.1:ℂ)) + 2 * π * I * (q.2:ℂ)) := by
      funext ⟨s, t⟩; show R s t = _; rw [hRdef]
    rw [hRuncurry]
    refine continuousOn_const.add (continuousOn_const.mul
      (Complex.continuous_exp.comp_continuousOn ?_))
    exact (continuousOn_const.mul (continuousOn_const.sub
      (Complex.continuous_ofReal.comp continuous_fst).continuousOn)).add
      (continuousOn_const.mul (Complex.continuous_ofReal.comp continuous_snd).continuousOn)
  have hRmapsto : MapsTo (Function.uncurry R) (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) V :=
    fun q hq => hrV (hRbound q.1 hq.1 q.2 hq.2)
  have hkRcont : ContinuousOn (Function.uncurry (fun s t => k (R s t)))
      (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := hk.comp hRcont hRmapsto
  have hkRper : ∀ s ∈ Icc (0:ℝ) 1, k (R s 1) = k (R s 0) := fun s hs => by
    rw [hRper s hs]
  have hkRne : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, k (R s t) ≠ k p := by
    intro s hs t ht heq
    exact hRne s hs t ht (hki (hrV (hRbound s hs t ht)) hpV heq)
  have hN₁e' : ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (N₁ t) = k (R 0 t) - k p := by
    intro t ht; rw [hR0]; exact hN₁e t ht
  have hR1cont : ContinuousOn (fun t => R 1 t) (Icc (0:ℝ) 1) := by
    have heq : (fun t : ℝ => R 1 t) = fun t : ℝ => p + (ρ₀:ℂ) * Complex.exp (2 * π * I * (t:ℂ)) :=
      funext hR1
    rw [heq]
    exact continuousOn_const.add (continuousOn_const.mul (Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp continuous_id).continuousOn)))
  have hkR1cont : ContinuousOn (fun t => k (R 1 t)) (Icc (0:ℝ) 1) :=
    hk.comp hR1cont (fun t ht => hrV (hRbound 1 (right_mem_Icc.2 zero_le_one) t ht))
  have hkR1ne : ∀ t ∈ Icc (0:ℝ) 1, k (R 1 t) ≠ k p := by
    intro t ht heq
    exact hRne 1 (right_mem_Icc.2 zero_le_one) t ht
      (hki (hrV (hRbound 1 (right_mem_Icc.2 zero_le_one) t ht)) hpV heq)
  obtain ⟨N₀, hN₀cont, hN₀e⟩ := exists_continuousOn_log_lift hkR1cont hkR1ne
  have hN₀e_explicit : ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (N₀ t) =
      k (p + (ρ₀:ℝ) * Complex.exp (2 * π * I * t)) - k p := by
    intro t ht; rw [hN₀e t ht, hR1]
  have hkey2 := lift_change_eq_of_homotopy hkRcont hkRper hkRne hN₁cont hN₀cont hN₁e' hN₀e
  have hkey3 := hloc ρ₀ hρ₀pos hρ₀r N₀ hN₀cont hN₀e_explicit
  linear_combination hkey1 + hkey2 + hkey3

theorem qcl_w_strictMono_of_cyclic {G : ExtPlane → ExtPlane}
    (hGc : ContinuousOn G (frontier (toExt upperHalf)))
    (hGi : InjOn G (frontier (toExt upperHalf)))
    (hGs : G '' frontier (toExt upperHalf) = frontier (toExt upperHalf))
    (hinf : G extInf = extInf) {x y : Fin 4 → ℝ} (hx : CyclicStrictMono x)
    (hy : CyclicStrictMono y)
    (hxy : ∀ i, G (((x i : ℝ) : ℂ) : ExtPlane) = (((y i : ℝ) : ℂ) : ExtPlane)) :
    ∃ f : ℝ → ℝ, Continuous f ∧ Function.Injective f ∧ StrictMono f ∧
      ∀ t : ℝ, G (((t : ℝ) : ℂ) : ExtPlane) = (((f t : ℝ) : ℂ) : ExtPlane) := by
  have hrange : range realToExtPlane = frontier (toExt upperHalf) := range_realToExtPlane
  have hmapsTo : MapsTo realToExtPlane univ (frontier (toExt upperHalf)) := by
    intro w _; rw [← hrange]; exact mem_range_self w
  have hex : ∀ w : OnePoint ℝ, ∃ w' : OnePoint ℝ, realToExtPlane w' = G (realToExtPlane w) := by
    intro w
    have hmem : G (realToExtPlane w) ∈ frontier (toExt upperHalf) := by
      rw [← hGs]; exact ⟨realToExtPlane w, hmapsTo (mem_univ w), rfl⟩
    rw [← hrange] at hmem
    exact hmem
  choose g hg using hex
  have hginj : Function.Injective g := by
    intro w1 w2 heq
    apply realToExtPlane_injective
    apply hGi (hmapsTo (mem_univ w1)) (hmapsTo (mem_univ w2))
    rw [← hg, ← hg, heq]
  have hgsurj : Function.Surjective g := by
    intro w
    have hmem : realToExtPlane w ∈ G '' frontier (toExt upperHalf) := by
      rw [hGs]; exact hmapsTo (mem_univ w)
    obtain ⟨q, hq, hqeq⟩ := hmem
    rw [← hrange] at hq
    obtain ⟨w', hw'⟩ := hq
    refine ⟨w', realToExtPlane_injective ?_⟩
    rw [hg, hw', hqeq]
  have hgcont : Continuous g := by
    have heq : realToExtPlane ∘ g = G ∘ realToExtPlane := funext hg
    have hcont : Continuous (G ∘ realToExtPlane) :=
      hGc.comp_continuous continuous_realToExtPlane (fun w => hmapsTo (mem_univ w))
    rw [← heq] at hcont
    exact isClosedEmbedding_realToExtPlane.isInducing.continuous_iff.2 hcont
  set h : OnePoint ℝ ≃ₜ OnePoint ℝ :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g ⟨hginj, hgsurj⟩) hgcont with hhdef
  have hhg : ∀ w, h w = g w := fun w => rfl
  have hhinf : h OnePoint.infty = OnePoint.infty := by
    rw [hhg]
    apply realToExtPlane_injective
    rw [hg, realToExtPlane_infty, hinf]
  obtain ⟨f, hfcont, hfinj, hf⟩ := exists_real_of_fixes_infty hhinf
  have hGf : ∀ t : ℝ, G (((t:ℝ):ℂ):ExtPlane) = (((f t : ℝ):ℂ):ExtPlane) := by
    intro t
    have h1 : h (t : OnePoint ℝ) = (f t : OnePoint ℝ) := hf t
    rw [hhg] at h1
    have h2 := congrArg realToExtPlane h1
    rwa [hg, realToExtPlane_coe] at h2
  rcases hfcont.strictMono_of_inj hfinj with hmono | hanti
  · exact ⟨f, hfcont, hfinj, hmono, hGf⟩
  · exfalso
    have hyf : ∀ i, y i = f (x i) := by
      intro i
      have heq : (((f (x i):ℝ):ℂ):ExtPlane) = (((y i:ℝ):ℂ):ExtPlane) :=
        (hGf (x i)).symm.trans (hxy i)
      exact_mod_cast (Complex.ofReal_injective (OnePoint.coe_injective heq)).symm
    obtain ⟨k, hk⟩ := hx
    have h01 : x (0 + k) < x (1 + k) := hk (show (0 : Fin 4) < 1 by decide)
    have h12 : x (1 + k) < x (2 + k) := hk (show (1 : Fin 4) < 2 by decide)
    have h23 : x (2 + k) < x (3 + k) := hk (show (2 : Fin 4) < 3 by decide)
    have hyneg : CyclicStrictMono (fun i => y (-i)) := by
      refine cyclicStrictMono_of_chain (1 - k) ?_ ?_ ?_
      · have e1 : -((0 : Fin 4) + (1 - k)) = 3 + k := by fin_cases k <;> decide
        have e2 : -((1 : Fin 4) + (1 - k)) = 2 + k := by fin_cases k <;> decide
        show y (-((0 : Fin 4) + (1 - k))) < y (-((1 : Fin 4) + (1 - k)))
        rw [e1, e2, hyf, hyf]; exact hanti h23
      · have e1 : -((1 : Fin 4) + (1 - k)) = 2 + k := by fin_cases k <;> decide
        have e2 : -((2 : Fin 4) + (1 - k)) = 1 + k := by fin_cases k <;> decide
        show y (-((1 : Fin 4) + (1 - k))) < y (-((2 : Fin 4) + (1 - k)))
        rw [e1, e2, hyf, hyf]; exact hanti h12
      · have e1 : -((2 : Fin 4) + (1 - k)) = 1 + k := by fin_cases k <;> decide
        have e2 : -((3 : Fin 4) + (1 - k)) = 0 + k := by fin_cases k <;> decide
        show y (-((2 : Fin 4) + (1 - k))) < y (-((3 : Fin 4) + (1 - k)))
        rw [e1, e2, hyf, hyf]; exact hanti h01
    exact not_cyclicStrictMono_of_cyclicStrictMono_neg hy hyneg


/-- **qcl_w_b helper.** The chord-endpoint parameters `t₁, t₂` on the circle of radius `R`
around the origin, for a half-plane of height `y₀ < R`: pure circle trigonometry, independent
of `f`/`g`/`ρ`/`L`, extracted so it can be elaborated (and heartbeat-budgeted) separately from
the main theorem. -/
theorem qcl_w_b_chord_endpoints (y₀ R : ℝ) (hy₀ : 0 < y₀) (hRy₀ : y₀ < R) :
    ∃ t₁ t₂ : ℝ, 0 < t₁ ∧ t₁ < t₂ ∧ t₂ < 1 ∧
      Real.sin (2 * π * t₁) = -(y₀/R) ∧ Real.sin (2 * π * t₂) = -(y₀/R) ∧
      Real.cos (2 * π * t₁) = -Real.sqrt (1 - (y₀/R)^2) ∧
      Real.cos (2 * π * t₂) = Real.sqrt (1 - (y₀/R)^2) ∧
      (∀ t ∈ Icc t₁ t₂, y₀/R ≤ -Real.sin (2 * π * t)) ∧
      (∀ t ∈ Icc (0:ℝ) t₁ ∪ Icc t₂ 1, -Real.sin (2 * π * t) ≤ y₀/R) := by
    set q : ℝ := y₀ / R with hqdef
    have hq0 : 0 < q := div_pos hy₀ (hy₀.trans hRy₀)
    have hq1 : q < 1 := (div_lt_one (hy₀.trans hRy₀)).2 hRy₀
    have harcsin_mem : Real.arcsin q ∈ Ioo (0:ℝ) (π/2) := by
      constructor
      · exact Real.arcsin_pos.2 hq0
      · exact Real.arcsin_lt_pi_div_two.2 hq1
    set α : ℝ := Real.arcsin q with hαdef
    have hα0 : 0 < α := harcsin_mem.1
    have hαp2 : α < π/2 := harcsin_mem.2
    have hsinα : Real.sin α = q := Real.sin_arcsin (by linarith) (by linarith)
    set t₁ : ℝ := 1/2 + α/(2*π) with ht1def
    set t₂ : ℝ := 1 - α/(2*π) with ht2def
    have hπpos : 0 < π := Real.pi_pos
    have hφ1 : 2*π*t₁ - π = α := by rw [ht1def]; field_simp; ring
    have hφ2 : 2*π*t₂ - π = π - α := by rw [ht2def]; field_simp; ring
    have hsinshift : ∀ t : ℝ, Real.sin (2*π*t) = -Real.sin (2*π*t - π) := by
      intro t
      linarith [Real.sin_sub_pi (2*π*t)]
    have hbound_hi : ∀ φ ∈ Icc α (π - α), q ≤ Real.sin φ := by
      intro φ hφ
      by_cases hle : φ ≤ π/2
      · have hαφ : α ≤ φ := hφ.1
        have hmono := Real.strictMonoOn_sin.monotoneOn ⟨by linarith, by linarith⟩
          ⟨by linarith, by linarith⟩ hαφ
        linarith [hsinα]
      · rw [not_le] at hle
        have hle2 : α ≤ π - φ := by linarith [hφ.2]
        have hsinref : Real.sin φ = Real.sin (π - φ) := (Real.sin_pi_sub φ).symm
        have hmono := Real.strictMonoOn_sin.monotoneOn
          (show α ∈ Icc (-(π/2)) (π/2) by constructor <;> linarith)
          (show π - φ ∈ Icc (-(π/2)) (π/2) by constructor <;> linarith) hle2
        rw [hsinref]
        linarith [hsinα]
    have hbound_lo_left : ∀ φ ∈ Icc (-π) α, Real.sin φ ≤ q := by
      intro φ hφ
      by_cases hge : -(π/2) ≤ φ
      · have hmono := Real.strictMonoOn_sin.monotoneOn
          (show φ ∈ Icc (-(π/2)) (π/2) by constructor <;> linarith [hφ.2])
          (show α ∈ Icc (-(π/2)) (π/2) by constructor <;> linarith) hφ.2
        linarith [hsinα]
      · rw [not_le] at hge
        have hsinneg : Real.sin φ = -Real.sin (φ + π) := by
          linarith [Real.sin_add_pi φ]
        have hmem : φ + π ∈ Icc (0:ℝ) (π/2) := ⟨by linarith [hφ.1], by linarith⟩
        have hnn : 0 ≤ Real.sin (φ + π) := Real.sin_nonneg_of_nonneg_of_le_pi hmem.1 (by linarith [hmem.2])
        rw [hsinneg]; linarith
    have hbound_lo_right : ∀ φ ∈ Icc (π - α) π, Real.sin φ ≤ q := by
      intro φ hφ
      have hsinref : Real.sin φ = Real.sin (π - φ) := (Real.sin_pi_sub φ).symm
      have hmem : π - φ ∈ Icc (0:ℝ) α := ⟨by linarith [hφ.2], by linarith [hφ.1]⟩
      have hmono := Real.strictMonoOn_sin.monotoneOn
        (show π - φ ∈ Icc (-(π/2)) (π/2) by constructor <;> linarith [hmem.1, hmem.2])
        (show α ∈ Icc (-(π/2)) (π/2) by constructor <;> linarith) hmem.2
      rw [hsinref]; linarith [hsinα]
    refine ⟨t₁, t₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ht1def]; positivity
    · rw [ht1def, ht2def]; nlinarith [hπpos]
    · rw [ht2def]; nlinarith [Real.pi_gt_three]
    · rw [hsinshift, hφ1, hsinα]
    · rw [hsinshift, hφ2, show Real.sin (π - α) = Real.sin α from Real.sin_pi_sub α, hsinα]
    · rw [show (2*π*t₁) = α + π by linarith [hφ1], Real.cos_add_pi,
        Real.cos_eq_sqrt_one_sub_sin_sq (by linarith) (by linarith), hsinα]
    · rw [show (2*π*t₂) = (π - α) + π by linarith [hφ2], Real.cos_add_pi,
        show Real.cos (π - α) = -Real.cos α from Real.cos_pi_sub α,
        Real.cos_eq_sqrt_one_sub_sin_sq (by linarith) (by linarith), hsinα]
      ring
    · intro t ht
      rw [hsinshift]
      have hφmem : 2*π*t - π ∈ Icc α (π - α) := ⟨by
        have hh := ht.1; rw [ht1def] at hh; nlinarith, by
        have hh := ht.2; rw [ht2def] at hh; nlinarith⟩
      linarith [hbound_hi _ hφmem]
    · rintro t (ht | ht)
      · rw [hsinshift]
        have hφmem : 2*π*t - π ∈ Icc (-π) α := ⟨by
          have hh := ht.1; nlinarith, by
          have hh := ht.2; rw [ht1def] at hh; nlinarith⟩
        linarith [hbound_lo_left _ hφmem]
      · rw [hsinshift]
        have hφmem : 2*π*t - π ∈ Icc (π - α) π := ⟨by
          have hh := ht.1; rw [ht2def] at hh; nlinarith, by
          have hh := ht.2; nlinarith⟩
        linarith [hbound_lo_right _ hφmem]

set_option maxHeartbeats 400000 in
theorem qcl_w_hloc_of_strictMono_boundary {g : ℂ → ℂ} {G : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension g upperHalf upperHalf G)
    (hgs : g '' upperHalf = upperHalf) (hinf : G extInf = extInf)
    {z₀ : ℂ} (hz₀ : z₀ ∈ upperHalf)
    (f : ℝ → ℝ) (hfcont : Continuous f) (hfinj : Function.Injective f)
    (hf : ∀ t : ℝ, G (((t : ℝ) : ℂ) : ExtPlane) = (((f t : ℝ) : ℂ) : ExtPlane))
    (hmono : StrictMono f) :
    ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (L t) = g (z₀ + ρ * Complex.exp (2 * π * I * t)) - g z₀) →
      L 1 - L 0 = 2 * π * I := by
  -- Reconstruct the redundant hypotheses of `wn_false_of_strictAnti_boundary` from `hG`, exactly
  -- as done at its call site inside `cyclicOrder_preserved_of_isHomeoExtension_of_fixes_infty`.
  obtain ⟨hFf, hFc, hFi, hFimg⟩ := hG
  have hUo : IsOpen upperHalf := scExt_isOpen_upperHalf
  have hFfr : G '' frontier (toExt upperHalf) = frontier (toExt upperHalf) :=
    IsHomeoExtension.image_frontier hUo hUo hgs ⟨hFf, hFc, hFi, hFimg⟩
  have hfr_eq : frontier (toExt upperHalf) = toExt {z : ℂ | z.im = 0} ∪ {extInf} :=
    scExt_frontier_toExt_upperHalf
  have hcl_eq : closure (toExt upperHalf) = toExt {z : ℂ | 0 ≤ z.im} ∪ {extInf} :=
    scExt_closure_toExt_upperHalf
  -- f is surjective onto ℝ.
  have hfsurj : Function.Surjective f := by
    intro s
    have hsmem : (((s:ℝ):ℂ):ExtPlane) ∈ frontier (toExt upperHalf) := by
      rw [hfr_eq]; exact Or.inl ⟨(s:ℂ), rfl, rfl⟩
    have hsmem' : (((s:ℝ):ℂ):ExtPlane) ∈ G '' frontier (toExt upperHalf) := by
      rw [hFfr]; exact hsmem
    obtain ⟨p, hpmem, hpeq⟩ := hsmem'
    induction p using OnePoint.rec with
    | infty => rw [hinf] at hpeq; exact absurd hpeq (OnePoint.infty_ne_coe _)
    | coe z =>
      rw [hfr_eq] at hpmem
      rcases hpmem with ⟨z', hz', hzeq⟩ | hz'
      · refine ⟨z'.re, ?_⟩
        have hz're : z' = (z'.re : ℂ) := Complex.ext rfl (by simpa using hz')
        have := hf z'.re
        rw [← hz're, hzeq] at this
        exact Complex.ofReal_injective (OnePoint.coe_injective (this.symm.trans hpeq))
      · exact absurd hz' (OnePoint.coe_ne_infty _)
  -- G₀: the ℂ-valued extraction of G on the closed half-plane.
  have hG0ex : ∀ z : ℂ, ∃ w : ℂ, 0 ≤ z.im → G ((z:ℂ):ExtPlane) = ((w:ℂ):ExtPlane) := by
    intro z
    by_cases hz : 0 ≤ z.im
    · rcases eq_or_lt_of_le hz with heq | hlt
      · have hzre : z = (z.re : ℂ) := Complex.ext rfl heq.symm
        exact ⟨f z.re, fun _ => by rw [hzre]; exact hf z.re⟩
      · exact ⟨g z, fun _ => hFf z hlt⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose G₀ hG₀ using hG0ex
  have hmapsto : ∀ z : ℂ, 0 ≤ z.im → ((z:ℂ):ExtPlane) ∈ closure (toExt upperHalf) := by
    intro z hz
    rw [hcl_eq]; exact Or.inl ⟨z, hz, rfl⟩
  have hG0cont : ContinuousOn G₀ {z : ℂ | 0 ≤ z.im} := by
    have hcompcont : ContinuousOn (fun z : ℂ => G ((z:ℂ):ExtPlane)) {z : ℂ | 0 ≤ z.im} :=
      hFc.comp (OnePoint.continuous_coe.continuousOn) hmapsto
    have heq : EqOn (fun z => ((G₀ z:ℂ):ExtPlane)) (fun z : ℂ => G ((z:ℂ):ExtPlane))
        {z : ℂ | 0 ≤ z.im} := fun z hz => (hG₀ z hz).symm
    have hcompcont' : ContinuousOn (fun z : ℂ => ((G₀ z:ℂ):ExtPlane)) {z : ℂ | 0 ≤ z.im} :=
      hcompcont.congr heq
    exact OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_iff.2 hcompcont'
  -- Basic quantities.
  set x₀ : ℝ := z₀.re with hx₀def
  set y₀ : ℝ := z₀.im with hy₀def
  have hy₀ : 0 < y₀ := hz₀
  set w₀ : ℂ := g z₀ with hw₀def
  have hw₀mem : w₀ ∈ upperHalf := hgs ▸ mem_image_of_mem g hz₀
  have hw₀ : 0 < w₀.im := hw₀mem
  -- H5, applied with K := ‖w₀‖ (needs G's continuity at ∞ restricted to the closed half-plane).
  have hH5 : ∃ M : ℝ, ∀ z : ℂ, 0 ≤ z.im → M < ‖z‖ →
      ∀ w : ℂ, G ((z:ℂ):ExtPlane) = ((w:ℂ):ExtPlane) → ‖w₀‖ < ‖w‖ := by
    have hinfcl : extInf ∈ closure (toExt upperHalf) := by rw [hcl_eq]; exact Or.inr rfl
    have hCWA : ContinuousWithinAt G (closure (toExt upperHalf)) extInf := hFc extInf hinfcl
    rw [ContinuousWithinAt, hinf] at hCWA
    have hmem : (toExt (closedBall (0:ℂ) ‖w₀‖))ᶜ ∪ {extInf} ∈ 𝓝 (extInf : ExtPlane) := by
      rw [OnePoint.nhds_infty_eq, mem_sup]
      refine ⟨?_, subset_union_right (mem_singleton _)⟩
      rw [Filter.mem_map]
      have hbase : (closedBall (0:ℂ) ‖w₀‖)ᶜ ∈ Filter.coclosedCompact ℂ :=
        (isCompact_closedBall (0:ℂ) ‖w₀‖).compl_mem_coclosedCompact_of_isClosed isClosed_closedBall
      filter_upwards [hbase] with z hz
      left
      intro hzmem
      obtain ⟨w, hw, hweq⟩ := hzmem
      exact hz (OnePoint.coe_injective hweq ▸ hw)
    have hpre : (G ⁻¹' ((toExt (closedBall (0:ℂ) ‖w₀‖))ᶜ ∪ {extInf})) ∈
        𝓝[closure (toExt upperHalf)] extInf := hCWA hmem
    rw [nhdsWithin, Filter.mem_inf_iff] at hpre
    obtain ⟨s, hs, t, ht, hst⟩ := hpre
    rw [OnePoint.nhds_infty_eq, Filter.mem_sup] at hs
    obtain ⟨hs1, -⟩ := hs
    rw [Filter.mem_map] at hs1
    obtain ⟨C, ⟨hCclosed, hCcompact⟩, hCsub⟩ := Filter.hasBasis_coclosedCompact.mem_iff.mp hs1
    obtain ⟨Mb, hMb⟩ := hCcompact.isBounded.subset_closedBall (0:ℂ)
    refine ⟨Mb, fun z hzmem hzM w hw => ?_⟩
    have hzC : z ∉ C := fun hzC0 => by
      have := hMb hzC0
      rw [mem_closedBall_iff_norm] at this
      simp only [sub_zero] at this
      linarith
    have hzs : (z:ExtPlane) ∈ s := hCsub hzC
    have hzt : (z:ExtPlane) ∈ t := mem_principal.mp ht (hmapsto z hzmem)
    have hzst : (z:ExtPlane) ∈ G ⁻¹' ((toExt (closedBall (0:ℂ) ‖w₀‖))ᶜ ∪ {extInf}) := by
      rw [hst]; exact ⟨hzs, hzt⟩
    simp only [mem_preimage, hw] at hzst
    rcases hzst with h | h
    · by_cases hwK : w ∈ closedBall (0:ℂ) ‖w₀‖
      · exact absurd ⟨w, hwK, rfl⟩ h
      · rw [mem_closedBall_iff_norm] at hwK
        simp only [sub_zero, not_le] at hwK
        linarith
    · exact absurd h (OnePoint.coe_ne_infty w)
  obtain ⟨M₀, hM₀⟩ := hH5
  set M : ℝ := max M₀ 0 with hMdef
  have hMnonneg : 0 ≤ M := le_max_right _ _
  have hM : ∀ z : ℂ, 0 ≤ z.im → M < ‖z‖ → ∀ w : ℂ, G ((z:ℂ):ExtPlane) = ((w:ℂ):ExtPlane) →
      ‖w₀‖ < ‖w‖ := fun z hz hzM w hw => hM₀ z hz (lt_of_le_of_lt (le_max_left _ _) hzM) w hw
  -- Surjectivity + monotonicity of `f` (MIRROR of `hfarleft`/`hfarright`: `f` increasing, so for
  -- `a` large, `f (x₀-a)` is very negative and `f (x₀+a)` is very positive).
  have hfarleft : ∃ a₀ : ℝ, ∀ a : ℝ, a₀ < a → f (x₀ - a) < w₀.re := by
    obtain ⟨t, ht⟩ := hfsurj (w₀.re - 1)
    refine ⟨x₀ - t, fun a ha => ?_⟩
    have hlt : x₀ - a < t := by linarith
    have := hmono hlt
    rw [ht] at this
    linarith
  have hfarright : ∃ a₀ : ℝ, ∀ a : ℝ, a₀ < a → w₀.re < f (x₀ + a) := by
    obtain ⟨t, ht⟩ := hfsurj (w₀.re + 1)
    refine ⟨t - x₀, fun a ha => ?_⟩
    have hlt : t < x₀ + a := by linarith
    have := hmono hlt
    rw [ht] at this
    linarith
  obtain ⟨a₁, ha₁⟩ := hfarleft
  obtain ⟨a₂, ha₂⟩ := hfarright
  -- Choose `R` large enough for all of: `R > M + ‖z₀‖`, `√(R²-y₀²) > a₁`, `√(R²-y₀²) > a₂`.
  set c : ℝ := y₀ + M + ‖z₀‖ + |a₁| + |a₂| + 1 with hcdef
  have hcpos : 0 < c := by positivity
  have heq : (Real.sqrt (c^2+y₀^2))^2 - y₀^2 = c^2 := by
    rw [Real.sq_sqrt (by positivity)]; ring
  have hc_lt : c < Real.sqrt (c^2+y₀^2) := by
    have h1 : c^2 < c^2 + y₀^2 := by nlinarith
    have h2 : Real.sqrt (c^2) < Real.sqrt (c^2+y₀^2) := Real.sqrt_lt_sqrt (by positivity) h1
    rwa [Real.sqrt_sq hcpos.le] at h2
  obtain ⟨R, hRy₀, hRM, hRa₁, hRa₂⟩ : ∃ R : ℝ, y₀ < R ∧ M + ‖z₀‖ < R ∧
      a₁ < Real.sqrt (R^2 - y₀^2) ∧ a₂ < Real.sqrt (R^2 - y₀^2) := by
    refine ⟨Real.sqrt (c^2 + y₀^2), ?_, ?_, ?_, ?_⟩
    · have h1 : y₀^2 < c^2 + y₀^2 := by nlinarith
      have h2 : Real.sqrt (y₀^2) < Real.sqrt (c^2+y₀^2) := Real.sqrt_lt_sqrt (by positivity) h1
      rwa [Real.sqrt_sq hy₀.le] at h2
    · have hc' : M + ‖z₀‖ < c := by
        rw [hcdef]; have h1 := abs_nonneg a₁; have h2 := abs_nonneg a₂; linarith
      linarith
    · rw [heq, Real.sqrt_sq hcpos.le]
      have h1 : a₁ ≤ |a₁| := le_abs_self a₁
      have h2 : |a₁| < c := by
        rw [hcdef]; have h3 := abs_nonneg a₂; have h4 := norm_nonneg z₀; linarith
      linarith
    · rw [heq, Real.sqrt_sq hcpos.le]
      have h1 : a₂ ≤ |a₂| := le_abs_self a₂
      have h2 : |a₂| < c := by
        rw [hcdef]; have h3 := abs_nonneg a₁; have h4 := norm_nonneg z₀; linarith
      linarith
  set a : ℝ := Real.sqrt (R^2 - y₀^2) with hadef
  have hR0 : 0 < R := hy₀.trans hRy₀
  -- H1: the radius function.
  obtain ⟨ρR, hρRcont, hρRbd, hρRper, hρRhalf, hρRhi, hρRbdy⟩ :
      ∃ ρR : ℝ → ℝ, Continuous ρR ∧ (∀ t : ℝ, y₀ ≤ ρR t ∧ ρR t ≤ R) ∧ ρR 1 = ρR 0 ∧
        (∀ (t : ℝ) (r : ℝ), 0 ≤ r → r ≤ ρR t →
          0 ≤ ((r:ℂ) * Complex.exp (2 * π * I * (t:ℂ))).im + y₀) ∧
        (∀ t : ℝ, -Real.sin (2 * π * t) ≤ y₀ / R → ρR t = R) ∧
        (∀ t : ℝ, y₀ / R ≤ -Real.sin (2 * π * t) →
          ((ρR t : ℂ) * Complex.exp (2 * π * I * (t:ℂ))).im + y₀ = 0) := by
    set q : ℝ := y₀ / R with hqdef
    have hq0 : 0 < q := div_pos hy₀ (hy₀.trans hRy₀)
    have hq1 : q < 1 := (div_lt_one (hy₀.trans hRy₀)).2 hRy₀
    set ρR : ℝ → ℝ := fun t => y₀ / max (-Real.sin (2 * π * t)) q with hρdef
    have hmaxpos : ∀ t, 0 < max (-Real.sin (2 * π * t)) q := fun t => lt_max_of_lt_right hq0
    have hmaxle1 : ∀ t, max (-Real.sin (2 * π * t)) q ≤ 1 := by
      intro t
      apply max_le
      · linarith [Real.neg_one_le_sin (2 * π * t)]
      · linarith
    have him : ∀ t : ℝ, (Complex.exp (2 * π * I * (t:ℂ))).im = Real.sin (2 * π * t) := by
      intro t
      rw [show (2 * π * I * (t:ℂ) : ℂ) = ((2 * π * t : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.exp_ofReal_mul_I_im (2 * π * t)
    have himul : ∀ t r : ℝ,
        ((r:ℂ) * Complex.exp (2 * π * I * (t:ℂ))).im = r * Real.sin (2 * π * t) := by
      intro t r
      rw [Complex.mul_im]
      simp [him t]
    refine ⟨ρR, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply Continuous.div continuous_const
      · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).neg.max continuous_const
      · exact fun t => (hmaxpos t).ne'
    · intro t
      constructor
      · rw [hρdef]
        show y₀ ≤ y₀ / max (-Real.sin (2 * π * t)) q
        rw [le_div_iff₀ (hmaxpos t)]
        nlinarith [hmaxle1 t]
      · rw [hρdef]
        show y₀ / max (-Real.sin (2 * π * t)) q ≤ R
        rw [div_le_iff₀ (hmaxpos t)]
        have hqle : q ≤ max (-Real.sin (2 * π * t)) q := le_max_right _ _
        have hRpos : (0:ℝ) < R := hy₀.trans hRy₀
        have hR' : y₀ ≤ R * max (-Real.sin (2 * π * t)) q := by
          calc y₀ = R * q := by rw [hqdef]; field_simp
          _ ≤ R * max (-Real.sin (2 * π * t)) q := by
                apply mul_le_mul_of_nonneg_left hqle (le_of_lt hRpos)
        linarith
    · show ρR 1 = ρR 0
      rw [hρdef]
      have h1 : Real.sin (2 * π * 1) = 0 := by
        rw [mul_one]; exact Real.sin_two_pi
      have h0 : Real.sin (2 * π * 0) = 0 := by simp
      simp only [h1, h0, neg_zero]
    · intro t r hr0 hrρ
      rw [himul]
      by_cases hs : 0 ≤ Real.sin (2 * π * t)
      · nlinarith
      · rw [not_le] at hs
        have hrρ' : r * max (-Real.sin (2*π*t)) q ≤ y₀ := by
          rw [hρdef] at hrρ
          rw [le_div_iff₀ (hmaxpos t)] at hrρ
          linarith [hrρ]
        have hcomp : r * (-Real.sin (2*π*t)) ≤ r * max (-Real.sin (2*π*t)) q :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hr0
        nlinarith
    · intro t ht
      rw [hρdef]
      show y₀ / max (-Real.sin (2 * π * t)) q = R
      have hmax : max (-Real.sin (2*π*t)) q = q := max_eq_right ht
      rw [hmax, hqdef]
      field_simp
    · intro t ht
      rw [himul]
      have hmeq : max (-Real.sin (2*π*t)) q = -Real.sin (2*π*t) := max_eq_left ht
      have hsne : Real.sin (2*π*t) ≠ 0 := by
        intro h0
        rw [h0] at ht
        linarith
      have hval : ρR t * Real.sin (2*π*t) = -y₀ := by
        rw [hρdef]
        show y₀ / max (-Real.sin (2 * π * t)) q * Real.sin (2 * π * t) = -y₀
        rw [hmeq]
        field_simp
      linarith [hval]
  -- H6: the chord endpoints (extracted into `qcl_w_b_chord_endpoints` to keep this
  -- declaration's own heartbeat cost down).
  obtain ⟨t₁, t₂, ht₁pos, ht₁t₂, ht₂lt1, hsint₁, hsint₂, hcost₁, hcost₂, hhi, hlo⟩ :=
    qcl_w_b_chord_endpoints y₀ R hy₀ hRy₀
  -- Now supply `ρ₁ := y₀` and let `ρ`, `L` be arbitrary satisfying the required bounds.
  refine ⟨y₀, hy₀, fun ρ hρpos hρy₀ L hLcont hLexp => ?_⟩
  -- The homotopy (depends on `ρ`).
  set e : ℝ → ℂ := fun t => Complex.exp (2 * π * I * (t:ℂ)) with hedef
  set H : ℝ → ℝ → ℂ := fun s t => G₀ (z₀ + ((1-s) * ρ + s * ρR t) * e t) with hHdef
  have hHmapsto : ∀ s ∈ Icc (0:ℝ) 1, ∀ t : ℝ, 0 ≤ (z₀ + ((1-s)*ρ+s*ρR t)*e t).im := by
    intro s hs t
    have hr0 : 0 ≤ (1-s)*ρ+s*ρR t := by
      have h1 : 0 ≤ (1-s)*ρ := mul_nonneg (by linarith [hs.2]) hρpos.le
      have h2 : 0 ≤ s*ρR t := mul_nonneg hs.1 (le_trans hy₀.le (hρRbd t).1)
      linarith
    have hrρR : (1-s)*ρ+s*ρR t ≤ ρR t := by
      have h1 : (1-s)*ρ ≤ (1-s)*ρR t := mul_le_mul_of_nonneg_left
        (le_trans hρy₀.le (hρRbd t).1) (by linarith [hs.2])
      nlinarith [hs.1, hs.2]
    have hkey := hρRhalf t ((1-s)*ρ+s*ρR t) hr0 hrρR
    have hcast : (((1-s)*ρ+s*ρR t : ℝ) : ℂ) = ((1-s)*ρ+s*ρR t : ℂ) := by push_cast; ring
    rw [hcast] at hkey
    have himeq : (z₀ + ((1-s)*ρ+s*ρR t : ℂ) * e t).im
        = (((1-s)*ρ+s*ρR t : ℂ) * e t).im + y₀ := by
      rw [Complex.add_im, hy₀def]; ring
    show 0 ≤ (z₀ + ((1-s)*ρ+s*ρR t : ℂ) * e t).im
    rw [himeq]
    exact hkey
  have hecont : Continuous e := by rw [hedef]; fun_prop
  have hHcont : ContinuousOn (Function.uncurry H) (Icc 0 1 ×ˢ Icc 0 1) := by
    have hpointcont : Continuous
        (fun p : ℝ × ℝ => z₀ + ((1-p.1)*ρ+p.1*ρR p.2) * e p.2) := by
      have h1 : Continuous (fun p : ℝ × ℝ => (1-p.1)*ρ+p.1*ρR p.2) := by fun_prop
      fun_prop
    have hmapsto2 : MapsTo (fun p : ℝ × ℝ => z₀ + ((1-p.1)*ρ+p.1*ρR p.2) * e p.2)
        (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) {z : ℂ | 0 ≤ z.im} :=
      fun p hp => hHmapsto p.1 hp.1 p.2
    have := hG0cont.comp hpointcont.continuousOn hmapsto2
    convert this using 1
    rfl
  have he1e0 : e 1 = e 0 := by
    rw [hedef]
    show Complex.exp (2 * π * I * (1:ℂ)) = Complex.exp (2 * π * I * (0:ℂ))
    rw [mul_zero, Complex.exp_zero, mul_one]
    rw [show (2 * (π:ℂ) * I : ℂ) = ((2*π:ℝ):ℂ) * I by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I]
    simp [Real.cos_two_pi, Real.sin_two_pi]
  have hHper : ∀ s ∈ Icc (0:ℝ) 1, H s 1 = H s 0 := by
    intro s hs
    rw [hHdef]
    show G₀ (z₀ + ((1-s)*ρ+s*ρR 1) * e 1) = G₀ (z₀ + ((1-s)*ρ+s*ρR 0) * e 0)
    rw [hρRper, he1e0]
  have hG0z0 : G₀ z₀ = w₀ := by
    have h1 := hG₀ z₀ hz₀.le
    have h2 := hFf z₀ hz₀
    rw [h1] at h2
    exact OnePoint.coe_injective h2
  have hHavoid : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, H s t - w₀ ≠ 0 := by
    intro s hs t ht hcontra
    rw [sub_eq_zero] at hcontra
    simp only [hHdef] at hcontra
    have hρRtpos : 0 < ρR t := lt_of_lt_of_le hy₀ (hρRbd t).1
    have hrpos : 0 < (1-s)*ρ+s*ρR t := by
      rcases lt_or_eq_of_le hs.2 with hs1 | hs1
      · have h1 : 0 < (1-s)*ρ := mul_pos (by linarith) hρpos
        have h2 : 0 ≤ s*ρR t := mul_nonneg hs.1 hρRtpos.le
        linarith
      · subst hs1
        nlinarith [hρRtpos]
    have hene : e t ≠ 0 := Complex.exp_ne_zero _
    have hrne : ((1-s)*ρ+s*ρR t : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
    have hprodne : ((1-s)*ρ+s*ρR t) * e t ≠ 0 := mul_ne_zero hrne hene
    have hzne : z₀ + ((1-s)*ρ+s*ρR t) * e t ≠ z₀ := by
      intro heq
      apply hprodne
      linear_combination heq
    have hmem1 : (0:ℝ) ≤ (z₀ + ((1-s)*ρ+s*ρR t) * e t).im := hHmapsto s hs t
    have hmem2 : (0:ℝ) ≤ z₀.im := hz₀.le
    have hGeq : G ((z₀ + ((1-s)*ρ+s*ρR t) * e t : ℂ):ExtPlane) = G ((z₀:ℂ):ExtPlane) := by
      rw [hG₀ _ hmem1, hG₀ _ hmem2, hcontra, hG0z0]
    have := hFi (hmapsto _ hmem1) (hmapsto _ hmem2) hGeq
    exact hzne (OnePoint.coe_injective this)
  -- Connect `H 0` to the given small circle `g (z₀ + ρ e t)`, and identify `L` (the GIVEN lift)
  -- as a lift of `H 0 t - w₀` directly (no need to invoke an external `hloc`, unlike the source).
  have hz0pos : ∀ t : ℝ, 0 < (z₀ + (ρ:ℂ) * Complex.exp (2 * π * I * (t:ℂ))).im := by
    intro t
    have him2 : (Complex.exp (2 * π * I * (t:ℂ))).im = Real.sin (2 * π * t) := by
      rw [show (2 * π * I * (t:ℂ) : ℂ) = ((2 * π * t : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.exp_ofReal_mul_I_im (2 * π * t)
    have heqim : (z₀ + (ρ:ℂ) * Complex.exp (2 * π * I * (t:ℂ))).im
        = y₀ + ρ * Real.sin (2 * π * t) := by
      rw [Complex.add_im, Complex.mul_im, him2]
      simp [hy₀def]
    rw [heqim]
    nlinarith [Real.neg_one_le_sin (2 * π * t), hρy₀, hρpos]
  have hG0eqg : ∀ t : ℝ,
      G₀ (z₀ + (ρ:ℂ) * Complex.exp (2 * π * I * (t:ℂ)))
        = g (z₀ + (ρ:ℂ) * Complex.exp (2 * π * I * (t:ℂ))) := by
    intro t
    have h1 := hG₀ _ (hz0pos t).le
    have h2 := hFf _ (hz0pos t)
    rw [h1] at h2
    exact OnePoint.coe_injective h2
  have hH0eq : ∀ t : ℝ, H 0 t = g (z₀ + (ρ:ℂ) * Complex.exp (2 * π * I * (t:ℂ))) := by
    intro t
    rw [hHdef]
    show G₀ (z₀ + ((1-(0:ℝ))*ρ+(0:ℝ)*ρR t) * e t)
        = g (z₀ + (ρ:ℂ) * Complex.exp (2 * π * I * (t:ℂ)))
    have harg : (z₀ + ((1-(0:ℝ))*ρ+(0:ℝ)*ρR t) * e t)
        = z₀ + (ρ:ℂ) * Complex.exp (2 * π * I * (t:ℂ)) := by
      rw [hedef]; push_cast; ring
    rw [harg]
    exact hG0eqg t
  have hLexp' : ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (L t) = H 0 t - w₀ := by
    intro t ht
    rw [hH0eq t]
    exact hLexp t ht
  -- Fresh lift of the big loop `H 1`, and its lift-change equals `L`'s (via the homotopy).
  have hH1cont : ContinuousOn (fun t => H 1 t) (Icc (0:ℝ) 1) := by
    have hcomp : ContinuousOn (fun t : ℝ => Function.uncurry H (1, t)) (Icc (0:ℝ) 1) :=
      hHcont.comp (continuousOn_const.prodMk continuousOn_id)
        (fun t ht => ⟨right_mem_Icc.2 zero_le_one, ht⟩)
    simpa [Function.uncurry] using hcomp
  obtain ⟨Γlift, hΓcont, hΓexp⟩ := exists_continuousOn_log_lift
    (γ := fun t => H 1 t) (w := w₀) hH1cont
    (fun t ht => sub_ne_zero.mp (hHavoid 1 (right_mem_Icc.2 zero_le_one) t ht))
  have hΓLeq : L 1 - L 0 = Γlift 1 - Γlift 0 :=
    lift_change_eq_of_homotopy hHcont hHper
      (fun s hs t ht => sub_ne_zero.mp (hHavoid s hs t ht)) hLcont hΓcont hLexp' hΓexp
  -- Periodicity of the given small loop forces `L 1 - L 0` to be an integer multiple of `2πI`.
  have hexp_eq : Complex.exp (L 1) = Complex.exp (L 0) := by
    rw [hLexp' 1 (right_mem_Icc.2 zero_le_one), hLexp' 0 (left_mem_Icc.2 zero_le_one),
      hHper 0 (left_mem_Icc.2 zero_le_one)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp_eq
  have hLchange : L 1 - L 0 = (n:ℂ) * (2 * (π:ℝ) * I) := by rw [hn]; ring
  have hΓn : Γlift 1 - Γlift 0 = (n:ℂ) * (2 * (π:ℝ) * I) := hΓLeq.symm.trans hLchange
  -- The three-piece geometric split: chord [t₁,t₂] and arcs [0,t₁], [t₂,1] (identical to the
  -- source: none of this uses monotonicity/antitonicity of `f`).
  have him2 : ∀ s : ℝ, (Complex.exp (2 * π * I * (s:ℂ))).im = Real.sin (2 * π * s) := by
    intro s
    rw [show (2 * π * I * (s:ℂ) : ℂ) = ((2 * π * s : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.exp_ofReal_mul_I_im (2 * π * s)
  have hre2 : ∀ s : ℝ, (Complex.exp (2 * π * I * (s:ℂ))).re = Real.cos (2 * π * s) := by
    intro s
    rw [show (2 * π * I * (s:ℂ) : ℂ) = ((2 * π * s : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.exp_ofReal_mul_I_re (2 * π * s)
  have hG0real : ∀ z : ℂ, z.im = 0 → G₀ z = f z.re := by
    intro z hz
    have hzre : z = (z.re:ℂ) := by apply Complex.ext <;> simp [hz]
    have h1 := hG₀ z hz.ge
    have h2 := hf z.re
    rw [← hzre] at h2
    rw [h1] at h2
    exact OnePoint.coe_injective h2
  have hρRt1 : ρR t₁ = R := hρRhi t₁ (by linarith [hsint₁])
  have hρRt2 : ρR t₂ = R := hρRhi t₂ (by linarith [hsint₂])
  have hRne : R ≠ 0 := hR0.ne'
  have hRa_eq : R * Real.sqrt (1 - (y₀/R)^2) = a := by
    have hnn : (0:ℝ) ≤ 1 - (y₀/R)^2 := by
      have hq2 : (y₀/R)^2 ≤ 1 := by
        rw [div_pow, div_le_one (by positivity)]
        nlinarith [hRy₀]
      linarith
    have hsq : (R * Real.sqrt (1 - (y₀/R)^2))^2 = R^2 - y₀^2 := by
      rw [mul_pow, Real.sq_sqrt hnn, div_pow]
      field_simp
    rw [hadef, ← hsq, Real.sqrt_sq (mul_nonneg hR0.le (Real.sqrt_nonneg _))]
  have hH1t1 : H 1 t₁ = (f (x₀ - a) : ℂ) := by
    have hH1eq : H 1 t₁ = G₀ (z₀ + (R:ℂ)*e t₁) := by
      rw [hHdef]
      show G₀ (z₀+((1-(1:ℝ))*ρ+(1:ℝ)*ρR t₁)*e t₁) = G₀ (z₀+(R:ℂ)*e t₁)
      congr 2; rw [hρRt1]; push_cast; ring
    have hzim0 : (z₀+(R:ℂ)*e t₁).im = 0 := by
      have hbd := hρRbdy t₁ (hhi t₁ ⟨le_refl t₁, ht₁t₂.le⟩)
      rw [hρRt1] at hbd
      rw [Complex.add_im, show e t₁ = Complex.exp (2*π*I*(t₁:ℂ)) from rfl]
      linarith [hy₀def]
    have hreeq : (z₀+(R:ℂ)*e t₁).re = x₀ - a := by
      rw [Complex.add_re, hedef]
      show z₀.re + ((R:ℂ)*Complex.exp (2*π*I*(t₁:ℂ))).re = x₀ - a
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hre2 t₁, hx₀def, hcost₁]
      ring_nf
      ring_nf at hRa_eq
      linarith [hRa_eq]
    rw [hH1eq, hG0real _ hzim0, hreeq]
  have hH1t2 : H 1 t₂ = (f (x₀ + a) : ℂ) := by
    have hH1eq : H 1 t₂ = G₀ (z₀ + (R:ℂ)*e t₂) := by
      rw [hHdef]
      show G₀ (z₀+((1-(1:ℝ))*ρ+(1:ℝ)*ρR t₂)*e t₂) = G₀ (z₀+(R:ℂ)*e t₂)
      congr 2; rw [hρRt2]; push_cast; ring
    have hzim0 : (z₀+(R:ℂ)*e t₂).im = 0 := by
      have hbd := hρRbdy t₂ (hhi t₂ ⟨ht₁t₂.le, le_refl t₂⟩)
      rw [hρRt2] at hbd
      rw [Complex.add_im, show e t₂ = Complex.exp (2*π*I*(t₂:ℂ)) from rfl]
      linarith [hy₀def]
    have hreeq : (z₀+(R:ℂ)*e t₂).re = x₀ + a := by
      rw [Complex.add_re, hedef]
      show z₀.re + ((R:ℂ)*Complex.exp (2*π*I*(t₂:ℂ))).re = x₀ + a
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hre2 t₂, hx₀def, hcost₂]
      ring_nf
      ring_nf at hRa_eq
      linarith [hRa_eq]
    rw [hH1eq, hG0real _ hzim0, hreeq]
  -- MIRROR of `hu1pos`/`hu2neg`: since `f` is increasing rather than decreasing, both signs flip.
  have hu1 : f (x₀ - a) - w₀.re < 0 := by linarith [ha₁ a hRa₁]
  have hu2 : 0 < f (x₀ + a) - w₀.re := by linarith [ha₂ a hRa₂]
  -- MIRROR of `hchord`: the chord contribution now lies in `(0, π)` instead of `(-π, 0)`.
  have hchord : (Γlift t₂ - Γlift t₁).im ∈ Ioo 0 π := by
    have hγt1 : H 1 t₁ - w₀ = ((f (x₀-a) - w₀.re : ℝ):ℂ) - I*w₀.im := by
      rw [hH1t1]; apply Complex.ext <;> simp
    have hγt2 : H 1 t₂ - w₀ = ((f (x₀+a) - w₀.re : ℝ):ℂ) - I*w₀.im := by
      rw [hH1t2]; apply Complex.ext <;> simp
    have harg1 : -π < Complex.arg (H 1 t₁ - w₀) ∧ Complex.arg (H 1 t₁ - w₀) < 0 := by
      rw [hγt1]; exact arg_ofReal_sub_I_mul_mem w₀.im hw₀ _
    have harg2 : -π < Complex.arg (H 1 t₂ - w₀) ∧ Complex.arg (H 1 t₂ - w₀) < 0 := by
      rw [hγt2]; exact arg_ofReal_sub_I_mul_mem w₀.im hw₀ _
    have hargmono : Complex.arg (H 1 t₁ - w₀) < Complex.arg (H 1 t₂ - w₀) := by
      rw [hγt1, hγt2]
      exact arg_ofReal_sub_I_mul_strictMono w₀.im hw₀ _ _ (by linarith [hu1, hu2])
    have hslit : ∀ t ∈ Icc t₁ t₂, H 1 t - w₀ ∈ slitPlane := by
      intro t ht
      have hzim0 : (z₀+(ρR t:ℂ)*e t).im = 0 := by
        have hbd := hρRbdy t (hhi t ht)
        rw [Complex.add_im, show e t = Complex.exp (2*π*I*(t:ℂ)) from rfl]
        linarith [hy₀def]
      have hH1eq : H 1 t = G₀ (z₀+(ρR t:ℂ)*e t) := by
        rw [hHdef]
        show G₀ (z₀+((1-(1:ℝ))*ρ+(1:ℝ)*ρR t)*e t) = G₀ (z₀+(ρR t:ℂ)*e t)
        congr 2; push_cast; ring
      rw [hH1eq, hG0real _ hzim0]
      rw [Complex.mem_slitPlane_iff]
      right
      simp [hw₀.ne']
    have hH1cont' : ContinuousOn (fun t => H 1 t) (Icc t₁ t₂) := by
      have hcomp : ContinuousOn (fun t : ℝ => Function.uncurry H (1, t)) (Icc t₁ t₂) :=
        hHcont.comp (continuousOn_const.prodMk continuousOn_id)
          (fun t ht => ⟨right_mem_Icc.2 zero_le_one,
            ⟨ht₁pos.le.trans ht.1, ht.2.trans ht₂lt1.le⟩⟩)
      simpa [Function.uncurry] using hcomp
    have hΓcont' : ContinuousOn Γlift (Icc t₁ t₂) :=
      hΓcont.mono (fun t ht => ⟨ht₁pos.le.trans ht.1, ht.2.trans ht₂lt1.le⟩)
    have hΓexp' : ∀ t ∈ Icc t₁ t₂, Complex.exp (Γlift t) = H 1 t - w₀ := fun t ht =>
      hΓexp t ⟨ht₁pos.le.trans ht.1, ht.2.trans ht₂lt1.le⟩
    have hkey := lift_sub_eq_log_sub_log (γ := fun t => H 1 t - w₀) ht₁t₂.le
      (hH1cont'.sub continuousOn_const) hΓcont' hslit hΓexp'
    have himeq := congrArg Complex.im hkey
    simp only [Complex.sub_im, Complex.log_im] at himeq
    rw [Complex.sub_im, himeq]
    exact ⟨by linarith [hargmono], by linarith [harg2.2, harg1.1]⟩
  -- MIRROR of `harcs`: the arcs contribution now lies in `(π, 2π)` instead of `(-2π, -π)`.
  have harcs : (Γlift 1 - Γlift t₂ + (Γlift t₁ - Γlift 0)).im ∈ Ioo π (2*π) := by
    have hG0im : ∀ z : ℂ, 0 ≤ z.im → 0 ≤ (G₀ z).im := by
      intro z hz
      have h1 := hG₀ z hz
      have h2 : G ((z:ℂ):ExtPlane) ∈ closure (toExt upperHalf) := by
        rw [← hFimg]; exact mem_image_of_mem G (hmapsto z hz)
      rw [h1, hcl_eq] at h2
      rcases h2 with ⟨w, hw, hweq⟩ | h2
      · rw [← OnePoint.coe_injective hweq]; exact hw
      · exact absurd h2 (OnePoint.coe_ne_infty _)
    have henorm : ∀ t : ℝ, ‖e t‖ = 1 := by
      intro t
      rw [hedef]
      show ‖Complex.exp (2*π*I*(t:ℂ))‖ = 1
      rw [Complex.norm_exp]
      have h0 : (2*π*I*(t:ℂ)).re = 0 := by simp
      rw [h0, Real.exp_zero]
    have hH1im : ∀ t : ℝ, 0 ≤ (H 1 t).im := by
      intro t
      rw [hHdef]
      show 0 ≤ (G₀ (z₀ + ((1-(1:ℝ))*ρ+(1:ℝ)*ρR t) * e t)).im
      apply hG0im
      have harg : (z₀ + ((1-(1:ℝ))*ρ+(1:ℝ)*ρR t) * e t) = z₀ + (ρR t : ℂ) * e t := by
        push_cast; ring
      rw [harg, Complex.add_im]
      have hr0 : (0:ℝ) ≤ ρR t := le_trans hy₀.le (hρRbd t).1
      have hkey := hρRhalf t (ρR t) hr0 le_rfl
      linarith [hy₀def]
    have hzRnorm : ∀ t : ℝ, R - ‖z₀‖ ≤ ‖z₀ + (R:ℂ) * e t‖ := by
      intro t
      have h1 := norm_add_le (-z₀) (z₀ + (R:ℂ)*e t)
      have h2 : -z₀ + (z₀+(R:ℂ)*e t) = (R:ℂ)*e t := by ring
      rw [h2, norm_neg] at h1
      have h3 : ‖(R:ℂ)*e t‖ = R := by
        rw [norm_mul, Complex.norm_real, henorm t, mul_one, Real.norm_of_nonneg hR0.le]
      rw [h3] at h1
      linarith
    have hHarcfar : ∀ t : ℝ, -Real.sin (2*π*t) ≤ y₀/R → ‖w₀‖ < ‖H 1 t‖ := by
      intro t ht
      have hρReq : ρR t = R := hρRhi t ht
      have hH1eq : H 1 t = G₀ (z₀ + (R:ℂ)*e t) := by
        rw [hHdef]
        show G₀ (z₀+((1-(1:ℝ))*ρ+(1:ℝ)*ρR t)*e t) = G₀ (z₀+(R:ℂ)*e t)
        congr 2; rw [hρReq]; push_cast; ring
      rw [hH1eq]
      have hzim' : 0 ≤ (z₀+(R:ℂ)*e t).im := by
        rw [Complex.add_im]
        have hkey := hρRhalf t R (hy₀.le.trans hRy₀.le) (hρReq ▸ le_rfl)
        linarith [hy₀def]
      exact hM (z₀+(R:ℂ)*e t) hzim' (by linarith [hzRnorm t, hRM]) (G₀ (z₀+(R:ℂ)*e t)) (hG₀ _ hzim')
    have hL_exp : ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (Γlift t - I*((π:ℝ)/2)) = -I*(H 1 t - w₀) := by
      intro t ht
      have hrw : Γlift t - I*((π:ℝ)/2) = Γlift t + (-(I*((π:ℝ)/2))) := by ring
      rw [hrw, Complex.exp_add, hΓexp t ht]
      have hexpi : Complex.exp (-(I*((π:ℝ)/2))) = -I := by
        rw [show (-(I*((π:ℝ)/2)):ℂ) = ((-(π:ℝ)/2:ℝ):ℂ)*I by push_cast; ring,
          Complex.exp_ofReal_mul_I]
        rw [neg_div, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
        simp
      rw [hexpi]
      ring
    have hΛslit_arc : ∀ t : ℝ, -Real.sin (2*π*t) ≤ y₀/R → -I*(H 1 t - w₀) ∈ slitPlane :=
      fun t ht => neg_I_mul_sub_mem_slitPlane (H 1 t) w₀ (hH1im t) hw₀ (hHarcfar t ht)
    have hH1cont_at : ∀ (S : Set ℝ), S ⊆ Icc (0:ℝ) 1 → ContinuousOn (fun t => H 1 t) S := by
      intro S hsub
      have hcomp : ContinuousOn (fun t : ℝ => Function.uncurry H (1, t)) S :=
        hHcont.comp (continuousOn_const.prodMk continuousOn_id)
          (fun t ht => ⟨right_mem_Icc.2 zero_le_one, hsub ht⟩)
      simpa [Function.uncurry] using hcomp
    have hsub1 : Icc (0:ℝ) t₁ ⊆ Icc (0:ℝ) 1 :=
      fun t ht => ⟨ht.1, ht.2.trans (ht₁t₂.le.trans ht₂lt1.le)⟩
    have hsub2 : Icc t₂ (1:ℝ) ⊆ Icc (0:ℝ) 1 :=
      fun t ht => ⟨(ht₁pos.le.trans ht₁t₂.le).trans ht.1, ht.2⟩
    have hkey1 := lift_sub_eq_log_sub_log ht₁pos.le
      (show ContinuousOn (fun t => -I*(H 1 t - w₀)) (Icc (0:ℝ) t₁) from
        continuousOn_const.mul ((hH1cont_at _ hsub1).sub continuousOn_const))
      (show ContinuousOn (fun t => Γlift t - I*((π:ℝ)/2)) (Icc (0:ℝ) t₁) from
        (hΓcont.mono hsub1).sub continuousOn_const)
      (fun t ht => hΛslit_arc t (hlo t (Or.inl ht)))
      (fun t ht => hL_exp t (hsub1 ht))
    have hkey2 := lift_sub_eq_log_sub_log ht₂lt1.le
      (show ContinuousOn (fun t => -I*(H 1 t - w₀)) (Icc t₂ (1:ℝ)) from
        continuousOn_const.mul ((hH1cont_at _ hsub2).sub continuousOn_const))
      (show ContinuousOn (fun t => Γlift t - I*((π:ℝ)/2)) (Icc t₂ (1:ℝ)) from
        (hΓcont.mono hsub2).sub continuousOn_const)
      (fun t ht => hΛslit_arc t (hlo t (Or.inr ht)))
      (fun t ht => hL_exp t (hsub2 ht))
    have hsimp1 : Γlift t₁ - Γlift 0
        = Complex.log (-I*(H 1 t₁ - w₀)) - Complex.log (-I*(H 1 0 - w₀)) := by
      linear_combination hkey1
    have hsimp2 : Γlift 1 - Γlift t₂
        = Complex.log (-I*(H 1 1 - w₀)) - Complex.log (-I*(H 1 t₂ - w₀)) := by
      linear_combination hkey2
    have hH11eq0 : H 1 1 = H 1 0 := hHper 1 (right_mem_Icc.2 zero_le_one)
    rw [hH11eq0] at hsimp2
    have hsum : (Γlift 1 - Γlift t₂) + (Γlift t₁ - Γlift 0)
        = Complex.log (-I*(H 1 t₁ - w₀)) - Complex.log (-I*(H 1 t₂ - w₀)) := by
      linear_combination hsimp1 + hsimp2
    have himeq2 : (Γlift 1 - Γlift t₂ + (Γlift t₁ - Γlift 0)).im
        = Complex.arg (-I*(H 1 t₁ - w₀)) - Complex.arg (-I*(H 1 t₂ - w₀)) := by
      have h := congrArg Complex.im hsum
      simpa [Complex.add_im, Complex.sub_im, Complex.log_im] using h
    rw [himeq2]
    have hγt1 : -I*(H 1 t₁ - w₀) = -(w₀.im:ℂ) - I*((f (x₀-a) - w₀.re : ℝ):ℂ) := by
      rw [hH1t1]; apply Complex.ext <;> simp
    have hγt2 : -I*(H 1 t₂ - w₀) = -(w₀.im:ℂ) - I*((f (x₀+a) - w₀.re : ℝ):ℂ) := by
      rw [hH1t2]; apply Complex.ext <;> simp
    have harg1 : π/2 < Complex.arg (-I*(H 1 t₁ - w₀)) ∧ Complex.arg (-I*(H 1 t₁ - w₀)) < π := by
      rw [hγt1]; exact arg_neg_ofReal_sub_I_mul_mem_neg w₀.im (f (x₀-a) - w₀.re) hw₀ hu1
    have harg2 : -π < Complex.arg (-I*(H 1 t₂ - w₀)) ∧ Complex.arg (-I*(H 1 t₂ - w₀)) < -π/2 := by
      rw [hγt2]; exact arg_neg_ofReal_sub_I_mul_mem_pos w₀.im (f (x₀+a) - w₀.re) hw₀ hu2
    exact ⟨by linarith [harg1.1, harg2.2], by linarith [harg1.2, harg2.1]⟩
  -- Total: `(Γlift 1 - Γlift 0).im ∈ Ioo π (3*π)`, but it also equals `2*π*n`; pin `n = 1`.
  have hcomplex_eq : Γlift 1 - Γlift 0 =
      (Γlift t₂ - Γlift t₁) + (Γlift 1 - Γlift t₂ + (Γlift t₁ - Γlift 0)) := by ring
  have htotal := congrArg Complex.im hcomplex_eq
  rw [Complex.add_im] at htotal
  have h2πIre : ((2:ℂ) * (π:ℝ) * I).re = 0 := by simp
  have h2πIim : ((2:ℂ) * (π:ℝ) * I).im = 2 * π := by simp
  have hΓnim : (Γlift 1 - Γlift 0).im = 2 * π * (n:ℝ) := by
    rw [hΓn, Complex.mul_im, h2πIre, h2πIim, Complex.intCast_im, Complex.intCast_re]
    ring
  have hlow : π < 2 * π * (n:ℝ) := by linarith [hchord.1, harcs.1, htotal, hΓnim]
  have hhigh : 2 * π * (n:ℝ) < 3 * π := by linarith [hchord.2, harcs.2, htotal, hΓnim]
  have hπpos : 0 < π := Real.pi_pos
  have hn_lb : (1:ℝ) < 2 * (n:ℝ) := by
    by_contra hcon
    rw [not_lt] at hcon
    have hprod : (0:ℝ) ≤ π * (1 - 2*(n:ℝ)) := mul_nonneg hπpos.le (by linarith)
    have hexpand : π * (1 - 2*(n:ℝ)) = π - 2*π*(n:ℝ) := by ring
    rw [hexpand] at hprod
    linarith [hlow]
  have hn_ub : 2 * (n:ℝ) < 3 := by
    by_contra hcon
    rw [not_lt] at hcon
    have hprod : (0:ℝ) ≤ π * (2*(n:ℝ) - 3) := mul_nonneg hπpos.le (by linarith)
    have hexpand : π * (2*(n:ℝ) - 3) = 2*π*(n:ℝ) - 3*π := by ring
    rw [hexpand] at hprod
    linarith [hhigh]
  have hn0 : (0:ℤ) < n := by
    have h1 : (0:ℝ) < (n:ℝ) := by linarith [hn_lb]
    exact_mod_cast h1
  have hn2 : n < 2 := by
    have h1 : (n:ℝ) < 2 := by linarith [hn_ub]
    exact_mod_cast h1
  have hn1 : n = 1 := by omega
  rw [hLchange, hn1]
  norm_num




/-! ### Theorem 8.2 — helpers of piece R -/


/-- Shared helper (extra, prefix `qcl_r_`): if `k` has local winding `+1` at `z₀` (on circles
staying in `ball z₀ r₀`, `k` injective there, `k` continuous there) and `A` is holomorphic near
`k z₀` with nonzero derivative, then `A ∘ k` has local winding `+1` at `z₀` too. (W1 applied to
`A`, combined with the continuity/shrinking bookkeeping needed to instantiate it on an actual
circle of small enough radius.) -/
theorem qcl_r_transport_conformal {k A : ℂ → ℂ} {z₀ : ℂ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hkcont : ContinuousOn k (ball z₀ r₀)) (hkne : ∀ z ∈ ball z₀ r₀, z ≠ z₀ → k z ≠ k z₀)
    (hloc : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (L t) = k (z₀ + ρ * Complex.exp (2 * π * I * t)) - k z₀) →
      L 1 - L 0 = 2 * π * I)
    {U : Set ℂ} (hU : IsOpen U) (hp : k z₀ ∈ U) (hA : DifferentiableOn ℂ A U)
    (hA' : deriv A (k z₀) ≠ 0) :
    ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (L t) = A (k (z₀ + ρ * Complex.exp (2 * π * I * t))) - A (k z₀)) →
      L 1 - L 0 = 2 * π * I := by
  obtain ⟨ρ₁, hρ₁pos, hloc_k⟩ := hloc
  obtain ⟨rW1, hrW1pos, hrW1sub, hW1⟩ := qcl_w_lift_change_eq_of_conformal hU hp hA hA'
  have hkcontz0 : ContinuousAt k z₀ :=
    hkcont.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr₀))
  have henorm : ∀ t : ℝ, ‖Complex.exp (2 * π * I * (t : ℂ))‖ = 1 := by
    intro t
    rw [Complex.norm_exp]
    have h0 : (2 * π * I * (t : ℂ)).re = 0 := by simp
    rw [h0, Real.exp_zero]
  have hαper0 : Complex.exp (2 * π * I * (0 : ℂ)) = Complex.exp (2 * π * I * (1 : ℂ)) := by
    have h1 : (2 * π * I * (0 : ℂ)) = 0 := by ring
    have h2 : (2 * π * I * (1 : ℂ)) = 2 * π * I := by ring
    rw [h1, h2, Complex.exp_zero, Complex.exp_two_pi_mul_I]
  obtain ⟨δ, hδpos, hδball⟩ := Metric.continuousAt_iff.1 hkcontz0 rW1 hrW1pos
  refine ⟨min ρ₁ (min δ r₀), lt_min hρ₁pos (lt_min hδpos hr₀), ?_⟩
  intro ρ hρpos hρlt L hLcont hLe
  have hρρ1 : ρ < ρ₁ := hρlt.trans_le (min_le_left _ _)
  have hρδ : ρ < δ := hρlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hρr0 : ρ < r₀ := hρlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  set α : ℝ → ℂ := fun t => k (z₀ + ρ * Complex.exp (2 * π * I * t)) with hαdef
  have hcircledist : ∀ t : ℝ, dist (z₀ + ρ * Complex.exp (2 * π * I * (t : ℂ))) z₀ = ρ := by
    intro t
    rw [dist_eq_norm]
    have heq : z₀ + (ρ : ℂ) * Complex.exp (2 * π * I * (t : ℂ)) - z₀ =
        (ρ : ℂ) * Complex.exp (2 * π * I * (t : ℂ)) := by ring
    rw [heq, norm_mul, henorm t, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos]
  have hcircleNez0 : ∀ t : ℝ, z₀ + ρ * Complex.exp (2 * π * I * (t : ℂ)) ≠ z₀ := by
    intro t heq
    have h0 : dist (z₀ + ρ * Complex.exp (2 * π * I * (t : ℂ))) z₀ = 0 := by
      rw [heq]; exact dist_self z₀
    rw [hcircledist t] at h0
    linarith [hρpos]
  have hcircleinball0 : ∀ t : ℝ, z₀ + ρ * Complex.exp (2 * π * I * (t : ℂ)) ∈ ball z₀ r₀ := by
    intro t
    rw [mem_ball, hcircledist t]
    exact hρr0
  have hcircleinball : ∀ t : ℝ,
      k (z₀ + ρ * Complex.exp (2 * π * I * (t : ℂ))) ∈ closedBall (k z₀) rW1 := by
    intro t
    have hlt : dist (k (z₀ + ρ * Complex.exp (2 * π * I * (t : ℂ)))) (k z₀) < rW1 :=
      hδball (by rw [hcircledist t]; exact hρδ)
    exact mem_closedBall.2 hlt.le
  have hαNep : ∀ t ∈ Icc (0 : ℝ) 1, α t ≠ k z₀ := fun t _ =>
    hkne _ (hcircleinball0 t) (hcircleNez0 t)
  have hαcirccont : Continuous fun t : ℝ => z₀ + (ρ : ℂ) * Complex.exp (2 * π * I * (t : ℂ)) := by
    fun_prop
  have hαcont : ContinuousOn α (Icc (0 : ℝ) 1) :=
    hkcont.comp hαcirccont.continuousOn (fun t _ => hcircleinball0 t)
  have hαperloop : α 1 = α 0 := by
    show k (z₀ + ρ * Complex.exp (2 * π * I * (1 : ℂ))) =
      k (z₀ + ρ * Complex.exp (2 * π * I * (0 : ℂ)))
    rw [hαper0]
  obtain ⟨L_k, hL_kcont, hL_keq⟩ :=
    exists_continuousOn_log_lift (γ := α) (w := k z₀) hαcont hαNep
  have hL_kdiff : L_k 1 - L_k 0 = 2 * π * I := hloc_k ρ hρpos hρρ1 L_k hL_kcont hL_keq
  have hW1result := hW1 α hαcont hαperloop (fun t _ => hcircleinball t) hαNep L_k L hL_kcont
    hLcont hL_keq hLe
  exact hW1result.trans hL_kdiff

/-- Shared helper (extra, prefix `qcl_r_`): if `f` is holomorphic near `w₀` with nonzero
derivative, `f w₀ = z₀`, and `k` has local winding `+1` at `z₀` (continuous, injective on
`ball z₀ r₀`), then `k ∘ f` has local winding `+1` at `w₀` too. (Trivial winding of `id` at `w₀`,
transported through `f` via `qcl_r_transport_conformal` to get the winding of the loop
`f`-image; then W2 upgrades `k`'s own circle-winding to that specific loop.) -/
theorem qcl_r_transport_precompose {k f : ℂ → ℂ} {w₀ z₀ : ℂ} (hz₀ : f w₀ = z₀)
    {U : Set ℂ} (hU : IsOpen U) (hw₀ : w₀ ∈ U) (hf : DifferentiableOn ℂ f U)
    (hfi : InjOn f U) (hf' : deriv f w₀ ≠ 0) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hkcont : ContinuousOn k (ball z₀ r₀)) (hki : InjOn k (ball z₀ r₀))
    (hloc : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (L t) = k (z₀ + ρ * Complex.exp (2 * π * I * t)) - k z₀) →
      L 1 - L 0 = 2 * π * I) :
    ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (L t) = k (f (w₀ + ρ * Complex.exp (2 * π * I * t))) - k (f w₀)) →
      L 1 - L 0 = 2 * π * I := by
  have henorm : ∀ t : ℝ, ‖Complex.exp (2 * π * I * (t : ℂ))‖ = 1 := by
    intro t
    rw [Complex.norm_exp]
    have h0 : (2 * π * I * (t : ℂ)).re = 0 := by simp
    rw [h0, Real.exp_zero]
  have hloc_id : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (L t) = (w₀ + ρ * Complex.exp (2 * π * I * t)) - w₀) →
      L 1 - L 0 = 2 * π * I := by
    refine ⟨1, one_pos, ?_⟩
    intro ρ hρpos _ L hLcont hLe
    set L₀ : ℝ → ℂ := fun t => (Real.log ρ : ℂ) + 2 * π * I * (t : ℂ) with hL₀def
    have hL₀cont : ContinuousOn L₀ (Icc (0 : ℝ) 1) := by fun_prop
    have hL₀eq : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L₀ t) =
        (w₀ + ρ * Complex.exp (2 * π * I * (t : ℂ))) - w₀ := by
      intro t _
      have heq : w₀ + (ρ : ℂ) * Complex.exp (2 * π * I * (t : ℂ)) - w₀ =
          (ρ : ℂ) * Complex.exp (2 * π * I * (t : ℂ)) := by ring
      rw [heq, hL₀def]
      show Complex.exp ((Real.log ρ : ℂ) + 2 * π * I * (t : ℂ)) = _
      rw [Complex.exp_add]
      congr 1
      rw [← Complex.ofReal_exp, Real.exp_log hρpos]
    have hkey := lift_change_eq_of_lifts hLcont hL₀cont hLe hL₀eq
    rw [hkey]
    show L₀ 1 - L₀ 0 = 2 * π * I
    rw [hL₀def]
    push_cast
    ring
  have hlocf := qcl_r_transport_conformal (k := id) (A := f) (z₀ := w₀) (r₀ := (1:ℝ)) one_pos
    continuous_id.continuousOn (fun z _ hzne => hzne) hloc_id hU hw₀ hf hf'
  obtain ⟨ρ_A, hρ_Apos, hloc_f⟩ := hlocf
  obtain ⟨ρ_k, hρ_kpos, hloc_k⟩ := hloc
  obtain ⟨ε_U, hε_Upos, hε_Uball⟩ := Metric.isOpen_iff.1 hU w₀ hw₀
  set r : ℝ := min (r₀ / 2) (ρ_k / 2) with hrdef
  have hrpos : 0 < r := lt_min (by linarith) (by linarith)
  have hrltr₀ : r < r₀ := (min_le_left _ _).trans_lt (by linarith)
  have hrltρk : r < ρ_k := (min_le_right _ _).trans_lt (by linarith)
  have hrsub : closedBall z₀ r ⊆ ball z₀ r₀ := closedBall_subset_ball hrltr₀
  have hfcontw0 : ContinuousAt f w₀ := (hf.differentiableAt (hU.mem_nhds hw₀)).continuousAt
  obtain ⟨δ, hδpos, hδball⟩ := Metric.continuousAt_iff.1 hfcontw0 r hrpos
  have hloc_k' : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (L t) = k (z₀ + ρ * Complex.exp (2 * π * I * t)) - k z₀) →
      L 1 - L 0 = 2 * π * I :=
    fun ρ hρpos hρle => hloc_k ρ hρpos (hρle.trans_lt hrltρk)
  refine ⟨min ρ_A (min δ (min ε_U r)), lt_min hρ_Apos (lt_min hδpos (lt_min hε_Upos hrpos)), ?_⟩
  intro ρ hρpos hρlt L hLcont hLe
  have hρA : ρ < ρ_A := hρlt.trans_le (min_le_left _ _)
  have hρδ : ρ < δ := hρlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hρεU : ρ < ε_U := hρlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hρr : ρ < r := hρlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  set α : ℝ → ℂ := fun t => f (w₀ + ρ * Complex.exp (2 * π * I * t)) with hαdef
  have hcircledist : ∀ t : ℝ, dist (w₀ + ρ * Complex.exp (2 * π * I * (t : ℂ))) w₀ = ρ := by
    intro t
    rw [dist_eq_norm]
    have heq : w₀ + (ρ : ℂ) * Complex.exp (2 * π * I * (t : ℂ)) - w₀ =
        (ρ : ℂ) * Complex.exp (2 * π * I * (t : ℂ)) := by ring
    rw [heq, norm_mul, henorm t, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos]
  have hcircleinU : ∀ t : ℝ, w₀ + ρ * Complex.exp (2 * π * I * (t : ℂ)) ∈ U := by
    intro t
    apply hε_Uball
    rw [Metric.mem_ball, hcircledist t]
    exact hρεU
  have hαinball : ∀ t : ℝ, α t ∈ closedBall z₀ r := by
    intro t
    have hlt : dist (f (w₀ + ρ * Complex.exp (2 * π * I * (t : ℂ)))) (f w₀) < r :=
      hδball (by rw [hcircledist t]; exact hρδ)
    rw [hz₀] at hlt
    exact mem_closedBall.2 hlt.le
  have hcircleNew0 : ∀ t : ℝ, w₀ + ρ * Complex.exp (2 * π * I * (t : ℂ)) ≠ w₀ := by
    intro t heq
    have h0 : dist (w₀ + ρ * Complex.exp (2 * π * I * (t : ℂ))) w₀ = 0 := by
      rw [heq]; exact dist_self w₀
    rw [hcircledist t] at h0
    linarith [hρpos]
  have hαNez0 : ∀ t : ℝ, α t ≠ z₀ := by
    intro t heq
    have hfeq : α t = f w₀ := by rw [heq, hz₀]
    exact hcircleNew0 t (hfi (hcircleinU t) hw₀ hfeq)
  have hαperloop : α 1 = α 0 := by
    have hper0 : Complex.exp (2 * π * I * (0 : ℂ)) = Complex.exp (2 * π * I * (1 : ℂ)) := by
      have h1 : (2 * π * I * (0 : ℂ)) = 0 := by ring
      have h2 : (2 * π * I * (1 : ℂ)) = 2 * π * I := by ring
      rw [h1, h2, Complex.exp_zero, Complex.exp_two_pi_mul_I]
    show f (w₀ + ρ * Complex.exp (2 * π * I * (1 : ℂ))) =
      f (w₀ + ρ * Complex.exp (2 * π * I * (0 : ℂ)))
    rw [hper0]
  have hαcont : ContinuousOn α (Icc (0 : ℝ) 1) := by
    have hcirccont : Continuous fun t : ℝ => w₀ + (ρ : ℂ) * Complex.exp (2 * π * I * (t : ℂ)) := by
      fun_prop
    exact hf.continuousOn.comp hcirccont.continuousOn (fun t _ => hcircleinU t)
  obtain ⟨L_f, hL_fcont, hL_feq⟩ :=
    exists_continuousOn_log_lift (γ := α) (w := z₀) hαcont (fun t _ => hαNez0 t)
  have hL_fdiff : L_f 1 - L_f 0 = 2 * π * I := by
    have hL_feq' : ∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (L_f t) = f (w₀ + ρ * Complex.exp (2 * π * I * t)) - f w₀ := by
      intro t ht; rw [hL_feq t ht, hz₀]
    exact hloc_f ρ hρpos hρA L_f hL_fcont hL_feq'
  have hVopen : IsOpen (ball z₀ r₀) := isOpen_ball
  have hLe' : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L t) = k (α t) - k z₀ := by
    intro t ht
    rw [hLe t ht, hz₀]
  exact qcl_w_lift_change_eq_of_injOn hVopen hrpos hrsub hkcont hki hloc_k'
    hαcont hαperloop (fun t _ => hαinball t) (fun t _ => hαNez0 t) hL_fcont hLcont hL_feq hLe'
    hL_fdiff

/-- **R2.** A self-homeomorphism of `ℍ` (with extension, NOT assumed to fix `∞`) with local
winding `+1` at some point preserves boundary cyclic order. -/
theorem qcl_r_cyclicStrictMono_of_hloc {g : ℂ → ℂ} {G : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension g upperHalf upperHalf G) (hgs : g '' upperHalf = upperHalf)
    {z₀ : ℂ} (hz₀ : z₀ ∈ upperHalf)
    (hloc : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (L t) = g (z₀ + ρ * Complex.exp (2 * π * I * t)) - g z₀) →
      L 1 - L 0 = 2 * π * I) :
    ∀ x : Fin 4 → ℝ, CyclicStrictMono x → ∀ y : Fin 4 → ℝ,
      (∀ i, G (((x i : ℝ) : ℂ) : ExtPlane) = (((y i : ℝ) : ℂ) : ExtPlane)) →
        CyclicStrictMono y := by
  by_cases hinf : G extInf = extInf
  · intro x hx y hy
    exact cyclicOrder_preserved_of_isHomeoExtension_of_fixes_infty hG hgs hinf hz₀ hloc x hx y hy
  · have hGfr : G '' frontier (toExt upperHalf) = frontier (toExt upperHalf) :=
      IsHomeoExtension.image_frontier scExt_isOpen_upperHalf scExt_isOpen_upperHalf hgs hG
    have hinfmem : extInf ∈ frontier (toExt upperHalf) := by
      rw [scExt_frontier_toExt_upperHalf]; exact Or.inr rfl
    have hGinfmem : G extInf ∈ frontier (toExt upperHalf) := hGfr ▸ mem_image_of_mem G hinfmem
    rw [scExt_frontier_toExt_upperHalf] at hGinfmem
    obtain ⟨r, hr⟩ : ∃ r : ℝ, G extInf = (((r : ℝ) : ℂ) : ExtPlane) := by
      rcases hGinfmem with h | h
      · obtain ⟨z, hz, hzeq⟩ := h
        exact ⟨z.re, by rw [← hzeq]; congr 1; exact Complex.ext_iff.2 ⟨rfl, hz⟩⟩
      · exact absurd h hinf
    have hdetM : (0 : ℝ) * (-r) - (-1) * (1 : ℝ) = 1 := by ring
    have hdetMpos : (0 : ℝ) < (0 : ℝ) * (-r) - (-1) * (1 : ℝ) := by rw [hdetM]; norm_num
    have hdetMC : ((0 : ℝ) : ℂ) * ((-r : ℝ) : ℂ) - ((-1 : ℝ) : ℂ) * ((1 : ℝ) : ℂ) ≠ 0 := by
      have h0 : ((0 : ℝ) * (-r) - (-1) * (1 : ℝ) : ℝ) ≠ 0 := hdetMpos.ne'
      exact_mod_cast h0
    set M : ℂ → ℂ := mobiusFn ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((-r : ℝ) : ℂ) with hMdef
    set E : ExtPlane ≃ₜ ExtPlane :=
      mobiusHomeomorph ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((-r : ℝ) : ℂ) hdetMC with hEdef
    have hEapp : ∀ w : ExtPlane, E w = mobiusExt ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ)
        ((-r : ℝ) : ℂ) w := fun w => rfl
    have hMconf : IsConformalOnto M upperHalf upperHalf := isConformalOnto_mobius_upperHalf hdetMpos
    have hEmaps : ∀ w ∈ upperHalf, E (w : ExtPlane) = ((M w : ℂ) : ExtPlane) := fun w hw => by
      rw [hEapp]
      exact mobiusExt_coe (mobiusFn_den_ne_zero_real hdetMpos.ne' hw)
    have hEimg : E '' toExt upperHalf = toExt upperHalf := mobiusExt_image_toExt_upperHalf hdetMpos
    have hgmaps : MapsTo g upperHalf upperHalf := fun z hz => hgs ▸ mem_image_of_mem g hz
    have hMgext : IsHomeoExtension (M ∘ g) upperHalf upperHalf (E ∘ G) :=
      IsHomeoExtension.comp_homeomorph hG hgmaps E hEmaps hEimg
    have hMgs : (M ∘ g) '' upperHalf = upperHalf := by
      rw [image_comp, hgs, hMconf.2.2]
    have hEGinf : (E ∘ G) extInf = extInf := by
      show E (G extInf) = extInf
      rw [hr, hEapp]
      have hden0 : (1 : ℂ) * ((r : ℝ) : ℂ) + ((-r : ℝ) : ℂ) = 0 := by push_cast; ring
      exact mobiusExt_coe_of_eq_zero hden0
    have hgz0mem : g z₀ ∈ upperHalf := hgmaps hz₀
    have hgz0ner : g z₀ ≠ ((r : ℝ) : ℂ) := by
      intro h
      have him : (g z₀).im = 0 := by rw [h]; simp
      have hpos : 0 < (g z₀).im := hgz0mem
      linarith
    have hden : ((1:ℝ) : ℂ) * g z₀ + ((-r : ℝ) : ℂ) ≠ 0 := by
      intro h
      apply hgz0ner
      push_cast at h
      linear_combination h
    have hMderivne : deriv M (g z₀) ≠ 0 := by
      rw [hMdef,
        (hasDerivAt_mobiusFn (a := ((0 : ℝ) : ℂ)) (b := ((-1 : ℝ) : ℂ)) hden).deriv]
      exact div_ne_zero hdetMC (pow_ne_zero 2 hden)
    -- Derive `hloc'` for `M ∘ g` at `z₀` from `hloc` (for `g`) via W1 applied to `M`.
    have hMopen : IsOpen {w : ℂ | (1 : ℂ) * w + ((-r : ℝ) : ℂ) ≠ 0} := by
      have heq : {w : ℂ | (1 : ℂ) * w + ((-r : ℝ) : ℂ) ≠ 0} =
          (fun w : ℂ => (1 : ℂ) * w + ((-r : ℝ) : ℂ)) ⁻¹' {(0 : ℂ)}ᶜ :=
        rfl
      rw [heq]
      exact ((continuous_const.mul continuous_id).add continuous_const).isOpen_preimage _
        isClosed_singleton.isOpen_compl
    have hgz0memU : g z₀ ∈ {w : ℂ | (1 : ℂ) * w + ((-r : ℝ) : ℂ) ≠ 0} := hden
    have hMdiffOn : DifferentiableOn ℂ M {w : ℂ | (1 : ℂ) * w + ((-r : ℝ) : ℂ) ≠ 0} := by
      intro w hw
      exact ((hasDerivAt_mobiusFn (a := ((0 : ℝ) : ℂ)) (b := ((-1 : ℝ) : ℂ))
        hw).differentiableAt).differentiableWithinAt
    have hgc : ContinuousOn g upperHalf := by
      rw [OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_iff]
      exact (hG.2.1.comp OnePoint.continuous_coe.continuousOn
        (fun z hz => subset_closure (mem_image_of_mem _ hz))).congr
        (fun z hz => (hG.1 z hz).symm)
    have hgi : InjOn g upperHalf := by
      intro a ha b hb hab
      have h1 : G (a : ExtPlane) = G (b : ExtPlane) := by rw [hG.1 a ha, hG.1 b hb, hab]
      have h2 := hG.2.2.1 (subset_closure (mem_image_of_mem _ ha))
        (subset_closure (mem_image_of_mem _ hb)) h1
      exact OnePoint.coe_injective h2
    obtain ⟨ε, hεpos, hεball⟩ := Metric.isOpen_iff.1 scExt_isOpen_upperHalf z₀ hz₀
    have hloc' := qcl_r_transport_conformal hεpos (hgc.mono hεball)
      (fun z hz hzne heq => hzne (hgi (hεball hz) hz₀ heq)) hloc hMopen hgz0memU hMdiffOn hMderivne
    have hW5core :=
      cyclicOrder_preserved_of_isHomeoExtension_of_fixes_infty hMgext hMgs hEGinf hz₀ hloc'
    intro x hx y hy
    have hxi_mem : ∀ i, (((x i : ℝ) : ℂ) : ExtPlane) ∈ closure (toExt upperHalf) := by
      intro i
      apply frontier_subset_closure
      rw [scExt_frontier_toExt_upperHalf]
      exact Or.inl ⟨(x i : ℝ), rfl, rfl⟩
    have hinfclos : extInf ∈ closure (toExt upperHalf) := frontier_subset_closure hinfmem
    have hyner : ∀ i, y i ≠ r := by
      intro i heq
      have h1 : G (((x i : ℝ) : ℂ) : ExtPlane) = G extInf := by rw [hy i, heq, hr]
      have h2 := hG.2.2.1 (hxi_mem i) hinfclos h1
      exact OnePoint.coe_ne_infty _ h2
    set y' : Fin 4 → ℝ := fun i => -1 / (y i - r) with hy'def
    have hEGvert : ∀ i, (E ∘ G) (((x i : ℝ) : ℂ) : ExtPlane) = (((y' i : ℝ) : ℂ) : ExtPlane) := by
      intro i
      show E (G (((x i : ℝ) : ℂ) : ExtPlane)) = _
      rw [hy i, hEapp]
      have hden2 : ((1:ℝ) : ℂ) * ((y i : ℝ) : ℂ) + ((-r : ℝ) : ℂ) ≠ 0 := by
        have hne : (y i - r : ℝ) ≠ 0 := sub_ne_zero.2 (hyner i)
        intro h
        apply hne
        have h' : ((y i - r : ℝ) : ℂ) = 0 := by push_cast at h ⊢; linear_combination h
        exact_mod_cast h'
      rw [mobiusExt_coe hden2]
      congr 1
      show mobiusFn ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((-r : ℝ) : ℂ) ((y i : ℝ) : ℂ) =
        (((y' i : ℝ)) : ℂ)
      rw [mobiusFn, hy'def]
      simp only
      push_cast
      congr 1 <;> ring
    have hy'cyc : CyclicStrictMono y' := hW5core x hx y' hEGvert
    have hdetInv : (0 : ℝ) < r * 0 - (-1) * 1 := by norm_num
    have hy'ne0 : ∀ i, y' i ≠ 0 := by
      intro i h
      rw [hy'def] at h
      simp only [neg_div, neg_eq_zero, div_eq_zero_iff] at h
      rcases h with h | h
      · norm_num at h
      · exact hyner i (sub_eq_zero.mp h)
    have hMinv : ∀ i, mobiusExt ((r : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((0 : ℝ) : ℂ)
        (((y' i : ℝ) : ℂ) : ExtPlane) = (((y i : ℝ) : ℂ) : ExtPlane) := by
      intro i
      have hden3 : ((1:ℝ) : ℂ) * ((y' i : ℝ) : ℂ) + ((0 : ℝ) : ℂ) ≠ 0 := by
        push_cast
        simpa using hy'ne0 i
      rw [mobiusExt_coe hden3]
      congr 1
      show mobiusFn ((r : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((0 : ℝ) : ℂ) ((y' i : ℝ) : ℂ) =
        ((y i : ℝ) : ℂ)
      rw [mobiusFn, hy'def]
      simp only
      have hne : (y i - r : ℝ) ≠ 0 := sub_ne_zero.2 (hyner i)
      have hneC : ((y i : ℝ) : ℂ) - ((r : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast sub_ne_zero.2 (hyner i)
      push_cast
      field_simp
      ring
    exact automorphism_upperHalf_preserves_cyclicOrder hdetInv y' hy'cyc y hMinv

/-- **R1.** A `K`-q.c. map has local winding `+1` at every point of its domain. -/
theorem qcl_r_hloc_of_isKQC {h : ℂ → ℂ} {U : Set ℂ} {K : ℝ} (hh : IsKQC h U K) {p : ℂ}
    (hp : p ∈ U) :
    ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (L t) = h (p + ρ * Complex.exp (2 * π * I * t)) - h p) →
      L 1 - L 0 = 2 * π * I := by
  obtain ⟨S, hpS, hSU⟩ := exists_topQuad_mem_closure_subset hh.1 hp
  obtain ⟨S', hS', -⟩ := hh.2.2.2 S hSU
  obtain ⟨hJ, hv, φ, Φ, x, hφ, hΦ, hx, hΦv⟩ := S.isTopQuad
  obtain ⟨hJ', hv', φ', Φ', x', hφ', hΦ', hx', hΦ'v⟩ := S'.isTopQuad
  have hSdomopen : IsOpen S.dom := hJ.1
  have hSdomU : S.dom ⊆ U := fun z hz => by
    have hzt := hSU (subset_closure (mem_image_of_mem _ hz))
    exact coe_mem_toExt_iff.mp hzt
  have hhcont : ContinuousOn h U := hh.2.2.1.1
  have hhinj : InjOn h U := hh.2.2.1.2.1
  have hfo : IsOpen (h '' S.dom) :=
    isOpen_image_of_continuousOn_injOn_of_subset hh.1 hhcont hhinj hSdomU hSdomopen
  obtain ⟨-, hext, -⟩ := image_isJordanDomain_of_open hh.1 hhcont hhinj hSU hfo
  have hext' : IsHomeoExtension h S.dom S'.dom (OnePoint.map h) := by
    rw [hS'.1]; exact hext
  set ψ : ℂ → ℂ := Function.invFunOn φ S.dom with hψdef
  set Ψ : ExtPlane → ExtPlane := Function.invFunOn Φ (closure (toExt S.dom)) with hΨdef
  have hφsymm : IsConformalOnto ψ upperHalf S.dom := hφ.symm hSdomopen
  have hφinvimg : ψ '' upperHalf = S.dom := hφsymm.2.2
  have hφinvext : IsHomeoExtension ψ upperHalf S.dom Ψ := isHomeoExtension_invFunOn hφ hΦ
  have hφinvmaps : MapsTo ψ upperHalf S.dom := by
    intro w hw; rw [← hφinvimg]; exact mem_image_of_mem _ hw
  have hstep1 : IsHomeoExtension (h ∘ ψ) upperHalf S'.dom (OnePoint.map h ∘ Ψ) :=
    IsHomeoExtension.comp hext' hφinvext hφinvmaps
  have hstep1img : (h ∘ ψ) '' upperHalf = S'.dom := by
    rw [Set.image_comp, hφinvimg, ← hS'.1]
  have hstep1maps : MapsTo (h ∘ ψ) upperHalf S'.dom := by
    intro w hw; rw [← hstep1img]; exact mem_image_of_mem _ hw
  have hstep2 : IsHomeoExtension (φ' ∘ (h ∘ ψ)) upperHalf upperHalf (Φ' ∘ (OnePoint.map h ∘ Ψ)) :=
    IsHomeoExtension.comp hΦ' hstep1 hstep1maps
  set κ : ℂ → ℂ := φ' ∘ (h ∘ ψ) with hκdef
  set Kext : ExtPlane → ExtPlane := Φ' ∘ (OnePoint.map h ∘ Ψ) with hKextdef
  have hKextext : IsHomeoExtension κ upperHalf upperHalf Kext := hstep2
  have hκimg : κ '' upperHalf = upperHalf := by
    rw [hκdef, Set.image_comp, hstep1img]
    exact hφ'.2.2
  have hΦinvcancel : ∀ i, Ψ (((x i : ℝ) : ℂ) : ExtPlane) = S.vert i := by
    intro i
    have hmem : S.vert i ∈ closure (toExt S.dom) := frontier_subset_closure (hv i)
    have h1 := hΦ.2.2.1.leftInvOn_invFunOn hmem
    rwa [hΦv i] at h1
  have hKextv : ∀ i, Kext (((x i : ℝ) : ℂ) : ExtPlane) = (((x' i : ℝ) : ℂ) : ExtPlane) := by
    intro i
    show Φ' (OnePoint.map h (Ψ (((x i : ℝ) : ℂ) : ExtPlane))) = _
    rw [hΦinvcancel i, ← hS'.2 i]
    exact hΦ'v i
  have hz₀mem : φ p ∈ upperHalf := hφ.2.2 ▸ mem_image_of_mem φ hpS
  have hlocκ : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (L t) = κ (φ p + ρ * Complex.exp (2 * π * I * t)) - κ (φ p)) →
      L 1 - L 0 = 2 * π * I := by
    by_cases hinf : Kext extInf = extInf
    · have hKextfr : Kext '' frontier (toExt upperHalf) = frontier (toExt upperHalf) :=
        IsHomeoExtension.image_frontier scExt_isOpen_upperHalf scExt_isOpen_upperHalf hκimg
          hKextext
      have hKextc : ContinuousOn Kext (frontier (toExt upperHalf)) :=
        hKextext.2.1.mono frontier_subset_closure
      have hKexti : InjOn Kext (frontier (toExt upperHalf)) :=
        hKextext.2.2.1.mono frontier_subset_closure
      obtain ⟨f, hfcont, hfinj, hfmono, hf⟩ :=
        qcl_w_strictMono_of_cyclic hKextc hKexti hKextfr hinf hx hx' hKextv
      exact qcl_w_hloc_of_strictMono_boundary hKextext hκimg hinf hz₀mem f hfcont hfinj hf hfmono
    · have hKextfr : Kext '' frontier (toExt upperHalf) = frontier (toExt upperHalf) :=
        IsHomeoExtension.image_frontier scExt_isOpen_upperHalf scExt_isOpen_upperHalf hκimg
          hKextext
      have hinfmem : extInf ∈ frontier (toExt upperHalf) := by
        rw [scExt_frontier_toExt_upperHalf]; exact Or.inr rfl
      have hKextinfmem : Kext extInf ∈ frontier (toExt upperHalf) :=
        hKextfr ▸ mem_image_of_mem Kext hinfmem
      rw [scExt_frontier_toExt_upperHalf] at hKextinfmem
      obtain ⟨r, hr⟩ : ∃ r : ℝ, Kext extInf = (((r : ℝ) : ℂ) : ExtPlane) := by
        rcases hKextinfmem with hh1 | hh1
        · obtain ⟨z, hz, hzeq⟩ := hh1
          exact ⟨z.re, by rw [← hzeq]; congr 1; exact Complex.ext_iff.2 ⟨rfl, hz⟩⟩
        · exact absurd hh1 hinf
      have hdetM : (0 : ℝ) * (-r) - (-1) * (1 : ℝ) = 1 := by ring
      have hdetMpos : (0 : ℝ) < (0 : ℝ) * (-r) - (-1) * (1 : ℝ) := by rw [hdetM]; norm_num
      have hdetMC : ((0 : ℝ) : ℂ) * ((-r : ℝ) : ℂ) - ((-1 : ℝ) : ℂ) * ((1 : ℝ) : ℂ) ≠ 0 := by
        have h0 : ((0 : ℝ) * (-r) - (-1) * (1 : ℝ) : ℝ) ≠ 0 := hdetMpos.ne'
        exact_mod_cast h0
      set M : ℂ → ℂ := mobiusFn ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((-r : ℝ) : ℂ)
        with hMdef
      set E : ExtPlane ≃ₜ ExtPlane :=
        mobiusHomeomorph ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((-r : ℝ) : ℂ) hdetMC with hEdef
      have hEapp : ∀ w : ExtPlane, E w = mobiusExt ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ)
          ((-r : ℝ) : ℂ) w := fun w => rfl
      have hMconf : IsConformalOnto M upperHalf upperHalf :=
        isConformalOnto_mobius_upperHalf hdetMpos
      have hEmaps : ∀ w ∈ upperHalf, E (w : ExtPlane) = ((M w : ℂ) : ExtPlane) := fun w hw => by
        rw [hEapp]
        exact mobiusExt_coe (mobiusFn_den_ne_zero_real hdetMpos.ne' hw)
      have hEimg : E '' toExt upperHalf = toExt upperHalf := mobiusExt_image_toExt_upperHalf hdetMpos
      have hκmaps : MapsTo κ upperHalf upperHalf := by
        intro w hw; rw [← hκimg]; exact mem_image_of_mem _ hw
      have hMKextext : IsHomeoExtension (M ∘ κ) upperHalf upperHalf (E ∘ Kext) :=
        IsHomeoExtension.comp_homeomorph hKextext hκmaps E hEmaps hEimg
      have hMKexts : (M ∘ κ) '' upperHalf = upperHalf := by
        rw [image_comp, hκimg, hMconf.2.2]
      have hEKextinf : (E ∘ Kext) extInf = extInf := by
        show E (Kext extInf) = extInf
        rw [hr, hEapp]
        have hden0 : (1 : ℂ) * ((r : ℝ) : ℂ) + ((-r : ℝ) : ℂ) = 0 := by push_cast; ring
        exact mobiusExt_coe_of_eq_zero hden0
      have hxi_mem : ∀ i, (((x i : ℝ) : ℂ) : ExtPlane) ∈ closure (toExt upperHalf) := by
        intro i
        apply frontier_subset_closure
        rw [scExt_frontier_toExt_upperHalf]
        exact Or.inl ⟨(x i : ℝ), rfl, rfl⟩
      have hinfclos : extInf ∈ closure (toExt upperHalf) := frontier_subset_closure hinfmem
      have hx'ner : ∀ i, x' i ≠ r := by
        intro i heq
        have h1 : Kext (((x i : ℝ) : ℂ) : ExtPlane) = Kext extInf := by rw [hKextv i, heq, hr]
        have h2 := hKextext.2.2.1 (hxi_mem i) hinfclos h1
        exact OnePoint.coe_ne_infty _ h2
      set y' : Fin 4 → ℝ := fun i => -1 / (x' i - r) with hy'def
      have hMx'eq : ∀ i, mobiusExt ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((-r : ℝ) : ℂ)
          (((x' i : ℝ) : ℂ) : ExtPlane) = (((y' i : ℝ) : ℂ) : ExtPlane) := by
        intro i
        have hden2 : ((1 : ℝ) : ℂ) * ((x' i : ℝ) : ℂ) + ((-r : ℝ) : ℂ) ≠ 0 := by
          have hne : (x' i - r : ℝ) ≠ 0 := sub_ne_zero.2 (hx'ner i)
          intro hh
          apply hne
          have h' : ((x' i - r : ℝ) : ℂ) = 0 := by push_cast at hh ⊢; linear_combination hh
          exact_mod_cast h'
        rw [mobiusExt_coe hden2]
        congr 1
        show mobiusFn ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((-r : ℝ) : ℂ) ((x' i : ℝ) : ℂ) =
          (((y' i : ℝ)) : ℂ)
        rw [mobiusFn, hy'def]
        simp only
        push_cast
        congr 1 <;> ring
      have hEKextv : ∀ i, (E ∘ Kext) (((x i : ℝ) : ℂ) : ExtPlane) = (((y' i : ℝ) : ℂ) : ExtPlane) := by
        intro i
        show E (Kext (((x i : ℝ) : ℂ) : ExtPlane)) = _
        rw [hKextv i, hEapp]
        exact hMx'eq i
      have hy'cyc : CyclicStrictMono y' :=
        automorphism_upperHalf_preserves_cyclicOrder hdetMpos x' hx' y' hMx'eq
      have hEKextfr : (E ∘ Kext) '' frontier (toExt upperHalf) = frontier (toExt upperHalf) :=
        IsHomeoExtension.image_frontier scExt_isOpen_upperHalf scExt_isOpen_upperHalf hMKexts
          hMKextext
      have hEKextc : ContinuousOn (E ∘ Kext) (frontier (toExt upperHalf)) :=
        hMKextext.2.1.mono frontier_subset_closure
      have hEKexti : InjOn (E ∘ Kext) (frontier (toExt upperHalf)) :=
        hMKextext.2.2.1.mono frontier_subset_closure
      obtain ⟨f, hfcont, hfinj, hfmono, hf⟩ :=
        qcl_w_strictMono_of_cyclic hEKextc hEKexti hEKextfr hEKextinf hx hy'cyc hEKextv
      obtain ⟨ρ₁, hρ₁pos, hlocMκ⟩ :=
        qcl_w_hloc_of_strictMono_boundary hMKextext hMKexts hEKextinf hz₀mem f hfcont hfinj hf
          hfmono
      -- Transport `hlocMκ` (local winding of `M ∘ κ`) back to `κ` via the explicit inverse
      -- Möbius map `Minv := mobiusFn r (-1) 1 0`, using `qcl_r_transport_conformal`.
      set Minv : ℂ → ℂ := mobiusFn ((r : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((0 : ℝ) : ℂ)
        with hMinvdef
      have hκz0ner : κ (φ p) ≠ ((r : ℝ) : ℂ) := by
        intro heq
        have him : (κ (φ p)).im = 0 := by rw [heq]; simp
        have hpos : 0 < (κ (φ p)).im := hκmaps hz₀mem
        linarith
      have hMw : ∀ w : ℂ, w ≠ ((r : ℝ) : ℂ) → M w = -1 / (w - ((r : ℝ) : ℂ)) := by
        intro w hw
        rw [hMdef, mobiusFn]
        congr 1 <;> push_cast <;> ring
      have hMwne0 : ∀ w : ℂ, w ≠ ((r : ℝ) : ℂ) → M w ≠ 0 := by
        intro w hw
        rw [hMw w hw]
        exact div_ne_zero (by norm_num) (sub_ne_zero.2 hw)
      have hMinvMcancel : ∀ w : ℂ, w ≠ ((r : ℝ) : ℂ) → Minv (M w) = w := by
        intro w hw
        have hwrne : w - ((r : ℝ) : ℂ) ≠ 0 := sub_ne_zero.2 hw
        rw [hMw w hw, hMinvdef, mobiusFn]
        field_simp
        push_cast
        ring
      have hMκcont : ContinuousOn (M ∘ κ) upperHalf := by
        rw [OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_iff]
        have h1 : ContinuousOn (fun z : ℂ => (E ∘ Kext) (z : ExtPlane)) upperHalf :=
          hMKextext.2.1.comp OnePoint.continuous_coe.continuousOn
            (fun z hz => subset_closure (mem_image_of_mem _ hz))
        exact h1.congr fun z hz => (hMKextext.1 z hz).symm
      have hMκinj : InjOn (M ∘ κ) upperHalf := by
        intro a ha b hb hab
        have ea : (E ∘ Kext) (a : ExtPlane) = ((M ∘ κ) a : ℂ) := hMKextext.1 a ha
        have eb : (E ∘ Kext) (b : ExtPlane) = ((M ∘ κ) b : ℂ) := hMKextext.1 b hb
        have h1 : (E ∘ Kext) (a : ExtPlane) = (E ∘ Kext) (b : ExtPlane) := by rw [ea, eb, hab]
        have h2 := hMKextext.2.2.1 (subset_closure (mem_image_of_mem _ ha))
          (subset_closure (mem_image_of_mem _ hb)) h1
        exact OnePoint.coe_injective h2
      obtain ⟨ε, hεpos, hεball⟩ := Metric.isOpen_iff.1 scExt_isOpen_upperHalf (φ p) hz₀mem
      have hMinvopen : IsOpen {w : ℂ | w ≠ (0 : ℂ)} := isOpen_ne
      have hMinvdiffOn : DifferentiableOn ℂ Minv {w : ℂ | w ≠ (0 : ℂ)} := by
        intro w hw
        have hw' : (1 : ℂ) * w + ((0 : ℝ) : ℂ) ≠ 0 := by simpa using hw
        exact (hasDerivAt_mobiusFn (a := ((r : ℝ) : ℂ)) (b := ((-1 : ℝ) : ℂ))
          hw').differentiableAt.differentiableWithinAt
      have hMκz0memU : (M ∘ κ) (φ p) ∈ {w : ℂ | w ≠ (0 : ℂ)} :=
        hMwne0 (κ (φ p)) hκz0ner
      have hMderivneat : deriv Minv ((M ∘ κ) (φ p)) ≠ 0 := by
        show deriv Minv (M (κ (φ p))) ≠ 0
        have hw' : ((1:ℝ) : ℂ) * (M (κ (φ p))) + ((0 : ℝ) : ℂ) ≠ 0 := by
          have := hMwne0 (κ (φ p)) hκz0ner
          simpa using this
        have hdetMinvC : ((r:ℝ):ℂ) * ((0:ℝ):ℂ) - ((-1:ℝ):ℂ) * ((1:ℝ):ℂ) ≠ 0 := by
          have : ((r:ℝ)*(0:ℝ) - (-1)*(1:ℝ) : ℝ) ≠ 0 := by norm_num
          exact_mod_cast this
        rw [hMinvdef, (hasDerivAt_mobiusFn (a := ((r:ℝ):ℂ)) (b := ((-1:ℝ):ℂ))
          (c := ((1:ℝ):ℂ)) (d := ((0:ℝ):ℂ)) hw').deriv]
        exact div_ne_zero hdetMinvC (pow_ne_zero 2 hw')
      have hlocMinvMκ := qcl_r_transport_conformal hεpos (hMκcont.mono hεball)
        (fun z hz hzne heqv => hzne (hMκinj (hεball hz) hz₀mem heqv)) ⟨ρ₁, hρ₁pos, hlocMκ⟩
        hMinvopen hMκz0memU hMinvdiffOn hMderivneat
      obtain ⟨ρ₁', hρ₁'pos, hlocMinvMκ'⟩ := hlocMinvMκ
      have henorm : ∀ t : ℝ, ‖Complex.exp (2 * π * I * (t : ℂ))‖ = 1 := by
        intro t
        rw [Complex.norm_exp]
        have h0 : (2 * π * I * (t : ℂ)).re = 0 := by simp
        rw [h0, Real.exp_zero]
      refine ⟨min ρ₁' ε, lt_min hρ₁'pos hεpos, ?_⟩
      intro ρ hρpos hρlt L hLcont hLe
      have hρρ1' : ρ < ρ₁' := hρlt.trans_le (min_le_left _ _)
      have hρε : ρ < ε := hρlt.trans_le (min_le_right _ _)
      apply hlocMinvMκ' ρ hρpos hρρ1' L hLcont
      intro t ht
      have hcircUH : φ p + ρ * Complex.exp (2 * π * I * (t : ℂ)) ∈ upperHalf := by
        apply hεball
        rw [Metric.mem_ball, dist_eq_norm]
        have heq : φ p + (ρ : ℂ) * Complex.exp (2 * π * I * (t : ℂ)) - φ p =
            (ρ : ℂ) * Complex.exp (2 * π * I * (t : ℂ)) := by ring
        rw [heq, norm_mul, henorm t, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hρpos]
        exact hρε
      have hκcircNer : κ (φ p + ρ * Complex.exp (2 * π * I * (t : ℂ))) ≠ ((r : ℝ) : ℂ) := by
        intro heq
        have him : (κ (φ p + ρ * Complex.exp (2 * π * I * (t : ℂ)))).im = 0 := by
          rw [heq]; simp
        have hpos : 0 < (κ (φ p + ρ * Complex.exp (2 * π * I * (t : ℂ)))).im :=
          hκmaps hcircUH
        linarith
      rw [hLe t ht]
      simp only [Function.comp_apply]
      rw [hMinvMcancel _ hκcircNer, hMinvMcancel _ hκz0ner]
  -- Transport `hlocκ` (local winding of `κ` at `φ p`) back to `h` (local winding at `p`):
  -- post-compose with `ψ' := invFunOn φ' S'.dom` to get `K := ψ' ∘ κ`'s winding at `φ p`,
  -- then pre-compose with `φ` (via `qcl_r_transport_precompose`) to get `K ∘ φ`'s winding at
  -- `p`; finally `K ∘ φ = h` on `S.dom` (both cancellations of the canonical maps).
  have henorm : ∀ t : ℝ, ‖Complex.exp (2 * π * I * (t : ℂ))‖ = 1 := by
    intro t
    rw [Complex.norm_exp]
    have h0 : (2 * π * I * (t : ℂ)).re = 0 := by simp
    rw [h0, Real.exp_zero]
  have hκmaps : MapsTo κ upperHalf upperHalf := by
    intro w hw; rw [← hκimg]; exact mem_image_of_mem _ hw
  set ψ' : ℂ → ℂ := Function.invFunOn φ' S'.dom with hψ'def
  have hφ'symm : IsConformalOnto ψ' upperHalf S'.dom := hφ'.symm hJ'.1
  have hκcont : ContinuousOn κ upperHalf := by
    rw [OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_iff]
    exact (hKextext.2.1.comp OnePoint.continuous_coe.continuousOn
      (fun z hz => subset_closure (mem_image_of_mem _ hz))).congr
      (fun z hz => (hKextext.1 z hz).symm)
  have hκinj : InjOn κ upperHalf := by
    intro a ha b hb hab
    have h1 : Kext (a : ExtPlane) = Kext (b : ExtPlane) := by
      rw [hKextext.1 a ha, hKextext.1 b hb, hab]
    have h2 := hKextext.2.2.1 (subset_closure (mem_image_of_mem _ ha))
      (subset_closure (mem_image_of_mem _ hb)) h1
    exact OnePoint.coe_injective h2
  have hκφpmem : κ (φ p) ∈ upperHalf := hκmaps hz₀mem
  have hψ'deriv : deriv ψ' (κ (φ p)) ≠ 0 :=
    deriv_ne_zero_of_injOn scExt_isOpen_upperHalf hφ'symm.1 hφ'symm.2.1 hκφpmem
  obtain ⟨ε₂, hε₂pos, hε₂ball⟩ := Metric.isOpen_iff.1 scExt_isOpen_upperHalf (φ p) hz₀mem
  have hlocK := qcl_r_transport_conformal (k := κ) (A := ψ') (z₀ := φ p) (r₀ := ε₂) hε₂pos
    (hκcont.mono hε₂ball) (fun z hz hzne heq => hzne (hκinj (hε₂ball hz) hz₀mem heq)) hlocκ
    scExt_isOpen_upperHalf hκφpmem hφ'symm.1 hψ'deriv
  set K : ℂ → ℂ := ψ' ∘ κ with hKdef
  have hψφeq : ∀ w ∈ S.dom, ψ (φ w) = w := hφ.2.1.leftInvOn_invFunOn
  have hκφeq : ∀ w ∈ S.dom, κ (φ w) = φ' (h w) := by
    intro w hw
    show φ' (h (ψ (φ w))) = φ' (h w)
    rw [hψφeq w hw]
  have hhw'dom : ∀ w ∈ S.dom, h w ∈ S'.dom := by
    intro w hw
    rw [hS'.1]; exact mem_image_of_mem h hw
  have hψ'φ'eq : ∀ w ∈ S'.dom, ψ' (φ' w) = w := hφ'.2.1.leftInvOn_invFunOn
  have hKeq : ∀ w ∈ S.dom, K (φ w) = h w := by
    intro w hw
    show ψ' (κ (φ w)) = h w
    rw [hκφeq w hw]
    exact hψ'φ'eq (h w) (hhw'dom w hw)
  have hKφp : K (φ p) = h p := hKeq p hpS
  have hKcont : ContinuousOn K upperHalf := hφ'symm.1.continuousOn.comp hκcont hκmaps
  have hKinj : InjOn K upperHalf := by
    intro a ha b hb hab
    have h2 := hφ'symm.2.1 (hκmaps ha) (hκmaps hb) hab
    exact hκinj ha hb h2
  have hderivφp : deriv φ p ≠ 0 := deriv_ne_zero_of_injOn hSdomopen hφ.1 hφ.2.1 hpS
  have hloc_h := qcl_r_transport_precompose (k := K) (f := φ) (w₀ := p) (z₀ := φ p) rfl
    hSdomopen hpS hφ.1 hφ.2.1 hderivφp hε₂pos (hKcont.mono hε₂ball) (hKinj.mono hε₂ball) hlocK
  obtain ⟨ρ_h, hρ_hpos, hloc_h'⟩ := hloc_h
  obtain ⟨ε₃, hε₃pos, hε₃ball⟩ := Metric.isOpen_iff.1 hSdomopen p hpS
  refine ⟨min ρ_h ε₃, lt_min hρ_hpos hε₃pos, ?_⟩
  intro ρ hρpos hρlt L hLcont hLe
  have hρh : ρ < ρ_h := hρlt.trans_le (min_le_left _ _)
  have hρε3 : ρ < ε₃ := hρlt.trans_le (min_le_right _ _)
  apply hloc_h' ρ hρpos hρh L hLcont
  intro t ht
  rw [hLe t ht]
  have hcircS : p + ρ * Complex.exp (2 * π * I * (t : ℂ)) ∈ S.dom := by
    apply hε₃ball
    rw [Metric.mem_ball, dist_eq_norm]
    have heqn : p + (ρ : ℂ) * Complex.exp (2 * π * I * (t : ℂ)) - p =
        (ρ : ℂ) * Complex.exp (2 * π * I * (t : ℂ)) := by ring
    rw [heqn, norm_mul, henorm t, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos]
    exact hρε3
  rw [hKeq _ hcircS, hKφp]



/-- **RH** (extra, prefix `qcl_r_c_`): the winding of `k ∘ A ∘ (radius-σ circle around z₀) − k p`
does not depend on `σ ∈ (0, r]`, for `A` continuous mapping `closedBall z₀ r` into a set where
`k` is continuous and injective, `A z₀ = p`, and `A w ≠ p` whenever `w ≠ z₀`.  (Radial homotopy
interpolating the radius linearly; `lift_change_eq_of_homotopy`.) -/
theorem qcl_r_c_radial_winding_eq {A k : ℂ → ℂ} {z₀ p : ℂ} {r : ℝ} (hr : 0 < r)
    (hAp : A z₀ = p) (hAne : ∀ w ∈ closedBall z₀ r, w ≠ z₀ → A w ≠ p)
    (hAcont : ContinuousOn A (closedBall z₀ r))
    (hkcont : ContinuousOn k (A '' closedBall z₀ r))
    (hki : InjOn k (A '' closedBall z₀ r))
    {ρ1 ρ2 : ℝ} (hρ1 : ρ1 ∈ Ioc (0:ℝ) r) (hρ2 : ρ2 ∈ Ioc (0:ℝ) r)
    {L1 L2 : ℝ → ℂ} (hL1cont : ContinuousOn L1 (Icc 0 1)) (hL2cont : ContinuousOn L2 (Icc 0 1))
    (hL1e : ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (L1 t) =
      k (A (z₀ + ρ1 * Complex.exp (2 * π * I * t))) - k p)
    (hL2e : ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (L2 t) =
      k (A (z₀ + ρ2 * Complex.exp (2 * π * I * t))) - k p) :
    L1 1 - L1 0 = L2 1 - L2 0 := by
  have henorm : ∀ t : ℝ, ‖Complex.exp (2 * π * I * (t : ℂ))‖ = 1 := by
    intro t
    rw [Complex.norm_exp]
    have h0 : (2 * π * I * (t : ℂ)).re = 0 := by simp
    rw [h0, Real.exp_zero]
  set σ : ℝ → ℝ := fun s => (1 - s) * ρ1 + s * ρ2 with hσdef
  have hσge : ∀ s ∈ Icc (0:ℝ) 1, min ρ1 ρ2 ≤ σ s := by
    intro s hs
    rw [hσdef]
    have h1 : min ρ1 ρ2 * (1 - s) ≤ ρ1 * (1 - s) :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (by linarith [hs.2])
    have h2 : min ρ1 ρ2 * s ≤ ρ2 * s := mul_le_mul_of_nonneg_right (min_le_right _ _) hs.1
    nlinarith [h1, h2]
  have hσpos : ∀ s ∈ Icc (0:ℝ) 1, 0 < σ s := fun s hs =>
    lt_of_lt_of_le (lt_min hρ1.1 hρ2.1) (hσge s hs)
  have hσle : ∀ s ∈ Icc (0:ℝ) 1, σ s ≤ r := by
    intro s hs
    rw [hσdef]
    have h1 : (1 - s) * ρ1 ≤ (1 - s) * r :=
      mul_le_mul_of_nonneg_left hρ1.2 (by linarith [hs.2])
    have h2 : s * ρ2 ≤ s * r := mul_le_mul_of_nonneg_left hρ2.2 hs.1
    nlinarith [h1, h2]
  set H : ℝ → ℝ → ℂ := fun s t =>
    k (A (z₀ + (σ s : ℂ) * Complex.exp (2 * π * I * t))) - k p with hHdef
  have hcircledist : ∀ s ∈ Icc (0:ℝ) 1, ∀ t : ℝ,
      dist (z₀ + (σ s : ℂ) * Complex.exp (2 * π * I * (t : ℂ))) z₀ = σ s := by
    intro s hs t
    rw [dist_eq_norm]
    have heq : z₀ + (σ s : ℂ) * Complex.exp (2 * π * I * (t : ℂ)) - z₀ =
        (σ s : ℂ) * Complex.exp (2 * π * I * (t : ℂ)) := by ring
    rw [heq, norm_mul, henorm t, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hσpos s hs)]
  have hcircleinball : ∀ s ∈ Icc (0:ℝ) 1, ∀ t : ℝ,
      z₀ + (σ s : ℂ) * Complex.exp (2 * π * I * (t : ℂ)) ∈ closedBall z₀ r := by
    intro s hs t
    rw [mem_closedBall, hcircledist s hs t]
    exact hσle s hs
  have hcircleNez0 : ∀ s ∈ Icc (0:ℝ) 1, ∀ t : ℝ,
      z₀ + (σ s : ℂ) * Complex.exp (2 * π * I * (t : ℂ)) ≠ z₀ := by
    intro s hs t heq
    have h0 : dist (z₀ + (σ s : ℂ) * Complex.exp (2 * π * I * (t : ℂ))) z₀ = 0 := by
      rw [heq]; exact dist_self z₀
    rw [hcircledist s hs t] at h0
    linarith [hσpos s hs]
  have hHne : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, H s t ≠ 0 := by
    intro s hs t _ heq
    rw [hHdef] at heq
    have h1 : k (A (z₀ + (σ s : ℂ) * Complex.exp (2 * π * I * (t : ℂ)))) = k p := by
      linear_combination heq
    have h2 : A (z₀ + (σ s : ℂ) * Complex.exp (2 * π * I * (t : ℂ))) = p :=
      hki (mem_image_of_mem A (hcircleinball s hs t)) (hAp ▸ mem_image_of_mem A
        (mem_closedBall_self hr.le)) h1
    exact hAne _ (hcircleinball s hs t) (hcircleNez0 s hs t) h2
  have hcirccont : Continuous (Function.uncurry (fun s t : ℝ =>
      z₀ + (σ s : ℂ) * Complex.exp (2 * π * I * (t : ℂ)))) := by
    have : Continuous σ := by fun_prop
    fun_prop
  have hHcont : ContinuousOn (Function.uncurry H) (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := by
    have heq : Function.uncurry H = fun q : ℝ × ℝ =>
        k (A (z₀ + (σ q.1 : ℂ) * Complex.exp (2 * π * I * (q.2 : ℂ)))) - k p := by
      funext ⟨s, t⟩; rfl
    rw [heq]
    refine (hkcont.comp (hAcont.comp hcirccont.continuousOn ?_) ?_).sub continuousOn_const
    · intro q hq; exact hcircleinball q.1 hq.1 q.2
    · intro q hq; exact mem_image_of_mem A (hcircleinball q.1 hq.1 q.2)
  have hHper : ∀ s ∈ Icc (0:ℝ) 1, H s 1 = H s 0 := by
    intro s _
    have hper0 : Complex.exp (2 * π * I * (0 : ℂ)) = Complex.exp (2 * π * I * (1 : ℂ)) := by
      have h1 : (2 * π * I * (0 : ℂ)) = 0 := by ring
      have h2 : (2 * π * I * (1 : ℂ)) = 2 * π * I := by ring
      rw [h1, h2, Complex.exp_zero, Complex.exp_two_pi_mul_I]
    show k (A (z₀ + (σ s : ℂ) * Complex.exp (2 * π * I * (1 : ℂ)))) - k p =
      k (A (z₀ + (σ s : ℂ) * Complex.exp (2 * π * I * (0 : ℂ)))) - k p
    rw [hper0]
  have hH0e : ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (L1 t) = H 0 t - 0 := by
    intro t ht
    rw [sub_zero, hL1e t ht]
    show k (A (z₀ + (ρ1:ℂ) * Complex.exp (2 * π * I * t))) - k p =
      k (A (z₀ + (σ 0 :ℂ) * Complex.exp (2 * π * I * t))) - k p
    have hσ0 : σ 0 = ρ1 := by rw [hσdef]; ring
    rw [hσ0]
  have hH1e : ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (L2 t) = H 1 t - 0 := by
    intro t ht
    rw [sub_zero, hL2e t ht]
    show k (A (z₀ + (ρ2:ℂ) * Complex.exp (2 * π * I * t))) - k p =
      k (A (z₀ + (σ 1 :ℂ) * Complex.exp (2 * π * I * t))) - k p
    have hσ1 : σ 1 = ρ2 := by rw [hσdef]; ring
    rw [hσ1]
  exact lift_change_eq_of_homotopy hHcont hHper hHne hL1cont hL2cont hH0e hH1e

theorem qcl_r_exists_image_quad {D : Set ℂ} (hDo : IsOpen D) {K : ℝ} {fn : ℕ → ℂ → ℂ}
    {f : ℂ → ℂ} (hqc : ∀ n, IsKQC (fn n) D K) (hlim : TendstoLocallyUniformlyOn fn f atTop D)
    (hfc : ContinuousOn f D) (hfi : InjOn f D) {Q : TopQuad}
    (hQ : closure (toExt Q.dom) ⊆ toExt D) : ∃ Q' : TopQuad, Q.IsImageUnder Q' f := by
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const continuous_im
  have hQdomD : Q.dom ⊆ D := fun w hw => by
    obtain ⟨v, hv, hvw⟩ := hQ (subset_closure (mem_image_of_mem _ hw))
    rw [← OnePoint.coe_injective hvw]; exact hv
  have hfQcont : ContinuousOn f Q.dom := hfc.mono hQdomD
  have hfQinj : InjOn f Q.dom := hfi.mono hQdomD
  obtain ⟨hQJ, hQv, φQ, ΦQ, x, hφQ, hΦQ, hxcyc, hxQ⟩ := Q.isTopQuad
  have hQdomOpen : IsOpen Q.dom := hQJ.1
  have hQo : IsOpen (f '' Q.dom) := isOpen_image_of_continuousOn_injOn hQdomOpen hfQcont hfQinj
  obtain ⟨hJD, hFext, hfr⟩ := image_isJordanDomain_of_open hDo hfc hfi hQ hQo
  have hb : Bornology.IsBounded (f '' Q.dom) := by
    apply isBounded_of_extInf_notMem_closure_toExt
    intro hmem
    have hsub : closure (toExt (f '' Q.dom)) ⊆ toExt (f '' D) :=
      closure_toExt_image_subset hfc hQ subset_rfl
    obtain ⟨w, -, hw⟩ := hsub hmem
    exact OnePoint.coe_ne_infty w hw
  obtain ⟨ψ, hψ, Ψ, hΨ⟩ := exists_conformalOnto_upperHalf_of_isJordanDomain hJD hb
  have hvfr : ∀ i, (OnePoint.map f ∘ Q.vert) i ∈ frontier (toExt (f '' Q.dom)) := by
    intro i
    rw [hfr]
    exact mem_image_of_mem _ (hQv i)
  obtain ⟨ψ', Ψ', y, hψ', hΨ', hΨ'v⟩ :=
    exists_uniformizer_finite_vertices hQo hψ hΨ hvfr
  -- conjugated self-homeomorphism `g` of `ℍ`, mirroring S06:1547's construction
  set φQinv : ℂ → ℂ := Function.invFunOn φQ Q.dom with hφQinvdef
  have hφQinvconf : IsConformalOnto φQinv upperHalf Q.dom := hφQ.symm hQdomOpen
  set g : ℂ → ℂ := ψ' ∘ f ∘ φQinv with hgdef
  have hgeq : g = ψ' ∘ (f ∘ φQinv) := rfl
  set ΦQinv : ExtPlane → ExtPlane := Function.invFunOn ΦQ (closure (toExt Q.dom)) with hΦQinvdef
  have hΦQinjC : InjOn ΦQ (closure (toExt Q.dom)) := hΦQ.2.2.1
  set G : ExtPlane → ExtPlane := Ψ' ∘ (OnePoint.map f) ∘ ΦQinv with hGdef
  have hGdef' : G = Ψ' ∘ ((OnePoint.map f) ∘ ΦQinv) := rfl
  have hΦQinvExt : IsHomeoExtension φQinv upperHalf Q.dom ΦQinv :=
    isHomeoExtension_invFunOn hφQ hΦQ
  have hstep1 : IsHomeoExtension (f ∘ φQinv) upperHalf (f '' Q.dom)
      ((OnePoint.map f) ∘ ΦQinv) :=
    IsHomeoExtension.comp hFext hΦQinvExt hφQinvconf.mapsTo
  have hfφmaps : MapsTo (f ∘ φQinv) upperHalf (f '' Q.dom) :=
    fun z hz => mem_image_of_mem f (hφQinvconf.mapsTo hz)
  have hGext : IsHomeoExtension g upperHalf upperHalf G := by
    rw [hgeq, hGdef']
    exact IsHomeoExtension.comp hΨ' hstep1 hfφmaps
  have hgs : g '' upperHalf = upperHalf := by
    rw [hgeq, image_comp, image_comp, hφQinvconf.2.2, hψ'.2.2]
  obtain ⟨z1, hz1⟩ := hQJ.2.1.nonempty
  set z₀ : ℂ := φQ z1 with hz₀def
  have hz₀mem : z₀ ∈ upperHalf := hφQ.2.2 ▸ mem_image_of_mem φQ hz1
  have hφQinvz₀ : φQinv z₀ = z1 := hφQ.2.1.leftInvOn_invFunOn hz1
  have hz1D : z1 ∈ D := hQdomD hz1
  -- local winding of `φQinv` at `z₀`
  have hφQinvDon : DifferentiableOn ℂ φQinv upperHalf := hφQinvconf.1
  have hφQinvDiffAt : DifferentiableAt ℂ φQinv z₀ := hφQinvDon.differentiableAt (hUo.mem_nhds hz₀mem)
  have hφQinvderivne : deriv φQinv z₀ ≠ 0 :=
    deriv_ne_zero_of_injOn hUo hφQinvDon hφQinvconf.2.1 hz₀mem
  obtain ⟨r₁, hr₁pos, hr₁sub, hW1a⟩ :=
    qcl_w_lift_change_eq_of_conformal hUo hz₀mem hφQinvDon hφQinvderivne
  -- local winding of `ψ'` at `f z1`
  have hfz1mem : f z1 ∈ f '' Q.dom := mem_image_of_mem f hz1
  have hψ'Don : DifferentiableOn ℂ ψ' (f '' Q.dom) := hψ'.1
  have hψ'DiffAt : DifferentiableAt ℂ ψ' (f z1) := hψ'Don.differentiableAt (hQo.mem_nhds hfz1mem)
  have hψ'derivne : deriv ψ' (f z1) ≠ 0 :=
    deriv_ne_zero_of_injOn hQo hψ'Don hψ'.2.1 hfz1mem
  obtain ⟨r₂, hr₂pos, hr₂sub, hW1b⟩ :=
    qcl_w_lift_change_eq_of_conformal hQo hfz1mem hψ'Don hψ'derivne
  -- Step A: fix `ρ*` first (independent of `n`), via continuity of `f ∘ φQinv` at `z₀`.
  have hfz1cont : ContinuousAt f z1 := hfc.continuousAt (hDo.mem_nhds hz1D)
  have hfφQinvz0cont : ContinuousAt f (φQinv z₀) := hφQinvz₀ ▸ hfz1cont
  have hφQinvcontz0 : ContinuousAt φQinv z₀ :=
    hφQinvDon.continuousOn.continuousAt (hUo.mem_nhds hz₀mem)
  have hcompcont : ContinuousAt (f ∘ φQinv) z₀ := hfφQinvz0cont.comp hφQinvcontz0
  obtain ⟨δ, hδpos, hδball⟩ := Metric.continuousAt_iff.1 hcompcont r₂ hr₂pos
  set ρstar : ℝ := min r₁ δ / 2 with hρstardef
  have hρstarpos : 0 < ρstar := by positivity
  have hρstarr1 : ρstar ≤ r₁ := by
    have := min_le_left r₁ δ; rw [hρstardef]; linarith
  have hρstarδ : ρstar < δ := by
    have := min_le_right r₁ δ; rw [hρstardef]; linarith
  set α : ℝ → ℝ → ℂ := fun σ t => φQinv (z₀ + (σ:ℂ) * Complex.exp (2 * π * I * t)) with hαdef
  have henorm : ∀ t : ℝ, ‖Complex.exp (2 * π * I * (t : ℂ))‖ = 1 := by
    intro t
    rw [Complex.norm_exp]
    have h0 : (2 * π * I * (t : ℂ)).re = 0 := by simp
    rw [h0, Real.exp_zero]
  have hcircledist : ∀ σ t : ℝ, dist (z₀ + (σ:ℂ) * Complex.exp (2 * π * I * (t:ℂ))) z₀ = |σ| := by
    intro σ t
    rw [dist_eq_norm]
    have heq : z₀ + (σ:ℂ) * Complex.exp (2 * π * I * (t:ℂ)) - z₀ =
        (σ:ℂ) * Complex.exp (2 * π * I * (t:ℂ)) := by ring
    rw [heq, norm_mul, henorm t, mul_one, Complex.norm_real, Real.norm_eq_abs]
  -- `α σ t ∈ closedBall z₀ r₁`-preimage-side, and `≠ z₁`, for `0 < σ ≤ ρstar`
  have hAcont : ContinuousOn φQinv (closedBall z₀ r₁) := hφQinvDon.continuousOn.mono hr₁sub
  have hAne : ∀ w ∈ closedBall z₀ r₁, w ≠ z₀ → φQinv w ≠ z1 := by
    intro w hw hwne heq
    exact hwne (hφQinvconf.2.1 (hr₁sub hw) (hr₁sub (mem_closedBall_self hr₁pos.le))
      (by rw [heq, hφQinvz₀]))
  have hAimgsub : φQinv '' closedBall z₀ r₁ ⊆ D := by
    rintro _ ⟨w, hw, rfl⟩
    exact hQdomD (hφQinvconf.mapsTo (hr₁sub hw))
  have hkcontf : ContinuousOn f (φQinv '' closedBall z₀ r₁) := hfc.mono hAimgsub
  have hkif : InjOn f (φQinv '' closedBall z₀ r₁) := hfi.mono hAimgsub
  have hcircUHball : ∀ σ ∈ Ioc (0:ℝ) ρstar, ∀ t : ℝ,
      z₀ + (σ:ℂ) * Complex.exp (2 * π * I * (t:ℂ)) ∈ closedBall z₀ r₁ := by
    intro σ hσ t
    rw [mem_closedBall, hcircledist σ t, abs_of_pos hσ.1]
    linarith [hσ.2, hρstarr1]
  have hασne : ∀ σ ∈ Ioc (0:ℝ) ρstar, ∀ t : ℝ, α σ t ≠ z1 := by
    intro σ hσ t
    apply hAne _ (hcircUHball σ hσ t)
    intro heq
    have h0 : dist (z₀ + (σ:ℂ) * Complex.exp (2 * π * I * (t:ℂ))) z₀ = 0 := by
      rw [heq]; exact dist_self z₀
    rw [hcircledist σ t, abs_of_pos hσ.1] at h0
    linarith [hσ.1]
  have hασinD : ∀ σ ∈ Ioc (0:ℝ) ρstar, ∀ t : ℝ, α σ t ∈ Q.dom :=
    fun σ hσ t => hφQinvconf.mapsTo (hr₁sub (hcircUHball σ hσ t))
  -- the loop `α ρstar` and its image under `f`, at the fixed radius `ρstar`
  have hαρstarcont : ContinuousOn (α ρstar) (Icc (0:ℝ) 1) := by
    have hcirc : ContinuousOn (fun t : ℝ => z₀ + (ρstar:ℂ) * Complex.exp (2 * π * I * (t:ℂ)))
        (Icc (0:ℝ) 1) := by fun_prop
    exact hAcont.comp hcirc (fun t _ => hcircUHball ρstar ⟨hρstarpos, le_refl _⟩ t)
  have hαρstarNe : ∀ t ∈ Icc (0:ℝ) 1, α ρstar t ≠ z1 :=
    fun t _ => hασne ρstar ⟨hρstarpos, le_refl _⟩ t
  have hfαρstarcont : ContinuousOn (fun t => f (α ρstar t)) (Icc (0:ℝ) 1) :=
    hfc.comp hαρstarcont (fun t ht => hQdomD (hασinD ρstar ⟨hρstarpos, le_refl _⟩ t))
  obtain ⟨t0, ht0mem, ht0min⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one)
    ((hfαρstarcont.sub continuousOn_const).norm)
  set m : ℝ := ‖f (α ρstar t0) - f z1‖ with hmdef
  have hmpos : 0 < m := by
    rw [hmdef]; exact norm_pos_iff.2 (sub_ne_zero.2 (fun heq => hαρstarNe t0 ht0mem
      (hfi (hQdomD (hασinD ρstar ⟨hρstarpos, le_refl _⟩ t0)) hz1D heq)))
  have hmle : ∀ t ∈ Icc (0:ℝ) 1, m ≤ ‖f (α ρstar t) - f z1‖ := fun t ht => ht0min ht
  -- Step D1-D2: pick `n` large via uniform convergence on the compact trace of `α ρstar`.
  set K : Set ℂ := (α ρstar '' Icc (0:ℝ) 1) ∪ {z1} with hKdef
  have hKD : K ⊆ D := by
    rintro w (⟨t, _, rfl⟩ | rfl)
    · exact hQdomD (hασinD ρstar ⟨hρstarpos, le_refl _⟩ t)
    · exact hz1D
  have hKcompact : IsCompact K :=
    (isCompact_Icc.image_of_continuousOn hαρstarcont).union isCompact_singleton
  have hunif : TendstoUniformlyOn fn f atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hDo).mp hlim K hKD hKcompact
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((Metric.tendstoUniformlyOn_iff.mp hunif) (m / 4) (by linarith))
  set n : ℕ := N with hndef
  have hnclose := hN n (le_refl N)
  have hclose1 : ∀ t ∈ Icc (0:ℝ) 1, dist (fn n (α ρstar t)) (f (α ρstar t)) < m / 4 :=
    fun t ht => dist_comm (f (α ρstar t)) (fn n (α ρstar t)) ▸ hnclose (α ρstar t) (Or.inl ⟨t, ht, rfl⟩)
  have hclose2 : dist (fn n z1) (f z1) < m / 4 :=
    dist_comm (f z1) (fn n z1) ▸ hnclose z1 (Or.inr rfl)
  have hfnDcont : ContinuousOn (fn n) D := (hqc n).2.2.1.1
  have hfnDinj : InjOn (fn n) D := (hqc n).2.2.1.2.1
  have hfnαρstarcont : ContinuousOn (fun t => fn n (α ρstar t)) (Icc (0:ℝ) 1) :=
    hfnDcont.comp hαρstarcont (fun t _ => hQdomD (hασinD ρstar ⟨hρstarpos, le_refl _⟩ t))
  have hlt_hyp : ∀ t ∈ Icc (0:ℝ) 1,
      ‖(f (α ρstar t) - f z1) - (fn n (α ρstar t) - fn n z1)‖ <
        ‖fn n (α ρstar t) - fn n z1‖ := by
    intro t ht
    set γt := f (α ρstar t) - f z1 with hγtdef
    set βt := fn n (α ρstar t) - fn n z1 with hβtdef
    have heq : γt - βt = (f (α ρstar t) - fn n (α ρstar t)) - (f z1 - fn n z1) := by
      rw [hγtdef, hβtdef]; ring
    have hb1 : ‖f (α ρstar t) - fn n (α ρstar t)‖ < m / 4 := by
      rw [← Complex.dist_eq, dist_comm]; exact hclose1 t ht
    have hb2 : ‖f z1 - fn n z1‖ < m / 4 := by
      rw [← Complex.dist_eq, dist_comm]; exact hclose2
    have hub : ‖γt - βt‖ < m / 2 := by
      rw [heq]
      calc ‖(f (α ρstar t) - fn n (α ρstar t)) - (f z1 - fn n z1)‖ ≤
          ‖f (α ρstar t) - fn n (α ρstar t)‖ + ‖f z1 - fn n z1‖ := norm_sub_le _ _
        _ < m / 2 := by linarith [hb1, hb2]
    have hγtge : m ≤ ‖γt‖ := by rw [hγtdef]; exact hmle t ht
    have hrev : ‖γt‖ - ‖βt‖ ≤ ‖γt - βt‖ := norm_sub_norm_le γt βt
    linarith [hub, hγtge, hrev]
  have hαρstarper : α ρstar 1 = α ρstar 0 := by
    show φQinv (z₀ + (ρstar:ℂ) * Complex.exp (2*π*I*(1:ℂ))) =
      φQinv (z₀ + (ρstar:ℂ) * Complex.exp (2*π*I*(0:ℂ)))
    have h1 : (2*π*I*(1:ℂ)) = 2*π*I := by ring
    have h2 : (2*π*I*(0:ℂ)) = 0 := by ring
    rw [h1, h2, Complex.exp_zero, Complex.exp_two_pi_mul_I]
  have hγcont : ContinuousOn (fun t => f (α ρstar t) - f z1) (Icc (0:ℝ) 1) :=
    hfαρstarcont.sub continuousOn_const
  have hβcont : ContinuousOn (fun t => fn n (α ρstar t) - fn n z1) (Icc (0:ℝ) 1) :=
    hfnαρstarcont.sub continuousOn_const
  have hγne0 : ∀ t ∈ Icc (0:ℝ) 1, f (α ρstar t) - f z1 ≠ 0 :=
    fun t ht => norm_pos_iff.1 (lt_of_lt_of_le hmpos (hmle t ht))
  have hβne0 : ∀ t ∈ Icc (0:ℝ) 1, fn n (α ρstar t) - fn n z1 ≠ 0 := by
    intro t ht heq
    exact hαρstarNe t ht (hfnDinj (hQdomD (hασinD ρstar ⟨hρstarpos, le_refl _⟩ t)) hz1D
      (sub_eq_zero.1 heq))
  obtain ⟨Lγ, hLγcont, hLγe0⟩ := exists_continuousOn_log_lift hγcont hγne0
  obtain ⟨Mβ, hMβcont, hMβe0⟩ := exists_continuousOn_log_lift hβcont hβne0
  have hLγe : ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (Lγ t) = f (α ρstar t) - f z1 := by
    intro t ht; rw [hLγe0 t ht, sub_zero]
  have hMβe : ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (Mβ t) = fn n (α ρstar t) - fn n z1 := by
    intro t ht; rw [hMβe0 t ht, sub_zero]
  have hMγeq := lift_change_eq_of_norm_sub_lt hγcont hβcont
    (by show f (α ρstar 1) - f z1 = f (α ρstar 0) - f z1; rw [hαρstarper])
    (by show fn n (α ρstar 1) - fn n z1 = fn n (α ρstar 0) - fn n z1; rw [hαρstarper])
    hlt_hyp hLγcont hMβcont hLγe hMβe
  -- Step D3-D6: R1 for `fn n` at `z1`, shrink to `ρ'`, W2, then RH (with `k := fn n`) back to `ρstar`.
  obtain ⟨ρ1n, hρ1npos, hloc_n⟩ := qcl_r_hloc_of_isKQC (hqc n) hz1D
  obtain ⟨εD, hεDpos, hεDball⟩ := Metric.isOpen_iff.1 hDo z1 hz1D
  set r' : ℝ := min ρ1n εD / 2 with hr'def
  have hr'pos : 0 < r' := by positivity
  have hr'ρ1n : r' < ρ1n := by have := min_le_left ρ1n εD; rw [hr'def]; linarith
  have hr'εD : r' < εD := by have := min_le_right ρ1n εD; rw [hr'def]; linarith
  have hr'D : closedBall z1 r' ⊆ D := (closedBall_subset_ball hr'εD).trans hεDball
  obtain ⟨δ', hδ'pos, hδ'ball⟩ := Metric.continuousAt_iff.1 hφQinvcontz0 r' hr'pos
  set ρ' : ℝ := min ρstar δ' / 2 with hρ'def
  have hρ'pos : 0 < ρ' := by positivity
  have hρ'ρstar : ρ' ≤ ρstar := by have := min_le_left ρstar δ'; rw [hρ'def]; linarith
  have hρ'δ' : ρ' < δ' := by have := min_le_right ρstar δ'; rw [hρ'def]; linarith
  have hασr' : ∀ t : ℝ, α ρ' t ∈ closedBall z1 r' := by
    intro t
    have hd : dist (z₀ + (ρ':ℂ) * Complex.exp (2*π*I*(t:ℂ))) z₀ < δ' := by
      rw [hcircledist ρ' t, abs_of_pos hρ'pos]; exact hρ'δ'
    have := hδ'ball hd
    rw [hφQinvz₀] at this
    exact mem_closedBall.2 this.le
  -- winding of the standard circle at radius `ρ'` around `z₀`, transported by `φQinv` (W1a)
  have hcircρ'cont : ContinuousOn (fun t : ℝ => z₀ + (ρ':ℂ) * Complex.exp (2*π*I*(t:ℂ)))
      (Icc (0:ℝ) 1) := by fun_prop
  have hcircρ'per : (z₀ + (ρ':ℂ) * Complex.exp (2*π*I*(1:ℂ))) =
      z₀ + (ρ':ℂ) * Complex.exp (2*π*I*(0:ℂ)) := by
    have h1 : (2*π*I*(1:ℂ)) = 2*π*I := by ring
    have h2 : (2*π*I*(0:ℂ)) = 0 := by ring
    rw [h1, h2, Complex.exp_zero, Complex.exp_two_pi_mul_I]
  have hcircρ'inball : ∀ t ∈ Icc (0:ℝ) 1,
      z₀ + (ρ':ℂ) * Complex.exp (2*π*I*(t:ℂ)) ∈ closedBall z₀ r₁ := by
    intro t _
    rw [mem_closedBall, hcircledist ρ' t, abs_of_pos hρ'pos]
    linarith [hρ'ρstar, hρstarr1]
  have hcircρ'ne : ∀ t ∈ Icc (0:ℝ) 1,
      z₀ + (ρ':ℂ) * Complex.exp (2*π*I*(t:ℂ)) ≠ z₀ := by
    intro t _ heq
    have h0 : dist (z₀ + (ρ':ℂ) * Complex.exp (2*π*I*(t:ℂ))) z₀ = 0 := by
      rw [heq]; exact dist_self z₀
    rw [hcircledist ρ' t, abs_of_pos hρ'pos] at h0
    linarith [hρ'pos]
  set Lρ' : ℝ → ℂ := fun t => (Real.log ρ' : ℂ) + 2*π*I*(t:ℂ) with hLρ'def
  have hLρ'cont : ContinuousOn Lρ' (Icc (0:ℝ) 1) := by fun_prop
  have hLρ'e : ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (Lρ' t) =
      z₀ + (ρ':ℂ) * Complex.exp (2*π*I*(t:ℂ)) - z₀ := by
    intro t _
    show Complex.exp ((Real.log ρ' : ℂ) + 2*π*I*(t:ℂ)) = _
    rw [Complex.exp_add]
    have heq : z₀ + (ρ':ℂ) * Complex.exp (2*π*I*(t:ℂ)) - z₀ =
        (ρ':ℂ) * Complex.exp (2*π*I*(t:ℂ)) := by ring
    rw [heq]
    congr 1
    rw [← Complex.ofReal_exp, Real.exp_log hρ'pos]
  have hLρ'diff : Lρ' 1 - Lρ' 0 = 2*π*I := by rw [hLρ'def]; push_cast; ring
  have hφcircρ'cont : ContinuousOn
      (fun t : ℝ => φQinv (z₀ + (ρ':ℂ) * Complex.exp (2*π*I*(t:ℂ)))) (Icc (0:ℝ) 1) :=
    hAcont.comp hcircρ'cont hcircρ'inball
  have hφcircρ'ne : ∀ t ∈ Icc (0:ℝ) 1,
      φQinv (z₀ + (ρ':ℂ) * Complex.exp (2*π*I*(t:ℂ))) ≠ z1 :=
    fun t ht => hAne _ (hcircρ'inball t ht) (hcircρ'ne t ht)
  obtain ⟨Mρ', hMρ'cont, hMρ'e0⟩ := exists_continuousOn_log_lift hφcircρ'cont hφcircρ'ne
  have hMρ'e0' : ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (Mρ' t) =
      φQinv (z₀ + (ρ':ℂ) * Complex.exp (2*π*I*(t:ℂ))) - φQinv z₀ := by
    intro t ht; rw [hMρ'e0 t ht, hφQinvz₀]
  have hW1a_result := hW1a (fun t : ℝ => z₀ + (ρ':ℂ) * Complex.exp (2*π*I*(t:ℂ)))
    hcircρ'cont hcircρ'per hcircρ'inball hcircρ'ne Lρ' Mρ' hLρ'cont hMρ'cont hLρ'e hMρ'e0'
  have hMρ'diff : Mρ' 1 - Mρ' 0 = 2*π*I := hW1a_result.trans hLρ'diff
  -- W2 with `k := fn n` at `p := z1`, radius `r'`, using `hMρ'diff` as the loop's own winding
  have hloc_n' : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r' → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0:ℝ) 1,
        Complex.exp (L t) = fn n (z1 + ρ * Complex.exp (2*π*I*t)) - fn n z1) →
      L 1 - L 0 = 2*π*I :=
    fun ρ hρpos hρle L hLcont hLe => hloc_n ρ hρpos (hρle.trans_lt hr'ρ1n) L hLcont hLe
  have hαρ'per : φQinv (z₀ + (ρ':ℂ) * Complex.exp (2*π*I*(1:ℂ))) =
      φQinv (z₀ + (ρ':ℂ) * Complex.exp (2*π*I*(0:ℂ))) := by rw [hcircρ'per]
  have hfnαρ'cont : ContinuousOn
      (fun t : ℝ => fn n (φQinv (z₀ + (ρ':ℂ) * Complex.exp (2*π*I*(t:ℂ))))) (Icc (0:ℝ) 1) :=
    hfnDcont.comp hφcircρ'cont (fun t _ => hr'D (hασr' t))
  have hfnαρ'ne : ∀ t ∈ Icc (0:ℝ) 1,
      fn n (φQinv (z₀ + (ρ':ℂ) * Complex.exp (2*π*I*(t:ℂ)))) ≠ fn n z1 := by
    intro t ht heq
    exact hφcircρ'ne t ht (hfnDinj (hr'D (hασr' t)) hz1D heq)
  obtain ⟨Nρ', hNρ'cont, hNρ'e0⟩ := exists_continuousOn_log_lift hfnαρ'cont hfnαρ'ne
  have hW2result := qcl_w_lift_change_eq_of_injOn hDo hr'pos hr'D hfnDcont hfnDinj hloc_n'
    hφcircρ'cont hαρ'per (fun t _ => hασr' t) hφcircρ'ne hMρ'cont hNρ'cont
    hMρ'e0 hNρ'e0 hMρ'diff
  -- RH (with `k := fn n`): transport from `ρ'` back up to the fixed `ρstar`
  have hRHn := qcl_r_c_radial_winding_eq hr₁pos hφQinvz₀ hAne hAcont
    (hfnDcont.mono hAimgsub) (hfnDinj.mono hAimgsub)
    ⟨hρstarpos, hρstarr1⟩ ⟨hρ'pos, hρ'ρstar.trans hρstarr1⟩
    hMβcont hNρ'cont hMβe hNρ'e0
  have hcore : Lγ 1 - Lγ 0 = 2 * π * I := by
    rw [hMγeq, hRHn, hW2result]
  -- Step B/C: assemble `hloc` for `g` at `z₀`, valid for ALL radii `< ρstar`
  have hloc_g : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0:ℝ) 1, Complex.exp (L t) = g (z₀ + ρ * Complex.exp (2*π*I*t)) - g z₀) →
      L 1 - L 0 = 2 * π * I := by
    refine ⟨ρstar, hρstarpos, ?_⟩
    intro ρ hρpos hρltρstar L hLcont hLe
    have hcircρcont : ContinuousOn (fun t : ℝ => z₀ + (ρ:ℂ) * Complex.exp (2*π*I*(t:ℂ)))
        (Icc (0:ℝ) 1) := by fun_prop
    have hcircρper : (z₀ + (ρ:ℂ) * Complex.exp (2*π*I*(1:ℂ))) =
        z₀ + (ρ:ℂ) * Complex.exp (2*π*I*(0:ℂ)) := by
      have h1 : (2*π*I*(1:ℂ)) = 2*π*I := by ring
      have h2 : (2*π*I*(0:ℂ)) = 0 := by ring
      rw [h1, h2, Complex.exp_zero, Complex.exp_two_pi_mul_I]
    have hcircρinball : ∀ t ∈ Icc (0:ℝ) 1,
        z₀ + (ρ:ℂ) * Complex.exp (2*π*I*(t:ℂ)) ∈ closedBall z₀ r₁ := by
      intro t _
      rw [mem_closedBall, hcircledist ρ t, abs_of_pos hρpos]
      linarith [hρltρstar, hρstarr1]
    have hcircρne : ∀ t ∈ Icc (0:ℝ) 1,
        z₀ + (ρ:ℂ) * Complex.exp (2*π*I*(t:ℂ)) ≠ z₀ := by
      intro t _ heq
      have h0 : dist (z₀ + (ρ:ℂ) * Complex.exp (2*π*I*(t:ℂ))) z₀ = 0 := by
        rw [heq]; exact dist_self z₀
      rw [hcircledist ρ t, abs_of_pos hρpos] at h0
      linarith [hρpos]
    have hφcircρcont : ContinuousOn
        (fun t : ℝ => φQinv (z₀ + (ρ:ℂ) * Complex.exp (2*π*I*(t:ℂ)))) (Icc (0:ℝ) 1) :=
      hAcont.comp hcircρcont hcircρinball
    have hφcircρne : ∀ t ∈ Icc (0:ℝ) 1,
        φQinv (z₀ + (ρ:ℂ) * Complex.exp (2*π*I*(t:ℂ))) ≠ z1 :=
      fun t ht => hAne _ (hcircρinball t ht) (hcircρne t ht)
    have hfαρinball2 : ∀ t ∈ Icc (0:ℝ) 1,
        f (φQinv (z₀ + (ρ:ℂ) * Complex.exp (2*π*I*(t:ℂ)))) ∈ closedBall (f z1) r₂ := by
      intro t _
      have hd : dist (z₀ + (ρ:ℂ) * Complex.exp (2*π*I*(t:ℂ))) z₀ < δ := by
        rw [hcircledist ρ t, abs_of_pos hρpos]; linarith [hρltρstar, hρstarδ]
      have hthis := hδball hd
      have heq0 : (f ∘ φQinv) z₀ = f z1 := by
        show f (φQinv z₀) = f z1; rw [hφQinvz₀]
      rw [heq0] at hthis
      exact mem_closedBall.2 hthis.le
    have hfαρcont : ContinuousOn
        (fun t : ℝ => f (φQinv (z₀ + (ρ:ℂ) * Complex.exp (2*π*I*(t:ℂ))))) (Icc (0:ℝ) 1) :=
      hkcontf.comp hφcircρcont (fun t ht => mem_image_of_mem φQinv (hcircρinball t ht))
    have hz1mem2 : z1 ∈ φQinv '' closedBall z₀ r₁ :=
      hφQinvz₀ ▸ mem_image_of_mem φQinv (mem_closedBall_self hr₁pos.le)
    have hfαρne : ∀ t ∈ Icc (0:ℝ) 1,
        f (φQinv (z₀ + (ρ:ℂ) * Complex.exp (2*π*I*(t:ℂ)))) ≠ f z1 := by
      intro t ht heq
      exact hφcircρne t ht (hkif (mem_image_of_mem φQinv (hcircρinball t ht)) hz1mem2 heq)
    obtain ⟨Lfα, hLfαcont, hLfαe0⟩ := exists_continuousOn_log_lift hfαρcont hfαρne
    have hLe' : ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (L t) =
        ψ' (f (φQinv (z₀ + (ρ:ℂ) * Complex.exp (2*π*I*(t:ℂ))))) - ψ' (f z1) := by
      intro t ht
      rw [hLe t ht]
      show g (z₀ + (ρ:ℂ) * Complex.exp (2*π*I*(t:ℂ))) - g z₀ = _
      rw [hgeq]
      show ψ' (f (φQinv (z₀ + (ρ:ℂ) * Complex.exp (2*π*I*(t:ℂ))))) - ψ' (f (φQinv z₀)) = _
      rw [hφQinvz₀]
    have hfαρper : (fun t : ℝ => f (φQinv (z₀ + (ρ:ℂ) * Complex.exp (2*π*I*(t:ℂ))))) 1 =
        (fun t : ℝ => f (φQinv (z₀ + (ρ:ℂ) * Complex.exp (2*π*I*(t:ℂ))))) 0 := by
      show f (φQinv (z₀ + (ρ:ℂ) * Complex.exp (2*π*I*(1:ℂ)))) =
        f (φQinv (z₀ + (ρ:ℂ) * Complex.exp (2*π*I*(0:ℂ))))
      rw [hcircρper]
    have hW1b_result := hW1b (fun t : ℝ => f (φQinv (z₀ + (ρ:ℂ) * Complex.exp (2*π*I*(t:ℂ)))))
      hfαρcont hfαρper hfαρinball2 hfαρne Lfα L hLfαcont hLcont hLfαe0 hLe'
    have hRHf := qcl_r_c_radial_winding_eq hr₁pos hφQinvz₀ hAne hAcont hkcontf hkif
      ⟨hρpos, hρltρstar.le.trans hρstarr1⟩ ⟨hρstarpos, hρstarr1⟩
      hLfαcont hLγcont hLfαe0 hLγe
    rw [hW1b_result, hRHf, hcore]
  -- Apply R2, then assemble `Q'`.
  have hGxy : ∀ i, G (((x i:ℝ):ℂ):ExtPlane) = (((y i:ℝ):ℂ):ExtPlane) := by
    intro i
    show Ψ' (OnePoint.map f (ΦQinv (((x i:ℝ):ℂ):ExtPlane))) = _
    have hQvimem : Q.vert i ∈ closure (toExt Q.dom) := frontier_subset_closure (hQv i)
    have hΦQinvcancel : ΦQinv (((x i:ℝ):ℂ):ExtPlane) = Q.vert i := by
      rw [hΦQinvdef, ← hxQ i]
      exact hΦQ.2.2.1.leftInvOn_invFunOn hQvimem
    rw [hΦQinvcancel]
    exact hΨ'v i
  have hCyc : CyclicStrictMono y :=
    qcl_r_cyclicStrictMono_of_hloc hGext hgs hz₀mem hloc_g x hxcyc y hGxy
  set Q' : TopQuad := ⟨f '' Q.dom, OnePoint.map f ∘ Q.vert, hJD, hvfr, ψ', Ψ', y, hψ', hΨ', hCyc, hΨ'v⟩
    with hQ'def
  exact ⟨Q', rfl, fun i => rfl⟩



/-! ### Theorem 8.2 — helpers of piece M -/


/-! ### Small reusable helpers -/

/-- If `Q.side i` equals `toExt S` for a plain subset `S` of `ℂ`, then `Q.sideC i = S`. -/
theorem qcl_m_sideC_eq_of_side_eq {Q : TopQuad} {i : Fin 4} {S : Set ℂ}
    (h : Q.side i = toExt S) : Q.sideC i = S := by
  ext z
  simp only [TopQuad.sideC, mem_setOf_eq, h, toExt, mem_image]
  constructor
  · rintro ⟨w, hw, hwz⟩
    rwa [OnePoint.coe_injective hwz] at hw
  · intro hz
    exact ⟨z, hz, rfl⟩

/-- Descend a homeomorphic boundary extension `F` between the closures of two *bounded* sets
`U, V ⊆ ℂ` to a genuine continuous injective `g : ℂ → ℂ` on `closure U`, agreeing with `f`
on `U` itself and with image `closure V`. -/
theorem qcl_m_descend {f : ℂ → ℂ} {U V : Set ℂ} {F : ExtPlane → ExtPlane}
    (hUb : Bornology.IsBounded U) (hVb : Bornology.IsBounded V)
    (hF : IsHomeoExtension f U V F) :
    ∃ g : ℂ → ℂ, (∀ z ∈ closure U, (g z : ExtPlane) = F (z : ExtPlane)) ∧
      ContinuousOn g (closure U) ∧ InjOn g (closure U) ∧ g '' closure U = closure V ∧
      EqOn g f U := by
  obtain ⟨hF1, hF2, hF3, hF4⟩ := hF
  have hUKe : closure (toExt U) = toExt (closure U) := closure_toExt_of_isBounded hUb
  have hVKe : closure (toExt V) = toExt (closure V) := closure_toExt_of_isBounded hVb
  have hmemU : ∀ z ∈ closure U, (z : ExtPlane) ∈ closure (toExt U) := fun z hz => by
    rw [hUKe]; exact mem_image_of_mem _ hz
  have hspec : ∀ z ∈ closure U, ∃ w ∈ closure V, F (z : ExtPlane) = (w : ExtPlane) := by
    intro z hz
    have h1 : F (z : ExtPlane) ∈ toExt (closure V) := by
      rw [← hVKe, ← hF4]; exact mem_image_of_mem F (hmemU z hz)
    obtain ⟨w, hw, hwe⟩ := h1
    exact ⟨w, hw, hwe.symm⟩
  have hgspec : ∀ z ∈ closure U, ∀ w : ℂ, F (z : ExtPlane) = (w : ExtPlane) →
      Function.invFun ((↑) : ℂ → ExtPlane) (F (z : ExtPlane)) = w := by
    intro z _ w hw
    apply OnePoint.coe_injective
    rw [Function.invFun_eq ⟨w, hw.symm⟩, hw]
  set g : ℂ → ℂ := fun z => Function.invFun ((↑) : ℂ → ExtPlane) (F (z : ExtPlane)) with hgdef
  refine ⟨g, fun z hz => ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨w, hw, hwe⟩ := hspec z hz
    simp only [hgdef]
    rw [hgspec z hz w hwe, hwe]
  · rw [OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_iff]
    have h1 : ContinuousOn (fun z : ℂ => F (z : ExtPlane)) (closure U) :=
      hF2.comp OnePoint.continuous_coe.continuousOn hmemU
    refine h1.congr fun z hz => ?_
    simp only [hgdef, Function.comp_apply]
    obtain ⟨w, hw, hwe⟩ := hspec z hz
    rw [hgspec z hz w hwe, hwe]
  · intro z1 hz1 z2 hz2 heq
    simp only [hgdef] at heq
    obtain ⟨w1, hw1, hwe1⟩ := hspec z1 hz1
    obtain ⟨w2, hw2, hwe2⟩ := hspec z2 hz2
    rw [hgspec z1 hz1 w1 hwe1, hgspec z2 hz2 w2 hwe2] at heq
    subst heq
    have hFeq : F (z1 : ExtPlane) = F (z2 : ExtPlane) := by rw [hwe1, hwe2]
    exact OnePoint.coe_injective (hF3 (hmemU z1 hz1) (hmemU z2 hz2) hFeq)
  · ext w
    simp only [mem_image, hgdef]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨w', hw', hwe⟩ := hspec z hz
      rw [hgspec z hz w' hwe]
      exact hw'
    · intro hw
      have h1 : (w : ExtPlane) ∈ F '' closure (toExt U) := by
        rw [hF4, hVKe]; exact mem_image_of_mem _ hw
      obtain ⟨p, hp, hpw⟩ := h1
      rw [hUKe] at hp
      obtain ⟨z, hz, rfl⟩ := hp
      exact ⟨z, hz, hgspec z hz w hpw⟩
  · intro z hz
    have hzc : z ∈ closure U := subset_closure hz
    have hFz : F (z : ExtPlane) = (f z : ExtPlane) := hF1 z hz
    simp only [hgdef]
    exact hgspec z hzc (f z) hFz

/-- If `g` is a homeomorphism of `U` onto `V` (open sets, `U` bounded) that extends continuously
and injectively to `closure U`, then `frontier V = g '' frontier U`. -/
theorem qcl_m_frontier_eq_image {g : ℂ → ℂ} {U V : Set ℂ} (hUo : IsOpen U) (hVo : IsOpen V)
    (hUb : Bornology.IsBounded U) (hgc : ContinuousOn g (closure U)) (hgi : InjOn g (closure U))
    (hgU : g '' U = V) : frontier V = g '' frontier U := by
  have hKc : IsCompact (closure U) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hUb.closure
  have h1 : IsCompact (g '' closure U) := hKc.image_of_continuousOn hgc
  have hcl : g '' closure U = closure V := by
    apply subset_antisymm
    · have h2 := hgc.image_closure
      rwa [hgU] at h2
    · exact closure_minimal (by rw [← hgU]; exact image_mono subset_closure) h1.isClosed
  rw [hVo.frontier_eq, ← hcl, ← hgU, hUo.frontier_eq, hgi.image_diff_subset subset_closure]

/-- For a *bounded* `TopQuad`, a side (as a subset of `ℂ̄`) is exactly `toExt` of its `ℂ`-version
`sideC`. -/
theorem qcl_m_side_eq_toExt_sideC {Q : TopQuad} (hQb : Bornology.IsBounded Q.dom) (i : Fin 4) :
    Q.side i = toExt (Q.sideC i) := by
  have hfrb : frontier (toExt Q.dom) = toExt (frontier Q.dom) :=
    frontier_toExt_of_isBounded hQb Q.isTopQuad.1.1
  have hsub : Q.side i ⊆ frontier (toExt Q.dom) := fun p hp => hp.1
  ext p
  constructor
  · intro hp
    have hp' : p ∈ toExt (frontier Q.dom) := hfrb ▸ hsub hp
    obtain ⟨z, hz, rfl⟩ := hp'
    exact ⟨z, hp, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact hz

/-- For a bounded `TopQuad`, a side (as a subset of `ℂ`) lies in the closure of the domain. -/
theorem qcl_m_sideC_subset_closure {Q : TopQuad} (hQb : Bornology.IsBounded Q.dom) (i : Fin 4) :
    Q.sideC i ⊆ closure Q.dom := by
  intro z hz
  have h1 : (z : ExtPlane) ∈ Q.side i := hz
  have h2 : (z : ExtPlane) ∈ closure (toExt Q.dom) := frontier_subset_closure h1.1
  rw [closure_toExt_of_isBounded hQb] at h2
  obtain ⟨w, hw, hwe⟩ := h2
  exact (OnePoint.coe_injective hwe) ▸ hw

/-- If `g` is continuous and injective on an open `D ⊇ closure Q₁.dom` and carries `Q₁` (bounded)
to `Q₂` (bounded) with matching vertices, then `g` carries the `i`-th side of `Q₁` (as a subset of
`ℂ`) onto that of `Q₂`. -/
theorem qcl_m_sideC_eq_image {D : Set ℂ} (hDo : IsOpen D) {g : ℂ → ℂ} (hgc : ContinuousOn g D)
    (hgi : InjOn g D) {Q₁ Q₂ : TopQuad} (hb1 : Bornology.IsBounded Q₁.dom)
    (hb2 : Bornology.IsBounded Q₂.dom) (hQ1D : closure (toExt Q₁.dom) ⊆ toExt D)
    (himg : g '' Q₁.dom = Q₂.dom) (hvert : ∀ j, Q₂.vert j = OnePoint.map g (Q₁.vert j)) (i : Fin 4) :
    Q₂.sideC i = g '' Q₁.sideC i := by
  have hQ2o : IsOpen Q₂.dom := Q₂.isTopQuad.1.1
  have hfo : IsOpen (g '' Q₁.dom) := himg ▸ hQ2o
  have h := image_isJordanDomain_of_open hDo hgc hgi hQ1D hfo
  have hext : IsHomeoExtension g Q₁.dom Q₂.dom (OnePoint.map g) := himg ▸ h.2.1
  have h1 := aqc_image_side_homeo hQ2o himg hext i
  rw [← hvert i, ← hvert (i + 1), ← hvert (i + 2), ← Q₂.side_eq_boundaryArc i] at h1
  have h2 : Q₁.side i = toExt (Q₁.sideC i) := qcl_m_side_eq_toExt_sideC hb1 i
  have h3 : Q₂.side i = toExt (Q₂.sideC i) := qcl_m_side_eq_toExt_sideC hb2 i
  rw [h2, h3] at h1
  have h4 : ∀ S : Set ℂ, OnePoint.map g '' toExt S = toExt (g '' S) := by
    intro S; simp only [toExt, image_image]; rfl
  rw [h4] at h1
  exact ((Set.image_eq_image OnePoint.coe_injective).1 h1).symm

/-- If `g` agrees with the `ExtPlane`-level map `F` (via coercion) on a set `C`, then for
`S ⊆ C`, `toExt (g '' S) = F '' toExt S`. -/
theorem qcl_m_toExt_image_eq {g : ℂ → ℂ} {F : ExtPlane → ExtPlane} {C S : Set ℂ}
    (heq : ∀ z ∈ C, (g z : ExtPlane) = F (z : ExtPlane)) (hSC : S ⊆ C) :
    toExt (g '' S) = F '' toExt S := by
  apply Set.Subset.antisymm
  · intro w hw
    obtain ⟨x, hx, hxw⟩ := hw
    obtain ⟨z, hz, hzx⟩ := hx
    refine ⟨(z : ExtPlane), ⟨z, hz, rfl⟩, ?_⟩
    rw [← heq z (hSC hz), hzx]
    exact hxw
  · intro w hw
    obtain ⟨p, hp, hpw⟩ := hw
    obtain ⟨z, hz, hzp⟩ := hp
    refine ⟨g z, ⟨z, hz, rfl⟩, ?_⟩
    rw [heq z (hSC hz), hzp]
    exact hpw

/-- If `g` is continuous on `S` at `x ∈ S`, and `f n → x` with `f n ∈ S` always, then
`g (f n) → g x`. -/
theorem qcl_m_tendsto_of_continuousOn {g : ℂ → ℂ} {S : Set ℂ} {x : ℂ} (hgc : ContinuousOn g S)
    (hxS : x ∈ S) {f : ℕ → ℂ} (hfS : ∀ n, f n ∈ S) (hf : Tendsto f atTop (𝓝 x)) :
    Tendsto (fun n => g (f n)) atTop (𝓝 (g x)) := by
  have h1 : Tendsto f atTop (𝓝[S] x) := tendsto_nhdsWithin_iff.2 ⟨hf, Eventually.of_forall hfS⟩
  exact (hgc x hxS).tendsto.comp h1

/-- Two points with the same real part are at distance the absolute difference of their
imaginary parts. -/
theorem qcl_m_dist_of_re_eq {p q : ℂ} (h : p.re = q.re) : dist p q = |p.im - q.im| := by
  rw [Complex.dist_eq, Complex.norm_def, Complex.normSq_apply]
  have h1 : (p - q).re = 0 := by rw [Complex.sub_re, h, sub_self]
  have h2 : (p - q).im = p.im - q.im := Complex.sub_im p q
  rw [h1, h2, mul_zero, zero_add, ← sq, Real.sqrt_sq_eq_abs]

/-- Two points with the same imaginary part are at distance the absolute difference of their
real parts. -/
theorem qcl_m_dist_of_im_eq {p q : ℂ} (h : p.im = q.im) : dist p q = |p.re - q.re| := by
  rw [Complex.dist_eq, Complex.norm_def, Complex.normSq_apply]
  have h1 : (p - q).im = 0 := by rw [Complex.sub_im, h, sub_self]
  have h2 : (p - q).re = p.re - q.re := Complex.sub_re p q
  rw [h1, h2, mul_zero, add_zero, ← sq, Real.sqrt_sq_eq_abs]

/-- The four sides of `rectQuad ha hb`, as subsets of `ℂ`: bottom, right, top, left. -/
theorem qcl_m_rectQuad_sideC {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (rectQuad ha hb).sideC 0 = Icc 0 a ×ℂ ({0} : Set ℝ) ∧
      (rectQuad ha hb).sideC 1 = ({a} : Set ℝ) ×ℂ Icc 0 b ∧
      (rectQuad ha hb).sideC 2 = Icc 0 a ×ℂ ({b} : Set ℝ) ∧
      (rectQuad ha hb).sideC 3 = ({0} : Set ℝ) ×ℂ Icc 0 b := by
  refine ⟨qcl_m_sideC_eq_of_side_eq ?_, qcl_m_sideC_eq_of_side_eq ?_, qcl_m_sideC_eq_of_side_eq ?_,
    qcl_m_sideC_eq_of_side_eq ?_⟩
  · rw [TopQuad.side_eq_boundaryArc]; exact boundaryArc_frontier_toExt_rectangle_bottom ha hb
  · rw [TopQuad.side_eq_boundaryArc]; exact aqc_boundaryArc_frontier_toExt_rectangle_right ha hb
  · rw [TopQuad.side_eq_boundaryArc]; exact boundaryArc_frontier_toExt_rectangle_top ha hb
  · rw [TopQuad.side_eq_boundaryArc]; exact aqc_boundaryArc_frontier_toExt_rectangle_left ha hb

/-- The finite complex value underlying `rectVert c d i`. -/
def qcl_m_rectVertC (c d : ℝ) : Fin 4 → ℂ := ![0, (c : ℂ), (c : ℂ) + (d : ℂ) * I, (d : ℂ) * I]

theorem qcl_m_rectVert_eq (c d : ℝ) (i : Fin 4) :
    rectVert c d i = ((qcl_m_rectVertC c d i : ℂ) : ExtPlane) := by
  fin_cases i <;> rfl

/-! ### M1 -/

/-- **M1.** Every bounded quadrilateral is the limit from inside of quadrilaterals with closures in
its interior. -/
theorem qcl_m_exists_tendsFromInside (Q : TopQuad) (hQb : Bornology.IsBounded Q.dom) :
    ∃ Qm : ℕ → TopQuad, TopQuad.TendsFromInside Qm Q ∧
      ∀ m, closure (toExt (Qm m).dom) ⊆ toExt Q.dom := by
  have hQo : IsOpen Q.dom := Q.isTopQuad.1.1
  obtain ⟨a, b, g, ha, hb, hgconf, G, hGext, hGv⟩ := thm1_1_exists_rectangle Q
  set ginv : ℂ → ℂ := Function.invFunOn g Q.dom with hginvdef
  set Ginv : ExtPlane → ExtPlane := Function.invFunOn G (closure (toExt Q.dom)) with hGinvdef
  have hginvConf : IsConformalOnto ginv (rectangle a b) Q.dom := hgconf.symm hQo
  have hGinvExt : IsHomeoExtension ginv (rectangle a b) Q.dom Ginv :=
    isHomeoExtension_invFunOn hgconf hGext
  have hGinv_vert : ∀ i, Ginv (rectVert a b i) = Q.vert i := by
    intro i
    have hmem : (Q.vert i : ExtPlane) ∈ closure (toExt Q.dom) :=
      frontier_subset_closure (Q.isTopQuad.2.1 i)
    have h := hGext.2.2.1.leftInvOn_invFunOn hmem
    rw [← hGv i]
    exact h
  -- descend `Ginv` to a genuine continuous injective ℂ → ℂ map on the closed rectangle
  obtain ⟨g0, hg0eq, hg0cont, hg0inj, hg0img, hg0eqOn⟩ :=
    qcl_m_descend (isBounded_rectangle a b) hQb hGinvExt
  have hQdom_eq : g0 '' (rectangle a b) = Q.dom := by
    rw [hg0eqOn.image_eq]; exact hginvConf.2.2
  have hfrontierQ : frontier Q.dom = g0 '' frontier (rectangle a b) :=
    qcl_m_frontier_eq_image (isOpen_rectangle a b) hQo (isBounded_rectangle a b) hg0cont hg0inj
      hQdom_eq
  have hQsideC : ∀ i, Q.sideC i = g0 '' ((rectQuad ha hb).sideC i) := by
    intro i
    have h1 := TopQuad.image_side (Q := rectQuad ha hb) (V := Q.dom) hQo hginvConf hGinvExt i
    have hrv : (rectQuad ha hb).vert = rectVert a b := rfl
    rw [hrv, hGinv_vert, hGinv_vert, hGinv_vert, ← Q.side_eq_boundaryArc i] at h1
    have h2 : (rectQuad ha hb).side i = toExt ((rectQuad ha hb).sideC i) :=
      qcl_m_side_eq_toExt_sideC (isBounded_rectangle a b) i
    have h3 : Q.side i = toExt (Q.sideC i) := qcl_m_side_eq_toExt_sideC hQb i
    rw [h2, h3] at h1
    have h4 : toExt (g0 '' ((rectQuad ha hb).sideC i)) = Ginv '' toExt ((rectQuad ha hb).sideC i) :=
      qcl_m_toExt_image_eq hg0eq (qcl_m_sideC_subset_closure (isBounded_rectangle a b) i)
    rw [h1] at h4
    exact (Set.image_eq_image OnePoint.coe_injective).1 h4.symm
  -- the shrink parameter
  set ε : ℕ → ℝ := fun m => min a b / (2 * ((m : ℝ) + 3)) with hεdef
  have hmab : 0 < min a b := lt_min ha hb
  have hεpos : ∀ m, 0 < ε m := fun m => div_pos hmab (by positivity)
  have hε2 : ∀ m : ℕ, 2 * ε m < min a b := by
    intro m
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hlt : ε m < min a b / 2 := by
      rw [hεdef, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_nonneg hmab.le hm]
    linarith
  have hεtendsto : Tendsto ε atTop (𝓝 0) := by
    have hcast : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hadd : Tendsto (fun m : ℕ => (m : ℝ) + 3) atTop atTop :=
      hcast.atTop_add tendsto_const_nhds
    have hg : Tendsto (fun m : ℕ => 2 * ((m : ℝ) + 3)) atTop atTop :=
      hadd.const_mul_atTop (by norm_num)
    have hkey : ε = fun m : ℕ => min a b / (2 * ((m : ℝ) + 3)) := hεdef
    rw [hkey]
    exact (tendsto_const_nhds (x := min a b)).div_atTop hg
  have ha' : ∀ m, 0 < a - 2 * ε m := fun m => by linarith [hε2 m, min_le_left a b]
  have hb' : ∀ m, 0 < b - 2 * ε m := fun m => by linarith [hε2 m, min_le_right a b]
  set cm : ℕ → ℂ := fun m => (ε m : ℂ) * (1 + I) with hcmdef
  -- translation is a conformal self-map of `ℂ`
  have htrans_conf : ∀ c : ℂ, IsConformalOnto (fun z : ℂ => z + c) univ univ := fun c =>
    ⟨(differentiable_id.add (differentiable_const c)).differentiableOn,
      fun x _ y _ h => by simpa using h,
      by rw [image_univ, Set.range_eq_univ]; exact fun w => ⟨w - c, by ring⟩⟩
  have hUsub : ∀ m, closure (toExt (rectQuad (ha' m) (hb' m)).dom) ⊆ toExt (univ : Set ℂ) := by
    intro m
    have hdom_eq : (rectQuad (ha' m) (hb' m)).dom = rectangle (a - 2 * ε m) (b - 2 * ε m) := rfl
    rw [hdom_eq, closure_toExt_of_isBounded (isBounded_rectangle (a - 2 * ε m) (b - 2 * ε m))]
    exact image_mono (subset_univ _)
  have hRm_exists : ∀ m : ℕ, ∃ Rm : TopQuad,
      (rectQuad (ha' m) (hb' m)).IsImageUnder Rm (fun z => z + cm m) ∧
        (rectQuad (ha' m) (hb' m)).ConfEquiv Rm := fun m =>
    TopQuad.exists_image_conformal isOpen_univ (htrans_conf (cm m)) (hUsub m)
  choose Rm hRm_img _hRm_confEquiv using hRm_exists
  have hRm_dom_eq : ∀ m, (Rm m).dom = (fun z => z + cm m) '' (rectQuad (ha' m) (hb' m)).dom :=
    fun m => (hRm_img m).1
  have hRm_vert_eq : ∀ m i, (Rm m).vert i = OnePoint.map (fun z => z + cm m)
      ((rectQuad (ha' m) (hb' m)).vert i) := fun m i => (hRm_img m).2 i
  have hdomRQ : ∀ m, (rectQuad (ha' m) (hb' m)).dom = rectangle (a - 2 * ε m) (b - 2 * ε m) := fun _ => rfl
  have hvertRQ : ∀ m, (rectQuad (ha' m) (hb' m)).vert = rectVert (a - 2 * ε m) (b - 2 * ε m) :=
    fun _ => rfl
  have hclosed_box_compact : ∀ m,
      IsCompact (Icc (0 : ℝ) (a - 2 * ε m) ×ℂ Icc (0 : ℝ) (b - 2 * ε m)) := fun _ =>
    isCompact_Icc.reProdIm isCompact_Icc
  have hRm_closure_eq : ∀ m, closure (Rm m).dom =
      (fun z => z + cm m) '' (Icc (0 : ℝ) (a - 2 * ε m) ×ℂ Icc (0 : ℝ) (b - 2 * ε m)) := by
    intro m
    rw [hRm_dom_eq m, hdomRQ m]
    show closure (⇑(Homeomorph.addRight (cm m)) '' rectangle (a - 2 * ε m) (b - 2 * ε m)) = _
    rw [← (Homeomorph.addRight (cm m)).image_closure, closure_rectangle_eq_reProdIm (ha' m) (hb' m)]
    rfl
  have hRm_bdd : ∀ m, Bornology.IsBounded (Rm m).dom := by
    intro m
    have hcbdd : Bornology.IsBounded (closure (Rm m).dom) := by
      rw [hRm_closure_eq m]
      exact ((hclosed_box_compact m).image (continuous_id.add continuous_const)).isBounded
    exact hcbdd.subset subset_closure
  have hcmre : ∀ m, (cm m).re = ε m := fun m => by rw [hcmdef]; simp
  have hcmim : ∀ m, (cm m).im = ε m := fun m => by rw [hcmdef]; simp
  have hbox_sub : ∀ m, (fun z : ℂ => z + cm m) ''
      (Icc (0 : ℝ) (a - 2 * ε m) ×ℂ Icc (0 : ℝ) (b - 2 * ε m)) ⊆ rectangle a b := by
    intro m w hw
    obtain ⟨z, hz, rfl⟩ := hw
    rw [mem_reProdIm] at hz
    obtain ⟨⟨hz1, hz2⟩, ⟨hz3, hz4⟩⟩ := hz
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Complex.add_re, hcmre]; linarith [hεpos m]
    · rw [Complex.add_re, hcmre]; linarith [hεpos m]
    · rw [Complex.add_im, hcmim]; linarith [hεpos m]
    · rw [Complex.add_im, hcmim]; linarith [hεpos m]
  have hRmc : ∀ m, closure (toExt (Rm m).dom) ⊆ toExt (rectangle a b) := by
    intro m
    rw [closure_toExt_of_isBounded (hRm_bdd m), hRm_closure_eq m]
    exact image_mono (hbox_sub m)
  have hRm_sub : ∀ m, (Rm m).dom ⊆ rectangle a b := by
    intro m
    have h1 : toExt (Rm m).dom ⊆ toExt (rectangle a b) := subset_closure.trans (hRmc m)
    exact (Set.image_subset_image_iff OnePoint.coe_injective).1 h1
  have hQm_exists : ∀ m, ∃ Q' : TopQuad, (Rm m).IsImageUnder Q' ginv ∧ (Rm m).ConfEquiv Q' :=
    fun m => TopQuad.exists_image_conformal (isOpen_rectangle a b) hginvConf (hRmc m)
  choose Qm hQm_img _hQm_confEquiv using hQm_exists
  have hQm_dom_eq : ∀ m, (Qm m).dom = ginv '' (Rm m).dom := fun m => (hQm_img m).1
  have hQm_vert_eq : ∀ m i, (Qm m).vert i = OnePoint.map ginv ((Rm m).vert i) :=
    fun m i => (hQm_img m).2 i
  have hQm_sub_Q : ∀ m, (Qm m).dom ⊆ Q.dom := by
    intro m
    rw [hQm_dom_eq m, ← hginvConf.2.2]
    exact image_mono (hRm_sub m)
  have hQm_closure_Q : ∀ m, closure (toExt (Qm m).dom) ⊆ toExt Q.dom := by
    intro m
    rw [hQm_dom_eq m]
    exact closure_toExt_image_subset hginvConf.1.continuousOn (hRmc m) hginvConf.2.2.le
  have hRm_closure_sub : ∀ m, closure (Rm m).dom ⊆ rectangle a b := by
    intro m
    have h1 : toExt (closure (Rm m).dom) ⊆ toExt (rectangle a b) := by
      rw [← closure_toExt_of_isBounded (hRm_bdd m)]; exact hRmc m
    exact (Set.image_subset_image_iff OnePoint.coe_injective).1 h1
  have hRmExt : ∀ m, IsHomeoExtension (fun z => z + cm m) (rectQuad (ha' m) (hb' m)).dom (Rm m).dom
      (OnePoint.map (fun z => z + cm m)) := by
    intro m
    have hfo : IsOpen ((fun z => z + cm m) '' (rectQuad (ha' m) (hb' m)).dom) := by
      rw [← hRm_dom_eq m]; exact (Rm m).isTopQuad.1.1
    have h := (image_isJordanDomain_of_open isOpen_univ (htrans_conf (cm m)).1.continuousOn
      (htrans_conf (cm m)).2.1 (hUsub m) hfo).2.1
    rw [hRm_dom_eq m]
    exact h
  have hQmExt : ∀ m, IsHomeoExtension ginv (Rm m).dom (Qm m).dom (OnePoint.map ginv) := by
    intro m
    have hfo : IsOpen (ginv '' (Rm m).dom) := by
      rw [← hQm_dom_eq m]; exact (Qm m).isTopQuad.1.1
    have h := (image_isJordanDomain_of_open (isOpen_rectangle a b) hginvConf.1.continuousOn
      hginvConf.2.1 (hRmc m) hfo).2.1
    rw [hQm_dom_eq m]
    exact h
  -- vertex convergence
  have hQm_vert_formula : ∀ m i, (Qm m).vert i =
      ((ginv (qcl_m_rectVertC (a - 2 * ε m) (b - 2 * ε m) i + cm m) : ℂ) : ExtPlane) := by
    intro m i
    rw [hQm_vert_eq m i, hRm_vert_eq m i, hvertRQ m, qcl_m_rectVert_eq]
    rfl
  have hAm : Tendsto (fun m : ℕ => a - 2 * ε m) atTop (𝓝 a) := by
    have h1 := hεtendsto.const_mul (2 : ℝ)
    simp only [mul_zero] at h1
    simpa using tendsto_const_nhds.sub h1
  have hBm : Tendsto (fun m : ℕ => b - 2 * ε m) atTop (𝓝 b) := by
    have h1 := hεtendsto.const_mul (2 : ℝ)
    simp only [mul_zero] at h1
    simpa using tendsto_const_nhds.sub h1
  have hcmtendsto : Tendsto cm atTop (𝓝 0) := by
    rw [hcmdef]
    have h1 : Tendsto (fun m : ℕ => ((ε m : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) := by
      have h2 : Tendsto (fun m : ℕ => ((ε m : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hεtendsto
      rwa [Complex.ofReal_zero] at h2
    simpa using h1.mul_const (1 + I)
  have hAmC : Tendsto (fun m : ℕ => ((a - 2 * ε m : ℝ) : ℂ)) atTop (𝓝 (a : ℂ)) :=
    (Complex.continuous_ofReal.tendsto a).comp hAm
  have hBmC : Tendsto (fun m : ℕ => ((b - 2 * ε m : ℝ) : ℂ)) atTop (𝓝 (b : ℂ)) :=
    (Complex.continuous_ofReal.tendsto b).comp hBm
  have hcorner_tendsto : ∀ i, Tendsto (fun m => qcl_m_rectVertC (a - 2 * ε m) (b - 2 * ε m) i)
      atTop (𝓝 (qcl_m_rectVertC a b i)) := by
    intro i
    fin_cases i
    · show Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (0 : ℂ))
      exact tendsto_const_nhds
    · show Tendsto (fun m => ((a - 2 * ε m : ℝ) : ℂ)) atTop (𝓝 (a : ℂ))
      exact hAmC
    · show Tendsto (fun m => ((a - 2 * ε m : ℝ) : ℂ) + ((b - 2 * ε m : ℝ) : ℂ) * I) atTop
        (𝓝 ((a : ℂ) + (b : ℂ) * I))
      exact hAmC.add (hBmC.mul_const I)
    · show Tendsto (fun m => ((b - 2 * ε m : ℝ) : ℂ) * I) atTop (𝓝 ((b : ℂ) * I))
      exact hBmC.mul_const I
  have hcorner_shift_tendsto : ∀ i, Tendsto
      (fun m => qcl_m_rectVertC (a - 2 * ε m) (b - 2 * ε m) i + cm m) atTop
      (𝓝 (qcl_m_rectVertC a b i)) := by
    intro i
    simpa using (hcorner_tendsto i).add hcmtendsto
  have hεlt_a : ∀ m, ε m < a := fun m => by linarith [hεpos m, hε2 m, min_le_left a b]
  have hεlt_b : ∀ m, ε m < b := fun m => by linarith [hεpos m, hε2 m, min_le_right a b]
  have hcorner_mem : ∀ m i, qcl_m_rectVertC (a - 2 * ε m) (b - 2 * ε m) i + cm m ∈ rectangle a b := by
    intro m i
    fin_cases i <;>
      simp [qcl_m_rectVertC, rectangle, hcmre, hcmim] <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hεpos m, hεlt_a m, hεlt_b m]
  have hvert_tendsto : ∀ i, Tendsto (fun m => (Qm m).vert i) atTop (𝓝 (Q.vert i)) := by
    intro i
    have hmemrect : qcl_m_rectVertC a b i ∈ closure (rectangle a b) := by
      rw [closure_rectangle_eq_reProdIm ha hb]
      fin_cases i <;> simp [qcl_m_rectVertC, mem_reProdIm] <;>
        refine ⟨?_, ?_⟩ <;> linarith [ha.le, hb.le]
    have hlimval : (g0 (qcl_m_rectVertC a b i) : ExtPlane) = Q.vert i := by
      rw [hg0eq _ hmemrect, ← qcl_m_rectVert_eq, hGinv_vert]
    have key : Tendsto (fun m => g0 (qcl_m_rectVertC (a - 2 * ε m) (b - 2 * ε m) i + cm m)) atTop
        (𝓝 (g0 (qcl_m_rectVertC a b i))) :=
      qcl_m_tendsto_of_continuousOn hg0cont hmemrect (fun m => subset_closure (hcorner_mem m i))
        (hcorner_shift_tendsto i)
    have heq : ∀ m, ginv (qcl_m_rectVertC (a - 2 * ε m) (b - 2 * ε m) i + cm m) =
        g0 (qcl_m_rectVertC (a - 2 * ε m) (b - 2 * ε m) i + cm m) :=
      fun m => (hg0eqOn (hcorner_mem m i)).symm
    have key2 : Tendsto (fun m => ginv (qcl_m_rectVertC (a - 2 * ε m) (b - 2 * ε m) i + cm m))
        atTop (𝓝 (g0 (qcl_m_rectVertC a b i))) := by
      simpa only [heq] using key
    have key3 := (OnePoint.continuous_coe.tendsto (g0 (qcl_m_rectVertC a b i))).comp key2
    simp only [Function.comp_def] at key3
    rw [hlimval] at key3
    have heq2 : (fun m => ((ginv (qcl_m_rectVertC (a - 2 * ε m) (b - 2 * ε m) i + cm m) : ℂ) :
        ExtPlane)) = fun m => (Qm m).vert i := funext fun m => (hQm_vert_formula m i).symm
    rwa [heq2] at key3
  -- frontier and side transport formulas
  have hfrontierRm : ∀ m, frontier (Rm m).dom =
      (fun z => z + cm m) '' frontier ((rectQuad (ha' m) (hb' m)).dom) := fun m =>
    qcl_m_frontier_eq_image (rectQuad (ha' m) (hb' m)).isTopQuad.1.1 (Rm m).isTopQuad.1.1
      (isBounded_rectangle _ _) ((htrans_conf (cm m)).1.continuousOn.mono (subset_univ _))
      ((htrans_conf (cm m)).2.1.mono (subset_univ _)) (hRm_dom_eq m).symm
  have hfrontierQm : ∀ m, frontier (Qm m).dom = ginv '' frontier (Rm m).dom := fun m =>
    qcl_m_frontier_eq_image (Rm m).isTopQuad.1.1 (Qm m).isTopQuad.1.1 (hRm_bdd m)
      (hginvConf.1.continuousOn.mono (hRm_closure_sub m))
      (hginvConf.2.1.mono (hRm_closure_sub m)) (hQm_dom_eq m).symm
  -- the geometric closeness estimate: a frontier point of the shrunk rectangle is within `ε m`
  -- of the frontier of the full rectangle, after the shift
  have hfrontier_close : ∀ m, ∀ w ∈ frontier (rectangle (a - 2 * ε m) (b - 2 * ε m)),
      ∃ u ∈ frontier (rectangle a b), dist (w + cm m) u ≤ ε m := by
    intro m w hw
    rw [frontier_rectangle (ha' m) (hb' m)] at hw
    rw [frontier_rectangle ha hb]
    rcases hw with hw | hw
    · rw [mem_reProdIm] at hw
      obtain ⟨hw1, hw2⟩ := hw
      rcases hw2 with hw2 | hw2
      · set u : ℂ := ((w.re + ε m : ℝ) : ℂ) with hudef
        have hure : u.re = w.re + ε m := by rw [hudef]; simp
        have huim : u.im = 0 := by rw [hudef]; simp
        refine ⟨u, Or.inl ?_, ?_⟩
        · rw [mem_reProdIm]
          refine ⟨⟨by rw [hure]; linarith [hw1.1, hεpos m],
            by rw [hure]; linarith [hw1.2, hεpos m]⟩, Or.inl huim⟩
        · have hre : (w + cm m).re = u.re := by rw [Complex.add_re, hcmre, hure]
          rw [qcl_m_dist_of_re_eq hre, Complex.add_im, hcmim, huim, hw2]
          simp [abs_of_nonneg (hεpos m).le]
      · set u : ℂ := ((w.re + ε m : ℝ) : ℂ) + (b : ℝ) * I with hudef
        have hure : u.re = w.re + ε m := by rw [hudef]; simp
        have huim : u.im = b := by rw [hudef]; simp
        refine ⟨u, Or.inl ?_, ?_⟩
        · rw [mem_reProdIm]
          refine ⟨⟨by rw [hure]; linarith [hw1.1, hεpos m],
            by rw [hure]; linarith [hw1.2, hεpos m]⟩, Or.inr huim⟩
        · have hre : (w + cm m).re = u.re := by rw [Complex.add_re, hcmre, hure]
          rw [qcl_m_dist_of_re_eq hre, Complex.add_im, hcmim, huim, hw2]
          have hval : b - 2 * ε m + ε m - b = -ε m := by ring
          rw [hval, abs_neg, abs_of_nonneg (hεpos m).le]
    · rw [mem_reProdIm] at hw
      obtain ⟨hw1, hw2⟩ := hw
      rcases hw1 with hw1 | hw1
      · set u : ℂ := ((w.im + ε m : ℝ) : ℂ) * I with hudef
        have hure : u.re = 0 := by rw [hudef]; simp
        have huim : u.im = w.im + ε m := by rw [hudef]; simp
        refine ⟨u, Or.inr ?_, ?_⟩
        · rw [mem_reProdIm]
          refine ⟨Or.inl hure, by rw [huim]; linarith [hw2.1, hεpos m],
            by rw [huim]; linarith [hw2.2, hεpos m]⟩
        · have him : (w + cm m).im = u.im := by rw [Complex.add_im, hcmim, huim]
          rw [qcl_m_dist_of_im_eq him, Complex.add_re, hcmre, hure, hw1]
          simp [abs_of_nonneg (hεpos m).le]
      · set u : ℂ := ((a : ℝ) : ℂ) + ((w.im + ε m : ℝ) : ℂ) * I with hudef
        have hure : u.re = a := by rw [hudef]; simp
        have huim : u.im = w.im + ε m := by rw [hudef]; simp
        refine ⟨u, Or.inr ?_, ?_⟩
        · rw [mem_reProdIm]
          refine ⟨Or.inr hure, by rw [huim]; linarith [hw2.1, hεpos m],
            by rw [huim]; linarith [hw2.2, hεpos m]⟩
        · have him : (w + cm m).im = u.im := by rw [Complex.add_im, hcmim, huim]
          rw [qcl_m_dist_of_im_eq him, Complex.add_re, hcmre, hure, hw1]
          have hval : a - 2 * ε m + ε m - a = -ε m := by ring
          rw [hval, abs_neg, abs_of_nonneg (hεpos m).le]
  -- uniform continuity of `g0` on the closed rectangle
  have hg0unif : UniformContinuousOn g0 (closure (rectangle a b)) :=
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (isBounded_rectangle a b).closure).uniformContinuousOn_of_continuous hg0cont
  -- the frontier clause
  have hfrontier_clause : ∀ δ > 0, ∀ᶠ m in atTop, ∀ z ∈ frontier (Qm m).dom,
      infDist z (frontier Q.dom) < δ := by
    intro δ hδ
    obtain ⟨η, hη, hηspec⟩ := uniformContinuousOn_iff.1 hg0unif δ hδ
    filter_upwards [hεtendsto.eventually_lt_const hη] with m hεm z hz
    rw [hfrontierQm m] at hz
    obtain ⟨w', hw', rfl⟩ := hz
    have hw'sub : w' ∈ rectangle a b := hRm_closure_sub m (frontier_subset_closure hw')
    rw [hfrontierRm m, hdomRQ m] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    dsimp only at hw'sub ⊢
    obtain ⟨u, hu, hdu⟩ := hfrontier_close m w hw
    rw [← hg0eqOn hw'sub]
    have hple : infDist (g0 (w + cm m)) (frontier Q.dom) ≤ dist (g0 (w + cm m)) (g0 u) :=
      infDist_le_dist_of_mem (by rw [hfrontierQ]; exact ⟨u, hu, rfl⟩)
    have hlt : dist (g0 (w + cm m)) (g0 u) < δ :=
      hηspec (w + cm m) (subset_closure hw'sub) u (frontier_subset_closure hu)
        (lt_of_le_of_lt hdu hεm)
    linarith
  -- side transport formulas
  have hQm_bdd : ∀ m, Bornology.IsBounded (Qm m).dom := fun m => hQb.subset (hQm_sub_Q m)
  have hRm_sideC : ∀ m i, (Rm m).sideC i =
      (fun z => z + cm m) '' (rectQuad (ha' m) (hb' m)).sideC i := by
    intro m i
    have hRmconf : IsConformalOnto (fun z => z + cm m) (rectQuad (ha' m) (hb' m)).dom (Rm m).dom :=
      ⟨(htrans_conf (cm m)).1.mono (subset_univ _), (htrans_conf (cm m)).2.1.mono (subset_univ _),
        (hRm_dom_eq m).symm⟩
    have h1 := TopQuad.image_side (Q := rectQuad (ha' m) (hb' m)) (V := (Rm m).dom)
      (Rm m).isTopQuad.1.1 hRmconf (hRmExt m) i
    rw [← hRm_vert_eq m i, ← hRm_vert_eq m (i + 1), ← hRm_vert_eq m (i + 2),
      ← (Rm m).side_eq_boundaryArc i] at h1
    have h2 : (rectQuad (ha' m) (hb' m)).side i = toExt ((rectQuad (ha' m) (hb' m)).sideC i) :=
      qcl_m_side_eq_toExt_sideC (isBounded_rectangle _ _) i
    have h3 : (Rm m).side i = toExt ((Rm m).sideC i) := qcl_m_side_eq_toExt_sideC (hRm_bdd m) i
    rw [h2, h3] at h1
    have h4 : ∀ S : Set ℂ, OnePoint.map (fun z => z + cm m) '' toExt S =
        toExt ((fun z => z + cm m) '' S) := by
      intro S; simp only [toExt, image_image]; rfl
    rw [h4] at h1
    exact ((Set.image_eq_image OnePoint.coe_injective).1 h1).symm
  have hQm_sideC : ∀ m i, (Qm m).sideC i = ginv '' (Rm m).sideC i := by
    intro m i
    have hQmconf : IsConformalOnto ginv (Rm m).dom (Qm m).dom :=
      ⟨hginvConf.1.mono (hRm_sub m), hginvConf.2.1.mono (hRm_sub m), (hQm_dom_eq m).symm⟩
    have h1 := TopQuad.image_side (Q := Rm m) (V := (Qm m).dom) (Qm m).isTopQuad.1.1 hQmconf
      (hQmExt m) i
    rw [← hQm_vert_eq m i, ← hQm_vert_eq m (i + 1), ← hQm_vert_eq m (i + 2),
      ← (Qm m).side_eq_boundaryArc i] at h1
    have h2 : (Rm m).side i = toExt ((Rm m).sideC i) := qcl_m_side_eq_toExt_sideC (hRm_bdd m) i
    have h3 : (Qm m).side i = toExt ((Qm m).sideC i) := qcl_m_side_eq_toExt_sideC (hQm_bdd m) i
    rw [h2, h3] at h1
    have h4 : ∀ S : Set ℂ, OnePoint.map ginv '' toExt S = toExt (ginv '' S) := by
      intro S; simp only [toExt, image_image]; rfl
    rw [h4] at h1
    exact ((Set.image_eq_image OnePoint.coe_injective).1 h1).symm
  -- geometric side-closeness: a point of side `i` of the shrunk rectangle is within `ε m`
  -- (after the shift) of the *same* side `i` of the full rectangle
  have hside_close : ∀ m i, ∀ w ∈ (rectQuad (ha' m) (hb' m)).sideC i,
      ∃ u ∈ (rectQuad ha hb).sideC i, dist (w + cm m) u ≤ ε m := by
    intro m i
    obtain ⟨s0, s1, s2, s3⟩ := qcl_m_rectQuad_sideC (ha' m) (hb' m)
    obtain ⟨t0, t1, t2, t3⟩ := qcl_m_rectQuad_sideC ha hb
    obtain ⟨iv, hiv⟩ := i
    interval_cases iv <;> intro w hw
    · change w ∈ (rectQuad (ha' m) (hb' m)).sideC 0 at hw
      change ∃ u ∈ (rectQuad ha hb).sideC 0, dist (w + cm m) u ≤ ε m
      simp only [s0, mem_reProdIm, mem_singleton_iff] at hw
      obtain ⟨hw1, hw2⟩ := hw
      set u : ℂ := ((w.re + ε m : ℝ) : ℂ) with hudef
      have hure : u.re = w.re + ε m := by rw [hudef]; simp
      have huim : u.im = 0 := by rw [hudef]; simp
      refine ⟨u, ?_, ?_⟩
      · simp only [t0, mem_reProdIm, mem_singleton_iff]
        exact ⟨⟨by rw [hure]; linarith [hw1.1, hεpos m], by rw [hure]; linarith [hw1.2, hεpos m]⟩,
          huim⟩
      · have hre : (w + cm m).re = u.re := by rw [Complex.add_re, hcmre, hure]
        rw [qcl_m_dist_of_re_eq hre, Complex.add_im, hcmim, huim, hw2]
        simp [abs_of_nonneg (hεpos m).le]
    · change w ∈ (rectQuad (ha' m) (hb' m)).sideC 1 at hw
      change ∃ u ∈ (rectQuad ha hb).sideC 1, dist (w + cm m) u ≤ ε m
      simp only [s1, mem_reProdIm, mem_singleton_iff] at hw
      obtain ⟨hw1, hw2⟩ := hw
      set u : ℂ := ((a : ℝ) : ℂ) + ((w.im + ε m : ℝ) : ℂ) * I with hudef
      have hure : u.re = a := by rw [hudef]; simp
      have huim : u.im = w.im + ε m := by rw [hudef]; simp
      refine ⟨u, ?_, ?_⟩
      · simp only [t1, mem_reProdIm, mem_singleton_iff]
        exact ⟨hure, by rw [huim]; linarith [hw2.1, hεpos m],
          by rw [huim]; linarith [hw2.2, hεpos m]⟩
      · have him : (w + cm m).im = u.im := by rw [Complex.add_im, hcmim, huim]
        rw [qcl_m_dist_of_im_eq him, Complex.add_re, hcmre, hure, hw1]
        have hval : a - 2 * ε m + ε m - a = -ε m := by ring
        rw [hval, abs_neg, abs_of_nonneg (hεpos m).le]
    · change w ∈ (rectQuad (ha' m) (hb' m)).sideC 2 at hw
      change ∃ u ∈ (rectQuad ha hb).sideC 2, dist (w + cm m) u ≤ ε m
      simp only [s2, mem_reProdIm, mem_singleton_iff] at hw
      obtain ⟨hw1, hw2⟩ := hw
      set u : ℂ := ((w.re + ε m : ℝ) : ℂ) + ((b : ℝ) : ℂ) * I with hudef
      have hure : u.re = w.re + ε m := by rw [hudef]; simp
      have huim : u.im = b := by rw [hudef]; simp
      refine ⟨u, ?_, ?_⟩
      · simp only [t2, mem_reProdIm, mem_singleton_iff]
        exact ⟨⟨by rw [hure]; linarith [hw1.1, hεpos m], by rw [hure]; linarith [hw1.2, hεpos m]⟩,
          huim⟩
      · have hre : (w + cm m).re = u.re := by rw [Complex.add_re, hcmre, hure]
        rw [qcl_m_dist_of_re_eq hre, Complex.add_im, hcmim, huim, hw2]
        have hval : b - 2 * ε m + ε m - b = -ε m := by ring
        rw [hval, abs_neg, abs_of_nonneg (hεpos m).le]
    · change w ∈ (rectQuad (ha' m) (hb' m)).sideC 3 at hw
      change ∃ u ∈ (rectQuad ha hb).sideC 3, dist (w + cm m) u ≤ ε m
      simp only [s3, mem_reProdIm, mem_singleton_iff] at hw
      obtain ⟨hw1, hw2⟩ := hw
      set u : ℂ := ((w.im + ε m : ℝ) : ℂ) * I with hudef
      have hure : u.re = 0 := by rw [hudef]; simp
      have huim : u.im = w.im + ε m := by rw [hudef]; simp
      refine ⟨u, ?_, ?_⟩
      · simp only [t3, mem_reProdIm, mem_singleton_iff]
        exact ⟨hure, by rw [huim]; linarith [hw2.1, hεpos m],
          by rw [huim]; linarith [hw2.2, hεpos m]⟩
      · have him : (w + cm m).im = u.im := by rw [Complex.add_im, hcmim, huim]
        rw [qcl_m_dist_of_im_eq him, Complex.add_re, hcmre, hure, hw1]
        simp [abs_of_nonneg (hεpos m).le]
  -- the side clause
  have hside_clause : ∀ i : Fin 4, ∀ δ > 0, ∀ᶠ m in atTop, ∀ z ∈ (Qm m).sideC i,
      infDist z (Q.sideC i) < δ := by
    intro i δ hδ
    obtain ⟨η, hη, hηspec⟩ := uniformContinuousOn_iff.1 hg0unif δ hδ
    filter_upwards [hεtendsto.eventually_lt_const hη] with m hεm z hz
    rw [hQm_sideC m i, hRm_sideC m i] at hz
    obtain ⟨w', hw', rfl⟩ := hz
    obtain ⟨w, hw, rfl⟩ := hw'
    dsimp only
    have hmem : w + cm m ∈ (Rm m).sideC i := (hRm_sideC m i).symm ▸ ⟨w, hw, rfl⟩
    have hw'sub : w + cm m ∈ rectangle a b :=
      hRm_closure_sub m (qcl_m_sideC_subset_closure (hRm_bdd m) i hmem)
    obtain ⟨u, hu, hdu⟩ := hside_close m i w hw
    rw [← hg0eqOn hw'sub]
    have hple : infDist (g0 (w + cm m)) (Q.sideC i) ≤ dist (g0 (w + cm m)) (g0 u) :=
      infDist_le_dist_of_mem (by rw [hQsideC i]; exact ⟨u, hu, rfl⟩)
    have hlt : dist (g0 (w + cm m)) (g0 u) < δ :=
      hηspec (w + cm m) (subset_closure hw'sub) u
        (qcl_m_sideC_subset_closure (isBounded_rectangle a b) i hu) (lt_of_le_of_lt hdu hεm)
    linarith
  exact ⟨Qm, ⟨hQm_sub_Q, hvert_tendsto, hfrontier_clause, hside_clause⟩, hQm_closure_Q⟩




/-- **M2.** If `Qₘ → Q` from inside with closures in `Q.dom`, `f` is a homeomorphism on
`D ⊇ closure Q.dom`, `fₙ → f` locally uniformly, and `Qₘ' m n` is the image of `Qₘ m` under
`fₙ`, then for a suitable diagonal selection `n = φ m`, `Qₘ' m (φ m) → Q'` from inside. -/
theorem qcl_m_exists_image_tendsFromInside {D : Set ℂ} (hDo : IsOpen D) {fn : ℕ → ℂ → ℂ}
    {f : ℂ → ℂ} (hfn : ∀ n, ContinuousOn (fn n) D) (hfni : ∀ n, InjOn (fn n) D)
    (hlim : TendstoLocallyUniformlyOn fn f atTop D) (hfc : ContinuousOn f D) (hfi : InjOn f D)
    {Q Q' : TopQuad} (hQ : closure (toExt Q.dom) ⊆ toExt D) (hQ' : Q.IsImageUnder Q' f)
    {Qm : ℕ → TopQuad} (hQm : TopQuad.TendsFromInside Qm Q)
    (hQmc : ∀ m, closure (toExt (Qm m).dom) ⊆ toExt Q.dom)
    {Qm' : ℕ → ℕ → TopQuad} (hQm' : ∀ m n, (Qm m).IsImageUnder (Qm' m n) (fn n)) :
    ∃ φ : ℕ → ℕ, TopQuad.TendsFromInside (fun m => Qm' m (φ m)) Q' := by
  -- Preliminaries: boundedness, compactness, uniform continuity/convergence on `C := closure Q.dom`.
  have hQdomD : Q.dom ⊆ D := by
    intro z hz
    have h1 := hQ (subset_closure (mem_image_of_mem _ hz))
    exact coe_mem_toExt_iff.mp h1
  have hextInfD : extInf ∉ toExt D := by
    rintro ⟨d, -, hd⟩
    exact OnePoint.coe_ne_infty d hd
  have hQb : Bornology.IsBounded Q.dom :=
    isBounded_of_extInf_notMem_closure_toExt (fun h => hextInfD (hQ h))
  have hQclosD : closure Q.dom ⊆ D := by
    intro z hz
    have himg := image_closure_subset_closure_image
      OnePoint.continuous_coe (s := Q.dom)
    have h1 : (z : ExtPlane) ∈ closure (toExt Q.dom) := himg (mem_image_of_mem _ hz)
    exact coe_mem_toExt_iff.mp (hQ h1)
  have hCcompact : IsCompact (closure Q.dom) := hQb.isCompact_closure
  set C : Set ℂ := closure Q.dom with hCdef
  have hfcC : ContinuousOn f C := hfc.mono hQclosD
  have hfnC : ∀ n, ContinuousOn (fn n) C := fun n => (hfn n).mono hQclosD
  have hfCunif : UniformContinuousOn f C := hCcompact.uniformContinuousOn_of_continuous hfcC
  have hlimC : TendstoUniformlyOn fn f atTop C :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hDo).1 hlim C hQclosD hCcompact
  -- Vertices are always finite (never `extInf`), since the quadrilaterals in play are bounded.
  have hvertfin : ∀ {R : TopQuad}, closure (toExt R.dom) ⊆ toExt D → ∀ i,
      ∃ c : ℂ, R.vert i = (c : ExtPlane) := by
    intro R hRD i
    have hmem : R.vert i ∈ frontier (toExt R.dom) := R.isTopQuad.2.1 i
    have hmemD : R.vert i ∈ toExt D := hRD (frontier_subset_closure hmem)
    induction hv : R.vert i using OnePoint.rec with
    | infty => rw [hv] at hmemD; exact absurd hmemD hextInfD
    | coe c => exact ⟨c, rfl⟩
  have hQmD : ∀ m, closure (toExt (Qm m).dom) ⊆ toExt D :=
    fun m => (hQmc m).trans (subset_closure.trans hQ)
  choose cQ hcQ using hvertfin hQ
  choose cQm hcQm using fun m => hvertfin (hQmD m)
  -- `Q'.vert i` and `(Qm' m n).vert i` are automatically finite, via `OnePoint.map`'s formula.
  have hcQ' : ∀ i, Q'.vert i = ((f (cQ i) : ℂ) : ExtPlane) := by
    intro i
    rw [hQ'.2 i, hcQ i]
    rfl
  have hcQm' : ∀ m n i, (Qm' m n).vert i = (((fn n) (cQm m i) : ℂ) : ExtPlane) := by
    intro m n i
    rw [(hQm' m n).2 i, hcQm m i]
    rfl
  have hQdomopen : IsOpen Q.dom := Q.isTopQuad.1.1
  have hQdomne : Q.dom.Nonempty := Q.isTopQuad.1.2.1.1
  have hQ'dom : Q'.dom = f '' Q.dom := hQ'.1
  have hQ'domopen : IsOpen Q'.dom := by
    rw [hQ'dom]; exact isOpen_image_of_continuousOn_injOn_of_subset hDo hfc hfi hQdomD hQdomopen
  have hfrQne : (frontier Q.dom).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, ← isClopen_iff_frontier_eq_empty, isClopen_iff] at h
    rcases h with h | h
    · exact hQdomne.ne_empty h
    · rw [h] at hQb
      exact NormedSpace.unbounded_univ ℝ ℂ hQb
  have hfrQcompact : IsCompact (frontier Q.dom) :=
    hCcompact.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hfrQDsub : frontier Q.dom ⊆ D := frontier_subset_closure.trans hQclosD
  -- `dom ⊆`, for each `m`: a suitable threshold on `n`.
  have hdomEv : ∀ m : ℕ, ∀ᶠ n in atTop, (Qm' m n).dom ⊆ Q'.dom := by
    intro m
    set Km : Set ℂ := closure (Qm m).dom with hKmdef
    have hKmQdom : Km ⊆ Q.dom := by
      intro z hz
      have himg := image_closure_subset_closure_image OnePoint.continuous_coe (s := (Qm m).dom)
      have h1 : (z : ExtPlane) ∈ closure (toExt (Qm m).dom) := himg (mem_image_of_mem _ hz)
      exact coe_mem_toExt_iff.mp (hQmc m h1)
    have hKmbdd : Bornology.IsBounded (Qm m).dom := hQb.subset (hQm.1 m)
    have hKmcompact : IsCompact Km := hKmbdd.isCompact_closure
    have hKmDsub : Km ⊆ D := hKmQdom.trans hQdomD
    have hKmdisjfr : Disjoint Km (frontier Q.dom) := by
      rw [Set.disjoint_left]
      intro z hz hzfr
      exact (disjoint_frontier_iff_isOpen.2 hQdomopen).le_bot ⟨hzfr, hKmQdom hz⟩
    have hfKmcompact : IsCompact (f '' Km) := hKmcompact.image_of_continuousOn (hfc.mono hKmDsub)
    have hffrQcompact : IsCompact (f '' frontier Q.dom) :=
      hfrQcompact.image_of_continuousOn (hfc.mono hfrQDsub)
    have hdisj : ∀ z ∈ Km, 0 < infDist (f z) (f '' frontier Q.dom) := by
      intro z hz
      have hne : (f '' frontier Q.dom).Nonempty := hfrQne.image f
      refine (Metric.infDist_pos_iff_notMem_closure hne).mp ?_
      rw [hffrQcompact.isClosed.closure_eq]
      rintro ⟨w, hwfr, hwz⟩
      have heq := hfi (hKmDsub hz) (hfrQDsub hwfr) hwz.symm
      exact hKmdisjfr.le_bot ⟨heq ▸ hz, hwfr⟩
    obtain ⟨δm, hδmpos, hδm⟩ :
        ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Km, δ ≤ infDist (f z) (f '' frontier Q.dom) := by
      rcases Km.eq_empty_or_nonempty with hKe | hKne
      · exact ⟨1, one_pos, fun z hz => absurd hz (by rw [hKe]; exact notMem_empty z)⟩
      · obtain ⟨z₀, hz₀, hmin⟩ := hKmcompact.exists_isMinOn hKne
          ((Metric.continuous_infDist_pt (f '' frontier Q.dom)).comp_continuousOn
            (hfc.mono hKmDsub))
        exact ⟨infDist (f z₀) (f '' frontier Q.dom), hdisj z₀ hz₀, fun z hz => hmin hz⟩
    have hNev : ∀ᶠ n in atTop, ∀ x ∈ C, dist (f x) (fn n x) < δm / 2 :=
      Metric.tendstoUniformlyOn_iff.1 hlimC (δm / 2) (by linarith)
    filter_upwards [hNev] with n hn
    rw [(hQm' m n).1]
    rintro _ ⟨z, hzQm, rfl⟩
    have hzKm : z ∈ Km := subset_closure hzQm
    have hzC : z ∈ C := subset_closure (hKmQdom hzKm)
    have hfrQ'eq : frontier Q'.dom = f '' frontier Q.dom :=
      qcl_m_frontier_eq_image hQdomopen hQ'domopen hQb hfcC (hfi.mono hQclosD) hQ'dom.symm
    have hdab : dist (fn n z) (f z) < δm / 2 := by rw [dist_comm]; exact hn z hzC
    have hseg : ∀ p ∈ segment ℝ (f z) (fn n z), p ∉ frontier Q'.dom := by
      intro p hp hpfr
      rw [hfrQ'eq] at hpfr
      have hdap : dist p (f z) ≤ dist (fn n z) (f z) := by
        obtain ⟨a, b, ha, hb, hab, hpeq⟩ := hp
        have ha' : a = 1 - b := by linarith
        have hbe : p - f z = b • (fn n z - f z) := by
          rw [← hpeq, ha']; module
        rw [dist_eq_norm, hbe, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb, ← dist_eq_norm]
        nlinarith [dist_nonneg (x := fn n z) (y := f z), ha, hb, hab]
      have h1 : δm / 2 < infDist p (f '' frontier Q.dom) := by
        have h2 := Metric.infDist_le_infDist_add_dist (x := f z) (y := p)
          (s := f '' frontier Q.dom)
        have h3 : δm ≤ infDist (f z) (f '' frontier Q.dom) := hδm z hzKm
        rw [dist_comm] at h2
        linarith [h2, h3, hdap, hdab]
      have h4 : infDist p (f '' frontier Q.dom) = 0 := Metric.infDist_zero_of_mem hpfr
      linarith [h1, h4]
    have haQ'dom : f z ∈ Q'.dom := by rw [hQ'dom]; exact mem_image_of_mem f (hKmQdom hzKm)
    have hclosuresub : closure Q'.dom ∩ segment ℝ (f z) (fn n z) ⊆ Q'.dom := by
      rintro p ⟨hpcl, hpseg⟩
      by_contra hpn
      exact hseg p hpseg ⟨hpcl, by rwa [hQ'domopen.interior_eq]⟩
    have hsegconn : IsPreconnected (segment ℝ (f z) (fn n z)) :=
      (convex_segment (f z) (fn n z)).isPreconnected
    have hsegsub : segment ℝ (f z) (fn n z) ⊆ Q'.dom :=
      hsegconn.subset_of_closure_inter_subset hQ'domopen
        ⟨f z, left_mem_segment ℝ _ _, haQ'dom⟩ hclosuresub
    exact hsegsub (right_mem_segment ℝ _ _)
  -- A single uniform bound per `m`, tight enough for `dom ⊆` and for every other clause via a
  -- triangle-inequality decomposition.
  have hgoodN : ∀ m : ℕ, ∀ᶠ n in atTop,
      (Qm' m n).dom ⊆ Q'.dom ∧ ∀ x ∈ C, dist (fn n x) (f x) < 1 / (m + 1 : ℝ) := by
    intro m
    have hpos : (0:ℝ) < 1 / (m + 1 : ℝ) := by positivity
    refine (hdomEv m).and ?_
    have hev := Metric.tendstoUniformlyOn_iff.1 hlimC (1 / (m + 1 : ℝ)) hpos
    filter_upwards [hev] with n hn x hx
    rw [dist_comm]; exact hn x hx
  choose φ hφ using fun m => (hgoodN m).exists
  have hcQiC : ∀ i, cQ i ∈ C := by
    intro i
    have h1 : (cQ i : ExtPlane) ∈ closure (toExt Q.dom) :=
      hcQ i ▸ frontier_subset_closure (Q.isTopQuad.2.1 i)
    rw [hCdef, OnePoint.isOpenEmbedding_coe.isInducing.closure_eq_preimage_closure_image]
    exact h1
  have hcQmiC : ∀ m i, cQm m i ∈ C := by
    intro m i
    have h1 : (Qm m).vert i ∈ toExt Q.dom :=
      hQmc m (frontier_subset_closure ((Qm m).isTopQuad.2.1 i))
    rw [hcQm m i] at h1
    exact subset_closure (coe_mem_toExt_iff.mp h1)
  -- Reusable per-`m` facts (also needed for the frontier/side clauses below).
  have hKmQdomAll : ∀ m, closure (Qm m).dom ⊆ Q.dom := by
    intro m z hz
    have himg := image_closure_subset_closure_image OnePoint.continuous_coe (s := (Qm m).dom)
    have h1 : (z : ExtPlane) ∈ closure (toExt (Qm m).dom) := himg (mem_image_of_mem _ hz)
    exact coe_mem_toExt_iff.mp (hQmc m h1)
  have hQmdomD : ∀ m, (Qm m).dom ⊆ D := fun m => (hQm.1 m).trans hQdomD
  have hQmclosD : ∀ m, closure (Qm m).dom ⊆ D := fun m => (hKmQdomAll m).trans hQdomD
  have hQmdomopen : ∀ m, IsOpen (Qm m).dom := fun m => (Qm m).isTopQuad.1.1
  have hQmbdd : ∀ m, Bornology.IsBounded (Qm m).dom := fun m => hQb.subset (hQm.1 m)
  have hQmn'domopen : ∀ m n, IsOpen (Qm' m n).dom := by
    intro m n
    rw [(hQm' m n).1]
    exact isOpen_image_of_continuousOn_injOn_of_subset hDo (hfn n) (hfni n) (hQmdomD m)
      (hQmdomopen m)
  have hfrQmn_eq : ∀ m n, frontier (Qm' m n).dom = fn n '' frontier (Qm m).dom := by
    intro m n
    exact qcl_m_frontier_eq_image (hQmdomopen m) (hQmn'domopen m n) (hQmbdd m)
      ((hfn n).mono (hQmclosD m)) ((hfni n).mono (hQmclosD m)) (hQm' m n).1.symm
  have hfrQ'eq : frontier Q'.dom = f '' frontier Q.dom :=
    qcl_m_frontier_eq_image hQdomopen hQ'domopen hQb hfcC (hfi.mono hQclosD) hQ'dom.symm
  refine ⟨φ, (fun m => (hφ m).1), ?_, ?_, ?_⟩
  · -- vertices
    intro i
    have hcQmtendsto : Tendsto (fun m => cQm m i) atTop (𝓝 (cQ i)) := by
      have h1 := hQm.2.1 i
      simp only [hcQm, hcQ] at h1
      exact OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff.mpr h1
    have hfcQmtendsto : Tendsto (fun m => f (cQm m i)) atTop (𝓝 (f (cQ i))) :=
      qcl_m_tendsto_of_continuousOn hfcC (hcQiC i) (hcQmiC · i) hcQmtendsto
    have herrtendsto : Tendsto (fun m => dist (fn (φ m) (cQm m i)) (f (cQm m i))) atTop (𝓝 0) := by
      have hbound : ∀ m, dist (fn (φ m) (cQm m i)) (f (cQm m i)) < 1 / (m + 1 : ℝ) :=
        fun m => (hφ m).2 (cQm m i) (hcQmiC m i)
      have hpos : ∀ m, 0 ≤ dist (fn (φ m) (cQm m i)) (f (cQm m i)) := fun m => dist_nonneg
      have htend0 : Tendsto (fun m : ℕ => 1 / ((m:ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact squeeze_zero hpos (fun m => (hbound m).le) htend0
    have hcoetendsto : Tendsto (fun m => (fn (φ m) (cQm m i) : ExtPlane)) atTop
        (𝓝 ((f (cQ i) : ℂ) : ExtPlane)) := by
      have hCtendsto : Tendsto (fun m => fn (φ m) (cQm m i)) atTop (𝓝 (f (cQ i))) := by
        rw [tendsto_iff_dist_tendsto_zero]
        have heq : ∀ m, dist (fn (φ m) (cQm m i)) (f (cQ i)) ≤
            dist (fn (φ m) (cQm m i)) (f (cQm m i)) + dist (f (cQm m i)) (f (cQ i)) :=
          fun m => dist_triangle _ _ _
        have h2 : Tendsto (fun m => dist (f (cQm m i)) (f (cQ i))) atTop (𝓝 0) := by
          rw [← tendsto_iff_dist_tendsto_zero]; exact hfcQmtendsto
        have h3 : Tendsto (fun m => dist (fn (φ m) (cQm m i)) (f (cQm m i)) +
            dist (f (cQm m i)) (f (cQ i))) atTop (𝓝 0) := by
          simpa using herrtendsto.add h2
        exact squeeze_zero (fun m => dist_nonneg) heq h3
      exact OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff.mp hCtendsto
    have hgoal : Tendsto (fun m => (Qm' m (φ m)).vert i) atTop (𝓝 (Q'.vert i)) := by
      have heq1 : ∀ m, (Qm' m (φ m)).vert i = ((fn (φ m) (cQm m i) : ℂ) : ExtPlane) :=
        fun m => hcQm' m (φ m) i
      have heq2 : Q'.vert i = ((f (cQ i) : ℂ) : ExtPlane) := hcQ' i
      rw [heq2]
      exact hcoetendsto.congr (fun m => (heq1 m).symm)
    exact hgoal
  · -- frontier
    intro ε hεpos
    obtain ⟨η, hηpos, hη⟩ := Metric.uniformContinuousOn_iff.1 hfCunif (ε / 2) (by linarith)
    have hev1 : ∀ᶠ m in atTop, ∀ w ∈ frontier (Qm m).dom, infDist w (frontier Q.dom) < η :=
      hQm.2.2.1 η hηpos
    have htend0 : Tendsto (fun m : ℕ => 1 / ((m:ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hev2 : ∀ᶠ m : ℕ in atTop, 1 / ((m:ℝ) + 1) < ε / 2 :=
      htend0.eventually_lt_const (by linarith)
    filter_upwards [hev1, hev2] with m hm1 hm2
    intro z hz
    rw [hfrQmn_eq m (φ m)] at hz
    obtain ⟨w, hwfr, rfl⟩ := hz
    have hwC : w ∈ C := subset_closure (hKmQdomAll m (frontier_subset_closure hwfr))
    have h1 : infDist w (frontier Q.dom) < η := hm1 w hwfr
    obtain ⟨w', hw'fr, hw'dist⟩ := (Metric.infDist_lt_iff hfrQne).mp h1
    have hw'C : w' ∈ C := frontier_subset_closure hw'fr
    have h2 : dist (f w) (f w') < ε / 2 := hη w hwC w' hw'C hw'dist
    have h3 : dist (fn (φ m) w) (f w) < 1 / ((m:ℝ) + 1) := (hφ m).2 w hwC
    have h4 : dist (fn (φ m) w) (f w') ≤ dist (fn (φ m) w) (f w) + dist (f w) (f w') :=
      dist_triangle _ _ _
    have h5 : dist (fn (φ m) w) (f w') < ε := by linarith [h2, h3, h4, hm2]
    calc infDist (fn (φ m) w) (frontier Q'.dom)
        ≤ dist (fn (φ m) w) (f w') := by
          rw [hfrQ'eq]; exact Metric.infDist_le_dist_of_mem (mem_image_of_mem f hw'fr)
      _ < ε := h5
  · -- sides
    have hQmtoExtD : ∀ m, closure (toExt (Qm m).dom) ⊆ toExt D :=
      fun m => (hQmc m).trans (subset_closure.trans hQ)
    have hQmn'bdd : ∀ m n, Bornology.IsBounded (Qm' m n).dom := by
      intro m n
      rw [(hQm' m n).1]
      exact (((hQmbdd m).isCompact_closure.image_of_continuousOn
        ((hfn n).mono (hQmclosD m))).isBounded).subset (image_mono subset_closure)
    have hQ'bdd : Bornology.IsBounded Q'.dom := by
      rw [hQ'dom]
      exact (hCcompact.image_of_continuousOn hfcC).isBounded.subset (image_mono subset_closure)
    have hsideQmn_eq : ∀ m n i, (Qm' m n).sideC i = fn n '' (Qm m).sideC i := by
      intro m n i
      exact qcl_m_sideC_eq_image hDo (hfn n) (hfni n) (hQmbdd m) (hQmn'bdd m n) (hQmtoExtD m)
        (hQm' m n).1.symm (hQm' m n).2 i
    have hsideQ'_eq : ∀ i, Q'.sideC i = f '' Q.sideC i :=
      fun i => qcl_m_sideC_eq_image hDo hfc hfi hQb hQ'bdd hQ hQ'dom.symm hQ'.2 i
    have hsideQne : ∀ i, (Q.sideC i).Nonempty := by
      intro i
      have h1 : Q.vert i ∈ Q.side i := ⟨Q.isTopQuad.2.1 i, Or.inl rfl⟩
      rw [qcl_m_side_eq_toExt_sideC hQb i] at h1
      obtain ⟨c, hc, -⟩ := h1
      exact ⟨c, hc⟩
    intro i ε hεpos
    obtain ⟨η, hηpos, hη⟩ := Metric.uniformContinuousOn_iff.1 hfCunif (ε / 2) (by linarith)
    have hev1 : ∀ᶠ m in atTop, ∀ w ∈ (Qm m).sideC i, infDist w (Q.sideC i) < η :=
      hQm.2.2.2 i η hηpos
    have htend0 : Tendsto (fun m : ℕ => 1 / ((m:ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hev2 : ∀ᶠ m : ℕ in atTop, 1 / ((m:ℝ) + 1) < ε / 2 :=
      htend0.eventually_lt_const (by linarith)
    filter_upwards [hev1, hev2] with m hm1 hm2
    intro z hz
    rw [hsideQmn_eq m (φ m) i] at hz
    obtain ⟨w, hwside, rfl⟩ := hz
    have hwC : w ∈ C := subset_closure (hKmQdomAll m (qcl_m_sideC_subset_closure (hQmbdd m) i hwside))
    have h1 : infDist w (Q.sideC i) < η := hm1 w hwside
    obtain ⟨w', hw'side, hw'dist⟩ := (Metric.infDist_lt_iff (hsideQne i)).mp h1
    have hw'C : w' ∈ C := qcl_m_sideC_subset_closure hQb i hw'side
    have h2 : dist (f w) (f w') < ε / 2 := hη w hwC w' hw'C hw'dist
    have h3 : dist (fn (φ m) w) (f w) < 1 / ((m:ℝ) + 1) := (hφ m).2 w hwC
    have h4 : dist (fn (φ m) w) (f w') ≤ dist (fn (φ m) w) (f w) + dist (f w) (f w') :=
      dist_triangle _ _ _
    have h5 : dist (fn (φ m) w) (f w') < ε := by linarith [h2, h3, h4, hm2]
    calc infDist (fn (φ m) w) (Q'.sideC i)
        ≤ dist (fn (φ m) w) (f w') := by
          rw [hsideQ'_eq]; exact Metric.infDist_le_dist_of_mem (mem_image_of_mem f hw'side)
      _ < ε := h5

/-- **M3.** `M(f(Q)) ≤ K M(Q)` for the limit map of a locally uniformly convergent sequence of
`K`-q.c. maps. -/
theorem qcl_m_modulus_le {D : Set ℂ} (hDo : IsOpen D) {K : ℝ} {fn : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hqc : ∀ n, IsKQC (fn n) D K) (hlim : TendstoLocallyUniformlyOn fn f atTop D)
    (hfc : ContinuousOn f D) (hfi : InjOn f D) {Q Q' : TopQuad}
    (hQ : closure (toExt Q.dom) ⊆ toExt D) (hQ' : Q.IsImageUnder Q' f) :
    Q'.modulus ≤ K * Q.modulus := by
  have hextInfD : extInf ∉ toExt D := by rintro ⟨d, -, hd⟩; exact OnePoint.coe_ne_infty d hd
  have hQb : Bornology.IsBounded Q.dom :=
    isBounded_of_extInf_notMem_closure_toExt (fun h => hextInfD (hQ h))
  obtain ⟨Qm, hQm, hQmc⟩ := qcl_m_exists_tendsFromInside Q hQb
  choose Qm' hQm' hmod using
    fun m n => (hqc n).2.2.2 (Qm m) ((hQmc m).trans (subset_closure.trans hQ))
  obtain ⟨φ, hφ⟩ := qcl_m_exists_image_tendsFromInside hDo (fun n => (hqc n).2.2.1.1)
    (fun n => (hqc n).2.2.1.2.1) hlim hfc hfi hQ hQ' hQm hQmc hQm'
  have hQ'b : Bornology.IsBounded Q'.dom := by
    have hQdomD : Q.dom ⊆ D :=
      fun z hz => coe_mem_toExt_iff.mp (hQ (subset_closure (mem_image_of_mem _ hz)))
    have hQclosD : closure Q.dom ⊆ D := by
      intro z hz
      have himg := image_closure_subset_closure_image OnePoint.continuous_coe (s := Q.dom)
      exact coe_mem_toExt_iff.mp (hQ (himg (mem_image_of_mem _ hz)))
    have hCcompact : IsCompact (closure Q.dom) := hQb.isCompact_closure
    rw [hQ'.1]
    exact (hCcompact.image_of_continuousOn (hfc.mono hQclosD)).isBounded.subset
      (image_mono subset_closure)
  have h1 : Tendsto (fun m => (Qm m).modulus) atTop (𝓝 Q.modulus) :=
    thm4_8_modulus_continuous hQb hQm
  have h2 : Tendsto (fun m => (Qm' m (φ m)).modulus) atTop (𝓝 Q'.modulus) :=
    thm4_8_modulus_continuous hQ'b hφ
  have h3 : Tendsto (fun m => K * (Qm m).modulus) atTop (𝓝 (K * Q.modulus)) := h1.const_mul K
  exact le_of_tendsto_of_tendsto' h2 h3 (fun m => hmod m (φ m))



/-! ### Theorem 8.2 — helpers of piece F -/

/-- **F1.** A continuous injective map on an open set is a homeomorphism onto its (open) image:
the inverse is continuous because `f` is an open map (`isOpen_image_of_continuousOn_injOn`). -/
theorem qcl_f_isHomeomorphOnto_of_injOn {f : ℂ → ℂ} {D : Set ℂ} (hDo : IsOpen D)
    (hfc : ContinuousOn f D) (hfi : InjOn f D) : IsHomeomorphOnto f D (f '' D) := by
  refine ⟨hfc, hfi, rfl, ?_⟩
  have hleft : ∀ z ∈ D, Function.invFunOn f D (f z) = z := fun z hz => hfi.leftInvOn_invFunOn hz
  rintro _ ⟨z, hz, rfl⟩
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set V : Set ℂ := D ∩ ball z ε with hVdef
  have hVo : IsOpen V := hDo.inter isOpen_ball
  have hzV : z ∈ V := ⟨hz, mem_ball_self hε⟩
  have hVD : V ⊆ D := inter_subset_left
  have hfVo : IsOpen (f '' V) :=
    isOpen_image_of_continuousOn_injOn hVo (hfc.mono hVD) (hfi.mono hVD)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hfVo (f z) (mem_image_of_mem f hzV)
  refine ⟨δ, hδ, ?_⟩
  rintro _ ⟨z', hz', rfl⟩ hdist
  obtain ⟨z'', hz''V, hz''eq⟩ := hball hdist
  have hz'' : z'' = z' := hfi (hVD hz''V) hz' hz''eq
  rw [hleft z' hz', hleft z hz]
  rw [← hz'']
  exact hz''V.2

/-- **Theorem 8.2**: if `K`-q.c. maps `fₙ` of a bounded domain `D` converge locally uniformly
to `f`, then `f` is either a constant or a `K`-q.c. map (with the same `K`).

Proved (2026-09-21) via the `qcl_` helpers above: Step 1 (constant or injective) by Theorem 7.4 and
`dcModulus_le_rhoArea` with the book's logarithmic density on a round annulus in the image; Step 2 by
Carathéodory (`image_isJordanDomain_of_open`, `exists_uniformizer_finite_vertices`), the winding-number
orientation argument (`qcl_r_exists_image_quad`) and Theorem 4.8 (`qcl_m_modulus_le`). -/
theorem thm8_2_limit {D : Set ℂ} (hD : Bornology.IsBounded D) (hDc : IsConnected D) {K : ℝ}
    {fn : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hqc : ∀ n, IsKQC (fn n) D K)
    (hlim : TendstoLocallyUniformlyOn fn f atTop D) :
    (∃ c : ℂ, ∀ z ∈ D, f z = c) ∨ IsKQC f D K := by
  have hDo : IsOpen D := (hqc 0).1
  have hfc : ContinuousOn f D :=
    hlim.continuousOn (Filter.Eventually.of_forall fun n => (hqc n).2.2.1.1).frequently
  by_cases hnc : ∃ c : ℂ, ∀ z ∈ D, f z = c
  · exact Or.inl hnc
  · right
    have hfi : InjOn f D := qcl_s_injOn hDc hqc hlim hfc hnc
    refine ⟨hDo, (hqc 0).2.1, qcl_f_isHomeomorphOnto_of_injOn hDo hfc hfi, fun Q hQ => ?_⟩
    obtain ⟨Q', hQ'⟩ := qcl_r_exists_image_quad hDo hqc hlim hfc hfi hQ
    exact ⟨Q', hQ', qcl_m_modulus_le hDo hqc hlim hfc hfi hQ hQ'⟩

end LiZhongQC
