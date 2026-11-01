import LiZhongQC.Ch02.S11_IntegralOperators
import LiZhongQC.Lemmas.HilbertInterpPair

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-! ## RT2–RT4: closing S11's last two non-wall sorries (`thm11_2_riesz_thorin`,
`hilbertNorm_continuousOn`) via RT1 (`hilbertH_boundedLp_interp_pair`).

Primed names throughout (avoid clashing with the still-present sorry'd S11 declarations, which
`-17` will relocate verbatim into `S11b_HilbertNorm.lean`). Everything that touches `hilbertNorm`
is tainted by exactly `zygmund_calderon`'s one sorry (the wall); everything else is clean. -/

/-- Shared witness for `hilbertNorm`'s defining `sSup`: the indicator of the unit disc lies in
every `L^p` (`p > 0`) and has nonzero `eLpNorm`. Reused by RT2 and RT3b. -/
theorem unitDiscIndicator_eLpNorm_ne_zero {p : ℝ} (hp0 : 0 < p) :
    MemLp ((ball (0:ℂ) 1).indicator fun _ => (1:ℂ)) (ENNReal.ofReal p) ∧
      eLpNorm ((ball (0:ℂ) 1).indicator fun _ => (1:ℂ)) (ENNReal.ofReal p) ≠ 0 := by
  refine ⟨memLp_indicator_const _ measurableSet_ball.nullMeasurableSet 1 (Or.inr measure_ball_lt_top.ne), ?_⟩
  have hsupp : {z : ℂ | (ball (0:ℂ) 1).indicator (fun _ => (1:ℂ)) z ≠ 0} = ball 0 1 := by
    ext z
    constructor
    · intro hz; by_contra hzb; exact hz (Set.indicator_of_notMem hzb _)
    · intro hz; rw [Set.mem_setOf_eq, Set.indicator_of_mem hz]; exact one_ne_zero
  rw [Ne, eLpNorm_eq_zero_iff (ENNReal.ofReal_pos.mpr hp0).ne']
  intro h
  have h0 : volume {z : ℂ | (ball (0:ℂ) 1).indicator (fun _ => (1:ℂ)) z ≠ 0} = 0 := by
    simpa [Filter.EventuallyEq, ae_iff] using h
  rw [hsupp] at h0
  exact (measure_ball_pos volume (0:ℂ) one_pos).ne' h0

/-- **RT2.** `Λ_p > 0` for `p > 1`. Tainted by `zygmund_calderon` (needed for finiteness /
`MemLp (hilbertH ω) p` of the witness). -/
theorem hilbertNorm_pos' {p : ℝ} (hp : 1 < p) : 0 < hilbertNorm p := by
  set ω : ℂ → ℂ := (ball (0:ℂ) 1).indicator fun _ => (1:ℂ) with hω_def
  obtain ⟨hωmem, hne⟩ := unitDiscIndicator_eLpNorm_ne_zero (p := p) (by linarith)
  obtain ⟨hωmem2, hne2⟩ := unitDiscIndicator_eLpNorm_ne_zero (p := 2) (by norm_num)
  have h2cast : ENNReal.ofReal (2:ℝ) = 2 := by norm_num
  rw [h2cast] at hωmem2 hne2
  have hHiso : eLpNorm (hilbertH ω) 2 = eLpNorm ω 2 := (hilbertH_memLp_two hωmem2).2
  have hHne2 : eLpNorm (hilbertH ω) 2 ≠ 0 := hHiso ▸ hne2
  have hpne0 : p ≠ 0 := by linarith
  obtain ⟨A, hA0, hbound⟩ := zygmund_calderon hp
  have hHmem : MemLp (hilbertH ω) (ENNReal.ofReal p) :=
    (hilbertH_memLp_of_smooth_bound hp hbound ω hωmem).1
  have hHne : eLpNorm (hilbertH ω) (ENNReal.ofReal p) ≠ 0 := by
    intro hz
    apply hHne2
    have haez : hilbertH ω =ᵐ[volume] 0 :=
      (eLpNorm_eq_zero_iff (ENNReal.ofReal_pos.mpr (by linarith)).ne').mp hz
    rw [eLpNorm_congr_ae haez, eLpNorm_zero]
  have hratio_pos : 0 < (eLpNorm (hilbertH ω) (ENNReal.ofReal p)).toReal /
      (eLpNorm ω (ENNReal.ofReal p)).toReal :=
    div_pos (ENNReal.toReal_pos hHne hHmem.eLpNorm_ne_top)
      (ENNReal.toReal_pos hne hωmem.eLpNorm_ne_top)
  exact lt_of_lt_of_le hratio_pos (le_csSup (hilbertNorm_bddAbove p hp) ⟨ω, hωmem, hne, rfl⟩)

/-- **RT3a.** Every smooth compactly-supported `φ` satisfies the `Λ_p`-bound. Tainted (needs
`MemLp (hilbertH φ) p`, i.e. the wall, off the degenerate `eLpNorm φ p = 0` branch). -/
theorem hilbertHSmooth_le_hilbertNorm {p : ℝ} (hp : 1 < p) :
    ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p) ≤
        ENNReal.ofReal (hilbertNorm p) * eLpNorm φ (ENNReal.ofReal p) := by
  intro φ hφ hc
  have hφmem : MemLp φ (ENNReal.ofReal p) volume := hφ.continuous.memLp_of_hasCompactSupport hc
  rcases eq_or_ne (eLpNorm φ (ENNReal.ofReal p) volume) 0 with hz | hne
  · obtain ⟨A, hA0, hbound⟩ := zygmund_calderon hp
    have hb := hbound φ hφ hc
    rw [hz, mul_zero] at hb
    rw [le_zero_iff.mp hb, hz, mul_zero]
  · have hle : (eLpNorm (hilbertH φ) (ENNReal.ofReal p) volume).toReal /
        (eLpNorm φ (ENNReal.ofReal p) volume).toReal ≤ hilbertNorm p :=
      le_csSup (hilbertNorm_bddAbove p hp) ⟨φ, hφmem, hne, rfl⟩
    have hωpos : (0:ℝ) < (eLpNorm φ (ENNReal.ofReal p) volume).toReal :=
      ENNReal.toReal_pos hne hφmem.eLpNorm_ne_top
    rw [div_le_iff₀ hωpos] at hle
    have hHmem : MemLp (hilbertH φ) (ENNReal.ofReal p) volume := hilbertH_memLp hp hφmem
    have h1 : eLpNorm (hilbertH φ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (hilbertNorm p * (eLpNorm φ (ENNReal.ofReal p) volume).toReal) := by
      rw [← ENNReal.ofReal_toReal hHmem.eLpNorm_ne_top]
      exact ENNReal.ofReal_le_ofReal hle
    rw [ENNReal.ofReal_mul (hilbertNorm_nonneg p), ENNReal.ofReal_toReal hφmem.eLpNorm_ne_top] at h1
    rwa [eLpNorm_congr_ae (hilbertH_eq_ae_smooth hφ hc)] at h1

/-- **RT3b.** The converse direction: any smooth-bound constant `A` dominates `Λ_p`. Tainted
(needs `MemLp (hilbertH ω) p` for every test `ω`, via `hilbertH_memLp_of_smooth_bound`, which
is itself clean — but the CALLER's own `hbound` is expected to come from the wall in practice). -/
theorem hilbertNorm_le_of_smooth_bound {p A : ℝ} (hp : 1 < p) (hA : 0 ≤ A)
    (hbound : ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p) ≤
        ENNReal.ofReal A * eLpNorm φ (ENNReal.ofReal p)) :
    hilbertNorm p ≤ A := by
  rw [hilbertNorm]
  apply csSup_le
  · obtain ⟨hωmem, hne⟩ := unitDiscIndicator_eLpNorm_ne_zero (p := p) (by linarith)
    exact ⟨_, ((ball (0:ℂ) 1).indicator fun _ => (1:ℂ)), hωmem, hne, rfl⟩
  · rintro c ⟨ω, hω, hne, rfl⟩
    have h1 := (hilbertH_memLp_of_smooth_bound hp hbound ω hω).2
    have hωpos : (0:ℝ) < (eLpNorm ω (ENNReal.ofReal p)).toReal :=
      ENNReal.toReal_pos hne hω.eLpNorm_ne_top
    rw [div_le_iff₀ hωpos]
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω.eLpNorm_ne_top) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA] at h2

/-- **RT3 (Theorem 11.2).** `log Λ_{1/s}` is convex on `s ∈ (0, 1)`, via RT1 applied to
`p₀ = 1/s₀`, `p₁ = 1/s₁`, `θ = b`. Tainted (through RT3a/RT3b/RT2). -/
theorem thm11_2_riesz_thorin' :
    ConvexOn ℝ (Ioo 0 1) (fun s : ℝ => Real.log (hilbertNorm (1 / s))) := by
  refine ⟨convex_Ioo 0 1, ?_⟩
  intro s₀ hs₀ s₁ hs₁ a b ha hb hab
  simp only [mem_Ioo] at hs₀ hs₁
  set p₀ := 1 / s₀ with hp₀_def
  set p₁ := 1 / s₁ with hp₁_def
  have hp₀ : (1:ℝ) < p₀ := by rw [hp₀_def, lt_div_iff₀ hs₀.1]; linarith [hs₀.2]
  have hp₁ : (1:ℝ) < p₁ := by rw [hp₁_def, lt_div_iff₀ hs₁.1]; linarith [hs₁.2]
  set p := 1 / (a * s₀ + b * s₁) with hp_def
  have hpos_comb : 0 < a * s₀ + b * s₁ := by
    rcases ha.eq_or_lt with rfl | ha'
    · simp only [zero_mul, zero_add]
      have : b = 1 := by linarith
      rw [this]; linarith [hs₁.1]
    · have : 0 < a * s₀ := mul_pos ha' hs₀.1
      rcases hb.eq_or_lt with rfl | hb'
      · simp only [zero_mul, add_zero]; exact this
      · have : 0 < b * s₁ := mul_pos hb' hs₁.1
        linarith
  have hlt1_comb : a * s₀ + b * s₁ < 1 := by
    have h0 : a * s₀ < a * 1 ∨ a = 0 := by
      rcases eq_or_lt_of_le ha with rfl | ha'
      · right; rfl
      · left; exact mul_lt_mul_of_pos_left hs₀.2 ha'
    have h1 : b * s₁ < b * 1 ∨ b = 0 := by
      rcases eq_or_lt_of_le hb with rfl | hb'
      · right; rfl
      · left; exact mul_lt_mul_of_pos_left hs₁.2 hb'
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · nlinarith
    · nlinarith
    · nlinarith
    · exfalso; rw [h0, h1] at hab; norm_num at hab
  have hp : (1:ℝ) < p := by rw [hp_def, lt_div_iff₀ hpos_comb]; linarith
  have hp0ne : s₀ ≠ 0 := hs₀.1.ne'
  have hp1ne : s₁ ≠ 0 := hs₁.1.ne'
  have hpne : (a * s₀ + b * s₁) ≠ 0 := hpos_comb.ne'
  have hrel : 1 / p = (1 - b) / p₀ + b / p₁ := by
    rw [hp_def, hp₀_def, hp₁_def, one_div_one_div]
    have e1 : (1 - b) / (1 / s₀) = (1 - b) * s₀ := by rw [div_eq_mul_inv, inv_div, div_one]
    have e2 : b / (1 / s₁) = b * s₁ := by rw [div_eq_mul_inv, inv_div, div_one]
    rw [e1, e2]
    have : a = 1 - b := by linarith
    rw [← this]
  have hM₀ : (0:ℝ) ≤ hilbertNorm p₀ := hilbertNorm_nonneg p₀
  have hM₁ : (0:ℝ) ≤ hilbertNorm p₁ := hilbertNorm_nonneg p₁
  have hbnd := hilbertH_boundedLp_interp_pair hp₀ hp₁ hM₀ hM₁
    (hilbertHSmooth_le_hilbertNorm hp₀) (hilbertHSmooth_le_hilbertNorm hp₁)
    (⟨hb, by linarith⟩ : b ∈ Icc (0:ℝ) 1) hrel
  have hle : hilbertNorm p ≤ hilbertNorm p₀ ^ (1 - b) * hilbertNorm p₁ ^ b :=
    hilbertNorm_le_of_smooth_bound hp
      (mul_nonneg (Real.rpow_nonneg hM₀ _) (Real.rpow_nonneg hM₁ _)) hbnd
  have hΛppos : 0 < hilbertNorm p := hilbertNorm_pos' hp
  have hΛ₀pos : 0 < hilbertNorm p₀ := hilbertNorm_pos' hp₀
  have hΛ₁pos : 0 < hilbertNorm p₁ := hilbertNorm_pos' hp₁
  have hlog := Real.log_le_log hΛppos hle
  rw [Real.log_mul (Real.rpow_pos_of_pos hΛ₀pos _).ne' (Real.rpow_pos_of_pos hΛ₁pos _).ne',
    Real.log_rpow hΛ₀pos, Real.log_rpow hΛ₁pos] at hlog
  show Real.log (hilbertNorm (1 / (a • s₀ + b • s₁))) ≤
    a • Real.log (hilbertNorm (1/s₀)) + b • Real.log (hilbertNorm (1/s₁))
  simp only [smul_eq_mul]
  rw [← hp_def, ← hp₀_def, ← hp₁_def]
  have haeq : a = 1 - b := by linarith
  rw [haeq]
  exact hlog

/-- **RT4.** `Λ_p` continuous on `p > 1`, via `ConvexOn.continuousOn` on the open interval `(0,1)`
plus `p ↦ 1/p` and `Real.exp`/`Real.log` round-tripping (`hilbertNorm_pos'`). -/
theorem hilbertNorm_continuousOn' : ContinuousOn hilbertNorm (Ioi 1) := by
  have hconv := thm11_2_riesz_thorin'.continuousOn isOpen_Ioo
  have hmaps : Set.MapsTo (fun p : ℝ => 1/p) (Ioi (1:ℝ)) (Ioo 0 1) := by
    intro p hp
    simp only [mem_Ioi] at hp
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one (by linarith : (0:ℝ) < p)]
    linarith
  have hcont_inv : ContinuousOn (fun p : ℝ => 1/p) (Ioi (1:ℝ)) := by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro p hp
    simp only [mem_Ioi] at hp
    exact (by linarith : (0:ℝ) < p).ne'
  have hcomp : ContinuousOn (fun p : ℝ => Real.log (hilbertNorm (1/(1/p)))) (Ioi (1:ℝ)) :=
    hconv.comp hcont_inv hmaps
  have heq : ∀ p ∈ Ioi (1:ℝ), hilbertNorm p = Real.exp (Real.log (hilbertNorm (1/(1/p)))) := by
    intro p hp
    simp only [mem_Ioi] at hp
    rw [one_div_one_div, Real.exp_log (hilbertNorm_pos' hp)]
  exact ContinuousOn.congr (Real.continuous_exp.comp_continuousOn' hcomp) heq

/-- **Theorem 11.3, Corollary 2.** `Λ_p → 1` as `p → 2`, exactly as the original S11 proof does
with `RT4` + the already-clean `thm11_3_cor1`. -/
theorem thm11_3_cor2' : Tendsto hilbertNorm (𝓝 2) (𝓝 1) := by
  have h := hilbertNorm_continuousOn'.continuousAt (Ioi_mem_nhds (by norm_num : (1:ℝ) < 2))
  rwa [ContinuousAt, thm11_3_cor1] at h

end LiZhongQC
