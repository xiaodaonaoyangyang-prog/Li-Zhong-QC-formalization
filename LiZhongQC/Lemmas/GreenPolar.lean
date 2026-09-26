import LiZhongQC.Lemmas.GreenDisc

open Complex Set MeasureTheory intervalIntegral Filter
open scoped Interval Real ComplexConjugate Topology ENNReal

noncomputable section
namespace LiZhongQC

/-- `polarCoord.symm (r, θ) + c = c + r e^{iθ} = circleMap c r θ`. -/
theorem polarCoord_symm_add_eq_circleMap (c : ℂ) (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) + c = circleMap c r θ := by
  simp only [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  ring

/-- Translation: `∫_{|z-c|<R} g = ∫_{|w|<R} g(w+c)`. -/
theorem setIntegral_ball_translate (g : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    ∫ z in Metric.ball c R, g z = ∫ w in Metric.ball (0 : ℂ) R, g (w + c) := by
  have hemb : MeasurableEmbedding (fun w : ℂ => w + c) :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  have hpre : (fun w : ℂ => w + c) ⁻¹' Metric.ball c R = Metric.ball (0 : ℂ) R := by
    ext w
    simp [Metric.mem_ball, dist_eq_norm]
  have htr := (measurePreserving_add_right volume c).setIntegral_preimage_emb hemb g
    (Metric.ball c R)
  rw [hpre] at htr
  exact htr.symm

/-- A `2π`-periodic integrand has the same integral over `(-π, π)` and over `(0, 2π)`. -/
theorem intervalIntegral_shift_period {ψ : ℝ → ℂ} (hψ : Function.Periodic ψ (2 * π)) :
    ∫ θ in (-π : ℝ)..π, ψ θ = ∫ θ in (0 : ℝ)..(2 * π), ψ θ := by
  have h := hψ.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at h
  exact h

/-- The polar region corresponding to the ball `|w| < R`. -/
theorem polarCoord_target_inter_ball {R : ℝ} :
    _root_.polarCoord.target ∩
        ((fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹' Metric.ball (0 : ℂ) R)
      = Set.Ioo 0 R ×ˢ Set.Ioo (-π) π := by
  ext p
  simp only [show _root_.polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π from rfl,
    Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage,
    Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, Set.mem_Ioi, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, by rwa [abs_of_pos h1] at h3⟩, h2⟩
  · rintro ⟨⟨h1, h1'⟩, h2⟩
    exact ⟨⟨h1, h2⟩, by rwa [abs_of_pos h1]⟩

/-- **Polar coordinates on a ball centred at `0`.** -/
theorem setIntegral_ball_zero_polar (G : ℂ → ℂ) (R : ℝ) :
    ∫ w in Metric.ball (0 : ℂ) R, G w
      = ∫ p in Set.Ioo 0 R ×ˢ Set.Ioo (-π) π,
          (p.1 : ℂ) * G (Complex.polarCoord.symm p) := by
  have hpolar := Complex.integral_comp_polarCoord_symm ((Metric.ball (0 : ℂ) R).indicator G)
  rw [MeasureTheory.integral_indicator measurableSet_ball] at hpolar
  rw [← hpolar]
  have hpt : ∀ p : ℝ × ℝ,
      p.1 • ((Metric.ball (0 : ℂ) R).indicator G) (Complex.polarCoord.symm p)
        = (Complex.polarCoord.symm ⁻¹' Metric.ball (0 : ℂ) R).indicator
            (fun q : ℝ × ℝ => (q.1 : ℂ) * G (Complex.polarCoord.symm q)) p := by
    intro p
    by_cases h : Complex.polarCoord.symm p ∈ Metric.ball (0 : ℂ) R
    · have hp : p ∈ Complex.polarCoord.symm ⁻¹' Metric.ball (0 : ℂ) R := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem hp, Complex.real_smul]
    · have hp : p ∉ Complex.polarCoord.symm ⁻¹' Metric.ball (0 : ℂ) R := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem hp, smul_zero]
  have hc : Continuous fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
    have he : (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
        = fun p : ℝ × ℝ => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * I) := by
      funext p
      exact Complex.polarCoord_symm_apply p
    rw [he]
    fun_prop
  simp only [hpt]
  rw [MeasureTheory.setIntegral_indicator (measurableSet_ball.preimage hc.measurable)]
  rw [polarCoord_target_inter_ball]

/-- The polar integrand is jointly continuous. -/
theorem continuous_polar_integrand {G : ℂ → ℂ} (hG : Continuous G) :
    Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * G (Complex.polarCoord.symm p) := by
  have he : (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
      = fun p : ℝ × ℝ => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * I) := by
    funext p
    exact Complex.polarCoord_symm_apply p
  have hsymm : Continuous fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
    rw [he]; fun_prop
  exact (Complex.continuous_ofReal.comp continuous_fst).mul (hG.comp hsymm)

/-- The polar integrand is integrable on the bounded polar region. -/
theorem integrableOn_polar {G : ℂ → ℂ} (hG : Continuous G) (R : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * G (Complex.polarCoord.symm p))
      (Set.Ioo 0 R ×ˢ Set.Ioo (-π) π) := by
  refine ((continuous_polar_integrand hG).continuousOn.integrableOn_compact
    ((isCompact_Icc (a := (0 : ℝ)) (b := R)).prod
      (isCompact_Icc (a := -π) (b := π)))).mono_set ?_
  exact Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self

/-- **Fubini on the polar region**, assuming only integrability.

The continuity in `setIntegral_polar_fubini` is used *only* to supply this integrability, so this
is the form to reach for when the integrand is singular (e.g. a Cauchy kernel `1/(ζ - z)` with
`z` inside the disc). -/
theorem setIntegral_polar_fubini' {G : ℂ → ℂ} {R : ℝ}
    (hint : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * G (Complex.polarCoord.symm p))
      (Set.Ioo 0 R ×ˢ Set.Ioo (-π) π)) :
    ∫ p in Set.Ioo 0 R ×ˢ Set.Ioo (-π) π, (p.1 : ℂ) * G (Complex.polarCoord.symm p)
      = ∫ r in Set.Ioo 0 R, ∫ θ in Set.Ioo (-π) π,
          (r : ℂ) * G (Complex.polarCoord.symm (r, θ)) := by
  rw [MeasureTheory.Measure.volume_eq_prod] at hint ⊢
  exact MeasureTheory.setIntegral_prod _ hint

/-- **Fubini on the polar region.** -/
theorem setIntegral_polar_fubini {G : ℂ → ℂ} (hG : Continuous G) (R : ℝ) :
    ∫ p in Set.Ioo 0 R ×ˢ Set.Ioo (-π) π, (p.1 : ℂ) * G (Complex.polarCoord.symm p)
      = ∫ r in Set.Ioo 0 R, ∫ θ in Set.Ioo (-π) π,
          (r : ℂ) * G (Complex.polarCoord.symm (r, θ)) := by
  exact setIntegral_polar_fubini' (integrableOn_polar hG R)

/-- **Polar coordinates for an integral over a disc**, assuming only integrability:
`∫_{|z-c|<R} g = ∫₀^R ∫₀^{2π} r · g(c + r e^{iθ}) dθ dr`.

This is the form to use when `g` is singular inside the disc — a Cauchy kernel `1/(ζ - z)` with
`z ∈ ball c R`, say — which `setIntegral_ball_eq_polar` excludes.  Continuity enters that version
*only* through `setIntegral_polar_fubini`; the translation, the change of variables and the
periodicity shift of the `θ`-range all work for an arbitrary integrand. -/
theorem setIntegral_ball_eq_polar' {g : ℂ → ℂ} (c : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hint : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * g (Complex.polarCoord.symm p + c))
      (Set.Ioo 0 R ×ˢ Set.Ioo (-π) π)) :
    ∫ z in Metric.ball c R, g z
      = ∫ r in (0 : ℝ)..R, ∫ θ in (0 : ℝ)..(2 * π), (r : ℂ) * g (circleMap c r θ) := by
  have hpi : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
  have hinner : ∀ r : ℝ, (∫ θ in Set.Ioo (-π) π, (r : ℂ) * g (circleMap c r θ))
      = ∫ θ in (0 : ℝ)..(2 * π), (r : ℂ) * g (circleMap c r θ) := by
    intro r
    have hper : Function.Periodic (fun θ : ℝ => (r : ℂ) * g (circleMap c r θ)) (2 * π) := by
      intro θ
      simp only
      rw [periodic_circleMap c r θ]
    rw [← intervalIntegral_shift_period hper, intervalIntegral.integral_of_le hpi,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [setIntegral_ball_translate g c R, setIntegral_ball_zero_polar (fun w => g (w + c)) R,
    setIntegral_polar_fubini' (G := fun w : ℂ => g (w + c)) hint]
  simp only [polarCoord_symm_add_eq_circleMap, hinner]
  rw [intervalIntegral.integral_of_le hR, MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- **Polar coordinates for an integral over a disc.**  For continuous `g`,
`∫_{|z-c|<R} g = ∫₀^R ∫₀^{2π} r · g(c + r e^{iθ}) dθ dr`. -/
theorem setIntegral_ball_eq_polar {g : ℂ → ℂ} (hg : Continuous g) (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    ∫ z in Metric.ball c R, g z
      = ∫ r in (0 : ℝ)..R, ∫ θ in (0 : ℝ)..(2 * π), (r : ℂ) * g (circleMap c r θ) := by
  have hgc : Continuous fun w : ℂ => g (w + c) := hg.comp (continuous_id.add continuous_const)
  have hpi : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
  have hinner : ∀ r : ℝ, (∫ θ in Set.Ioo (-π) π, (r : ℂ) * g (circleMap c r θ))
      = ∫ θ in (0 : ℝ)..(2 * π), (r : ℂ) * g (circleMap c r θ) := by
    intro r
    have hper : Function.Periodic (fun θ : ℝ => (r : ℂ) * g (circleMap c r θ)) (2 * π) := by
      intro θ
      simp only
      rw [periodic_circleMap c r θ]
    rw [← intervalIntegral_shift_period hper, intervalIntegral.integral_of_le hpi,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [setIntegral_ball_translate g c R, setIntegral_ball_zero_polar (fun w => g (w + c)) R,
    setIntegral_polar_fubini hgc R]
  simp only [polarCoord_symm_add_eq_circleMap, hinner]
  rw [intervalIntegral.integral_of_le hR, MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- **Green's formula on a disc** (11.9), for `f ∈ C¹(ℂ)`:
`∮_{|z-c|=R} f dz = 2i ∬_{|z-c|<R} ∂_z̄ f dx dy`. -/
theorem green_disc_dzbar {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    (∮ z in C(c, R), f z) = 2 * I * ∫ z in Metric.ball c R, dzbar f z := by
  rw [circleIntegral_eq_integral_polar hf c R,
    setIntegral_ball_eq_polar (continuous_dzbar hf) c hR]
  have hinner : ∀ r : ℝ, (∫ θ in (0 : ℝ)..(2 * π), (r : ℂ) * dzbar f (circleMap c r θ))
      = (r : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), dzbar f (circleMap c r θ) := fun r =>
    intervalIntegral.integral_const_mul _ _
  simp only [hinner]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun r _ => ?_
  ring

/-- **Green's formula on a disc** (11.10), for `f ∈ C¹(ℂ)`:
`∮_{∂D} f dz̄ = -2i ∬_D ∂_z f dx dy`, with the `dz̄` boundary integral written out as in §11.2.

Obtained from `green_disc_dzbar` applied to `conj ∘ f` and conjugated, using the book's (6.3). -/
theorem green_disc_dz {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ θ in (0 : ℝ)..2 * π, f (circleMap c R θ) * conj (deriv (circleMap c R) θ))
      = -2 * I * ∫ z in Metric.ball c R, dz f z := by
  have hdif : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hcg : ContDiff ℝ 1 fun w : ℂ => conj (f w) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp hf
  have h := green_disc_dzbar hcg c hR
  have hdzbar : ∀ z : ℂ, dzbar (fun w => conj (f w)) z = conj (dz f z) := fun z =>
    ((eq6_3 (hdif z)).1).symm
  simp only [hdzbar] at h
  rw [integral_conj, circleIntegral] at h
  have hlhs : conj (∫ θ in (0 : ℝ)..2 * π,
        deriv (circleMap c R) θ • conj (f (circleMap c R θ)))
      = ∫ θ in (0 : ℝ)..2 * π, f (circleMap c R θ) * conj (deriv (circleMap c R) θ) := by
    rw [← intervalIntegral_conj]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [smul_eq_mul, map_mul, Complex.conj_conj]
    ring
  have h2 := congrArg (starRingEnd ℂ) h
  rw [hlhs, map_mul, map_mul, Complex.conj_I, map_ofNat, Complex.conj_conj] at h2
  linear_combination h2

/-! ## Localizing the hypothesis

`green_disc_dzbar` asks for `f` of class `C¹` on all of `ℂ`.  The version below asks only that
`f` be `C¹` on some open set containing the closed disc, which is what "f ∈ C¹(D̄)" means in
practice.  The reduction is a cutoff: multiply `f` by a `ContDiffBump` that is `1` on a
neighbourhood of the closed disc and supported inside the open set. -/

/-- **Cutoff.**  If `f` is `C¹` on an open `U` containing `closedBall c R`, there is a `g` of
class `C¹` on *all* of `ℂ` agreeing with `f` on a ball strictly larger than `closedBall c R`.
Obtained by multiplying by a `ContDiffBump` that is `1` near the closed disc and supported
inside `U`. -/
theorem exists_contDiff_eqOn_ball {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (c : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hsub : Metric.closedBall c R ⊆ U) :
    ∃ (g : ℂ → ℂ) (R' : ℝ), R < R' ∧ ContDiff ℝ 1 g ∧ ∀ z ∈ Metric.ball c R', g z = f z := by
  obtain ⟨δ, hδ, hδsub⟩ := (isCompact_closedBall c R).exists_cthickening_subset_open hU hsub
  rw [cthickening_closedBall hδ.le hR c] at hδsub
  set χ : ContDiffBump c :=
    ⟨R + δ / 3, R + 2 * δ / 3, by positivity, by linarith⟩ with hχ
  have hrOut : Metric.closedBall c χ.rOut ⊆ U := by
    refine subset_trans ?_ hδsub
    exact Metric.closedBall_subset_closedBall (by simp only [hχ]; linarith)
  set g : ℂ → ℂ := fun z => ((χ z : ℝ) : ℂ) * f z with hg_def
  have hχC : ContDiff ℝ 1 fun z : ℂ => ((χ z : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hg : ContDiff ℝ 1 g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Metric.closedBall c χ.rOut
    · exact hχC.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds (hrOut hx)))
    · have hopen : IsOpen {z : ℂ | χ.rOut < dist z c} :=
        isOpen_lt continuous_const (continuous_id.dist continuous_const)
      have hxmem : x ∈ {z : ℂ | χ.rOut < dist z c} := by
        simpa [Metric.mem_closedBall, not_le] using hx
      have hev : g =ᶠ[nhds x] fun _ => (0 : ℂ) := by
        filter_upwards [hopen.mem_nhds hxmem] with z hz
        have hz0 : χ z = 0 := χ.zero_of_le_dist (le_of_lt hz)
        simp [hg_def, hz0]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  refine ⟨g, R + δ / 3, by linarith, hg, fun z hz => ?_⟩
  have hz1 : χ z = 1 :=
    χ.one_of_mem_closedBall (by
      simp only [hχ, Metric.mem_closedBall]
      exact le_of_lt (Metric.mem_ball.1 hz))
  simp [hg_def, hz1]

/-- The circle `|z-c| = R` lies in any strictly larger ball about `c`. -/
theorem circleMap_mem_ball {c : ℂ} {R R' : ℝ} (hR : 0 ≤ R) (hRR' : R < R') (θ : ℝ) :
    circleMap c R θ ∈ Metric.ball c R' := by
  have hs := circleMap_mem_sphere' c R θ
  rw [Metric.mem_sphere] at hs
  rw [Metric.mem_ball, hs, abs_of_nonneg hR]
  exact hRR'

/-- **Green's formula (11.9) on a disc, for `f` of class `C¹` near the closed disc.** -/
theorem green_disc_dzbar_of_contDiffOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (c : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hsub : Metric.closedBall c R ⊆ U) :
    (∮ z in C(c, R), f z) = 2 * I * ∫ z in Metric.ball c R, dzbar f z := by
  obtain ⟨g, R', hRR', hg, hgf⟩ := exists_contDiff_eqOn_ball hU hf c hR hsub
  have h := green_disc_dzbar hg c hR
  have hcirc : (∮ z in C(c, R), g z) = ∮ z in C(c, R), f z := by
    rw [circleIntegral, circleIntegral]
    exact intervalIntegral.integral_congr fun θ _ => by
      rw [hgf _ (circleMap_mem_ball hR hRR' θ)]
  have hint : ∫ z in Metric.ball c R, dzbar g z = ∫ z in Metric.ball c R, dzbar f z := by
    refine setIntegral_congr_fun measurableSet_ball fun z hz => ?_
    have hev : g =ᶠ[nhds z] f := by
      filter_upwards [Metric.isOpen_ball.mem_nhds
        (Metric.ball_subset_ball hRR'.le hz)] with w hw
      exact hgf w hw
    simp only [dzbar, hev.fderiv_eq]
  rw [hcirc, hint] at h
  exact h

/-- **Green's formula (11.10) on a disc, for `f` of class `C¹` near the closed disc.** -/
theorem green_disc_dz_of_contDiffOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (c : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hsub : Metric.closedBall c R ⊆ U) :
    (∫ θ in (0 : ℝ)..2 * π, f (circleMap c R θ) * conj (deriv (circleMap c R) θ))
      = -2 * I * ∫ z in Metric.ball c R, dz f z := by
  obtain ⟨g, R', hRR', hg, hgf⟩ := exists_contDiff_eqOn_ball hU hf c hR hsub
  have h := green_disc_dz hg c hR
  have hbd : (∫ θ in (0 : ℝ)..2 * π, g (circleMap c R θ) * conj (deriv (circleMap c R) θ))
      = ∫ θ in (0 : ℝ)..2 * π, f (circleMap c R θ) * conj (deriv (circleMap c R) θ) :=
    intervalIntegral.integral_congr fun θ _ => by
      rw [hgf _ (circleMap_mem_ball hR hRR' θ)]
  have hint : ∫ z in Metric.ball c R, dz g z = ∫ z in Metric.ball c R, dz f z := by
    refine setIntegral_congr_fun measurableSet_ball fun z hz => ?_
    have hev : g =ᶠ[nhds z] f := by
      filter_upwards [Metric.isOpen_ball.mem_nhds
        (Metric.ball_subset_ball hRR'.le hz)] with w hw
      exact hgf w hw
    simp only [dz, hev.fderiv_eq]
  rw [hbd, hint] at h
  exact h

/-! ## Exhaustion: from `C¹` near the disc to `C¹` on the closed disc -/

/-- For `f` of class `C¹` on `closedBall c R`, the formal derivatives are bounded on the open
ball (they extend continuously to the compact closed ball), hence integrable there. -/
theorem integrableOn_dzbar_ball {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContDiffOn ℝ 1 f (Metric.closedBall c R)) :
    IntegrableOn (dzbar f) (Metric.ball c R) := by
  have hud : UniqueDiffOn ℝ (Metric.closedBall c R) :=
    uniqueDiffOn_convex (convex_closedBall c R)
      (by rw [interior_closedBall c hR.ne']; exact ⟨c, Metric.mem_ball_self hR⟩)
  have hcw : ContinuousOn (fderivWithin ℝ f (Metric.closedBall c R)) (Metric.closedBall c R) :=
    hf.continuousOn_fderivWithin hud le_rfl
  obtain ⟨M, hM⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hcw
  have hdiffAt : ∀ z ∈ Metric.ball c R, DifferentiableAt ℝ f z := by
    intro z hz
    exact (hf.contDiffAt (Metric.closedBall_mem_nhds_of_mem hz)).differentiableAt one_ne_zero
  have heq : ∀ z ∈ Metric.ball c R,
      fderiv ℝ f z = fderivWithin ℝ f (Metric.closedBall c R) z := by
    intro z hz
    exact (fderivWithin_eq_fderiv (hud z (Metric.ball_subset_closedBall hz)) (hdiffAt z hz)).symm
  have hbd : ∀ z ∈ Metric.ball c R, ‖dzbar f z‖ ≤ M := by
    intro z hz
    have hz' : z ∈ Metric.closedBall c R := Metric.ball_subset_closedBall hz
    have hop := hM z hz'
    have h1 : ‖fderiv ℝ f z 1‖ ≤ M := by
      rw [heq z hz]
      have := (fderivWithin ℝ f (Metric.closedBall c R) z).le_opNorm (1 : ℂ)
      simpa using this.trans (by simpa using hop)
    have hI : ‖fderiv ℝ f z I‖ ≤ M := by
      rw [heq z hz]
      have := (fderivWithin ℝ f (Metric.closedBall c R) z).le_opNorm I
      simpa using this.trans (by simpa using hop)
    have : ‖dzbar f z‖ ≤ (‖fderiv ℝ f z 1‖ + ‖fderiv ℝ f z I‖) / 2 := by
      simp only [dzbar, norm_div]
      rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
      gcongr
      calc ‖fderiv ℝ f z 1 + I * fderiv ℝ f z I‖
          ≤ ‖fderiv ℝ f z 1‖ + ‖I * fderiv ℝ f z I‖ := norm_add_le _ _
        _ = ‖fderiv ℝ f z 1‖ + ‖fderiv ℝ f z I‖ := by simp
    linarith
  have hmeas : AEStronglyMeasurable (dzbar f) (volume.restrict (Metric.ball c R)) := by
    have hcont : ContinuousOn (dzbar f) (Metric.ball c R) :=
      (continuousOn_dz_dzbar (hf.mono Metric.ball_subset_closedBall) Metric.isOpen_ball).2
    exact hcont.aestronglyMeasurable measurableSet_ball
  refine ⟨hmeas, MeasureTheory.HasFiniteIntegral.restrict_of_bounded (C := M)
    measure_ball_lt_top ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz using hbd z hz

/-- **Green's formula (11.9) on a disc, for `f` of class `C¹` on the closed disc.**
This is the statement of `eq11_9_green_dz`.

Proof: for every `R' < R` the closed disc of radius `R'` sits inside the *open* disc of radius
`R`, where `f` is `C¹`, so `green_disc_dzbar_of_contDiffOn` applies; then let `R' ↑ R`, using
dominated convergence on the circle integral and `tendsto_setIntegral_of_monotone` on the area
integral. -/
theorem green_disc_dzbar_closedBall {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContDiffOn ℝ 1 f (Metric.closedBall c R)) :
    (∮ z in C(c, R), f z) = 2 * I * ∫ z in Metric.ball c R, dzbar f z := by
  -- an exhausting sequence of radii
  set u : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hu_def
  have hu0 : ∀ n, 0 < u n := fun n => by rw [hu_def]; positivity
  have hu1 : ∀ n, u n ≤ 1 := fun n => by
    rw [hu_def]
    rw [div_le_one (by positivity)]
    simp only [le_add_iff_nonneg_left]
    positivity
  have hutend : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set rn : ℕ → ℝ := fun n => R * (1 - u n) with hrn_def
  have hrn0 : ∀ n, 0 ≤ rn n := fun n => by
    rw [hrn_def]; have := hu1 n; positivity
  have hrnR : ∀ n, rn n < R := fun n => by
    rw [hrn_def]
    nlinarith [hu0 n]
  have htend : Tendsto rn atTop (𝓝 R) := by
    have : Tendsto (fun n => R * (1 - u n)) atTop (𝓝 (R * (1 - 0))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.sub hutend)
    simpa using this
  have hmono : Monotone rn := by
    intro m n hmn
    rw [hrn_def]
    have hmn' : ((m : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
      have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hmn
      linarith
    have hun : u n ≤ u m := by
      rw [hu_def]
      exact one_div_le_one_div_of_le (by positivity) hmn'
    nlinarith [hR]
  -- the identity at each radius `rn n`
  have hstep : ∀ n, (∮ z in C(c, rn n), f z)
      = 2 * I * ∫ z in Metric.ball c (rn n), dzbar f z := by
    intro n
    refine green_disc_dzbar_of_contDiffOn Metric.isOpen_ball
      (hf.mono Metric.ball_subset_closedBall) c (hrn0 n) ?_
    exact Metric.closedBall_subset_ball (hrnR n)
  -- the circles stay in the closed disc
  have hdistc : ∀ (r : ℝ) (θ : ℝ), dist (circleMap c r θ) c = |r| := by
    intro r θ
    have := circleMap_mem_sphere' c r θ
    rwa [Metric.mem_sphere] at this
  have hmemcb : ∀ (n : ℕ) (θ : ℝ), circleMap c (rn n) θ ∈ Metric.closedBall c R := by
    intro n θ
    rw [Metric.mem_closedBall, hdistc, abs_of_nonneg (hrn0 n)]
    exact (hrnR n).le
  have hmemcbR : ∀ θ : ℝ, circleMap c R θ ∈ Metric.closedBall c R := by
    intro θ
    rw [Metric.mem_closedBall, hdistc, abs_of_nonneg hR.le]
  -- area integrals converge
  have hunion : (⋃ n, Metric.ball c (rn n)) = Metric.ball c R := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun n => Metric.ball_subset_ball (hrnR n).le
    · intro z hz
      rw [Metric.mem_ball] at hz
      obtain ⟨n, hn⟩ := (htend.eventually (eventually_gt_nhds hz)).exists
      exact Set.mem_iUnion.2 ⟨n, Metric.mem_ball.2 hn⟩
  have hballmono : Monotone fun n => Metric.ball c (rn n) := fun m n hmn =>
    Metric.ball_subset_ball (hmono hmn)
  have hRHS : Tendsto (fun n => ∫ z in Metric.ball c (rn n), dzbar f z) atTop
      (𝓝 (∫ z in Metric.ball c R, dzbar f z)) := by
    have hintg : IntegrableOn (dzbar f) (⋃ n, Metric.ball c (rn n)) := by
      rw [hunion]; exact integrableOn_dzbar_ball hR hf
    have h := MeasureTheory.tendsto_setIntegral_of_monotone
      (fun n => measurableSet_ball) hballmono hintg
    rwa [hunion] at h
  -- circle integrals converge, by dominated convergence
  obtain ⟨M', hM'⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hf.continuousOn
  have hctr : ∀ θ : ℝ, Continuous fun r : ℝ => circleMap c r θ := by
    intro θ
    simp only [circleMap]
    fun_prop
  have hcontF : ∀ r : ℝ, (∀ θ : ℝ, circleMap c r θ ∈ Metric.closedBall c R) →
      Continuous fun θ : ℝ => deriv (circleMap c r) θ • f (circleMap c r θ) := by
    intro r hmem
    have h1 : Continuous fun θ : ℝ => deriv (circleMap c r) θ := by
      simp only [deriv_circleMap, circleMap]
      fun_prop
    have h2 : Continuous fun θ : ℝ => f (circleMap c r θ) :=
      hf.continuousOn.comp_continuous (continuous_circleMap c r) hmem
    exact h1.smul h2
  have hLHS : Tendsto (fun n => ∮ z in C(c, rn n), f z) atTop (𝓝 (∮ z in C(c, R), f z)) := by
    simp only [circleIntegral]
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => R * M') (Filter.Eventually.of_forall fun n =>
        (hcontF (rn n) (hmemcb n)).aestronglyMeasurable) ?_ ?_ ?_
    · refine Filter.Eventually.of_forall fun n => ?_
      filter_upwards with θ _
      rw [norm_smul, deriv_circleMap]
      have hexp : ‖Complex.exp ((θ : ℂ) * I)‖ = 1 := by
        simp [Complex.norm_exp_ofReal_mul_I]
      have hd : ‖circleMap 0 (rn n) θ * I‖ = rn n := by
        simp only [circleMap, zero_add, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, hexp, abs_of_nonneg (hrn0 n)]
      rw [hd]
      have h1 : ‖f (circleMap c (rn n) θ)‖ ≤ M' := hM' _ (hmemcb n θ)
      have h2 : (0 : ℝ) ≤ M' := le_trans (norm_nonneg _) h1
      nlinarith [hrn0 n, (hrnR n).le]
    · exact _root_.intervalIntegrable_const
    · filter_upwards with θ _
      have h1 : Tendsto (fun n => circleMap c (rn n) θ) atTop (𝓝 (circleMap c R θ)) :=
        ((hctr θ).tendsto R).comp htend
      have hfc : Tendsto (fun n => f (circleMap c (rn n) θ)) atTop
          (𝓝 (f (circleMap c R θ))) := by
        have hcw : ContinuousWithinAt f (Metric.closedBall c R) (circleMap c R θ) :=
          hf.continuousOn _ (hmemcbR θ)
        exact hcw.tendsto.comp
          (tendsto_nhdsWithin_iff.2 ⟨h1, Filter.Eventually.of_forall fun n => hmemcb n θ⟩)
      have hdc : Tendsto (fun n => deriv (circleMap c (rn n)) θ) atTop
          (𝓝 (deriv (circleMap c R) θ)) := by
        have hc : Tendsto (fun n => ((rn n : ℝ) : ℂ)) atTop (𝓝 ((R : ℝ) : ℂ)) :=
          (Complex.continuous_ofReal.tendsto R).comp htend
        simp only [deriv_circleMap, circleMap, zero_add]
        exact (hc.mul_const _).mul_const _
      exact hdc.smul hfc
  -- conclude
  have hconst : Tendsto (fun n => (2 : ℂ) * I * ∫ z in Metric.ball c (rn n), dzbar f z) atTop
      (𝓝 (2 * I * ∫ z in Metric.ball c R, dzbar f z)) := tendsto_const_nhds.mul hRHS
  have heqfun : (fun n => ∮ z in C(c, rn n), f z)
      = fun n => (2 : ℂ) * I * ∫ z in Metric.ball c (rn n), dzbar f z := funext hstep
  rw [heqfun] at hLHS
  exact tendsto_nhds_unique hLHS hconst

/-- **Green's formula (11.10) on a disc, for `f` of class `C¹` on the closed disc.**
This is the statement of `eq11_10_green_dzbar`. -/
theorem green_disc_dz_closedBall {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContDiffOn ℝ 1 f (Metric.closedBall c R)) :
    (∫ θ in (0 : ℝ)..2 * π, f (circleMap c R θ) * conj (deriv (circleMap c R) θ))
      = -2 * I * ∫ z in Metric.ball c R, dz f z := by
  have hdif : ∀ z ∈ Metric.ball c R, DifferentiableAt ℝ f z := fun z hz =>
    (hf.contDiffAt (Metric.closedBall_mem_nhds_of_mem hz)).differentiableAt one_ne_zero
  have hcg : ContDiffOn ℝ 1 (fun w : ℂ => conj (f w)) (Metric.closedBall c R) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn hf
  have h := green_disc_dzbar_closedBall hR hcg
  have hrw : ∫ z in Metric.ball c R, dzbar (fun w => conj (f w)) z
      = ∫ z in Metric.ball c R, conj (dz f z) :=
    setIntegral_congr_fun measurableSet_ball
      (fun z hz => ((eq6_3 (hdif z hz)).1).symm)
  rw [hrw, integral_conj, circleIntegral] at h
  have hlhs : conj (∫ θ in (0 : ℝ)..2 * π,
        deriv (circleMap c R) θ • conj (f (circleMap c R θ)))
      = ∫ θ in (0 : ℝ)..2 * π, f (circleMap c R θ) * conj (deriv (circleMap c R) θ) := by
    rw [← intervalIntegral_conj]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [smul_eq_mul, map_mul, Complex.conj_conj]
    ring
  have h2 := congrArg (starRingEnd ℂ) h
  rw [hlhs, map_mul, map_mul, Complex.conj_I, map_ofNat, Complex.conj_conj] at h2
  linear_combination h2

/-! ## Transferring integrability into polar coordinates

Mathlib has the Bochner and `lintegral` *changes of variables* for polar coordinates, but no
transfer of **integrability**.  Since the `lintegral` version holds for an arbitrary
`ℝ≥0∞`-valued function, finiteness of `∫⁻ ‖g‖ₑ` transfers, which is what integrability on the
polar region needs. -/

/-- The `lintegral` polar formula on a ball centred at `0`. -/
theorem lintegral_ball_zero_polar (F : ℂ → ℝ≥0∞) (R : ℝ) :
    ∫⁻ w in Metric.ball (0 : ℂ) R, F w
      = ∫⁻ p in Set.Ioo 0 R ×ˢ Set.Ioo (-π) π,
          ENNReal.ofReal p.1 * F (Complex.polarCoord.symm p) := by
  have hpolar := Complex.lintegral_comp_polarCoord_symm ((Metric.ball (0 : ℂ) R).indicator F)
  rw [lintegral_indicator measurableSet_ball] at hpolar
  rw [← hpolar]
  have hc : Continuous fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
    have he : (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
        = fun p : ℝ × ℝ => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * I) := by
      funext p
      exact Complex.polarCoord_symm_apply p
    rw [he]
    fun_prop
  have hpt : ∀ p : ℝ × ℝ,
      ENNReal.ofReal p.1 • ((Metric.ball (0 : ℂ) R).indicator F) (Complex.polarCoord.symm p)
        = (Complex.polarCoord.symm ⁻¹' Metric.ball (0 : ℂ) R).indicator
            (fun q : ℝ × ℝ => ENNReal.ofReal q.1 * F (Complex.polarCoord.symm q)) p := by
    intro p
    by_cases h : Complex.polarCoord.symm p ∈ Metric.ball (0 : ℂ) R
    · have hp : p ∈ Complex.polarCoord.symm ⁻¹' Metric.ball (0 : ℂ) R := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem hp, smul_eq_mul]
    · have hp : p ∉ Complex.polarCoord.symm ⁻¹' Metric.ball (0 : ℂ) R := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem hp, smul_zero]
  simp only [hpt]
  rw [MeasureTheory.setLIntegral_indicator (measurableSet_ball.preimage hc.measurable),
    Set.inter_comm, polarCoord_target_inter_ball]

/-- **Integrability transfers into polar coordinates.** -/
theorem integrableOn_polar_of_integrableOn_ball {g : ℂ → ℂ} {R : ℝ}
    (hmeas : Measurable g) (hint : IntegrableOn g (Metric.ball (0 : ℂ) R)) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * g (Complex.polarCoord.symm p))
      (Set.Ioo 0 R ×ˢ Set.Ioo (-π) π) := by
  have hc : Continuous fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
    have he : (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
        = fun p : ℝ × ℝ => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * I) := by
      funext p
      exact Complex.polarCoord_symm_apply p
    rw [he]
    fun_prop
  refine ⟨((Complex.continuous_ofReal.comp continuous_fst).measurable.mul
    (hmeas.comp hc.measurable)).aestronglyMeasurable.restrict, ?_⟩
  have hkey : ∫⁻ p in Set.Ioo 0 R ×ˢ Set.Ioo (-π) π,
      ‖(p.1 : ℂ) * g (Complex.polarCoord.symm p)‖ₑ
      = ∫⁻ w in Metric.ball (0 : ℂ) R, ‖g w‖ₑ := by
    rw [lintegral_ball_zero_polar (fun w => ‖g w‖ₑ) R]
    refine setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) fun p hp => ?_
    rw [enorm_mul]
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp.1.1]
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm, hkey]
  exact hint.2

end LiZhongQC
