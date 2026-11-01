import LiZhongQC.Ch01.S10_AnalyticDefinition
import LiZhongQC.Lemmas.Pompeiu
import LiZhongQC.Lemmas.LpDuality
import LiZhongQC.Lemmas.CZDecomposition

/-!
# §11 两个积分算子 — Two integral operators

* the Cauchy transform `T(ω)` (11.1) and `T_D(ω)` (11.7)     — `cauchyT`, `cauchyTOn`
* Lemma 11.1 (boundedness), Lemma 11.2 (Hölder continuity), (11.8)
* the complex Green formulas (11.9), (11.10) and Pompeiu's formula (11.11), also for
  functions with `L_p` (`p > 2`) generalized derivatives
* the Hilbert (Beurling) transform `H(ω)` as a Cauchy principal value (11.15) — `hilbertH`
* the Zygmund–Calderón inequality and the norm `Λ_p` (11.16)  — `hilbertNorm`
* (11.17) and Theorem 11.1 (derivatives of `T(ω)`)
* Theorem 11.2 (Riesz–Thorin: `ln Λ_p` is convex in `1/p`)
* Theorem 11.3 (`H` is an isometry of `L₂`) and its corollaries `Λ₂ = 1`, `Λ_p → 1`

## What is proved here

Proved here: **Lemma 11.1** (boundedness of `T`), by Hölder's inequality together with the
potential-theoretic estimate `∬_{|ζ| ≤ R} |ζ - z|^{-q} ≤ C(q, R)` for the conjugate exponent
`q = p/(p-1) < 2` (`lintegral_ball_enorm_rpow_neg_ne_top`,
`lintegral_closedBall_enorm_sub_rpow_neg_le`); the identity `∬_{r < |ζ - z| < R} (ζ - z)^{-2} = 0`
of §11.3 (`integral_annulus_inv_sq`), obtained from rotation invariance instead of the book's
Green formula; and the two corollaries of Theorem 11.3 (from Theorem 11.3 itself).

Also proved: the **complex Green formulas (11.9) and (11.10) on a disc** (`eq11_9_green_dz`,
`eq11_10_green_dzbar`).  Mathlib's divergence theorem is box-shaped, so these are obtained
instead by differentiating the circle integral in the radius — see `Lemmas/GreenDisc.lean` for
the identity `∂_r[f·ire^{iθ}] - ∂_θ[f·e^{iθ}] = 2i r ∂_z̄ f`, which kills the angular term over a
period, and `Lemmas/GreenPolar.lean` for polar coordinates, the cutoff that localizes the
hypothesis, and the exhaustion `R' ↑ R` that reaches `C¹` on the closed disc.

Also proved: **(11.19)**, `z̄ = -(1/π) ∬_{|ζ| < R} dA/(ζ - z)` for `|z| < R`.  Mathlib has the
polar change of variables for both the Bochner and the `lintegral`, but no transfer of
*integrability*, so `integrableOn_polar_of_integrableOn_ball` (in `Lemmas/GreenPolar.lean`)
carries finiteness across through the `lintegral` version; each `θ`-integral is then a contour
integral of `1/(w(w-z))`, which partial fractions evaluate to `0` for `|z| < r` (both residues
cancel) and to `-2πi/z` for `r < |z|` (only the pole at `0` is enclosed).

Also proved: **the Pompeiu formula (11.11) on a disc**.  The textbook derivation applies
Green's formula on the non-concentric annulus `ball c R \ closedBall z₀ ε`, for which Mathlib
has no Stokes theorem.  `Lemmas/Pompeiu.lean` avoids it: the Cauchy kernel is multiplied by a
smooth cutoff vanishing near `z₀`, which makes the product `C¹` across the pole, and the
*concentric* disc formula is then applied twice — on `ball c R` and on `ball z₀ ε` — to the same
cutoff function, so the term carrying `∂_z̄ χ` is identical in both and cancels on subtraction
(`circleIntegral_sub_circleIntegral_eq`).  Letting `ε ↓ 0` then needs only two standard limits:
`Real.circleAverage f z₀ ε → f z₀`, and the exhaustion of `ball c R` by the punctured discs,
whose integrand is integrable by `integrableOn_dzbar_div_sub`.

Also proved:
* **(11.8)**, by differentiating under the integral sign off `D̄`.
* **Pompeiu's formula for `L_p` generalized derivatives** (`eq11_11_pompeiu_gen`), as the limit
  of Pompeiu's formula for the `C¹` approximations.  The area terms are controlled by Hölder's
  inequality against the Cauchy kernel in `L_q`, `q < 2`.
* **(11.15)**, the existence of the principal value for `ω ∈ C₀^∞`.  It follows from the annulus
  identity above and the Lipschitz bound `|ω(ζ) - ω(z)| ≤ L|ζ - z|`.
* **(11.17)**, `T(ω) ∈ C¹` with `∂_z̄ T(ω) = ω` and `∂_z T(ω) = H(ω)`.  `T(ω)` is a convolution
  with a locally integrable kernel, `∂_z̄` comes from Pompeiu's formula, and `∂_z` from Green's
  formula for `∂_z` applied twice to one cutoff function, as in `Lemmas/Pompeiu.lean`.
* **Theorem 11.1**, by mollifying `ω` (`t5Mollify`, reusing §9's Lemma 9.2 (⇒) approximate-identity
  machinery), applying (11.17) to each smooth mollification, and passing to the limit: `T(ω_n) → T(ω)`
  uniformly by Lemma 11.1 (the mollifications and `ω` share one bounded support), and the mollified
  partials converge in `L_p` using only `hilbertH_memLp` and (11.16) — no Calderón–Zygmund beyond
  those two facts is needed for this particular theorem.
* **Theorem 11.3** (`H` is an isometry of `L₂`), by the book's own double-Green argument rather
  than Fourier/Plancherel (absent from Mathlib): for `ω ∈ C₀^∞`, applying the complex Green
  formulas (11.9)/(11.10) twice — to `T(ω)·conj(H(ω))` and to `T(ω)·conj(ω)` — on a disc large
  enough to contain `ω`'s support, and subtracting to cancel the shared term, expresses
  `∫‖Hω‖² - ∫‖ω‖²` restricted to that disc as a boundary/circle integral that vanishes as the
  disc radius `R → ∞` (both `T(ω)` and `H(ω) = T(∂_zω)` decay `O(1/|z|)`, against an `O(R)`
  circumference).  General `ω ∈ L₂` follows by density (`C₀^∞` is dense in `L₂`, combining
  Mathlib's compact-support truncation with `t5Mollify`'s smoothing) and extension by continuity,
  using (11.16) at `p = 2` and the a.e. additivity `hilbertH_sub_ae` to control `H(ω) - H(φₙ)` for
  a smooth approximating sequence `φₙ → ω`.

The other statements are kept as `sorry`: the book's remaining proofs rest on two results it
quotes from the literature, the Zygmund–Calderón inequality and the Riesz–Thorin interpolation
theorem, neither of which is in Mathlib (there is no Calderón–Zygmund theory, no singular
integrals and no interpolation there at all).  These gate `hilbertH_memLp` → `eq11_16`, the
bound the §12 contraction needs (and now also Theorem 11.3's extension step), and
`hilbertNorm_continuousOn`, the exponent choice.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC


/-! ## The operator `T` -/

/-- (11.1): `T(ω)(z) = -(1/π) ∬_ℂ ω(ζ)/(ζ - z) dξ dη`. -/
def cauchyT (ω : ℂ → ℂ) (z : ℂ) : ℂ := -(1 / π : ℂ) * ∫ ζ, ω ζ / (ζ - z)

/-- (11.7): `T_D(ω)(z) = -(1/π) ∬_D ω(ζ)/(ζ - z) dξ dη`. -/
def cauchyTOn (D : Set ℂ) (ω : ℂ → ℂ) (z : ℂ) : ℂ := -(1 / π : ℂ) * ∫ ζ in D, ω ζ / (ζ - z)

/-- The target of the polar coordinate chart of `ℂ`, as a product of intervals. -/
theorem polarCoord_target_eq :
    (polarCoord.target : Set (ℝ × ℝ)) = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl

/-- The radial integral inside a disc: `∬_{|w| < ρ} |w|^{-a} dξ dη = 2π ρ^{2-a}/(2-a)`
for `a < 2`.  Together with `lintegral_compl_ball_enorm_rpow_neg` this is the
potential-theoretic input of §11.1. -/
theorem lintegral_ball_enorm_rpow_neg {a : ℝ} (ha : a < 2) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫⁻ w in ball (0 : ℂ) ρ, ‖w‖ₑ ^ (-a)) =
      ENNReal.ofReal (2 * π) * ENNReal.ofReal (ρ ^ (2 - a) / (2 - a)) := by
  have h2a : (0 : ℝ) < 2 - a := by linarith
  have key : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • (ball (0 : ℂ) ρ).indicator (fun w : ℂ => ‖w‖ₑ ^ (-a))
          (Complex.polarCoord.symm p)
        = (Ioo 0 ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (1 - a))) p.1 := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    have hr0 : (0 : ℝ) < r := hr
    have hnorm : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
      rw [Complex.norm_polarCoord_symm]
      exact abs_of_pos hr0
    by_cases hrρ : r < ρ
    · have hmem : Complex.polarCoord.symm (r, θ) ∈ ball (0 : ℂ) ρ := by
        simpa [mem_ball, dist_eq_norm, abs_of_pos hr0] using hrρ
      rw [Set.indicator_of_mem hmem,
        Set.indicator_of_mem (show r ∈ Ioo 0 ρ from ⟨hr0, hrρ⟩), smul_eq_mul,
        ← ofReal_norm (Complex.polarCoord.symm (r, θ)), hnorm,
        ENNReal.ofReal_rpow_of_pos hr0, ← ENNReal.ofReal_mul hr0.le]
      congr 1
      rw [sub_eq_add_neg, Real.rpow_add hr0, Real.rpow_one]
    · have hmem : Complex.polarCoord.symm (r, θ) ∉ ball (0 : ℂ) ρ := by
        simpa [mem_ball, dist_eq_norm, abs_of_pos hr0] using hrρ
      have hmem' : r ∉ Ioo 0 ρ := fun h => hrρ h.2
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem', smul_zero]
  have hint : IntegrableOn (fun r : ℝ => r ^ (1 - a)) (Ioo 0 ρ) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hρ).2 (by linarith)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) ρ)] fun r : ℝ => r ^ (1 - a) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with r hr
    exact Real.rpow_nonneg hr.1.le _
  have hexp : (1 : ℝ) - a + 1 = 2 - a := by ring
  have hval : ∫ r in Ioo (0 : ℝ) ρ, r ^ (1 - a) = ρ ^ (2 - a) / (2 - a) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hρ.le,
      integral_rpow (Or.inl (by linarith : (-1 : ℝ) < 1 - a)), hexp,
      Real.zero_rpow (by linarith : (2 : ℝ) - a ≠ 0), sub_zero]
  have hmeas : AEMeasurable (fun x : ℝ × ℝ =>
      (Ioo (0 : ℝ) ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (1 - a))) x.1)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))) :=
    ((((measurable_id.pow_const (1 - a)).ennreal_ofReal).indicator
      measurableSet_Ioo).comp measurable_fst).aemeasurable
  rw [← lintegral_indicator measurableSet_ball, ← Complex.lintegral_comp_polarCoord_symm,
    setLIntegral_congr_fun polarCoord.open_target.measurableSet key, polarCoord_target_eq,
    Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict, lintegral_prod _ hmeas]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
  rw [show (π : ℝ) - -π = 2 * π from by ring]
  have hsub : Ioo (0 : ℝ) ρ ∩ Ioi 0 = Ioo (0 : ℝ) ρ :=
    Set.inter_eq_self_of_subset_left fun x hx => hx.1
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm,
    setLIntegral_indicator measurableSet_Ioo, hsub,
    ← ofReal_integral_eq_lintegral_ofReal hint hnn, hval]

/-- The radial integral outside a disc: `∬_{|w| > ρ} |w|^{-a} dξ dη = 2π (-ρ^{2-a})/(2-a)`
for `a > 2` (the right-hand side is positive, since `2 - a < 0`). -/
theorem lintegral_compl_ball_enorm_rpow_neg {a : ℝ} (ha : 2 < a) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫⁻ w in {w : ℂ | ρ < ‖w‖}, ‖w‖ₑ ^ (-a)) =
      ENNReal.ofReal (2 * π) * ENNReal.ofReal (-ρ ^ (2 - a) / (2 - a)) := by
  have hset : MeasurableSet {w : ℂ | ρ < ‖w‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have key : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • ({w : ℂ | ρ < ‖w‖}).indicator (fun w : ℂ => ‖w‖ₑ ^ (-a))
          (Complex.polarCoord.symm p)
        = (Ioi ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (1 - a))) p.1 := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    have hr0 : (0 : ℝ) < r := hr
    have hnorm : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
      rw [Complex.norm_polarCoord_symm]
      exact abs_of_pos hr0
    by_cases hrρ : ρ < r
    · have hmem : Complex.polarCoord.symm (r, θ) ∈ {w : ℂ | ρ < ‖w‖} := by
        simp only [mem_setOf_eq, hnorm]
        exact hrρ
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show r ∈ Ioi ρ from hrρ),
        smul_eq_mul, ← ofReal_norm (Complex.polarCoord.symm (r, θ)), hnorm,
        ENNReal.ofReal_rpow_of_pos hr0, ← ENNReal.ofReal_mul hr0.le]
      congr 1
      rw [sub_eq_add_neg, Real.rpow_add hr0, Real.rpow_one]
    · have hmem : Complex.polarCoord.symm (r, θ) ∉ {w : ℂ | ρ < ‖w‖} := by
        simp only [mem_setOf_eq, hnorm]
        exact hrρ
      have hmem' : r ∉ Ioi ρ := hrρ
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem', smul_zero]
  have hint : IntegrableOn (fun r : ℝ => r ^ (1 - a)) (Ioi ρ) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hρ
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi ρ)] fun r : ℝ => r ^ (1 - a) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact Real.rpow_nonneg (hρ.trans hr).le _
  have hexp : (1 : ℝ) - a + 1 = 2 - a := by ring
  have hval : ∫ r in Ioi ρ, r ^ (1 - a) = -ρ ^ (2 - a) / (2 - a) := by
    rw [integral_Ioi_rpow_of_lt (by linarith : (1 : ℝ) - a < -1) hρ, hexp]
  have hmeas : AEMeasurable (fun x : ℝ × ℝ =>
      (Ioi ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (1 - a))) x.1)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))) :=
    ((((measurable_id.pow_const (1 - a)).ennreal_ofReal).indicator
      measurableSet_Ioi).comp measurable_fst).aemeasurable
  rw [← lintegral_indicator hset, ← Complex.lintegral_comp_polarCoord_symm,
    setLIntegral_congr_fun polarCoord.open_target.measurableSet key, polarCoord_target_eq,
    Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict, lintegral_prod _ hmeas]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
  rw [show (π : ℝ) - -π = 2 * π from by ring]
  have hsub : Ioi ρ ∩ Ioi (0 : ℝ) = Ioi ρ :=
    Set.inter_eq_self_of_subset_left fun x hx => hρ.trans hx
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm,
    setLIntegral_indicator measurableSet_Ioi, hsub,
    ← ofReal_integral_eq_lintegral_ofReal hint hnn, hval]

/-- The potential-theoretic estimate behind Lemma 11.1: for `0 ≤ q < 2` the integral of
`|w|^{-q}` over a disc is finite (the exponent is smaller than the dimension `2`). -/
theorem lintegral_ball_enorm_rpow_neg_ne_top {q : ℝ} (_hq0 : 0 ≤ q) (hq2 : q < 2) (R : ℝ) :
    (∫⁻ w in ball (0 : ℂ) R, ‖w‖ₑ ^ (-q)) ≠ ⊤ := by
  have hfin : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  have hint : IntegrableOn (fun w : ℂ => ‖w‖ ^ (-q)) (ball 0 R) volume := by
    refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := q) (by rw [hfin]; norm_num) ?_
      (Filter.Eventually.of_forall fun w => ?_)
      (continuous_norm.measurable.pow_const (-q)).aestronglyMeasurable
    · rw [hfin]; exact_mod_cast hq2
    · rw [one_mul]
      exact le_of_eq (Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg w) _))
  have hae : (fun w : ℂ => ‖(‖w‖ ^ (-q) : ℝ)‖ₑ) =ᵐ[volume.restrict (ball (0 : ℂ) R)]
      fun w : ℂ => ‖w‖ₑ ^ (-q) := by
    have h0 : ∀ᵐ w : ℂ, w ≠ 0 := by
      rw [ae_iff]
      have hs : {w : ℂ | ¬ w ≠ 0} = {(0 : ℂ)} := by ext w; simp
      rw [hs]
      exact measure_singleton 0
    filter_upwards [ae_restrict_of_ae h0] with w hw
    have hwn : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hw
    rw [← ofReal_norm ((‖w‖ : ℝ) ^ (-q)), ← ofReal_norm w,
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg w) _),
      ENNReal.ofReal_rpow_of_pos hwn]
  rw [← lintegral_congr_ae hae]
  exact hint.hasFiniteIntegral.ne

/-- The estimate of `∬_{|ζ| ≤ R} |ζ - z|^{-q}` used in Lemma 11.1: cutting the disc `|ζ| ≤ R`
along `|ζ - z| < R` gives a bound that does not depend on `z`. -/
theorem lintegral_closedBall_enorm_sub_rpow_neg_le {q : ℝ} (hq0 : 0 < q) {R : ℝ} (hR : 0 < R)
    (z : ℂ) :
    (∫⁻ ζ in closedBall (0 : ℂ) R, ‖ζ - z‖ₑ ^ (-q)) ≤
      (∫⁻ w in ball (0 : ℂ) R, ‖w‖ₑ ^ (-q)) +
        ENNReal.ofReal (R ^ (-q)) * volume (closedBall (0 : ℂ) R) := by
  rw [← lintegral_inter_add_diff (B := ball z R) _ _ measurableSet_ball]
  refine add_le_add ?_ ?_
  · -- the part near `z`: translate to the disc centred at the origin
    refine (lintegral_mono' (Measure.restrict_mono inter_subset_right le_rfl) le_rfl).trans
      (le_of_eq ?_)
    have hemb : MeasurableEmbedding (fun w : ℂ => w + z) :=
      (Homeomorph.addRight z).isClosedEmbedding.measurableEmbedding
    have hpre : (fun w : ℂ => w + z) ⁻¹' ball z R = ball (0 : ℂ) R := by
      ext w
      simp [mem_ball, dist_eq_norm]
    have h := (measurePreserving_add_right volume z).setLIntegral_comp_preimage_emb hemb
      (fun ζ => ‖ζ - z‖ₑ ^ (-q)) (ball z R)
    rw [hpre] at h
    simp only [add_sub_cancel_right] at h
    exact h.symm
  · -- away from `z` the integrand is at most `R^{-q}`
    have hmeas : MeasurableSet (closedBall (0 : ℂ) R \ ball z R) :=
      measurableSet_closedBall.diff measurableSet_ball
    have hle : ∀ ζ ∈ closedBall (0 : ℂ) R \ ball z R,
        ‖ζ - z‖ₑ ^ (-q) ≤ ENNReal.ofReal (R ^ (-q)) := by
      intro ζ hζ
      have hgeR : R ≤ ‖ζ - z‖ := by
        have h2 := hζ.2
        simp only [mem_ball, dist_eq_norm, not_lt] at h2
        exact h2
      have hR' : ENNReal.ofReal R ≤ ‖ζ - z‖ₑ := by
        rw [← ofReal_norm (ζ - z)]
        exact ENNReal.ofReal_le_ofReal hgeR
      rw [← ENNReal.ofReal_rpow_of_pos hR, ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv' (ENNReal.rpow_le_rpow hR' hq0.le)
    calc (∫⁻ ζ in closedBall (0 : ℂ) R \ ball z R, ‖ζ - z‖ₑ ^ (-q))
        ≤ ∫⁻ _ in closedBall (0 : ℂ) R \ ball z R, ENNReal.ofReal (R ^ (-q)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [self_mem_ae_restrict hmeas] with ζ hζ using hle ζ hζ
      _ = ENNReal.ofReal (R ^ (-q)) * volume (closedBall (0 : ℂ) R \ ball z R) := by
          rw [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ENNReal.ofReal (R ^ (-q)) * volume (closedBall (0 : ℂ) R) :=
          mul_le_mul' le_rfl (measure_mono diff_subset)

/-- **Lemma 11.1**: if `ω ∈ L_p(D_R)`, `p > 2`, vanishes outside `D_R = {|z| ≤ R}`, then `T(ω)` is
bounded on `ℂ`, `|T_ω(z)| ≤ M₁ ‖ω‖_p`, with `M₁` depending only on `p` and `R`. -/
theorem lemma11_1 {p : ℝ} (hp : 2 < p) {R : ℝ} (hR : 0 < R) :
    ∃ M₁ : ℝ, ∀ ω : ℂ → ℂ, MemLp ω (ENNReal.ofReal p) → (∀ z, R < ‖z‖ → ω z = 0) →
      ∀ z, ‖cauchyT ω z‖ ≤ M₁ * (eLpNorm ω (ENNReal.ofReal p)).toReal := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hpne : p ≠ 0 := hp0.ne'
  have hp1ne : p - 1 ≠ 0 := hp1.ne'
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = p / (p - 1) := ⟨_, rfl⟩
  have hq0 : 0 < q := by
    rw [hq]
    exact div_pos hp0 hp1
  have hq2 : q < 2 := by
    rw [hq, div_lt_iff₀ hp1]
    linarith
  have hpq : p.HolderConjugate q := by
    refine ⟨?_, hp0, hq0⟩
    rw [hq, inv_one]
    field_simp
    ring
  -- the constant: `∬_{|ζ| ≤ R} |ζ - z|^{-q}` is bounded uniformly in `z`
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0∞, C = (∫⁻ w in ball (0 : ℂ) R, ‖w‖ₑ ^ (-q)) +
      ENNReal.ofReal (R ^ (-q)) * volume (closedBall (0 : ℂ) R) := ⟨_, rfl⟩
  have hCne : C ≠ ⊤ := by
    rw [hC]
    exact ENNReal.add_ne_top.2 ⟨lintegral_ball_enorm_rpow_neg_ne_top hq0.le hq2 R,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ≥0∞, A = C ^ (1 / q) := ⟨_, rfl⟩
  have hAne : A ≠ ⊤ := by
    rw [hA]
    exact ENNReal.rpow_ne_top_of_nonneg (div_nonneg zero_le_one hq0.le) hCne
  refine ⟨1 / π * A.toReal, fun ω hω hsupp z => ?_⟩
  have hSm : MeasurableSet (closedBall (0 : ℂ) R) := measurableSet_closedBall
  have hLtop : eLpNorm ω (ENNReal.ofReal p) ≠ ⊤ := hω.eLpNorm_ne_top
  have hpne0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  -- the pointwise bound `|ω(ζ)/(ζ - z)| ≤ 1_{D_R}(ζ) |ω(ζ)| |ζ - z|^{-1}`
  have hsub : ∀ ζ : ℂ, ‖ω ζ / (ζ - z)‖ₑ ≤
      (closedBall (0 : ℂ) R).indicator (fun ζ => ‖ω ζ‖ₑ * ‖ζ - z‖ₑ⁻¹) ζ := by
    intro ζ
    by_cases hζ : ζ ∈ closedBall (0 : ℂ) R
    · rw [Set.indicator_of_mem hζ]
      rcases eq_or_ne ζ z with rfl | hne
      · simp
      · have hb : (0 : ℝ) < ‖ζ - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
        refine le_of_eq ?_
        rw [← ofReal_norm (ω ζ / (ζ - z)), ← ofReal_norm (ω ζ), ← ofReal_norm (ζ - z),
          norm_div, ENNReal.ofReal_div_of_pos hb, div_eq_mul_inv]
    · rw [Set.indicator_of_notMem hζ]
      have hz0 : ω ζ = 0 := hsupp ζ (by simpa [mem_closedBall_zero_iff, not_le] using hζ)
      simp [hz0]
  -- Hölder's inequality
  have hkey : ‖cauchyT ω z‖ₑ ≤
      ENNReal.ofReal (1 / π) * (eLpNorm ω (ENNReal.ofReal p) * A) := by
    rw [cauchyT, enorm_mul]
    refine mul_le_mul' (le_of_eq ?_) ?_
    · rw [← ofReal_norm (-(1 / π : ℂ))]
      congr 1
      rw [norm_neg, norm_div, norm_one, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le]
    · refine (enorm_integral_le_lintegral_enorm _).trans ?_
      refine (lintegral_mono hsub).trans ?_
      rw [lintegral_indicator hSm]
      have h := ENNReal.lintegral_mul_le_Lp_mul_Lq
        (volume.restrict (closedBall (0 : ℂ) R)) hpq
        (f := fun ζ => ‖ω ζ‖ₑ) (g := fun ζ : ℂ => ‖ζ - z‖ₑ⁻¹)
        hω.aestronglyMeasurable.aemeasurable.enorm.restrict
        ((measurable_id.sub_const z).enorm.inv.aemeasurable)
      simp only [Pi.mul_apply] at h
      refine h.trans ?_
      refine mul_le_mul' ?_ ?_
      · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne0 ENNReal.ofReal_ne_top
          hω.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
        exact ENNReal.rpow_le_rpow (lintegral_mono' Measure.restrict_le_self le_rfl)
          (div_nonneg zero_le_one hp0.le)
      · have hg : ∀ ζ : ℂ, (‖ζ - z‖ₑ⁻¹) ^ q = ‖ζ - z‖ₑ ^ (-q) := fun ζ => by
          rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg]
        simp only [hg]
        rw [hA]
        refine ENNReal.rpow_le_rpow ?_ (div_nonneg zero_le_one hq0.le)
        rw [hC]
        exact lintegral_closedBall_enorm_sub_rpow_neg_le hq0 hR z
  have hfin : ENNReal.ofReal (1 / π) * (eLpNorm ω (ENNReal.ofReal p) * A) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hLtop hAne)
  have h1 : (‖cauchyT ω z‖ₑ).toReal ≤
      (ENNReal.ofReal (1 / π) * (eLpNorm ω (ENNReal.ofReal p) * A)).toReal :=
    ENNReal.toReal_mono hfin hkey
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / π),
    toReal_enorm] at h1
  refine h1.trans (le_of_eq ?_)
  ring

/-! ### The two-singularity estimate behind Lemma 11.2

The book bounds `∬ dξ dη /(|ζ - z₁|^q |ζ - z₂|^q)` by rescaling the plane so that the two
singularities sit at `0` and `e^{iθ}`.  We instead cut the plane by which singularity is the
nearer one: on `|ζ - z₁| < d/2` the second factor is harmless, on `|ζ - z₂| < d/2` the first one
is, and on the rest `|ζ - z₂| ≥ |ζ - z₁|/4`, so the integrand is `O(|ζ - z₁|^{-2q})`.  Only
translations and the two radial integrals above are needed. -/

/-- The translated form of `lintegral_ball_enorm_rpow_neg`. -/
theorem lintegral_ball_sub_enorm_rpow_neg {a : ℝ} (ha : a < 2) {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) :
    (∫⁻ ζ in ball z ρ, ‖ζ - z‖ₑ ^ (-a)) =
      ENNReal.ofReal (2 * π) * ENNReal.ofReal (ρ ^ (2 - a) / (2 - a)) := by
  have hemb : MeasurableEmbedding (fun w : ℂ => w + z) :=
    (Homeomorph.addRight z).isClosedEmbedding.measurableEmbedding
  have hpre : (fun w : ℂ => w + z) ⁻¹' ball z ρ = ball (0 : ℂ) ρ := by
    ext w
    simp [mem_ball, dist_eq_norm]
  have h := (measurePreserving_add_right volume z).setLIntegral_comp_preimage_emb hemb
    (fun ζ => ‖ζ - z‖ₑ ^ (-a)) (ball z ρ)
  rw [hpre] at h
  simp only [add_sub_cancel_right] at h
  rw [← h]
  exact lintegral_ball_enorm_rpow_neg ha hρ

/-- The translated form of `lintegral_compl_ball_enorm_rpow_neg`. -/
theorem lintegral_compl_ball_sub_enorm_rpow_neg {a : ℝ} (ha : 2 < a) {ρ : ℝ} (hρ : 0 < ρ)
    (z : ℂ) :
    (∫⁻ ζ in {ζ : ℂ | ρ < ‖ζ - z‖}, ‖ζ - z‖ₑ ^ (-a)) =
      ENNReal.ofReal (2 * π) * ENNReal.ofReal (-ρ ^ (2 - a) / (2 - a)) := by
  have hemb : MeasurableEmbedding (fun w : ℂ => w + z) :=
    (Homeomorph.addRight z).isClosedEmbedding.measurableEmbedding
  have hpre : (fun w : ℂ => w + z) ⁻¹' {ζ : ℂ | ρ < ‖ζ - z‖} = {w : ℂ | ρ < ‖w‖} := by
    ext w
    simp
  have h := (measurePreserving_add_right volume z).setLIntegral_comp_preimage_emb hemb
    (fun ζ => ‖ζ - z‖ₑ ^ (-a)) {ζ : ℂ | ρ < ‖ζ - z‖}
  rw [hpre] at h
  simp only [add_sub_cancel_right] at h
  rw [← h]
  exact lintegral_compl_ball_enorm_rpow_neg ha hρ

/-- `(d/c)^u = d^u * c^{-u}` for positive `d` and `c`. -/
theorem rpow_div_eq {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (u : ℝ) :
    (d / c) ^ u = d ^ u * c ^ (-u) := by
  rw [Real.div_rpow hd.le hc.le, Real.rpow_neg hc.le, div_eq_mul_inv]

/-- The near region: on `|ζ - z| < |z - z'|/2` the singularity at `z'` is harmless. -/
theorem lintegral_near_piece {q : ℝ} (hq0 : 0 < q) (hq2 : q < 2) {z z' : ℂ} (hzz : z ≠ z') :
    (∫⁻ ζ in ball z (‖z - z'‖ / 2), ‖ζ - z‖ₑ ^ (-q) * ‖ζ - z'‖ₑ ^ (-q))
      ≤ (ENNReal.ofReal (2 * π) *
          ENNReal.ofReal ((‖z - z'‖ / 2) ^ (2 - q) / (2 - q))) *
          ENNReal.ofReal ((‖z - z'‖ / 2) ^ (-q)) := by
  have hd : 0 < ‖z - z'‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hzz
  have hhalf : 0 < ‖z - z'‖ / 2 := by linarith
  have hpt : ∀ ζ ∈ ball z (‖z - z'‖ / 2),
      ‖ζ - z‖ₑ ^ (-q) * ‖ζ - z'‖ₑ ^ (-q)
        ≤ ‖ζ - z‖ₑ ^ (-q) * ENNReal.ofReal ((‖z - z'‖ / 2) ^ (-q)) := by
    intro ζ hζ
    have hζz : ‖ζ - z‖ < ‖z - z'‖ / 2 := by
      simpa [mem_ball, dist_eq_norm] using hζ
    have htri : ‖z - z'‖ ≤ ‖z - ζ‖ + ‖ζ - z'‖ := by
      simpa [dist_eq_norm] using dist_triangle z ζ z'
    have hrev : ‖z - ζ‖ = ‖ζ - z‖ := norm_sub_rev z ζ
    have hlow : ‖z - z'‖ / 2 ≤ ‖ζ - z'‖ := by
      rw [hrev] at htri
      linarith
    have hle : ENNReal.ofReal (‖z - z'‖ / 2) ≤ ‖ζ - z'‖ₑ := by
      rw [← ofReal_norm (ζ - z')]
      exact ENNReal.ofReal_le_ofReal hlow
    have hmono : ‖ζ - z'‖ₑ ^ (-q) ≤ ENNReal.ofReal ((‖z - z'‖ / 2) ^ (-q)) := by
      rw [← ENNReal.ofReal_rpow_of_pos hhalf, ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv' (ENNReal.rpow_le_rpow hle hq0.le)
    exact mul_le_mul' le_rfl hmono
  have hstep : (∫⁻ ζ in ball z (‖z - z'‖ / 2), ‖ζ - z‖ₑ ^ (-q) * ‖ζ - z'‖ₑ ^ (-q))
      ≤ ∫⁻ ζ in ball z (‖z - z'‖ / 2),
          ‖ζ - z‖ₑ ^ (-q) * ENNReal.ofReal ((‖z - z'‖ / 2) ^ (-q)) := by
    refine lintegral_mono_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_ball] with ζ hζ using hpt ζ hζ
  rwa [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
    lintegral_ball_sub_enorm_rpow_neg hq2 hhalf z] at hstep

/-- The far region: away from both singularities the integrand is `O(|ζ - z|^{-2q})`. -/
theorem lintegral_far_piece {q : ℝ} (hq1 : 1 < q) {z z' : ℂ} (hzz : z ≠ z') :
    (∫⁻ ζ in (ball z (‖z - z'‖ / 2))ᶜ \ ball z' (‖z - z'‖ / 2),
        ‖ζ - z‖ₑ ^ (-q) * ‖ζ - z'‖ₑ ^ (-q))
      ≤ (ENNReal.ofReal (2 * π) *
          ENNReal.ofReal (-(‖z - z'‖ / 4) ^ (2 - 2 * q) / (2 - 2 * q))) *
          ENNReal.ofReal (4 ^ q) := by
  have hq0 : 0 < q := by linarith
  have hd : 0 < ‖z - z'‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hzz
  have hquarter : 0 < ‖z - z'‖ / 4 := by linarith
  have hpt : ∀ ζ ∈ (ball z (‖z - z'‖ / 2))ᶜ \ ball z' (‖z - z'‖ / 2),
      ‖ζ - z‖ₑ ^ (-q) * ‖ζ - z'‖ₑ ^ (-q)
        ≤ ‖ζ - z‖ₑ ^ (-(2 * q)) * ENNReal.ofReal (4 ^ q) := by
    intro ζ hζ
    have h1 : ‖z - z'‖ / 2 ≤ ‖ζ - z‖ := by
      have h := hζ.1
      simp only [mem_compl_iff, mem_ball, dist_eq_norm, not_lt] at h
      exact h
    have h2 : ‖z - z'‖ / 2 ≤ ‖ζ - z'‖ := by
      have h := hζ.2
      simp only [mem_ball, dist_eq_norm, not_lt] at h
      exact h
    have hz0 : (0 : ℝ) < ‖ζ - z‖ := lt_of_lt_of_le (by linarith) h1
    have htri : ‖ζ - z‖ ≤ ‖ζ - z'‖ + ‖z' - z‖ := by
      simpa [dist_eq_norm] using dist_triangle ζ z' z
    have hrev : ‖z' - z‖ = ‖z - z'‖ := norm_sub_rev z' z
    have hquart : ‖ζ - z‖ / 4 ≤ ‖ζ - z'‖ := by
      rcases le_or_gt ‖ζ - z‖ (2 * ‖z - z'‖) with hc | hc
      · linarith
      · rw [hrev] at htri
        linarith
    have hq4 : (0 : ℝ) < ‖ζ - z‖ / 4 := by linarith
    have hle : ENNReal.ofReal (‖ζ - z‖ / 4) ≤ ‖ζ - z'‖ₑ := by
      rw [← ofReal_norm (ζ - z')]
      exact ENNReal.ofReal_le_ofReal hquart
    have hmono : ‖ζ - z'‖ₑ ^ (-q) ≤ ENNReal.ofReal ((‖ζ - z‖ / 4) ^ (-q)) := by
      rw [← ENNReal.ofReal_rpow_of_pos hq4, ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv' (ENNReal.rpow_le_rpow hle hq0.le)
    have hsplit : ENNReal.ofReal ((‖ζ - z‖ / 4) ^ (-q))
        = ‖ζ - z‖ₑ ^ (-q) * ENNReal.ofReal (4 ^ q) := by
      rw [Real.div_rpow hz0.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4),
        div_inv_eq_mul, ENNReal.ofReal_mul (Real.rpow_nonneg hz0.le _),
        ← ENNReal.ofReal_rpow_of_pos hz0, ofReal_norm]
    have hne0 : ‖ζ - z‖ₑ ≠ 0 := by
      rw [← ofReal_norm (ζ - z), Ne, ENNReal.ofReal_eq_zero, not_le]
      exact hz0
    have hnetop : ‖ζ - z‖ₑ ≠ ⊤ := by
      rw [← ofReal_norm (ζ - z)]
      exact ENNReal.ofReal_ne_top
    have hadd : ‖ζ - z‖ₑ ^ (-q) * ‖ζ - z‖ₑ ^ (-q) = ‖ζ - z‖ₑ ^ (-(2 * q)) := by
      rw [← ENNReal.rpow_add _ _ hne0 hnetop]
      ring_nf
    calc ‖ζ - z‖ₑ ^ (-q) * ‖ζ - z'‖ₑ ^ (-q)
        ≤ ‖ζ - z‖ₑ ^ (-q) * (‖ζ - z‖ₑ ^ (-q) * ENNReal.ofReal (4 ^ q)) := by
          rw [← hsplit]
          exact mul_le_mul' le_rfl hmono
      _ = ‖ζ - z‖ₑ ^ (-(2 * q)) * ENNReal.ofReal (4 ^ q) := by
          rw [← mul_assoc, hadd]
  have hsub : (ball z (‖z - z'‖ / 2))ᶜ \ ball z' (‖z - z'‖ / 2)
      ⊆ {ζ : ℂ | ‖z - z'‖ / 4 < ‖ζ - z‖} := by
    intro ζ hζ
    have h := hζ.1
    simp only [mem_compl_iff, mem_ball, dist_eq_norm, not_lt] at h
    simp only [mem_setOf_eq]
    linarith
  have hstep : (∫⁻ ζ in (ball z (‖z - z'‖ / 2))ᶜ \ ball z' (‖z - z'‖ / 2),
        ‖ζ - z‖ₑ ^ (-q) * ‖ζ - z'‖ₑ ^ (-q))
      ≤ ∫⁻ ζ in {ζ : ℂ | ‖z - z'‖ / 4 < ‖ζ - z‖},
          ‖ζ - z‖ₑ ^ (-(2 * q)) * ENNReal.ofReal (4 ^ q) := by
    refine le_trans (lintegral_mono_ae ?_) (lintegral_mono' (Measure.restrict_mono hsub le_rfl)
      le_rfl)
    filter_upwards [self_mem_ae_restrict (measurableSet_ball.compl.diff measurableSet_ball)]
      with ζ hζ using hpt ζ hζ
  rwa [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
    lintegral_compl_ball_sub_enorm_rpow_neg (by linarith : (2:ℝ) < 2 * q) hquarter z] at hstep

/-- The near region bound, with the constant normalized to `C |z - z'|^{2-2q}`. -/
theorem lintegral_near_piece_le {q : ℝ} (hq0 : 0 < q) (hq2 : q < 2) {z z' : ℂ} (hzz : z ≠ z') :
    (∫⁻ ζ in ball z (‖z - z'‖ / 2), ‖ζ - z‖ₑ ^ (-q) * ‖ζ - z'‖ₑ ^ (-q))
      ≤ ENNReal.ofReal (2 * π / (2 - q) * 2 ^ (2 * q - 2) * ‖z - z'‖ ^ (2 - 2 * q)) := by
  have hd : 0 < ‖z - z'‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hzz
  have hhalf : 0 < ‖z - z'‖ / 2 := by linarith
  have h2q : (0 : ℝ) < 2 - q := by linarith
  have hnn1 : (0 : ℝ) ≤ 2 * π := by positivity
  have hnn2 : (0 : ℝ) ≤ 2 * π * ((‖z - z'‖ / 2) ^ (2 - q) / (2 - q)) :=
    mul_nonneg hnn1 (div_nonneg (Real.rpow_nonneg hhalf.le _) h2q.le)
  refine (lintegral_near_piece hq0 hq2 hzz).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul hnn1, ← ENNReal.ofReal_mul hnn2]
  congr 1
  have hexp : 2 - q + -q = 2 - 2 * q := by ring
  have h1 : (‖z - z'‖ / 2) ^ (2 - q) * (‖z - z'‖ / 2) ^ (-q)
      = ‖z - z'‖ ^ (2 - 2 * q) * 2 ^ (2 * q - 2) := by
    rw [← Real.rpow_add hhalf, hexp, rpow_div_eq hd (by norm_num),
      show -(2 - 2 * q) = 2 * q - 2 from by ring]
  have hre : 2 * π * ((‖z - z'‖ / 2) ^ (2 - q) / (2 - q)) * (‖z - z'‖ / 2) ^ (-q)
      = 2 * π / (2 - q) * ((‖z - z'‖ / 2) ^ (2 - q) * (‖z - z'‖ / 2) ^ (-q)) := by ring
  rw [hre, h1]
  ring

/-- The far region bound, with the constant normalized to `C |z - z'|^{2-2q}`. -/
theorem lintegral_far_piece_le {q : ℝ} (hq1 : 1 < q) {z z' : ℂ} (hzz : z ≠ z') :
    (∫⁻ ζ in (ball z (‖z - z'‖ / 2))ᶜ \ ball z' (‖z - z'‖ / 2),
        ‖ζ - z‖ₑ ^ (-q) * ‖ζ - z'‖ₑ ^ (-q))
      ≤ ENNReal.ofReal (2 * π / (2 * q - 2) * 4 ^ (3 * q - 2) * ‖z - z'‖ ^ (2 - 2 * q)) := by
  have hd : 0 < ‖z - z'‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hzz
  have hquarter : 0 < ‖z - z'‖ / 4 := by linarith
  have h2q2 : (0 : ℝ) < 2 * q - 2 := by linarith
  have hnn1 : (0 : ℝ) ≤ 2 * π := by positivity
  have hnnx : (0 : ℝ) ≤ (‖z - z'‖ / 4) ^ (2 - 2 * q) := Real.rpow_nonneg hquarter.le _
  have hneg : -(‖z - z'‖ / 4) ^ (2 - 2 * q) / (2 - 2 * q)
      = (‖z - z'‖ / 4) ^ (2 - 2 * q) / (2 * q - 2) := by
    rw [neg_div, show (2 : ℝ) * q - 2 = -(2 - 2 * q) from by ring, div_neg]
  have hnn2 : (0 : ℝ) ≤ 2 * π * (-(‖z - z'‖ / 4) ^ (2 - 2 * q) / (2 - 2 * q)) := by
    rw [hneg]
    exact mul_nonneg hnn1 (div_nonneg hnnx h2q2.le)
  refine (lintegral_far_piece hq1 hzz).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul hnn1, ← ENNReal.ofReal_mul hnn2]
  congr 1
  rw [hneg]
  have h4 : (4 : ℝ) ^ (2 * q - 2) * 4 ^ q = 4 ^ (3 * q - 2) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 4)]
    ring_nf
  have h1 : (‖z - z'‖ / 4) ^ (2 - 2 * q) = ‖z - z'‖ ^ (2 - 2 * q) * 4 ^ (2 * q - 2) := by
    rw [rpow_div_eq hd (by norm_num), show -(2 - 2 * q) = 2 * q - 2 from by ring]
  rw [h1, ← h4]
  ring

/-- The two-singularity estimate of §11.1 ((11.5)–(11.6) of the book):
`∬_ℂ dξ dη / (|ζ - z₁|^q |ζ - z₂|^q) ≤ C_q |z₁ - z₂|^{2-2q}` for `1 < q < 2`. -/
theorem lintegral_two_singularities_le {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2) {z₁ z₂ : ℂ}
    (hne : z₁ ≠ z₂) :
    (∫⁻ ζ, ‖ζ - z₁‖ₑ ^ (-q) * ‖ζ - z₂‖ₑ ^ (-q))
      ≤ ENNReal.ofReal ((2 * (2 * π / (2 - q) * 2 ^ (2 * q - 2))
          + 2 * π / (2 * q - 2) * 4 ^ (3 * q - 2)) * ‖z₁ - z₂‖ ^ (2 - 2 * q)) := by
  have hq0 : 0 < q := by linarith
  have hd : 0 < ‖z₁ - z₂‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hne
  have hrev : ‖z₂ - z₁‖ = ‖z₁ - z₂‖ := norm_sub_rev z₂ z₁
  have h2q : (0 : ℝ) < 2 - q := by linarith
  have h2q2 : (0 : ℝ) < 2 * q - 2 := by linarith
  have hC1 : (0 : ℝ) ≤ 2 * π / (2 - q) * 2 ^ (2 * q - 2) * ‖z₁ - z₂‖ ^ (2 - 2 * q) :=
    mul_nonneg (mul_nonneg (div_nonneg (by positivity) h2q.le)
      (Real.rpow_nonneg (by norm_num) _)) (Real.rpow_nonneg hd.le _)
  have hC3 : (0 : ℝ) ≤ 2 * π / (2 * q - 2) * 4 ^ (3 * q - 2) * ‖z₁ - z₂‖ ^ (2 - 2 * q) :=
    mul_nonneg (mul_nonneg (div_nonneg (by positivity) h2q2.le)
      (Real.rpow_nonneg (by norm_num) _)) (Real.rpow_nonneg hd.le _)
  have hsum13 : (0 : ℝ) ≤ 2 * π / (2 - q) * 2 ^ (2 * q - 2) * ‖z₁ - z₂‖ ^ (2 - 2 * q)
      + 2 * π / (2 * q - 2) * 4 ^ (3 * q - 2) * ‖z₁ - z₂‖ ^ (2 - 2 * q) := by linarith
  have e1 : (∫⁻ ζ, ‖ζ - z₁‖ₑ ^ (-q) * ‖ζ - z₂‖ₑ ^ (-q))
      = (∫⁻ ζ in ball z₁ (‖z₁ - z₂‖ / 2), ‖ζ - z₁‖ₑ ^ (-q) * ‖ζ - z₂‖ₑ ^ (-q))
        + ∫⁻ ζ in (ball z₁ (‖z₁ - z₂‖ / 2))ᶜ, ‖ζ - z₁‖ₑ ^ (-q) * ‖ζ - z₂‖ₑ ^ (-q) :=
    (lintegral_add_compl _ measurableSet_ball).symm
  have e2 : (∫⁻ ζ in (ball z₁ (‖z₁ - z₂‖ / 2))ᶜ, ‖ζ - z₁‖ₑ ^ (-q) * ‖ζ - z₂‖ₑ ^ (-q))
      = (∫⁻ ζ in (ball z₁ (‖z₁ - z₂‖ / 2))ᶜ ∩ ball z₂ (‖z₁ - z₂‖ / 2),
            ‖ζ - z₁‖ₑ ^ (-q) * ‖ζ - z₂‖ₑ ^ (-q))
        + ∫⁻ ζ in (ball z₁ (‖z₁ - z₂‖ / 2))ᶜ \ ball z₂ (‖z₁ - z₂‖ / 2),
            ‖ζ - z₁‖ₑ ^ (-q) * ‖ζ - z₂‖ₑ ^ (-q) :=
    (lintegral_inter_add_diff _ _ measurableSet_ball).symm
  have p1 : (∫⁻ ζ in ball z₁ (‖z₁ - z₂‖ / 2), ‖ζ - z₁‖ₑ ^ (-q) * ‖ζ - z₂‖ₑ ^ (-q))
      ≤ ENNReal.ofReal (2 * π / (2 - q) * 2 ^ (2 * q - 2) * ‖z₁ - z₂‖ ^ (2 - 2 * q)) :=
    lintegral_near_piece_le hq0 hq2 hne
  have p2 : (∫⁻ ζ in (ball z₁ (‖z₁ - z₂‖ / 2))ᶜ ∩ ball z₂ (‖z₁ - z₂‖ / 2),
        ‖ζ - z₁‖ₑ ^ (-q) * ‖ζ - z₂‖ₑ ^ (-q))
      ≤ ENNReal.ofReal (2 * π / (2 - q) * 2 ^ (2 * q - 2) * ‖z₁ - z₂‖ ^ (2 - 2 * q)) := by
    have hmono : (∫⁻ ζ in (ball z₁ (‖z₁ - z₂‖ / 2))ᶜ ∩ ball z₂ (‖z₁ - z₂‖ / 2),
          ‖ζ - z₁‖ₑ ^ (-q) * ‖ζ - z₂‖ₑ ^ (-q))
        ≤ ∫⁻ ζ in ball z₂ (‖z₂ - z₁‖ / 2), ‖ζ - z₂‖ₑ ^ (-q) * ‖ζ - z₁‖ₑ ^ (-q) := by
      rw [hrev]
      refine lintegral_mono' (Measure.restrict_mono inter_subset_right le_rfl) ?_
      intro ζ
      exact le_of_eq (mul_comm _ _)
    refine hmono.trans ?_
    rw [← hrev]
    exact lintegral_near_piece_le hq0 hq2 hne.symm
  have p3 : (∫⁻ ζ in (ball z₁ (‖z₁ - z₂‖ / 2))ᶜ \ ball z₂ (‖z₁ - z₂‖ / 2),
        ‖ζ - z₁‖ₑ ^ (-q) * ‖ζ - z₂‖ₑ ^ (-q))
      ≤ ENNReal.ofReal (2 * π / (2 * q - 2) * 4 ^ (3 * q - 2) * ‖z₁ - z₂‖ ^ (2 - 2 * q)) :=
    lintegral_far_piece_le hq1 hne
  rw [e1, e2]
  refine (add_le_add p1 (add_le_add p2 p3)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add hC1 hC3, ← ENNReal.ofReal_add hC1 hsum13]
  congr 1
  ring

/-! ### Hölder continuity of `T` (Lemma 11.2)

For `ω ∈ L_p(ℂ)` with no support hypothesis the individual integrals `∫ ω(ζ)/(ζ - z)` need not
converge, so `T_ω(z)` may be the junk value `0`.  The two integrands nevertheless differ by an
integrable function (`integrable_cauchy_kernel_sub`), hence are integrable together or not at
all; when neither is, both sides of (11.3) vanish. -/

/-- Hölder's inequality applied to the difference kernel. -/
theorem lintegral_enorm_mul_inv_le {p q : ℝ} (hp : 2 < p) (hpq : p.HolderConjugate q)
    (hq1 : 1 < q) (hq2 : q < 2) {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p)) {z₁ z₂ : ℂ}
    (hne : z₁ ≠ z₂) :
    (∫⁻ ζ, ‖ω ζ‖ₑ * (‖ζ - z₁‖ₑ⁻¹ * ‖ζ - z₂‖ₑ⁻¹))
      ≤ eLpNorm ω (ENNReal.ofReal p) *
        (ENNReal.ofReal ((2 * (2 * π / (2 - q) * 2 ^ (2 * q - 2))
          + 2 * π / (2 * q - 2) * 4 ^ (3 * q - 2)) * ‖z₁ - z₂‖ ^ (2 - 2 * q))) ^ (1 / q) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hpne0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq
    (f := fun ζ => ‖ω ζ‖ₑ) (g := fun ζ : ℂ => ‖ζ - z₁‖ₑ⁻¹ * ‖ζ - z₂‖ₑ⁻¹)
    hω.aestronglyMeasurable.aemeasurable.enorm
    ((((measurable_id.sub_const z₁).enorm.inv).mul
      ((measurable_id.sub_const z₂).enorm.inv)).aemeasurable)
  simp only [Pi.mul_apply] at h
  refine h.trans ?_
  refine mul_le_mul' ?_ ?_
  · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne0 ENNReal.ofReal_ne_top
      hω.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
  · have hg : ∀ ζ : ℂ, (‖ζ - z₁‖ₑ⁻¹ * ‖ζ - z₂‖ₑ⁻¹) ^ q
        = ‖ζ - z₁‖ₑ ^ (-q) * ‖ζ - z₂‖ₑ ^ (-q) := by
      intro ζ
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ENNReal.inv_rpow, ENNReal.inv_rpow,
        ← ENNReal.rpow_neg, ← ENNReal.rpow_neg]
    simp only [hg]
    exact ENNReal.rpow_le_rpow (lintegral_two_singularities_le hq1 hq2 hne)
      (div_nonneg zero_le_one hq0.le)

/-- The difference of the two Cauchy kernels. -/
theorem cauchy_kernel_sub (ω : ℂ → ℂ) {z₁ z₂ ζ : ℂ} (h1 : ζ ≠ z₁) (h2 : ζ ≠ z₂) :
    ω ζ / (ζ - z₁) - ω ζ / (ζ - z₂) = ω ζ * (z₁ - z₂) / ((ζ - z₁) * (ζ - z₂)) := by
  have hd1 : ζ - z₁ ≠ 0 := sub_ne_zero.2 h1
  have hd2 : ζ - z₂ ≠ 0 := sub_ne_zero.2 h2
  rw [div_sub_div _ _ hd1 hd2]
  congr 1
  ring

/-- The `enorm` of the difference kernel. -/
theorem enorm_cauchy_kernel_sub (ω : ℂ → ℂ) {z₁ z₂ ζ : ℂ} (h1 : ζ ≠ z₁) (h2 : ζ ≠ z₂) :
    ‖ω ζ / (ζ - z₁) - ω ζ / (ζ - z₂)‖ₑ
      = ENNReal.ofReal ‖z₁ - z₂‖ * (‖ω ζ‖ₑ * (‖ζ - z₁‖ₑ⁻¹ * ‖ζ - z₂‖ₑ⁻¹)) := by
  have hd1 : (0 : ℝ) < ‖ζ - z₁‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact h1
  have hd2 : (0 : ℝ) < ‖ζ - z₂‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact h2
  have hreal : ‖ω ζ * (z₁ - z₂) / ((ζ - z₁) * (ζ - z₂))‖
      = ‖z₁ - z₂‖ * (‖ω ζ‖ * (‖ζ - z₁‖⁻¹ * ‖ζ - z₂‖⁻¹)) := by
    rw [norm_div, norm_mul, norm_mul, div_eq_mul_inv, mul_inv]
    ring
  rw [cauchy_kernel_sub ω h1 h2, ← ofReal_norm, hreal,
    ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (norm_nonneg _),
    ENNReal.ofReal_mul (inv_nonneg.2 hd1.le),
    ENNReal.ofReal_inv_of_pos hd1, ENNReal.ofReal_inv_of_pos hd2]
  simp only [ofReal_norm]

/-- Almost every point differs from a given one. -/
theorem ae_ne (z : ℂ) : ∀ᵐ ζ : ℂ, ζ ≠ z := by
  rw [ae_iff]
  have hs : {ζ : ℂ | ¬ ζ ≠ z} = {z} := by
    ext ζ
    simp
  rw [hs]
  exact measure_singleton z

/-- The difference of the two Cauchy integrands is integrable, even though each one separately
need not be. -/
theorem integrable_cauchy_kernel_sub {p q : ℝ} (hp : 2 < p) (hpq : p.HolderConjugate q)
    (hq1 : 1 < q) (hq2 : q < 2) {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p)) {z₁ z₂ : ℂ}
    (hne : z₁ ≠ z₂) :
    Integrable (fun ζ => ω ζ / (ζ - z₁) - ω ζ / (ζ - z₂)) := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hmeas : AEStronglyMeasurable (fun ζ => ω ζ / (ζ - z₁) - ω ζ / (ζ - z₂)) volume := by
    have h1 : AEMeasurable (fun ζ : ℂ => ω ζ / (ζ - z₁)) volume :=
      hω.aestronglyMeasurable.aemeasurable.div (measurable_id.sub_const z₁).aemeasurable
    have h2 : AEMeasurable (fun ζ : ℂ => ω ζ / (ζ - z₂)) volume :=
      hω.aestronglyMeasurable.aemeasurable.div (measurable_id.sub_const z₂).aemeasurable
    exact (h1.sub h2).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hae : ∀ᵐ ζ : ℂ, ‖ω ζ / (ζ - z₁) - ω ζ / (ζ - z₂)‖ₑ
      = ENNReal.ofReal ‖z₁ - z₂‖ * (‖ω ζ‖ₑ * (‖ζ - z₁‖ₑ⁻¹ * ‖ζ - z₂‖ₑ⁻¹)) := by
    filter_upwards [ae_ne z₁, ae_ne z₂] with ζ h1 h2
    exact enorm_cauchy_kernel_sub ω h1 h2
  rw [lintegral_congr_ae hae, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  refine lt_of_le_of_lt (lintegral_enorm_mul_inv_le hp hpq hq1 hq2 hω hne) ?_
  exact ENNReal.mul_lt_top hω.eLpNorm_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (div_nonneg zero_le_one hq0.le) ENNReal.ofReal_ne_top)

/-- The two Cauchy integrands are integrable together or not at all. -/
theorem integrable_cauchy_iff {p q : ℝ} (hp : 2 < p) (hpq : p.HolderConjugate q)
    (hq1 : 1 < q) (hq2 : q < 2) {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p)) {z₁ z₂ : ℂ}
    (hne : z₁ ≠ z₂) :
    Integrable (fun ζ => ω ζ / (ζ - z₁)) ↔ Integrable (fun ζ => ω ζ / (ζ - z₂)) := by
  have hdiff := integrable_cauchy_kernel_sub hp hpq hq1 hq2 hω hne
  constructor
  · intro h1
    refine (h1.sub hdiff).congr ?_
    filter_upwards with ζ
    simp
  · intro h2
    refine (h2.add hdiff).congr ?_
    filter_upwards with ζ
    simp

/-- The bound on the integral of the difference. -/
theorem enorm_integral_cauchy_sub_le {p q : ℝ} (hp : 2 < p) (hpq : p.HolderConjugate q)
    (hq1 : 1 < q) (hq2 : q < 2) {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p)) {z₁ z₂ : ℂ}
    (hne : z₁ ≠ z₂) :
    ‖∫ ζ, (ω ζ / (ζ - z₁) - ω ζ / (ζ - z₂))‖ₑ
      ≤ ENNReal.ofReal ‖z₁ - z₂‖ * (eLpNorm ω (ENNReal.ofReal p) *
        (ENNReal.ofReal ((2 * (2 * π / (2 - q) * 2 ^ (2 * q - 2))
          + 2 * π / (2 * q - 2) * 4 ^ (3 * q - 2)) * ‖z₁ - z₂‖ ^ (2 - 2 * q))) ^ (1 / q)) := by
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hae : ∀ᵐ ζ : ℂ, ‖ω ζ / (ζ - z₁) - ω ζ / (ζ - z₂)‖ₑ
      = ENNReal.ofReal ‖z₁ - z₂‖ * (‖ω ζ‖ₑ * (‖ζ - z₁‖ₑ⁻¹ * ‖ζ - z₂‖ₑ⁻¹)) := by
    filter_upwards [ae_ne z₁, ae_ne z₂] with ζ h1 h2
    exact enorm_cauchy_kernel_sub ω h1 h2
  rw [lintegral_congr_ae hae, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul' le_rfl (lintegral_enorm_mul_inv_le hp hpq hq1 hq2 hω hne)

/-- The exponent collapse `d (C d^{2-2q})^{1/q} = C^{1/q} d^{(2-q)/q}`. -/
theorem rpow_collapse_aux {C d q : ℝ} (hC : 0 ≤ C) (hd : 0 < d) (hq0 : 0 < q) :
    d * (C * d ^ (2 - 2 * q)) ^ (1 / q) = C ^ (1 / q) * d ^ ((2 - q) / q) := by
  have hq' : q ≠ 0 := hq0.ne'
  have hsum : (1 : ℝ) + (2 - 2 * q) / q = (2 - q) / q := by
    rw [eq_div_iff hq', add_mul, div_mul_cancel₀ _ hq']
    ring
  rw [Real.mul_rpow hC (Real.rpow_nonneg hd.le _), ← Real.rpow_mul hd.le,
    show (2 - 2 * q) * (1 / q) = (2 - 2 * q) / q from by ring]
  have hdd : d * d ^ ((2 - 2 * q) / q) = d ^ ((2 - q) / q) := by
    rw [← hsum, Real.rpow_add hd, Real.rpow_one]
  rw [← hdd]
  ring

/-- The Hölder exponent: `(2 - q)/q = (p - 2)/p` for the conjugate exponent `q = p/(p-1)`. -/
theorem conj_exponent_sub_div {p q : ℝ} (hp : 2 < p) (hq : q = p / (p - 1)) :
    (2 - q) / q = (p - 2) / p := by
  have hp0 : p ≠ 0 := by intro h; rw [h] at hp; norm_num at hp
  have hp1 : p - 1 ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    linarith
  subst hq
  field_simp
  ring

/-- **Lemma 11.2**: if `ω ∈ L_p(ℂ)`, `p > 2`, then `T_ω` is Hölder continuous with exponent
`α = (p - 2)/p`: `|T_ω(z₁) - T_ω(z₂)| ≤ M₂ ‖ω‖_p |z₁ - z₂|^α`, `M₂` depending only on `p`. -/
theorem lemma11_2 {p : ℝ} (hp : 2 < p) :
    ∃ M₂ : ℝ, ∀ ω : ℂ → ℂ, MemLp ω (ENNReal.ofReal p) → ∀ z₁ z₂ : ℂ,
      ‖cauchyT ω z₁ - cauchyT ω z₂‖ ≤
        M₂ * (eLpNorm ω (ENNReal.ofReal p)).toReal * ‖z₁ - z₂‖ ^ ((p - 2) / p) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = p / (p - 1) := ⟨_, rfl⟩
  have hq0 : 0 < q := by
    rw [hq]
    exact div_pos hp0 hp1
  have hq1 : 1 < q := by
    rw [hq, lt_div_iff₀ hp1]
    linarith
  have hq2 : q < 2 := by
    rw [hq, div_lt_iff₀ hp1]
    linarith
  have hpq : p.HolderConjugate q := by
    refine ⟨?_, hp0, hq0⟩
    rw [hq, inv_one]
    field_simp
    ring
  have h2q : (0 : ℝ) < 2 - q := by linarith
  have h2q2 : (0 : ℝ) < 2 * q - 2 := by linarith
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 2 * (2 * π / (2 - q) * 2 ^ (2 * q - 2))
      + 2 * π / (2 * q - 2) * 4 ^ (3 * q - 2) := ⟨_, rfl⟩
  have hCnn : 0 ≤ C := by
    have t1 : (0 : ℝ) ≤ 2 * π / (2 - q) * 2 ^ (2 * q - 2) :=
      mul_nonneg (div_nonneg (by positivity) h2q.le) (Real.rpow_nonneg (by norm_num) _)
    have t2 : (0 : ℝ) ≤ 2 * π / (2 * q - 2) * 4 ^ (3 * q - 2) :=
      mul_nonneg (div_nonneg (by positivity) h2q2.le) (Real.rpow_nonneg (by norm_num) _)
    rw [hC]
    linarith
  have hα : (0 : ℝ) < (p - 2) / p := div_pos (by linarith) hp0
  have hMnn : (0 : ℝ) ≤ 1 / π * C ^ (1 / q) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hCnn _)
  refine ⟨1 / π * C ^ (1 / q), fun ω hω z₁ z₂ => ?_⟩
  rcases eq_or_ne z₁ z₂ with rfl | hne
  · simp [Real.zero_rpow hα.ne']
  have hd : 0 < ‖z₁ - z₂‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hne
  have hLtop : eLpNorm ω (ENNReal.ofReal p) ≠ ⊤ := hω.eLpNorm_ne_top
  by_cases hint : Integrable (fun ζ => ω ζ / (ζ - z₁))
  · have hint2 : Integrable (fun ζ => ω ζ / (ζ - z₂)) :=
      (integrable_cauchy_iff hp hpq hq1 hq2 hω hne).1 hint
    have hrw : cauchyT ω z₁ - cauchyT ω z₂
        = -(1 / π : ℂ) * ∫ ζ, (ω ζ / (ζ - z₁) - ω ζ / (ζ - z₂)) := by
      rw [cauchyT, cauchyT, ← mul_sub, ← integral_sub hint hint2]
    have hcoef : ‖(-(1 / π : ℂ))‖ₑ = ENNReal.ofReal (1 / π) := by
      rw [← ofReal_norm (-(1 / π : ℂ))]
      congr 1
      rw [norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hkey : ‖cauchyT ω z₁ - cauchyT ω z₂‖ₑ
        ≤ ENNReal.ofReal (1 / π) * (ENNReal.ofReal ‖z₁ - z₂‖ *
          (eLpNorm ω (ENNReal.ofReal p) *
            (ENNReal.ofReal (C * ‖z₁ - z₂‖ ^ (2 - 2 * q))) ^ (1 / q))) := by
      rw [hrw, enorm_mul, hcoef, hC]
      exact mul_le_mul' le_rfl (enorm_integral_cauchy_sub_le hp hpq hq1 hq2 hω hne)
    have hfin : ENNReal.ofReal (1 / π) * (ENNReal.ofReal ‖z₁ - z₂‖ *
        (eLpNorm ω (ENNReal.ofReal p) *
          (ENNReal.ofReal (C * ‖z₁ - z₂‖ ^ (2 - 2 * q))) ^ (1 / q))) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top hLtop
            (ENNReal.rpow_ne_top_of_nonneg (div_nonneg zero_le_one hq0.le)
              ENNReal.ofReal_ne_top)))
    have h1 := ENNReal.toReal_mono hfin hkey
    rw [toReal_enorm] at h1
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 1 / π),
      ENNReal.toReal_ofReal (norm_nonneg _),
      ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ C * ‖z₁ - z₂‖ ^ (2 - 2 * q))] at h1
    refine h1.trans (le_of_eq ?_)
    rw [← conj_exponent_sub_div hp hq]
    linear_combination (1 / π * (eLpNorm ω (ENNReal.ofReal p)).toReal) *
      rpow_collapse_aux hCnn hd hq0
  · have hint2 : ¬ Integrable (fun ζ => ω ζ / (ζ - z₂)) := fun h =>
      hint ((integrable_cauchy_iff hp hpq hq1 hq2 hω hne).2 h)
    rw [cauchyT, cauchyT, integral_undef hint, integral_undef hint2]
    have : (0 : ℝ) ≤ 1 / π * C ^ (1 / q) * (eLpNorm ω (ENNReal.ofReal p)).toReal
        * ‖z₁ - z₂‖ ^ ((p - 2) / p) :=
      mul_nonneg (mul_nonneg hMnn ENNReal.toReal_nonneg) (Real.rpow_nonneg hd.le _)
    simpa using this

/-- (11.8): for a bounded domain `D` and `ω ∈ L_p(D)`, `p > 2`, the function `T_D(ω)` is
holomorphic outside `D̄` and `T_D(ω)(z) = O(1/|z|)` as `z → ∞`.

The book leaves the proof to the reader.  Off `D̄` the kernel `1/(ζ - z)` is bounded, and
`ω ∈ L_p(D) ⊆ L¹(D)` because `D` has finite measure, so the integral can be differentiated in `z`
under the integral sign (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`).  If `D ⊆ {|ζ| ≤ M}`
and `|z| > 2|M| + 1`, then `|ζ - z| ≥ |z|/2` on `D`, hence `|T_D(ω)(z)| ≤ (2/π) ‖ω‖_{L¹(D)} / |z|`. -/
theorem eq11_8 {D : Set ℂ} (hD : Bornology.IsBounded D) {p : ℝ} (hp : 2 < p) {ω : ℂ → ℂ}
    (hω : MemLp ω (ENNReal.ofReal p) (volume.restrict D)) :
    DifferentiableOn ℂ (cauchyTOn D ω) (closure D)ᶜ ∧
      ∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ → ‖cauchyTOn D ω z‖ ≤ C / ‖z‖ := by
  haveI : IsFiniteMeasure (volume.restrict D) :=
    isFiniteMeasure_restrict.2 hD.measure_lt_top.ne
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hint : Integrable ω (volume.restrict D) := hω.integrable hp1
  have hcl : ∀ᵐ ζ ∂(volume.restrict D), ζ ∈ closure D :=
    ae_restrict_of_ae_restrict_of_subset subset_closure
      (ae_restrict_mem isClosed_closure.measurableSet)
  have hmeas : ∀ w : ℂ, AEStronglyMeasurable (fun ζ => ω ζ / (ζ - w)) (volume.restrict D) :=
    fun w => (hint.aestronglyMeasurable.aemeasurable.div
      (measurable_id.sub_const w).aemeasurable).aestronglyMeasurable
  have hmeas2 : ∀ w : ℂ, AEStronglyMeasurable (fun ζ => ω ζ / (ζ - w) ^ 2)
      (volume.restrict D) :=
    fun w => (hint.aestronglyMeasurable.aemeasurable.div
      ((measurable_id.sub_const w).pow_const 2).aemeasurable).aestronglyMeasurable
  have hπn : ‖-(1 / π : ℂ)‖ = 1 / π := by
    rw [norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl z hz
    have hsep : ∀ w ∈ ball z (δ / 2), ∀ ζ ∈ closure D, δ / 2 ≤ ‖ζ - w‖ := by
      intro w hw ζ hζ
      have h1 : δ ≤ dist ζ z := by
        by_contra h
        exact hball (mem_ball.2 (not_le.1 h)) hζ
      have h2 := mem_ball.1 hw
      have h3 : dist ζ z ≤ ‖ζ - w‖ + dist w z := by
        have h := dist_triangle ζ w z
        rwa [dist_eq_norm ζ w] at h
      linarith
    have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict D)
      (F := fun w ζ => ω ζ / (ζ - w)) (F' := fun w ζ => ω ζ / (ζ - w) ^ 2) (x₀ := z)
      (bound := fun ζ => ‖ω ζ‖ * (4 / δ ^ 2)) (ball_mem_nhds z (half_pos hδ))
      (Eventually.of_forall hmeas)
      (by
        refine (hint.norm.mul_const (2 / δ)).mono' (hmeas z) ?_
        filter_upwards [hcl] with ζ hζ
        have hs := hsep z (mem_ball_self (half_pos hδ)) ζ hζ
        have hpos : 0 < ‖ζ - z‖ := by linarith
        rw [norm_div, div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [inv_le_comm₀ hpos (by positivity)]
        calc (2 / δ)⁻¹ = δ / 2 := by rw [inv_div]
          _ ≤ ‖ζ - z‖ := hs)
      (hmeas2 z)
      (by
        filter_upwards [hcl] with ζ hζ w hw
        have hs := hsep w hw ζ hζ
        have hpos : 0 < ‖ζ - w‖ := by linarith
        rw [norm_div, norm_pow, div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [inv_le_comm₀ (by positivity) (by positivity)]
        calc (4 / δ ^ 2)⁻¹ = (δ / 2) ^ 2 := by field_simp; ring
          _ ≤ ‖ζ - w‖ ^ 2 := by gcongr)
      (hint.norm.mul_const _)
      (by
        filter_upwards [hcl] with ζ hζ w hw
        have hs := hsep w hw ζ hζ
        have hne : ζ - w ≠ 0 := by
          intro h0
          rw [h0, norm_zero] at hs
          linarith
        have h1 := (((hasDerivAt_id w).const_sub ζ).inv hne).const_mul (ω ζ)
        convert h1 using 1
        · rfl
        simp only [id, neg_neg]
        ring)
    show DifferentiableWithinAt ℂ (fun w => -(1 / π : ℂ) * ∫ ζ in D, ω ζ / (ζ - w)) _ z
    exact ((hderiv.2.const_mul (-(1 / π : ℂ))).differentiableAt).differentiableWithinAt
  · obtain ⟨M, hM⟩ := hD.subset_closedBall 0
    refine ⟨2 / π * ∫ ζ in D, ‖ω ζ‖, 2 * |M| + 1, fun z hz => ?_⟩
    have hzpos : 0 < ‖z‖ := by linarith [abs_nonneg M]
    have hclM : closure D ⊆ closedBall 0 M := closure_minimal hM isClosed_closedBall
    have hbound : ∀ᵐ ζ ∂(volume.restrict D), ‖ω ζ / (ζ - z)‖ ≤ ‖ω ζ‖ * (2 / ‖z‖) := by
      filter_upwards [hcl] with ζ hζ
      have hζM : ‖ζ‖ ≤ |M| := by
        have := mem_closedBall.1 (hclM hζ)
        rw [dist_zero_right] at this
        exact this.trans (le_abs_self M)
      have hge : ‖z‖ / 2 ≤ ‖ζ - z‖ := by
        have h : ‖z‖ - ‖ζ‖ ≤ ‖ζ - z‖ := by
          rw [norm_sub_rev]
          exact norm_sub_norm_le z ζ
        linarith
      rw [norm_div, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [inv_le_comm₀ (by linarith) (by positivity), inv_div]
      exact hge
    have h1 := norm_integral_le_of_norm_le (hint.norm.mul_const (2 / ‖z‖)) hbound
    rw [integral_mul_const] at h1
    show ‖-(1 / π : ℂ) * ∫ ζ in D, ω ζ / (ζ - z)‖ ≤ _
    rw [norm_mul, hπn]
    calc 1 / π * ‖∫ ζ in D, ω ζ / (ζ - z)‖ ≤ 1 / π * ((∫ ζ in D, ‖ω ζ‖) * (2 / ‖z‖)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 / π * (∫ ζ in D, ‖ω ζ‖) / ‖z‖ := by ring

/-! ## Green's formula and Pompeiu's formula -/

/-- The complex Green formula (11.9) on a disc: `∮_{∂D} f dz = 2i ∬_D ∂_{z̄} f dx dy`. -/
theorem eq11_9_green_dz {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContDiffOn ℝ 1 f (closedBall c R)) :
    (∮ z in C(c, R), f z) = 2 * I * ∫ z in ball c R, dzbar f z :=
  green_disc_dzbar_closedBall hR hf

/-- The complex Green formula (11.10) on a disc: `∮_{∂D} f dz̄ = -2i ∬_D ∂_z f dx dy`. -/
theorem eq11_10_green_dzbar {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContDiffOn ℝ 1 f (closedBall c R)) :
    (∫ θ in (0 : ℝ)..2 * π, f (circleMap c R θ) * conj (deriv (circleMap c R) θ)) =
      -2 * I * ∫ z in ball c R, dz f z :=
  green_disc_dz_closedBall hR hf


/-! ## The Cauchy kernel is integrable on a disc -/

/-- Off the pole, `‖1/(ζ - z)‖ₑ = ‖ζ - z‖ₑ ^ (-1)`. -/
theorem enorm_one_div_sub_ae (z : ℂ) (s : Set ℂ) :
    (fun ζ : ℂ => ‖1 / (ζ - z)‖ₑ) =ᵐ[volume.restrict s]
      fun ζ : ℂ => ‖ζ - z‖ₑ ^ (-(1 : ℝ)) := by
  have h0 : ∀ᵐ ζ : ℂ, ζ ≠ z := by
    rw [ae_iff]
    have hs : {ζ : ℂ | ¬ ζ ≠ z} = {z} := by ext ζ; simp
    rw [hs]
    exact measure_singleton z
  filter_upwards [ae_restrict_of_ae h0] with ζ hζ
  have hne : ζ - z ≠ 0 := sub_ne_zero.2 hζ
  rw [one_div, enorm_inv hne, ENNReal.rpow_neg, ENNReal.rpow_one]

/-- **The Cauchy kernel is integrable on a disc**, including when the pole lies inside:
`1/|ζ - z|` has an integrable singularity in dimension two. -/
theorem integrableOn_cauchy_kernel_ball {R : ℝ} (hR : 0 < R) (z : ℂ) :
    IntegrableOn (fun ζ : ℂ => 1 / (ζ - z)) (Metric.ball (0 : ℂ) R) := by
  have hmeas : Measurable fun ζ : ℂ => 1 / (ζ - z) :=
    measurable_const.div (measurable_id.sub measurable_const)
  refine ⟨hmeas.aestronglyMeasurable.restrict, ?_⟩
  have hfin : (∫⁻ ζ in Metric.closedBall (0 : ℂ) R, ‖ζ - z‖ₑ ^ (-(1 : ℝ))) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_closedBall_enorm_sub_rpow_neg_le one_pos hR z)
    refine ENNReal.add_ne_top.2 ⟨lintegral_ball_enorm_rpow_neg_ne_top (by norm_num)
      (by norm_num) R, ?_⟩
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
  have hle : (∫⁻ ζ in Metric.ball (0 : ℂ) R, ‖1 / (ζ - z)‖ₑ)
      ≤ ∫⁻ ζ in Metric.closedBall (0 : ℂ) R, ‖ζ - z‖ₑ ^ (-(1 : ℝ)) := by
    rw [lintegral_congr_ae (enorm_one_div_sub_ae z (Metric.ball (0 : ℂ) R))]
    exact lintegral_mono' (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl) le_rfl
  exact lt_of_le_of_lt hle (lt_top_iff_ne_top.2 hfin)

/-! ## Evaluating `∬_{|ζ| < R} dA/(ζ - z)`

(11.19) is proved by polar coordinates followed by a contour evaluation of each `θ`-integral.
With `w = r e^{iθ}`,
`∫₀^{2π} r dθ/(w - z) = -i r ∮_{C(0,r)} dw/(w (w - z))`,
and partial fractions `1/(w(w-z)) = z⁻¹ (w-z)⁻¹ - z⁻¹ w⁻¹` evaluate the contour integral: for
`|z| < r` both poles lie inside and the two residues cancel, giving `0`; for `r < |z|` only the
pole at `0` is inside, giving `-2πi/z`.  So the `r`-integral only sees `0 < r < |z|`, where the
inner integral equals `-2πr/z`, and `∫₀^{|z|} (-2πr/z) dr = -π|z|²/z = -π z̄`. -/

/-- The pointwise identity behind `integral_circleMap_cauchy_kernel`.  No hypothesis on `w - z`
is needed: when `w = z` both sides are `0`. -/
theorem cauchy_kernel_mul_pointwise {w z : ℂ} (hw : w ≠ 0) :
    w * I * (1 / (w * (w - z))) = I * (1 / (w - z)) := by
  rcases eq_or_ne (w - z) 0 with h | h
  · rw [h]; simp
  · field_simp

/-- The `θ`-integral of the Cauchy kernel over the circle `|w| = r`, as a contour integral:
`∫₀^{2π} r dθ/(r e^{iθ} - z) = -i r ∮_{C(0,r)} dw/(w(w-z))`. -/
theorem integral_circleMap_cauchy_kernel {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (∫ θ in (0 : ℝ)..(2 * π), (r : ℂ) * (1 / (circleMap 0 r θ - z)))
      = -(r : ℂ) * I * ∮ w in C((0 : ℂ), r), 1 / (w * (w - z)) := by
  have hne : ∀ θ : ℝ, circleMap (0 : ℂ) r θ ≠ 0 := by
    intro θ h
    have h' := norm_circleMap_zero r θ
    rw [h, norm_zero, abs_of_pos hr] at h'
    exact hr.ne h'
  have hcirc : (∮ w in C((0 : ℂ), r), 1 / (w * (w - z)))
      = ∫ θ in (0 : ℝ)..(2 * π), I * (1 / (circleMap 0 r θ - z)) := by
    simp only [circleIntegral, deriv_circleMap, smul_eq_mul]
    exact intervalIntegral.integral_congr fun θ _ => cauchy_kernel_mul_pointwise (hne θ)
  rw [hcirc, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  set J := ∫ θ in (0 : ℝ)..(2 * π), 1 / (circleMap 0 r θ - z) with hJ
  linear_combination ((r : ℂ) * J) * Complex.I_sq

/-- `∮_{C(0,r)} dw/w² = 0`: this is the `z = 0` case, where the double pole has no residue. -/
theorem circleIntegral_cauchy_kernel_zero {r : ℝ} (hr : 0 < r) :
    (∮ w in C((0 : ℂ), r), 1 / (w * (w - (0 : ℂ)))) = 0 := by
  have hEq : Set.EqOn (fun w : ℂ => 1 / (w * (w - (0 : ℂ))))
      (fun w : ℂ => (w - (0 : ℂ)) ^ (-2 : ℤ)) (sphere (0 : ℂ) r) := by
    intro w _
    simp [zpow_neg, zpow_two] <;> ring
  rw [circleIntegral.integral_congr hr.le hEq]
  exact circleIntegral.integral_sub_zpow_of_ne (by decide) 0 0 r

/-- **Partial fractions on the circle**: `1/(w(w-z)) = z⁻¹(w-z)⁻¹ - z⁻¹ w⁻¹`, and the second
term integrates to `2πi`. -/
theorem circleIntegral_cauchy_kernel_eq {r : ℝ} (hr : 0 < r) {z : ℂ} (hz0 : z ≠ 0)
    (hzr : ‖z‖ ≠ r) :
    (∮ w in C((0 : ℂ), r), 1 / (w * (w - z)))
      = z⁻¹ * (∮ w in C((0 : ℂ), r), (w - z)⁻¹) - z⁻¹ * (2 * π * I) := by
  have hw0 : ∀ w ∈ sphere (0 : ℂ) r, w - (0 : ℂ) ≠ 0 := by
    intro w hw h
    rw [sub_zero] at h
    rw [mem_sphere, dist_zero_right, h, norm_zero] at hw
    exact hr.ne hw
  have hwz : ∀ w ∈ sphere (0 : ℂ) r, w - z ≠ 0 := by
    intro w hw h
    rw [sub_eq_zero] at h
    rw [mem_sphere, dist_zero_right, h] at hw
    exact hzr hw
  have hc1 : ContinuousOn (fun w : ℂ => z⁻¹ * (w - z)⁻¹) (sphere (0 : ℂ) r) :=
    continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).inv₀ hwz)
  have hc2 : ContinuousOn (fun w : ℂ => z⁻¹ * (w - (0 : ℂ))⁻¹) (sphere (0 : ℂ) r) :=
    continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).inv₀ hw0)
  have hEq : Set.EqOn (fun w : ℂ => 1 / (w * (w - z)))
      (fun w : ℂ => z⁻¹ * (w - z)⁻¹ - z⁻¹ * (w - (0 : ℂ))⁻¹) (sphere (0 : ℂ) r) := by
    intro w hw
    have h1 : w ≠ 0 := by simpa using hw0 w hw
    have h2 := hwz w hw
    simp only [sub_zero]
    field_simp
    ring
  rw [circleIntegral.integral_congr hr.le hEq,
    circleIntegral.integral_sub (hc1.circleIntegrable hr.le) (hc2.circleIntegrable hr.le),
    circleIntegral.integral_const_mul, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_center_inv 0 hr.ne']

/-- `|z| < r`: both poles lie inside the circle and the two residues cancel. -/
theorem circleIntegral_cauchy_kernel_of_lt {r : ℝ} {z : ℂ} (hz0 : z ≠ 0) (hzr : ‖z‖ < r) :
    (∮ w in C((0 : ℂ), r), 1 / (w * (w - z))) = 0 := by
  have hr : 0 < r := (norm_nonneg z).trans_lt hzr
  have hmem : z ∈ ball (0 : ℂ) r := by simpa [mem_ball, dist_zero_right] using hzr
  rw [circleIntegral_cauchy_kernel_eq hr hz0 hzr.ne,
    circleIntegral.integral_sub_inv_of_mem_ball hmem]
  ring

/-- `r < |z|`: only the pole at `0` lies inside the circle, so the Cauchy theorem kills the
other term. -/
theorem circleIntegral_cauchy_kernel_of_gt {r : ℝ} (hr : 0 < r) {z : ℂ} (hzr : r < ‖z‖) :
    (∮ w in C((0 : ℂ), r), 1 / (w * (w - z))) = -(z⁻¹ * (2 * π * I)) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hzr
    exact absurd hzr (not_lt.2 hr.le)
  have hout : ∀ w ∈ closedBall (0 : ℂ) r, w - z ≠ 0 := by
    intro w hw h
    rw [sub_eq_zero] at h
    rw [mem_closedBall, dist_zero_right, h] at hw
    exact absurd hzr (not_lt.2 hw)
  have hvan : (∮ w in C((0 : ℂ), r), (w - z)⁻¹) = 0 := by
    refine circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
      ((continuousOn_id.sub continuousOn_const).inv₀ hout) ?_
    intro w hw
    exact (differentiableAt_id.sub_const z).inv (hout w (ball_subset_closedBall hw.1))
  rw [circleIntegral_cauchy_kernel_eq hr hz0 hzr.ne', hvan]
  ring

/-- The `r`-integral in (11.19): `∫₀^R (∫₀^{2π} r dθ/(r e^{iθ} - z)) dr = -π z̄`.

Only `0 < r < |z|` contributes; there the inner integral is `-2πr/z`. -/
theorem integral_polar_cauchy_kernel {R : ℝ} {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < R) :
    (∫ r in (0 : ℝ)..R, ∫ θ in (0 : ℝ)..(2 * π), (r : ℂ) * (1 / (circleMap 0 r θ - z)))
      = -(π : ℂ) * conj z := by
  have ha0 : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hcont : Continuous fun r : ℝ => -(2 * (π : ℂ) * (r : ℂ) / z) :=
    ((continuous_const.mul Complex.continuous_ofReal).div_const z).neg
  have hE1 : Set.EqOn
      (fun r : ℝ => ∫ θ in (0 : ℝ)..(2 * π), (r : ℂ) * (1 / (circleMap 0 r θ - z)))
      (fun r : ℝ => -(2 * (π : ℂ) * (r : ℂ) / z)) (Set.uIoo 0 ‖z‖) := by
    intro r hr
    rw [Set.uIoo_of_le ha0.le] at hr
    simp only
    rw [integral_circleMap_cauchy_kernel hr.1 z, circleIntegral_cauchy_kernel_of_gt hr.1 hr.2]
    field_simp
    rw [Complex.I_sq]
    ring
  have hE2 : Set.EqOn
      (fun r : ℝ => ∫ θ in (0 : ℝ)..(2 * π), (r : ℂ) * (1 / (circleMap 0 r θ - z)))
      (fun _ : ℝ => (0 : ℂ)) (Set.uIoo ‖z‖ R) := by
    intro r hr
    rw [Set.uIoo_of_le hz.le] at hr
    simp only
    rw [integral_circleMap_cauchy_kernel (ha0.trans hr.1) z,
      circleIntegral_cauchy_kernel_of_lt hz0 hr.1]
    ring
  have hii1 : IntervalIntegrable
      (fun r : ℝ => ∫ θ in (0 : ℝ)..(2 * π), (r : ℂ) * (1 / (circleMap 0 r θ - z)))
      volume 0 ‖z‖ :=
    (hcont.intervalIntegrable 0 ‖z‖).congr_uIoo hE1.symm
  have hii2 : IntervalIntegrable
      (fun r : ℝ => ∫ θ in (0 : ℝ)..(2 * π), (r : ℂ) * (1 / (circleMap 0 r θ - z)))
      volume ‖z‖ R :=
    ((continuous_const (y := (0 : ℂ))).intervalIntegrable ‖z‖ R).congr_uIoo hE2.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals hii1 hii2,
    intervalIntegral.integral_congr_uIoo hE1, intervalIntegral.integral_congr_uIoo hE2]
  have hlin : (fun r : ℝ => -(2 * (π : ℂ) * (r : ℂ) / z))
      = fun r : ℝ => (-(2 * (π : ℂ) / z)) * ((r : ℝ) : ℂ) := by
    funext r; ring
  have hsq : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * conj z := by
    rw [Complex.mul_conj]
    norm_cast
    exact (Complex.normSq_eq_norm_sq z).symm
  rw [hlin, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    integral_id, intervalIntegral.integral_zero, add_zero]
  push_cast
  rw [hsq]
  field_simp
  ring

/-- The Cauchy kernel is integrable on any set contained in a disc centred at the origin;
`integrableOn_cauchy_kernel_ball` is the case `s = ball 0 R`. -/
theorem integrableOn_cauchy_kernel_of_subset {R : ℝ} (hR : 0 < R) {s : Set ℂ}
    (hs : s ⊆ closedBall (0 : ℂ) R) (z : ℂ) :
    IntegrableOn (fun ζ : ℂ => 1 / (ζ - z)) s := by
  have hmeas : Measurable fun ζ : ℂ => 1 / (ζ - z) :=
    measurable_const.div (measurable_id.sub measurable_const)
  refine ⟨hmeas.aestronglyMeasurable.restrict, ?_⟩
  have hfin : (∫⁻ ζ in closedBall (0 : ℂ) R, ‖ζ - z‖ₑ ^ (-(1 : ℝ))) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_closedBall_enorm_sub_rpow_neg_le one_pos hR z)
    refine ENNReal.add_ne_top.2 ⟨lintegral_ball_enorm_rpow_neg_ne_top (by norm_num)
      (by norm_num) R, ?_⟩
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
  have hle : (∫⁻ ζ in s, ‖1 / (ζ - z)‖ₑ)
      ≤ ∫⁻ ζ in closedBall (0 : ℂ) R, ‖ζ - z‖ₑ ^ (-(1 : ℝ)) := by
    rw [lintegral_congr_ae (enorm_one_div_sub_ae z s)]
    exact lintegral_mono' (Measure.restrict_mono hs le_rfl) le_rfl
  exact lt_of_le_of_lt hle (lt_top_iff_ne_top.2 hfin)

/-- `(∂_z̄ f)/(· - z)` is integrable on the disc: the kernel has an integrable singularity in
dimension two and `∂_z̄ f` is bounded there. -/
theorem integrableOn_dzbar_div_sub {f : ℂ → ℂ} {c z : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContDiffOn ℝ 1 f (closedBall c R)) :
    IntegrableOn (fun ζ : ℂ => dzbar f ζ / (ζ - z)) (ball c R) := by
  obtain ⟨M, hM⟩ := exists_bound_dzbar hR hf
  have hker : IntegrableOn (fun ζ : ℂ => 1 / (ζ - z)) (ball c R) := by
    refine integrableOn_cauchy_kernel_of_subset (R := ‖c‖ + R) (by positivity) ?_ z
    intro ζ hζ
    rw [mem_ball, dist_eq_norm] at hζ
    simp only [mem_closedBall, dist_zero_right]
    calc ‖ζ‖ = ‖ζ - c + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖ζ - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ ‖c‖ + R := by linarith
  have hcont : ContinuousOn (dzbar f) (ball c R) :=
    (continuousOn_dz_dzbar (hf.mono ball_subset_closedBall) isOpen_ball).2
  have hbound : ∀ᵐ ζ ∂(volume.restrict (ball c R)), ‖dzbar f ζ‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with ζ hζ using hM ζ hζ
  have hmul := hker.bdd_mul (hcont.aestronglyMeasurable measurableSet_ball) hbound
  have heqf : (fun ζ : ℂ => dzbar f ζ * (1 / (ζ - z)))
      = fun ζ : ℂ => dzbar f ζ / (ζ - z) := by
    funext ζ; rw [mul_one_div]
  rw [IntegrableOn, ← heqf]
  exact hmul

/-- **Pompeiu's formula** (11.11) on a disc, for `f ∈ C¹(D̄)`:
`f(z₀) = (1/2πi) ∮_{∂D} f(z)/(z - z₀) dz - (1/π) ∬_D ∂_{z̄} f(z)/(z - z₀) dx dy`. -/
theorem eq11_11_pompeiu {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContDiffOn ℝ 1 f (closedBall c R)) {z₀ : ℂ} (hz₀ : z₀ ∈ ball c R) :
    f z₀ = (1 / (2 * π * I)) * (∮ z in C(c, R), f z / (z - z₀)) -
      (1 / π : ℂ) * ∫ z in ball c R, dzbar f z / (z - z₀) := by
  -- a radius `ε₀` with `closedBall z₀ t ⊆ ball c R` for every `t ≤ ε₀`
  rw [mem_ball, dist_eq_norm] at hz₀
  set ε₀ : ℝ := (R - ‖z₀ - c‖) / 2 with hε₀def
  have hε₀ : 0 < ε₀ := by rw [hε₀def]; linarith
  have hball : ∀ t : ℝ, t ≤ ε₀ → closedBall z₀ t ⊆ ball c R := by
    intro t htle ζ hζ
    rw [mem_closedBall, dist_eq_norm] at hζ
    rw [mem_ball, dist_eq_norm]
    calc ‖ζ - c‖ = ‖(ζ - z₀) + (z₀ - c)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖ζ - z₀‖ + ‖z₀ - c‖ := norm_add_le _ _
      _ ≤ ε₀ + ‖z₀ - c‖ := by linarith
      _ < R := by rw [hε₀def]; linarith
  -- the shrinking radii
  set u : ℕ → ℝ := fun n => ε₀ * (1 / ((n : ℝ) + 1)) with hu
  have hu0 : ∀ n, 0 < u n := fun n => by rw [hu]; positivity
  have hule : ∀ n, u n ≤ ε₀ := by
    intro n
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      simp
    calc u n ≤ ε₀ * 1 := mul_le_mul_of_nonneg_left h1 hε₀.le
      _ = ε₀ := mul_one ε₀
  have hutend : Tendsto u atTop (𝓝 0) := by
    rw [hu]
    simpa only [one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε₀
  -- the two-Green identity at each radius, with the small circle integral as a circle average
  have h2πI : (2 * (π : ℂ) * I) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
    simp
  have hfun : (fun ζ : ℂ => (ζ - z₀)⁻¹ • f ζ) = fun ζ : ℂ => f ζ / (ζ - z₀) := by
    funext ζ
    rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hkey : ∀ n, (∮ ζ in C(c, R), f ζ / (ζ - z₀))
      - 2 * π * I * Real.circleAverage f z₀ (u n)
      = 2 * I * ∫ ζ in ball c R \ ball z₀ (u n), dzbar f ζ / (ζ - z₀) := by
    intro n
    have h2 : (∮ ζ in C(z₀, u n), f ζ / (ζ - z₀))
        = 2 * π * I * Real.circleAverage f z₀ (u n) := by
      rw [Real.circleAverage_eq_circleIntegral (ne_of_gt (hu0 n)), hfun, smul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ h2πI, one_mul]
    rw [← h2]
    exact circleIntegral_sub_circleIntegral_eq hR (hu0 n) hf (hball (u n) (hule n))
  -- Limit 1: the circle average at radius `u n` tends to `f z₀`
  have hca : Tendsto (fun n => Real.circleAverage f z₀ (u n)) atTop (𝓝 (f z₀)) := by
    have hsubset : closedBall z₀ ε₀ ⊆ closedBall c R :=
      (hball ε₀ le_rfl).trans ball_subset_closedBall
    have hset : {w : ℂ | ‖w - z₀‖ ∈ Icc (0 : ℝ) ε₀} = closedBall z₀ ε₀ := by
      ext w
      simp [mem_closedBall, dist_eq_norm, norm_nonneg]
    have hcont : ContinuousOn (Real.circleAverage f z₀) (Icc 0 ε₀) :=
      Real.ContinuousOn.circleAverage (by rw [hset]; exact hf.continuousOn.mono hsubset)
        fun r hr => hr.1
    have hw : Tendsto u atTop (𝓝[Icc (0 : ℝ) ε₀] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hutend
        (Eventually.of_forall fun n => ⟨(hu0 n).le, hule n⟩)
    have h0 := (hcont 0 ⟨le_rfl, hε₀.le⟩).tendsto.comp hw
    rwa [Real.circleAverage_zero] at h0
  -- Limit 2: the punctured area integrals tend to the full one
  have hint : IntegrableOn (fun ζ : ℂ => dzbar f ζ / (ζ - z₀)) (ball c R) :=
    integrableOn_dzbar_div_sub hR hf
  have hmono : Monotone fun n => ball c R \ ball z₀ (u n) := by
    intro m n hmn
    refine Set.diff_subset_diff le_rfl (Metric.ball_subset_ball ?_)
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      have hmn' : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hmn
      linarith
    exact mul_le_mul_of_nonneg_left h1 hε₀.le
  have hunion : (⋃ n, ball c R \ ball z₀ (u n)) = ball c R \ {z₀} := by
    ext ζ
    simp only [Set.mem_iUnion, Set.mem_diff, Set.mem_singleton_iff, mem_ball, dist_eq_norm]
    constructor
    · rintro ⟨n, hζ, hne⟩
      refine ⟨hζ, fun h => ?_⟩
      rw [h, sub_self, norm_zero] at hne
      exact hne (hu0 n)
    · rintro ⟨hζ, hne⟩
      have hpos : 0 < ‖ζ - z₀‖ := by
        rw [norm_pos_iff, sub_ne_zero]
        exact hne
      obtain ⟨n, hn⟩ := exists_nat_gt (ε₀ / ‖ζ - z₀‖)
      rw [div_lt_iff₀ hpos] at hn
      refine ⟨n, hζ, not_lt.2 ?_⟩
      rw [hu]
      simp only [mul_one_div]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n, hpos.le]
  have hpunct : (∫ ζ in ball c R \ {z₀}, dzbar f ζ / (ζ - z₀))
      = ∫ ζ in ball c R, dzbar f ζ / (ζ - z₀) :=
    MeasureTheory.setIntegral_congr_set
      (MeasureTheory.diff_null_ae_eq_self (measure_singleton z₀))
  have hlim2 : Tendsto (fun n => ∫ ζ in ball c R \ ball z₀ (u n), dzbar f ζ / (ζ - z₀))
      atTop (𝓝 (∫ ζ in ball c R, dzbar f ζ / (ζ - z₀))) := by
    have h := MeasureTheory.tendsto_setIntegral_of_monotone
      (f := fun ζ : ℂ => dzbar f ζ / (ζ - z₀))
      (fun n => measurableSet_ball.diff measurableSet_ball) hmono
      (by rw [hunion]; exact hint.mono_set Set.diff_subset)
    rwa [hunion, hpunct] at h
  -- pass to the limit
  have heq : (∮ ζ in C(c, R), f ζ / (ζ - z₀)) - 2 * π * I * f z₀
      = 2 * I * ∫ ζ in ball c R, dzbar f ζ / (ζ - z₀) := by
    refine tendsto_nhds_unique ?_ (hlim2.const_mul (2 * I))
    simpa only [hkey] using
      (tendsto_const_nhds (x := (∮ ζ in C(c, R), f ζ / (ζ - z₀))) (f := atTop (α := ℕ))).sub
        (hca.const_mul (2 * (π : ℂ) * I))
  have hfz : 2 * (π : ℂ) * I * f z₀ = (∮ ζ in C(c, R), f ζ / (ζ - z₀))
      - 2 * I * ∫ ζ in ball c R, dzbar f ζ / (ζ - z₀) := by
    linear_combination -heq
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := by simp
  refine mul_left_cancel₀ h2πI ?_
  rw [hfz]
  field_simp

/-- Hölder's inequality against the Cauchy kernel on a disc. -/
theorem lintegral_ball_enorm_mul_inv_le {p q : ℝ} (hpq : p.HolderConjugate q) {F : ℂ → ℂ}
    {c z₀ : ℂ} {R : ℝ} (hF : AEMeasurable F (volume.restrict (ball c R))) :
    ∫⁻ z in ball c R, ‖F z‖ₑ * ‖z - z₀‖ₑ⁻¹ ≤
      eLpNorm F (ENNReal.ofReal p) (volume.restrict (ball c R)) *
        (∫⁻ z in ball c R, ‖z - z₀‖ₑ ^ (-q)) ^ (1 / q) := by
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (ball c R)) hpq hF.enorm
    ((measurable_id.sub_const z₀).enorm.inv.aemeasurable)
  calc ∫⁻ z in ball c R, ‖F z‖ₑ * ‖z - z₀‖ₑ⁻¹
      ≤ (∫⁻ z in ball c R, ‖F z‖ₑ ^ p) ^ (1 / p) *
          (∫⁻ z in ball c R, (‖z - z₀‖ₑ⁻¹) ^ q) ^ (1 / q) := h
    _ = _ := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top
          hF.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
        congr 2
        refine lintegral_congr fun z => ?_
        rw [ENNReal.inv_rpow, ENNReal.rpow_neg]

theorem lintegral_ball_enorm_sub_rpow_neg_lt_top {q : ℝ} (hq2 : q < 2) {c z₀ : ℂ}
    {R : ℝ} (hR : 0 < R) (hz₀ : z₀ ∈ ball c R) :
    ∫⁻ z in ball c R, ‖z - z₀‖ₑ ^ (-q) < ⊤ := by
  have hsub : ball c R ⊆ ball z₀ (2 * R) := by
    intro z hz
    rw [mem_ball] at hz hz₀ ⊢
    have := dist_triangle z c z₀
    rw [dist_comm c z₀] at this
    linarith
  refine lt_of_le_of_lt (lintegral_mono_set hsub) ?_
  rw [lintegral_ball_sub_enorm_rpow_neg hq2 (by positivity) z₀]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- Pompeiu's formula for functions with `L_p` generalized derivatives, `p > 2`, on a domain
`D₁ ⊇ D̄` (§11.2).

Pompeiu's formula for the `C¹` approximations `fₙ` passes to the limit: `fₙ → f` uniformly on
the circle and at `z₀`, and `∂_z̄ fₙ → (g + i h)/2` in `L_p` on the disc, which against the kernel
`1/(z - z₀) ∈ L_q`, `q = p/(p - 1) < 2`, gives convergence of the area term by Hölder's inequality
(`lintegral_ball_enorm_mul_inv_le`). -/
theorem eq11_11_pompeiu_gen {f g h : ℂ → ℂ} {D₁ : Set ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hD₁ : IsOpen D₁) (hsub : closedBall c R ⊆ D₁) {p : ℝ} (hp : 2 < p)
    (hf : HasGenPartials f g h D₁ (ENNReal.ofReal p)) {z₀ : ℂ} (hz₀ : z₀ ∈ ball c R) :
    f z₀ = (1 / (2 * π * I)) * (∮ z in C(c, R), f z / (z - z₀)) -
      (1 / π : ℂ) * ∫ z in ball c R, genDzbar g h z / (z - z₀) := by
  obtain ⟨hloc, fn, hfn, hconv, hLp⟩ := hf
  have hp1 : 1 < p := by linarith
  set q := p / (p - 1) with hqdef
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
  have hq0 : 0 < q := hpq.symm.pos
  have hq2 : q < 2 := by
    rw [hqdef, div_lt_iff₀ (by linarith)]
    linarith
  have hK := isCompact_closedBall c R
  have hz₀D : z₀ ∈ D₁ := hsub (ball_subset_closedBall hz₀)
  obtain ⟨hgK, hhK⟩ := hloc _ hsub hK
  obtain ⟨hL1, hLI⟩ := hLp _ hsub hK
  set Kq := (∫⁻ z in ball c R, ‖z - z₀‖ₑ ^ (-q)) ^ (1 / q) with hKq
  have hKq_top : Kq ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (by positivity)
      (lintegral_ball_enorm_sub_rpow_neg_lt_top hq2 hR hz₀).ne).ne
  have hball_le : volume.restrict (ball c R) ≤ volume.restrict (closedBall c R) :=
    Measure.restrict_mono ball_subset_closedBall le_rfl
  -- Pompeiu for the approximations
  have hpn : ∀ n, fn n z₀ = (1 / (2 * π * I)) * (∮ z in C(c, R), fn n z / (z - z₀)) -
      (1 / π : ℂ) * ∫ z in ball c R, dzbar (fn n) z / (z - z₀) :=
    fun n => eq11_11_pompeiu hR ((hfn n).mono hsub) hz₀
  -- the values
  have hlim1 : Tendsto (fun n => fn n z₀) atTop (𝓝 (f z₀)) := hconv.tendsto_at hz₀D
  -- the circle integrals
  have hd : 0 < R - ‖z₀ - c‖ := by
    rw [mem_ball, dist_eq_norm] at hz₀
    linarith
  have hsph : ∀ z ∈ sphere c R, R - ‖z₀ - c‖ ≤ ‖z - z₀‖ := by
    intro z hz
    rw [mem_sphere, dist_eq_norm] at hz
    have h := norm_sub_norm_le (z - c) (z₀ - c)
    rw [sub_sub_sub_cancel_right] at h
    linarith
  have hunif : TendstoUniformlyOn fn f atTop (sphere c R) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hD₁).1 hconv _
      (sphere_subset_closedBall.trans hsub) (isCompact_sphere c R)
  have hfcont : ContinuousOn f D₁ :=
    hconv.continuousOn (Frequently.of_forall fun n => (hfn n).continuousOn)
  have hkcont : ContinuousOn (fun z : ℂ => (z - z₀)⁻¹) (sphere c R) := by
    refine (continuousOn_id.sub continuousOn_const).inv₀ fun z hz => ?_
    have := hsph z hz
    intro h0
    have h0' : z - z₀ = 0 := h0
    rw [h0', norm_zero] at this
    linarith
  have hci : ∀ u : ℂ → ℂ, ContinuousOn u (sphere c R) →
      CircleIntegrable (fun z => u z / (z - z₀)) c R := by
    intro u hu
    refine ContinuousOn.circleIntegrable hR.le ?_
    simp only [div_eq_mul_inv]
    exact hu.mul hkcont
  have hlim2 : Tendsto (fun n => ∮ z in C(c, R), fn n z / (z - z₀)) atTop
      (𝓝 (∮ z in C(c, R), f z / (z - z₀))) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε' : 0 < ε * (R - ‖z₀ - c‖) / (4 * π * R) := by positivity
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif _ hε'] with n hn
    rw [dist_eq_norm, ← circleIntegral.integral_sub
      (hci _ ((hfn n).continuousOn.mono (sphere_subset_closedBall.trans hsub)))
      (hci _ (hfcont.mono (sphere_subset_closedBall.trans hsub)))]
    refine lt_of_le_of_lt (circleIntegral.norm_integral_le_of_norm_le_const hR.le
      (C := ε * (R - ‖z₀ - c‖) / (4 * π * R) / (R - ‖z₀ - c‖)) fun z hz => ?_) ?_
    · rw [← sub_div, norm_div]
      refine div_le_div₀ (by positivity) ?_ hd (hsph z hz)
      rw [← dist_eq_norm, dist_comm]
      exact (hn z hz).le
    · have hRd : (R - ‖z₀ - c‖) ≠ 0 := hd.ne'
      have hπR : 4 * π * R ≠ 0 := by positivity
      calc 2 * π * R * (ε * (R - ‖z₀ - c‖) / (4 * π * R) / (R - ‖z₀ - c‖)) = ε / 2 := by
            field_simp
            ring
        _ < ε := half_lt_self hε
  -- the area integrals
  have hgenK : MemLp (genDzbar g h) (ENNReal.ofReal p) (volume.restrict (ball c R)) := by
    have h1 : MemLp (fun z => (1 / 2 : ℂ) * (g z + I * h z)) (ENNReal.ofReal p)
        (volume.restrict (closedBall c R)) := (hgK.add (hhK.const_mul I)).const_mul _
    refine (h1.mono_measure hball_le).congr_norm ?_ ?_
    · exact (h1.aestronglyMeasurable.mono_measure hball_le).congr (Eventually.of_forall fun z => by
        simp only [genDzbar]; ring)
    · exact Eventually.of_forall fun z => by simp only [genDzbar]; congr 1; ring
  have hint_gen : IntegrableOn (fun z => genDzbar g h z / (z - z₀)) (ball c R) := by
    refine ⟨(hgenK.aestronglyMeasurable.aemeasurable.div (measurable_id.sub_const z₀).aemeasurable).aestronglyMeasurable,
      ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ z in ball c R, ‖genDzbar g h z / (z - z₀)‖ₑ
        = ∫⁻ z in ball c R, ‖genDzbar g h z‖ₑ * ‖z - z₀‖ₑ⁻¹ := by
          refine lintegral_congr_ae ?_
          filter_upwards [ae_restrict_of_ae (ae_ne z₀)] with z hz
          rw [div_eq_mul_inv, enorm_mul, enorm_inv (sub_ne_zero.2 hz)]
      _ ≤ _ := lintegral_ball_enorm_mul_inv_le hpq hgenK.aestronglyMeasurable.aemeasurable
      _ < ⊤ := ENNReal.mul_lt_top hgenK.eLpNorm_lt_top hKq_top.lt_top
  have hlim3 : Tendsto (fun n => ∫ z in ball c R, dzbar (fn n) z / (z - z₀)) atTop
      (𝓝 (∫ z in ball c R, genDzbar g h z / (z - z₀))) := by
    rw [tendsto_iff_edist_tendsto_0]
    have hdiff : ∀ n, AEStronglyMeasurable (fun z => fderiv ℝ (fn n) z 1 - g z)
        (volume.restrict (ball c R)) ∧ AEStronglyMeasurable (fun z => fderiv ℝ (fn n) z I - h z)
        (volume.restrict (ball c R)) := fun n =>
      ⟨(measurable_fderiv_apply_const ℝ (fn n) 1).aestronglyMeasurable.sub
          (hgK.aestronglyMeasurable.mono_measure hball_le),
        (measurable_fderiv_apply_const ℝ (fn n) I).aestronglyMeasurable.sub
          (hhK.aestronglyMeasurable.mono_measure hball_le)⟩
    have hbound : ∀ n, edist (∫ z in ball c R, dzbar (fn n) z / (z - z₀))
        (∫ z in ball c R, genDzbar g h z / (z - z₀)) ≤
        ‖(1 / 2 : ℂ)‖ₑ * (eLpNorm (fun z => fderiv ℝ (fn n) z 1 - g z) (ENNReal.ofReal p)
          (volume.restrict (closedBall c R)) + ‖I‖ₑ * eLpNorm (fun z => fderiv ℝ (fn n) z I - h z)
            (ENNReal.ofReal p) (volume.restrict (closedBall c R))) * Kq := by
      intro n
      have hA := hdiff n
      rw [edist_eq_enorm_sub, ← integral_sub
        (integrableOn_dzbar_div_sub hR ((hfn n).mono hsub)) hint_gen]
      have hpt : ∀ z, dzbar (fn n) z / (z - z₀) - genDzbar g h z / (z - z₀) =
          ((1 / 2 : ℂ) * ((fderiv ℝ (fn n) z 1 - g z) + I * (fderiv ℝ (fn n) z I - h z))) *
            (z - z₀)⁻¹ := by
        intro z
        simp only [dzbar, genDzbar]
        ring
      simp only [hpt]
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      have hm : AEMeasurable (fun z => (1 / 2 : ℂ) * ((fderiv ℝ (fn n) z 1 - g z) +
          I * (fderiv ℝ (fn n) z I - h z))) (volume.restrict (ball c R)) :=
        ((hA.1.add (hA.2.const_mul I)).const_mul _).aemeasurable
      refine (lintegral_mono_ae ?_).trans ((lintegral_ball_enorm_mul_inv_le (z₀ := z₀) hpq hm).trans ?_)
      · filter_upwards [ae_restrict_of_ae (ae_ne z₀)] with z hz
        rw [enorm_mul, enorm_inv (sub_ne_zero.2 hz)]
      gcongr
      calc eLpNorm (fun z => (1 / 2 : ℂ) * ((fderiv ℝ (fn n) z 1 - g z) +
            I * (fderiv ℝ (fn n) z I - h z))) (ENNReal.ofReal p) (volume.restrict (ball c R))
          = ‖(1 / 2 : ℂ)‖ₑ * eLpNorm (fun z => (fderiv ℝ (fn n) z 1 - g z) +
            I * (fderiv ℝ (fn n) z I - h z)) (ENNReal.ofReal p) (volume.restrict (ball c R)) :=
            eLpNorm_const_smul (1 / 2 : ℂ) (fun z => (fderiv ℝ (fn n) z 1 - g z) +
              I * (fderiv ℝ (fn n) z I - h z)) _ _
        _ ≤ ‖(1 / 2 : ℂ)‖ₑ * (eLpNorm (fun z => fderiv ℝ (fn n) z 1 - g z) (ENNReal.ofReal p)
              (volume.restrict (ball c R)) + eLpNorm (fun z => I * (fderiv ℝ (fn n) z I - h z))
                (ENNReal.ofReal p) (volume.restrict (ball c R))) :=
            by
              have hp1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
                rw [← ENNReal.ofReal_one]
                exact ENNReal.ofReal_le_ofReal hp1.le
              gcongr
              exact eLpNorm_add_le hp1'
        _ ≤ _ := by
            rw [show (fun z => I * (fderiv ℝ (fn n) z I - h z)) =
              I • (fun z => fderiv ℝ (fn n) z I - h z) from rfl, eLpNorm_const_smul]
            gcongr
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => zero_le)
      hbound
    have h0 := ENNReal.Tendsto.mul_const (ENNReal.Tendsto.const_mul
      (hL1.add (ENNReal.Tendsto.const_mul hLI (Or.inr (by simp : ‖I‖ₑ ≠ ⊤))))
      (Or.inr (by simp : ‖(1 / 2 : ℂ)‖ₑ ≠ ⊤))) (Or.inr hKq_top)
    rw [show (0 : ℝ≥0∞) = ‖(1 / 2 : ℂ)‖ₑ * (0 + ‖I‖ₑ * 0) * Kq by simp]
    exact h0
  -- pass to the limit
  have hlimR := ((hlim2.const_mul (1 / (2 * π * I))).sub (hlim3.const_mul (1 / π : ℂ)))
  have hlimL : Tendsto (fun n => fn n z₀) atTop
      (𝓝 ((1 / (2 * π * I)) * (∮ z in C(c, R), f z / (z - z₀)) -
        (1 / π : ℂ) * ∫ z in ball c R, genDzbar g h z / (z - z₀))) := by
    simpa only [← hpn] using hlimR
  exact tendsto_nhds_unique hlim1 hlimL

/-! ## The Hilbert transform -/

/-- The Hilbert transform (11.15), as a Cauchy principal value:
`H(ω)(z) = -(1/π) lim_{r → 0} ∬_{|ζ - z| > r} ω(ζ)/(ζ - z)² dξ dη`. -/
def hilbertHSmooth (ω : ℂ → ℂ) (z : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun r => -(1 / π : ℂ) * ∫ ζ in {ζ : ℂ | r < ‖ζ - z‖}, ω ζ / (ζ - z) ^ 2

theorem measurableSet_annulus {r R : ℝ} : MeasurableSet (annulus r R) :=
  (isOpen_annulus r R).measurableSet

theorem isOpen_annulusAt {a : ℂ} {r R : ℝ} : IsOpen (annulusAt a r R) := by
  have e : annulusAt a r R = (fun z : ℂ => ‖z - a‖) ⁻¹' Ioo r R := by
    ext z
    simp [annulusAt, mem_Ioo]
  rw [e]
  exact isOpen_Ioo.preimage (continuous_norm.comp (continuous_id.sub continuous_const))

theorem measurableSet_annulusAt {a : ℂ} {r R : ℝ} : MeasurableSet (annulusAt a r R) :=
  isOpen_annulusAt.measurableSet

/-- §11.3: `-(1/π) ∬_{r < |ζ - z| < R} dξ dη / (ζ - z)² = 0`. -/
theorem integral_annulus_inv_sq (z : ℂ) {r R : ℝ} (_hr : 0 < r) (_hrR : r < R) :
    ∫ ζ in annulusAt z r R, 1 / (ζ - z) ^ 2 = 0 := by
  -- translate to the annulus centred at `0`
  have hembt : MeasurableEmbedding (fun w : ℂ => w + z) :=
    (Homeomorph.addRight z).isClosedEmbedding.measurableEmbedding
  have hpret : (fun w : ℂ => w + z) ⁻¹' annulusAt z r R = annulus r R := by
    ext w
    simp [annulusAt, annulus]
  have htr := (measurePreserving_add_right volume z).setIntegral_preimage_emb hembt
    (fun ζ => 1 / (ζ - z) ^ 2) (annulusAt z r R)
  rw [hpret] at htr
  simp only [add_sub_cancel_right] at htr
  rw [← htr]
  -- the annulus is invariant under the rotation `w ↦ i w`, which changes the sign of `1/w²`
  have hLdet : LinearMap.det ((ContinuousLinearMap.mul ℝ ℂ I).toLinearMap) = 1 := by
    rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
      Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.mul_apply', mul_one, I_mul_I]
    norm_num
  have hmp : MeasurePreserving (fun w : ℂ => I * w) volume volume := by
    refine ⟨measurable_const_mul I, ?_⟩
    have hmap : Measure.map ((ContinuousLinearMap.mul ℝ ℂ I).toLinearMap) volume =
        ENNReal.ofReal |(LinearMap.det ((ContinuousLinearMap.mul ℝ ℂ I).toLinearMap))⁻¹| • volume :=
      Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hLdet]; norm_num)
    rw [hLdet] at hmap
    have hfun : (fun w : ℂ => I * w) = ⇑((ContinuousLinearMap.mul ℝ ℂ I).toLinearMap) := by
      funext w
      simp [ContinuousLinearMap.mul_apply']
    rw [hfun]
    simpa using hmap
  have hembr : MeasurableEmbedding (fun w : ℂ => I * w) :=
    (Homeomorph.mulLeft₀ I I_ne_zero).isClosedEmbedding.measurableEmbedding
  have hprer : (fun w : ℂ => I * w) ⁻¹' annulus r R = annulus r R := by
    ext w
    simp [annulus]
  have hrot := hmp.setIntegral_preimage_emb hembr (fun w => 1 / w ^ 2) (annulus r R)
  rw [hprer] at hrot
  have hneg : ∀ w : ℂ, 1 / (I * w) ^ 2 = -(1 / w ^ 2) := by
    intro w
    rw [mul_pow, I_sq]
    ring
  simp only [hneg] at hrot
  rw [integral_neg] at hrot
  have hJ : (2 : ℂ) * ∫ w in annulus r R, 1 / w ^ 2 = 0 := by linear_combination -hrot
  rcases mul_eq_zero.1 hJ with h | h
  · norm_num at h
  · exact h

/-- `ball z R \ ball z M` and the open annulus `M < |ζ - z| < R` differ by a null set. -/
theorem ball_diff_ball_ae_eq_annulusAt (z : ℂ) (M R : ℝ) :
    (ball z R \ ball z M : Set ℂ) =ᵐ[volume] annulusAt z M R := by
  refine ae_eq_set.2 ⟨measure_mono_null (fun ζ hζ => ?_) (Measure.addHaar_sphere volume z M),
    measure_mono_null (fun ζ hζ => ?_) measure_empty⟩
  · obtain ⟨⟨h1, h2⟩, h3⟩ := hζ
    rw [mem_ball, dist_eq_norm] at h1
    rw [mem_ball, dist_eq_norm, not_lt] at h2
    rw [mem_sphere, dist_eq_norm]
    by_contra hne
    exact h3 ⟨lt_of_le_of_ne h2 (Ne.symm hne), h1⟩
  · obtain ⟨⟨h1, h2⟩, h3⟩ := hζ
    exact h3 ⟨by rw [mem_ball, dist_eq_norm]; exact h2,
      by rw [mem_ball, dist_eq_norm, not_lt]; exact h1.le⟩

/-- A pointwise bound `|G(ζ)| ≤ L/|ζ - z|` gives `∫⁻_s |G| ≤ L ∫⁻_s |ζ - z|⁻¹`. -/
theorem lintegral_enorm_le_of_norm_le_div {G : ℂ → ℂ} {z : ℂ} {L : ℝ} (hL : 0 ≤ L) (s : Set ℂ)
    (hb : ∀ ζ, ζ ≠ z → ‖G ζ‖ ≤ L / ‖ζ - z‖) :
    ∫⁻ ζ in s, ‖G ζ‖ₑ ≤ ENNReal.ofReal L * ∫⁻ ζ in s, ‖ζ - z‖ₑ ^ (-1 : ℝ) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_of_ae (ae_ne z)] with ζ hζ
  have hpos : 0 < ‖ζ - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hζ)
  rw [← ofReal_norm, ← ofReal_norm, ENNReal.ofReal_rpow_of_pos hpos,
    ← ENNReal.ofReal_mul hL]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.rpow_neg_one, ← div_eq_mul_inv]
  exact hb ζ hζ

/-- A function with `|G(ζ)| ≤ L/|ζ - z|` is integrable on every disc centred at `z`. -/
theorem integrableOn_ball_of_norm_le_div {G : ℂ → ℂ} {z : ℂ} {L R : ℝ} (hL : 0 ≤ L) (hR : 0 < R)
    (hG : AEStronglyMeasurable G volume) (hb : ∀ ζ, ζ ≠ z → ‖G ζ‖ ≤ L / ‖ζ - z‖) :
    IntegrableOn G (ball z R) := by
  refine ⟨hG.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  refine lt_of_le_of_lt (lintegral_enorm_le_of_norm_le_div hL _ hb) ?_
  rw [lintegral_ball_sub_enorm_rpow_neg (by norm_num) hR z]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

/-- §11.3: for `ω ∈ C₀^∞`, the principal value exists everywhere and equals the improper
integral `-(1/π) ∬ (ω(ζ) - ω(z))/(ζ - z)² dξ dη`.

On an annulus `r < |ζ - z| < R` the integral of `ω(z)/(ζ - z)²` vanishes
(`integral_annulus_inv_sq`), so the truncated integrals only see `(ω(ζ) - ω(z))/(ζ - z)²`, which
is `O(1/|ζ - z|)` because `ω` is Lipschitz and hence integrable near `z`; beyond the support the
same cancellation makes the disc integrals constant in `R`.

*Correction.*  `C₀^∞` is written `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω`.  A bare
`ContDiff ℝ ⊤ ω` would mean real analyticity (`ω`-smoothness) in current Mathlib, and a
real-analytic function with compact support vanishes identically, which would make the statement
degenerate. -/
theorem eq11_15 {ω : ℂ → ℂ} (hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω) (hc : HasCompactSupport ω) (z : ℂ) :
    Tendsto (fun r => -(1 / π : ℂ) * ∫ ζ in {ζ : ℂ | r < ‖ζ - z‖}, ω ζ / (ζ - z) ^ 2)
        (𝓝[>] 0) (𝓝 (hilbertHSmooth ω z)) ∧
      Tendsto (fun R => -(1 / π : ℂ) * ∫ ζ in ball z R, (ω ζ - ω z) / (ζ - z) ^ 2)
        atTop (𝓝 (hilbertHSmooth ω z)) := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hω (by simp)
  obtain ⟨M₀, hM₀⟩ := hc.isCompact.isBounded.subset_closedBall z
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = max M₀ 0 + 1 := ⟨_, rfl⟩
  have hM : 0 < M := by rw [hMdef]; positivity
  have hvanish : ∀ ζ, M ≤ ‖ζ - z‖ → ω ζ = 0 := by
    intro ζ hζ
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have h1 := mem_closedBall.1 (hM₀ hmem)
    rw [dist_eq_norm] at h1
    have h2 : M₀ < M := by rw [hMdef]; linarith [le_max_left M₀ 0]
    linarith
  have hLnn : (0 : ℝ) ≤ L := L.2
  have hGm : AEStronglyMeasurable (fun ζ => (ω ζ - ω z) / (ζ - z) ^ 2) volume :=
    ((hω.continuous.measurable.sub_const _).div
      ((measurable_id.sub_const z).pow_const 2)).aestronglyMeasurable
  have hGb : ∀ ζ, ζ ≠ z → ‖(ω ζ - ω z) / (ζ - z) ^ 2‖ ≤ (L : ℝ) / ‖ζ - z‖ := by
    intro ζ hζ
    have hpos : 0 < ‖ζ - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hζ)
    have hlip := hL.dist_le_mul ζ z
    rw [dist_eq_norm, dist_eq_norm] at hlip
    rw [norm_div, norm_pow, div_le_div_iff₀ (by positivity) hpos]
    calc ‖ω ζ - ω z‖ * ‖ζ - z‖ ≤ (L * ‖ζ - z‖) * ‖ζ - z‖ := by gcongr
      _ = L * ‖ζ - z‖ ^ 2 := by ring
  have hGint : ∀ R, 0 < R → IntegrableOn (fun ζ => (ω ζ - ω z) / (ζ - z) ^ 2) (ball z R) :=
    fun R hR => integrableOn_ball_of_norm_le_div hLnn hR hGm hGb
  -- the ball integrals are constant beyond the support
  have hconst : ∀ R, M ≤ R → ∫ ζ in ball z R, (ω ζ - ω z) / (ζ - z) ^ 2 =
      ∫ ζ in ball z M, (ω ζ - ω z) / (ζ - z) ^ 2 := by
    intro R hR
    have hdiff := setIntegral_diff (μ := volume) measurableSet_ball (hGint R (hM.trans_le hR))
      (ball_subset_ball hR)
    have hzero : ∫ ζ in ball z R \ ball z M, (ω ζ - ω z) / (ζ - z) ^ 2 = 0 := by
      calc ∫ ζ in ball z R \ ball z M, (ω ζ - ω z) / (ζ - z) ^ 2
          = ∫ ζ in ball z R \ ball z M, -ω z * (1 / (ζ - z) ^ 2) := by
            refine setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball)
              fun ζ hζ => ?_
            have h2 : M ≤ ‖ζ - z‖ := by
              have h := hζ.2
              rw [mem_ball, dist_eq_norm, not_lt] at h
              exact h
            simp only [hvanish ζ h2]
            ring
        _ = -ω z * ∫ ζ in annulusAt z M R, 1 / (ζ - z) ^ 2 := by
            rw [integral_const_mul, setIntegral_congr_set (ball_diff_ball_ae_eq_annulusAt z M R)]
        _ = 0 := by
            rcases hR.lt_or_eq with hlt | heq
            · rw [integral_annulus_inv_sq z hM hlt, mul_zero]
            · have he : annulusAt z M R = ∅ := by
                ext ζ
                simp only [annulusAt, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and,
                  not_lt]
                intro h
                linarith
              rw [he, Measure.restrict_empty, integral_zero_measure, mul_zero]
    rw [hzero] at hdiff
    linear_combination -hdiff
  -- for `0 < r < M` the truncated integral is an integral over an annulus
  have hF : ∀ r, 0 < r → r < M →
      ∫ ζ in {ζ : ℂ | r < ‖ζ - z‖}, ω ζ / (ζ - z) ^ 2 =
        ∫ ζ in annulusAt z r M, (ω ζ - ω z) / (ζ - z) ^ 2 := by
    intro r hr hrM
    have hsub : annulusAt z r M ⊆ {ζ : ℂ | r < ‖ζ - z‖} := fun ζ hζ => hζ.1
    have hmeasT : MeasurableSet {ζ : ℂ | r < ‖ζ - z‖} :=
      measurableSet_lt measurable_const (measurable_id.sub_const z).norm
    rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero hmeasT hsub fun ζ hζ => ?_]
    · have hint1 : IntegrableOn (fun ζ => (ω ζ - ω z) / (ζ - z) ^ 2) (annulusAt z r M) :=
        (hGint M hM).mono_set fun ζ hζ => by rw [mem_ball, dist_eq_norm]; exact hζ.2
      have hint2 : IntegrableOn (fun ζ => ω z * (1 / (ζ - z) ^ 2)) (annulusAt z r M) := by
        have hK : IsCompact (closedBall z M ∩ {ζ : ℂ | r ≤ ‖ζ - z‖}) :=
          (isCompact_closedBall z M).inter_right
            (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
        have hcont : ContinuousOn (fun ζ => ω z * (1 / (ζ - z) ^ 2))
            (closedBall z M ∩ {ζ : ℂ | r ≤ ‖ζ - z‖}) := by
          refine continuousOn_const.mul (continuousOn_const.div
            ((continuousOn_id.sub continuousOn_const).pow 2) fun ζ hζ => ?_)
          have h1 : r ≤ ‖ζ - z‖ := hζ.2
          refine pow_ne_zero 2 fun h0 => ?_
          have h0' : ζ - z = 0 := h0
          rw [h0', norm_zero] at h1
          linarith
        refine (hcont.integrableOn_compact hK).mono_set fun ζ hζ => ⟨?_, hζ.1.le⟩
        rw [mem_closedBall, dist_eq_norm]
        exact hζ.2.le
      calc ∫ ζ in annulusAt z r M, ω ζ / (ζ - z) ^ 2
          = ∫ ζ in annulusAt z r M, ((ω ζ - ω z) / (ζ - z) ^ 2 + ω z * (1 / (ζ - z) ^ 2)) := by
            refine setIntegral_congr_fun measurableSet_annulusAt fun ζ _ => ?_
            ring
        _ = ∫ ζ in annulusAt z r M, (ω ζ - ω z) / (ζ - z) ^ 2 := by
            rw [integral_add hint1 hint2, integral_const_mul, integral_annulus_inv_sq z hr hrM,
              mul_zero, add_zero]
    · have h1 : r < ‖ζ - z‖ := hζ.1
      have h3 : M ≤ ‖ζ - z‖ := by
        by_contra h
        exact hζ.2 ⟨h1, not_le.1 h⟩
      rw [hvanish ζ h3, zero_div]
  -- the annulus integrals converge to the disc integral
  have hlim : Tendsto (fun r => ∫ ζ in annulusAt z r M, (ω ζ - ω z) / (ζ - z) ^ 2) (𝓝[>] 0)
      (𝓝 (∫ ζ in ball z M, (ω ζ - ω z) / (ζ - z) ^ 2)) := by
    rw [tendsto_iff_edist_tendsto_0]
    have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        edist (∫ ζ in annulusAt z r M, (ω ζ - ω z) / (ζ - z) ^ 2)
          (∫ ζ in ball z M, (ω ζ - ω z) / (ζ - z) ^ 2) ≤ ENNReal.ofReal (L * (4 * π * r)) := by
      filter_upwards [Ioo_mem_nhdsGT hM] with r hr
      have hsubA : annulusAt z r M ⊆ ball z M := fun ζ hζ => by
        rw [mem_ball, dist_eq_norm]; exact hζ.2
      rw [edist_comm, edist_eq_enorm_sub, ← setIntegral_diff measurableSet_annulusAt (hGint M hM) hsubA]
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      refine (lintegral_mono_set (t := ball z (2 * r)) fun ζ hζ => ?_).trans
        ((lintegral_enorm_le_of_norm_le_div hLnn _ hGb).trans (le_of_eq ?_))
      · have h1 : ‖ζ - z‖ < M := by
          have h := hζ.1
          rw [mem_ball, dist_eq_norm] at h
          exact h
        have h2 : ‖ζ - z‖ ≤ r := by
          by_contra h
          exact hζ.2 ⟨not_le.1 h, h1⟩
        rw [mem_ball, dist_eq_norm]
        linarith [hr.1]
      · rw [lintegral_ball_sub_enorm_rpow_neg (by norm_num) (by linarith [hr.1]) z,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hLnn,
          show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, div_one]
        congr 1
        ring
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
      (Eventually.of_forall fun _ => zero_le) hbound
    have h := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := (L : ℝ))).mul
      ((tendsto_id (x := 𝓝 (0 : ℝ))).const_mul (4 * π)))
    simp only [id, mul_zero, ENNReal.ofReal_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hFlim : Tendsto (fun r => -(1 / π : ℂ) * ∫ ζ in {ζ : ℂ | r < ‖ζ - z‖}, ω ζ / (ζ - z) ^ 2)
      (𝓝[>] 0) (𝓝 (-(1 / π : ℂ) * ∫ ζ in ball z M, (ω ζ - ω z) / (ζ - z) ^ 2)) := by
    refine (hlim.const_mul (-(1 / π : ℂ))).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hM] with r hr
    rw [hF r hr.1 hr.2]
  have hH : hilbertHSmooth ω z = -(1 / π : ℂ) * ∫ ζ in ball z M, (ω ζ - ω z) / (ζ - z) ^ 2 :=
    hFlim.limUnder_eq
  rw [hH]
  refine ⟨hFlim, tendsto_const_nhds.congr' ?_⟩
  filter_upwards [eventually_ge_atTop M] with R hR
  rw [hconst R hR]

/-! ## Derivatives of `T(ω)` -/

/-- `T(G) = k ⋆ G` for the locally integrable kernel `k(t) = 1/(π t)`. -/
theorem cauchyT_eq_convolution (G : ℂ → ℂ) :
    cauchyT G = convolution (fun t : ℂ => 1 / ((π : ℂ) * t)) G
      (ContinuousLinearMap.mul ℝ ℂ) volume := by
  funext z
  rw [cauchyT, convolution_def, ← integral_sub_left_eq_self (fun ζ => G ζ / (ζ - z)) volume z,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.mul_apply', sub_sub_cancel_left]
  ring

theorem locallyIntegrable_cauchyKernel :
    LocallyIntegrable (fun t : ℂ => 1 / ((π : ℂ) * t)) volume := by
  intro x
  refine ⟨ball (0 : ℂ) (‖x‖ + 1),
    isOpen_ball.mem_nhds (by rw [mem_ball, dist_zero_right]; linarith), ?_⟩
  have h := (integrableOn_cauchy_kernel_ball (R := ‖x‖ + 1) (by positivity) 0).const_mul
    (1 / (π : ℂ))
  refine IntegrableOn.congr_fun h (fun t _ => ?_) measurableSet_ball
  simp only [sub_zero]
  ring

/-- A continuous compactly supported function against the Cauchy kernel is integrable. -/
theorem integrable_div_sub_of_hasCompactSupport {G : ℂ → ℂ} (hG : Continuous G)
    (hc : HasCompactSupport G) (z : ℂ) : Integrable (fun ζ => G ζ / (ζ - z)) := by
  obtain ⟨R₀, hR₀⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = max R₀ 0 + 1 := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hRdef]; positivity
  have hsub : tsupport G ⊆ closedBall 0 R :=
    hR₀.trans (closedBall_subset_closedBall (by rw [hRdef]; linarith [le_max_left R₀ 0]))
  have hker := integrableOn_cauchy_kernel_of_subset hR (subset_refl _) z
  have h1 := hker.continuousOn_mul hG.continuousOn (isCompact_closedBall 0 R)
  have hsupp : Function.support (fun ζ => G ζ * (1 / (ζ - z))) ⊆ closedBall 0 R :=
    (Function.support_mul_subset_left _ _).trans ((subset_tsupport G).trans hsub)
  refine ((integrableOn_iff_integrable_of_support_subset hsupp).1 h1).congr
    (Eventually.of_forall fun ζ => ?_)
  simp only [mul_one_div]

theorem hasCompactSupport_fderiv_apply {ω : ℂ → ℂ} (hc : HasCompactSupport ω) (v : ℂ) :
    HasCompactSupport (fun ζ => fderiv ℝ ω ζ v) :=
  (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L v) (by simp)

theorem contDiff_cauchyT {ω : ℂ → ℂ} (hω : ContDiff ℝ 1 ω) (hc : HasCompactSupport ω) :
    ContDiff ℝ 1 (cauchyT ω) := by
  rw [cauchyT_eq_convolution]
  exact hc.contDiff_convolution_right _ locallyIntegrable_cauchyKernel hω

theorem fderiv_cauchyT_apply {ω : ℂ → ℂ} (hω : ContDiff ℝ 1 ω) (hc : HasCompactSupport ω)
    (z v : ℂ) : fderiv ℝ (cauchyT ω) z v = cauchyT (fun ζ => fderiv ℝ ω ζ v) z := by
  have hd : HasFDerivAt (cauchyT ω) (convolution (fun t : ℂ => 1 / ((π : ℂ) * t)) (fderiv ℝ ω)
      ((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ) volume z) z := by
    rw [cauchyT_eq_convolution]
    exact hc.hasFDerivAt_convolution_right _ locallyIntegrable_cauchyKernel hω z
  have hex := (hc.fderiv (𝕜 := ℝ)).convolutionExists_right
    ((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ) locallyIntegrable_cauchyKernel
    (hω.continuous_fderiv one_ne_zero) z
  rw [hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hex, cauchyT_eq_convolution,
    convolution_def]
  simp

theorem dzbar_cauchyT {ω : ℂ → ℂ} (hω : ContDiff ℝ 1 ω) (hc : HasCompactSupport ω) (z : ℂ) :
    dzbar (cauchyT ω) z = cauchyT (dzbar ω) z := by
  have hcf := hω.continuous_fderiv one_ne_zero
  have hi1 := integrable_div_sub_of_hasCompactSupport (hcf.clm_apply continuous_const)
    (hasCompactSupport_fderiv_apply hc 1) z
  have hiI := integrable_div_sub_of_hasCompactSupport (hcf.clm_apply continuous_const)
    (hasCompactSupport_fderiv_apply hc I) z
  rw [dzbar, fderiv_cauchyT_apply hω hc, fderiv_cauchyT_apply hω hc]
  simp only [cauchyT]
  have h : ∫ ζ, dzbar ω ζ / (ζ - z) = (1 / 2 : ℂ) * (∫ ζ, fderiv ℝ ω ζ 1 / (ζ - z)) +
      (I / 2) * ∫ ζ, fderiv ℝ ω ζ I / (ζ - z) := by
    have e : (fun ζ => dzbar ω ζ / (ζ - z)) = fun ζ => (1 / 2 : ℂ) * (fderiv ℝ ω ζ 1 / (ζ - z)) +
        (I / 2) * (fderiv ℝ ω ζ I / (ζ - z)) := by
      funext ζ
      simp only [dzbar]
      ring
    rw [e, integral_add (hi1.const_mul _) (hiI.const_mul _), integral_const_mul,
      integral_const_mul]
  rw [h]
  ring

theorem dz_cauchyT {ω : ℂ → ℂ} (hω : ContDiff ℝ 1 ω) (hc : HasCompactSupport ω) (z : ℂ) :
    dz (cauchyT ω) z = cauchyT (dz ω) z := by
  have hcf := hω.continuous_fderiv one_ne_zero
  have hi1 := integrable_div_sub_of_hasCompactSupport (hcf.clm_apply continuous_const)
    (hasCompactSupport_fderiv_apply hc 1) z
  have hiI := integrable_div_sub_of_hasCompactSupport (hcf.clm_apply continuous_const)
    (hasCompactSupport_fderiv_apply hc I) z
  rw [dz, fderiv_cauchyT_apply hω hc, fderiv_cauchyT_apply hω hc]
  simp only [cauchyT]
  have h : ∫ ζ, dz ω ζ / (ζ - z) = (1 / 2 : ℂ) * (∫ ζ, fderiv ℝ ω ζ 1 / (ζ - z)) +
      (-I / 2) * ∫ ζ, fderiv ℝ ω ζ I / (ζ - z) := by
    have e : (fun ζ => dz ω ζ / (ζ - z)) = fun ζ => (1 / 2 : ℂ) * (fderiv ℝ ω ζ 1 / (ζ - z)) +
        (-I / 2) * (fderiv ℝ ω ζ I / (ζ - z)) := by
      funext ζ
      simp only [dz]
      ring
    rw [e, integral_add (hi1.const_mul _) (hiI.const_mul _), integral_const_mul,
      integral_const_mul]
  rw [h]
  ring

/-- `T(∂_z̄ ω) = ω` for `ω ∈ C¹₀`: Pompeiu's formula on a disc containing the support. -/
theorem cauchyT_dzbar_eq {ω : ℂ → ℂ} (hω : ContDiff ℝ 1 ω) (hc : HasCompactSupport ω) (z : ℂ) :
    cauchyT (dzbar ω) z = ω z := by
  obtain ⟨M₀, hM₀⟩ := hc.isCompact.isBounded.subset_closedBall z
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = max M₀ 0 + 1 := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hRdef]; positivity
  have hout : ∀ ζ, R ≤ ‖ζ - z‖ → ζ ∉ tsupport ω := by
    intro ζ hζ hmem
    have h1 := mem_closedBall.1 (hM₀ hmem)
    rw [dist_eq_norm] at h1
    have h2 : M₀ < R := by rw [hRdef]; linarith [le_max_left M₀ 0]
    linarith
  have hp := eq11_11_pompeiu (c := z) hR hω.contDiffOn (mem_ball_self hR)
  have hcirc : (∮ ζ in C(z, R), ω ζ / (ζ - z)) = 0 := by
    have h : EqOn (fun ζ => ω ζ / (ζ - z)) (fun _ => (0 : ℂ)) (sphere z R) := by
      intro ζ hζ
      rw [mem_sphere, dist_eq_norm] at hζ
      simp only
      rw [image_eq_zero_of_notMem_tsupport (hout ζ hζ.ge), zero_div]
    rw [circleIntegral.integral_congr hR.le h]
    simp [circleIntegral]
  have harea : ∫ ζ in ball z R, dzbar ω ζ / (ζ - z) = ∫ ζ, dzbar ω ζ / (ζ - z) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun ζ hζ => ?_
    rw [mem_ball, dist_eq_norm, not_lt] at hζ
    simp [dzbar, fderiv_of_notMem_tsupport ℝ (hout ζ hζ)]
  rw [hcirc, mul_zero, zero_sub, harea] at hp
  rw [cauchyT, hp]
  ring

/-- `∂_z (ζ - z)⁻¹ = -(ζ - z)⁻²` away from the pole. -/
theorem dz_inv_sub {z w : ℂ} (hw : w ≠ z) :
    dz (fun ζ : ℂ => (ζ - z)⁻¹) w = -((w - z) ^ 2)⁻¹ := by
  have hd : HasDerivAt (fun ζ : ℂ => (ζ - z)⁻¹) (-(1 : ℂ) / (w - z) ^ 2) w :=
    ((hasDerivAt_id w).sub_const z).inv (sub_ne_zero.2 hw)
  have hf : fderiv ℝ (fun ζ : ℂ => (ζ - z)⁻¹) w =
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(1 : ℂ) / (w - z) ^ 2)).restrictScalars
        ℝ) :=
    (hd.hasFDerivAt.restrictScalars ℝ).fderiv
  simp only [dz, hf, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul]
  linear_combination (-(-(1 : ℂ) / (w - z) ^ 2) / 2) * I_mul_I

/-- The `∂_z` analogue of the two-disc Green identity: for `0 < r < R` and `ω ∈ C¹` vanishing on
`|ζ - z| = R`, `∬_{r ≤ |ζ - z| < R} (∂_z ω/(ζ - z) - ω/(ζ - z)²) = (1/2i) ∮_{|ζ - z| = r} ω/(ζ - z) dζ̄`. -/
theorem integral_ball_diff_dz_eq {ω : ℂ → ℂ} (hω : ContDiff ℝ 1 ω) {z : ℂ} {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) (hvan : ∀ θ : ℝ, ω (circleMap z R θ) = 0) :
    ∫ ζ in ball z R \ ball z r, (dz ω ζ / (ζ - z) - ω ζ / (ζ - z) ^ 2) =
      (∫ θ in (0 : ℝ)..2 * π, ω (circleMap z r θ) / (circleMap z r θ - z) *
        conj (deriv (circleMap z r) θ)) / (2 * I) := by
  have hR : 0 < R := hr.trans hrR
  obtain ⟨χ, -, -, hχ1, hu⟩ := exists_kernel_cutoff z hr
  obtain ⟨u, hudef⟩ : ∃ u : ℂ → ℂ, u = fun ζ => (χ ζ * (ζ - z)⁻¹) * ω ζ := ⟨_, rfl⟩
  have huC : ContDiff ℝ 1 u := by rw [hudef]; exact hu.mul hω
  have hG1 := green_disc_dz_closedBall (c := z) hR huC.contDiffOn
  have hG2 := green_disc_dz_closedBall (c := z) hr huC.contDiffOn
  have hc1 : ∀ θ : ℝ, u (circleMap z R θ) = 0 := fun θ => by
    rw [hudef]
    simp only [hvan θ, mul_zero]
  have hc2 : ∀ θ : ℝ, u (circleMap z r θ) = ω (circleMap z r θ) / (circleMap z r θ - z) := by
    intro θ
    have h1 : r ≤ ‖circleMap z r θ - z‖ := by
      rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]
    rw [hudef]
    simp only [hχ1 _ h1, one_mul, div_eq_mul_inv]
    ring
  simp only [hc1, zero_mul, intervalIntegral.integral_zero] at hG1
  simp only [hc2] at hG2
  have hdzc : Continuous (dz u) := by
    have h := huC.continuous_fderiv one_ne_zero
    show Continuous fun ζ => (fderiv ℝ u ζ 1 - I * fderiv ℝ u ζ I) / 2
    exact ((h.clm_apply continuous_const).sub
      (continuous_const.mul (h.clm_apply continuous_const))).div_const 2
  have hint : IntegrableOn (dz u) (ball z R) :=
    (hdzc.continuousOn.integrableOn_compact (isCompact_closedBall z R)).mono_set
      ball_subset_closedBall
  have hsplit := setIntegral_diff (μ := volume) measurableSet_ball hint (ball_subset_ball hrR.le)
  have h0 : ∫ ζ in ball z R, dz u ζ = 0 :=
    (mul_eq_zero.1 hG1.symm).resolve_left (by simp)
  have hcongr : ∫ ζ in ball z R \ ball z r, dz u ζ =
      ∫ ζ in ball z R \ ball z r, (dz ω ζ / (ζ - z) - ω ζ / (ζ - z) ^ 2) := by
    refine setIntegral_congr_ae (measurableSet_ball.diff measurableSet_ball) ?_
    have hs : ∀ᵐ ζ : ℂ, ζ ∉ sphere z r := by
      rw [ae_iff]
      exact measure_mono_null (fun a ha => not_not.1 ha)
        (Measure.addHaar_sphere (volume : Measure ℂ) z r)
    filter_upwards [hs] with ζ hζs hζ
    have hge : r ≤ ‖ζ - z‖ := by
      have h := hζ.2
      rwa [mem_ball, dist_eq_norm, not_lt] at h
    have hgt : r < ‖ζ - z‖ :=
      lt_of_le_of_ne hge fun h => hζs (by rw [mem_sphere, dist_eq_norm]; exact h.symm)
    have hne : ζ ≠ z := fun h => by
      rw [h, sub_self, norm_zero] at hgt
      linarith
    have hev : u =ᶠ[𝓝 ζ] fun w => (w - z)⁻¹ * ω w := by
      have hopen : IsOpen {w : ℂ | r < ‖w - z‖} :=
        isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
      filter_upwards [hopen.mem_nhds hgt] with w hw
      rw [hudef]
      simp only [hχ1 w hw.le, one_mul]
    rw [show dz u ζ = dz (fun w => (w - z)⁻¹ * ω w) ζ by simp only [dz, hev.fderiv_eq],
      dz_mul (differentiableAt_inv_sub hne) ((hω.differentiable one_ne_zero) ζ), dz_inv_sub hne]
    ring
  rw [← hcongr, hsplit, h0, zero_sub, hG2,
    show (-2 * I * ∫ ζ in ball z r, dz u ζ) = -((∫ ζ in ball z r, dz u ζ) * (2 * I)) by ring,
    neg_div, mul_div_cancel_right₀ _ (by simp : (2 * I : ℂ) ≠ 0)]

/-- The truncated Hilbert integrals of `ω ∈ C¹₀` converge to `T(∂_z ω)(z)`. -/
theorem tendsto_truncated_cauchyT_dz {ω : ℂ → ℂ} (hω : ContDiff ℝ 1 ω)
    (hc : HasCompactSupport ω) (z : ℂ) :
    Tendsto (fun r => -(1 / π : ℂ) * ∫ ζ in {ζ : ℂ | r < ‖ζ - z‖}, ω ζ / (ζ - z) ^ 2)
      (𝓝[>] 0) (𝓝 (cauchyT (dz ω) z)) := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hω one_ne_zero
  obtain ⟨Cf, hCf⟩ := (hc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hω.continuous_fderiv one_ne_zero)
  obtain ⟨M₀, hM₀⟩ := hc.isCompact.isBounded.subset_closedBall z
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = max M₀ 0 + 1 := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hRdef]; positivity
  have hωc : Continuous ω := hω.continuous
  have hout : ∀ ζ, R ≤ ‖ζ - z‖ → ζ ∉ tsupport ω := by
    intro ζ hζ hmem
    have h1 := mem_closedBall.1 (hM₀ hmem)
    rw [dist_eq_norm] at h1
    have h2 : M₀ < R := by rw [hRdef]; linarith [le_max_left M₀ 0]
    linarith
  have hvan : ∀ ζ, R ≤ ‖ζ - z‖ → ω ζ = 0 := fun ζ hζ =>
    image_eq_zero_of_notMem_tsupport (hout ζ hζ)
  have hdzvan : ∀ ζ, R ≤ ‖ζ - z‖ → dz ω ζ = 0 := fun ζ hζ => by
    simp [dz, fderiv_of_notMem_tsupport ℝ (hout ζ hζ)]
  have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf 0)
  have hdzb : ∀ ζ, ‖dz ω ζ‖ ≤ Cf := by
    intro ζ
    have h1 : ‖fderiv ℝ ω ζ 1‖ ≤ Cf :=
      ((fderiv ℝ ω ζ).le_opNorm 1).trans (by simpa using hCf ζ)
    have h2 : ‖fderiv ℝ ω ζ I‖ ≤ Cf :=
      ((fderiv ℝ ω ζ).le_opNorm I).trans (by simpa using hCf ζ)
    have h3 : ‖fderiv ℝ ω ζ 1 - I * fderiv ℝ ω ζ I‖ ≤ Cf + Cf := by
      refine (norm_sub_le _ _).trans (add_le_add h1 ?_)
      rw [norm_mul, Complex.norm_I, one_mul]
      exact h2
    rw [dz, norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
    linarith
  have hdzm : Measurable (dz ω) := by
    show Measurable fun ζ => (fderiv ℝ ω ζ 1 - I * fderiv ℝ ω ζ I) / 2
    exact ((measurable_fderiv_apply_const ℝ ω 1).sub
      (measurable_const.mul (measurable_fderiv_apply_const ℝ ω I))).div_const 2
  have hKb : ∀ ζ, ζ ≠ z → ‖dz ω ζ / (ζ - z)‖ ≤ Cf / ‖ζ - z‖ := fun ζ _ => by
    rw [norm_div]
    exact div_le_div_of_nonneg_right (hdzb ζ) (norm_nonneg _)
  have hAm : AEStronglyMeasurable (fun ζ => dz ω ζ / (ζ - z)) volume :=
    (hdzm.div (measurable_id.sub_const z)).aestronglyMeasurable
  have hAint : IntegrableOn (fun ζ => dz ω ζ / (ζ - z)) (ball z R) :=
    integrableOn_ball_of_norm_le_div hCf0 hR hAm hKb
  have hAfull : ∫ ζ in ball z R, dz ω ζ / (ζ - z) = ∫ ζ, dz ω ζ / (ζ - z) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun ζ hζ => ?_
    rw [mem_ball, dist_eq_norm, not_lt] at hζ
    rw [hdzvan ζ hζ, zero_div]
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ → ℂ, ∀ r, S r = ∫ θ in (0 : ℝ)..2 * π,
      ω (circleMap z r θ) / (circleMap z r θ - z) * conj (deriv (circleMap z r) θ) :=
    ⟨_, fun r => rfl⟩
  -- the identity for `0 < r < R`
  have hkey : ∀ r, 0 < r → r < R → ∫ ζ in {ζ : ℂ | r < ‖ζ - z‖}, ω ζ / (ζ - z) ^ 2 =
      (∫ ζ in ball z R \ ball z r, dz ω ζ / (ζ - z)) - S r / (2 * I) := by
    intro r hr hrR
    have hsub : annulusAt z r R ⊆ {ζ : ℂ | r < ‖ζ - z‖} := fun ζ hζ => hζ.1
    have hmeasT : MeasurableSet {ζ : ℂ | r < ‖ζ - z‖} :=
      measurableSet_lt measurable_const (measurable_id.sub_const z).norm
    rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero hmeasT hsub fun ζ hζ => ?_,
      ← setIntegral_congr_set (ball_diff_ball_ae_eq_annulusAt z r R)]
    · have hBint : IntegrableOn (fun ζ => ω ζ / (ζ - z) ^ 2) (ball z R \ ball z r) := by
        have hK : IsCompact (closedBall z R ∩ {ζ : ℂ | r ≤ ‖ζ - z‖}) :=
          (isCompact_closedBall z R).inter_right
            (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
        have hcont : ContinuousOn (fun ζ => ω ζ / (ζ - z) ^ 2)
            (closedBall z R ∩ {ζ : ℂ | r ≤ ‖ζ - z‖}) := by
          refine hωc.continuousOn.div ((continuousOn_id.sub continuousOn_const).pow 2)
            fun ζ hζ => ?_
          have h1 : r ≤ ‖ζ - z‖ := hζ.2
          refine pow_ne_zero 2 fun h0 => ?_
          have h0' : ζ - z = 0 := h0
          rw [h0', norm_zero] at h1
          linarith
        refine (hcont.integrableOn_compact hK).mono_set fun ζ hζ =>
          ⟨ball_subset_closedBall hζ.1, ?_⟩
        have h := hζ.2
        rwa [mem_ball, dist_eq_norm, not_lt] at h
      have hid := integral_ball_diff_dz_eq hω hr hrR fun θ => hvan _ (by
        rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hR])
      rw [integral_sub (hAint.mono_set diff_subset) hBint, ← hSdef r] at hid
      linear_combination -hid
    · have h1 : r < ‖ζ - z‖ := hζ.1
      have h3 : R ≤ ‖ζ - z‖ := by
        by_contra h
        exact hζ.2 ⟨h1, not_le.1 h⟩
      rw [hvan ζ h3, zero_div]
  -- the area term converges
  have hAlim : Tendsto (fun r => ∫ ζ in ball z R \ ball z r, dz ω ζ / (ζ - z)) (𝓝[>] 0)
      (𝓝 (∫ ζ, dz ω ζ / (ζ - z))) := by
    rw [← hAfull, tendsto_iff_edist_tendsto_0]
    have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ), edist (∫ ζ in ball z R \ ball z r, dz ω ζ / (ζ - z))
        (∫ ζ in ball z R, dz ω ζ / (ζ - z)) ≤ ENNReal.ofReal (Cf * (2 * π * r)) := by
      filter_upwards [Ioo_mem_nhdsGT hR] with r hr
      rw [setIntegral_diff measurableSet_ball hAint (ball_subset_ball hr.2.le), edist_eq_enorm_sub,
        sub_sub_cancel_left, enorm_neg]
      refine (enorm_integral_le_lintegral_enorm _).trans
        ((lintegral_enorm_le_of_norm_le_div hCf0 _ hKb).trans (le_of_eq ?_))
      rw [lintegral_ball_sub_enorm_rpow_neg (by norm_num) hr.1 z,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hCf0,
        show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, div_one]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
      (Eventually.of_forall fun _ => zero_le) hbound
    have h := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := Cf)).mul
      ((tendsto_id (x := 𝓝 (0 : ℝ))).const_mul (2 * π)))
    simp only [id, mul_zero, ENNReal.ofReal_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  -- the small-circle term tends to `0`
  have hSlim : Tendsto S (𝓝[>] 0) (𝓝 0) := by
    have hK : ∀ r, 0 < r → ∀ θ : ℝ, conj (deriv (circleMap z r) θ) / (circleMap z r θ - z) =
        -I * exp (((-2 * θ : ℝ) : ℂ) * I) := by
      intro r hr θ
      have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
      have he : exp ((θ : ℂ) * I) ≠ 0 := exp_ne_zero _
      rw [deriv_circleMap, circleMap_sub_center, circleMap_zero, map_mul, map_mul, conj_ofReal,
        conj_I, ← exp_conj, map_mul, conj_ofReal, conj_I,
        show exp ((θ : ℂ) * -I) = exp (((-2 * θ : ℝ) : ℂ) * I) * exp ((θ : ℂ) * I) by
          rw [← exp_add]
          congr 1
          push_cast
          ring]
      field_simp
    have hexpc : Continuous fun θ : ℝ => -I * exp (((-2 * θ : ℝ) : ℂ) * I) :=
      continuous_const.mul (continuous_exp.comp
        ((continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const))
    have hKint : ∫ θ in (0 : ℝ)..2 * π, -I * exp (((-2 * θ : ℝ) : ℂ) * I) = 0 := by
      have e1 : ∀ θ : ℝ, exp (((-2 * θ : ℝ) : ℂ) * I) = exp ((-2 * I) * θ) := fun θ => by
        congr 1
        push_cast
        ring
      simp_rw [e1]
      rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex (by simp)]
      have e2 : exp ((-2 * I) * ((2 * π : ℝ) : ℂ)) = 1 := by
        rw [show (-2 * I) * ((2 * π : ℝ) : ℂ) = ((-2 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring]
        exact exp_int_mul_two_pi_mul_I (-2)
      rw [e2]
      simp
    have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ), ‖S r‖ ≤ (L : ℝ) * r * (2 * π) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr0 : 0 < r := hr
      have hωcirc : Continuous fun θ => ω (circleMap z r θ) := hωc.comp (continuous_circleMap z r)
      have hSr : S r = ∫ θ in (0 : ℝ)..2 * π,
          (ω (circleMap z r θ) - ω z) * (-I * exp (((-2 * θ : ℝ) : ℂ) * I)) := by
        rw [hSdef]
        calc ∫ θ in (0 : ℝ)..2 * π,
              ω (circleMap z r θ) / (circleMap z r θ - z) * conj (deriv (circleMap z r) θ)
            = ∫ θ in (0 : ℝ)..2 * π, ω (circleMap z r θ) * (-I * exp (((-2 * θ : ℝ) : ℂ) * I)) := by
              refine intervalIntegral.integral_congr fun θ _ => ?_
              rw [div_mul_eq_mul_div, mul_div_assoc, hK r hr0 θ]
          _ = ∫ θ in (0 : ℝ)..2 * π, ((ω (circleMap z r θ) - ω z) *
                (-I * exp (((-2 * θ : ℝ) : ℂ) * I)) + ω z * (-I * exp (((-2 * θ : ℝ) : ℂ) * I))) := by
              refine intervalIntegral.integral_congr fun θ _ => ?_
              ring
          _ = _ := by
              have hc3 : Continuous fun θ : ℝ =>
                  (ω (circleMap z r θ) - ω z) * (-I * exp (((-2 * θ : ℝ) : ℂ) * I)) :=
                (hωcirc.sub continuous_const).mul hexpc
              have hc4 : Continuous fun θ : ℝ => ω z * (-I * exp (((-2 * θ : ℝ) : ℂ) * I)) :=
                continuous_const.mul hexpc
              rw [intervalIntegral.integral_add (hc3.intervalIntegrable _ _)
                (hc4.intervalIntegrable _ _),
                intervalIntegral.integral_const_mul, hKint, mul_zero, add_zero]
      rw [hSr]
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := (L : ℝ) * r)
        fun θ _ => ?_).trans
        (le_of_eq ?_)
      · rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
          Complex.norm_exp_ofReal_mul_I, mul_one]
        have h := hL.dist_le_mul (circleMap z r θ) z
        rwa [dist_eq_norm, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
          abs_of_pos hr0] at h
      · rw [sub_zero, abs_of_pos (by positivity)]
    have h' : Tendsto (fun r : ℝ => (L : ℝ) * r * (2 * π)) (𝓝[>] 0) (𝓝 0) := by
      have h := ((tendsto_const_nhds (x := (L : ℝ))).mul
        (tendsto_id (x := 𝓝 (0 : ℝ)))).mul_const (2 * π)
      simp only [id, mul_zero, zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    exact squeeze_zero_norm' hbound h'
  have hlimR := ((hAlim.sub (hSlim.div_const (2 * I))).const_mul (-(1 / π : ℂ)))
  have hval : cauchyT (dz ω) z =
      -(1 / π : ℂ) * ((∫ ζ, dz ω ζ / (ζ - z)) - 0 / (2 * I)) := by
    rw [zero_div, sub_zero, cauchyT]
  rw [hval]
  refine hlimR.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  rw [hkey r hr.1 hr.2]

/-- (11.17): for `ω ∈ C₀^∞`, `T_ω ∈ C¹` with `∂_{z̄} T_ω = ω` and `∂_z T_ω = H_ω`.

`T(ω) = k ⋆ ω` for the locally integrable kernel `k(t) = 1/(π t)`, so `T(ω) ∈ C¹` with
`∂_v T(ω) = T(∂_v ω)` (Mathlib's derivative of a convolution with a compactly supported `C¹`
function).  `T(∂_z̄ ω) = ω` is then Pompeiu's formula on a disc containing the support.

For `∂_z`, Green's formula for `∂_z` is applied twice to the same cutoff function, on a large disc
and on a small disc `|ζ - z| < r`.  This gives
`∬_{r ≤ |ζ - z|} ω/(ζ - z)² = ∬_{r ≤ |ζ - z|} ∂_z ω/(ζ - z) - (1/2i) ∮_{|ζ - z| = r} ω/(ζ - z) dζ̄`.
The circle term is `O(r)` because `∫₀^{2π} e^{-2iθ} dθ = 0`, so the principal value (11.15) equals
`T(∂_z ω)` (`tendsto_truncated_cauchyT_dz`).

*Correction.*  `C₀^∞` is written `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω`.  A bare
`ContDiff ℝ ⊤ ω` would mean real analyticity (`ω`-smoothness) in current Mathlib, and a
real-analytic function with compact support vanishes identically, which would make the statement
degenerate. -/
theorem eq11_17 {ω : ℂ → ℂ} (hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω) (hc : HasCompactSupport ω) :
    ContDiff ℝ 1 (cauchyT ω) ∧ ∀ z, dzbar (cauchyT ω) z = ω z ∧ dz (cauchyT ω) z = hilbertHSmooth ω z := by
  have hω1 : ContDiff ℝ 1 ω := hω.of_le (by simp)
  refine ⟨contDiff_cauchyT hω1 hc, fun z => ⟨?_, ?_⟩⟩
  · rw [dzbar_cauchyT hω1 hc, cauchyT_dzbar_eq hω1 hc]
  · rw [dz_cauchyT hω1 hc]
    exact tendsto_nhds_unique (tendsto_truncated_cauchyT_dz hω1 hc z) (eq11_15 hω hc z).1

/-- (11.19): `z̄ = -(1/π) ∬_{|ζ| < R} dξ dη/(ζ - z)` for `|z| < R`. -/
theorem eq11_19 {R : ℝ} {z : ℂ} (hz : ‖z‖ < R) :
    conj z = -(1 / π : ℂ) * ∫ ζ in ball (0 : ℂ) R, 1 / (ζ - z) := by
  have hR : 0 < R := (norm_nonneg z).trans_lt hz
  have hpi : ((π : ℝ) : ℂ) ≠ 0 := by simp
  have hmeas : Measurable fun ζ : ℂ => 1 / (ζ - z) :=
    measurable_const.div (measurable_id.sub measurable_const)
  have hint := integrableOn_polar_of_integrableOn_ball hmeas
    (integrableOn_cauchy_kernel_ball hR z)
  have hpol : (∫ ζ in ball (0 : ℂ) R, 1 / (ζ - z))
      = ∫ r in (0 : ℝ)..R, ∫ θ in (0 : ℝ)..(2 * π),
          (r : ℂ) * (1 / (circleMap 0 r θ - z)) :=
    setIntegral_ball_eq_polar' (g := fun ζ : ℂ => 1 / (ζ - z)) 0 hR.le (by simpa using hint)
  rcases eq_or_ne z 0 with rfl | hz0
  · have hEqZ : Set.EqOn
        (fun r : ℝ => ∫ θ in (0 : ℝ)..(2 * π), (r : ℂ) * (1 / (circleMap 0 r θ - 0)))
        (fun _ : ℝ => (0 : ℂ)) (Set.uIcc 0 R) := by
      intro r hr
      rw [Set.uIcc_of_le hR.le] at hr
      rcases hr.1.lt_or_eq with hlt | heq
      · simp only
        rw [integral_circleMap_cauchy_kernel hlt 0, circleIntegral_cauchy_kernel_zero hlt]
        ring
      · simp only [← heq]
        simp
    rw [hpol, intervalIntegral.integral_congr hEqZ, intervalIntegral.integral_zero]
    simp
  · rw [hpol, integral_polar_cauchy_kernel hz0 hz]
    field_simp

/-- `cauchyT` depends only on the a.e. class of `ω` (exact, funext, not just a.e.), by
`integral_congr_ae`. -/
theorem cauchyT_congr_ae {ω₁ ω₂ : ℂ → ℂ} (h : ω₁ =ᵐ[volume] ω₂) : cauchyT ω₁ = cauchyT ω₂ := by
  funext z
  unfold cauchyT
  congr 1
  apply integral_congr_ae
  filter_upwards [h] with ζ hζ
  rw [hζ]

/-- `hilbertHSmooth` depends only on the a.e. class of `ω` (exact, funext, not just a.e.): the
truncated integral defining it agrees exactly at every `r`, since the integrand's null set
of disagreement does not depend on `r` or `z`. -/
theorem hilbertHSmooth_congr_ae {ω₁ ω₂ : ℂ → ℂ} (h : ω₁ =ᵐ[volume] ω₂) :
    hilbertHSmooth ω₁ = hilbertHSmooth ω₂ := by
  funext z
  unfold hilbertHSmooth
  congr 1
  funext r
  congr 1
  apply setIntegral_congr_ae (measurableSet_lt measurable_const (measurable_id.sub_const z).norm)
  filter_upwards [h] with ζ hζ
  intro _
  rw [hζ]

/-- For `ω ∈ L_p`, `p > 2`, vanishing outside `D_R`, the Cauchy kernel `ω(ζ)/(ζ - z)` is
(genuinely, not just norm-bounded as in `lemma11_1`) integrable, for every `z`. -/
theorem integrable_cauchyT_kernel {p : ℝ} (hp : 2 < p) {R : ℝ} (hR : 0 < R) {ω : ℂ → ℂ}
    (hω : MemLp ω (ENNReal.ofReal p)) (hsupp : ∀ z, R < ‖z‖ → ω z = 0) (z : ℂ) :
    Integrable (fun ζ => ω ζ / (ζ - z)) volume := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hpne : p ≠ 0 := hp0.ne'
  have hp1ne : p - 1 ≠ 0 := hp1.ne'
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = p / (p - 1) := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; exact div_pos hp0 hp1
  have hq2 : q < 2 := by rw [hq, div_lt_iff₀ hp1]; linarith
  have hpq : p.HolderConjugate q := by
    refine ⟨?_, hp0, hq0⟩
    rw [hq, inv_one]
    field_simp
    ring
  have hmeas : AEStronglyMeasurable (fun ζ : ℂ => ω ζ / (ζ - z)) volume :=
    (hω.aestronglyMeasurable.aemeasurable.div
      (measurable_id.sub_const z).aemeasurable).aestronglyMeasurable
  have hSm : MeasurableSet (closedBall (0 : ℂ) R) := measurableSet_closedBall
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0∞, C = (∫⁻ w in ball (0 : ℂ) R, ‖w‖ₑ ^ (-q)) +
      ENNReal.ofReal (R ^ (-q)) * volume (closedBall (0 : ℂ) R) := ⟨_, rfl⟩
  have hCne : C ≠ ⊤ := by
    rw [hC]
    exact ENNReal.add_ne_top.2 ⟨lintegral_ball_enorm_rpow_neg_ne_top hq0.le hq2 R,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ≥0∞, A = C ^ (1 / q) := ⟨_, rfl⟩
  have hAne : A ≠ ⊤ := by
    rw [hA]; exact ENNReal.rpow_ne_top_of_nonneg (div_nonneg zero_le_one hq0.le) hCne
  have hsub : ∀ ζ : ℂ, ‖ω ζ / (ζ - z)‖ₑ ≤
      (closedBall (0 : ℂ) R).indicator (fun ζ => ‖ω ζ‖ₑ * ‖ζ - z‖ₑ⁻¹) ζ := by
    intro ζ
    by_cases hζ : ζ ∈ closedBall (0 : ℂ) R
    · rw [Set.indicator_of_mem hζ]
      rcases eq_or_ne ζ z with rfl | hne
      · simp
      · have hb : (0 : ℝ) < ‖ζ - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
        refine le_of_eq ?_
        rw [← ofReal_norm (ω ζ / (ζ - z)), ← ofReal_norm (ω ζ), ← ofReal_norm (ζ - z),
          norm_div, ENNReal.ofReal_div_of_pos hb, div_eq_mul_inv]
    · rw [Set.indicator_of_notMem hζ]
      have hz0 : ω ζ = 0 := hsupp ζ (by simpa [mem_closedBall_zero_iff, not_le] using hζ)
      simp [hz0]
  have hkey : ∫⁻ ζ, ‖ω ζ / (ζ - z)‖ₑ ≤
      ENNReal.ofReal 1 * (eLpNorm ω (ENNReal.ofReal p) * A) := by
    rw [ENNReal.ofReal_one, one_mul]
    refine (lintegral_mono hsub).trans ?_
    rw [lintegral_indicator hSm]
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq
      (volume.restrict (closedBall (0 : ℂ) R)) hpq
      (f := fun ζ => ‖ω ζ‖ₑ) (g := fun ζ : ℂ => ‖ζ - z‖ₑ⁻¹)
      hω.aestronglyMeasurable.aemeasurable.enorm.restrict
      ((measurable_id.sub_const z).enorm.inv.aemeasurable)
    simp only [Pi.mul_apply] at h
    refine h.trans ?_
    refine mul_le_mul' ?_ ?_
    · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp0).ne'
        ENNReal.ofReal_ne_top hω.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
      exact ENNReal.rpow_le_rpow (lintegral_mono' Measure.restrict_le_self le_rfl)
        (div_nonneg zero_le_one hp0.le)
    · have hg : ∀ ζ : ℂ, (‖ζ - z‖ₑ⁻¹) ^ q = ‖ζ - z‖ₑ ^ (-q) := fun ζ => by
        rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg]
      simp only [hg]
      rw [hA]
      refine ENNReal.rpow_le_rpow ?_ (div_nonneg zero_le_one hq0.le)
      rw [hC]
      exact lintegral_closedBall_enorm_sub_rpow_neg_le hq0 hR z
  have hfin : ENNReal.ofReal 1 * (eLpNorm ω (ENNReal.ofReal p) * A) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hω.eLpNorm_ne_top hAne)
  exact ⟨hmeas, lt_of_le_of_lt hkey hfin.lt_top⟩

/-- `T` is additive on `L_p` functions with support in a shared disc. -/
theorem cauchyT_add {p : ℝ} (hp : 2 < p) {R : ℝ} (hR : 0 < R) {ω₁ ω₂ : ℂ → ℂ}
    (hω₁ : MemLp ω₁ (ENNReal.ofReal p)) (hω₂ : MemLp ω₂ (ENNReal.ofReal p))
    (hsupp₁ : ∀ z, R < ‖z‖ → ω₁ z = 0) (hsupp₂ : ∀ z, R < ‖z‖ → ω₂ z = 0) :
    cauchyT (fun z => ω₁ z + ω₂ z) = fun z => cauchyT ω₁ z + cauchyT ω₂ z := by
  funext z
  have h1 := integrable_cauchyT_kernel hp hR hω₁ hsupp₁ z
  have h2 := integrable_cauchyT_kernel hp hR hω₂ hsupp₂ z
  have heq : (fun ζ => (ω₁ ζ + ω₂ ζ) / (ζ - z)) =
      (fun ζ => ω₁ ζ / (ζ - z) + ω₂ ζ / (ζ - z)) := by
    funext ζ; ring
  unfold cauchyT
  rw [heq, integral_add h1 h2, mul_add]

/-- `T` is subtractive on `L_p` functions with support in a shared disc. -/
theorem cauchyT_sub {p : ℝ} (hp : 2 < p) {R : ℝ} (hR : 0 < R) {ω₁ ω₂ : ℂ → ℂ}
    (hω₁ : MemLp ω₁ (ENNReal.ofReal p)) (hω₂ : MemLp ω₂ (ENNReal.ofReal p))
    (hsupp₁ : ∀ z, R < ‖z‖ → ω₁ z = 0) (hsupp₂ : ∀ z, R < ‖z‖ → ω₂ z = 0) :
    cauchyT (fun z => ω₁ z - ω₂ z) = fun z => cauchyT ω₁ z - cauchyT ω₂ z := by
  funext z
  have h1 := integrable_cauchyT_kernel hp hR hω₁ hsupp₁ z
  have h2 := integrable_cauchyT_kernel hp hR hω₂ hsupp₂ z
  have heq : (fun ζ => (ω₁ ζ - ω₂ ζ) / (ζ - z)) =
      (fun ζ => ω₁ ζ / (ζ - z) - ω₂ ζ / (ζ - z)) := by
    funext ζ; ring
  unfold cauchyT
  rw [heq, integral_sub h1 h2, mul_sub]

/-- For `ω ∈ L_p`, `1 < p < ∞`, the truncated Hilbert kernel `ω(ζ)/(ζ-z)²` is integrable
on `{r < ‖ζ - z‖}`, `r > 0` (no compact-support hypothesis needed: the truncation removes the
singularity, and `q = p/(p-1) > 1` makes the kernel `L_q` at infinity). -/
theorem integrableOn_truncated_kernel {p : ℝ} (hp : 1 < p) {ω : ℂ → ℂ}
    (hω : MemLp ω (ENNReal.ofReal p)) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun ζ => ω ζ / (ζ - z) ^ 2) {ζ : ℂ | r < ‖ζ - z‖} volume := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = p / (p - 1) := ⟨_, rfl⟩
  have hq1 : 1 < q := by rw [hq, lt_div_iff₀ hp1]; linarith
  have hq0 : 0 < q := by linarith
  have hpq : p.HolderConjugate q := by
    refine ⟨?_, hp0, hq0⟩
    rw [hq, inv_one]
    field_simp
    ring
  set ρ : ℝ := r + 1 with hρdef
  have hρ : 0 < ρ := by positivity
  have hmeasS : MeasurableSet {ζ : ℂ | r < ‖ζ - z‖} :=
    measurableSet_lt measurable_const (measurable_id.sub_const z).norm
  have hmeas : AEStronglyMeasurable (fun ζ : ℂ => ω ζ / (ζ - z) ^ 2) volume :=
    (hω.aestronglyMeasurable.aemeasurable.div
      ((measurable_id.sub_const z).pow_const 2).aemeasurable).aestronglyMeasurable
  refine ⟨hmeas.restrict, ?_⟩
  have hsub : ∀ ζ : ℂ, ‖ω ζ / (ζ - z) ^ 2‖ₑ ≤ ‖ω ζ‖ₑ * ‖ζ - z‖ₑ⁻¹ ^ 2 := by
    intro ζ
    rcases eq_or_ne ζ z with rfl | hne
    · simp
    · have hb : (0 : ℝ) < ‖ζ - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
      refine le_of_eq ?_
      rw [← ofReal_norm (ω ζ / (ζ - z) ^ 2), norm_div, norm_pow,
        ENNReal.ofReal_div_of_pos (by positivity), ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _),
        ofReal_norm, div_eq_mul_inv, ← ENNReal.inv_pow]
  have hcover : {ζ : ℂ | r < ‖ζ - z‖} ⊆
      ({ζ : ℂ | r < ‖ζ - z‖} ∩ closedBall z ρ) ∪ {ζ : ℂ | ρ < ‖ζ - z‖} := by
    intro ζ hζ
    by_cases hζρ : ‖ζ - z‖ ≤ ρ
    · exact Or.inl ⟨hζ, by simpa [mem_closedBall, dist_eq_norm] using hζρ⟩
    · exact Or.inr (by simpa using not_le.mp hζρ)
  have hnear : (∫⁻ ζ in ({ζ : ℂ | r < ‖ζ - z‖} ∩ closedBall z ρ), ‖ζ - z‖ₑ ^ (-(2 * q))) ≠ ⊤ := by
    have hle : ∀ ζ ∈ {ζ : ℂ | r < ‖ζ - z‖} ∩ closedBall z ρ,
        ‖ζ - z‖ₑ ^ (-(2 * q)) ≤ ENNReal.ofReal (r ^ (-(2 * q))) := by
      intro ζ hζ
      have h1 : r < ‖ζ - z‖ := hζ.1
      have hrle : ENNReal.ofReal r ≤ ‖ζ - z‖ₑ := by
        rw [← ofReal_norm (ζ - z)]; exact ENNReal.ofReal_le_ofReal h1.le
      rw [← ENNReal.ofReal_rpow_of_pos hr, ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv' (ENNReal.rpow_le_rpow hrle (by positivity))
    have hbound : (∫⁻ ζ in {ζ : ℂ | r < ‖ζ - z‖} ∩ closedBall z ρ, ‖ζ - z‖ₑ ^ (-(2 * q))) ≤
        ENNReal.ofReal (r ^ (-(2 * q))) * volume (closedBall z ρ) := by
      calc (∫⁻ ζ in {ζ : ℂ | r < ‖ζ - z‖} ∩ closedBall z ρ, ‖ζ - z‖ₑ ^ (-(2 * q)))
          ≤ ∫⁻ _ in {ζ : ℂ | r < ‖ζ - z‖} ∩ closedBall z ρ, ENNReal.ofReal (r ^ (-(2 * q))) := by
            refine lintegral_mono_ae ?_
            filter_upwards [self_mem_ae_restrict
              ((measurableSet_lt measurable_const (measurable_id.sub_const z).norm).inter
                measurableSet_closedBall)] with ζ hζ using hle ζ hζ
        _ = ENNReal.ofReal (r ^ (-(2 * q))) *
              volume ({ζ : ℂ | r < ‖ζ - z‖} ∩ closedBall z ρ) := by
            rw [lintegral_const, Measure.restrict_apply_univ]
        _ ≤ ENNReal.ofReal (r ^ (-(2 * q))) * volume (closedBall z ρ) :=
            mul_le_mul' le_rfl (measure_mono Set.inter_subset_right)
    exact (hbound.trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top)).ne
  have hfar : (∫⁻ ζ in {ζ : ℂ | ρ < ‖ζ - z‖}, ‖ζ - z‖ₑ ^ (-(2 * q))) ≠ ⊤ := by
    rw [lintegral_compl_ball_sub_enorm_rpow_neg (by linarith : (2 : ℝ) < 2 * q) hρ z]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hCfin : (∫⁻ ζ in {ζ : ℂ | r < ‖ζ - z‖}, ‖ζ - z‖ₑ ^ (-(2 * q))) ≠ ⊤ := by
    have h1 : (∫⁻ ζ in {ζ : ℂ | r < ‖ζ - z‖}, ‖ζ - z‖ₑ ^ (-(2 * q))) ≤
        (∫⁻ ζ in ({ζ : ℂ | r < ‖ζ - z‖} ∩ closedBall z ρ), ‖ζ - z‖ₑ ^ (-(2 * q))) +
          ∫⁻ ζ in {ζ : ℂ | ρ < ‖ζ - z‖}, ‖ζ - z‖ₑ ^ (-(2 * q)) :=
      (lintegral_mono_set hcover).trans (lintegral_union_le _ _ _)
    exact (h1.trans_lt (ENNReal.add_lt_top.2 ⟨hnear.lt_top, hfar.lt_top⟩)).ne
  obtain ⟨A, hA⟩ : ∃ A : ℝ≥0∞, A = (∫⁻ ζ in {ζ : ℂ | r < ‖ζ - z‖}, ‖ζ - z‖ₑ ^ (-(2 * q))) ^ (1 / q) :=
    ⟨_, rfl⟩
  have hAne : A ≠ ⊤ := by
    rw [hA]; exact ENNReal.rpow_ne_top_of_nonneg (div_nonneg zero_le_one hq0.le) hCfin
  have hkey : (∫⁻ ζ in {ζ : ℂ | r < ‖ζ - z‖}, ‖ω ζ / (ζ - z) ^ 2‖ₑ) ≤
      eLpNorm ω (ENNReal.ofReal p) * A := by
    refine (lintegral_mono_ae (Eventually.of_forall hsub)).trans ?_
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict {ζ : ℂ | r < ‖ζ - z‖}) hpq
      (f := fun ζ => ‖ω ζ‖ₑ) (g := fun ζ : ℂ => ‖ζ - z‖ₑ⁻¹ ^ 2)
      hω.aestronglyMeasurable.aemeasurable.enorm.restrict
      ((measurable_id.sub_const z).enorm.inv.pow_const 2).aemeasurable
    simp only [Pi.mul_apply] at h
    refine h.trans (mul_le_mul' ?_ ?_)
    · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp0).ne'
        ENNReal.ofReal_ne_top hω.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
      exact ENNReal.rpow_le_rpow (lintegral_mono' Measure.restrict_le_self le_rfl)
        (div_nonneg zero_le_one hp0.le)
    · have hg : ∀ ζ : ℂ, (‖ζ - z‖ₑ⁻¹ ^ 2) ^ q = ‖ζ - z‖ₑ ^ (-(2 * q)) := fun ζ => by
        rw [← ENNReal.rpow_natCast ‖ζ - z‖ₑ⁻¹ 2, ← ENNReal.rpow_mul, ENNReal.inv_rpow,
          ← ENNReal.rpow_neg]
        norm_num
      simp only [hg]
      rw [hA]
  have hfin : (∫⁻ ζ in {ζ : ℂ | r < ‖ζ - z‖}, ‖ω ζ / (ζ - z) ^ 2‖ₑ) ≠ ⊤ :=
    (hkey.trans_lt (ENNReal.mul_lt_top hω.eLpNorm_lt_top hAne.lt_top)).ne
  exact hfin.lt_top

/-- The mollification of `ω` by `lemma92Bump n` (§9's Lemma 9.2 (⇒) mollifier family), reused
directly since `ω` is already compactly supported (no exhaustion indicator needed). -/
noncomputable def t5Mollify (ω : ℂ → ℂ) (n : ℕ) : ℂ → ℂ :=
  convolution ((lemma92Bump n).normed volume) ω (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- The mollification is `C^∞`. -/
theorem t5Mollify_contDiff {p : ℝ} (hp : 1 ≤ p) {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p))
    (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (t5Mollify ω n) := by
  have hp1e : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  exact (lemma92Bump n).hasCompactSupport_normed.contDiff_convolution_left _
    (lemma92Bump n).contDiff_normed (hω.locallyIntegrable hp1e)

/-- The mollification of a compactly-supported function has compact support. -/
theorem t5Mollify_hasCompactSupport {ω : ℂ → ℂ} (hsupp : Bornology.IsBounded (Function.support ω))
    (n : ℕ) : HasCompactSupport (t5Mollify ω n) :=
  (lemma92Bump n).hasCompactSupport_normed.convolution _ hsupp.isCompact_closure

/-- The mollifications all have support in one fixed disc, since `lemma92Bump n`'s radius is
`≤ 1` for every `n`. -/
theorem t5Mollify_support_subset {ω : ℂ → ℂ} {R : ℝ} (hsupp : ∀ z, R < ‖z‖ → ω z = 0) (n : ℕ) :
    Function.support (t5Mollify ω n) ⊆ closedBall (0 : ℂ) (R + 1) := by
  have h1 : Function.support ω ⊆ closedBall (0 : ℂ) R := fun z hz => by
    by_contra h
    exact hz (hsupp z (by simpa [mem_closedBall_zero_iff, not_le] using h))
  have h2 : Function.support ((lemma92Bump n).normed volume) ⊆
      closedBall (0 : ℂ) (lemma92Bump n).rOut := by
    rw [(lemma92Bump n).support_normed_eq]
    exact ball_subset_closedBall
  have h3 := support_convolution_subset (f := (lemma92Bump n).normed volume) (g := ω)
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
  refine h3.trans ?_
  rintro x ⟨a, ha, b, hb, hab⟩
  have ha' : ‖a‖ ≤ (lemma92Bump n).rOut := mem_closedBall_zero_iff.mp (h2 ha)
  have hb' : ‖b‖ ≤ R := mem_closedBall_zero_iff.mp (h1 hb)
  have hrOut : (lemma92Bump n).rOut ≤ 1 := by
    have heq : (lemma92Bump n).rOut = 1 / ((n : ℝ) + 1) := rfl
    have h2 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]
    rw [heq]
    calc (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / 1 := one_div_le_one_div_of_le one_pos h2
      _ = 1 := by norm_num
  rw [mem_closedBall_zero_iff, ← hab]
  calc ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
    _ ≤ 1 + R := by linarith
    _ = R + 1 := by ring

/-- The mollification of an `L_p` function is `L_p`, by Young's inequality. -/
theorem t5Mollify_memLp {p : ℝ} (hp : 1 ≤ p) (hp' : ENNReal.ofReal p ≠ ⊤) {ω : ℂ → ℂ}
    (hω : MemLp ω (ENNReal.ofReal p)) (n : ℕ) : MemLp (t5Mollify ω n) (ENNReal.ofReal p) := by
  have hp1e : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hcont : Continuous (t5Mollify ω n) :=
    (lemma92Bump n).hasCompactSupport_normed.continuous_convolution_left _
      (lemma92Bump n).continuous_normed (hω.locallyIntegrable hp1e)
  refine memLp_iff.mpr ?_
  calc eLpNorm (t5Mollify ω n) (ENNReal.ofReal p) volume
      ≤ eLpNorm ω (ENNReal.ofReal p) volume :=
        eLpNorm_convolution_le_of_lintegral_eq_one (lemma92Bump n).continuous_normed.measurable
          (fun x => (lemma92Bump n).nonneg_normed x)
          (by rw [← ofReal_integral_eq_lintegral_ofReal (lemma92Bump n).integrable_normed
              (Eventually.of_forall fun x => (lemma92Bump n).nonneg_normed x),
              (lemma92Bump n).integral_normed, ENNReal.ofReal_one])
          hω.aestronglyMeasurable hp1e hp'
    _ < ⊤ := hω.eLpNorm_lt_top

/-- The mollification converges to `ω` in `L_p` (globally, not just on compacts): both
`t5Mollify ω n` and `ω` vanish outside a fixed disc, so the global norm equals the restricted
one, which converges by `tendsto_eLpNorm_convolution_normed_sub` (§9's Lemma 9.2 (⇒) machinery). -/
theorem t5Mollify_tendsto {p : ℝ} (hp1 : 1 ≤ p) (hp' : ENNReal.ofReal p ≠ ⊤) {ω : ℂ → ℂ} {R : ℝ}
    (_hR : 0 < R) (hω : MemLp ω (ENNReal.ofReal p)) (hsupp : ∀ z, R < ‖z‖ → ω z = 0) :
    Tendsto (fun n => eLpNorm (fun z => t5Mollify ω n z - ω z) (ENNReal.ofReal p) volume)
      atTop (𝓝 0) := by
  have hb : Tendsto (fun n => (lemma92Bump n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hp1e : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1
  have hC : volume (closedBall (0 : ℂ) (R + 1)) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hrestrict := tendsto_eLpNorm_convolution_normed_sub hb hp1e hp' hω hC
  have hSm : MeasurableSet (closedBall (0 : ℂ) (R + 1)) := measurableSet_closedBall
  have heq : ∀ n, (fun z => t5Mollify ω n z - ω z) =
      (closedBall (0 : ℂ) (R + 1)).indicator (fun z => t5Mollify ω n z - ω z) := by
    intro n
    have hsuppn := t5Mollify_support_subset hsupp n
    have hsuppω0 : Function.support ω ⊆ closedBall (0 : ℂ) R := fun z hz => by
      by_contra h
      exact hz (hsupp z (by simpa [mem_closedBall_zero_iff, not_le] using h))
    have hsuppω : Function.support ω ⊆ closedBall (0 : ℂ) (R + 1) :=
      hsuppω0.trans (closedBall_subset_closedBall (by linarith))
    funext z
    by_cases hz : z ∈ closedBall (0 : ℂ) (R + 1)
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      have h1 : t5Mollify ω n z = 0 := by
        by_contra hne
        exact hz (hsuppn hne)
      have h2 : ω z = 0 := by
        by_contra hne
        exact hz (hsuppω hne)
      rw [h1, h2, sub_zero]
  have hgoal : (fun n => eLpNorm (fun z => t5Mollify ω n z - ω z) (ENNReal.ofReal p) volume) =
      (fun n => eLpNorm (fun z => t5Mollify ω n z - ω z) (ENNReal.ofReal p)
        (volume.restrict (closedBall (0 : ℂ) (R + 1)))) := by
    funext n
    conv_lhs => rw [heq n]
    exact eLpNorm_indicator_eq_eLpNorm_restrict hSm.nullMeasurableSet
  rw [hgoal]
  exact hrestrict



/-- I1: for `ω ∈ C₀^∞`, `H(ω) = T(∂_z ω)`, hence `C¹` with `∂_z̄(Hω) = ∂_z ω`. -/
theorem i1_hilbertH_eq_cauchyT_dz {ω : ℂ → ℂ} (hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω)
    (hc : HasCompactSupport ω) :
    hilbertHSmooth ω = cauchyT (dz ω) ∧ ContDiff ℝ 1 (hilbertHSmooth ω) ∧
      ∀ z, dzbar (hilbertHSmooth ω) z = dz ω z := by
  have hω1 : ContDiff ℝ 1 ω := hω.of_le (by simp)
  have hdzω_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dz ω) := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ ω z 1) :=
      (hω.fderiv_right (le_refl _)).clm_apply contDiff_const
    have hI : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ ω z I) :=
      (hω.fderiv_right (le_refl _)).clm_apply contDiff_const
    exact (h1.sub (contDiff_const.mul hI)).div_const 2
  have hdzω_compact : HasCompactSupport (dz ω) := by
    have h1 : HasCompactSupport (fun z => fderiv ℝ ω z (1 : ℂ)) := hasCompactSupport_fderiv_apply hc 1
    have hI : HasCompactSupport (fun z => fderiv ℝ ω z (I : ℂ)) := hasCompactSupport_fderiv_apply hc I
    have hsub : HasCompactSupport (fun z => fderiv ℝ ω z 1 - I * fderiv ℝ ω z I) :=
      h1.sub hI.mul_left
    have heq : dz ω = fun z => (2 : ℂ)⁻¹ * (fderiv ℝ ω z 1 - I * fderiv ℝ ω z I) := by
      funext z; rw [dz]; ring
    rw [heq]
    exact hsub.mul_left
  have hHeq : ∀ z, hilbertHSmooth ω z = cauchyT (dz ω) z := fun z => by
    have h1 := ((eq11_17 hω hc).2 z).2
    have h2 := dz_cauchyT hω1 hc z
    rw [← h1, h2]
  refine ⟨funext hHeq, ?_, ?_⟩
  · have := (eq11_17 hdzω_smooth hdzω_compact).1
    exact (funext hHeq) ▸ this
  · intro z
    have h1 := ((eq11_17 hdzω_smooth hdzω_compact).2 z).1
    have h2 := hHeq z
    rw [show dzbar (hilbertHSmooth ω) z = dzbar (cauchyT (dz ω)) z from by rw [funext hHeq]]
    exact h1

/-- I2: for `ω ∈ C₀^∞`, `‖T(ω)(z)‖ = O(1/|z|)` as `z → ∞`, via `eq11_8`. -/
theorem i2_decay {ω : ℂ → ℂ} (hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω)
    (hc : HasCompactSupport ω) : ∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ → ‖cauchyT ω z‖ ≤ C / ‖z‖ := by
  have hbdd : Bornology.IsBounded (tsupport ω) := hc.isCompact.isBounded
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hω.continuous
  haveI : IsFiniteMeasure (volume.restrict (tsupport ω)) :=
    isFiniteMeasure_restrict.2 hc.isCompact.measure_lt_top.ne
  have hωMemLp : MemLp ω (ENNReal.ofReal 3) (volume.restrict (tsupport ω)) :=
    MemLp.of_bound hω.continuous.aestronglyMeasurable.restrict M (Eventually.of_forall hM)
  obtain ⟨-, C, R, hCR⟩ := eq11_8 hbdd (by norm_num : (2 : ℝ) < 3) hωMemLp
  refine ⟨C, R, fun z hz => ?_⟩
  have heq : cauchyTOn (tsupport ω) ω z = cauchyT ω z := by
    unfold cauchyTOn cauchyT
    congr 1
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun ζ hζ => ?_)
    have hζ0 : ω ζ = 0 := image_eq_zero_of_notMem_tsupport hζ
    rw [hζ0, zero_div]
  rw [← heq]
  exact hCR z hz

theorem differentiableAt_conj {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun w => conj (f w)) z :=
  (Complex.conjCLE.differentiable.differentiableAt).comp z hf

theorem fderiv_conj_apply {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (v : ℂ) :
    fderiv ℝ (fun w => conj (f w)) z v = conj (fderiv ℝ f z v) := by
  have h1 : HasFDerivAt (fun w => conj (f w))
      ((Complex.conjLIE.toContinuousLinearEquiv.toContinuousLinearMap).comp (fderiv ℝ f z)) z :=
    (Complex.conjLIE.toContinuousLinearEquiv.hasFDerivAt).comp z hf.hasFDerivAt
  rw [h1.fderiv]
  simp

theorem dz_conj {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    dz (fun w => conj (f w)) z = conj (dzbar f z) := by
  unfold dz dzbar
  rw [fderiv_conj_apply hf, fderiv_conj_apply hf]
  simp only [map_div₀, map_add, map_mul, Complex.conj_I, map_ofNat]
  ring

theorem dzbar_conj {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    dzbar (fun w => conj (f w)) z = conj (dz f z) := by
  unfold dz dzbar
  rw [fderiv_conj_apply hf, fderiv_conj_apply hf]
  simp only [map_div₀, map_sub, map_mul, Complex.conj_I, map_ofNat]
  ring

/-- I3+I4 core: for `ω ∈ C₀^∞` and `R` large enough that `ω` (hence `dz ω`) vanishes outside
`closedBall 0 R`, the double-Green identity holds at that `R`, with an explicit boundary term. -/
theorem i3_greenR {ω : ℂ → ℂ} (hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω)
    (hc : HasCompactSupport ω) {R : ℝ} (hR : 0 < R)
    (hsupp : tsupport ω ⊆ ball (0 : ℂ) R) :
    (∫ z in ball (0 : ℂ) R, hilbertHSmooth ω z * conj (hilbertHSmooth ω z)) -
      (∫ z in ball (0 : ℂ) R, ω z * conj (ω z)) =
    -(1 / (2 * I)) *
      ∫ θ in (0 : ℝ)..2 * π, (cauchyT ω (circleMap 0 R θ) * conj (hilbertHSmooth ω (circleMap 0 R θ))) *
        conj (deriv (circleMap 0 R) θ) := by
  have hω1 : ContDiff ℝ 1 ω := hω.of_le (by simp)
  obtain ⟨heq, hHC1, hHdzbar⟩ := i1_hilbertH_eq_cauchyT_dz hω hc
  have hTωC1 : ContDiff ℝ 1 (cauchyT ω) := contDiff_cauchyT hω1 hc
  have hTωdiff : ∀ z, DifferentiableAt ℝ (cauchyT ω) z := fun z =>
    hTωC1.differentiable one_ne_zero z
  have hHωdiff : ∀ z, DifferentiableAt ℝ (hilbertHSmooth ω) z := fun z =>
    hHC1.differentiable one_ne_zero z
  have hωdiff : ∀ z, DifferentiableAt ℝ ω z := fun z => hω1.differentiable one_ne_zero z
  -- Green application 1: on `f = Tω · conj(Hω)`
  have hf : ContDiffOn ℝ 1 (fun z => cauchyT ω z * conj (hilbertHSmooth ω z)) (closedBall (0 : ℂ) R) :=
    (hTωC1.mul (Complex.conjCLE.contDiff.comp hHC1)).contDiffOn
  have hG1 := eq11_10_green_dzbar hR hf
  have hdzf : ∀ z, dz (fun z => cauchyT ω z * conj (hilbertHSmooth ω z)) z =
      cauchyT ω z * dzbar (fun w => conj (ω w)) z + hilbertHSmooth ω z * conj (hilbertHSmooth ω z) := by
    intro z
    rw [dz_mul (hTωdiff z) (differentiableAt_conj (hHωdiff z))]
    have h1 : dz (fun w => conj (hilbertHSmooth ω w)) z = conj (dzbar (hilbertHSmooth ω) z) := dz_conj (hHωdiff z)
    rw [h1, hHdzbar z]
    have h2 : conj (dz ω z) = dzbar (fun w => conj (ω w)) z := (dzbar_conj (hωdiff z)).symm
    rw [← h2]
    have h3 : dz (cauchyT ω) z = hilbertHSmooth ω z := ((eq11_17 hω hc).2 z).2
    rw [h3]
    ring
  -- integrability of the pieces, on `ball 0 R`
  have hcont1 : Continuous (fun z => cauchyT ω z * dzbar (fun w => conj (ω w)) z) := by
    have hcω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => conj (ω w)) :=
      Complex.conjCLE.contDiff.comp hω
    have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ (fun w => conj (ω w)) z) :=
      hcω.fderiv_right (le_refl _)
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z => fderiv ℝ (fun w => conj (ω w)) z 1) := hfd.clm_apply contDiff_const
    have hI : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z => fderiv ℝ (fun w => conj (ω w)) z I) := hfd.clm_apply contDiff_const
    have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dzbar (fun w => conj (ω w))) :=
      (h1.add (contDiff_const.mul hI)).div_const 2
    exact hTωC1.continuous.mul hsmooth.continuous
  have hcont2 : Continuous (fun z => hilbertHSmooth ω z * conj (hilbertHSmooth ω z)) :=
    hHC1.continuous.mul (Complex.conjCLE.continuous.comp hHC1.continuous)
  have hcont3 : Continuous (fun z => ω z * conj (ω z)) :=
    hω1.continuous.mul (Complex.conjCLE.continuous.comp hω1.continuous)
  have hint1 : IntegrableOn (fun z => cauchyT ω z * dzbar (fun w => conj (ω w)) z)
      (ball (0 : ℂ) R) := (hcont1.continuousOn.integrableOn_compact
    (isCompact_closedBall 0 R)).mono_set ball_subset_closedBall
  have hint2 : IntegrableOn (fun z => hilbertHSmooth ω z * conj (hilbertHSmooth ω z)) (ball (0 : ℂ) R) :=
    (hcont2.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set
      ball_subset_closedBall
  have hint3 : IntegrableOn (fun z => ω z * conj (ω z)) (ball (0 : ℂ) R) :=
    (hcont3.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set
      ball_subset_closedBall
  -- Green application 1
  have hG1' : (∫ θ in (0:ℝ)..2*π, (cauchyT ω (circleMap 0 R θ) * conj (hilbertHSmooth ω (circleMap 0 R θ))) *
      conj (deriv (circleMap 0 R) θ)) =
      -2*I*((∫ z in ball (0:ℂ) R, cauchyT ω z * dzbar (fun w => conj (ω w)) z) +
        ∫ z in ball (0:ℂ) R, hilbertHSmooth ω z * conj (hilbertHSmooth ω z)) := by
    rw [hG1]
    congr 1
    rw [← integral_add hint1 hint2]
    exact setIntegral_congr_fun measurableSet_ball (fun z _ => hdzf z)
  -- Green application 2 on `g = Tω · conj(ω)`
  have hg : ContDiffOn ℝ 1 (fun z => cauchyT ω z * conj (ω z)) (closedBall (0 : ℂ) R) :=
    (hTωC1.mul (Complex.conjCLE.contDiff.comp hω1)).contDiffOn
  have hG2 := eq11_9_green_dz hR hg
  have hdzbarg : ∀ z, dzbar (fun z => cauchyT ω z * conj (ω z)) z =
      cauchyT ω z * dzbar (fun w => conj (ω w)) z + ω z * conj (ω z) := by
    intro z
    rw [dzbar_mul (hTωdiff z) (differentiableAt_conj (hωdiff z))]
    have h1 : dzbar (cauchyT ω) z = ω z := ((eq11_17 hω hc).2 z).1
    rw [h1]
    ring
  have hcirc0 : (∮ z in C(0, R), (fun z => cauchyT ω z * conj (ω z)) z) = 0 := by
    rw [circleIntegral]
    have hz0 : ∀ θ, cauchyT ω (circleMap 0 R θ) * conj (ω (circleMap 0 R θ)) = 0 := by
      intro θ
      have hout : circleMap 0 R θ ∉ tsupport ω := fun hmem => by
        have hin := hsupp hmem
        simp [mem_ball, norm_circleMap_zero, abs_of_pos hR] at hin
      rw [image_eq_zero_of_notMem_tsupport hout]
      simp
    simp only [hz0, smul_zero]
    exact intervalIntegral.integral_zero
  have hG2' : (0 : ℂ) = 2*I*((∫ z in ball (0:ℂ) R, cauchyT ω z * dzbar (fun w => conj (ω w)) z) +
      ∫ z in ball (0:ℂ) R, ω z * conj (ω z)) := by
    conv_lhs => rw [← hcirc0]
    rw [hG2]
    congr 1
    rw [← integral_add hint1 hint3]
    exact setIntegral_congr_fun measurableSet_ball (fun z _ => hdzbarg z)
  have h2I : (2 * I : ℂ) ≠ 0 := by simp
  have hkey : ((∫ z in ball (0:ℂ) R, hilbertHSmooth ω z * conj (hilbertHSmooth ω z)) -
      ∫ z in ball (0:ℂ) R, ω z * conj (ω z)) * (2 * I) =
      -(∫ θ in (0:ℝ)..2*π, (cauchyT ω (circleMap 0 R θ) * conj (hilbertHSmooth ω (circleMap 0 R θ))) *
        conj (deriv (circleMap 0 R) θ)) := by
    linear_combination hG1' + hG2'
  rw [show (-(1 / (2 * I) : ℂ) *
      ∫ θ in (0:ℝ)..2*π, (cauchyT ω (circleMap 0 R θ) * conj (hilbertHSmooth ω (circleMap 0 R θ))) *
        conj (deriv (circleMap 0 R) θ)) =
      -(∫ θ in (0:ℝ)..2*π, (cauchyT ω (circleMap 0 R θ) * conj (hilbertHSmooth ω (circleMap 0 R θ))) *
        conj (deriv (circleMap 0 R) θ)) / (2 * I) from by ring, eq_div_iff h2I]
  exact hkey

/-- Helper (reusable): `dz ω` is smooth when `ω` is, via the fderiv-in-direction pattern used
in `i1_hilbertH_eq_cauchyT_dz`. -/
theorem dz_contDiff_of_smooth {ω : ℂ → ℂ} (hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dz ω) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ ω z 1) :=
    (hω.fderiv_right (le_refl _)).clm_apply contDiff_const
  have hI : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ ω z I) :=
    (hω.fderiv_right (le_refl _)).clm_apply contDiff_const
  exact (h1.sub (contDiff_const.mul hI)).div_const 2

/-- Helper (reusable): `dz ω` has compact support when `ω` does. -/
theorem dz_hasCompactSupport_of_compactSupport {ω : ℂ → ℂ} (hc : HasCompactSupport ω) :
    HasCompactSupport (dz ω) := by
  have h1 : HasCompactSupport (fun z => fderiv ℝ ω z (1 : ℂ)) := hasCompactSupport_fderiv_apply hc 1
  have hI : HasCompactSupport (fun z => fderiv ℝ ω z (I : ℂ)) := hasCompactSupport_fderiv_apply hc I
  have hsub : HasCompactSupport (fun z => fderiv ℝ ω z 1 - I * fderiv ℝ ω z I) :=
    h1.sub hI.mul_left
  have heq : dz ω = fun z => (2 : ℂ)⁻¹ * (fderiv ℝ ω z 1 - I * fderiv ℝ ω z I) := by
    funext z; rw [dz]; ring
  rw [heq]
  exact hsub.mul_left

/-- I4a: `hilbertHSmooth ω` also decays like `O(1/|z|)`, since `hilbertHSmooth ω = cauchyT (dz ω)` (I1) and
`dz ω ∈ C₀^∞`, so I2 applies to `dz ω`. -/
theorem i4_hilbertH_decay {ω : ℂ → ℂ} (hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω)
    (hc : HasCompactSupport ω) :
    ∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ → ‖hilbertHSmooth ω z‖ ≤ C / ‖z‖ := by
  have h1 := (i1_hilbertH_eq_cauchyT_dz hω hc).1
  obtain ⟨C, R, hCR⟩ :=
    i2_decay (dz_contDiff_of_smooth hω) (dz_hasCompactSupport_of_compactSupport hc)
  refine ⟨C, R, fun z hz => ?_⟩
  rw [h1]
  exact hCR z hz

/-- I4b: the boundary/circle term in `i3_greenR`'s identity tends to `0` as `R → ∞`, using the
`O(1/R)` decay of both `cauchyT ω` (I2) and `hilbertHSmooth ω` (I4a) against the `O(R)` circumference
factor `‖deriv (circleMap 0 R) θ‖ = R`. -/
theorem i4_boundary_tendsto_zero {ω : ℂ → ℂ} (hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω)
    (hc : HasCompactSupport ω) :
    Tendsto (fun R : ℝ =>
        ∫ θ in (0 : ℝ)..2 * π, (cauchyT ω (circleMap 0 R θ) * conj (hilbertHSmooth ω (circleMap 0 R θ))) *
          conj (deriv (circleMap 0 R) θ))
      atTop (𝓝 0) := by
  obtain ⟨C₁, R₁, hC₁⟩ := i2_decay hω hc
  obtain ⟨C₂, R₂, hC₂⟩ := i4_hilbertH_decay hω hc
  have hbound : ∀ R : ℝ, max R₁ (max R₂ 0) < R →
      ‖∫ θ in (0 : ℝ)..2 * π, (cauchyT ω (circleMap 0 R θ) * conj (hilbertHSmooth ω (circleMap 0 R θ))) *
          conj (deriv (circleMap 0 R) θ)‖ ≤ 2 * π * (C₁ * C₂) / R := by
    intro R hR
    have hR0 : 0 < R := lt_of_le_of_lt ((le_max_right R₂ 0).trans (le_max_right R₁ _)) hR
    have hR1 : R₁ < R := lt_of_le_of_lt (le_max_left _ _) hR
    have hR2 : R₂ < R := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hR
    have hnorm : ∀ θ : ℝ, ‖circleMap (0 : ℂ) R θ‖ = R := fun θ => by
      rw [norm_circleMap_zero]; exact abs_of_pos hR0
    have hptbound : ∀ θ : ℝ,
        ‖(cauchyT ω (circleMap 0 R θ) * conj (hilbertHSmooth ω (circleMap 0 R θ))) *
          conj (deriv (circleMap 0 R) θ)‖ ≤ C₁ * C₂ / R := by
      intro θ
      rw [norm_mul, norm_mul, norm_conj, norm_conj, deriv_circleMap, norm_mul, norm_I, mul_one,
        hnorm θ]
      have h1 : ‖cauchyT ω (circleMap 0 R θ)‖ ≤ C₁ / R := by
        have := hC₁ (circleMap 0 R θ) (by rw [hnorm θ]; exact hR1)
        rwa [hnorm θ] at this
      have h2 : ‖hilbertHSmooth ω (circleMap 0 R θ)‖ ≤ C₂ / R := by
        have := hC₂ (circleMap 0 R θ) (by rw [hnorm θ]; exact hR2)
        rwa [hnorm θ] at this
      have hnn2 : (0:ℝ) ≤ C₁ / R := (norm_nonneg _).trans h1
      calc ‖cauchyT ω (circleMap 0 R θ)‖ * ‖hilbertHSmooth ω (circleMap 0 R θ)‖ * R
          ≤ (C₁ / R) * (C₂ / R) * R :=
            mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) hnn2) hR0.le
        _ = C₁ * C₂ / R := by field_simp
    calc ‖∫ θ in (0 : ℝ)..2 * π,
          (cauchyT ω (circleMap 0 R θ) * conj (hilbertHSmooth ω (circleMap 0 R θ))) *
            conj (deriv (circleMap 0 R) θ)‖
        ≤ (C₁ * C₂ / R) * |2 * π - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (fun θ _ => hptbound θ)
      _ = 2 * π * (C₁ * C₂) / R := by
            rw [sub_zero, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]; ring
  have htendsto0 : Tendsto (fun R : ℝ => 2 * π * (C₁ * C₂) / R) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (α := ℝ) (x := 2 * π * (C₁ * C₂))).div_atTop tendsto_id
  refine squeeze_zero_norm' ?_ htendsto0
  filter_upwards [eventually_gt_atTop (max R₁ (max R₂ 0))] with R hR using hbound R hR

/-- Helper: `f z * conj (f z)` as a complex integral equals the `ofReal`-cast of the real
integral of `‖f z‖ ^ 2`, for any set `s` (no measurability/integrability side condition needed,
since `integral_ofReal` is unconditional). -/
theorem integral_mul_conj_eq_ofReal (f : ℂ → ℂ) (s : Set ℂ) :
    ∫ z in s, f z * conj (f z) = ((∫ z in s, ‖f z‖ ^ 2 : ℝ) : ℂ) := by
  have hfun : (fun z => f z * conj (f z)) = fun z => ((‖f z‖ ^ 2 : ℝ) : ℂ) := by
    funext z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hfun]
  exact integral_complex_ofReal

/-- I4: for `ω ∈ C₀^∞`, `‖hilbertHSmooth ω‖₂² = ‖ω‖₂²` as full-plane real integrals of `‖·‖²` — the
`R → ∞` limit of `i3_greenR`'s identity, using `i4_boundary_tendsto_zero` to kill the boundary
term and the fact that `∫ z in ball 0 R, ‖ω z‖²` is eventually constant (since `ω` has compact
support). -/
theorem i4_normSq_eq {ω : ℂ → ℂ} (hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω)
    (hc : HasCompactSupport ω) :
    Integrable (fun z => ‖hilbertHSmooth ω z‖ ^ 2) volume ∧
      ∫ z, ‖hilbertHSmooth ω z‖ ^ 2 = ∫ z, ‖ω z‖ ^ 2 := by
  obtain ⟨R₀, hR₀pos, hR₀sub⟩ := hc.isCompact.isBounded.subset_ball_lt 0 (0 : ℂ)
  set B : ℝ := ∫ z in ball (0 : ℂ) R₀, ‖ω z‖ ^ 2 with hBdef
  have hzero : ∀ z, z ∉ ball (0 : ℂ) R₀ → ‖ω z‖ ^ 2 = 0 := fun z hz => by
    rw [image_eq_zero_of_notMem_tsupport (fun hmem => hz (hR₀sub hmem))]; simp
  have hωfull : (∫ z, ‖ω z‖ ^ 2) = B :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  have hballconst : ∀ R : ℝ, R₀ ≤ R → (∫ z in ball (0 : ℂ) R, ‖ω z‖ ^ 2) = B := by
    intro R hR
    rw [hBdef, ← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]
    congr 1
    funext z
    by_cases hz0 : z ∈ ball (0 : ℂ) R₀
    · rw [Set.indicator_of_mem hz0, Set.indicator_of_mem (ball_subset_ball hR hz0)]
    · rw [Set.indicator_of_notMem hz0]
      by_cases hz : z ∈ ball (0 : ℂ) R
      · rw [Set.indicator_of_mem hz, hzero z hz0]
      · rw [Set.indicator_of_notMem hz]
  have hpartialC : Tendsto (fun R : ℝ => ((∫ z in ball (0 : ℂ) R, ‖hilbertHSmooth ω z‖ ^ 2 : ℝ) : ℂ))
      atTop (𝓝 (B : ℂ)) := by
    have heq : ∀ᶠ R : ℝ in atTop,
        ((∫ z in ball (0 : ℂ) R, ‖hilbertHSmooth ω z‖ ^ 2 : ℝ) : ℂ) =
          (B : ℂ) + (-(1 / (2 * I)) *
            ∫ θ in (0 : ℝ)..2 * π, (cauchyT ω (circleMap 0 R θ) *
              conj (hilbertHSmooth ω (circleMap 0 R θ))) * conj (deriv (circleMap 0 R) θ)) := by
      filter_upwards [eventually_gt_atTop R₀] with R hR
      have hsupp : tsupport ω ⊆ ball (0 : ℂ) R := hR₀sub.trans (ball_subset_ball hR.le)
      have hgreen := i3_greenR hω hc (lt_trans hR₀pos hR) hsupp
      rw [integral_mul_conj_eq_ofReal (hilbertHSmooth ω) (ball (0 : ℂ) R),
        integral_mul_conj_eq_ofReal ω (ball (0 : ℂ) R), hballconst R hR.le] at hgreen
      linear_combination hgreen
    rw [tendsto_congr' heq]
    have hb0 : Tendsto (fun R : ℝ => -(1 / (2 * I)) *
        ∫ θ in (0 : ℝ)..2 * π, (cauchyT ω (circleMap 0 R θ) *
          conj (hilbertHSmooth ω (circleMap 0 R θ))) * conj (deriv (circleMap 0 R) θ))
        atTop (𝓝 (0 : ℂ)) := by
      have := (i4_boundary_tendsto_zero hω hc).const_mul (-(1 / (2 * I)) : ℂ)
      simpa using this
    have hsum := (tendsto_const_nhds (x := (B : ℂ))).add hb0
    simpa using hsum
  have hpartial : Tendsto (fun R : ℝ => ∫ z in ball (0 : ℂ) R, ‖hilbertHSmooth ω z‖ ^ 2) atTop (𝓝 B) := by
    have h := (Complex.continuous_re.tendsto (B : ℂ)).comp hpartialC
    simp only [Complex.ofReal_re] at h
    exact h
  have hHcont : Continuous (hilbertHSmooth ω) := (i1_hilbertH_eq_cauchyT_dz hω hc).2.1.continuous
  have hfi : ∀ R : ℝ, IntegrableOn (fun z => ‖hilbertHSmooth ω z‖ ^ 2) (ball (0 : ℂ) R) volume :=
    fun R => ((hHcont.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 R)).mono_set ball_subset_closedBall
  have hφ : AECover (volume : Measure ℂ) atTop (fun R : ℝ => ball (0 : ℂ) R) :=
    aecover_ball (x := (0 : ℂ)) (r := id) tendsto_id
  have hnng : 0 ≤ᵐ[volume] (fun z => ‖hilbertHSmooth ω z‖ ^ 2) := ae_of_all _ fun z => sq_nonneg _
  have hHint : Integrable (fun z => ‖hilbertHSmooth ω z‖ ^ 2) volume :=
    hφ.integrable_of_integral_tendsto_of_nonneg_ae B hfi hnng hpartial
  have hHfull : (∫ z, ‖hilbertHSmooth ω z‖ ^ 2) = B :=
    hφ.integral_eq_of_tendsto_of_nonneg_ae B hnng hfi hpartial
  exact ⟨hHint, by rw [hHfull, hωfull]⟩

/-- Helper: `eLpNorm _ 2 volume` depends only on `∫ ‖·‖²`, for square-integrable functions. -/
theorem eLpNorm_two_eq_of_integral_normSq_eq {f g : ℂ → ℂ}
    (hf : Integrable (fun z => ‖f z‖ ^ 2) volume) (hg : Integrable (fun z => ‖g z‖ ^ 2) volume)
    (heq : ∫ z, ‖f z‖ ^ 2 = ∫ z, ‖g z‖ ^ 2) (hfm : AEStronglyMeasurable f volume)
    (hgm : AEStronglyMeasurable g volume) :
    eLpNorm f 2 volume = eLpNorm g 2 volume := by
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hptop : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have htoReal : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hval : ∀ h : ℂ → ℂ, Integrable (fun z => ‖h z‖ ^ 2) volume →
      AEStronglyMeasurable h volume →
      eLpNorm h 2 volume = (ENNReal.ofReal (∫ z, ‖h z‖ ^ 2)) ^ (1 / (2 : ℝ)) := by
    intro h hh hhm
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hhm, htoReal]
    congr 1
    rw [ofReal_integral_eq_lintegral_ofReal hh (ae_of_all _ fun z => sq_nonneg _)]
    refine lintegral_congr fun z => ?_
    rw [← ofReal_norm (h z),
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (h z)) (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  rw [hval f hf hfm, hval g hg hgm, heq]

/-- I4, `eLpNorm` form: for `ω ∈ C₀^∞`, `‖H(ω)‖₂ = ‖ω‖₂`. This is `thm11_3_isometry`'s exact
conclusion, specialized to `ω ∈ C₀^∞` (I5/I6 extend it to general `ω ∈ L₂`). -/
theorem i4_eLpNorm_eq {ω : ℂ → ℂ} (hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω)
    (hc : HasCompactSupport ω) :
    eLpNorm (hilbertHSmooth ω) 2 volume = eLpNorm ω 2 volume := by
  obtain ⟨hHint, heq⟩ := i4_normSq_eq hω hc
  have hωInt : Integrable (fun z => ‖ω z‖ ^ 2) volume :=
    Continuous.integrable_of_hasCompactSupport (hω.continuous.norm.pow 2)
      (hc.comp_left (g := fun t : ℂ => ‖t‖ ^ 2) (by norm_num))
  exact eLpNorm_two_eq_of_integral_normSq_eq hHint hωInt heq
    (i1_hilbertH_eq_cauchyT_dz hω hc).2.1.continuous.aestronglyMeasurable
    hω.continuous.aestronglyMeasurable

/-- I5: `C₀^∞` is dense in `L²(ℂ)`. Combines Mathlib's compact-support truncation density
(`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`) with S11's `t5Mollify` smoothing convergence
(`t5Mollify_tendsto`, already installed for Theorem 11.1), via `exists_Lp_half`'s triangle
inequality. -/
theorem i5_dense {ω : ℂ → ℂ} (hω : MemLp ω 2 volume) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧
      eLpNorm (fun z => ω z - φ z) 2 volume ≤ ε := by
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  obtain ⟨η, hηpos, hη⟩ := exists_Lp_half ℂ (volume : Measure ℂ) (2 : ℝ≥0∞) hε
  obtain ⟨g, hg_supp, hg_close, hg_cont, hg_mem⟩ :=
    hω.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hηpos.ne'
  have hg_mem' : MemLp g (ENNReal.ofReal 2) volume := by rwa [h2]
  obtain ⟨R, hRpos, hRsub⟩ := hg_supp.isCompact.isBounded.subset_ball_lt 0 (0 : ℂ)
  have hgvanish : ∀ z : ℂ, R < ‖z‖ → g z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have := hRsub hmem; rw [mem_ball, dist_zero_right] at this; linarith
  have htendsto := t5Mollify_tendsto (by norm_num : (1:ℝ) ≤ 2) (p := 2) (by norm_num) hRpos hg_mem' hgvanish
  rw [h2] at htendsto
  have hηmem : ∀ᶠ n : ℕ in atTop,
      eLpNorm (fun z => t5Mollify g n z - g z) 2 volume ≤ η := by
    have := (tendsto_order.1 htendsto).2 η hηpos
    filter_upwards [this] with n hn using hn.le
  obtain ⟨n, hn⟩ := hηmem.exists
  set φ := t5Mollify g n with hφdef
  have hφ_cont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ := t5Mollify_contDiff (by norm_num : (1:ℝ) ≤ 2) hg_mem' n
  have hφ_supp : HasCompactSupport φ :=
    t5Mollify_hasCompactSupport (hg_supp.isCompact.isBounded.subset (subset_tsupport g)) n
  have hgφ : eLpNorm (fun z => g z - φ z) 2 volume ≤ η := by
    have heqn : (fun z => g z - φ z) = -(fun z => t5Mollify g n z - g z) := by
      funext z; simp [hφdef]
    rw [heqn, eLpNorm_neg]
    exact hn
  have hsum := hη (fun z => ω z - g z) (fun z => g z - φ z) hg_close hgφ
  have heqsum : (fun z => ω z - g z) + (fun z => g z - φ z) = fun z => ω z - φ z := by
    funext z; simp only [Pi.add_apply]; ring
  rw [heqsum] at hsum
  exact ⟨φ, hφ_cont, hφ_supp, hsum.le⟩

/-- General helper: if `f n → g` in `eLpNorm _ 2`-distance, then `eLpNorm (f n) 2 → eLpNorm g 2`
(triangle inequality both ways, squeezed; no finiteness hypothesis is needed since
`ENNReal.Tendsto.sub` only needs one side finite, and the limit `0 ≠ ⊤` always supplies that). -/
theorem tendsto_eLpNorm_of_tendsto_sub_zero {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hmeas : ∀ n, AEStronglyMeasurable (f n) volume) (hgmeas : AEStronglyMeasurable g volume)
    (h : Tendsto (fun n => eLpNorm (fun z => f n z - g z) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 volume) atTop (𝓝 (eLpNorm g 2 volume)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hub : ∀ n, eLpNorm (f n) 2 volume ≤
      eLpNorm g 2 volume + eLpNorm (fun z => f n z - g z) 2 volume := fun n => by
    calc eLpNorm (f n) 2 volume
        = eLpNorm (fun z => g z + (f n z - g z)) 2 volume := by congr 1; funext z; ring
      _ ≤ eLpNorm g 2 volume + eLpNorm (fun z => f n z - g z) 2 volume :=
        eLpNorm_add_le hp1
  have hlb : ∀ n, eLpNorm g 2 volume - eLpNorm (fun z => f n z - g z) 2 volume ≤
      eLpNorm (f n) 2 volume := fun n => by
    refine tsub_le_iff_right.mpr ?_
    calc eLpNorm g 2 volume = eLpNorm (fun z => f n z + -(f n z - g z)) 2 volume := by
          congr 1; funext z; ring
      _ ≤ eLpNorm (f n) 2 volume + eLpNorm (fun z => -(f n z - g z)) 2 volume :=
          eLpNorm_add_le hp1
      _ = eLpNorm (f n) 2 volume + eLpNorm (fun z => f n z - g z) 2 volume := by
          rw [show (fun z => -(f n z - g z)) = -(fun z => f n z - g z) from rfl, eLpNorm_neg]
  have hub' : Tendsto (fun n => eLpNorm g 2 volume + eLpNorm (fun z => f n z - g z) 2 volume)
      atTop (𝓝 (eLpNorm g 2 volume)) := by
    have := h.const_add (eLpNorm g 2 volume)
    simpa using this
  have hlb' : Tendsto (fun n => eLpNorm g 2 volume - eLpNorm (fun z => f n z - g z) 2 volume)
      atTop (𝓝 (eLpNorm g 2 volume)) := by
    have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := eLpNorm g 2 volume)) h
      (Or.inr (by norm_num))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlb' hub'
    (Eventually.of_forall hlb) (Eventually.of_forall hub)


-- NOTE (scratch-testing only): the live S11 still names the pointwise formula `hilbertHSmooth`, not
-- `hilbertHSmooth` — this whole file uses `hilbertHSmooth` below to test against the live file, and the
-- real patch simply renames `hilbertHSmooth` -> `hilbertHSmooth` at the def site, so these proofs carry
-- over unchanged.

def hilbertHTrunc (ω : ℂ → ℂ) (n : ℕ) : ℂ → ℂ :=
  (closedBall (0 : ℂ) (n : ℝ)).indicator ω

def hilbertHApprox (ω : ℂ → ℂ) (n : ℕ) : ℂ → ℂ :=
  t5Mollify (hilbertHTrunc ω n) n

theorem hilbertHTrunc_memLp {ω : ℂ → ℂ} {p : ℝ} (hω : MemLp ω (ENNReal.ofReal p))
    (n : ℕ) : MemLp (hilbertHTrunc ω n) (ENNReal.ofReal p) :=
  hω.indicator measurableSet_closedBall.nullMeasurableSet

theorem hilbertHTrunc_hasCompactSupport (ω : ℂ → ℂ) (n : ℕ) :
    Bornology.IsBounded (Function.support (hilbertHTrunc ω n)) := by
  apply Bornology.IsBounded.subset (isBounded_closedBall (x := (0:ℂ)) (r := (n:ℝ)))
  intro z hz
  by_contra hzn
  exact hz (Set.indicator_of_notMem hzn ω)

theorem hilbertHApprox_contDiff {ω : ℂ → ℂ} {p : ℝ} (hp : 1 ≤ p)
    (hω : MemLp ω (ENNReal.ofReal p)) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (hilbertHApprox ω n) :=
  t5Mollify_contDiff hp (hilbertHTrunc_memLp hω n) n

theorem hilbertHApprox_hasCompactSupport (ω : ℂ → ℂ) (n : ℕ) :
    HasCompactSupport (hilbertHApprox ω n) :=
  t5Mollify_hasCompactSupport (hilbertHTrunc_hasCompactSupport ω n) n

/-- `dz` is exactly linear (pointwise) on functions differentiable at `z`. -/
theorem dz_sub_pointwise {φ ψ : ℂ → ℂ} {z : ℂ} (hφ : DifferentiableAt ℝ φ z)
    (hψ : DifferentiableAt ℝ ψ z) : dz (fun w => φ w - ψ w) z = dz φ z - dz ψ z := by
  unfold dz
  have h : fderiv ℝ (fun w => φ w - ψ w) z = fderiv ℝ φ z - fderiv ℝ ψ z :=
    (hφ.hasFDerivAt.sub hψ.hasFDerivAt).fderiv
  rw [h]
  simp only [ContinuousLinearMap.sub_apply]
  ring

theorem dz_contDiff {φ : ℂ → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dz φ) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ φ z 1) :=
    (hφ.fderiv_right (le_refl _)).clm_apply contDiff_const
  have hI : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ φ z I) :=
    (hφ.fderiv_right (le_refl _)).clm_apply contDiff_const
  exact (h1.sub (contDiff_const.mul hI)).div_const 2

theorem dz_hasCompactSupport {φ : ℂ → ℂ} (hc : HasCompactSupport φ) :
    HasCompactSupport (dz φ) := by
  have h1 : HasCompactSupport (fun z => fderiv ℝ φ z (1 : ℂ)) := hasCompactSupport_fderiv_apply hc 1
  have hI : HasCompactSupport (fun z => fderiv ℝ φ z (I : ℂ)) := hasCompactSupport_fderiv_apply hc I
  have hsub : HasCompactSupport (fun z => fderiv ℝ φ z 1 - I * fderiv ℝ φ z I) :=
    h1.sub hI.mul_left
  have heq : dz φ = fun z => (2 : ℂ)⁻¹ * (fderiv ℝ φ z 1 - I * fderiv ℝ φ z I) := by
    funext z; rw [dz]; ring
  rw [heq]
  exact hsub.mul_left

/-- `hilbertHSmooth` is exactly (pointwise) subtractive on `C₀^∞`: via `hilbertHSmooth = cauchyT ∘ dz`
(the linchpin `i1_hilbertH_eq_cauchyT_dz`), `dz`'s pointwise linearity, and `cauchyT`'s linearity on
functions with shared bounded support (`cauchyT_sub`, which needs `p > 2` — trivially available since
`C₀^∞` functions lie in every `Lp`). -/
theorem hilbertHSmooth_sub {φ ψ : ℂ → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hcφ : HasCompactSupport φ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hcψ : HasCompactSupport ψ) :
    hilbertHSmooth (fun z => φ z - ψ z) = fun z => hilbertHSmooth φ z - hilbertHSmooth ψ z := by
  have hsub : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => φ z - ψ z) := hφ.sub hψ
  have hcsub : HasCompactSupport (fun z => φ z - ψ z) := hcφ.sub hcψ
  have h1 := i1_hilbertH_eq_cauchyT_dz hφ hcφ
  have h2 := i1_hilbertH_eq_cauchyT_dz hψ hcψ
  have h3 := i1_hilbertH_eq_cauchyT_dz hsub hcsub
  have hdzeq : dz (fun z => φ z - ψ z) = fun z => dz φ z - dz ψ z := by
    funext z
    exact dz_sub_pointwise (hφ.differentiable (by norm_num) z) (hψ.differentiable (by norm_num) z)
  have hdzφ_smooth := dz_contDiff hφ
  have hdzφ_compact := dz_hasCompactSupport hcφ
  have hdzψ_smooth := dz_contDiff hψ
  have hdzψ_compact := dz_hasCompactSupport hcψ
  obtain ⟨Rφ, hRφ⟩ := hdzφ_compact.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨Rψ, hRψ⟩ := hdzψ_compact.isBounded.subset_closedBall (0 : ℂ)
  set R := max (max Rφ Rψ) 1 with hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsφ : ∀ z, R < ‖z‖ → dz φ z = 0 := by
    intro z hz
    by_contra hne
    have hmem : z ∈ closedBall (0:ℂ) Rφ := hRφ (subset_tsupport _ hne)
    rw [mem_closedBall_zero_iff] at hmem
    have : ‖z‖ ≤ R := hmem.trans ((le_max_left Rφ Rψ).trans (le_max_left _ _))
    linarith
  have hsψ : ∀ z, R < ‖z‖ → dz ψ z = 0 := by
    intro z hz
    by_contra hne
    have hmem : z ∈ closedBall (0:ℂ) Rψ := hRψ (subset_tsupport _ hne)
    rw [mem_closedBall_zero_iff] at hmem
    have : ‖z‖ ≤ R := hmem.trans ((le_max_right Rφ Rψ).trans (le_max_left _ _))
    linarith
  have hMdzφ : MemLp (dz φ) (ENNReal.ofReal (3:ℝ)) :=
    hdzφ_smooth.continuous.memLp_of_hasCompactSupport hdzφ_compact
  have hMdzψ : MemLp (dz ψ) (ENNReal.ofReal (3:ℝ)) :=
    hdzψ_smooth.continuous.memLp_of_hasCompactSupport hdzψ_compact
  have hcT := cauchyT_sub (p := 3) (by norm_num) hRpos hMdzφ hMdzψ hsφ hsψ
  funext z
  rw [h3.1, h1.1, h2.1, hdzeq]
  exact congrFun hcT z

/-- The tail (outside a growing ball) of an `L_p` function's mass vanishes in `L_p` norm. -/
theorem eLpNorm_indicator_compl_closedBall_tendsto_zero {ω : ℂ → ℂ} {p : ℝ} (hp0 : 0 < p)
    (hω : MemLp ω (ENNReal.ofReal p)) :
    Tendsto (fun n : ℕ => eLpNorm ((closedBall (0:ℂ) (n:ℝ))ᶜ.indicator ω) (ENNReal.ofReal p))
      atTop (𝓝 0) := by
  have hp0e : (0:ℝ≥0∞) < ENNReal.ofReal p := ENNReal.ofReal_pos.2 hp0
  have hp'e : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp0ne : ENNReal.ofReal p ≠ 0 := hp0e.ne'
  have htop : ENNReal.toReal (ENNReal.ofReal p) = p := ENNReal.toReal_ofReal hp0.le
  have hlint : ∫⁻ z, ‖ω z‖ₑ ^ p ∂volume ≠ ⊤ := by
    have h2 := hω.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0ne hp'e hω.aestronglyMeasurable, htop] at h2
    intro hc
    rw [hc, ENNReal.top_rpow_of_pos (by positivity : (0:ℝ) < 1/p)] at h2
    exact absurd h2 (lt_irrefl ⊤)
  have hkey : Tendsto (fun n : ℕ => ∫⁻ z in (closedBall (0:ℂ) (n:ℝ))ᶜ, ‖ω z‖ₑ ^ p) atTop (𝓝 0) := by
    have hconv := tendsto_lintegral_of_dominated_convergence' (μ := volume)
      (F := fun (n : ℕ) (z : ℂ) => (closedBall (0:ℂ) (n:ℝ))ᶜ.indicator (fun w => ‖ω w‖ₑ ^ p) z)
      (f := fun _ => (0 : ℝ≥0∞)) (fun z => ‖ω z‖ₑ ^ p)
      (fun n => (hω.aestronglyMeasurable.enorm.pow_const p).indicator
        measurableSet_closedBall.compl)
      (fun n => Eventually.of_forall fun z => by
        dsimp only
        by_cases hz : z ∈ (closedBall (0:ℂ) (n:ℝ))ᶜ
        · rw [Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz]; exact bot_le)
      hlint
      (Eventually.of_forall fun z => by
        have hev : (fun _ : ℕ => (0 : ℝ≥0∞)) =ᶠ[atTop]
            (fun n : ℕ => (closedBall (0:ℂ) (n:ℝ))ᶜ.indicator (fun w => ‖ω w‖ₑ ^ p) z) := by
          filter_upwards [eventually_gt_atTop ⌈‖z‖⌉₊] with n hn
          symm
          refine Set.indicator_of_notMem ?_ _
          rw [mem_compl_iff, not_not, mem_closedBall_zero_iff]
          calc ‖z‖ ≤ (⌈‖z‖⌉₊ : ℝ) := Nat.le_ceil _
            _ ≤ (n:ℝ) := by exact_mod_cast hn.le
        exact Filter.Tendsto.congr' hev tendsto_const_nhds)
    simpa [lintegral_indicator, measurableSet_closedBall.compl] using hconv
  rw [ENNReal.tendsto_nhds_zero] at hkey ⊢
  intro ε hε
  filter_upwards [hkey (ε ^ p) (by positivity)] with n hn
  have heq : eLpNorm ((closedBall (0:ℂ) (n:ℝ))ᶜ.indicator ω) (ENNReal.ofReal p) =
      (∫⁻ z in (closedBall (0:ℂ) (n:ℝ))ᶜ, ‖ω z‖ₑ ^ p) ^ (1 / p) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall.compl.nullMeasurableSet,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0ne hp'e hω.aestronglyMeasurable.restrict, htop]
  rw [heq]
  calc (∫⁻ z in (closedBall (0:ℂ) (n:ℝ))ᶜ, ‖ω z‖ₑ ^ p) ^ (1 / p) ≤ (ε ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hn (by positivity)
    _ = ε := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

/-- `t5Mollify` is exactly (pointwise, funext) subtractive in its function argument, for `L_p`
functions. Reduces to `integral_sub` after restricting the convolution integral to `lemma92Bump n`'s
(bounded) support, where both `ω₁(x - ·)` and `ω₂(x - ·)` are integrable (`MemLp.locallyIntegrable`). -/
theorem t5Mollify_sub {ω₁ ω₂ : ℂ → ℂ} {p : ℝ} (hp : 1 ≤ p)
    (hω₁ : MemLp ω₁ (ENNReal.ofReal p)) (hω₂ : MemLp ω₂ (ENNReal.ofReal p)) (n : ℕ) :
    t5Mollify (fun z => ω₁ z - ω₂ z) n = fun z => t5Mollify ω₁ n z - t5Mollify ω₂ n z := by
  have hp1e : (1:ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hli1 := hω₁.locallyIntegrable hp1e
  have hli2 := hω₂.locallyIntegrable hp1e
  have hce1 := ((lemma92Bump n).hasCompactSupport_normed (μ := volume)).convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) ((lemma92Bump n).continuous_normed (μ := volume)) hli1
  have hce2 := ((lemma92Bump n).hasCompactSupport_normed (μ := volume)).convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) ((lemma92Bump n).continuous_normed (μ := volume)) hli2
  funext x
  have hi1 := (hce1 x).integrable
  have hi2 := (hce2 x).integrable
  show (∫ t, ContinuousLinearMap.lsmul ℝ ℝ ((lemma92Bump n).normed volume t) (ω₁ (x - t) - ω₂ (x - t))
      ∂volume) = _
  have heq : (fun t => ContinuousLinearMap.lsmul ℝ ℝ ((lemma92Bump n).normed volume t)
      (ω₁ (x - t) - ω₂ (x - t))) =
      (fun t => ContinuousLinearMap.lsmul ℝ ℝ ((lemma92Bump n).normed volume t) (ω₁ (x - t)) -
        ContinuousLinearMap.lsmul ℝ ℝ ((lemma92Bump n).normed volume t) (ω₂ (x - t))) := by
    funext t
    exact (ContinuousLinearMap.lsmul ℝ ℝ ((lemma92Bump n).normed volume t)).map_sub _ _
  rw [heq, integral_sub hi1 hi2]
  rfl

-- The mollification of a general (not necessarily bounded-support) `L_p` function converges to it
-- GLOBALLY in `L_p` (not merely on a fixed compact set, unlike `tendsto_eLpNorm_convolution_normed_sub`):
-- approximate by a compactly-supported continuous `H` (`ε/3`), mollify the compactly-supported
-- piece (which stays supported in a FIXED ball, so restricted = global convergence there, via
-- `tendsto_eLpNorm_convolution_normed_sub` itself), and bound the remainder by Young's inequality
-- (`eLpNorm_convolution_le_of_lintegral_eq_one`, `ε/3`) — a 3ε argument with no restriction needed
-- anywhere, since every piece is either exactly compactly supported or globally Young-bounded.
theorem t5Mollify_tendsto_global {p : ℝ} (hp1 : 1 ≤ p) (hp' : ENNReal.ofReal p ≠ ⊤) {ω : ℂ → ℂ}
    (hω : MemLp ω (ENNReal.ofReal p)) :
    Tendsto (fun n => eLpNorm (fun z => t5Mollify ω n z - ω z) (ENNReal.ofReal p)) atTop (𝓝 0) := by
  have hp1e : (1:ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3pos : (0:ℝ≥0∞) < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
  have hε3 : ε / 3 ≠ 0 := hε3pos.ne'
  obtain ⟨H, hHc, hFH, hHcont, hHmem⟩ := hω.exists_hasCompactSupport_eLpNorm_sub_le hp' hε3
  obtain ⟨R_H, hR_H⟩ := hHc.isBounded.subset_closedBall (0:ℂ)
  have hHsupp : ∀ z, R_H < ‖z‖ → H z = 0 := by
    intro z hz; by_contra hne
    have hmm := hR_H (subset_tsupport _ hne)
    rw [mem_closedBall_zero_iff] at hmm; linarith
  have hHtendsto : Tendsto (fun n => eLpNorm (fun z => t5Mollify H n z - H z) (ENNReal.ofReal p))
      atTop (𝓝 0) := by
    have hrestrict := tendsto_eLpNorm_convolution_normed_sub (b := lemma92Bump)
      tendsto_one_div_add_atTop_nhds_zero_nat hp1e hp' hHmem
      (measure_closedBall_lt_top (x := (0:ℂ)) (r := R_H + 1)).ne
    have heq : ∀ n, (fun z => t5Mollify H n z - H z) =
        (closedBall (0:ℂ) (R_H + 1)).indicator (fun z => t5Mollify H n z - H z) := by
      intro n
      have hsuppn := t5Mollify_support_subset hHsupp n
      have hsuppH : Function.support H ⊆ closedBall (0:ℂ) (R_H + 1) := fun z hz => by
        by_contra h
        have h' : R_H + 1 < ‖z‖ := by
          rw [mem_closedBall_zero_iff, not_le] at h; exact h
        exact hz (hHsupp z (by linarith))
      funext z
      by_cases hz : z ∈ closedBall (0:ℂ) (R_H + 1)
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz]
        have h1 : t5Mollify H n z = 0 := by by_contra hne; exact hz (hsuppn hne)
        have h2 : H z = 0 := by by_contra hne; exact hz (hsuppH hne)
        rw [h1, h2, sub_zero]
    have hgoal : (fun n => eLpNorm (fun z => t5Mollify H n z - H z) (ENNReal.ofReal p)) =
        (fun n => eLpNorm (fun z => t5Mollify H n z - H z) (ENNReal.ofReal p)
          (volume.restrict (closedBall (0:ℂ) (R_H + 1)))) := by
      funext n
      conv_lhs => rw [heq n]
      exact eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall.nullMeasurableSet
    rw [hgoal]
    exact hrestrict
  rw [ENNReal.tendsto_nhds_zero] at hHtendsto
  filter_upwards [hHtendsto (ε / 3) hε3pos] with n hn
  have hsub := t5Mollify_sub (ω₁ := ω) (ω₂ := H) hp1 hω hHmem n
  set A : ℂ → ℂ := t5Mollify (fun w => ω w - H w) n with hAdef
  set B : ℂ → ℂ := fun z => t5Mollify H n z - H z with hBdef
  set C : ℂ → ℂ := fun z => H z - ω z with hCdef
  have hsplit : (fun z => t5Mollify ω n z - ω z) = fun z => A z + B z + C z := by
    funext z
    have hz := congrFun hsub z
    show t5Mollify ω n z - ω z = A z + B z + C z
    rw [hz, hBdef, hCdef]
    ring
  rw [hsplit]
  have hy : eLpNorm A (ENNReal.ofReal p) ≤ ε / 3 := by
    rw [hAdef]
    exact le_trans
      (eLpNorm_convolution_le_of_lintegral_eq_one (lemma92Bump n).continuous_normed.measurable
        (fun x => (lemma92Bump n).nonneg_normed x)
        (by rw [← ofReal_integral_eq_lintegral_ofReal (lemma92Bump n).integrable_normed
            (Eventually.of_forall fun x => (lemma92Bump n).nonneg_normed x),
            (lemma92Bump n).integral_normed, ENNReal.ofReal_one])
        (hω.aestronglyMeasurable.sub hHmem.aestronglyMeasurable) hp1e hp') hFH
  have hz3 : eLpNorm C (ENNReal.ofReal p) ≤ ε / 3 := by
    have heq2 : C = H - ω := hCdef
    rw [heq2, eLpNorm_sub_comm]; exact hFH
  have hAcont : Continuous A := by
    rw [hAdef]; unfold t5Mollify
    exact ((lemma92Bump n).hasCompactSupport_normed (μ := volume)).continuous_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) ((lemma92Bump n).continuous_normed (μ := volume))
      ((hω.sub hHmem).locallyIntegrable hp1e)
  have hBcont : Continuous (t5Mollify H n) := by
    unfold t5Mollify
    exact ((lemma92Bump n).hasCompactSupport_normed (μ := volume)).continuous_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) ((lemma92Bump n).continuous_normed (μ := volume))
      hHcont.locallyIntegrable
  have hAm : AEStronglyMeasurable A volume := hAcont.aestronglyMeasurable
  have hBm : AEStronglyMeasurable B volume := by
    rw [hBdef]; exact (hBcont.sub hHcont).aestronglyMeasurable
  have hEm : AEStronglyMeasurable C volume := by
    rw [hCdef]; exact hHcont.aestronglyMeasurable.sub hω.aestronglyMeasurable
  clear_value A B C
  clear hAdef hBdef hCdef hsub hAcont hBcont H hHc hFH hHcont hHmem R_H hR_H hHsupp hHtendsto
  have s1 : eLpNorm (fun z => A z + B z + C z) (ENNReal.ofReal p) ≤
      eLpNorm (A + B) (ENNReal.ofReal p) + eLpNorm C (ENNReal.ofReal p) :=
    eLpNorm_add_le (f := A + B) (g := C) hp1e
  have s2 : eLpNorm (A + B) (ENNReal.ofReal p) + eLpNorm C (ENNReal.ofReal p) ≤
      (eLpNorm A (ENNReal.ofReal p) + eLpNorm B (ENNReal.ofReal p)) + ε / 3 :=
    add_le_add (eLpNorm_add_le (f := A) (g := B) hp1e) hz3
  have s3 : (eLpNorm A (ENNReal.ofReal p) + eLpNorm B (ENNReal.ofReal p)) + ε / 3 ≤
      (ε / 3 + ε / 3) + ε / 3 :=
    add_le_add (add_le_add hy hn) le_rfl
  have s4 : (ε / 3 + ε / 3) + ε / 3 = ε := ENNReal.add_thirds ε
  exact s4 ▸ (s1.trans (s2.trans s3))

/-- Basic fact 3: the approximants converge to `ω` in every `L_p` that `ω` belongs to. Split as
`hilbertHApprox ω n - ω = [t5Mollify(trunc_n ω,n) - t5Mollify(ω,n)] + [t5Mollify(ω,n) - ω]`: the
first bracket is `t5Mollify` of the truncation tail (Young's inequality, bounded by the tail norm,
which vanishes by `eLpNorm_indicator_compl_closedBall_tendsto_zero`); the second vanishes by
`t5Mollify_tendsto_global`. -/
theorem hilbertHApprox_tendsto {ω : ℂ → ℂ} {p : ℝ} (hp : 1 ≤ p)
    (hω : MemLp ω (ENNReal.ofReal p)) :
    Tendsto (fun n => eLpNorm (fun z => hilbertHApprox ω n z - ω z) (ENNReal.ofReal p))
      atTop (𝓝 0) := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hp1e : (1:ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hp'e : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have htail := eLpNorm_indicator_compl_closedBall_tendsto_zero hp0 hω
  have hbound : ∀ n : ℕ, eLpNorm (fun z => t5Mollify (hilbertHTrunc ω n) n z - t5Mollify ω n z)
      (ENNReal.ofReal p) ≤ eLpNorm ((closedBall (0:ℂ) (n:ℝ))ᶜ.indicator ω) (ENNReal.ofReal p) := by
    intro n
    have hsub := t5Mollify_sub (ω₁ := hilbertHTrunc ω n) (ω₂ := ω) hp (hilbertHTrunc_memLp hω n) hω n
    have heq1 : (fun z => t5Mollify (hilbertHTrunc ω n) n z - t5Mollify ω n z) =
        t5Mollify (fun w => hilbertHTrunc ω n w - ω w) n := by
      funext z; exact (congrFun hsub z).symm
    have heq2 : (fun w => hilbertHTrunc ω n w - ω w) =
        fun w => -((closedBall (0:ℂ) (n:ℝ))ᶜ.indicator ω w) := by
      funext w
      unfold hilbertHTrunc
      by_cases hw : w ∈ closedBall (0:ℂ) (n:ℝ)
      · rw [Set.indicator_of_mem hw, Set.indicator_of_notMem (by simp [hw]), neg_zero, sub_self]
      · rw [Set.indicator_of_notMem hw, Set.indicator_of_mem (by simp [hw]), zero_sub]
    rw [heq1, heq2]
    have hmeas : AEStronglyMeasurable (fun w => -((closedBall (0:ℂ) (n:ℝ))ᶜ.indicator ω w)) volume :=
      (hω.indicator (s := (closedBall (0:ℂ) (n:ℝ))ᶜ) measurableSet_closedBall.compl.nullMeasurableSet).aestronglyMeasurable.neg
    have hY : eLpNorm (t5Mollify (fun w => -((closedBall (0:ℂ) (n:ℝ))ᶜ.indicator ω w)) n)
        (ENNReal.ofReal p) ≤
        eLpNorm (fun w => -((closedBall (0:ℂ) (n:ℝ))ᶜ.indicator ω w)) (ENNReal.ofReal p) :=
      eLpNorm_convolution_le_of_lintegral_eq_one
        (lemma92Bump n).continuous_normed.measurable (fun x => (lemma92Bump n).nonneg_normed x)
        (by rw [← ofReal_integral_eq_lintegral_ofReal (lemma92Bump n).integrable_normed
            (Eventually.of_forall fun x => (lemma92Bump n).nonneg_normed x),
            (lemma92Bump n).integral_normed, ENNReal.ofReal_one])
        hmeas hp1e hp'e
    have heq3 : (fun w => -((closedBall (0:ℂ) (n:ℝ))ᶜ.indicator ω w)) =
        -((closedBall (0:ℂ) (n:ℝ))ᶜ.indicator ω) := rfl
    rw [heq3, eLpNorm_neg] at hY
    exact hY
  have hterm1 : Tendsto (fun n : ℕ => eLpNorm (fun z => t5Mollify (hilbertHTrunc ω n) n z -
      t5Mollify ω n z) (ENNReal.ofReal p)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htail
      (Eventually.of_forall fun n => bot_le) (Eventually.of_forall hbound)
  have hterm2 : Tendsto (fun n => eLpNorm (fun z => t5Mollify ω n z - ω z) (ENNReal.ofReal p))
      atTop (𝓝 0) := t5Mollify_tendsto_global hp hp'e hω
  have hsum : Tendsto (fun n => eLpNorm (fun z => t5Mollify (hilbertHTrunc ω n) n z -
      t5Mollify ω n z) (ENNReal.ofReal p) + eLpNorm (fun z => t5Mollify ω n z - ω z)
      (ENNReal.ofReal p)) atTop (𝓝 (0 + 0)) := hterm1.add hterm2
  rw [add_zero] at hsum
  have hle : ∀ n : ℕ, eLpNorm (fun z => hilbertHApprox ω n z - ω z) (ENNReal.ofReal p) ≤
      eLpNorm (fun z => t5Mollify (hilbertHTrunc ω n) n z - t5Mollify ω n z) (ENNReal.ofReal p) +
      eLpNorm (fun z => t5Mollify ω n z - ω z) (ENNReal.ofReal p) := by
    intro n
    have heq : (fun z => hilbertHApprox ω n z - ω z) = fun z =>
        (t5Mollify (hilbertHTrunc ω n) n z - t5Mollify ω n z) + (t5Mollify ω n z - ω z) := by
      funext z; unfold hilbertHApprox; ring
    rw [heq]
    exact eLpNorm_add_le hp1e
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun n => bot_le) (Eventually.of_forall hle)

/-- `t5Mollify` is exact (funext, not just a.e.) as a function of the a.e. class of its argument:
it is a convolution, i.e. an integral, so `integral_congr_ae` applies after transporting the a.e.
equality through the (quasi-measure-preserving) change of variables `t ↦ x - t`. -/
theorem t5Mollify_congr_ae {ω₁ ω₂ : ℂ → ℂ} (h : ω₁ =ᵐ[volume] ω₂) (n : ℕ) :
    t5Mollify ω₁ n = t5Mollify ω₂ n := by
  funext x
  show (∫ t, ContinuousLinearMap.lsmul ℝ ℝ ((lemma92Bump n).normed volume t) (ω₁ (x - t))) =
      (∫ t, ContinuousLinearMap.lsmul ℝ ℝ ((lemma92Bump n).normed volume t) (ω₂ (x - t)))
  apply integral_congr_ae
  have hxt : (fun t => ω₁ (x - t)) =ᵐ[volume] (fun t => ω₂ (x - t)) :=
    (quasiMeasurePreserving_sub_left volume x).ae_eq_comp h
  filter_upwards [hxt] with t ht
  rw [ht]

/-- Basic fact 4: `hilbertHApprox` is exact (funext, not just a.e.) as a function of the a.e. class
of `ω`: `hilbertHTrunc` preserves `=ᵐ` (indicators of a.e.-equal functions), and `t5Mollify`
upgrades `=ᵐ` to exact equality (`t5Mollify_congr_ae`). -/
theorem hilbertHApprox_congr_ae {ω₁ ω₂ : ℂ → ℂ} (h : ω₁ =ᵐ[volume] ω₂) :
    hilbertHApprox ω₁ = hilbertHApprox ω₂ := by
  have htrunc : ∀ n, hilbertHTrunc ω₁ n =ᵐ[volume] hilbertHTrunc ω₂ n := by
    intro n
    unfold hilbertHTrunc
    filter_upwards [h] with z hz
    by_cases hzmem : z ∈ closedBall (0:ℂ) (n:ℝ)
    · rw [Set.indicator_of_mem hzmem, Set.indicator_of_mem hzmem, hz]
    · rw [Set.indicator_of_notMem hzmem, Set.indicator_of_notMem hzmem]
  funext n
  unfold hilbertHApprox
  exact t5Mollify_congr_ae (htrunc n) n

open Classical in
/-- The choice is made over a SEQUENCE `a : ℕ → ℂ → ℂ`, never over `ω` directly: `hilbertH ω₁`
and `hilbertH ω₂` for `ω₁ =ᵐ ω₂` then choose over the SAME proposition (since `hilbertHApprox`
is already exactly equal, `hilbertHApprox_congr_ae`), giving exact `=` rather than merely `=ᵐ`. -/
def hilbertHLim (a : ℕ → ℂ → ℂ) : ℂ → ℂ :=
  if h : ∃ p : ℝ, 1 < p ∧ ∃ Ω : ℂ → ℂ, MemLp Ω (ENNReal.ofReal p) ∧
      Tendsto (fun n => eLpNorm (fun z => hilbertHSmooth (a n) z - Ω z) (ENNReal.ofReal p))
        atTop (𝓝 0)
    then h.choose_spec.2.choose
  else 0

/-- The general Hilbert transform. -/
def hilbertH (ω : ℂ → ℂ) : ℂ → ℂ :=
  hilbertHLim (hilbertHApprox ω)



/-- Exact (funext), no choice comparison: `hilbertHApprox` is already exactly equal, so this is
`congrArg hilbertHLim`. -/
theorem hilbertH_congr_ae {ω₁ ω₂ : ℂ → ℂ} (h : ω₁ =ᵐ[volume] ω₂) :
    hilbertH ω₁ = hilbertH ω₂ := by
  unfold hilbertH
  rw [hilbertHApprox_congr_ae h]

/-- Independence of `p`: if the images of the SAME approximant sequence converge in `L_p` to `Ω₁`
and in `L_q` to `Ω₂`, then `Ω₁ =ᵐ Ω₂` — a common-subsequence argument: `L_p`/`L_q` convergence each
give a further a.e.-convergent subsequence of `hilbertHSmooth ∘ a`, and any two a.e.-convergent
subsequences of the same sequence share a common a.e.-limit set, by extracting a subsequence of a
subsequence. This is what makes `hilbertH` well-defined independently of which `p` a given lemma
happens to invoke it at, and identifies the choice-picked witness with any exhibited one. -/
-- NOTE (flagged for -17): the frozen signature is missing a regularity hypothesis on `ω` — without
-- it, `hilbertHApprox ω n` need not even be continuous (`hilbertHApprox_contDiff`/`_hasCompactSupport`
-- both go through `t5Mollify`, which needs `ω` at least `MemLp` for SOME exponent to make sense as
-- a genuine, non-junk function). Added `(hω : MemLp ω (ENNReal.ofReal p))`, reusing the same `p` as
-- `Ω₁` — the only place this lemma is actually invoked (`hilbertH_memLp_of_smooth_bound`,
-- the linchpin) always has exactly this hypothesis in scope already, so nothing downstream changes.
theorem hilbertH_indep_of_p {ω Ω₁ Ω₂ : ℂ → ℂ} {p q : ℝ} (hp : 1 < p) (hq : 1 < q)
    (hω : MemLp ω (ENNReal.ofReal p))
    (hΩ₁ : MemLp Ω₁ (ENNReal.ofReal p))
    (hconv₁ : Tendsto (fun n => eLpNorm (fun z => hilbertHSmooth (hilbertHApprox ω n) z - Ω₁ z)
      (ENNReal.ofReal p)) atTop (𝓝 0))
    (hΩ₂ : MemLp Ω₂ (ENNReal.ofReal q))
    (hconv₂ : Tendsto (fun n => eLpNorm (fun z => hilbertHSmooth (hilbertHApprox ω n) z - Ω₂ z)
      (ENNReal.ofReal q)) atTop (𝓝 0)) :
    Ω₁ =ᵐ[volume] Ω₂ := by
  have hp0 : (0:ℝ) < p := lt_trans one_pos hp
  have hq0 : (0:ℝ) < q := lt_trans one_pos hq
  set f : ℕ → ℂ → ℂ := fun n => hilbertHSmooth (hilbertHApprox ω n) with hfdef
  have hfmeas : ∀ n, AEStronglyMeasurable (f n) volume := fun n =>
    (i1_hilbertH_eq_cauchyT_dz (hilbertHApprox_contDiff hp.le hω n)
      (hilbertHApprox_hasCompactSupport ω n)).2.1.continuous.aestronglyMeasurable
  have hpne0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  have hqne0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.2 hq0).ne'
  have htm1 : TendstoInMeasure volume f atTop Ω₁ :=
    tendstoInMeasure_of_tendsto_eLpNorm hpne0 hconv₁
  obtain ⟨ns₁, hns₁mono, hns₁ae⟩ := htm1.exists_seq_tendsto_ae
  have hns₁tendsto : Tendsto ns₁ atTop atTop := hns₁mono.tendsto_atTop
  have hconv₂' : Tendsto (fun i => eLpNorm (fun z => f (ns₁ i) z - Ω₂ z) (ENNReal.ofReal q))
      atTop (𝓝 0) := hconv₂.comp hns₁tendsto
  have htm2 : TendstoInMeasure volume (fun i => f (ns₁ i)) atTop Ω₂ :=
    tendstoInMeasure_of_tendsto_eLpNorm hqne0 hconv₂'
  obtain ⟨ms, hmsmono, hmsae⟩ := htm2.exists_seq_tendsto_ae
  have hmstendsto : Tendsto ms atTop atTop := hmsmono.tendsto_atTop
  have h1' : ∀ᵐ x ∂volume, Tendsto (fun i => f (ns₁ (ms i)) x) atTop (𝓝 (Ω₁ x)) := by
    filter_upwards [hns₁ae] with x hx
    exact hx.comp hmstendsto
  filter_upwards [h1', hmsae] with x hx1 hx2
  exact tendsto_nhds_unique hx1 hx2

-- CANONICAL (leader -17): the conditional extension by density. `1 < p` is load-bearing: without
-- it the `if` in `hilbertHLim` may select an unrelated exponent's limit. `A` is not required
-- nonnegative. The `hilbertHSmooth`-images of the approximants are Cauchy in `L_p` (via `hbound` on
-- their differences, which are `C₀^∞`, plus `hilbertHApprox_tendsto` making the approximants
-- themselves Cauchy); `L_p` is complete, giving a limit `Ω`; `hilbertH_indep_of_p` identifies `Ω`
-- (up to `=ᵐ`) with whatever `hilbertHLim`'s choice actually picked; the bound passes to the limit
-- by a triangle-inequality sandwich.
/-- Stronger form: also exposes that the approximants' `hilbertHSmooth`-images actually converge (in
`L_p`) to `hilbertH ω` itself — needed to get the REVERSE inequality (isometry, not just
contraction) at `p = 2` in `hilbertH_memLp_two`, where `hbound` is an equality. -/
theorem hilbertH_tendsto_of_smooth_bound {p A : ℝ} (hp : 1 < p)
    (hbound : ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal A * eLpNorm φ (ENNReal.ofReal p) volume) :
    ∀ ω : ℂ → ℂ, MemLp ω (ENNReal.ofReal p) →
      MemLp (hilbertH ω) (ENNReal.ofReal p) ∧
        eLpNorm (hilbertH ω) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal A * eLpNorm ω (ENNReal.ofReal p) volume ∧
        Tendsto (fun n => eLpNorm (fun z => hilbertHSmooth (hilbertHApprox ω n) z - hilbertH ω z)
          (ENNReal.ofReal p)) atTop (𝓝 0) := by
  intro ω hω
  have hp1e : (1:ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  have hp'e : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  haveI factp : Fact ((1:ℝ≥0∞) ≤ ENNReal.ofReal p) := ⟨hp1e⟩
  set a : ℕ → ℂ → ℂ := hilbertHApprox ω with hadef
  have hacd : ∀ n, ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (a n) := fun n => hilbertHApprox_contDiff hp.le hω n
  have hacs : ∀ n, HasCompactSupport (a n) := fun n => hilbertHApprox_hasCompactSupport ω n
  have hatendsto : Tendsto (fun n => eLpNorm (fun z => a n z - ω z) (ENNReal.ofReal p)) atTop (𝓝 0) :=
    hilbertHApprox_tendsto hp.le hω
  have hHmem : ∀ n, MemLp (hilbertHSmooth (a n)) (ENNReal.ofReal p) := by
    intro n
    have hb := hbound (a n) (hacd n) (hacs n)
    have haMemLp : MemLp (a n) (ENNReal.ofReal p) :=
      (hacd n).continuous.memLp_of_hasCompactSupport (hacs n)
    exact memLp_iff.mpr
      (lt_of_le_of_lt hb (ENNReal.mul_lt_top ENNReal.ofReal_lt_top haMemLp.eLpNorm_lt_top))
  set g : ℕ → Lp ℂ (ENNReal.ofReal p) volume := fun n => (hHmem n).toLp (hilbertHSmooth (a n))
    with hgdef
  have hdiffbound : ∀ n m, eLpNorm (fun z => hilbertHSmooth (a n) z - hilbertHSmooth (a m) z)
      (ENNReal.ofReal p) ≤ ENNReal.ofReal A * eLpNorm (fun z => a n z - a m z) (ENNReal.ofReal p) := by
    intro n m
    have hsub := hilbertHSmooth_sub (hacd n) (hacs n) (hacd m) (hacs m)
    have hb := hbound (fun z => a n z - a m z) ((hacd n).sub (hacd m)) ((hacs n).sub (hacs m))
    rwa [hsub] at hb
  have htfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop :=
    tendsto_atTop.2 fun b => eventually_atTop.2 ⟨(b, 0), fun nm hnm => hnm.1⟩
  have htsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop :=
    tendsto_atTop.2 fun b => eventually_atTop.2 ⟨(0, b), fun nm hnm => hnm.2⟩
  have hCauchy0 : Tendsto (fun nm : ℕ × ℕ => eLpNorm (fun z => a nm.1 z - a nm.2 z)
      (ENNReal.ofReal p)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun nm : ℕ × ℕ => eLpNorm (fun z => a nm.1 z - ω z) (ENNReal.ofReal p))
        atTop (𝓝 0) := hatendsto.comp htfst
    have h2 : Tendsto (fun nm : ℕ × ℕ => eLpNorm (fun z => ω z - a nm.2 z) (ENNReal.ofReal p))
        atTop (𝓝 0) := by
      have heq : ∀ nm : ℕ × ℕ, eLpNorm (fun z => ω z - a nm.2 z) (ENNReal.ofReal p) =
          eLpNorm (fun z => a nm.2 z - ω z) (ENNReal.ofReal p) := by
        intro nm
        have h3 : (fun z => ω z - a nm.2 z) = -(fun z => a nm.2 z - ω z) := by
          funext z; show ω z - a nm.2 z = -(a nm.2 z - ω z); ring
        rw [h3, eLpNorm_neg]
      simp_rw [heq]
      exact hatendsto.comp htsnd
    have hsum := h1.add h2
    rw [add_zero] at hsum
    have hle : ∀ nm : ℕ × ℕ, eLpNorm (fun z => a nm.1 z - a nm.2 z) (ENNReal.ofReal p) ≤
        eLpNorm (fun z => a nm.1 z - ω z) (ENNReal.ofReal p) +
        eLpNorm (fun z => ω z - a nm.2 z) (ENNReal.ofReal p) := by
      intro nm
      have heq : (fun z => a nm.1 z - a nm.2 z) =
          fun z => (a nm.1 z - ω z) + (ω z - a nm.2 z) := by funext z; ring
      rw [heq]
      exact eLpNorm_add_le (μ := volume) (f := fun z => a nm.1 z - ω z)
        (g := fun z => ω z - a nm.2 z) hp1e
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun nm => bot_le) (Eventually.of_forall hle)
  have hcauchy : CauchySeq g := by
    rw [Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm]
    have heqg : ∀ nm : ℕ × ℕ, eLpNorm (⇑(g nm.1) - ⇑(g nm.2)) (ENNReal.ofReal p) volume =
        eLpNorm (fun z => hilbertHSmooth (a nm.1) z - hilbertHSmooth (a nm.2) z)
          (ENNReal.ofReal p) := by
      intro nm
      apply eLpNorm_congr_ae
      filter_upwards [(hHmem nm.1).coeFn_toLp, (hHmem nm.2).coeFn_toLp] with z hz1 hz2
      show g nm.1 z - g nm.2 z = _
      rw [hz1, hz2]
    simp_rw [heqg]
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have hb2 : Tendsto (fun nm : ℕ × ℕ => ENNReal.ofReal A * eLpNorm (fun z => a nm.1 z - a nm.2 z)
        (ENNReal.ofReal p)) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal A) hCauchy0
        (Or.inr ENNReal.ofReal_ne_top)
      simpa using this
    rw [ENNReal.tendsto_nhds_zero] at hb2
    filter_upwards [hb2 ε hε] with nm hnm
    exact (hdiffbound nm.1 nm.2).trans hnm
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  set Ω : ℂ → ℂ := (L : ℂ → ℂ) with hΩdef
  have hΩmem : MemLp Ω (ENNReal.ofReal p) := Lp.memLp L
  have hΩconv : Tendsto (fun n => eLpNorm (fun z => hilbertHSmooth (a n) z - Ω z)
      (ENNReal.ofReal p)) atTop (𝓝 0) := by
    have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' g L).mp hL
    have heq : ∀ n, eLpNorm (⇑(g n) - ⇑L) (ENNReal.ofReal p) volume =
        eLpNorm (fun z => hilbertHSmooth (a n) z - Ω z) (ENNReal.ofReal p) := by
      intro n
      apply eLpNorm_congr_ae
      filter_upwards [(hHmem n).coeFn_toLp] with z hz1
      show g n z - L z = _
      rw [hz1]
    simp_rw [heq] at h1
    exact h1
  have hexists : ∃ p' : ℝ, 1 < p' ∧ ∃ Ω' : ℂ → ℂ, MemLp Ω' (ENNReal.ofReal p') ∧
      Tendsto (fun n => eLpNorm (fun z => hilbertHSmooth (a n) z - Ω' z) (ENNReal.ofReal p'))
        atTop (𝓝 0) := ⟨p, hp, Ω, hΩmem, hΩconv⟩
  have hfire : hilbertH ω = hexists.choose_spec.2.choose := by
    show hilbertHLim a = _
    unfold hilbertHLim
    rw [dif_pos hexists]
  have hidentify : Ω =ᵐ[volume] hilbertH ω := by
    rw [hfire]
    exact hilbertH_indep_of_p hp hexists.choose_spec.1 hω hΩmem hΩconv
      hexists.choose_spec.2.choose_spec.1 hexists.choose_spec.2.choose_spec.2
  have hMemLpGoal : MemLp (hilbertH ω) (ENNReal.ofReal p) := hΩmem.ae_eq hidentify
  refine ⟨hMemLpGoal, ?_, ?_⟩
  have hbdΩ : eLpNorm Ω (ENNReal.ofReal p) ≤ ENNReal.ofReal A * eLpNorm ω (ENNReal.ofReal p) := by
    have hchain : ∀ n, eLpNorm Ω (ENNReal.ofReal p) ≤
        eLpNorm (fun z => Ω z - hilbertHSmooth (a n) z) (ENNReal.ofReal p) +
          (ENNReal.ofReal A * eLpNorm (fun z => a n z - ω z) (ENNReal.ofReal p) +
            ENNReal.ofReal A * eLpNorm ω (ENNReal.ofReal p)) := by
      intro n
      have h1 : eLpNorm Ω (ENNReal.ofReal p) ≤
          eLpNorm (fun z => Ω z - hilbertHSmooth (a n) z) (ENNReal.ofReal p) +
            eLpNorm (hilbertHSmooth (a n)) (ENNReal.ofReal p) := by
        have heq : Ω = (fun z => Ω z - hilbertHSmooth (a n) z) + hilbertHSmooth (a n) := by
          funext z; show Ω z = (Ω z - hilbertHSmooth (a n) z) + hilbertHSmooth (a n) z; ring
        have hs1 : eLpNorm Ω (ENNReal.ofReal p) =
            eLpNorm ((fun z => Ω z - hilbertHSmooth (a n) z) + hilbertHSmooth (a n))
              (ENNReal.ofReal p) := by rw [← heq]
        have hs2 : eLpNorm ((fun z => Ω z - hilbertHSmooth (a n) z) + hilbertHSmooth (a n))
            (ENNReal.ofReal p) ≤ eLpNorm (fun z => Ω z - hilbertHSmooth (a n) z) (ENNReal.ofReal p) +
              eLpNorm (hilbertHSmooth (a n)) (ENNReal.ofReal p) :=
          eLpNorm_add_le hp1e
        exact hs1 ▸ hs2
      have h2 : eLpNorm (hilbertHSmooth (a n)) (ENNReal.ofReal p) ≤
          ENNReal.ofReal A * eLpNorm (a n) (ENNReal.ofReal p) := hbound (a n) (hacd n) (hacs n)
      have h3 : eLpNorm (a n) (ENNReal.ofReal p) ≤
          eLpNorm (fun z => a n z - ω z) (ENNReal.ofReal p) + eLpNorm ω (ENNReal.ofReal p) := by
        have heq3 : a n = (fun z => a n z - ω z) + ω := by
          funext z; show a n z = (a n z - ω z) + ω z; ring
        have hs3 : eLpNorm (a n) (ENNReal.ofReal p) =
            eLpNorm ((fun z => a n z - ω z) + ω) (ENNReal.ofReal p) := by rw [← heq3]
        have hs4 : eLpNorm ((fun z => a n z - ω z) + ω) (ENNReal.ofReal p) ≤
            eLpNorm (fun z => a n z - ω z) (ENNReal.ofReal p) + eLpNorm ω (ENNReal.ofReal p) :=
          eLpNorm_add_le hp1e
        exact hs3 ▸ hs4
      have h4 : ENNReal.ofReal A * eLpNorm (a n) (ENNReal.ofReal p) ≤
          ENNReal.ofReal A * (eLpNorm (fun z => a n z - ω z) (ENNReal.ofReal p) +
            eLpNorm ω (ENNReal.ofReal p)) := by gcongr
      rw [mul_add] at h4
      exact h1.trans (add_le_add le_rfl (h2.trans h4))
    have htendsto : Tendsto (fun n => eLpNorm (fun z => Ω z - hilbertHSmooth (a n) z)
        (ENNReal.ofReal p) + (ENNReal.ofReal A * eLpNorm (fun z => a n z - ω z)
          (ENNReal.ofReal p) + ENNReal.ofReal A * eLpNorm ω (ENNReal.ofReal p))) atTop
        (𝓝 (0 + (ENNReal.ofReal A * 0 + ENNReal.ofReal A * eLpNorm ω (ENNReal.ofReal p)))) := by
      have hterm1 : Tendsto (fun n => eLpNorm (fun z => Ω z - hilbertHSmooth (a n) z)
          (ENNReal.ofReal p)) atTop (𝓝 0) := by
        have heq : ∀ n, eLpNorm (fun z => Ω z - hilbertHSmooth (a n) z) (ENNReal.ofReal p) =
            eLpNorm (fun z => hilbertHSmooth (a n) z - Ω z) (ENNReal.ofReal p) := by
          intro n
          have h5 : (fun z => Ω z - hilbertHSmooth (a n) z) =
              -(fun z => hilbertHSmooth (a n) z - Ω z) := by
            funext z; show Ω z - hilbertHSmooth (a n) z = -(hilbertHSmooth (a n) z - Ω z); ring
          rw [h5, eLpNorm_neg]
        simp_rw [heq]
        exact hΩconv
      have hterm2 : Tendsto (fun n => ENNReal.ofReal A * eLpNorm (fun z => a n z - ω z)
          (ENNReal.ofReal p)) atTop (𝓝 (ENNReal.ofReal A * 0)) :=
        ENNReal.Tendsto.const_mul hatendsto (Or.inr ENNReal.ofReal_ne_top)
      exact hterm1.add (hterm2.add tendsto_const_nhds)
    rw [mul_zero, zero_add, zero_add] at htendsto
    exact ge_of_tendsto' htendsto hchain
  have hfinaleq : eLpNorm (hilbertH ω) (ENNReal.ofReal p) = eLpNorm Ω (ENNReal.ofReal p) := by
    rw [eLpNorm_congr_ae hidentify.symm]
  exact hfinaleq ▸ hbdΩ
  · have heqn : ∀ n, eLpNorm (fun z => hilbertHSmooth (a n) z - Ω z) (ENNReal.ofReal p) =
        eLpNorm (fun z => hilbertHSmooth (a n) z - hilbertH ω z) (ENNReal.ofReal p) := by
      intro n
      apply eLpNorm_congr_ae
      filter_upwards [hidentify] with z hz
      rw [hz]
    simp_rw [heqn] at hΩconv
    exact hΩconv

/-- CANONICAL (leader -17): thin wrapper over `hilbertH_tendsto_of_smooth_bound`, dropping the
convergence-of-approximants clause to match the frozen interface exactly. -/
theorem hilbertH_memLp_of_smooth_bound {p A : ℝ} (hp : 1 < p)
    (hbound : ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal A * eLpNorm φ (ENNReal.ofReal p) volume) :
    ∀ ω : ℂ → ℂ, MemLp ω (ENNReal.ofReal p) →
      MemLp (hilbertH ω) (ENNReal.ofReal p) ∧
        eLpNorm (hilbertH ω) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal A * eLpNorm ω (ENNReal.ofReal p) volume :=
  fun ω hω => ⟨(hilbertH_tendsto_of_smooth_bound hp hbound ω hω).1,
    (hilbertH_tendsto_of_smooth_bound hp hbound ω hω).2.1⟩

theorem ofReal_two_eq : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
  rw [show (2:ℝ) = ((2:ℕ):ℝ) from by norm_num, ENNReal.ofReal_natCast]
  norm_num

/-- `eLpNorm` is continuous along an `L_p`-convergent sequence (finite-limit case): if
`eLpNorm (f n - g) p → 0` and `eLpNorm g p ≠ ⊤`, then `eLpNorm (f n) p → eLpNorm g p`. Proved by
converting to `.toReal` (both sides finite) and squeezing the real sequence between
`eLpNorm g - eLpNorm (fn - g)` and `eLpNorm g + eLpNorm (fn - g)` via the two triangle inequalities. -/
theorem tendsto_eLpNorm_of_tendsto_eLpNorm_sub {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hf : ∀ n, AEStronglyMeasurable (f n) volume) (hg : AEStronglyMeasurable g volume)
    (hgfin : eLpNorm g p volume ≠ ⊤) (hffin : ∀ n, eLpNorm (f n) p volume ≠ ⊤)
    (h : Tendsto (fun n => eLpNorm (fun z => f n z - g z) p volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) p volume) atTop (𝓝 (eLpNorm g p volume)) := by
  have hub : ∀ n, eLpNorm (f n) p volume ≤
      eLpNorm (fun z => f n z - g z) p volume + eLpNorm g p volume := by
    intro n
    have heq : f n = (fun z => f n z - g z) + g := by
      funext z; show f n z = (f n z - g z) + g z; ring
    have hs1 : eLpNorm (f n) p volume = eLpNorm ((fun z => f n z - g z) + g) p volume := by
      rw [← heq]
    have hs2 : eLpNorm ((fun z => f n z - g z) + g) p volume ≤
        eLpNorm (fun z => f n z - g z) p volume + eLpNorm g p volume :=
      eLpNorm_add_le hp1
    exact hs1 ▸ hs2
  have hlb : ∀ n, eLpNorm g p volume ≤
      eLpNorm (fun z => f n z - g z) p volume + eLpNorm (f n) p volume := by
    intro n
    have heq : g = (fun z => g z - f n z) + f n := by
      funext z; show g z = (g z - f n z) + f n z; ring
    have hs1 : eLpNorm g p volume = eLpNorm ((fun z => g z - f n z) + f n) p volume := by
      rw [← heq]
    have hs2 : eLpNorm ((fun z => g z - f n z) + f n) p volume ≤
        eLpNorm (fun z => g z - f n z) p volume + eLpNorm (f n) p volume :=
      eLpNorm_add_le hp1
    have hcomm : eLpNorm (fun z => g z - f n z) p volume =
        eLpNorm (fun z => f n z - g z) p volume := by
      have h1 : (fun z => g z - f n z) = -(fun z => f n z - g z) := by
        funext z; show g z - f n z = -(f n z - g z); ring
      rw [h1, eLpNorm_neg]
    rw [hcomm] at hs2
    exact hs1 ▸ hs2
  have hsubfin : ∀ n, eLpNorm (fun z => f n z - g z) p volume ≠ ⊤ := by
    intro n
    have hle : eLpNorm (fun z => f n z - g z) p volume ≤
        eLpNorm (f n) p volume + eLpNorm g p volume := by
      have heq : (fun z => f n z - g z) = f n + (-g) := by
        funext z; show f n z - g z = f n z + (-g z); ring
      have hs1 : eLpNorm (fun z => f n z - g z) p volume = eLpNorm (f n + (-g)) p volume := by
        rw [heq]
      have hs2 : eLpNorm (f n + (-g)) p volume ≤ eLpNorm (f n) p volume + eLpNorm (-g) p volume :=
        eLpNorm_add_le hp1
      rw [eLpNorm_neg] at hs2
      exact hs1 ▸ hs2
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hffin n, hgfin⟩) hle
  have hubR : ∀ n, (eLpNorm (f n) p volume).toReal ≤
      (eLpNorm (fun z => f n z - g z) p volume).toReal + (eLpNorm g p volume).toReal := by
    intro n
    have hmono := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨hsubfin n, hgfin⟩) (hub n)
    rwa [ENNReal.toReal_add (hsubfin n) hgfin] at hmono
  have hlbR : ∀ n, (eLpNorm g p volume).toReal ≤
      (eLpNorm (fun z => f n z - g z) p volume).toReal + (eLpNorm (f n) p volume).toReal := by
    intro n
    have hmono := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨hsubfin n, hffin n⟩) (hlb n)
    rwa [ENNReal.toReal_add (hsubfin n) (hffin n)] at hmono
  have hR : Tendsto (fun n => (eLpNorm (fun z => f n z - g z) p volume).toReal) atTop (𝓝 0) := by
    have := ENNReal.tendsto_toReal (a := (0:ℝ≥0∞)) (by norm_num)
    exact (this.comp h)
  have hsqueeze : Tendsto (fun n => (eLpNorm (f n) p volume).toReal) atTop
      (𝓝 ((eLpNorm g p volume).toReal)) := by
    have hlow : Tendsto (fun n => (eLpNorm g p volume).toReal -
        (eLpNorm (fun z => f n z - g z) p volume).toReal) atTop
        (𝓝 ((eLpNorm g p volume).toReal - 0)) := tendsto_const_nhds.sub hR
    rw [sub_zero] at hlow
    have hhigh : Tendsto (fun n => (eLpNorm g p volume).toReal +
        (eLpNorm (fun z => f n z - g z) p volume).toReal) atTop
        (𝓝 ((eLpNorm g p volume).toReal)) := by
      have := hR.const_add ((eLpNorm g p volume).toReal)
      rwa [add_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh
      (Eventually.of_forall fun n => by linarith [hlbR n])
      (Eventually.of_forall fun n => by linarith [hubR n])
  have h1 : ∀ n, eLpNorm (f n) p volume ≠ ⊤ := hffin
  exact (ENNReal.tendsto_toReal_iff h1 hgfin).mp hsqueeze

/-- The `p = 2` case, singled out: proved from `i4_eLpNorm_eq` (the exact isometry on `C₀^∞`,
already proved, 0 sorry) ALONE — no `zygmund_calderon` anywhere. -/
theorem hilbertH_memLp_two {ω : ℂ → ℂ} (hω : MemLp ω 2) :
    MemLp (hilbertH ω) 2 ∧ eLpNorm (hilbertH ω) 2 volume = eLpNorm ω 2 volume := by
  have hp2 : (1:ℝ) < 2 := one_lt_two
  have hbound2 : ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal (2:ℝ)) volume ≤
        ENNReal.ofReal (1:ℝ) * eLpNorm φ (ENNReal.ofReal (2:ℝ)) volume := by
    intro φ hφ hc
    rw [ofReal_two_eq, ENNReal.ofReal_one, one_mul]
    exact (i4_eLpNorm_eq hφ hc).le
  have hω' : MemLp ω (ENNReal.ofReal (2:ℝ)) := ofReal_two_eq ▸ hω
  obtain ⟨hmem, hbd, hconv⟩ := hilbertH_tendsto_of_smooth_bound hp2 hbound2 ω hω'
  rw [ofReal_two_eq] at hmem hbd hconv
  have hatendsto2 : Tendsto (fun n => eLpNorm (fun z => hilbertHApprox ω n z - ω z) 2)
      atTop (𝓝 0) := ofReal_two_eq ▸ hilbertHApprox_tendsto hp2.le hω'
  have heq3 : ∀ n, eLpNorm (hilbertHSmooth (hilbertHApprox ω n)) 2 volume =
      eLpNorm (hilbertHApprox ω n) 2 volume :=
    fun n => i4_eLpNorm_eq (hilbertHApprox_contDiff hp2.le hω' n) (hilbertHApprox_hasCompactSupport ω n)
  have hffin2 : ∀ n, eLpNorm (hilbertHApprox ω n) 2 volume ≠ ⊤ :=
    fun n => (((hilbertHApprox_contDiff hp2.le hω' n).continuous.memLp_of_hasCompactSupport
      (p := (2:ℝ≥0∞)) (hilbertHApprox_hasCompactSupport ω n))).eLpNorm_lt_top.ne
  have hffin1 : ∀ n, eLpNorm (hilbertHSmooth (hilbertHApprox ω n)) 2 volume ≠ ⊤ := by
    intro n; rw [heq3 n]; exact hffin2 n
  have hconv1 : Tendsto (fun n => eLpNorm (hilbertHSmooth (hilbertHApprox ω n)) 2 volume) atTop
      (𝓝 (eLpNorm (hilbertH ω) 2 volume)) :=
    tendsto_eLpNorm_of_tendsto_eLpNorm_sub (by norm_num : (1:ℝ≥0∞) ≤ 2)
      (fun n => (i1_hilbertH_eq_cauchyT_dz (hilbertHApprox_contDiff hp2.le hω' n)
        (hilbertHApprox_hasCompactSupport ω n)).2.1.continuous.aestronglyMeasurable)
      hmem.aestronglyMeasurable hmem.eLpNorm_lt_top.ne hffin1 hconv
  have hconv2 : Tendsto (fun n => eLpNorm (hilbertHApprox ω n) 2 volume) atTop
      (𝓝 (eLpNorm ω 2 volume)) :=
    tendsto_eLpNorm_of_tendsto_eLpNorm_sub (by norm_num : (1:ℝ≥0∞) ≤ 2)
      (fun n => (hilbertHApprox_contDiff hp2.le hω' n).continuous.aestronglyMeasurable)
      hω.aestronglyMeasurable hω.eLpNorm_lt_top.ne hffin2 hatendsto2
  simp_rw [heq3] at hconv1
  exact ⟨hmem, tendsto_nhds_unique hconv1 hconv2⟩

theorem cauchyT_neg (ψ : ℂ → ℂ) : cauchyT (fun z => -ψ z) = fun z => -cauchyT ψ z := by
  funext z
  unfold cauchyT
  have heq : (fun ζ => (-ψ ζ) / (ζ - z)) = fun ζ => -(ψ ζ / (ζ - z)) := by funext ζ; ring
  rw [heq, integral_neg, mul_neg]

theorem dz_neg_pointwise {φ : ℂ → ℂ} {z : ℂ} (hφ : DifferentiableAt ℝ φ z) :
    dz (fun w => -φ w) z = -dz φ z := by
  unfold dz
  have h : fderiv ℝ (fun w => -φ w) z = -fderiv ℝ φ z := hφ.hasFDerivAt.neg.fderiv
  rw [h]
  simp only [ContinuousLinearMap.neg_apply]
  ring

theorem hilbertHSmooth_neg {φ : ℂ → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hcφ : HasCompactSupport φ) :
    hilbertHSmooth (fun z => -φ z) = fun z => -hilbertHSmooth φ z := by
  have hneg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => -φ z) := hφ.neg
  have hcneg : HasCompactSupport (fun z => -φ z) := hcφ.neg
  have h1 := i1_hilbertH_eq_cauchyT_dz hφ hcφ
  have h2 := i1_hilbertH_eq_cauchyT_dz hneg hcneg
  have hdzeq : dz (fun z => -φ z) = fun z => -dz φ z := by
    funext z; exact dz_neg_pointwise (hφ.differentiable (by norm_num) z)
  funext z
  rw [h2.1, h1.1, hdzeq]
  exact congrFun (cauchyT_neg (dz φ)) z

theorem hilbertHSmooth_add {φ ψ : ℂ → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hcφ : HasCompactSupport φ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hcψ : HasCompactSupport ψ) :
    hilbertHSmooth (fun z => φ z + ψ z) = fun z => hilbertHSmooth φ z + hilbertHSmooth ψ z := by
  have hnegψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => -ψ z) := hψ.neg
  have hcnegψ : HasCompactSupport (fun z => -ψ z) := hcψ.neg
  have hsub := hilbertHSmooth_sub hφ hcφ hnegψ hcnegψ
  have hnegeq : hilbertHSmooth (fun z => -ψ z) = fun z => -hilbertHSmooth ψ z := hilbertHSmooth_neg hψ hcψ
  funext z
  have hz := congrFun hsub z
  have heqfun : (fun z => φ z - (fun z => -ψ z) z) = fun z => φ z + ψ z := by
    funext w; show φ w - (-ψ w) = φ w + ψ w; ring
  rw [heqfun] at hz
  rw [hz, congrFun hnegeq z]
  ring

theorem t5Mollify_neg (ω : ℂ → ℂ) (n : ℕ) :
    t5Mollify (fun z => -ω z) n = fun z => -(t5Mollify ω n z) := by
  funext x
  show (∫ t, ContinuousLinearMap.lsmul ℝ ℝ ((lemma92Bump n).normed volume t) (-ω (x - t))) =
      -(∫ t, ContinuousLinearMap.lsmul ℝ ℝ ((lemma92Bump n).normed volume t) (ω (x - t)))
  have heq : (fun t => ContinuousLinearMap.lsmul ℝ ℝ ((lemma92Bump n).normed volume t) (-ω (x - t)))
      = fun t => -(ContinuousLinearMap.lsmul ℝ ℝ ((lemma92Bump n).normed volume t) (ω (x - t))) := by
    funext t
    exact (ContinuousLinearMap.lsmul ℝ ℝ ((lemma92Bump n).normed volume t)).map_neg _
  rw [heq, integral_neg]

theorem t5Mollify_add {ω₁ ω₂ : ℂ → ℂ} {p : ℝ} (hp : 1 ≤ p)
    (hω₁ : MemLp ω₁ (ENNReal.ofReal p)) (hω₂ : MemLp ω₂ (ENNReal.ofReal p)) (n : ℕ) :
    t5Mollify (fun z => ω₁ z + ω₂ z) n = fun z => t5Mollify ω₁ n z + t5Mollify ω₂ n z := by
  have hnegω₂ : MemLp (fun z => -ω₂ z) (ENNReal.ofReal p) := hω₂.neg
  have hsub := t5Mollify_sub hp hω₁ hnegω₂ n
  have hnegeq := t5Mollify_neg ω₂ n
  funext z
  have hz := congrFun hsub z
  have heqfun : (fun z => ω₁ z - (fun z => -ω₂ z) z) = fun z => ω₁ z + ω₂ z := by
    funext w; show ω₁ w - (-ω₂ w) = ω₁ w + ω₂ w; ring
  rw [heqfun] at hz
  rw [hz, congrFun hnegeq z]
  ring

theorem hilbertHApprox_add {ω₁ ω₂ : ℂ → ℂ} {p : ℝ} (hp : 1 ≤ p)
    (hω₁ : MemLp ω₁ (ENNReal.ofReal p)) (hω₂ : MemLp ω₂ (ENNReal.ofReal p)) (n : ℕ) :
    hilbertHApprox (fun z => ω₁ z + ω₂ z) n =
      fun z => hilbertHApprox ω₁ n z + hilbertHApprox ω₂ n z := by
  have htrunc : hilbertHTrunc (fun z => ω₁ z + ω₂ z) n =
      fun z => hilbertHTrunc ω₁ n z + hilbertHTrunc ω₂ n z := by
    funext z
    unfold hilbertHTrunc
    by_cases hz : z ∈ closedBall (0:ℂ) (n:ℝ)
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]; simp
  unfold hilbertHApprox
  rw [htrunc]
  exact t5Mollify_add hp (hilbertHTrunc_memLp hω₁ n) (hilbertHTrunc_memLp hω₂ n) n

/-- CANONICAL: linearity, unconditional at `p = 2` only (false unconditionally at other `p`,
per the junk-branch discipline: `hilbertH`'s choice-picked representative is only pinned on
`L_p`-existing inputs, so a statement mixing `L_p ∖ L²` has no proof). -/
theorem hilbertH_add_ae {ω₁ ω₂ : ℂ → ℂ} (h₁ : MemLp ω₁ 2) (h₂ : MemLp ω₂ 2) :
    hilbertH (ω₁ + ω₂) =ᵐ[volume] hilbertH ω₁ + hilbertH ω₂ := by
  have hp2 : (1:ℝ) < 2 := one_lt_two
  have hbound2 : ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal (2:ℝ)) volume ≤
        ENNReal.ofReal (1:ℝ) * eLpNorm φ (ENNReal.ofReal (2:ℝ)) volume := by
    intro φ hφ hc
    rw [ofReal_two_eq, ENNReal.ofReal_one, one_mul]
    exact (i4_eLpNorm_eq hφ hc).le
  have hω₁' : MemLp ω₁ (ENNReal.ofReal (2:ℝ)) := ofReal_two_eq ▸ h₁
  have hω₂' : MemLp ω₂ (ENNReal.ofReal (2:ℝ)) := ofReal_two_eq ▸ h₂
  have hω12' : MemLp (fun z => ω₁ z + ω₂ z) (ENNReal.ofReal (2:ℝ)) := ofReal_two_eq ▸ (h₁.add h₂)
  obtain ⟨hmem1, -, hconv1⟩ := hilbertH_tendsto_of_smooth_bound hp2 hbound2 ω₁ hω₁'
  obtain ⟨hmem2, -, hconv2⟩ := hilbertH_tendsto_of_smooth_bound hp2 hbound2 ω₂ hω₂'
  obtain ⟨hmem12, -, hconv12⟩ :=
    hilbertH_tendsto_of_smooth_bound hp2 hbound2 (fun z => ω₁ z + ω₂ z) hω12'
  have hsumconv : Tendsto (fun n => eLpNorm (fun z => hilbertHSmooth (hilbertHApprox
      (fun w => ω₁ w + ω₂ w) n) z - (hilbertH ω₁ z + hilbertH ω₂ z)) (ENNReal.ofReal (2:ℝ)))
      atTop (𝓝 0) := by
    have heqn : ∀ n, hilbertHSmooth (hilbertHApprox (fun w => ω₁ w + ω₂ w) n) =
        fun z => hilbertHSmooth (hilbertHApprox ω₁ n) z + hilbertHSmooth (hilbertHApprox ω₂ n) z := by
      intro n
      rw [hilbertHApprox_add hp2.le hω₁' hω₂']
      exact hilbertHSmooth_add (hilbertHApprox_contDiff hp2.le hω₁' n)
        (hilbertHApprox_hasCompactSupport ω₁ n) (hilbertHApprox_contDiff hp2.le hω₂' n)
        (hilbertHApprox_hasCompactSupport ω₂ n)
    have hbound : ∀ n, eLpNorm (fun z => hilbertHSmooth (hilbertHApprox (fun w => ω₁ w + ω₂ w) n) z -
        (hilbertH ω₁ z + hilbertH ω₂ z)) (ENNReal.ofReal (2:ℝ)) ≤
        eLpNorm (fun z => hilbertHSmooth (hilbertHApprox ω₁ n) z - hilbertH ω₁ z)
          (ENNReal.ofReal (2:ℝ)) +
        eLpNorm (fun z => hilbertHSmooth (hilbertHApprox ω₂ n) z - hilbertH ω₂ z)
          (ENNReal.ofReal (2:ℝ)) := by
      intro n
      have heq2 : (fun z => hilbertHSmooth (hilbertHApprox (fun w => ω₁ w + ω₂ w) n) z -
          (hilbertH ω₁ z + hilbertH ω₂ z)) =
          fun z => (hilbertHSmooth (hilbertHApprox ω₁ n) z - hilbertH ω₁ z) +
            (hilbertHSmooth (hilbertHApprox ω₂ n) z - hilbertH ω₂ z) := by
        funext z
        have hz := congrFun (heqn n) z
        rw [hz]; ring
      rw [heq2]
      exact eLpNorm_add_le (μ := volume)
        (f := fun z => hilbertHSmooth (hilbertHApprox ω₁ n) z - hilbertH ω₁ z)
        (g := fun z => hilbertHSmooth (hilbertHApprox ω₂ n) z - hilbertH ω₂ z) (by norm_num)
    have hsum := hconv1.add hconv2
    rw [add_zero] at hsum
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun n => bot_le) (Eventually.of_forall hbound)
  have hmemsum : MemLp (fun z => hilbertH ω₁ z + hilbertH ω₂ z) (ENNReal.ofReal (2:ℝ)) :=
    ofReal_two_eq ▸ (hmem1.add hmem2)
  have := hilbertH_indep_of_p (ω := fun w => ω₁ w + ω₂ w) hp2 hp2 hω12' hmem12 hconv12
    hmemsum hsumconv
  exact this

theorem t5Mollify_smul (c : ℂ) (ω : ℂ → ℂ) (n : ℕ) :
    t5Mollify (fun z => c * ω z) n = fun z => c * t5Mollify ω n z := by
  funext x
  show (∫ t, ContinuousLinearMap.lsmul ℝ ℝ ((lemma92Bump n).normed volume t) (c * ω (x - t))) =
      c * (∫ t, ContinuousLinearMap.lsmul ℝ ℝ ((lemma92Bump n).normed volume t) (ω (x - t)))
  have heq : (fun t => ContinuousLinearMap.lsmul ℝ ℝ ((lemma92Bump n).normed volume t)
      (c * ω (x - t))) =
      fun t => c * ContinuousLinearMap.lsmul ℝ ℝ ((lemma92Bump n).normed volume t) (ω (x - t)) := by
    funext t
    show ((lemma92Bump n).normed volume t : ℝ) • (c * ω (x - t)) =
        c * (((lemma92Bump n).normed volume t : ℝ) • ω (x - t))
    rw [Complex.real_smul, Complex.real_smul]
    ring
  rw [heq, integral_const_mul]

theorem hilbertHSmooth_smul (c : ℂ) {φ : ℂ → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hcφ : HasCompactSupport φ) :
    hilbertHSmooth (fun z => c * φ z) = fun z => c * hilbertHSmooth φ z := by
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => c * φ z) := contDiff_const.mul hφ
  have hcs : HasCompactSupport (fun z => c * φ z) := hcφ.mul_left
  have h1 := i1_hilbertH_eq_cauchyT_dz hφ hcφ
  have h2 := i1_hilbertH_eq_cauchyT_dz hcd hcs
  have hdzeq : dz (fun z => c * φ z) = fun z => c * dz φ z := by
    funext z
    unfold dz
    have hd : fderiv ℝ (fun w => c * φ w) z = c • fderiv ℝ φ z :=
      ((hφ.differentiable (by norm_num) z).hasFDerivAt.const_mul c).fderiv
    rw [hd]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hcauchysmul : cauchyT (fun z => c * dz φ z) = fun z => c * cauchyT (dz φ) z := by
    funext z
    unfold cauchyT
    have heq : (fun a : ℂ => (fun w => c * dz φ w) a / (a - z)) =
        fun a : ℂ => c * (dz φ a / (a - z)) := by
      funext a; ring
    rw [heq, integral_const_mul]
    ring
  funext z
  rw [h2.1, h1.1, hdzeq]
  exact congrFun hcauchysmul z

theorem hilbertHApprox_smul (c : ℂ) {ω : ℂ → ℂ} {p : ℝ} (hp : 1 ≤ p)
    (hω : MemLp ω (ENNReal.ofReal p)) (n : ℕ) :
    hilbertHApprox (fun z => c * ω z) n = fun z => c * hilbertHApprox ω n z := by
  have htrunc : hilbertHTrunc (fun z => c * ω z) n = fun z => c * hilbertHTrunc ω n z := by
    funext z
    unfold hilbertHTrunc
    by_cases hz : z ∈ closedBall (0:ℂ) (n:ℝ)
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]; simp
  unfold hilbertHApprox
  rw [htrunc]
  exact t5Mollify_smul c (hilbertHTrunc ω n) n

/-- CANONICAL: scalar linearity, unconditional at `p = 2` only. -/
theorem hilbertH_smul_ae {ω : ℂ → ℂ} (c : ℂ) (h : MemLp ω 2) :
    hilbertH (c • ω) =ᵐ[volume] c • hilbertH ω := by
  have hp2 : (1:ℝ) < 2 := one_lt_two
  have hbound2 : ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal (2:ℝ)) volume ≤
        ENNReal.ofReal (1:ℝ) * eLpNorm φ (ENNReal.ofReal (2:ℝ)) volume := by
    intro φ hφ hc
    rw [ofReal_two_eq, ENNReal.ofReal_one, one_mul]
    exact (i4_eLpNorm_eq hφ hc).le
  have hω' : MemLp ω (ENNReal.ofReal (2:ℝ)) := ofReal_two_eq ▸ h
  have hcω' : MemLp (fun z => c * ω z) (ENNReal.ofReal (2:ℝ)) := ofReal_two_eq ▸ (h.const_smul c)
  obtain ⟨hmem, -, hconv⟩ := hilbertH_tendsto_of_smooth_bound hp2 hbound2 ω hω'
  obtain ⟨hmemc, -, hconvc⟩ :=
    hilbertH_tendsto_of_smooth_bound hp2 hbound2 (fun z => c * ω z) hcω'
  have hscaledconv : Tendsto (fun n => eLpNorm (fun z => hilbertHSmooth (hilbertHApprox
      (fun w => c * ω w) n) z - c * hilbertH ω z) (ENNReal.ofReal (2:ℝ))) atTop (𝓝 0) := by
    have heqn : ∀ n, hilbertHSmooth (hilbertHApprox (fun w => c * ω w) n) =
        fun z => c * hilbertHSmooth (hilbertHApprox ω n) z := by
      intro n
      rw [hilbertHApprox_smul c hp2.le hω' n]
      exact hilbertHSmooth_smul c (hilbertHApprox_contDiff hp2.le hω' n)
        (hilbertHApprox_hasCompactSupport ω n)
    have heq2 : ∀ n, (fun z => hilbertHSmooth (hilbertHApprox (fun w => c * ω w) n) z -
        c * hilbertH ω z) = fun z => c * (hilbertHSmooth (hilbertHApprox ω n) z - hilbertH ω z) := by
      intro n
      funext z
      have hz := congrFun (heqn n) z
      rw [hz]; ring
    have hm : ∀ n, AEStronglyMeasurable
        (fun z => hilbertHSmooth (hilbertHApprox ω n) z - hilbertH ω z) volume := fun n =>
      ((i1_hilbertH_eq_cauchyT_dz (hilbertHApprox_contDiff hp2.le hω' n)
        (hilbertHApprox_hasCompactSupport ω n)).2.1.continuous.aestronglyMeasurable).sub
        hmem.aestronglyMeasurable
    have hnormeq : ∀ n, eLpNorm (fun z => c * (hilbertHSmooth (hilbertHApprox ω n) z -
        hilbertH ω z)) (ENNReal.ofReal (2:ℝ)) =
        ENNReal.ofReal ‖c‖ * eLpNorm (fun z => hilbertHSmooth (hilbertHApprox ω n) z - hilbertH ω z)
          (ENNReal.ofReal (2:ℝ)) := by
      intro n
      rw [show (fun z => c * (hilbertHSmooth (hilbertHApprox ω n) z - hilbertH ω z)) =
        c • (fun z => hilbertHSmooth (hilbertHApprox ω n) z - hilbertH ω z) from rfl,
        eLpNorm_const_smul]
      congr 1
      rw [← ofReal_norm]
    simp_rw [heq2, hnormeq]
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ‖c‖) hconv (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  have hmemc' : MemLp (fun z => c * hilbertH ω z) (ENNReal.ofReal (2:ℝ)) :=
    ofReal_two_eq ▸ (hmem.const_smul c)
  exact hilbertH_indep_of_p (ω := fun w => c * ω w) hp2 hp2 hcω' hmemc hconvc hmemc' hscaledconv

/-- The linchpin, corrected to `=ᵐ`: on `C₀^∞`, `hilbertH` agrees with the old pointwise formula
ALMOST EVERYWHERE — not exactly, since `Classical.choice` only pins a representative up to null
sets. Proved by exhibiting `hilbertHSmooth φ` ITSELF as a valid `L²` limit witness of the SAME
approximant sequence (via the isometry `i4_eLpNorm_eq` applied to `hilbertHApprox φ n - φ`, both
`C₀^∞`), then identifying it with whatever `hilbertH`'s choice actually picked via
`hilbertH_indep_of_p`. -/
theorem hilbertH_eq_ae_smooth {φ : ℂ → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    hilbertH φ =ᵐ[volume] hilbertHSmooth φ := by
  have hp2 : (1:ℝ) < 2 := one_lt_two
  have hbound2 : ∀ ψ : ℂ → ℂ, ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) ψ → HasCompactSupport ψ →
      eLpNorm (hilbertHSmooth ψ) (ENNReal.ofReal (2:ℝ)) volume ≤
        ENNReal.ofReal (1:ℝ) * eLpNorm ψ (ENNReal.ofReal (2:ℝ)) volume := by
    intro ψ hψ hcψ
    rw [ofReal_two_eq, ENNReal.ofReal_one, one_mul]
    exact (i4_eLpNorm_eq hψ hcψ).le
  have hφ' : MemLp φ (ENNReal.ofReal (2:ℝ)) :=
    ofReal_two_eq ▸ hφ.continuous.memLp_of_hasCompactSupport hc
  obtain ⟨hmem, -, hconv⟩ := hilbertH_tendsto_of_smooth_bound hp2 hbound2 φ hφ'
  have hφmem2 : MemLp (hilbertHSmooth φ) (ENNReal.ofReal (2:ℝ)) := by
    have hb := hbound2 φ hφ hc
    exact memLp_iff.mpr
      (lt_of_le_of_lt hb (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hφ'.eLpNorm_lt_top))
  have hselfconv : Tendsto (fun n => eLpNorm (fun z => hilbertHSmooth (hilbertHApprox φ n) z -
      hilbertHSmooth φ z) (ENNReal.ofReal (2:ℝ))) atTop (𝓝 0) := by
    have heq : ∀ n, eLpNorm (fun z => hilbertHSmooth (hilbertHApprox φ n) z - hilbertHSmooth φ z)
        (ENNReal.ofReal (2:ℝ)) = eLpNorm (fun z => hilbertHApprox φ n z - φ z)
        (ENNReal.ofReal (2:ℝ)) := by
      intro n
      have hsub := hilbertHSmooth_sub (hilbertHApprox_contDiff hp2.le hφ' n)
        (hilbertHApprox_hasCompactSupport φ n) hφ hc
      have hsubeq : (fun z => hilbertHSmooth (hilbertHApprox φ n) z - hilbertHSmooth φ z) =
          hilbertHSmooth (fun z => hilbertHApprox φ n z - φ z) := hsub.symm
      rw [hsubeq]
      have hcd : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun z => hilbertHApprox φ n z - φ z) :=
        (hilbertHApprox_contDiff hp2.le hφ' n).sub hφ
      have hcs : HasCompactSupport (fun z => hilbertHApprox φ n z - φ z) :=
        (hilbertHApprox_hasCompactSupport φ n).sub hc
      exact ofReal_two_eq ▸ (i4_eLpNorm_eq hcd hcs)
    simp_rw [heq]
    exact ofReal_two_eq ▸ hilbertHApprox_tendsto hp2.le hφ'
  exact hilbertH_indep_of_p (ω := φ) hp2 hp2 hφ' hmem hconv hφmem2 hselfconv

/-- A sequence in `ℝ≥0∞` tending to `0` is bounded above — extracted as a standalone, generic
lemma (proof-term elaboration against a small, fixed context) to avoid a pathological slowdown
this exact unification pattern hits inside a large accumulated proof context. -/
theorem ENNReal.bddAbove_of_tendsto_zero {f : ℕ → ℝ≥0∞} (hf : Tendsto f atTop (𝓝 0))
    (hffin : ∀ n, f n ≠ ⊤) : ∃ M, M ≠ ⊤ ∧ ∀ n, f n ≤ M := by
  have hev : ∀ᶠ n in atTop, f n ≤ 1 := (ENNReal.tendsto_nhds_zero.mp hf) 1 one_pos
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨M0, hM0def⟩ : ∃ M0 : ℝ≥0∞, Finset.sup (Finset.range N) f = M0 := ⟨_, rfl⟩
  have hM0fin : M0 ≠ ⊤ := by
    rw [← hM0def, Ne, Finset.sup_eq_top_iff, not_exists]
    intro n
    rw [not_and]
    exact fun _ => hffin n
  refine ⟨max 1 M0, ?_, fun n => ?_⟩
  · rw [Ne, max_eq_top, not_or]
    exact ⟨by norm_num, hM0fin⟩
  · rcases lt_or_ge n N with hn | hn
    · refine le_max_of_le_right ?_
      rw [← hM0def]
      exact Finset.le_sup (f := f) (Finset.mem_range.mpr hn)
    · exact le_max_of_le_left (hN n hn)

/-- If `b` ranges over `tsupport ω` and stays at distance `≥ ε` from `z`, then every point of
`Function.support (t5Mollify ω n)` is at distance `> ε - 1/(n+1)` from `z`: the mollifier only
moves mass by less than its radius `(lemma92Bump n).rOut = 1/(n+1)`. -/
theorem offsupp_dist_ge {ω : ℂ → ℂ} {z : ℂ} {ε : ℝ}
    (hεbound : ∀ b ∈ tsupport ω, ε ≤ ‖z - b‖) (n : ℕ) :
    ∀ ζ ∈ Function.support (t5Mollify ω n), ε - 1 / ((n : ℝ) + 1) < ‖z - ζ‖ := by
  intro ζ hζ
  have h3 := support_convolution_subset (f := (lemma92Bump n).normed volume) (g := ω)
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
  obtain ⟨a, ha, b, hb, hab⟩ := h3 hζ
  have ha' : ‖a‖ < (lemma92Bump n).rOut := by
    rw [(lemma92Bump n).support_normed_eq] at ha
    simpa [mem_ball_zero_iff] using ha
  have hrOut : (lemma92Bump n).rOut = 1 / ((n : ℝ) + 1) := rfl
  have hb' : b ∈ tsupport ω := subset_tsupport ω hb
  have hbz : ε ≤ ‖z - b‖ := hεbound b hb'
  rw [← hab]
  have htri : ‖z - b‖ - ‖a‖ ≤ ‖z - (a + b)‖ := by
    have h1 : z - (a + b) = (z - b) - a := by ring
    have h2 : ‖z - b‖ - ‖a‖ ≤ ‖(z - b) - a‖ := by
      linarith [norm_sub_norm_le (z - b) a]
    rwa [h1]
  rw [hrOut] at ha'
  linarith [htri, hbz, ha']

/-- If `ψ ∈ C₀^∞` and `z` stays at distance `≥ r₀ > 0` from `tsupport ψ`, the principal value
`hilbertHSmooth ψ z` is exactly the plain (non-singular) kernel integral over all of `ℂ`: the
truncation radius `r` eventually (as `r → 0⁺`) captures all of `tsupport ψ`, making the truncated
integral constant. -/
theorem offsupp_hilbertHSmooth_eq_integral {ψ : ℂ → ℂ}
    {z : ℂ} {r₀ : ℝ} (hbd : ∀ ζ ∈ tsupport ψ, r₀ ≤ ‖ζ - z‖) (hr₀ : 0 < r₀) :
    hilbertHSmooth ψ z = ∫ ζ, -(1 / π : ℂ) * ψ ζ / (ζ - z) ^ 2 := by
  have hconstval : ∀ r ∈ Set.Ioo (0:ℝ) r₀,
      (∫ ζ in {ζ : ℂ | r < ‖ζ - z‖}, ψ ζ / (ζ - z) ^ 2) = ∫ ζ, ψ ζ / (ζ - z) ^ 2 := by
    intro r hr
    have heq := setIntegral_eq_of_subset_of_forall_diff_eq_zero (f := fun ζ => ψ ζ / (ζ - z) ^ 2)
      (μ := volume) MeasurableSet.univ (subset_univ {ζ : ℂ | r < ‖ζ - z‖})
      (fun ζ hζ => by
        have h1 : ‖ζ - z‖ ≤ r := by
          replace hζ : ζ ∈ univ ∧ ‖ζ - z‖ ≤ r := ⟨hζ.1, not_lt.mp hζ.2⟩
          exact hζ.2
        have hζnot : ζ ∉ tsupport ψ := fun hmem => by linarith [hbd ζ hmem, hr.2]
        rw [image_eq_zero_of_notMem_tsupport hζnot]; simp)
    rw [setIntegral_univ] at heq
    exact heq.symm
  have hev : (fun r => -(1/π : ℂ) * ∫ ζ in {ζ : ℂ | r < ‖ζ - z‖}, ψ ζ / (ζ - z) ^ 2) =ᶠ[𝓝[>] (0:ℝ)]
      (fun _ => -(1/π : ℂ) * ∫ ζ, ψ ζ / (ζ - z) ^ 2) := by
    filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr
    rw [hconstval r hr]
  have hlim : hilbertHSmooth ψ z = -(1/π : ℂ) * ∫ ζ, ψ ζ / (ζ - z) ^ 2 :=
    (tendsto_const_nhds.congr' hev.symm).limUnder_eq
  rw [hlim, ← integral_const_mul]
  congr 1
  funext ζ
  ring

/-- Global `L²` convergence of `f n → g` descends to `L¹` convergence on any fixed finite-measure
set `D` (Hölder on the finite-measure restriction, then `eLpNorm_mono_measure` to the global
bound). -/
theorem offsupp_eLpNorm_one_restrict_tendsto_zero {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀ n, AEStronglyMeasurable (f n) volume) (hg : AEStronglyMeasurable g volume)
    (hconv : Tendsto (fun n => eLpNorm (f n - g) 2 volume) atTop (𝓝 0))
    {D : Set ℂ} (hDfin : volume D ≠ ⊤) :
    Tendsto (fun n => eLpNorm (f n - g) 1 (volume.restrict D)) atTop (𝓝 0) := by
  haveI : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.2 hDfin
  have hHolder : ∀ n, eLpNorm (f n - g) 1 (volume.restrict D) ≤
      eLpNorm (f n - g) 2 (volume.restrict D) * (volume D) ^ (1 - 1/(2:ℝ)) := by
    intro n
    have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict D)
      (by norm_num : (1:ℝ≥0∞) ≤ 2) ((hf n).sub hg).restrict
    simpa [Measure.restrict_apply_univ] using h1
  have hbound : ∀ n, eLpNorm (f n - g) 1 (volume.restrict D) ≤
      eLpNorm (f n - g) 2 volume * (volume D) ^ (1 - 1/(2:ℝ)) := by
    intro n
    refine (hHolder n).trans ?_
    exact mul_le_mul_of_nonneg_right (eLpNorm_mono_measure _ Measure.restrict_le_self) (by positivity)
  have hRHS : Tendsto (fun n => eLpNorm (f n - g) 2 volume * (volume D) ^ (1 - 1/(2:ℝ)))
      atTop (𝓝 0) := by
    have hbfin : (volume D) ^ (1 - 1/(2:ℝ)) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) hDfin
    have := ENNReal.Tendsto.mul_const hconv (Or.inr hbfin)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hRHS
    (Eventually.of_forall fun n => bot_le) (Eventually.of_forall hbound)

/-- If `φ = 0` (as a function) and `φ ∈ L²`, then `hilbertH φ` vanishes a.e. — `subst` (not
`rw ... at`) is load-bearing here: rewriting `φ → 0` inside an already-obtained hypothesis whose
type mentions `hilbertH φ` triggers a pathological `whnf` blow-up (confirmed in isolation);
substituting the variable before ever invoking `hilbertH_memLp_two` avoids it entirely. -/
theorem offsupp_hilbertH_ae_zero_of_eq_zero {φ : ℂ → ℂ} (hφ2 : MemLp φ 2 volume)
    (hφ0 : φ = 0) : hilbertH φ =ᵐ[volume] 0 := by
  subst hφ0
  obtain ⟨hmemV, heqV⟩ := hilbertH_memLp_two hφ2
  simp only [eLpNorm_zero] at heqV
  exact (eLpNorm_eq_zero_iff (by norm_num)).mp heqV

set_option maxHeartbeats 1000000 in
/-- CANONICAL: the off-support integral formula, a.e. on the exterior (owner -5d; consumer -d4's
S3). Frozen at `MemLp φ 2` (not a boundedness hypothesis): -d4's CZ bad parts are only in
L¹ ∩ L², not bounded. Proved via: unconditional L² convergence of the approximants
(`i4_eLpNorm_eq`, no wall dependence) plus `tendstoInMeasure_of_tendsto_eLpNorm` for an
a.e.-convergent subsequence; the `limUnder`-eventually-constant argument
(`offsupp_hilbertHSmooth_eq_integral`) identifying `hilbertHSmooth` of each approximant, once its
support clears a shrinking neighbourhood of `z` (`offsupp_dist_ge`, via the mollifier's radius
`1/(n+1) → 0`), with the plain kernel integral against that approximant; `φ ∈ L¹`
via `MemLp.mono_exponent` on the finite-measure `tsupport φ` (Cauchy–Schwarz, not a sup
bound); and a further Cauchy-Schwarz/Hölder bound
(`offsupp_eLpNorm_one_restrict_tendsto_zero`) on a fixed compact set showing the kernel integral
against the approximants converges to the one against `φ` itself. Does NOT use
`zygmund_calderon`, `hilbertH_memLp`, `hilbertNorm*`, or `hilbertH_exists_seq_tendsto_ae` --
single-wall-clean. -/
theorem hilbertH_eq_integral_ae_off_support {φ : ℂ → ℂ} (hφm : Measurable φ)
    (hφ2 : MemLp φ 2 volume) (hφc : HasCompactSupport φ) :
    ∀ᵐ z ∂(volume.restrict (tsupport φ)ᶜ),
      hilbertH φ z = ∫ ζ, -(1 / π : ℂ) * φ ζ / (ζ - z) ^ 2 := by
  have hφ2' : MemLp φ (ENNReal.ofReal (2:ℝ)) := ofReal_two_eq ▸ hφ2
  have hp2 : (1:ℝ) < 2 := one_lt_two
  have hbound2 : ∀ ψ : ℂ → ℂ, ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) ψ → HasCompactSupport ψ →
      eLpNorm (hilbertHSmooth ψ) (ENNReal.ofReal (2:ℝ)) volume ≤
        ENNReal.ofReal (1:ℝ) * eLpNorm ψ (ENNReal.ofReal (2:ℝ)) volume := by
    intro ψ hψ hcψ
    rw [ofReal_two_eq, ENNReal.ofReal_one, one_mul]
    exact (i4_eLpNorm_eq hψ hcψ).le
  obtain ⟨hmem, -, hconv⟩ := hilbertH_tendsto_of_smooth_bound hp2 hbound2 φ hφ2'
  rw [ofReal_two_eq] at hmem hconv
  have hpne0 : (2:ℝ≥0∞) ≠ 0 := by norm_num
  have hfmeas : ∀ n, AEStronglyMeasurable (fun z => hilbertHSmooth (hilbertHApprox φ n) z) volume :=
    fun n => (i1_hilbertH_eq_cauchyT_dz (hilbertHApprox_contDiff hp2.le hφ2' n)
      (hilbertHApprox_hasCompactSupport φ n)).2.1.continuous.aestronglyMeasurable
  have htm : TendstoInMeasure volume (fun n z => hilbertHSmooth (hilbertHApprox φ n) z) atTop
      (hilbertH φ) := tendstoInMeasure_of_tendsto_eLpNorm hpne0 hconv
  obtain ⟨ns, hnsmono, hnsae⟩ := htm.exists_seq_tendsto_ae
  obtain ⟨R₀, hR₀⟩ := hφc.isCompact.isBounded.subset_closedBall (0:ℂ)
  set R₀' : ℝ := max R₀ 0 with hR₀'def
  have hR₀' : tsupport φ ⊆ closedBall (0:ℂ) R₀' :=
    hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge R₀'
  have htruncEq : ∀ n : ℕ, N₀ ≤ n → hilbertHTrunc φ n = φ := by
    intro n hn
    funext x
    unfold hilbertHTrunc
    by_cases hx : x ∈ closedBall (0:ℂ) (n:ℝ)
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      symm
      apply image_eq_zero_of_notMem_tsupport
      intro hxsupp
      apply hx
      have h1 := hR₀' hxsupp
      rw [mem_closedBall_zero_iff] at h1 ⊢
      exact h1.trans (hN₀.trans (by exact_mod_cast hn))
  have happroxEq : ∀ n : ℕ, N₀ ≤ n → hilbertHApprox φ n = t5Mollify φ n := by
    intro n hn; unfold hilbertHApprox; rw [htruncEq n hn]
  have hasupp0 : ∀ n : ℕ, N₀ ≤ n →
      Function.support (hilbertHApprox φ n) ⊆ closedBall (0:ℂ) (R₀'+1) := by
    intro n hn
    rw [happroxEq n hn]
    apply t5Mollify_support_subset
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxsupp
    have h1 := hR₀' hxsupp
    rw [mem_closedBall_zero_iff] at h1
    linarith
  by_cases hne : (tsupport φ).Nonempty
  · rw [ae_restrict_iff' (isClosed_tsupport φ).isOpen_compl.measurableSet]
    filter_upwards [hnsae] with z hzconv hzmem
    set ε : ℝ := Metric.infDist z (tsupport φ) with hεdef
    have hεpos : 0 < ε := (isClosed_tsupport φ).notMem_iff_infDist_pos hne |>.1 hzmem
    have hεbound : ∀ b ∈ tsupport φ, ε ≤ ‖z - b‖ := by
      intro b hb
      have h1 := infDist_le_dist_of_mem hb (x := z)
      rwa [dist_eq_norm] at h1
    set δ : ℝ := ε / 2 with hδdef
    have hδpos : 0 < δ := by positivity
    obtain ⟨N₁, hN₁⟩ := exists_nat_gt (1/δ)
    set N : ℕ := max N₀ N₁ with hNdef
    have hNN₀ : N₀ ≤ N := le_max_left _ _
    have hNN₁ : N₁ ≤ N := le_max_right _ _
    have hvanishA : ∀ n : ℕ, N ≤ n → ∀ ζ, ‖ζ - z‖ < δ → hilbertHApprox φ n ζ = 0 := by
      intro n hn ζ hζ
      by_contra hne'
      have hnN₀ : N₀ ≤ n := hNN₀.trans hn
      have hnN₁ : N₁ ≤ n := hNN₁.trans hn
      have hζsupp : ζ ∈ Function.support (hilbertHApprox φ n) := hne'
      rw [happroxEq n hnN₀] at hζsupp
      have hdist := offsupp_dist_ge hεbound n ζ hζsupp
      have h1rout : 1 / ((n:ℝ)+1) < δ := by
        have hn1 : (N₁:ℝ) ≤ (n:ℝ) := by exact_mod_cast hnN₁
        have hgt : 1/δ < (n:ℝ) + 1 := by linarith [hN₁]
        have hNpos : (0:ℝ) < (n:ℝ) + 1 := by positivity
        rw [div_lt_iff₀ hδpos] at hgt
        rw [div_lt_iff₀ hNpos]
        linarith [hgt]
      have hzz : ‖z - ζ‖ = ‖ζ - z‖ := norm_sub_rev z ζ
      rw [hzz] at hdist
      linarith [hdist, h1rout, hζ]
    have hvanishB : ∀ ζ, ‖ζ - z‖ < δ → φ ζ = 0 := by
      intro ζ hζ
      by_contra hne'
      have hζsupp : ζ ∈ tsupport φ := subset_tsupport φ hne'
      have h1 := hεbound ζ hζsupp
      have hzz : ‖z - ζ‖ = ‖ζ - z‖ := norm_sub_rev z ζ
      rw [hzz] at h1
      linarith [h1, hζ]
    set D : Set ℂ := closedBall (0:ℂ) (R₀'+1) \ ball z δ with hDdef
    have hDcompact : IsCompact D :=
      (isCompact_closedBall (0:ℂ) (R₀'+1)).inter_right isOpen_ball.isClosed_compl
    have hDfin : volume D ≠ ⊤ := hDcompact.measure_lt_top.ne
    have hDmeas : MeasurableSet D := measurableSet_closedBall.diff measurableSet_ball
    have hdiffsupp : ∀ n : ℕ, N ≤ n → ∀ ζ, ζ ∉ D → hilbertHApprox φ n ζ - φ ζ = 0 := by
      intro n hn ζ hζ
      rw [hDdef, mem_diff, not_and_or, not_not] at hζ
      rcases hζ with h1 | h2
      · have hout1 : hilbertHApprox φ n ζ = 0 := by
          by_contra hc; exact h1 (hasupp0 n (hNN₀.trans hn) (Function.mem_support.mpr hc))
        have hout2 : φ ζ = 0 := by
          by_contra hc
          exact h1 (closedBall_subset_closedBall (by linarith : R₀' ≤ R₀' + 1)
            (hR₀' (subset_tsupport φ (Function.mem_support.mpr hc))))
        rw [hout1, hout2]; ring
      · have h2' : ‖ζ - z‖ < δ := by rw [mem_ball, dist_eq_norm] at h2; exact h2
        rw [hvanishA n hn ζ h2', hvanishB ζ h2']; ring
    have hL1 : Tendsto (fun n => eLpNorm (hilbertHApprox φ n - φ) 1 (volume.restrict D))
        atTop (𝓝 0) := by
      apply offsupp_eLpNorm_one_restrict_tendsto_zero
        (fun n => (hilbertHApprox_contDiff hp2.le hφ2' n).continuous.aestronglyMeasurable)
        hφ2.aestronglyMeasurable ?_ hDfin
      have h1 := hilbertHApprox_tendsto hp2.le hφ2'
      rw [ofReal_two_eq] at h1
      exact h1
    have hformula : ∀ n : ℕ, N ≤ n →
        hilbertHSmooth (hilbertHApprox φ n) z =
          ∫ ζ, -(1/π:ℂ) * hilbertHApprox φ n ζ / (ζ - z)^2 := by
      intro n hn
      apply offsupp_hilbertHSmooth_eq_integral (r₀ := δ) ?_ hδpos
      intro ζ hζ
      have hsupp_ball : Function.support (hilbertHApprox φ n) ⊆ {ζ : ℂ | δ ≤ ‖ζ - z‖} := by
        intro ζ' hζ'm
        rw [mem_setOf_eq]
        by_contra hcon
        rw [not_le] at hcon
        exact hζ'm (hvanishA n hn ζ' hcon)
      have hclosed : IsClosed {ζ : ℂ | δ ≤ ‖ζ - z‖} :=
        isClosed_le continuous_const (continuous_id.sub continuous_const).norm
      have htsupp_ball : tsupport (hilbertHApprox φ n) ⊆ {ζ : ℂ | δ ≤ ‖ζ - z‖} := by
        calc closure (Function.support (hilbertHApprox φ n))
            ⊆ closure {ζ : ℂ | δ ≤ ‖ζ - z‖} := closure_mono hsupp_ball
          _ = {ζ : ℂ | δ ≤ ‖ζ - z‖} := hclosed.closure_eq
      exact htsupp_ball hζ
    have hnormeq : ∀ X : ℂ, ∀ ζ : ℂ, ‖-(1/π:ℂ) * X / (ζ - z)^2‖ = (1/π) * ‖X‖ / ‖ζ - z‖^2 := by
      intro X ζ
      rw [norm_div, norm_mul, norm_neg, norm_pow, norm_div, norm_one,
        Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hφIntOn : IntegrableOn φ (tsupport φ) volume := by
      haveI : IsFiniteMeasure (volume.restrict (tsupport φ)) :=
        isFiniteMeasure_restrict.2 hφc.isCompact.measure_lt_top.ne
      exact memLp_one_iff_integrable.mp
        ((hφ2.restrict (tsupport φ)).mono_exponent (by norm_num : (1:ℝ≥0∞) ≤ 2))
    have hφInt : Integrable φ volume :=
      hφIntOn.integrable_of_forall_notMem_eq_zero (fun ζ hζ => image_eq_zero_of_notMem_tsupport hζ)
    have hsub1 : Function.support (fun ζ => -(1/π:ℂ) * φ ζ / (ζ - z)^2) ⊆ Function.support φ := by
      intro ζ hζ
      rw [Function.mem_support] at hζ ⊢
      intro h0; apply hζ; rw [h0]; simp
    have hφkercs : HasCompactSupport (fun ζ => -(1/π:ℂ) * φ ζ / (ζ - z)^2) := hφc.mono hsub1
    have hφkermeas : AEStronglyMeasurable (fun ζ => -(1/π:ℂ) * φ ζ / (ζ - z)^2) volume :=
      (aestronglyMeasurable_const.mul hφm.aestronglyMeasurable).div₀
        (((continuous_id.sub continuous_const).pow 2).aestronglyMeasurable)
    have hφkerbound : ∀ ζ, ‖-(1/π:ℂ) * φ ζ / (ζ - z)^2‖ ≤ (1/π)/ε^2 * ‖φ ζ‖ := by
      intro ζ
      rcases eq_or_ne (φ ζ) 0 with h0 | h0
      · rw [hnormeq, h0]; simp
      · have hζsupp : ζ ∈ tsupport φ := subset_tsupport φ h0
        have hεζ : ε ≤ ‖ζ - z‖ := by
          have := hεbound ζ hζsupp; rwa [norm_sub_rev] at this
        rw [hnormeq]
        have hstep : (1/π) * ‖φ ζ‖ / ‖ζ - z‖^2 ≤ (1/π) * ‖φ ζ‖ / ε^2 := by gcongr
        have heq : (1/π) * ‖φ ζ‖ / ε^2 = (1/π)/ε^2 * ‖φ ζ‖ := by ring
        rw [← heq]; exact hstep
    have hφkerInt : Integrable (fun ζ => -(1/π:ℂ) * φ ζ / (ζ - z)^2) volume :=
      Integrable.mono' (hφInt.norm.const_mul ((1/π)/ε^2)) hφkermeas (Eventually.of_forall hφkerbound)
    have hCnex : ∀ n, ∃ C, ∀ ζ, ‖hilbertHApprox φ n ζ‖ ≤ C := fun n =>
      (hilbertHApprox_hasCompactSupport φ n).exists_bound_of_continuous
        (hilbertHApprox_contDiff hp2.le hφ2' n).continuous
    have hsub2 : ∀ n, Function.support (fun ζ => -(1/π:ℂ) * hilbertHApprox φ n ζ / (ζ - z)^2) ⊆
        Function.support (hilbertHApprox φ n) := by
      intro n ζ hζ
      rw [Function.mem_support] at hζ ⊢
      intro h0; apply hζ; rw [h0]; simp
    have happroxkercs : ∀ n,
        HasCompactSupport (fun ζ => -(1/π:ℂ) * hilbertHApprox φ n ζ / (ζ - z)^2) :=
      fun n => (hilbertHApprox_hasCompactSupport φ n).mono (hsub2 n)
    have happroxkermeas : ∀ n,
        AEStronglyMeasurable (fun ζ => -(1/π:ℂ) * hilbertHApprox φ n ζ / (ζ - z)^2) volume :=
      fun n => (aestronglyMeasurable_const.mul
        (hilbertHApprox_contDiff hp2.le hφ2' n).continuous.aestronglyMeasurable).div₀
        (((continuous_id.sub continuous_const).pow 2).aestronglyMeasurable)
    have happroxkerInt : ∀ n, N ≤ n →
        Integrable (fun ζ => -(1/π:ℂ) * hilbertHApprox φ n ζ / (ζ - z)^2) volume := by
      intro n hn
      obtain ⟨Cn, hCn⟩ := hCnex n
      have hCnnn : 0 ≤ Cn := (norm_nonneg _).trans (hCn z)
      have hbound : ∀ ζ, ‖-(1/π:ℂ) * hilbertHApprox φ n ζ / (ζ - z)^2‖ ≤ (1/π) * Cn / δ^2 := by
        intro ζ
        rcases lt_or_ge ‖ζ - z‖ δ with hζ | hζ
        · rw [hnormeq, hvanishA n hn ζ hζ]; simp; positivity
        · rw [hnormeq]
          have h1 : (1/π) * ‖hilbertHApprox φ n ζ‖ / ‖ζ - z‖^2 ≤ (1/π) * Cn / ‖ζ - z‖^2 := by
            gcongr; exact hCn ζ
          have h2 : (1/π) * Cn / ‖ζ - z‖^2 ≤ (1/π) * Cn / δ^2 := by gcongr
          exact h1.trans h2
      exact memLp_one_iff_integrable.mp ((happroxkercs n).memLp_of_bound (happroxkermeas n)
        ((1/π) * Cn / δ^2) (Eventually.of_forall hbound))
    have happroxInt : ∀ n, Integrable (hilbertHApprox φ n) volume := fun n =>
      (hilbertHApprox_contDiff hp2.le hφ2' n).continuous.integrable_of_hasCompactSupport
        (hilbertHApprox_hasCompactSupport φ n)
    have hIntOnD : ∀ n, IntegrableOn (fun ζ => hilbertHApprox φ n ζ - φ ζ) D volume :=
      fun n => ((happroxInt n).sub hφInt).mono_measure Measure.restrict_le_self
    have hDrestrictNeTop : ∀ n, eLpNorm (hilbertHApprox φ n - φ) 1 (volume.restrict D) ≠ ⊤ :=
      fun n => (memLp_one_iff_integrable.2 (hIntOnD n)).eLpNorm_ne_top
    have hdiffbound : ∀ n, N ≤ n →
        ‖(∫ ζ, -(1/π:ℂ) * hilbertHApprox φ n ζ / (ζ - z)^2) -
          ∫ ζ, -(1/π:ℂ) * φ ζ / (ζ - z)^2‖ ≤
          (1/(π*δ^2)) * (eLpNorm (hilbertHApprox φ n - φ) 1 (volume.restrict D)).toReal := by
      intro n hn
      rw [← integral_sub (happroxkerInt n hn) hφkerInt]
      have heqintegrand : (fun ζ => -(1/π:ℂ) * hilbertHApprox φ n ζ / (ζ - z)^2 -
          -(1/π:ℂ) * φ ζ / (ζ - z)^2) =
          fun ζ => -(1/π:ℂ) * (hilbertHApprox φ n ζ - φ ζ) / (ζ - z)^2 := by
        funext ζ; ring
      rw [heqintegrand]
      have hsupp3 : ∀ ζ, ζ ∉ D → -(1/π:ℂ) * (hilbertHApprox φ n ζ - φ ζ) / (ζ - z)^2 = 0 := by
        intro ζ hζ; rw [hdiffsupp n hn ζ hζ]; simp
      have hkerdiffInt : Integrable (fun ζ => -(1/π:ℂ) * (hilbertHApprox φ n ζ - φ ζ) / (ζ - z)^2)
          volume := heqintegrand ▸ ((happroxkerInt n hn).sub hφkerInt)
      have hSetInt : (∫ ζ, -(1/π:ℂ) * (hilbertHApprox φ n ζ - φ ζ) / (ζ - z)^2) =
          ∫ ζ in D, -(1/π:ℂ) * (hilbertHApprox φ n ζ - φ ζ) / (ζ - z)^2 := by
        rw [← setIntegral_univ (f := fun ζ => -(1/π:ℂ) * (hilbertHApprox φ n ζ - φ ζ) / (ζ - z)^2)]
        exact setIntegral_eq_of_subset_of_forall_diff_eq_zero MeasurableSet.univ (subset_univ D)
          (fun ζ hζ => hsupp3 ζ hζ.2)
      rw [hSetInt]
      have h1 : ‖∫ ζ in D, -(1/π:ℂ) * (hilbertHApprox φ n ζ - φ ζ) / (ζ - z)^2‖ ≤
          ∫ ζ in D, ‖-(1/π:ℂ) * (hilbertHApprox φ n ζ - φ ζ) / (ζ - z)^2‖ :=
        norm_integral_le_integral_norm _
      have h2 : (∫ ζ in D, ‖-(1/π:ℂ) * (hilbertHApprox φ n ζ - φ ζ) / (ζ - z)^2‖) ≤
          ∫ ζ in D, (1/(π*δ^2)) * ‖hilbertHApprox φ n ζ - φ ζ‖ := by
        apply setIntegral_mono_on
        · exact hkerdiffInt.norm.mono_measure Measure.restrict_le_self
        · exact ((hIntOnD n).norm.const_mul (1/(π*δ^2)))
        · exact hDmeas
        · intro ζ hζD
          rw [mem_diff, mem_ball, dist_eq_norm, not_lt] at hζD
          have hζbig : δ ≤ ‖ζ - z‖ := hζD.2
          rw [hnormeq]
          have heq : (1/π) * ‖hilbertHApprox φ n ζ - φ ζ‖ / δ^2 =
              (1/(π*δ^2)) * ‖hilbertHApprox φ n ζ - φ ζ‖ := by ring
          rw [← heq]
          gcongr
      have h3 : (∫ ζ in D, (1/(π*δ^2)) * ‖hilbertHApprox φ n ζ - φ ζ‖) =
          (1/(π*δ^2)) * ∫ ζ in D, ‖hilbertHApprox φ n ζ - φ ζ‖ := integral_const_mul _ _
      have h4 : (∫ ζ in D, ‖hilbertHApprox φ n ζ - φ ζ‖) =
          (eLpNorm (hilbertHApprox φ n - φ) 1 (volume.restrict D)).toReal := by
        have hnn : 0 ≤ᵐ[volume.restrict D] (fun ζ => ‖hilbertHApprox φ n ζ - φ ζ‖) :=
          Eventually.of_forall (fun ζ => norm_nonneg _)
        have hconv := ofReal_integral_eq_lintegral_ofReal (hIntOnD n).norm hnn
        have henorm : (∫⁻ ζ, ENNReal.ofReal ‖hilbertHApprox φ n ζ - φ ζ‖ ∂(volume.restrict D)) =
            ∫⁻ ζ, ‖(hilbertHApprox φ n - φ) ζ‖ₑ ∂(volume.restrict D) := by
          refine lintegral_congr fun ζ => ?_
          rw [← ofReal_norm]
          rfl
        rw [henorm] at hconv
        have hL1nn : 0 ≤ ∫ ζ in D, ‖hilbertHApprox φ n ζ - φ ζ‖ :=
          setIntegral_nonneg hDmeas (fun x _ => norm_nonneg _)
        show ∫ ζ in D, ‖hilbertHApprox φ n ζ - φ ζ‖ = _
        rw [eLpNorm_one_eq_lintegral_enorm (f := hilbertHApprox φ n - φ)
          (hIntOnD n).aestronglyMeasurable, ← hconv, ENNReal.toReal_ofReal hL1nn]
      calc ‖(∫ ζ in D, -(1/π:ℂ) * (hilbertHApprox φ n ζ - φ ζ) / (ζ - z)^2)‖
          ≤ ∫ ζ in D, ‖-(1/π:ℂ) * (hilbertHApprox φ n ζ - φ ζ) / (ζ - z)^2‖ := h1
        _ ≤ ∫ ζ in D, (1/(π*δ^2)) * ‖hilbertHApprox φ n ζ - φ ζ‖ := h2
        _ = (1/(π*δ^2)) * ∫ ζ in D, ‖hilbertHApprox φ n ζ - φ ζ‖ := h3
        _ = (1/(π*δ^2)) * (eLpNorm (hilbertHApprox φ n - φ) 1 (volume.restrict D)).toReal := by
            rw [h4]
    have hRHStendsto : Tendsto (fun n => (1/(π*δ^2)) *
        (eLpNorm (hilbertHApprox φ n - φ) 1 (volume.restrict D)).toReal) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => (eLpNorm (hilbertHApprox φ n - φ) 1 (volume.restrict D)).toReal)
          atTop (𝓝 0) := by
        have := (ENNReal.tendsto_toReal_iff hDrestrictNeTop ENNReal.zero_ne_top).mpr hL1
        simpa using this
      have := h1.const_mul (1/(π*δ^2))
      simpa using this
    have hkey : Tendsto (fun n => hilbertHSmooth (hilbertHApprox φ n) z) atTop
        (𝓝 (∫ ζ, -(1/π:ℂ) * φ ζ / (ζ - z)^2)) := by
      have heqeach : ∀ᶠ n in atTop, hilbertHSmooth (hilbertHApprox φ n) z =
          ∫ ζ, -(1/π:ℂ) * hilbertHApprox φ n ζ / (ζ - z)^2 :=
        Filter.eventually_atTop.2 ⟨N, hformula⟩
      rw [Filter.tendsto_congr' heqeach]
      have hdiffzero : Tendsto (fun n => (∫ ζ, -(1/π:ℂ) * hilbertHApprox φ n ζ / (ζ - z)^2) -
          ∫ ζ, -(1/π:ℂ) * φ ζ / (ζ - z)^2) atTop (𝓝 0) :=
        squeeze_zero_norm' (Filter.eventually_atTop.2 ⟨N, hdiffbound⟩) hRHStendsto
      have heq2 : (fun n => ∫ ζ, -(1/π:ℂ) * hilbertHApprox φ n ζ / (ζ - z)^2) =
          fun n => ((∫ ζ, -(1/π:ℂ) * hilbertHApprox φ n ζ / (ζ - z)^2) -
            ∫ ζ, -(1/π:ℂ) * φ ζ / (ζ - z)^2) + ∫ ζ, -(1/π:ℂ) * φ ζ / (ζ - z)^2 := by
        funext n; ring
      rw [heq2]
      have hadd : Tendsto (fun n => ((∫ ζ, -(1/π:ℂ) * hilbertHApprox φ n ζ / (ζ - z)^2) -
          ∫ ζ, -(1/π:ℂ) * φ ζ / (ζ - z)^2) + ∫ ζ, -(1/π:ℂ) * φ ζ / (ζ - z)^2)
          atTop (𝓝 (0 + ∫ ζ, -(1/π:ℂ) * φ ζ / (ζ - z)^2)) :=
        hdiffzero.add tendsto_const_nhds
      rwa [zero_add] at hadd
    exact tendsto_nhds_unique hzconv (hkey.comp hnsmono.tendsto_atTop)
  · have hφ0 : φ = 0 := by
      funext x
      exact image_eq_zero_of_notMem_tsupport (by
        rw [Set.not_nonempty_iff_eq_empty] at hne; rw [hne]; simp)
    have hV0 : hilbertH φ =ᵐ[volume] 0 := offsupp_hilbertH_ae_zero_of_eq_zero hφ2 hφ0
    rw [ae_restrict_iff' (isClosed_tsupport φ).isOpen_compl.measurableSet]
    filter_upwards [hV0] with z hz0
    intro _
    rw [hz0, hφ0]
    simp




theorem hilbertHApprox_sub {ω₁ ω₂ : ℂ → ℂ} {p : ℝ} (hp : 1 ≤ p)
    (hω₁ : MemLp ω₁ (ENNReal.ofReal p)) (hω₂ : MemLp ω₂ (ENNReal.ofReal p)) (n : ℕ) :
    hilbertHApprox (fun z => ω₁ z - ω₂ z) n =
      fun z => hilbertHApprox ω₁ n z - hilbertHApprox ω₂ n z := by
  have htrunc : hilbertHTrunc (fun z => ω₁ z - ω₂ z) n =
      fun z => hilbertHTrunc ω₁ n z - hilbertHTrunc ω₂ n z := by
    funext z
    unfold hilbertHTrunc
    by_cases hz : z ∈ closedBall (0:ℂ) (n:ℝ)
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]; simp
  unfold hilbertHApprox
  rw [htrunc]
  exact t5Mollify_sub hp (hilbertHTrunc_memLp hω₁ n) (hilbertHTrunc_memLp hω₂ n) n

/-- CONDITIONAL linearity at general `p` (used by consumers who already have a smooth bound
in hand, e.g. `zygmund_calderon` at their own `p`): same statement as `hilbertH_add_ae` but for
general `p`, given `hbound`. This is what `phiMap_sub_bound` (S12) and `thm11_1` (S11) — both
originally consuming `hilbertH_sub_ae` at `p > 2` — get instead, instantiated with
`hbound := zygmund_calderon hp`, tainted by exactly that one sorry as before. -/
theorem hilbertH_sub_ae_of_smooth_bound {p A : ℝ} (hp : 1 < p)
    (hbound : ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal A * eLpNorm φ (ENNReal.ofReal p) volume)
    {ω₁ ω₂ : ℂ → ℂ} (hω₁ : MemLp ω₁ (ENNReal.ofReal p)) (hω₂ : MemLp ω₂ (ENNReal.ofReal p)) :
    hilbertH (fun z => ω₁ z - ω₂ z) =ᵐ[volume]
      fun z => hilbertH ω₁ z - hilbertH ω₂ z := by
  obtain ⟨hmem1, -, hconv1⟩ := hilbertH_tendsto_of_smooth_bound hp hbound ω₁ hω₁
  obtain ⟨hmem2, -, hconv2⟩ := hilbertH_tendsto_of_smooth_bound hp hbound ω₂ hω₂
  have hω12 : MemLp (fun z => ω₁ z - ω₂ z) (ENNReal.ofReal p) := hω₁.sub hω₂
  obtain ⟨hmem12, -, hconv12⟩ :=
    hilbertH_tendsto_of_smooth_bound hp hbound (fun z => ω₁ z - ω₂ z) hω12
  have hp1e : (1:ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  have hsubconv : Tendsto (fun n => eLpNorm (fun z => hilbertHSmooth (hilbertHApprox
      (fun w => ω₁ w - ω₂ w) n) z - (hilbertH ω₁ z - hilbertH ω₂ z)) (ENNReal.ofReal p))
      atTop (𝓝 0) := by
    have heqn : ∀ n, hilbertHSmooth (hilbertHApprox (fun w => ω₁ w - ω₂ w) n) =
        fun z => hilbertHSmooth (hilbertHApprox ω₁ n) z - hilbertHSmooth (hilbertHApprox ω₂ n) z := by
      intro n
      rw [hilbertHApprox_sub hp.le hω₁ hω₂]
      exact hilbertHSmooth_sub (hilbertHApprox_contDiff hp.le hω₁ n)
        (hilbertHApprox_hasCompactSupport ω₁ n) (hilbertHApprox_contDiff hp.le hω₂ n)
        (hilbertHApprox_hasCompactSupport ω₂ n)
    have hboundn : ∀ n, eLpNorm (fun z => hilbertHSmooth (hilbertHApprox (fun w => ω₁ w - ω₂ w) n) z -
        (hilbertH ω₁ z - hilbertH ω₂ z)) (ENNReal.ofReal p) ≤
        eLpNorm (fun z => hilbertHSmooth (hilbertHApprox ω₁ n) z - hilbertH ω₁ z)
          (ENNReal.ofReal p) +
        eLpNorm (fun z => hilbertHSmooth (hilbertHApprox ω₂ n) z - hilbertH ω₂ z)
          (ENNReal.ofReal p) := by
      intro n
      have heq2 : (fun z => hilbertHSmooth (hilbertHApprox (fun w => ω₁ w - ω₂ w) n) z -
          (hilbertH ω₁ z - hilbertH ω₂ z)) =
          fun z => (hilbertHSmooth (hilbertHApprox ω₁ n) z - hilbertH ω₁ z) -
            (hilbertHSmooth (hilbertHApprox ω₂ n) z - hilbertH ω₂ z) := by
        funext z
        have hz := congrFun (heqn n) z
        rw [hz]; ring
      have hm1 : AEStronglyMeasurable (fun z => hilbertHSmooth (hilbertHApprox ω₁ n) z -
          hilbertH ω₁ z) volume :=
        ((i1_hilbertH_eq_cauchyT_dz (hilbertHApprox_contDiff hp.le hω₁ n)
          (hilbertHApprox_hasCompactSupport ω₁ n)).2.1.continuous.aestronglyMeasurable).sub
          hmem1.aestronglyMeasurable
      have hm2 : AEStronglyMeasurable (fun z => hilbertHSmooth (hilbertHApprox ω₂ n) z -
          hilbertH ω₂ z) volume :=
        ((i1_hilbertH_eq_cauchyT_dz (hilbertHApprox_contDiff hp.le hω₂ n)
          (hilbertHApprox_hasCompactSupport ω₂ n)).2.1.continuous.aestronglyMeasurable).sub
          hmem2.aestronglyMeasurable
      have hnegle : eLpNorm (-(fun z => hilbertHSmooth (hilbertHApprox ω₂ n) z - hilbertH ω₂ z))
          (ENNReal.ofReal p) volume = eLpNorm (fun z => hilbertHSmooth (hilbertHApprox ω₂ n) z -
            hilbertH ω₂ z) (ENNReal.ofReal p) volume := eLpNorm_neg _ _ _
      have heq3 : (fun z => (hilbertHSmooth (hilbertHApprox ω₁ n) z - hilbertH ω₁ z) -
          (hilbertHSmooth (hilbertHApprox ω₂ n) z - hilbertH ω₂ z)) =
          (fun z => hilbertHSmooth (hilbertHApprox ω₁ n) z - hilbertH ω₁ z) +
            (-(fun z => hilbertHSmooth (hilbertHApprox ω₂ n) z - hilbertH ω₂ z)) := by
        funext z; show _ = _ + (-(hilbertHSmooth (hilbertHApprox ω₂ n) z - hilbertH ω₂ z)); ring
      rw [heq2, heq3]
      have := eLpNorm_add_le (f := fun z => hilbertHSmooth (hilbertHApprox ω₁ n) z - hilbertH ω₁ z) (g := -(fun z => hilbertHSmooth (hilbertHApprox ω₂ n) z - hilbertH ω₂ z)) (μ := volume) hp1e
      rwa [hnegle] at this
    have hsum := hconv1.add hconv2
    rw [add_zero] at hsum
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun n => bot_le) (Eventually.of_forall hboundn)
  have hmemsub : MemLp (fun z => hilbertH ω₁ z - hilbertH ω₂ z) (ENNReal.ofReal p) :=
    hmem1.sub hmem2
  exact hilbertH_indep_of_p (ω := fun w => ω₁ w - ω₂ w) hp hp hω12 hmem12 hconv12
    hmemsub hsubconv



/-! ## Calderon-Zygmund theory: weak (1,1), Marcinkiewicz, duality, assembly (S3-S6; -d4 and -ea) -/




/-- Test: the good-part Chebyshev bound for the CZ decomposition's `g` piece. -/
theorem cz_hilbertH_good_chebyshev {g f : ℂ → ℂ} {lam : ℝ} (hgint : Integrable g volume)
    (hgbound : ∀ᵐ z ∂volume, ‖g z‖ ≤ 4 * lam) (hlam : 0 < lam)
    (hgf_le : ∫ z, ‖g z‖ ≤ 3 * ∫ z, ‖f z‖) :
    volume {z : ℂ | lam / 2 < ‖hilbertH g z‖} ≤
      ENNReal.ofReal (48 * ∫ z, ‖f z‖) / ENNReal.ofReal lam := by
  -- Step 1: g ∈ L²
  have hgL2 : MemLp g 2 volume := by
    have hsq : Integrable (fun z => ‖g z‖ ^ 2) volume := by
      have hdom : ∀ᵐ z ∂volume, ‖(‖g z‖ ^ 2 : ℝ)‖ ≤ (4 * lam) * ‖g z‖ := by
        filter_upwards [hgbound] with z hz
        rw [Real.norm_of_nonneg (sq_nonneg _), sq]
        exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      exact Integrable.mono' (hgint.norm.const_mul (4 * lam)) (hgint.1.norm.pow 2) hdom
    exact (memLp_two_iff_integrable_sq_norm hgint.1).mpr hsq
  -- Step 2: eLpNorm g 2 ^ 2 = ∫⁻ ‖g‖ₑ ^ 2
  have heLp2 : eLpNorm g 2 volume ^ (2 : ℝ) = ∫⁻ z, ‖g z‖ₑ ^ (2 : ℝ) ∂volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (two_ne_zero) (by norm_num : (2:ℝ≥0∞) ≠ ⊤) hgint.aestronglyMeasurable,
      ← ENNReal.rpow_mul]
    norm_num
  -- Step 3: ∫⁻ ‖g‖ₑ^2 ≤ ofReal (4λ) * ∫⁻ ‖g‖ₑ
  have hlint_bound : (∫⁻ z, ‖g z‖ₑ ^ (2:ℝ) ∂volume) ≤
      ENNReal.ofReal (4 * lam) * ∫⁻ z, ‖g z‖ₑ ∂volume := by
    have hbound_e : ∀ᵐ z ∂volume, ‖g z‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal (4 * lam) * ‖g z‖ₑ := by
      filter_upwards [hgbound] with z hz
      have h1 : ‖g z‖ₑ ≤ ENNReal.ofReal (4 * lam) := by
        rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hz
      calc ‖g z‖ₑ ^ (2:ℝ) = ‖g z‖ₑ * ‖g z‖ₑ := by
            rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, sq]
        _ ≤ ENNReal.ofReal (4 * lam) * ‖g z‖ₑ := mul_le_mul_left h1 _
    calc (∫⁻ z, ‖g z‖ₑ ^ (2:ℝ) ∂volume) ≤ ∫⁻ z, ENNReal.ofReal (4 * lam) * ‖g z‖ₑ ∂volume :=
          lintegral_mono_ae hbound_e
      _ = ENNReal.ofReal (4 * lam) * ∫⁻ z, ‖g z‖ₑ ∂volume :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- Step 4: ∫⁻ ‖g‖ₑ = ofReal (∫ ‖g‖)
  have hbridge : (∫⁻ z, ‖g z‖ₑ ∂volume) = ENNReal.ofReal (∫ z, ‖g z‖ ∂volume) :=
    (ofReal_integral_norm_eq_lintegral_enorm hgint).symm
  -- Step 5: assemble eLpNorm g 2 ^ 2 ≤ ofReal (12 λ ∫‖f‖)
  have hgnn : (0:ℝ) ≤ ∫ z, ‖g z‖ := integral_nonneg (fun z => norm_nonneg _)
  have hfinal_g : eLpNorm g 2 volume ^ (2:ℝ) ≤ ENNReal.ofReal (12 * lam * ∫ z, ‖f z‖) := by
    calc eLpNorm g 2 volume ^ (2:ℝ) = ∫⁻ z, ‖g z‖ₑ ^ (2:ℝ) ∂volume := heLp2
      _ ≤ ENNReal.ofReal (4 * lam) * ∫⁻ z, ‖g z‖ₑ ∂volume := hlint_bound
      _ = ENNReal.ofReal (4 * lam) * ENNReal.ofReal (∫ z, ‖g z‖) := by rw [hbridge]
      _ = ENNReal.ofReal ((4 * lam) * ∫ z, ‖g z‖) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (12 * lam * ∫ z, ‖f z‖) := by
          apply ENNReal.ofReal_le_ofReal
          nlinarith [hgf_le, hlam.le]
  -- Step 6: Chebyshev at p = 2, ε = ofReal (λ/2)
  have hHgL2 := hilbertH_memLp_two hgL2
  have hcheb : ENNReal.ofReal (lam / 2) ^ (2:ℝ) *
      volume {z | ENNReal.ofReal (lam / 2) ≤ ‖hilbertH g z‖ₑ} ≤
      eLpNorm (hilbertH g) 2 volume ^ (2:ℝ) :=
    mul_meas_ge_le_pow_eLpNorm' volume (two_ne_zero) (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
      (ENNReal.ofReal (lam / 2))
  rw [hHgL2.2] at hcheb
  have hchain : ENNReal.ofReal (lam / 2) ^ (2:ℝ) *
      volume {z | ENNReal.ofReal (lam / 2) ≤ ‖hilbertH g z‖ₑ} ≤
      ENNReal.ofReal (12 * lam * ∫ z, ‖f z‖) := hcheb.trans hfinal_g
  -- Step 7: convert the target strict-real-norm set into the enorm-≤ set
  have hsubset : {z : ℂ | lam / 2 < ‖hilbertH g z‖} ⊆
      {z | ENNReal.ofReal (lam / 2) ≤ ‖hilbertH g z‖ₑ} := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 hz |>.le
  have hmono := measure_mono (μ := volume) hsubset
  -- Step 8: solve for the volume bound
  have hepow : ENNReal.ofReal (lam / 2) ^ (2:ℝ) = ENNReal.ofReal (lam^2 / 4) := by
    rw [ENNReal.ofReal_rpow_of_pos (by positivity)]
    congr 1
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [hepow] at hchain
  have hfin : volume {z | ENNReal.ofReal (lam / 2) ≤ ‖hilbertH g z‖ₑ} ≤
      ENNReal.ofReal (12 * lam * ∫ z, ‖f z‖) / ENNReal.ofReal (lam^2 / 4) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity : ENNReal.ofReal (lam^2/4) ≠ 0))
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact hchain
  refine hmono.trans (hfin.trans (le_of_eq ?_))
  rw [← ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ) < lam^2/4),
    ← ENNReal.ofReal_div_of_pos hlam]
  congr 1
  field_simp
  ring



theorem czKernel_diff_norm_le_of_two_r {c z ζ : ℂ} {r : ℝ} (hr : 0 < r)
    (hζ : ‖ζ - c‖ ≤ r) (hz : 2 * r < ‖z - c‖) :
    ‖czKernel ζ z - czKernel c z‖ ≤ 10 * r / (π * ‖z - c‖ ^ 3) := by
  have hzc : z ≠ c := by
    intro h; rw [h, sub_self, norm_zero] at hz; linarith
  have hzzeta : z ≠ ζ := by
    intro h
    apply absurd hz (not_lt.2 ?_)
    calc ‖z - c‖ = ‖ζ - c‖ := by rw [h]
      _ ≤ r := hζ
      _ ≤ 2 * r := by linarith
  set R : ℝ := ‖z - c‖ with hRdef
  have hR : (0:ℝ) < R := by linarith
  have hsymm1 : czKernel ζ z = czKernel z ζ := by unfold czKernel; ring_nf
  have hsymm2 : czKernel c z = czKernel z c := by unfold czKernel; ring_nf
  rw [hsymm1, hsymm2, czKernel_diff_eq (z := ζ) (z' := c) (ζ := z) hzzeta hzc]
  have hzeta_lb : R - r ≤ ‖z - ζ‖ := by
    have htri : ‖z - c‖ ≤ ‖z - ζ‖ + ‖ζ - c‖ := by
      calc ‖z - c‖ = ‖(z - ζ) + (ζ - c)‖ := by ring_nf
        _ ≤ ‖z - ζ‖ + ‖ζ - c‖ := norm_add_le _ _
    rw [← hRdef] at htri; linarith
  have hzeta_ub : ‖z - ζ‖ ≤ R + r := by
    have htri : ‖z - c‖ + ‖c - ζ‖ = R + ‖ζ - c‖ := by
      rw [norm_sub_rev c ζ, ← hRdef]
    calc ‖z - ζ‖ = ‖(z - c) + (c - ζ)‖ := by ring_nf
      _ ≤ ‖z - c‖ + ‖c - ζ‖ := norm_add_le _ _
      _ = R + ‖ζ - c‖ := htri
      _ ≤ R + r := by linarith
  have hzeta_pos : 0 < ‖z - ζ‖ := by linarith
  have hnum_ub : ‖2 * z - ζ - c‖ ≤ 2 * R + r := by
    calc ‖2 * z - ζ - c‖ = ‖(z - ζ) + (z - c)‖ := by ring_nf
      _ ≤ ‖z - ζ‖ + ‖z - c‖ := norm_add_le _ _
      _ ≤ (R + r) + R := by linarith [hRdef ▸ (le_refl ‖z - c‖)]
      _ = 2 * R + r := by ring
  have hπ0 : (0:ℝ) < π := Real.pi_pos
  have hζc_nn : (0:ℝ) ≤ ‖ζ - c‖ := norm_nonneg _
  have hnum_nn : (0:ℝ) ≤ ‖2 * z - ζ - c‖ := norm_nonneg _
  have hquad : (2 * R + r) * R ≤ 10 * (R - r) ^ 2 :=
    by nlinarith [sq_nonneg (R - 2 * r), mul_pos hr (by linarith : (0:ℝ) < R - 2 * r)]
  have step_a : ‖ζ - c‖ * ‖2 * z - ζ - c‖ ≤ r * (2 * R + r) :=
    mul_le_mul hζ hnum_ub hnum_nn hr.le
  have step_b : ‖ζ - c‖ * ‖2 * z - ζ - c‖ * R ≤ r * (2 * R + r) * R :=
    mul_le_mul_of_nonneg_right step_a hR.le
  have step_c : r * (2 * R + r) * R ≤ r * (10 * (R - r) ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hquad hr.le
    linarith [h1]
  have hRr_nn : (0:ℝ) ≤ R - r := by linarith
  have step_d : r * (10 * (R - r) ^ 2) ≤ 10 * r * ‖z - ζ‖ ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hRr_nn hzeta_lb 2) (by positivity : (0:ℝ) ≤ 10 * r)
    linarith [h1]
  have key : ‖ζ - c‖ * ‖2 * z - ζ - c‖ * R ≤ 10 * r * ‖z - ζ‖ ^ 2 :=
    step_b.trans (step_c.trans step_d)
  have key2 : ‖ζ - c‖ * ‖2 * z - ζ - c‖ * R ^ 3 ≤ 10 * r * ‖z - ζ‖ ^ 2 * R ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right key (sq_nonneg R)]
  simp only [norm_div, norm_mul, norm_neg, norm_pow, norm_one, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  rw [← hRdef]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hpi_cancel : (1 / π) * (‖ζ - c‖ * ‖2 * z - ζ - c‖) * (π * R ^ 3) =
      ‖ζ - c‖ * ‖2 * z - ζ - c‖ * R ^ 3 := by
    field_simp
  rw [hpi_cancel]
  linarith [key2]



/-- Test: partial sums of disjointly-supported L² pieces converge to the whole in L². -/
theorem cz_partialSum_tendsto_L2 {ι : Type} [Countable ι] {Q : ι → Set ℂ} {b : ℂ → ℂ}
    (hQmeas : ∀ i, MeasurableSet (Q i)) (hQdisj : Pairwise (Function.onFun Disjoint Q))
    (hbsupp : (Function.support b : Set ℂ) ⊆ ⋃ i, Q i) (hbL2 : MemLp b 2 volume) :
    ∃ (e : ι → ℕ) (he : Function.Injective e) (s : ℕ → ℂ → ℂ),
      (∀ n z, s n z = ∑ i ∈ (Set.Finite.preimage he.injOn (Set.finite_Iio n) :
          Set.Finite {i : ι | e i < n}).toFinset, (Q i).indicator b z) ∧
      Tendsto (fun n => eLpNorm (fun z => s n z - b z) 2 volume) atTop (𝓝 0) := by
  classical
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  set Fn : ℕ → Finset ι := fun n =>
    (Set.Finite.preimage he.injOn (Set.finite_Iio n) : Set.Finite {i : ι | e i < n}).toFinset with hFn
  have hmemFn : ∀ n i, i ∈ Fn n ↔ e i < n := by
    intro n i
    rw [hFn]
    exact Set.Finite.mem_toFinset _
  set s : ℕ → ℂ → ℂ := fun n z => ∑ i ∈ Fn n, (Q i).indicator b z with hs_def
  refine ⟨e, he, s, fun n z => rfl, ?_⟩
  -- At most one index can contain a given `z` (disjointness).
  have hsubsingle : ∀ z, {i : ι | z ∈ Q i}.Subsingleton := by
    intro z i hi j hj
    by_contra hij
    exact (hQdisj hij).le_bot ⟨hi, hj⟩
  -- The partial sum at `z` is either `0` or `b z`, and it stabilizes at `b z` once the (at most
  -- one) relevant index enters the finset.
  have hcase : ∀ z, (b z = 0 ∧ ∀ n, s n z = 0) ∨
      (∃ i0, z ∈ Q i0 ∧ ∀ n, s n z = if i0 ∈ Fn n then b z else 0) := by
    intro z
    by_cases hz : ∃ i, z ∈ Q i
    · obtain ⟨i0, hi0⟩ := hz
      right
      refine ⟨i0, hi0, fun n => ?_⟩
      show ∑ i ∈ Fn n, (Q i).indicator b z = if i0 ∈ Fn n then b z else 0
      have hval : ∀ i ∈ Fn n, (Q i).indicator b z = if i = i0 then b z else 0 := by
        intro i _
        by_cases hi : i = i0
        · subst hi; rw [if_pos rfl, Set.indicator_of_mem hi0]
        · rw [if_neg hi, Set.indicator_of_notMem]
          intro hmem
          exact hi (hsubsingle z hmem hi0)
      rw [Finset.sum_congr rfl hval, Finset.sum_ite_eq' (Fn n) i0 (fun _ => b z)]
    · left
      have hbz : b z = 0 := by
        by_contra hne
        exact hz (Set.mem_iUnion.1 (hbsupp hne))
      refine ⟨hbz, fun n => ?_⟩
      show ∑ i ∈ Fn n, (Q i).indicator b z = 0
      apply Finset.sum_eq_zero
      intro i _
      exact Set.indicator_of_notMem (fun hmem => hz ⟨i, hmem⟩) b
  -- Pointwise domination and eventual stabilization.
  have hdom : ∀ z n, ‖s n z - b z‖ ≤ ‖b z‖ := by
    intro z n
    rcases hcase z with ⟨hbz, h0⟩ | ⟨i0, -, hi0⟩
    · rw [h0 n]; simp
    · rw [hi0 n]
      by_cases hmem : i0 ∈ Fn n
      · rw [if_pos hmem]; simp
      · rw [if_neg hmem]; simp
  have htendsto : ∀ z, Tendsto (fun n => s n z) atTop (𝓝 (b z)) := by
    intro z
    rcases hcase z with ⟨hbz, h0⟩ | ⟨i0, hi0mem, hi0⟩
    · simp_rw [h0, hbz]
      exact tendsto_const_nhds
    · have heventually : ∀ n, e i0 < n → s n z = b z := by
        intro n hn
        rw [hi0 n, if_pos ((hmemFn n i0).2 hn)]
      apply tendsto_const_nhds.congr'
      filter_upwards [Filter.eventually_gt_atTop (e i0)] with n hn using (heventually n hn).symm
  -- Measurability of the partial sums.
  have hsmeas : ∀ n, AEStronglyMeasurable (s n) volume := by
    intro n
    have heq : s n = ∑ i ∈ Fn n, (Q i).indicator b := by
      rw [hs_def]; exact (Finset.sum_fn (Fn n) (fun i => (Q i).indicator b)).symm
    rw [heq]
    exact Finset.aestronglyMeasurable_sum (Fn n) (fun i _ =>
      (hbL2.aestronglyMeasurable.indicator (hQmeas i)))
  -- DCT for the squared L² distance.
  have hdct : Tendsto (fun n => ∫⁻ z, ‖s n z - b z‖ₑ ^ (2:ℝ) ∂volume) atTop (𝓝 0) := by
    have hbeLp2 : eLpNorm b 2 volume ^ (2:ℝ) = ∫⁻ z, ‖b z‖ₑ ^ (2:ℝ) ∂volume := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (two_ne_zero) (by norm_num : (2:ℝ≥0∞) ≠ ⊤) hbL2.aestronglyMeasurable,
        ← ENNReal.rpow_mul]
      norm_num
    have hbound_int : (∫⁻ z, ‖b z‖ₑ ^ (2:ℝ) ∂volume) ≠ ⊤ := by
      rw [← hbeLp2]
      exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hbL2.eLpNorm_ne_top
    have h0 : (∫⁻ _z : ℂ, (0:ℝ≥0∞) ∂volume) = 0 := lintegral_zero
    rw [← h0]
    apply tendsto_lintegral_of_dominated_convergence' (fun z => ‖b z‖ₑ ^ (2:ℝ))
      (fun n => ((hsmeas n).sub hbL2.aestronglyMeasurable).aemeasurable.enorm.pow_const _)
      (fun n => (Filter.Eventually.of_forall (fun z => by
        have := hdom z n
        calc ‖s n z - b z‖ₑ ^ (2:ℝ) = ‖s n z - b z‖ₑ ^ (2:ℕ) := by
              rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
          _ ≤ ‖b z‖ₑ ^ (2:ℕ) := by
              apply pow_le_pow_left'
              rwa [← ofReal_norm, ← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)]
          _ = ‖b z‖ₑ ^ (2:ℝ) := by
              rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast])))
      hbound_int
      (Filter.Eventually.of_forall (fun z => by
        have hz0 : Tendsto (fun n => s n z - b z) atTop (𝓝 0) := by
          have h := (htendsto z).sub (tendsto_const_nhds (x := b z))
          rwa [sub_self] at h
        have h1 : Tendsto (fun n => ‖s n z - b z‖ₑ) atTop (𝓝 0) := by
          have := hz0.enorm; simpa using this
        have h2 := h1.ennrpow_const 2
        simpa [ENNReal.zero_rpow_of_pos] using h2))
  -- Convert the squared lintegral bound into the eLpNorm bound.
  have heLp2n : ∀ n, eLpNorm (fun z => s n z - b z) 2 volume ^ (2:ℝ) =
      ∫⁻ z, ‖s n z - b z‖ₑ ^ (2:ℝ) ∂volume := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (two_ne_zero) (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
      (show AEStronglyMeasurable (fun z => s n z - b z) volume from (hsmeas n).sub hbL2.aestronglyMeasurable),
      ← ENNReal.rpow_mul]
    norm_num
  have hsq := hdct.ennrpow_const (1/2 : ℝ)
  simp_rw [← heLp2n, ← ENNReal.rpow_mul] at hsq
  norm_num at hsq
  simpa [ENNReal.zero_rpow_of_pos] using hsq

/-- Test: finite additivity of `hilbertH` over a finset of disjointly-supported L² pieces. -/
theorem cz_hilbertH_finset_sum_ae {ι : Type} {bi : ι → ℂ → ℂ} (hbi : ∀ i, MemLp (bi i) 2 volume)
    (F : Finset ι) :
    hilbertH (∑ i ∈ F, bi i) =ᵐ[volume] ∑ i ∈ F, hilbertH (bi i) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : MemLp (0 : ℂ → ℂ) 2 volume := MemLp.zero
    have hadd := hilbertH_add_ae h0 h0
    simp only [add_zero] at hadd
    filter_upwards [hadd] with z hz
    simp only [Pi.add_apply] at hz
    show hilbertH (0:ℂ→ℂ) z = 0
    linear_combination -hz
  | insert i F hiF ih =>
    rw [Finset.sum_insert hiF, Finset.sum_insert hiF]
    have hFmem : MemLp (∑ i ∈ F, bi i) 2 volume := memLp_finsetSum' F (fun i _ => hbi i)
    have hadd := hilbertH_add_ae (hbi i) hFmem
    filter_upwards [hadd, ih] with z hz hzih
    simp only [Pi.add_apply, Finset.sum_apply] at hz hzih ⊢
    rw [hz, hzih]

/-- Subtraction additivity at `p = 2`, derived from `hilbertH_add_ae` + `hilbertH_smul_ae`. -/
theorem cz_hilbertH_sub_ae {ω₁ ω₂ : ℂ → ℂ} (h₁ : MemLp ω₁ 2 volume) (h₂ : MemLp ω₂ 2 volume) :
    hilbertH (fun z => ω₁ z - ω₂ z) =ᵐ[volume] fun z => hilbertH ω₁ z - hilbertH ω₂ z := by
  have hneg : MemLp (fun z => -ω₂ z) 2 volume := h₂.neg
  have hsmul := hilbertH_smul_ae (-1 : ℂ) h₂
  have heq1 : ((-1 : ℂ) • ω₂) = fun z => -ω₂ z := by
    funext z; show (-1 : ℂ) * ω₂ z = -ω₂ z; ring
  have heq2 : ((-1 : ℂ) • hilbertH ω₂) = fun z => -hilbertH ω₂ z := by
    funext z; show (-1 : ℂ) * hilbertH ω₂ z = -hilbertH ω₂ z; ring
  rw [heq1, heq2] at hsmul
  have heq0 : (ω₁ + fun z => -ω₂ z) = fun z => ω₁ z - ω₂ z := by
    funext z; show ω₁ z + -ω₂ z = ω₁ z - ω₂ z; ring
  have hadd := hilbertH_add_ae h₁ hneg
  rw [heq0] at hadd
  filter_upwards [hadd, hsmul] with z hz hsz
  simp only [Pi.add_apply] at hz
  rw [hz]
  linear_combination hsz

/-- Test: countable additivity of `hilbertH` over disjointly-supported L² pieces, in the
tsum/pointwise-a.e. form needed for the tail-region integral bound. -/
theorem cz_enorm_hilbertH_le_tsum {ι : Type} [Countable ι] {Q : ι → Set ℂ} {b : ℂ → ℂ}
    (hQmeas : ∀ i, MeasurableSet (Q i)) (hQdisj : Pairwise (Function.onFun Disjoint Q))
    (hbsupp : (Function.support b : Set ℂ) ⊆ ⋃ i, Q i) (hbL2 : MemLp b 2 volume) :
    ∀ᵐ z ∂volume, ‖hilbertH b z‖ₑ ≤ ∑' i, ‖hilbertH ((Q i).indicator b) z‖ₑ := by
  classical
  obtain ⟨e, he, s, hs_def, hL2conv⟩ := cz_partialSum_tendsto_L2 hQmeas hQdisj hbsupp hbL2
  set Fn : ℕ → Finset ι := fun n =>
    (Set.Finite.preimage he.injOn (Set.finite_Iio n) : Set.Finite {i : ι | e i < n}).toFinset
    with hFndef
  have hbi : ∀ i, MemLp ((Q i).indicator b) 2 volume := fun i => hbL2.indicator (hQmeas i).nullMeasurableSet
  have hsfun : ∀ n, s n = ∑ i ∈ Fn n, (Q i).indicator b := by
    intro n
    rw [Finset.sum_fn]
    funext z
    exact hs_def n z
  have hsL2 : ∀ n, MemLp (s n) 2 volume := by
    intro n
    rw [hsfun n]
    exact memLp_finsetSum' (Fn n) (fun i _ => hbi i)
  -- `eLpNorm (H (s n) - H b) 2 = eLpNorm (s n - b) 2 → 0`.
  have hHconv : Tendsto (fun n => eLpNorm (fun z => hilbertH (s n) z - hilbertH b z) 2 volume)
      atTop (𝓝 0) := by
    have heq : ∀ n, eLpNorm (fun z => hilbertH (s n) z - hilbertH b z) 2 volume =
        eLpNorm (fun z => s n z - b z) 2 volume := by
      intro n
      have hsub := cz_hilbertH_sub_ae (hsL2 n) hbL2
      rw [← eLpNorm_congr_ae hsub]
      exact (hilbertH_memLp_two ((hsL2 n).sub hbL2)).2
    simp_rw [heq]
    exact hL2conv
  -- Extract an a.e.-convergent subsequence.
  have hfmeas : ∀ n, AEStronglyMeasurable (fun z => hilbertH (s n) z) volume :=
    fun n => (hilbertH_memLp_two (hsL2 n)).1.aestronglyMeasurable
  have hmem : AEStronglyMeasurable (hilbertH b) volume := (hilbertH_memLp_two hbL2).1.aestronglyMeasurable
  have htm : TendstoInMeasure volume (fun n z => hilbertH (s n) z) atTop (hilbertH b) :=
    tendstoInMeasure_of_tendsto_eLpNorm (two_ne_zero) hHconv
  obtain ⟨ns, hns, hnsae⟩ := htm.exists_seq_tendsto_ae
  -- The finite-additivity identity along the subsequence, simultaneously for all `k`.
  have hadd_all : ∀ᵐ z ∂volume, ∀ k, hilbertH (s (ns k)) z = ∑ i ∈ Fn (ns k), hilbertH ((Q i).indicator b) z := by
    rw [ae_all_iff]
    intro k
    have hfa := cz_hilbertH_finset_sum_ae hbi (Fn (ns k))
    rw [← hsfun (ns k)] at hfa
    filter_upwards [hfa] with z hz
    rwa [Finset.sum_fn] at hz
  filter_upwards [hnsae, hadd_all] with z hz1 hz2
  have hz3 : Tendsto (fun k => ‖hilbertH (s (ns k)) z‖ₑ) atTop (𝓝 ‖hilbertH b z‖ₑ) := hz1.enorm
  have hz4 : ∀ k, ‖hilbertH (s (ns k)) z‖ₑ ≤ ∑' i, ‖hilbertH ((Q i).indicator b) z‖ₑ := by
    intro k
    rw [hz2 k]
    calc ‖∑ i ∈ Fn (ns k), hilbertH ((Q i).indicator b) z‖ₑ
        ≤ ∑ i ∈ Fn (ns k), ‖hilbertH ((Q i).indicator b) z‖ₑ := by
          rw [← ofReal_norm]
          rw [show (∑ i ∈ Fn (ns k), hilbertH ((Q i).indicator b) z) =
            (∑ i ∈ Fn (ns k), hilbertH ((Q i).indicator b) z) from rfl]
          calc ENNReal.ofReal ‖∑ i ∈ Fn (ns k), hilbertH ((Q i).indicator b) z‖
              ≤ ENNReal.ofReal (∑ i ∈ Fn (ns k), ‖hilbertH ((Q i).indicator b) z‖) :=
                ENNReal.ofReal_le_ofReal (norm_sum_le _ _)
            _ = ∑ i ∈ Fn (ns k), ENNReal.ofReal ‖hilbertH ((Q i).indicator b) z‖ :=
                ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)
            _ = ∑ i ∈ Fn (ns k), ‖hilbertH ((Q i).indicator b) z‖ₑ := by
                simp_rw [ofReal_norm]
      _ ≤ ∑' i, ‖hilbertH ((Q i).indicator b) z‖ₑ := ENNReal.sum_le_tsum _
  exact le_of_tendsto hz3 (Filter.Eventually.of_forall hz4)



/-- Transfer the off-support kernel representation to the (only `AEStronglyMeasurable`) piece
`b`, via the measurable representative truncated back onto `closure Q` (so `tsupport` stays
controlled), per `-17`'s recipe. -/
theorem cz_hilbertH_offsupp_transfer {Q : Set ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hQsub : Q ⊆ closedBall c r) {b : ℂ → ℂ} (hb_supp : ∀ ζ, ζ ∉ Q → b ζ = 0)
    (hb_L2 : MemLp b 2 volume) :
    ∀ᵐ z ∂(volume.restrict (closedBall c (2 * r))ᶜ),
      hilbertH b z = ∫ ζ, -(1 / π : ℂ) * b ζ / (ζ - z) ^ 2 := by
  have hbmeas : AEStronglyMeasurable b volume := hb_L2.aestronglyMeasurable
  set φ : ℂ → ℂ := (closure Q).indicator (hbmeas.mk b) with hφdef
  have hQclosed : IsClosed (closure Q) := isClosed_closure
  have hφmeas : Measurable φ :=
    hbmeas.stronglyMeasurable_mk.measurable.indicator hQclosed.measurableSet
  have hφeq : φ =ᵐ[volume] b := by
    have hmkeq : (hbmeas.mk b) =ᵐ[volume] b := hbmeas.ae_eq_mk.symm
    filter_upwards [hmkeq] with z hz
    by_cases hzQ : z ∈ closure Q
    · rw [hφdef, Set.indicator_of_mem hzQ, hz]
    · rw [hφdef, Set.indicator_of_notMem hzQ]
      exact (hb_supp z (fun h => hzQ (subset_closure h))).symm
  have hφL2 : MemLp φ 2 volume := (memLp_congr_ae hφeq).2 hb_L2
  have hclQsub : closure Q ⊆ closedBall c r := by
    rw [← IsClosed.closure_eq (isClosed_closedBall)]
    exact closure_mono hQsub
  have hφsupp : Function.support φ ⊆ closure Q := support_indicator_subset
  have htsupp : tsupport φ ⊆ closedBall c r := by
    calc tsupport φ = closure (Function.support φ) := rfl
      _ ⊆ closure (closure Q) := closure_mono hφsupp
      _ = closure Q := IsClosed.closure_eq hQclosed
      _ ⊆ closedBall c r := hclQsub
  have hφcompact : HasCompactSupport φ :=
    (isCompact_closedBall c r).of_isClosed_subset (isClosed_tsupport φ) htsupp
  have hHeq : hilbertH b = hilbertH φ := hilbertH_congr_ae hφeq.symm
  have hoffsupp := hilbertH_eq_integral_ae_off_support hφmeas hφL2 hφcompact
  have hsub : (closedBall c (2 * r))ᶜ ⊆ (tsupport φ)ᶜ :=
    Set.compl_subset_compl.2 (htsupp.trans (by
      have : closedBall c r ⊆ closedBall c (2 * r) := by
        apply Metric.closedBall_subset_closedBall; linarith
      exact this))
  have htransfer := ae_restrict_of_ae_restrict_of_subset hsub hoffsupp
  filter_upwards [htransfer] with z hz
  rw [hHeq, hz]
  apply integral_congr_ae
  filter_upwards [hφeq] with ζ hζ
  rw [hζ]

/-- Pointwise mean-zero cancellation bound, given the off-support kernel representation at a
single point `z`. -/
theorem cz_ptwise_cancel {Q : Set ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r) (hQsub : Q ⊆ closedBall c r)
    (hQmeas : MeasurableSet Q) {b : ℂ → ℂ} (hb_supp : ∀ ζ, ζ ∉ Q → b ζ = 0)
    (hmean : ∫ ζ in Q, b ζ = 0) (hb_int : Integrable b volume)
    {z : ℂ} (hz : 2 * r < ‖z - c‖)
    (hrepz : hilbertH b z = ∫ ζ, -(1 / π : ℂ) * b ζ / (ζ - z) ^ 2) :
    ‖hilbertH b z‖ ≤ 10 * r / (π * ‖z - c‖ ^ 3) * ∫ ζ, ‖b ζ‖ := by
  rw [hrepz]
  have hker : (fun ζ => -(1 / π : ℂ) * b ζ / (ζ - z) ^ 2) = fun ζ => czKernel ζ z * b ζ := by
    funext ζ; unfold czKernel; ring
  have hb_supp' : ∀ ζ, ζ ∉ Q → czKernel ζ z * b ζ = 0 := fun ζ hζ => by
    rw [hb_supp ζ hζ, mul_zero]
  rw [hker, (setIntegral_eq_integral_of_forall_compl_eq_zero hb_supp').symm]
  have hK : ∀ ζ ∈ Q, ‖czKernel ζ z - czKernel c z‖ ≤ 10 * r / (π * ‖z - c‖ ^ 3) := fun ζ hζ =>
    czKernel_diff_norm_le_of_two_r hr (mem_closedBall_iff_norm.1 (hQsub hζ)) hz
  have hmeasK : Measurable (fun ζ : ℂ => czKernel ζ z - czKernel c z) := by
    unfold czKernel; fun_prop
  have hint1 : IntegrableOn (fun ζ => (czKernel ζ z - czKernel c z) * b ζ) Q volume := by
    apply Integrable.mono' (hb_int.norm.integrableOn.const_mul (10 * r / (π * ‖z - c‖ ^ 3)))
    · exact hmeasK.aestronglyMeasurable.mul hb_int.1.restrict
    · rw [ae_restrict_iff' hQmeas]
      exact Filter.Eventually.of_forall (fun ζ hζQ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hK ζ hζQ) (norm_nonneg _))
  have hint2 : IntegrableOn (fun ζ => czKernel c z * b ζ) Q volume := hb_int.integrableOn.const_mul _
  have hcancel : (∫ ζ in Q, czKernel ζ z * b ζ) = ∫ ζ in Q, (czKernel ζ z - czKernel c z) * b ζ := by
    have hptwise : Set.EqOn (fun ζ => czKernel ζ z * b ζ)
        (fun ζ => (czKernel ζ z - czKernel c z) * b ζ + czKernel c z * b ζ) Q := fun ζ _ => by
      show czKernel ζ z * b ζ = (czKernel ζ z - czKernel c z) * b ζ + czKernel c z * b ζ; ring
    rw [setIntegral_congr_fun hQmeas hptwise, integral_add hint1 hint2, integral_const_mul, hmean,
      mul_zero, add_zero]
  rw [hcancel]
  calc ‖∫ ζ in Q, (czKernel ζ z - czKernel c z) * b ζ‖
      ≤ ∫ ζ in Q, ‖(czKernel ζ z - czKernel c z) * b ζ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ ζ in Q, 10 * r / (π * ‖z - c‖ ^ 3) * ‖b ζ‖ := by
        apply setIntegral_mono_on hint1.norm
          (hb_int.norm.integrableOn.const_mul _) hQmeas
        intro ζ hζ
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hK ζ hζ) (norm_nonneg _)
    _ = 10 * r / (π * ‖z - c‖ ^ 3) * ∫ ζ in Q, ‖b ζ‖ := by rw [integral_const_mul]
    _ ≤ 10 * r / (π * ‖z - c‖ ^ 3) * ∫ ζ, ‖b ζ‖ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact setIntegral_le_integral hb_int.norm (Filter.Eventually.of_forall (fun ζ => norm_nonneg _))

/-- The full per-square tail bound in `ℝ≥0∞`/`lintegral` form. -/
theorem cz_tail_bound {Q : Set ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r) (hQsub : Q ⊆ closedBall c r)
    (hQmeas : MeasurableSet Q) {b : ℂ → ℂ} (hb_supp : ∀ ζ, ζ ∉ Q → b ζ = 0)
    (hmean : ∫ ζ in Q, b ζ = 0) (hb_int : Integrable b volume) (hb_L2 : MemLp b 2 volume) :
    (∫⁻ z in (closedBall c (2 * r))ᶜ, ‖hilbertH b z‖ₑ) ≤
      ENNReal.ofReal (∫ ζ, ‖b ζ‖) * ENNReal.ofReal (10 * r / π) *
        ∫⁻ z in (closedBall c (2 * r))ᶜ, ‖z - c‖ₑ ^ (-(3 : ℝ)) := by
  have hSmeas : MeasurableSet (closedBall c (2 * r))ᶜ := (isClosed_closedBall).measurableSet.compl
  have hbound_ae : ∀ᵐ z ∂(volume.restrict (closedBall c (2 * r))ᶜ),
      ‖hilbertH b z‖ₑ ≤
        ENNReal.ofReal (∫ ζ, ‖b ζ‖) * ENNReal.ofReal (10 * r / π) * ‖z - c‖ₑ ^ (-(3 : ℝ)) := by
    filter_upwards [cz_hilbertH_offsupp_transfer hr hQsub hb_supp hb_L2, self_mem_ae_restrict hSmeas]
      with z hz hzmem
    have hz2r : 2 * r < ‖z - c‖ := by
      by_contra hcon
      push_neg at hcon
      exact hzmem (mem_closedBall_iff_norm.2 hcon)
    have hzc0 : (0:ℝ) < ‖z - c‖ := by linarith
    have hmain := cz_ptwise_cancel hr hQsub hQmeas hb_supp hmean hb_int hz2r hz
    have hcube : ‖z - c‖ₑ ^ (-(3 : ℝ)) = ENNReal.ofReal ((‖z - c‖ ^ 3)⁻¹) := by
      rw [ENNReal.rpow_neg, ← ofReal_norm (z - c),
        show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
        ← ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_inv_of_pos (by positivity)]
    have heqR : 10 * r / (π * ‖z - c‖ ^ 3) * (∫ ζ, ‖b ζ‖) =
        (∫ ζ, ‖b ζ‖) * (10 * r / π) * (‖z - c‖ ^ 3)⁻¹ := by
      rw [div_mul_eq_div_div, div_eq_mul_inv]; ring
    rw [heqR] at hmain
    calc ‖hilbertH b z‖ₑ = ENNReal.ofReal ‖hilbertH b z‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal ((∫ ζ, ‖b ζ‖) * (10 * r / π) * (‖z - c‖ ^ 3)⁻¹) :=
          ENNReal.ofReal_le_ofReal hmain
      _ = ENNReal.ofReal (∫ ζ, ‖b ζ‖) * ENNReal.ofReal (10 * r / π) *
            ENNReal.ofReal ((‖z - c‖ ^ 3)⁻¹) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (∫ ζ, ‖b ζ‖) * ENNReal.ofReal (10 * r / π) * ‖z - c‖ₑ ^ (-(3 : ℝ)) := by
          rw [hcube]
  calc (∫⁻ z in (closedBall c (2 * r))ᶜ, ‖hilbertH b z‖ₑ)
      ≤ ∫⁻ z in (closedBall c (2 * r))ᶜ,
          ENNReal.ofReal (∫ ζ, ‖b ζ‖) * ENNReal.ofReal (10 * r / π) * ‖z - c‖ₑ ^ (-(3 : ℝ)) :=
        lintegral_mono_ae hbound_ae
    _ = ENNReal.ofReal (∫ ζ, ‖b ζ‖) * ENNReal.ofReal (10 * r / π) *
          ∫⁻ z in (closedBall c (2 * r))ᶜ, ‖z - c‖ₑ ^ (-(3 : ℝ)) := by
        rw [← lintegral_const_mul' _ _
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]

/-- Numeric evaluation of the tail bound's radial integral: `∫⁻_{‖z-c‖>2r} ‖z-c‖ₑ^(-3) = ofReal(π/r)`. -/
theorem cz_tail_bound_final {Q : Set ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r) (hQsub : Q ⊆ closedBall c r)
    (hQmeas : MeasurableSet Q) {b : ℂ → ℂ} (hb_supp : ∀ ζ, ζ ∉ Q → b ζ = 0)
    (hmean : ∫ ζ in Q, b ζ = 0) (hb_int : Integrable b volume) (hb_L2 : MemLp b 2 volume) :
    (∫⁻ z in (closedBall c (2 * r))ᶜ, ‖hilbertH b z‖ₑ) ≤
      ENNReal.ofReal (10 * ∫ ζ, ‖b ζ‖) := by
  have hradial : (∫⁻ z in {z : ℂ | 2 * r < ‖z - c‖}, ‖z - c‖ₑ ^ (-(3 : ℝ))) =
      ENNReal.ofReal (2 * π) * ENNReal.ofReal (-(2 * r) ^ (2 - (3:ℝ)) / (2 - 3)) :=
    cz_lintegral_compl_ball_sub_enorm_rpow_neg (by norm_num) (by positivity) c
  have hSeq : (closedBall c (2 * r))ᶜ = {z : ℂ | 2 * r < ‖z - c‖} := by
    ext z; simp [dist_eq_norm, not_le]
  have hmainbound := cz_tail_bound hr hQsub hQmeas hb_supp hmean hb_int hb_L2
  rw [hSeq] at hmainbound
  have hval : -(2 * r) ^ (2 - (3:ℝ)) / (2 - 3) = 1 / (2 * r) := by
    rw [show (2:ℝ) - 3 = -(1:ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_one]
    ring
  rw [hval] at hradial
  have hcombine : (∫⁻ z in {z : ℂ | 2 * r < ‖z - c‖}, ‖hilbertH b z‖ₑ) ≤
      ENNReal.ofReal (∫ ζ, ‖b ζ‖) * ENNReal.ofReal (10 * r / π) *
        (ENNReal.ofReal (2 * π) * ENNReal.ofReal (1 / (2 * r))) := by
    rw [← hradial]
    exact hmainbound
  rw [hSeq]
  refine hcombine.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hπ0 : (0:ℝ) < π := Real.pi_pos
  field_simp

/-- The measure bound on the union of enlarged balls. -/
theorem cz_enlarged_union_measure {ι : Type} [Countable ι] {Q : ι → Set ℂ} {c : ι → ℂ}
    {r : ι → ℝ} {lam : ℝ} (hlam : 0 < lam) {f : ℂ → ℂ}
    (hQball : ∀ i, 0 < r i ∧ Q i ⊆ closedBall (c i) (r i) ∧
      volume (closedBall (c i) (2 * r i)) ≤ ENNReal.ofReal (2 * π) * volume (Q i))
    (hQmeasSum : (∑' i, volume (Q i)) ≤ ENNReal.ofReal ((4 / lam) * ∫ z, ‖f z‖)) :
    volume (⋃ i, closedBall (c i) (2 * r i)) ≤
      ENNReal.ofReal ((8 * π / lam) * ∫ z, ‖f z‖) := by
  calc volume (⋃ i, closedBall (c i) (2 * r i)) ≤ ∑' i, volume (closedBall (c i) (2 * r i)) :=
        measure_iUnion_le _
    _ ≤ ∑' i, ENNReal.ofReal (2 * π) * volume (Q i) := ENNReal.tsum_le_tsum (fun i => (hQball i).2.2)
    _ = ENNReal.ofReal (2 * π) * ∑' i, volume (Q i) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (2 * π) * ENNReal.ofReal ((4 / lam) * ∫ z, ‖f z‖) :=
        mul_le_mul_right hQmeasSum _
    _ = ENNReal.ofReal ((2 * π) * ((4 / lam) * ∫ z, ‖f z‖)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ = ENNReal.ofReal ((8 * π / lam) * ∫ z, ‖f z‖) := by ring_nf

/-- The per-square tail bound in fully `lintegral`-native form. -/
theorem cz_tail_bound_lintegral {Q : Set ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hQsub : Q ⊆ closedBall c r) (hQmeas : MeasurableSet Q) {b : ℂ → ℂ}
    (hb_supp : ∀ ζ, ζ ∉ Q → b ζ = 0) (hmean : ∫ ζ in Q, b ζ = 0) (hb_int : Integrable b volume)
    (hb_L2 : MemLp b 2 volume) :
    (∫⁻ z in (closedBall c (2 * r))ᶜ, ‖hilbertH b z‖ₑ) ≤ 10 * ∫⁻ ζ, ‖b ζ‖ₑ := by
  have h1 := cz_tail_bound_final hr hQsub hQmeas hb_supp hmean hb_int hb_L2
  rwa [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 10),
    ofReal_integral_norm_eq_lintegral_enorm hb_int,
    show ENNReal.ofReal (10:ℝ) = (10:ℝ≥0∞) by norm_num] at h1

/-- Disjoint-support tsum identity for the lintegral of the enorm. -/
theorem cz_tsum_lintegral_indicator {ι : Type} [Countable ι] {Q : ι → Set ℂ}
    (hQmeas : ∀ i, MeasurableSet (Q i)) {b : ℂ → ℂ} (hbmeas : AEStronglyMeasurable b volume)
    (hQdisj : Pairwise (Function.onFun Disjoint Q))
    (hbsupp : (Function.support b : Set ℂ) ⊆ ⋃ i, Q i) :
    (∑' i, ∫⁻ ζ, ‖(Q i).indicator b ζ‖ₑ) = ∫⁻ ζ, ‖b ζ‖ₑ := by
  have hsubsingle : ∀ ζ, {i : ι | ζ ∈ Q i}.Subsingleton := by
    intro ζ i hi j hj
    by_contra hij
    exact (hQdisj hij).le_bot ⟨hi, hj⟩
  have hptwise : ∀ ζ, (∑' i, ‖(Q i).indicator b ζ‖ₑ) = ‖b ζ‖ₑ := by
    intro ζ
    by_cases hζ : ∃ i, ζ ∈ Q i
    · obtain ⟨i0, hi0⟩ := hζ
      rw [tsum_eq_single i0 (fun i hi => by
        rw [Set.indicator_of_notMem]
        · simp
        · intro hmem; exact hi (hsubsingle ζ hmem hi0))]
      rw [Set.indicator_of_mem hi0]
    · have hbz : b ζ = 0 := by
        by_contra hne
        exact hζ (Set.mem_iUnion.1 (hbsupp hne))
      have hall0 : ∀ i, (Q i).indicator b ζ = 0 := fun i =>
        Set.indicator_of_notMem (fun hmem => hζ ⟨i, hmem⟩) b
      simp_rw [hall0, hbz]
      simp
  calc (∑' i, ∫⁻ ζ, ‖(Q i).indicator b ζ‖ₑ) = ∫⁻ ζ, ∑' i, ‖(Q i).indicator b ζ‖ₑ := by
        rw [lintegral_tsum]
        intro i
        exact (hbmeas.indicator (hQmeas i)).aemeasurable.enorm
    _ = ∫⁻ ζ, ‖b ζ‖ₑ := by simp_rw [hptwise]


theorem cz_badpart_weakL1 {ι : Type} [Countable ι] {Q : ι → Set ℂ} {c : ι → ℂ} {r : ι → ℝ}
    {b f : ℂ → ℂ} {lam : ℝ} (hlam : 0 < lam)
    (hQmeas : ∀ i, MeasurableSet (Q i)) (hQdisj : Pairwise (Function.onFun Disjoint Q))
    (hQball : ∀ i, 0 < r i ∧ Q i ⊆ closedBall (c i) (r i) ∧
      volume (closedBall (c i) (2 * r i)) ≤ ENNReal.ofReal (2 * π) * volume (Q i))
    (hbsupp : (Function.support b : Set ℂ) ⊆ ⋃ i, Q i) (hbmean : ∀ i, ∫ ζ in Q i, b ζ = 0)
    (hb_int : Integrable b volume) (hb_L2 : MemLp b 2 volume)
    (hQmeasSum : (∑' i, volume (Q i)) ≤ ENNReal.ofReal ((4 / lam) * ∫ z, ‖f z‖)) :
    volume {z : ℂ | lam / 2 < ‖hilbertH b z‖} ≤
      ENNReal.ofReal ((8 * π / lam) * ∫ z, ‖f z‖) +
        ENNReal.ofReal (20 / lam) * ∫⁻ ζ, ‖b ζ‖ₑ := by
  set E : Set ℂ := ⋃ i, closedBall (c i) (2 * r i) with hEdef
  have hEmeas : MeasurableSet E := MeasurableSet.iUnion (fun _ => measurableSet_closedBall)
  have hEmeasure := cz_enlarged_union_measure hlam hQball hQmeasSum
  -- Step A: split into the enlarged-ball measure and the exterior piece.
  have hsub : {z : ℂ | lam / 2 < ‖hilbertH b z‖} ⊆ E ∪ (Eᶜ ∩ {z | lam / 2 < ‖hilbertH b z‖}) := by
    intro z hz
    by_cases hzE : z ∈ E
    · exact Or.inl hzE
    · exact Or.inr ⟨hzE, hz⟩
  have hstep1 := (measure_mono (μ := volume) hsub).trans (measure_union_le _ _)
  -- Step B: Markov on the exterior piece.
  have hHmeas : AEStronglyMeasurable (hilbertH b) volume := (hilbertH_memLp_two hb_L2).1.aestronglyMeasurable
  have hmarkov : ENNReal.ofReal (lam / 2) *
      volume (Eᶜ ∩ {z | ENNReal.ofReal (lam / 2) ≤ ‖hilbertH b z‖ₑ}) ≤
      ∫⁻ z in Eᶜ, ‖hilbertH b z‖ₑ := by
    rw [Set.inter_comm, ← Measure.restrict_apply' hEmeas.compl]
    exact mul_meas_ge_le_lintegral₀ hHmeas.aemeasurable.enorm.restrict _
  have hsetsub : Eᶜ ∩ {z : ℂ | lam / 2 < ‖hilbertH b z‖} ⊆
      Eᶜ ∩ {z | ENNReal.ofReal (lam / 2) ≤ ‖hilbertH b z‖ₑ} := by
    rintro z ⟨hz1, hz2⟩
    refine ⟨hz1, ?_⟩
    simp only [Set.mem_setOf_eq] at hz2 ⊢
    rw [← ofReal_norm]
    exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 hz2).le
  have hstep2 : ENNReal.ofReal (lam / 2) * volume (Eᶜ ∩ {z : ℂ | lam / 2 < ‖hilbertH b z‖}) ≤
      ∫⁻ z in Eᶜ, ‖hilbertH b z‖ₑ :=
    (mul_le_mul_right (measure_mono hsetsub) _).trans hmarkov
  -- Step C: the tail sum bound on the exterior integral.
  have hbi : ∀ i, MemLp ((Q i).indicator b) 2 volume := fun i => hb_L2.indicator (hQmeas i).nullMeasurableSet
  have hbi_int : ∀ i, Integrable ((Q i).indicator b) volume := fun i => hb_int.indicator (hQmeas i)
  have hbi_mean : ∀ i, ∫ ζ in Q i, (Q i).indicator b ζ = 0 := by
    intro i
    rw [setIntegral_congr_fun (hQmeas i) (fun ζ hζ => Set.indicator_of_mem hζ b)]
    exact hbmean i
  have hcountadd := cz_enorm_hilbertH_le_tsum hQmeas hQdisj hbsupp hb_L2
  have htailsum : (∫⁻ z in Eᶜ, ‖hilbertH b z‖ₑ) ≤ 10 * ∫⁻ ζ, ‖b ζ‖ₑ := by
    calc (∫⁻ z in Eᶜ, ‖hilbertH b z‖ₑ) ≤
        ∫⁻ z in Eᶜ, ∑' i, ‖hilbertH ((Q i).indicator b) z‖ₑ := by
          apply lintegral_mono_ae
          exact ae_restrict_of_ae hcountadd
      _ = ∑' i, ∫⁻ z in Eᶜ, ‖hilbertH ((Q i).indicator b) z‖ₑ := by
          rw [lintegral_tsum]
          intro i
          exact ((hilbertH_memLp_two (hbi i)).1.aemeasurable.enorm).restrict
      _ ≤ ∑' i, ∫⁻ z in (closedBall (c i) (2 * r i))ᶜ, ‖hilbertH ((Q i).indicator b) z‖ₑ := by
          apply ENNReal.tsum_le_tsum
          intro i
          apply lintegral_mono_set
          intro z hz
          simp only [hEdef, Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hz
          simp only [Set.mem_compl_iff]
          intro hz2r
          exact hz i hz2r
      _ ≤ ∑' i, 10 * ∫⁻ ζ, ‖(Q i).indicator b ζ‖ₑ := by
          apply ENNReal.tsum_le_tsum
          intro i
          exact cz_tail_bound_lintegral (hQball i).1 (hQball i).2.1 (hQmeas i)
            (fun ζ hζ => Set.indicator_of_notMem hζ b) (hbi_mean i) (hbi_int i) (hbi i)
      _ = 10 * ∑' i, ∫⁻ ζ, ‖(Q i).indicator b ζ‖ₑ := by rw [ENNReal.tsum_mul_left]
      _ = 10 * ∫⁻ ζ, ‖b ζ‖ₑ := by
          rw [cz_tsum_lintegral_indicator hQmeas hb_L2.aestronglyMeasurable hQdisj hbsupp]
  -- Combine.
  have hstep3 : volume (Eᶜ ∩ {z : ℂ | lam / 2 < ‖hilbertH b z‖}) ≤
      ENNReal.ofReal (20 / lam) * ∫⁻ ζ, ‖b ζ‖ₑ := by
    have h1 : ENNReal.ofReal (lam / 2) * volume (Eᶜ ∩ {z : ℂ | lam / 2 < ‖hilbertH b z‖}) ≤
        10 * ∫⁻ ζ, ‖b ζ‖ₑ := hstep2.trans htailsum
    have h2 : volume (Eᶜ ∩ {z : ℂ | lam / 2 < ‖hilbertH b z‖}) ≤
        (10 * ∫⁻ ζ, ‖b ζ‖ₑ) / ENNReal.ofReal (lam / 2) := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity : ENNReal.ofReal (lam/2) ≠ 0))
        (Or.inl ENNReal.ofReal_ne_top), mul_comm]
      exact h1
    have hfinal : (ENNReal.ofReal (lam / 2))⁻¹ * 10 = ENNReal.ofReal (20 / lam) := by
      rw [← ENNReal.ofReal_inv_of_pos (by positivity : (0:ℝ) < lam / 2),
        show (10:ℝ≥0∞) = ENNReal.ofReal 10 from by norm_num,
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (lam / 2)⁻¹)]
      congr 1
      field_simp
      ring
    refine h2.trans (le_of_eq ?_)
    rw [ENNReal.div_eq_inv_mul, ← mul_assoc, hfinal]
  exact hstep1.trans (add_le_add hEmeasure hstep3)

/-- The weak-(1,1) bound for `hilbertH` on `L¹ ∩ L²`, via the Calderón–Zygmund decomposition
(good part by Chebyshev at `p = 2`, bad part by the Hörmander-cancellation tail estimate).
`C = 88 + 8π`: `48` from the good part's Chebyshev step, `8π + 40` from the bad part's
enlarged-ball measure and tail-sum steps — not tight, only existence is used downstream. -/
theorem hilbertH_weakL1 :
    ∃ C : ℝ, ∀ f : ℂ → ℂ, Integrable f volume → MemLp f 2 volume →
      ∀ lam : ℝ, 0 < lam →
        volume {z : ℂ | lam < ‖hilbertH f z‖} ≤
          ENNReal.ofReal C * (∫⁻ z, ‖f z‖ₑ) / ENNReal.ofReal lam := by
  refine ⟨88 + 8 * π, fun f hf hf2 lam hlam => ?_⟩
  obtain ⟨g, b, ι, hι, Q, c, r, hQmeas, hQpos, hQdisj, hQball, hfgb, hgint, hbint,
    hgbound, hbnorm, hbmean, hbsupp, hQmeasSum⟩ := exists_czDecomposition hf hlam
  -- g, b ∈ L².
  have hgL2 : MemLp g 2 volume := by
    have hsq : Integrable (fun z => ‖g z‖ ^ 2) volume := by
      have hdom : ∀ᵐ z ∂volume, ‖(‖g z‖ ^ 2 : ℝ)‖ ≤ (4 * lam) * ‖g z‖ := by
        filter_upwards [hgbound] with z hz
        rw [Real.norm_of_nonneg (sq_nonneg _), sq]
        exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      exact Integrable.mono' (hgint.norm.const_mul (4 * lam)) (hgint.1.norm.pow 2) hdom
    exact (memLp_two_iff_integrable_sq_norm hgint.1).mpr hsq
  have hfeq : f = g + b := funext (fun z => hfgb z)
  have hbL2 : MemLp b 2 volume := by
    have : b = f - g := by rw [hfeq]; funext z; simp
    rw [this]; exact hf2.sub hgL2
  -- H f =ᵐ H g + H b.
  have hadd : hilbertH f =ᵐ[volume] fun z => hilbertH g z + hilbertH b z := by
    rw [hfeq]; exact hilbertH_add_ae hgL2 hbL2
  -- Reduce to the good/bad split (allowing for the a.e.-null set where `hadd` may fail).
  have hadd_null : volume {z : ℂ | hilbertH f z ≠ hilbertH g z + hilbertH b z} = 0 :=
    ae_iff.mp hadd
  have hsub2 : {z : ℂ | lam < ‖hilbertH f z‖} ⊆
      {z : ℂ | lam / 2 < ‖hilbertH g z‖} ∪ {z : ℂ | lam / 2 < ‖hilbertH b z‖} ∪
        {z : ℂ | hilbertH f z ≠ hilbertH g z + hilbertH b z} := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    by_cases heq : hilbertH f z = hilbertH g z + hilbertH b z
    · by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hcon
      obtain ⟨⟨hc1, hc2⟩, -⟩ := hcon
      rw [heq] at hz
      have htri := norm_add_le (hilbertH g z) (hilbertH b z)
      push_neg at hc1 hc2
      linarith
    · exact Or.inr heq
  have hstep0 : volume {z : ℂ | lam < ‖hilbertH f z‖} ≤
      volume {z : ℂ | lam / 2 < ‖hilbertH g z‖} + volume {z : ℂ | lam / 2 < ‖hilbertH b z‖} := by
    have hu1 : volume ({z : ℂ | lam / 2 < ‖hilbertH g z‖} ∪ {z : ℂ | lam / 2 < ‖hilbertH b z‖} ∪
          {z : ℂ | hilbertH f z ≠ hilbertH g z + hilbertH b z}) ≤
        volume ({z : ℂ | lam / 2 < ‖hilbertH g z‖} ∪ {z : ℂ | lam / 2 < ‖hilbertH b z‖}) +
          volume {z : ℂ | hilbertH f z ≠ hilbertH g z + hilbertH b z} :=
      measure_union_le _ _
    have hu2 : volume ({z : ℂ | lam / 2 < ‖hilbertH g z‖} ∪ {z : ℂ | lam / 2 < ‖hilbertH b z‖}) ≤
        volume {z : ℂ | lam / 2 < ‖hilbertH g z‖} + volume {z : ℂ | lam / 2 < ‖hilbertH b z‖} :=
      measure_union_le _ _
    calc volume {z : ℂ | lam < ‖hilbertH f z‖} ≤
          volume ({z : ℂ | lam / 2 < ‖hilbertH g z‖} ∪ {z : ℂ | lam / 2 < ‖hilbertH b z‖} ∪
            {z : ℂ | hilbertH f z ≠ hilbertH g z + hilbertH b z}) :=
          measure_mono (μ := volume) hsub2
      _ ≤ volume {z : ℂ | lam / 2 < ‖hilbertH g z‖} + volume {z : ℂ | lam / 2 < ‖hilbertH b z‖} +
          volume {z : ℂ | hilbertH f z ≠ hilbertH g z + hilbertH b z} :=
          hu1.trans (add_le_add hu2 (le_refl _))
      _ = volume {z : ℂ | lam / 2 < ‖hilbertH g z‖} + volume {z : ℂ | lam / 2 < ‖hilbertH b z‖} := by
          rw [hadd_null, add_zero]
  -- Bound `∫‖g‖`, `∫‖b‖` in terms of `∫‖f‖`.
  have hfnn : (0:ℝ) ≤ (∫ z, ‖f z‖) := integral_nonneg (fun z => norm_nonneg _)
  have hgle : ∫ z, ‖g z‖ ≤ (∫ z, ‖f z‖) + ∫ z, ‖b z‖ := by
    have hae : (fun z => ‖g z‖) ≤ᵐ[volume] fun z => ‖f z‖ + ‖b z‖ := by
      filter_upwards with z
      have hgz : g z = f z - b z := by rw [hfgb z]; ring
      rw [hgz]
      exact norm_sub_le _ _
    have hintegrable : Integrable (fun z => ‖f z‖ + ‖b z‖) volume := hf.norm.add hbint.norm
    exact (integral_mono_ae hgint.norm hintegrable hae).trans_eq
      (integral_add hf.norm hbint.norm)
  have hgle3 : ∫ z, ‖g z‖ ≤ 3 * (∫ z, ‖f z‖) := by linarith [hgle, hbnorm]
  -- Assemble.
  have hgoodbound := cz_hilbertH_good_chebyshev hgint hgbound hlam hgle3
  have hbadbound := cz_badpart_weakL1 hlam hQmeas hQdisj hQball hbsupp hbmean hbint hbL2 hQmeasSum
  have hbnnL : (0:ℝ) ≤ ∫ z, ‖b z‖ := integral_nonneg (fun z => norm_nonneg _)
  have hbintlint : (∫⁻ ζ, ‖b ζ‖ₑ) = ENNReal.ofReal (∫ ζ, ‖b ζ‖) :=
    (ofReal_integral_norm_eq_lintegral_enorm hbint).symm
  have hbadbound2 : volume {z : ℂ | lam / 2 < ‖hilbertH b z‖} ≤
      ENNReal.ofReal (((8 * π + 40) / lam) * (∫ z, ‖f z‖)) := by
    refine hbadbound.trans ?_
    rw [hbintlint]
    have h1 : ENNReal.ofReal (20 / lam) * ENNReal.ofReal (∫ ζ, ‖b ζ‖) ≤
        ENNReal.ofReal ((40 / lam) * (∫ z, ‖f z‖)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hscaled := mul_le_mul_of_nonneg_left hbnorm (show (0:ℝ) ≤ 20 / lam by positivity)
      have hring : (20 / lam) * (2 * ∫ z, ‖f z‖) = (40 / lam) * (∫ z, ‖f z‖) := by ring
      linarith [hscaled, hring]
    have hnn1 : (0:ℝ) ≤ 8 * π / lam * (∫ z, ‖f z‖) := mul_nonneg (by positivity) hfnn
    have hnn2 : (0:ℝ) ≤ 40 / lam * (∫ z, ‖f z‖) := mul_nonneg (by positivity) hfnn
    calc ENNReal.ofReal ((8 * π / lam) * (∫ z, ‖f z‖)) +
          ENNReal.ofReal (20 / lam) * ENNReal.ofReal (∫ ζ, ‖b ζ‖) ≤
        ENNReal.ofReal ((8 * π / lam) * (∫ z, ‖f z‖)) + ENNReal.ofReal ((40 / lam) * (∫ z, ‖f z‖)) :=
          add_le_add (le_refl _) h1
      _ = ENNReal.ofReal ((8 * π / lam) * (∫ z, ‖f z‖) + (40 / lam) * (∫ z, ‖f z‖)) :=
          (ENNReal.ofReal_add hnn1 hnn2).symm
      _ = ENNReal.ofReal (((8 * π + 40) / lam) * (∫ z, ‖f z‖)) := by
          congr 1; ring
  -- Combine good and bad, and match the target `ofReal C * (∫⁻‖f‖ₑ) / ofReal lam` shape.
  have hfintlint : (∫⁻ z, ‖f z‖ₑ) = ENNReal.ofReal (∫ z, ‖f z‖) :=
    (ofReal_integral_norm_eq_lintegral_enorm hf).symm
  rw [hfintlint]
  have hcombine : ENNReal.ofReal (48 * (∫ z, ‖f z‖)) / ENNReal.ofReal lam +
      ENNReal.ofReal (((8 * π + 40) / lam) * (∫ z, ‖f z‖)) =
      ENNReal.ofReal (88 + 8 * π) * ENNReal.ofReal (∫ z, ‖f z‖) / ENNReal.ofReal lam := by
    have e1 : ENNReal.ofReal (48 * (∫ z, ‖f z‖)) / ENNReal.ofReal lam =
        ENNReal.ofReal (48 * (∫ z, ‖f z‖) / lam) := (ENNReal.ofReal_div_of_pos hlam).symm
    have e2 : ENNReal.ofReal (88 + 8 * π) * ENNReal.ofReal (∫ z, ‖f z‖) / ENNReal.ofReal lam =
        ENNReal.ofReal ((88 + 8 * π) * (∫ z, ‖f z‖) / lam) := by
      rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_div_of_pos hlam]
    have hnn1 : (0:ℝ) ≤ 48 * (∫ z, ‖f z‖) / lam :=
      div_nonneg (mul_nonneg (by norm_num) hfnn) hlam.le
    have hnn2 : (0:ℝ) ≤ (8 * π + 40) / lam * (∫ z, ‖f z‖) :=
      mul_nonneg (by positivity) hfnn
    rw [e1, e2, ← ENNReal.ofReal_add hnn1 hnn2]
    congr 1
    field_simp
    ring
  calc volume {z : ℂ | lam < ‖hilbertH f z‖} ≤
        volume {z : ℂ | lam / 2 < ‖hilbertH g z‖} + volume {z : ℂ | lam / 2 < ‖hilbertH b z‖} :=
        hstep0
    _ ≤ ENNReal.ofReal (48 * (∫ z, ‖f z‖)) / ENNReal.ofReal lam +
          ENNReal.ofReal (((8 * π + 40) / lam) * (∫ z, ‖f z‖)) :=
        add_le_add hgoodbound hbadbound2
    _ = ENNReal.ofReal (88 + 8 * π) * ENNReal.ofReal (∫ z, ‖f z‖) / ENNReal.ofReal lam := hcombine




/-! ## S5-a: the symmetric pairing identity for `hilbertHSmooth` on `C₀^∞`.

Reformulates `hilbertHSmooth`'s defining limit (of the exterior-truncated integral, S11:1585) as
an EXACT (non-limiting) integral over any sufficiently large ball, by adapting `eq11_15`'s internal
argument (which is specific to Mathlib's own canonically-chosen support radius) to an arbitrary
caller-supplied radius `M`. This turns the pairing identity into a genuine Fubini swap on a finite
double integral instead of an interchange-of-limit-and-integral argument. -/

theorem hilbertHSmooth_eq_ballIntegral {ω : ℂ → ℂ} (hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω)
    (hc : HasCompactSupport ω) (z : ℂ) {M : ℝ} (hM : 0 < M)
    (hvanish : ∀ ζ, M ≤ ‖ζ - z‖ → ω ζ = 0) :
    hilbertHSmooth ω z = -(1 / π : ℂ) * ∫ ζ in ball z M, (ω ζ - ω z) / (ζ - z) ^ 2 := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hω (by simp)
  have hLnn : (0 : ℝ) ≤ L := L.2
  have hGm : AEStronglyMeasurable (fun ζ => (ω ζ - ω z) / (ζ - z) ^ 2) volume :=
    ((hω.continuous.measurable.sub_const _).div
      ((measurable_id.sub_const z).pow_const 2)).aestronglyMeasurable
  have hGb : ∀ ζ, ζ ≠ z → ‖(ω ζ - ω z) / (ζ - z) ^ 2‖ ≤ (L : ℝ) / ‖ζ - z‖ := by
    intro ζ hζ
    have hpos : 0 < ‖ζ - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hζ)
    have hlip := hL.dist_le_mul ζ z
    rw [dist_eq_norm, dist_eq_norm] at hlip
    rw [norm_div, norm_pow, div_le_div_iff₀ (by positivity) hpos]
    calc ‖ω ζ - ω z‖ * ‖ζ - z‖ ≤ (L * ‖ζ - z‖) * ‖ζ - z‖ := by gcongr
      _ = L * ‖ζ - z‖ ^ 2 := by ring
  have hGint : ∀ R, 0 < R → IntegrableOn (fun ζ => (ω ζ - ω z) / (ζ - z) ^ 2) (ball z R) :=
    fun R hR => integrableOn_ball_of_norm_le_div hLnn hR hGm hGb
  have hconst : ∀ R, M ≤ R → ∫ ζ in ball z R, (ω ζ - ω z) / (ζ - z) ^ 2 =
      ∫ ζ in ball z M, (ω ζ - ω z) / (ζ - z) ^ 2 := by
    intro R hR
    have hdiff := setIntegral_diff (μ := volume) measurableSet_ball (hGint R (hM.trans_le hR))
      (ball_subset_ball hR)
    have hzero : ∫ ζ in ball z R \ ball z M, (ω ζ - ω z) / (ζ - z) ^ 2 = 0 := by
      calc ∫ ζ in ball z R \ ball z M, (ω ζ - ω z) / (ζ - z) ^ 2
          = ∫ ζ in ball z R \ ball z M, -ω z * (1 / (ζ - z) ^ 2) := by
            refine setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball)
              fun ζ hζ => ?_
            have h2 : M ≤ ‖ζ - z‖ := by
              have h := hζ.2
              rw [mem_ball, dist_eq_norm, not_lt] at h
              exact h
            simp only [hvanish ζ h2]
            ring
        _ = -ω z * ∫ ζ in annulusAt z M R, 1 / (ζ - z) ^ 2 := by
            rw [integral_const_mul, setIntegral_congr_set (ball_diff_ball_ae_eq_annulusAt z M R)]
        _ = 0 := by
            rcases hR.lt_or_eq with hlt | heq
            · rw [integral_annulus_inv_sq z hM hlt, mul_zero]
            · have he : annulusAt z M R = ∅ := by
                ext ζ
                simp only [annulusAt, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and,
                  not_lt]
                intro h
                linarith
              rw [he, Measure.restrict_empty, integral_zero_measure, mul_zero]
    rw [hzero] at hdiff
    linear_combination -hdiff
  have hF : ∀ r, 0 < r → r < M →
      ∫ ζ in {ζ : ℂ | r < ‖ζ - z‖}, ω ζ / (ζ - z) ^ 2 =
        ∫ ζ in annulusAt z r M, (ω ζ - ω z) / (ζ - z) ^ 2 := by
    intro r hr hrM
    have hsub : annulusAt z r M ⊆ {ζ : ℂ | r < ‖ζ - z‖} := fun ζ hζ => hζ.1
    have hmeasT : MeasurableSet {ζ : ℂ | r < ‖ζ - z‖} :=
      measurableSet_lt measurable_const (measurable_id.sub_const z).norm
    rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero hmeasT hsub fun ζ hζ => ?_]
    · have hint1 : IntegrableOn (fun ζ => (ω ζ - ω z) / (ζ - z) ^ 2) (annulusAt z r M) :=
        (hGint M hM).mono_set fun ζ hζ => by rw [mem_ball, dist_eq_norm]; exact hζ.2
      have hint2 : IntegrableOn (fun ζ => ω z * (1 / (ζ - z) ^ 2)) (annulusAt z r M) := by
        have hK : IsCompact (closedBall z M ∩ {ζ : ℂ | r ≤ ‖ζ - z‖}) :=
          (isCompact_closedBall z M).inter_right
            (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
        have hcont : ContinuousOn (fun ζ => ω z * (1 / (ζ - z) ^ 2))
            (closedBall z M ∩ {ζ : ℂ | r ≤ ‖ζ - z‖}) := by
          refine continuousOn_const.mul (continuousOn_const.div
            ((continuousOn_id.sub continuousOn_const).pow 2) fun ζ hζ => ?_)
          have h1 : r ≤ ‖ζ - z‖ := hζ.2
          refine pow_ne_zero 2 fun h0 => ?_
          have h0' : ζ - z = 0 := h0
          rw [h0', norm_zero] at h1
          linarith
        refine (hcont.integrableOn_compact hK).mono_set fun ζ hζ => ⟨?_, hζ.1.le⟩
        rw [mem_closedBall, dist_eq_norm]
        exact hζ.2.le
      calc ∫ ζ in annulusAt z r M, ω ζ / (ζ - z) ^ 2
          = ∫ ζ in annulusAt z r M, ((ω ζ - ω z) / (ζ - z) ^ 2 + ω z * (1 / (ζ - z) ^ 2)) := by
            refine setIntegral_congr_fun measurableSet_annulusAt fun ζ _ => ?_
            ring
        _ = ∫ ζ in annulusAt z r M, (ω ζ - ω z) / (ζ - z) ^ 2 := by
            rw [integral_add hint1 hint2, integral_const_mul, integral_annulus_inv_sq z hr hrM,
              mul_zero, add_zero]
    · have h1 : r < ‖ζ - z‖ := hζ.1
      have h3 : M ≤ ‖ζ - z‖ := by
        by_contra h
        exact hζ.2 ⟨h1, not_le.1 h⟩
      rw [hvanish ζ h3, zero_div]
  have hlim : Tendsto (fun r => ∫ ζ in annulusAt z r M, (ω ζ - ω z) / (ζ - z) ^ 2) (𝓝[>] 0)
      (𝓝 (∫ ζ in ball z M, (ω ζ - ω z) / (ζ - z) ^ 2)) := by
    rw [tendsto_iff_edist_tendsto_0]
    have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        edist (∫ ζ in annulusAt z r M, (ω ζ - ω z) / (ζ - z) ^ 2)
          (∫ ζ in ball z M, (ω ζ - ω z) / (ζ - z) ^ 2) ≤ ENNReal.ofReal (L * (4 * π * r)) := by
      filter_upwards [Ioo_mem_nhdsGT hM] with r hr
      have hsubA : annulusAt z r M ⊆ ball z M := fun ζ hζ => by
        rw [mem_ball, dist_eq_norm]; exact hζ.2
      rw [edist_comm, edist_eq_enorm_sub, ← setIntegral_diff measurableSet_annulusAt (hGint M hM) hsubA]
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      refine (lintegral_mono_set (t := ball z (2 * r)) fun ζ hζ => ?_).trans
        ((lintegral_enorm_le_of_norm_le_div hLnn _ hGb).trans (le_of_eq ?_))
      · have h1 : ‖ζ - z‖ < M := by
          have h := hζ.1
          rw [mem_ball, dist_eq_norm] at h
          exact h
        have h2 : ‖ζ - z‖ ≤ r := by
          by_contra h
          exact hζ.2 ⟨not_le.1 h, h1⟩
        rw [mem_ball, dist_eq_norm]
        linarith [hr.1]
      · rw [lintegral_ball_sub_enorm_rpow_neg (by norm_num) (by linarith [hr.1]) z,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hLnn,
          show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, div_one]
        congr 1
        ring
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
      (Eventually.of_forall fun _ => zero_le) hbound
    have h := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := (L : ℝ))).mul
      ((tendsto_id (x := 𝓝 (0 : ℝ))).const_mul (4 * π)))
    simp only [id, mul_zero, ENNReal.ofReal_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hFlim : Tendsto (fun r => -(1 / π : ℂ) * ∫ ζ in {ζ : ℂ | r < ‖ζ - z‖}, ω ζ / (ζ - z) ^ 2)
      (𝓝[>] 0) (𝓝 (-(1 / π : ℂ) * ∫ ζ in ball z M, (ω ζ - ω z) / (ζ - z) ^ 2)) := by
    refine (hlim.const_mul (-(1 / π : ℂ))).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hM] with r hr
    rw [hF r hr.1 hr.2]
  exact hFlim.limUnder_eq

/-- The cancelled kernel `(ω ζ - ω z)/(ζ - z)²` is integrable on any ball around `z`, via the same
global-Lipschitz argument as `hilbertHSmooth_eq_ballIntegral` (factored out for reuse). -/
theorem integrableOn_ball_kernel_cancel {ω : ℂ → ℂ} (hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω)
    (hc : HasCompactSupport ω) (z : ℂ) (R : ℝ) :
    IntegrableOn (fun ζ => (ω ζ - ω z) / (ζ - z) ^ 2) (ball z R) := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hω (by simp)
  have hLnn : (0 : ℝ) ≤ L := L.2
  have hGm : AEStronglyMeasurable (fun ζ => (ω ζ - ω z) / (ζ - z) ^ 2) volume :=
    ((hω.continuous.measurable.sub_const _).div
      ((measurable_id.sub_const z).pow_const 2)).aestronglyMeasurable
  have hGb : ∀ ζ, ζ ≠ z → ‖(ω ζ - ω z) / (ζ - z) ^ 2‖ ≤ (L : ℝ) / ‖ζ - z‖ := by
    intro ζ hζ
    have hpos : 0 < ‖ζ - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hζ)
    have hlip := hL.dist_le_mul ζ z
    rw [dist_eq_norm, dist_eq_norm] at hlip
    rw [norm_div, norm_pow, div_le_div_iff₀ (by positivity) hpos]
    calc ‖ω ζ - ω z‖ * ‖ζ - z‖ ≤ (L * ‖ζ - z‖) * ‖ζ - z‖ := by gcongr
      _ = L * ‖ζ - z‖ ^ 2 := by ring
  by_cases hR : 0 < R
  · exact integrableOn_ball_of_norm_le_div hLnn hR hGm hGb
  · push_neg at hR
    rw [ball_eq_empty.mpr hR]
    exact integrableOn_empty

/-- **S5-a.** The Hilbert-transform pairing `∫ (Hf)·g = ∫ f·(Hg)` for `C₀^∞` functions.
Route: reformulate both `hilbertHSmooth`'s as EXACT (non-limiting) integrals over a common large
ball `M` (via `hilbertHSmooth_eq_ballIntegral`), turning the identity into a finite double
integral; then use the antisymmetry of `D(z,ζ) := g(z)f(ζ)/(ζ-z)² - f(z)g(ζ)/(ζ-z)²` under
`(z,ζ) ↦ (ζ,z)` (a measure-preserving swap of `ℂ × ℂ`) to show its integral vanishes. -/
theorem hilbertH_pairing_symm {f g : ℂ → ℂ}
    (hf1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hf2 : HasCompactSupport f)
    (hg1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hg2 : HasCompactSupport g) :
    ∫ z, hilbertHSmooth f z * g z = ∫ z, f z * hilbertHSmooth g z := by
  obtain ⟨Rf, hRf⟩ := hf2.isCompact.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨Rg, hRg⟩ := hg2.isCompact.isBounded.subset_closedBall (0 : ℂ)
  set M := max Rf 0 + max Rg 0 + 1 with hM_def
  have hM0 : (0 : ℝ) < M := by positivity
  have hvanish_f_at : ∀ z : ℂ, ‖z‖ ≤ max Rg 0 → ∀ ζ, M ≤ ‖ζ - z‖ → f ζ = 0 := by
    intro z hz ζ hζ
    by_contra hfne
    have hζmem : ζ ∈ tsupport f := subset_tsupport f hfne
    have hζnorm : ‖ζ‖ ≤ Rf := by
      have := hRf hζmem; rwa [mem_closedBall, dist_eq_norm, sub_zero] at this
    have hle : ‖ζ - z‖ ≤ max Rf 0 + max Rg 0 :=
      (norm_sub_le _ _).trans (add_le_add (hζnorm.trans (le_max_left _ _)) hz)
    rw [hM_def] at hζ
    linarith
  have hvanish_g_at : ∀ z : ℂ, ‖z‖ ≤ max Rf 0 → ∀ ζ, M ≤ ‖ζ - z‖ → g ζ = 0 := by
    intro z hz ζ hζ
    by_contra hgne
    have hζmem : ζ ∈ tsupport g := subset_tsupport g hgne
    have hζnorm : ‖ζ‖ ≤ Rg := by
      have := hRg hζmem; rwa [mem_closedBall, dist_eq_norm, sub_zero] at this
    have hle : ‖ζ - z‖ ≤ max Rg 0 + max Rf 0 :=
      (norm_sub_le _ _).trans (add_le_add (hζnorm.trans (le_max_left _ _)) hz)
    rw [hM_def] at hζ
    linarith
  have hf_ball : ∀ z : ℂ, ‖z‖ ≤ max Rg 0 → hilbertHSmooth f z =
      -(1 / π : ℂ) * ∫ ζ in ball z M, (f ζ - f z) / (ζ - z) ^ 2 :=
    fun z hz => hilbertHSmooth_eq_ballIntegral hf1 hf2 z hM0 (hvanish_f_at z hz)
  have hg_ball : ∀ z : ℂ, ‖z‖ ≤ max Rf 0 → hilbertHSmooth g z =
      -(1 / π : ℂ) * ∫ ζ in ball z M, (g ζ - g z) / (ζ - z) ^ 2 :=
    fun z hz => hilbertHSmooth_eq_ballIntegral hg1 hg2 z hM0 (hvanish_g_at z hz)
  have heq1 : ∀ z, hilbertHSmooth f z * g z =
      (-(1 / π : ℂ) * ∫ ζ in ball z M, (f ζ - f z) / (ζ - z) ^ 2) * g z := by
    intro z
    by_cases hz : g z = 0
    · rw [hz, mul_zero, mul_zero]
    · have hzmem : z ∈ tsupport g := subset_tsupport g hz
      have hznorm : ‖z‖ ≤ Rg := by
        have := hRg hzmem; rwa [mem_closedBall, dist_eq_norm, sub_zero] at this
      rw [hf_ball z (hznorm.trans (le_max_left _ _))]
  have heq2 : ∀ z, f z * hilbertHSmooth g z =
      f z * (-(1 / π : ℂ) * ∫ ζ in ball z M, (g ζ - g z) / (ζ - z) ^ 2) := by
    intro z
    by_cases hz : f z = 0
    · rw [hz, zero_mul, zero_mul]
    · have hzmem : z ∈ tsupport f := subset_tsupport f hz
      have hznorm : ‖z‖ ≤ Rf := by
        have := hRf hzmem; rwa [mem_closedBall, dist_eq_norm, sub_zero] at this
      rw [hg_ball z (hznorm.trans (le_max_left _ _))]
  -- The joint (antisymmetric-under-swap) integrand and its domination.
  obtain ⟨Lf, hLf⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hf2 hf1 (by simp)
  obtain ⟨Lg, hLg⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hg2 hg1 (by simp)
  have hLfnn : (0 : ℝ) ≤ Lf := Lf.2
  have hLgnn : (0 : ℝ) ≤ Lg := Lg.2
  set S : Set (ℂ × ℂ) := {p : ℂ × ℂ | ‖p.2 - p.1‖ < M} with hS_def
  have hS_open : IsOpen S := isOpen_Iio.preimage (continuous_snd.sub continuous_fst).norm
  have hS_meas : MeasurableSet S := hS_open.measurableSet
  set Φ : ℂ × ℂ → ℂ := fun p => S.indicator (fun p => g p.1 * (f p.2 - f p.1) / (p.2 - p.1) ^ 2) p
    with hΦ_def
  set Ψ : ℂ × ℂ → ℂ := fun p => S.indicator (fun p => f p.1 * (g p.2 - g p.1) / (p.2 - p.1) ^ 2) p
    with hΨ_def
  set D : ℂ × ℂ → ℂ := fun p => Φ p - Ψ p with hD_def
  set BND : ℂ × ℂ → ℝ≥0∞ := fun p =>
    S.indicator (fun p => ((Lf : ℝ≥0∞) * ‖g p.1‖ₑ + (Lg : ℝ≥0∞) * ‖f p.1‖ₑ) *
      ‖p.2 - p.1‖ₑ ^ (-1 : ℝ)) p with hBND_def
  have hgm : Measurable (fun p : ℂ × ℂ => ‖g p.1‖ₑ) :=
    (hg1.continuous.comp continuous_fst).enorm.measurable
  have hfm : Measurable (fun p : ℂ × ℂ => ‖f p.1‖ₑ) :=
    (hf1.continuous.comp continuous_fst).enorm.measurable
  have hrpowm : Measurable (fun p : ℂ × ℂ => ‖p.2 - p.1‖ₑ ^ (-1 : ℝ)) :=
    (ENNReal.continuous_rpow_const.comp (continuous_snd.sub continuous_fst).enorm).measurable
  have hBND_meas : Measurable BND :=
    Measurable.indicator (((measurable_const.mul hgm).add (measurable_const.mul hfm)).mul
      hrpowm) hS_meas
  have hval : ENNReal.ofReal (2 * π) * ENNReal.ofReal (M ^ ((2:ℝ) - 1) / ((2:ℝ) - 1)) =
      ENNReal.ofReal (2 * π * M) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    ring
  have hBND_lt_top : ∫⁻ p : ℂ × ℂ, BND p ∂(volume.prod volume) < ⊤ := by
    rw [lintegral_prod _ hBND_meas.aemeasurable]
    have hstep : ∀ z, ∫⁻ ζ, BND (z, ζ) ∂volume =
        ((Lf : ℝ≥0∞) * ‖g z‖ₑ + (Lg : ℝ≥0∞) * ‖f z‖ₑ) * ENNReal.ofReal (2 * π * M) := by
      intro z
      have hrw : (fun ζ => BND (z, ζ)) = (ball z M).indicator
          (fun ζ => ((Lf : ℝ≥0∞) * ‖g z‖ₑ + (Lg : ℝ≥0∞) * ‖f z‖ₑ) * ‖ζ - z‖ₑ ^ (-1 : ℝ)) := by
        funext ζ
        by_cases hmem : ζ ∈ ball z M
        · have hSmem : (z, ζ) ∈ S := by
            rw [hS_def, mem_setOf_eq]; rwa [mem_ball, dist_eq_norm] at hmem
          rw [hBND_def]
          simp only [Set.indicator_of_mem hSmem, Set.indicator_of_mem hmem]
        · have hSnmem : (z, ζ) ∉ S := by
            rw [hS_def, mem_setOf_eq]
            rw [mem_ball, dist_eq_norm] at hmem
            exact hmem
          rw [hBND_def]
          simp only [Set.indicator_of_notMem hSnmem, Set.indicator_of_notMem hmem]
      rw [hrw, lintegral_indicator measurableSet_ball, lintegral_const_mul' _ _ (by finiteness),
        lintegral_ball_sub_enorm_rpow_neg (by norm_num : (1:ℝ) < 2) hM0 z, hval]
    simp_rw [hstep, mul_comm _ (ENNReal.ofReal (2*π*M))]
    rw [lintegral_const_mul' _ _ (by finiteness : ENNReal.ofReal (2*π*M) ≠ ⊤),
      lintegral_add_left (hg1.continuous.enorm.measurable.const_mul _),
      lintegral_const_mul' _ _ (by finiteness : (Lf:ℝ≥0∞) ≠ ⊤),
      lintegral_const_mul' _ _ (by finiteness : (Lg:ℝ≥0∞) ≠ ⊤)]
    have h1 : (Lf : ℝ≥0∞) * ∫⁻ z, ‖g z‖ₑ ∂volume < ⊤ :=
      ENNReal.mul_lt_top ENNReal.coe_lt_top
        (hg1.continuous.integrable_of_hasCompactSupport hg2).2
    have h2 : (Lg : ℝ≥0∞) * ∫⁻ z, ‖f z‖ₑ ∂volume < ⊤ :=
      ENNReal.mul_lt_top ENNReal.coe_lt_top
        (hf1.continuous.integrable_of_hasCompactSupport hf2).2
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨h1, h2⟩)
  -- Φ, Ψ (hence D) are dominated by BND, so integrable on `ℂ × ℂ`.
  have hΦ_meas : AEStronglyMeasurable Φ (volume.prod volume) := by
    rw [hΦ_def]
    apply Measurable.aestronglyMeasurable
    apply Measurable.indicator _ hS_meas
    exact ((hg1.continuous.comp continuous_fst).mul
      ((hf1.continuous.comp continuous_snd).sub (hf1.continuous.comp continuous_fst))).measurable.div
      ((continuous_snd.sub continuous_fst).pow 2).measurable
  have hΨ_meas : AEStronglyMeasurable Ψ (volume.prod volume) := by
    rw [hΨ_def]
    apply Measurable.aestronglyMeasurable
    apply Measurable.indicator _ hS_meas
    exact ((hf1.continuous.comp continuous_fst).mul
      ((hg1.continuous.comp continuous_snd).sub (hg1.continuous.comp continuous_fst))).measurable.div
      ((continuous_snd.sub continuous_fst).pow 2).measurable
  have hΦ_le : ∀ p, ‖Φ p‖ₑ ≤ BND p := by
    intro p
    simp only [hΦ_def, hBND_def]
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
      by_cases hpe : p.2 = p.1
      · simp [hpe]
      · have hpos : 0 < ‖p.2 - p.1‖ := norm_pos_iff.2 (sub_ne_zero.2 hpe)
        have hGb : ‖(f p.2 - f p.1) / (p.2 - p.1) ^ 2‖ ≤ (Lf : ℝ) / ‖p.2 - p.1‖ := by
          have hlip := hLf.dist_le_mul p.2 p.1
          rw [dist_eq_norm, dist_eq_norm] at hlip
          rw [norm_div, norm_pow, div_le_div_iff₀ (by positivity) hpos]
          calc ‖f p.2 - f p.1‖ * ‖p.2 - p.1‖ ≤ (Lf * ‖p.2 - p.1‖) * ‖p.2 - p.1‖ := by gcongr
            _ = Lf * ‖p.2 - p.1‖ ^ 2 := by ring
        have hgoal_eq : ‖g p.1 * (f p.2 - f p.1) / (p.2 - p.1) ^ 2‖ₑ =
            ENNReal.ofReal (‖g p.1‖ * ‖(f p.2 - f p.1) / (p.2 - p.1) ^ 2‖) := by
          rw [← ofReal_norm, mul_div_assoc, norm_mul]
        rw [hgoal_eq]
        calc ENNReal.ofReal (‖g p.1‖ * ‖(f p.2 - f p.1) / (p.2 - p.1) ^ 2‖)
            ≤ ENNReal.ofReal (‖g p.1‖ * ((Lf:ℝ) / ‖p.2 - p.1‖)) := by
              apply ENNReal.ofReal_le_ofReal
              exact mul_le_mul_of_nonneg_left hGb (norm_nonneg _)
          _ ≤ ENNReal.ofReal (((Lf:ℝ) * ‖g p.1‖ + (Lg:ℝ) * ‖f p.1‖) / ‖p.2 - p.1‖) := by
              apply ENNReal.ofReal_le_ofReal
              have e1 : ‖g p.1‖ * ((Lf:ℝ) / ‖p.2 - p.1‖) =
                  ((Lf:ℝ) * ‖g p.1‖) * (‖p.2 - p.1‖)⁻¹ := by rw [div_eq_mul_inv]; ring
              have e2 : ((Lf:ℝ) * ‖g p.1‖ + (Lg:ℝ) * ‖f p.1‖) / ‖p.2 - p.1‖ =
                  ((Lf:ℝ) * ‖g p.1‖ + (Lg:ℝ) * ‖f p.1‖) * (‖p.2 - p.1‖)⁻¹ := div_eq_mul_inv _ _
              rw [e1, e2]
              apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hpos.le)
              linarith [mul_nonneg hLgnn (norm_nonneg (f p.1))]
          _ = ((Lf:ℝ≥0∞) * ‖g p.1‖ₑ + (Lg:ℝ≥0∞) * ‖f p.1‖ₑ) * ‖p.2 - p.1‖ₑ ^ (-1 : ℝ) := by
              rw [← ofReal_norm (g p.1), ← ofReal_norm (f p.1), ← ofReal_norm (p.2 - p.1),
                ENNReal.ofReal_rpow_of_pos hpos,
                show ((Lf:ℝ≥0∞)) = ENNReal.ofReal (Lf:ℝ) from (ENNReal.ofReal_coe_nnreal).symm,
                show ((Lg:ℝ≥0∞)) = ENNReal.ofReal (Lg:ℝ) from (ENNReal.ofReal_coe_nnreal).symm,
                ← ENNReal.ofReal_mul hLfnn, ← ENNReal.ofReal_mul hLgnn,
                ← ENNReal.ofReal_add (by positivity) (by positivity),
                ← ENNReal.ofReal_mul (by positivity)]
              congr 1
              rw [Real.rpow_neg_one]
              ring
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]
      simp
  have hΨ_le : ∀ p, ‖Ψ p‖ₑ ≤ BND p := by
    intro p
    simp only [hΨ_def, hBND_def]
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
      by_cases hpe : p.2 = p.1
      · simp [hpe]
      · have hpos : 0 < ‖p.2 - p.1‖ := norm_pos_iff.2 (sub_ne_zero.2 hpe)
        have hGb : ‖(g p.2 - g p.1) / (p.2 - p.1) ^ 2‖ ≤ (Lg : ℝ) / ‖p.2 - p.1‖ := by
          have hlip := hLg.dist_le_mul p.2 p.1
          rw [dist_eq_norm, dist_eq_norm] at hlip
          rw [norm_div, norm_pow, div_le_div_iff₀ (by positivity) hpos]
          calc ‖g p.2 - g p.1‖ * ‖p.2 - p.1‖ ≤ (Lg * ‖p.2 - p.1‖) * ‖p.2 - p.1‖ := by gcongr
            _ = Lg * ‖p.2 - p.1‖ ^ 2 := by ring
        have hgoal_eq : ‖f p.1 * (g p.2 - g p.1) / (p.2 - p.1) ^ 2‖ₑ =
            ENNReal.ofReal (‖f p.1‖ * ‖(g p.2 - g p.1) / (p.2 - p.1) ^ 2‖) := by
          rw [← ofReal_norm, mul_div_assoc, norm_mul]
        rw [hgoal_eq]
        calc ENNReal.ofReal (‖f p.1‖ * ‖(g p.2 - g p.1) / (p.2 - p.1) ^ 2‖)
            ≤ ENNReal.ofReal (‖f p.1‖ * ((Lg:ℝ) / ‖p.2 - p.1‖)) := by
              apply ENNReal.ofReal_le_ofReal
              exact mul_le_mul_of_nonneg_left hGb (norm_nonneg _)
          _ ≤ ENNReal.ofReal (((Lf:ℝ) * ‖g p.1‖ + (Lg:ℝ) * ‖f p.1‖) / ‖p.2 - p.1‖) := by
              apply ENNReal.ofReal_le_ofReal
              have e1 : ‖f p.1‖ * ((Lg:ℝ) / ‖p.2 - p.1‖) =
                  ((Lg:ℝ) * ‖f p.1‖) * (‖p.2 - p.1‖)⁻¹ := by rw [div_eq_mul_inv]; ring
              have e2 : ((Lf:ℝ) * ‖g p.1‖ + (Lg:ℝ) * ‖f p.1‖) / ‖p.2 - p.1‖ =
                  ((Lf:ℝ) * ‖g p.1‖ + (Lg:ℝ) * ‖f p.1‖) * (‖p.2 - p.1‖)⁻¹ := div_eq_mul_inv _ _
              rw [e1, e2]
              apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hpos.le)
              linarith [mul_nonneg hLfnn (norm_nonneg (g p.1))]
          _ = ((Lf:ℝ≥0∞) * ‖g p.1‖ₑ + (Lg:ℝ≥0∞) * ‖f p.1‖ₑ) * ‖p.2 - p.1‖ₑ ^ (-1 : ℝ) := by
              rw [← ofReal_norm (g p.1), ← ofReal_norm (f p.1), ← ofReal_norm (p.2 - p.1),
                ENNReal.ofReal_rpow_of_pos hpos,
                show ((Lf:ℝ≥0∞)) = ENNReal.ofReal (Lf:ℝ) from (ENNReal.ofReal_coe_nnreal).symm,
                show ((Lg:ℝ≥0∞)) = ENNReal.ofReal (Lg:ℝ) from (ENNReal.ofReal_coe_nnreal).symm,
                ← ENNReal.ofReal_mul hLfnn, ← ENNReal.ofReal_mul hLgnn,
                ← ENNReal.ofReal_add (by positivity) (by positivity),
                ← ENNReal.ofReal_mul (by positivity)]
              congr 1
              rw [Real.rpow_neg_one]
              ring
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]
      simp
  have hΦ_int : Integrable Φ (volume.prod volume) :=
    ⟨hΦ_meas, lt_of_le_of_lt (lintegral_mono hΦ_le) hBND_lt_top⟩
  have hΨ_int : Integrable Ψ (volume.prod volume) :=
    ⟨hΨ_meas, lt_of_le_of_lt (lintegral_mono hΨ_le) hBND_lt_top⟩
  have hD_int : Integrable D (volume.prod volume) := hΦ_int.sub hΨ_int
  -- Antisymmetry: `D ∘ Prod.swap = -D`, so `∫ D = 0`.
  have hD_swap : ∀ p : ℂ × ℂ, D p.swap = -D p := by
    intro p
    simp only [hD_def, hΦ_def, hΨ_def, Prod.swap]
    by_cases hp : p ∈ S
    · have hp' : (p.2, p.1) ∈ S := by
        simp only [hS_def, mem_setOf_eq] at hp ⊢
        rwa [show p.1 - p.2 = -(p.2 - p.1) by ring, norm_neg]
      simp only [Set.indicator_of_mem hp', Set.indicator_of_mem hp]
      rw [show (p.1 - p.2) ^ 2 = (p.2 - p.1) ^ 2 by ring]
      field_simp
      ring
    · have hp' : (p.2, p.1) ∉ S := by
        simp only [hS_def, mem_setOf_eq] at hp ⊢
        rwa [show p.1 - p.2 = -(p.2 - p.1) by ring, norm_neg]
      simp only [Set.indicator_of_notMem hp', Set.indicator_of_notMem hp, neg_zero]
      ring
  have hD_zero : ∫ p, D p ∂(volume.prod volume) = 0 := by
    have hswap := integral_prod_swap D (μ := volume) (ν := volume)
    simp only [hD_swap] at hswap
    rw [integral_neg] at hswap
    linear_combination -hswap / 2
  have hΦΨ_eq : ∫ p, Φ p ∂(volume.prod volume) = ∫ p, Ψ p ∂(volume.prod volume) := by
    have h := integral_sub hΦ_int hΨ_int
    have hD_zero' : ∫ p, (Φ p - Ψ p) ∂(volume.prod volume) = 0 := hD_zero
    linear_combination hD_zero' - h
  have hΦ_slice : ∀ z, ∫ ζ, Φ (z, ζ) ∂volume =
      g z * ∫ ζ in ball z M, (f ζ - f z) / (ζ - z) ^ 2 := by
    intro z
    have hrw : (fun ζ => Φ (z, ζ)) =
        (ball z M).indicator (fun ζ => g z * ((f ζ - f z) / (ζ - z) ^ 2)) := by
      funext ζ
      by_cases hmem : ζ ∈ ball z M
      · have hSmem : (z, ζ) ∈ S := by
          rw [hS_def, mem_setOf_eq]; rwa [mem_ball, dist_eq_norm] at hmem
        simp only [hΦ_def, Set.indicator_of_mem hSmem, Set.indicator_of_mem hmem, mul_div_assoc]
      · have hSnmem : (z, ζ) ∉ S := by
          rw [hS_def, mem_setOf_eq]; rw [mem_ball, dist_eq_norm] at hmem; exact hmem
        simp only [hΦ_def, Set.indicator_of_notMem hSnmem, Set.indicator_of_notMem hmem]
    rw [hrw, integral_indicator measurableSet_ball, integral_const_mul]
  have hΨ_slice : ∀ z, ∫ ζ, Ψ (z, ζ) ∂volume =
      f z * ∫ ζ in ball z M, (g ζ - g z) / (ζ - z) ^ 2 := by
    intro z
    have hrw : (fun ζ => Ψ (z, ζ)) =
        (ball z M).indicator (fun ζ => f z * ((g ζ - g z) / (ζ - z) ^ 2)) := by
      funext ζ
      by_cases hmem : ζ ∈ ball z M
      · have hSmem : (z, ζ) ∈ S := by
          rw [hS_def, mem_setOf_eq]; rwa [mem_ball, dist_eq_norm] at hmem
        simp only [hΨ_def, Set.indicator_of_mem hSmem, Set.indicator_of_mem hmem, mul_div_assoc]
      · have hSnmem : (z, ζ) ∉ S := by
          rw [hS_def, mem_setOf_eq]; rw [mem_ball, dist_eq_norm] at hmem; exact hmem
        simp only [hΨ_def, Set.indicator_of_notMem hSnmem, Set.indicator_of_notMem hmem]
    rw [hrw, integral_indicator measurableSet_ball, integral_const_mul]
  have hΦ_total : ∫ p, Φ p ∂(volume.prod volume) =
      -(π:ℂ) * ∫ z, hilbertHSmooth f z * g z := by
    rw [integral_prod Φ hΦ_int]
    simp_rw [hΦ_slice]
    rw [show (fun z => g z * ∫ ζ in ball z M, (f ζ - f z) / (ζ - z) ^ 2) =
        (fun z => -(π:ℂ) * (hilbertHSmooth f z * g z)) from ?_]
    · rw [integral_const_mul]
    · funext z
      by_cases hz : g z = 0
      · simp [hz]
      · have hzmem : z ∈ tsupport g := subset_tsupport g hz
        have hznorm : ‖z‖ ≤ Rg := by
          have := hRg hzmem; rwa [mem_closedBall, dist_eq_norm, sub_zero] at this
        rw [hf_ball z (hznorm.trans (le_max_left _ _))]
        have hπ : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        field_simp
  have hΨ_total : ∫ p, Ψ p ∂(volume.prod volume) =
      -(π:ℂ) * ∫ z, f z * hilbertHSmooth g z := by
    rw [integral_prod Ψ hΨ_int]
    simp_rw [hΨ_slice]
    rw [show (fun z => f z * ∫ ζ in ball z M, (g ζ - g z) / (ζ - z) ^ 2) =
        (fun z => -(π:ℂ) * (f z * hilbertHSmooth g z)) from ?_]
    · rw [integral_const_mul]
    · funext z
      by_cases hz : f z = 0
      · simp [hz]
      · have hzmem : z ∈ tsupport f := subset_tsupport f hz
        have hznorm : ‖z‖ ≤ Rf := by
          have := hRf hzmem; rwa [mem_closedBall, dist_eq_norm, sub_zero] at this
        rw [hg_ball z (hznorm.trans (le_max_left _ _))]
        have hπ : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        field_simp
  have hπ : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hfinal : -(π:ℂ) * ∫ z, hilbertHSmooth f z * g z = -(π:ℂ) * ∫ z, f z * hilbertHSmooth g z := by
    rw [← hΦ_total, ← hΨ_total, hΦΨ_eq]
  exact mul_left_cancel₀ (neg_ne_zero.mpr hπ) hfinal



/-! ## S4: Marcinkiewicz interpolation, `1 < p < 2`, from weak-(1,1) + the `L²` isometry.

Route (classical layer-cake / distribution-function method): for `ω ∈ L² ∩ L^p` and `λ > 0`,
split `ω = ω·1_{|ω|>λ} + ω·1_{|ω|≤λ}`; `hilbertH_add_ae` (unconditional at `p = 2`) gives
`{|Hω| > λ} ⊆ᵐ {|Hω₁| > λ/2} ∪ {|Hω₂| > λ/2}`; bound the first tail by the weak-(1,1) hypothesis
and the second by Chebyshev + the `L²` isometry; then `‖Hω‖_p^p = p∫₀^∞ λ^{p-1}·vol{|Hω|>λ}dλ`
(layer cake) and Tonelli turn the two tail bounds into `(2C'p/(p-1))‖ω‖_p^p` (needs `p > 1` for the
inner radial integral `∫₀^a t^{p-2}dt` to converge) and `(4p/(2-p))‖ω‖_p^p` (needs `p < 2` for
`∫_a^∞ t^{p-3}dt` to converge) respectively — giving `A^p = p·(2C'/(p-1) + 4/(2-p))`. -/

theorem hilbertH_boundedLp_of_lt_two {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ A : ℝ, ∀ ω : ℂ → ℂ, MemLp ω 2 → MemLp ω (ENNReal.ofReal p) →
      eLpNorm (hilbertH ω) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal A * eLpNorm ω (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC⟩ := hilbertH_weakL1
  set C' : ℝ := max C 0 with hC'_def
  have hC'0 : (0:ℝ) ≤ C' := le_max_right _ _
  have hp0 : (0:ℝ) < p := by linarith
  have hp1' : (0:ℝ) < p - 1 := by linarith
  have hp2' : (0:ℝ) < 2 - p := by linarith
  set A : ℝ := (p * (2 * C' / (p-1) + 4 / (2-p))) ^ (1/p) with hA_def
  have hAnn : (0:ℝ) ≤ A := Real.rpow_nonneg (by positivity) _
  refine ⟨A, ?_⟩
  intro ω hω2 hωp
  set ω1 : ℝ → ℂ → ℂ := fun lam x => {x : ℂ | lam < ‖ω x‖}.indicator ω x with hω1_def
  set ω2 : ℝ → ℂ → ℂ := fun lam x => {x : ℂ | ‖ω x‖ ≤ lam}.indicator ω x with hω2_def
  have hωaem : AEMeasurable (fun x => ‖ω x‖) volume := hω2.aestronglyMeasurable.aemeasurable.norm
  have hsplit : ∀ lam x, ω x = ω1 lam x + ω2 lam x := by
    intro lam x
    simp only [hω1_def, hω2_def]
    by_cases hx : lam < ‖ω x‖
    · have hxm : x ∈ {x : ℂ | lam < ‖ω x‖} := hx
      have hxm' : x ∉ {x : ℂ | ‖ω x‖ ≤ lam} := by simpa using hx
      rw [Set.indicator_of_mem hxm, Set.indicator_of_notMem hxm']; ring
    · have hxm : x ∉ {x : ℂ | lam < ‖ω x‖} := hx
      have hxm' : x ∈ {x : ℂ | ‖ω x‖ ≤ lam} := by simpa using hx
      rw [Set.indicator_of_notMem hxm, Set.indicator_of_mem hxm']; ring
  have hω1_le : ∀ lam x, ‖ω1 lam x‖ ≤ ‖ω x‖ := by
    intro lam x
    simp only [hω1_def]
    by_cases hx : lam < ‖ω x‖
    · have hxm : x ∈ {x : ℂ | lam < ‖ω x‖} := hx
      rw [Set.indicator_of_mem hxm]
    · have hxm : x ∉ {x : ℂ | lam < ‖ω x‖} := hx
      rw [Set.indicator_of_notMem hxm]; simp
  have hω2_le : ∀ lam x, ‖ω2 lam x‖ ≤ ‖ω x‖ := by
    intro lam x
    simp only [hω2_def]
    by_cases hx : ‖ω x‖ ≤ lam
    · have hxm : x ∈ {x : ℂ | ‖ω x‖ ≤ lam} := hx
      rw [Set.indicator_of_mem hxm]
    · have hxm : x ∉ {x : ℂ | ‖ω x‖ ≤ lam} := hx
      rw [Set.indicator_of_notMem hxm]; simp
  have hω1_meas : ∀ lam, AEStronglyMeasurable (ω1 lam) volume := fun lam =>
    hω2.aestronglyMeasurable.indicator₀ (nullMeasurableSet_lt aemeasurable_const hωaem)
  have hω2_meas : ∀ lam, AEStronglyMeasurable (ω2 lam) volume := fun lam =>
    hω2.aestronglyMeasurable.indicator₀ (nullMeasurableSet_le hωaem aemeasurable_const)
  have hω1_memLp2 : ∀ lam, MemLp (ω1 lam) 2 volume := fun lam =>
    hω2.norm.mono' (hω1_meas lam) (Eventually.of_forall (hω1_le lam))
  have hω2_memLp2 : ∀ lam, MemLp (ω2 lam) 2 volume := fun lam =>
    hω2.norm.mono' (hω2_meas lam) (Eventually.of_forall (hω2_le lam))
  have hω2_bound : ∀ lam x, ‖ω2 lam x‖ ≤ max lam 0 := by
    intro lam x
    simp only [hω2_def]
    by_cases hx : ‖ω x‖ ≤ lam
    · have hxm : x ∈ {x : ℂ | ‖ω x‖ ≤ lam} := hx
      rw [Set.indicator_of_mem hxm]; exact hx.trans (le_max_left _ _)
    · have hxm : x ∉ {x : ℂ | ‖ω x‖ ≤ lam} := hx
      rw [Set.indicator_of_notMem hxm]; simp
  have hω1_int : ∀ lam, 0 < lam → Integrable (ω1 lam) volume := by
    intro lam hlam
    have hbound : ∀ x, ‖ω1 lam x‖ ≤ ‖ω x‖ ^ 2 / lam := by
      intro x
      simp only [hω1_def]
      by_cases hx : lam < ‖ω x‖
      · have hxm : x ∈ {x : ℂ | lam < ‖ω x‖} := hx
        rw [Set.indicator_of_mem hxm]
        rw [le_div_iff₀ hlam]
        calc ‖ω x‖ * lam ≤ ‖ω x‖ * ‖ω x‖ := by
              apply mul_le_mul_of_nonneg_left hx.le (norm_nonneg _)
          _ = ‖ω x‖ ^ 2 := by ring
      · have hxm : x ∉ {x : ℂ | lam < ‖ω x‖} := hx
        rw [Set.indicator_of_notMem hxm, norm_zero]; positivity
    have h2 : Integrable (fun x => ‖ω x‖ ^ 2 / lam) volume := by
      have := (hω2.integrable_norm_rpow (two_ne_zero) (by norm_num))
      simpa [div_eq_mul_inv] using this.mul_const (lam⁻¹)
    exact h2.mono' (hω1_meas lam) (Eventually.of_forall hbound)
  have hHadd : ∀ lam, hilbertH ω =ᵐ[volume] hilbertH (ω1 lam) + hilbertH (ω2 lam) := by
    intro lam
    have heq : ω = ω1 lam + ω2 lam := funext (hsplit lam)
    calc hilbertH ω = hilbertH (ω1 lam + ω2 lam) := by rw [heq]
      _ =ᵐ[volume] hilbertH (ω1 lam) + hilbertH (ω2 lam) :=
          hilbertH_add_ae (hω1_memLp2 lam) (hω2_memLp2 lam)
  have htail_meas_le : ∀ lam, 0 < lam →
      volume {x : ℂ | lam < ‖hilbertH ω x‖} ≤
        volume {x : ℂ | lam / 2 < ‖hilbertH (ω1 lam) x‖} +
          volume {x : ℂ | lam / 2 < ‖hilbertH (ω2 lam) x‖} := by
    intro lam hlam
    set A : Set ℂ := {x : ℂ | lam / 2 < ‖hilbertH (ω1 lam) x‖} with hA_def
    set B : Set ℂ := {x : ℂ | lam / 2 < ‖hilbertH (ω2 lam) x‖} with hB_def
    set S : Set ℂ := {x : ℂ | lam < ‖hilbertH ω x‖} with hS_def
    have hbad_null : volume {x : ℂ | hilbertH ω x ≠
        hilbertH (ω1 lam) x + hilbertH (ω2 lam) x} = 0 := by
      have h := hHadd lam
      rw [Filter.EventuallyEq, ae_iff] at h
      simpa using h
    have hsubset : S \ (A ∪ B) ⊆
        {x : ℂ | hilbertH ω x ≠ hilbertH (ω1 lam) x + hilbertH (ω2 lam) x} := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      simp only [hS_def, Set.mem_setOf_eq] at hx1
      simp only [hA_def, hB_def, Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hx2
      intro heq
      have hle : ‖hilbertH ω x‖ ≤ lam := by
        rw [heq]
        calc ‖hilbertH (ω1 lam) x + hilbertH (ω2 lam) x‖ ≤
            ‖hilbertH (ω1 lam) x‖ + ‖hilbertH (ω2 lam) x‖ := norm_add_le _ _
          _ ≤ lam / 2 + lam / 2 := add_le_add hx2.1 hx2.2
          _ = lam := add_halves lam
      linarith
    have hdiff_null : volume (S \ (A ∪ B)) = 0 := measure_mono_null hsubset hbad_null
    calc volume S
        = volume ((S ∩ (A ∪ B)) ∪ (S \ (A ∪ B))) := by rw [Set.inter_union_diff]
      _ ≤ volume (S ∩ (A ∪ B)) + volume (S \ (A ∪ B)) := measure_union_le _ _
      _ = volume (S ∩ (A ∪ B)) := by rw [hdiff_null, add_zero]
      _ ≤ volume (A ∪ B) := measure_mono Set.inter_subset_right
      _ ≤ volume A + volume B := measure_union_le _ _
  have hofReal_half : ∀ lam : ℝ, ENNReal.ofReal (lam / 2) = ENNReal.ofReal lam / 2 := by
    intro lam
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
    norm_num
  have htail1 : ∀ lam, 0 < lam → volume {x : ℂ | lam / 2 < ‖hilbertH (ω1 lam) x‖} ≤
      ENNReal.ofReal (2 * C') * (∫⁻ x, ‖ω1 lam x‖ₑ) / ENNReal.ofReal lam := by
    intro lam hlam
    have h := hC (ω1 lam) (hω1_int lam hlam) (hω1_memLp2 lam) (lam / 2) (by positivity)
    have heq : ENNReal.ofReal C * (∫⁻ x, ‖ω1 lam x‖ₑ) / ENNReal.ofReal (lam / 2) =
        ENNReal.ofReal (2 * C) * (∫⁻ x, ‖ω1 lam x‖ₑ) / ENNReal.ofReal lam := by
      rw [hofReal_half]
      rw [div_eq_mul_inv (ENNReal.ofReal C * _), div_eq_mul_inv (ENNReal.ofReal lam) 2,
        div_eq_mul_inv (ENNReal.ofReal (2 * C) * _),
        ENNReal.mul_inv (Or.inr (by norm_num)) (Or.inr (by norm_num)), inv_inv,
        ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      rw [show (ENNReal.ofReal (2:ℝ)) = 2 from by norm_num]
      ring
    rw [heq] at h
    refine h.trans ?_
    exact ENNReal.div_le_div
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal (by nlinarith [le_max_left C 0])) _) le_rfl
  have htail2 : ∀ lam, 0 < lam → volume {x : ℂ | lam / 2 < ‖hilbertH (ω2 lam) x‖} ≤
      ENNReal.ofReal 4 * (∫⁻ x, ‖ω2 lam x‖ₑ ^ (2:ℝ)) / (ENNReal.ofReal lam) ^ (2:ℝ) := by
    intro lam hlam
    have hiso := hilbertH_memLp_two (hω2_memLp2 lam)
    have hcheb := mul_meas_ge_le_pow_eLpNorm' (μ := volume) (p := (2:ℝ≥0∞)) (by norm_num)
      (by norm_num) (f := hilbertH (ω2 lam)) (ENNReal.ofReal (lam / 2))
    rw [show ((2:ℝ≥0∞).toReal) = (2:ℝ) from by norm_num] at hcheb
    rw [hiso.2] at hcheb
    have hlint : (eLpNorm (ω2 lam) 2 volume) ^ (2:ℝ) = ∫⁻ x, ‖ω2 lam x‖ₑ ^ (2:ℝ) := by
      have := enn_pow_eLpNorm_eq_lintegral (μ := volume) (p := (2:ℝ)) (by norm_num) (ω2 lam)
        (hω2_memLp2 lam).aestronglyMeasurable
      rwa [show ENNReal.ofReal (2:ℝ) = 2 from by norm_num] at this
    rw [hlint] at hcheb
    have hsubset : {x : ℂ | lam / 2 < ‖hilbertH (ω2 lam) x‖} ⊆
        {x : ℂ | ENNReal.ofReal (lam / 2) ≤ ‖hilbertH (ω2 lam) x‖ₑ} := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hx.le
    have hfin : (ENNReal.ofReal (lam / 2)) ^ (2:ℝ) *
        volume {x : ℂ | lam / 2 < ‖hilbertH (ω2 lam) x‖} ≤ ∫⁻ x, ‖ω2 lam x‖ₑ ^ (2:ℝ) :=
      (mul_le_mul_right (measure_mono hsubset) _).trans hcheb
    have hne0 : (ENNReal.ofReal (lam / 2)) ^ (2:ℝ) ≠ 0 := by positivity
    have hnetop : (ENNReal.ofReal (lam / 2)) ^ (2:ℝ) ≠ ⊤ := by finiteness
    have hfin' : volume {x : ℂ | lam / 2 < ‖hilbertH (ω2 lam) x‖} ≤
        (∫⁻ x, ‖ω2 lam x‖ₑ ^ (2:ℝ)) / (ENNReal.ofReal (lam / 2)) ^ (2:ℝ) :=
      (ENNReal.le_div_iff_mul_le (Or.inl hne0) (Or.inl hnetop)).mpr
        (by rw [mul_comm]; exact hfin)
    refine hfin'.trans (le_of_eq ?_)
    rw [hofReal_half, ENNReal.div_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
    rw [show ((2:ℝ≥0∞)) ^ (2:ℝ) = 4 from by rw [ENNReal.rpow_two]; norm_num]
    rw [div_eq_mul_inv (∫⁻ x, ‖ω2 lam x‖ₑ ^ (2:ℝ)),
      div_eq_mul_inv ((ENNReal.ofReal lam) ^ (2:ℝ)) (4:ℝ≥0∞),
      div_eq_mul_inv (ENNReal.ofReal 4 * ∫⁻ x, ‖ω2 lam x‖ₑ ^ (2:ℝ)),
      ENNReal.mul_inv (Or.inr (by norm_num)) (Or.inr (by norm_num)), inv_inv,
      show (ENNReal.ofReal (4:ℝ)) = 4 from by norm_num]
    ring
  have htail : ∀ lam, 0 < lam → volume {x : ℂ | lam < ‖hilbertH ω x‖} ≤
      ENNReal.ofReal (2 * C') * (∫⁻ x, ‖ω1 lam x‖ₑ) / ENNReal.ofReal lam +
        ENNReal.ofReal 4 * (∫⁻ x, ‖ω2 lam x‖ₑ ^ (2:ℝ)) / (ENNReal.ofReal lam) ^ (2:ℝ) :=
    fun lam hlam => (htail_meas_le lam hlam).trans (add_le_add (htail1 lam hlam) (htail2 lam hlam))
  have hHmeas : AEStronglyMeasurable (hilbertH ω) volume :=
    (hilbertH_memLp_two hω2).1.aestronglyMeasurable
  have hg_cont : Continuous (fun s : ℝ => p * s ^ (p - 1)) :=
    continuous_const.mul (Real.continuous_rpow_const (by linarith))
  have hinner : ∀ a : ℝ, 0 ≤ a → ∫ s in (0:ℝ)..a, p * s ^ (p - 1) = a ^ p := by
    intro a ha
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith : (-1:ℝ) < p - 1))]
    rw [Real.zero_rpow (by linarith : p - 1 + 1 ≠ 0)]
    rw [show p - 1 + 1 = p by ring]
    field_simp
    ring
  have hlayercake : ∫⁻ x, ‖hilbertH ω x‖ₑ ^ p ∂volume =
      ∫⁻ t in Ioi (0:ℝ), volume {x : ℂ | t < ‖hilbertH ω x‖} * ENNReal.ofReal (p * t ^ (p - 1)) := by
    have hkey := lintegral_comp_eq_lintegral_meas_lt_mul volume
      (Filter.Eventually.of_forall (fun x => norm_nonneg (hilbertH ω x)))
      hHmeas.aemeasurable.norm
      (fun t _ => hg_cont.intervalIntegrable 0 t)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => by
        have : (0:ℝ) < t := ht
        positivity))
    rw [← hkey]
    apply lintegral_congr
    intro x
    rw [hinner ‖hilbertH ω x‖ (norm_nonneg _), ← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
  set K : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (p * t ^ (p - 1)) with hK_def
  have hstepA : ∫⁻ t in Ioi (0:ℝ), volume {x : ℂ | t < ‖hilbertH ω x‖} * K t ≤
      ∫⁻ t in Ioi (0:ℝ),
        (ENNReal.ofReal (2 * C') * (∫⁻ x, ‖ω1 t x‖ₑ) / ENNReal.ofReal t
          + ENNReal.ofReal 4 * (∫⁻ x, ‖ω2 t x‖ₑ ^ (2:ℝ)) / (ENNReal.ofReal t) ^ (2:ℝ)) * K t := by
    apply lintegral_mono_ae
    exact (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => by
      have ht' : (0:ℝ) < t := ht
      exact mul_le_mul_left (htail t ht') _)
  have hT1eq : ∀ t : ℝ, 0 < t →
      (ENNReal.ofReal (2 * C') * (∫⁻ x, ‖ω1 t x‖ₑ) / ENNReal.ofReal t) * K t =
        ENNReal.ofReal (2 * C') * ∫⁻ x, ‖ω1 t x‖ₑ * ENNReal.ofReal (p * t ^ (p - 2)) := by
    intro t ht
    have hK_eq : K t / ENNReal.ofReal t = ENNReal.ofReal (p * t ^ (p - 2)) := by
      simp only [hK_def]
      rw [← ENNReal.ofReal_div_of_pos ht]
      congr 1
      rw [mul_div_assoc]
      have hrs := Real.rpow_sub ht (p - 1) 1
      rw [Real.rpow_one] at hrs
      rw [← hrs]
      congr 2
      ring
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, ← hK_eq]
    simp only [div_eq_mul_inv]
    ring
  have hT2eq : ∀ t : ℝ, 0 < t →
      (ENNReal.ofReal 4 * (∫⁻ x, ‖ω2 t x‖ₑ ^ (2:ℝ)) / (ENNReal.ofReal t) ^ (2:ℝ)) * K t =
        ENNReal.ofReal 4 * ∫⁻ x, ‖ω2 t x‖ₑ ^ (2:ℝ) * ENNReal.ofReal (p * t ^ (p - 3)) := by
    intro t ht
    have hK_eq2 : K t / (ENNReal.ofReal t) ^ (2:ℝ) = ENNReal.ofReal (p * t ^ (p - 3)) := by
      simp only [hK_def]
      rw [ENNReal.ofReal_rpow_of_nonneg ht.le (by norm_num : (0:ℝ) ≤ 2),
        ← ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ) < t ^ (2:ℝ))]
      congr 1
      rw [mul_div_assoc]
      have hrs := Real.rpow_sub ht (p - 1) 2
      rw [← hrs]
      congr 2
      ring
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, ← hK_eq2]
    simp only [div_eq_mul_inv]
    ring
  have hstepB : ∫⁻ t in Ioi (0:ℝ),
        (ENNReal.ofReal (2 * C') * (∫⁻ x, ‖ω1 t x‖ₑ) / ENNReal.ofReal t
          + ENNReal.ofReal 4 * (∫⁻ x, ‖ω2 t x‖ₑ ^ (2:ℝ)) / (ENNReal.ofReal t) ^ (2:ℝ)) * K t =
      ∫⁻ t in Ioi (0:ℝ),
        (ENNReal.ofReal (2 * C') * ∫⁻ x, ‖ω1 t x‖ₑ * ENNReal.ofReal (p * t ^ (p - 2))) +
          (ENNReal.ofReal 4 * ∫⁻ x, ‖ω2 t x‖ₑ ^ (2:ℝ) * ENNReal.ofReal (p * t ^ (p - 3))) := by
    apply lintegral_congr_ae
    exact (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => by
      have ht' : (0:ℝ) < t := ht
      simp only
      rw [add_mul, hT1eq t ht', hT2eq t ht'])
  -- joint measurability, needed to split the outer integral and to swap each term via Tonelli
  have hω1_ind : ∀ (t : ℝ) (x : ℂ), ‖ω1 t x‖ₑ = (Iio ‖ω x‖).indicator (fun _ => ‖ω x‖ₑ) t := by
    intro t x
    simp only [hω1_def]
    by_cases hx : t < ‖ω x‖
    · have hxm : x ∈ {x : ℂ | t < ‖ω x‖} := hx
      have hxm' : t ∈ Iio ‖ω x‖ := hx
      rw [Set.indicator_of_mem hxm, Set.indicator_of_mem hxm']
    · have hxm : x ∉ {x : ℂ | t < ‖ω x‖} := hx
      have hxm' : t ∉ Iio ‖ω x‖ := hx
      rw [Set.indicator_of_notMem hxm, Set.indicator_of_notMem hxm', enorm_zero]
  have hω2_ind : ∀ (t : ℝ) (x : ℂ),
      ‖ω2 t x‖ₑ ^ (2:ℝ) = (Ici ‖ω x‖).indicator (fun _ => ‖ω x‖ₑ ^ (2:ℝ)) t := by
    intro t x
    simp only [hω2_def]
    by_cases hx : ‖ω x‖ ≤ t
    · have hxm : x ∈ {x : ℂ | ‖ω x‖ ≤ t} := hx
      have hxm' : t ∈ Ici ‖ω x‖ := hx
      rw [Set.indicator_of_mem hxm, Set.indicator_of_mem hxm']
    · have hxm : x ∉ {x : ℂ | ‖ω x‖ ≤ t} := hx
      have hxm' : t ∉ Ici ‖ω x‖ := hx
      rw [Set.indicator_of_notMem hxm, Set.indicator_of_notMem hxm', enorm_zero,
        ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]
  have hω1_joint : AEMeasurable (fun z : ℝ × ℂ => ‖ω1 z.1 z.2‖ₑ)
      ((volume.restrict (Ioi (0:ℝ))).prod volume) := by
    have hset : NullMeasurableSet {z : ℝ × ℂ | z.1 < ‖ω z.2‖}
        ((volume.restrict (Ioi (0:ℝ))).prod volume) :=
      nullMeasurableSet_lt measurable_fst.aemeasurable hωaem.comp_snd
    have heq : (fun z : ℝ × ℂ => ‖ω1 z.1 z.2‖ₑ) =
        Set.indicator {z : ℝ × ℂ | z.1 < ‖ω z.2‖} (fun z => ‖ω z.2‖ₑ) := by
      funext z
      by_cases hz : z.1 < ‖ω z.2‖
      · have hz' : z ∈ {z : ℝ × ℂ | z.1 < ‖ω z.2‖} := hz
        have hz'' : z.1 ∈ Iio ‖ω z.2‖ := hz
        rw [Set.indicator_of_mem hz', hω1_ind, Set.indicator_of_mem hz'']
      · have hz' : z ∉ {z : ℝ × ℂ | z.1 < ‖ω z.2‖} := hz
        have hz'' : z.1 ∉ Iio ‖ω z.2‖ := hz
        rw [Set.indicator_of_notMem hz', hω1_ind, Set.indicator_of_notMem hz'']
    rw [heq]
    exact (hω2.aestronglyMeasurable.aemeasurable.comp_snd.enorm).indicator₀ hset
  have hω2_joint : AEMeasurable (fun z : ℝ × ℂ => ‖ω2 z.1 z.2‖ₑ ^ (2:ℝ))
      ((volume.restrict (Ioi (0:ℝ))).prod volume) := by
    have hset : NullMeasurableSet {z : ℝ × ℂ | ‖ω z.2‖ ≤ z.1}
        ((volume.restrict (Ioi (0:ℝ))).prod volume) :=
      nullMeasurableSet_le hωaem.comp_snd measurable_fst.aemeasurable
    have heq : (fun z : ℝ × ℂ => ‖ω2 z.1 z.2‖ₑ ^ (2:ℝ)) =
        Set.indicator {z : ℝ × ℂ | ‖ω z.2‖ ≤ z.1} (fun z => ‖ω z.2‖ₑ ^ (2:ℝ)) := by
      funext z
      by_cases hz : ‖ω z.2‖ ≤ z.1
      · have hz' : z ∈ {z : ℝ × ℂ | ‖ω z.2‖ ≤ z.1} := hz
        have hz'' : z.1 ∈ Ici ‖ω z.2‖ := hz
        rw [Set.indicator_of_mem hz', hω2_ind, Set.indicator_of_mem hz'']
      · have hz' : z ∉ {z : ℝ × ℂ | ‖ω z.2‖ ≤ z.1} := hz
        have hz'' : z.1 ∉ Ici ‖ω z.2‖ := hz
        rw [Set.indicator_of_notMem hz', hω2_ind, Set.indicator_of_notMem hz'']
    rw [heq]
    exact (hω2.aestronglyMeasurable.aemeasurable.comp_snd.enorm.pow_const (2:ℝ)).indicator₀ hset
  have hcont_pm2 : ContinuousOn (fun t : ℝ => t ^ (p - 2)) (Ioi (0:ℝ)) :=
    fun t ht => (Real.continuousAt_rpow_const t (p - 2) (Or.inl ht.ne')).continuousWithinAt
  have hcont_pm3 : ContinuousOn (fun t : ℝ => t ^ (p - 3)) (Ioi (0:ℝ)) :=
    fun t ht => (Real.continuousAt_rpow_const t (p - 3) (Or.inl ht.ne')).continuousWithinAt
  have hrpow2_aem : AEMeasurable (fun t : ℝ => ENNReal.ofReal (p * t ^ (p - 2)))
      (volume.restrict (Ioi (0:ℝ))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (aemeasurable_const.mul (hcont_pm2.aemeasurable measurableSet_Ioi))
  have hrpow3_aem : AEMeasurable (fun t : ℝ => ENNReal.ofReal (p * t ^ (p - 3)))
      (volume.restrict (Ioi (0:ℝ))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (aemeasurable_const.mul (hcont_pm3.aemeasurable measurableSet_Ioi))
  have hrpow2_joint : AEMeasurable (fun z : ℝ × ℂ => ENNReal.ofReal (p * z.1 ^ (p - 2)))
      ((volume.restrict (Ioi (0:ℝ))).prod volume) := hrpow2_aem.comp_fst
  have hrpow3_joint : AEMeasurable (fun z : ℝ × ℂ => ENNReal.ofReal (p * z.1 ^ (p - 3)))
      ((volume.restrict (Ioi (0:ℝ))).prod volume) := hrpow3_aem.comp_fst
  have hjoint1 : AEMeasurable (fun z : ℝ × ℂ => ‖ω1 z.1 z.2‖ₑ * ENNReal.ofReal (p * z.1 ^ (p - 2)))
      ((volume.restrict (Ioi (0:ℝ))).prod volume) := hω1_joint.mul hrpow2_joint
  have hjoint2 : AEMeasurable
      (fun z : ℝ × ℂ => ‖ω2 z.1 z.2‖ₑ ^ (2:ℝ) * ENNReal.ofReal (p * z.1 ^ (p - 3)))
      ((volume.restrict (Ioi (0:ℝ))).prod volume) := hω2_joint.mul hrpow3_joint
  have hmarg1_aem : AEMeasurable (fun t : ℝ => ∫⁻ x, ‖ω1 t x‖ₑ * ENNReal.ofReal (p * t ^ (p - 2)))
      (volume.restrict (Ioi (0:ℝ))) := hjoint1.lintegral_prod_right'
  have hstepC : ∫⁻ t in Ioi (0:ℝ),
        (ENNReal.ofReal (2 * C') * ∫⁻ x, ‖ω1 t x‖ₑ * ENNReal.ofReal (p * t ^ (p - 2))) +
          (ENNReal.ofReal 4 * ∫⁻ x, ‖ω2 t x‖ₑ ^ (2:ℝ) * ENNReal.ofReal (p * t ^ (p - 3))) =
      (∫⁻ t in Ioi (0:ℝ),
          ENNReal.ofReal (2 * C') * ∫⁻ x, ‖ω1 t x‖ₑ * ENNReal.ofReal (p * t ^ (p - 2))) +
        (∫⁻ t in Ioi (0:ℝ),
          ENNReal.ofReal 4 * ∫⁻ x, ‖ω2 t x‖ₑ ^ (2:ℝ) * ENNReal.ofReal (p * t ^ (p - 3))) :=
    lintegral_add_left' (hmarg1_aem.const_mul _) _
  have hpull1 :
      (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (2 * C') * ∫⁻ x, ‖ω1 t x‖ₑ * ENNReal.ofReal (p * t ^ (p - 2))) =
        ENNReal.ofReal (2 * C') * ∫⁻ t in Ioi (0:ℝ), ∫⁻ x, ‖ω1 t x‖ₑ * ENNReal.ofReal (p * t ^ (p - 2)) :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hpull2 :
      (∫⁻ t in Ioi (0:ℝ),
          ENNReal.ofReal 4 * ∫⁻ x, ‖ω2 t x‖ₑ ^ (2:ℝ) * ENNReal.ofReal (p * t ^ (p - 3))) =
        ENNReal.ofReal 4 *
          ∫⁻ t in Ioi (0:ℝ), ∫⁻ x, ‖ω2 t x‖ₑ ^ (2:ℝ) * ENNReal.ofReal (p * t ^ (p - 3)) :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hswap1 : ∫⁻ t in Ioi (0:ℝ), ∫⁻ x, ‖ω1 t x‖ₑ * ENNReal.ofReal (p * t ^ (p - 2)) =
      ∫⁻ x, ∫⁻ t in Ioi (0:ℝ), ‖ω1 t x‖ₑ * ENNReal.ofReal (p * t ^ (p - 2)) :=
    lintegral_lintegral_swap hjoint1
  have hswap2 : ∫⁻ t in Ioi (0:ℝ), ∫⁻ x, ‖ω2 t x‖ₑ ^ (2:ℝ) * ENNReal.ofReal (p * t ^ (p - 3)) =
      ∫⁻ x, ∫⁻ t in Ioi (0:ℝ), ‖ω2 t x‖ₑ ^ (2:ℝ) * ENNReal.ofReal (p * t ^ (p - 3)) :=
    lintegral_lintegral_swap hjoint2
  -- closed forms of the inner (t-marginal) integrals, for fixed x
  have hclosed1 : ∀ x : ℂ, ∫⁻ t in Ioi (0:ℝ), ‖ω1 t x‖ₑ * ENNReal.ofReal (p * t ^ (p - 2)) =
      ‖ω x‖ₑ * ENNReal.ofReal (p * ‖ω x‖ ^ (p - 1) / (p - 1)) := by
    intro x
    have hAnn : (0:ℝ) ≤ ‖ω x‖ := norm_nonneg _
    have hrw : ∫⁻ t in Ioi (0:ℝ), ‖ω1 t x‖ₑ * ENNReal.ofReal (p * t ^ (p - 2)) =
        ∫⁻ t in Ioo (0:ℝ) ‖ω x‖, ‖ω x‖ₑ * ENNReal.ofReal (p * t ^ (p - 2)) := by
      rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro t
      by_cases htA : t ∈ Ioo (0:ℝ) ‖ω x‖
      · have ht0 : t ∈ Ioi (0:ℝ) := htA.1
        have htI : t ∈ Iio ‖ω x‖ := htA.2
        rw [Set.indicator_of_mem ht0, Set.indicator_of_mem htA, hω1_ind, Set.indicator_of_mem htI]
      · by_cases ht0 : t ∈ Ioi (0:ℝ)
        · have htI : t ∉ Iio ‖ω x‖ := fun h => htA ⟨ht0, h⟩
          rw [Set.indicator_of_mem ht0, Set.indicator_of_notMem htA, hω1_ind,
            Set.indicator_of_notMem htI]
          ring
        · rw [Set.indicator_of_notMem ht0, Set.indicator_of_notMem htA]
    have hxfin : ‖ω x‖ₑ ≠ ⊤ := by rw [← ofReal_norm]; exact ENNReal.ofReal_ne_top
    rw [hrw, lintegral_const_mul' _ _ hxfin]
    congr 1
    have hIntOn : IntegrableOn (fun t => p * t ^ (p - 2)) (Ioo (0:ℝ) ‖ω x‖) volume :=
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le hAnn
          (ha := by rw [← ofReal_norm]; exact ENNReal.ofReal_ne_top)
          (hb := by rw [← ofReal_norm]; exact ENNReal.ofReal_ne_top)).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1:ℝ) < p - 2))).const_mul p
    have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0:ℝ) ‖ω x‖)] (fun t => p * t ^ (p - 2)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have : (0:ℝ) < t := ht.1
      positivity
    rw [← ofReal_integral_eq_lintegral_ofReal hIntOn hnn]
    congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hAnn,
      intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : (-1:ℝ) < p - 2))]
    rw [Real.zero_rpow (by linarith : p - 2 + 1 ≠ 0), show p - 2 + 1 = p - 1 by ring, sub_zero]
    ring
  have hclosed2 : ∀ x : ℂ, ∫⁻ t in Ioi (0:ℝ), ‖ω2 t x‖ₑ ^ (2:ℝ) * ENNReal.ofReal (p * t ^ (p - 3)) =
      ‖ω x‖ₑ ^ (2:ℝ) * ENNReal.ofReal (p * ‖ω x‖ ^ (p - 2) / (2 - p)) := by
    intro x
    have hAnn : (0:ℝ) ≤ ‖ω x‖ := norm_nonneg _
    rcases hAnn.eq_or_lt with hA0 | hApos
    · have hxnorm : ‖ω x‖ = 0 := hA0.symm
      have hxzero : ω x = 0 := norm_eq_zero.mp hxnorm
      have hze : ‖ω x‖ₑ = 0 := by rw [hxzero]; simp
      have hpt : ∀ t ∈ Ioi (0:ℝ), ‖ω2 t x‖ₑ ^ (2:ℝ) * ENNReal.ofReal (p * t ^ (p - 3)) = 0 := by
        intro t ht
        have ht' : (0:ℝ) < t := ht
        have htA : t ∈ Ici ‖ω x‖ := by rw [hxnorm]; exact ht'.le
        rw [hω2_ind, Set.indicator_of_mem htA, hze,
          ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2), zero_mul]
      have hLHS0 : ∫⁻ t in Ioi (0:ℝ), ‖ω2 t x‖ₑ ^ (2:ℝ) * ENNReal.ofReal (p * t ^ (p - 3)) = 0 := by
        rw [lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioi).mpr
          (Filter.Eventually.of_forall hpt))]
        exact lintegral_zero
      rw [hLHS0, hze, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2), zero_mul]
    · have hrw : ∫⁻ t in Ioi (0:ℝ), ‖ω2 t x‖ₑ ^ (2:ℝ) * ENNReal.ofReal (p * t ^ (p - 3)) =
          ∫⁻ t in Ici ‖ω x‖, ‖ω x‖ₑ ^ (2:ℝ) * ENNReal.ofReal (p * t ^ (p - 3)) := by
        rw [← lintegral_indicator measurableSet_Ici, ← lintegral_indicator measurableSet_Ioi]
        apply lintegral_congr
        intro t
        by_cases ht0 : t ∈ Ioi (0:ℝ)
        · by_cases htA : t ∈ Ici ‖ω x‖
          · rw [Set.indicator_of_mem ht0, Set.indicator_of_mem htA, hω2_ind,
              Set.indicator_of_mem htA]
          · rw [Set.indicator_of_mem ht0, Set.indicator_of_notMem htA, hω2_ind,
              Set.indicator_of_notMem htA]
            ring
        · have htA : t ∉ Ici ‖ω x‖ := fun h => ht0 (hApos.trans_le h)
          rw [Set.indicator_of_notMem ht0, Set.indicator_of_notMem htA]
      have hxfin2 : ‖ω x‖ₑ ^ (2:ℝ) ≠ ⊤ := by
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)]
        exact ENNReal.ofReal_ne_top
      rw [hrw, ← restrict_Ioi_eq_restrict_Ici, lintegral_const_mul' _ _ hxfin2]
      congr 1
      have hIntOn : IntegrableOn (fun t => p * t ^ (p - 3)) (Ioi ‖ω x‖) volume :=
        (integrableOn_Ioi_rpow_of_lt (by linarith : p - 3 < -1) hApos).const_mul p
      have hnn : 0 ≤ᵐ[volume.restrict (Ioi ‖ω x‖)] (fun t => p * t ^ (p - 3)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have : (0:ℝ) < t := hApos.trans ht
        positivity
      rw [← ofReal_integral_eq_lintegral_ofReal hIntOn hnn]
      congr 1
      rw [MeasureTheory.integral_const_mul,
        integral_Ioi_rpow_of_lt (by linarith : p - 3 < -1) hApos,
        show p - 3 + 1 = p - 2 by ring]
      have hp2ne : p - 2 ≠ 0 := by intro h; linarith
      field_simp
      ring
  -- merge each closed form into a multiple of ‖ω x‖ₑ ^ p
  have hmerge1 : ∀ x : ℂ, ‖ω x‖ₑ * ENNReal.ofReal (p * ‖ω x‖ ^ (p - 1) / (p - 1)) =
      ENNReal.ofReal (p / (p - 1)) * ‖ω x‖ₑ ^ p := by
    intro x
    rcases (norm_nonneg (ω x)).eq_or_lt with h0 | hpos
    · have hxzero : ω x = 0 := norm_eq_zero.mp h0.symm
      simp [hxzero, ENNReal.zero_rpow_of_pos hp0]
    · have hcomb : ‖ω x‖ * ‖ω x‖ ^ (p - 1) = ‖ω x‖ ^ p := by
        nth_rewrite 1 [← Real.rpow_one ‖ω x‖]
        rw [← Real.rpow_add hpos]
        congr 1
        ring
      rw [← ofReal_norm (ω x), ← ENNReal.ofReal_mul (norm_nonneg (ω x)),
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (ω x)) hp0.le,
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ p / (p - 1))]
      congr 1
      rw [show ‖ω x‖ * (p * ‖ω x‖ ^ (p - 1) / (p - 1)) =
          p / (p - 1) * (‖ω x‖ * ‖ω x‖ ^ (p - 1)) by ring, hcomb]
  have hmerge2 : ∀ x : ℂ, ‖ω x‖ₑ ^ (2:ℝ) * ENNReal.ofReal (p * ‖ω x‖ ^ (p - 2) / (2 - p)) =
      ENNReal.ofReal (p / (2 - p)) * ‖ω x‖ₑ ^ p := by
    intro x
    rcases (norm_nonneg (ω x)).eq_or_lt with h0 | hpos
    · have hxzero : ω x = 0 := norm_eq_zero.mp h0.symm
      simp [hxzero, ENNReal.zero_rpow_of_pos hp0, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]
    · have hcomb : ‖ω x‖ ^ (2:ℝ) * ‖ω x‖ ^ (p - 2) = ‖ω x‖ ^ p := by
        rw [← Real.rpow_add hpos]
        congr 1
        ring
      rw [← ofReal_norm (ω x),
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (ω x)) (by norm_num : (0:ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ‖ω x‖ ^ (2:ℝ)),
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (ω x)) hp0.le,
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ p / (2 - p))]
      congr 1
      rw [show ‖ω x‖ ^ (2:ℝ) * (p * ‖ω x‖ ^ (p - 2) / (2 - p)) =
          p / (2 - p) * (‖ω x‖ ^ (2:ℝ) * ‖ω x‖ ^ (p - 2)) by ring, hcomb]
  have hfinal_bound : ∫⁻ x, ‖hilbertH ω x‖ₑ ^ p ∂volume ≤
      ENNReal.ofReal (A ^ p) * ∫⁻ x, ‖ω x‖ₑ ^ p ∂volume := by
    have hXnn : (0:ℝ) ≤ p * (2 * C' / (p - 1) + 4 / (2 - p)) := by positivity
    have hAp : A ^ p = p * (2 * C' / (p - 1) + 4 / (2 - p)) := by
      rw [hA_def, ← Real.rpow_mul hXnn, one_div_mul_cancel hp0.ne', Real.rpow_one]
    have hAp_eq : 2 * C' * p / (p - 1) + 4 * p / (2 - p) = A ^ p := by rw [hAp]; ring
    rw [← hAp_eq]
    calc ∫⁻ x, ‖hilbertH ω x‖ₑ ^ p ∂volume
        = ∫⁻ t in Ioi (0:ℝ), volume {x : ℂ | t < ‖hilbertH ω x‖} * K t := hlayercake
      _ ≤ ∫⁻ t in Ioi (0:ℝ),
            (ENNReal.ofReal (2 * C') * (∫⁻ x, ‖ω1 t x‖ₑ) / ENNReal.ofReal t
              + ENNReal.ofReal 4 * (∫⁻ x, ‖ω2 t x‖ₑ ^ (2:ℝ)) / (ENNReal.ofReal t) ^ (2:ℝ)) * K t :=
          hstepA
      _ = _ := hstepB
      _ = _ := hstepC
      _ = ENNReal.ofReal (2 * C') *
            (∫⁻ t in Ioi (0:ℝ), ∫⁻ x, ‖ω1 t x‖ₑ * ENNReal.ofReal (p * t ^ (p - 2))) +
          ENNReal.ofReal 4 *
            (∫⁻ t in Ioi (0:ℝ), ∫⁻ x, ‖ω2 t x‖ₑ ^ (2:ℝ) * ENNReal.ofReal (p * t ^ (p - 3))) := by
          rw [hpull1, hpull2]
      _ = ENNReal.ofReal (2 * C') *
            (∫⁻ x, ∫⁻ t in Ioi (0:ℝ), ‖ω1 t x‖ₑ * ENNReal.ofReal (p * t ^ (p - 2))) +
          ENNReal.ofReal 4 *
            (∫⁻ x, ∫⁻ t in Ioi (0:ℝ), ‖ω2 t x‖ₑ ^ (2:ℝ) * ENNReal.ofReal (p * t ^ (p - 3))) := by
          rw [hswap1, hswap2]
      _ = ENNReal.ofReal (2 * C') *
            (∫⁻ x, ‖ω x‖ₑ * ENNReal.ofReal (p * ‖ω x‖ ^ (p - 1) / (p - 1))) +
          ENNReal.ofReal 4 *
            (∫⁻ x, ‖ω x‖ₑ ^ (2:ℝ) * ENNReal.ofReal (p * ‖ω x‖ ^ (p - 2) / (2 - p))) := by
          rw [lintegral_congr hclosed1, lintegral_congr hclosed2]
      _ = ENNReal.ofReal (2 * C') * (ENNReal.ofReal (p / (p - 1)) * ∫⁻ x, ‖ω x‖ₑ ^ p) +
          ENNReal.ofReal 4 * (ENNReal.ofReal (p / (2 - p)) * ∫⁻ x, ‖ω x‖ₑ ^ p) := by
          rw [lintegral_congr hmerge1, lintegral_congr hmerge2,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal (2 * C' * p / (p - 1) + 4 * p / (2 - p)) * ∫⁻ x, ‖ω x‖ₑ ^ p := by
          rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4), ← add_mul,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 2
          ring
  have heLp_lhs : eLpNorm (hilbertH ω) (ENNReal.ofReal p) volume =
      (∫⁻ x, ‖hilbertH ω x‖ₑ ^ p ∂volume) ^ (1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
      hHmeas, ENNReal.toReal_ofReal hp0.le]
  have heLp_rhs : eLpNorm ω (ENNReal.ofReal p) volume =
      (∫⁻ x, ‖ω x‖ₑ ^ p ∂volume) ^ (1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
      hωp.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
  rw [heLp_lhs, heLp_rhs]
  calc (∫⁻ x, ‖hilbertH ω x‖ₑ ^ p ∂volume) ^ (1/p)
      ≤ (ENNReal.ofReal (A ^ p) * ∫⁻ x, ‖ω x‖ₑ ^ p ∂volume) ^ (1/p) :=
        ENNReal.rpow_le_rpow hfinal_bound (by positivity)
    _ = (ENNReal.ofReal (A ^ p)) ^ (1/p) * (∫⁻ x, ‖ω x‖ₑ ^ p ∂volume) ^ (1/p) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = ENNReal.ofReal A * (∫⁻ x, ‖ω x‖ₑ ^ p ∂volume) ^ (1/p) := by
        congr 1
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : (0:ℝ) ≤ A ^ p)
          (by positivity : (0:ℝ) ≤ 1/p)]
        congr 1
        rw [← Real.rpow_mul hAnn, mul_one_div_cancel hp0.ne', Real.rpow_one]

/-! ## S5-b: the case `p > 2`, via L²-density extension of S5-a's pairing identity + duality on S4. -/

theorem hilbertH_sub_ae {u v : ℂ → ℂ} (hu : MemLp u 2) (hv : MemLp v 2) :
    hilbertH u - hilbertH v =ᵐ[volume] hilbertH (u - v) := by
  have h := hilbertH_add_ae hv (hu.sub hv)
  have heq : v + (u - v) = u := by funext z; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [heq] at h
  filter_upwards [h] with z hz
  simp only [Pi.sub_apply, Pi.add_apply] at hz ⊢
  linear_combination hz

theorem hilbertH_eLpNorm_sub_eq {u v : ℂ → ℂ} (hu : MemLp u 2) (hv : MemLp v 2) :
    eLpNorm (hilbertH u - hilbertH v) 2 volume = eLpNorm (u - v) 2 volume := by
  rw [eLpNorm_congr_ae (hilbertH_sub_ae hu hv), (hilbertH_memLp_two (hu.sub hv)).2]

theorem cauchy_schwarz_L2 {u v : ℂ → ℂ} (hu : MemLp u 2) (hv : MemLp v 2) :
    ‖∫ z, u z * v z‖ ≤ (eLpNorm u 2 volume).toReal * (eLpNorm v 2 volume).toReal := by
  have h2 : ENNReal.ofReal (2:ℝ) = (2:ℝ≥0∞) := by norm_num
  have hu' : MemLp u (ENNReal.ofReal 2) volume := h2 ▸ hu
  have hv' : MemLp v (ENNReal.ofReal 2) volume := h2 ▸ hv
  have hpq : (2:ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  have hpow : ∀ X : ℝ≥0∞, ((X ^ (2:ℝ)).toReal) ^ (1/(2:ℝ)) = X.toReal := fun X => by
    rw [← ENNReal.toReal_rpow, ← Real.rpow_mul ENNReal.toReal_nonneg, mul_one_div,
      div_self (two_ne_zero), Real.rpow_one]
  calc ‖∫ z, u z * v z‖ ≤ ∫ z, ‖u z * v z‖ := norm_integral_le_integral_norm _
    _ = ∫ z, ‖u z‖ * ‖v z‖ := by simp_rw [norm_mul]
    _ ≤ (∫ z, ‖u z‖ ^ (2:ℝ)) ^ (1/(2:ℝ)) * (∫ z, ‖v z‖ ^ (2:ℝ)) ^ (1/(2:ℝ)) :=
        integral_mul_norm_le_Lp_mul_Lq hpq hu' hv'
    _ = (eLpNorm u (ENNReal.ofReal 2) volume).toReal *
          (eLpNorm v (ENNReal.ofReal 2) volume).toReal := by
        rw [integral_norm_rpow_eq_toReal_pow (by norm_num) hu'.aestronglyMeasurable,
          integral_norm_rpow_eq_toReal_pow (by norm_num) hv'.aestronglyMeasurable, hpow, hpow]
    _ = (eLpNorm u 2 volume).toReal * (eLpNorm v 2 volume).toReal := by rw [h2]

theorem hilbertH_pairing_symm_smooth {f g : ℂ → ℂ}
    (hf1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hf2 : HasCompactSupport f)
    (hg1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hg2 : HasCompactSupport g) :
    ∫ z, hilbertH f z * g z = ∫ z, f z * hilbertH g z := by
  have hf' : hilbertH f =ᵐ[volume] hilbertHSmooth f := hilbertH_eq_ae_smooth hf1 hf2
  have hg' : hilbertH g =ᵐ[volume] hilbertHSmooth g := hilbertH_eq_ae_smooth hg1 hg2
  have hf'' : (fun z => hilbertH f z * g z) =ᵐ[volume] (fun z => hilbertHSmooth f z * g z) :=
    hf'.mono fun z hz => by simp only; rw [hz]
  have hg'' : (fun z => f z * hilbertH g z) =ᵐ[volume] (fun z => f z * hilbertHSmooth g z) :=
    hg'.mono fun z hz => by simp only; rw [hz]
  rw [integral_congr_ae hf'', integral_congr_ae hg'']
  exact hilbertH_pairing_symm hf1 hf2 hg1 hg2

theorem hilbertH_pairing_symm_L2 {f g : ℂ → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) :
    ∫ z, hilbertH f z * g z = ∫ z, f z * hilbertH g z := by
  have hHf : MemLp (hilbertH f) 2 volume := (hilbertH_memLp_two hf).1
  have hHg : MemLp (hilbertH g) 2 volume := (hilbertH_memLp_two hg).1
  have key : ∀ ε : ℝ, 0 < ε →
      ‖(∫ z, hilbertH f z * g z) - ∫ z, f z * hilbertH g z‖ ≤ ε := by
    intro ε hε
    set M : ℝ := 1 + (eLpNorm f 2 volume).toReal + (eLpNorm g 2 volume).toReal with hM_def
    have hMpos : 0 < M := by positivity
    set δ : ℝ := min 1 (ε / (2 * M)) with hδ_def
    have hδpos : 0 < δ := by positivity
    have hδle1 : δ ≤ 1 := min_le_left _ _
    have hδbound : 2 * δ * M ≤ ε := by
      rcases min_cases (1:ℝ) (ε / (2 * M)) with ⟨heq, hge⟩ | ⟨heq, _⟩
      · rw [hδ_def, heq]
        have h2M : 1 * (2 * M) ≤ ε := (le_div_iff₀ (by positivity)).mp hge
        linarith
      · rw [hδ_def, heq]
        have heq2 : 2 * (ε / (2 * M)) * M = ε := by field_simp
        linarith [heq2]
    obtain ⟨f', hf'cs, hf'sm, hf'close⟩ :=
      MemLp.exist_eLpNorm_sub_le (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num) hf hδpos
    obtain ⟨g', hg'cs, hg'sm, hg'close⟩ :=
      MemLp.exist_eLpNorm_sub_le (p := (2:ℝ≥0∞)) (by norm_num) (by norm_num) hg hδpos
    have hf'mem : MemLp f' 2 volume := hf'sm.continuous.memLp_of_hasCompactSupport hf'cs
    have hg'mem : MemLp g' 2 volume := hg'sm.continuous.memLp_of_hasCompactSupport hg'cs
    have hf'closeR : (eLpNorm (f - f') 2 volume).toReal ≤ δ := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hf'close
      rwa [ENNReal.toReal_ofReal hδpos.le] at h
    have hg'closeR : (eLpNorm (g - g') 2 volume).toReal ≤ δ := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg'close
      rwa [ENNReal.toReal_ofReal hδpos.le] at h
    have hg'norm : (eLpNorm g' 2 volume).toReal ≤ (eLpNorm g 2 volume).toReal + δ := by
      have htri : eLpNorm g' 2 volume ≤ eLpNorm g 2 volume + eLpNorm (g - g') 2 volume := by
        have heq2 : g' = g - (g - g') := by funext z; simp only [Pi.sub_apply]; ring
        conv_lhs => rw [heq2]
        exact eLpNorm_sub_le (by norm_num)
      have hne1 : eLpNorm g 2 volume ≠ ⊤ := hg.eLpNorm_ne_top
      have hne2 : eLpNorm (g - g') 2 volume ≠ ⊤ := (hg.sub hg'mem).eLpNorm_ne_top
      calc (eLpNorm g' 2 volume).toReal ≤
            (eLpNorm g 2 volume + eLpNorm (g - g') 2 volume).toReal :=
            ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hne1, hne2⟩) htri
        _ = (eLpNorm g 2 volume).toReal + (eLpNorm (g - g') 2 volume).toReal :=
            ENNReal.toReal_add hne1 hne2
        _ ≤ (eLpNorm g 2 volume).toReal + δ := by linarith
    have hf'norm : (eLpNorm f' 2 volume).toReal ≤ (eLpNorm f 2 volume).toReal + δ := by
      have htri : eLpNorm f' 2 volume ≤ eLpNorm f 2 volume + eLpNorm (f - f') 2 volume := by
        have heq2 : f' = f - (f - f') := by funext z; simp only [Pi.sub_apply]; ring
        conv_lhs => rw [heq2]
        exact eLpNorm_sub_le (by norm_num)
      have hne1 : eLpNorm f 2 volume ≠ ⊤ := hf.eLpNorm_ne_top
      have hne2 : eLpNorm (f - f') 2 volume ≠ ⊤ := (hf.sub hf'mem).eLpNorm_ne_top
      calc (eLpNorm f' 2 volume).toReal ≤
            (eLpNorm f 2 volume + eLpNorm (f - f') 2 volume).toReal :=
            ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hne1, hne2⟩) htri
        _ = (eLpNorm f 2 volume).toReal + (eLpNorm (f - f') 2 volume).toReal :=
            ENNReal.toReal_add hne1 hne2
        _ ≤ (eLpNorm f 2 volume).toReal + δ := by linarith
    have hmid : ∫ z, hilbertH f' z * g' z = ∫ z, f' z * hilbertH g' z :=
      hilbertH_pairing_symm_smooth hf'sm hf'cs hg'sm hg'cs
    have hHf'mem : MemLp (hilbertH f') 2 volume := (hilbertH_memLp_two hf'mem).1
    have hHg'mem : MemLp (hilbertH g') 2 volume := (hilbertH_memLp_two hg'mem).1
    -- Term A: ∫ Hf·g - ∫ Hf'·g'
    have hAeq : (∫ z, hilbertH f z * g z) - ∫ z, hilbertH f' z * g' z =
        (∫ z, hilbertH f z * (g z - g' z)) +
          ∫ z, (hilbertH f z - hilbertH f' z) * g' z := by
      have i1 : Integrable (fun z => hilbertH f z * g z) volume := hHf.integrable_mul hg
      have i3 : Integrable (fun z => hilbertH f' z * g' z) volume :=
        hHf'mem.integrable_mul hg'mem
      have i4 : Integrable (fun z => hilbertH f z * (g z - g' z)) volume :=
        hHf.integrable_mul (hg.sub hg'mem)
      have i5 : Integrable (fun z => (hilbertH f z - hilbertH f' z) * g' z) volume :=
        (hHf.sub hHf'mem).integrable_mul hg'mem
      rw [← MeasureTheory.integral_add i4 i5]
      have e2 : ∀ z, hilbertH f z * (g z - g' z) + (hilbertH f z - hilbertH f' z) * g' z =
          hilbertH f z * g z - hilbertH f' z * g' z := fun z => by ring
      rw [integral_congr_ae (Filter.Eventually.of_forall e2), MeasureTheory.integral_sub i1 i3]
    have hA1 : ‖∫ z, hilbertH f z * (g z - g' z)‖ ≤
        (eLpNorm f 2 volume).toReal * δ := by
      calc ‖∫ z, hilbertH f z * (g z - g' z)‖ ≤
            (eLpNorm (hilbertH f) 2 volume).toReal * (eLpNorm (g - g') 2 volume).toReal :=
            cauchy_schwarz_L2 hHf (hg.sub hg'mem)
        _ = (eLpNorm f 2 volume).toReal * (eLpNorm (g - g') 2 volume).toReal := by
            rw [(hilbertH_memLp_two hf).2]
        _ ≤ (eLpNorm f 2 volume).toReal * δ := by
            apply mul_le_mul_of_nonneg_left hg'closeR ENNReal.toReal_nonneg
    have hA2 : ‖∫ z, (hilbertH f z - hilbertH f' z) * g' z‖ ≤
        δ * ((eLpNorm g 2 volume).toReal + δ) := by
      calc ‖∫ z, (hilbertH f z - hilbertH f' z) * g' z‖ ≤
            (eLpNorm (hilbertH f - hilbertH f') 2 volume).toReal *
              (eLpNorm g' 2 volume).toReal :=
            cauchy_schwarz_L2 (hHf.sub hHf'mem) hg'mem
        _ = (eLpNorm (f - f') 2 volume).toReal * (eLpNorm g' 2 volume).toReal := by
            rw [hilbertH_eLpNorm_sub_eq hf hf'mem]
        _ ≤ δ * ((eLpNorm g 2 volume).toReal + δ) :=
            mul_le_mul hf'closeR hg'norm ENNReal.toReal_nonneg hδpos.le
    have hTermA : ‖(∫ z, hilbertH f z * g z) - ∫ z, hilbertH f' z * g' z‖ ≤
        (eLpNorm f 2 volume).toReal * δ + δ * ((eLpNorm g 2 volume).toReal + δ) := by
      rw [hAeq]
      exact (norm_add_le _ _).trans (add_le_add hA1 hA2)
    -- Term C: ∫ f'·Hg' - ∫ f·Hg
    have hCeq : (∫ z, f' z * hilbertH g' z) - ∫ z, f z * hilbertH g z =
        (∫ z, f' z * (hilbertH g' z - hilbertH g z)) +
          ∫ z, (f' z - f z) * hilbertH g z := by
      have j1 : Integrable (fun z => f' z * hilbertH g' z) volume := hf'mem.integrable_mul hHg'mem
      have j3 : Integrable (fun z => f z * hilbertH g z) volume := hf.integrable_mul hHg
      have j4 : Integrable (fun z => f' z * (hilbertH g' z - hilbertH g z)) volume :=
        hf'mem.integrable_mul (hHg'mem.sub hHg)
      have j5 : Integrable (fun z => (f' z - f z) * hilbertH g z) volume :=
        (hf'mem.sub hf).integrable_mul hHg
      rw [← MeasureTheory.integral_add j4 j5]
      have e2 : ∀ z, f' z * (hilbertH g' z - hilbertH g z) + (f' z - f z) * hilbertH g z =
          f' z * hilbertH g' z - f z * hilbertH g z := fun z => by ring
      rw [integral_congr_ae (Filter.Eventually.of_forall e2), MeasureTheory.integral_sub j1 j3]
    have hC1 : ‖∫ z, f' z * (hilbertH g' z - hilbertH g z)‖ ≤
        ((eLpNorm f 2 volume).toReal + δ) * δ := by
      calc ‖∫ z, f' z * (hilbertH g' z - hilbertH g z)‖ ≤
            (eLpNorm f' 2 volume).toReal * (eLpNorm (hilbertH g' - hilbertH g) 2 volume).toReal :=
            cauchy_schwarz_L2 hf'mem (hHg'mem.sub hHg)
        _ = (eLpNorm f' 2 volume).toReal * (eLpNorm (g' - g) 2 volume).toReal := by
            rw [hilbertH_eLpNorm_sub_eq hg'mem hg]
        _ ≤ ((eLpNorm f 2 volume).toReal + δ) * δ := by
            rw [eLpNorm_sub_comm (f := g') (g := g)]
            exact mul_le_mul hf'norm hg'closeR ENNReal.toReal_nonneg (by positivity)
    have hC2 : ‖∫ z, (f' z - f z) * hilbertH g z‖ ≤ δ * (eLpNorm g 2 volume).toReal := by
      calc ‖∫ z, (f' z - f z) * hilbertH g z‖ ≤
            (eLpNorm (f' - f) 2 volume).toReal * (eLpNorm (hilbertH g) 2 volume).toReal :=
            cauchy_schwarz_L2 (hf'mem.sub hf) hHg
        _ = (eLpNorm (f' - f) 2 volume).toReal * (eLpNorm g 2 volume).toReal := by
            rw [(hilbertH_memLp_two hg).2]
        _ ≤ δ * (eLpNorm g 2 volume).toReal := by
            rw [eLpNorm_sub_comm (f := f') (g := f)]
            exact mul_le_mul_of_nonneg_right hf'closeR ENNReal.toReal_nonneg
    have hTermC : ‖(∫ z, f' z * hilbertH g' z) - ∫ z, f z * hilbertH g z‖ ≤
        ((eLpNorm f 2 volume).toReal + δ) * δ + δ * (eLpNorm g 2 volume).toReal := by
      rw [hCeq]
      exact (norm_add_le _ _).trans (add_le_add hC1 hC2)
    have hfull : (∫ z, hilbertH f z * g z) - ∫ z, f z * hilbertH g z =
        ((∫ z, hilbertH f z * g z) - ∫ z, hilbertH f' z * g' z) +
          ((∫ z, hilbertH f' z * g' z) - ∫ z, f' z * hilbertH g' z) +
          ((∫ z, f' z * hilbertH g' z) - ∫ z, f z * hilbertH g z) := by ring
    rw [hfull]
    have hzero : (∫ z, hilbertH f' z * g' z) - ∫ z, f' z * hilbertH g' z = 0 :=
      sub_eq_zero.mpr hmid
    rw [hzero, add_zero]
    refine (norm_add_le _ _).trans ?_
    have hboundA : (eLpNorm f 2 volume).toReal * δ + δ * ((eLpNorm g 2 volume).toReal + δ) ≤
        δ * M := by
      rw [hM_def]
      nlinarith [ENNReal.toReal_nonneg (a := eLpNorm f 2 volume),
        ENNReal.toReal_nonneg (a := eLpNorm g 2 volume), hδle1, hδpos.le]
    have hboundC : ((eLpNorm f 2 volume).toReal + δ) * δ + δ * (eLpNorm g 2 volume).toReal ≤
        δ * M := by
      rw [hM_def]
      nlinarith [ENNReal.toReal_nonneg (a := eLpNorm f 2 volume),
        ENNReal.toReal_nonneg (a := eLpNorm g 2 volume), hδle1, hδpos.le]
    calc ‖(∫ z, hilbertH f z * g z) - ∫ z, hilbertH f' z * g' z‖ +
          ‖(∫ z, f' z * hilbertH g' z) - ∫ z, f z * hilbertH g z‖ ≤
          δ * M + δ * M := add_le_add (hTermA.trans hboundA) (hTermC.trans hboundC)
      _ = 2 * δ * M := by ring
      _ ≤ ε := hδbound
  have hnn : (0:ℝ) ≤ ‖(∫ z, hilbertH f z * g z) - ∫ z, f z * hilbertH g z‖ := norm_nonneg _
  have hz : ‖(∫ z, hilbertH f z * g z) - ∫ z, f z * hilbertH g z‖ = 0 :=
    le_antisymm (le_of_forall_pos_le_add (fun ε hε => by simpa using key ε hε)) hnn
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Smooth compactly-supported functions have exact kernel decay `~ ‖z‖⁻²` off the support,
hence lie in every `L^p`, `p > 1` (not just `L²`). -/
theorem hilbertHSmooth_memLp {φ : ℂ → ℂ} (hφ1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφ2 : HasCompactSupport φ) {p : ℝ} (hp : 1 < p) :
    MemLp (hilbertHSmooth φ) (ENNReal.ofReal p) volume := by
  have hcont : Continuous (hilbertHSmooth φ) :=
    (i1_hilbertH_eq_cauchyT_dz hφ1 hφ2).2.1.continuous
  have hφcont : Continuous φ := hφ1.continuous
  obtain ⟨R, hR0, hRsub⟩ : ∃ R : ℝ, 0 < R ∧ tsupport φ ⊆ closedBall (0:ℂ) R := by
    obtain ⟨R', hR'⟩ := hφ2.isCompact.isBounded.subset_closedBall (0:ℂ)
    exact ⟨max R' 1, by positivity, hR'.trans (closedBall_subset_closedBall (le_max_left _ _))⟩
  have hL1 : Integrable (fun ζ => ‖φ ζ‖) volume :=
    hφcont.norm.integrable_of_hasCompactSupport hφ2.norm
  set L1 : ℝ := ∫ ζ, ‖φ ζ‖ with hL1_def
  set C : ℝ := 4 * L1 / π + 1 with hC_def
  have hCpos : 0 < C := by positivity
  have hbd : ∀ z : ℂ, 2 * R ≤ ‖z‖ → ‖hilbertHSmooth φ z‖ ≤ C / ‖z‖ ^ 2 := by
    intro z hz
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hz
    have hzR : z ∉ tsupport φ := by
      intro hmem
      have hle := hRsub hmem
      rw [mem_closedBall, dist_eq_norm, sub_zero] at hle
      linarith
    have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport hzR
    set M : ℝ := R + ‖z‖ + 1 with hM_def
    have hM0 : 0 < M := by positivity
    have hvanish : ∀ ζ, M ≤ ‖ζ - z‖ → φ ζ = 0 := by
      intro ζ hζ
      by_contra hne
      have hζmem : ζ ∈ tsupport φ := subset_tsupport φ hne
      have hζR : ‖ζ‖ ≤ R := by
        have h := hRsub hζmem
        rwa [mem_closedBall, dist_eq_norm, sub_zero] at h
      have hle2 : ‖ζ - z‖ ≤ R + ‖z‖ := (norm_sub_le _ _).trans (by linarith)
      linarith
    have heq := hilbertHSmooth_eq_ballIntegral hφ1 hφ2 z hM0 hvanish
    simp only [hφz, sub_zero] at heq
    have hintg : IntegrableOn (fun ζ => φ ζ / (ζ - z) ^ 2) (ball z M) volume := by
      have h := integrableOn_ball_kernel_cancel hφ1 hφ2 z M
      simpa [hφz] using h
    have hnorm1 : ‖(-(1/π : ℂ))‖ = 1 / π := by
      rw [norm_neg, norm_div, norm_one, norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hstep1 : ‖hilbertHSmooth φ z‖ ≤
        (1 / π) * ∫ ζ in ball z M, ‖φ ζ / (ζ - z) ^ 2‖ := by
      rw [heq, norm_mul, hnorm1]
      gcongr
      exact norm_integral_le_integral_norm _
    have hpt : ∀ ζ : ℂ, ‖φ ζ / (ζ - z) ^ 2‖ ≤ 4 * ‖φ ζ‖ / ‖z‖ ^ 2 := by
      intro ζ
      rw [norm_div, norm_pow]
      by_cases hζ0 : φ ζ = 0
      · simp [hζ0]
      · have hζmem : ζ ∈ tsupport φ := subset_tsupport φ hζ0
        have hζR : ‖ζ‖ ≤ R := by
          have h := hRsub hζmem
          rwa [mem_closedBall, dist_eq_norm, sub_zero] at h
        have htri : ‖z‖ ≤ ‖z - ζ‖ + ‖ζ‖ := by simpa using norm_add_le (z - ζ) ζ
        have hlow : ‖z‖ / 2 ≤ ‖z - ζ‖ := by linarith
        have hlow' : ‖z‖ / 2 ≤ ‖ζ - z‖ := by rwa [norm_sub_rev] at hlow
        have hpos2 : 0 < ‖ζ - z‖ := lt_of_lt_of_le (by positivity) hlow'
        have hsq : (‖z‖ / 2) ^ 2 ≤ ‖ζ - z‖ ^ 2 := by
          apply pow_le_pow_left₀ (by positivity) hlow'
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hsq (norm_nonneg (φ ζ))]
    have hRHSint : Integrable (fun ζ => 4 * ‖φ ζ‖ / ‖z‖ ^ 2) volume := by
      have h := hL1.const_mul (4 / ‖z‖ ^ 2)
      refine h.congr (Filter.Eventually.of_forall fun ζ => ?_)
      ring
    have hstep2 : (∫ ζ in ball z M, ‖φ ζ / (ζ - z) ^ 2‖) ≤ ∫ ζ, 4 * ‖φ ζ‖ / ‖z‖ ^ 2 :=
      (setIntegral_mono_ae hintg.norm hRHSint.restrict (Eventually.of_forall hpt)).trans
        (setIntegral_le_integral hRHSint (Eventually.of_forall (fun ζ => by positivity)))
    have hfinal : (∫ ζ, 4 * ‖φ ζ‖ / ‖z‖ ^ 2) = 4 * L1 / ‖z‖ ^ 2 := by
      have hrw : (fun ζ => 4 * ‖φ ζ‖ / ‖z‖ ^ 2) = fun ζ => (4 / ‖z‖ ^ 2) * ‖φ ζ‖ := by
        funext ζ; ring
      rw [hrw, integral_const_mul, hL1_def]; ring
    calc ‖hilbertHSmooth φ z‖ ≤ (1/π) * ∫ ζ in ball z M, ‖φ ζ / (ζ - z) ^ 2‖ := hstep1
      _ ≤ (1/π) * ∫ ζ, 4 * ‖φ ζ‖ / ‖z‖ ^ 2 := by gcongr
      _ = (4 * L1 / π) / ‖z‖ ^ 2 := by rw [hfinal]; ring
      _ ≤ C / ‖z‖ ^ 2 := by
          apply div_le_div_of_nonneg_right (by linarith) (by positivity)
  refine memLp_iff.mpr ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr (by linarith)).ne'
    ENNReal.ofReal_ne_top hcont.aestronglyMeasurable, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ p)]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
  rw [← lintegral_add_compl (fun x => ‖hilbertHSmooth φ x‖ₑ ^ p)
    (measurableSet_closedBall : MeasurableSet (closedBall (0:ℂ) (2 * R)))]
  refine (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩).ne
  · -- inside the closed ball: bounded, finite measure
    obtain ⟨K, hK⟩ := (isCompact_closedBall (0:ℂ) (2*R)).exists_bound_of_continuousOn
      hcont.continuousOn
    calc ∫⁻ z in closedBall (0:ℂ) (2*R), ‖hilbertHSmooth φ z‖ₑ ^ p ≤
          ∫⁻ _z in closedBall (0:ℂ) (2*R), ENNReal.ofReal (max K 0) ^ p := by
          apply setLIntegral_mono' measurableSet_closedBall
          intro z hzmem
          apply ENNReal.rpow_le_rpow _ (by linarith)
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal ((hK z hzmem).trans (le_max_left _ _))
      _ = ENNReal.ofReal (max K 0) ^ p * volume (closedBall (0:ℂ) (2*R)) := by
          rw [setLIntegral_const]
      _ < ⊤ := by
          apply ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
          exact measure_closedBall_lt_top
  · -- outside: the ~‖z‖⁻² decay, integrable for p > 1
    have hset : (closedBall (0:ℂ) (2*R))ᶜ = {z : ℂ | 2*R < ‖z - (0:ℂ)‖} := by
      ext z; simp [mem_closedBall, dist_eq_norm, not_le]
    have hpt2 : ∀ z : ℂ, z ∈ (closedBall (0:ℂ) (2*R))ᶜ →
        ‖hilbertHSmooth φ z‖ₑ ^ p ≤ ENNReal.ofReal C ^ p * ‖z - (0:ℂ)‖ₑ ^ (-(2 * p) : ℝ) := by
      intro z hz
      rw [sub_zero]
      rw [mem_compl_iff, mem_closedBall_zero_iff, not_le] at hz
      have hz2 : 2 * R ≤ ‖z‖ := hz.le
      have hzpos : (0:ℝ) < ‖z‖ := lt_of_lt_of_le (by positivity) hz2
      have hb := hbd z hz2
      have hb' : ‖hilbertHSmooth φ z‖ₑ ≤ ENNReal.ofReal C * ‖z‖ₑ ^ (-2 : ℝ) := by
        have hCz : C / ‖z‖ ^ 2 = C * ‖z‖ ^ (-2:ℝ) := by
          rw [Real.rpow_neg hzpos.le, Real.rpow_two]
          ring
        have hb2 : ‖hilbertHSmooth φ z‖ ≤ C * ‖z‖ ^ (-2:ℝ) := by rw [← hCz]; exact hb
        rw [← ofReal_norm, ← ofReal_norm (x := z), ENNReal.ofReal_rpow_of_pos hzpos,
          ← ENNReal.ofReal_mul hCpos.le]
        exact ENNReal.ofReal_le_ofReal hb2
      calc ‖hilbertHSmooth φ z‖ₑ ^ p ≤ (ENNReal.ofReal C * ‖z‖ₑ ^ (-2:ℝ)) ^ p :=
            ENNReal.rpow_le_rpow hb' (by linarith)
        _ = ENNReal.ofReal C ^ p * ‖z‖ₑ ^ (-(2 * p) : ℝ) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith), ← ENNReal.rpow_mul]
            congr 2
            ring
    calc ∫⁻ z in (closedBall (0:ℂ) (2*R))ᶜ, ‖hilbertHSmooth φ z‖ₑ ^ p ≤
          ∫⁻ z in (closedBall (0:ℂ) (2*R))ᶜ,
            ENNReal.ofReal C ^ p * ‖z - (0:ℂ)‖ₑ ^ (-(2 * p) : ℝ) :=
          setLIntegral_mono' measurableSet_closedBall.compl hpt2
      _ = ENNReal.ofReal C ^ p *
            ∫⁻ z in {z : ℂ | 2*R < ‖z - (0:ℂ)‖}, ‖z - (0:ℂ)‖ₑ ^ (-(2 * p) : ℝ) := by
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
            ENNReal.ofReal_ne_top), hset]
      _ < ⊤ := by
          rw [lintegral_compl_ball_sub_enorm_rpow_neg (a := 2*p) (by linarith) (by positivity) 0]
          finiteness

theorem hilbertH_boundedLp_of_gt_two {p : ℝ} (hp : 2 < p) :
    ∃ A : ℝ, ∀ ω : ℂ → ℂ, MemLp ω 2 → MemLp ω (ENNReal.ofReal p) →
      eLpNorm (hilbertH ω) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal A * eLpNorm ω (ENNReal.ofReal p) volume := by
  set q : ℝ := p / (p - 1) with hq_def
  have hp0 : (0:ℝ) < p := by linarith
  have hp1 : (0:ℝ) < p - 1 := by linarith
  have hq1 : 1 < q := by
    rw [hq_def, lt_div_iff₀ hp1]; linarith
  have hq2 : q < 2 := by
    rw [hq_def, div_lt_iff₀ hp1]; nlinarith
  have hpq : p.HolderConjugate q := by
    refine ⟨?_, hp0, by linarith⟩
    rw [hq_def, inv_div]
    field_simp
    ring
  obtain ⟨Aq0, hAq0⟩ := hilbertH_boundedLp_of_lt_two hq1 hq2
  set Aq : ℝ := max Aq0 0 with hAq_def
  have hAqnn : 0 ≤ Aq := le_max_right _ _
  have hofReal_eq : ENNReal.ofReal Aq0 = ENNReal.ofReal Aq := by
    rcases le_total 0 Aq0 with h | h
    · rw [hAq_def, max_eq_left h]
    · rw [hAq_def, max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  have hAq : ∀ ω : ℂ → ℂ, MemLp ω 2 volume → MemLp ω (ENNReal.ofReal q) volume →
      eLpNorm (hilbertH ω) (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal Aq * eLpNorm ω (ENNReal.ofReal q) volume := by
    intro ω hω2 hωq
    rw [← hofReal_eq]
    exact hAq0 ω hω2 hωq
  refine ⟨Aq, fun ω hω2 hωp => ?_⟩
  have hbound : ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal Aq * eLpNorm φ (ENNReal.ofReal p) volume := by
    intro φ hφ1 hφ2
    have hφmem2 : MemLp φ 2 volume := hφ1.continuous.memLp_of_hasCompactSupport hφ2
    have hφmemp : MemLp φ (ENNReal.ofReal p) volume :=
      hφ1.continuous.memLp_of_hasCompactSupport hφ2
    have hHφmem : MemLp (hilbertHSmooth φ) (ENNReal.ofReal p) volume :=
      hilbertHSmooth_memLp hφ1 hφ2 (by linarith : (1:ℝ) < p)
    set Cconst : ℝ := Aq * (eLpNorm φ (ENNReal.ofReal p) volume).toReal with hCconst_def
    have hCconstnn : 0 ≤ Cconst := by positivity
    have := eLpNorm_le_of_forall_dual_simpleFunc_le hpq hHφmem hCconstnn
      (fun g hg => by
        have hgmemq : MemLp (g : ℂ → ℂ) (ENNReal.ofReal q) volume :=
          lt_of_le_of_lt hg (by norm_num)
        have hgmem2 : MemLp (g : ℂ → ℂ) 2 volume := by
          have hqne0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
          exact MeasureTheory.SimpleFunc.memLp_of_finite_measure_preimage 2
            ((MeasureTheory.SimpleFunc.memLp_iff hqne0 ENNReal.ofReal_ne_top).mp hgmemq)
        have heq1 : (∫ z, hilbertHSmooth φ z * g z) = ∫ z, hilbertH φ z * g z := by
          apply integral_congr_ae
          filter_upwards [hilbertH_eq_ae_smooth hφ1 hφ2] with z hz
          rw [hz]
        rw [heq1, hilbertH_pairing_symm_L2 hφmem2 hgmem2]
        have hHgbound : eLpNorm (hilbertH g) (ENNReal.ofReal q) volume ≤
            ENNReal.ofReal Aq * eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume :=
          hAq g hgmem2 hgmemq
        have hHgmemq : MemLp (hilbertH (g : ℂ → ℂ)) (ENNReal.ofReal q) volume :=
          lt_of_le_of_lt hHgbound
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgmemq.eLpNorm_lt_top)
        have hHolder : ‖∫ z, φ z * hilbertH g z‖ ≤
            (eLpNorm φ (ENNReal.ofReal p) volume).toReal *
              (eLpNorm (hilbertH g) (ENNReal.ofReal q) volume).toReal := by
          have hpowp : ((eLpNorm φ (ENNReal.ofReal p) volume ^ p).toReal) ^ (1/p) =
              (eLpNorm φ (ENNReal.ofReal p) volume).toReal := by
            rw [← ENNReal.toReal_rpow, ← Real.rpow_mul ENNReal.toReal_nonneg, mul_one_div,
              div_self hp0.ne', Real.rpow_one]
          have hpowq : ((eLpNorm (hilbertH g) (ENNReal.ofReal q) volume ^ q).toReal) ^ (1/q) =
              (eLpNorm (hilbertH g) (ENNReal.ofReal q) volume).toReal := by
            rw [← ENNReal.toReal_rpow, ← Real.rpow_mul ENNReal.toReal_nonneg, mul_one_div,
              div_self (by linarith : q ≠ 0), Real.rpow_one]
          calc ‖∫ z, φ z * hilbertH g z‖ ≤ ∫ z, ‖φ z * hilbertH g z‖ :=
                norm_integral_le_integral_norm _
            _ = ∫ z, ‖φ z‖ * ‖hilbertH g z‖ := by simp_rw [norm_mul]
            _ ≤ (∫ z, ‖φ z‖ ^ p) ^ (1/p) * (∫ z, ‖hilbertH g z‖ ^ q) ^ (1/q) :=
                integral_mul_norm_le_Lp_mul_Lq hpq hφmemp hHgmemq
            _ = (eLpNorm φ (ENNReal.ofReal p) volume).toReal *
                  (eLpNorm (hilbertH g) (ENNReal.ofReal q) volume).toReal := by
                rw [integral_norm_rpow_eq_toReal_pow (by linarith) hφmemp.aestronglyMeasurable,
                  integral_norm_rpow_eq_toReal_pow (by linarith) hHgmemq.aestronglyMeasurable, hpowp, hpowq]
        have hHgboundR : (eLpNorm (hilbertH g) (ENNReal.ofReal q) volume).toReal ≤
            Aq * (eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume).toReal := by
          have h1 := ENNReal.toReal_mono (by finiteness) hHgbound
          rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hAqnn] at h1
        have hgnormR : (eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume).toReal ≤ 1 := by
          have h1 := ENNReal.toReal_mono (by norm_num) hg
          rwa [ENNReal.toReal_one] at h1
        rw [hCconst_def]
        calc ‖∫ z, φ z * hilbertH g z‖ ≤
              (eLpNorm φ (ENNReal.ofReal p) volume).toReal *
                (eLpNorm (hilbertH g) (ENNReal.ofReal q) volume).toReal := hHolder
          _ ≤ (eLpNorm φ (ENNReal.ofReal p) volume).toReal * (Aq * 1) := by
              apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
              exact hHgboundR.trans (by nlinarith [hgnormR])
          _ = Aq * (eLpNorm φ (ENNReal.ofReal p) volume).toReal := by ring)
    rwa [ENNReal.ofReal_mul hAqnn, ENNReal.ofReal_toReal hφmemp.eLpNorm_ne_top] at this
  obtain ⟨-, hfin⟩ := hilbertH_memLp_of_smooth_bound (by linarith : (1:ℝ) < p) hbound ω hωp
  exact hfin



theorem zygmund_calderon_of_cz {p : ℝ} (hp : 1 < p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal A * eLpNorm φ (ENNReal.ofReal p) volume := by
  rcases lt_trichotomy p 2 with hp2 | hp2 | hp2
  · -- 1 < p < 2, via S4.
    obtain ⟨A, hA⟩ := hilbertH_boundedLp_of_lt_two hp hp2
    refine ⟨max A 0, le_max_right _ _, fun φ hφ1 hφ2 => ?_⟩
    have hφL2 : MemLp φ 2 volume := hφ1.continuous.memLp_of_hasCompactSupport hφ2
    have hφLp : MemLp φ (ENNReal.ofReal p) volume := hφ1.continuous.memLp_of_hasCompactSupport hφ2
    have hbound := hA φ hφL2 hφLp
    have hcongr : hilbertH φ =ᵐ[volume] hilbertHSmooth φ := hilbertH_eq_ae_smooth hφ1 hφ2
    rw [eLpNorm_congr_ae hcongr] at hbound
    refine hbound.trans (mul_le_mul_left ?_ _)
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  · -- p = 2, via the exact isometry.
    subst hp2
    refine ⟨1, zero_le_one, fun φ hφ1 hφ2 => ?_⟩
    rw [ofReal_two_eq, ENNReal.ofReal_one, one_mul]
    exact (i4_eLpNorm_eq hφ1 hφ2).le
  · -- p > 2, via S5.
    obtain ⟨A, hA⟩ := hilbertH_boundedLp_of_gt_two hp2
    refine ⟨max A 0, le_max_right _ _, fun φ hφ1 hφ2 => ?_⟩
    have hφL2 : MemLp φ 2 volume := hφ1.continuous.memLp_of_hasCompactSupport hφ2
    have hφLp : MemLp φ (ENNReal.ofReal p) volume := hφ1.continuous.memLp_of_hasCompactSupport hφ2
    have hbound := hA φ hφL2 hφLp
    have hcongr : hilbertH φ =ᵐ[volume] hilbertHSmooth φ := hilbertH_eq_ae_smooth hφ1 hφ2
    rw [eLpNorm_congr_ae hcongr] at hbound
    refine hbound.trans (mul_le_mul_left ?_ _)
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)


/-- The Calderón–Zygmund bound on `C₀^∞` (THE WALL — cites Vekua's monograph, owner -d4), in
`ENNReal` form matching `hilbertH_tendsto_of_smooth_bound`'s `hbound` hypothesis. -/
theorem zygmund_calderon {p : ℝ} (hp : 1 < p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal A * eLpNorm φ (ENNReal.ofReal p) volume := by
  exact zygmund_calderon_of_cz hp

/-- The operator norm `Λ_p = sup ‖H(ω)‖_p / ‖ω‖_p` of `H` on `L_p`. -/
def hilbertNorm (p : ℝ) : ℝ :=
  sSup {c : ℝ | ∃ ω : ℂ → ℂ, MemLp ω (ENNReal.ofReal p) ∧ eLpNorm ω (ENNReal.ofReal p) ≠ 0 ∧
    c = (eLpNorm (hilbertH ω) (ENNReal.ofReal p)).toReal / (eLpNorm ω (ENNReal.ofReal p)).toReal}

theorem hilbertNorm_nonneg (p : ℝ) : 0 ≤ hilbertNorm p := by
  rw [hilbertNorm]
  refine Real.sSup_nonneg ?_
  rintro c ⟨ω, -, -, rfl⟩
  exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- (11.16'), `ENNReal` form: `‖H(ω)‖_p ≤ Λ_p ‖ω‖_p` for all `ω ∈ L_p`, `1 < p < ∞`. Tainted by
exactly `zygmund_calderon`'s one sorry. -/
theorem hilbertNorm_bddAbove (p : ℝ) (hp : 1 < p) :
    BddAbove {c : ℝ | ∃ ω : ℂ → ℂ, MemLp ω (ENNReal.ofReal p) ∧ eLpNorm ω (ENNReal.ofReal p) ≠ 0 ∧
      c = (eLpNorm (hilbertH ω) (ENNReal.ofReal p)).toReal / (eLpNorm ω (ENNReal.ofReal p)).toReal} := by
  obtain ⟨A, hA0, hbound⟩ := zygmund_calderon hp
  refine ⟨A, ?_⟩
  rintro c ⟨ω, hω, hne, rfl⟩
  have hb := (hilbertH_memLp_of_smooth_bound hp hbound ω hω).2
  have hωpos : (0:ℝ) < (eLpNorm ω (ENNReal.ofReal p)).toReal := by
    rcases eq_or_ne (eLpNorm ω (ENNReal.ofReal p)) ⊤ with htop | htop
    · exact absurd htop hω.eLpNorm_ne_top
    · exact (ENNReal.toReal_pos hne htop)
  rw [div_le_iff₀ hωpos]
  have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω.eLpNorm_ne_top) hb
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA0] at h1

/-- `hilbertH` extends to a bounded linear operator on `L_p`, `1 < p < ∞` — general form,
tainted by `zygmund_calderon`'s one sorry. -/
theorem hilbertH_memLp {p : ℝ} (hp : 1 < p) {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p)) :
    MemLp (hilbertH ω) (ENNReal.ofReal p) := by
  obtain ⟨A, hA0, hbound⟩ := zygmund_calderon hp
  exact (hilbertH_memLp_of_smooth_bound hp hbound ω hω).1

/-- (11.16): `‖H(ω)‖_p ≤ Λ_p ‖ω‖_p` for all `ω ∈ L_p`, `1 < p < ∞`. -/
theorem eq11_16 {p : ℝ} (hp : 1 < p) {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p)) :
    (eLpNorm (hilbertH ω) (ENNReal.ofReal p)).toReal ≤
      hilbertNorm p * (eLpNorm ω (ENNReal.ofReal p)).toReal := by
  rcases eq_or_ne (eLpNorm ω (ENNReal.ofReal p)) 0 with hzero | hne
  · obtain ⟨A, hA0, hbound⟩ := zygmund_calderon hp
    have hb := (hilbertH_memLp_of_smooth_bound hp hbound ω hω).2
    rw [hzero, mul_zero] at hb
    have hH0 : eLpNorm (hilbertH ω) (ENNReal.ofReal p) = 0 := le_zero_iff.mp hb
    rw [hzero, hH0, ENNReal.toReal_zero, mul_zero]
  · have hb := hilbertNorm_bddAbove p hp
    have hmem : (eLpNorm (hilbertH ω) (ENNReal.ofReal p)).toReal /
        (eLpNorm ω (ENNReal.ofReal p)).toReal ∈
        {c : ℝ | ∃ ω : ℂ → ℂ, MemLp ω (ENNReal.ofReal p) ∧ eLpNorm ω (ENNReal.ofReal p) ≠ 0 ∧
          c = (eLpNorm (hilbertH ω) (ENNReal.ofReal p)).toReal /
            (eLpNorm ω (ENNReal.ofReal p)).toReal} := ⟨ω, hω, hne, rfl⟩
    have hle := le_csSup hb hmem
    have hωpos : (0:ℝ) < (eLpNorm ω (ENNReal.ofReal p)).toReal :=
      ENNReal.toReal_pos hne hω.eLpNorm_ne_top
    rwa [div_le_iff₀ hωpos] at hle

/-- (11.16), `ENNReal` form: equivalent to `eq11_16` (both sides are finite, using
`hilbertH_memLp` and `hilbertNorm_nonneg`), but more directly composable in `eLpNorm` chains. -/
theorem eq11_16_eLpNorm {p : ℝ} (hp : 1 < p) {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p)) :
    eLpNorm (hilbertH ω) (ENNReal.ofReal p) ≤
      ENNReal.ofReal (hilbertNorm p) * eLpNorm ω (ENNReal.ofReal p) := by
  have hb := eq11_16 hp hω
  have h1 : eLpNorm (hilbertH ω) (ENNReal.ofReal p) ≠ ⊤ := (hilbertH_memLp hp hω).eLpNorm_ne_top
  have h2 : eLpNorm ω (ENNReal.ofReal p) ≠ ⊤ := hω.eLpNorm_ne_top
  have hc := ENNReal.ofReal_le_ofReal hb
  rwa [ENNReal.ofReal_toReal h1, ENNReal.ofReal_mul (hilbertNorm_nonneg p),
    ENNReal.ofReal_toReal h2] at hc

/-! ## Linearity block (for `-ea`'s analytic-family / simple-function needs). -/

/-- Extract an a.e.-pointwise-convergent SUBSEQUENCE of the approximants' `hilbertHSmooth`-images,
converging to `hilbertH ω` — the common tool behind both `hilbertH_tendsto_zero_ae_of_bounded_support`
and `hilbertH_eq_integral_ae_off_support`. -/
theorem hilbertH_exists_seq_tendsto_ae {ω : ℂ → ℂ} {p : ℝ} (hp : 1 < p)
    (hω : MemLp ω (ENNReal.ofReal p)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ z ∂volume, Tendsto (fun k => hilbertHSmooth (hilbertHApprox ω (ns k)) z) atTop
        (𝓝 (hilbertH ω z)) := by
  obtain ⟨A, hA0, hbound⟩ := zygmund_calderon hp
  obtain ⟨hmem, -, hconv⟩ := hilbertH_tendsto_of_smooth_bound hp hbound ω hω
  have hp0 : (0:ℝ) < p := lt_trans one_pos hp
  have hpne0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  have hfmeas : ∀ n, AEStronglyMeasurable (fun z => hilbertHSmooth (hilbertHApprox ω n) z) volume :=
    fun n => (i1_hilbertH_eq_cauchyT_dz (hilbertHApprox_contDiff hp.le hω n)
      (hilbertHApprox_hasCompactSupport ω n)).2.1.continuous.aestronglyMeasurable
  have htm : TendstoInMeasure volume (fun n z => hilbertHSmooth (hilbertHApprox ω n) z) atTop
      (hilbertH ω) := tendstoInMeasure_of_tendsto_eLpNorm hpne0 hconv
  obtain ⟨ns, hns, hnsae⟩ := htm.exists_seq_tendsto_ae
  exact ⟨ns, hns, hnsae⟩

-- Strengthened from `hp : 1 ≤ p` (as in -17's proposal) to `hp : 1 < p`: `hilbertH` is only
-- pinned to a genuine (non-junk) limit for `p > 1` (via `hilbertHLim`'s `if`-condition); the sole
-- consumer (S12 `thm12_1_smooth_case`) already has `1 < p` in scope, so this is a no-op change
-- there (pass `hp1` directly instead of `hp1.le`).
set_option maxHeartbeats 1000000 in
theorem hilbertH_tendsto_zero_ae_of_bounded_support {ω : ℂ → ℂ} {p : ℝ} (hp : 1 < p)
    (hω : MemLp ω (ENNReal.ofReal p)) (hbdd : Bornology.IsBounded (Function.support ω)) :
    ∃ S : Set ℂ, volume Sᶜ = 0 ∧
      Tendsto (hilbertH ω) (cocompact ℂ ⊓ Filter.principal S) (𝓝 0) := by
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall (0:ℂ)
  have hRsupp : ∀ z, R < ‖z‖ → ω z = 0 := by
    intro z hz
    by_contra hne
    have := hR (Function.mem_support.mpr hne)
    rw [mem_closedBall_zero_iff] at this
    linarith
  set R' : ℝ := max R 0 with hR'def
  have hR'0 : (0:ℝ) ≤ R' := le_max_right _ _
  have hRsupp' : ∀ z, R' < ‖z‖ → ω z = 0 := fun z hz => hRsupp z (lt_of_le_of_lt (le_max_left R 0) hz)
  have hRsupp'trunc : ∀ n z, R' < ‖z‖ → hilbertHTrunc ω n z = 0 := by
    intro n z hz
    unfold hilbertHTrunc
    by_cases hzmem : z ∈ closedBall (0:ℂ) (n:ℝ)
    · rw [Set.indicator_of_mem hzmem]; exact hRsupp' z hz
    · rw [Set.indicator_of_notMem hzmem]
  -- each approximant has support in the FIXED ball closedBall 0 (R'+1)
  have hasupp : ∀ n z, R' + 1 < ‖z‖ → hilbertHApprox ω n z = 0 := by
    intro n z hz
    have hsub := t5Mollify_support_subset (hRsupp'trunc n) n
    by_contra hne
    have hmem := hsub (Function.mem_support.mpr hne)
    rw [mem_closedBall_zero_iff] at hmem
    linarith
  -- the uniform (in n) decay bound, via the SAME direct-formula argument as the old
  -- `hilbertH_tendsto_zero_of_bounded_support`, applied to `hilbertHApprox ω n` in place of `ω`
  have haMemLp : ∀ n, MemLp (hilbertHApprox ω n) (ENNReal.ofReal p) :=
    fun n => (hilbertHApprox_contDiff hp.le hω n).continuous.memLp_of_hasCompactSupport
      (hilbertHApprox_hasCompactSupport ω n)
  set L : ℕ → ℝ := fun n => ∫ ζ in closedBall (0:ℂ) (R'+1), ‖hilbertHApprox ω n ζ‖ with hLdef
  have hLnn : ∀ n, 0 ≤ L n := fun n =>
    setIntegral_nonneg measurableSet_closedBall (fun _ _ => norm_nonneg _)
  -- L is a bounded sequence: `hilbertHApprox_tendsto` gives global Lp convergence to ω; on the
  -- FIXED finite-measure ball K = closedBall 0 (R'+1), Hölder embeds Lp(K) into L¹(K) (since
  -- p > 1), giving L¹(K) convergence of `hilbertHApprox ω n` to ω, hence `L n → ∫_K |ω|`; a
  -- convergent real sequence is bounded. NOT closed here for time (routine but not short: needs
  -- the quantitative Hölder step `‖f‖_{L¹(K)} ≤ ‖f‖_{Lp(K)} * (vol K)^{1-1/p}`, e.g. via
  -- `ENNReal.lintegral_mul_le_Lp_mul_Lq` with the second function constant 1, as already used
  -- for `integrable_cauchyT_kernel` above) — flagged honestly rather than rushed.
  have hLbdd : ∃ C, ∀ n, L n ≤ C := by
    have hatendsto : Tendsto (fun n => eLpNorm (fun z => hilbertHApprox ω n z - ω z)
        (ENNReal.ofReal p)) atTop (𝓝 0) := hilbertHApprox_tendsto hp.le hω
    clear_value R' L
    clear hR hRsupp hR'def
    -- global `L_p` boundedness of the approximants, via the standalone lemma above
    obtain ⟨M0, hMfin, hMbdd⟩ := ENNReal.bddAbove_of_tendsto_zero hatendsto
      (fun n => ((haMemLp n).sub hω).eLpNorm_ne_top)
    have hpMemLpbdd : ∀ n, eLpNorm (hilbertHApprox ω n) (ENNReal.ofReal p) ≤
        M0 + eLpNorm ω (ENNReal.ofReal p) := by
      intro n
      have heq : hilbertHApprox ω n = (fun z => hilbertHApprox ω n z - ω z) + ω := by
        funext z; show hilbertHApprox ω n z = (hilbertHApprox ω n z - ω z) + ω z; ring
      have hs1 : eLpNorm (hilbertHApprox ω n) (ENNReal.ofReal p) =
          eLpNorm ((fun z => hilbertHApprox ω n z - ω z) + ω) (ENNReal.ofReal p) := by rw [← heq]
      have hp1e : (1:ℝ≥0∞) ≤ ENNReal.ofReal p := by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
      have hs2 : eLpNorm ((fun z => hilbertHApprox ω n z - ω z) + ω) (ENNReal.ofReal p) ≤
          eLpNorm (fun z => hilbertHApprox ω n z - ω z) (ENNReal.ofReal p) +
            eLpNorm ω (ENNReal.ofReal p) :=
        eLpNorm_add_le hp1e
      have hs3 := add_le_add (hMbdd n) (le_refl (eLpNorm ω (ENNReal.ofReal p)))
      exact hs1 ▸ (hs2.trans hs3)
    -- Hölder on the finite-measure ball K = closedBall 0 (R'+1): ‖·‖_{L¹(K)} ≤ ‖·‖_{Lp(K)} ·
    -- (vol K)^{1-1/p} ≤ ‖·‖_{Lp,global} · (vol K)^{1-1/p}, uniformly in n
    set K : Set ℂ := closedBall (0:ℂ) (R'+1) with hKdef
    haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
    have hHolder : ∀ n, eLpNorm (hilbertHApprox ω n) 1 (volume.restrict K) ≤
        eLpNorm (hilbertHApprox ω n) (ENNReal.ofReal p) (volume.restrict K) *
          (volume K) ^ (1 - 1/p) := by
      intro n
      have h1e : (1:ℝ≥0∞) ≤ ENNReal.ofReal p := by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
      have hp0 : (0:ℝ) ≤ p := le_trans zero_le_one hp.le
      have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict K)
        h1e ((haMemLp n).aestronglyMeasurable.restrict)
      simpa [ENNReal.toReal_ofReal hp0] using this
    have hCbound : ∀ n, eLpNorm (hilbertHApprox ω n) 1 (volume.restrict K) ≤
        (M0 + eLpNorm ω (ENNReal.ofReal p)) * (volume K) ^ (1 - 1/p) := by
      intro n
      refine (hHolder n).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have ht1 : eLpNorm (hilbertHApprox ω n) (ENNReal.ofReal p) (volume.restrict K) ≤
          eLpNorm (hilbertHApprox ω n) (ENNReal.ofReal p) volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
      exact ht1.trans (hpMemLpbdd n)
    set Cfin : ℝ≥0∞ := (M0 + eLpNorm ω (ENNReal.ofReal p)) * (volume K) ^ (1 - 1/p)
      with hCfindef
    have hCfinne : Cfin ≠ ⊤ := by
      refine ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨hMfin, hω.eLpNorm_ne_top⟩) ?_
      exact ENNReal.rpow_ne_top_of_nonneg (by
        have : (1:ℝ) ≤ p := hp.le
        simp only [sub_nonneg]
        rw [div_le_one (lt_trans one_pos hp)]
        linarith) measure_closedBall_lt_top.ne
    refine ⟨Cfin.toReal, fun n => ?_⟩
    have hIntOnn : IntegrableOn (hilbertHApprox ω n) K volume :=
      ((haMemLp n).mono_measure Measure.restrict_le_self).integrable (by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le)
    have hLeq : L n = (eLpNorm (hilbertHApprox ω n) 1 (volume.restrict K)).toReal := by
      have hnn : 0 ≤ᵐ[volume.restrict K] (fun ζ => ‖hilbertHApprox ω n ζ‖) :=
        Eventually.of_forall (fun x => norm_nonneg _)
      have hconv := ofReal_integral_eq_lintegral_ofReal hIntOnn.norm hnn
      have henorm : (∫⁻ ζ, ENNReal.ofReal ‖hilbertHApprox ω n ζ‖ ∂(volume.restrict K)) =
          ∫⁻ ζ, ‖hilbertHApprox ω n ζ‖ₑ ∂(volume.restrict K) := by
        refine lintegral_congr fun ζ => ?_
        rw [← ofReal_norm]
      rw [henorm] at hconv
      have hLnval : L n = ∫ ζ in K, ‖hilbertHApprox ω n ζ‖ := by rw [hLdef]
      rw [hLnval, eLpNorm_one_eq_lintegral_enorm hIntOnn.aestronglyMeasurable, ← hconv,
        ENNReal.toReal_ofReal (hLnval ▸ hLnn n)]
    rw [hLeq]
    exact ENNReal.toReal_mono hCfinne (hCbound n)
  obtain ⟨C, hC⟩ := hLbdd
  have hCnn : 0 ≤ C := (hLnn 0).trans (hC 0)
  have hbound : ∀ n z, R' + 1 < ‖z‖ →
      ‖hilbertHSmooth (hilbertHApprox ω n) z‖ ≤ (1/π) * ((‖z‖ - (R'+1))^2)⁻¹ * C := by
    intro n z hz
    set ω' := hilbertHApprox ω n with hω'def
    have hIntOn : IntegrableOn ω' (closedBall (0:ℂ) (R'+1)) := by
      haveI : IsFiniteMeasure (volume.restrict (closedBall (0:ℂ) (R'+1))) :=
        isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
      exact ((haMemLp n).mono_measure Measure.restrict_le_self).integrable (by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le)
    have hconstval : ∀ r ∈ Set.Ioo (0:ℝ) (‖z‖ - (R'+1)),
        (∫ ζ in {ζ : ℂ | r < ‖ζ - z‖}, ω' ζ / (ζ - z) ^ 2) =
          ∫ ζ in closedBall (0:ℂ) (R'+1), ω' ζ / (ζ - z) ^ 2 := by
      intro r hr
      have hsub : closedBall (0:ℂ) (R'+1) ⊆ {ζ : ℂ | r < ‖ζ - z‖} := by
        intro ζ hζ
        rw [mem_closedBall_zero_iff] at hζ
        show r < ‖ζ - z‖
        have h1 : ‖z‖ - (R'+1) ≤ ‖ζ - z‖ := by
          have h2 : ‖z‖ - ‖ζ‖ ≤ ‖z - ζ‖ := by linarith [norm_sub_norm_le z ζ]
          have h3 : ‖z - ζ‖ = ‖ζ - z‖ := norm_sub_rev z ζ
          nlinarith [hζ]
        linarith [hr.2]
      have hmeas : MeasurableSet {ζ : ℂ | r < ‖ζ - z‖} :=
        isOpen_Ioi.measurableSet.preimage (continuous_id.sub continuous_const).norm.measurable
      apply setIntegral_eq_of_subset_of_forall_diff_eq_zero hmeas hsub
      intro ζ hζ
      have h1 : ζ ∉ closedBall (0:ℂ) (R'+1) := hζ.2
      rw [mem_closedBall_zero_iff, not_le] at h1
      rw [hω'def, hasupp n ζ h1]; simp
    have hHeq : hilbertHSmooth ω' z = -(1/π : ℂ) * ∫ ζ in closedBall (0:ℂ) (R'+1), ω' ζ / (ζ - z) ^ 2 := by
      have hev : (fun r => -(1/π : ℂ) * ∫ ζ in {ζ : ℂ | r < ‖ζ - z‖}, ω' ζ / (ζ - z) ^ 2) =ᶠ[𝓝[>] (0:ℝ)]
          (fun _ => -(1/π : ℂ) * ∫ ζ in closedBall (0:ℂ) (R'+1), ω' ζ / (ζ - z) ^ 2) := by
        filter_upwards [Ioo_mem_nhdsGT (by linarith : (0:ℝ) < ‖z‖ - (R'+1))] with r hr
        rw [hconstval r hr]
      exact (tendsto_const_nhds.congr' hev.symm).limUnder_eq
    rw [hHeq, norm_mul]
    have h1 : ‖(-(1/π : ℂ))‖ = 1/π := by
      rw [norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    rw [h1]
    have hkbound : ∀ ζ ∈ closedBall (0:ℂ) (R'+1), ‖ω' ζ / (ζ - z) ^ 2‖ ≤
        ((‖z‖ - (R'+1))^2)⁻¹ * ‖ω' ζ‖ := by
      intro ζ hζ
      rw [mem_closedBall_zero_iff] at hζ
      have h1 : ‖z‖ - (R'+1) ≤ ‖ζ - z‖ := by
        have h2 : ‖z‖ - ‖ζ‖ ≤ ‖z - ζ‖ := by linarith [norm_sub_norm_le z ζ]
        have h3 : ‖z - ζ‖ = ‖ζ - z‖ := norm_sub_rev z ζ
        nlinarith [hζ]
      have hpos : (0:ℝ) < ‖z‖ - (R'+1) := by linarith
      have hζzpos : (0:ℝ) < ‖ζ - z‖ := lt_of_lt_of_le hpos h1
      rw [norm_div, norm_pow, div_eq_mul_inv, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [inv_le_inv₀ (pow_pos hζzpos 2) (by positivity)]
      exact pow_le_pow_left₀ hpos.le h1 2
    have hLHSmeas : AEStronglyMeasurable (fun ζ : ℂ => ‖ω' ζ / (ζ - z) ^ 2‖)
        (volume.restrict (closedBall (0:ℂ) (R'+1))) := by
      have hωAEM : AEMeasurable ω' (volume.restrict (closedBall (0:ℂ) (R'+1))) :=
        hIntOn.aestronglyMeasurable.aemeasurable
      have hdenAEM : AEMeasurable (fun ζ : ℂ => (ζ - z) ^ 2)
          (volume.restrict (closedBall (0:ℂ) (R'+1))) :=
        ((continuous_id.sub continuous_const).pow 2).aemeasurable
      exact (hωAEM.div hdenAEM).aestronglyMeasurable.norm
    have hLHSint : IntegrableOn (fun ζ => ‖ω' ζ / (ζ - z) ^ 2‖) (closedBall (0:ℂ) (R'+1)) := by
      apply Integrable.mono' (hIntOn.norm.const_mul (((‖z‖ - (R'+1))^2)⁻¹)) hLHSmeas
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with ζ hζ
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact hkbound ζ hζ
    have h2 : ‖∫ ζ in closedBall (0:ℂ) (R'+1), ω' ζ / (ζ - z) ^ 2‖ ≤ ((‖z‖ - (R'+1))^2)⁻¹ * L n := by
      have hs1 : ‖∫ ζ in closedBall (0:ℂ) (R'+1), ω' ζ / (ζ - z) ^ 2‖ ≤
          ∫ ζ in closedBall (0:ℂ) (R'+1), ‖ω' ζ / (ζ - z) ^ 2‖ := norm_integral_le_integral_norm _
      have hs2 : (∫ ζ in closedBall (0:ℂ) (R'+1), ‖ω' ζ / (ζ - z) ^ 2‖) ≤
          ∫ ζ in closedBall (0:ℂ) (R'+1), ((‖z‖ - (R'+1))^2)⁻¹ * ‖ω' ζ‖ :=
        setIntegral_mono_on hLHSint (hIntOn.norm.const_mul _) measurableSet_closedBall hkbound
      have hs3 : (∫ ζ in closedBall (0:ℂ) (R'+1), ((‖z‖ - (R'+1))^2)⁻¹ * ‖ω' ζ‖) =
          ((‖z‖ - (R'+1))^2)⁻¹ * L n := integral_const_mul _ _
      rw [← hs3]; exact hs1.trans hs2
    have hs4 : 1/π * ‖∫ ζ in closedBall (0:ℂ) (R'+1), ω' ζ / (ζ - z) ^ 2‖ ≤
        1/π * (((‖z‖ - (R'+1))^2)⁻¹ * L n) := mul_le_mul_of_nonneg_left h2 (by positivity)
    have hs5 : 1/π * (((‖z‖ - (R'+1))^2)⁻¹ * L n) ≤ 1/π * (((‖z‖ - (R'+1))^2)⁻¹ * C) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hC n) (by positivity)) (by positivity)
    have := hs4.trans hs5
    linarith [this]
  obtain ⟨ns, hnsmono, hnsae⟩ := hilbertH_exists_seq_tendsto_ae hp hω
  set S : Set ℂ := {z : ℂ | Tendsto (fun k => hilbertHSmooth (hilbertHApprox ω (ns k)) z) atTop
    (𝓝 (hilbertH ω z))} with hSdef
  refine ⟨S, hnsae, ?_⟩
  -- pointwise bound on `hilbertH ω`, for z ∈ S with `‖z‖ > R' + 1`: pass `hbound` to the limit
  -- along the subsequence
  have hVbound : ∀ z ∈ S, R' + 1 < ‖z‖ →
      ‖hilbertH ω z‖ ≤ (1/π) * ((‖z‖ - (R'+1))^2)⁻¹ * C := by
    intro z hzS hz
    have htendsnorm : Tendsto (fun k => ‖hilbertHSmooth (hilbertHApprox ω (ns k)) z‖) atTop
        (𝓝 ‖hilbertH ω z‖) := (continuous_norm.tendsto _).comp hzS
    exact le_of_tendsto' htendsnorm (fun k => hbound (ns k) z hz)
  -- the bound itself tends to 0 as ‖z‖ → ∞
  have hgtendsto : Tendsto (fun z : ℂ => (1/π) * ((‖z‖ - (R'+1))^2)⁻¹ * C) (cocompact ℂ) (𝓝 0) := by
    have h1 : Tendsto (fun z : ℂ => ‖z‖ - (R'+1)) (cocompact ℂ) atTop := by
      have hnorm : Tendsto (norm : ℂ → ℝ) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
      rw [Filter.tendsto_atTop] at hnorm ⊢
      intro b
      filter_upwards [hnorm (b + (R'+1))] with z hz
      linarith
    have h2 : Tendsto (fun z : ℂ => ((‖z‖ - (R'+1))^2)⁻¹) (cocompact ℂ) (𝓝 0) :=
      tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (n := 2) (by norm_num)).comp h1)
    have h3 : Tendsto (fun z : ℂ => (1/π) * ((‖z‖ - (R'+1))^2)⁻¹ * C) (cocompact ℂ)
        (𝓝 (1/π * 0 * C)) := (tendsto_const_nhds.mul h2).mul tendsto_const_nhds
    simpa using h3
  have hgtendsto' : Tendsto (fun z : ℂ => (1/π) * ((‖z‖ - (R'+1))^2)⁻¹ * C)
      (cocompact ℂ ⊓ Filter.principal S) (𝓝 0) := hgtendsto.mono_left inf_le_left
  have hRev : ∀ᶠ z : ℂ in cocompact ℂ ⊓ Filter.principal S, z ∈ S ∧ R' + 1 < ‖z‖ := by
    have h1 : ∀ᶠ z : ℂ in cocompact ℂ ⊓ Filter.principal S, z ∈ S :=
      Filter.eventually_inf_principal.2 (Eventually.of_forall (fun _ h => h))
    have h2 : ∀ᶠ z : ℂ in cocompact ℂ ⊓ Filter.principal S, R' + 1 < ‖z‖ := by
      have hsub : (closedBall (0:ℂ) (R'+1))ᶜ ⊆ {z : ℂ | R' + 1 < ‖z‖} := by
        intro z hz
        rw [mem_compl_iff, mem_closedBall_zero_iff, not_le] at hz
        exact hz
      exact Filter.mem_inf_of_left (Filter.mem_cocompact.2 ⟨closedBall (0:ℂ) (R'+1),
        isCompact_closedBall _ _, hsub⟩ : {z : ℂ | R' + 1 < ‖z‖} ∈ cocompact ℂ)
    exact h1.and h2
  refine squeeze_zero_norm' ?_ hgtendsto'
  filter_upwards [hRev] with z ⟨hzS, hzr⟩ using hVbound z hzS hzr

/-- **Theorem 11.1**: if `ω ∈ L_p`, `p > 2`, has bounded support, then `T_ω` has `L_p`
generalized derivatives in the whole plane, with `∂_{z̄} T_ω = ω` and `∂_z T_ω = H_ω` a.e.
(equivalently, `(T_ω)'_x = H_ω + ω` and `(T_ω)'_y = i(H_ω - ω)`).

Proved by mollifying `ω` (`t5Mollify`) into `C₀^∞` approximations `ω_n`, applying (11.17) to
`T(ω_n)`, and passing to the limit: `T(ω_n) → T(ω)` uniformly by `lemma11_1` (since `ω_n - ω`
has uniformly bounded support), and the mollified partials converge in `L_p` using only
`hilbertH_memLp` (existence of the principal value a.e.) and (11.16) (`H` bounded on `L_p`). -/
theorem thm11_1 {p : ℝ} (hp : 2 < p) {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p))
    (hsupp : Bornology.IsBounded (Function.support ω)) :
    HasGenPartials (cauchyT ω) (fun z => hilbertH ω z + ω z) (fun z => I * (hilbertH ω z - ω z))
      univ (ENNReal.ofReal p) ∧
    (∀ z, genDzbar (fun z => hilbertH ω z + ω z) (fun z => I * (hilbertH ω z - ω z)) z = ω z) ∧
    ∀ z, genDz (fun z => hilbertH ω z + ω z) (fun z => I * (hilbertH ω z - ω z)) z = hilbertH ω z := by
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hp1' : (1 : ℝ) < p := by linarith
  have hpne : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨R₀, hR₀⟩ := hsupp.subset_closedBall (0 : ℂ)
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = max R₀ 1 := ⟨_, rfl⟩
  have hR : (0 : ℝ) < R := by rw [hRdef]; positivity
  have hsuppR : ∀ z : ℂ, R < ‖z‖ → ω z = 0 := by
    intro z hz
    by_contra h
    have hz' : z ∈ closedBall (0 : ℂ) R₀ := hR₀ h
    rw [mem_closedBall_zero_iff] at hz'
    have hle : R₀ ≤ R := by rw [hRdef]; exact le_max_left _ _
    linarith
  set ωn : ℕ → ℂ → ℂ := fun n => t5Mollify ω n with hωndef
  set fn : ℕ → ℂ → ℂ := fun n => cauchyT (ωn n) with hfndef
  have hωnCD : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ωn n) := fun n => t5Mollify_contDiff hp1 hω n
  have hωnCS : ∀ n, HasCompactSupport (ωn n) := fun n => t5Mollify_hasCompactSupport hsupp n
  have hωnSupp : ∀ n, Function.support (ωn n) ⊆ closedBall (0 : ℂ) (R + 1) := fun n =>
    t5Mollify_support_subset hsuppR n
  have hωnMemLp : ∀ n, MemLp (ωn n) (ENNReal.ofReal p) := fun n => t5Mollify_memLp hp1 hpne hω n
  have hωnTendsto : Tendsto (fun n => eLpNorm (fun z => ωn n z - ω z) (ENNReal.ofReal p) volume)
      atTop (𝓝 0) := t5Mollify_tendsto hp1 hpne hR hω hsuppR
  have hωSupp1 : ∀ z : ℂ, R + 1 < ‖z‖ → ω z = 0 := fun z hz => hsuppR z (by linarith)
  have hωnSupp1 : ∀ n, ∀ z : ℂ, R + 1 < ‖z‖ → ωn n z = 0 := fun n z hz => by
    by_contra h
    have hmem : z ∈ closedBall (0 : ℂ) (R + 1) := hωnSupp n h
    rw [mem_closedBall_zero_iff] at hmem
    linarith
  have h17 : ∀ n, ContDiff ℝ 1 (fn n) ∧
      ∀ z, dzbar (fn n) z = ωn n z ∧ dz (fn n) z = hilbertHSmooth (ωn n) z := fun n =>
    eq11_17 (hωnCD n) (hωnCS n)
  have hHsub : ∀ n, hilbertH (fun z => ωn n z - ω z) =ᵐ[volume]
      fun z => hilbertHSmooth (ωn n) z - hilbertH ω z := fun n => by
    obtain ⟨A, hA0, hbound⟩ := zygmund_calderon hp1'
    have hs1 := hilbertH_sub_ae_of_smooth_bound hp1' hbound (hωnMemLp n) hω
    have hs2 : hilbertH (ωn n) =ᵐ[volume] hilbertHSmooth (ωn n) :=
      hilbertH_eq_ae_smooth (hωnCD n) (hωnCS n)
    filter_upwards [hs1, hs2] with z hz1 hz2
    rw [hz1, hz2]
  refine ⟨⟨?_, fn, fun n => (h17 n).1.contDiffOn, ?_, ?_⟩, ?_, ?_⟩
  · -- (i) MemLp of `g`, `h` on compacts
    intro C _ _
    have hg : MemLp (fun z => hilbertH ω z + ω z) (ENNReal.ofReal p) :=
      (hilbertH_memLp hp1' hω).add hω
    have hh : MemLp (fun z => I * (hilbertH ω z - ω z)) (ENNReal.ofReal p) :=
      ((hilbertH_memLp hp1' hω).sub hω).const_mul I
    exact ⟨hg.restrict _, hh.restrict _⟩
  · -- (iii) locally uniform (in fact uniform) convergence of `fn` to `cauchyT ω`
    obtain ⟨M₁, hM₁⟩ := lemma11_1 hp (show (0 : ℝ) < R + 1 by linarith)
    have h0 : Tendsto (fun n => (eLpNorm (fun z => ωn n z - ω z)
        (ENNReal.ofReal p) volume).toReal) atTop (𝓝 0) := by
      have hc := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hωnTendsto
      simpa [Function.comp_def] using hc
    have hMreal : Tendsto (fun n => M₁ * (eLpNorm (fun z => ωn n z - ω z)
        (ENNReal.ofReal p) volume).toReal) atTop (𝓝 0) := by
      simpa using h0.const_mul M₁
    have hsubeq : ∀ n, cauchyT (fun z => ωn n z - ω z) = fun z => fn n z - cauchyT ω z := fun n =>
      cauchyT_sub hp (show (0 : ℝ) < R + 1 by linarith) (hωnMemLp n) hω (hωnSupp1 n) hωSupp1
    have hunif : TendstoUniformly fn (cauchyT ω) atTop := by
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      filter_upwards [hMreal.eventually (gt_mem_nhds hε)] with n hn
      intro z
      rw [dist_eq_norm, norm_sub_rev, ← congrFun (hsubeq n) z]
      have hψsupp : ∀ z : ℂ, R + 1 < ‖z‖ → ωn n z - ω z = 0 := fun z hz => by
        rw [hωnSupp1 n z hz, hωSupp1 z hz, sub_zero]
      exact lt_of_le_of_lt (hM₁ _ ((hωnMemLp n).sub hω) hψsupp z) hn
    exact hunif.tendstoLocallyUniformly.tendstoLocallyUniformlyOn
  · -- (iv) L_p-on-compacts convergence of the mollified partials
    intro C _ _
    have hfx : ∀ n z, fderiv ℝ (fn n) z 1 = dz (fn n) z + dzbar (fn n) z := fun n z => by
      unfold dz dzbar; ring
    have hfy : ∀ n z, fderiv ℝ (fn n) z I = I * (dz (fn n) z - dzbar (fn n) z) := fun n z => by
      unfold dz dzbar
      have hI2 : I ^ 2 = -1 := Complex.I_sq
      have hexpand : I * ((fderiv ℝ (fn n) z 1 - I * fderiv ℝ (fn n) z I) / 2 -
          (fderiv ℝ (fn n) z 1 + I * fderiv ℝ (fn n) z I) / 2) =
          -I ^ 2 * fderiv ℝ (fn n) z I := by ring
      rw [hexpand, hI2]; ring
    have key1 : ∀ n z, fderiv ℝ (fn n) z 1 - (hilbertH ω z + ω z) =
        (hilbertHSmooth (ωn n) z - hilbertH ω z) + (ωn n z - ω z) := fun n z => by
      rw [hfx n z, ((h17 n).2 z).2, ((h17 n).2 z).1]; ring
    have key2 : ∀ n z, fderiv ℝ (fn n) z I - I * (hilbertH ω z - ω z) =
        I * ((hilbertHSmooth (ωn n) z - hilbertH ω z) - (ωn n z - ω z)) := fun n z => by
      rw [hfy n z, ((h17 n).2 z).2, ((h17 n).2 z).1]; ring
    have hbound1 : ∀ n, eLpNorm (fun z => fderiv ℝ (fn n) z 1 - (hilbertH ω z + ω z))
        (ENNReal.ofReal p) volume ≤
        (1 + ENNReal.ofReal (hilbertNorm p)) * eLpNorm (fun z => ωn n z - ω z)
          (ENNReal.ofReal p) volume := by
      intro n
      have hcong : (fun z => fderiv ℝ (fn n) z 1 - (hilbertH ω z + ω z)) =ᵐ[volume]
          fun z => (ωn n z - ω z) + hilbertH (fun z => ωn n z - ω z) z := by
        filter_upwards [hHsub n] with z hz
        rw [key1 n z, hz]
        ring
      rw [eLpNorm_congr_ae hcong]
      have hp1e : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1
      calc eLpNorm (fun z => (ωn n z - ω z) + hilbertH (fun z => ωn n z - ω z) z)
            (ENNReal.ofReal p) volume
          ≤ eLpNorm (fun z => ωn n z - ω z) (ENNReal.ofReal p) volume +
              eLpNorm (hilbertH (fun z => ωn n z - ω z)) (ENNReal.ofReal p) volume :=
            eLpNorm_add_le hp1e
        _ ≤ eLpNorm (fun z => ωn n z - ω z) (ENNReal.ofReal p) volume +
              ENNReal.ofReal (hilbertNorm p) * eLpNorm (fun z => ωn n z - ω z)
                (ENNReal.ofReal p) volume := by
            gcongr
            exact eq11_16_eLpNorm hp1' ((hωnMemLp n).sub hω)
        _ = (1 + ENNReal.ofReal (hilbertNorm p)) * eLpNorm (fun z => ωn n z - ω z)
              (ENNReal.ofReal p) volume := by ring
    have hp1e : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1
    have hbound2 : ∀ n, eLpNorm (fun z => fderiv ℝ (fn n) z I - I * (hilbertH ω z - ω z))
        (ENNReal.ofReal p) volume ≤
        (1 + ENNReal.ofReal (hilbertNorm p)) * eLpNorm (fun z => ωn n z - ω z)
          (ENNReal.ofReal p) volume := by
      intro n
      have hcong : (fun z => fderiv ℝ (fn n) z I - I * (hilbertH ω z - ω z)) =ᵐ[volume]
          (I : ℂ) • fun z => hilbertH (fun z => ωn n z - ω z) z - (ωn n z - ω z) := by
        filter_upwards [hHsub n] with z hz
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [key2 n z, hz]
      rw [eLpNorm_congr_ae hcong, eLpNorm_const_smul]
      have hInorm : ‖(I : ℂ)‖ₑ = 1 := by
        rw [← ofReal_norm, Complex.norm_I, ENNReal.ofReal_one]
      rw [hInorm, one_mul]
      calc eLpNorm (fun z => hilbertH (fun z => ωn n z - ω z) z - (ωn n z - ω z))
            (ENNReal.ofReal p) volume
          ≤ eLpNorm (hilbertH (fun z => ωn n z - ω z)) (ENNReal.ofReal p) volume +
              eLpNorm (fun z => ωn n z - ω z) (ENNReal.ofReal p) volume :=
            eLpNorm_sub_le hp1e
        _ ≤ ENNReal.ofReal (hilbertNorm p) * eLpNorm (fun z => ωn n z - ω z)
              (ENNReal.ofReal p) volume + eLpNorm (fun z => ωn n z - ω z)
              (ENNReal.ofReal p) volume := by
            gcongr
            exact eq11_16_eLpNorm hp1' ((hωnMemLp n).sub hω)
        _ = (1 + ENNReal.ofReal (hilbertNorm p)) * eLpNorm (fun z => ωn n z - ω z)
              (ENNReal.ofReal p) volume := by ring
    have hCne : (1 + ENNReal.ofReal (hilbertNorm p)) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩
    have hzero : Tendsto (fun n => (1 + ENNReal.ofReal (hilbertNorm p)) *
        eLpNorm (fun z => ωn n z - ω z) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul hωnTendsto (Or.inr hCne)
      simpa using h
    have main1 : Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (fn n) z 1 - (hilbertH ω z + ω z))
        (ENNReal.ofReal p) volume) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
        (Eventually.of_forall fun n => bot_le) (Eventually.of_forall hbound1)
    have main2 : Tendsto (fun n => eLpNorm
        (fun z => fderiv ℝ (fn n) z I - I * (hilbertH ω z - ω z))
        (ENNReal.ofReal p) volume) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
        (Eventually.of_forall fun n => bot_le) (Eventually.of_forall hbound2)
    refine ⟨?_, ?_⟩
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds main1
        (Eventually.of_forall fun n => bot_le)
        (Eventually.of_forall fun n => eLpNorm_mono_measure _ Measure.restrict_le_self)
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds main2
        (Eventually.of_forall fun n => bot_le)
        (Eventually.of_forall fun n => eLpNorm_mono_measure _ Measure.restrict_le_self)
  · -- genDzbar identity
    intro z
    unfold genDzbar
    have hI2 : I ^ 2 = -1 := Complex.I_sq
    have hexpand : ((hilbertH ω z + ω z) + I * (I * (hilbertH ω z - ω z))) / 2 =
        ((hilbertH ω z + ω z) + I ^ 2 * (hilbertH ω z - ω z)) / 2 := by ring
    rw [hexpand, hI2]; ring
  · -- genDz identity
    intro z
    unfold genDz
    have hI2 : I ^ 2 = -1 := Complex.I_sq
    have hexpand : ((hilbertH ω z + ω z) - I * (I * (hilbertH ω z - ω z))) / 2 =
        ((hilbertH ω z + ω z) - I ^ 2 * (hilbertH ω z - ω z)) / 2 := by ring
    rw [hexpand, hI2]; ring

/-! ## The norm `Λ_p` -/

/-- **Theorem 11.3**: `H` preserves the `L₂` norm, `‖H(ω)‖₂ = ‖ω‖₂` for `ω ∈ L₂`.

Reproved directly from `hilbertH_memLp_two` (the exact isometry via `i4_eLpNorm_eq` and the
Cauchy+completeness construction) — no density/continuity argument needed at this level, and no
Calderón–Zygmund wall: `#print axioms` on this theorem should report only
`[propext, Classical.choice, Quot.sound]`. -/
theorem thm11_3_isometry {ω : ℂ → ℂ} (hω : MemLp ω 2) : eLpNorm (hilbertH ω) 2 = eLpNorm ω 2 :=
  (hilbertH_memLp_two hω).2


/-- **Theorem 11.3, Corollary 1**: `Λ₂ = 1`. -/
theorem thm11_3_cor1 : hilbertNorm 2 = 1 := by
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  -- a witness: the indicator of the unit disc
  have hmem : MemLp ((ball (0 : ℂ) 1).indicator fun _ => (1 : ℂ)) (ENNReal.ofReal 2) :=
    memLp_indicator_const _ measurableSet_ball.nullMeasurableSet 1 (Or.inr measure_ball_lt_top.ne)
  have hsupp : {z : ℂ | (ball (0 : ℂ) 1).indicator (fun _ => (1 : ℂ)) z ≠ 0} = ball 0 1 := by
    ext z
    constructor
    · intro hz
      by_contra hzb
      exact hz (Set.indicator_of_notMem hzb _)
    · intro hz
      rw [Set.mem_setOf_eq, Set.indicator_of_mem hz]
      exact one_ne_zero
  have hne : eLpNorm ((ball (0 : ℂ) 1).indicator fun _ => (1 : ℂ)) (ENNReal.ofReal 2) ≠ 0 := by
    rw [h2, Ne, eLpNorm_eq_zero_iff (by norm_num)]
    intro h
    have h0 : volume {z : ℂ | (ball (0 : ℂ) 1).indicator (fun _ => (1 : ℂ)) z ≠ 0} = 0 := by
      simpa [Filter.EventuallyEq, ae_iff] using h
    rw [hsupp] at h0
    exact (measure_ball_pos volume (0 : ℂ) one_pos).ne' h0
  have hratio : ∀ ω : ℂ → ℂ, MemLp ω (ENNReal.ofReal 2) → eLpNorm ω (ENNReal.ofReal 2) ≠ 0 →
      (eLpNorm (hilbertH ω) (ENNReal.ofReal 2)).toReal /
        (eLpNorm ω (ENNReal.ofReal 2)).toReal = 1 := by
    intro ω hω hne'
    rw [h2] at hω hne' ⊢
    rw [thm11_3_isometry hω, div_self (ENNReal.toReal_ne_zero.2 ⟨hne', hω.eLpNorm_ne_top⟩)]
  have hset : {c : ℝ | ∃ ω : ℂ → ℂ, MemLp ω (ENNReal.ofReal 2) ∧
      eLpNorm ω (ENNReal.ofReal 2) ≠ 0 ∧
      c = (eLpNorm (hilbertH ω) (ENNReal.ofReal 2)).toReal /
        (eLpNorm ω (ENNReal.ofReal 2)).toReal} = {1} := by
    ext c
    simp only [mem_setOf_eq, mem_singleton_iff]
    constructor
    · rintro ⟨ω, hω, hne', rfl⟩
      exact hratio ω hω hne'
    · rintro rfl
      exact ⟨_, hmem, hne, (hratio _ hmem hne).symm⟩
  rw [hilbertNorm, hset, csSup_singleton]


end LiZhongQC
