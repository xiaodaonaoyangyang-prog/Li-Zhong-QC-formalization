import References.GarnettMarshall2005.Ch03.S02_LogarithmicPotential

/-!
# Garnett–Marshall, Chapter III §3: The energy integral

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. III §3 (pp. 79–82;
`full.md` P1:3582–3763).

Conventions as in §1–§2. The book has one symbol `I(·)` for the energy; it is modelled by two names (leader ruling
B2): `energySigned ν` (real-valued) for a signed measure `ν` with compact support and finite energy (3.1), the setting
of Theorem 3.1, and `energy μ` (in `[−∞, +∞]`, with the value `+∞` allowed) for a positive measure, finite with
compact support, the energy `I(σ)` of the measures `σ ∈ P(E)` used from §4 on. Signed measures are Mathlib's
`SignedMeasure ℂ` (finite signed Borel measures), `|ν|` is the total variation `ν.totalVariation`, and `ν` has compact
support when `|ν|` vanishes off a compact set. Area measure is `volume` on `ℂ`, and `|∇U|` is the norm of the real
derivative `fderiv ℝ U z`.

* Definition ((3.1), finite energy of a signed measure with compact support, §3, P1:3584–3590) — `HasFiniteEnergy`
* Definition (the energy integral `I(ν)` of a signed measure with finite energy, §3, P1:3590–3594) — `energySigned`
* Definition (the energy `I(σ)` of a positive measure, with values in `(−∞, +∞]`, §3–§4, used from (4.1) on) —
  `energy`
* Theorem 3.1 (§3) — `thm3_3_1_a`, `thm3_3_1_b`
* Lemma 3.2 (§3; (3.9), (3.10)) — `lemma3_3_2`

Not stated (inventory U−): the identity `I(ν) = ∫ U_ν dν` in the definition (P1:3593, Fubini's theorem under (3.1));
the announcement "the energy integral is positive definite on the space of signed measures with finite energy and zero
integral" (P1:3596, restated as Theorem 3.1); Green's formula (3.2) and the displays (3.3)–(3.8), steps of the proof of
Theorem 3.1.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References ContDiff

noncomputable section

namespace GarnettMarshall2005

/-- **Definition** ((3.1), finite energy, Ch. III §3, P1:3584–3590). Let `ν` be a signed measure with compact
support. If (3.1) `∬ |log (1/|z − ζ|)| d|ν|(ζ) d|ν|(z) < ∞`, we say `ν` has finite energy.
Modelling: `ν : SignedMeasure ℂ` and `|ν|` its total variation; the kernel `|log (1/|z − ζ|)|` is `absLogKernel`
(`+∞` on the diagonal) and the double integral a lower integral in `[0, ∞]`. -/
def HasFiniteEnergy (ν : SignedMeasure ℂ) : Prop :=
  ∫⁻ z, ∫⁻ ζ, absLogKernel z ζ ∂ν.totalVariation ∂ν.totalVariation < ⊤

/-- **Definition** (the energy integral, Ch. III §3, P1:3590–3594). For a signed measure `ν` with compact support and
finite energy, `I(ν) = ∬ log (1/|z − ζ|) dν(ζ) dν(z)`.
Modelling (leader ruling B2): real-valued, through the Jordan decomposition `ν = ν⁺ − ν⁻`: the four iterated integrals
of `log (1/|z − ζ|)` with respect to `ν^±(ζ)` and `ν^±(z)`, with their signs. Under (3.1) they converge absolutely,
and the diagonal `z = ζ`, where the real kernel `−log |z − ζ|` takes the junk value `−log 0 = 0`, is `|ν| × |ν|`-null
(the kernel `absLogKernel` is `+∞` there), so the value is the book's. Junk: when (3.1) fails (the Bochner integral of
a non-integrable function is `0`); every statement assumes (3.1). The energy of a positive measure, which may be `+∞`,
is `energy`. -/
def energySigned (ν : SignedMeasure ℂ) : ℝ :=
  let P := ν.toJordanDecomposition.posPart
  let N := ν.toJordanDecomposition.negPart
  let k : ℂ → ℂ → ℝ := fun z ζ => -Real.log ‖z - ζ‖
  (∫ z, ∫ ζ, k z ζ ∂P ∂P) - (∫ z, ∫ ζ, k z ζ ∂N ∂P) - (∫ z, ∫ ζ, k z ζ ∂P ∂N) + ∫ z, ∫ ζ, k z ζ ∂N ∂N

/-- **Definition** (the energy `I(σ)` of a positive measure, Ch. III §3, P1:3593, used with the value `+∞` from §4 on:
(4.1), Lemma 4.2, Corollary 4.3). `I(σ) = ∬ log (1/|z − ζ|) dσ(ζ) dσ(z) ∈ (−∞, +∞]`.
Modelling (leader ruling B2): the double lower integral of the positive part of the kernel `logKernel` minus that of
its negative part, in `[−∞, +∞]`. For a finite measure with compact support the negative part is finite, so the value
is the book's, `+∞` exactly when the positive part diverges. Junk: `⊥` (the difference `∞ − ∞`) only for measures
that are not finite with compact support; every statement assumes both. The book's single symbol `I(·)` is
modelled by two names (leader ruling B2): for a positive finite measure `μ` with compact support whose signed
measure satisfies (3.1), `energy μ` equals `energySigned` of that signed measure (the integral splits into its
positive and negative parts); no statement mixes the two. -/
def energy (μ : Measure ℂ) : EReal :=
  ((∫⁻ z, ∫⁻ ζ, (logKernel z ζ).toENNReal ∂μ ∂μ : ℝ≥0∞) : EReal) -
    ((∫⁻ z, ∫⁻ ζ, (-logKernel z ζ).toENNReal ∂μ ∂μ : ℝ≥0∞) : EReal)

/-- **Theorem 3.1** (Ch. III §3; cited at P1:3804, 3832 in the proof of Theorem 4.1, and in Exercise 3, P1:5124), first
part. If (3.1) holds and if `∫ dν = 0`, then `I(ν) ≥ 0`.
Modelling: "H (3.1) holds" (P1:3598) is "If (3.1) holds" [OCR or misprint; inline, no crop]; `ν` is a signed measure
with compact support (the standing assumption of §3); `∫ dν = 0` is `ν(ℂ) = 0`. -/
theorem thm3_3_1_a {ν : SignedMeasure ℂ} (hK : ∃ K : Set ℂ, IsCompact K ∧ ν.totalVariation Kᶜ = 0)
    (hν : HasFiniteEnergy ν) (h0 : ν univ = 0) : 0 ≤ energySigned ν := by
  sorry

/-- **Theorem 3.1** (Ch. III §3), second part. Under the hypotheses of the first part, if moreover `I(ν) = 0`, then
`ν ≡ 0`. -/
theorem thm3_3_1_b {ν : SignedMeasure ℂ} (hK : ∃ K : Set ℂ, IsCompact K ∧ ν.totalVariation Kᶜ = 0)
    (hν : HasFiniteEnergy ν) (h0 : ν univ = 0) (hI : energySigned ν = 0) : ν = 0 := by
  sorry

/-- Helper (Ch. III §3, Lemma 3.2). Elementary inequality in `[0, ∞]`: `(x + y)² ≤ 2x² + 2y²`. -/
theorem gm33_add_sq (x y : ℝ≥0∞) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp
  rcases eq_or_ne y ⊤ with rfl | hy
  · simp
  lift x to ℝ≥0 using hx
  lift y to ℝ≥0 using hy
  norm_cast
  rw [← NNReal.coe_le_coe]
  push_cast
  nlinarith [sq_nonneg ((x : ℝ) - (y : ℝ))]

/-- Helper (Ch. III §3, Lemma 3.2). Cauchy–Schwarz for lower integrals over an interval: `(∫₀ᵀ g)² ≤ T ∫₀ᵀ g²`. -/
theorem gm33_cs {g : ℝ → ℝ≥0∞} (hg : Measurable g) (T : ℝ) :
    (∫⁻ t in Set.Ioc (0 : ℝ) T, g t) ^ 2 ≤
      ENNReal.ofReal T * ∫⁻ t in Set.Ioc (0 : ℝ) T, g t ^ 2 := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) T))
    Real.HolderConjugate.two_two hg.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have hsq : ∀ y : ℝ≥0∞, (y ^ (1 / 2 : ℝ)) ^ 2 = y := fun y => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have h1 : ∫⁻ t in Set.Ioc (0 : ℝ) T, (g t) ^ (2 : ℝ) = ∫⁻ t in Set.Ioc (0 : ℝ) T, g t ^ 2 := by
    simp only [ENNReal.rpow_two]
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, MeasureTheory.lintegral_const, one_mul,
    MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, h1] at h
  calc (∫⁻ t in Set.Ioc (0 : ℝ) T, g t) ^ 2
      ≤ ((∫⁻ t in Set.Ioc (0 : ℝ) T, g t ^ 2) ^ (1 / 2 : ℝ) * (ENNReal.ofReal T) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left' h 2
    _ = ENNReal.ofReal T * ∫⁻ t in Set.Ioc (0 : ℝ) T, g t ^ 2 := by
        rw [mul_pow, hsq, hsq, mul_comm]

/-- Helper (Ch. III §3, Lemma 3.2). Integrating along the horizontal ray: for a smooth real function `U` and `T ≥ 0`,
`|U(z)| ≤ |U(z + T)| + ∫₀ᵀ |∇U(z + t)| dt`. -/
theorem gm33_pointwise {U : ℂ → ℝ} (hU : ContDiff ℝ ∞ U) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    ‖U z‖ₑ ≤ ‖U (z + (T : ℂ))‖ₑ + ∫⁻ t in Set.Ioc (0 : ℝ) T, ‖fderiv ℝ U (z + (t : ℂ))‖ₑ := by
  have hdiff : Differentiable ℝ U := hU.differentiable (by simp)
  have hder : ∀ t : ℝ, HasDerivAt (fun s : ℝ => U (z + (s : ℂ))) (fderiv ℝ U (z + (t : ℂ)) (1 : ℂ)) t :=
    fun t => by
      have h1 : HasDerivAt (fun s : ℝ => z + (s : ℂ)) (1 : ℂ) t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_add z
      exact (hdiff (z + (t : ℂ))).hasFDerivAt.comp_hasDerivAt t h1
  have hcont : Continuous fun t : ℝ => fderiv ℝ U (z + (t : ℂ)) (1 : ℂ) :=
    ((hU.continuous_fderiv (by simp)).comp
      (continuous_const.add Complex.continuous_ofReal)).clm_apply continuous_const
  have hftc : ∫ t in (0 : ℝ)..T, fderiv ℝ U (z + (t : ℂ)) (1 : ℂ) =
      U (z + (T : ℂ)) - U (z + ((0 : ℝ) : ℂ)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t) (hcont.intervalIntegrable _ _)
  have hz : U z = U (z + (T : ℂ)) - ∫ t in (0 : ℝ)..T, fderiv ℝ U (z + (t : ℂ)) (1 : ℂ) := by
    rw [hftc]
    simp
  calc ‖U z‖ₑ = ‖U (z + (T : ℂ)) - ∫ t in (0 : ℝ)..T, fderiv ℝ U (z + (t : ℂ)) (1 : ℂ)‖ₑ := by
        rw [← hz]
    _ ≤ ‖U (z + (T : ℂ))‖ₑ + ‖∫ t in (0 : ℝ)..T, fderiv ℝ U (z + (t : ℂ)) (1 : ℂ)‖ₑ := enorm_sub_le
    _ ≤ _ := by
        refine add_le_add le_rfl ?_
        rw [intervalIntegral.integral_of_le hT]
        refine (MeasureTheory.enorm_integral_le_lintegral_enorm _).trans
          (MeasureTheory.lintegral_mono fun t => ?_)
        rw [← ofReal_norm, ← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        simpa using (fderiv ℝ U (z + (t : ℂ))).le_opNorm (1 : ℂ)

/-- Helper (Ch. III §3, Lemma 3.2). Cauchy–Schwarz and Tonelli for the horizontal rays: for a measurable
`D : ℂ → [0, ∞]`, `∫_K (∫₀ᵀ D(z + t) dt)² dz ≤ T² ∫ D²`. -/
theorem gm33_horizontal {D : ℂ → ℝ≥0∞} (hD : Measurable D) {T : ℝ} (hT : 0 ≤ T) {K : Set ℂ}
    (hK : MeasurableSet K) :
    ∫⁻ z in K, (∫⁻ t in Set.Ioc (0 : ℝ) T, D (z + (t : ℂ))) ^ 2 ≤
      ENNReal.ofReal T ^ 2 * ∫⁻ z, D z ^ 2 := by
  have _ := hT
  have _ := hK
  have hmeas2 : Measurable fun q : ℂ × ℝ => D (q.1 + (q.2 : ℂ)) :=
    hD.comp (measurable_fst.add (Complex.measurable_ofReal.comp measurable_snd))
  have hmz : ∀ z : ℂ, Measurable fun t : ℝ => D (z + (t : ℂ)) := fun z =>
    hD.comp (measurable_const.add Complex.measurable_ofReal)
  calc ∫⁻ z in K, (∫⁻ t in Set.Ioc (0 : ℝ) T, D (z + (t : ℂ))) ^ 2
      ≤ ∫⁻ z in K, ENNReal.ofReal T * ∫⁻ t in Set.Ioc (0 : ℝ) T, D (z + (t : ℂ)) ^ 2 :=
        MeasureTheory.lintegral_mono fun z => gm33_cs (hmz z) T
    _ = ENNReal.ofReal T * ∫⁻ z in K, ∫⁻ t in Set.Ioc (0 : ℝ) T, D (z + (t : ℂ)) ^ 2 :=
        MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal T * ∫⁻ t in Set.Ioc (0 : ℝ) T, ∫⁻ z in K, D (z + (t : ℂ)) ^ 2 := by
        rw [MeasureTheory.lintegral_lintegral_swap]
        exact (hmeas2.pow_const 2).aemeasurable
    _ ≤ ENNReal.ofReal T * ∫⁻ t in Set.Ioc (0 : ℝ) T, ∫⁻ z, D z ^ 2 := by
        refine mul_le_mul' le_rfl (MeasureTheory.lintegral_mono fun t => ?_)
        calc ∫⁻ z in K, D (z + (t : ℂ)) ^ 2 ≤ ∫⁻ z, D (z + (t : ℂ)) ^ 2 :=
              MeasureTheory.setLIntegral_le_lintegral _ _
          _ = ∫⁻ z, D z ^ 2 :=
              MeasureTheory.lintegral_add_right_eq_self (fun z => D z ^ 2) (t : ℂ)
    _ = ENNReal.ofReal T ^ 2 * ∫⁻ z, D z ^ 2 := by
        rw [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
        ring

/-- **Lemma 3.2** (Ch. III §3; cited at P1:3722 in the proof of Theorem 3.1, and in App. G, P3:4392). Assume
`U_n ∈ C^∞(ℂ)` satisfy (3.9) `|U_n(z)| ≤ C/|z|` and `‖∇U_n‖₂ → 0`. Then (3.10) `∬_K |U_n|² dx dy → 0` for every
compact set `K`.
Modelling: `U_n` real-valued and smooth (`ContDiff ℝ ∞`); one constant `C` for all `n` (the proof of Theorem 3.1
applies the lemma with "`U_ε(z) = O(1/|z|)` uniformly in `ε`"); (3.9) is multiplied out, `|z| |U_n(z)| ≤ C`, since
`C/|z|` at `z = 0` would be the junk value `C/0 = 0` (at `z = 0` the book's bound is no condition); `‖∇U_n‖₂` is the
`L²(dx dy)` norm of `|∇U_n| = ‖fderiv ℝ U_n z‖`; the integrals are in `[0, ∞]`. The formulas were checked against
the equation images. -/
theorem lemma3_3_2 {U : ℕ → ℂ → ℝ} (hU : ∀ n, ContDiff ℝ ∞ (U n)) {C : ℝ} (hC : ∀ n z, ‖z‖ * |U n z| ≤ C)
    (hgrad : Tendsto (fun n => eLpNorm (fderiv ℝ (U n)) 2 volume) atTop (𝓝 0)) :
    ∀ K : Set ℂ, IsCompact K → Tendsto (fun n => ∫⁻ z in K, ‖U n z‖ₑ ^ 2) atTop (𝓝 0) := by
  intro K hK
  obtain ⟨ρ', hρ'⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  set ρ : ℝ := max ρ' 0 with hρdef
  have hρ0 : 0 ≤ ρ := le_max_right _ _
  have hρ : K ⊆ closedBall (0 : ℂ) ρ := hρ'.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hC0 : 0 ≤ C := by simpa using hC 0 0
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hvK : MeasureTheory.volume K < ⊤ := hK.measure_lt_top
  set D : ℕ → ℂ → ℝ≥0∞ := fun n z => ‖fderiv ℝ (U n) z‖ₑ with hD
  have hDm : ∀ n, Measurable (D n) := fun n =>
    ((hU n).continuous_fderiv (by simp)).measurable.enorm
  have hgrad : Tendsto (fun n => ∫⁻ z, D n z ^ 2) atTop (𝓝 0) := by
    have h1 : ∀ n, ∫⁻ z, D n z ^ 2 = (eLpNorm (fderiv ℝ (U n)) 2 MeasureTheory.volume) ^ 2 := fun n => by
      have := eLpNorm_nnreal_pow_eq_lintegral (μ := MeasureTheory.volume) (f := fderiv ℝ (U n)) (p := 2)
        (by norm_num) ((hU n).continuous_fderiv (by simp)).aestronglyMeasurable
      simpa [hD, ENNReal.rpow_two] using this.symm
    simp_rw [h1]
    have := ((ENNReal.continuous_pow 2).tendsto 0).comp hgrad
    simpa [Function.comp_def] using this
  have hmain : ∀ (n : ℕ) (T : ℝ), ρ < T → ∫⁻ z in K, ‖U n z‖ₑ ^ 2 ≤
      2 * (ENNReal.ofReal (C / (T - ρ)) ^ 2 * MeasureTheory.volume K) +
        2 * (ENNReal.ofReal T ^ 2 * ∫⁻ z, D n z ^ 2) := by
    intro n T hT
    have hT0 : 0 ≤ T := hρ0.trans hT.le
    have hTρ : 0 < T - ρ := sub_pos.2 hT
    set a : ℝ≥0∞ := ENNReal.ofReal (C / (T - ρ)) with ha
    set I : ℂ → ℝ≥0∞ := fun z => ∫⁻ t in Set.Ioc (0 : ℝ) T, D n (z + (t : ℂ)) with hI
    have hpt : ∀ z ∈ K, ‖U n z‖ₑ ≤ a + I z := by
      intro z hz
      refine (gm33_pointwise (hU n) z hT0).trans (add_le_add ?_ le_rfl)
      have h1 : ‖z‖ ≤ ρ := mem_closedBall_zero_iff.1 (hρ hz)
      have h2 : T - ρ ≤ ‖z + (T : ℂ)‖ := by
        have := norm_sub_norm_le (T : ℂ) (-z)
        rw [sub_neg_eq_add, norm_neg, Complex.norm_real, Real.norm_of_nonneg hT0, add_comm] at this
        linarith
      have h3 := hC n (z + (T : ℂ))
      have hpos : 0 < ‖z + (T : ℂ)‖ := lt_of_lt_of_le hTρ h2
      have h4 : |U n (z + (T : ℂ))| ≤ C / (T - ρ) := by
        calc |U n (z + (T : ℂ))| ≤ C / ‖z + (T : ℂ)‖ := by
              rw [le_div_iff₀ hpos]
              linarith
          _ ≤ C / (T - ρ) := div_le_div_of_nonneg_left hC0 hTρ h2
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using h4)
    calc ∫⁻ z in K, ‖U n z‖ₑ ^ 2
        ≤ ∫⁻ z in K, (2 * a ^ 2 + 2 * (I z) ^ 2) := by
          refine MeasureTheory.setLIntegral_mono' hKm fun z hz => ?_
          exact (pow_le_pow_left' (hpt z hz) 2).trans (gm33_add_sq _ _)
      _ = 2 * a ^ 2 * MeasureTheory.volume K + 2 * ∫⁻ z in K, (I z) ^ 2 := by
          rw [MeasureTheory.lintegral_add_left measurable_const, MeasureTheory.lintegral_const,
            MeasureTheory.Measure.restrict_apply_univ,
            MeasureTheory.lintegral_const_mul' _ _ (by norm_num)]
      _ ≤ 2 * (a ^ 2 * MeasureTheory.volume K) + 2 * (ENNReal.ofReal T ^ 2 * ∫⁻ z, D n z ^ 2) := by
          rw [mul_assoc]
          gcongr
          exact gm33_horizontal (hDm n) hT0 hKm
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hlim : Tendsto (fun T : ℝ => 2 * (ENNReal.ofReal (C / (T - ρ)) ^ 2 * MeasureTheory.volume K))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => C / (T - ρ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ (-ρ) tendsto_id)
    have h2 : Tendsto (fun T : ℝ => ENNReal.ofReal (C / (T - ρ))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal h1
    have h3 := ((ENNReal.continuous_pow 2).tendsto 0).comp h2
    have h4 := ENNReal.Tendsto.mul_const h3 (Or.inr hvK.ne)
    have h5 := ENNReal.Tendsto.const_mul h4 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    simpa using h5
  obtain ⟨T1, hT1⟩ := Filter.eventually_atTop.1
    ((ENNReal.tendsto_nhds_zero.1 hlim) (ε / 2) (ENNReal.half_pos hε.ne'))
  set T : ℝ := max T1 (ρ + 1) with hT
  have hTρ : ρ < T := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hT' := hT1 T (le_max_left _ _)
  have h2 : Tendsto (fun n => 2 * (ENNReal.ofReal T ^ 2 * ∫⁻ z, D n z ^ 2)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hgrad (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) :
      (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal T ^ 2 ≠ ⊤)
    have := ENNReal.Tendsto.const_mul this (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    simpa using this
  filter_upwards [ENNReal.tendsto_nhds_zero.1 h2 (ε / 2) (ENNReal.half_pos hε.ne')] with n hn
  calc ∫⁻ z in K, ‖U n z‖ₑ ^ 2 ≤ _ := hmain n T hTρ
    _ ≤ ε / 2 + ε / 2 := add_le_add hT' hn
    _ = ε := ENNReal.add_halves ε

end GarnettMarshall2005
