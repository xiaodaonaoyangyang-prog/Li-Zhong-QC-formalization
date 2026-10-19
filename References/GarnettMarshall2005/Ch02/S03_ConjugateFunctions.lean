import References.GarnettMarshall2005.Ch02.S02_GreenFunctionsPoissonKernels

/-!
# Garnett–Marshall, Chapter II §3: Conjugate functions

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. II §3 (pp. 50–59;
`full.md` P1:2264–2695).

Conventions as in Chapter I: `𝔻 = LiZhongQC.unitDisc`, `∂𝔻 = Metric.sphere 0 1`, `e^{iθ} = circleMap 0 1 θ`; a
function "on `∂𝔻`" is a function on `ℂ` read on the circle, and the book's `f(θ)` is `f(e^{iθ})`. `L^p(∂𝔻)` and
`‖·‖_∞` are taken with respect to `dθ` (`arcMeasure`, total mass `2π`); `u` is the Poisson integral
`poissonIntegral f` of a real `f ∈ L¹(∂𝔻)`. `∇u` is the real derivative `fderiv ℝ u z`, and `|∇u(z)|` is its norm.
The book's `O(·)` bounds are global bounds on `𝔻`, written `∃ C, ∀ z ∈ 𝔻, … ≤ C · …`. Norms of function classes
(`‖f‖_{C^α}`, `‖f‖_{Z*}`) take values in `[0, ∞]` and are compared there. The boundary conjugate `f̃` is defined up
to a null set; the classes `C^α` and `Z*` are read through essential suprema (`eLpNorm · ⊤`), so the statements do
not see its junk values. The level `λ` is written `lam` (`λ` is a Lean keyword).

* Definition (the conjugate function `ũ` of the Poisson integral `u` of a real `f ∈ L¹(∂𝔻)`, §3, P1:2266–2272) —
  `conjugateFunction`
* Definition ((3.1), the boundary conjugate function `f̃`, §3) — `boundaryConjugate`
* Formula (3.1) (§3, P1:2274–2284): the nontangential limit `f̃` of `ũ` exists almost everywhere — `eq2_3_1`
* Theorem 3.1 (Zygmund, §3) — `thm2_3_1_a`, `thm2_3_1_b`
* Definition ((3.2), the Lipschitz class `C^α` and its norm, §3) — `MemLipschitzClass`, `lipschitzClassNorm`
* Definition (the Herglotz integral of `f`, §3, P1:2400–2404) — `herglotzIntegral`
* Formula (3.3) (§3) — `eq2_3_3`
* Definition (`∇u = (∂u/∂x, ∂u/∂y)`, §3, P1:2406) — exists: `fderiv` (the real derivative of u at z, a linear form
  on the plane whose norm is the length of the gradient)
* Formula (3.4) (§3) — `eq2_3_4`
* Formula (3.5) (§3) — `eq2_3_5`
* Formula (3.6) (§3) — `eq2_3_6`
* Theorem 3.2 (§3; with (3.7), (3.8), (3.9); (a) ⇔ (b) is Privalov's theorem, P1:2392, 2468) — `thm2_3_2`,
  `thm2_3_2_bounds`
* Definition (the classes `C^{k+α}(∂𝔻)` and `C^{k+α}(𝔻̄)`, §3, P1:2527–2533) — `MemCkAlphaCircle`,
  `MemCkAlphaClosedDisc`
* Corollary 3.3 (§3) — `cor2_3_3`
* Definition (the Zygmund class `Z*`, its norm, Zygmund functions, §3, P1:2565–2577) — `MemZygmund`, `zygmundNorm`
* Definition (`|∇₂u(z)| = |∇u_x|`, §3, P1:2579–2585) — `grad2Norm`
* Formula (3.10) (§3; with its converse, P1:2585–2591) — `eq2_3_10`
* Theorem 3.4 (§3; with (3.11), (3.12)) — `thm2_3_4`, `thm2_3_4_bounds`
* Definition (Lipschitz function on `∂𝔻`, `|f(θ + t) − f(θ)| ≤ M|t|`, §3, P1:2559–2563) — exists: `LipschitzWith`
  (for θ ↦ f(e^{iθ}) on the real line with constant M; the inequality is written out where it is used)
* Unlabelled (§3, P1:2613–2619): `Z* ⊆ C^α` for all `α < 1`, `f` and `f̃` are continuous for `f ∈ Z*`, and Lipschitz
  functions are in `Z*` (the scale `C¹ ⊂ Lipschitz ⊂ Z* ⊂ C^α ⊂ C`), with the norm bound `‖f‖_{C^α} ≤ C_α ‖f‖_{Z*}`
  used in App. J (P3:5342) — `zygmund_subset_lipschitzClass`, `lipschitzClassNorm_le_zygmundNorm`

Not stated (inventory U−): for `|u| < π/2`, `φ(z) = ∫₀^z e^{i(u + iũ)} dζ` is a conformal map with `u = arg φ'`
(P1:2286–2298; used only for the example of §4, P1:2734); the examples of unbounded `f̃` for continuous `f`
(P1:2300–2306); every `f ∈ C^α` agrees almost everywhere with a continuous function (P1:2386, not cited); Theorem 3.2
fails for `α = 1` and Corollary 3.3 fails for `α = 0` (P1:2559–2565, negative claims, Exercise 13); the identity
`|∇₂u| = |F''|` and its integral formula (P1:2579–2583, part of the definition text). (3.13) is a step of the proof of
Theorem 3.4.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (unitDisc)
open InnerProductSpace (HarmonicOnNhd)

/-- **Definition** (the conjugate function, Ch. II §3, P1:2266–2272). Let `f ∈ L¹(∂𝔻)` be real and let `u(z)` be the
Poisson integral of `f` on `𝔻`. Then `u` is harmonic and real, and there exists a unique harmonic function `ũ(z)` such
that `ũ(0) = 0` and `F = u + iũ` is analytic on `𝔻`; `ũ` is called the conjugate function or harmonic conjugate of
`u`.
Modelling: the value over all such functions (the registered "value over all maps" pattern), a single point for
`z ∈ 𝔻` by the uniqueness (the existence is part of (3.3), `eq2_3_3`). Junk: `0` for `z ∉ 𝔻` (the values there are
unconstrained); never used there. -/
def conjugateFunction (f : ℂ → ℝ) (z : ℂ) : ℝ :=
  sSup {r : ℝ | ∃ v : ℂ → ℝ, HarmonicOnNhd v unitDisc ∧ v 0 = 0 ∧
    AnalyticOnNhd ℂ (fun w => ((poissonIntegral f w : ℝ) : ℂ) + (v w : ℂ) * I) unitDisc ∧ v z = r}

/-- **Definition** ((3.1), the boundary values of the conjugate function, Ch. II §3, P1:2274–2276).
`f̃(θ) = lim_{Γ_α(e^{iθ})∋z→e^{iθ}} ũ(z)`, the nontangential limit of `ũ`.
Modelling: the value at `ζ = e^{iθ}` of the nontangential limit (through every cone `Γ_α`, `α > 1`), taken as the
supremum of the set of such limits, which has at most one element. Junk: `0` on the null set where the limit fails
(`eq2_3_1`) and off `∂𝔻`; the statements read `f̃` only almost everywhere. -/
def boundaryConjugate (f : ℂ → ℝ) (ζ : ℂ) : ℝ :=
  sSup {A : ℝ | HasNontangentialLimit (conjugateFunction f) ζ A}

/-- **Formula (3.1)** (Ch. II §3, P1:2274–2284; cited at P1:2346 "by (3.1) and Fatou's lemma", and wherever `f̃` is
used). For real `f ∈ L¹(∂𝔻)` the nontangential limit (3.1) of `ũ` exists almost everywhere.
Modelling: almost every `ζ ∈ ∂𝔻` (for `dθ`), `ũ` has the nontangential limit `f̃(ζ)` at `ζ`. -/
theorem eq2_3_1 {f : ℂ → ℝ} (hf : Integrable f arcMeasure) :
    ∀ᵐ ζ ∂arcMeasure, HasNontangentialLimit (conjugateFunction f) ζ (boundaryConjugate f ζ) := by
  sorry

/-- **Theorem 3.1** (Zygmund; Ch. II §3), part (a) (cited at VII, P2:2625, "Zygmund's theorem, Theorem II.3.1"). Let
`f ∈ L^∞(∂𝔻)` be real with `‖f‖_∞ ≤ 1`. For `0 < λ < π/2` there is a constant `C_λ`, depending only on `λ`, such that
`∫ e^{λ|f̃(θ)|} dθ/2π ≤ C_λ`.
Modelling: `∀ λ, ∃ C_λ, ∀ f`; the integral is a lower Lebesgue integral in `[0, ∞]` over `∂𝔻` with respect to `dθ`,
so that it also asserts integrability. -/
theorem thm2_3_1_a {lam : ℝ} (hlam₀ : 0 < lam) (hlam₁ : lam < π / 2) :
    ∃ C : ℝ, ∀ f : ℂ → ℝ, MemLp f ⊤ arcMeasure → eLpNorm f ⊤ arcMeasure ≤ 1 →
      (∫⁻ ζ, ENNReal.ofReal (Real.exp (lam * |boundaryConjugate f ζ|)) ∂arcMeasure) / ENNReal.ofReal (2 * π) ≤
        ENNReal.ofReal C := by
  sorry

/-- **Definition** (the Lipschitz class `C^α`, Ch. II §3, P1:2380–2384). Let `0 < α < 1`. The Lipschitz class is
`C^α = {f ∈ L^∞(∂𝔻) : sup_{t>0} ‖f(θ + t) − f(θ)‖_∞ / t^α < ∞}`.
Modelling: `f(θ + t)` is `f(e^{it} ζ)` for `ζ = e^{iθ}`, and `‖·‖_∞` is the essential supremum over `∂𝔻` for `dθ`;
the finiteness of the supremum is a bound `C t^α` for all `t > 0`. The book's range is `0 < α < 1` (the statements
assume it); `f` may take values in any normed space (§4 applies the class to the conformal map `φ` on `∂𝔻`). -/
def MemLipschitzClass {V : Type*} [NormedAddCommGroup V] (α : ℝ) (f : ℂ → V) : Prop :=
  MemLp f ⊤ arcMeasure ∧ ∃ C : ℝ, ∀ t : ℝ, 0 < t →
    eLpNorm (fun ζ => f (Complex.exp (t * I) * ζ) - f ζ) ⊤ arcMeasure ≤ ENNReal.ofReal (C * t ^ α)

/-- **Definition** ((3.2), the Lipschitz norm, Ch. II §3, P1:2386–2390).
`‖f‖_{C^α} = ‖f‖_∞ + sup_{t>0} ‖f(θ + t) − f(θ)‖_∞ / t^α`, with values in `[0, ∞]` (finite exactly on `C^α`). -/
def lipschitzClassNorm {V : Type*} [NormedAddCommGroup V] (α : ℝ) (f : ℂ → V) : ℝ≥0∞ :=
  eLpNorm f ⊤ arcMeasure + ⨆ (t : ℝ) (_ : 0 < t),
    eLpNorm (fun ζ => f (Complex.exp (t * I) * ζ) - f ζ) ⊤ arcMeasure / ENNReal.ofReal (t ^ α)

/-- **Definition** (the Herglotz integral, Ch. II §3, P1:2400–2404). The analytic function
`F(z) = ∫_{−π}^{π} ((e^{it} + z)/(e^{it} − z)) f(t) dt/2π` of (3.3) is called the Herglotz integral of `f`.
Modelling: Mathlib's `herglotzRieszKernel 0 z ζ = (ζ + z)/(ζ − z)` averaged over the unit circle (`circleAverage`,
the mean `(1/2π) ∫₀^{2π}`, the same as `∫_{−π}^{π} … dt/2π` by periodicity), for real `f`. Junk: `0` when `f` is not
integrable on `∂𝔻` (every statement assumes integrability); for `|z| ≥ 1` the kernel is not the book's (never used
there). -/
def herglotzIntegral (f : ℂ → ℝ) (z : ℂ) : ℂ :=
  Real.circleAverage (fun ζ => herglotzRieszKernel 0 z ζ * (f ζ : ℂ)) 0 1

/-- Helper (Ch. II §3, bridge). The arc measure `dθ` of the unit circle is finite (total mass `2π`). -/
theorem gm23_isFiniteMeasure_arcMeasure : IsFiniteMeasure arcMeasure := by
  unfold arcMeasure
  have : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) (2 * π))) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  exact MeasureTheory.Measure.isFiniteMeasure_map _ _

/-- Helper (Ch. II §3). The norm of the real-linear functional `w ↦ Re (c w)` on `ℂ` is `‖c‖` (proved form). -/
theorem gm23_norm_re_mul_aux (c : ℂ) (L : ℂ →L[ℝ] ℝ) (hL : ∀ w, L w = (c * w).re) : ‖L‖ = ‖c‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c) (fun w => ?_)
    rw [hL, Real.norm_eq_abs]
    calc |(c * w).re| ≤ ‖c * w‖ := Complex.abs_re_le_norm _
      _ = ‖c‖ * ‖w‖ := norm_mul _ _
  · by_cases hc : c = 0
    · simp [hc]
    · have hcn : 0 < ‖c‖ := norm_pos_iff.2 hc
      have h1 := L.le_opNorm (starRingEnd ℂ c)
      rw [hL, Complex.norm_conj] at h1
      have h2 : (c * (starRingEnd ℂ c)).re = ‖c‖ ^ 2 := by
        rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
      rw [h2, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
      nlinarith

/-- Helper (Ch. II §3). If `g` agrees near `z` with the real part of a function with complex derivative `d` at `z`, then
`‖fderiv ℝ g z‖ = ‖d‖`. -/
theorem gm23_norm_fderiv_re {F : ℂ → ℂ} {g : ℂ → ℝ} {z d : ℂ} (hF : HasDerivAt F d z)
    (hg : g =ᶠ[𝓝 z] fun w => (F w).re) : ‖fderiv ℝ g z‖ = ‖d‖ := by
  set L0 : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.toSpanSingleton ℂ d).restrictScalars ℝ with hL0
  have hFD : HasFDerivAt (fun w => (F w).re) (Complex.reCLM.comp L0) z :=
    Complex.reCLM.hasFDerivAt.comp z (hF.hasFDerivAt.restrictScalars ℝ)
  have hfd : fderiv ℝ g z = Complex.reCLM.comp L0 := (hFD.congr_of_eventuallyEq hg).fderiv
  rw [hfd]
  exact gm23_norm_re_mul_aux _ _ (fun w => by simp [hL0, mul_comm])

/-- Helper (Ch. II §3). Harmonicity at a point is invariant under translations. -/
theorem gm23_harmonicAt_translate {u : ℂ → ℝ} {c x : ℂ} (h : InnerProductSpace.HarmonicAt u (c + x)) :
    InnerProductSpace.HarmonicAt (fun y => u (c + y)) x := by
  obtain ⟨h1, h2⟩ := h
  have hc : ContDiffAt ℝ 2 (fun y : ℂ => c + y) x := contDiffAt_const.add contDiffAt_id
  refine ⟨h1.comp x hc, ?_⟩
  have hlap : ∀ y, Laplacian.laplacian (fun y => u (c + y)) y =
      Laplacian.laplacian u (c + y) := fun y => by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
      InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
    simp only [iteratedFDeriv_comp_add_left]
  have hcont : Tendsto (fun y : ℂ => c + y) (𝓝 x) (𝓝 (c + x)) :=
    (continuous_const.add continuous_id).tendsto x
  filter_upwards [hcont.eventually h2] with y hy
  rw [hlap]
  exact hy

/-- Helper (Ch. II §3, bridge). An `arcMeasure`-integrable function is circle integrable for `circleAverage` on the
unit circle. -/
theorem gm23_circleIntegrable {f : ℂ → ℝ} (hf : Integrable f arcMeasure) : CircleIntegrable f 0 1 := by
  have hm : AEMeasurable (circleMap 0 1) (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) (2 * π))) :=
    (continuous_circleMap 0 1).measurable.aemeasurable
  have h1 : Integrable (fun θ => f (circleMap 0 1 θ)) (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) (2 * π))) :=
    (MeasureTheory.integrable_map_measure hf.aestronglyMeasurable hm).1 hf
  show IntervalIntegrable (fun θ => f (circleMap 0 1 θ)) MeasureTheory.volume 0 (2 * π)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
  exact h1

/-- Helper (Ch. II §3, bridge). In the disc the Poisson integral is the real part of the Herglotz integral
(`Re ((e^{it} + z)/(e^{it} − z)) = (1 − |z|²)/|e^{it} − z|²`). -/
theorem gm23_poissonIntegral_eq_re {f : ℂ → ℝ} (hf : Integrable f arcMeasure) {z : ℂ} (hz : z ∈ unitDisc) :
    poissonIntegral f z = (herglotzIntegral f z).re := by
  have hz' : z ∉ sphere (0 : ℂ) |(1 : ℝ)| := by
    have : ‖z‖ < 1 := by simpa [unitDisc] using hz
    simp only [abs_one, mem_sphere_iff_norm, sub_zero]
    exact this.ne
  have h := re_circleAverage_herglotzRieszKernel_smul (g := f) (gm23_circleIntegrable hf) hz'
  unfold herglotzIntegral poissonIntegral
  simp only [smul_eq_mul] at h ⊢
  rw [h]
  congr 1
  funext ζ
  simp [poissonKernel_eq_re_herglotzRieszKernel]

/-- Helper (Ch. II §3, bridge). The Herglotz integral is analytic in the disc, its imaginary part is harmonic, and it
is real at `0`. -/
theorem gm23_herglotz_analytic {f : ℂ → ℝ} (hf : Integrable f arcMeasure) :
    AnalyticOnNhd ℂ (herglotzIntegral f) unitDisc ∧
      HarmonicOnNhd (fun w => (herglotzIntegral f w).im) unitDisc ∧ (herglotzIntegral f 0).im = 0 := by
  have hcirc := gm23_circleIntegrable hf
  have hg : CircleIntegrable (fun ζ => (f ζ : ℂ)) 0 1 := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hcirc ⊢
    exact Complex.ofRealCLM.integrable_comp hcirc
  have hA : AnalyticOnNhd ℂ (herglotzIntegral f) unitDisc := by
    refine (analyticOnNhd_circleAverage_herglotzRieszKernel_smul hg).mono (fun w hw => ?_)
    have : ‖w‖ < 1 := by simpa [unitDisc] using hw
    simp only [abs_one, Set.mem_compl_iff, mem_sphere_iff_norm, sub_zero]
    exact this.ne
  refine ⟨hA, fun w hw => (hA w hw).harmonicAt_im, ?_⟩
  have hk : ∀ θ : ℝ, herglotzRieszKernel 0 0 (circleMap 0 1 θ) * (f (circleMap 0 1 θ) : ℂ) =
      ((f (circleMap 0 1 θ) : ℝ) : ℂ) := fun θ => by
    have : circleMap 0 1 θ ≠ 0 := by simp [circleMap]
    rw [herglotzRieszKernel_def]
    simp [this]
  unfold herglotzIntegral Real.circleAverage
  simp_rw [hk]
  rw [intervalIntegral.integral_ofReal]
  simp

/-- Helper (Ch. II §3, bridge). The derivative of the Herglotz integral:
`F'(z) = (1/π) ∫_{−π}^{π} e^{it} f(e^{it})/(e^{it} − z)² dt`. -/
theorem gm23_deriv_herglotz {f : ℂ → ℝ} (hf : Integrable f arcMeasure) {z : ℂ} (hz : z ∈ unitDisc) :
    deriv (herglotzIntegral f) z =
      (∫ t in (-π)..π, circleMap 0 1 t * (f (circleMap 0 1 t) : ℂ) / (circleMap 0 1 t - z) ^ 2) / (π : ℂ) := by
  have hcirc := gm23_circleIntegrable hf
  have hg : CircleIntegrable (fun ζ => (f ζ : ℂ)) 0 1 := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hcirc ⊢
    exact Complex.ofRealCLM.integrable_comp hcirc
  have hz' : z ∉ sphere (0 : ℂ) |(1 : ℝ)| := by
    have : ‖z‖ < 1 := by simpa [unitDisc] using hz
    simp only [abs_one, mem_sphere_iff_norm, sub_zero]
    exact this.ne
  have hd := hasDerivAt_circleAverage_herglotzRieszKernel_smul hg hz'
  have hdd : deriv (herglotzIntegral f) z =
      Real.circleAverage (fun ζ => (2 * ζ / (ζ - z) ^ 2) • (f ζ : ℂ)) 0 1 := hd.deriv
  rw [hdd]
  unfold Real.circleAverage
  set G : ℝ → ℂ := fun θ => (2 * circleMap 0 1 θ / (circleMap 0 1 θ - z) ^ 2) • (f (circleMap 0 1 θ) : ℂ) with hG
  have hper : Function.Periodic G (2 * π) := fun θ => by
    simp only [hG, periodic_circleMap 0 1 θ]
  have hshift := hper.intervalIntegral_add_eq 0 (-π)
  rw [zero_add, show -π + 2 * π = π by ring] at hshift
  have hG2 : ∀ t : ℝ, G t = 2 * (circleMap 0 1 t * (f (circleMap 0 1 t) : ℂ) / (circleMap 0 1 t - z) ^ 2) :=
    fun t => by
      simp only [hG, smul_eq_mul]
      ring
  show ((2 * π)⁻¹ : ℝ) • ∫ θ in (0 : ℝ)..2 * π, G θ = _
  rw [hshift]
  simp_rw [hG2]
  rw [intervalIntegral.integral_const_mul]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Complex.real_smul]
  push_cast
  field_simp

/-- Helper (Ch. II §3, uniqueness of the conjugate). A harmonic `v` with `v(0) = 0` such that `u + iv` is analytic in the
disc is the imaginary part of the Herglotz integral. -/
theorem gm23_conjugate_unique {f : ℂ → ℝ} (hf : Integrable f arcMeasure) {v : ℂ → ℝ}
    (hv : HarmonicOnNhd v unitDisc) (hv0 : v 0 = 0)
    (hva : AnalyticOnNhd ℂ (fun w => ((poissonIntegral f w : ℝ) : ℂ) + (v w : ℂ) * I) unitDisc) {z : ℂ}
    (hz : z ∈ unitDisc) : v z = (herglotzIntegral f z).im := by
  have _ := hv
  obtain ⟨hF, hH, h0⟩ := gm23_herglotz_analytic hf
  set H : ℂ → ℂ := fun w => ((poissonIntegral f w : ℝ) : ℂ) + (v w : ℂ) * I - herglotzIntegral f w with hHdef
  have hHa : AnalyticOnNhd ℂ H unitDisc := by
    refine hva.sub hF |>.congr isOpen_ball (fun w hw => rfl)
  have hHform : ∀ w ∈ unitDisc, H w = (((v w - (herglotzIntegral f w).im : ℝ)) : ℂ) * I := by
    intro w hw
    simp only [hHdef]
    rw [gm23_poissonIntegral_eq_re hf hw]
    apply Complex.ext <;> simp
  have hH0 : H 0 = 0 := by
    rw [hHform 0 (by simp [unitDisc]), hv0, h0]
    simp
  have hev : ∀ᶠ w in 𝓝 (0 : ℂ), H w = H 0 := by
    rcases (hHa 0 (by simp [unitDisc])).eventually_constant_or_nhds_le_map_nhds with h | h
    · exact h
    · exfalso
      have hre : ∀ᶠ w in 𝓝 (0 : ℂ), (H w).re = 0 := by
        filter_upwards [isOpen_ball.mem_nhds (show (0 : ℂ) ∈ unitDisc by simp [unitDisc])] with w hw
        rw [hHform w hw]
        simp
      have hmem : {x : ℂ | x.re = 0} ∈ Filter.map H (𝓝 0) := hre
      have h' := h hmem
      rw [hH0] at h'
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 h'
      have : ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ε := by
        rw [mem_ball_zero_iff]
        simp [abs_of_pos hε]
        linarith
      have := hball this
      simp at this
      linarith
  have hzero : EqOn H (fun _ => (0 : ℂ)) unitDisc := by
    refine hHa.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (isPreconnected_ball) (show (0 : ℂ) ∈ unitDisc by simp [unitDisc]) ?_
    filter_upwards [hev] with w hw using by rw [hw, hH0]
  have := hzero hz
  rw [hHform z hz] at this
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h2 := (mul_eq_zero.1 this).resolve_right hI
  have := Complex.ofReal_eq_zero.1 h2
  linarith

/-- Helper (Ch. II §3). The norm of the real-linear functional `w ↦ Re (c w)` on `ℂ` is `‖c‖`. -/
theorem gm23_norm_re_mul (c : ℂ) (L : ℂ →L[ℝ] ℝ) (hL : ∀ w, L w = (c * w).re) : ‖L‖ = ‖c‖ := by
  exact gm23_norm_re_mul_aux c L hL

/-- Helper (Ch. II §3). The Poisson kernel integrates to one:
`∫_{−π}^{π} dt/(π |e^{it} − z|²) = 2/(1 − |z|²)`. -/
theorem gm23_poisson_total {z : ℂ} (hz : z ∈ unitDisc) :
    ∫ t in (-π)..π, 1 / (π * ‖circleMap 0 1 t - z‖ ^ 2) = 2 / (1 - ‖z‖ ^ 2) := by
  have hz' : ‖z‖ < 1 := by simpa [unitDisc] using hz
  have h1 : Real.circleAverage (poissonKernel 0 z • fun _ : ℂ => (1 : ℝ)) 0 1 = 1 :=
    (InnerProductSpace.harmonicOnNhd_const (1 : ℝ)).circleAverage_poissonKernel_smul (by simpa using hz')
  have hker : ∀ t : ℝ, poissonKernel 0 z (circleMap 0 1 t) =
      (1 - ‖z‖ ^ 2) * (1 / ‖circleMap 0 1 t - z‖ ^ 2) := fun t => by
    simp [poissonKernel_def]
    ring
  unfold Real.circleAverage at h1
  simp only [Pi.mul_apply, smul_eq_mul, mul_one, hker] at h1
  rw [intervalIntegral.integral_const_mul] at h1
  have hKper : Function.Periodic (fun t : ℝ => 1 / (π * ‖circleMap 0 1 t - z‖ ^ 2)) (2 * π) :=
    fun t => by simp only [periodic_circleMap 0 1 t]
  have hshift := hKper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at hshift
  rw [hshift]
  have hsplit : ∀ t : ℝ, 1 / (π * ‖circleMap 0 1 t - z‖ ^ 2) = π⁻¹ * (1 / ‖circleMap 0 1 t - z‖ ^ 2) :=
    fun t => by rw [one_div, one_div, mul_inv]
  simp_rw [hsplit]
  rw [intervalIntegral.integral_const_mul]
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hz2 : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hJ : (1 - ‖z‖ ^ 2) * (∫ t in (0 : ℝ)..2 * π, 1 / ‖circleMap 0 1 t - z‖ ^ 2) = 2 * π := by
    have := h1
    field_simp at this
    linarith
  generalize (∫ t in (0 : ℝ)..2 * π, 1 / ‖circleMap 0 1 t - z‖ ^ 2) = J at hJ ⊢
  rw [eq_div_iff hz2.ne']
  field_simp
  linarith [hJ]

/-- Helper (Ch. II §3). The size of `(1/π) ∫ e^{it} f(e^{it})/(e^{it} − z)² dt` for `f ∈ L^∞`:
at most `‖f‖_∞ ∫ dt/(π |e^{it} − z|²)`. -/
theorem gm23_integral_bound {f : ℂ → ℝ} (hf : MemLp f ⊤ arcMeasure) {z : ℂ} (hz : z ∈ unitDisc) :
    ‖(∫ t in (-π)..π, circleMap 0 1 t * (f (circleMap 0 1 t) : ℂ) / (circleMap 0 1 t - z) ^ 2) / (π : ℂ)‖ ≤
      (∫ t in (-π)..π, 1 / (π * ‖circleMap 0 1 t - z‖ ^ 2)) * (eLpNorm f ⊤ arcMeasure).toReal := by
  have hfin := gm23_isFiniteMeasure_arcMeasure
  have hfi : Integrable f arcMeasure := hf.integrable le_top
  have hz' : ‖z‖ < 1 := by simpa [unitDisc] using hz
  set M : ℝ := (eLpNorm f ⊤ arcMeasure).toReal with hM
  have hMnn : 0 ≤ M := ENNReal.toReal_nonneg
  have hMtop : eLpNorm f ⊤ arcMeasure ≠ ⊤ := hf.eLpNorm_ne_top
  have hae : ∀ᵐ ζ ∂arcMeasure, ‖f ζ‖ ≤ M := by
    filter_upwards [enorm_ae_le_eLpNormEssSup f arcMeasure] with ζ hζ
    have hζ' : ‖f ζ‖ₑ ≤ eLpNorm f ⊤ arcMeasure := by
      rw [eLpNorm_exponent_top]
      · exact hζ
      · exact hf.aestronglyMeasurable
    have := ENNReal.toReal_mono hMtop hζ'
    simpa using this
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) (2 * π))), ‖f (circleMap 0 1 θ)‖ ≤ M :=
    MeasureTheory.ae_of_ae_map (continuous_circleMap 0 1).measurable.aemeasurable hae
  -- the integrands
  set g : ℝ → ℂ := fun t => circleMap 0 1 t * (f (circleMap 0 1 t) : ℂ) / (circleMap 0 1 t - z) ^ 2 with hg
  set K : ℝ → ℝ := fun t => 1 / (π * ‖circleMap 0 1 t - z‖ ^ 2) with hK
  have hgper : Function.Periodic g (2 * π) := fun t => by simp only [hg, periodic_circleMap 0 1 t]
  have hKper : Function.Periodic K (2 * π) := fun t => by simp only [hK, periodic_circleMap 0 1 t]
  have hs1 := hgper.intervalIntegral_add_eq (-π) 0
  have hs2 := hKper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at hs1 hs2
  rw [hs1, hs2]
  have hzs : z ∉ sphere (0 : ℂ) |(1 : ℝ)| := by
    simp only [abs_one, mem_sphere_iff_norm, sub_zero]
    exact hz'.ne
  have hφ : ContinuousOn (fun ζ : ℂ => ζ / (ζ - z) ^ 2) (sphere (0 : ℂ) |(1 : ℝ)|) := by
    refine ContinuousOn.div continuousOn_id (by fun_prop) (fun ζ hζ => ?_)
    have : ζ - z ≠ 0 := fun h => hzs (by rw [← sub_eq_zero.1 h]; exact hζ)
    exact pow_ne_zero 2 this
  have hcf : CircleIntegrable (fun ζ => (f ζ : ℂ)) 0 1 := by
    have hcirc := gm23_circleIntegrable hfi
    simp only [CircleIntegrable, intervalIntegrable_iff] at hcirc ⊢
    exact Complex.ofRealCLM.integrable_comp hcirc
  have hgi : IntervalIntegrable g MeasureTheory.volume 0 (2 * π) := by
    have h := hcf.continuousOn_smul hφ
    have h' : IntervalIntegrable (fun θ : ℝ => (circleMap 0 1 θ / (circleMap 0 1 θ - z) ^ 2) •
        (f (circleMap 0 1 θ) : ℂ)) MeasureTheory.volume 0 (2 * π) := h
    have hg2 : g = fun θ : ℝ => (circleMap 0 1 θ / (circleMap 0 1 θ - z) ^ 2) • (f (circleMap 0 1 θ) : ℂ) := by
      funext t
      simp only [hg, smul_eq_mul]
      ring
    rw [hg2]
    exact h'
  have hne : ∀ t : ℝ, 0 < ‖circleMap 0 1 t - z‖ := fun t => by
    apply norm_pos_iff.2
    intro h0
    have : ‖z‖ = 1 := by
      have := congrArg norm (sub_eq_zero.1 h0)
      simpa using this.symm
    linarith
  have hBc : Continuous fun t : ℝ => M * (1 / ‖circleMap 0 1 t - z‖ ^ 2) :=
    continuous_const.mul (continuous_const.div ((((continuous_circleMap 0 1).sub continuous_const).norm).pow 2)
      (fun t => pow_ne_zero 2 (hne t).ne'))
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have h1 : ‖∫ t in (0 : ℝ)..2 * π, g t‖ ≤ ∫ t in (0 : ℝ)..2 * π, ‖g t‖ :=
    intervalIntegral.norm_integral_le_integral_norm h2π
  have h2 : ∫ t in (0 : ℝ)..2 * π, ‖g t‖ ≤ ∫ t in (0 : ℝ)..2 * π, M * (1 / ‖circleMap 0 1 t - z‖ ^ 2) := by
    rw [intervalIntegral.integral_of_le h2π, intervalIntegral.integral_of_le h2π]
    refine MeasureTheory.integral_mono_ae ?_ ?_ ?_
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).1 hgi.norm
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).1 (hBc.intervalIntegrable _ _)
    · filter_upwards [haeθ] with t ht
      have hn : ‖g t‖ = ‖f (circleMap 0 1 t)‖ / ‖circleMap 0 1 t - z‖ ^ 2 := by
        simp [hg]
      rw [hn, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right ht (by positivity)
  have h3 : ∫ t in (0 : ℝ)..2 * π, M * (1 / ‖circleMap 0 1 t - z‖ ^ 2) =
      M * ∫ t in (0 : ℝ)..2 * π, 1 / ‖circleMap 0 1 t - z‖ ^ 2 := intervalIntegral.integral_const_mul _ _
  have hKs : ∫ t in (0 : ℝ)..2 * π, K t = π⁻¹ * ∫ t in (0 : ℝ)..2 * π, 1 / ‖circleMap 0 1 t - z‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only [hK]
    rw [one_div, one_div, mul_inv]
  have hnorm : ‖(∫ t in (0 : ℝ)..2 * π, g t) / (π : ℂ)‖ = ‖∫ t in (0 : ℝ)..2 * π, g t‖ / π := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [hnorm, hKs]
  have hpi : 0 < π := Real.pi_pos
  rw [div_le_iff₀ hpi]
  calc ‖∫ t in (0 : ℝ)..2 * π, g t‖ ≤ M * ∫ t in (0 : ℝ)..2 * π, 1 / ‖circleMap 0 1 t - z‖ ^ 2 := by
        rw [← h3]; exact h1.trans h2
    _ = π⁻¹ * (∫ t in (0 : ℝ)..2 * π, 1 / ‖circleMap 0 1 t - z‖ ^ 2) * M * π := by
        field_simp

/-- Helper (Ch. II §3). Gradient estimate at the centre of a disc: a real function harmonic on a neighbourhood of the
closed disc `B̄(c, r)` and bounded by `M` there satisfies `|∇u(c)| ≤ 2M/r`. -/
theorem gm23_gradient_ball {u : ℂ → ℝ} {c : ℂ} {r M : ℝ} (hr : 0 < r) (hu : HarmonicOnNhd u (closedBall c r))
    (hM : ∀ x ∈ closedBall c r, |u x| ≤ M) : ‖fderiv ℝ u c‖ ≤ 2 * M / r := by
  set U : ℂ → ℝ := fun x => u (c + x) with hU
  have hmemc : ∀ x ∈ closedBall (0 : ℂ) r, c + x ∈ closedBall c r := fun x hx => by
    rw [mem_closedBall_zero_iff] at hx
    rw [mem_closedBall, dist_eq_norm]
    simpa using hx
  have hUh : HarmonicOnNhd U (closedBall 0 r) := fun x hx => gm23_harmonicAt_translate (hu (c + x) (hmemc x hx))
  have hUM : ∀ x ∈ closedBall (0 : ℂ) r, |U x| ≤ M := fun x hx => hM _ (hmemc x hx)
  have hUcont : ContinuousOn U (closedBall 0 r) := hUh.continuousOn
  have hcirc : CircleIntegrable (fun ζ => (U ζ : ℂ)) 0 r :=
    ContinuousOn.circleIntegrable hr.le
      ((Complex.continuous_ofReal.comp_continuousOn (hUcont.mono sphere_subset_closedBall)))
  have hcircR : CircleIntegrable U 0 r := ContinuousOn.circleIntegrable hr.le (hUcont.mono sphere_subset_closedBall)
  have hz0 : (0 : ℂ) ∉ sphere (0 : ℂ) |r| := by
    simpa [abs_of_pos hr] using hr.ne
  have hd := hasDerivAt_circleAverage_herglotzRieszKernel_smul hcirc hz0
  have hev : U =ᶠ[𝓝 (0 : ℂ)] fun w => (Real.circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • (U ζ : ℂ)) 0 r).re := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with w hw
    have hws : w ∉ sphere (0 : ℂ) |r| := by
      rw [mem_ball_zero_iff] at hw
      simp only [mem_sphere_iff_norm, sub_zero, abs_of_pos hr]
      exact hw.ne
    rw [re_circleAverage_herglotzRieszKernel_smul hcircR hws]
    exact (hUh.circleAverage_re_herglotzRieszKernel_smul hw).symm
  have hnorm := gm23_norm_fderiv_re hd hev
  have htr : fderiv ℝ U 0 = fderiv ℝ u c := by
    simp only [hU]
    rw [fderiv_comp_add_left]
    simp
  rw [← htr, hnorm]
  have hker : ContinuousOn (fun ζ : ℂ => 2 * ζ / (ζ - 0) ^ 2) (sphere (0 : ℂ) |r|) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun ζ hζ => ?_)
    have : ζ ≠ 0 := by
      intro h0
      rw [h0] at hζ
      exact hz0 hζ
    simpa using this
  refine (Real.norm_circleAverage_le_circleAverage_norm).trans ?_
  refine Real.circleAverage_mono_on_of_le_circle (a := 2 * M / r) (hcirc.continuousOn_smul hker).norm
    (fun x hx => ?_)
  have hxr : ‖x‖ = r := by
    rw [mem_sphere_iff_norm, sub_zero, abs_of_pos hr] at hx
    exact hx
  have hxc : x ∈ closedBall (0 : ℂ) r := sphere_subset_closedBall (by simpa [abs_of_pos hr] using hx)
  have hUx := hUM x hxc
  have hrpos := hr
  simp only [norm_smul, norm_div, norm_mul, norm_pow, sub_zero, hxr, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  calc 2 * r / r ^ 2 * |U x| ≤ 2 * r / r ^ 2 * M := by
        apply mul_le_mul_of_nonneg_left hUx (by positivity)
    _ = 2 * M / r := by field_simp

/-- **Formula (3.3)** (Ch. II §3, P1:2394–2402; cited at P1:2404, 2410, 2468). In the Poisson integral formula
`u(z) = Re ∫_{−π}^{π} ((e^{it} + z)/(e^{it} − z)) f(t) dt/2π` the kernel is analytic in `z ∈ 𝔻` and real at `z = 0`;
the uniqueness of `ũ` then shows (3.3) `u(z) + iũ(z) = F(z) = ∫_{−π}^{π} ((e^{it} + z)/(e^{it} − z)) f(t) dt/2π`.
Modelling: for real `f ∈ L¹(∂𝔻)` and `z ∈ 𝔻`. -/
theorem eq2_3_3 {f : ℂ → ℝ} (hf : Integrable f arcMeasure) {z : ℂ} (hz : z ∈ unitDisc) :
    ((poissonIntegral f z : ℝ) : ℂ) + (conjugateFunction f z : ℂ) * I = herglotzIntegral f z := by
  have hS : {r : ℝ | ∃ v : ℂ → ℝ, HarmonicOnNhd v unitDisc ∧ v 0 = 0 ∧
      AnalyticOnNhd ℂ (fun w => ((poissonIntegral f w : ℝ) : ℂ) + (v w : ℂ) * I) unitDisc ∧ v z = r} =
      {(herglotzIntegral f z).im} := by
    ext r
    constructor
    · rintro ⟨v, hv, hv0, hva, rfl⟩
      exact gm23_conjugate_unique hf hv hv0 hva hz
    · intro hr
      rw [Set.mem_singleton_iff] at hr
      subst hr
      obtain ⟨hF, hH, h0⟩ := gm23_herglotz_analytic hf
      refine ⟨fun w => (herglotzIntegral f w).im, hH, h0, ?_, rfl⟩
      refine hF.congr isOpen_ball (fun w hw => ?_)
      show herglotzIntegral f w = ((poissonIntegral f w : ℝ) : ℂ) + ((herglotzIntegral f w).im : ℂ) * I
      rw [gm23_poissonIntegral_eq_re hf hw, Complex.re_add_im]
  have hcj : conjugateFunction f z = (herglotzIntegral f z).im := by
    unfold conjugateFunction
    rw [hS, csSup_singleton]
  rw [hcj, gm23_poissonIntegral_eq_re hf hz, Complex.re_add_im]

/-- **Formula (3.4)** (Ch. II §3, P1:2410–2416; cited at P1:2472 and in VII, P2:1878 "(II.3.4)"). If `u` is harmonic
and bounded on `𝔻`, then `u` is the Poisson integral of some `f ∈ L^∞(∂𝔻)` and by (3.3) and the Cauchy–Riemann
equations, (3.4) `|∇u(z)| = |F'(z)| = |∫_{−π}^{π} e^{it} f(t)/(e^{it} − z)² dt/π|`.
Modelling: stated for `u` the Poisson integral of a real `f ∈ L^∞(∂𝔻)` (that every bounded harmonic `u` is one is
Corollary I.2.5, `cor1_2_5`) and `z ∈ 𝔻`; `F` is the Herglotz integral of `f`. The formula was checked against the
equation image. -/
theorem eq2_3_4 {f : ℂ → ℝ} (hf : MemLp f ⊤ arcMeasure) {z : ℂ} (hz : z ∈ unitDisc) :
    ‖fderiv ℝ (poissonIntegral f) z‖ = ‖deriv (herglotzIntegral f) z‖ ∧
      ‖deriv (herglotzIntegral f) z‖ =
        ‖(∫ t in (-π)..π, circleMap 0 1 t * (f (circleMap 0 1 t) : ℂ) / (circleMap 0 1 t - z) ^ 2) / π‖ := by
  have := gm23_isFiniteMeasure_arcMeasure
  have hfi : Integrable f arcMeasure := hf.integrable le_top
  have hF := (gm23_herglotz_analytic hfi).1
  have hFz : HasDerivAt (herglotzIntegral f) (deriv (herglotzIntegral f) z) z :=
    (hF z hz).differentiableAt.hasDerivAt
  have hev : poissonIntegral f =ᶠ[𝓝 z] fun w => (herglotzIntegral f w).re := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw using gm23_poissonIntegral_eq_re hfi hw
  set L0 : ℂ →L[ℝ] ℂ :=
    (ContinuousLinearMap.toSpanSingleton ℂ (deriv (herglotzIntegral f) z)).restrictScalars ℝ with hL0
  have hFD : HasFDerivAt (fun w => (herglotzIntegral f w).re) (Complex.reCLM.comp L0) z :=
    Complex.reCLM.hasFDerivAt.comp z (hFz.hasFDerivAt.restrictScalars ℝ)
  have hfd : fderiv ℝ (poissonIntegral f) z = Complex.reCLM.comp L0 :=
    (hFD.congr_of_eventuallyEq hev).fderiv
  have hnorm : ‖fderiv ℝ (poissonIntegral f) z‖ = ‖deriv (herglotzIntegral f) z‖ := by
    rw [hfd]
    exact gm23_norm_re_mul _ _ (fun w => by simp [hL0, mul_comm])
  refine ⟨hnorm, ?_⟩
  rw [gm23_deriv_herglotz hfi hz]

/-- **Formula (3.5)** (Ch. II §3, P1:2418–2422; cited at P1:2226, 2424–2432, 2472 and in VII, P2:1878 "(II.3.5)").
Therefore `|∇u(z)| ≤ (∫_{−π}^{π} dt/(π |e^{it} − z|²)) ‖f‖_∞ ≤ 2(1 − |z|)⁻¹ ‖f‖_∞`.
Modelling: for `u` the Poisson integral of a real `f ∈ L^∞(∂𝔻)` and `z ∈ 𝔻`; `‖f‖_∞` is the (finite) essential
supremum as a real number. The constant `2` was checked against the equation image. -/
theorem eq2_3_5 {f : ℂ → ℝ} (hf : MemLp f ⊤ arcMeasure) {z : ℂ} (hz : z ∈ unitDisc) :
    ‖fderiv ℝ (poissonIntegral f) z‖ ≤
        (∫ t in (-π)..π, 1 / (π * ‖circleMap 0 1 t - z‖ ^ 2)) * (eLpNorm f ⊤ arcMeasure).toReal ∧
      (∫ t in (-π)..π, 1 / (π * ‖circleMap 0 1 t - z‖ ^ 2)) * (eLpNorm f ⊤ arcMeasure).toReal ≤
        2 * (1 - ‖z‖)⁻¹ * (eLpNorm f ⊤ arcMeasure).toReal := by
  have h4 := eq2_3_4 hf hz
  have hz1 : ‖z‖ < 1 := by simpa [unitDisc] using hz
  have hN : 0 ≤ (eLpNorm f ⊤ arcMeasure).toReal := ENNReal.toReal_nonneg
  have hmain := gm23_integral_bound hf hz
  refine ⟨?_, ?_⟩
  · calc ‖fderiv ℝ (poissonIntegral f) z‖ = ‖deriv (herglotzIntegral f) z‖ := h4.1
      _ = _ := h4.2
      _ ≤ _ := hmain
  · rw [gm23_poisson_total hz]
    have h1 : 0 < 1 - ‖z‖ := by linarith
    have h2 : 1 - ‖z‖ ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have h3 : 2 / (1 - ‖z‖ ^ 2) ≤ 2 * (1 - ‖z‖)⁻¹ := by
      rw [← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (by norm_num) h1 h2
    exact mul_le_mul_of_nonneg_right h3 hN

/-- **Formula (3.6)** (Ch. II §3, P1:2424–2430; "we will often use", cited at P1:2585, 2643). If `u(z)` is harmonic
and `|u(z)| ≤ M` on `B(z, R)`, then (3.6) `sup_{B(z, R/2)} |∇u| ≤ 4M/R`.
Modelling: `u` real-valued and harmonic on the open disc `B(z, R)`; the bound at every point of `B(z, R/2)`. The
constant `4` was checked against the equation image. -/
theorem eq2_3_6 {u : ℂ → ℝ} {z : ℂ} {R M : ℝ} (hu : HarmonicOnNhd u (ball z R)) (hM : ∀ w ∈ ball z R, |u w| ≤ M) :
    ∀ w ∈ ball z (R / 2), ‖fderiv ℝ u w‖ ≤ 4 * M / R := by
  intro w hw
  have hR : 0 < R := by
    have := mem_ball.1 hw
    have := dist_nonneg (x := w) (y := z)
    linarith
  have hsub : closedBall w (R / 2) ⊆ ball z R := by
    intro x hx
    rw [mem_ball] at hw ⊢
    have h1 := mem_closedBall.1 hx
    have := dist_triangle x w z
    linarith
  have h := gm23_gradient_ball (u := u) (c := w) (r := R / 2) (M := M) (by linarith) (hu.mono hsub)
    (fun x hx => hM x (hsub hx))
  calc ‖fderiv ℝ u w‖ ≤ 2 * M / (R / 2) := h
    _ = 4 * M / R := by field_simp; ring

/-- **Theorem 3.2** (Ch. II §3; cited at P1:2557, 2559, 2621, 2882 and in VII, P2:2072). Let `0 < α < 1`, let
`f ∈ L^∞(∂𝔻)` be real, and let `u(z)` be the Poisson integral of `f`. Then the following conditions are equivalent:
(a) `f ∈ C^α`; (b) `f̃ ∈ C^α`; (c) `|∇u(z)| = O((1 − |z|)^{α−1})`; (d) `u ∈ C^α(𝔻̄)`, that is, for all
`z₁, z₂ ∈ 𝔻`, `|u(z₁) − u(z₂)| = O(|z₁ − z₂|^α)`.
Modelling: the `O`-bounds are global bounds on `𝔻`; (b) reads `f̃` through essential suprema, so the null set where
`f̃` is junk is not seen. The equivalence (a) ⇔ (b) is Privalov's theorem (P1:2392, 2468; not the Privalov theorem
of VI.2). -/
theorem thm2_3_2 {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) {f : ℂ → ℝ} (hf : MemLp f ⊤ arcMeasure) :
    List.TFAE [MemLipschitzClass α f, MemLipschitzClass α (boundaryConjugate f),
      ∃ C : ℝ, ∀ z ∈ unitDisc, ‖fderiv ℝ (poissonIntegral f) z‖ ≤ C * (1 - ‖z‖) ^ (α - 1),
      ∃ C : ℝ, ∀ z₁ ∈ unitDisc, ∀ z₂ ∈ unitDisc,
        |poissonIntegral f z₁ - poissonIntegral f z₂| ≤ C * ‖z₁ - z₂‖ ^ α] := by
  sorry

/-- **Theorem 3.2** (Ch. II §3), the estimates. Moreover there is a constant `C₁`, independent of `α`, such that
(3.7) `‖f̃‖_{C^α} ≤ C₁/(α(1 − α)) ‖f‖_{C^α}`, (3.8) `|∇u(z)| ≤ C₁/(1 − α) (1 − |z|)^{α−1} ‖f‖_{C^α}`, and (3.9)
`sup_{z₁≠z₂} |u(z₁) − u(z₂)|/|z₁ − z₂|^α ≤ (C₁/α) sup_{|z|<1} {(1 − |z|)^{1−α} |∇u(z)|}`.
Modelling: `∃ C₁, ∀ α ∈ (0, 1), ∀ f` (the constant is absolute); `f ∈ L^∞(∂𝔻)` real and `u` its Poisson integral;
all three inequalities in `[0, ∞]` (they hold trivially when the right side is infinite); (3.8) at every `z ∈ 𝔻`. The
constants `C₁/(α(1 − α))`, `C₁/(1 − α)`, `C₁/α` were checked against the equation images. -/
theorem thm2_3_2_bounds :
    ∃ C₁ : ℝ, ∀ α : ℝ, 0 < α → α < 1 → ∀ f : ℂ → ℝ, MemLp f ⊤ arcMeasure →
      lipschitzClassNorm α (boundaryConjugate f) ≤
          ENNReal.ofReal (C₁ / (α * (1 - α))) * lipschitzClassNorm α f ∧
        (∀ z ∈ unitDisc, ENNReal.ofReal ‖fderiv ℝ (poissonIntegral f) z‖ ≤
          ENNReal.ofReal (C₁ / (1 - α) * (1 - ‖z‖) ^ (α - 1)) * lipschitzClassNorm α f) ∧
        (⨆ (z₁ : ℂ) (_ : z₁ ∈ unitDisc) (z₂ : ℂ) (_ : z₂ ∈ unitDisc) (_ : z₁ ≠ z₂),
            ENNReal.ofReal (|poissonIntegral f z₁ - poissonIntegral f z₂| / ‖z₁ - z₂‖ ^ α)) ≤
          ENNReal.ofReal (C₁ / α) *
            ⨆ z ∈ unitDisc, ENNReal.ofReal ((1 - ‖z‖) ^ (1 - α) * ‖fderiv ℝ (poissonIntegral f) z‖) := by
  sorry

/-- **Definition** (the class `C^{k+α}(∂𝔻)`, Ch. II §3, P1:2527). Let `k` be a non-negative integer, `0 ≤ α < 1` and
`f ∈ C(∂𝔻)`. We say `f ∈ C^{k+α}` if `f` is `k` times continuously differentiable on `∂𝔻` and `(d/dθ)^k f ∈ C^α` if
`α > 0`.
Modelling: differentiability in `θ`: `θ ↦ f(e^{iθ})` is `C^k` on `ℝ` (this contains `f ∈ C(∂𝔻)`), and its `k`-th
derivative, read as the function `e^{iθ} ↦ (d/dθ)^k f(e^{iθ})` on `∂𝔻` (through `arg`), is in `C^α` when `α > 0`. -/
def MemCkAlphaCircle {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ) (α : ℝ) (f : ℂ → V) : Prop :=
  ContDiff ℝ k (fun θ : ℝ => f (circleMap 0 1 θ)) ∧
    (0 < α → MemLipschitzClass α fun ζ : ℂ => iteratedDeriv k (fun θ : ℝ => f (circleMap 0 1 θ)) (arg ζ))

/-- **Definition** (the class `C^{k+α}(𝔻̄)`, Ch. II §3, P1:2527–2533). If `F(z)` is analytic on `𝔻`, we say
`F ∈ C^{k+α}(𝔻̄)` if `F` and its first `k` derivatives `F', F'', …, F^{(k)}` extend continuously to `𝔻̄` and if there
is `C` such that `|F^{(k)}(z₁) − F^{(k)}(z₂)| ≤ C |z₁ − z₂|^α` for all `z₁, z₂ ∈ 𝔻̄`.
Modelling: the Hölder bound is for the continuous extension of `F^{(k)}` to `𝔻̄`. -/
def MemCkAlphaClosedDisc (k : ℕ) (α : ℝ) (F : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ F unitDisc ∧
    (∀ j ≤ k, ∃ G : ℂ → ℂ, ContinuousOn G (closedBall 0 1) ∧ EqOn G (iteratedDeriv j F) unitDisc) ∧
    ∃ G : ℂ → ℂ, ContinuousOn G (closedBall 0 1) ∧ EqOn G (iteratedDeriv k F) unitDisc ∧
      ∃ C : ℝ, ∀ z₁ ∈ closedBall (0 : ℂ) 1, ∀ z₂ ∈ closedBall (0 : ℂ) 1, ‖G z₁ - G z₂‖ ≤ C * ‖z₁ - z₂‖ ^ α

/-- **Corollary 3.3** (Ch. II §3; cited at P1:2565, 2854, 2868, 2882, 2888). Assume `k` is a non-negative integer and
assume `0 < α < 1`. Let `f ∈ C(∂𝔻)` be real and let `F(z) = u(z) + iũ(z)` be the Herglotz integral of `f`. Then
`F ∈ C^{k+α}(𝔻̄)` if and only if `f ∈ C^{k+α}(∂𝔻)`. -/
theorem cor2_3_3 (k : ℕ) {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) {f : ℂ → ℝ} (hf : ContinuousOn f (sphere 0 1)) :
    MemCkAlphaClosedDisc k α (herglotzIntegral f) ↔ MemCkAlphaCircle k α f := by
  sorry

/-- **Definition** (the Zygmund class `Z*`, Zygmund functions, Ch. II §3, P1:2565–2569, 2577). The Zygmund class
`Z*` of continuous `f` on `∂𝔻` such that `sup_{t>0} ‖f(θ + t) + f(θ − t) − 2f(θ)‖_∞ / t < ∞`. When `f ∈ Z*`, we
say `f` is a Zygmund function.
Modelling: `f(θ ± t)` is `f(e^{±it} ζ)` for `ζ = e^{iθ}`; the supremum is finite when there is a bound `C t` for all
`t > 0`; values in any normed space (later chapters apply the class to complex boundary values). -/
def MemZygmund {V : Type*} [NormedAddCommGroup V] (f : ℂ → V) : Prop :=
  ContinuousOn f (sphere 0 1) ∧ ∃ C : ℝ, ∀ t : ℝ, 0 < t →
    eLpNorm (fun ζ => f (Complex.exp (t * I) * ζ) + f (Complex.exp (-(t * I)) * ζ) - (2 : ℕ) • f ζ) ⊤ arcMeasure ≤
      ENNReal.ofReal (C * t)

/-- **Definition** (the Zygmund norm, Ch. II §3, P1:2571–2575).
`‖f‖_{Z*} = ‖f‖_∞ + sup_{t>0} ‖f(θ + t) + f(θ − t) − 2f(θ)‖_∞ / t`, with values in `[0, ∞]`. -/
def zygmundNorm {V : Type*} [NormedAddCommGroup V] (f : ℂ → V) : ℝ≥0∞ :=
  eLpNorm f ⊤ arcMeasure + ⨆ (t : ℝ) (_ : 0 < t),
    eLpNorm (fun ζ => f (Complex.exp (t * I) * ζ) + f (Complex.exp (-(t * I)) * ζ) - (2 : ℕ) • f ζ) ⊤ arcMeasure /
      ENNReal.ofReal t

/-- **Definition** (`|∇₂u(z)|`, Ch. II §3, P1:2579–2585). `|∇₂u(z)| = |∇u_x| = (|u_xx(z)|² + |u_yx(z)|²)^{1/2}`
(which the book notes equals `|F''(z)|` for the Herglotz integral `F` of `f`).
Modelling: the norm of the real derivative at `z` of `u_x = ∂u/∂x` (the derivative of `u` in the direction `1`). -/
def grad2Norm (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  ‖fderiv ℝ (fun w => fderiv ℝ u w 1) z‖

/-- **Formula (3.10)** (Ch. II §3, P1:2585–2591; cited at P1:2591, 2613, 2657), with its converse. If `f ∈ C^α`, then
(3.8) and (3.6), applied to `u_x` in the disc `B(z, (1 − |z|)/2)`, give (3.10) `|∇₂u(z)| = O((1 − |z|)^{α−2})`.
Conversely, if (3.10) holds, then integrating `F''` along radii shows that `|∇u(z)| = O((1 − |z|)^{α−1})`, and
`f ∈ C^α`.
Modelling: `f ∈ L¹(∂𝔻)` real (the setting of the definition of `∇₂u`, P1:2585), `0 < α < 1`, `u` the Poisson integral
of `f`; the `O`-bound is global on `𝔻`. -/
theorem eq2_3_10 {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) {f : ℂ → ℝ} (hf : Integrable f arcMeasure) :
    MemLipschitzClass α f ↔
      ∃ C : ℝ, ∀ z ∈ unitDisc, grad2Norm (poissonIntegral f) z ≤ C * (1 - ‖z‖) ^ (α - 2) := by
  sorry

/-- **Theorem 3.4** (Ch. II §3; cited in VII, P2:1952, and in App. J, P3:5336, where it is printed "Theorem II.3.3"
[misprint]; App. J's second "Theorem II.3.3", P3:5342, is the `Z*`-scale claim after it). Let `f ∈ L^∞(∂𝔻)` be
real and let `u(z)` be the Poisson integral of `f`. Then the following are equivalent:
(a) `f ∈ Z*`; (b) `f̃ ∈ Z*`; (c) `|∇₂u(z)| = O((1 − |z|)^{−1})`.
Modelling: `Z*` is a class of continuous functions, so for `f ∈ L^∞` (a) and (b) mean that `f`, resp. `f̃`, agrees
almost everywhere with a member of `Z*`; the `O`-bound is global on `𝔻`. -/
theorem thm2_3_4 {f : ℂ → ℝ} (hf : MemLp f ⊤ arcMeasure) :
    List.TFAE [∃ g : ℂ → ℝ, MemZygmund g ∧ f =ᵐ[arcMeasure] g,
      ∃ g : ℂ → ℝ, MemZygmund g ∧ boundaryConjugate f =ᵐ[arcMeasure] g,
      ∃ C : ℝ, ∀ z ∈ unitDisc, grad2Norm (poissonIntegral f) z ≤ C * (1 - ‖z‖)⁻¹] := by
  sorry

/-- **Theorem 3.4** (Ch. II §3), the estimates. There is a constant `C` such that (3.11) `‖f̃‖_{Z*} ≤ C ‖f‖_{Z*}` and
(3.12) `(1/C) ‖f‖_{Z*} ≤ ‖f‖_∞ + sup_{z∈𝔻} {(1 − |z|) |∇₂u(z)|} ≤ C ‖f‖_{Z*}`.
Modelling: `∃ C > 0, ∀ f` (an absolute constant), `f ∈ L^∞(∂𝔻)` real and `u` its Poisson integral; the norms and the
middle term of (3.12) in `[0, ∞]` (the norms read `f` and `f̃` through essential suprema). -/
theorem thm2_3_4_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℝ, MemLp f ⊤ arcMeasure →
      zygmundNorm (boundaryConjugate f) ≤ ENNReal.ofReal C * zygmundNorm f ∧
        (ENNReal.ofReal C)⁻¹ * zygmundNorm f ≤
          eLpNorm f ⊤ arcMeasure + ⨆ z ∈ unitDisc, ENNReal.ofReal ((1 - ‖z‖) * grad2Norm (poissonIntegral f) z) ∧
        eLpNorm f ⊤ arcMeasure + ⨆ z ∈ unitDisc, ENNReal.ofReal ((1 - ‖z‖) * grad2Norm (poissonIntegral f) z) ≤
          ENNReal.ofReal C * zygmundNorm f := by
  sorry

/-- **Unlabelled** (Ch. II §3, P1:2613–2619; used in App. J, P3:5342, "`Λ*` is an equicontinuous family", cited
there as "Theorem II.3.3"). By (3.12) and (3.10), `Z* ⊆ C^α` for all `α < 1`. In particular, if `f ∈ Z*`, then `f`
and `f̃` are continuous. On the other hand, if `f` is Lipschitz, then clearly `f ∈ Z*`. Thus we have the increasing
scale of spaces `C¹ ⊂ Lipschitz ⊂ Z* ⊂ C^α ⊂ C`, `α < 1`.
Modelling: for real `f` on `∂𝔻`: `f ∈ Z*` gives `f ∈ C^α` for every `α ∈ (0, 1)` (the book's range of `C^α`), and `f̃`
is continuous on `∂𝔻` (`f` is continuous by the definition of `Z*`; `f̃` is the nontangential limit of `ũ` at every
point, since `ũ` is then the Poisson integral of a continuous function); "Lipschitz" is
`|f(θ + t) − f(θ)| ≤ M |t|`, i.e. `LipschitzWith` for `θ ↦ f(e^{iθ})`. The two ends of the scale
(`C¹ ⊂ Lipschitz`, and `C^α ⊂ C` up to null sets, P1:2386) are elementary and not stated. -/
theorem zygmund_subset_lipschitzClass (f : ℂ → ℝ) :
    (MemZygmund f → (∀ α : ℝ, 0 < α → α < 1 → MemLipschitzClass α f) ∧
      ContinuousOn (boundaryConjugate f) (sphere 0 1)) ∧
    ((∃ M : ℝ, ∀ θ t : ℝ, |f (circleMap 0 1 (θ + t)) - f (circleMap 0 1 θ)| ≤ M * |t|) → MemZygmund f) := by
  sorry

/-- Helper (Ch. II §3, dyadic iteration). If `2 ω(s) ≤ ω(2s) + l s` for all `s > 0`, then
`ω(t) ≤ 2⁻ⁿ ω(2ⁿ t) + n l t / 2`. -/
theorem gm23_iter (ω : ℝ → ℝ) (l : ℝ) (hstep : ∀ s : ℝ, 0 < s → 2 * ω s ≤ ω (2 * s) + l * s) {t : ℝ}
    (ht : 0 < t) (n : ℕ) : ω t ≤ (1 / 2 : ℝ) ^ n * ω (2 ^ n * t) + n * l * t / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := hstep (2 ^ n * t) (by positivity)
    have h2 : (2 : ℝ) ^ n * t * 2 = 2 ^ (n + 1) * t := by ring
    have hpow : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by
      rw [← mul_pow]; norm_num
    have hn : (0 : ℝ) < (1 / 2) ^ n := by positivity
    calc ω t ≤ (1 / 2 : ℝ) ^ n * ω (2 ^ n * t) + n * l * t / 2 := ih
      _ ≤ (1 / 2 : ℝ) ^ n * ((ω (2 * (2 ^ n * t)) + l * (2 ^ n * t)) / 2) + n * l * t / 2 := by
          gcongr
          linarith
      _ = (1 / 2 : ℝ) ^ (n + 1) * ω (2 ^ (n + 1) * t) + ((n + 1 : ℕ) : ℝ) * l * t / 2 := by
          have e1 : 2 * (2 ^ n * t) = 2 ^ (n + 1) * t := by ring
          rw [e1, pow_succ (1 / 2 : ℝ) n]
          push_cast
          have : (1 / 2 : ℝ) ^ n * (l * (2 ^ n * t)) = l * t := by
            calc (1 / 2 : ℝ) ^ n * (l * (2 ^ n * t)) = ((1 / 2 : ℝ) ^ n * 2 ^ n) * (l * t) := by ring
              _ = l * t := by rw [hpow, one_mul]
          nlinarith [this]

/-- Helper (Ch. II §3, `Z* ⊆ C^α`). Real form of the dyadic estimate. -/
theorem gm23_dyadic_real {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ω : ℝ → ℝ) (a l : ℝ), 0 ≤ a → 0 ≤ l → (∀ t : ℝ, 0 < t → 0 ≤ ω t ∧ ω t ≤ 2 * a) →
      (∀ s : ℝ, 0 < s → 2 * ω s ≤ ω (2 * s) + l * s) → ∀ t : ℝ, 0 < t → ω t ≤ C * (a + l) * t ^ α := by
  have hβ : 0 < 1 - α := by linarith
  have hk : 0 ≤ 1 / (1 - α) := by positivity
  refine ⟨2 + 1 / (1 - α), by positivity, ?_⟩
  intro ω a l ha hl hω hstep t ht
  have htα : 0 < t ^ α := Real.rpow_pos_of_pos ht α
  by_cases ht1 : 1 ≤ t
  · have h1 : 1 ≤ t ^ α := Real.one_le_rpow ht1 hα₀.le
    calc ω t ≤ 2 * a := (hω t ht).2
      _ ≤ (2 + 1 / (1 - α)) * (a + l) := by nlinarith [mul_nonneg hk ha, mul_nonneg hk hl]
      _ ≤ (2 + 1 / (1 - α)) * (a + l) * t ^ α := le_mul_of_one_le_right (by positivity) h1
  · have ht1' : t < 1 := not_le.1 ht1
    set n : ℕ := ⌈Real.logb 2 (1 / t)⌉₊ with hn
    have hinv : 1 ≤ 1 / t := by rw [le_div_iff₀ ht]; linarith
    have hlogb0 : 0 ≤ Real.logb 2 (1 / t) := Real.logb_nonneg (by norm_num) hinv
    have h2n : 1 / t ≤ (2 : ℝ) ^ n := by
      have h1 : Real.logb 2 (1 / t) ≤ n := Nat.le_ceil _
      calc 1 / t = (2 : ℝ) ^ (Real.logb 2 (1 / t)) :=
            (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
        _ ≤ (2 : ℝ) ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
        _ = (2 : ℝ) ^ n := Real.rpow_natCast 2 n
    have h12 : (1 / 2 : ℝ) ^ n ≤ t := by
      rw [one_div, inv_pow, inv_le_comm₀ (by positivity) ht, ← one_div]
      exact h2n
    have hnlt : (n : ℝ) < Real.logb 2 (1 / t) + 1 := Nat.ceil_lt_add_one hlogb0
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hlogt : 0 ≤ Real.log (1 / t) := Real.log_nonneg hinv
    have hlogb : Real.logb 2 (1 / t) ≤ 2 * Real.log (1 / t) := by
      rw [Real.logb]
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hlogle : Real.log (1 / t) ≤ (1 / t) ^ (1 - α) / (1 - α) :=
      Real.log_le_rpow_div (by positivity) hβ
    have hpow : t * (1 / t) ^ (1 - α) = t ^ α := by
      calc t * (1 / t) ^ (1 - α) = t / t ^ (1 - α) := by
            rw [one_div, Real.inv_rpow ht.le, div_eq_mul_inv]
        _ = t ^ (1 - (1 - α)) := by rw [Real.rpow_sub ht 1 (1 - α), Real.rpow_one]
        _ = t ^ α := by congr 1; ring
    set X : ℝ := (1 / t) ^ (1 - α) with hX
    have hX0 : 0 ≤ X := by positivity
    have hnle : (n : ℝ) ≤ 2 * (1 / (1 - α)) * X + 1 := by
      have h1 : Real.log (1 / t) ≤ 1 / (1 - α) * X := by
        calc Real.log (1 / t) ≤ X / (1 - α) := hlogle
          _ = 1 / (1 - α) * X := by ring
      linarith
    have hωn : ω (2 ^ n * t) ≤ 2 * a := (hω _ (by positivity)).2
    have hωn0 : 0 ≤ ω (2 ^ n * t) := (hω _ (by positivity)).1
    have hmain := gm23_iter ω l hstep ht n
    have htle : t ≤ t ^ α := by
      have := Real.rpow_le_rpow_of_exponent_ge ht ht1'.le hα₁.le
      simpa using this
    have hA : (1 / 2 : ℝ) ^ n * ω (2 ^ n * t) ≤ t * (2 * a) :=
      mul_le_mul h12 hωn hωn0 ht.le
    have hB : (n : ℝ) * l * t / 2 ≤ (2 * (1 / (1 - α)) * X + 1) * l * t / 2 := by
      have : 0 ≤ l * t / 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hnle this]
    have hC : (2 * (1 / (1 - α)) * X + 1) * l * t / 2 = 1 / (1 - α) * l * t ^ α + l * t / 2 := by
      rw [← hpow]
      ring
    have hD : l * t / 2 ≤ l * t ^ α / 2 := by
      have := mul_le_mul_of_nonneg_left htle hl
      linarith
    have hE : t * (2 * a) ≤ 2 * a * t ^ α := by nlinarith [mul_le_mul_of_nonneg_left htle ha]
    have hk' : 0 ≤ 1 / (1 - α) * l * t ^ α := by positivity
    calc ω t ≤ (1 / 2 : ℝ) ^ n * ω (2 ^ n * t) + n * l * t / 2 := hmain
      _ ≤ t * (2 * a) + (1 / (1 - α) * l * t ^ α + l * t / 2) := by linarith [hA, hB, hC]
      _ ≤ 2 * a * t ^ α + (1 / (1 - α) * l * t ^ α + l * t ^ α / 2) := by linarith [hE, hD]
      _ ≤ (2 + 1 / (1 - α)) * (a + l) * t ^ α := by
          have h1 : 0 ≤ 1 / (1 - α) * a * t ^ α := by positivity
          have h2 : 0 ≤ l * t ^ α := by positivity
          nlinarith [h1, h2, hk']

/-- Helper (Ch. II §3, rotation invariance). The arc measure charges every relatively open nonempty subset of the unit
circle. -/
theorem gm23_arcMeasure_pos {V : Set ℂ} (hV : IsOpen V) (hne : (V ∩ sphere (0 : ℂ) 1).Nonempty) :
    0 < arcMeasure (V ∩ sphere (0 : ℂ) 1) := by
  obtain ⟨ζ0, hζ0V, hζ0S⟩ := hne
  have hmeas : MeasurableSet (V ∩ sphere (0 : ℂ) 1) := hV.measurableSet.inter isClosed_sphere.measurableSet
  have hpre : circleMap 0 1 ⁻¹' (V ∩ sphere (0 : ℂ) 1) = circleMap 0 1 ⁻¹' V := by
    ext θ
    simp
  unfold arcMeasure
  rw [Measure.map_apply (continuous_circleMap 0 1).measurable hmeas,
    Measure.restrict_apply ((continuous_circleMap 0 1).measurable hmeas), hpre]
  obtain ⟨θ0, hθ0, hθ0eq⟩ : ζ0 ∈ circleMap 0 1 '' Set.Ioc 0 (2 * π) := by
    rw [image_circleMap_Ioc]
    simpa using hζ0S
  subst hθ0eq
  have hW : IsOpen (circleMap 0 1 ⁻¹' V) := hV.preimage (continuous_circleMap 0 1)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hW θ0 hζ0V
  have hθpos : 0 < θ0 := hθ0.1
  have hsub : Set.Ioo (max 0 (θ0 - δ)) θ0 ⊆ circleMap 0 1 ⁻¹' V ∩ Set.Ioc 0 (2 * π) := by
    intro θ hθ
    refine ⟨hball ?_, ⟨lt_of_le_of_lt (le_max_left _ _) hθ.1, hθ.2.le.trans hθ0.2⟩⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have := lt_of_le_of_lt (le_max_right _ _) hθ.1
    constructor <;> linarith [hθ.2]
  calc 0 < MeasureTheory.volume (Set.Ioo (max 0 (θ0 - δ)) θ0) := by
        rw [Real.volume_Ioo]
        refine ENNReal.ofReal_pos.2 ?_
        have : max 0 (θ0 - δ) < θ0 := max_lt hθpos (by linarith)
        linarith
    _ ≤ _ := MeasureTheory.measure_mono hsub

/-- Helper (Ch. II §3, rotation invariance). For a function continuous on the unit circle the essential supremum with
respect to `arcMeasure` is the supremum over the circle. -/
theorem gm23_eLpNorm_top_eq {g : ℂ → ℝ} (hg : ContinuousOn g (sphere (0 : ℂ) 1)) :
    eLpNorm g ⊤ arcMeasure = ⨆ ζ ∈ sphere (0 : ℂ) 1, ‖g ζ‖ₑ := by
  have hS : ∀ᵐ ζ ∂arcMeasure, ζ ∈ sphere (0 : ℂ) 1 := by
    rw [MeasureTheory.ae_iff]
    have hm : MeasurableSet {ζ : ℂ | ¬ ζ ∈ sphere (0 : ℂ) 1} := isClosed_sphere.measurableSet.compl
    unfold arcMeasure
    rw [Measure.map_apply (continuous_circleMap 0 1).measurable hm]
    have : circleMap 0 1 ⁻¹' {ζ : ℂ | ¬ ζ ∈ sphere (0 : ℂ) 1} = ∅ := by
      ext θ
      simp
    rw [this]
    simp
  have hmeasg : AEStronglyMeasurable g arcMeasure := by
    have := hg.aestronglyMeasurable (μ := arcMeasure) isClosed_sphere.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem hS] at this
  apply le_antisymm
  · rw [eLpNorm_exponent_top]
    · refine essSup_le_of_ae_le _ ?_
      filter_upwards [hS] with ζ hζ
      exact le_iSup₂ (f := fun ζ (_ : ζ ∈ sphere (0 : ℂ) 1) => ‖g ζ‖ₑ) ζ hζ
    · exact hmeasg
  · refine iSup₂_le fun ζ0 hζ0 => ?_
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨c, hc1, hc2⟩ := exists_between hlt
    obtain ⟨V, hVo, hVeq⟩ := (continuousOn_iff'.1 hg.enorm) (Set.Ioi c) isOpen_Ioi
    have hne : (V ∩ sphere (0 : ℂ) 1).Nonempty := ⟨ζ0, by rw [← hVeq]; exact ⟨hc2, hζ0⟩⟩
    have hpos := gm23_arcMeasure_pos hVo hne
    have hae : ∀ᵐ ζ ∂arcMeasure, ‖g ζ‖ₑ ≤ eLpNorm g ⊤ arcMeasure := by
      have := enorm_ae_le_eLpNormEssSup g arcMeasure
      rwa [← eLpNorm_exponent_top hmeasg] at this
    have hzero : arcMeasure (V ∩ sphere (0 : ℂ) 1) = 0 := by
      rw [← hVeq]
      refine MeasureTheory.measure_mono_null (fun ζ hζ => ?_) (MeasureTheory.ae_iff.1 hae)
      intro hle
      exact lt_irrefl _ (hc1.trans (hζ.1.trans_le hle))
    exact hpos.ne' hzero

/-- Helper (Ch. II §3, `Z* ⊆ C^α`). For a Zygmund function `f` (continuous on `∂𝔻`): (a) the modulus of continuity
`ω(t) = ‖f(θ + t) − f(θ)‖_∞` is at most `2‖f‖_∞`; (b) if the second differences satisfy
`‖f(θ + s) + f(θ − s) − 2f(θ)‖_∞ ≤ Λ s` for all `s > 0`, then `2 ω(t) ≤ ω(2t) + Λ t`
(the second difference at `θ + t` with step `t`, and rotation invariance of the essential supremum). -/
theorem gm23_modulus_step {f : ℂ → ℝ} (hf : MemZygmund f) :
    (∀ t : ℝ, 0 < t →
      eLpNorm (fun ζ => f (Complex.exp (t * I) * ζ) - f ζ) ⊤ arcMeasure ≤ 2 * eLpNorm f ⊤ arcMeasure) ∧
    ∀ Λ : ℝ≥0∞, (∀ s : ℝ, 0 < s →
        eLpNorm (fun ζ => f (Complex.exp (s * I) * ζ) + f (Complex.exp (-(s * I)) * ζ) - (2 : ℕ) • f ζ) ⊤
          arcMeasure ≤ Λ * ENNReal.ofReal s) →
      ∀ t : ℝ, 0 < t →
        2 * eLpNorm (fun ζ => f (Complex.exp (t * I) * ζ) - f ζ) ⊤ arcMeasure ≤
          eLpNorm (fun ζ => f (Complex.exp ((2 * t : ℝ) * I) * ζ) - f ζ) ⊤ arcMeasure + Λ * ENNReal.ofReal t := by
  have hfc : ContinuousOn f (sphere (0 : ℂ) 1) := hf.1
  have hnorm : ∀ t : ℝ, ‖Complex.exp (t * I)‖ = 1 := fun t => Complex.norm_exp_ofReal_mul_I t
  have hnorm' : ∀ t : ℝ, ‖Complex.exp (-(t * I))‖ = 1 := fun t => by
    have := Complex.norm_exp_ofReal_mul_I (-t)
    simpa using this
  have hrotS : ∀ c : ℂ, ‖c‖ = 1 → ∀ ζ ∈ sphere (0 : ℂ) 1, c * ζ ∈ sphere (0 : ℂ) 1 := fun c hc ζ hζ => by
    rw [mem_sphere_zero_iff_norm] at hζ ⊢
    rw [norm_mul, hc, hζ, one_mul]
  have hrotc : ∀ c : ℂ, ‖c‖ = 1 → ContinuousOn (fun ζ => f (c * ζ)) (sphere (0 : ℂ) 1) := fun c hc =>
    hfc.comp (continuous_const.mul continuous_id).continuousOn (fun ζ hζ => hrotS c hc ζ hζ)
  have hΔc : ∀ t : ℝ, ContinuousOn (fun ζ => f (Complex.exp (t * I) * ζ) - f ζ) (sphere (0 : ℂ) 1) :=
    fun t => (hrotc _ (hnorm t)).sub hfc
  have hDc : ∀ s : ℝ, ContinuousOn
      (fun ζ => f (Complex.exp (s * I) * ζ) + f (Complex.exp (-(s * I)) * ζ) - (2 : ℕ) • f ζ)
      (sphere (0 : ℂ) 1) := fun s =>
    ((hrotc _ (hnorm s)).add (hrotc _ (hnorm' s))).sub (hfc.const_smul (2 : ℕ) : ContinuousOn (fun ζ => (2 : ℕ) • f ζ) _)
  have hrot1 : ∀ t : ℝ, ∀ ζ ∈ sphere (0 : ℂ) 1, Complex.exp (t * I) * ζ ∈ sphere (0 : ℂ) 1 :=
    fun t ζ hζ => hrotS _ (hnorm t) ζ hζ
  refine ⟨fun t ht => ?_, fun Λ hΛ t ht => ?_⟩
  · rw [gm23_eLpNorm_top_eq (hΔc t), gm23_eLpNorm_top_eq hfc]
    refine iSup₂_le fun ζ hζ => ?_
    calc ‖f (Complex.exp (t * I) * ζ) - f ζ‖ₑ ≤ ‖f (Complex.exp (t * I) * ζ)‖ₑ + ‖f ζ‖ₑ := enorm_sub_le
      _ ≤ (⨆ ζ ∈ sphere (0 : ℂ) 1, ‖f ζ‖ₑ) + ⨆ ζ ∈ sphere (0 : ℂ) 1, ‖f ζ‖ₑ :=
          add_le_add (le_iSup₂ (f := fun ζ (_ : ζ ∈ sphere (0 : ℂ) 1) => ‖f ζ‖ₑ) _ (hrot1 t ζ hζ))
            (le_iSup₂ (f := fun ζ (_ : ζ ∈ sphere (0 : ℂ) 1) => ‖f ζ‖ₑ) ζ hζ)
      _ = 2 * ⨆ ζ ∈ sphere (0 : ℂ) 1, ‖f ζ‖ₑ := (two_mul _).symm
  · have hΛ' : ∀ s : ℝ, 0 < s → ∀ ζ ∈ sphere (0 : ℂ) 1,
        ‖f (Complex.exp (s * I) * ζ) + f (Complex.exp (-(s * I)) * ζ) - (2 : ℕ) • f ζ‖ₑ ≤
          Λ * ENNReal.ofReal s := fun s hs ζ hζ => by
      refine le_trans (le_iSup₂ (f := fun ζ (_ : ζ ∈ sphere (0 : ℂ) 1) =>
        ‖f (Complex.exp (s * I) * ζ) + f (Complex.exp (-(s * I)) * ζ) - (2 : ℕ) • f ζ‖ₑ) ζ hζ) ?_
      rw [← gm23_eLpNorm_top_eq (hDc s)]
      exact hΛ s hs
    rw [gm23_eLpNorm_top_eq (hΔc t), gm23_eLpNorm_top_eq (hΔc (2 * t))]
    rw [ENNReal.mul_iSup]
    simp_rw [ENNReal.mul_iSup]
    refine iSup₂_le fun ζ hζ => ?_
    have hη := hrot1 t ζ hζ
    have e1 : Complex.exp (t * I) * (Complex.exp (t * I) * ζ) = Complex.exp (((2 * t : ℝ) : ℂ) * I) * ζ := by
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    have e2 : Complex.exp (-(t * I)) * (Complex.exp (t * I) * ζ) = ζ := by
      rw [← mul_assoc, ← Complex.exp_add]
      simp
    have hid : 2 * (f (Complex.exp (t * I) * ζ) - f ζ) =
        (f (Complex.exp (((2 * t : ℝ) : ℂ) * I) * ζ) - f ζ) -
          (f (Complex.exp (t * I) * (Complex.exp (t * I) * ζ)) +
            f (Complex.exp (-(t * I)) * (Complex.exp (t * I) * ζ)) - (2 : ℕ) • f (Complex.exp (t * I) * ζ)) := by
      rw [e1, e2]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      ring
    have h2 : (2 : ℝ≥0∞) * ‖f (Complex.exp (t * I) * ζ) - f ζ‖ₑ =
        ‖2 * (f (Complex.exp (t * I) * ζ) - f ζ)‖ₑ := by
      rw [enorm_mul]
      congr 1
      rw [← ofReal_norm]
      simp
    rw [h2, hid]
    refine (enorm_sub_le).trans (add_le_add ?_ (hΛ' t ht _ hη))
    exact le_iSup₂ (f := fun ζ (_ : ζ ∈ sphere (0 : ℂ) 1) =>
      ‖f (Complex.exp (((2 * t : ℝ) : ℂ) * I) * ζ) - f ζ‖ₑ) ζ hζ

/-- Helper (Ch. II §3, `Z* ⊆ C^α`). The dyadic iteration: a function `ω : (0, ∞) → [0, ∞]` with `ω ≤ 2N` and
`2 ω(t) ≤ ω(2t) + Λ t` satisfies `ω(t) ≤ C_α (N + Λ) t^α` for `0 < α < 1`, with `C_α` depending only on `α`. -/
theorem gm23_dyadic {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ C : ℝ≥0, ∀ (ω : ℝ → ℝ≥0∞) (N Λ : ℝ≥0∞), (∀ t : ℝ, 0 < t → ω t ≤ 2 * N) →
      (∀ t : ℝ, 0 < t → 2 * ω t ≤ ω (2 * t) + Λ * ENNReal.ofReal t) →
        ∀ t : ℝ, 0 < t → ω t ≤ (C : ℝ≥0∞) * (N + Λ) * ENNReal.ofReal (t ^ α) := by
  obtain ⟨C, hCpos, hC⟩ := gm23_dyadic_real hα₀ hα₁
  refine ⟨C.toNNReal, fun ω N Λ hN hstep t ht => ?_⟩
  have htα : 0 < t ^ α := Real.rpow_pos_of_pos ht α
  have hCne : ((C.toNNReal : ℝ≥0) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Real.toNNReal_pos.2 hCpos).ne'
  have hαne : ENNReal.ofReal (t ^ α) ≠ 0 := by simpa using htα
  by_cases hNtop : N = ⊤
  · rw [hNtop]
    simp [hCne, hαne]
  by_cases hΛtop : Λ = ⊤
  · rw [hΛtop]
    simp [hCne, hαne]
  have hωfin : ∀ s : ℝ, 0 < s → ω s ≠ ⊤ := fun s hs =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) hNtop) (hN s hs)
  set a : ℝ := N.toReal with ha
  set l : ℝ := Λ.toReal with hl
  set ω' : ℝ → ℝ := fun s => (ω s).toReal with hω'
  have h1 : ∀ s : ℝ, 0 < s → 0 ≤ ω' s ∧ ω' s ≤ 2 * a := fun s hs => by
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hNtop) (hN s hs)
    simpa [ENNReal.toReal_mul, ha, hω'] using this
  have h2 : ∀ s : ℝ, 0 < s → 2 * ω' s ≤ ω' (2 * s) + l * s := fun s hs => by
    have hfin : ω (2 * s) + Λ * ENNReal.ofReal s ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨hωfin _ (by positivity), ENNReal.mul_ne_top hΛtop ENNReal.ofReal_ne_top⟩
    have := ENNReal.toReal_mono hfin (hstep s hs)
    rw [ENNReal.toReal_mul, ENNReal.toReal_add (hωfin _ (by positivity))
      (ENNReal.mul_ne_top hΛtop ENNReal.ofReal_ne_top), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hs.le] at this
    simpa [hω', hl] using this
  have hmain := hC ω' a l ENNReal.toReal_nonneg ENNReal.toReal_nonneg h1 h2 t ht
  calc ω t = ENNReal.ofReal (ω' t) := (ENNReal.ofReal_toReal (hωfin t ht)).symm
    _ ≤ ENNReal.ofReal (C * (a + l) * t ^ α) := ENNReal.ofReal_le_ofReal hmain
    _ = ((C.toNNReal : ℝ≥0) : ℝ≥0∞) * (N + Λ) * ENNReal.ofReal (t ^ α) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hNtop, ENNReal.ofReal_toReal hΛtop]
        rfl

/-- **Unlabelled** (Ch. II §3, P1:2613–2619, with (3.12) and (3.10); used in App. J, P3:5342, where a bounded family
in `Z*` is equicontinuous, cited as "Theorem II.3.3" [misprint]). For `0 < α < 1` there is a constant `C_α` such that
`‖f‖_{C^α} ≤ C_α ‖f‖_{Z*}` for every `f ∈ Z*`.
Modelling: real `f` on `∂𝔻`; the norms are `lipschitzClassNorm` and `zygmundNorm` (in `[0, ∞]`); `C_α` depends only
on `α`. -/
theorem lipschitzClassNorm_le_zygmundNorm {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ C : ℝ≥0, ∀ f : ℂ → ℝ, MemZygmund f → lipschitzClassNorm α f ≤ (C : ℝ≥0∞) * zygmundNorm f := by
  obtain ⟨C, hC⟩ := gm23_dyadic hα₀ hα₁
  refine ⟨C + 1, fun f hf => ?_⟩
  set N : ℝ≥0∞ := eLpNorm f ⊤ arcMeasure with hN
  set Λ : ℝ≥0∞ := ⨆ (t : ℝ) (_ : 0 < t),
    eLpNorm (fun ζ => f (Complex.exp (t * I) * ζ) + f (Complex.exp (-(t * I)) * ζ) - (2 : ℕ) • f ζ) ⊤
      arcMeasure / ENNReal.ofReal t with hΛ
  obtain ⟨ha, hb⟩ := gm23_modulus_step hf
  have hsd : ∀ s : ℝ, 0 < s →
      eLpNorm (fun ζ => f (Complex.exp (s * I) * ζ) + f (Complex.exp (-(s * I)) * ζ) - (2 : ℕ) • f ζ) ⊤
        arcMeasure ≤ Λ * ENNReal.ofReal s := fun s hs => by
    have h1 : eLpNorm (fun ζ => f (Complex.exp (s * I) * ζ) + f (Complex.exp (-(s * I)) * ζ) - (2 : ℕ) • f ζ) ⊤
        arcMeasure / ENNReal.ofReal s ≤ Λ := by
      refine le_iSup₂_of_le s hs le_rfl
    exact (ENNReal.div_le_iff (by simpa using hs) ENNReal.ofReal_ne_top).1 h1
  set ω : ℝ → ℝ≥0∞ := fun t => eLpNorm (fun ζ => f (Complex.exp (t * I) * ζ) - f ζ) ⊤ arcMeasure with hω
  have hbound : ∀ t : ℝ, 0 < t → ω t ≤ (C : ℝ≥0∞) * (N + Λ) * ENNReal.ofReal (t ^ α) := by
    refine hC ω N Λ ha ?_
    intro t ht
    have := hb Λ hsd t ht
    simpa [hω] using this
  have hsup : (⨆ (t : ℝ) (_ : 0 < t), ω t / ENNReal.ofReal (t ^ α)) ≤ (C : ℝ≥0∞) * (N + Λ) := by
    refine iSup₂_le fun t ht => ?_
    have hpos : ENNReal.ofReal (t ^ α) ≠ 0 := by
      simpa using Real.rpow_pos_of_pos ht α
    exact (ENNReal.div_le_iff hpos ENNReal.ofReal_ne_top).2 (hbound t ht)
  show N + (⨆ (t : ℝ) (_ : 0 < t), ω t / ENNReal.ofReal (t ^ α)) ≤ ((C + 1 : ℝ≥0) : ℝ≥0∞) * zygmundNorm f
  calc N + (⨆ (t : ℝ) (_ : 0 < t), ω t / ENNReal.ofReal (t ^ α)) ≤ N + (C : ℝ≥0∞) * (N + Λ) :=
        add_le_add le_rfl hsup
    _ ≤ (C : ℝ≥0∞) * (N + Λ) + 1 * (N + Λ) := by
        rw [one_mul, add_comm N]
        exact add_le_add le_rfl le_self_add
    _ = ((C + 1 : ℝ≥0) : ℝ≥0∞) * zygmundNorm f := by
        rw [← add_mul]
        simp [zygmundNorm, hN, hΛ]

/-- Helper (Ch. II §3, Theorem 3.1(b)). The arc measure is carried by the unit circle (proved form). -/
theorem gm23_ae_sphere_aux : ∀ᵐ ζ ∂arcMeasure, ζ ∈ sphere (0 : ℂ) 1 := by
  rw [MeasureTheory.ae_iff]
  have hm : MeasurableSet {ζ : ℂ | ¬ ζ ∈ sphere (0 : ℂ) 1} := isClosed_sphere.measurableSet.compl
  unfold arcMeasure
  rw [Measure.map_apply (continuous_circleMap 0 1).measurable hm]
  have : circleMap 0 1 ⁻¹' {ζ : ℂ | ¬ ζ ∈ sphere (0 : ℂ) 1} = ∅ := by
    ext θ
    simp
  rw [this]
  simp

/-- Helper (Ch. II §3, Theorem 3.1(b)). The real part of an analytic polynomial is `arcMeasure`-integrable (proved
form). -/
theorem gm23_integrable_poly_aux (p : Polynomial ℂ) : Integrable (fun ζ => (p.eval ζ).re) arcMeasure := by
  have hfin := gm23_isFiniteMeasure_arcMeasure
  have hc : Continuous fun ζ : ℂ => (p.eval ζ).re := Complex.continuous_re.comp p.continuous
  obtain ⟨B, hB⟩ := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn hc.continuousOn
  refine Integrable.of_bound hc.aestronglyMeasurable B ?_
  filter_upwards [gm23_ae_sphere_aux] with ζ hζ using hB ζ hζ

/-- Helper (Ch. II §3, Theorem 3.1(b)). Every function in the span of the Fourier monomials is `p₁(z) + p₂(z⁻¹)` for
polynomials `p₁`, `p₂`, with `z = toCircle x`. -/
theorem gm23_fourier_span (q : C(AddCircle (2 * π), ℂ))
    (hq : q ∈ Submodule.span ℂ (Set.range (@fourier (2 * π)))) :
    ∃ p₁ p₂ : Polynomial ℂ, ∀ x : AddCircle (2 * π),
      q x = p₁.eval (AddCircle.toCircle x : ℂ) + p₂.eval ((AddCircle.toCircle x : ℂ)⁻¹) := by
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨n, rfl⟩ := hq
    rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
    · refine ⟨Polynomial.X ^ m, 0, fun x => ?_⟩
      rw [fourier_apply, AddCircle.toCircle_zsmul]
      simp
    · refine ⟨0, Polynomial.X ^ m, fun x => ?_⟩
      rw [fourier_apply, AddCircle.toCircle_zsmul]
      simp [zpow_neg]
  | zero => exact ⟨0, 0, fun x => by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨p₁, p₂, h⟩ := ha
    obtain ⟨p₁', p₂', h'⟩ := hb
    exact ⟨p₁ + p₁', p₂ + p₂', fun x => by simp [h x, h' x]; ring⟩
  | smul c a _ ha =>
    obtain ⟨p₁, p₂, h⟩ := ha
    exact ⟨Polynomial.C c * p₁, Polynomial.C c * p₂, fun x => by simp [h x]; ring⟩

/-- Helper (Ch. II §3, Theorem 3.1(b)). The Poisson integral of a function bounded by `1` almost everywhere on the
circle is bounded by `1` in the disc. -/
theorem gm23_poisson_le {g : ℂ → ℝ} (hg : Integrable g arcMeasure) (hb : ∀ᵐ ζ ∂arcMeasure, ‖g ζ‖ ≤ 1)
    {z : ℂ} (hz : z ∈ unitDisc) : |poissonIntegral g z| ≤ 1 := by
  have hz1 : ‖z‖ < 1 := by simpa [unitDisc] using hz
  have hone : Real.circleAverage (poissonKernel 0 z • fun _ : ℂ => (1 : ℝ)) 0 1 = 1 :=
    (InnerProductSpace.harmonicOnNhd_const (1 : ℝ)).circleAverage_poissonKernel_smul (by simpa using hz1)
  have hne : ∀ θ : ℝ, 0 < ‖circleMap 0 1 θ - z‖ := fun θ => by
    apply norm_pos_iff.2
    intro h0
    have : ‖z‖ = 1 := by
      have := congrArg norm (sub_eq_zero.1 h0)
      simpa using this.symm
    linarith
  have hKdef : ∀ θ : ℝ, poissonKernel 0 z (circleMap 0 1 θ) = (1 - ‖z‖ ^ 2) / ‖circleMap 0 1 θ - z‖ ^ 2 :=
    fun θ => by simp [poissonKernel_def]
  have hK0 : ∀ θ : ℝ, 0 ≤ poissonKernel 0 z (circleMap 0 1 θ) := fun θ => by
    rw [hKdef]
    exact div_nonneg (by nlinarith [norm_nonneg z]) (sq_nonneg _)
  have hKc : Continuous fun θ : ℝ => poissonKernel 0 z (circleMap 0 1 θ) := by
    have : (fun θ : ℝ => poissonKernel 0 z (circleMap 0 1 θ)) =
        fun θ => (1 - ‖z‖ ^ 2) / ‖circleMap 0 1 θ - z‖ ^ 2 := funext hKdef
    rw [this]
    exact continuous_const.div (((continuous_circleMap 0 1).sub continuous_const).norm.pow 2)
      (fun θ => pow_ne_zero 2 (hne θ).ne')
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) (2 * π))), ‖g (circleMap 0 1 θ)‖ ≤ 1 :=
    MeasureTheory.ae_of_ae_map (continuous_circleMap 0 1).measurable.aemeasurable hb
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hgcirc : CircleIntegrable g 0 1 := gm23_circleIntegrable hg
  have hKg : IntervalIntegrable (fun θ : ℝ => poissonKernel 0 z (circleMap 0 1 θ) * g (circleMap 0 1 θ))
      MeasureTheory.volume 0 (2 * π) := by
    have := IntervalIntegrable.continuousOn_mul (hf := hgcirc) (hg := hKc.continuousOn)
    exact this
  have hKint : IntervalIntegrable (fun θ : ℝ => poissonKernel 0 z (circleMap 0 1 θ)) MeasureTheory.volume 0 (2 * π) :=
    hKc.intervalIntegrable _ _
  have hone' : (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 z (circleMap 0 1 θ) = 1 := by
    simpa [Real.circleAverage_def] using hone
  have hA : |∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 z (circleMap 0 1 θ) * g (circleMap 0 1 θ)| ≤
      ∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 z (circleMap 0 1 θ) := by
    refine (intervalIntegral.abs_integral_le_integral_abs h2π).trans ?_
    rw [intervalIntegral.integral_of_le h2π, intervalIntegral.integral_of_le h2π]
    refine MeasureTheory.integral_mono_ae ?_ ?_ ?_
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).1 hKg.abs
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).1 hKint
    · filter_upwards [haeθ] with θ hθ
      rw [abs_mul, abs_of_nonneg (hK0 θ)]
      calc poissonKernel 0 z (circleMap 0 1 θ) * |g (circleMap 0 1 θ)|
          ≤ poissonKernel 0 z (circleMap 0 1 θ) * 1 := mul_le_mul_of_nonneg_left (by simpa using hθ) (hK0 θ)
        _ = _ := mul_one _
  unfold poissonIntegral Real.circleAverage
  simp only [smul_eq_mul]
  rw [abs_mul, abs_of_pos (inv_pos.2 (by positivity))]
  calc (2 * π)⁻¹ * |∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 z (circleMap 0 1 θ) * g (circleMap 0 1 θ)|
      ≤ (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 z (circleMap 0 1 θ) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
    _ = 1 := hone'

/-- Helper (Ch. II §3, Theorem 3.1(b)). Lower integral over `(0, 2π]` as an average. -/
theorem gm23_lintegral_avg {h : ℝ → ℝ} (hc : Continuous h) (h0 : ∀ θ, 0 ≤ h θ) :
    (∫⁻ θ in Set.Ioc (0 : ℝ) (2 * π), ENNReal.ofReal (h θ)) / ENNReal.ofReal (2 * π) =
      ENNReal.ofReal ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, h θ) := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hint : Integrable h (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) (2 * π))) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).1 (hc.intervalIntegrable _ _)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall h0),
    ← intervalIntegral.integral_of_le h2π, ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  ring

/-- Helper (Ch. II §3, Theorem 3.1(b)). The mean value inequality for `e^{± l g̃}`: with `|Re F| ≤ 1` on the disc and
`0 ≤ l < π/2`, `cos l · avg e^{± l Im F} ≤ 1` on every circle of radius `r < 1`. -/
theorem gm23_exp_mean_signed {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F unitDisc) (hF0 : (F 0).im = 0)
    (hu1 : ∀ z ∈ unitDisc, |(F z).re| ≤ 1) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < π / 2) {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    Real.cos l * Real.circleAverage (fun w => Real.exp (s * l * (F w).im)) 0 r ≤ 1 := by
  set G : ℂ → ℂ := fun w => Complex.exp (((-(s * l) : ℝ) : ℂ) * I * F w) with hG
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hReG : ∀ w, (G w).re = Real.exp (s * l * (F w).im) * Real.cos (l * (F w).re) := by
    intro w
    simp only [hG, Complex.exp_re]
    have hre : ((((-(s * l) : ℝ) : ℂ) * I * F w)).re = s * l * (F w).im := by
      simp [Complex.mul_re, Complex.mul_im]
    have him : ((((-(s * l) : ℝ) : ℂ) * I * F w)).im = -(s * l) * (F w).re := by
      simp [Complex.mul_re, Complex.mul_im]
    have key : ∀ a : ℝ, Real.cos (-(s * l) * a) = Real.cos (l * a) := by
      intro a
      rcases hs with rfl | rfl
      · rw [show -(1 * l) * a = -(l * a) by ring, Real.cos_neg]
      · rw [show -(-1 * l) * a = l * a by ring]
    rw [hre, him, key]
  have hGa : ∀ w ∈ unitDisc, AnalyticAt ℂ G w := fun w hw =>
    (analyticAt_const.mul (hF w hw)).cexp
  have hsub : closedBall (0 : ℂ) |r| ⊆ unitDisc := by
    intro w hw
    rw [mem_closedBall_zero_iff, abs_of_pos hr.1] at hw
    simp only [unitDisc, mem_ball_zero_iff]
    exact lt_of_le_of_lt hw hr.2
  have hHar : InnerProductSpace.HarmonicOnNhd (fun w => (G w).re) (closedBall (0 : ℂ) |r|) :=
    fun w hw => (hGa w (hsub hw)).harmonicAt_re
  have hmean : Real.circleAverage (fun w => (G w).re) 0 r = (G 0).re := hHar.circleAverage_eq
  have h0mem : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]
  have hG0 : (G 0).re ≤ 1 := by
    rw [hReG, hF0, mul_zero, Real.exp_zero, one_mul]
    exact Real.cos_le_one _
  -- continuity on the circle
  have hFc : ContinuousOn F unitDisc := fun w hw => (hF w hw).continuousAt.continuousWithinAt
  have hsph : sphere (0 : ℂ) |r| ⊆ unitDisc := fun w hw => hsub (sphere_subset_closedBall hw)
  have hI1 : CircleIntegrable (fun w => Real.exp (s * l * (F w).im)) 0 r := by
    refine ContinuousOn.circleIntegrable' ?_
    exact (Real.continuous_exp.comp_continuousOn
      ((continuous_const.mul Complex.continuous_im |>.comp_continuousOn (hFc.mono hsph))))
  have hI2 : CircleIntegrable (fun w => (G w).re) 0 r := by
    refine ContinuousOn.circleIntegrable' ?_
    have : ContinuousOn G (sphere (0 : ℂ) |r|) := fun w hw => (hGa w (hsph hw)).continuousAt.continuousWithinAt
    exact Complex.continuous_re.comp_continuousOn this
  have hmono : Real.circleAverage (fun w => Real.cos l * Real.exp (s * l * (F w).im)) 0 r ≤
      Real.circleAverage (fun w => (G w).re) 0 r := by
    refine Real.circleAverage_mono (hI1.const_mul _) hI2 (fun w hw => ?_)
    have hwd : w ∈ unitDisc := hsph hw
    rw [hReG]
    have hcos : Real.cos l ≤ Real.cos (l * (F w).re) := by
      rw [← Real.cos_abs (l * (F w).re), abs_mul, abs_of_nonneg hl0]
      refine Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos]) ?_
      calc l * |(F w).re| ≤ l * 1 := mul_le_mul_of_nonneg_left (hu1 w hwd) hl0
        _ = l := mul_one l
    calc Real.cos l * Real.exp (s * l * (F w).im)
        ≤ Real.cos (l * (F w).re) * Real.exp (s * l * (F w).im) :=
          mul_le_mul_of_nonneg_right hcos (Real.exp_pos _).le
      _ = Real.exp (s * l * (F w).im) * Real.cos (l * (F w).re) := mul_comm _ _
  have hcs : Real.circleAverage (fun w => Real.cos l * Real.exp (s * l * (F w).im)) 0 r =
      Real.cos l * Real.circleAverage (fun w => Real.exp (s * l * (F w).im)) 0 r := by
    simp only [Real.circleAverage_def, intervalIntegral.integral_const_mul, smul_eq_mul]
    ring
  rw [← hcs]
  exact hmono.trans (hmean ▸ hG0)

/-- Helper (Ch. II §3, Theorem 3.1(b)). Continuous functions on the circle are uniformly approximated by real parts of
analytic polynomials (trigonometric polynomials). -/
theorem gm23_trig_approx {f : ℂ → ℝ} (hfc : ContinuousOn f (sphere (0 : ℂ) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ ζ ∈ sphere (0 : ℂ) 1, |f ζ - (p.eval ζ).re| ≤ ε := by
  have : Fact ((0 : ℝ) < 2 * π) := ⟨by positivity⟩
  set e : AddCircle (2 * π) ≃ₜ Circle := AddCircle.homeomorphCircle (T := 2 * π) (by positivity) with he
  have hcoe : ∀ x, ((e x : Circle) : ℂ) ∈ sphere (0 : ℂ) 1 := fun x => by
    simp
  have hcc : Continuous fun x : AddCircle (2 * π) => ((e x : Circle) : ℂ) := by fun_prop
  have hcont : Continuous fun x : AddCircle (2 * π) => f ((e x : Circle) : ℂ) :=
    hfc.comp_continuous hcc hcoe
  set F : C(AddCircle (2 * π), ℂ) := ⟨fun x => ((f ((e x : Circle) : ℂ) : ℝ) : ℂ),
    Complex.continuous_ofReal.comp hcont⟩ with hF
  have hmem : F ∈ (Submodule.span ℂ (Set.range (@fourier (2 * π)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]; trivial
  have hmem2 : F ∈ closure ((Submodule.span ℂ (Set.range (@fourier (2 * π))) : Submodule ℂ C(AddCircle (2 * π), ℂ)) :
      Set C(AddCircle (2 * π), ℂ)) := hmem
  obtain ⟨q, hqs, hFq⟩ := Metric.mem_closure_iff.1 hmem2 ε hε
  obtain ⟨p₁, p₂, hp⟩ := gm23_fourier_span q hqs
  refine ⟨p₁ + p₂.map (starRingEnd ℂ), fun ζ hζ => ?_⟩
  have hζc : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.1 hζ
  set c : Circle := ⟨ζ, hζ⟩ with hc
  obtain ⟨x, hx⟩ := e.surjective c
  have hxz : ((e x : Circle) : ℂ) = ζ := by rw [hx]
  have hdist : ‖F x - q x‖ ≤ ε := by
    have := ContinuousMap.dist_apply_le_dist (f := F) (g := q) x
    rw [dist_eq_norm] at this
    exact this.trans (le_of_lt hFq)
  have hto : (AddCircle.toCircle x : ℂ) = ζ := by
    rw [← hxz, he, AddCircle.homeomorphCircle_apply]
  have hqx := hp x
  rw [hto] at hqx
  have hinvc : ζ⁻¹ = (starRingEnd ℂ) ζ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hζc]
    simp
  have hinv : (starRingEnd ℂ) (ζ⁻¹) = ζ := by
    rw [hinvc, Complex.conj_conj]
  have hmap : (p₂.map (starRingEnd ℂ)).eval ζ = (starRingEnd ℂ) (p₂.eval ζ⁻¹) := by
    conv_lhs => rw [← hinv]
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  have hFx : F x = ((f ζ : ℝ) : ℂ) := by simp [hF, hxz]
  have hre : (f ζ : ℝ) - ((p₁ + p₂.map (starRingEnd ℂ)).eval ζ).re = (F x - q x).re := by
    rw [Polynomial.eval_add, hmap, hFx, hqx]
    simp
  rw [hre]
  exact (Complex.abs_re_le_norm _).trans hdist

/-- Helper (Ch. II §3, Theorem 3.1(b)). The conjugate function of the real part of an analytic polynomial is bounded in
the disc. -/
theorem gm23_conj_polynomial (p : Polynomial ℂ) :
    ∃ C : ℝ, ∀ z ∈ unitDisc, |conjugateFunction (fun ζ => (p.eval ζ).re) z| ≤ C := by
  have hfin := gm23_isFiniteMeasure_arcMeasure
  have hpi := gm23_integrable_poly_aux p
  have hdiff : Differentiable ℂ (fun w : ℂ => p.eval w) := p.differentiable
  have hanal : ∀ w : ℂ, AnalyticAt ℂ (fun w : ℂ => p.eval w) w := fun w => hdiff.analyticAt w
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn p.continuous.continuousOn
  refine ⟨2 * B, fun z hz => ?_⟩
  -- the Poisson integral of `Re p` is `Re p`
  have hPoi : ∀ w ∈ unitDisc, poissonIntegral (fun ζ => (p.eval ζ).re) w = (p.eval w).re := by
    intro w hw
    have hh : InnerProductSpace.HarmonicOnNhd (fun ζ : ℂ => (p.eval ζ).re) (closedBall (0 : ℂ) 1) :=
      fun x _ => (hanal x).harmonicAt_re
    exact hh.circleAverage_poissonKernel_smul (by simpa [unitDisc] using hw)
  set v : ℂ → ℝ := fun w => (p.eval w).im - (p.eval 0).im with hv
  have hvh : InnerProductSpace.HarmonicOnNhd v unitDisc := fun x _ =>
    (hanal x).harmonicAt_im.sub (InnerProductSpace.harmonicAt_const _)
  have hva : AnalyticOnNhd ℂ (fun w => ((poissonIntegral (fun ζ => (p.eval ζ).re) w : ℝ) : ℂ) + (v w : ℂ) * I)
      unitDisc := by
    have h1 : AnalyticOnNhd ℂ (fun w : ℂ => p.eval w - ((p.eval 0).im : ℂ) * I) unitDisc :=
      fun x _ => (hanal x).sub analyticAt_const
    refine h1.congr isOpen_ball (fun w hw => ?_)
    show p.eval w - ((p.eval 0).im : ℂ) * I = _
    rw [hPoi w hw]
    simp only [hv]
    push_cast
    apply Complex.ext <;> simp
  have hu := gm23_conjugate_unique hpi hvh (by simp [hv]) hva hz
  have hc : conjugateFunction (fun ζ => (p.eval ζ).re) z = v z := by
    have := congrArg Complex.im (eq2_3_3 hpi hz)
    simp at this
    rw [hu]
    simpa using this
  rw [hc]
  have hzc : z ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hz
  have h0c : (0 : ℂ) ∈ closedBall (0 : ℂ) 1 := mem_closedBall_self zero_le_one
  have b1 := hB z hzc
  have b2 := hB 0 h0c
  simp only [hv]
  calc |(p.eval z).im - (p.eval 0).im| ≤ |(p.eval z).im| + |(p.eval 0).im| := abs_sub _ _
    _ ≤ ‖p.eval z‖ + ‖p.eval 0‖ := add_le_add (Complex.abs_im_le_norm _) (Complex.abs_im_le_norm _)
    _ ≤ 2 * B := by linarith

/-- Helper (Ch. II §3, Theorem 3.1(b)). The conjugate function is linear: `(P + c g)~ = P~ + c g~` in the disc for
integrable `P`, `g`. -/
theorem gm23_conj_lin {P g : ℂ → ℝ} (hP : Integrable P arcMeasure) (hg : Integrable g arcMeasure) (c : ℝ) {z : ℂ}
    (hz : z ∈ unitDisc) :
    conjugateFunction (fun ζ => P ζ + c * g ζ) z = conjugateFunction P z + c * conjugateFunction g z := by
  have hconj : ∀ h : ℂ → ℝ, Integrable h arcMeasure → ∀ w ∈ unitDisc,
      conjugateFunction h w = (herglotzIntegral h w).im := by
    intro h hh w hw
    have := congrArg Complex.im (eq2_3_3 hh hw)
    simpa using this
  have hsum : Integrable (fun ζ => P ζ + c * g ζ) arcMeasure := hP.add (hg.const_mul c)
  rw [hconj _ hsum z hz, hconj P hP z hz, hconj g hg z hz]
  have hzs : z ∉ sphere (0 : ℂ) |(1 : ℝ)| := by
    have : ‖z‖ < 1 := by simpa [unitDisc] using hz
    simp only [abs_one, mem_sphere_iff_norm, sub_zero]
    exact this.ne
  have hcl : ∀ h : ℂ → ℝ, Integrable h arcMeasure →
      CircleIntegrable (fun ζ => herglotzRieszKernel 0 z ζ * (h ζ : ℂ)) 0 1 := by
    intro h hh
    have hcirc := gm23_circleIntegrable hh
    have hc : CircleIntegrable (fun ζ => (h ζ : ℂ)) 0 1 := by
      simp only [CircleIntegrable, intervalIntegrable_iff] at hcirc ⊢
      exact Complex.ofRealCLM.integrable_comp hcirc
    exact hc.continuousOn_smul (continuousOn_herglotzRieszKernel_sphere hzs)
  have h1 : herglotzIntegral (fun ζ => P ζ + c * g ζ) z = herglotzIntegral P z + (c : ℂ) * herglotzIntegral g z := by
    unfold herglotzIntegral
    have e : ∀ ζ : ℂ, herglotzRieszKernel 0 z ζ * ((P ζ + c * g ζ : ℝ) : ℂ) =
        herglotzRieszKernel 0 z ζ * (P ζ : ℂ) + (c : ℂ) * (herglotzRieszKernel 0 z ζ * (g ζ : ℂ)) := fun ζ => by
      push_cast; ring
    simp_rw [e]
    have hcl2 : CircleIntegrable (fun ζ => (c : ℂ) * (herglotzRieszKernel 0 z ζ * (g ζ : ℂ))) 0 1 :=
      (hcl g hg).const_mul _
    rw [Real.circleAverage_fun_add (hcl P hP) hcl2]
    congr 1
    simp only [Real.circleAverage_def, intervalIntegral.integral_const_mul]
    rw [Complex.real_smul, Complex.real_smul]
    ring
  rw [h1]
  simp

/-- Helper (Ch. II §3, Theorem 3.1(b)). The interior estimate of Zygmund's theorem: for real `g ∈ L^∞` with
`‖g‖_∞ ≤ 1` and `0 ≤ λ < π/2`, `(1/2π) ∫ e^{λ|ũ(re^{iθ})|} dθ ≤ 2/cos λ` for every `r < 1`. -/
theorem gm23_exp_mean {g : ℂ → ℝ} (hg : MemLp g ⊤ arcMeasure) (hg1 : eLpNorm g ⊤ arcMeasure ≤ 1) {l : ℝ}
    (hl0 : 0 ≤ l) (hl : l < π / 2) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (Real.exp (l * |conjugateFunction g (circleMap 0 r θ)|))) /
        ENNReal.ofReal (2 * π) ≤ ENNReal.ofReal (2 / Real.cos l) := by
  have hfin := gm23_isFiniteMeasure_arcMeasure
  have hgi : Integrable g arcMeasure := hg.integrable le_top
  have hgb : ∀ᵐ ζ ∂arcMeasure, ‖g ζ‖ ≤ 1 := by
    filter_upwards [enorm_ae_le_eLpNormEssSup g arcMeasure] with ζ hζ
    have h1 : ‖g ζ‖ₑ ≤ eLpNorm g ⊤ arcMeasure := by
      rw [eLpNorm_exponent_top]
      · exact hζ
      · exact hg.aestronglyMeasurable
    have := h1.trans hg1
    rw [← ofReal_norm] at this
    exact ENNReal.ofReal_le_one.1 this
  obtain ⟨hFa, -, hF0⟩ := gm23_herglotz_analytic hgi
  have him : ∀ z ∈ unitDisc, conjugateFunction g z = (herglotzIntegral g z).im := by
    intro z hz
    have := congrArg Complex.im (eq2_3_3 hgi hz)
    simpa using this
  have hu1 : ∀ z ∈ unitDisc, |(herglotzIntegral g z).re| ≤ 1 := by
    intro z hz
    rw [← gm23_poissonIntegral_eq_re hgi hz]
    exact gm23_poisson_le hgi hgb hz
  have hrd : ∀ θ : ℝ, circleMap 0 r θ ∈ unitDisc := fun θ => by
    simp only [unitDisc, mem_ball_zero_iff, norm_circleMap_zero]
    rw [abs_of_pos hr.1]
    exact hr.2
  have hcongr : ∀ θ : ℝ, Real.exp (l * |conjugateFunction g (circleMap 0 r θ)|) =
      Real.exp (l * |(herglotzIntegral g (circleMap 0 r θ)).im|) := fun θ => by
    rw [him _ (hrd θ)]
  simp_rw [hcongr]
  have hFc : ContinuousOn (herglotzIntegral g) unitDisc := fun w hw =>
    (hFa w hw).continuousAt.continuousWithinAt
  have hFcirc : Continuous fun θ : ℝ => herglotzIntegral g (circleMap 0 r θ) :=
    hFc.comp_continuous (continuous_circleMap 0 r) hrd
  have hcont : Continuous fun θ : ℝ => Real.exp (l * |(herglotzIntegral g (circleMap 0 r θ)).im|) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_abs.comp (Complex.continuous_im.comp hFcirc)))
  rw [gm23_lintegral_avg hcont (fun θ => (Real.exp_pos _).le)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcl : 0 < Real.cos l := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hl⟩
  have hp := gm23_exp_mean_signed hFa hF0 hu1 hl0 hl hr (s := 1) (Or.inl rfl)
  have hm := gm23_exp_mean_signed hFa hF0 hu1 hl0 hl hr (s := -1) (Or.inr rfl)
  have hcircle : (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, Real.exp (l * |(herglotzIntegral g (circleMap 0 r θ)).im|) =
      Real.circleAverage (fun w => Real.exp (l * |(herglotzIntegral g w).im|)) 0 r := by
    simp [Real.circleAverage_def]
  rw [hcircle]
  have hsph : sphere (0 : ℂ) |r| ⊆ unitDisc := fun w hw => by
    rw [mem_sphere_zero_iff_norm, abs_of_pos hr.1] at hw
    simp only [unitDisc, mem_ball_zero_iff]
    rw [hw]; exact hr.2
  have hci : ∀ s : ℝ, CircleIntegrable (fun w => Real.exp (s * l * (herglotzIntegral g w).im)) 0 r := fun s => by
    refine ContinuousOn.circleIntegrable' ?_
    exact Real.continuous_exp.comp_continuousOn
      ((continuous_const.mul Complex.continuous_im).comp_continuousOn (hFc.mono hsph))
  have hca : CircleIntegrable (fun w => Real.exp (l * |(herglotzIntegral g w).im|)) 0 r := by
    refine ContinuousOn.circleIntegrable' ?_
    exact Real.continuous_exp.comp_continuousOn
      ((continuous_const.mul (continuous_abs.comp Complex.continuous_im)).comp_continuousOn (hFc.mono hsph))
  have hle : Real.circleAverage (fun w => Real.exp (l * |(herglotzIntegral g w).im|)) 0 r ≤
      Real.circleAverage (fun w => Real.exp (1 * l * (herglotzIntegral g w).im)) 0 r +
        Real.circleAverage (fun w => Real.exp (-1 * l * (herglotzIntegral g w).im)) 0 r := by
    rw [← Real.circleAverage_fun_add (hci 1) (hci (-1))]
    refine Real.circleAverage_mono hca ((hci 1).add (hci (-1))) (fun w _ => ?_)
    show Real.exp (l * |(herglotzIntegral g w).im|) ≤
      Real.exp (1 * l * (herglotzIntegral g w).im) + Real.exp (-1 * l * (herglotzIntegral g w).im)
    rcases abs_cases (herglotzIntegral g w).im with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
      have := Real.exp_pos (-1 * l * (herglotzIntegral g w).im)
      have e : Real.exp (l * (herglotzIntegral g w).im) = Real.exp (1 * l * (herglotzIntegral g w).im) := by
        rw [one_mul]
      linarith
    · rw [h]
      have := Real.exp_pos (1 * l * (herglotzIntegral g w).im)
      have e : Real.exp (l * -(herglotzIntegral g w).im) = Real.exp (-1 * l * (herglotzIntegral g w).im) := by
        congr 1; ring
      linarith
  rw [le_div_iff₀ hcl]
  nlinarith [hle, hp, hm]

/-- Helper (Ch. II §3, Theorem 3.1(b)). The arc measure is carried by the unit circle. -/
theorem gm23_ae_sphere : ∀ᵐ ζ ∂arcMeasure, ζ ∈ sphere (0 : ℂ) 1 := by
  exact gm23_ae_sphere_aux

/-- Helper (Ch. II §3, Theorem 3.1(b)). The real part of an analytic polynomial is `arcMeasure`-integrable. -/
theorem gm23_integrable_poly (p : Polynomial ℂ) : Integrable (fun ζ => (p.eval ζ).re) arcMeasure := by
  exact gm23_integrable_poly_aux p

/-- **Theorem 3.1** (Zygmund; Ch. II §3), part (b) (cited at P1:2800 "by part (b) of Theorem 3.1"). Let `f ∈ L^∞(∂𝔻)`
be real with `‖f‖_∞ ≤ 1`. If `f ∈ C(∂𝔻)`, then for all `λ < ∞`,
`sup_{0<r<1} ∫ e^{λ|ũ(re^{iθ})|} dθ/2π < ∞`.
Modelling: `f` continuous on `∂𝔻`; `λ` any real number; the integral over `θ ∈ (0, 2π]` as a lower integral and the
supremum in `[0, ∞]`. -/
theorem thm2_3_1_b {f : ℂ → ℝ} (hf : MemLp f ⊤ arcMeasure) (hf1 : eLpNorm f ⊤ arcMeasure ≤ 1)
    (hfc : ContinuousOn f (sphere 0 1)) (lam : ℝ) :
    ⨆ r ∈ Ioo (0 : ℝ) 1, (∫⁻ θ in Ioc 0 (2 * π),
      ENNReal.ofReal (Real.exp (lam * |conjugateFunction f (circleMap 0 r θ)|))) / ENNReal.ofReal (2 * π) < ⊤ := by
  have hfin := gm23_isFiniteMeasure_arcMeasure
  have hfi : Integrable f arcMeasure := hf.integrable le_top
  set L : ℝ := |lam| with hL
  have hL0 : 0 ≤ L := abs_nonneg _
  set ε : ℝ := (π / 4) / (L + 1) with hε
  have hεpos : 0 < ε := by positivity
  have hLε : L * ε < π / 4 := by
    have h1 : L * ε = (π / 4) * (L / (L + 1)) := by
      rw [hε]; field_simp
    have h2 : L / (L + 1) < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    rw [h1]
    nlinarith [Real.pi_pos]
  obtain ⟨p, hp⟩ := gm23_trig_approx hfc hεpos
  obtain ⟨C, hC⟩ := gm23_conj_polynomial p
  set P : ℂ → ℝ := fun ζ => (p.eval ζ).re with hP
  set g : ℂ → ℝ := fun ζ => (f ζ - P ζ) / ε with hg
  have hPi : Integrable P arcMeasure := gm23_integrable_poly p
  have hgi : Integrable g arcMeasure := (hfi.sub hPi).div_const ε
  have hgb : ∀ᵐ ζ ∂arcMeasure, ‖g ζ‖ ≤ 1 := by
    filter_upwards [gm23_ae_sphere] with ζ hζ
    have := hp ζ hζ
    simp only [hg, Real.norm_eq_abs, abs_div, abs_of_pos hεpos]
    rw [div_le_one hεpos]
    exact this
  have hgm : MemLp g ⊤ arcMeasure := MemLp.of_bound hgi.aestronglyMeasurable 1 hgb
  have hg1 : eLpNorm g ⊤ arcMeasure ≤ 1 := by
    rw [eLpNorm_exponent_top hgi.aestronglyMeasurable]
    simpa using eLpNormEssSup_le_of_ae_bound hgb
  have hfe : f = fun ζ => P ζ + ε * g ζ := by
    funext ζ
    simp only [hg]
    field_simp
    ring
  have hLε0 : 0 ≤ L * ε := by positivity
  have hLεlt : L * ε < π / 2 := by linarith [Real.pi_pos]
  have hcosx : 0 < Real.cos (L * ε) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hLεlt⟩
  -- the uniform bound
  have hbound : ∀ r ∈ Ioo (0 : ℝ) 1, (∫⁻ θ in Ioc 0 (2 * π),
      ENNReal.ofReal (Real.exp (lam * |conjugateFunction f (circleMap 0 r θ)|))) / ENNReal.ofReal (2 * π) ≤
      ENNReal.ofReal (Real.exp (L * C)) * ENNReal.ofReal (2 / Real.cos (L * ε)) := by
    intro r hr
    have hmean := gm23_exp_mean hgm hg1 hLε0 hLεlt hr
    have hpt : ∀ θ : ℝ, ENNReal.ofReal (Real.exp (lam * |conjugateFunction f (circleMap 0 r θ)|)) ≤
        ENNReal.ofReal (Real.exp (L * C)) *
          ENNReal.ofReal (Real.exp ((L * ε) * |conjugateFunction g (circleMap 0 r θ)|)) := by
      intro θ
      have hzd : circleMap 0 r θ ∈ unitDisc := by
        simp only [unitDisc, mem_ball_zero_iff, norm_circleMap_zero]
        rw [abs_of_pos hr.1]; exact hr.2
      have hlin : conjugateFunction f (circleMap 0 r θ) =
          conjugateFunction P (circleMap 0 r θ) + ε * conjugateFunction g (circleMap 0 r θ) := by
        have := gm23_conj_lin hPi hgi ε hzd
        rw [← hfe] at this
        exact this
      have hPC : |conjugateFunction P (circleMap 0 r θ)| ≤ C := hC _ hzd
      have h1 : |conjugateFunction f (circleMap 0 r θ)| ≤ C + ε * |conjugateFunction g (circleMap 0 r θ)| := by
        rw [hlin]
        calc |conjugateFunction P (circleMap 0 r θ) + ε * conjugateFunction g (circleMap 0 r θ)|
            ≤ |conjugateFunction P (circleMap 0 r θ)| + |ε * conjugateFunction g (circleMap 0 r θ)| :=
              abs_add_le _ _
          _ ≤ C + ε * |conjugateFunction g (circleMap 0 r θ)| := by
              rw [abs_mul, abs_of_pos hεpos]; linarith
      have h2 : lam * |conjugateFunction f (circleMap 0 r θ)| ≤ L * (C + ε * |conjugateFunction g (circleMap 0 r θ)|) := by
        calc lam * |conjugateFunction f (circleMap 0 r θ)| ≤ |lam| * |conjugateFunction f (circleMap 0 r θ)| :=
              mul_le_mul_of_nonneg_right (le_abs_self lam) (abs_nonneg _)
          _ ≤ L * (C + ε * |conjugateFunction g (circleMap 0 r θ)|) := by
              rw [← hL]; exact mul_le_mul_of_nonneg_left h1 hL0
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      nlinarith [h2]
    calc (∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (Real.exp (lam * |conjugateFunction f (circleMap 0 r θ)|))) /
          ENNReal.ofReal (2 * π)
        ≤ (∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (Real.exp (L * C)) *
            ENNReal.ofReal (Real.exp ((L * ε) * |conjugateFunction g (circleMap 0 r θ)|))) /
          ENNReal.ofReal (2 * π) := by
          gcongr with θ
          exact hpt θ
      _ = ENNReal.ofReal (Real.exp (L * C)) *
          ((∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (Real.exp ((L * ε) * |conjugateFunction g (circleMap 0 r θ)|))) /
            ENNReal.ofReal (2 * π)) := by
          rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_div_assoc]
      _ ≤ ENNReal.ofReal (Real.exp (L * C)) * ENNReal.ofReal (2 / Real.cos (L * ε)) := by
          gcongr
  refine lt_of_le_of_lt (iSup₂_le fun r hr => hbound r hr) ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

end GarnettMarshall2005
