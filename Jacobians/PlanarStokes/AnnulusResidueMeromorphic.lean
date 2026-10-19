/-
  The single-pole residue lemma for a meromorphic integrand (Forster (10.21), assembled).

  `AnnulusResidueIntegral.lean` computes the Forster (10.21) area integral for one negative
  power, `∫_ℂ ∂̄(χ·(·−c)^{−k}) = −π·δ_{k,1}` (`integral_dbar_radialCutoff_zpow`).  This file
  assembles the §5–§7 plan of that file's header into the full single-pole atom:

    `∫_ℂ ∂̄(χ·m) = −π · Res_c m`        (`integral_dbar_radialCutoff_meromorphic`)

  for `m` meromorphic at `c` and honestly analytic on a punctured ball `ball c r \ {c}` whose
  radius dominates the cutoff (`s₁ < r²`), with `χ = η(normSq(·−c))` a radial `C¹` profile going
  `1 → 0` between `s₀` and `s₁` (`0 < s₀ < s₁`).

  Proof layout:
  * principal-part split `m = P + G` (`exists_principalPart_meromorphicAt`): `P = negTail c b N`
    carries the pole, and the junk-repaired complement `G := update (m − P) c (R c)` is analytic
    on the WHOLE ball `ball c r` — the split is a *pointwise identity off `c`* (not just a germ),
    because `G` is literally defined as `m − P` away from `c`;
  * the `G`-term dies: `χ·G` is `C¹` with compact support, so `∫ ∂̄(χ·G) = 0` by the planar
    Stokes lemma (`integral_dbar_eq_zero`, Forster (10.20));
  * the `P`-term is the finite sum of single-power computations,
    `∫ ∂̄(χ·P) = ∑_k b_k·(−π·δ_{k,1}) = −π·b₁`, with the sum/integral swap justified by the
    explicit continuous compactly-supported closed form `η′(normSq(z−c))·(z−c)^{1−k}`;
  * `resAt m c = resAt P c + resAt G c = b₁ + 0` by the `resAt` calculus.

  Also provided for the global assembly (`ResidueTheoremStokes.lean`):
  * `integral_radialDeriv_mul_eq_resAt` — the closed-form version
    `∫_ℂ η′(normSq(z−c))·(z−c)·m(z) = −π·Res_c m` (the integrand the global ledger transports);
  * `continuous_radialDerivForm` / `hasCompactSupport_radialDerivForm` — the reusable
    continuity/support kit for `η′(normSq(·−c))·F`-shaped integrands.

  Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §10, computation (10.21) inside
  the proof of the Residue Theorem (text p. 80).
-/
import Jacobians.PlanarStokes.AnnulusResidueIntegral

-- The ℂ-as-ℝ-module diamond fix used across the Dolbeault tree (see `AnnulusResidueIntegral`).
set_option backward.isDefEq.respectTransparency false

open Complex Metric MeasureTheory Filter Set Topology
open scoped Real

namespace Jacobians.Dolbeault

open FormTracePrincipalPart

/-! ### §A1 — the radial cutoff is globally `C¹`, and basic annulus geometry -/

/-- The shifted squared modulus `w ↦ normSq (w − c)` is `C^∞` (a real polynomial in `re`/`im`). -/
theorem contDiff_normSq_sub (c : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w : ℂ => Complex.normSq (w - c)) := by
  have heq : (fun w : ℂ => Complex.normSq (w - c))
      = fun w : ℂ => (w - c).re * (w - c).re + (w - c).im * (w - c).im := by
    funext w
    simp [Complex.normSq_apply]
  rw [heq]
  have hre : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℂ => (w - c).re) :=
    (Complex.reCLM.contDiff).comp (contDiff_id.sub contDiff_const)
  have him : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℂ => (w - c).im) :=
    (Complex.imCLM.contDiff).comp (contDiff_id.sub contDiff_const)
  exact (hre.mul hre).add (him.mul him)

/-- The complexified radial cutoff `χ = η(normSq(·−c))` is globally `C¹`. -/
theorem contDiff_radialCutoff {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η) (c : ℂ) :
    ContDiff ℝ 1 (fun w : ℂ => (η (Complex.normSq (w - c)) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (hη.comp ((contDiff_normSq_sub c).of_le (by simp)))

/-- `normSq (z − c) ≤ s₁ < r²` puts `z` in the metric ball `ball c r`. -/
theorem mem_ball_of_normSq_le {c z : ℂ} {s₁ r : ℝ} (hr : 0 < r) (hs₁r : s₁ < r ^ 2)
    (hz : Complex.normSq (z - c) ≤ s₁) : z ∈ ball c r := by
  rw [mem_ball, Complex.dist_eq]
  have habs : Complex.normSq (z - c) = ‖z - c‖ ^ 2 := Complex.normSq_eq_norm_sq (z - c)
  nlinarith [norm_nonneg (z - c)]

/-- `z` outside the closed `√s₁`-ball means `normSq (z − c) > s₁`. -/
theorem normSq_gt_of_notMem_closedBall {c z : ℂ} {s₁ : ℝ} (hs₁ : 0 ≤ s₁)
    (hz : z ∉ closedBall c (Real.sqrt s₁)) : s₁ < Complex.normSq (z - c) := by
  rw [mem_closedBall, not_le, Complex.dist_eq] at hz
  have habs : Complex.normSq (z - c) = ‖z - c‖ ^ 2 := Complex.normSq_eq_norm_sq (z - c)
  nlinarith [Real.sq_sqrt hs₁, Real.sqrt_nonneg s₁, norm_nonneg (z - c)]

/-- The region `normSq (· − c) > s₁` is open: a strict bound at `z` holds near `z`. -/
theorem eventually_normSq_gt {c z : ℂ} {s₁ : ℝ} (hz : s₁ < Complex.normSq (z - c)) :
    ∀ᶠ w in 𝓝 z, s₁ < Complex.normSq (w - c) := by
  have hcont : ContinuousAt (fun w : ℂ => Complex.normSq (w - c)) z :=
    (contDiff_normSq_sub c).continuous.continuousAt
  filter_upwards [hcont.preimage_mem_nhds (Ioi_mem_nhds hz)] with w hw
  exact hw

/-- The region `normSq (· − c) < s₀` is open: a strict bound at `z` holds near `z`. -/
theorem eventually_normSq_lt {c z : ℂ} {s₀ : ℝ} (hz : Complex.normSq (z - c) < s₀) :
    ∀ᶠ w in 𝓝 z, Complex.normSq (w - c) < s₀ := by
  have hcont : ContinuousAt (fun w : ℂ => Complex.normSq (w - c)) z :=
    (contDiff_normSq_sub c).continuous.continuousAt
  filter_upwards [hcont.preimage_mem_nhds (Iio_mem_nhds hz)] with w hw
  exact hw

/-! ### §A2 — the continuity/support kit for `η′(normSq(·−c))·F` closed forms

The global ledger's planar integrands all have the shape `η′(normSq(z−c)) · F z` with `F`
continuous on a punctured ball covering the closed annulus.  The profile derivative vanishes
identically below `s₀` and above `s₁`, killing both the singularity of `F` at `c` AND any junk
values of `F` far away — so the product is continuous on ALL of `ℂ` and compactly supported. -/

/-- Pointwise vanishing of the profile derivative below `s₀`. -/
theorem radialDeriv_eq_zero_of_lt {η : ℝ → ℝ} {s₀ : ℝ} (h1 : ∀ s ≤ s₀, η s = 1)
    {c z : ℂ} (hz : Complex.normSq (z - c) < s₀) :
    deriv η (Complex.normSq (z - c)) = 0 :=
  deriv_profile_eq_zero_left h1 hz

/-- Pointwise vanishing of the profile derivative above `s₁`. -/
theorem radialDeriv_eq_zero_of_gt {η : ℝ → ℝ} {s₁ : ℝ} (h0 : ∀ s, s₁ ≤ s → η s = 0)
    {c z : ℂ} (hz : s₁ < Complex.normSq (z - c)) :
    deriv η (Complex.normSq (z - c)) = 0 :=
  deriv_profile_eq_zero_right h0 hz

/-- **Continuity of `η′(normSq(·−c))·F`-shaped closed forms.**  `F` only needs continuity at the
points of the OPEN punctured region `0 < normSq(·−c) < s₂` (`s₁ < s₂`): below `s₀` and above `s₁`
the profile-derivative factor vanishes identically (`0 < s₀`, profile `1 → 0`), so junk values of
`F` at the centre or far away are killed. -/
theorem continuous_radialDerivForm {η : ℝ → ℝ} {s₀ s₁ s₂ : ℝ} (hη : ContDiff ℝ 1 η)
    (hs₀ : 0 < s₀) (hs₂ : s₁ < s₂)
    (h1 : ∀ s ≤ s₀, η s = 1) (h0 : ∀ s, s₁ ≤ s → η s = 0) (c : ℂ) {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, z ≠ c → Complex.normSq (z - c) < s₂ → ContinuousAt F z) :
    Continuous fun z : ℂ => Complex.ofReal (deriv η (Complex.normSq (z - c))) * F z := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hgt : s₁ < Complex.normSq (z - c)
  · -- above `s₁`: the form vanishes on the open region `normSq > s₁`
    have hev : (fun w : ℂ => Complex.ofReal (deriv η (Complex.normSq (w - c))) * F w)
        =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [eventually_normSq_gt hgt] with w hw
      rw [radialDeriv_eq_zero_of_gt h0 hw, Complex.ofReal_zero, zero_mul]
    exact continuousAt_const.congr hev.symm
  · push Not at hgt
    by_cases hzc : z = c
    · -- at the centre: the form vanishes on the open region `normSq < s₀`
      have hlt : Complex.normSq (z - c) < s₀ := by simp [hzc, hs₀]
      have hev : (fun w : ℂ => Complex.ofReal (deriv η (Complex.normSq (w - c))) * F w)
          =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [eventually_normSq_lt hlt] with w hw
        rw [radialDeriv_eq_zero_of_lt h1 hw, Complex.ofReal_zero, zero_mul]
      exact continuousAt_const.congr hev.symm
    · -- the honest region: product of continuous factors
      have hlt : Complex.normSq (z - c) < s₂ := lt_of_le_of_lt hgt hs₂
      have hd : ContinuousAt (fun w : ℂ =>
          Complex.ofReal (deriv η (Complex.normSq (w - c)))) z :=
        Complex.continuous_ofReal.continuousAt.comp
          (((hη.continuous_deriv le_rfl).comp
            (contDiff_normSq_sub c).continuous).continuousAt)
      exact hd.mul (hF z hzc hlt)

/-- **Compact support of `η′(normSq(·−c))·F`-shaped closed forms** (support inside the closed
`√s₁`-ball). -/
theorem hasCompactSupport_radialDerivForm {η : ℝ → ℝ} {s₁ : ℝ}
    (h0 : ∀ s, s₁ ≤ s → η s = 0) (hs₁ : 0 ≤ s₁) (c : ℂ) (F : ℂ → ℂ) :
    HasCompactSupport fun z : ℂ => Complex.ofReal (deriv η (Complex.normSq (z - c))) * F z := by
  refine HasCompactSupport.intro (isCompact_closedBall c (Real.sqrt s₁)) ?_
  intro z hz
  rw [radialDeriv_eq_zero_of_gt h0 (normSq_gt_of_notMem_closedBall hs₁ hz),
    Complex.ofReal_zero, zero_mul]

/-! ### §A3 — the junk-repaired analytic complement `G` -/

/-- The `negTail` is analytic at every point OTHER than its centre (each term is a constant times
a `zpow` of `(· − c)`, nonvanishing base). -/
theorem analyticAt_negTail_self_punctured (c : ℂ) (b : ℕ → ℂ) (N : ℕ) {z : ℂ} (hz : z ≠ c) :
    AnalyticAt ℂ (negTail c b N) z :=
  analyticAt_negTail_of_ne b N hz

section PrincipalSplit

variable {m : ℂ → ℂ} {c : ℂ} {r : ℝ}

/-- **The junk-repaired analytic complement.**  Given the principal-part split data
(`exists_principalPart_meromorphicAt`), the function `G := update (m − P) c (R c)` agrees with
`m − P` at every `z ≠ c` *by definition*, and is analytic on the whole ball `ball c r` whenever
`m` is analytic on the punctured ball.  This upgrades the germ-level split to a pointwise global
identity `m = P + G` off `c`. -/
theorem analyticAt_update_complement {N : ℕ} {b : ℕ → ℂ} {R : ℂ → ℂ}
    (hR_an : AnalyticAt ℂ R c)
    (hsplit : m =ᶠ[𝓝[≠] c] fun z => negTail c b N z + R z)
    (hman : ∀ z ∈ ball c r \ {c}, AnalyticAt ℂ m z) :
    ∀ z ∈ ball c r, AnalyticAt ℂ
      (Function.update (fun w => m w - negTail c b N w) c (R c)) z := by
  set P := negTail c b N with hP
  set G := Function.update (fun w => m w - P w) c (R c) with hG
  have hGoff : ∀ w : ℂ, w ≠ c → G w = m w - P w := fun w hw =>
    Function.update_of_ne hw _ _
  intro z hzball
  by_cases hzc : z = c
  · -- at the centre: `G` is germ-equal to the analytic remainder `R`
    subst hzc
    refine hR_an.congr ?_
    have hne : ∀ᶠ w in 𝓝[≠] z, G w = R w := by
      filter_upwards [hsplit, self_mem_nhdsWithin] with w hw hwz
      have hwz' : w ≠ z := by simpa using hwz
      rw [hGoff w hwz', hw]
      ring
    have hpt : G z = R z := Function.update_self _ _ _
    have hfull : ∀ᶠ w in 𝓝 z, G w = R w := by
      rw [← nhdsNE_sup_pure z, Filter.eventually_sup]
      exact ⟨hne, Filter.eventually_pure.mpr hpt⟩
    exact (Filter.EventuallyEq.symm hfull)
  · -- off the centre: `G = m − P` near `z`, both analytic
    have hev : G =ᶠ[𝓝 z] fun w => m w - P w := by
      filter_upwards [compl_singleton_mem_nhds hzc] with w hw
      exact hGoff w hw
    refine AnalyticAt.congr ?_ hev.symm
    exact (hman z ⟨hzball, hzc⟩).sub (analyticAt_negTail_self_punctured c b N hzc)

end PrincipalSplit

/-! ### §A4 — the assembled single-pole atom -/

section Atom

variable (c : ℂ) {η : ℝ → ℝ} {s₀ s₁ r : ℝ}

/-- **The Forster (10.21) single-pole atom, meromorphic integrand.**  For a radial `C¹` cutoff
`χ = η(normSq(·−c))` (profile `1 → 0` between `s₀` and `s₁`, `0 < s₀ < s₁`) and `m` meromorphic
at `c`, honestly analytic on a punctured ball of radius `r` dominating the cutoff (`s₁ < r²`),

  `∫_ℂ ∂̄(χ·m) = −π · Res_c m`.

Principal-part split + planar Stokes for the complement + the single-power computation. -/
theorem integral_dbar_radialCutoff_meromorphic (hη : ContDiff ℝ 1 η)
    (hs₀ : 0 < s₀) (hs : s₀ < s₁)
    (h1 : ∀ s ≤ s₀, η s = 1) (h0 : ∀ s, s₁ ≤ s → η s = 0)
    {m : ℂ → ℂ} (hm : MeromorphicAt m c) (hr : 0 < r) (hs₁r : s₁ < r ^ 2)
    (hman : ∀ z ∈ ball c r \ {c}, AnalyticAt ℂ m z) :
    ∫ z : ℂ, DbarDisk.dbar (fun w => (η (Complex.normSq (w - c)) : ℂ) * m w) z
      = -(π : ℂ) * resAt m c := by
  classical
  -- the principal-part split and the junk-repaired complement
  obtain ⟨N, b, R, hR_an, hsplit⟩ := exists_principalPart_meromorphicAt hm
  set χ : ℂ → ℂ := fun w => (η (Complex.normSq (w - c)) : ℂ) with hχ
  set P : ℂ → ℂ := negTail c b N with hPdef
  set G : ℂ → ℂ := Function.update (fun w => m w - P w) c (R c) with hGdef
  have hGoff : ∀ w : ℂ, w ≠ c → G w = m w - P w := fun w hw => Function.update_of_ne hw _ _
  have hmPG : ∀ w : ℂ, w ≠ c → m w = P w + G w := fun w hw => by rw [hGoff w hw]; ring
  have hG_an : ∀ z ∈ ball c r, AnalyticAt ℂ G z :=
    analyticAt_update_complement hR_an hsplit hman
  have hχC1 : ContDiff ℝ 1 χ := contDiff_radialCutoff hη c
  have hs₁pos : 0 < s₁ := lt_trans hs₀ hs
  -- differentiability of the pieces at punctured-ball points
  have hP_diff : ∀ z : ℂ, z ≠ c → DifferentiableAt ℝ (fun w => χ w * P w) z := by
    intro z hz
    exact (hχC1.differentiable one_ne_zero z).mul
      (((analyticAt_negTail_self_punctured c b N hz).differentiableAt).restrictScalars ℝ)
  have hG_diff : ∀ z ∈ ball c r, DifferentiableAt ℝ (fun w => χ w * G w) z := by
    intro z hz
    exact (hχC1.differentiable one_ne_zero z).mul
      (((hG_an z hz).differentiableAt).restrictScalars ℝ)
  -- vanishing germs above `s₁` (all the cutoff products vanish on the open outer region)
  have houter : ∀ (F : ℂ → ℂ) {z : ℂ}, s₁ < Complex.normSq (z - c) →
      (fun w => χ w * F w) =ᶠ[𝓝 z] fun _ => 0 := by
    intro F z hgt
    filter_upwards [eventually_normSq_gt hgt] with w hw
    show (η (Complex.normSq (w - c)) : ℂ) * F w = 0
    rw [h0 _ hw.le, Complex.ofReal_zero, zero_mul]
  -- (δ1) pointwise additivity of `∂̄` off the centre
  have hδ1 : ∀ z : ℂ, z ≠ c →
      DbarDisk.dbar (fun w => χ w * m w) z
        = DbarDisk.dbar (fun w => χ w * P w) z + DbarDisk.dbar (fun w => χ w * G w) z := by
    intro z hz
    by_cases hball : z ∈ ball c r
    · have hcongr : (fun w => χ w * m w) =ᶠ[𝓝 z]
          fun w => χ w * P w + χ w * G w := by
        filter_upwards [compl_singleton_mem_nhds hz] with w hw
        rw [hmPG w hw]
        ring
      rw [DbarDisk.dbar_congr hcongr]
      exact DbarDisk.dbar_fun_add (hP_diff z hz) (hG_diff z hball)
    · -- outside the ball forces `normSq > s₁`, where everything vanishes identically
      have hgt : s₁ < Complex.normSq (z - c) := by
        by_contra hle
        push Not at hle
        exact hball (mem_ball_of_normSq_le hr hs₁r hle)
      rw [DbarDisk.dbar_congr (houter m hgt), DbarDisk.dbar_congr (houter P hgt),
        DbarDisk.dbar_congr (houter G hgt)]
      simp
  -- (δ2) the complement integral dies by planar Stokes (Forster 10.20)
  have hχG_C1 : ContDiff ℝ 1 (fun w => χ w * G w) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hball : z ∈ ball c r
    · exact (hχC1.contDiffAt).mul
        (ContDiffAt.restrict_scalars ℝ ((hG_an z hball).contDiffAt))
    · have hgt : s₁ < Complex.normSq (z - c) := by
        by_contra hle
        push Not at hle
        exact hball (mem_ball_of_normSq_le hr hs₁r hle)
      exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const (houter G hgt)
  have hχG_supp : HasCompactSupport (fun w => χ w * G w) := by
    refine HasCompactSupport.intro (isCompact_closedBall c (Real.sqrt s₁)) ?_
    intro z hz
    have hgt : s₁ < Complex.normSq (z - c) := normSq_gt_of_notMem_closedBall hs₁pos.le hz
    show (η (Complex.normSq (z - c)) : ℂ) * G z = 0
    rw [h0 _ hgt.le, Complex.ofReal_zero, zero_mul]
  have hG_int : (∫ z : ℂ, DbarDisk.dbar (fun w => χ w * G w) z) = 0 :=
    integral_dbar_eq_zero _ hχG_C1 hχG_supp
  -- (δ3) the principal-part integral: termwise single-power computations
  -- closed form of each term (continuous, compactly supported) for the sum/integral swap
  have hterm_ae : ∀ k ∈ Finset.Icc 1 N,
      (fun z => DbarDisk.dbar (fun w => χ w * (b k * (w - c) ^ (-(k : ℤ)))) z)
        =ᵐ[volume] fun z => b k * (Complex.ofReal (deriv η (Complex.normSq (z - c)))
          * (z - c) ^ (-(k : ℤ) + 1)) := by
    intro k _
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton c)] with z hz
    have hcongr : (fun w => χ w * (b k * (w - c) ^ (-(k : ℤ))))
        =ᶠ[𝓝 z] fun w => b k * (χ w * (w - c) ^ (-(k : ℤ))) :=
      Filter.Eventually.of_forall fun w => by ring
    rw [DbarDisk.dbar_congr hcongr,
      DbarDisk.dbar_fun_const_mul (b k)
        (f := fun w => (η (Complex.normSq (w - c)) : ℂ) * (w - c) ^ (-(k : ℤ)))
        ((differentiableAt_comp_normSq hη c z).mul
          (((differentiableAt_zpow_sub c (-(k : ℤ)) hz)).restrictScalars ℝ)),
      dbar_radialProfile_mul_zpow hη c (-(k : ℤ)) hz]
  have hterm_cont : ∀ k : ℕ, Continuous fun z =>
      Complex.ofReal (deriv η (Complex.normSq (z - c))) * (z - c) ^ (-(k : ℤ) + 1) := by
    intro k
    refine continuous_radialDerivForm (s₂ := r ^ 2) hη hs₀ hs₁r h1 h0 c
      (F := fun z => (z - c) ^ (-(k : ℤ) + 1)) (fun z hz _ => ?_)
    exact ((differentiableAt_zpow_sub c (-(k : ℤ) + 1) hz).continuousAt)
  have hterm_supp : ∀ k : ℕ, HasCompactSupport fun z =>
      Complex.ofReal (deriv η (Complex.normSq (z - c))) * (z - c) ^ (-(k : ℤ) + 1) :=
    fun k => hasCompactSupport_radialDerivForm h0 hs₁pos.le c _
  have hterm_intble : ∀ k ∈ Finset.Icc 1 N,
      Integrable (fun z => DbarDisk.dbar (fun w => χ w * (b k * (w - c) ^ (-(k : ℤ)))) z)
        volume := by
    intro k hk
    refine Integrable.congr ?_ (hterm_ae k hk).symm
    exact (((hterm_cont k).integrable_of_hasCompactSupport (hterm_supp k)).const_mul (b k))
  -- the pointwise expansion of `∂̄(χ·P)` into the terms, off the centre
  have hP_expand : ∀ z : ℂ, z ≠ c →
      DbarDisk.dbar (fun w => χ w * P w) z
        = ∑ k ∈ Finset.Icc 1 N,
            DbarDisk.dbar (fun w => χ w * (b k * (w - c) ^ (-(k : ℤ)))) z := by
    intro z hz
    have hcongr : (fun w => χ w * P w)
        =ᶠ[𝓝 z] fun w => ∑ k ∈ Finset.Icc 1 N, χ w * (b k * (w - c) ^ (-(k : ℤ))) := by
      refine Filter.Eventually.of_forall fun w => ?_
      show χ w * negTail c b N w = _
      simp only [negTail, Finset.mul_sum]
    rw [DbarDisk.dbar_congr hcongr]
    refine DbarDisk.dbar_fun_sum fun k _ => ?_
    exact (hχC1.differentiable one_ne_zero z).mul
      ((((differentiableAt_zpow_sub c (-(k : ℤ)) hz).const_mul (b k))).restrictScalars ℝ)
  have hP_int : (∫ z : ℂ, DbarDisk.dbar (fun w => χ w * P w) z)
      = ∑ k ∈ Finset.Icc 1 N, b k * (if k = 1 then -(π : ℂ) else 0) := by
    have hae : (fun z => DbarDisk.dbar (fun w => χ w * P w) z)
        =ᵐ[volume] fun z => ∑ k ∈ Finset.Icc 1 N,
            DbarDisk.dbar (fun w => χ w * (b k * (w - c) ^ (-(k : ℤ)))) z := by
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton c)] with z hz
      exact hP_expand z hz
    rw [integral_congr_ae hae, integral_finsetSum _ hterm_intble]
    refine Finset.sum_congr rfl fun k hk => ?_
    -- each term: pull the constant out and use the single-power computation
    have hconst_ae : (fun z => DbarDisk.dbar (fun w => χ w * (b k * (w - c) ^ (-(k : ℤ)))) z)
        =ᵐ[volume] fun z =>
          b k * DbarDisk.dbar (fun w => χ w * (w - c) ^ (-(k : ℤ))) z := by
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton c)] with z hz
      have hcongr : (fun w => χ w * (b k * (w - c) ^ (-(k : ℤ))))
          =ᶠ[𝓝 z] fun w => b k * (χ w * (w - c) ^ (-(k : ℤ))) :=
        Filter.Eventually.of_forall fun w => by ring
      rw [DbarDisk.dbar_congr hcongr,
        DbarDisk.dbar_fun_const_mul (b k)
          (f := fun w => (η (Complex.normSq (w - c)) : ℂ) * (w - c) ^ (-(k : ℤ)))
          ((differentiableAt_comp_normSq hη c z).mul
            (((differentiableAt_zpow_sub c (-(k : ℤ)) hz)).restrictScalars ℝ))]
    rw [integral_congr_ae hconst_ae, integral_const_mul,
      integral_dbar_radialCutoff_zpow c hη hs₀ hs h1 h0 k]
  -- (δ4) the residue of `m` is the principal part's `b 1` coefficient
  have hres : resAt m c = ∑ k ∈ Finset.Icc 1 N, b k * (if k = 1 then 1 else 0) := by
    have hcongr : m =ᶠ[𝓝[≠] c] fun w => P w + G w := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact hmPG w (by simpa using hw)
    have hPholo : HoloPunctured P c := by
      refine ⟨1, one_pos, fun z hz => ?_⟩
      exact (analyticAt_negTail_self_punctured c b N
        (Set.mem_singleton_iff.not.mp hz.2)).differentiableAt
    have hGholo : HoloPunctured G c :=
      ⟨r, hr, fun z hz => (hG_an z hz.1).differentiableAt⟩
    have hadd : resAt (fun w => P w + G w) c = resAt P c + resAt G c := by
      have h := resAt_add hPholo hGholo
      simpa [Pi.add_def] using h
    have hsum := resAt_finset_sum (Finset.Icc 1 N)
      (fun k => fun z => b k * (z - c) ^ (-(k : ℤ)))
      (fun k _ => holoPunctured_const_mul_zpow (b k) c (-(k : ℤ)))
    have hresP : resAt P c = ∑ k ∈ Finset.Icc 1 N, b k * (if k = 1 then 1 else 0) := by
      calc resAt P c
          = resAt (fun z => ∑ k ∈ Finset.Icc 1 N, b k * (z - c) ^ (-(k : ℤ))) c := rfl
        _ = ∑ k ∈ Finset.Icc 1 N, resAt (fun z => b k * (z - c) ^ (-(k : ℤ))) c := hsum
        _ = ∑ k ∈ Finset.Icc 1 N, b k * (if k = 1 then 1 else 0) :=
            Finset.sum_congr rfl fun k _ => resAt_const_mul_zpow_neg (b k) c k
    have hresG : resAt G c = 0 :=
      resAt_eq_zero_of_differentiableOn_ball hr fun z hz => (hG_an z hz).differentiableAt
    rw [resAt_congr hcongr, hadd, hresP, hresG, add_zero]
  -- assemble
  have hae_main : (fun z => DbarDisk.dbar (fun w => χ w * m w) z)
      =ᵐ[volume] fun z => DbarDisk.dbar (fun w => χ w * P w) z
        + DbarDisk.dbar (fun w => χ w * G w) z := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton c)] with z hz
    exact hδ1 z hz
  have hP_intble : Integrable (fun z => DbarDisk.dbar (fun w => χ w * P w) z) volume := by
    have hae : (fun z => DbarDisk.dbar (fun w => χ w * P w) z)
        =ᵐ[volume] fun z => ∑ k ∈ Finset.Icc 1 N,
            DbarDisk.dbar (fun w => χ w * (b k * (w - c) ^ (-(k : ℤ)))) z := by
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton c)] with z hz
      exact hP_expand z hz
    exact Integrable.congr (integrable_finsetSum _ hterm_intble) hae.symm
  have hG_intble : Integrable (fun z => DbarDisk.dbar (fun w => χ w * G w) z) volume := by
    have hcont : Continuous fun z => DbarDisk.dbar (fun w => χ w * G w) z := by
      rw [continuous_iff_continuousAt]
      exact fun z => DbarDisk.continuousAt_dbar_of_contDiffAt hχG_C1.contDiffAt
    have hsupp : HasCompactSupport fun z => DbarDisk.dbar (fun w => χ w * G w) z := by
      refine HasCompactSupport.intro (isCompact_closedBall c (Real.sqrt s₁)) ?_
      intro z hz
      have hgt : s₁ < Complex.normSq (z - c) := normSq_gt_of_notMem_closedBall hs₁pos.le hz
      rw [DbarDisk.dbar_congr (houter G hgt)]
      simp
    exact hcont.integrable_of_hasCompactSupport hsupp
  rw [integral_congr_ae hae_main, integral_add hP_intble hG_intble, hG_int, add_zero, hP_int,
    hres, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases eq_or_ne k 1 with hk1 | hk1
  · rw [hk1, if_pos rfl, if_pos rfl]
    ring
  · rw [if_neg hk1, if_neg hk1]
    ring

/-- **The closed-form version of the single-pole atom** — the integrand the global ledger
transports between charts:

  `∫_ℂ η′(normSq(z−c)) · (z−c) · m(z) = −π · Res_c m`.

Off the centre this is literally `∂̄(χ·m)` (Leibniz + holomorphy of `m`), and the centre is a
null set. -/
theorem integral_radialDeriv_mul_eq_resAt (hη : ContDiff ℝ 1 η)
    (hs₀ : 0 < s₀) (hs : s₀ < s₁)
    (h1 : ∀ s ≤ s₀, η s = 1) (h0 : ∀ s, s₁ ≤ s → η s = 0)
    {m : ℂ → ℂ} (hm : MeromorphicAt m c) (hr : 0 < r) (hs₁r : s₁ < r ^ 2)
    (hman : ∀ z ∈ ball c r \ {c}, AnalyticAt ℂ m z) :
    ∫ z : ℂ, (Complex.ofReal (deriv η (Complex.normSq (z - c))) * (z - c) * m z)
      = -(π : ℂ) * resAt m c := by
  rw [← integral_dbar_radialCutoff_meromorphic c hη hs₀ hs h1 h0 hm hr hs₁r hman]
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton c)] with z hz
  by_cases hball : z ∈ ball c r
  · -- Leibniz: `∂̄(χ·m) = χ·∂̄m + m·∂̄χ = m·η′(normSq)·(z−c)`
    have hm_diff : DifferentiableAt ℂ m z := (hman z ⟨hball, hz⟩).differentiableAt
    rw [DbarDisk.dbar_fun_mul (differentiableAt_comp_normSq hη c z)
        (hm_diff.restrictScalars ℝ),
      DbarDisk.dbar_eq_zero_of_differentiableAt hm_diff, mul_zero, zero_add,
      dbar_comp_normSq hη c z]
    ring
  · -- outside the ball: `normSq > s₁`, both sides vanish
    have hgt : s₁ < Complex.normSq (z - c) := by
      by_contra hle
      push Not at hle
      exact hball (mem_ball_of_normSq_le hr hs₁r hle)
    have houter : (fun w => (η (Complex.normSq (w - c)) : ℂ) * m w) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [eventually_normSq_gt hgt] with w hw
      rw [h0 _ hw.le, Complex.ofReal_zero, zero_mul]
    rw [radialDeriv_eq_zero_of_gt h0 hgt, DbarDisk.dbar_congr houter,
      Complex.ofReal_zero, zero_mul, zero_mul]
    simp

end Atom

end Jacobians.Dolbeault
