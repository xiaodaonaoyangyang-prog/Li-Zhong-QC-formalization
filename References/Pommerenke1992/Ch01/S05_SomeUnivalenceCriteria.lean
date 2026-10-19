import References.Pommerenke1992.Ch01.S04_SequencesOfConformalMaps
import LiZhongQC.Ch05.S20_SchwarzDomains

/-!
# Pommerenke 1992, Ch. 1 §1.5 Some Univalence Criteria

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §1.5; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 882–962.

* Theorem 1.9 — `thm1_9`
* Boundary principle (a named consequence of Corollary 2.10, §1.5) — `boundary_principle`
* Proposition 1.10 — `prop1_10_a`, `prop1_10_b`
* Theorem 1.11 (Becker's univalence criterion) — `thm1_11_a`, `thm1_11_b`
* Theorem 1.12 (Nehari's univalence criterion) — `thm1_12_a`, `thm1_12_b`, `thm1_12_c`
* Epstein's univalence criterion (quoted, §1.5) — `epstein_criterion`

The two-part results are split into their independent parts: the criterion and the sharpness of its constant
(Theorems 1.11 and 1.12, with the pole statement of 1.12 as a third part), and the univalence and Jordan-image parts
of Proposition 1.10.

Not items (DESIGN §3): (1.5.4), `Re[(f(z₂) - f(z₁))/(z₂ - z₁)] > 0` in a convex domain (a step inside the proof of
Proposition 1.10; the proof of Proposition 3.20 cites it again, l. 2899); the remarks on the methods of proof of
Theorems 1.11, 1.12 and of Epstein's criterion.
-/

open Complex Set Metric Filter Topology
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsJordanCurve IsJordanDomain schwarzian IsLocUnivMero
  IsUnivMero)
open LehtoVirtanen1973 (IsSimplyConnectedDomain localRep)

/-- **Theorem 1.9** (§1.5). Let `f` be nonconstant and analytic in the domain `H ⊆ Ĉ` and let `G` be the inner domain
of the Jordan curve `J`. If (1.5.1) `f(z) → J` as `z → ∂H` — that is, if `(zₙ)` is any sequence in `H` whose limit
points lie on `∂H`, then all limit points of `(f(zₙ))` lie on `J` — then `f(H) = G`. If furthermore `f` assumes in
`H` some value of `G` only once (with multiplicity 1), then `f` is injective and `H` is simply connected.
Modelling:
- `H` is a domain of the sphere, and `f : Ĉ → Ĉ` has finite values in `H` and is analytic in the charts of the
  sphere (`LehtoVirtanen1973.localRep`, which covers `∞ ∈ H`); `J ⊆ ℂ`.
- Limit points of sequences are cluster points in `Ĉ`.
- Multiplicity 1 is a non-vanishing derivative in the chart. -/
theorem thm1_9 {H : Set ExtPlane} (hH : References.IsDomainExt H) {f : ExtPlane → ExtPlane}
    (hfin : ∀ z ∈ H, f z ≠ extInf) (hcont : ContinuousOn f H)
    (han : ∀ z ∈ H, DifferentiableAt ℂ (localRep f z) 0) (hnc : ∃ z₁ ∈ H, ∃ z₂ ∈ H, f z₁ ≠ f z₂)
    {J : Set ℂ} (hJ : IsJordanCurve (toExt J))
    (hbd : ∀ z : ℕ → ExtPlane, (∀ n, z n ∈ H) → (∀ p, MapClusterPt p atTop z → p ∈ frontier H) →
      ∀ q, MapClusterPt q atTop (f ∘ z) → q ∈ toExt J) :
    f '' H = toExt (innerDomain J) ∧
      ((∃ v ∈ innerDomain J, ∃ z ∈ H, f z = v ∧ deriv (localRep f z) 0 ≠ 0 ∧ ∀ z' ∈ H, f z' = v → z' = z) →
        InjOn f H ∧ IsSimplyConnectedDomain H) := by
  sorry

/-- **Boundary principle** (§1.5, l. 910; a consequence of Corollary 2.10). If `f` is analytic in `𝔻` and continuous
and injective on `𝕋`, then `f` is injective also in `𝔻`.
Modelling: `f` is continuous on the closed disc, the boundary values being its values on `𝕋`. -/
theorem boundary_principle {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hcont : ContinuousOn f (closedBall 0 1)) (hinj : InjOn f (sphere 0 1)) : InjOn f unitDisc := by
  sorry

/-- The chord argument of Proposition 1.10 ((1.5.4)): if `f` is continuous on the segment `[z₁, z₂]`, `z₁ ≠ z₂`, and
complex differentiable with `Re f' > 0` at its interior points, then `f(z₁) ≠ f(z₂)`: the real function
`t ↦ Re (f(z₁ + t(z₂ - z₁))/(z₂ - z₁))` is strictly increasing on `[0, 1]`. -/
theorem p92_1_ne_of_re_deriv_pos {f : ℂ → ℂ} {z₁ z₂ : ℂ} (hne : z₁ ≠ z₂)
    (hc : ContinuousOn (fun t : ℝ => f (z₁ + (t : ℂ) * (z₂ - z₁))) (Icc 0 1))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℂ f (z₁ + (t : ℂ) * (z₂ - z₁)) ∧
      0 < (deriv f (z₁ + (t : ℂ) * (z₂ - z₁))).re) : f z₁ ≠ f z₂ := by
  intro heq
  have hd0 : z₂ - z₁ ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hder : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun s : ℝ => (f (z₁ + (s : ℂ) * (z₂ - z₁)) / (z₂ - z₁)).re)
      (deriv f (z₁ + (t : ℂ) * (z₂ - z₁))).re t := by
    intro t ht
    have hfd : HasDerivAt f (deriv f (z₁ + (t : ℂ) * (z₂ - z₁))) (z₁ + (t : ℂ) * (z₂ - z₁)) :=
      (hd t ht).1.hasDerivAt
    have hlin : HasDerivAt (fun w : ℂ => z₁ + w * (z₂ - z₁)) (z₂ - z₁) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const (z₂ - z₁)).const_add z₁
    have hE : HasDerivAt (fun w : ℂ => f (z₁ + w * (z₂ - z₁)) / (z₂ - z₁))
        (deriv f (z₁ + (t : ℂ) * (z₂ - z₁))) (t : ℂ) := by
      have h := (hfd.comp (t : ℂ) hlin).div_const (z₂ - z₁)
      rwa [mul_div_assoc, div_self hd0, mul_one] at h
    exact hE.real_of_complex
  have hmono : StrictMonoOn (fun s : ℝ => (f (z₁ + (s : ℂ) * (z₂ - z₁)) / (z₂ - z₁)).re) (Icc 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 1)
      (Complex.continuous_re.comp_continuousOn (hc.div_const _)) fun t ht => ?_
    rw [interior_Icc] at ht
    rw [(hder t ht).deriv]
    exact (hd t ht).2
  have hlt := hmono (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_lt_one
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.ofReal_one, one_mul, add_sub_cancel] at hlt
  rw [heq] at hlt
  exact lt_irrefl _ hlt

/-- **Proposition 1.10** (§1.5), first part. Let `f` be analytic in the convex domain `H`. If (1.5.3)
`Re f'(z) > 0` for `z ∈ H`, then `f` is univalent in `H`. -/
theorem prop1_10_a {H : Set ℂ} (hHo : IsOpen H) (hHc : Convex ℝ H) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f H)
    (hre : ∀ z ∈ H, 0 < (deriv f z).re) : InjOn f H := by
  intro z₁ h₁ z₂ h₂ heq
  by_contra hne
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, z₁ + (t : ℂ) * (z₂ - z₁) ∈ H := by
    intro t ht
    have := hHc.add_smul_sub_mem h₁ h₂ ht
    simpa [Complex.real_smul] using this
  exact p92_1_ne_of_re_deriv_pos hne (hf.continuousOn.comp (by fun_prop) fun t ht => hseg t ht)
    (fun t ht => ⟨hf.differentiableAt (hHo.mem_nhds (hseg t (Ioo_subset_Icc_self ht))),
      hre _ (hseg t (Ioo_subset_Icc_self ht))⟩) heq

/-- **Proposition 1.10** (§1.5), second part. If `H = 𝔻`, (1.5.3) holds and `f` is continuous in `𝔻̄`, then `f(𝔻)`
is a Jordan domain. -/
theorem prop1_10_b {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hre : ∀ z ∈ unitDisc, 0 < (deriv f z).re)
    (hcont : ContinuousOn f (closedBall 0 1)) : IsJordanDomain (f '' unitDisc) := by
  have hKcv : StrictConvex ℝ (closedBall (0 : ℂ) 1) := strictConvex_closedBall ℝ 0 1
  -- `f` is injective on the closed disc: the open chords lie in `𝔻` (strict convexity)
  have hinjK : InjOn f (closedBall 0 1) := by
    intro z₁ h₁ z₂ h₂ heq
    by_contra hne
    have hseg : ∀ t ∈ Icc (0 : ℝ) 1, z₁ + (t : ℂ) * (z₂ - z₁) ∈ closedBall (0 : ℂ) 1 := by
      intro t ht
      have := (convex_closedBall (0 : ℂ) 1).add_smul_sub_mem h₁ h₂ ht
      simpa [Complex.real_smul] using this
    have hopen : ∀ t ∈ Ioo (0 : ℝ) 1, z₁ + (t : ℂ) * (z₂ - z₁) ∈ unitDisc := by
      intro t ht
      have hmem : z₁ + (t : ℂ) * (z₂ - z₁) ∈ openSegment ℝ z₁ z₂ := by
        rw [openSegment_eq_image']
        exact ⟨t, ht, by simp [Complex.real_smul]⟩
      have := hKcv.openSegment_subset h₁ h₂ hne hmem
      rwa [interior_closedBall (0 : ℂ) one_ne_zero] at this
    refine p92_1_ne_of_re_deriv_pos hne (hcont.comp (by fun_prop) fun t ht => hseg t ht)
      (fun t ht => ⟨hf.differentiableAt (isOpen_ball.mem_nhds (hopen t ht)), hre _ (hopen t ht)⟩) heq
  have hinj : InjOn f unitDisc := hinjK.mono ball_subset_closedBall
  have hconf : LiZhongQC.IsConformalOnto f unitDisc (f '' unitDisc) := ⟨hf, hinj, rfl⟩
  have hVo : IsOpen (f '' unitDisc) := hconf.isOpen isOpen_ball
  have hVc : IsConnected (f '' unitDisc) := (isConnected_ball one_pos).image f hf.continuousOn
  have hKc : IsCompact (f '' closedBall 0 1) := (isCompact_closedBall 0 1).image_of_continuousOn hcont
  have hVb : Bornology.IsBounded (f '' unitDisc) := hKc.isBounded.subset (image_mono ball_subset_closedBall)
  have hclos : closure (f '' unitDisc) = f '' closedBall 0 1 := by
    refine subset_antisymm (closure_minimal (image_mono ball_subset_closedBall) hKc.isClosed) ?_
    have h := (show ContinuousOn f (closure (ball (0 : ℂ) 1)) by
      rwa [closure_ball (0 : ℂ) one_ne_zero]).image_closure
    rwa [closure_ball (0 : ℂ) one_ne_zero] at h
  have hfront : frontier (f '' unitDisc) = f '' sphere 0 1 := by
    rw [hVo.frontier_eq, hclos]
    ext w
    constructor
    · rintro ⟨⟨z, hzK, rfl⟩, hnot⟩
      refine ⟨z, ?_, rfl⟩
      rw [mem_sphere_zero_iff_norm]
      refine le_antisymm (mem_closedBall_zero_iff.1 hzK) (not_lt.1 fun hlt => hnot ⟨z, ?_, rfl⟩)
      exact mem_ball_zero_iff.2 hlt
    · rintro ⟨z, hzS, rfl⟩
      refine ⟨⟨z, sphere_subset_closedBall hzS, rfl⟩, fun ⟨z', hz', heq⟩ => ?_⟩
      have := hinjK (ball_subset_closedBall hz') (sphere_subset_closedBall hzS) heq
      rw [this] at hz'
      have h' := mem_ball_zero_iff.1 hz'
      rw [mem_sphere_zero_iff_norm.1 hzS] at h'
      exact lt_irrefl _ h'
  refine ⟨hVo, hVc, ?_⟩
  rw [LiZhongQC.frontier_toExt_of_isBounded' hVb hVo, hfront]
  exact LiZhongQC.iod_isJordanCurve_image_sphere one_pos (hcont.mono sphere_subset_closedBall)
    (hinjK.mono sphere_subset_closedBall)

/-- **Theorem 1.11** (§1.5; Becker's univalence criterion), the criterion. Let `f` be analytic and locally univalent
in `𝔻`. If `(1 - |z|²)|z f''(z)/f'(z)| ≤ 1` for `z ∈ 𝔻`, then `f` is univalent in `𝔻`. -/
theorem thm1_11_a {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hloc : ∀ z ∈ unitDisc, deriv f z ≠ 0)
    (hB : ∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) * ‖z * deriv (deriv f) z / deriv f z‖ ≤ 1) : InjOn f unitDisc := by
  sorry

/-- **Theorem 1.11** (§1.5), sharpness: the constant `1` is best possible. For every `c > 1` there is a function `f`,
analytic and locally univalent in `𝔻`, with `(1 - |z|²)|z f''/f'| ≤ c` in `𝔻`, which is not univalent. -/
theorem thm1_11_b {c : ℝ} (hc : 1 < c) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f unitDisc ∧ (∀ z ∈ unitDisc, deriv f z ≠ 0) ∧
      (∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) * ‖z * deriv (deriv f) z / deriv f z‖ ≤ c) ∧ ¬ InjOn f unitDisc := by
  sorry

/-- Dilation: for `0 < r ≤ 1`, `z ↦ f(rz)` is locally univalent and meromorphic in `𝔻` with `f`; at a pole `rz` of `f`
the reciprocal of its normal form is `w ↦ u(rw)`, `u` the reciprocal of the normal form of `f` at `rz`. -/
theorem p92_1_dilate {f : ℂ → ℂ} (hf : IsLocUnivMero f unitDisc) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    IsLocUnivMero (fun w => f (r * w)) unitDisc := by
  have hT : ∀ z : ℂ, AnalyticAt ℂ (fun w : ℂ => (r : ℂ) * w) z := fun z => analyticAt_const.mul analyticAt_id
  have hmem : ∀ z ∈ unitDisc, (r : ℂ) * z ∈ unitDisc := fun z hz => by
    have hz' := mem_ball_zero_iff.1 hz
    refine mem_ball_zero_iff.2 ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    nlinarith [norm_nonneg z]
  have hr0' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hTd : ∀ z : ℂ, deriv (fun w : ℂ => (r : ℂ) * w) z = r := fun z => by
    simp
  refine ⟨fun z hz => (hf.1 _ (hmem z hz)).comp_analyticAt (hT z), fun z hz => ?_⟩
  rcases hf.2 _ (hmem z hz) with ⟨hA, hA'⟩ | ⟨hneg, hu, hu'⟩
  · left
    refine ⟨hA.comp_of_eq (hT z) rfl, ?_⟩
    rw [show (fun w => f (r * w)) = f ∘ fun w : ℂ => (r : ℂ) * w from rfl,
      deriv_comp z hA.differentiableAt (hT z).differentiableAt, hTd]
    exact mul_ne_zero hA' hr0'
  · right
    set p := (r : ℂ) * z with hp
    set u : ℂ → ℂ := fun w => (toMeromorphicNFAt f p w)⁻¹ with hudef
    have hmero := hf.1 p (hmem z hz)
    have hfu : f =ᶠ[𝓝[≠] p] fun w => (u w)⁻¹ := by
      filter_upwards [hmero.eq_nhdsNE_toMeromorphicNFAt] with w hw
      simp only [hudef, inv_inv]
      exact hw
    have hu0 : u p = 0 := by
      have hNA : ¬ AnalyticAt ℂ (toMeromorphicNFAt f p) p := fun hA => by
        have h := meromorphicOrderAt_congr hmero.eq_nhdsNE_toMeromorphicNFAt
        rw [h] at hneg
        exact absurd (meromorphicNFAt_toMeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr hA)
          (not_le.2 hneg)
      rcases meromorphicNFAt_iff_analyticAt_or.mp (meromorphicNFAt_toMeromorphicNFAt (f := f) (x := p)) with
        hA | ⟨-, -, h0⟩
      · exact absurd hA hNA
      · simp [hudef, h0]
    set G : ℂ → ℂ := fun w => u (r * w) with hG
    have hGa : AnalyticAt ℂ G z := hu.comp_of_eq (hT z) rfl
    have hG' : deriv G z ≠ 0 := by
      rw [show G = u ∘ fun w : ℂ => (r : ℂ) * w from rfl,
        deriv_comp z hu.differentiableAt (hT z).differentiableAt, hTd]
      exact mul_ne_zero hu' hr0'
    have hTt : Tendsto (fun w : ℂ => (r : ℂ) * w) (𝓝[≠] z) (𝓝[≠] p) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((hT z).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun w hw h => hw (mul_left_cancel₀ hr0' h))
    have hfG : (fun w => f (r * w)) =ᶠ[𝓝[≠] z] fun w => (G w)⁻¹ := hTt.eventually hfu
    have h1 : meromorphicOrderAt G z = 1 := by
      rw [hGa.meromorphicOrderAt_eq, hGa.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hu0 hG']
      rfl
    have hord : meromorphicOrderAt (fun w => (G w)⁻¹) z = -1 := by
      show meromorphicOrderAt G⁻¹ z = -1
      rw [meromorphicOrderAt_inv, h1]
    have hNF : toMeromorphicNFAt (fun w => f (r * w)) z =ᶠ[𝓝 z] fun w => (G w)⁻¹ := by
      have h := LiZhongQC.toMeromorphicNFAt_congr_nhdsNE hfG
      rwa [(toMeromorphicNFAt_eq_self (f := fun w => (G w)⁻¹) (x := z)).mpr hGa.meromorphicNFAt.inv] at h
    have hinv : (fun w => (toMeromorphicNFAt (fun w => f (r * w)) z w)⁻¹) =ᶠ[𝓝 z] G := by
      filter_upwards [hNF] with w hw
      rw [hw, inv_inv]
    refine ⟨?_, hGa.congr hinv.symm, ?_⟩
    · rw [meromorphicOrderAt_congr hfG, hord]
      decide
    · rw [hinv.deriv_eq]
      exact hG'

/-- Dilation: `S_{f(r·)}(z) = r² S_f(rz)` (`eq1_2_16` with `σ = id`, `τ(z) = rz`). -/
theorem p92_1_dilate_schwarzian {f : ℂ → ℂ} (hf : IsLocUnivMero f unitDisc) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    {z : ℂ} (hz : z ∈ unitDisc) : schwarzian (fun w => f (r * w)) z = r ^ 2 * schwarzian f (r * z) := by
  have hmem : (r : ℂ) * z ∈ unitDisc := by
    have hz' := mem_ball_zero_iff.1 hz
    refine mem_ball_zero_iff.2 ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    nlinarith [norm_nonneg z]
  have h := eq1_2_16 (a := 1) (b := 0) (c := 0) (d := 1) (a' := r) (b' := 0) (c' := 0) (d' := 1) isOpen_ball hf
    (by norm_num) (by simpa using hr0.ne') (z := z) (by norm_num)
    (by simp only [add_zero, zero_mul, zero_add, div_one]; exact hmem)
  have e1 : (fun w : ℂ => (1 * f ((r * w + 0) / (0 * w + 1)) + 0) / (0 * f ((r * w + 0) / (0 * w + 1)) + 1)) =
      fun w => f (r * w) := by
    funext w
    simp
  have e2 : (fun w : ℂ => ((r : ℂ) * w + 0) / (0 * w + 1)) = fun w => (r : ℂ) * w := by
    funext w
    simp
  rw [e1, e2] at h
  have hd : deriv (fun w : ℂ => (r : ℂ) * w) z = r := by
    simp
  rw [h, hd]
  simp only [add_zero, zero_mul, zero_add, div_one]
  ring

/-- **Theorem 1.12** (§1.5; Nehari's univalence criterion), the criterion. Let `f` be meromorphic and locally
univalent in `𝔻`. If `(1 - |z|²)² |S_f(z)| ≤ 2` for `z ∈ 𝔻`, then `f` is univalent in `𝔻`.
Modelling: "meromorphic and locally univalent" is `LiZhongQC.IsLocUnivMero`, "univalent" is `LiZhongQC.IsUnivMero`.
The project's `LiZhongQC.thm20_1_disc_isSchwarz` assumes the strict bound on the supremum and is narrower. -/
theorem thm1_12_a {f : ℂ → ℂ} (hf : IsLocUnivMero f unitDisc)
    (hS : ∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzian f z‖ ≤ 2) : IsUnivMero f unitDisc := by
  -- every dilation `f(r·)`, `0 < r < 1`, satisfies the strict bound of `LiZhongQC.thm20_1_disc_isSchwarz`
  have hfr : ∀ r : ℝ, 0 < r → r < 1 → IsUnivMero (fun w => f (r * w)) unitDisc := by
    intro r hr0 hr1
    have hloc := p92_1_dilate hf hr0 hr1.le
    refine LiZhongQC.thm20_1_disc_isSchwarz.2.2 _ hloc (lt_of_le_of_lt (iSup₂_le fun z hz => ?_)
      ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by nlinarith : r ^ 2 / 2 < 1 / 2)))
    apply ENNReal.ofReal_le_ofReal
    have hz' := mem_ball_zero_iff.1 hz
    have hrz : ‖(r : ℂ) * z‖ = r * ‖z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    have hmem : (r : ℂ) * z ∈ unitDisc := by
      refine mem_ball_zero_iff.2 ?_
      rw [hrz]
      nlinarith [norm_nonneg z]
    have hS' := hS _ hmem
    rw [hrz] at hS'
    have hpos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have hq := norm_nonneg (schwarzian f (r * z))
    have hle1 : (1 - ‖z‖ ^ 2) ^ 2 ≤ (1 - (r * ‖z‖) ^ 2) ^ 2 := by
      apply pow_le_pow_left₀ hpos.le
      nlinarith [norm_nonneg z, mul_le_mul_of_nonneg_right hr1.le (sq_nonneg ‖z‖)]
    have e : ‖schwarzian (fun w => f (r * w)) z‖ / LiZhongQC.poincareDensity unitDisc z ^ 2 =
        r ^ 2 * ((1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzian f (r * z)‖) / 4 := by
      rw [p92_1_dilate_schwarzian hf hr0 hr1.le hz, LiZhongQC.poincareDensity_unitDisc hz,
        LiZhongQC.poincareDensityDisc, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      field_simp
      ring
    rw [e]
    have h2 : (1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzian f (r * z)‖ ≤ 2 :=
      le_trans (mul_le_mul_of_nonneg_right hle1 hq) hS'
    nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg r)]
  -- points of `𝔻` are images `r w` of points of `𝔻` for `r` close to `1`
  have hpick : ∀ z₁ z₂ : ℂ, z₁ ∈ unitDisc → z₂ ∈ unitDisc → ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      z₁ / r ∈ unitDisc ∧ z₂ / r ∈ unitDisc ∧ (r : ℂ) * (z₁ / r) = z₁ ∧ (r : ℂ) * (z₂ / r) = z₂ := by
    intro z₁ z₂ h₁ h₂
    have h₁' := mem_ball_zero_iff.1 h₁
    have h₂' := mem_ball_zero_iff.1 h₂
    set r := (max ‖z₁‖ ‖z₂‖ + 1) / 2 with hr
    have hm : max ‖z₁‖ ‖z₂‖ < 1 := max_lt h₁' h₂'
    have hr0 : 0 < r := by rw [hr]; positivity
    have hr1 : r < 1 := by rw [hr]; linarith
    have hlt₁ : ‖z₁‖ < r := by rw [hr]; linarith [le_max_left ‖z₁‖ ‖z₂‖]
    have hlt₂ : ‖z₂‖ < r := by rw [hr]; linarith [le_max_right ‖z₁‖ ‖z₂‖]
    have hr0' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    refine ⟨r, hr0, hr1, ?_, ?_, mul_div_cancel₀ _ hr0', mul_div_cancel₀ _ hr0'⟩
    · refine mem_ball_zero_iff.2 ?_
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, div_lt_one hr0]
      exact hlt₁
    · refine mem_ball_zero_iff.2 ?_
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, div_lt_one hr0]
      exact hlt₂
  have hT : ∀ (r : ℝ) (w : ℂ), AnalyticAt ℂ (fun v : ℂ => (r : ℂ) * v) w := fun r w =>
    analyticAt_const.mul analyticAt_id
  refine ⟨hf, fun z₁ hz₁ z₂ hz₂ heq => ?_, fun p₁ hp₁ p₂ hp₂ => ?_⟩
  · obtain ⟨r, hr0, hr1, hw₁, hw₂, e₁, e₂⟩ := hpick z₁ z₂ hz₁.1 hz₂.1
    have hA₁ : AnalyticAt ℂ (fun w => f (r * w)) (z₁ / r) := hz₁.2.comp_of_eq (hT r _) e₁
    have hA₂ : AnalyticAt ℂ (fun w => f (r * w)) (z₂ / r) := hz₂.2.comp_of_eq (hT r _) e₂
    have h := (hfr r hr0 hr1).2.1 ⟨hw₁, hA₁⟩ ⟨hw₂, hA₂⟩ (by simp only [e₁, e₂]; exact heq)
    rw [← e₁, ← e₂, h]
  · obtain ⟨r, hr0, hr1, hw₁, hw₂, e₁, e₂⟩ := hpick p₁ p₂ hp₁.1 hp₂.1
    have hr0' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have hnot : ∀ p : ℂ, ¬ AnalyticAt ℂ f p → ¬ AnalyticAt ℂ (fun w => f (r * w)) (p / r) := by
      intro p hp hA
      apply hp
      have hdiv : AnalyticAt ℂ (fun v : ℂ => v / r) p := analyticAt_id.div_const
      have h := hA.comp_of_eq hdiv rfl
      have e : ((fun w => f (r * w)) ∘ fun v : ℂ => v / r) = f := by
        funext v
        simp [mul_div_cancel₀ _ hr0']
      rwa [e] at h
    have h := (hfr r hr0 hr1).2.2 ⟨hw₁, hnot p₁ hp₁.2⟩ ⟨hw₂, hnot p₂ hp₂.2⟩
    rw [← e₁, ← e₂, h]

/-- **Theorem 1.12** (§1.5), sharpness: the bound `2` is best possible. For every `c > 2` there is a locally univalent
meromorphic `f` in `𝔻` with `(1 - |z|²)² |S_f(z)| ≤ c` in `𝔻`, which is not univalent.
Modelling: stated in the book's normalization; the project's `LiZhongQC.thm20_1_not_isSchwarz` is the same fact for
the quarter-normalized norm `LiZhongQC.schwarzianNorm` (constant `1/2`). -/
theorem thm1_12_b {c : ℝ} (hc : 2 < c) :
    ∃ f : ℂ → ℂ, IsLocUnivMero f unitDisc ∧ (∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzian f z‖ ≤ c) ∧
      ¬ IsUnivMero f unitDisc := by
  have h := LiZhongQC.thm20_1_not_isSchwarz (a := c / 4) (by linarith)
  by_contra hcon
  apply h
  refine ⟨LiZhongQC.neh_isHyperbolicSimplyConnected_unitDisc, by linarith, fun f hf hSn => ?_⟩
  by_contra hnu
  apply hcon
  refine ⟨f, hf, fun z hz => ?_, hnu⟩
  have hle : ENNReal.ofReal (‖schwarzian f z‖ / LiZhongQC.poincareDensity unitDisc z ^ 2) ≤
      LiZhongQC.schwarzianNorm f unitDisc := le_iSup₂_of_le z hz le_rfl
  have hlt := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).1 (lt_of_le_of_lt hle hSn)
  have hz' := mem_ball_zero_iff.1 hz
  have hpos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have e : ‖schwarzian f z‖ / LiZhongQC.poincareDensity unitDisc z ^ 2 =
      (1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzian f z‖ / 4 := by
    rw [LiZhongQC.poincareDensity_unitDisc hz, LiZhongQC.poincareDensityDisc]
    field_simp
    ring
  rw [e] at hlt
  linarith

/-- **Theorem 1.12** (§1.5), the pole statement. Under the hypotheses of the criterion, if `f(0) ∈ ℂ` and
`f''(0) = 0`, then `f` has no pole in `𝔻`.
Modelling: `f(0) ∈ ℂ` is analyticity of `f` at `0`; "no pole" is analyticity at every point of `𝔻` (a locally
univalent meromorphic function is analytic or has a pole at each point). -/
theorem thm1_12_c {f : ℂ → ℂ} (hf : IsLocUnivMero f unitDisc)
    (hS : ∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzian f z‖ ≤ 2) (h0 : AnalyticAt ℂ f 0)
    (h2 : deriv (deriv f) 0 = 0) : ∀ z ∈ unitDisc, AnalyticAt ℂ f z := by
  sorry

/-- **Epstein's univalence criterion** (§1.5, quoted). Let `f` be meromorphic and `g` analytic in `𝔻`. If both
functions are locally univalent and if
`|½ (1 - |z|²)² [S_f(z) - S_g(z)] + (1 - |z|²) z̄ g''(z)/g'(z)| ≤ 1` for `z ∈ 𝔻`, then `f` is univalent in `𝔻`. -/
theorem epstein_criterion {f g : ℂ → ℂ} (hf : IsLocUnivMero f unitDisc) (hg : DifferentiableOn ℂ g unitDisc)
    (hg' : ∀ z ∈ unitDisc, deriv g z ≠ 0)
    (hE : ∀ z ∈ unitDisc, ‖1 / 2 * ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) ^ 2 * (schwarzian f z - schwarzian g z) +
      ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * conj z * (deriv (deriv g) z / deriv g z)‖ ≤ 1) :
    IsUnivMero f unitDisc := by
  sorry

end Pommerenke1992
