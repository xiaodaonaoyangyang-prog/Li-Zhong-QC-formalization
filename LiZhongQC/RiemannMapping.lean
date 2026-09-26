/-
# The Riemann Mapping Theorem

A Lean 4 / Mathlib formalization following the extremal (Koebe–Fejér–Riesz) proof, written
blueprint-style: every mathematical step is a named declaration.

## Status

Complete: no `sorry`, and every declaration depends only on `[propext, Classical.choice,
Quot.sound]` (checked with `#print axioms` on all declarations, 2026-09-13).  The file is not
imported by `LiZhongQC.lean`; check it with `lake env lean LiZhongQC/RiemannMapping.lean`.

Changes from the original skeleton:
* `Complex.abs` (removed from Mathlib) is written as the norm `‖·‖`, and `invFunOn` as
  `Function.invFunOn`.
* `derivVal_normalize` has the extra hypothesis `hcomp`; without it the statement is false
  (take `c = -1`).
* `exists_primitive_of_simplyConnected` sits at the end, after the main theorems: it is proved
  from the Riemann map (pull back a primitive on the disc, `DifferentiableOn.isExactOn_ball`)
  instead of by homotopy invariance of contour integrals.
* Helper lemmas were added; no other statement changed.

Routes that differ from the sketches: the bridge `hasHolomorphicSqrt_of_simplyConnected` uses
Mathlib's continuous branches of roots and logarithms (`exists_continuousOn_pow_eq`,
`exists_continuousOn_eqOn_exp_comp`); `hurwitz_injOn` uses the maximum modulus principle instead of
Rouché's theorem; `montel` extracts a subsequence converging on a countable dense set
(`IsCompact.tendsto_subseq`) and upgrades it with Arzelà–Ascoli
(`EquicontinuousOn.tendsto_uniformOnFun_iff_pi'`).

## Design decisions

* Domains are `U : Set ℂ` with `IsOpen U`, and functions are `ℂ → ℂ` constrained by
  `DifferentiableOn ℂ f U`.  Working with the subtype `↥U` makes composition,
  `deriv` and `InjOn` lemmas considerably more painful.
* Simple connectivity enters **only** through `HasHolomorphicSqrt` (hypothesis (H)).
  The main theorem takes (H) as a hypothesis; `hasHolomorphicSqrt_of_simplyConnected`
  is a separate, replaceable bridge carrying all the topology.
* Uniqueness is stated as `EqOn f g U`, NOT as `∃!`.  Two functions `ℂ → ℂ` agreeing
  on `U` are genuinely different terms, so `∃!` would be false as stated.

## Markers

* `-- MATHLIB?`  — likely already exists; search Loogle before proving.
* `-- HEAVY`     — substantial prerequisite; budget real time.
* `-- NUMERIC`   — pure real-arithmetic side goal.
-/

import Mathlib

namespace RMT

open Set Filter Metric Topology Complex

noncomputable section

/-- The open unit disc. -/
abbrev disc : Set ℂ := Metric.ball (0 : ℂ) 1

lemma mem_disc {z : ℂ} : z ∈ disc ↔ ‖z‖ < 1 := by
  exact mem_ball_zero_iff

/-! ###############################################################
    ## §0.  Generic complex-analysis prerequisites
    ############################################################### -/

section Prerequisites

/-- Cauchy estimate for the first derivative of a bounded holomorphic function. -/
-- MATHLIB?  (`Complex.norm_deriv_le_aux`, `Complex.norm_deriv_le_div_of_mapsTo_ball`,
--            or derive from `Complex.cauchyIntegralFormula` / `circleIntegral` API)
theorem deriv_le_of_mapsTo_disc
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hmap : MapsTo f U disc) {z₀ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hball : closedBall z₀ δ ⊆ U) :
    ‖deriv f z₀‖ ≤ 1 / δ := by
  have hd : DiffContOnCl ℂ f (ball z₀ δ) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball z₀ hδ.ne']
    exact hf.mono hball
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ hd fun z hz => ?_
  have hzU : z ∈ U := hball (sphere_subset_closedBall hz)
  exact (mem_ball_zero_iff.1 (hmap hzU)).le

/-- A non-vanishing analytic function has an analytic `n`-th root near a point.  (Helper for
`deriv_ne_zero_of_injOn`; ported from `LiZhongQC.exists_analyticAt_pow_eq`.) -/
theorem exists_analyticAt_pow_eq {h : ℂ → ℂ} {z₀ : ℂ} (hh : AnalyticAt ℂ h z₀) (h0 : h z₀ ≠ 0)
    {n : ℕ} (hn : 0 < n) :
    ∃ k : ℂ → ℂ, AnalyticAt ℂ k z₀ ∧ k z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, k z ^ n = h z := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (h z₀) hn
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hc
    exact h0 hc.symm
  have hu : AnalyticAt ℂ (fun z => h z / h z₀) z₀ := hh.div_const
  have hu1 : (fun z => h z / h z₀) z₀ ∈ slitPlane := by
    simp only [div_self h0]
    exact one_mem_slitPlane
  refine ⟨fun z => c * exp (log (h z / h z₀) / n), ?_, ?_, ?_⟩
  · exact analyticAt_const.mul ((hu.clog hu1).div_const.cexp)
  · exact mul_ne_zero hc0 (exp_ne_zero _)
  · have hev : ∀ᶠ z in 𝓝 z₀, h z ≠ 0 := hh.continuousAt.eventually_ne h0
    filter_upwards [hev] with z hz
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have e : (n : ℂ) * (log (h z / h z₀) / n) = log (h z / h z₀) := by
      field_simp
    rw [mul_pow, ← exp_nat_mul, e, exp_log (div_ne_zero hz h0), hc]
    field_simp

/-- Injective holomorphic maps have nonvanishing derivative. -/
-- MATHLIB?
theorem deriv_ne_zero_of_injOn
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) {z : ℂ} (hz : z ∈ U) :
    deriv f z ≠ 0 := by
  revert z
  intro z₀ hz₀ hd
  have hfa : AnalyticAt ℂ f z₀ := hf.analyticAt (hU.mem_nhds hz₀)
  have hga : AnalyticAt ℂ (fun z => f z - f z₀) z₀ := hfa.sub analyticAt_const
  -- the order of `f - f z₀` at `z₀` is finite
  have htop : analyticOrderAt (fun z => f z - f z₀) z₀ ≠ ⊤ := by
    intro htop
    have hev := analyticOrderAt_eq_top.1 htop
    have hev' : ∀ᶠ z in 𝓝[≠] z₀, (f z - f z₀ = 0 ∧ z ∈ U) ∧ z ∈ ({z₀}ᶜ : Set ℂ) :=
      ((hev.and (hU.mem_nhds hz₀)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨z, ⟨hgz, hzU⟩, hzne⟩ := hev'.exists
    exact hzne (hinj hzU hz₀ (sub_eq_zero.1 hgz))
  -- the order is at least two, since `f' (z₀) = 0`
  have hge : (2 : ℕ∞) ≤ analyticOrderAt (fun z => f z - f z₀) z₀ := by
    have h1 : (1 : ℕ∞) ≤ analyticOrderAt (deriv f) z₀ := by
      rw [Order.one_le_iff_ne_zero]
      exact hfa.deriv.analyticOrderAt_ne_zero.2 hd
    rw [← hfa.analyticOrderAt_deriv_add_one]
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ analyticOrderAt (deriv f) z₀ + 1 := by gcongr
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
  have hn2 : 2 ≤ n := by
    rw [← hn] at hge
    exact_mod_cast hge
  obtain ⟨h, hha, hh0, hgev⟩ := hga.analyticOrderAt_eq_natCast.1 hn.symm
  obtain ⟨k, hka, hk0, hkev⟩ := exists_analyticAt_pow_eq hha hh0 (by omega : 0 < n)
  -- `f - f z₀ = φⁿ` with `φ = (z - z₀) k` a local diffeomorphism at `z₀`
  set φ : ℂ → ℂ := fun z => (z - z₀) * k z with hφ
  have hφa : AnalyticAt ℂ φ z₀ := (analyticAt_id.sub analyticAt_const).mul hka
  have hφ0 : φ z₀ = 0 := by simp [hφ]
  have hφd : deriv φ z₀ = k z₀ := by
    have hder : HasDerivAt (fun z => (z - z₀) * k z) (1 * k z₀ + (z₀ - z₀) * deriv k z₀) z₀ :=
      ((hasDerivAt_id' z₀).sub_const z₀).mul hka.differentiableAt.hasDerivAt
    exact hder.deriv.trans (by ring)
  have hmap : map φ (𝓝 z₀) = 𝓝 (φ z₀) :=
    hφa.hasStrictDerivAt.map_nhds_eq (by rw [hφd]; exact hk0)
  have hSmem : {z | f z - f z₀ = φ z ^ n ∧ z ∈ U} ∈ 𝓝 z₀ := by
    filter_upwards [hgev, hkev, hU.mem_nhds hz₀] with z hz hkz hzU
    refine ⟨?_, hzU⟩
    rw [hz]
    simp only [hφ, smul_eq_mul, mul_pow, hkz]
  have himg : φ '' {z | f z - f z₀ = φ z ^ n ∧ z ∈ U} ∈ 𝓝 (0 : ℂ) := by
    rw [← hφ0, ← hmap]
    exact image_mem_map hSmem
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 himg
  -- two distinct points with the same `n`-th power
  have hprim : IsPrimitiveRoot (exp (2 * Real.pi * I / n)) n :=
    Complex.isPrimitiveRoot_exp n (by omega)
  have hω1 : exp (2 * Real.pi * I / n) ≠ 1 := hprim.ne_one (by omega)
  have hωn : exp (2 * Real.pi * I / n) ^ n = 1 := hprim.pow_eq_one
  have hωnorm : ‖exp (2 * Real.pi * I / n)‖ = 1 := hprim.norm'_eq_one (by omega)
  have hw0 : ((ε / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (half_pos hε).ne'
  have hnorm : ‖((ε / 2 : ℝ) : ℂ)‖ < ε := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hw₁ : ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ε := mem_ball_zero_iff.2 hnorm
  have hw₂ : ((ε / 2 : ℝ) : ℂ) * exp (2 * Real.pi * I / n) ∈ Metric.ball (0 : ℂ) ε := by
    rw [mem_ball_zero_iff, norm_mul, hωnorm, mul_one]
    exact hnorm
  obtain ⟨z₁, ⟨hz₁, hz₁U⟩, hφz₁⟩ := hball hw₁
  obtain ⟨z₂, ⟨hz₂, hz₂U⟩, hφz₂⟩ := hball hw₂
  have hne : z₁ ≠ z₂ := by
    rintro rfl
    apply hω1
    have e : ((ε / 2 : ℝ) : ℂ) * exp (2 * Real.pi * I / n) = ((ε / 2 : ℝ) : ℂ) * 1 := by
      rw [mul_one, ← hφz₂, hφz₁]
    exact mul_left_cancel₀ hw0 e
  apply hne
  apply hinj hz₁U hz₂U
  have e₁ : f z₁ - f z₀ = ((ε / 2 : ℝ) : ℂ) ^ n := by rw [hz₁, hφz₁]
  have e₂ : f z₂ - f z₀ = ((ε / 2 : ℝ) : ℂ) ^ n := by rw [hz₂, hφz₂, mul_pow, hωn, mul_one]
  linear_combination e₁ - e₂

/-- An injective holomorphic map is a biholomorphism onto its (open) image. -/
-- MATHLIB?  (open mapping theorem + inverse function theorem)
theorem differentiableOn_invFunOn_of_injOn
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) :
    IsOpen (f '' U) ∧ DifferentiableOn ℂ (Function.invFunOn f U) (f '' U) := by
  have hstrict : ∀ z ∈ U, HasStrictDerivAt f (deriv f z) z := fun z hz =>
    (hf.analyticAt (hU.mem_nhds hz)).hasStrictDerivAt
  have hne : ∀ z ∈ U, deriv f z ≠ 0 := fun z hz => deriv_ne_zero_of_injOn hU hf hinj hz
  have hopen : IsOpen (f '' U) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨z, hz, rfl⟩
    rw [← (hstrict z hz).map_nhds_eq (hne z hz)]
    exact image_mem_map (hU.mem_nhds hz)
  refine ⟨hopen, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hleft : ∀ᶠ x in 𝓝 z, Function.invFunOn f U (f x) = x := by
    filter_upwards [hU.mem_nhds hz] with x hx
    exact hinj.leftInvOn_invFunOn hx
  exact (HasDerivAt.differentiableAt (HasStrictDerivAt.hasDerivAt
    ((hstrict z hz).to_local_left_inverse (hne z hz) hleft))).differentiableWithinAt

/-- A family of holomorphic maps `U → 𝔻` is equicontinuous at every point of `U`: the Cauchy
estimate bounds all derivatives by `4/δ` on `ball z (δ/4)` when `ball z δ ⊆ U`, and the mean value
inequality on that convex ball makes every member `(4/δ)`-Lipschitz there.  (Helper for `montel`.) -/
theorem equicontinuousAt_of_mapsTo_disc
    {U : Set ℂ} (hU : IsOpen U) (f : ℕ → ℂ → ℂ)
    (hdiff : ∀ n, DifferentiableOn ℂ (f n) U)
    (hmap : ∀ n, MapsTo (f n) U disc) {z : ℂ} (hz : z ∈ U) :
    EquicontinuousAt f z := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU z hz
  have hr0 : (0 : ℝ) < δ / 4 := by positivity
  have hsub : ∀ w ∈ ball z (δ / 4), closedBall w (δ / 4) ⊆ U := by
    intro w hw
    have hwz : dist w z < δ / 4 := mem_ball.1 hw
    refine (closedBall_subset_closedBall' (ε₂ := δ / 2) (by linarith)).trans
      ((closedBall_subset_ball (by linarith)).trans hball)
  have hbound : ∀ n, ∀ w ∈ ball z (δ / 4), ‖deriv (f n) w‖ ≤ 1 / (δ / 4) := fun n w hw =>
    deriv_le_of_mapsTo_disc hU (hdiff n) (hmap n) hr0 (hsub w hw)
  have hlip : ∀ n, ∀ w ∈ ball z (δ / 4), ‖f n w - f n z‖ ≤ (1 / (δ / 4)) * ‖w - z‖ :=
    fun n w hw =>
      (convex_ball z (δ / 4)).norm_image_sub_le_of_norm_deriv_le
        (fun x hx => (hdiff n).differentiableAt
          (hU.mem_nhds (hsub x hx (mem_closedBall_self hr0.le))))
        (hbound n) (mem_ball_self hr0) hw
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  refine ⟨min (δ / 4) (ε * (δ / 4) / 2), by positivity, fun w hw n => ?_⟩
  have hw1 : dist w z < δ / 4 := lt_of_lt_of_le hw (min_le_left _ _)
  have hw2 : dist w z < ε * (δ / 4) / 2 := lt_of_lt_of_le hw (min_le_right _ _)
  have hkey : (1 / (δ / 4)) * (ε * (δ / 4) / 2) = ε / 2 := by
    field_simp
  rw [dist_comm, dist_eq_norm]
  calc ‖f n w - f n z‖ ≤ (1 / (δ / 4)) * ‖w - z‖ := hlip n w (mem_ball.2 hw1)
    _ = (1 / (δ / 4)) * dist w z := by rw [dist_eq_norm]
    _ < (1 / (δ / 4)) * (ε * (δ / 4) / 2) := by gcongr
    _ = ε / 2 := hkey
    _ < ε := by linarith

/-- **Montel**.  A sequence of holomorphic functions on `U` with values in the unit
disc has a locally uniformly convergent subsequence, with holomorphic limit.

This is the main analytic prerequisite.  Proof: Cauchy estimates give a uniform
bound on `deriv` over compacts, hence local equicontinuity; then Arzelà–Ascoli on a
compact exhaustion plus a diagonal extraction. -/
-- HEAVY.  Needed pieces: `EquicontinuousOn`, an Arzelà–Ascoli statement,
-- `exists_seq_forall_mem_compactExhaustion`-style exhaustion, diagonal argument.
theorem montel
    {U : Set ℂ} (hU : IsOpen U) (f : ℕ → ℂ → ℂ)
    (hdiff : ∀ n, DifferentiableOn ℂ (f n) U)
    (hmap : ∀ n, MapsTo (f n) U disc) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g U ∧
      TendstoLocallyUniformlyOn (fun k => f (φ k)) g atTop U := by
  have hequi : ∀ z ∈ U, EquicontinuousAt f z := fun z hz =>
    equicontinuousAt_of_mapsTo_disc hU f hdiff hmap hz
  -- a countable dense subset of `U`
  obtain ⟨D₀, hD₀c, hD₀d⟩ := TopologicalSpace.exists_countable_dense ℂ
  have hDc : (D₀ ∩ U).Countable := hD₀c.mono inter_subset_left
  haveI : Countable ↥(D₀ ∩ U) := hDc.to_subtype
  -- a subsequence converging at every point of `D₀ ∩ U`, by compactness of `D → closedBall 0 1`
  have hcpt : IsCompact (Set.pi (univ : Set ↥(D₀ ∩ U)) fun _ => closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hmem : ∀ n, (fun d : ↥(D₀ ∩ U) => f n d) ∈
      Set.pi (univ : Set ↥(D₀ ∩ U)) fun _ => closedBall (0 : ℂ) 1 := by
    intro n
    rw [Set.mem_univ_pi]
    intro d
    exact ball_subset_closedBall (hmap n d.2.2)
  obtain ⟨a, -, φ, hφ, hlim⟩ := hcpt.tendsto_subseq hmem
  rw [tendsto_pi_nhds] at hlim
  -- the subsequence is Cauchy, hence convergent, at every point of `U`
  have hconv : ∀ z ∈ U, ∃ l : ℂ, Tendsto (fun k => f (φ k) z) atTop (𝓝 l) := by
    intro z hz
    refine cauchySeq_tendsto_of_complete ?_
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := Metric.equicontinuousAt_iff.1 (hequi z hz) (ε / 3) (by positivity)
    obtain ⟨d, hdD, hdz, hdU⟩ : ∃ d ∈ D₀, d ∈ ball z δ ∧ d ∈ U := by
      obtain ⟨d, hd, hd2⟩ :=
        hD₀d.exists_mem_open (isOpen_ball.inter hU) ⟨z, mem_ball_self hδ, hz⟩
      exact ⟨d, hd, hd2.1, hd2.2⟩
    have hd : Tendsto (fun k => f (φ k) d) atTop (𝓝 (a ⟨d, hdD, hdU⟩)) := hlim ⟨d, hdD, hdU⟩
    rw [Metric.tendsto_atTop] at hd
    obtain ⟨N, hN⟩ := hd (ε / 6) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have h1 : dist (f (φ n) z) (f (φ n) d) < ε / 3 := hδε d (mem_ball.1 hdz) (φ n)
    have h3 : dist (f (φ N) d) (f (φ N) z) < ε / 3 := by
      rw [dist_comm]
      exact hδε d (mem_ball.1 hdz) (φ N)
    have h2 : dist (f (φ n) d) (f (φ N) d) < ε / 3 := by
      have hn2 : dist (f (φ n) d) (a ⟨d, hdD, hdU⟩) < ε / 6 := hN n hn
      have hN2 : dist (f (φ N) d) (a ⟨d, hdD, hdU⟩) < ε / 6 := hN N le_rfl
      calc dist (f (φ n) d) (f (φ N) d)
          ≤ dist (f (φ n) d) (a ⟨d, hdD, hdU⟩) + dist (a ⟨d, hdD, hdU⟩) (f (φ N) d) :=
            dist_triangle _ _ _
        _ = dist (f (φ n) d) (a ⟨d, hdD, hdU⟩) + dist (f (φ N) d) (a ⟨d, hdD, hdU⟩) := by
            rw [dist_comm (a ⟨d, hdD, hdU⟩)]
        _ < ε / 6 + ε / 6 := add_lt_add hn2 hN2
        _ = ε / 3 := by ring
    calc dist (f (φ n) z) (f (φ N) z)
        ≤ dist (f (φ n) z) (f (φ n) d) + dist (f (φ n) d) (f (φ N) d)
            + dist (f (φ N) d) (f (φ N) z) := dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add h1 h2) h3
      _ = ε := by ring
  choose! g hg using hconv
  -- locally uniform convergence: uniform on every compact `K ⊆ U`
  have hloc : TendstoLocallyUniformlyOn (fun k => f (φ k)) g atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
    intro K hKU hK
    have hKeqAt : ∀ z ∈ K, EquicontinuousAt (fun k => f (φ k)) z := fun z hz V hV =>
      (hequi z (hKU hz) V hV).mono fun x hx i => hx (φ i)
    have hKeq : EquicontinuousOn (fun k => f (φ k)) K := fun z hz =>
      (hKeqAt z hz).equicontinuousWithinAt K
    have hpt : Tendsto (fun k => K.restrict (f (φ k))) atTop (𝓝 (K.restrict g)) := by
      rw [tendsto_pi_nhds]
      intro z
      exact hg z (hKU z.2)
    have hK1 : ∀ K' ∈ ({K} : Set (Set ℂ)), IsCompact K' := fun K' hK' =>
      (mem_singleton_iff.1 hK') ▸ hK
    have hK2 : ∀ K' ∈ ({K} : Set (Set ℂ)), EquicontinuousOn (fun k => f (φ k)) K' :=
      fun K' hK' => (mem_singleton_iff.1 hK') ▸ hKeq
    have hunif := (EquicontinuousOn.tendsto_uniformOnFun_iff_pi' hK1 hK2 atTop g).2 (by
      rw [sUnion_singleton]
      exact hpt)
    rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at hunif
    exact hunif K (mem_singleton K)
  have hgd : DifferentiableOn ℂ g U :=
    hloc.differentiableOn (Eventually.of_forall fun k => hdiff (φ k)) hU
  exact ⟨φ, hφ, g, hgd, hloc⟩

/-- Locally uniform limits of holomorphic functions have convergent derivatives. -/
-- MATHLIB?  (`Mathlib/Analysis/Complex/LocallyUniformLimit.lean`:
--            `TendstoLocallyUniformlyOn.differentiableOn`, `.deriv` — check exact names)
theorem tendsto_deriv_of_tendstoLocallyUniformlyOn
    {U : Set ℂ} (hU : IsOpen U) {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hconv : TendstoLocallyUniformlyOn F g atTop U) {z : ℂ} (hz : z ∈ U) :
    Tendsto (fun n => deriv (F n) z) atTop (𝓝 (deriv g z)) := by
  exact (hconv.deriv (Eventually.of_forall hF) hU).tendsto_at hz

/-- **Hurwitz** (injectivity form).  A locally uniform limit of injective
holomorphic functions on a domain is injective or constant.

Proof: if `g a = g b = w` with `a ≠ b` and `g` nonconstant, the zeros of `g - w` are
isolated; pick disjoint closed discs around `a`, `b` on whose boundaries `|g - w| ≥ m > 0`;
Rouché then forces `F n - w` to have a zero in each disc for large `n`. -/
-- HEAVY.  Requires Rouché / the argument principle.
theorem hurwitz_injOn
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U) {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U) (hinj : ∀ n, InjOn (F n) U)
    (hg : DifferentiableOn ℂ g U)
    (hconv : TendstoLocallyUniformlyOn F g atTop U)
    (hnonconst : ∃ a ∈ U, ∃ b ∈ U, g a ≠ g b) :
    InjOn g U := by
  intro a ha b hb hab
  by_contra hne
  -- `g - g b` is analytic on `U`, vanishes at `a`, and is not identically zero,
  -- so its zeros near `a` are isolated
  have hgan : ∀ z ∈ U, AnalyticAt ℂ (fun w => g w - g b) z :=
    fun z hz => (hg.analyticAt (hU.mem_nhds hz)).sub analyticAt_const
  have hnot : ¬ (∀ᶠ z in 𝓝 a, g z - g b = 0) := by
    intro hev
    have h0 : EqOn (fun w => g w - g b) 0 U :=
      AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hgan hUc.isPreconnected ha hev
    obtain ⟨x, hx, y, hy, hxy⟩ := hnonconst
    have hx0 : g x - g b = 0 := h0 hx
    have hy0 : g y - g b = 0 := h0 hy
    exact hxy (by linear_combination hx0 - hy0)
  have hiso : ∀ᶠ z in 𝓝[≠] a, g z - g b ≠ 0 :=
    (hgan a ha).eventually_eq_zero_or_eventually_ne_zero.resolve_left hnot
  -- a closed disc `D = closedBall a r ⊆ U` with `b ∉ D` and `g - g b ≠ 0` on its boundary
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU a ha
  rw [eventually_nhdsWithin_iff] at hiso
  obtain ⟨δ, hδ, hδiso⟩ := Metric.eventually_nhds_iff.mp hiso
  have hab' : 0 < dist a b := dist_pos.mpr hne
  set r : ℝ := min (ε / 2) (min (δ / 2) (dist a b / 2)) with hr
  have hr0 : 0 < r := lt_min (half_pos hε) (lt_min (half_pos hδ) (half_pos hab'))
  have hrε : r < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hrδ : r < δ := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hδ)
  have hrab : r < dist a b :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hab')
  have hDU : closedBall a r ⊆ U := fun z hz =>
    hεU (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) hrε))
  have hbD : b ∉ closedBall a r := by
    intro hbD
    rw [mem_closedBall, dist_comm] at hbD
    linarith
  have hsph : ∀ z ∈ sphere a r, g z - g b ≠ 0 := by
    intro z hz
    rw [mem_sphere] at hz
    refine hδiso (by rw [hz]; exact hrδ) ?_
    rw [Set.mem_compl_singleton_iff]
    intro hza
    rw [hza, dist_self] at hz
    exact hr0.ne hz
  -- the minimum `m > 0` of `‖g - g b‖` on the boundary circle
  have hsph_ne : (sphere a r).Nonempty :=
    ⟨a + r, by rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg hr0.le]⟩
  have hcont : ContinuousOn (fun z => ‖g z - g b‖) (sphere a r) :=
    ((hg.continuousOn.mono (sphere_subset_closedBall.trans hDU)).sub continuousOn_const).norm
  obtain ⟨zm, hzm, hmin⟩ := (isCompact_sphere a r).exists_isMinOn hsph_ne hcont
  set m : ℝ := ‖g zm - g b‖ with hm
  have hm0 : 0 < m := norm_pos_iff.mpr (hsph zm hzm)
  have hm_le : ∀ z ∈ sphere a r, m ≤ ‖g z - g b‖ := fun z hz => hmin hz
  -- pick `n` with `F n` within `m/4` of `g` on `D` and at `b`
  have hunif : TendstoUniformlyOn F g atTop (closedBall a r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hconv _ hDU (isCompact_closedBall a r)
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  have h1 : ∀ᶠ n in atTop, ∀ x ∈ closedBall a r, dist (g x) (F n x) < m / 4 :=
    hunif _ (by positivity)
  have h2 : ∀ᶠ n in atTop, dist (F n b) (g b) < m / 4 :=
    (Metric.tendsto_nhds.mp (hconv.tendsto_at hb)) _ (by positivity)
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  -- `h := F n - F n b` is zero-free on `D` (injectivity, `b ∉ D`) and `≥ m/2` on `∂D`
  have hne_D : ∀ z ∈ closedBall a r, F n z - F n b ≠ 0 := by
    intro z hz hcon
    have hzb : z = b := hinj n (hDU hz) hb (sub_eq_zero.mp hcon)
    rw [hzb] at hz
    exact hbD hz
  have hlow : ∀ z ∈ sphere a r, m / 2 ≤ ‖F n z - F n b‖ := by
    intro z hz
    have e1 := hn1 z (sphere_subset_closedBall hz)
    have e2 := hn2
    rw [dist_eq_norm] at e1 e2
    have e3 := hm_le z hz
    have hsplit : g z - g b = (g z - F n z) + (F n z - F n b) + (F n b - g b) := by ring
    have e4 : ‖g z - g b‖ ≤ ‖g z - F n z‖ + ‖F n z - F n b‖ + ‖F n b - g b‖ := by
      rw [hsplit]
      have t1 := norm_add_le (g z - F n z + (F n z - F n b)) (F n b - g b)
      have t2 := norm_add_le (g z - F n z) (F n z - F n b)
      linarith
    linarith
  -- maximum modulus for `1/h` on the disc gives `‖h a‖ ≥ m/2`
  have hdiff : DifferentiableOn ℂ (fun z => (F n z - F n b)⁻¹) (closedBall a r) :=
    (((hF n).mono hDU).sub_const _).inv hne_D
  have hdc : DiffContOnCl ℂ (fun z => (F n z - F n b)⁻¹) (ball a r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rwa [closure_ball a hr0.ne']
  have hC : ∀ z ∈ frontier (ball a r), ‖(F n z - F n b)⁻¹‖ ≤ 2 / m := by
    intro z hz
    rw [frontier_ball a hr0.ne'] at hz
    have hpos : 0 < ‖F n z - F n b‖ := norm_pos_iff.mpr (hne_D z (sphere_subset_closedBall hz))
    rw [norm_inv, inv_le_comm₀ hpos (by positivity), inv_div]
    exact hlow z hz
  have hacl : a ∈ closure (ball a r) := by
    rw [closure_ball a hr0.ne']; exact mem_closedBall_self hr0.le
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc hC hacl
  have hna : 0 < ‖F n a - F n b‖ := norm_pos_iff.mpr (hne_D a (mem_closedBall_self hr0.le))
  rw [norm_inv, inv_le_comm₀ hna (by positivity), inv_div] at hmax
  -- but `h a = (F n a - g a) - (F n b - g b)` is smaller than `m/2`
  have e1 := hn1 a (mem_closedBall_self hr0.le)
  have e2 := hn2
  rw [dist_eq_norm] at e1 e2
  have hsplit : F n a - F n b = -(g a - F n a) - (F n b - g b) := by rw [hab]; ring
  have e4 : ‖F n a - F n b‖ ≤ ‖g a - F n a‖ + ‖F n b - g b‖ := by
    rw [hsplit]
    exact (norm_sub_le _ _).trans (by rw [norm_neg])
  linarith

/-- **Schwarz lemma**, equality form: a holomorphic self-map of the disc fixing `0`
with `|f' 0| = 1` is a rotation. -/
-- MATHLIB?  (`Mathlib/Analysis/Complex/Schwarz.lean` — check for the equality case,
--            it may only have the inequalities `Complex.abs_deriv_le_div_of_mapsTo_ball`.)
theorem schwarz_eq_rotation
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disc) (hmap : MapsTo f disc disc)
    (h0 : f 0 = 0) (hderiv : ‖deriv f 0‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ EqOn f (fun z => c * z) disc := by
  have hd : DifferentiableOn ℂ f (ball (0 : ℂ) 1) := hf
  have hmaps : MapsTo f (ball (0 : ℂ) 1) (closedBall (f 0) 1) := by
    rw [h0]; exact fun z hz => ball_subset_closedBall (hmap hz)
  have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hdsl : ‖dslope f 0 0‖ = 1 / 1 := by rw [dslope_same, hderiv, div_one]
  have haff := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hd hmaps h0mem hdsl
  refine ⟨deriv f 0, hderiv, fun z hz => ?_⟩
  have h : f z = f 0 + (z - 0) • dslope f 0 0 := haff hz
  show f z = deriv f 0 * z
  rw [h, dslope_same, h0, zero_add, sub_zero, smul_eq_mul, mul_comm]

end Prerequisites

/-! ###############################################################
    ## §1.  Hypothesis (H): holomorphic square roots
    ############################################################### -/

/-- **(H)**  Every zero-free holomorphic function on `U` has a holomorphic square root.

This is the *only* consequence of simple connectivity used in the proof of RMT. -/
def HasHolomorphicSqrt (U : Set ℂ) : Prop :=
  ∀ g : ℂ → ℂ, DifferentiableOn ℂ g U → (∀ z ∈ U, g z ≠ 0) →
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h U ∧ ∀ z ∈ U, h z ^ 2 = g z

section Bridge

/-- Holomorphic logarithms exist on simply connected domains. -/
theorem exists_holomorphic_log_of_simplyConnected
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U) [SimplyConnectedSpace ↥U]
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (hne : ∀ z ∈ U, g z ≠ 0) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h U ∧ ∀ z ∈ U, Complex.exp (h z) = g z := by
  have hsc : IsSimplyConnected U := ‹SimplyConnectedSpace ↥U›
  have h0 : (0 : ℂ) ∉ g '' U := by
    rintro ⟨z, hz, hz0⟩
    exact hne z hz hz0
  obtain ⟨h, hhc, hh⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc hU hg.continuousOn h0
  refine ⟨h, fun z hz => ?_, fun z hz => hh hz⟩
  -- near `z`, `h = L ∘ g` for `L` the local inverse of `exp` at `h z`, which is holomorphic
  have hexp : HasStrictDerivAt Complex.exp (Complex.exp (h z)) (h z) :=
    Complex.hasStrictDerivAt_exp _
  have hne' : Complex.exp (h z) ≠ 0 := Complex.exp_ne_zero _
  have hhz : Complex.exp (h z) = g z := hh hz
  have hcont : ContinuousAt h z := hhc.continuousAt (hU.mem_nhds hz)
  have hev : h =ᶠ[𝓝 z] fun y => hexp.localInverse _ _ _ hne' (g y) := by
    have h1 : ∀ᶠ y in 𝓝 z, hexp.localInverse _ _ _ hne' (Complex.exp (h y)) = h y :=
      hcont.tendsto.eventually (hexp.eventually_left_inverse hne')
    have h2 : ∀ᶠ y in 𝓝 z, Complex.exp (h y) = g y := by
      filter_upwards [hU.mem_nhds hz] with y hy
      exact hh hy
    filter_upwards [h1, h2] with y hy1 hy2
    rw [← hy1, hy2]
  have hdiff : DifferentiableAt ℂ (fun y => hexp.localInverse _ _ _ hne' (g y)) z := by
    have hgz : DifferentiableAt ℂ g z := hg.differentiableAt (hU.mem_nhds hz)
    have hLz : DifferentiableAt ℂ (hexp.localInverse _ _ _ hne') (g z) := by
      rw [← hhz]
      exact HasDerivAt.differentiableAt (HasStrictDerivAt.hasDerivAt (hexp.to_localInverse hne'))
    exact hLz.comp z hgz
  exact (hev.differentiableAt_iff.2 hdiff).differentiableWithinAt

/-- The bridge: simple connectivity implies (H). -/
theorem hasHolomorphicSqrt_of_simplyConnected
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U) [SimplyConnectedSpace ↥U] :
    HasHolomorphicSqrt U := by
  intro g hg hne
  obtain ⟨l, hl, hlg⟩ := exists_holomorphic_log_of_simplyConnected hU hUc hg hne
  refine ⟨fun z => Complex.exp (l z / 2), (hl.div_const 2).cexp, fun z hz => ?_⟩
  have : Complex.exp (l z / 2) ^ 2 = Complex.exp (l z) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [this, hlg z hz]

end Bridge

/-! ###############################################################
    ## §2.  Disc automorphisms (Blaschke factors)
    ############################################################### -/

section Blaschke

/-- `blaschke w z = (z - w) / (1 - conj w * z)`, the disc automorphism sending `w ↦ 0`. -/
def blaschke (w z : ℂ) : ℂ := (z - w) / (1 - (starRingEnd ℂ) w * z)

variable {w : ℂ}

/-- `|z|² < 1 ↔ |z| < 1`. -/
lemma normSq_lt_one_iff {z : ℂ} : normSq z < 1 ↔ ‖z‖ < 1 := by
  rw [Complex.normSq_eq_norm_sq]
  constructor
  · intro h; nlinarith [norm_nonneg z]
  · intro h; nlinarith [norm_nonneg z]

/-- The algebraic identity behind the Blaschke factor:
`|1 - w̄ z|² - |z - w|² = (1 - |z|²)(1 - |w|²)`. -/
lemma normSq_blaschke_key (w z : ℂ) :
    normSq (1 - (starRingEnd ℂ) w * z) - normSq (z - w) = (1 - normSq z) * (1 - normSq w) := by
  simp only [normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

/-- `w̄ w = |w|²` as a complex number. -/
lemma conj_mul_self_eq_norm_sq (w : ℂ) : (starRingEnd ℂ) w * w = ((‖w‖ : ℝ) : ℂ) ^ 2 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

lemma blaschke_denom_ne_zero (hw : w ∈ disc) {z : ℂ} (hz : z ∈ disc) :
    1 - (starRingEnd ℂ) w * z ≠ 0 := by
  have hw' : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  intro hcon
  have h1 : normSq (1 - (starRingEnd ℂ) w * z) = 0 := by rw [hcon, map_zero]
  have h2 := normSq_blaschke_key w z
  rw [h1] at h2
  have hza : normSq z < 1 := normSq_lt_one_iff.mpr hz'
  have haa : normSq w < 1 := normSq_lt_one_iff.mpr hw'
  nlinarith [normSq_nonneg (z - w)]

lemma differentiableOn_blaschke (hw : w ∈ disc) :
    DifferentiableOn ℂ (blaschke w) disc := by
  intro z hz
  have hden := blaschke_denom_ne_zero hw hz
  refine DifferentiableAt.differentiableWithinAt ?_
  exact (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => v - w) z).div
    (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 - (starRingEnd ℂ) w * v) z) hden

lemma blaschke_mapsTo (hw : w ∈ disc) : MapsTo (blaschke w) disc disc := by
  intro z hz
  have hw' : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hden := blaschke_denom_ne_zero hw hz
  have hza : normSq z < 1 := normSq_lt_one_iff.mpr hz'
  have haa : normSq w < 1 := normSq_lt_one_iff.mpr hw'
  have hkey := normSq_blaschke_key w z
  have hlt : normSq (z - w) < normSq (1 - (starRingEnd ℂ) w * z) := by nlinarith
  rw [mem_ball_zero_iff, ← normSq_lt_one_iff, blaschke, normSq_div,
    div_lt_one (normSq_pos.mpr hden)]
  exact hlt

lemma blaschke_injOn (hw : w ∈ disc) : InjOn (blaschke w) disc := by
  intro z₁ h₁ z₂ h₂ heq
  have d₁ := blaschke_denom_ne_zero hw h₁
  have d₂ := blaschke_denom_ne_zero hw h₂
  have hne := blaschke_denom_ne_zero hw hw
  rw [blaschke, blaschke, div_eq_div_iff d₁ d₂] at heq
  have h0 : (z₁ - z₂) * (1 - (starRingEnd ℂ) w * w) = 0 := by linear_combination heq
  rcases mul_eq_zero.mp h0 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hne

lemma blaschke_self (hw : w ∈ disc) : blaschke w w = 0 := by
  simp [blaschke]

lemma blaschke_zero (hw : w ∈ disc) : blaschke w 0 = -w := by
  simp [blaschke]

/-- `blaschke (-w)` inverts `blaschke w`. -/
lemma blaschke_leftInverse (hw : w ∈ disc) :
    ∀ z ∈ disc, blaschke (-w) (blaschke w z) = z := by
  intro z hz
  have hden := blaschke_denom_ne_zero hw hz
  have hden' : (1 : ℂ) - z * (starRingEnd ℂ) w ≠ 0 := by rw [mul_comm]; exact hden
  have hne := blaschke_denom_ne_zero hw hw
  have key : (1 : ℂ) - (starRingEnd ℂ) (-w) * blaschke w z
      = (1 - (starRingEnd ℂ) w * w) / (1 - (starRingEnd ℂ) w * z) := by
    simp only [blaschke, map_neg, neg_mul, sub_neg_eq_add]
    field_simp
    ring
  have keynum : blaschke w z - -w
      = z * (1 - (starRingEnd ℂ) w * w) / (1 - (starRingEnd ℂ) w * z) := by
    simp only [blaschke, sub_neg_eq_add]
    field_simp
    ring
  have hden2 : (1 : ℂ) - (starRingEnd ℂ) (-w) * blaschke w z ≠ 0 := by
    rw [key]; exact div_ne_zero hne hden
  rw [blaschke, div_eq_iff hden2, keynum, key, mul_div_assoc]

/-- The derivative of the Blaschke factor, as a `HasDerivAt`. -/
lemma hasDerivAt_blaschke (hw : w ∈ disc) {z : ℂ} (hz : z ∈ disc) :
    HasDerivAt (blaschke w)
      ((1 - (starRingEnd ℂ) w * w) / (1 - (starRingEnd ℂ) w * z) ^ 2) z := by
  have hden := blaschke_denom_ne_zero hw hz
  have h0 : HasDerivAt (fun v : ℂ => v) 1 z := hasDerivAt_id z
  have h1 : HasDerivAt (fun v : ℂ => v - w) 1 z := by simpa using h0.sub_const w
  have h2 : HasDerivAt (fun v : ℂ => 1 - (starRingEnd ℂ) w * v) (-(starRingEnd ℂ) w) z := by
    simpa using HasDerivAt.const_sub 1 (h0.const_mul ((starRingEnd ℂ) w))
  have h3 := h1.div h2 hden
  have hfun : blaschke w = fun v : ℂ => (v - w) / (1 - (starRingEnd ℂ) w * v) := rfl
  rw [hfun]
  convert h3 using 1
  field_simp
  ring

/-- `deriv (blaschke w) z = (1 - |w|²) / (1 - conj w * z)²`. -/
lemma deriv_blaschke (hw : w ∈ disc) {z : ℂ} (hz : z ∈ disc) :
    deriv (blaschke w) z
      = ((1 : ℂ) - ((‖w‖ : ℝ) : ℂ) ^ 2) / (1 - (starRingEnd ℂ) w * z) ^ 2 := by
  rw [(hasDerivAt_blaschke hw hz).deriv, conj_mul_self_eq_norm_sq]

lemma deriv_blaschke_at_zero (hw : w ∈ disc) :
    deriv (blaschke w) 0 = (1 : ℂ) - ((‖w‖ : ℝ) : ℂ) ^ 2 := by
  rw [deriv_blaschke hw (mem_ball_self one_pos)]
  simp

lemma deriv_blaschke_at_self (hw : w ∈ disc) :
    deriv (blaschke w) w = 1 / ((1 : ℂ) - ((‖w‖ : ℝ) : ℂ) ^ 2) := by
  have hne : (1 : ℂ) - ((‖w‖ : ℝ) : ℂ) ^ 2 ≠ 0 := by
    rw [← conj_mul_self_eq_norm_sq]; exact blaschke_denom_ne_zero hw hw
  rw [deriv_blaschke hw hw, conj_mul_self_eq_norm_sq, sq ((1 : ℂ) - ((‖w‖ : ℝ) : ℂ) ^ 2),
    div_mul_eq_div_div, div_self hne]

end Blaschke

/-! ###############################################################
    ## §3.  The competing family 𝓕
    ############################################################### -/

section Family

variable (U : Set ℂ) (z₀ : ℂ)

/-- Membership in the extremal family: injective holomorphic `U → 𝔻`,
normalized by `f z₀ = 0` and `deriv f z₀ ∈ ℝ_{>0}`. -/
structure IsCompetitor (f : ℂ → ℂ) : Prop where
  diff    : DifferentiableOn ℂ f U
  injOn   : InjOn f U
  mapsTo  : MapsTo f U disc
  center  : f z₀ = 0
  im_zero : (deriv f z₀).im = 0
  re_pos  : 0 < (deriv f z₀).re

/-- The extremal functional: `f ↦ Re (deriv f z₀)`. -/
def derivVal (f : ℂ → ℂ) : ℝ := (deriv f z₀).re

/-- The family as a set of functions. -/
def Fam : Set (ℂ → ℂ) := {f | IsCompetitor U z₀ f}

variable {U z₀}

/-- For a competitor the derivative at `z₀` is a positive real, so the functional is its norm. -/
lemma IsCompetitor.derivVal_eq_norm {f : ℂ → ℂ} (hf : IsCompetitor U z₀ f) :
    derivVal z₀ f = ‖deriv f z₀‖ := by
  have hD : deriv f z₀ = (((deriv f z₀).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [hf.im_zero])
  show (deriv f z₀).re = ‖deriv f z₀‖
  conv_rhs => rw [hD]
  rw [Complex.norm_real, Real.norm_of_nonneg hf.re_pos.le]

/-- Closure property used three times (Steps A, C, D): post-composing a competitor-like
map with a Blaschke factor and a unimodular rotation returns a competitor. -/
lemma isCompetitor_normalize
    {f : ℂ → ℂ} (hdiff : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    (hmap : MapsTo f U disc) (hz₀ : z₀ ∈ U) (hUo : IsOpen U) :
    ∃ (c : ℂ), ‖c‖ = 1 ∧
      IsCompetitor U z₀ (fun z => c * blaschke (f z₀) (f z)) := by
  have hf0 : f z₀ ∈ disc := hmap hz₀
  have hfd : DifferentiableAt ℂ f z₀ := hdiff.differentiableAt (hUo.mem_nhds hz₀)
  have hD : HasDerivAt (fun z => blaschke (f z₀) (f z))
      (deriv (blaschke (f z₀)) (f z₀) * deriv f z₀) z₀ :=
    (hasDerivAt_blaschke hf0 hf0).differentiableAt.hasDerivAt.comp z₀ hfd.hasDerivAt
  set D₀ : ℂ := deriv (blaschke (f z₀)) (f z₀) * deriv f z₀ with hD₀
  have hf' : deriv f z₀ ≠ 0 := deriv_ne_zero_of_injOn hUo hdiff hinj hz₀
  have hb' : deriv (blaschke (f z₀)) (f z₀) ≠ 0 := by
    rw [deriv_blaschke_at_self hf0]
    refine one_div_ne_zero ?_
    rw [← conj_mul_self_eq_norm_sq]
    exact blaschke_denom_ne_zero hf0 hf0
  have hD₀ne : D₀ ≠ 0 := mul_ne_zero hb' hf'
  have hnorm : ‖D₀‖ ≠ 0 := norm_ne_zero_iff.mpr hD₀ne
  set c : ℂ := ((‖D₀‖ : ℝ) : ℂ) / D₀ with hc
  have hc1 : ‖c‖ = 1 := by
    rw [hc, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), div_self hnorm]
  have hc0 : c ≠ 0 := by
    intro hcon; rw [hcon, norm_zero] at hc1; exact zero_ne_one hc1
  have hcD : HasDerivAt (fun z => c * blaschke (f z₀) (f z)) (c * D₀) z₀ := hD.const_mul c
  have hval : c * D₀ = ((‖D₀‖ : ℝ) : ℂ) := div_mul_cancel₀ _ hD₀ne
  refine ⟨c, hc1, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((differentiableOn_blaschke hf0).comp hdiff hmap).const_mul c
  · intro a ha b hb hab
    have hab' : c * blaschke (f z₀) (f a) = c * blaschke (f z₀) (f b) := hab
    have h1 : blaschke (f z₀) (f a) = blaschke (f z₀) (f b) := mul_left_cancel₀ hc0 hab'
    exact hinj ha hb (blaschke_injOn hf0 (hmap ha) (hmap hb) h1)
  · intro z hz
    show c * blaschke (f z₀) (f z) ∈ disc
    rw [mem_ball_zero_iff, norm_mul, hc1, one_mul]
    exact mem_ball_zero_iff.mp (blaschke_mapsTo hf0 (hmap hz))
  · show c * blaschke (f z₀) (f z₀) = 0
    rw [blaschke_self hf0, mul_zero]
  · rw [hcD.deriv, hval, Complex.ofReal_im]
  · rw [hcD.deriv, hval, Complex.ofReal_re]
    exact norm_pos_iff.mpr hD₀ne

/-- The derivative of the normalized map, in terms of the original.

The hypothesis `hcomp` (the normalized map is a competitor, i.e. `c` is the rotation making its
derivative at `z₀` positive) is needed: for another unimodular `c`, e.g. `c = -1`, the real part
`derivVal` is smaller, even negative. -/
lemma derivVal_normalize
    {f : ℂ → ℂ} {c : ℂ} (hc : ‖c‖ = 1)
    (hdiff : DifferentiableOn ℂ f U) (hmap : MapsTo f U disc)
    (hz₀ : z₀ ∈ U) (hUo : IsOpen U)
    (hcomp : IsCompetitor U z₀ (fun z => c * blaschke (f z₀) (f z))) :
    derivVal z₀ (fun z => c * blaschke (f z₀) (f z))
      = ‖deriv f z₀‖ / (1 - ‖f z₀‖ ^ 2) := by
  have hf0 : f z₀ ∈ disc := hmap hz₀
  have hf0n : ‖f z₀‖ < 1 := mem_ball_zero_iff.mp hf0
  have hfd : DifferentiableAt ℂ f z₀ := hdiff.differentiableAt (hUo.mem_nhds hz₀)
  have hr : 0 < 1 - ‖f z₀‖ ^ 2 := by nlinarith [norm_nonneg (f z₀)]
  have hne : ((1 - ‖f z₀‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hcast : (1 : ℂ) - ((‖f z₀‖ : ℝ) : ℂ) ^ 2 = ((1 - ‖f z₀‖ ^ 2 : ℝ) : ℂ) := by norm_cast
  have hD : HasDerivAt (fun z => c * blaschke (f z₀) (f z))
      (c * (((1 - ‖f z₀‖ ^ 2 : ℝ) : ℂ)⁻¹ * deriv f z₀)) z₀ := by
    have h1 := ((hasDerivAt_blaschke hf0 hf0).comp z₀ hfd.hasDerivAt).const_mul c
    rw [conj_mul_self_eq_norm_sq, hcast, sq (((1 - ‖f z₀‖ ^ 2 : ℝ) : ℂ)), div_mul_eq_div_div,
      div_self hne, one_div] at h1
    exact h1
  rw [hcomp.derivVal_eq_norm, hD.deriv, norm_mul, norm_mul, hc, one_mul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg hr.le, inv_mul_eq_div]

end Family

/-! ###############################################################
    ## §4.  Step A — the family is nonempty
    ############################################################### -/

section StepA

variable {U : Set ℂ} {z₀ : ℂ}

/-- A holomorphic square root of `z - a` is injective on `U` and its image is
disjoint from its own negative. -/
lemma sqrt_shift_injOn_and_disjoint
    (hUo : IsOpen U) (hH : HasHolomorphicSqrt U) {a : ℂ} (ha : a ∉ U)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (hsq : ∀ z ∈ U, g z ^ 2 = z - a) :
    InjOn g U ∧ ∀ z₁ ∈ U, ∀ z₂ ∈ U, g z₁ ≠ - g z₂ := by
  refine ⟨fun z₁ hz₁ z₂ hz₂ h => ?_, fun z₁ hz₁ z₂ hz₂ h => ?_⟩
  · have h1 := hsq z₁ hz₁
    rw [h, hsq z₂ hz₂] at h1
    linear_combination -h1
  · have h1 := hsq z₁ hz₁
    rw [h, neg_sq, hsq z₂ hz₂] at h1
    have hz : z₁ = z₂ := by linear_combination -h1
    subst hz
    have h0 : g z₁ = 0 := by linear_combination h / 2
    have h2 := hsq z₁ hz₁
    rw [h0] at h2
    apply ha
    have h3 : z₁ = a := by linear_combination -h2
    rw [← h3]
    exact hz₁

/-- `U` embeds injectively and holomorphically into the unit disc. -/
lemma exists_injective_map_to_disc
    (hUo : IsOpen U) (hUc : IsConnected U) (hUne : Uᶜ.Nonempty)
    (hH : HasHolomorphicSqrt U) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h U ∧ InjOn h U ∧ MapsTo h U disc := by
  obtain ⟨a, ha⟩ := hUne
  -- (H) applied to the zero-free function `z ↦ z - a`
  obtain ⟨g, hg, hsq⟩ := hH (fun z => z - a) (differentiableOn_id.sub_const a)
    (fun z hz h0 => ha ((sub_eq_zero.1 h0) ▸ hz))
  have hsq2 : ∀ z ∈ U, g z ^ 2 = z - a := hsq
  obtain ⟨hinj, hdisj⟩ := sqrt_shift_injOn_and_disjoint hUo hH ha hg hsq2
  -- `g '' U` is open, so it contains a ball `ball (g x) ρ`; then `ball (-g x) ρ` misses `g '' U`
  have hopen : IsOpen (g '' U) := (differentiableOn_invFunOn_of_injOn hUo hg hinj).1
  obtain ⟨x, hx⟩ := hUc.nonempty
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hopen (g x) ⟨x, hx, rfl⟩
  have hfar : ∀ z ∈ U, ρ ≤ ‖g z + g x‖ := by
    intro z hz
    by_contra hlt
    rw [not_le] at hlt
    have hmem : -g z ∈ ball (g x) ρ := by
      rw [mem_ball, dist_eq_norm, show -g z - g x = -(g z + g x) by ring, norm_neg]
      exact hlt
    obtain ⟨w, hw, hgw⟩ := hball hmem
    exact hdisj w hw z hz hgw
  have hden : ∀ z ∈ U, g z + g x ≠ 0 := fun z hz h0 => by
    have h1 := hfar z hz
    rw [h0, norm_zero] at h1
    exact absurd h1 (not_le.2 hρ)
  have hρne : ((ρ / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  refine ⟨fun z => ((ρ / 2 : ℝ) : ℂ) / (g z + g x), ?_, ?_, ?_⟩
  · exact (differentiableOn_const _).div (hg.add_const _) hden
  · intro z₁ hz₁ z₂ hz₂ heq
    have heq2 : ((ρ / 2 : ℝ) : ℂ) / (g z₁ + g x) = ((ρ / 2 : ℝ) : ℂ) / (g z₂ + g x) := heq
    have h1 := (div_eq_div_iff (hden z₁ hz₁) (hden z₂ hz₂)).1 heq2
    have h2 : g z₂ + g x = g z₁ + g x := mul_left_cancel₀ hρne h1
    exact hinj hz₁ hz₂ (add_right_cancel h2).symm
  · intro z hz
    have hpos : 0 < ‖g z + g x‖ := lt_of_lt_of_le hρ (hfar z hz)
    rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      div_lt_one hpos]
    linarith [hfar z hz]

/-- **Step A.**  `𝓕` is nonempty. -/
theorem fam_nonempty
    (hUo : IsOpen U) (hUc : IsConnected U) (hUne : Uᶜ.Nonempty)
    (hH : HasHolomorphicSqrt U) (hz₀ : z₀ ∈ U) :
    (Fam U z₀).Nonempty := by
  obtain ⟨h, hdiff, hinj, hmap⟩ := exists_injective_map_to_disc hUo hUc hUne hH
  obtain ⟨c, -, hc⟩ := isCompetitor_normalize hdiff hinj hmap hz₀ hUo
  exact ⟨_, hc⟩

end StepA

/-! ###############################################################
    ## §5.  Step B — the extremal problem is well posed
    ############################################################### -/

section StepB

variable {U : Set ℂ} {z₀ : ℂ}

/-- **Step B.**  The functional is bounded above on `𝓕` by `1 / δ` for any
`δ` with `closedBall z₀ δ ⊆ U`. -/
theorem bddAbove_derivVal
    (hUo : IsOpen U) (hz₀ : z₀ ∈ U) :
    BddAbove (derivVal z₀ '' Fam U z₀) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hUo z₀ hz₀
  have hcb : closedBall z₀ (δ / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hball
  refine ⟨1 / (δ / 2), ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  have hfc : IsCompetitor U z₀ f := hf
  calc derivVal z₀ f = (deriv f z₀).re := rfl
    _ ≤ ‖deriv f z₀‖ := Complex.re_le_norm _
    _ ≤ 1 / (δ / 2) := deriv_le_of_mapsTo_disc hUo hfc.diff hfc.mapsTo (by positivity) hcb

/-- The supremum of the extremal functional. -/
def M (U : Set ℂ) (z₀ : ℂ) : ℝ := sSup (derivVal z₀ '' Fam U z₀)

theorem M_pos
    (hUo : IsOpen U) (hUc : IsConnected U) (hUne : Uᶜ.Nonempty)
    (hH : HasHolomorphicSqrt U) (hz₀ : z₀ ∈ U) :
    0 < M U z₀ := by
  obtain ⟨f, hf⟩ := fam_nonempty hUo hUc hUne hH hz₀
  have hfc : IsCompetitor U z₀ f := hf
  exact lt_csSup_of_lt (bddAbove_derivVal hUo hz₀) ⟨f, hf, rfl⟩ hfc.re_pos

end StepB

/-! ###############################################################
    ## §6.  Step C — the supremum is attained
    ############################################################### -/

section StepC

variable {U : Set ℂ} {z₀ : ℂ}

/-- **Step C.**  Montel + Hurwitz + maximum modulus: the supremum is attained. -/
theorem exists_extremal
    (hUo : IsOpen U) (hUc : IsConnected U) (hUne : Uᶜ.Nonempty)
    (hH : HasHolomorphicSqrt U) (hz₀ : z₀ ∈ U) :
    ∃ f ∈ Fam U z₀, derivVal z₀ f = M U z₀ := by
  -- 1. a maximizing sequence `fₙ ∈ 𝓕` with `derivVal fₙ → M`
  have hne : (derivVal z₀ '' Fam U z₀).Nonempty := (fam_nonempty hUo hUc hUne hH hz₀).image _
  obtain ⟨u, -, hu, hmem⟩ := exists_seq_tendsto_sSup hne (bddAbove_derivVal hUo hz₀)
  simp only [Set.mem_image] at hmem
  choose f hfF hfu using hmem
  have hfc : ∀ n, IsCompetitor U z₀ (f n) := fun n => hfF n
  -- 2. Montel: a locally uniformly convergent subsequence with holomorphic limit `g`
  obtain ⟨φ, hφ, g, hgd, hconv⟩ := montel hUo f (fun n => (hfc n).diff) (fun n => (hfc n).mapsTo)
  -- 3. the derivatives converge, so `deriv g z₀ = M > 0` is a positive real
  have hder := tendsto_deriv_of_tendstoLocallyUniformlyOn hUo (fun k => (hfc (φ k)).diff) hconv hz₀
  have hre : Tendsto (fun k => (deriv (f (φ k)) z₀).re) atTop (𝓝 (deriv g z₀).re) :=
    (Complex.continuous_re.tendsto _).comp hder
  have him : Tendsto (fun k => (deriv (f (φ k)) z₀).im) atTop (𝓝 (deriv g z₀).im) :=
    (Complex.continuous_im.tendsto _).comp hder
  have hre' : Tendsto (fun k => (deriv (f (φ k)) z₀).re) atTop (𝓝 (M U z₀)) := by
    have hfun : (fun k => (deriv (f (φ k)) z₀).re) = fun k => u (φ k) :=
      funext fun k => hfu (φ k)
    rw [hfun]
    exact hu.comp hφ.tendsto_atTop
  have hgre : (deriv g z₀).re = M U z₀ := tendsto_nhds_unique hre hre'
  have hgim : (deriv g z₀).im = 0 := by
    have hfun : (fun k => (deriv (f (φ k)) z₀).im) = fun _ => 0 :=
      funext fun k => (hfc (φ k)).im_zero
    rw [hfun] at him
    exact tendsto_nhds_unique him tendsto_const_nhds
  have hM := M_pos hUo hUc hUne hH hz₀
  -- 6. `g z₀ = 0` by passing to the limit
  have hg0 : g z₀ = 0 := by
    have h1 := hconv.tendsto_at hz₀
    have hfun : (fun k => f (φ k) z₀) = fun _ => 0 := funext fun k => (hfc (φ k)).center
    rw [hfun] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  -- `‖g‖ ≤ 1` on `U`
  have hle : ∀ z ∈ U, ‖g z‖ ≤ 1 := by
    intro z hz
    have h1 := (hconv.tendsto_at hz).norm
    exact le_of_tendsto' h1 fun k => (mem_ball_zero_iff.mp ((hfc (φ k)).mapsTo hz)).le
  -- `g` is nonconstant since `deriv g z₀ ≠ 0`
  have hnonconst : ∃ a ∈ U, ∃ b ∈ U, g a ≠ g b := by
    by_contra hcon
    push Not at hcon
    have hev : g =ᶠ[𝓝 z₀] fun _ => g z₀ := by
      filter_upwards [hUo.mem_nhds hz₀] with z hz using hcon z hz z₀ hz₀
    have h0 : deriv g z₀ = 0 := by rw [hev.deriv_eq, deriv_const]
    rw [h0, Complex.zero_re] at hgre
    linarith
  -- 4. Hurwitz: `g` is injective
  have hinj : InjOn g U :=
    hurwitz_injOn hUo hUc (fun k => (hfc (φ k)).diff) (fun k => (hfc (φ k)).injOn) hgd hconv
      hnonconst
  -- 5. maximum modulus: `‖g‖ < 1` on `U`
  have hmap : MapsTo g U disc := by
    intro z hz
    rw [mem_ball_zero_iff]
    rcases lt_or_eq_of_le (hle z hz) with h | h
    · exact h
    · exfalso
      have hmax : IsMaxOn (norm ∘ g) U z := isMaxOn_iff.mpr fun y hy => by
        show ‖g y‖ ≤ ‖g z‖
        rw [h]; exact hle y hy
      have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUc.isPreconnected hUo hgd hz
        hmax
      obtain ⟨a, ha, b, hb, hab⟩ := hnonconst
      exact hab ((hconst ha).trans (hconst hb).symm)
  have hgFam : IsCompetitor U z₀ g := ⟨hgd, hinj, hmap, hg0, hgim, by rw [hgre]; exact hM⟩
  exact ⟨g, hgFam, hgre⟩

end StepC

/-! ###############################################################
    ## §7.  Step D — the extremal map is surjective
    ############################################################### -/

section StepD

/-- The arithmetic gain of the square-root trick. -/
-- NUMERIC.  Substitute `s = Real.sqrt t`; `nlinarith [sq_nonneg (1 - s)]`.
theorem sqrt_gain {t : ℝ} (h₀ : 0 < t) (h₁ : t < 1) :
    1 < (1 + t) / (2 * Real.sqrt t) := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr h₀
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt h₀.le
  have hs1 : Real.sqrt t < 1 := by
    rw [Real.sqrt_lt' one_pos, one_pow]; exact h₁
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hs1)]

variable {U : Set ℂ} {z₀ : ℂ}

/-- If the extremal map omitted a value `w₀`, the square-root trick would produce a
competitor with strictly larger derivative. -/
theorem exists_better_of_not_surjOn
    (hUo : IsOpen U) (hUc : IsConnected U) (hH : HasHolomorphicSqrt U) (hz₀ : z₀ ∈ U)
    {f : ℂ → ℂ} (hf : IsCompetitor U z₀ f)
    {w₀ : ℂ} (hw₀ : w₀ ∈ disc) (homit : w₀ ∉ f '' U) :
    ∃ g ∈ Fam U z₀, derivVal z₀ f < derivVal z₀ g := by
  have hw₀n : ‖w₀‖ < 1 := mem_ball_zero_iff.mp hw₀
  have hnw₀ : -w₀ ∈ disc := by rw [mem_ball_zero_iff, norm_neg]; exact hw₀n
  -- `G := blaschke w₀ ∘ f` is holomorphic and zero-free on `U`
  set G : ℂ → ℂ := fun z => blaschke w₀ (f z) with hGdef
  have hGdiff : DifferentiableOn ℂ G U := (differentiableOn_blaschke hw₀).comp hf.diff hf.mapsTo
  have hGne : ∀ z ∈ U, G z ≠ 0 := by
    intro z hz hcon
    apply homit
    refine ⟨z, hz, ?_⟩
    have h1 := blaschke_leftInverse hw₀ (f z) (hf.mapsTo hz)
    rw [show blaschke w₀ (f z) = 0 from hcon, blaschke_zero hnw₀, neg_neg] at h1
    exact h1.symm
  -- the holomorphic square root `F` of `G`, injective into the disc
  obtain ⟨F, hFdiff, hFsq⟩ := hH G hGdiff hGne
  have hFmap : MapsTo F U disc := by
    intro z hz
    rw [mem_ball_zero_iff]
    have h1 : ‖F z‖ ^ 2 = ‖G z‖ := by rw [← norm_pow, hFsq z hz]
    have h2 : ‖G z‖ < 1 := mem_ball_zero_iff.mp (blaschke_mapsTo hw₀ (hf.mapsTo hz))
    nlinarith [norm_nonneg (F z)]
  have hFinj : InjOn F U := by
    intro a ha b hb hab
    have h1 : G a = G b := by rw [← hFsq a ha, ← hFsq b hb, hab]
    exact hf.injOn ha hb (blaschke_injOn hw₀ (hf.mapsTo ha) (hf.mapsTo hb) h1)
  -- normalize `F` into a competitor `g`
  obtain ⟨c, hc, hcomp⟩ := isCompetitor_normalize hFdiff hFinj hFmap hz₀ hUo
  refine ⟨fun z => c * blaschke (F z₀) (F z), hcomp, ?_⟩
  rw [derivVal_normalize hc hFdiff hFmap hz₀ hUo hcomp, hf.derivVal_eq_norm]
  -- `F z₀² = -w₀`, so `‖F z₀‖² = ‖w₀‖ ∈ (0, 1)`
  have hGz₀ : G z₀ = -w₀ := by
    show blaschke w₀ (f z₀) = -w₀
    rw [hf.center]; exact blaschke_zero hw₀
  have hFz₀ : F z₀ ^ 2 = -w₀ := by rw [hFsq z₀ hz₀, hGz₀]
  have hFz₀n : ‖F z₀‖ ^ 2 = ‖w₀‖ := by rw [← norm_pow, hFz₀, norm_neg]
  have ht0 : 0 < ‖w₀‖ := by
    rw [norm_pos_iff]
    rintro rfl
    exact homit ⟨z₀, hz₀, hf.center⟩
  have hs0 : 0 < ‖F z₀‖ := by nlinarith [norm_nonneg (F z₀)]
  -- chain rule: `2 F z₀ F'(z₀) = G'(z₀) = (1 - ‖w₀‖²) f'(z₀)`
  have hFd : DifferentiableAt ℂ F z₀ := hFdiff.differentiableAt (hUo.mem_nhds hz₀)
  have hfd : DifferentiableAt ℂ f z₀ := hf.diff.differentiableAt (hUo.mem_nhds hz₀)
  have hcast : (1 : ℂ) - ((‖w₀‖ : ℝ) : ℂ) ^ 2 = ((1 - ‖w₀‖ ^ 2 : ℝ) : ℂ) := by norm_cast
  have hGd : HasDerivAt G (((1 - ‖w₀‖ ^ 2 : ℝ) : ℂ) * deriv f z₀) z₀ := by
    have h1 := (hasDerivAt_blaschke hw₀ (hf.mapsTo hz₀)).comp z₀ hfd.hasDerivAt
    rw [hf.center, mul_zero, sub_zero, one_pow, div_one, conj_mul_self_eq_norm_sq, hcast] at h1
    exact h1
  have hev : (fun z => F z ^ 2) =ᶠ[𝓝 z₀] G := by
    filter_upwards [hUo.mem_nhds hz₀] with z hz using hFsq z hz
  have hF2 : HasDerivAt (fun z => F z ^ 2) (((1 - ‖w₀‖ ^ 2 : ℝ) : ℂ) * deriv f z₀) z₀ :=
    hGd.congr_of_eventuallyEq hev
  have hF2' : HasDerivAt (fun z => F z ^ 2) ((2 : ℕ) * F z₀ ^ (2 - 1) * deriv F z₀) z₀ :=
    hFd.hasDerivAt.fun_pow 2
  have hkey : ((1 - ‖w₀‖ ^ 2 : ℝ) : ℂ) * deriv f z₀ = 2 * F z₀ * deriv F z₀ := by
    rw [hF2.unique hF2']
    norm_num
  have hr : (0 : ℝ) ≤ 1 - ‖w₀‖ ^ 2 := by nlinarith [norm_nonneg w₀]
  have hnorm : (1 - ‖w₀‖ ^ 2) * ‖deriv f z₀‖ = 2 * ‖F z₀‖ * ‖deriv F z₀‖ := by
    have := congrArg norm hkey
    rwa [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr,
      RCLike.norm_two] at this
  -- the comparison
  have hA : 0 < ‖deriv f z₀‖ := by rw [← hf.derivVal_eq_norm]; exact hf.re_pos
  have hsg := sqrt_gain ht0 hw₀n
  rw [← hFz₀n, Real.sqrt_sq (norm_nonneg _),
    lt_div_iff₀ (show (0 : ℝ) < 2 * ‖F z₀‖ by linarith), one_mul] at hsg
  rw [lt_div_iff₀ (show (0 : ℝ) < 1 - ‖F z₀‖ ^ 2 by linarith)]
  rw [← hFz₀n] at hnorm
  have hprod : 0 < ‖deriv f z₀‖ * (1 - ‖F z₀‖ ^ 2) * (1 + ‖F z₀‖ ^ 2 - 2 * ‖F z₀‖) :=
    mul_pos (mul_pos hA (by linarith)) (by linarith)
  have h2s : 2 * ‖F z₀‖ * (‖deriv f z₀‖ * (1 - ‖F z₀‖ ^ 2)) < 2 * ‖F z₀‖ * ‖deriv F z₀‖ := by
    rw [← hnorm]
    nlinarith [hprod]
  exact lt_of_mul_lt_mul_left h2s (by positivity)

/-- **Step D.**  A maximizer is surjective onto the disc. -/
theorem surjOn_of_extremal
    (hUo : IsOpen U) (hUc : IsConnected U) (hUne : Uᶜ.Nonempty)
    (hH : HasHolomorphicSqrt U) (hz₀ : z₀ ∈ U)
    {f : ℂ → ℂ} (hf : IsCompetitor U z₀ f) (hmax : derivVal z₀ f = M U z₀) :
    f '' U = disc := by
  refine Subset.antisymm hf.mapsTo.image_subset ?_
  intro w₀ hw₀
  by_contra homit
  obtain ⟨g, hg, hlt⟩ := exists_better_of_not_surjOn hUo hUc hH hz₀ hf hw₀ homit
  have hle : derivVal z₀ g ≤ M U z₀ :=
    le_csSup (bddAbove_derivVal hUo hz₀) (mem_image_of_mem _ hg)
  rw [hmax] at hlt
  exact absurd hle (not_le.mpr hlt)

end StepD

/-! ###############################################################
    ## §8.  Main theorems
    ############################################################### -/

section Main

variable {U : Set ℂ} {z₀ : ℂ}

/-- **Riemann Mapping Theorem**, existence, under hypothesis (H). -/
theorem exists_riemannMap_of_hasHolomorphicSqrt
    (hUo : IsOpen U) (hUc : IsConnected U) (hUne : Uᶜ.Nonempty)
    (hH : HasHolomorphicSqrt U) (hz₀ : z₀ ∈ U) :
    ∃ f : ℂ → ℂ, IsCompetitor U z₀ f ∧ BijOn f U disc := by
  obtain ⟨f, hfF, hmax⟩ := exists_extremal hUo hUc hUne hH hz₀
  have hf : IsCompetitor U z₀ f := hfF
  have himg := surjOn_of_extremal hUo hUc hUne hH hz₀ hf hmax
  exact ⟨f, hf, hf.mapsTo, hf.injOn, himg.symm.subset⟩

/-- The transfer map `g ∘ f⁻¹ : 𝔻 → 𝔻` of two competitors `f`, `g`, the first of which is onto:
holomorphic, a self-map of the disc fixing `0`, with `h ∘ f = g` on `U`. -/
lemma exists_transfer (hUo : IsOpen U) (hz₀ : z₀ ∈ U) {f g : ℂ → ℂ}
    (hf : IsCompetitor U z₀ f) (hfs : BijOn f U disc) (hg : IsCompetitor U z₀ g) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h disc ∧ MapsTo h disc disc ∧ h 0 = 0 ∧
      (∀ z ∈ U, h (f z) = g z) ∧ deriv g z₀ = deriv h 0 * deriv f z₀ := by
  obtain ⟨-, hinvd⟩ := differentiableOn_invFunOn_of_injOn hUo hf.diff hf.injOn
  rw [hfs.image_eq] at hinvd
  set φ : ℂ → ℂ := Function.invFunOn f U with hφ
  have hφmap : MapsTo φ disc U := fun w hw => Function.invFunOn_mem (hfs.surjOn hw)
  have hφleft : ∀ z ∈ U, φ (f z) = z := fun z hz => hf.injOn.leftInvOn_invFunOn hz
  have hφ0 : φ 0 = z₀ := by
    have h := hφleft z₀ hz₀
    rwa [hf.center] at h
  refine ⟨fun w => g (φ w), hg.diff.comp hinvd hφmap, fun w hw => hg.mapsTo (hφmap hw),
    ?_, ?_, ?_⟩
  · show g (φ 0) = 0
    rw [hφ0]; exact hg.center
  · intro z hz
    show g (φ (f z)) = g z
    rw [hφleft z hz]
  · have hev : g =ᶠ[𝓝 z₀] fun z => g (φ (f z)) := by
      filter_upwards [hUo.mem_nhds hz₀] with z hz
      rw [hφleft z hz]
    have hfd : DifferentiableAt ℂ f z₀ := hf.diff.differentiableAt (hUo.mem_nhds hz₀)
    have hhd0 : HasDerivAt (fun w => g (φ w)) (deriv (fun w => g (φ w)) 0) (f z₀) := by
      rw [hf.center]
      exact ((hg.diff.comp hinvd hφmap).differentiableAt
        (isOpen_ball.mem_nhds (mem_ball_self one_pos))).hasDerivAt
    have hcomp := hhd0.comp z₀ hfd.hasDerivAt
    rw [hev.deriv_eq]
    exact hcomp.deriv

/-- Schwarz: the derivative of a competitor is bounded by that of an onto competitor. -/
lemma norm_deriv_le_of_bijOn (hUo : IsOpen U) (hz₀ : z₀ ∈ U) {f g : ℂ → ℂ}
    (hf : IsCompetitor U z₀ f) (hfs : BijOn f U disc) (hg : IsCompetitor U z₀ g) :
    ‖deriv g z₀‖ ≤ ‖deriv f z₀‖ := by
  obtain ⟨h, hhd, hhmap, hh0, -, hgd⟩ := exists_transfer hUo hz₀ hf hfs hg
  have hmaps : MapsTo h (ball (0 : ℂ) 1) (closedBall (h 0) 1) := by
    rw [hh0]; exact fun w hw => ball_subset_closedBall (hhmap hw)
  have hsch : ‖deriv h 0‖ ≤ 1 := Complex.norm_deriv_le_one_of_mapsTo_ball hhd hmaps one_pos
  rw [hgd, norm_mul]
  calc ‖deriv h 0‖ * ‖deriv f z₀‖ ≤ 1 * ‖deriv f z₀‖ :=
        mul_le_mul_of_nonneg_right hsch (norm_nonneg _)
    _ = ‖deriv f z₀‖ := one_mul _

/-- **Step E.**  Uniqueness, via the Schwarz lemma.

Note this is `EqOn`, not `∃!`: two functions `ℂ → ℂ` agreeing on `U` are distinct
terms, so `∃!` would be false as stated. -/
theorem riemannMap_unique
    (hUo : IsOpen U) (hUc : IsConnected U) (hz₀ : z₀ ∈ U)
    {f g : ℂ → ℂ}
    (hf : IsCompetitor U z₀ f) (hfs : BijOn f U disc)
    (hg : IsCompetitor U z₀ g) (hgs : BijOn g U disc) :
    EqOn f g U := by
  obtain ⟨h, hhd, hhmap, hh0, hhf, hgd⟩ := exists_transfer hUo hz₀ hf hfs hg
  have h1 := norm_deriv_le_of_bijOn hUo hz₀ hf hfs hg
  have h2 := norm_deriv_le_of_bijOn hUo hz₀ hg hgs hf
  have hf' : deriv f z₀ ≠ 0 := by
    intro hcon
    have := hf.re_pos
    rw [hcon, Complex.zero_re] at this
    exact lt_irrefl _ this
  have hfn : ‖deriv f z₀‖ ≠ 0 := norm_ne_zero_iff.mpr hf'
  have hh0' : deriv h 0 = deriv g z₀ / deriv f z₀ := by
    rw [hgd, mul_div_assoc, div_self hf', mul_one]
  have hhn : ‖deriv h 0‖ = 1 := by
    rw [hh0', norm_div, div_eq_one_iff_eq hfn]
    exact le_antisymm h1 h2
  obtain ⟨c, hc, hceq⟩ := schwarz_eq_rotation hhd hhmap hh0 hhn
  -- `c = deriv h 0` is a positive real of modulus one, hence `1`
  have hcd : deriv h 0 = c := by
    have hev : h =ᶠ[𝓝 0] fun z => c * z := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self one_pos)] with z hz using hceq hz
    have hid : HasDerivAt (fun z : ℂ => z) 1 0 := hasDerivAt_id 0
    have hcm : HasDerivAt (fun z : ℂ => c * z) (c * 1) 0 := hid.const_mul c
    rw [hev.deriv_eq, hcm.deriv, mul_one]
  have hfre : deriv f z₀ = (((deriv f z₀).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [hf.im_zero])
  have hgre : deriv g z₀ = (((deriv g z₀).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [hg.im_zero])
  have hcre : c = (((deriv g z₀).re / (deriv f z₀).re : ℝ) : ℂ) := by
    rw [← hcd, hh0', Complex.ofReal_div, ← hfre, ← hgre]
  have hpos : 0 < (deriv g z₀).re / (deriv f z₀).re := div_pos hg.re_pos hf.re_pos
  have hc1 : c = 1 := by
    rw [hcre] at hc
    rw [Complex.norm_real, Real.norm_of_nonneg hpos.le] at hc
    rw [hcre, hc, Complex.ofReal_one]
  intro z hz
  have h3 : h (f z) = c * f z := hceq (hf.mapsTo hz)
  rw [hhf z hz, hc1, one_mul] at h3
  exact h3.symm

/-- **Riemann Mapping Theorem**, topological form. -/
theorem exists_riemannMap
    (hUo : IsOpen U) (hUc : IsConnected U) (hUne : Uᶜ.Nonempty)
    [SimplyConnectedSpace ↥U] (hz₀ : z₀ ∈ U) :
    ∃ f : ℂ → ℂ, IsCompetitor U z₀ f ∧ BijOn f U disc :=
  exists_riemannMap_of_hasHolomorphicSqrt hUo hUc hUne
    (hasHolomorphicSqrt_of_simplyConnected hUo hUc) hz₀

/-- The inverse of a Riemann map is a holomorphic bijection `𝔻 → U`. -/
theorem invFunOn_riemannMap {U : Set ℂ} (hUo : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) (hb : BijOn f U disc) :
    DifferentiableOn ℂ (Function.invFunOn f U) disc ∧ BijOn (Function.invFunOn f U) disc U := by
  constructor
  · have h := (differentiableOn_invFunOn_of_injOn hUo hf hinj).2
    rwa [hb.image_eq] at h
  · exact hb.invOn_invFunOn.symm.bijOn hb.surjOn.mapsTo_invFunOn hb.mapsTo

/-- Corollary: any two simply connected proper subdomains of `ℂ` are biholomorphic. -/
theorem exists_biholomorph_of_simplyConnected
    {V : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U) (hUne : Uᶜ.Nonempty)
    [SimplyConnectedSpace ↥U]
    (hVo : IsOpen V) (hVc : IsConnected V) (hVne : Vᶜ.Nonempty)
    [SimplyConnectedSpace ↥V] :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ BijOn f U V ∧
      DifferentiableOn ℂ (Function.invFunOn f U) V := by
  obtain ⟨z₁, hz₁⟩ := hUc.nonempty
  obtain ⟨w₁, hw₁⟩ := hVc.nonempty
  obtain ⟨φU, hφU, hφUb⟩ := exists_riemannMap hUo hUc hUne hz₁
  obtain ⟨φV, hφV, hφVb⟩ := exists_riemannMap hVo hVc hVne hw₁
  obtain ⟨hψV, hψVb⟩ := invFunOn_riemannMap hVo hφV.diff hφV.injOn hφVb
  -- `f := φV⁻¹ ∘ φU`
  have hfd : DifferentiableOn ℂ (Function.invFunOn φV V ∘ φU) U :=
    hψV.comp hφU.diff hφUb.mapsTo
  have hfb : BijOn (Function.invFunOn φV V ∘ φU) U V := hψVb.comp hφUb
  refine ⟨Function.invFunOn φV V ∘ φU, hfd, hfb, ?_⟩
  have h := (differentiableOn_invFunOn_of_injOn hUo hfd hfb.injOn).2
  rwa [hfb.image_eq] at h

/-- Holomorphic functions on a simply connected domain have primitives.
This is homotopy invariance of contour integrals + Cauchy's theorem. -/
-- HEAVY.  Mathlib has primitives on convex / star-shaped sets; the simply connected
-- case may need to be built.  Check `Complex.hasPrimitives`, `DiffContOnCl`,
-- `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`.
theorem exists_primitive_of_simplyConnected
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U) [SimplyConnectedSpace ↥U]
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧ ∀ z ∈ U, deriv G z = g z := by
  by_cases hUne : Uᶜ.Nonempty
  · obtain ⟨z₁, hz₁⟩ := hUc.nonempty
    obtain ⟨φ, hφ, hφb⟩ := exists_riemannMap hU hUc hUne hz₁
    obtain ⟨hψ, hψb⟩ := invFunOn_riemannMap hU hφ.diff hφ.injOn hφb
    -- the transported integrand `(g ∘ ψ) · ψ'` is holomorphic on the disc
    have hh : DifferentiableOn ℂ
        (fun w => g (Function.invFunOn φ U w) * deriv (Function.invFunOn φ U) w) disc :=
      (hg.comp hψ hψb.mapsTo).mul (hψ.deriv isOpen_ball)
    obtain ⟨P, hP⟩ := hh.isExactOn_ball
    have hPd : DifferentiableOn ℂ P disc := fun w hw =>
      (hP w hw).differentiableAt.differentiableWithinAt
    refine ⟨P ∘ φ, hPd.comp hφ.diff hφb.mapsTo, fun z hz => ?_⟩
    have hφz : φ z ∈ disc := hφb.mapsTo hz
    have hφd : DifferentiableAt ℂ φ z := hφ.diff.differentiableAt (hU.mem_nhds hz)
    have hψd : DifferentiableAt ℂ (Function.invFunOn φ U) (φ z) :=
      hψ.differentiableAt (isOpen_ball.mem_nhds hφz)
    have hG : HasDerivAt (P ∘ φ)
        (g (Function.invFunOn φ U (φ z)) * deriv (Function.invFunOn φ U) (φ z) * deriv φ z) z :=
      (hP (φ z) hφz).comp z hφd.hasDerivAt
    rw [hG.deriv]
    -- `ψ (φ z) = z`, and `ψ' (φ z) · φ' z = 1` since `ψ ∘ φ = id` near `z`
    have hψφ : Function.invFunOn φ U (φ z) = z := hφ.injOn.leftInvOn_invFunOn hz
    have hone : deriv (Function.invFunOn φ U) (φ z) * deriv φ z = 1 := by
      have hev : (Function.invFunOn φ U ∘ φ) =ᶠ[𝓝 z] id := by
        filter_upwards [hU.mem_nhds hz] with w hw
        exact hφ.injOn.leftInvOn_invFunOn hw
      have h := hev.deriv_eq
      rw [deriv_id, deriv_comp z hψd hφd] at h
      exact h
    rw [hψφ, mul_assoc, hone, mul_one]
  · have hUuniv : U = univ := by
      rw [Set.not_nonempty_iff_eq_empty, compl_empty_iff] at hUne
      exact hUne
    subst hUuniv
    obtain ⟨G, hG⟩ := (differentiableOn_univ.1 hg).isExactOn_univ
    exact ⟨G, fun z _ => (hG z (mem_univ z)).differentiableAt.differentiableWithinAt,
      fun z _ => (hG z (mem_univ z)).deriv⟩

end Main

end

end RMT
