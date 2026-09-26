import LiZhongQC.Ch01.S05_ExtremalProblems
import LiZhongQC.Lemmas.DiscAutomorphism
import LiZhongQC.Lemmas.WeierstrassValues

/-!
# §14 Poincaré 度量与模函数 — The Poincaré metric and the elliptic modular function

* §14.1 the Poincaré metric of the unit disc (14.1)–(14.3), of simply connected domains and
  of the upper half-plane                               — `poincareDensityDisc`,
                                                           `poincareDensity`, `poincareDist`
* §14.2 the elliptic modular function `φ` and the Poincaré metric of `ℂ̄ ∖ {0, 1, ∞}`
                                                         — `modularPhi`, `puncturedSphereDensity`
* §14.3 `φ` via the Weierstrass `℘` function (14.10), (14.20), the function `λ(v)` (14.21),
  its product expansions (14.23), (14.24) and the estimates (14.25)–(14.27)

## What is proved here

All statements of §14.1 are proved:
* (14.2), the Poincaré length of `[0, r]`;
* the invariance of the disc metric under the automorphisms of `Δ`, and the geodesic property
  (14.3);
* the density of a simply connected domain and its independence of the Riemann map;
* the Poincaré distance and the geodesics of the upper half-plane (`poincareDist_upperHalf`,
  `upperHalf_geodesic`).

From §§14.2–14.3, the lattice identities (14.8) and (14.9) of the Weierstrass `℘` function are
proved, and so are the modular identities (14.4), (14.5) and (14.12).  The modular identities
follow from those lattice identities together with the periodicity and evenness of Mathlib's
`℘` (`PeriodPair.weierstrassP`).

Also proved (2026-09-24): the `Γ(2)`-invariance of `φ`; (14.11); (14.13)–(14.15); and (14.20), that `φ` maps `A`
conformally onto `ℍ` fixing `0, 1, ∞`.  They rest on the value distribution of `℘`
(`℘(z) = ℘(z') ↔ z ≡ ±z'`, hence `e₁, e₂, e₃` distinct; `Lemmas/WeierstrassValues.lean`, by an argument principle on
a period box), the holomorphy of `e_j` in `w`, a row / `q`-series expansion of `e₃ - e₂` and `e₁ - e₂` (signs on
`∂A`, cusp limits, asymptotics at `∞`), and a properness/degree argument (`mphi_isConformalOnto_of_W3`).  The
book's route through `v = Λ(ρ)` is not used.

The rest of §§14.2–14.3 is kept as `sorry`: the product expansions (14.23), (14.24).
Also proved (2026-09-25): the covering property of `φ` and (14.6), at the end of the file: `φ` is
`Γ(2)`-invariant, open, onto `ℂ ∖ {0, 1}`, and its fibers are the `Γ(2)`-orbits (every point is
`Γ(2)`-equivalent to one of `F = {|Re w| ≤ 1, |w ∓ 1/2| ≥ 1/2}`, `F = A ∪ (A - 1) ∪ sides`, `φ` is
injective on `A` and `φ(w - 1) = 1 - φ(w)`; non-real values first, then all values by openness of `φ`
and closedness of the orbit relation); Mathlib's quotient-covering theorem for the free, properly
discontinuous action of the index-2 subgroup `Γ(2)' = {γ ∈ Γ(2) : γ₀₀ ≡ 1 mod 4}` then gives the
covering.  (14.6) follows since `|φ'(w)| Im w` is `Γ(2)`-invariant.
Also proved (2026-09-24): (14.19), (14.21) `λ(v) = -φ(iv)`, via `-℘` mapping the quarter-period rectangle conformally
onto `ℍ` (`rect_wp_conformal`, from the value distribution of `℘`) and a modulus comparison `Λ(ρ) = v`.
Also proved (2026-09-24): the monotonicity and limits of `Λ`, `λ ∘ Λ = id`, and the estimates (14.25), (14.26), from
(5.18) `Λ(ρ) = (2/π) μ(√(1/(1+ρ)))` and the bounds (14.27) on `μ`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-! ## Curves between two points -/

/-- `γ` is a rectifiable curve in `D` from `z₁` to `z₂` (Lipschitz on `[0,1]`). -/
def IsPathIn (D : Set ℂ) (z₁ z₂ : ℂ) (γ : LRCurve) : Prop :=
  (∃ K : ℝ≥0, LipschitzOnWith K γ.toFun (Icc 0 1)) ∧ γ.toFun 0 = z₁ ∧ γ.toFun 1 = z₂ ∧
    γ.closedTrace ⊆ D

/-- The distance in `D` between `z₁` and `z₂` for the conformal metric `ρ |dz|`: the infimum of
the `ρ`-lengths of the rectifiable curves in `D` joining them. -/
def metricDist (D : Set ℂ) (ρ : ℂ → ℝ≥0∞) (z₁ z₂ : ℂ) : ℝ≥0∞ :=
  ⨅ γ ∈ {γ : LRCurve | IsPathIn D z₁ z₂ γ}, γ.rhoLength ρ

/-! ## §14.1 The Poincaré metric of the unit disc -/

/-- (14.1): the Poincaré density `2/(1 - |z|²)` of the unit disc. -/
def poincareDensityDisc (z : ℂ) : ℝ := 2 / (1 - ‖z‖ ^ 2)

/-- (14.2): the Poincaré length of the segment `[0, r]` is `ln((1+r)/(1-r))`. -/
theorem eq14_2 {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    ∫ x in (0 : ℝ)..r, 2 / (1 - x ^ 2) = Real.log ((1 + r) / (1 - r)) := by
  have huIcc : Set.uIcc (0 : ℝ) r = Set.Icc 0 r := Set.uIcc_of_le hr₀.le
  have hpos : ∀ x ∈ Set.Icc (0 : ℝ) r, 0 < 1 + x ∧ 0 < 1 - x := by
    intro x hx
    constructor <;> [linarith [hx.1]; linarith [hx.2]]
  -- `log (1 + x) - log (1 - x)` is an antiderivative of `2/(1 - x²)`
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) r,
      HasDerivAt (fun y : ℝ => Real.log (1 + y) - Real.log (1 - y)) (2 / (1 - x ^ 2)) x := by
    intro x hx
    rw [huIcc] at hx
    obtain ⟨hp1, hp2⟩ := hpos x hx
    have h1 : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
      simpa using ((hasDerivAt_id x).const_add (1 : ℝ)).log hp1.ne'
    have h2 : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1 / (1 - x)) x := by
      simpa using ((hasDerivAt_id x).const_sub (1 : ℝ)).log hp2.ne'
    have h3 := h1.sub h2
    have hne1 : (1 : ℝ) + x ≠ 0 := hp1.ne'
    have hne2 : (1 : ℝ) - x ≠ 0 := hp2.ne'
    have hx2 : (1 : ℝ) - x ^ 2 ≠ 0 := by nlinarith
    convert h3 using 1
    field_simp
    ring
  have hcont : ContinuousOn (fun x : ℝ => 2 / (1 - x ^ 2)) (Set.uIcc 0 r) := by
    rw [huIcc]
    refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
    intro x hx
    obtain ⟨hp1, hp2⟩ := hpos x hx
    have hfac : (1 : ℝ) - x ^ 2 = (1 + x) * (1 - x) := by ring
    rw [hfac]
    positivity
  have hint : IntervalIntegrable (fun x : ℝ => 2 / (1 - x ^ 2)) volume 0 r :=
    hcont.intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have h1r : (0 : ℝ) < 1 + r := by linarith
  have h2r : (0 : ℝ) < 1 - r := by linarith
  rw [Real.log_div h1r.ne' h2r.ne']
  simp

/-- The Poincaré density of the disc is invariant under `z ↦ c M_a(z)` with `|c| = 1`, which by
`exists_rotation_blaschke_of_isConformalOnto_unitDisc` is the general conformal self-map. -/
theorem poincareDensityDisc_rotBlaschke {c a : ℂ} (hc : ‖c‖ = 1) (ha : ‖a‖ < 1) {z : ℂ}
    (hz : ‖z‖ < 1) :
    poincareDensityDisc (c * blaschke a z) * ‖deriv (fun w : ℂ => c * blaschke a w) z‖
      = poincareDensityDisc z := by
  have hden := blaschke_den_ne_zero ha hz
  have hNpos : 0 < normSq (1 - conj a * z) := normSq_pos.mpr hden
  have has : normSq a < 1 := normSq_lt_one_iff.mpr ha
  have hzs : normSq z < 1 := normSq_lt_one_iff.mpr hz
  have hd : HasDerivAt (fun w : ℂ => c * blaschke a w)
      (c * ((1 - a * conj a) / (1 - conj a * z) ^ 2)) z := (hasDerivAt_blaschke ha hz).const_mul _
  have hnum : (1 : ℂ) - a * conj a = ((1 - normSq a : ℝ) : ℂ) := by
    rw [Complex.mul_conj]; push_cast; ring
  have hdn : ‖deriv (fun w : ℂ => c * blaschke a w) z‖
      = (1 - normSq a) / normSq (1 - conj a * z) := by
    rw [hd.deriv, norm_mul, hc, one_mul, norm_div, hnum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith), norm_pow, Complex.sq_norm]
  have himg : poincareDensityDisc (c * blaschke a z)
      = 2 * normSq (1 - conj a * z) / ((1 - normSq z) * (1 - normSq a)) := by
    have hval : ‖c * blaschke a z‖ ^ 2 = normSq (blaschke a z) := by
      rw [norm_mul, hc, one_mul, Complex.sq_norm]
    rw [poincareDensityDisc, hval, one_sub_normSq_blaschke ha hz, div_div_eq_mul_div]
  rw [himg, hdn, poincareDensityDisc, Complex.sq_norm]
  have h1 : (1 : ℝ) - normSq z ≠ 0 := by linarith
  have h2 : (1 : ℝ) - normSq a ≠ 0 := by linarith
  field_simp

/-- §14.1: the Poincaré metric is invariant under the automorphisms
`w = e^{iα}(z - z₀)/(1 - z̄₀ z)` of the disc: `2|dw|/(1 - |w|²) = 2|dz|/(1 - |z|²)`. -/
theorem poincareDensityDisc_invariant {z₀ : ℂ} (hz₀ : z₀ ∈ unitDisc) (α : ℝ) {z : ℂ}
    (hz : z ∈ unitDisc) :
    poincareDensityDisc (exp (α * I) * (z - z₀) / (1 - conj z₀ * z)) *
        ‖deriv (fun z => exp (α * I) * (z - z₀) / (1 - conj z₀ * z)) z‖ =
      poincareDensityDisc z := by
  have he : (fun w : ℂ => exp (α * I) * (w - z₀) / (1 - conj z₀ * w))
      = fun w : ℂ => exp (α * I) * blaschke z₀ w := by
    funext w
    rw [blaschke, mul_div_assoc]
  have hpt : exp (α * I) * (z - z₀) / (1 - conj z₀ * z) = exp (α * I) * blaschke z₀ z := by
    rw [blaschke, mul_div_assoc]
  rw [hpt, he]
  exact poincareDensityDisc_rotBlaschke (Complex.norm_exp_ofReal_mul_I α)
    (mem_ball_zero_iff.mp hz₀) (mem_ball_zero_iff.mp hz)

/-! ### Infrastructure for the Poincaré length lower bound

The radial primitive `F(s) = log((1+s)/(1-s))` of the disc density, and the comparison
`|d‖γ‖/dt| ≤ ‖γ'‖` that lets a curve's `ρ`-length be bounded below by the radial one. -/

/-- `F s = log(1+s) - log(1-s)`, the primitive of the disc density along a radius. -/
noncomputable def logRatio (s : ℝ) : ℝ := Real.log (1 + s) - Real.log (1 - s)

theorem logRatio_zero : logRatio 0 = 0 := by simp [logRatio]

theorem logRatio_eq {s : ℝ} (h₁ : -1 < s) (h₂ : s < 1) :
    logRatio s = Real.log ((1 + s) / (1 - s)) := by
  rw [logRatio, Real.log_div (by linarith) (by linarith)]

/-- `F' s = 1/(1+s) + 1/(1-s) = 2/(1-s²)`, the disc density `2/(1-s²)` along a radius. -/
theorem hasDerivAt_logRatio {s : ℝ} (h₁ : -1 < s) (h₂ : s < 1) :
    HasDerivAt logRatio (2 / (1 - s ^ 2)) s := by
  have h1 : (1 : ℝ) + s ≠ 0 := by linarith
  have h2 : (1 : ℝ) - s ≠ 0 := by linarith
  have d1 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + s)) s := by
    have := (((hasDerivAt_id s).const_add 1).log h1)
    simpa [one_div] using this
  have d2 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1 / (1 - s)) s := by
    have h := ((hasDerivAt_id s).const_sub 1).log h2
    simpa [div_eq_iff h2] using h
  have h3 : (1 : ℝ) - s ^ 2 ≠ 0 := by
    have : (1 : ℝ) - s ^ 2 = (1 - s) * (1 + s) := by ring
    rw [this]
    exact mul_ne_zero h2 h1
  have := d1.sub d2
  convert this using 1
  · first | rfl | (funext x; simp [logRatio])
  · field_simp
    ring

/-- On `[0, M]` with `M < 1` the primitive is Lipschitz, with constant `1 + 1/(1-M)`. -/
theorem lipschitzOn_logRatio {M : ℝ} (hM0 : 0 ≤ M) (hM1 : M < 1) :
    LipschitzOnWith (Real.toNNReal (1 + 1 / (1 - M))) logRatio (Icc 0 M) := by
  refine (convex_Icc (0 : ℝ) M).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun s => 2 / (1 - s ^ 2)) (fun s hs => ?_) (fun s hs => ?_)
  · exact (hasDerivAt_logRatio (by linarith [hs.1]) (by linarith [hs.2])).hasDerivWithinAt
  · obtain ⟨hs0, hsM⟩ := hs
    have h1s : 0 < 1 - s := by linarith
    have h1M : 0 < 1 - M := by linarith
    have hsp : 0 < 1 + s := by linarith
    have hpos : 0 < 1 - s ^ 2 := by nlinarith
    have hle : 2 / (1 - s ^ 2) ≤ 1 + 1 / (1 - M) := by
      have hsplit : 2 / (1 - s ^ 2) = 1 / (1 - s) + 1 / (1 + s) := by
        field_simp
        ring
      rw [hsplit]
      have ha : 1 / (1 - s) ≤ 1 / (1 - M) := by
        apply one_div_le_one_div_of_le h1M
        linarith
      have hb : 1 / (1 + s) ≤ 1 := by
        rw [div_le_one hsp]
        linarith
      linarith
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity),
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact hle

/-- Wherever both derivatives exist, the derivative of `‖f‖` is dominated by `‖f'‖`: the norm is
`1`-Lipschitz, so the difference quotients are dominated termwise. -/
theorem abs_deriv_norm_le {f : ℝ → ℂ} {c : ℂ} {d t : ℝ}
    (hf : HasDerivAt f c t) (hu : HasDerivAt (fun s => ‖f s‖) d t) : |d| ≤ ‖c‖ := by
  have hf' : Tendsto (slope f t) (𝓝[≠] t) (𝓝 c) := hasDerivAt_iff_tendsto_slope.mp hf
  have hu' : Tendsto (slope (fun s => ‖f s‖) t) (𝓝[≠] t) (𝓝 d) :=
    hasDerivAt_iff_tendsto_slope.mp hu
  have hdom : ∀ y : ℝ, |slope (fun s => ‖f s‖) t y| ≤ ‖slope f t y‖ := by
    intro y
    rcases eq_or_ne y t with rfl | hy
    · simp [slope_same]
    · have hpos : (0 : ℝ) < |y - t| := abs_pos.mpr (sub_ne_zero.mpr hy)
      have e1 : slope (fun s => ‖f s‖) t y = (‖f y‖ - ‖f t‖) / (y - t) := slope_def_field _ _ _
      have e2 : ‖slope f t y‖ = ‖f y - f t‖ / |y - t| := by
        rw [slope, vsub_eq_sub, norm_smul, norm_inv, Real.norm_eq_abs]
        ring
      rw [e1, e2, abs_div]
      gcongr
      exact abs_norm_sub_norm_le _ _
  have h1 : Tendsto (fun y => |slope (fun s => ‖f s‖) t y|) (𝓝[≠] t) (𝓝 |d|) := hu'.abs
  have h2 : Tendsto (fun y => ‖slope f t y‖) (𝓝[≠] t) (𝓝 ‖c‖) := hf'.norm
  exact le_of_tendsto_of_tendsto' h1 h2 hdom

/-- `re` and `im` are `1`-Lipschitz. -/
theorem lipschitzWith_re : LipschitzWith 1 Complex.re :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa [Complex.dist_eq, Real.dist_eq, ← Complex.sub_re] using Complex.abs_re_le_norm (x - y)

theorem lipschitzWith_im : LipschitzWith 1 Complex.im :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa [Complex.dist_eq, Real.dist_eq, ← Complex.sub_im] using Complex.abs_im_le_norm (x - y)

/-- A map `ℝ → ℂ` Lipschitz on `[a,b]` is differentiable almost everywhere there, via its real and
imaginary parts (absolutely continuous, hence a.e. differentiable).  Mathlib's
`AbsolutelyContinuousOnInterval.ae_differentiableAt` is stated only for real-valued functions. -/
theorem ae_differentiableAt_of_lipschitzOn {f : ℝ → ℂ} {K : ℝ≥0} {a b : ℝ}
    (hf : LipschitzOnWith K f (uIcc a b)) :
    ∀ᵐ t, t ∈ uIcc a b → DifferentiableAt ℝ f t := by
  have hre : AbsolutelyContinuousOnInterval (fun t => (f t).re) a b :=
    ((lipschitzWith_re.comp_lipschitzOnWith hf).weaken
      (one_mul K).le).absolutelyContinuousOnInterval
  have him : AbsolutelyContinuousOnInterval (fun t => (f t).im) a b :=
    ((lipschitzWith_im.comp_lipschitzOnWith hf).weaken
      (one_mul K).le).absolutelyContinuousOnInterval
  filter_upwards [hre.ae_differentiableAt, him.ae_differentiableAt] with t h1 h2 ht
  have d1 := (h1 ht).hasDerivAt
  have d2 := (h2 ht).hasDerivAt
  have e : f = fun s => ((f s).re : ℂ) + ((f s).im : ℂ) * I := by
    funext s
    exact (Complex.re_add_im _).symm
  rw [e]
  exact (d1.ofReal_comp.add (d2.ofReal_comp.mul_const I)).differentiableAt

/-- For an integrable real function, `ofReal` of the integral is at most the lower integral of
`ofReal`: the negative part only helps.  This is the `ℝ`-to-`ℝ≥0∞` seam between the fundamental
theorem of calculus and `LRCurve.rhoLength`. -/
theorem ofReal_setIntegral_le_lintegral {f : ℝ → ℝ} {s : Set ℝ} (hf : IntegrableOn f s) :
    ENNReal.ofReal (∫ t in s, f t) ≤ ∫⁻ t in s, ENNReal.ofReal (f t) := by
  have hmax : IntegrableOn (fun t => max (f t) 0) s := by
    refine MeasureTheory.Integrable.mono hf
      (hf.aestronglyMeasurable.sup aestronglyMeasurable_const)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rcases le_total (f t) 0 with h | h
    · rw [max_eq_right h]; simp
    · rw [max_eq_left h]
  have hle : ∫ t in s, f t ≤ ∫ t in s, max (f t) 0 :=
    setIntegral_mono_ae hf hmax (Filter.Eventually.of_forall fun t => le_max_left _ _)
  have heq : ∀ t, ENNReal.ofReal (max (f t) 0) = ENNReal.ofReal (f t) := by
    intro t
    rcases le_total (f t) 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_eq_zero.mpr h]
    · rw [max_eq_left h]
  calc ENNReal.ofReal (∫ t in s, f t)
      ≤ ENNReal.ofReal (∫ t in s, max (f t) 0) := ENNReal.ofReal_le_ofReal hle
    _ = ∫⁻ t in s, ENNReal.ofReal (max (f t) 0) :=
        ofReal_integral_eq_lintegral_ofReal hmax
          (Filter.Eventually.of_forall fun t => le_max_right _ _)
    _ = ∫⁻ t in s, ENNReal.ofReal (f t) := by simp_rw [heq]

/-- §14.1: every curve joining `0` to `r ∈ (0,1)` has Poincaré length at least
`ln((1+r)/(1-r))`, the length of the radius.

The curve's closed trace is a compact subset of `Δ`, so `‖γ‖ ≤ M < 1`; on `[0,M]` the primitive
`F(s) = log((1+s)/(1-s))` of the radial density is Lipschitz, so `F ∘ ‖γ‖` is absolutely
continuous and the fundamental theorem of calculus evaluates `∫ (F ∘ ‖γ‖)'` as `F(r)`.  Pointwise
`(F ∘ ‖γ‖)' = F'(‖γ‖) · (‖γ‖)' ≤ F'(‖γ‖) · ‖γ'‖`, which is the integrand of the `ρ`-length. -/
theorem poincare_segment_shortest {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {γ : LRCurve}
    (hγ : IsPathIn unitDisc 0 r γ) :
    ENNReal.ofReal (Real.log ((1 + r) / (1 - r))) ≤
      γ.rhoLength (fun z => ENNReal.ofReal (poincareDensityDisc z)) := by
  obtain ⟨⟨K, hK⟩, h0, h1, htr⟩ := hγ
  have huIcc : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  -- the closed trace is compact inside `Δ`, so `‖γ‖ ≤ M < 1`
  have hcont : ContinuousOn γ.toFun (Icc 0 1) := hK.continuousOn
  have hne : (γ.toFun '' Icc (0 : ℝ) 1).Nonempty := ⟨γ.toFun 0, ⟨0, by norm_num, rfl⟩⟩
  have hcompact : IsCompact (γ.toFun '' Icc (0 : ℝ) 1) := isCompact_Icc.image_of_continuousOn hcont
  obtain ⟨z₀, hz₀mem, hz₀max⟩ := hcompact.exists_isMaxOn hne continuous_norm.continuousOn
  set M : ℝ := ‖z₀‖ with hMdef
  have hM1 : M < 1 := mem_ball_zero_iff.mp (htr hz₀mem)
  have hM0 : 0 ≤ M := norm_nonneg _
  have hbd : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ.toFun t‖ ≤ M := fun t ht => hz₀max ⟨t, ht, rfl⟩
  -- `u = ‖γ‖`, `G = F ∘ u`
  set u : ℝ → ℝ := fun t => ‖γ.toFun t‖ with hudef
  have hu : LipschitzOnWith K u (Icc (0 : ℝ) 1) :=
    LipschitzWith.comp_lipschitzOnWith lipschitzWith_one_norm hK |>.weaken (one_mul K).le
  have hmaps : MapsTo u (Icc (0 : ℝ) 1) (Icc 0 M) := fun t ht => ⟨norm_nonneg _, hbd t ht⟩
  set G : ℝ → ℝ := fun t => logRatio (u t) with hGdef
  have hGac : AbsolutelyContinuousOnInterval G 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := Real.toNNReal (1 + 1 / (1 - M)) * K)
    rw [huIcc]
    exact (lipschitzOn_logRatio hM0 hM1).comp hu hmaps
  have huac : AbsolutelyContinuousOnInterval u 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := K)
    rw [huIcc]; exact hu
  -- the fundamental theorem of calculus
  have hG0 : G 0 = 0 := by simp only [hGdef, hudef, h0, norm_zero, logRatio_zero]
  have hG1 : G 1 = Real.log ((1 + r) / (1 - r)) := by
    have hu1 : u 1 = r := by
      simp only [hudef, h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₀]
    simp only [hGdef, hu1]
    exact logRatio_eq (by linarith) hr₁
  have hFTC : ∫ t in (0 : ℝ)..1, deriv G t = Real.log ((1 + r) / (1 - r)) := by
    rw [hGac.integral_deriv_eq_sub, hG0, hG1, sub_zero]
  -- the pointwise comparison, almost everywhere on `(0,1)`
  have hae : ∀ᵐ t, t ∈ Ioo (0 : ℝ) 1 →
      deriv G t ≤ poincareDensityDisc (γ.toFun t) * ‖deriv γ.toFun t‖ := by
    have hγae : ∀ᵐ t, t ∈ uIcc (0 : ℝ) 1 → DifferentiableAt ℝ γ.toFun t :=
      ae_differentiableAt_of_lipschitzOn (K := K) (by rw [huIcc]; exact hK)
    filter_upwards [hγae, huac.ae_differentiableAt] with t hγt hut ht
    have htI : t ∈ uIcc (0 : ℝ) 1 := by rw [huIcc]; exact Ioo_subset_Icc_self ht
    have hnorm : |deriv u t| ≤ ‖deriv γ.toFun t‖ :=
      abs_deriv_norm_le (hγt htI).hasDerivAt (hut htI).hasDerivAt
    have hutM : u t ≤ M := hbd t (Ioo_subset_Icc_self ht)
    have hutlt : u t < 1 := lt_of_le_of_lt hutM hM1
    have hutnn : 0 ≤ u t := norm_nonneg _
    have hden : 0 < 1 - (u t) ^ 2 := by nlinarith
    have hGd : HasDerivAt G (2 / (1 - (u t) ^ 2) * deriv u t) t :=
      (hasDerivAt_logRatio (by linarith : (-1 : ℝ) < u t) hutlt).comp t (hut htI).hasDerivAt
    have hpos : 0 < 2 / (1 - (u t) ^ 2) := by positivity
    have hdens : poincareDensityDisc (γ.toFun t) = 2 / (1 - (u t) ^ 2) := rfl
    rw [hGd.deriv, hdens]
    calc 2 / (1 - (u t) ^ 2) * deriv u t
        ≤ 2 / (1 - (u t) ^ 2) * |deriv u t| := by nlinarith [le_abs_self (deriv u t)]
      _ ≤ 2 / (1 - (u t) ^ 2) * ‖deriv γ.toFun t‖ := by nlinarith
  -- assemble
  have hderivGint : IntegrableOn (deriv G) (Ioo (0 : ℝ) 1) :=
    (hGac.intervalIntegrable_deriv.1).mono_set Ioo_subset_Ioc_self
  have hIoo : ∫ t in (0 : ℝ)..1, deriv G t = ∫ t in Ioo (0 : ℝ) 1, deriv G t := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact (setIntegral_congr_set Ioo_ae_eq_Ioc).symm
  calc ENNReal.ofReal (Real.log ((1 + r) / (1 - r)))
      = ENNReal.ofReal (∫ t in Ioo (0 : ℝ) 1, deriv G t) := by rw [← hIoo, hFTC]
    _ ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (deriv G t) :=
        ofReal_setIntegral_le_lintegral hderivGint
    _ ≤ ∫⁻ t in Ioo (0 : ℝ) 1,
          ENNReal.ofReal (poincareDensityDisc (γ.toFun t)) * ‖deriv γ.toFun t‖ₑ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hae] with t ht hb
        have hle := hb ht
        have hutM : u t ≤ M := hbd t (Ioo_subset_Icc_self ht)
        have hden : 0 < 1 - (u t) ^ 2 := by nlinarith [norm_nonneg (γ.toFun t), hM1, hM0]
        have hdnn : 0 ≤ poincareDensityDisc (γ.toFun t) := by
          show 0 ≤ 2 / (1 - (u t) ^ 2)
          positivity
        calc ENNReal.ofReal (deriv G t)
            ≤ ENNReal.ofReal (poincareDensityDisc (γ.toFun t) * ‖deriv γ.toFun t‖) :=
              ENNReal.ofReal_le_ofReal hle
          _ = ENNReal.ofReal (poincareDensityDisc (γ.toFun t)) * ‖deriv γ.toFun t‖ₑ := by
              rw [ENNReal.ofReal_mul hdnn, ofReal_norm]
    _ = γ.rhoLength (fun z => ENNReal.ofReal (poincareDensityDisc z)) := rfl

/-! ### The radius as a locally rectifiable curve

The witness needed for the upper bound in (14.3): `metricDist` is an infimum over paths,
so a curve joining the two points must actually be exhibited. -/

/-- The straight segment `t ↦ t w` from `0` to `w`, as a locally rectifiable curve. -/
def segCurve (w : ℂ) : LRCurve where
  toFun := fun t => (t : ℂ) * w
  locallyLipschitzOn := by
    intro x _
    refine ⟨‖w‖₊, univ, univ_mem, ?_⟩
    rw [lipschitzOnWith_univ]
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Complex.dist_eq, ← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Real.dist_eq]
    simp [mul_comm, coe_nnnorm]

@[simp] theorem segCurve_apply (w : ℂ) (t : ℝ) : (segCurve w).toFun t = (t : ℂ) * w := rfl

theorem hasDerivAt_segCurve (w : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (s : ℂ) * w) w t := by
  have h : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  simpa using h.mul_const w

@[simp] theorem segCurve_deriv (w : ℂ) (t : ℝ) : deriv (segCurve w).toFun t = w :=
  (hasDerivAt_segCurve w t).deriv

theorem segCurve_norm {w : ℂ} {t : ℝ} (ht : 0 ≤ t) : ‖(segCurve w).toFun t‖ = t * ‖w‖ := by
  rw [segCurve_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]



/-- The `ρ`-length of the radius `[0, w]` is `ln((1+|w|)/(1-|w|))`. -/
theorem rhoLength_segCurve {s : ℝ} (hs₀ : 0 < s) (hs₁ : s < 1) {w : ℂ} (hw : ‖w‖ = s) :
    (segCurve w).rhoLength (fun z => ENNReal.ofReal (poincareDensityDisc z))
      = ENNReal.ofReal (Real.log ((1 + s) / (1 - s))) := by
  have hden : ∀ t ∈ Icc (0 : ℝ) 1, 0 < 1 - (t * s) ^ 2 := by
    intro t ht
    have h1 : t * s ≤ s := by nlinarith [ht.1, ht.2]
    have h2 : 0 ≤ t * s := by nlinarith [ht.1]
    nlinarith
  set g : ℝ → ℝ := fun t => 2 * s / (1 - (t * s) ^ 2) with hgdef
  have hgcont : ContinuousOn g (Icc (0 : ℝ) 1) :=
    ContinuousOn.div continuousOn_const (by fun_prop) fun t ht => ne_of_gt (hden t ht)
  have hgint : IntegrableOn g (Ioo (0 : ℝ) 1) :=
    (hgcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hgnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact le_of_lt (div_pos (by linarith) (hden t (Ioo_subset_Icc_self ht)))
  -- the integrand matches `g`
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1,
      ENNReal.ofReal (poincareDensityDisc ((segCurve w).toFun t))
          * ‖deriv (segCurve w).toFun t‖ₑ = ENNReal.ofReal (g t) := by
    intro t ht
    have hn : ‖(segCurve w).toFun t‖ = t * s := by
      rw [segCurve_norm ht.1.le, hw]
    have hd : poincareDensityDisc ((segCurve w).toFun t) = 2 / (1 - (t * s) ^ 2) := by
      rw [poincareDensityDisc, hn]
    have hpos : (0:ℝ) ≤ 2 / (1 - (t * s) ^ 2) :=
      le_of_lt (div_pos (by norm_num) (hden t (Ioo_subset_Icc_self ht)))
    rw [hd, segCurve_deriv, ← ofReal_norm, hw, ← ENNReal.ofReal_mul hpos]
    congr 1
    rw [hgdef]
    ring
  rw [LRCurve.rhoLength, setLIntegral_congr_fun measurableSet_Ioo hpt,
    ← ofReal_integral_eq_lintegral_ofReal hgint hgnn]
  congr 1
  -- the substitution `x = t s`
  have hIoo : ∫ t in Ioo (0 : ℝ) 1, g t = ∫ t in (0 : ℝ)..1, g t := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact setIntegral_congr_set Ioo_ae_eq_Ioc
  rw [hIoo, hgdef]
  have hsub : ∫ t in (0 : ℝ)..1, 2 * s / (1 - (t * s) ^ 2)
      = s * ∫ t in (0 : ℝ)..1, 2 / (1 - (t * s) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; ring
  rw [hsub, intervalIntegral.integral_comp_mul_right (fun x => 2 / (1 - x ^ 2)) (ne_of_gt hs₀),
    zero_mul, one_mul, eq14_2 hs₀ hs₁, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (ne_of_gt hs₀), one_mul]

/-- The `ρ`-length of the radius, allowing the degenerate case `w = 0`: needed because `z₁ = z₂`
in (14.3) collapses the segment to a point. -/
theorem rhoLength_segCurve_of_nonneg {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s < 1) {w : ℂ} (hw : ‖w‖ = s) :
    (segCurve w).rhoLength (fun z => ENNReal.ofReal (poincareDensityDisc z))
      = ENNReal.ofReal (Real.log ((1 + s) / (1 - s))) := by
  rcases eq_or_lt_of_le hs₀ with h | h
  · have hw0 : w = 0 := by rw [← norm_eq_zero, hw, ← h]
    subst hw0
    rw [← h]
    norm_num [LRCurve.rhoLength]
  · exact rhoLength_segCurve h hs₁ hw

/-- The disc density pulls back to itself under a Blaschke factor — the form
`LRCurve.rhoLength_image_conformal` consumes. -/
theorem poincareDensityDisc_pullback_blaschke {a : ℂ} (ha : ‖a‖ < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    poincareDensityDisc (blaschke a z) * ‖deriv (blaschke a) z‖ = poincareDensityDisc z := by
  simpa using poincareDensityDisc_rotBlaschke (c := 1) (by simp) ha hz

/-- ...and under a rotation. -/
theorem poincareDensityDisc_pullback_rot {c : ℂ} (hc : ‖c‖ = 1) {z : ℂ} (hz : ‖z‖ < 1) :
    poincareDensityDisc (c * z) * ‖deriv (fun w : ℂ => c * w) z‖ = poincareDensityDisc z := by
  have h := poincareDensityDisc_rotBlaschke (a := 0) hc (by simp) hz
  simpa [blaschke] using h

/-- A rotation is a conformal self-map of the disc. -/
theorem isConformalOnto_rot {c : ℂ} (hc : ‖c‖ = 1) :
    IsConformalOnto (fun z => c * z) unitDisc unitDisc := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; norm_num at hc
  refine ⟨by fun_prop, fun z₁ _ z₂ _ h => mul_left_cancel₀ hc0 h, ?_⟩
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine mem_ball_zero_iff.mpr ?_
    rw [norm_mul, hc, one_mul]
    exact mem_ball_zero_iff.mp hy
  · intro hz
    refine ⟨c⁻¹ * z, ?_, by field_simp⟩
    refine mem_ball_zero_iff.mpr ?_
    rw [norm_mul, norm_inv, hc, inv_one, one_mul]
    exact mem_ball_zero_iff.mp hz

/-- Composing a curve in `Δ` with a conformal self-map `z ↦ c M_a(z)` leaves the Poincaré length
unchanged: the density pulls back to itself. -/
theorem rhoLength_comp_rotBlaschke {c a : ℂ} (hc : ‖c‖ = 1) (ha : ‖a‖ < 1)
    {γ γ' : LRCurve} (hγ : γ.trace ⊆ unitDisc)
    (heq : EqOn γ'.toFun ((fun z => c * blaschke a z) ∘ γ.toFun) (Ioo 0 1)) :
    γ'.rhoLength (fun z => ENNReal.ofReal (poincareDensityDisc z))
      = γ.rhoLength (fun z => ENNReal.ofReal (poincareDensityDisc z)) := by
  have hconf : IsConformalOnto (fun z => c * blaschke a z) unitDisc unitDisc :=
    (isConformalOnto_rot hc).comp (isConformalOnto_blaschke ha)
  rw [LRCurve.rhoLength_image_conformal (D := unitDisc) isOpen_ball hconf hγ heq]
  refine LRCurve.rhoLength_congr fun z hz => ?_
  have hmem := hγ hz
  have hzd : ‖z‖ < 1 := mem_ball_zero_iff.mp hmem
  have himg : ‖c * blaschke a z‖ < 1 := by
    rw [norm_mul, hc, one_mul]
    exact blaschke_mem_unitDisc ha hzd
  have hdnn : (0 : ℝ) ≤ poincareDensityDisc (c * blaschke a z) := by
    have : 0 < 1 - ‖c * blaschke a z‖ ^ 2 := by nlinarith [norm_nonneg (c * blaschke a z)]
    exact le_of_lt (div_pos (by norm_num) this)
  rw [indicator_of_mem hmem, ← ofReal_norm, ← ENNReal.ofReal_mul hdnn,
    poincareDensityDisc_rotBlaschke hc ha hzd]

/-! ### Paths and holomorphic maps -/

/-- A holomorphic function on an open set is locally Lipschitz there. -/
theorem locallyLipschitzOn_of_differentiableOn_open {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D) : LocallyLipschitzOn D f := by
  intro z hz
  obtain ⟨K, t, ht, hK⟩ :=
    (((hf.analyticAt (hD.mem_nhds hz)).contDiffAt (n := 1)).restrict_scalars ℝ).exists_lipschitzOnWith
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩

/-- The image of a path in `D` under a holomorphic map of `D` into `D'` is a path in `D'`: the map
is Lipschitz on the compact closed trace. -/
theorem exists_isPathIn_comp {D D' : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D) (hmaps : MapsTo f D D') {z₁ z₂ : ℂ} {γ : LRCurve}
    (hγ : IsPathIn D z₁ z₂ γ) :
    ∃ γ' : LRCurve, γ'.toFun = f ∘ γ.toFun ∧ IsPathIn D' (f z₁) (f z₂) γ' := by
  obtain ⟨⟨K, hK⟩, h0, h1, htr⟩ := hγ
  have hcpt : IsCompact γ.closedTrace := isCompact_Icc.image_of_continuousOn hK.continuousOn
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hcpt
    ((locallyLipschitzOn_of_differentiableOn_open hD hf).mono htr)
  have hcomp : LipschitzOnWith (L * K) (f ∘ γ.toFun) (Icc 0 1) :=
    hL.comp hK (mapsTo_image γ.toFun (Icc 0 1))
  refine ⟨⟨f ∘ γ.toFun, fun x hx =>
    ⟨L * K, Icc 0 1, mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2), hcomp⟩⟩,
    rfl, ⟨L * K, hcomp⟩, ?_, ?_, ?_⟩
  · show f (γ.toFun 0) = f z₁
    rw [h0]
  · show f (γ.toFun 1) = f z₂
    rw [h1]
  · rintro _ ⟨t, ht, rfl⟩
    exact hmaps (htr ⟨t, ht, rfl⟩)

/-- Every complex number is rotated onto its modulus. -/
theorem exists_rot_mul_eq_norm (w : ℂ) : ∃ c : ℂ, ‖c‖ = 1 ∧ c * w = (‖w‖ : ℂ) := by
  by_cases hw : w = 0
  · exact ⟨1, by simp, by simp [hw]⟩
  · refine ⟨(‖w‖ : ℂ) / w, ?_, ?_⟩
    · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hw)]
    · field_simp

/-- The inverse of `z ↦ c M_a(z)` is again of this form: `M_{-a}(c̄ w) = c̄ M_{-ca}(w)`. -/
theorem blaschke_neg_conj_mul {c a w : ℂ} (hc : ‖c‖ = 1) :
    blaschke (-a) (conj c * w) = conj c * blaschke (-(c * a)) w := by
  have hcc : conj c * c = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  show (conj c * w - -a) / (1 - conj (-a) * (conj c * w))
    = conj c * ((w - -(c * a)) / (1 - conj (-(c * a)) * w))
  rw [mul_div_assoc']
  congr 1
  · linear_combination (-a) * hcc
  · simp only [map_neg, map_mul]
    ring

/-- The segment `[0, s]` of the real axis, `0 ≤ s < 1`, is a path in the disc. -/
theorem isPathIn_segCurve {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s < 1) :
    IsPathIn unitDisc 0 (s : ℂ) (segCurve (s : ℂ)) := by
  refine ⟨⟨‖(s : ℂ)‖₊, ?_⟩, by simp, by simp, ?_⟩
  · refine LipschitzOnWith.of_dist_le_mul fun a _ b _ => le_of_eq ?_
    rw [segCurve_apply, segCurve_apply, Complex.dist_eq, ← sub_mul, ← Complex.ofReal_sub,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.dist_eq, coe_nnnorm, mul_comm]
  · rintro _ ⟨t, ht, rfl⟩
    refine mem_ball_zero_iff.mpr ?_
    rw [segCurve_norm ht.1, Complex.norm_real, Real.norm_of_nonneg hs₀]
    nlinarith [ht.2]

/-- (14.3): the Poincaré distance in `Δ`,
`d(z₁, z₂) = ln((1 + |(z₂-z₁)/(1-z̄₁z₂)|)/(1 - |(z₂-z₁)/(1-z̄₁z₂)|))`. -/
theorem eq14_3 {z₁ z₂ : ℂ} (h₁ : z₁ ∈ unitDisc) (h₂ : z₂ ∈ unitDisc) :
    metricDist unitDisc (fun z => ENNReal.ofReal (poincareDensityDisc z)) z₁ z₂ =
      ENNReal.ofReal (Real.log ((1 + ‖(z₂ - z₁) / (1 - conj z₁ * z₂)‖) /
        (1 - ‖(z₂ - z₁) / (1 - conj z₁ * z₂)‖))) := by
  have ha : ‖z₁‖ < 1 := mem_ball_zero_iff.mp h₁
  have hz2 : ‖z₂‖ < 1 := mem_ball_zero_iff.mp h₂
  have hB : (z₂ - z₁) / (1 - conj z₁ * z₂) = blaschke z₁ z₂ := rfl
  rw [hB]
  have hρ0 : 0 ≤ ‖blaschke z₁ z₂‖ := norm_nonneg _
  have hρ1 : ‖blaschke z₁ z₂‖ < 1 := blaschke_mem_unitDisc ha hz2
  obtain ⟨c, hc, hcB⟩ := exists_rot_mul_eq_norm (blaschke z₁ z₂)
  have hcc : conj c * c = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  have hfconf : IsConformalOnto (fun z => c * blaschke z₁ z) unitDisc unitDisc :=
    (isConformalOnto_rot hc).comp (isConformalOnto_blaschke ha)
  apply le_antisymm
  · -- upper bound: the radius `[0, ρ]` pulled back by `(c M_{z₁})⁻¹`
    have hc' : ‖conj c‖ = 1 := by rw [Complex.norm_conj, hc]
    have ha' : ‖-(c * z₁)‖ < 1 := by
      rw [norm_neg, norm_mul, hc, one_mul]
      exact ha
    have hgd : DifferentiableOn ℂ (fun w => conj c * blaschke (-(c * z₁)) w) unitDisc :=
      (differentiableOn_blaschke ha').const_mul _
    have hgmaps : MapsTo (fun w => conj c * blaschke (-(c * z₁)) w) unitDisc unitDisc := by
      intro w hw
      refine mem_ball_zero_iff.mpr ?_
      rw [norm_mul, hc', one_mul]
      exact blaschke_mem_unitDisc ha' (mem_ball_zero_iff.mp hw)
    have hseg := isPathIn_segCurve hρ0 hρ1
    obtain ⟨γ₀, hγ₀, hγ₀path⟩ := exists_isPathIn_comp isOpen_ball hgd hgmaps hseg
    have hg0 : conj c * blaschke (-(c * z₁)) 0 = z₁ := by
      simp only [blaschke, map_neg, map_mul, zero_sub, neg_neg, mul_zero, sub_zero, div_one]
      rw [← mul_assoc, hcc, one_mul]
    have hg1 : conj c * blaschke (-(c * z₁)) (‖blaschke z₁ z₂‖ : ℂ) = z₂ := by
      rw [← hcB, ← blaschke_neg_conj_mul hc, ← mul_assoc, hcc, one_mul,
        blaschke_neg_blaschke ha hz2]
    rw [hg0, hg1] at hγ₀path
    have hlen : γ₀.rhoLength (fun z => ENNReal.ofReal (poincareDensityDisc z))
        = ENNReal.ofReal (Real.log ((1 + ‖blaschke z₁ z₂‖) / (1 - ‖blaschke z₁ z₂‖))) := by
      rw [rhoLength_comp_rotBlaschke hc' ha' (γ := segCurve (‖blaschke z₁ z₂‖ : ℂ)) ?_ ?_]
      · exact rhoLength_segCurve_of_nonneg hρ0 hρ1
          (by rw [Complex.norm_real, Real.norm_of_nonneg hρ0])
      · rintro _ ⟨t, ht, rfl⟩
        exact hseg.2.2.2 ⟨t, Ioo_subset_Icc_self ht, rfl⟩
      · intro t _
        rw [hγ₀]
    calc metricDist unitDisc (fun z => ENNReal.ofReal (poincareDensityDisc z)) z₁ z₂
        ≤ γ₀.rhoLength (fun z => ENNReal.ofReal (poincareDensityDisc z)) :=
          iInf₂_le γ₀ hγ₀path
      _ = _ := hlen
  · -- lower bound: every competitor maps to a path from `0` to `ρ` of the same length
    refine le_iInf₂ fun γ hγ => ?_
    obtain ⟨γ', hγ'eq, hγ'path⟩ := exists_isPathIn_comp isOpen_ball hfconf.1 hfconf.mapsTo hγ
    rw [blaschke_self, mul_zero, hcB] at hγ'path
    have hlen : γ'.rhoLength (fun z => ENNReal.ofReal (poincareDensityDisc z))
        = γ.rhoLength (fun z => ENNReal.ofReal (poincareDensityDisc z)) := by
      refine rhoLength_comp_rotBlaschke hc ha ?_ ?_
      · rintro _ ⟨t, ht, rfl⟩
        exact hγ.2.2.2 ⟨t, Ioo_subset_Icc_self ht, rfl⟩
      · intro t _
        rw [hγ'eq]
    rw [← hlen]
    rcases eq_or_lt_of_le hρ0 with h0 | hpos
    · rw [← h0]
      simp
    · exact poincare_segment_shortest hpos hρ1 hγ'path

/-- The Poincaré density `η_D(z) = 2|f'(z)|/(1 - |f(z)|²)` of a simply connected domain `D`
with more than one boundary point, `f : D → Δ` conformal (§14.1). -/
def poincareDensity (D : Set ℂ) (z : ℂ) : ℝ :=
  sSup {r : ℝ | ∃ f : ℂ → ℂ, IsConformalOnto f D unitDisc ∧ r = 2 * ‖deriv f z‖ / (1 - ‖f z‖ ^ 2)}

/-- §14.1: the Poincaré density of `D` does not depend on the choice of the conformal map
`f : D → Δ`.

The hypothesis `IsOpen D` is added to the book's statement: the book's `D` is a *domain*, and
without openness the unrestricted `deriv f z` bears no relation to `f` on `D` and
`IsConformalOnto.symm` is unavailable. -/
theorem poincareDensity_well_defined {D : Set ℂ} (hD : IsOpen D) {f g : ℂ → ℂ}
    (hf : IsConformalOnto f D unitDisc) (hg : IsConformalOnto g D unitDisc) {z : ℂ} (hz : z ∈ D) :
    2 * ‖deriv f z‖ / (1 - ‖f z‖ ^ 2) = 2 * ‖deriv g z‖ / (1 - ‖g z‖ ^ 2) ∧
      poincareDensity D z = 2 * ‖deriv f z‖ / (1 - ‖f z‖ ^ 2) := by
  -- every competing conformal map gives the same value as `f`
  have key : ∀ k : ℂ → ℂ, IsConformalOnto k D unitDisc →
      2 * ‖deriv k z‖ / (1 - ‖k z‖ ^ 2) = 2 * ‖deriv f z‖ / (1 - ‖f z‖ ^ 2) := by
    intro k hk
    have hfs : IsConformalOnto (Function.invFunOn f D) unitDisc D := hf.symm hD
    obtain ⟨c, a, hc, ha, heq⟩ :=
      exists_rotation_blaschke_of_isConformalOnto_unitDisc (hk.comp hfs)
    have hpt : ∀ w ∈ D, k w = c * blaschke a (f w) := by
      intro w hw
      have h1 : (k ∘ Function.invFunOn f D) (f w) = c * blaschke a (f w) := heq (hf.mapsTo hw)
      rwa [Function.comp_apply, hf.2.1.leftInvOn_invFunOn hw] at h1
    have hfz : ‖f z‖ < 1 := mem_ball_zero_iff.mp (hf.mapsTo hz)
    have hfd : HasDerivAt f (deriv f z) z :=
      (hf.1.analyticAt (hD.mem_nhds hz)).differentiableAt.hasDerivAt
    have hbd : HasDerivAt (fun v : ℂ => c * blaschke a v)
        (c * ((1 - a * conj a) / (1 - conj a * f z) ^ 2)) (f z) :=
      (hasDerivAt_blaschke ha hfz).const_mul _
    have hgerm : k =ᶠ[𝓝 z] fun w => c * blaschke a (f w) := by
      filter_upwards [hD.mem_nhds hz] with w hw
      exact hpt w hw
    have hkd : HasDerivAt k
        (c * ((1 - a * conj a) / (1 - conj a * f z) ^ 2) * deriv f z) z :=
      (hbd.comp z hfd).congr_of_eventuallyEq hgerm
    have hdk : deriv k z = deriv (fun w : ℂ => c * blaschke a w) (f z) * deriv f z := by
      rw [hkd.deriv, hbd.deriv]
    have hrot := poincareDensityDisc_rotBlaschke hc ha hfz
    rw [poincareDensityDisc, poincareDensityDisc] at hrot
    rw [hpt z hz, hdk, norm_mul]
    have e1 : 2 * (‖deriv (fun w : ℂ => c * blaschke a w) (f z)‖ * ‖deriv f z‖)
        / (1 - ‖c * blaschke a (f z)‖ ^ 2)
        = 2 / (1 - ‖c * blaschke a (f z)‖ ^ 2)
            * ‖deriv (fun w : ℂ => c * blaschke a w) (f z)‖ * ‖deriv f z‖ := by
      ring
    rw [e1, hrot]
    ring
  refine ⟨(key g hg).symm, ?_⟩
  have hset : {r : ℝ | ∃ k : ℂ → ℂ, IsConformalOnto k D unitDisc ∧
      r = 2 * ‖deriv k z‖ / (1 - ‖k z‖ ^ 2)} = {2 * ‖deriv f z‖ / (1 - ‖f z‖ ^ 2)} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact key k hk
    · rintro rfl
      exact ⟨f, hf, rfl⟩
  rw [poincareDensity, hset, csSup_singleton]

/-- The Poincaré density of the unit disc is `2/(1 - |z|²)`. -/
theorem poincareDensity_unitDisc {z : ℂ} (hz : z ∈ unitDisc) :
    poincareDensity unitDisc z = poincareDensityDisc z := by
  have hid : IsConformalOnto id unitDisc unitDisc := isConformalOnto_id unitDisc
  rw [(poincareDensity_well_defined (D := unitDisc) isOpen_ball hid hid hz).2,
    poincareDensityDisc]
  simp

/-- §14.1: the Poincaré metric of the upper half-plane is `|dz|/y`. -/
theorem poincareDensity_upperHalf {z : ℂ} (hz : z ∈ upperHalf) :
    poincareDensity upperHalf z = 1 / z.im := by
  have hz' : 0 < z.im := hz
  have hden := cayley_den_ne_zero hz'
  have hpos : 0 < normSq (z + I) := normSq_pos.mpr hden
  -- `C'(z) = 2i/(z + i)²`
  have hd : HasDerivAt cayley (2 * I / (z + I) ^ 2) z := by
    have h0 : HasDerivAt (fun w : ℂ => w) 1 z := hasDerivAt_id z
    have h1 : HasDerivAt (fun w : ℂ => w - I) 1 z := by simpa using h0.sub_const I
    have h2 : HasDerivAt (fun w : ℂ => w + I) 1 z := by simpa using h0.add_const I
    have hfun : cayley = fun w : ℂ => (w - I) / (w + I) := rfl
    rw [hfun]
    convert h1.div h2 hden using 1
    field_simp
    ring
  have hdn : ‖deriv cayley z‖ = 2 / normSq (z + I) := by
    rw [hd.deriv, norm_div, norm_mul, norm_pow, Complex.sq_norm]
    simp
  have hval : 1 - ‖cayley z‖ ^ 2 = 4 * z.im / normSq (z + I) := by
    rw [Complex.sq_norm, cayley, normSq_div, eq_div_iff (ne_of_gt hpos), sub_mul, one_mul,
      div_mul_cancel₀ _ (ne_of_gt hpos)]
    linarith [normSq_cayley_key z]
  rw [(poincareDensity_well_defined isOpen_upperHalf isConformalOnto_cayley
    isConformalOnto_cayley hz).2, hdn, hval]
  have hne : z.im ≠ 0 := ne_of_gt hz'
  field_simp
  norm_num

/-- The Poincaré distance of a simply connected domain. -/
def poincareDist (D : Set ℂ) (z₁ z₂ : ℂ) : ℝ≥0∞ :=
  metricDist D (fun z => ENNReal.ofReal (poincareDensity D z)) z₁ z₂

/-! ### Transfer of the metric distance by a conformal map -/

/-- Two curves agreeing on `(0, 1)` have the same `ρ`-length. -/
theorem LRCurve.rhoLength_congr_toFun {γ₁ γ₂ : LRCurve} (h : EqOn γ₁.toFun γ₂.toFun (Ioo 0 1))
    (ρ : ℂ → ℝ≥0∞) : γ₁.rhoLength ρ = γ₂.rhoLength ρ := by
  unfold LRCurve.rhoLength
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have hev : γ₁.toFun =ᶠ[𝓝 t] γ₂.toFun := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact h hs
  rw [h ht, hev.deriv_eq]

/-- The `ρ'`-length of `f ∘ γ` is the `ρ`-length of `γ` when `ρ = (ρ' ∘ f) |f'|` on `D`. -/
theorem LRCurve.rhoLength_comp_of_isConformalOnto {D D' : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : IsConformalOnto f D D') {ρ ρ' : ℂ → ℝ≥0∞}
    (hρ : ∀ z ∈ D, ρ z = ρ' (f z) * ‖deriv f z‖ₑ) {γ γ' : LRCurve} (hγ : γ.trace ⊆ D)
    (heq : γ'.toFun = f ∘ γ.toFun) : γ'.rhoLength ρ' = γ.rhoLength ρ := by
  rw [LRCurve.rhoLength_image_conformal hD hf hγ (fun t _ => by rw [heq]) ρ']
  refine LRCurve.rhoLength_congr fun z hz => ?_
  rw [indicator_of_mem (hγ hz), hρ z (hγ hz)]

/-- **Conformal invariance of the metric distance.**  If `f : D → D'` is conformal with holomorphic
inverse `g`, and `ρ = (ρ' ∘ f) |f'|` on `D`, then `f` is an isometry from `(D, ρ)` to `(D', ρ')`. -/
theorem metricDist_eq_of_isConformalOnto {D D' : Set ℂ} (hD : IsOpen D) (hD' : IsOpen D')
    {f g : ℂ → ℂ} (hf : IsConformalOnto f D D') (hg : DifferentiableOn ℂ g D')
    (hgmaps : MapsTo g D' D) (hfg : ∀ w ∈ D', f (g w) = w) (hgf : ∀ z ∈ D, g (f z) = z)
    {ρ ρ' : ℂ → ℝ≥0∞} (hρ : ∀ z ∈ D, ρ z = ρ' (f z) * ‖deriv f z‖ₑ) {a b : ℂ} (ha : a ∈ D)
    (hb : b ∈ D) : metricDist D ρ a b = metricDist D' ρ' (f a) (f b) := by
  have hfwd : ∀ {γ γ' : LRCurve}, γ.trace ⊆ D → γ'.toFun = f ∘ γ.toFun →
      γ'.rhoLength ρ' = γ.rhoLength ρ := fun hγ heq =>
    LRCurve.rhoLength_comp_of_isConformalOnto hD hf hρ hγ heq
  apply le_antisymm
  · refine le_iInf₂ fun β hβ => ?_
    obtain ⟨γ, hγeq, hγpath⟩ := exists_isPathIn_comp hD' hg hgmaps hβ
    rw [hgf a ha, hgf b hb] at hγpath
    obtain ⟨γ', hγ'eq, -⟩ := exists_isPathIn_comp hD hf.1 hf.mapsTo hγpath
    have htr : γ.trace ⊆ D := by
      rintro _ ⟨t, ht, rfl⟩
      exact hγpath.2.2.2 ⟨t, Ioo_subset_Icc_self ht, rfl⟩
    calc metricDist D ρ a b ≤ γ.rhoLength ρ := iInf₂_le γ hγpath
      _ = γ'.rhoLength ρ' := (hfwd htr hγ'eq).symm
      _ = β.rhoLength ρ' := LRCurve.rhoLength_congr_toFun (fun t ht => by
          rw [hγ'eq, Function.comp_apply, hγeq, Function.comp_apply]
          exact hfg _ (hβ.2.2.2 ⟨t, Ioo_subset_Icc_self ht, rfl⟩)) ρ'
  · refine le_iInf₂ fun γ hγ => ?_
    obtain ⟨γ', hγ'eq, hγ'path⟩ := exists_isPathIn_comp hD hf.1 hf.mapsTo hγ
    have htr : γ.trace ⊆ D := by
      rintro _ ⟨t, ht, rfl⟩
      exact hγ.2.2.2 ⟨t, Ioo_subset_Icc_self ht, rfl⟩
    calc metricDist D' ρ' (f a) (f b) ≤ γ'.rhoLength ρ' := iInf₂_le γ' hγ'path
      _ = γ.rhoLength ρ := hfwd htr hγ'eq

/-! ### The Poincaré distance of the upper half-plane -/

/-- The pseudo-hyperbolic distance of `Δ` read through the Cayley transform:
`|(C w - C z)/(1 - conj (C z) C w)| = |w - z| / |w - z̄|`. -/
theorem norm_cayley_blaschke {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) :
    ‖(cayley b - cayley a) / (1 - conj (cayley a) * cayley b)‖ = ‖b - a‖ / ‖b - conj a‖ := by
  have hA := cayley_den_ne_zero ha
  have hB := cayley_den_ne_zero hb
  have hconjA : conj (a + I) = conj a - I := by simp [sub_eq_add_neg]
  have hAc : conj a - I ≠ 0 := by
    rw [← hconjA]
    exact (map_ne_zero _).2 hA
  have hab : conj a - b ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at him
    linarith
  have hI : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  have hN : cayley b - cayley a = 2 * I * (b - a) / ((a + I) * (b + I)) := by
    unfold cayley
    field_simp
    ring
  have hcj : conj (cayley a) = (conj a + I) / (conj a - I) := by
    simp only [cayley, map_div₀, map_sub, map_add, Complex.conj_I]
    ring
  have hDn : 1 - conj (cayley a) * cayley b = 2 * I * (conj a - b) / ((conj a - I) * (b + I)) := by
    rw [hcj]
    unfold cayley
    field_simp
    ring
  have heq : (cayley b - cayley a) / (1 - conj (cayley a) * cayley b)
      = (b - a) / (conj a - b) * ((conj a - I) / (a + I)) := by
    rw [hN, hDn]
    field_simp
  rw [heq, norm_mul, norm_div, norm_div, ← hconjA, Complex.norm_conj, norm_sub_rev (conj a) b]
  have hA' : ‖a + I‖ ≠ 0 := norm_ne_zero_iff.2 hA
  field_simp

/-- `ln((1 + p/q)/(1 - p/q)) = 2 arsinh(p/(2√y))` when `q² = p² + 4y`. -/
theorem log_ratio_eq_two_arsinh {p q y : ℝ} (hp : 0 ≤ p) (hy : 0 < y) (hq0 : 0 < q)
    (hq : q ^ 2 = p ^ 2 + 4 * y) :
    Real.log ((1 + p / q) / (1 - p / q)) = 2 * Real.arsinh (p / (2 * √y)) := by
  have hsy : 0 < √y := Real.sqrt_pos.2 hy
  have hsy2 : √y ^ 2 = y := Real.sq_sqrt hy.le
  have hqp : p < q := by nlinarith
  have hs : √(1 + (p / (2 * √y)) ^ 2) = q / (2 * √y) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    field_simp
    nlinarith [hsy2, hq]
  have harsinh : Real.arsinh (p / (2 * √y)) = Real.log (p / (2 * √y) + q / (2 * √y)) := by
    show Real.log (p / (2 * √y) + √(1 + (p / (2 * √y)) ^ 2)) = _
    rw [hs]
  have htwo : (2 : ℝ) * Real.log (p / (2 * √y) + q / (2 * √y))
      = Real.log ((p / (2 * √y) + q / (2 * √y)) ^ 2) := by
    rw [Real.log_pow]
    norm_num
  rw [harsinh, htwo]
  congr 1
  have hqp' : q - p ≠ 0 := by linarith
  have hq' : q ≠ 0 := hq0.ne'
  have key : (1 + p / q) / (1 - p / q) = (q + p) / (q - p) := by
    field_simp
  have key2 : ((p + q) / (2 * √y)) ^ 2 = (q + p) / (q - p) := by
    rw [div_pow, mul_pow, hsy2, div_eq_div_iff (by positivity) hqp']
    linear_combination (q + p) * hq
  rw [key, ← add_div, key2]

/-- The Poincaré distance of the upper half-plane coincides with Mathlib's hyperbolic distance
on `ℍ`. -/
theorem poincareDist_upperHalf (z w : UpperHalfPlane) :
    poincareDist upperHalf z w = ENNReal.ofReal (dist z w) := by
  have hzi : 0 < (z : ℂ).im := z.im_pos
  have hwi : 0 < (w : ℂ).im := w.im_pos
  have hz : (z : ℂ) ∈ upperHalf := hzi
  have hw : (w : ℂ) ∈ upperHalf := hwi
  have hden : ∀ u ∈ upperHalf, ENNReal.ofReal (poincareDensity upperHalf u)
      = ENNReal.ofReal (poincareDensityDisc (cayley u)) * ‖deriv cayley u‖ₑ := by
    intro u hu
    have h := (poincareDensity_well_defined isOpen_upperHalf isConformalOnto_cayley
      isConformalOnto_cayley hu).2
    have hcu : ‖cayley u‖ < 1 := mem_ball_zero_iff.mp (cayley_mem_unitDisc hu)
    have hpos : 0 ≤ poincareDensityDisc (cayley u) :=
      le_of_lt (div_pos two_pos (by nlinarith [norm_nonneg (cayley u)]))
    rw [h, ← ofReal_norm, ← ENNReal.ofReal_mul hpos, poincareDensityDisc]
    congr 1
    ring
  have hginv : DifferentiableOn ℂ cayleyInv unitDisc := fun u hu =>
    ((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => I * (1 + v)) u).div
      (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 - v) u)
      (cayleyInv_den_ne_zero (mem_ball_zero_iff.mp hu))).differentiableWithinAt
  unfold poincareDist
  rw [metricDist_eq_of_isConformalOnto (a := (z : ℂ)) (b := (w : ℂ)) (D' := unitDisc)
    (ρ' := fun v => ENNReal.ofReal (poincareDensityDisc v))
    isOpen_upperHalf isOpen_ball isConformalOnto_cayley hginv
    (fun u hu => cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp hu))
    (fun u hu => cayley_cayleyInv (mem_ball_zero_iff.mp hu)) (fun u hu => cayleyInv_cayley hu)
    hden hz hw, eq14_3 (cayley_mem_unitDisc hzi) (cayley_mem_unitDisc hwi),
    norm_cayley_blaschke hzi hwi, UpperHalfPlane.dist_eq, Complex.dist_eq, norm_sub_rev (z : ℂ)]
  congr 1
  have hzw : 0 < ‖(w : ℂ) - conj (z : ℂ)‖ := by
    refine norm_pos_iff.2 fun h => ?_
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at him
    have := z.im_pos
    have := w.im_pos
    simp only [UpperHalfPlane.coe_im] at him
    linarith
  refine log_ratio_eq_two_arsinh (norm_nonneg _) (mul_pos z.im_pos w.im_pos) hzw ?_
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-! ### Vertical geodesics of the upper half-plane -/

theorem hasDerivAt_vertCurve (x L₁ L₂ t : ℝ) :
    HasDerivAt (fun t : ℝ => (x : ℂ) + (Real.exp ((1 - t) * L₁ + t * L₂) : ℂ) * I)
      ((Real.exp ((1 - t) * L₁ + t * L₂) * (L₂ - L₁) : ℝ) * I) t := by
  have h1 : HasDerivAt (fun t : ℝ => (1 - t) * L₁ + t * L₂) (L₂ - L₁) t := by
    have := (((hasDerivAt_id t).const_sub 1).mul_const L₁).add ((hasDerivAt_id t).mul_const L₂)
    convert this using 1
    · funext y
      simp only [Pi.add_apply, id]
    · ring
  exact (h1.exp.ofReal_comp.mul_const I).const_add (x : ℂ)

theorem contDiff_vertCurve (x L₁ L₂ : ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => (x : ℂ) + (Real.exp ((1 - t) * L₁ + t * L₂) : ℂ) * I) := by
  have h : ContDiff ℝ 1 (fun t : ℝ => Real.exp ((1 - t) * L₁ + t * L₂)) := by fun_prop
  exact contDiff_const.add ((Complex.ofRealCLM.contDiff.comp h).mul contDiff_const)

/-- The vertical segment `t ↦ x + s₁^{1-t} s₂^t i`, of constant hyperbolic speed (proof machinery
for `upperHalf_geodesic`). -/
def vertCurve (x s₁ s₂ : ℝ) : LRCurve where
  toFun := fun t => (x : ℂ) + (Real.exp ((1 - t) * Real.log s₁ + t * Real.log s₂) : ℂ) * I
  locallyLipschitzOn :=
    (contDiff_vertCurve x (Real.log s₁) (Real.log s₂)).locallyLipschitz.locallyLipschitzOn

theorem vertCurve_re (x s₁ s₂ t : ℝ) : ((vertCurve x s₁ s₂).toFun t).re = x := by
  show ((x : ℂ) + (Real.exp ((1 - t) * Real.log s₁ + t * Real.log s₂) : ℂ) * I).re = x
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

theorem vertCurve_im (x s₁ s₂ t : ℝ) :
    ((vertCurve x s₁ s₂).toFun t).im = Real.exp ((1 - t) * Real.log s₁ + t * Real.log s₂) := by
  show ((x : ℂ) + (Real.exp ((1 - t) * Real.log s₁ + t * Real.log s₂) : ℂ) * I).im = _
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, zero_add, add_zero]

theorem vertCurve_isPathIn {x s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) :
    IsPathIn upperHalf ((x : ℂ) + (s₁ : ℂ) * I) ((x : ℂ) + (s₂ : ℂ) * I) (vertCurve x s₁ s₂) := by
  refine ⟨LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc
    (contDiff_vertCurve x (Real.log s₁) (Real.log s₂)).locallyLipschitz.locallyLipschitzOn,
    ?_, ?_, ?_⟩
  · show (x : ℂ) + (Real.exp ((1 - (0 : ℝ)) * Real.log s₁ + (0 : ℝ) * Real.log s₂) : ℂ) * I = _
    rw [sub_zero, one_mul, zero_mul, add_zero, Real.exp_log hs₁]
  · show (x : ℂ) + (Real.exp ((1 - (1 : ℝ)) * Real.log s₁ + (1 : ℝ) * Real.log s₂) : ℂ) * I = _
    rw [sub_self, zero_mul, one_mul, zero_add, Real.exp_log hs₂]
  · rintro _ ⟨t, -, rfl⟩
    show 0 < ((vertCurve x s₁ s₂).toFun t).im
    rw [vertCurve_im]
    exact Real.exp_pos _

theorem vertCurve_rhoLength {x s₁ s₂ : ℝ} (_hs₁ : 0 < s₁) (_hs₂ : 0 < s₂) :
    (vertCurve x s₁ s₂).rhoLength (fun z => ENNReal.ofReal (poincareDensity upperHalf z))
      = ENNReal.ofReal |Real.log s₂ - Real.log s₁| := by
  unfold LRCurve.rhoLength
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1,
      ENNReal.ofReal (poincareDensity upperHalf ((vertCurve x s₁ s₂).toFun t))
        * ‖deriv (vertCurve x s₁ s₂).toFun t‖ₑ = ENNReal.ofReal |Real.log s₂ - Real.log s₁| := by
    intro t _
    have hep : 0 < Real.exp ((1 - t) * Real.log s₁ + t * Real.log s₂) := Real.exp_pos _
    have him : ((vertCurve x s₁ s₂).toFun t).im
        = Real.exp ((1 - t) * Real.log s₁ + t * Real.log s₂) := vertCurve_im x s₁ s₂ t
    have hmem : (vertCurve x s₁ s₂).toFun t ∈ upperHalf := by
      show 0 < ((vertCurve x s₁ s₂).toFun t).im
      rw [him]
      exact hep
    have hd : deriv (vertCurve x s₁ s₂).toFun t
        = ((Real.exp ((1 - t) * Real.log s₁ + t * Real.log s₂) * (Real.log s₂ - Real.log s₁) : ℝ)
          : ℂ) * I :=
      (hasDerivAt_vertCurve x (Real.log s₁) (Real.log s₂) t).deriv
    rw [poincareDensity_upperHalf hmem, him, hd, ← ofReal_norm,
      ← ENNReal.ofReal_mul (le_of_lt (one_div_pos.2 hep))]
    congr 1
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos hep]
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioo hpt, setLIntegral_const, Real.volume_Ioo, sub_zero,
    ENNReal.ofReal_one, mul_one]

/-- `|ln s₂ - ln s₁| = 2 arsinh(|s₂ - s₁|/(2√(s₁ s₂)))`. -/
theorem abs_log_sub_eq_two_arsinh {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) :
    |Real.log s₂ - Real.log s₁| = 2 * Real.arsinh (|s₂ - s₁| / (2 * √(s₁ * s₂))) := by
  have hq : s₁ + s₂ ≠ 0 := (add_pos hs₁ hs₂).ne'
  rw [← log_ratio_eq_two_arsinh (abs_nonneg _) (mul_pos hs₁ hs₂) (add_pos hs₁ hs₂)
    (by rw [sq_abs]; ring)]
  rcases le_total s₁ s₂ with h | h
  · have e1 : 1 + |s₂ - s₁| / (s₁ + s₂) = 2 * s₂ / (s₁ + s₂) := by
      rw [abs_of_nonneg (sub_nonneg.2 h), eq_div_iff hq, add_mul, div_mul_cancel₀ _ hq]
      ring
    have e2 : 1 - |s₂ - s₁| / (s₁ + s₂) = 2 * s₁ / (s₁ + s₂) := by
      rw [abs_of_nonneg (sub_nonneg.2 h), eq_div_iff hq, sub_mul, div_mul_cancel₀ _ hq]
      ring
    rw [abs_of_nonneg (sub_nonneg.2 (Real.log_le_log hs₁ h)), ← Real.log_div hs₂.ne' hs₁.ne', e1, e2]
    congr 1
    field_simp
  · have e1 : 1 + |s₂ - s₁| / (s₁ + s₂) = 2 * s₁ / (s₁ + s₂) := by
      rw [abs_of_nonpos (sub_nonpos.2 h), eq_div_iff hq, add_mul, div_mul_cancel₀ _ hq]
      ring
    have e2 : 1 - |s₂ - s₁| / (s₁ + s₂) = 2 * s₂ / (s₁ + s₂) := by
      rw [abs_of_nonpos (sub_nonpos.2 h), eq_div_iff hq, sub_mul, div_mul_cancel₀ _ hq]
      ring
    rw [abs_of_nonpos (sub_nonpos.2 (Real.log_le_log hs₂ h)), neg_sub,
      ← Real.log_div hs₁.ne' hs₂.ne', e1, e2]
    congr 1
    field_simp

/-- The Poincaré length of the vertical curve is the Poincaré distance of its endpoints. -/
theorem vertCurve_rhoLength_eq_poincareDist {x s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) :
    (vertCurve x s₁ s₂).rhoLength (fun z => ENNReal.ofReal (poincareDensity upperHalf z))
      = poincareDist upperHalf ((x : ℂ) + (s₁ : ℂ) * I) ((x : ℂ) + (s₂ : ℂ) * I) := by
  have hm₁ : 0 < ((x : ℂ) + (s₁ : ℂ) * I).im := by simpa using hs₁
  have hm₂ : 0 < ((x : ℂ) + (s₂ : ℂ) * I).im := by simpa using hs₂
  rw [vertCurve_rhoLength hs₁ hs₂]
  have hpd : poincareDist upperHalf ((x : ℂ) + (s₁ : ℂ) * I) ((x : ℂ) + (s₂ : ℂ) * I)
      = ENNReal.ofReal (dist (⟨_, hm₁⟩ : UpperHalfPlane) ⟨_, hm₂⟩) :=
    poincareDist_upperHalf ⟨_, hm₁⟩ ⟨_, hm₂⟩
  rw [hpd]
  congr 1
  have hd : dist ((⟨_, hm₁⟩ : UpperHalfPlane) : ℂ) ((⟨_, hm₂⟩ : UpperHalfPlane) : ℂ) = |s₂ - s₁| := by
    show dist ((x : ℂ) + (s₁ : ℂ) * I) ((x : ℂ) + (s₂ : ℂ) * I) = _
    rw [Complex.dist_eq, show (x : ℂ) + (s₁ : ℂ) * I - ((x : ℂ) + (s₂ : ℂ) * I)
      = ((s₁ - s₂ : ℝ) : ℂ) * I by push_cast; ring, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  have hi₁ : (⟨_, hm₁⟩ : UpperHalfPlane).im = s₁ := by
    show ((x : ℂ) + (s₁ : ℂ) * I).im = s₁
    simp
  have hi₂ : (⟨_, hm₂⟩ : UpperHalfPlane).im = s₂ := by
    show ((x : ℂ) + (s₂ : ℂ) * I).im = s₂
    simp
  rw [UpperHalfPlane.dist_eq, hd, hi₁, hi₂]
  exact abs_log_sub_eq_two_arsinh hs₁ hs₂

theorem exists_vertical_geodesic {z₁ z₂ : ℂ} (h₁ : z₁ ∈ upperHalf) (h₂ : z₂ ∈ upperHalf)
    (hre : z₁.re = z₂.re) :
    ∃ γ : LRCurve, IsPathIn upperHalf z₁ z₂ γ ∧
      γ.rhoLength (fun z => ENNReal.ofReal (poincareDensity upperHalf z)) =
        poincareDist upperHalf z₁ z₂ ∧
      ∀ t ∈ Icc (0 : ℝ) 1, (γ.toFun t).re = z₁.re := by
  have hs₁ : 0 < z₁.im := h₁
  have hs₂ : 0 < z₂.im := h₂
  have e₁ : (z₁.re : ℂ) + (z₁.im : ℂ) * I = z₁ := Complex.re_add_im z₁
  have e₂ : (z₁.re : ℂ) + (z₂.im : ℂ) * I = z₂ := by rw [hre]; exact Complex.re_add_im z₂
  refine ⟨vertCurve z₁.re z₁.im z₂.im, ?_, ?_, fun t _ => vertCurve_re _ _ _ t⟩
  · have h := vertCurve_isPathIn (x := z₁.re) hs₁ hs₂
    rwa [e₁, e₂] at h
  · have h := vertCurve_rhoLength_eq_poincareDist (x := z₁.re) hs₁ hs₂
    rwa [e₁, e₂] at h

/-! ### Real fractional linear maps of the upper half-plane -/

/-- The real fractional linear map `w ↦ (a w + b)/(c w + d)` (proof machinery for
`upperHalf_geodesic`). -/
def realMobius (a b c d : ℝ) (w : ℂ) : ℂ := ((a : ℂ) * w + b) / ((c : ℂ) * w + d)

theorem realMobius_den_ne_zero {a b c d : ℝ} (h : 0 < a * d - b * c) {w : ℂ} (hw : 0 < w.im) :
    (c : ℂ) * w + d ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, Complex.zero_im, Complex.add_re, Complex.mul_re, sub_zero, Complex.zero_re] at him hre
  have hc : c = 0 := by
    rcases mul_eq_zero.1 him with hc | hc
    · exact hc
    · exact absurd hc hw.ne'
  rw [hc, zero_mul, zero_add] at hre
  rw [hc, hre] at h
  simp at h

theorem im_realMobius {a b c d : ℝ} {w : ℂ} :
    (realMobius a b c d w).im = (a * d - b * c) * w.im / normSq ((c : ℂ) * w + d) := by
  unfold realMobius
  rw [Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, sub_zero]
  rw [div_sub_div_same]
  congr 1
  ring

theorem hasDerivAt_realMobius {a b c d : ℝ} {w : ℂ} (hden : (c : ℂ) * w + d ≠ 0) :
    HasDerivAt (realMobius a b c d) (((a * d - b * c : ℝ) : ℂ) / ((c : ℂ) * w + d) ^ 2) w := by
  have hn : HasDerivAt (fun v : ℂ => (a : ℂ) * v + b) a w := by
    simpa using ((hasDerivAt_id w).const_mul (a : ℂ)).add_const (b : ℂ)
  have hd : HasDerivAt (fun v : ℂ => (c : ℂ) * v + d) c w := by
    simpa using ((hasDerivAt_id w).const_mul (c : ℂ)).add_const (d : ℂ)
  have h := hn.div hd hden
  convert h using 1
  · rfl
  · push_cast
    ring

theorem realMobius_mem_upperHalf {a b c d : ℝ} (h : 0 < a * d - b * c) {w : ℂ} (hw : 0 < w.im) :
    realMobius a b c d w ∈ upperHalf := by
  show 0 < (realMobius a b c d w).im
  rw [im_realMobius]
  exact div_pos (mul_pos h hw) (normSq_pos.2 (realMobius_den_ne_zero h hw))

theorem differentiableOn_realMobius {a b c d : ℝ} (h : 0 < a * d - b * c) :
    DifferentiableOn ℂ (realMobius a b c d) upperHalf := fun _ hw =>
  (hasDerivAt_realMobius (realMobius_den_ne_zero h hw)).differentiableAt.differentiableWithinAt

/-- Real fractional linear maps with positive determinant preserve the Poincaré density of `ℍ`. -/
theorem poincareDensity_upperHalf_realMobius {a b c d : ℝ} (h : 0 < a * d - b * c) {w : ℂ}
    (hw : 0 < w.im) :
    ENNReal.ofReal (poincareDensity upperHalf w) =
      ENNReal.ofReal (poincareDensity upperHalf (realMobius a b c d w)) *
        ‖deriv (realMobius a b c d) w‖ₑ := by
  have hden := realMobius_den_ne_zero h hw
  have hns : 0 < normSq ((c : ℂ) * w + d) := normSq_pos.2 hden
  have hmem := realMobius_mem_upperHalf h hw
  have himM : 0 < (realMobius a b c d w).im := hmem
  rw [poincareDensity_upperHalf hw, poincareDensity_upperHalf hmem,
    (hasDerivAt_realMobius hden).deriv, ← ofReal_norm,
    ← ENNReal.ofReal_mul (le_of_lt (one_div_pos.2 himM)), im_realMobius]
  congr 1
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg h.le, Complex.sq_norm]
  have hw' : w.im ≠ 0 := hw.ne'
  field_simp

theorem realMobius_realMobius_inv {p q : ℝ} (hpq : p < q) {w : ℂ} (hw : 0 < w.im) :
    realMobius q p 1 1 (realMobius 1 (-p) (-1) q w) = w := by
  have hu : (q : ℂ) - w ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hqp : (q : ℂ) - p ≠ 0 := by
    rw [← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.2 (sub_pos.2 hpq).ne'
  have e1 : ((1 : ℝ) : ℂ) * w + ((-p : ℝ) : ℂ) = w - p := by
    simp only [Complex.ofReal_one, Complex.ofReal_neg]
    ring
  have e2 : ((-1 : ℝ) : ℂ) * w + (q : ℂ) = q - w := by
    simp only [Complex.ofReal_one, Complex.ofReal_neg]
    ring
  have e3 : (q : ℂ) * ((w - p) / (q - w)) + p = w * (q - p) / (q - w) := by
    rw [mul_div_assoc', div_add' _ _ _ hu]
    congr 1
    ring
  have e4 : ((1 : ℝ) : ℂ) * ((w - p) / (q - w)) + ((1 : ℝ) : ℂ) = (q - p) / (q - w) := by
    rw [mul_div_assoc', div_add' _ _ _ hu]
    congr 1
    simp only [Complex.ofReal_one]
    ring
  unfold realMobius
  rw [e1, e2, e3, e4, div_div_div_cancel_right₀ hu, mul_div_assoc, div_self hqp, mul_one]

theorem realMobius_inv_realMobius {p q : ℝ} (hpq : p < q) {v : ℂ} (hv : 0 < v.im) :
    realMobius 1 (-p) (-1) q (realMobius q p 1 1 v) = v := by
  have hv1 : v + 1 ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hqp : (q : ℂ) - p ≠ 0 := by
    rw [← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.2 (sub_pos.2 hpq).ne'
  have e1 : ((1 : ℝ) : ℂ) * v + ((1 : ℝ) : ℂ) = v + 1 := by
    simp only [Complex.ofReal_one, one_mul]
  have e3 : ((1 : ℝ) : ℂ) * ((q * v + p) / (v + 1)) + ((-p : ℝ) : ℂ) = v * (q - p) / (v + 1) := by
    rw [mul_div_assoc', div_add' _ _ _ hv1]
    congr 1
    simp only [Complex.ofReal_one, Complex.ofReal_neg]
    ring
  have e4 : ((-1 : ℝ) : ℂ) * ((q * v + p) / (v + 1)) + (q : ℂ) = (q - p) / (v + 1) := by
    rw [mul_div_assoc', div_add' _ _ _ hv1]
    congr 1
    simp only [Complex.ofReal_one, Complex.ofReal_neg]
    ring
  unfold realMobius
  rw [e1, e3, e4, div_div_div_cancel_right₀ hv1, mul_div_assoc, div_self hqp, mul_one]

/-- A holomorphic map with a holomorphic inverse between two sets is conformal onto. -/
theorem isConformalOnto_of_leftInverse {D D' : Set ℂ} {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f D)
    (hfmaps : MapsTo f D D') (hgmaps : MapsTo g D' D) (hfg : ∀ w ∈ D', f (g w) = w)
    (hgf : ∀ z ∈ D, g (f z) = z) : IsConformalOnto f D D' := by
  refine ⟨hf, fun z₁ h₁ z₂ h₂ heq => ?_, ?_⟩
  · rw [← hgf z₁ h₁, ← hgf z₂ h₂, heq]
  · refine subset_antisymm (image_subset_iff.2 hfmaps) fun w hw => ⟨g w, hgmaps hw, hfg w hw⟩

/-- On the circle `|w - c| = R`, the map `w ↦ (w - (c - R))/((c + R) - w)` takes values on the
imaginary axis. -/
theorem re_realMobius_eq_zero_of_norm_sub {c R : ℝ} {w : ℂ} (hwc : ‖w - c‖ = R) :
    (realMobius 1 (-(c - R)) (-1) (c + R) w).re = 0 := by
  have hsq : normSq (w - c) = R ^ 2 := by rw [← hwc, Complex.sq_norm]
  unfold realMobius
  rw [Complex.div_re, ← add_div, div_eq_zero_iff]
  left
  simp only [normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero] at hsq
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, sub_zero]
  linear_combination (-1 : ℝ) * hsq

/-- The inverse map sends the imaginary axis to the circle `|w - c| = R`. -/
theorem norm_realMobius_imag_sub {c R s : ℝ} (hR : 0 < R) :
    ‖realMobius (c + R) (c - R) 1 1 ((s : ℂ) * I) - c‖ = R := by
  have hden : (s : ℂ) * I + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have heq : realMobius (c + R) (c - R) 1 1 ((s : ℂ) * I) - c
      = (R : ℂ) * (((s : ℂ) * I - 1) / ((s : ℂ) * I + 1)) := by
    unfold realMobius
    push_cast
    rw [one_mul]
    field_simp
    ring
  have h1 : ‖(s : ℂ) * I - 1‖ = ‖(s : ℂ) * I + 1‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm]
    simp only [normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.one_re, Complex.one_im]
    ring
  rw [heq, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, h1,
    div_self (norm_ne_zero_iff.2 hden), mul_one]

/-! ### Circular geodesics -/

theorem exists_circle_geodesic {z₁ z₂ : ℂ} (h₁ : z₁ ∈ upperHalf) (h₂ : z₂ ∈ upperHalf)
    (hre : z₁.re ≠ z₂.re) :
    ∃ γ : LRCurve, IsPathIn upperHalf z₁ z₂ γ ∧
      γ.rhoLength (fun z => ENNReal.ofReal (poincareDensity upperHalf z)) =
        poincareDist upperHalf z₁ z₂ ∧
      ∃ c : ℝ, ∃ R : ℝ, 0 < R ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖γ.toFun t - c‖ = R := by
  have hy₁ : 0 < z₁.im := h₁
  have hy₂ : 0 < z₂.im := h₂
  have hsub : z₂.re - z₁.re ≠ 0 := sub_ne_zero.2 (Ne.symm hre)
  -- the circle through `z₁`, `z₂` centred on the real axis
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (normSq z₂ - normSq z₁) / (2 * (z₂.re - z₁.re)) := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ‖z₁ - c‖ := ⟨_, rfl⟩
  have hR : 0 < R := by
    rw [hRdef]
    refine norm_pos_iff.2 fun h0 => ?_
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hc₁ : ‖z₁ - c‖ = R := hRdef.symm
  have hc₂ : ‖z₂ - c‖ = R := by
    rw [hRdef, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm]
    have h2 : (2 : ℝ) * (z₂.re - z₁.re) ≠ 0 := mul_ne_zero two_ne_zero hsub
    have hcc : c * (2 * (z₂.re - z₁.re)) = normSq z₂ - normSq z₁ := by
      rw [hc, div_mul_cancel₀ _ h2]
    simp only [normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero] at hcc ⊢
    linear_combination -hcc
  -- the maps `M : w ↦ (w - p)/(q - w)` and its inverse `N : v ↦ (q v + p)/(v + 1)`
  have hpq : c - R < c + R := by linarith
  have hM : (0 : ℝ) < 1 * (c + R) - (-(c - R)) * (-1) := by linarith
  have hN : (0 : ℝ) < (c + R) * 1 - (c - R) * 1 := by linarith
  have hNM : ∀ w ∈ upperHalf, realMobius (c + R) (c - R) 1 1
      (realMobius 1 (-(c - R)) (-1) (c + R) w) = w := fun w hw => realMobius_realMobius_inv hpq hw
  have hMN : ∀ v ∈ upperHalf, realMobius 1 (-(c - R)) (-1) (c + R)
      (realMobius (c + R) (c - R) 1 1 v) = v := fun v hv => realMobius_inv_realMobius hpq hv
  have hMconf : IsConformalOnto (realMobius 1 (-(c - R)) (-1) (c + R)) upperHalf upperHalf :=
    isConformalOnto_of_leftInverse (differentiableOn_realMobius hM)
      (fun w hw => realMobius_mem_upperHalf hM hw) (fun v hv => realMobius_mem_upperHalf hN hv)
      hMN hNM
  have hNconf : IsConformalOnto (realMobius (c + R) (c - R) 1 1) upperHalf upperHalf :=
    isConformalOnto_of_leftInverse (differentiableOn_realMobius hN)
      (fun v hv => realMobius_mem_upperHalf hN hv) (fun w hw => realMobius_mem_upperHalf hM hw)
      hNM hMN
  -- the images of `z₁`, `z₂` lie on the imaginary axis
  set s₁ : ℝ := (realMobius 1 (-(c - R)) (-1) (c + R) z₁).im with hs₁def
  set s₂ : ℝ := (realMobius 1 (-(c - R)) (-1) (c + R) z₂).im with hs₂def
  have hs₁ : 0 < s₁ := realMobius_mem_upperHalf hM hy₁
  have hs₂ : 0 < s₂ := realMobius_mem_upperHalf hM hy₂
  have hMz₁ : realMobius 1 (-(c - R)) (-1) (c + R) z₁ = ((0 : ℝ) : ℂ) + (s₁ : ℂ) * I :=
    Complex.ext (by rw [re_realMobius_eq_zero_of_norm_sub hc₁]; simp) (by simp [hs₁def])
  have hMz₂ : realMobius 1 (-(c - R)) (-1) (c + R) z₂ = ((0 : ℝ) : ℂ) + (s₂ : ℂ) * I :=
    Complex.ext (by rw [re_realMobius_eq_zero_of_norm_sub hc₂]; simp) (by simp [hs₂def])
  -- the vertical geodesic between the images, and its image under `N`
  have hβ := vertCurve_isPathIn (x := 0) hs₁ hs₂
  obtain ⟨γ, hγeq, hγpath⟩ := exists_isPathIn_comp isOpen_upperHalf hNconf.1 hNconf.mapsTo hβ
  rw [← hMz₁, ← hMz₂, hNM z₁ h₁, hNM z₂ h₂] at hγpath
  refine ⟨γ, hγpath, ?_, c, R, hR, fun t _ => ?_⟩
  · have hβtr : (vertCurve 0 s₁ s₂).trace ⊆ upperHalf := by
      rintro _ ⟨t, ht, rfl⟩
      exact hβ.2.2.2 ⟨t, Ioo_subset_Icc_self ht, rfl⟩
    rw [LRCurve.rhoLength_comp_of_isConformalOnto isOpen_upperHalf hNconf
      (fun v hv => poincareDensity_upperHalf_realMobius hN hv) hβtr hγeq,
      vertCurve_rhoLength_eq_poincareDist hs₁ hs₂, ← hMz₁, ← hMz₂]
    unfold poincareDist
    exact (metricDist_eq_of_isConformalOnto isOpen_upperHalf isOpen_upperHalf hMconf
      (differentiableOn_realMobius hN) (fun v hv => realMobius_mem_upperHalf hN hv) hMN hNM
      (fun w hw => poincareDensity_upperHalf_realMobius hM hw) h₁ h₂).symm
  · rw [hγeq, Function.comp_apply]
    show ‖realMobius (c + R) (c - R) 1 1 (((0 : ℝ) : ℂ)
      + (Real.exp ((1 - t) * Real.log s₁ + t * Real.log s₂) : ℂ) * I) - c‖ = R
    rw [Complex.ofReal_zero, zero_add]
    exact norm_realMobius_imag_sub hR

/-- §14.1: the Poincaré geodesics of `ℍ` are the half-circles orthogonal to `ℝ` and the vertical
half-lines: the distance between `z₁` and `z₂` is realized by a curve on such a line. -/
theorem upperHalf_geodesic {z₁ z₂ : ℂ} (h₁ : z₁ ∈ upperHalf) (h₂ : z₂ ∈ upperHalf) :
    ∃ γ : LRCurve, IsPathIn upperHalf z₁ z₂ γ ∧
      γ.rhoLength (fun z => ENNReal.ofReal (poincareDensity upperHalf z)) = poincareDist upperHalf z₁ z₂ ∧
      ((∀ t ∈ Icc (0 : ℝ) 1, (γ.toFun t).re = z₁.re) ∨
        ∃ c : ℝ, ∃ R : ℝ, 0 < R ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖γ.toFun t - c‖ = R) := by
  by_cases hre : z₁.re = z₂.re
  · obtain ⟨γ, hγ, hlen, hv⟩ := exists_vertical_geodesic h₁ h₂ hre
    exact ⟨γ, hγ, hlen, Or.inl hv⟩
  · obtain ⟨γ, hγ, hlen, c, R, hR, hcirc⟩ := exists_circle_geodesic h₁ h₂ hre
    exact ⟨γ, hγ, hlen, Or.inr ⟨c, R, hR, hcirc⟩⟩

/-! ## §14.2–14.3 The elliptic modular function -/

/-- `1` and `w` are `ℝ`-linearly independent when `Im w > 0`. -/
theorem linearIndependent_one_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    LinearIndependent ℝ ![(1 : ℂ), w] := by
  refine LinearIndependent.pair_iff.mpr fun s t hst => ?_
  have him : t * w.im = 0 := by simpa using congrArg Complex.im hst
  have ht : t = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · exact absurd h hw.ne'
  subst ht
  have hre : s = 0 := by simpa using congrArg Complex.re hst
  exact ⟨hre, rfl⟩

/-- The period pair `(1, w)` for `Im w > 0`. -/
def periodPairOf (w : ℂ) (hw : 0 < w.im) : PeriodPair := ⟨1, w, linearIndependent_one_of_im_pos hw⟩

/-- `e₁(w) = ℘(1/2; 1, w)`, `e₂(w) = ℘(w/2; 1, w)`, `e₃(w) = ℘((1+w)/2; 1, w)` (indices `0,1,2`). -/
def weierstrassE (w : ℂ) (j : Fin 3) : ℂ :=
  if hw : 0 < w.im then (periodPairOf w hw).weierstrassP (![1 / 2, w / 2, (1 + w) / 2] j) else 0

/-- The elliptic modular function (14.10), (14.20): `φ(w) = (e₃ - e₁)/(e₃ - e₂)`. -/
def modularPhi (w : ℂ) : ℂ :=
  (weierstrassE w 2 - weierstrassE w 0) / (weierstrassE w 2 - weierstrassE w 1)

/-- The region `A = {0 < u < 1, |w - 1/2| > 1/2, v > 0}` of Figure 3.14.1. -/
def modularRegionA : Set ℂ := {w : ℂ | 0 < w.re ∧ w.re < 1 ∧ 1 / 2 < ‖w - 1 / 2‖ ∧ 0 < w.im}

/-- `℘` only depends on the lattice. -/
theorem weierstrassP_eq_of_lattice_iff {L L' : PeriodPair}
    (h : ∀ x : ℂ, x ∈ L'.lattice ↔ x ∈ L.lattice) (z : ℂ) :
    L'.weierstrassP z = L.weierstrassP z := by
  have hlat : L'.lattice = L.lattice := SetLike.ext h
  simp only [PeriodPair.weierstrassP]
  rw [hlat]

/-- `℘(kz; kΛ) = k⁻² ℘(z; Λ)`, for lattices described by membership. -/
theorem weierstrassP_mul_of_mem_lattice_iff (L L' : PeriodPair) {k : ℂ} (hk : k ≠ 0)
    (hmem : ∀ x : ℂ, k * x ∈ L'.lattice ↔ x ∈ L.lattice) (z : ℂ) :
    L'.weierstrassP (k * z) = k⁻¹ ^ 2 * L.weierstrassP z := by
  obtain ⟨e, he⟩ : ∃ e : L.lattice ≃ L'.lattice, ∀ l : L.lattice, (e l : ℂ) = k * l :=
    ⟨⟨fun l => ⟨k * l, (hmem l).2 l.2⟩,
      fun l' => ⟨k⁻¹ * l', (hmem _).1 (by rw [mul_inv_cancel_left₀ hk]; exact l'.2)⟩,
      fun l => Subtype.ext (inv_mul_cancel_left₀ hk _),
      fun l' => Subtype.ext (mul_inv_cancel_left₀ hk _)⟩, fun _ => rfl⟩
  have hterm : ∀ l : ℂ, 1 / (k * z - k * l) ^ 2 - 1 / (k * l) ^ 2
      = k⁻¹ ^ 2 * (1 / (z - l) ^ 2 - 1 / l ^ 2) := by
    intro l
    rw [← mul_sub, mul_pow, mul_pow]
    simp only [one_div, mul_inv]
    ring
  simp only [PeriodPair.weierstrassP]
  rw [← e.tsum_eq]
  simp only [he, hterm]
  exact tsum_mul_left

theorem weierstrassE_zero_eq {w : ℂ} (hw : 0 < w.im) :
    weierstrassE w 0 = (periodPairOf w hw).weierstrassP (1 / 2) := by
  rw [weierstrassE, dif_pos hw]
  rfl

theorem weierstrassE_one_eq {w : ℂ} (hw : 0 < w.im) :
    weierstrassE w 1 = (periodPairOf w hw).weierstrassP (w / 2) := by
  rw [weierstrassE, dif_pos hw]
  rfl

theorem weierstrassE_two_eq {w : ℂ} (hw : 0 < w.im) :
    weierstrassE w 2 = (periodPairOf w hw).weierstrassP ((1 + w) / 2) := by
  rw [weierstrassE, dif_pos hw]
  rfl

theorem periodPairOf_weierstrassP_add_one {w : ℂ} (hw : 0 < w.im) (z : ℂ) :
    (periodPairOf w hw).weierstrassP (z + 1) = (periodPairOf w hw).weierstrassP z :=
  (periodPairOf w hw).weierstrassP_add_coe z ⟨1, (periodPairOf w hw).ω₁_mem_lattice⟩

theorem periodPairOf_weierstrassP_sub_one {w : ℂ} (hw : 0 < w.im) (z : ℂ) :
    (periodPairOf w hw).weierstrassP (z - 1) = (periodPairOf w hw).weierstrassP z :=
  (periodPairOf w hw).weierstrassP_sub_coe z ⟨1, (periodPairOf w hw).ω₁_mem_lattice⟩

theorem periodPairOf_weierstrassP_add_self {w : ℂ} (hw : 0 < w.im) (z : ℂ) :
    (periodPairOf w hw).weierstrassP (z + w) = (periodPairOf w hw).weierstrassP z :=
  (periodPairOf w hw).weierstrassP_add_coe z ⟨w, (periodPairOf w hw).ω₂_mem_lattice⟩

/-- (14.4): `φ(w + 2) = φ(w)`. -/
theorem eq14_4 {w : ℂ} (hw : 0 < w.im) : modularPhi (w + 2) = modularPhi w := by
  have hw2 : 0 < (w + 2).im := by simpa using hw
  have hlat : ∀ x : ℂ, x ∈ (periodPairOf (w + 2) hw2).lattice ↔
      x ∈ (periodPairOf w hw).lattice := by
    intro x
    simp only [PeriodPair.mem_lattice, periodPairOf]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m + 2 * n, n, by push_cast; ring⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨m - 2 * n, n, by push_cast; ring⟩
  have hP := weierstrassP_eq_of_lattice_iff hlat
  have e0 : weierstrassE (w + 2) 0 = weierstrassE w 0 := by
    rw [weierstrassE_zero_eq hw2, weierstrassE_zero_eq hw, hP]
  have e1 : weierstrassE (w + 2) 1 = weierstrassE w 1 := by
    rw [weierstrassE_one_eq hw2, weierstrassE_one_eq hw, hP,
      show (w + 2) / 2 = w / 2 + 1 by ring, periodPairOf_weierstrassP_add_one]
  have e2 : weierstrassE (w + 2) 2 = weierstrassE w 2 := by
    rw [weierstrassE_two_eq hw2, weierstrassE_two_eq hw, hP,
      show (1 + (w + 2)) / 2 = (1 + w) / 2 + 1 by ring, periodPairOf_weierstrassP_add_one]
  simp only [modularPhi, e0, e1, e2]

/-- (14.5): `φ(w) = φ(w/(2w+1))`. -/
theorem eq14_5 {w : ℂ} (hw : 0 < w.im) : modularPhi (w / (2 * w + 1)) = modularPhi w := by
  have hne : 2 * w + 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.one_im, Complex.zero_im, zero_mul, add_zero] at h'
    linarith
  have hw' : 0 < (w / (2 * w + 1)).im := by
    have hn : 0 < Complex.normSq (2 * w + 1) := Complex.normSq_pos.2 hne
    have h : (w / (2 * w + 1)).im = w.im / Complex.normSq (2 * w + 1) := by
      rw [Complex.div_im]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, Complex.one_im]
      ring
    rw [h]
    exact div_pos hw hn
  have hq : (2 * w + 1) * (w / (2 * w + 1)) = w := mul_div_cancel₀ w hne
  have hmem : ∀ x : ℂ, (2 * w + 1) * x ∈ (periodPairOf w hw).lattice ↔
      x ∈ (periodPairOf (w / (2 * w + 1)) hw').lattice := by
    intro x
    simp only [PeriodPair.mem_lattice, periodPairOf]
    constructor
    · rintro ⟨m, n, e⟩
      refine ⟨m, n - 2 * m, ?_⟩
      apply mul_left_cancel₀ hne
      push_cast
      linear_combination e + ((n : ℂ) - 2 * m) * hq
    · rintro ⟨m, n, rfl⟩
      refine ⟨m, 2 * m + n, ?_⟩
      push_cast
      linear_combination (-(n : ℂ)) * hq
  have hscale : ∀ z : ℂ, (periodPairOf (w / (2 * w + 1)) hw').weierstrassP z =
      (2 * w + 1) ^ 2 * (periodPairOf w hw).weierstrassP ((2 * w + 1) * z) := by
    intro z
    rw [weierstrassP_mul_of_mem_lattice_iff _ _ hne hmem z, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hne, one_pow, one_mul]
  have e0 : weierstrassE (w / (2 * w + 1)) 0 = (2 * w + 1) ^ 2 * weierstrassE w 0 := by
    rw [weierstrassE_zero_eq hw', weierstrassE_zero_eq hw, hscale,
      show (2 * w + 1) * (1 / 2) = 1 / 2 + w by ring, periodPairOf_weierstrassP_add_self]
  have e1 : weierstrassE (w / (2 * w + 1)) 1 = (2 * w + 1) ^ 2 * weierstrassE w 1 := by
    rw [weierstrassE_one_eq hw', weierstrassE_one_eq hw, hscale,
      show (2 * w + 1) * (w / (2 * w + 1) / 2) = w / 2 by rw [mul_div_assoc', hq]]
  have e2 : weierstrassE (w / (2 * w + 1)) 2 = (2 * w + 1) ^ 2 * weierstrassE w 2 := by
    rw [weierstrassE_two_eq hw', weierstrassE_two_eq hw, hscale,
      show (2 * w + 1) * ((1 + w / (2 * w + 1)) / 2) = (1 + w) / 2 + w by
        rw [mul_div_assoc', mul_add, mul_one, hq]; ring,
      periodPairOf_weierstrassP_add_self]
  simp only [modularPhi, e0, e1, e2]
  rw [← mul_sub, ← mul_sub, mul_div_mul_left _ _ (pow_ne_zero 2 hne)]

/-! ### Helpers for `modularPhi_gamma2_invariant` (`g2_`): Euclidean descent in `Γ(2)`

`Γ(2)` is generated by `w ↦ w + 2`, `w ↦ w/(2w + 1)` and `-1`.  Instead of proving that
generation statement we run the descent directly on the integer entries: for `(a b; c d)` with
`ad - bc = 1`, `a, d` odd and `b, c` even, left multiplication by `(1 2m; 0 1)` or `(1 0; 2m 1)`
lowers `|a| + |c|` until `c = 0`, and each step changes the Möbius image by one of the two
generating maps, under which `φ` is invariant by (14.4) and (14.5). -/

/-- The imaginary part of a Möbius image `(aw + b)/(cw + d)`, `ad - bc = 1`, is
`Im w / |cw + d|² > 0`. -/
theorem g2_im_mobius {a b c d : ℤ} {w : ℂ} (hw : 0 < w.im) (hdet : a * d - b * c = 1)
    (hden : (c : ℂ) * w + d ≠ 0) :
    0 < (((a : ℂ) * w + b) / ((c : ℂ) * w + d)).im := by
  have hns : 0 < Complex.normSq ((c : ℂ) * w + d) := Complex.normSq_pos.mpr hden
  have hdet' : (a : ℝ) * d - b * c = 1 := by exact_mod_cast hdet
  have key : ((a : ℂ) * w + b).im * ((c : ℂ) * w + d).re -
      ((a : ℂ) * w + b).re * ((c : ℂ) * w + d).im = w.im := by
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, zero_mul, sub_zero, add_zero]
    linear_combination w.im * hdet'
  rw [Complex.div_im, ← sub_div, key]
  exact div_pos hw hns

/-- `cw + d ≠ 0` for `Im w > 0` unless `c = d = 0`. -/
theorem g2_den_ne_zero {c d : ℤ} {w : ℂ} (hw : 0 < w.im) (h : c ≠ 0 ∨ d ≠ 0) :
    (c : ℂ) * w + d ≠ 0 := by
  intro h0
  have him : ((c : ℂ) * w + d).im = c * w.im := by
    simp [Complex.add_im, Complex.mul_im]
  have hre : ((c : ℂ) * w + d).re = c * w.re + d := by
    simp [Complex.add_re, Complex.mul_re]
  have h1 : (c : ℝ) * w.im = 0 := by rw [← him, h0, Complex.zero_im]
  have hc0 : (c : ℝ) = 0 := by
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact h2
    · exact absurd h2 hw.ne'
  rcases h with hc | hd
  · exact hc (by exact_mod_cast hc0)
  · have h2 : (c : ℝ) * w.re + d = 0 := by rw [← hre, h0, Complex.zero_re]
    rw [hc0, zero_mul, zero_add] at h2
    exact hd (by exact_mod_cast h2)

/-- `ad - bc = 1` forces `(c, d) ≠ (0, 0)`. -/
theorem g2_cd_ne_zero {a b c d : ℤ} (hdet : a * d - b * c = 1) : c ≠ 0 ∨ d ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  rw [h.1, h.2] at hdet
  simp at hdet

theorem g2_im_add (w : ℂ) (k : ℤ) : (w + 2 * (k : ℂ)).im = w.im := by
  simp

/-- (14.4) iterated: `φ(w + 2k) = φ(w)` for every integer `k`. -/
theorem g2_shift (k : ℤ) {w : ℂ} (hw : 0 < w.im) : modularPhi (w + 2 * k) = modularPhi w := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have hw' : 0 < (w + 2 * ((k : ℤ) : ℂ)).im := by rw [g2_im_add]; exact hw
    have e : w + 2 * (((k : ℤ) + 1 : ℤ) : ℂ) = (w + 2 * ((k : ℤ) : ℂ)) + 2 := by
      push_cast; ring
    rw [e, eq14_4 hw', ih]
  | pred k ih =>
    have hw' : 0 < (w + 2 * ((-(k : ℤ) - 1 : ℤ) : ℂ)).im := by rw [g2_im_add]; exact hw
    have e : (w + 2 * ((-(k : ℤ) - 1 : ℤ) : ℂ)) + 2 = w + 2 * ((-(k : ℤ) : ℤ) : ℂ) := by
      push_cast; ring
    have h := eq14_4 hw'
    rw [e] at h
    rw [← h, ih]

theorem g2_im_uact (m : ℤ) {v : ℂ} (hv : 0 < v.im) : 0 < (v / (2 * m * v + 1)).im := by
  have hden : (2 * (m : ℂ) * v + 1) ≠ 0 := by
    have := g2_den_ne_zero (c := 2 * m) (d := 1) hv (Or.inr one_ne_zero)
    push_cast at this
    exact this
  have hns : 0 < Complex.normSq (2 * (m : ℂ) * v + 1) := Complex.normSq_pos.mpr hden
  have key : v.im * (2 * (m : ℂ) * v + 1).re - v.re * (2 * (m : ℂ) * v + 1).im = v.im := by
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
    ring
  rw [Complex.div_im, ← sub_div, key]
  exact div_pos hv hns

/-- (14.5) iterated: `φ(v/(2mv + 1)) = φ(v)` for every integer `m`. -/
theorem g2_uact (m : ℤ) {v : ℂ} (hv : 0 < v.im) :
    modularPhi (v / (2 * m * v + 1)) = modularPhi v := by
  have hden : ∀ k : ℤ, (2 * (k : ℂ) * v + 1) ≠ 0 := fun k => by
    have := g2_den_ne_zero (c := 2 * k) (d := 1) hv (Or.inr one_ne_zero)
    push_cast at this
    exact this
  -- `u/(2u + 1) = v/(2(k+1)v + 1)` for `u = v/(2kv + 1)`
  have step : ∀ k : ℤ, (v / (2 * k * v + 1)) / (2 * (v / (2 * k * v + 1)) + 1) =
      v / (2 * ((k + 1 : ℤ) : ℂ) * v + 1) := by
    intro k
    have h1 : 2 * (v / (2 * k * v + 1)) + 1 = (2 * ((k + 1 : ℤ) : ℂ) * v + 1) / (2 * k * v + 1) := by
      rw [eq_div_iff (hden k), add_mul, mul_assoc, div_mul_cancel₀ _ (hden k), one_mul]
      push_cast
      ring
    rw [h1, div_div_div_cancel_right₀ (hden k)]
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [← step (k : ℤ), eq14_5 (g2_im_uact (k : ℤ) hv), ih]
  | pred k ih =>
    have h := step (-(k : ℤ) - 1)
    rw [sub_add_cancel] at h
    rw [← h, eq14_5 (g2_im_uact (-(k : ℤ) - 1) hv)] at ih
    exact ih

/-- The descent step: for `y ≠ 0` and `x + y` odd, some `x + 2my` is smaller than `y`
in absolute value (the remainder of `x` modulo `2y`, recentred). -/
theorem g2_exists_reduce (x y : ℤ) (hy : y ≠ 0) (hxy : Odd (x + y)) :
    ∃ m : ℤ, (x + 2 * m * y).natAbs < y.natAbs := by
  -- reduce to `y > 0`
  suffices key : ∀ y : ℤ, 0 < y → Odd (x + y) → ∃ m : ℤ, (x + 2 * m * y).natAbs < y.natAbs by
    rcases lt_or_gt_of_ne hy with hneg | hpos
    · have hodd : Odd (x + -y) := by
        have h := hxy.sub_even (even_two_mul y)
        convert h using 1
        ring
      obtain ⟨m, hm⟩ := key (-y) (by omega) hodd
      refine ⟨-m, ?_⟩
      rw [Int.natAbs_neg] at hm
      convert hm using 2
      ring
    · exact key y hpos hxy
  intro y hy hxy
  have h2y : 0 < 2 * y := by omega
  have hr0 : 0 ≤ x % (2 * y) := Int.emod_nonneg x (by omega)
  have hr1 : x % (2 * y) < 2 * y := Int.emod_lt_of_pos x h2y
  have hx : x % (2 * y) + 2 * y * (x / (2 * y)) = x := by rw [Int.emod_def]; ring
  have hry : x % (2 * y) ≠ y := by
    intro hry
    apply Int.not_even_iff_odd.2 hxy
    exact ⟨y + y * (x / (2 * y)), by linear_combination -hx + hry⟩
  rcases lt_or_gt_of_ne hry with hlt | hgt
  · refine ⟨-(x / (2 * y)), ?_⟩
    have e : x + 2 * -(x / (2 * y)) * y = x % (2 * y) := by linear_combination -hx
    rw [e]
    exact Int.natAbs_lt_natAbs_of_nonneg_of_lt hr0 hlt
  · refine ⟨-(x / (2 * y) + 1), ?_⟩
    have e : x + 2 * -(x / (2 * y) + 1) * y = -(2 * y - x % (2 * y)) := by
      linear_combination -hx
    rw [e, Int.natAbs_neg]
    exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (by omega) (by omega)

theorem g2_even_of_zmod {a : ℤ} (h : (a : ZMod 2) = 0) : Even a := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  exact even_iff_two_dvd.2 (by exact_mod_cast h)

theorem g2_odd_of_zmod {a : ℤ} (h : (a : ZMod 2) = 1) : Odd a := by
  have h' : ((a - 1 : ℤ) : ZMod 2) = 0 := by push_cast; rw [h, sub_self]
  exact Int.not_even_iff_odd.1 (Int.even_sub_one.1 (g2_even_of_zmod h'))

/-- The descent: `φ ∘ γ = φ` for every integer matrix `(a b; c d)` of determinant one with
`a, d` odd and `b, c` even, by strong induction on `|a| + |c|`. -/
theorem g2_main (n : ℕ) : ∀ (a b c d : ℤ), a.natAbs + c.natAbs = n → a * d - b * c = 1 →
    Odd a → Even b → Even c → Odd d → ∀ w : ℂ, 0 < w.im →
    modularPhi (((a : ℂ) * w + b) / ((c : ℂ) * w + d)) = modularPhi w := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b c d hn hdet ha hb hc hd w hw
  by_cases hc0 : c = 0
  · -- `c = 0`: `a = d = ±1` and the map is a translation by the even integer `±b`
    subst hc0
    have had : a * d = 1 := by simpa using hdet
    obtain ⟨k, hk⟩ := hb
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have e : (((1 : ℤ) : ℂ) * w + b) / (((0 : ℤ) : ℂ) * w + ((1 : ℤ) : ℂ)) = w + 2 * k := by
        rw [hk]; push_cast; ring
      rw [e]
      exact g2_shift k hw
    · have e : (((-1 : ℤ) : ℂ) * w + b) / (((0 : ℤ) : ℂ) * w + ((-1 : ℤ) : ℂ)) =
          w + 2 * (-k : ℤ) := by
        rw [hk]; push_cast; ring
      rw [e]
      exact g2_shift (-k) hw
  · have ha0 : a ≠ 0 := by
      rintro rfl
      exact (Int.not_even_iff_odd.2 ha) ⟨0, by simp⟩
    have hden : (c : ℂ) * w + d ≠ 0 := g2_den_ne_zero hw (Or.inl hc0)
    set v : ℂ := ((a : ℂ) * w + b) / ((c : ℂ) * w + d) with hv
    have hvim : 0 < v.im := g2_im_mobius hw hdet hden
    have hne : a.natAbs ≠ c.natAbs := by
      intro h
      rcases Int.natAbs_eq_natAbs_iff.1 h with h1 | h1
      · exact (Int.not_even_iff_odd.2 ha) (h1 ▸ hc)
      · exact (Int.not_even_iff_odd.2 ha) (h1 ▸ hc.neg)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `|a| < |c|`: lower `|c|` by a left multiplication with `(1 0; 2m 1)`
      obtain ⟨m, hm⟩ := g2_exists_reduce c a ha0 (hc.add_odd ha)
      have hc' : Even (c + 2 * m * a) := hc.add ((even_two_mul m).mul_right a)
      have hd' : Odd (d + 2 * m * b) := hd.add_even ((even_two_mul m).mul_right b)
      have hdet' : a * (d + 2 * m * b) - b * (c + 2 * m * a) = 1 := by linear_combination hdet
      have hlt' : a.natAbs + (c + 2 * m * a).natAbs < n := by
        rw [← hn]
        exact Nat.add_lt_add_left (lt_trans hm hlt) _
      have h := ih _ hlt' a b (c + 2 * m * a) (d + 2 * m * b) rfl hdet' ha hb hc' hd' w hw
      have hden' : ((c + 2 * m * a : ℤ) : ℂ) * w + ((d + 2 * m * b : ℤ) : ℂ) ≠ 0 :=
        g2_den_ne_zero hw (g2_cd_ne_zero hdet')
      have e : ((a : ℂ) * w + b) / (((c + 2 * m * a : ℤ) : ℂ) * w + ((d + 2 * m * b : ℤ) : ℂ)) =
          v / (2 * m * v + 1) := by
        have h1 : 2 * (m : ℂ) * v + 1 =
            (((c + 2 * m * a : ℤ) : ℂ) * w + ((d + 2 * m * b : ℤ) : ℂ)) / ((c : ℂ) * w + d) := by
          rw [hv, eq_div_iff hden, add_mul, mul_assoc, div_mul_cancel₀ _ hden, one_mul]
          push_cast
          ring
        rw [h1, hv, div_div_div_cancel_right₀ hden]
      rw [e, g2_uact m hvim] at h
      exact h
    · -- `|a| > |c|`: lower `|a|` by a left multiplication with `(1 2m; 0 1)`
      obtain ⟨m, hm⟩ := g2_exists_reduce a c hc0 (ha.add_even hc)
      have ha' : Odd (a + 2 * m * c) := ha.add_even ((even_two_mul m).mul_right c)
      have hb' : Even (b + 2 * m * d) := hb.add ((even_two_mul m).mul_right d)
      have hdet' : (a + 2 * m * c) * d - (b + 2 * m * d) * c = 1 := by linear_combination hdet
      have hlt' : (a + 2 * m * c).natAbs + c.natAbs < n := by
        rw [← hn]
        exact Nat.add_lt_add_right (lt_trans hm hgt) _
      have h := ih _ hlt' (a + 2 * m * c) (b + 2 * m * d) c d rfl hdet' ha' hb' hc hd w hw
      have e : (((a + 2 * m * c : ℤ) : ℂ) * w + ((b + 2 * m * d : ℤ) : ℂ)) / ((c : ℂ) * w + d) =
          v + 2 * m := by
        rw [hv, div_add' _ _ _ hden]
        push_cast
        ring
      rw [e, g2_shift m hvim] at h
      exact h

/-- §14.2: `φ` is invariant under the modular group `Γ(2)` of transformations
`w ↦ (aw + b)/(cw + d)`, `ad - bc = 1`, `(a b; c d) ≡ I mod 2`. -/
theorem modularPhi_gamma2_invariant {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma 2) {w : ℂ} (hw : 0 < w.im) :
    modularPhi ((γ 0 0 * w + γ 0 1) / (γ 1 0 * w + γ 1 1)) = modularPhi w := by
  obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  exact g2_main _ (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) rfl hdet (g2_odd_of_zmod h00)
    (g2_even_of_zmod h01) (g2_even_of_zmod h10) (g2_odd_of_zmod h11) w hw

/-- (14.9): `℘(kz; kω₁, kω₂) = k⁻² ℘(z; ω₁, ω₂)`. -/
theorem eq14_9 (L L' : PeriodPair) {k : ℂ} (hk : k ≠ 0) (h₁ : L'.ω₁ = k * L.ω₁)
    (h₂ : L'.ω₂ = k * L.ω₂) (z : ℂ) : L'.weierstrassP (k * z) = k⁻¹ ^ 2 * L.weierstrassP z := by
  -- `L'` is the lattice `k · L`
  have hmem : ∀ x : ℂ, k * x ∈ L'.lattice ↔ x ∈ L.lattice := by
    intro x
    simp only [PeriodPair.mem_lattice, h₁, h₂]
    constructor
    · rintro ⟨m, n, e⟩
      exact ⟨m, n, mul_left_cancel₀ hk (by rw [← e]; ring)⟩
    · rintro ⟨m, n, e⟩
      exact ⟨m, n, by rw [← e]; ring⟩
  obtain ⟨e, he⟩ : ∃ e : L.lattice ≃ L'.lattice, ∀ l : L.lattice, (e l : ℂ) = k * l :=
    ⟨⟨fun l => ⟨k * l, (hmem l).2 l.2⟩,
      fun l' => ⟨k⁻¹ * l', (hmem _).1 (by rw [mul_inv_cancel_left₀ hk]; exact l'.2)⟩,
      fun l => Subtype.ext (inv_mul_cancel_left₀ hk _),
      fun l' => Subtype.ext (mul_inv_cancel_left₀ hk _)⟩, fun _ => rfl⟩
  -- termwise, including the junk values `1 / 0 = 0`
  have hterm : ∀ l : ℂ, 1 / (k * z - k * l) ^ 2 - 1 / (k * l) ^ 2
      = k⁻¹ ^ 2 * (1 / (z - l) ^ 2 - 1 / l ^ 2) := by
    intro l
    rw [← mul_sub, mul_pow, mul_pow]
    simp only [one_div, mul_inv]
    ring
  simp only [PeriodPair.weierstrassP]
  rw [← e.tsum_eq]
  simp only [he, hterm]
  exact tsum_mul_left

/-- (14.8): `℘(z; ω₁ + ω₂, ω₂) = ℘(z; ω₁, ω₂)`. -/
theorem eq14_8 (L L' : PeriodPair) (h₁ : L'.ω₁ = L.ω₁ + L.ω₂) (h₂ : L'.ω₂ = L.ω₂) (z : ℂ) :
    L'.weierstrassP z = L.weierstrassP z := by
  have hlat : L'.lattice = L.lattice := by
    simp only [PeriodPair.lattice, h₁, h₂]
    apply le_antisymm
    · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨add_mem (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp)),
        Submodule.subset_span (by simp)⟩
    · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨?_, Submodule.subset_span (by simp)⟩
      have h := sub_mem
        (Submodule.subset_span (R := ℤ) (show L.ω₁ + L.ω₂ ∈ ({L.ω₁ + L.ω₂, L.ω₂} : Set ℂ) by simp))
        (Submodule.subset_span (R := ℤ) (show L.ω₂ ∈ ({L.ω₁ + L.ω₂, L.ω₂} : Set ℂ) by simp))
      simpa using h
  simp only [PeriodPair.weierstrassP]
  rw [hlat]

/-! ### Helpers for (14.11) (`mphi_`): distinctness of `e₁, e₂, e₃` and the shift `w ↦ w + 1` -/

/-- The three values `e₁(w), e₂(w), e₃(w)` are pairwise distinct for `Im w > 0`: `℘` takes each
value only twice in a period parallelogram (`half_period_values_ne`, from
`Lemmas/WeierstrassValues`). -/
theorem mphi_weierstrassE_pairwise_ne {w : ℂ} (hw : 0 < w.im) :
    weierstrassE w 0 ≠ weierstrassE w 1 ∧ weierstrassE w 0 ≠ weierstrassE w 2 ∧
      weierstrassE w 1 ≠ weierstrassE w 2 := by
  rw [weierstrassE_zero_eq hw, weierstrassE_one_eq hw, weierstrassE_two_eq hw]
  exact half_period_values_ne (L := periodPairOf w hw) rfl hw

/-- `w ↦ w + 1` keeps the lattice `⟨1, w⟩` and swaps the half periods `w/2` and `(1 + w)/2` modulo
the lattice: `e₁(w + 1) = e₁(w)`, `e₂(w + 1) = e₃(w)`, `e₃(w + 1) = e₂(w)`. -/
theorem mphi_weierstrassE_add_one {w : ℂ} (hw : 0 < w.im) :
    weierstrassE (w + 1) 0 = weierstrassE w 0 ∧
    weierstrassE (w + 1) 1 = weierstrassE w 2 ∧
    weierstrassE (w + 1) 2 = weierstrassE w 1 := by
  have hw1 : 0 < (w + 1).im := by simpa using hw
  have hlat : ∀ x : ℂ, x ∈ (periodPairOf (w + 1) hw1).lattice ↔
      x ∈ (periodPairOf w hw).lattice := by
    intro x
    simp only [PeriodPair.mem_lattice, periodPairOf]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m + n, n, by push_cast; ring⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨m - n, n, by push_cast; ring⟩
  have hP := weierstrassP_eq_of_lattice_iff hlat
  refine ⟨?_, ?_, ?_⟩
  · rw [weierstrassE_zero_eq hw1, weierstrassE_zero_eq hw, hP]
  · rw [weierstrassE_one_eq hw1, weierstrassE_two_eq hw, hP,
      show (w + 1) / 2 = (1 + w) / 2 by ring]
  · rw [weierstrassE_two_eq hw1, weierstrassE_one_eq hw, hP,
      show (1 + (w + 1)) / 2 = w / 2 + 1 by ring, periodPairOf_weierstrassP_add_one]

/-- (14.11): `q(w + 1) = 1 - q(w)`.

Proved (2026-09-24): the lattice of `(1, w + 1)` is that of `(1, w)`, so `e₁(w + 1) = e₁(w)` while
`e₂` and `e₃` are swapped (`mphi_weierstrassE_add_one`); the identity then only needs
`e₂(w) ≠ e₃(w)` (`mphi_weierstrassE_pairwise_ne`), the degree-two property of `℘`
(`half_period_values_ne`, proved with the argument principle on a period parallelogram in
`Lemmas/WeierstrassValues`). -/
theorem eq14_11 {w : ℂ} (hw : 0 < w.im) : modularPhi (w + 1) = 1 - modularPhi w := by
  obtain ⟨e0, e1, e2⟩ := mphi_weierstrassE_add_one hw
  obtain ⟨-, -, h12⟩ := mphi_weierstrassE_pairwise_ne hw
  have hd : weierstrassE w 2 - weierstrassE w 1 ≠ 0 := sub_ne_zero.2 (Ne.symm h12)
  have hd' : weierstrassE w 1 - weierstrassE w 2 ≠ 0 := sub_ne_zero.2 h12
  simp only [modularPhi, e0, e1, e2]
  field_simp
  ring

/-- (14.12): `q(-1/w) = 1/q(w)`. -/
theorem eq14_12 {w : ℂ} (hw : 0 < w.im) : modularPhi (-1 / w) = 1 / modularPhi w := by
  have hne : w ≠ 0 := fun h => by rw [h, Complex.zero_im] at hw; exact lt_irrefl 0 hw
  have hw' : 0 < (-1 / w).im := by
    have hn : 0 < Complex.normSq w := Complex.normSq_pos.2 hne
    have h : (-1 / w).im = w.im / Complex.normSq w := by
      rw [Complex.div_im]
      simp only [Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, neg_zero,
        zero_mul, zero_div, zero_sub]
      ring
    rw [h]
    exact div_pos hw hn
  have hmem : ∀ x : ℂ, w * x ∈ (periodPairOf w hw).lattice ↔
      x ∈ (periodPairOf (-1 / w) hw').lattice := by
    intro x
    simp only [PeriodPair.mem_lattice, periodPairOf]
    constructor
    · rintro ⟨m, n, e⟩
      refine ⟨n, -m, ?_⟩
      field_simp
      push_cast
      linear_combination e
    · rintro ⟨m, n, rfl⟩
      refine ⟨-n, m, ?_⟩
      field_simp
      push_cast
      ring
  have hscale : ∀ z : ℂ, (periodPairOf (-1 / w) hw').weierstrassP z =
      w ^ 2 * (periodPairOf w hw).weierstrassP (w * z) := by
    intro z
    rw [weierstrassP_mul_of_mem_lattice_iff _ _ hne hmem z, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hne, one_pow, one_mul]
  have e0 : weierstrassE (-1 / w) 0 = w ^ 2 * weierstrassE w 1 := by
    rw [weierstrassE_zero_eq hw', weierstrassE_one_eq hw, hscale,
      show w * (1 / 2) = w / 2 by ring]
  have e1 : weierstrassE (-1 / w) 1 = w ^ 2 * weierstrassE w 0 := by
    rw [weierstrassE_one_eq hw', weierstrassE_zero_eq hw, hscale,
      show w * (-1 / w / 2) = -(1 / 2) by field_simp, PeriodPair.weierstrassP_neg]
  have e2 : weierstrassE (-1 / w) 2 = w ^ 2 * weierstrassE w 2 := by
    rw [weierstrassE_two_eq hw', weierstrassE_two_eq hw, hscale,
      show w * ((1 + -1 / w) / 2) = (1 + w) / 2 - 1 by field_simp; ring,
      periodPairOf_weierstrassP_sub_one]
  simp only [modularPhi, e0, e1, e2]
  rw [← mul_sub, ← mul_sub, mul_div_mul_left _ _ (pow_ne_zero 2 hne), one_div_div]

/-! ### Helpers for (14.13)–(14.15) (`mphi_`): signs on the imaginary axis

`℘(a) - ℘(b)` is summed row by row, and each row sum has the closed form
`∑_m 1/(ζ + m)² = -4π² y/(1 - y)²`, `y = e^{2πiζ}`, so on the imaginary axis every row of
`e₃ - e₂` is a positive real. -/

/-- The row sum `∑_{m ∈ ℤ} 1/(ζ + m)²` of a Weierstrass lattice sum (`℘` is summed row by row). -/
def mphi_rowS (ζ : ℂ) : ℂ := ∑' m : ℤ, 1 / (ζ + m) ^ 2

/-- The row sum converges absolutely (Eisenstein-series summability). -/
theorem mphi_rowS_summable (ζ : ℂ) : Summable fun m : ℤ => 1 / (ζ + m) ^ 2 := by
  have h := EisensteinSeries.linear_right_summable ζ 1 (k := 2) (by norm_num)
  refine h.congr fun m => ?_
  simp [one_div]

/-- For `Im ζ > 0`: `∑_m 1/(ζ + m)² = -4π² y/(1 - y)²` with `y = e^{2πiζ}` (the `q`-expansion
identity `EisensteinSeries.qExpansion_identity` with `k = 1`). -/
theorem mphi_rowS_eq_of_im_pos {ζ : ℂ} (hζ : 0 < ζ.im) :
    mphi_rowS ζ = -4 * (π : ℂ) ^ 2 * (cexp (2 * π * I * ζ) / (1 - cexp (2 * π * I * ζ)) ^ 2) := by
  have h := EisensteinSeries.qExpansion_identity (k := 1) le_rfl ⟨ζ, hζ⟩
  have hq : ‖cexp (2 * π * I * ζ)‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨ζ, hζ⟩
  have hg := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℂ) hq).tsum_eq
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h
  rw [mphi_rowS, h, hg]
  ring_nf
  rw [I_sq]
  ring

/-- The row sum is even. -/
theorem mphi_rowS_neg (ζ : ℂ) : mphi_rowS (-ζ) = mphi_rowS ζ := by
  rw [mphi_rowS, mphi_rowS, ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun m => ?_
  simp only [Equiv.neg_apply, Int.cast_neg]
  rw [show -ζ + -(m : ℂ) = -(ζ + m) by ring, neg_sq]

/-- The row sum is `1`-periodic. -/
theorem mphi_rowS_add_one (ζ : ℂ) : mphi_rowS (ζ + 1) = mphi_rowS ζ := by
  rw [mphi_rowS, mphi_rowS]
  conv_rhs => rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]
  refine tsum_congr fun m => ?_
  simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one]
  ring_nf

/-- The row sum, indexed by `ζ - m`. -/
theorem mphi_rowS_hasSum_neg (ζ : ℂ) : HasSum (fun m : ℤ => 1 / (ζ - m) ^ 2) (mphi_rowS ζ) := by
  have h := (mphi_rowS_summable ζ).hasSum
  rw [← (Equiv.neg ℤ).hasSum_iff] at h
  unfold mphi_rowS
  convert h using 2 with m
  simp [sub_eq_add_neg]

/-- `℘(a) - ℘(b)` for the lattice `⟨1, w⟩`, summed row by row: the `n`-th row contributes
`mphi_rowS (a - n w) - mphi_rowS (b - n w)`. -/
theorem mphi_wp_sub_hasSum_rows {w : ℂ} (hw : 0 < w.im) (a b : ℂ) :
    HasSum (fun n : ℤ => mphi_rowS (a - n * w) - mphi_rowS (b - n * w))
      ((periodPairOf w hw).weierstrassP a -
        (periodPairOf w hw).weierstrassP b) := by
  set L := periodPairOf w hw with hL
  have h1 := (L.hasSum_weierstrassP a).sub (L.hasSum_weierstrassP b)
  set e : ℤ × ℤ ≃ L.lattice := (Equiv.prodComm ℤ ℤ).trans L.latticeEquivProd.symm.toEquiv
    with he
  have hev : ∀ p : ℤ × ℤ, ((e p : L.lattice) : ℂ) = p.2 + p.1 * w := by
    intro p
    simp only [he, Equiv.trans_apply, Equiv.prodComm_apply, LinearEquiv.coe_toEquiv]
    rw [L.latticeEquiv_symm_apply]
    simp [hL, periodPairOf]
  rw [← e.hasSum_iff] at h1
  have h2 : HasSum (fun p : ℤ × ℤ => 1 / (a - (p.2 + p.1 * w)) ^ 2 - 1 / (b - (p.2 + p.1 * w)) ^ 2)
      (L.weierstrassP a - L.weierstrassP b) := by
    convert h1 using 2 with p
    simp only [Function.comp_apply, hev]
    ring
  refine h2.prod_fiberwise fun n => ?_
  have ha := mphi_rowS_hasSum_neg (a - n * w)
  have hb := mphi_rowS_hasSum_neg (b - n * w)
  convert ha.sub hb using 2 with m
  simp only
  ring_nf

/-- `e^{2πi (sI)} = e^{-2πs}`. -/
theorem mphi_cexp_two_pi_I_mul_I (s : ℝ) :
    cexp (2 * π * I * ((s : ℂ) * I)) = (Real.exp (-2 * π * s) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- The row sum on the imaginary axis: `mphi_rowS (sI) = -4π² e^{-2πs}/(1 - e^{-2πs})²` for
`s > 0`. -/
theorem mphi_rowS_I {s : ℝ} (hs : 0 < s) :
    mphi_rowS ((s : ℂ) * I) =
      ((-4 * π ^ 2 * (Real.exp (-2 * π * s) / (1 - Real.exp (-2 * π * s)) ^ 2) : ℝ) : ℂ) := by
  rw [mphi_rowS_eq_of_im_pos (by simpa using hs), mphi_cexp_two_pi_I_mul_I]
  push_cast
  ring

/-- The row sum on `Re ζ = 1/2`: `mphi_rowS (1/2 + sI) = 4π² e^{-2πs}/(1 + e^{-2πs})²` for
`s > 0`. -/
theorem mphi_rowS_half_I {s : ℝ} (hs : 0 < s) :
    mphi_rowS (1 / 2 + (s : ℂ) * I) =
      ((4 * π ^ 2 * (Real.exp (-2 * π * s) / (1 + Real.exp (-2 * π * s)) ^ 2) : ℝ) : ℂ) := by
  rw [mphi_rowS_eq_of_im_pos (by simpa using hs)]
  have : cexp (2 * π * I * (1 / 2 + (s : ℂ) * I)) = -(Real.exp (-2 * π * s) : ℂ) := by
    rw [show 2 * π * I * (1 / 2 + (s : ℂ) * I) = π * I + 2 * π * I * ((s : ℂ) * I) by ring,
      Complex.exp_add, mphi_cexp_two_pi_I_mul_I, Complex.exp_pi_mul_I]
    ring
  rw [this]
  push_cast
  ring

/-- `mphi_rowP s = 4π² (e^{-2πs}/(1 + e^{-2πs})² + e^{-2πs}/(1 - e^{-2πs})²)`: the row term
`mphi_rowS (1/2 + tI) - mphi_rowS (tI)` for `s = |t|`. -/
def mphi_rowP (s : ℝ) : ℝ :=
  4 * π ^ 2 * (Real.exp (-2 * π * s) / (1 + Real.exp (-2 * π * s)) ^ 2 +
    Real.exp (-2 * π * s) / (1 - Real.exp (-2 * π * s)) ^ 2)

/-- `mphi_rowP s > 0` for `s > 0`. -/
theorem mphi_rowP_pos {s : ℝ} (hs : 0 < s) : 0 < mphi_rowP s := by
  have h1 : Real.exp (-2 * π * s) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have h0 := Real.exp_pos (-2 * π * s)
  unfold mphi_rowP
  have : 0 < (1 - Real.exp (-2 * π * s)) ^ 2 := by nlinarith
  positivity

/-- The row difference `mphi_rowS (1/2 + tI) - mphi_rowS (tI)` equals `mphi_rowP |t|` for
`t ≠ 0`. -/
theorem mphi_rowDiff_eq {t : ℝ} (ht : t ≠ 0) :
    mphi_rowS (1 / 2 + (t : ℂ) * I) - mphi_rowS ((t : ℂ) * I) = (mphi_rowP |t| : ℂ) := by
  rcases lt_or_gt_of_ne ht with h | h
  · have h' : 0 < -t := by linarith
    have e1 : mphi_rowS (1 / 2 + (t : ℂ) * I) = mphi_rowS (1 / 2 + ((-t : ℝ) : ℂ) * I) := by
      rw [← mphi_rowS_neg, ← mphi_rowS_add_one]
      congr 1
      push_cast
      ring
    have e2 : mphi_rowS ((t : ℂ) * I) = mphi_rowS (((-t : ℝ) : ℂ) * I) := by
      rw [← mphi_rowS_neg]
      congr 1
      push_cast
      ring
    rw [e1, e2, mphi_rowS_half_I h', mphi_rowS_I h', abs_of_neg h, mphi_rowP]
    push_cast
    ring
  · rw [mphi_rowS_half_I h, mphi_rowS_I h, abs_of_pos h, mphi_rowP]
    push_cast
    ring

/-- `e₃(iv) - e₂(iv)` is a positive real number. -/
theorem mphi_weierstrassE_two_sub_one_iv {v : ℝ} (hv : 0 < v) :
    ∃ r : ℝ, 0 < r ∧
      weierstrassE ((v : ℂ) * I) 2 - weierstrassE ((v : ℂ) * I) 1 = r := by
  have hw : 0 < ((v : ℂ) * I).im := by simpa using hv
  rw [weierstrassE_two_eq hw, weierstrassE_one_eq hw]
  have h := mphi_wp_sub_hasSum_rows hw ((1 + (v : ℂ) * I) / 2) ((v : ℂ) * I / 2)
  have hne : ∀ n : ℤ, ((1 / 2 - n) * v : ℝ) ≠ 0 := by
    intro n
    refine mul_ne_zero ?_ hv.ne'
    intro h0
    have : (2 * n : ℝ) = 1 := by linarith
    have h2 : (2 * n : ℤ) = 1 := by exact_mod_cast this
    omega
  have hterm : ∀ n : ℤ, mphi_rowS ((1 + (v : ℂ) * I) / 2 - n * ((v : ℂ) * I)) -
      mphi_rowS ((v : ℂ) * I / 2 - n * ((v : ℂ) * I)) = (mphi_rowP |(1 / 2 - n) * v| : ℂ) := by
    intro n
    rw [← mphi_rowDiff_eq (hne n)]
    congr 2 <;> push_cast <;> ring
  simp only [hterm] at h
  refine ⟨∑' n : ℤ, mphi_rowP |(1 / 2 - n) * v|, ?_, ?_⟩
  · have hs : Summable fun n : ℤ => mphi_rowP |(1 / 2 - n) * v| :=
      Complex.summable_ofReal.mp h.summable
    exact hs.tsum_pos (fun n => (mphi_rowP_pos (abs_pos.mpr (hne n))).le) 0
      (mphi_rowP_pos (abs_pos.mpr (hne 0)))
  · rw [Complex.ofReal_tsum]
    exact h.tsum_eq.symm

/-- The lattice transformation `w ↦ -1/w` (the internals of `eq14_12`):
`e₁(-1/w) = w² e₂(w)`, `e₂(-1/w) = w² e₁(w)`, `e₃(-1/w) = w² e₃(w)`. -/
theorem mphi_weierstrassE_neg_inv {w : ℂ} (hw : 0 < w.im) :
    weierstrassE (-1 / w) 0 = w ^ 2 * weierstrassE w 1 ∧
    weierstrassE (-1 / w) 1 = w ^ 2 * weierstrassE w 0 ∧
    weierstrassE (-1 / w) 2 = w ^ 2 * weierstrassE w 2 := by
  have hne : w ≠ 0 := fun h => by rw [h, Complex.zero_im] at hw; exact lt_irrefl 0 hw
  have hw' : 0 < (-1 / w).im := by
    have hn : 0 < Complex.normSq w := Complex.normSq_pos.2 hne
    have h : (-1 / w).im = w.im / Complex.normSq w := by
      rw [Complex.div_im]
      simp only [Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, neg_zero,
        zero_mul, zero_div, zero_sub]
      ring
    rw [h]
    exact div_pos hw hn
  have hmem : ∀ x : ℂ, w * x ∈ (periodPairOf w hw).lattice ↔
      x ∈ (periodPairOf (-1 / w) hw').lattice := by
    intro x
    simp only [PeriodPair.mem_lattice, periodPairOf]
    constructor
    · rintro ⟨m, n, e⟩
      refine ⟨n, -m, ?_⟩
      field_simp
      push_cast
      linear_combination e
    · rintro ⟨m, n, rfl⟩
      refine ⟨-n, m, ?_⟩
      field_simp
      push_cast
      ring
  have hscale : ∀ z : ℂ, (periodPairOf (-1 / w) hw').weierstrassP z =
      w ^ 2 * (periodPairOf w hw).weierstrassP (w * z) := by
    intro z
    rw [weierstrassP_mul_of_mem_lattice_iff _ _ hne hmem z, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hne, one_pow, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [weierstrassE_zero_eq hw', weierstrassE_one_eq hw, hscale,
      show w * (1 / 2) = w / 2 by ring]
  · rw [weierstrassE_one_eq hw', weierstrassE_zero_eq hw, hscale,
      show w * (-1 / w / 2) = -(1 / 2) by field_simp, PeriodPair.weierstrassP_neg]
  · rw [weierstrassE_two_eq hw', weierstrassE_two_eq hw, hscale,
      show w * ((1 + -1 / w) / 2) = (1 + w) / 2 - 1 by field_simp; ring,
      periodPairOf_weierstrassP_sub_one]

/-- `e₁(iv) - e₃(iv)` is a positive real number (via `w ↦ -1/w` and the previous lemma). -/
theorem mphi_weierstrassE_zero_sub_two_iv {v : ℝ} (hv : 0 < v) :
    ∃ s : ℝ, 0 < s ∧
      weierstrassE ((v : ℂ) * I) 0 - weierstrassE ((v : ℂ) * I) 2 = s := by
  obtain ⟨r, hr, hE⟩ := mphi_weierstrassE_two_sub_one_iv (inv_pos.2 hv)
  have hw : 0 < (((v⁻¹ : ℝ) : ℂ) * I).im := by simpa using hv
  obtain ⟨h0, -, h2⟩ := mphi_weierstrassE_neg_inv hw
  have hvI : -1 / (((v⁻¹ : ℝ) : ℂ) * I) = (v : ℂ) * I := by
    have : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
    push_cast
    field_simp
    rw [I_sq]
  rw [hvI] at h0 h2
  refine ⟨v⁻¹ ^ 2 * r, by positivity, ?_⟩
  rw [h0, h2, ← mul_sub, show weierstrassE (((v⁻¹ : ℝ) : ℂ) * I) 1 -
    weierstrassE (((v⁻¹ : ℝ) : ℂ) * I) 2 = -(r : ℂ) by rw [← hE]; ring]
  push_cast
  rw [mul_pow, I_sq]
  ring

/-- (14.13)–(14.15): `q(iv) < 0`, `q(1 + iv) > 1` and `0 < q(1/(1 - iv)) < 1`, all real. -/
theorem eq14_13_15 {v : ℝ} (hv : 0 < v) :
    (modularPhi (v * I)).im = 0 ∧ (modularPhi (v * I)).re < 0 ∧
      (modularPhi (1 + v * I)).im = 0 ∧ 1 < (modularPhi (1 + v * I)).re ∧
      (modularPhi (1 / (1 - v * I))).im = 0 ∧ 0 < (modularPhi (1 / (1 - v * I))).re ∧
      (modularPhi (1 / (1 - v * I))).re < 1 := by
  obtain ⟨r, hr, hE21⟩ := mphi_weierstrassE_two_sub_one_iv hv
  obtain ⟨s, hs, hE02⟩ := mphi_weierstrassE_zero_sub_two_iv hv
  have hw : 0 < ((v : ℂ) * I).im := by simpa using hv
  -- `φ(iv) = -s/r`
  have hphi : modularPhi ((v : ℂ) * I) = ((-s / r : ℝ) : ℂ) := by
    rw [modularPhi, hE21, show weierstrassE ((v : ℂ) * I) 2 -
      weierstrassE ((v : ℂ) * I) 0 = -(s : ℂ) by rw [← hE02]; ring]
    push_cast
    ring
  -- `φ(1 + iv) = (s + r)/r`
  have hphi1 : modularPhi (1 + (v : ℂ) * I) = (((s + r) / r : ℝ) : ℂ) := by
    obtain ⟨a0, a1, a2⟩ := mphi_weierstrassE_add_one hw
    rw [add_comm, modularPhi, a0, a1, a2]
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [show weierstrassE ((v : ℂ) * I) 1 - weierstrassE ((v : ℂ) * I) 0 =
        -((s : ℂ) + r) by rw [← hE02, ← hE21]; ring,
      show weierstrassE ((v : ℂ) * I) 1 - weierstrassE ((v : ℂ) * I) 2 =
        -(r : ℂ) by rw [← hE21]; ring]
    push_cast
    field_simp
  -- `φ(1/(1 - iv)) = 1/φ(1 + iv)`
  have hw2 : 0 < (-1 + (v : ℂ) * I).im := by simpa using hv
  have hphi2 : modularPhi (1 / (1 - (v : ℂ) * I)) = ((r / (s + r) : ℝ) : ℂ) := by
    have h12 := eq14_12 hw2
    have h4 := eq14_4 hw2
    rw [show -1 + (v : ℂ) * I + 2 = 1 + (v : ℂ) * I by ring, hphi1] at h4
    rw [show (1 : ℂ) / (1 - (v : ℂ) * I) = -1 / (-1 + (v : ℂ) * I) by
      rw [show (-1 : ℂ) + (v : ℂ) * I = -(1 - (v : ℂ) * I) by ring, div_neg, neg_div, neg_neg],
      h12, ← h4]
    have : (s + r : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have hsr : 0 < s + r := by positivity
  refine ⟨by rw [hphi, Complex.ofReal_im], ?_, by rw [hphi1, Complex.ofReal_im], ?_,
    by rw [hphi2, Complex.ofReal_im], ?_, ?_⟩
  · rw [hphi, Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (by linarith) hr
  · rw [hphi1, Complex.ofReal_re, lt_div_iff₀ hr]
    linarith
  · rw [hphi2, Complex.ofReal_re]
    positivity
  · rw [hphi2, Complex.ofReal_re, div_lt_one hsr]
    linarith

/-! ### (14.27) — helpers -/

/-! ### Piece L: Landen's identity for `μ` -/

theorem em_mu_landen {u : ℝ} (hu₀ : 0 < u) (hu₁ : u < 1) :
    grotzschMu ((1 - u) / (1 + u)) = 2 * grotzschMu (Real.sqrt (1 - u ^ 2)) := by
  obtain ⟨hL1, hL2⟩ := e57_landen_param hu₀ hu₁
  have hv₀ : 0 < (1 - u) / (1 + u) := div_pos (by linarith) (by linarith)
  have hv₁ : (1 - u) / (1 + u) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hs₀ : 0 < Real.sqrt (1 - u ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hs₁ : Real.sqrt (1 - u ^ 2) < 1 := by
    rw [Real.sqrt_lt' one_pos]; nlinarith
  rw [gm_grotzschMu_eq hv₀ hv₁, gm_grotzschMu_eq hs₀ hs₁, e57_sideA_eq hv₀ hv₁,
    e57_sideA_eq hs₀ hs₁, hL2]
  have hsq : Real.sqrt (1 - Real.sqrt (1 - u ^ 2) ^ 2) = u := by
    rw [Real.sq_sqrt (by nlinarith), sub_sub_cancel, Real.sqrt_sq hu₀.le]
  rw [hsq, e57_landen hu₀ hu₁]
  have hbs : scSideB (Real.sqrt (1 - u ^ 2)) =
      (1 + (1 - u) / (1 + u)) * scSideB ((1 - u) / (1 + u)) := by
    rw [← hL1, e57_landen hv₀ hv₁]
  rw [hbs]
  have hbv := (scSide_pos hv₀ hv₁).2
  have hbu := (scSide_pos hu₀ hu₁).2
  have h1u : (0 : ℝ) < 1 + u := by linarith
  field_simp
  ring

/-! ### Piece B: elementary bounds on the Schwarz–Christoffel sides -/

/-- FTC for a nonnegative derivative: the derivative is interval integrable and integrates to the
increment of the primitive. -/
theorem emB_ftc_nonneg {F f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hcont : ContinuousOn F (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x) (hpos : ∀ x ∈ Ioo a b, 0 ≤ f x) :
    IntervalIntegrable f volume a b ∧ ∫ x in a..b, f x = F b - F a := by
  have hint : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      (intervalIntegral.integrableOn_deriv_of_nonneg hcont hderiv hpos)
  exact ⟨hint, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint⟩

/-- For `0 ≤ u` and `0 < v ≤ 1`: `1/√u ≤ 1/√(u v)` (both sides vanish when `u = 0`). -/
theorem emB_inv_sqrt_le_mul {u v : ℝ} (hu : 0 ≤ u) (hv₀ : 0 < v) (hv₁ : v ≤ 1) :
    1 / Real.sqrt u ≤ 1 / Real.sqrt (u * v) := by
  rcases hu.eq_or_lt with h | h
  · subst h; simp
  · exact one_div_le_one_div_of_le (Real.sqrt_pos.2 (mul_pos h hv₀))
      (Real.sqrt_le_sqrt (mul_le_of_le_one_right h.le hv₁))

/-- `∫₁^c dx/√(x²-1) = arcosh c` (with interval integrability). -/
theorem emB_integral_arcosh {c : ℝ} (hc : 1 ≤ c) :
    IntervalIntegrable (fun x : ℝ => 1 / Real.sqrt (x ^ 2 - 1)) volume 1 c ∧
      ∫ x in (1 : ℝ)..c, 1 / Real.sqrt (x ^ 2 - 1) = Real.arcosh c := by
  obtain ⟨h1, h2⟩ := emB_ftc_nonneg (F := Real.arcosh)
    (f := fun x : ℝ => 1 / Real.sqrt (x ^ 2 - 1)) hc
    (Real.continuousOn_arcosh.mono Icc_subset_Ici_self)
    (fun x hx => by simpa [one_div] using Real.hasDerivAt_arcosh (show x ∈ Ioi 1 from hx.1))
    (fun x _ => by positivity)
  exact ⟨h1, by rw [h2, Real.arcosh_zero, sub_zero]⟩

theorem em_sideA_ge {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) : Real.log (1 / k) ≤ scSideA k := by
  have h1k : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  have hA : IntervalIntegrable
      (fun x : ℝ => 1 / Real.sqrt ((x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2))) volume 1 (1 / k) :=
    intervalIntegral.intervalIntegrable_of_integral_ne_zero
      (show (∫ x in (1 : ℝ)..(1 / k), 1 / Real.sqrt ((x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2))) ≠ 0 from
        (scSide_pos hk₀ hk₁).1.ne')
  obtain ⟨hh, hcosh⟩ := emB_integral_arcosh h1k.le
  have hle : Real.arcosh (1 / k) ≤ scSideA k := by
    rw [← hcosh]
    unfold scSideA
    refine intervalIntegral.integral_mono_on_of_le_Ioo h1k.le hh hA fun x hx => ?_
    have hx0 : 0 < x := by linarith [hx.1]
    have hkx : k * x < 1 := by
      have := hx.2
      rwa [lt_div_iff₀ hk₀, mul_comm] at this
    have hkx0 : 0 < k * x := mul_pos hk₀ hx0
    refine emB_inv_sqrt_le_mul (by nlinarith [hx.1]) (by nlinarith) (by nlinarith)
  refine le_trans ?_ hle
  unfold Real.arcosh
  exact Real.log_le_log (by positivity) (le_add_of_nonneg_right (Real.sqrt_nonneg _))

/-- `∫₋₁¹ dx/√(1-x²) = π` (with interval integrability). -/
theorem emB_integral_arcsin :
    IntervalIntegrable (fun x : ℝ => 1 / Real.sqrt (1 - x ^ 2)) volume (-1) 1 ∧
      ∫ x in (-1 : ℝ)..1, 1 / Real.sqrt (1 - x ^ 2) = π := by
  obtain ⟨h1, h2⟩ := emB_ftc_nonneg (F := Real.arcsin)
    (f := fun x : ℝ => 1 / Real.sqrt (1 - x ^ 2)) (by norm_num)
    Real.continuous_arcsin.continuousOn
    (fun x hx => Real.hasDerivAt_arcsin hx.1.ne' hx.2.ne) (fun x _ => by positivity)
  refine ⟨h1, ?_⟩
  rw [h2, Real.arcsin_one, Real.arcsin_neg_one]
  ring

/-- The integrand of `scSideB` is interval integrable on `[-1, 1]`. -/
theorem emB_sideB_integrable {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    IntervalIntegrable (fun x : ℝ => 1 / Real.sqrt ((1 - x ^ 2) * (1 - k ^ 2 * x ^ 2)))
      volume (-1) 1 :=
  intervalIntegral.intervalIntegrable_of_integral_ne_zero
    (show (∫ x in (-1 : ℝ)..1, 1 / Real.sqrt ((1 - x ^ 2) * (1 - k ^ 2 * x ^ 2))) ≠ 0 from
      (scSide_pos hk₀ hk₁).2.ne')

theorem em_sideB_ge {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) : π ≤ scSideB k := by
  obtain ⟨hg, hπ⟩ := emB_integral_arcsin
  rw [← hπ]
  unfold scSideB
  refine intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hg
    (emB_sideB_integrable hk₀ hk₁) fun x hx => ?_
  have hx1 := hx.1
  have hx2 := hx.2
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hxx : x ^ 2 < 1 := by nlinarith
  exact emB_inv_sqrt_le_mul (by nlinarith) (by nlinarith [sq_nonneg x, sq_nonneg k])
    (by nlinarith [sq_nonneg x, sq_nonneg k])

/-- For `0 ≤ u` and `0 < c ≤ v`: `1/√(u v) ≤ (1/√c)·(1/√u)`. -/
theorem emB_inv_sqrt_mul_le {u v c : ℝ} (hu : 0 ≤ u) (hc : 0 < c) (hcv : c ≤ v) :
    1 / Real.sqrt (u * v) ≤ 1 / Real.sqrt c * (1 / Real.sqrt u) := by
  rcases hu.eq_or_lt with h | h
  · subst h; simp
  · rw [Real.sqrt_mul h.le, one_div_mul_one_div, mul_comm (Real.sqrt c)]
    exact one_div_le_one_div_of_le (mul_pos (Real.sqrt_pos.2 h) (Real.sqrt_pos.2 hc))
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcv) (Real.sqrt_nonneg _))

theorem em_sideB_le {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    scSideB k ≤ π / Real.sqrt (1 - k ^ 2) := by
  obtain ⟨hg, hπ⟩ := emB_integral_arcsin
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hle : scSideB k ≤ ∫ x in (-1 : ℝ)..1,
      1 / Real.sqrt (1 - k ^ 2) * (1 / Real.sqrt (1 - x ^ 2)) := by
    unfold scSideB
    refine intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
      (emB_sideB_integrable hk₀ hk₁) (hg.const_mul _) fun x hx => ?_
    have hx1 := hx.1
    have hx2 := hx.2
    have hxx : x ^ 2 < 1 := by nlinarith
    exact emB_inv_sqrt_mul_le (by nlinarith) (by linarith)
      (by nlinarith [sq_nonneg x, sq_nonneg k, mul_le_mul_of_nonneg_left hxx.le (sq_nonneg k)])
  rw [intervalIntegral.integral_const_mul, hπ] at hle
  refine hle.trans (le_of_eq ?_)
  ring

/-! ### Piece C: the upper bound on `a` -/

/-- Pointwise invariance of the density `dx/√((x²-1)(1-k²x²))` under the involution `x ↦ 1/(kx)`. -/
theorem emC_pointwise {k x : ℝ} (hk₀ : 0 < k) (hx : 0 < x)
    (hP : 0 < (x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2)) :
    |-(1 / (k * x ^ 2))| * (1 / Real.sqrt (((1 / (k * x)) ^ 2 - 1) * (1 - k ^ 2 * (1 / (k * x)) ^ 2))) =
      1 / Real.sqrt ((x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2)) := by
  have hid : ((1 / (k * x)) ^ 2 - 1) * (1 - k ^ 2 * (1 / (k * x)) ^ 2) =
      ((x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2)) * (1 / (k * x ^ 2)) ^ 2 := by
    field_simp
  have ha : 0 < 1 / (k * x ^ 2) := by positivity
  have hs : 0 < Real.sqrt ((x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2)) := Real.sqrt_pos.2 hP
  rw [hid, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq ha.le, abs_neg, abs_of_pos ha]
  field_simp

/-- The involution `x ↦ 1/(kx)` maps `(1, c)` injectively onto `(c, 1/k)` when `k c² = 1`. -/
theorem emC_image {k c : ℝ} (hk₀ : 0 < k) (hc : 0 < c) (hkc : k * c ^ 2 = 1) :
    (fun x : ℝ => 1 / (k * x)) '' Ioo 1 c = Ioo c (1 / k) ∧
      InjOn (fun x : ℝ => 1 / (k * x)) (Ioo 1 c) := by
  refine ⟨Subset.antisymm ?_ ?_, ?_⟩
  · rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
    have hx0 : 0 < x := by linarith
    have hkx : 0 < k * x := mul_pos hk₀ hx0
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hkx]
      nlinarith [mul_lt_mul_of_pos_left hx2 (mul_pos hk₀ hc)]
    · rw [div_lt_div_iff₀ hkx hk₀]
      nlinarith
  · rintro y ⟨hy1, hy2⟩
    have hy0 : 0 < y := by linarith
    have hky : 0 < k * y := mul_pos hk₀ hy0
    have hky1 : k * y < 1 := by
      have := (lt_div_iff₀ hk₀).1 hy2; linarith
    refine ⟨1 / (k * y), ⟨?_, ?_⟩, ?_⟩
    · rw [lt_div_iff₀ hky]; linarith
    · rw [div_lt_iff₀ hky]
      nlinarith [mul_lt_mul_of_pos_left hy1 (mul_pos hk₀ hc)]
    · field_simp
  · intro x hx y hy hxy
    have hx0 : 0 < x := by linarith [hx.1]
    have hy0 : 0 < y := by linarith [hy.1]
    simp only at hxy
    rw [div_eq_div_iff (by positivity) (by positivity)] at hxy
    nlinarith

/-- `∫₁^c dx/√(x²-1) = log(c + √(c²-1))` (and the integrand is integrable), for `1 ≤ c`. -/
theorem emC_arcosh {c : ℝ} (hc : 1 ≤ c) :
    IntervalIntegrable (fun x : ℝ => 1 / Real.sqrt (x ^ 2 - 1)) volume 1 c ∧
      ∫ x in (1 : ℝ)..c, 1 / Real.sqrt (x ^ 2 - 1) = Real.log (c + Real.sqrt (c ^ 2 - 1)) := by
  set F : ℝ → ℝ := fun x => Real.log (x + Real.sqrt (x ^ 2 - 1)) with hF
  have hpos : ∀ x ∈ Icc (1 : ℝ) c, 0 < x + Real.sqrt (x ^ 2 - 1) := fun x hx => by
    have := Real.sqrt_nonneg (x ^ 2 - 1); linarith [hx.1]
  have hcont : ContinuousOn F (Icc 1 c) := by
    refine ContinuousOn.log ?_ fun x hx => (hpos x hx).ne'
    exact (continuous_id.add (by fun_prop)).continuousOn
  have hder : ∀ x ∈ Ioo (1 : ℝ) c, HasDerivAt F (1 / Real.sqrt (x ^ 2 - 1)) x := by
    intro x hx
    have hx1 : 0 < x ^ 2 - 1 := by nlinarith [hx.1]
    have hs : 0 < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.2 hx1
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2 - 1) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).sub_const 1
    have h2 : HasDerivAt (fun x : ℝ => Real.sqrt (x ^ 2 - 1))
        (2 * x / (2 * Real.sqrt (x ^ 2 - 1))) x := h1.sqrt hx1.ne'
    have h3 : HasDerivAt (fun x : ℝ => x + Real.sqrt (x ^ 2 - 1))
        (1 + 2 * x / (2 * Real.sqrt (x ^ 2 - 1))) x := (hasDerivAt_id' x).add h2
    have hp : 0 < x + Real.sqrt (x ^ 2 - 1) := by linarith [hx.1]
    have h4 : HasDerivAt F ((1 + 2 * x / (2 * Real.sqrt (x ^ 2 - 1))) /
        (x + Real.sqrt (x ^ 2 - 1))) x := h3.log hp.ne'
    refine h4.congr_deriv ?_
    field_simp
    ring
  have hnn : ∀ x ∈ Ioo (1 : ℝ) c, 0 ≤ 1 / Real.sqrt (x ^ 2 - 1) := fun x _ => by positivity
  have hint : IntervalIntegrable (fun x : ℝ => 1 / Real.sqrt (x ^ 2 - 1)) volume 1 c :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hc).2
      (intervalIntegral.integrableOn_deriv_of_nonneg hcont hder hnn)
  refine ⟨hint, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hc hcont hder hint]
  simp [hF]

theorem em_sideA_le {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    scSideA k ≤ Real.log (4 / k) / Real.sqrt (1 - k) := by
  set f : ℝ → ℝ := fun x => 1 / Real.sqrt ((x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2)) with hf
  set c : ℝ := Real.sqrt (1 / k) with hcdef
  have hk1 : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc2 : c ^ 2 = 1 / k := Real.sq_sqrt (by positivity)
  have hkc : k * c ^ 2 = 1 := by rw [hc2]; field_simp
  have hc1 : 1 < c := by
    rw [hcdef, Real.lt_sqrt zero_le_one]; simpa using hk1
  have hck : c < 1 / k := by rw [← hc2]; nlinarith
  -- integrability of `f` on `[1, 1/k]`
  have hA : scSideA k = ∫ x in (1 : ℝ)..(1 / k), f x := rfl
  have hint : IntervalIntegrable f volume 1 (1 / k) :=
    intervalIntegral.intervalIntegrable_of_integral_ne_zero (hA ▸ (scSide_pos hk₀ hk₁).1.ne')
  have h1 : IntervalIntegrable f volume 1 c :=
    hint.mono_set (uIcc_subset_uIcc left_mem_uIcc (by rw [uIcc_of_le hk1.le]; exact ⟨hc1.le, hck.le⟩))
  have h2 : IntervalIntegrable f volume c (1 / k) :=
    hint.mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le hk1.le]; exact ⟨hc1.le, hck.le⟩) right_mem_uIcc)
  -- positivity of the radicand on `(1, c)`
  have hP : ∀ x ∈ Ioo (1 : ℝ) c, 0 < (x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2) := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have : k ^ 2 * x ^ 2 < k ^ 2 * c ^ 2 := by
      have := pow_lt_pow_left₀ hx.2 hx0.le two_ne_zero
      nlinarith [pow_pos hk₀ 2]
    have hkk : k ^ 2 * c ^ 2 = k := by rw [pow_two k, mul_assoc, hkc, mul_one]
    apply mul_pos <;> nlinarith [hx.1]
  -- the second half equals the first half
  have hsym : ∫ x in c..(1 / k), f x = ∫ x in (1 : ℝ)..c, f x := by
    obtain ⟨himg, hinj⟩ := emC_image hk₀ hc0 hkc
    have hder : ∀ x ∈ Ioo (1 : ℝ) c, HasDerivWithinAt (fun x : ℝ => 1 / (k * x))
        (-(1 / (k * x ^ 2))) (Ioo 1 c) x := by
      intro x hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      have h := ((hasDerivAt_id x).const_mul k).inv (by simp only [id]; exact mul_ne_zero hk₀.ne' hx0)
      refine HasDerivAt.hasDerivWithinAt ?_
      convert h using 1
      · funext y; simp [one_div]
      · simp only [id]; field_simp
    have hcv := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hder hinj f
    rw [himg] at hcv
    rw [intervalIntegral.integral_of_le hck.le, integral_Ioc_eq_integral_Ioo, hcv,
      intervalIntegral.integral_of_le hc1.le, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    simp only [smul_eq_mul, hf]
    exact emC_pointwise hk₀ (by linarith [hx.1]) (hP x hx)
  -- the pointwise bound on `(1, c)`
  obtain ⟨hgint, hgval⟩ := emC_arcosh hc1.le
  have hs1k : 0 < Real.sqrt (1 - k) := Real.sqrt_pos.2 (by linarith)
  have hbound : ∫ x in (1 : ℝ)..c, f x ≤
      ∫ x in (1 : ℝ)..c, (Real.sqrt (1 - k))⁻¹ * (1 / Real.sqrt (x ^ 2 - 1)) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hc1.le h1 (hgint.const_mul _) ?_
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hx1 : 0 < x ^ 2 - 1 := by nlinarith [hx.1]
    have hkk : k ^ 2 * x ^ 2 ≤ k := by
      have : x ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hx0.le hx.2.le 2
      have hkk : k ^ 2 * c ^ 2 = k := by rw [pow_two k, mul_assoc, hkc, mul_one]
      nlinarith [pow_pos hk₀ 2]
    have hle : (x ^ 2 - 1) * (1 - k) ≤ (x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hx1.le
    have hsq : Real.sqrt ((x ^ 2 - 1) * (1 - k)) ≤ Real.sqrt ((x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2)) :=
      Real.sqrt_le_sqrt hle
    rw [Real.sqrt_mul hx1.le] at hsq
    have hsx : 0 < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.2 hx1
    simp only [hf]
    rw [inv_mul_eq_div, div_div, one_div_le_one_div (lt_of_lt_of_le (by positivity) hsq)
      (by positivity)]
    linarith [hsq]
  rw [intervalIntegral.integral_const_mul, hgval] at hbound
  -- `log(c + √(c²-1)) ≤ log(2c)`
  have hlog : Real.log (c + Real.sqrt (c ^ 2 - 1)) ≤ Real.log (2 * c) := by
    have hs : Real.sqrt (c ^ 2 - 1) ≤ c := by
      rw [Real.sqrt_le_left hc0.le]; linarith
    have hp : 0 < c + Real.sqrt (c ^ 2 - 1) := by
      have := Real.sqrt_nonneg (c ^ 2 - 1); linarith
    exact Real.log_le_log hp (by linarith)
  have h4k : Real.log (4 / k) = 2 * Real.log (2 * c) := by
    have hlp := Real.log_pow (2 * c) 2
    push_cast at hlp
    rw [← hlp, mul_pow, hc2]
    congr 1
    field_simp
    norm_num
  rw [hA, ← intervalIntegral.integral_add_adjacent_intervals h1 h2, hsym, h4k]
  have : (Real.sqrt (1 - k))⁻¹ * Real.log (c + Real.sqrt (c ^ 2 - 1)) ≤
      (Real.sqrt (1 - k))⁻¹ * Real.log (2 * c) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  rw [div_eq_inv_mul]
  linarith

/-! ### Piece D: a priori bounds and the iteration -/

theorem em_upper_apriori : ∃ C : ℝ, ∀ r : ℝ, 0 < r → r < 1 → grotzschMu r ≤ Real.log (4 / r) + C := by
  refine ⟨max 8 (grotzschMu (1 / 2)), fun r hr₀ hr₁ => ?_⟩
  have hL : 0 ≤ Real.log (4 / r) := Real.log_nonneg (by rw [le_div_iff₀ hr₀]; linarith)
  rcases le_or_gt r (1 / 2) with hr | hr
  · have ha := (scSide_pos hr₀ hr₁).1
    have hb := (scSide_pos hr₀ hr₁).2
    have hμa : grotzschMu r ≤ scSideA r := by
      rw [gm_grotzschMu_eq hr₀ hr₁, div_le_iff₀ hb]
      nlinarith [mul_le_mul_of_nonneg_left (em_sideB_ge hr₀ hr₁) ha.le]
    have hA := em_sideA_le hr₀ hr₁
    set q := Real.sqrt (1 - r) with hq_def
    have hq0 : 0 < q := Real.sqrt_pos.2 (by linarith)
    have hq2 : q ^ 2 = 1 - r := Real.sq_sqrt (by linarith)
    have hq1 : q ≤ 1 := by nlinarith
    have hqh : 1 / 2 ≤ q := by nlinarith
    have hLr : Real.log (4 / r) * r ≤ 4 := by
      have h1 := Real.log_le_sub_one_of_pos (show 0 < 4 / r by positivity)
      have h2 : (4 / r - 1) * r = 4 - r := by field_simp
      nlinarith [mul_le_mul_of_nonneg_right h1 hr₀.le]
    have hbound : Real.log (4 / r) / q ≤ Real.log (4 / r) + 8 := by
      rw [div_le_iff₀ hq0]
      have h1q : 1 - q ≤ r := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h1q hL]
    have := le_max_left 8 (grotzschMu (1 / 2))
    linarith
  · have hmono : grotzschMu r ≤ grotzschMu (1 / 2) :=
      grotzschMu_strictAntiOn.antitoneOn ⟨by norm_num, by norm_num⟩ ⟨hr₀, hr₁⟩ hr.le
    have := le_max_right 8 (grotzschMu (1 / 2))
    linarith

theorem em_lower_apriori :
    ∃ C : ℝ, ∀ r : ℝ, 0 < r → r < 1 → Real.log (4 * Real.sqrt (1 - r ^ 2) / r) - C ≤ grotzschMu r := by
  refine ⟨Real.log 4 + 1, fun r hr₀ hr₁ => ?_⟩
  have ha := (scSide_pos hr₀ hr₁).1
  have hb := (scSide_pos hr₀ hr₁).2
  set q := Real.sqrt (1 - r ^ 2) with hq_def
  have hr2 : 0 < 1 - r ^ 2 := by nlinarith
  have hq0 : 0 < q := Real.sqrt_pos.2 hr2
  have hq2 : q ^ 2 = 1 - r ^ 2 := Real.sq_sqrt hr2.le
  have hq1 : q ≤ 1 := by nlinarith
  have hA := em_sideA_ge hr₀ hr₁
  have hB := em_sideB_le hr₀ hr₁
  set ℓ := Real.log (1 / r) with hℓ_def
  have hℓ : 0 ≤ ℓ := Real.log_nonneg (by rw [le_div_iff₀ hr₀]; linarith)
  have hbq : scSideB r * q ≤ π := by rwa [le_div_iff₀ hq0] at hB
  have hμ : scSideA r * q ≤ grotzschMu r := by
    rw [gm_grotzschMu_eq hr₀ hr₁, le_div_iff₀ hb]
    nlinarith [mul_le_mul_of_nonneg_left hbq ha.le]
  have hℓr : ℓ * r ^ 2 ≤ 1 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 / r by positivity)
    have h2 : (1 / r - 1) * r ^ 2 = r - r ^ 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg r)]
  have h1q : 1 - q ≤ r ^ 2 := by nlinarith
  have hlog : Real.log (4 * q / r) ≤ Real.log 4 + ℓ := by
    rw [hℓ_def, ← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (by linarith) hr₀.le
  nlinarith [mul_le_mul_of_nonneg_right hA hq0.le, mul_le_mul_of_nonneg_left h1q hℓ]

/-- Landen step for the iteration: every `s ∈ (0,1)` is the Landen image `2√ρ/(1+ρ)` of some `ρ ∈ (0,1)`,
with `μ(ρ) = 2μ(s)`, `ln(4/ρ) ≤ 2 ln(4/s)` and `2 ln(4√(1-s²)/s) ≤ ln(4√(1-ρ²)/ρ)`. -/
theorem emD_landen_step {s : ℝ} (hs₀ : 0 < s) (hs₁ : s < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ grotzschMu ρ = 2 * grotzschMu s ∧
      Real.log (4 / ρ) ≤ 2 * Real.log (4 / s) ∧
      2 * Real.log (4 * Real.sqrt (1 - s ^ 2) / s) ≤ Real.log (4 * Real.sqrt (1 - ρ ^ 2) / ρ) := by
  set u := Real.sqrt (1 - s ^ 2) with hu_def
  have hs2 : 0 < 1 - s ^ 2 := by nlinarith
  have hu₀ : 0 < u := Real.sqrt_pos.2 hs2
  have hu₁ : u < 1 := by rw [hu_def, Real.sqrt_lt' one_pos]; nlinarith
  have hu2 : u ^ 2 = 1 - s ^ 2 := Real.sq_sqrt hs2.le
  have hsu : s ^ 2 = 1 - u ^ 2 := by linarith
  have hsq : Real.sqrt (1 - u ^ 2) = s := by rw [← hsu, Real.sqrt_sq hs₀.le]
  have h1u : (0 : ℝ) < 1 + u := by linarith
  have h1u' : (0 : ℝ) < 1 - u := by linarith
  refine ⟨(1 - u) / (1 + u), div_pos h1u' h1u, (div_lt_one h1u).2 (by linarith), ?_, ?_, ?_⟩
  · rw [em_mu_landen hu₀ hu₁, hsq]
  · have e1 : 4 / ((1 - u) / (1 + u)) = 4 * (1 + u) / (1 - u) := by field_simp
    rw [e1, show (2 : ℝ) * Real.log (4 / s) = Real.log ((4 / s) ^ 2) by rw [Real.log_pow]; norm_num]
    apply Real.log_le_log (by positivity)
    rw [div_pow, hsu, div_le_div_iff₀ h1u' (by nlinarith)]
    nlinarith [mul_le_mul_of_nonneg_left (show (1 + u) ^ 2 ≤ 4 by nlinarith) h1u'.le]
  · rw [(e57_landen_param hu₀ hu₁).2]
    set t := Real.sqrt u with ht_def
    have ht₀ : 0 < t := Real.sqrt_pos.2 hu₀
    have ht2 : t ^ 2 = u := Real.sq_sqrt hu₀.le
    have ht₁ : t < 1 := by nlinarith
    have e1 : 4 * (2 * t / (1 + u)) / ((1 - u) / (1 + u)) = 8 * t / (1 - u) := by
      field_simp; ring
    rw [e1, show (2 : ℝ) * Real.log (4 * u / s) = Real.log ((4 * u / s) ^ 2) by
      rw [Real.log_pow]; norm_num]
    apply Real.log_le_log (by positivity)
    rw [div_pow, hsu, div_le_div_iff₀ (by nlinarith) h1u']
    have h3 : 2 * t ^ 3 ≤ t ^ 2 + 1 := by
      nlinarith [mul_le_mul_of_nonneg_left ht₁.le (sq_nonneg t)]
    have key : 2 * u ^ 2 ≤ t * (1 + u) := by
      rw [← ht2]; nlinarith [mul_le_mul_of_nonneg_left h3 ht₀.le]
    nlinarith [mul_le_mul_of_nonneg_right key h1u'.le]

/-- The upper half of (14.27). -/
theorem em_upper {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) : grotzschMu r ≤ Real.log (4 / r) := by
  obtain ⟨C, hC⟩ := em_upper_apriori
  have key : ∀ n : ℕ, ∀ r : ℝ, 0 < r → r < 1 →
      grotzschMu r - Real.log (4 / r) ≤ C * (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => intro r h0 h1; rw [pow_zero, mul_one]; linarith [hC r h0 h1]
    | succ n ih =>
      intro s h0 h1
      obtain ⟨ρ, hρ0, hρ1, hμ, hl, -⟩ := emD_landen_step h0 h1
      have := ih ρ hρ0 hρ1
      rw [pow_succ]
      linarith
  have ht : Tendsto (fun n : ℕ => C * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul C
  have := ge_of_tendsto' ht (fun n => key n r hr₀ hr₁)
  linarith

/-- The lower half of (14.27). -/
theorem em_lower {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    Real.log (4 * Real.sqrt (1 - r ^ 2) / r) ≤ grotzschMu r := by
  obtain ⟨C, hC⟩ := em_lower_apriori
  have key : ∀ n : ℕ, ∀ r : ℝ, 0 < r → r < 1 →
      -(C * (1 / 2 : ℝ) ^ n) ≤ grotzschMu r - Real.log (4 * Real.sqrt (1 - r ^ 2) / r) := by
    intro n
    induction n with
    | zero => intro r h0 h1; rw [pow_zero, mul_one]; linarith [hC r h0 h1]
    | succ n ih =>
      intro s h0 h1
      obtain ⟨ρ, hρ0, hρ1, hμ, -, hl⟩ := emD_landen_step h0 h1
      have := ih ρ hρ0 hρ1
      rw [pow_succ]
      linarith
  have ht : Tendsto (fun n : ℕ => -(C * (1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul C).neg
  have := le_of_tendsto' ht (fun n => key n r hr₀ hr₁)
  linarith

/-- For `ρ > 0` the point `r = √(1/(1+ρ))` of (5.18) lies in `(0, 1)`, and `(4/r)² = 16(ρ + 1)`,
`(4√(1 - r²)/r)² = 16ρ`. -/
theorem lam14_sqrt_facts {ρ : ℝ} (hρ : 0 < ρ) :
    0 < Real.sqrt (1 / (1 + ρ)) ∧ Real.sqrt (1 / (1 + ρ)) < 1 ∧
      (4 / Real.sqrt (1 / (1 + ρ))) ^ 2 = 16 * (ρ + 1) ∧
      (4 * Real.sqrt (1 - Real.sqrt (1 / (1 + ρ)) ^ 2) / Real.sqrt (1 / (1 + ρ))) ^ 2 = 16 * ρ := by
  have h1 : (0 : ℝ) < 1 + ρ := by linarith
  have hq0 : (0 : ℝ) < 1 / (1 + ρ) := by positivity
  have hq1 : 1 / (1 + ρ) < 1 := (div_lt_one h1).2 (by linarith)
  have hr2 : Real.sqrt (1 / (1 + ρ)) ^ 2 = 1 / (1 + ρ) := Real.sq_sqrt hq0.le
  have hs0 : 0 ≤ 1 - Real.sqrt (1 / (1 + ρ)) ^ 2 := by rw [hr2]; linarith
  refine ⟨Real.sqrt_pos.2 hq0, (Real.sqrt_lt' one_pos).2 (by rwa [one_pow]), ?_, ?_⟩
  · rw [div_pow, hr2]
    field_simp
    ring
  · rw [div_pow, mul_pow, Real.sq_sqrt hs0, hr2]
    field_simp
    ring

/-- The bounds (14.26), `ln 16ρ ≤ π Λ(ρ) ≤ ln 16(ρ + 1)`: by (5.18) `π Λ(ρ) = 2 μ(r)` with
`r = √(1/(1+ρ))`, and twice (14.27) at `r` reads `ln 16ρ ≤ 2 μ(r) ≤ ln 16(ρ + 1)`. -/
theorem lam14_log_bounds {ρ : ℝ} (hρ : 0 < ρ) :
    Real.log (16 * ρ) ≤ π * quadLambda ρ ∧ π * quadLambda ρ ≤ Real.log (16 * (ρ + 1)) := by
  obtain ⟨h0, h1, hA, hB⟩ := lam14_sqrt_facts hρ
  have hΛ : π * quadLambda ρ = 2 * grotzschMu (Real.sqrt (1 / (1 + ρ))) := by
    rw [eq5_18 hρ]
    field_simp
  rw [hΛ, ← hA, ← hB, Real.log_pow, Real.log_pow]
  push_cast
  exact ⟨by linarith [em_lower h0 h1], by linarith [em_upper h0 h1]⟩

/-- `Λ(ρ)` is strictly increasing on `(0, ∞)` with `Λ(ρ) → 0` as `ρ → 0` and `Λ(ρ) → ∞` as
`ρ → ∞` (§14.3). -/
theorem quadLambda_strictMono :
    StrictMonoOn quadLambda (Ioi 0) ∧ Tendsto quadLambda (𝓝[>] 0) (𝓝 0) ∧
      Tendsto quadLambda atTop atTop := by
  -- monotone: (5.18), `ρ ↦ √(1/(1+ρ))` decreasing into `(0, 1)`, `μ` decreasing
  have hmono : StrictMonoOn quadLambda (Ioi 0) := by
    intro a ha b hb hab
    have ha' : 0 < a := ha
    have hb' : 0 < b := hb
    obtain ⟨ha0, ha1, -, -⟩ := lam14_sqrt_facts ha'
    obtain ⟨hb0, hb1, -, -⟩ := lam14_sqrt_facts hb'
    have hlt : Real.sqrt (1 / (1 + b)) < Real.sqrt (1 / (1 + a)) :=
      Real.sqrt_lt_sqrt (by positivity) (one_div_lt_one_div_of_lt (by linarith) (by linarith))
    rw [eq5_18 ha', eq5_18 hb']
    exact mul_lt_mul_of_pos_left (grotzschMu_strictAntiOn ⟨hb0, hb1⟩ ⟨ha0, ha1⟩ hlt)
      (by positivity)
  -- `Λ → ∞`: `Λ(ρ) ≥ ln(16ρ)/π` (14.26)
  have hinf : Tendsto quadLambda atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ ((Real.tendsto_log_atTop.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 16))).atTop_div_const Real.pi_pos)
    filter_upwards [eventually_gt_atTop 0] with ρ hρ
    show Real.log (16 * ρ) / π ≤ quadLambda ρ
    rw [div_le_iff₀' Real.pi_pos]
    exact (lam14_log_bounds hρ).1
  -- `Λ → 0` at `0⁺`: `Λ(ρ) = 1/Λ(1/ρ)` (5.20)
  have hzero : Tendsto quadLambda (𝓝[>] 0) (𝓝 0) := by
    have hinv : Tendsto (fun ρ : ℝ => 1 / ρ) (𝓝[>] 0) atTop := by
      simpa only [one_div] using tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
    have h1 : Tendsto (fun ρ : ℝ => quadLambda (1 / ρ)) (𝓝[>] 0) atTop := hinf.comp hinv
    refine h1.inv_tendsto_atTop.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    exact (eq_inv_of_mul_eq_one_left (eq5_20 hρ)).symm
  exact ⟨hmono, hzero, hinf⟩

/-- `λ(v) = Λ⁻¹(v)`, the inverse function of `Λ` (§14.3). -/
def lambdaInv (v : ℝ) : ℝ := sSup {ρ : ℝ | 0 < ρ ∧ quadLambda ρ ≤ v}

/-- `λ` is the inverse of `Λ`. -/
theorem lambdaInv_quadLambda {ρ : ℝ} (hρ : 0 < ρ) : lambdaInv (quadLambda ρ) = ρ := by
  have hS : {σ : ℝ | 0 < σ ∧ quadLambda σ ≤ quadLambda ρ} = Ioc 0 ρ := by
    ext σ
    exact ⟨fun h => ⟨h.1, (quadLambda_strictMono.1.le_iff_le h.1 hρ).1 h.2⟩,
      fun h => ⟨h.1, (quadLambda_strictMono.1.le_iff_le h.1 hρ).2 h.2⟩⟩
  rw [lambdaInv, hS, csSup_Ioc hρ]

/-! ### ℘-rectangle track: interface between the ℘-on-the-rectangle facts (P1) and the modulus assembly (P2).
Coordinator-fixed statements; P1 proves them, P2 uses them. `L` is a period pair `⟨1, v i⟩`. -/

/-- An integer whose real cast lies strictly between `-1` and `1` is `0`. -/
theorem rect_p1_int_eq_zero {m : ℤ} (h0 : (-1 : ℝ) < m) (h1 : (m : ℝ) < 1) : m = 0 := by
  have a : (-1 : ℤ) < m := by exact_mod_cast h0
  have b : m < 1 := by exact_mod_cast h1
  omega

/-- Coordinates of a point of the lattice `⟨1, v i⟩`: `Re z = m` and `Im z = n v` with `m, n ∈ ℤ`. -/
theorem rect_p1_lattice_coords {L : PeriodPair} {v : ℝ} (h1 : L.ω₁ = 1)
    (h2 : L.ω₂ = (v : ℂ) * I) {z : ℂ} (hz : z ∈ L.lattice) :
    ∃ m n : ℤ, z.re = m ∧ z.im = n * v := by
  rw [PeriodPair.mem_lattice] at hz
  obtain ⟨m, n, rfl⟩ := hz
  exact ⟨m, n, by simp [h1, h2], by simp [h1, h2]⟩

/-- The lattice `⟨1, v i⟩` is stable under complex conjugation. -/
theorem rect_p1_conj_mem {L : PeriodPair} {v : ℝ} (h1 : L.ω₁ = 1) (h2 : L.ω₂ = (v : ℂ) * I) :
    ∀ x : ℂ, x ∈ L.lattice → conj x ∈ L.lattice := by
  intro x hx
  rw [PeriodPair.mem_lattice] at hx ⊢
  obtain ⟨m, n, rfl⟩ := hx
  refine ⟨m, -n, ?_⟩
  rw [h1, h2]
  apply Complex.ext <;> simp

/-- Conjugation symmetry of `℘` for a conjugation-stable lattice: `conj (℘ z) = ℘ (conj z)`. -/
theorem rect_p1_conj_weierstrassP (L : PeriodPair)
    (hL : ∀ x : ℂ, x ∈ L.lattice → conj x ∈ L.lattice) (z : ℂ) :
    conj (L.weierstrassP z) = L.weierstrassP (conj z) := by
  let e : L.lattice ≃ L.lattice :=
    ⟨fun l => ⟨conj (l : ℂ), hL _ l.2⟩, fun l => ⟨conj (l : ℂ), hL _ l.2⟩,
      fun l => Subtype.ext (by simp), fun l => Subtype.ext (by simp)⟩
  simp only [PeriodPair.weierstrassP]
  rw [Complex.conj_tsum, ← e.tsum_eq]
  refine tsum_congr fun l => ?_
  simp [e, map_sub, map_pow]

/-- A point of the open quarter-period rectangle is not a lattice point. -/
theorem rect_p1_not_mem_lattice {L : PeriodPair} {v : ℝ} (h1 : L.ω₁ = 1)
    (h2 : L.ω₂ = (v : ℂ) * I) {z : ℂ} (hz : z ∈ rectangle (1 / 2) (v / 2)) :
    z ∉ L.lattice := by
  intro hL
  obtain ⟨m, n, hre, -⟩ := rect_p1_lattice_coords h1 h2 hL
  obtain ⟨hr0, hr1, -, -⟩ := hz
  have hm : m = 0 := rect_p1_int_eq_zero (by linarith) (by linarith)
  subst hm
  simp only [Int.cast_zero] at hre
  linarith

/-- `℘` takes no real value on the open quarter-period rectangle. -/
theorem rect_p1_wp_im_ne_zero {L : PeriodPair} {v : ℝ} (hv : 0 < v) (h1 : L.ω₁ = 1)
    (h2 : L.ω₂ = (v : ℂ) * I) {z : ℂ} (hz : z ∈ rectangle (1 / 2) (v / 2)) :
    (L.weierstrassP z).im ≠ 0 := by
  intro him
  have hτ : 0 < L.ω₂.im := by rw [h2]; simpa using hv
  have hzL : z ∉ L.lattice := rect_p1_not_mem_lattice h1 h2 hz
  have hzL' : conj z ∉ L.lattice := fun hL => hzL (by simpa using rect_p1_conj_mem h1 h2 _ hL)
  have heq : L.weierstrassP z = L.weierstrassP (conj z) := by
    rw [← rect_p1_conj_weierstrassP L (rect_p1_conj_mem h1 h2) z]
    exact (Complex.conj_eq_iff_im.mpr him).symm
  obtain ⟨hr0, hr1, hi0, hi1⟩ := hz
  rcases (weierstrassP_eq_iff_of_one h1 hτ hzL hzL').1 heq with hL | hL
  · obtain ⟨m, n, -, hn⟩ := rect_p1_lattice_coords h1 h2 hL
    simp only [Complex.sub_im, Complex.conj_im] at hn
    have a : (0 : ℝ) < n := by
      by_contra hc
      push Not at hc
      nlinarith
    have b : (n : ℝ) < 1 := by
      by_contra hc
      push Not at hc
      nlinarith
    have a' : (0 : ℤ) < n := by exact_mod_cast a
    have b' : n < 1 := by exact_mod_cast b
    omega
  · obtain ⟨m, n, hm, -⟩ := rect_p1_lattice_coords h1 h2 hL
    simp only [Complex.add_re, Complex.conj_re] at hm
    have a : (0 : ℝ) < m := by linarith
    have b : (m : ℝ) < 1 := by linarith
    have a' : (0 : ℤ) < m := by exact_mod_cast a
    have b' : m < 1 := by exact_mod_cast b
    omega

/-- The decomposition `℘ z = ℘[L - 0] z + 1 / z²` of `℘` at its pole `0`. -/
theorem rect_p1_wp_decomp (L : PeriodPair) (z : ℂ) :
    L.weierstrassP z = L.weierstrassPExcept 0 z + 1 / z ^ 2 := by
  have h := L.weierstrassPExcept_add ⟨0, L.lattice.zero_mem⟩ z
  rw [← h]
  simp

/-- Near `0` on the diagonal of the open quarter-period rectangle, `-℘` takes a value in the
upper half-plane. -/
theorem rect_p1_exists_im_pos (L : PeriodPair) {v : ℝ} (hv : 0 < v) :
    ∃ z ∈ rectangle (1 / 2) (v / 2), 0 < (-L.weierstrassP z).im := by
  have hcont : ContinuousAt (L.weierstrassPExcept 0) 0 :=
    (L.analyticAt_weierstrassPExcept 0).continuousAt
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
  set t : ℝ := min (min (δ / 4) (1 / 4)) (v / 4) with ht
  have ht0 : 0 < t := lt_min (lt_min (by linarith) (by norm_num)) (by linarith)
  have ht1 : t ≤ δ / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have ht2 : t ≤ 1 / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have ht3 : t ≤ v / 4 := min_le_right _ _
  set z : ℂ := (t : ℂ) * (1 + I) with hz
  have hzre : z.re = t := by simp [hz]
  have hzim : z.im = t := by simp [hz]
  refine ⟨z, ⟨by rw [hzre]; exact ht0, by rw [hzre]; linarith, by rw [hzim]; exact ht0,
    by rw [hzim]; linarith⟩, ?_⟩
  have hnorm : ‖z‖ < δ := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [hzre, hzim, abs_of_pos ht0] at this
    linarith
  have hE : ‖L.weierstrassPExcept 0 z‖ < 1 := by
    have := hball (x := z) (by simpa [dist_eq_norm] using hnorm)
    simpa [dist_eq_norm] using this
  have hinv : (1 / z ^ 2).im = -(1 / (2 * t ^ 2)) := by
    have hz2 : z ^ 2 = ((2 * t ^ 2 : ℝ) : ℂ) * I := by
      rw [hz]
      push_cast
      ring_nf
      rw [I_sq]
      ring
    rw [hz2, one_div, mul_inv, Complex.inv_I, ← Complex.ofReal_inv]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
      Complex.neg_im, Complex.I_re, Complex.I_im]
    ring
  rw [rect_p1_wp_decomp L z, neg_im, add_im, hinv]
  have hre := abs_le.mp ((Complex.abs_im_le_norm (L.weierstrassPExcept 0 z)).trans hE.le)
  have h8 : 8 ≤ 1 / (2 * t ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  linarith [hre.1, hre.2]

/-- The closed quarter-period rectangle `[0, 1/2] × [0, v/2]`. -/
def rect_box (v : ℝ) : Set ℂ := {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 / 2 ∧ 0 ≤ z.im ∧ z.im ≤ v / 2}

/-- The closure of the open quarter-period rectangle is the closed one. -/
theorem rect_closure_rectangle {v : ℝ} (hv : 0 < v) : closure (rectangle (1 / 2) (v / 2)) = rect_box v := by
  rw [rectangle_eq_reProdIm, Complex.closure_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1 / 2),
    closure_Ioo (by linarith : (0 : ℝ) < v / 2).ne]
  ext z
  simp [rect_box, Complex.mem_reProdIm, and_assoc]

/-- Lattice points in the closed quarter-period rectangle: only `0`. -/
theorem rect_closedRect_lattice {L : PeriodPair} {v : ℝ} (hv : 0 < v) (h1 : L.ω₁ = 1)
    (h2 : L.ω₂ = (v : ℂ) * I) :
    ∀ z ∈ rect_box v, z ∈ L.lattice → z = 0 := by
  intro z hz hzL
  obtain ⟨m, n, hre, him⟩ := rect_p1_lattice_coords h1 h2 hzL
  obtain ⟨hr0, hr1, hi0, hi1⟩ := hz
  have hm : m = 0 := rect_p1_int_eq_zero (by linarith) (by linarith)
  have hn : n = 0 := by
    apply rect_p1_int_eq_zero
    · by_contra hc
      push Not at hc
      nlinarith
    · by_contra hc
      push Not at hc
      nlinarith
  subst hm hn
  apply Complex.ext <;> simp [hre, him]

/-- `℘` is injective on the closed quarter-period rectangle minus the lattice point `0`. -/
theorem rect_wp_injOn {L : PeriodPair} {v : ℝ} (hv : 0 < v) (h1 : L.ω₁ = 1)
    (h2 : L.ω₂ = (v : ℂ) * I) :
    InjOn L.weierstrassP (rect_box v \ {0}) := by
  intro z hz z' hz' h
  have hτ : 0 < L.ω₂.im := by rw [h2]; simpa using hv
  have hzL : z ∉ L.lattice := fun hL => hz.2 (rect_closedRect_lattice hv h1 h2 z hz.1 hL)
  have hzL' : z' ∉ L.lattice := fun hL => hz'.2 (rect_closedRect_lattice hv h1 h2 z' hz'.1 hL)
  obtain ⟨⟨hr0, hr1, hi0, hi1⟩, -⟩ := hz
  obtain ⟨⟨hr0', hr1', hi0', hi1'⟩, -⟩ := hz'
  rcases (weierstrassP_eq_iff_of_one h1 hτ hzL hzL').1 h with hL | hL
  · obtain ⟨m, n, hre, him⟩ := rect_p1_lattice_coords h1 h2 hL
    simp only [Complex.sub_re, Complex.sub_im] at hre him
    have hm : m = 0 := rect_p1_int_eq_zero (by linarith) (by linarith)
    have hn : n = 0 := by
      apply rect_p1_int_eq_zero
      · by_contra hc
        push Not at hc
        nlinarith
      · by_contra hc
        push Not at hc
        nlinarith
    subst hm hn
    simp only [Int.cast_zero, zero_mul] at hre him
    apply Complex.ext <;> linarith
  · obtain ⟨m, n, hre, him⟩ := rect_p1_lattice_coords h1 h2 hL
    simp only [Complex.add_re, Complex.add_im] at hre him
    have hm : m = 0 ∨ m = 1 := by
      have a : (-1 : ℤ) < m := by exact_mod_cast (show (-1 : ℝ) < m by linarith)
      have b : m < 2 := by exact_mod_cast (show (m : ℝ) < 2 by linarith)
      omega
    have hn : n = 0 ∨ n = 1 := by
      have a : (-1 : ℝ) < n := by
        by_contra hc
        push Not at hc
        nlinarith
      have b : (n : ℝ) < 2 := by
        by_contra hc
        push Not at hc
        nlinarith
      have a' : (-1 : ℤ) < n := by exact_mod_cast a
      have b' : n < 2 := by exact_mod_cast b
      omega
    apply Complex.ext
    · rcases hm with rfl | rfl <;> simp only [Int.cast_zero, Int.cast_one] at hre <;> linarith
    · rcases hn with rfl | rfl <;> simp only [Int.cast_zero, Int.cast_one, zero_mul, one_mul] at him <;>
        linarith

/-- `℘` is real on the boundary of the quarter-period rectangle (away from `0`). -/
theorem rect_wp_im_eq_zero {L : PeriodPair} {v : ℝ} (hv : 0 < v) (h1 : L.ω₁ = 1)
    (h2 : L.ω₂ = (v : ℂ) * I) :
    ∀ z ∈ rect_box v \ {0}, z ∉ rectangle (1 / 2) (v / 2) →
      (L.weierstrassP z).im = 0 := by
  have _ := hv
  intro z hz hzR
  obtain ⟨⟨hr0, hr1, hi0, hi1⟩, -⟩ := hz
  have hconj := rect_p1_conj_weierstrassP L (rect_p1_conj_mem h1 h2) z
  apply Complex.conj_eq_iff_im.mp
  rw [hconj]
  have hcases : z.re = 0 ∨ z.re = 1 / 2 ∨ z.im = 0 ∨ z.im = v / 2 := by
    by_contra hc
    push Not at hc
    exact hzR ⟨lt_of_le_of_ne hr0 (Ne.symm hc.1), lt_of_le_of_ne hr1 hc.2.1,
      lt_of_le_of_ne hi0 (Ne.symm hc.2.2.1), lt_of_le_of_ne hi1 hc.2.2.2⟩
  have hω₁ : (1 : ℂ) ∈ L.lattice := h1 ▸ L.ω₁_mem_lattice
  have hω₂ : (v : ℂ) * I ∈ L.lattice := h2 ▸ L.ω₂_mem_lattice
  rcases hcases with h | h | h | h
  · have hc : conj z = -z := by
      apply Complex.ext <;> simp [h]
    rw [hc, PeriodPair.weierstrassP_neg]
  · have hc : conj z = -(z - ((⟨1, hω₁⟩ : L.lattice) : ℂ)) := by
      apply Complex.ext
      · simp [h]
        norm_num
      · simp
    rw [hc, PeriodPair.weierstrassP_neg, PeriodPair.weierstrassP_sub_coe]
  · rw [Complex.conj_eq_iff_im.mpr h]
  · have hc : conj z = z - ((⟨(v : ℂ) * I, hω₂⟩ : L.lattice) : ℂ) := by
      apply Complex.ext
      · simp
      · simp [h]
        ring
    rw [hc, PeriodPair.weierstrassP_sub_coe]

/-- `|℘(z)| → ∞` as `z → 0`. -/
theorem rect_wp_tendsto_zero {L : PeriodPair} {v : ℝ} (hv : 0 < v) (h1 : L.ω₁ = 1)
    (h2 : L.ω₂ = (v : ℂ) * I) :
    Tendsto (fun z => ‖L.weierstrassP z‖) (𝓝[≠] 0) atTop := by
  have _ := hv
  have _ := h1
  have _ := h2
  have hcont : ContinuousAt (L.weierstrassPExcept 0) 0 :=
    (L.analyticAt_weierstrassPExcept 0).continuousAt
  have hbd : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖L.weierstrassPExcept 0 z‖ ≤ 1 := by
    have h0 : ∀ᶠ z in 𝓝 (0 : ℂ), ‖L.weierstrassPExcept 0 z‖ < 1 :=
      hcont.norm.eventually (eventually_lt_nhds (by simp : ‖L.weierstrassPExcept 0 0‖ < 1))
    exact (h0.filter_mono nhdsWithin_le_nhds).mono fun z hz => hz.le
  have hinv : Tendsto (fun z : ℂ => ‖z⁻¹‖ ^ 2) (𝓝[≠] 0) atTop :=
    (tendsto_pow_atTop two_ne_zero).comp tendsto_norm_inv_nhdsNE_zero_atTop
  refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-1) hinv)
  filter_upwards [hbd] with z hz
  rw [rect_p1_wp_decomp L z]
  have hn : ‖(1 : ℂ) / z ^ 2‖ = ‖z⁻¹‖ ^ 2 := by rw [one_div, ← inv_pow, norm_pow]
  have := norm_sub_le (L.weierstrassPExcept 0 z + 1 / z ^ 2) (L.weierstrassPExcept 0 z)
  rw [add_sub_cancel_left, hn] at this
  linarith

/-- `-℘` maps the open quarter-period rectangle conformally onto the upper half-plane. -/
theorem rect_wp_conformal {L : PeriodPair} {v : ℝ} (hv : 0 < v) (h1 : L.ω₁ = 1)
    (h2 : L.ω₂ = (v : ℂ) * I) :
    IsConformalOnto (fun z => -L.weierstrassP z) (rectangle (1 / 2) (v / 2)) upperHalf := by
  set R := rectangle (1 / 2) (v / 2) with hR
  set f : ℂ → ℂ := fun z => -L.weierstrassP z with hf
  have hRL : R ⊆ (L.lattice : Set ℂ)ᶜ := fun z hz => rect_p1_not_mem_lattice h1 h2 hz
  have hRbox : R ⊆ rect_box v \ {0} := by
    intro z hz
    obtain ⟨hr0, hr1, hi0, hi1⟩ := hz
    refine ⟨⟨hr0.le, hr1.le, hi0.le, hi1.le⟩, ?_⟩
    rintro rfl
    simp at hr0
  have han : AnalyticOnNhd ℂ f R := (L.analyticOnNhd_weierstrassP.mono hRL).neg
  have hinj : InjOn f R := fun z hz z' hz' h =>
    rect_wp_injOn hv h1 h2 (hRbox hz) (hRbox hz') (neg_injective h)
  have hpre : IsPreconnected R := (convex_rectangle _ _).isPreconnected
  refine ⟨han.differentiableOn, hinj, ?_⟩
  obtain ⟨z₀, hz₀R, hz₀⟩ := rect_p1_exists_im_pos L hv
  -- `f '' R ⊆ ℍ`: `Im f` does not vanish on the preconnected `R` and is positive at `z₀`
  have hsub : f '' R ⊆ upperHalf := by
    rintro _ ⟨z, hzR, rfl⟩
    show 0 < (f z).im
    by_contra hneg
    push Not at hneg
    have hcont : ContinuousOn (fun z => (f z).im) R :=
      Complex.continuous_im.comp_continuousOn han.continuousOn
    obtain ⟨w, hwR, hw0⟩ := hpre.intermediate_value hzR hz₀R hcont ⟨hneg, hz₀.le⟩
    exact rect_p1_wp_im_ne_zero hv h1 h2 hwR (by simpa [hf] using hw0)
  -- `f '' R` is open (open mapping theorem; `f` is injective, hence not constant)
  have hopen : IsOpen (f '' R) := by
    rcases han.is_constant_or_isOpen hpre with ⟨w, hw⟩ | hop
    · exfalso
      have pa : (⟨1 / 8, v / 4⟩ : ℂ) ∈ R :=
        ⟨by norm_num, by norm_num, by show (0 : ℝ) < v / 4; positivity,
          by show v / 4 < v / 2; linarith⟩
      have pb : (⟨1 / 4, v / 4⟩ : ℂ) ∈ R :=
        ⟨by norm_num, by norm_num, by show (0 : ℝ) < v / 4; positivity,
          by show v / 4 < v / 2; linarith⟩
      have := congrArg Complex.re (hinj pa pb ((hw _ pa).trans (hw _ pb).symm))
      norm_num at this
    · exact hop R subset_rfl (isOpen_rectangle _ _)
  -- limit points of `f '' R` in `ℍ` lie in `f '' R`
  have hclosed : closure (f '' R) ∩ upperHalf ⊆ f '' R := by
    rintro c ⟨hcl, hc⟩
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp
      ((rect_wp_tendsto_zero hv h1 h2).eventually_gt_atTop (‖c‖ + 1))
    set K := rect_box v ∩ {z : ℂ | r ≤ ‖z‖} with hK
    have hKbox : K ⊆ rect_box v \ {0} := by
      rintro z ⟨hzb, hzr⟩
      refine ⟨hzb, ?_⟩
      rintro rfl
      have hr0 : r ≤ ‖(0 : ℂ)‖ := hzr
      rw [norm_zero] at hr0
      linarith
    have hKL : K ⊆ (L.lattice : Set ℂ)ᶜ := fun z hz hzL =>
      (hKbox hz).2 (rect_closedRect_lattice hv h1 h2 z (hKbox hz).1 hzL)
    have hboxc : IsCompact (rect_box v) := by
      have : rect_box v = Icc 0 (1 / 2) ×ℂ Icc 0 (v / 2) := by
        ext z
        simp [rect_box, Complex.mem_reProdIm, and_assoc]
      rw [this]
      exact isCompact_Icc.reProdIm isCompact_Icc
    have hKc : IsCompact K := hboxc.inter_right (isClosed_le continuous_const continuous_norm)
    have hfK : IsCompact (f '' K) :=
      hKc.image_of_continuousOn (L.differentiableOn_weierstrassP.continuousOn.mono hKL).neg
    have hcK : c ∈ f '' K := by
      apply hfK.isClosed.closure_subset
      rw [Metric.mem_closure_iff] at hcl ⊢
      intro ε hε
      obtain ⟨b, ⟨z, hzR, rfl⟩, hb⟩ := hcl (min ε 1) (lt_min hε one_pos)
      refine ⟨f z, ⟨z, ⟨(hRbox hzR).1, ?_⟩, rfl⟩, lt_of_lt_of_le hb (min_le_left _ _)⟩
      show r ≤ ‖z‖
      by_contra hlt
      push Not at hlt
      have hbig : ‖c‖ + 1 < ‖L.weierstrassP z‖ :=
        hball ⟨by simpa [dist_eq_norm] using hlt, (hRbox hzR).2⟩
      have h1' : dist c (f z) < 1 := lt_of_lt_of_le hb (min_le_right _ _)
      rw [dist_eq_norm] at h1'
      have := norm_sub_le c (c - f z)
      rw [sub_sub_cancel] at this
      simp only [hf, norm_neg] at this
      linarith
    obtain ⟨z, hzK, hzc⟩ := hcK
    by_cases hzR : z ∈ R
    · exact ⟨z, hzR, hzc⟩
    · exfalso
      have him := rect_wp_im_eq_zero hv h1 h2 z (hKbox hzK) hzR
      rw [← hzc] at hc
      have hc' : 0 < (f z).im := hc
      simp only [hf, neg_im, him, neg_zero, lt_irrefl] at hc'
  refine Subset.antisymm hsub ?_
  exact isConnected_upperHalf.isPreconnected.subset_of_closure_inter_subset hopen
    ⟨f z₀, hsub ⟨z₀, hz₀R, rfl⟩, ⟨z₀, hz₀R, rfl⟩⟩ hclosed

/-! ### ℘-rectangle track, piece P2: the modulus assembly for (14.19) and (14.21)

`-℘` maps the quarter-period rectangle `R(0, 1/2, (1+iv)/2, iv/2)` conformally onto `ℍ`, with boundary
extension `rect_p2_ext` (`0 ↦ ∞`); the real Möbius map `ζ ↦ (ζ + e₁)/(-ζ - e₂)` then sends the vertices
`∞, -e₁, -e₃, -e₂` to `-1, 0, ρ, ∞`, `ρ = (e₁ - e₃)/(e₃ - e₂)`.  Comparing moduli (Theorems 1.2, 1.3)
gives `Λ(ρ) = v`. -/

/-- The boundary extension of `-℘` from the closed quarter-period rectangle to `ℂ̄`: `∞` at `∞` and at
the lattice point `0`, and `-℘(z)` at every other finite point `z`. -/
def rect_p2_ext (L : PeriodPair) (p : ExtPlane) : ExtPlane :=
  OnePoint.elim p extInf fun z => if z = 0 then extInf else ((-L.weierstrassP z : ℂ) : ExtPlane)

/-- `rect_p2_ext` sends the finite point `0` to `∞`. -/
theorem rect_p2_ext_zero (L : PeriodPair) : rect_p2_ext L ((0 : ℂ) : ExtPlane) = extInf := by
  show (if (0 : ℂ) = 0 then extInf else ((-L.weierstrassP 0 : ℂ) : ExtPlane)) = extInf
  rw [ite_eq_left rfl]

/-- `rect_p2_ext` sends a finite point `z ≠ 0` to `-℘(z)`. -/
theorem rect_p2_ext_coe_of_ne (L : PeriodPair) {z : ℂ} (hz : z ≠ 0) :
    rect_p2_ext L (z : ExtPlane) = ((-L.weierstrassP z : ℂ) : ExtPlane) := by
  show (if z = 0 then extInf else ((-L.weierstrassP z : ℂ) : ExtPlane)) = _
  rw [ite_eq_right hz]

/-- The closure in `ℂ̄` of the open quarter-period rectangle is the closed one. -/
theorem rect_p2_closure_toExt {v : ℝ} (hv : 0 < v) :
    closure (toExt (rectangle (1 / 2) (v / 2))) = toExt (rect_box v) := by
  rw [closure_toExt_of_isBounded (isBounded_rectangle _ _), rect_closure_rectangle hv]

/-- `rect_p2_ext` is continuous at every point of the closed quarter-period rectangle: at `0` because
`|℘| → ∞`, elsewhere because `℘` is holomorphic off the lattice. -/
theorem rect_p2_continuousAt {L : PeriodPair} {v : ℝ} (hv : 0 < v) (h1 : L.ω₁ = 1)
    (h2 : L.ω₂ = (v : ℂ) * I) {z : ℂ} (hz : z ∈ rect_box v) :
    ContinuousAt (rect_p2_ext L) (z : ExtPlane) := by
  rw [OnePoint.continuousAt_coe]
  by_cases h0 : z = 0
  · subst h0
    show Tendsto (fun w : ℂ => rect_p2_ext L (w : ExtPlane)) (𝓝 0)
      (𝓝 (rect_p2_ext L ((0 : ℂ) : ExtPlane)))
    rw [rect_p2_ext_zero, ← nhdsNE_sup_pure (0 : ℂ)]
    refine Tendsto.sup ?_ ?_
    · have hcob : Tendsto (fun w => -L.weierstrassP w) (𝓝[≠] 0) (Bornology.cobounded ℂ) := by
        rw [← tendsto_norm_atTop_iff_cobounded]
        simpa only [norm_neg] using rect_wp_tendsto_zero hv h1 h2
      rw [cobounded_eq_cocompact, ← coclosedCompact_eq_cocompact] at hcob
      refine (OnePoint.tendsto_coe_infty.comp hcob).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact (rect_p2_ext_coe_of_ne L hw).symm
    · rw [tendsto_pure_left]
      intro s hs
      rw [rect_p2_ext_zero]
      exact mem_of_mem_nhds hs
  · have hnl : z ∉ L.lattice := fun hl => h0 (rect_closedRect_lattice hv h1 h2 z hz hl)
    have hdiff : DifferentiableAt ℂ L.weierstrassP z :=
      L.differentiableOn_weierstrassP.differentiableAt
        (L.isClosed_lattice.isOpen_compl.mem_nhds hnl)
    have hcont : ContinuousAt (fun w => ((-L.weierstrassP w : ℂ) : ExtPlane)) z :=
      OnePoint.continuous_coe.continuousAt.comp hdiff.continuousAt.neg
    refine hcont.congr ?_
    filter_upwards [eventually_ne_nhds h0] with w hw
    exact (rect_p2_ext_coe_of_ne L hw).symm

/-- `rect_p2_ext` is a homeomorphic boundary extension of `-℘` from the open quarter-period rectangle
onto the upper half-plane. -/
theorem rect_p2_isHomeoExtension {L : PeriodPair} {v : ℝ} (hv : 0 < v) (h1 : L.ω₁ = 1)
    (h2 : L.ω₂ = (v : ℂ) * I) :
    IsHomeoExtension (fun z => -L.weierstrassP z) (rectangle (1 / 2) (v / 2)) upperHalf
      (rect_p2_ext L) := by
  have hconf := rect_wp_conformal hv h1 h2
  have hcl := rect_p2_closure_toExt hv
  have hR0 : ∀ z ∈ rectangle (1 / 2) (v / 2), z ≠ 0 := by
    rintro z hz rfl
    exact lt_irrefl _ hz.1
  have hcont : ContinuousOn (rect_p2_ext L) (closure (toExt (rectangle (1 / 2) (v / 2)))) := by
    rw [hcl]
    rintro _ ⟨z, hz, rfl⟩
    exact (rect_p2_continuousAt hv h1 h2 hz).continuousWithinAt
  refine ⟨fun z hz => rect_p2_ext_coe_of_ne L (hR0 z hz), hcont, ?_, ?_⟩
  · rw [hcl]
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩ heq
    by_cases hz0 : z = 0
    · by_cases hw0 : w = 0
      · rw [hz0, hw0]
      · rw [hz0, rect_p2_ext_zero, rect_p2_ext_coe_of_ne L hw0] at heq
        exact absurd heq.symm (OnePoint.coe_ne_infty _)
    · by_cases hw0 : w = 0
      · rw [hw0, rect_p2_ext_zero, rect_p2_ext_coe_of_ne L hz0] at heq
        exact absurd heq (OnePoint.coe_ne_infty _)
      · rw [rect_p2_ext_coe_of_ne L hz0, rect_p2_ext_coe_of_ne L hw0] at heq
        have h' : L.weierstrassP z = L.weierstrassP w := neg_injective (OnePoint.coe_injective heq)
        rw [rect_wp_injOn hv h1 h2 ⟨hz, hz0⟩ ⟨hw, hw0⟩ h']
  · apply subset_antisymm
    · rw [hcl, scExt_closure_toExt_upperHalf]
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      by_cases hz0 : z = 0
      · rw [hz0, rect_p2_ext_zero]
        exact Or.inr rfl
      · rw [rect_p2_ext_coe_of_ne L hz0]
        refine Or.inl ⟨_, ?_, rfl⟩
        show 0 ≤ (-L.weierstrassP z).im
        by_cases hzR : z ∈ rectangle (1 / 2) (v / 2)
        · have hmem : -L.weierstrassP z ∈ upperHalf := by
            rw [← hconf.2.2]
            exact ⟨z, hzR, rfl⟩
          exact le_of_lt hmem
        · rw [neg_im, rect_wp_im_eq_zero hv h1 h2 z ⟨hz, hz0⟩ hzR, neg_zero]
    · have hK : IsCompact (rect_p2_ext L '' closure (toExt (rectangle (1 / 2) (v / 2)))) :=
        isClosed_closure.isCompact.image_of_continuousOn hcont
      refine closure_minimal ?_ hK.isClosed
      rintro _ ⟨w, hw, rfl⟩
      rw [← hconf.2.2] at hw
      obtain ⟨z, hz, rfl⟩ := hw
      exact ⟨(z : ExtPlane), subset_closure ⟨z, hz, rfl⟩, rect_p2_ext_coe_of_ne L (hR0 z hz)⟩

/-- The modulus identity behind (14.19) and (14.21): with `r = e₃(iv) - e₂(iv) > 0` and
`s = e₁(iv) - e₃(iv) > 0`, `Λ(s/r) = v`.  The real Möbius map `ζ ↦ (ζ + e₁)/(-ζ - e₂)` composed with `-℘`
maps the quarter-period rectangle `R(0, 1/2, (1+iv)/2, iv/2)` conformally onto `ℍ(-1, 0, s/r, ∞)`, the
rotation of `ℍ(∞, -1, 0, s/r)`; then `1/v = M(R) = 1/Λ(s/r)` by Theorems 1.3 and 1.2. -/
theorem rect_p2_quadLambda {v r s : ℝ} (hv : 0 < v) (hr : 0 < r) (hs : 0 < s)
    (hE21 : weierstrassE ((v : ℂ) * I) 2 - weierstrassE ((v : ℂ) * I) 1 = r)
    (hE02 : weierstrassE ((v : ℂ) * I) 0 - weierstrassE ((v : ℂ) * I) 2 = s) :
    quadLambda (s / r) = v := by
  have hw : 0 < ((v : ℂ) * I).im := by simpa using hv
  set L := periodPairOf ((v : ℂ) * I) hw with hL
  have h1 : L.ω₁ = 1 := rfl
  have h2 : L.ω₂ = (v : ℂ) * I := rfl
  have he0 := weierstrassE_zero_eq hw
  have he1 := weierstrassE_one_eq hw
  have he2 := weierstrassE_two_eq hw
  rw [← hL] at he0 he1 he2
  -- `e₂ = ℘(iv/2)` is real: `iv/2` lies on the boundary of the rectangle
  have hvI0 : (v : ℂ) * I / 2 ≠ 0 := by
    have : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
    simp [this]
  have hre : ((v : ℂ) * I / 2).re = 0 := by simp
  have him2 : ((v : ℂ) * I / 2).im = v / 2 := by simp
  have hbox : (v : ℂ) * I / 2 ∈ rect_box v := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hre]
    · rw [hre]
      norm_num
    · rw [him2]
      positivity
    · rw [him2]
  have hnR : (v : ℂ) * I / 2 ∉ rectangle (1 / 2) (v / 2) := fun h => by
    have h' := h.1
    rw [hre] at h'
    exact lt_irrefl 0 h'
  have him : (L.weierstrassP ((v : ℂ) * I / 2)).im = 0 :=
    rect_wp_im_eq_zero hv h1 h2 _ ⟨hbox, hvI0⟩ hnR
  set E₂ : ℝ := (L.weierstrassP ((v : ℂ) * I / 2)).re with hE₂
  have hP2 : L.weierstrassP ((v : ℂ) * I / 2) = (E₂ : ℂ) := by
    apply Complex.ext <;> simp [hE₂, him]
  have hP3 : L.weierstrassP ((1 + (v : ℂ) * I) / 2) = ((E₂ + r : ℝ) : ℂ) := by
    rw [← he2]
    push_cast
    linear_combination hE21 + he1 + hP2
  have hP1 : L.weierstrassP (1 / 2) = ((E₂ + r + s : ℝ) : ℂ) := by
    rw [← he0]
    push_cast
    linear_combination hE02 + hE21 + he1 + hP2
  -- the real Möbius map `m(ζ) = (ζ + E₁)/(-ζ - E₂)`, `E₁ = E₂ + r + s`
  have hdet : (0 : ℝ) < 1 * -E₂ - (E₂ + r + s) * -1 := by linarith
  have hS' : ((1 : ℝ) : ℂ) * ((-E₂ : ℝ) : ℂ) - ((E₂ + r + s : ℝ) : ℂ) * ((-1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hdet.ne'
  set e := mobiusHomeomorph ((1 : ℝ) : ℂ) ((E₂ + r + s : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((-E₂ : ℝ) : ℂ) hS'
    with he
  have heS : ∀ w ∈ upperHalf, e (w : ExtPlane) = ((mobiusFn ((1 : ℝ) : ℂ) ((E₂ + r + s : ℝ) : ℂ)
      ((-1 : ℝ) : ℂ) ((-E₂ : ℝ) : ℂ) w : ℂ) : ExtPlane) :=
    fun w hw => by
      rw [he, mobiusHomeomorph_apply]
      exact mobiusExt_coe (mobiusFn_den_ne_zero_real hdet.ne' hw)
  have himgS : e '' toExt upperHalf = toExt upperHalf := by
    rw [he]
    exact mobiusExt_image_toExt_upperHalf hdet
  have hρ : 0 < s / r := div_pos hs hr
  set Q : TopQuad := ⟨upperHalf, _, isTopQuad_upperHalf_lambda hρ⟩ with hQ
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  have hb : 0 < v / 2 := by positivity
  have hconfR := rect_wp_conformal hv h1 h2
  have hv1 : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  have hv2 : ((1 / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * I = (1 + (v : ℂ) * I) / 2 := by push_cast; ring
  have hv3 : ((v / 2 : ℝ) : ℂ) * I = (v : ℂ) * I / 2 := by push_cast; ring
  have hconf : (rectQuad ha hb).ConfEquiv Q.rotate := by
    refine ⟨_, _, (isConformalOnto_mobius_upperHalf hdet).comp hconfR,
      (rect_p2_isHomeoExtension hv h1 h2).comp_homeomorph hconfR.mapsTo e heS himgS, fun i => ?_⟩
    fin_cases i
    · show e (rect_p2_ext L ((0 : ℂ) : ExtPlane)) = (((-1 : ℝ) : ℂ) : ExtPlane)
      rw [rect_p2_ext_zero, he, mobiusHomeomorph_apply, mobiusExt_ofReal_infty (by norm_num)]
      norm_num
    · show e (rect_p2_ext L (((1 / 2 : ℝ) : ℂ) : ExtPlane)) = ((0 : ℂ) : ExtPlane)
      have hden : (-1 : ℝ) * -(E₂ + r + s) + -E₂ ≠ 0 := by nlinarith
      rw [hv1, rect_p2_ext_coe_of_ne L (by norm_num), hP1, ← ofReal_neg, he, mobiusHomeomorph_apply,
        mobiusExt_ofReal_coe hden]
      congr 1
      rw [show (1 : ℝ) * -(E₂ + r + s) + (E₂ + r + s) = 0 by ring, zero_div, ofReal_zero]
    · show e (rect_p2_ext L ((((1 / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * I : ℂ) : ExtPlane)) =
        (((s / r : ℝ) : ℂ) : ExtPlane)
      have hne : (1 + (v : ℂ) * I) / 2 ≠ 0 := by
        intro h0
        have := congrArg Complex.re h0
        simp at this
      have hden : (-1 : ℝ) * -(E₂ + r) + -E₂ ≠ 0 := by nlinarith
      rw [hv2, rect_p2_ext_coe_of_ne L hne, hP3, ← ofReal_neg, he, mobiusHomeomorph_apply,
        mobiusExt_ofReal_coe hden]
      congr 2
      rw [div_eq_div_iff hden hr.ne']
      ring
    · show e (rect_p2_ext L ((((v / 2 : ℝ) : ℂ) * I : ℂ) : ExtPlane)) = extInf
      rw [hv3, rect_p2_ext_coe_of_ne L hvI0, hP2, ← ofReal_neg, he, mobiusHomeomorph_apply,
        mobiusExt_ofReal_coe_of_eq_zero (by ring)]
  have hm := thm1_3_modulus_conformal_invariant hconf
  rw [modulus_rectQuad] at hm
  have hrot := thm1_2_modulus_rotate Q
  have hQm : quadLambda (s / r) = Q.modulus := rfl
  rw [hQm, hrot, ← hm]
  field_simp

/-- `λ(v) = s/r` for `r = e₃(iv) - e₂(iv) > 0` and `s = e₁(iv) - e₃(iv) > 0`: `λ` inverts `Λ`. -/
theorem rect_p2_lambdaInv_eq {v r s : ℝ} (hv : 0 < v) (hr : 0 < r) (hs : 0 < s)
    (hE21 : weierstrassE ((v : ℂ) * I) 2 - weierstrassE ((v : ℂ) * I) 1 = r)
    (hE02 : weierstrassE ((v : ℂ) * I) 0 - weierstrassE ((v : ℂ) * I) 2 = s) :
    lambdaInv v = s / r := by
  calc lambdaInv v = lambdaInv (quadLambda (s / r)) := by
        rw [rect_p2_quadLambda hv hr hs hE21 hE02]
    _ = s / r := lambdaInv_quadLambda (div_pos hs hr)

/-- (14.19) `λ(v) = -φ(iv)`, stated as `eq14_19`. -/
theorem rect_eq14_19_aux {v : ℝ} (hv : 0 < v) : lambdaInv v = -(modularPhi (v * I)).re := by
  obtain ⟨r, hr, hE21⟩ := mphi_weierstrassE_two_sub_one_iv hv
  obtain ⟨s, hs, hE02⟩ := mphi_weierstrassE_zero_sub_two_iv hv
  have hphi : modularPhi ((v : ℂ) * I) = ((-(s / r) : ℝ) : ℂ) := by
    rw [modularPhi, hE21, show weierstrassE ((v : ℂ) * I) 2 - weierstrassE ((v : ℂ) * I) 0 =
      -(s : ℂ) by rw [← hE02]; ring]
    push_cast
    ring
  rw [rect_p2_lambdaInv_eq hv hr hs hE21 hE02, hphi, Complex.ofReal_re, neg_neg]

/-- (14.21) `λ(v) = (e₁(iv) - e₃(iv))/(e₃(iv) - e₂(iv))`, stated as `eq14_21`. -/
theorem rect_eq14_21_aux {v : ℝ} (hv : 0 < v) :
    (lambdaInv v : ℂ) = (weierstrassE (v * I) 0 - weierstrassE (v * I) 2) /
      (weierstrassE (v * I) 2 - weierstrassE (v * I) 1) := by
  obtain ⟨r, hr, hE21⟩ := mphi_weierstrassE_two_sub_one_iv hv
  obtain ⟨s, hs, hE02⟩ := mphi_weierstrassE_zero_sub_two_iv hv
  rw [rect_p2_lambdaInv_eq hv hr hs hE21 hE02, hE21, hE02]
  push_cast
  ring

/-- (14.18)–(14.19): `Λ⁻¹(v) = -q(iv)`. -/
theorem eq14_19 {v : ℝ} (hv : 0 < v) : lambdaInv v = -(modularPhi (v * I)).re := by
  exact rect_eq14_19_aux hv

/-- (14.21): `λ(v) = (e₁(iv) - e₃(iv))/(e₃(iv) - e₂(iv))`. -/
theorem eq14_21 {v : ℝ} (hv : 0 < v) :
    (lambdaInv v : ℂ) = (weierstrassE (v * I) 0 - weierstrassE (v * I) 2) /
      (weierstrassE (v * I) 2 - weierstrassE (v * I) 1) := by
  exact rect_eq14_21_aux hv

/-- (14.23): `λ(v) = (e^{πv}/16) ∏_{n ≥ 1} ((1 - e^{-(2n-1)πv})/(1 + e^{-2nπv}))⁸`. -/
theorem eq14_23 {v : ℝ} (hv : 0 < v) :
    lambdaInv v = Real.exp (π * v) / 16 *
      ∏' n : ℕ, ((1 - Real.exp (-(2 * (n + 1 : ℝ) - 1) * π * v)) /
        (1 + Real.exp (-2 * (n + 1 : ℝ) * π * v))) ^ 8 := by
  sorry

/-- (14.24): `λ(v) + 1 = (e^{πv}/16) ∏_{n ≥ 1} ((1 + e^{-(2n-1)πv})/(1 + e^{-2nπv}))⁸`. -/
theorem eq14_24 {v : ℝ} (hv : 0 < v) :
    lambdaInv v + 1 = Real.exp (π * v) / 16 *
      ∏' n : ℕ, ((1 + Real.exp (-(2 * (n + 1 : ℝ) - 1) * π * v)) /
        (1 + Real.exp (-2 * (n + 1 : ℝ) * π * v))) ^ 8 := by
  sorry

/-- (14.25): `16 λ(v) ≤ e^{πv} ≤ 16 (λ(v) + 1)`. -/
theorem eq14_25 {v : ℝ} (hv : 0 < v) :
    16 * lambdaInv v ≤ Real.exp (π * v) ∧ Real.exp (π * v) ≤ 16 * (lambdaInv v + 1) := by
  set S := {ρ : ℝ | 0 < ρ ∧ quadLambda ρ ≤ v}
  have hL : lambdaInv v = sSup S := rfl
  -- `ρ ∈ S`: `ln 16ρ ≤ π Λ(ρ) ≤ π v`, so `16 ρ ≤ e^{πv}`
  have hmem : ∀ ρ ∈ S, ρ ≤ Real.exp (π * v) / 16 := by
    rintro ρ ⟨hρ, hΛ⟩
    have h := (lam14_log_bounds hρ).1.trans (mul_le_mul_of_nonneg_left hΛ Real.pi_pos.le)
    rw [Real.log_le_iff_le_exp (by positivity)] at h
    rw [le_div_iff₀ (by norm_num)]
    linarith
  -- `S ≠ ∅` since `Λ → 0` at `0⁺`
  have hne : S.Nonempty := by
    obtain ⟨ρ, h1, h2⟩ :=
      ((quadLambda_strictMono.2.1.eventually_lt_const hv).and self_mem_nhdsWithin).exists
    exact ⟨ρ, h2, h1.le⟩
  have hbdd : BddAbove S := ⟨Real.exp (π * v) / 16, fun ρ h => hmem ρ h⟩
  have hpos : 0 < lambdaInv v := by
    obtain ⟨ρ, hρ⟩ := hne
    rw [hL]
    exact hρ.1.trans_le (le_csSup hbdd hρ)
  refine ⟨?_, ?_⟩
  · have h := csSup_le hne hmem
    rw [← hL, le_div_iff₀ (by norm_num)] at h
    linarith
  · -- else some `ρ > λ(v)` has `16(ρ + 1) < e^{πv}`, but `ρ ∉ S`: `π v < π Λ(ρ) ≤ ln 16(ρ + 1)`
    refine not_lt.1 fun hcon => ?_
    obtain ⟨ρ, hLρ, hρ16⟩ : ∃ ρ, lambdaInv v < ρ ∧ 16 * (ρ + 1) < Real.exp (π * v) :=
      ⟨(lambdaInv v + (Real.exp (π * v) / 16 - 1)) / 2, by linarith, by linarith⟩
    have hρ0 : 0 < ρ := hpos.trans hLρ
    have hΛ : v < quadLambda ρ := by
      refine not_le.1 fun h => ?_
      have h' := le_csSup hbdd (show ρ ∈ S from ⟨hρ0, h⟩)
      rw [← hL] at h'
      linarith
    have h2 := (mul_lt_mul_of_pos_left hΛ Real.pi_pos).trans_le (lam14_log_bounds hρ0).2
    rw [Real.lt_log_iff_exp_lt (by positivity)] at h2
    linarith

/-- (14.26): `ln 16ρ ≤ π Λ(ρ) ≤ ln 16(ρ + 1)`. -/
theorem eq14_26 {ρ : ℝ} (hρ : 0 < ρ) :
    Real.log (16 * ρ) ≤ π * quadLambda ρ ∧ π * quadLambda ρ ≤ Real.log (16 * (ρ + 1)) := by
  exact lam14_log_bounds hρ

/-- (14.27): `ln(4√(1 - r²)/r) ≤ μ(r) ≤ ln(4/r)` for `0 < r < 1`.

Proved (2026-09-23) without (14.23)–(14.26): `μ(r) = π a_r/b_r` and Landen's identity
`μ((1-u)/(1+u)) = 2μ(√(1-u²))` (`em_mu_landen`) give `h(s) ≤ h(ρ)/2` for `h = μ - ln(4/·)` and
`k(s) ≥ k(ρ)/2` for `k = μ - ln(4√(1-·²)/·)`; elementary bounds on the Schwarz–Christoffel side integrals give
a priori `h ≤ C`, `k ≥ -C`, and iterating yields `h ≤ 0 ≤ k`. -/
theorem eq14_27 {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    Real.log (4 * Real.sqrt (1 - r ^ 2) / r) ≤ grotzschMu r ∧ grotzschMu r ≤ Real.log (4 / r) :=
  ⟨em_lower hr₀ hr₁, em_upper hr₀ hr₁⟩

/-! ### Holomorphy of `e₁, e₂, e₃` in the period `w` (`mphi_`)

The lattice sum of `℘(z_j(w); 1, w)` is reindexed over `Fin 2 → ℤ` and bounded locally uniformly on
`ℍ` with the Eisenstein-series estimates (`EisensteinSeries.r`), so it is a locally uniform limit of
holomorphic functions. -/

/-- The half-period `z_j(w)`. -/
def mphi_wE_halfPeriod (j : Fin 3) (w : ℂ) : ℂ := ![1 / 2, w / 2, (1 + w) / 2] j

/-- The lattice point `v₀ w + v₁` (order chosen to match `EisensteinSeries.r_mul_max_le`). -/
def mphi_wE_latPt (v : Fin 2 → ℤ) (w : ℂ) : ℂ := (v 0 : ℂ) * w + v 1

/-- The reindexed summand of `℘(z_j(w); 1, w)`. -/
def mphi_wE_summand (j : Fin 3) (v : Fin 2 → ℤ) (w : ℂ) : ℂ :=
  1 / (mphi_wE_halfPeriod j w - mphi_wE_latPt v w) ^ 2 - 1 / mphi_wE_latPt v w ^ 2

/-- Step 1: reindex the lattice sum over `Fin 2 → ℤ`. -/
theorem mphi_weierstrassE_eq_tsum_summand (j : Fin 3) {w : ℂ} (hw : 0 < w.im) :
    weierstrassE w j = ∑' v : Fin 2 → ℤ, mphi_wE_summand j v w := by
  simp only [weierstrassE, hw, ↓reduceDIte, PeriodPair.weierstrassP]
  rw [← (((finTwoArrowEquiv ℤ).trans (Equiv.prodComm ℤ ℤ)).trans
      (periodPairOf w hw).latticeEquivProd.symm.toEquiv).tsum_eq]
  refine tsum_congr fun v => ?_
  have he : ((((finTwoArrowEquiv ℤ).trans (Equiv.prodComm ℤ ℤ)).trans
      (periodPairOf w hw).latticeEquivProd.symm.toEquiv) v : ℂ) = mphi_wE_latPt v w := by
    rw [Equiv.trans_apply, LinearEquiv.coe_toEquiv, PeriodPair.latticeEquiv_symm_apply]
    simp [periodPairOf, mphi_wE_latPt]
    ring
  rw [he]
  rfl

/-- Step 2: the Eisenstein lower bound `‖v₀ w + v₁‖ ≥ r(w) ‖v‖`. -/
theorem mphi_wE_latPt_lower (w : UpperHalfPlane) (v : Fin 2 → ℤ) :
    EisensteinSeries.r w * ‖v‖ ≤ ‖mphi_wE_latPt v (w : ℂ)‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [mphi_wE_latPt]
  exact EisensteinSeries.r_mul_max_le w hv

/-- Step 3a: the half-period is never a lattice point. -/
theorem mphi_wE_halfPeriod_sub_latPt_ne (j : Fin 3) (v : Fin 2 → ℤ) {w : ℂ} (hw : 0 < w.im) :
    mphi_wE_halfPeriod j w - mphi_wE_latPt v w ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  have odd_half : ∀ n : ℤ, (2 : ℝ) * n - 1 ≠ 0 := fun n hn => by
    have : (2 : ℤ) * n = 1 := by exact_mod_cast (sub_eq_zero.mp hn)
    omega
  fin_cases j <;> simp [mphi_wE_halfPeriod, mphi_wE_latPt] at hre him
  · rcases him with h0 | h0
    · simp [h0] at hre
      exact odd_half (v 1) (by linarith)
    · linarith
  · have : ((2 : ℝ) * v 0 - 1) * w.im = 0 := by linear_combination (-2 : ℝ) * him
    rcases mul_eq_zero.mp this with h | h
    · exact odd_half _ h
    · linarith
  · have : ((2 : ℝ) * v 0 - 1) * w.im = 0 := by linear_combination (-2 : ℝ) * him
    rcases mul_eq_zero.mp this with h | h
    · exact odd_half _ h
    · linarith

/-- Step 3b: each summand is holomorphic on `ℍ`. -/
theorem mphi_wE_summand_differentiableOn (j : Fin 3) (v : Fin 2 → ℤ) :
    DifferentiableOn ℂ (mphi_wE_summand j v) {w : ℂ | 0 < w.im} := by
  have hhp : Differentiable ℂ (fun w => mphi_wE_halfPeriod j w) := by
    fin_cases j <;> (simp [mphi_wE_halfPeriod]; try fun_prop)
  have h1 : DifferentiableOn ℂ (fun w => 1 / (mphi_wE_halfPeriod j w - mphi_wE_latPt v w) ^ 2)
      {w : ℂ | 0 < w.im} := by
    refine DifferentiableOn.div (differentiableOn_const 1) ?_
      (fun w hw => pow_ne_zero 2 (mphi_wE_halfPeriod_sub_latPt_ne j v hw))
    unfold mphi_wE_latPt
    fun_prop
  have h2 : DifferentiableOn ℂ (fun w => 1 / mphi_wE_latPt v w ^ 2) {w : ℂ | 0 < w.im} := by
    refine (EisensteinSeries.div_linear_zpow_differentiableOn 2 v).congr fun w _ => ?_
    simp [mphi_wE_latPt, zpow_neg, one_div]
  exact h1.sub h2

/-- Step 4: size of the half-period. -/
theorem mphi_norm_wE_halfPeriod_le (j : Fin 3) (w : ℂ) :
    ‖mphi_wE_halfPeriod j w‖ ≤ (1 + ‖w‖) / 2 := by
  have h0 := norm_nonneg w
  fin_cases j <;> simp [mphi_wE_halfPeriod]
  · linarith
  · linarith
  · have := norm_add_le (1 : ℂ) w
    rw [norm_one] at this
    linarith

/-- Step 5: the uniform tail bound on the ball `B(w₀, Im w₀ / 2)`, cofinitely in `v`. -/
theorem mphi_wE_summand_bound {w0 : ℂ} (hw0 : 0 < w0.im) (j : Fin 3) :
    ∀ᶠ v in cofinite, ∀ w ∈ Metric.ball w0 (w0.im / 2),
      ‖mphi_wE_summand j v w‖ ≤ 10 * (‖w0‖ + w0.im / 2 + 1) *
        (EisensteinSeries.r ⟨⟨|w0.re| + w0.im / 2, w0.im / 2⟩, by positivity⟩ ^ (-3 : ℝ) *
          ‖v‖ ^ (-3 : ℝ)) := by
  set ρ := w0.im / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  set r0 := EisensteinSeries.r ⟨⟨|w0.re| + ρ, ρ⟩, hρ0⟩ with hr0def
  have hr0 : 0 < r0 := EisensteinSeries.r_pos _
  set R := ‖w0‖ + ρ + 1 with hRdef
  have hR : 0 < R := by positivity
  have hcof : ∀ᶠ v : Fin 2 → ℤ in cofinite, 2 * R / r0 ≤ ‖v‖ :=
    (tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding
      Topology.IsClosedEmbedding.id).eventually_ge_atTop _
  filter_upwards [hcof] with v hv w hw
  have hww0 : ‖w - w0‖ < ρ := by simpa [dist_eq_norm] using hw
  have him : ρ < w.im := by
    have h1 := Complex.abs_im_le_norm (w - w0)
    rw [Complex.sub_im] at h1
    have := (abs_lt.mp (h1.trans_lt hww0)).1
    linarith
  have hre : |w.re| ≤ |w0.re| + ρ := by
    have h1 := Complex.abs_re_le_norm (w - w0)
    rw [Complex.sub_re] at h1
    have h2 := abs_sub_abs_le_abs_sub w.re w0.re
    linarith
  have hnorm : ‖w‖ ≤ ‖w0‖ + ρ := by
    have := norm_sub_norm_le w w0
    linarith
  have hwpos : 0 < w.im := hρ0.trans him
  let wH : UpperHalfPlane := ⟨w, hwpos⟩
  have hstrip : wH ∈ UpperHalfPlane.verticalStrip (|w0.re| + ρ) ρ := ⟨hre, him.le⟩
  have hrr : r0 ≤ EisensteinSeries.r wH :=
    EisensteinSeries.r_lower_bound_on_verticalStrip wH hρ0 hstrip
  have hlat : r0 * ‖v‖ ≤ ‖mphi_wE_latPt v w‖ :=
    (mul_le_mul_of_nonneg_right hrr (norm_nonneg _)).trans (mphi_wE_latPt_lower wH v)
  have h2R : 2 * R ≤ r0 * ‖v‖ := by
    have := (div_le_iff₀ hr0).mp hv
    linarith [mul_comm r0 ‖v‖]
  have hs : ‖mphi_wE_halfPeriod j w‖ < R := by
    have := mphi_norm_wE_halfPeriod_le j w
    linarith
  have hb := PeriodPair.weierstrassP_bound R hR (mphi_wE_halfPeriod j w) hs (mphi_wE_latPt v w)
    (h2R.trans hlat)
  have hpos : 0 < r0 * ‖v‖ := by linarith
  calc ‖mphi_wE_summand j v w‖ ≤ 10 * R * ‖mphi_wE_latPt v w‖ ^ (-3 : ℝ) := hb
    _ ≤ 10 * R * (r0 * ‖v‖) ^ (-3 : ℝ) := by
        gcongr 10 * R * ?_
        exact Real.rpow_le_rpow_of_nonpos hpos hlat (by norm_num)
    _ = 10 * R * (r0 ^ (-3 : ℝ) * ‖v‖ ^ (-3 : ℝ)) := by
        rw [Real.mul_rpow hr0.le (norm_nonneg _)]

/-- **W2**: `w ↦ e_j(w)` is holomorphic on the upper half-plane. -/
theorem mphi_differentiableOn_weierstrassE (j : Fin 3) :
    DifferentiableOn ℂ (fun w => weierstrassE w j) {w : ℂ | 0 < w.im} := by
  intro w0 hw0
  have hw0' : 0 < w0.im := hw0
  refine DifferentiableAt.differentiableWithinAt ?_
  have hρ0 : 0 < w0.im / 2 := by positivity
  have hU : IsOpen (Metric.ball w0 (w0.im / 2)) := Metric.isOpen_ball
  have hUH : Metric.ball w0 (w0.im / 2) ⊆ {w : ℂ | 0 < w.im} := by
    intro w hw
    have hww0 : ‖w - w0‖ < w0.im / 2 := by simpa [dist_eq_norm] using hw
    have h1 := Complex.abs_im_le_norm (w - w0)
    rw [Complex.sub_im] at h1
    have := (abs_lt.mp (h1.trans_lt hww0)).1
    show 0 < w.im
    linarith
  have hsum : Summable fun v : Fin 2 → ℤ => 10 * (‖w0‖ + w0.im / 2 + 1) *
      (EisensteinSeries.r ⟨⟨|w0.re| + w0.im / 2, w0.im / 2⟩, hρ0⟩ ^ (-3 : ℝ) * ‖v‖ ^ (-3 : ℝ)) :=
    ((EisensteinSeries.summable_one_div_norm_rpow (by norm_num : (2 : ℝ) < 3)).mul_left
      _).mul_left _
  have hTU := tendstoUniformlyOn_tsum_of_cofinite_eventually hsum (mphi_wE_summand_bound hw0' j)
  have hdiff : DifferentiableOn ℂ (fun w => ∑' v, mphi_wE_summand j v w)
      (Metric.ball w0 (w0.im / 2)) :=
    hTU.tendstoLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall fun s => DifferentiableOn.fun_sum fun v _ =>
        (mphi_wE_summand_differentiableOn j v).mono hUH) hU
  have heq : ∀ w ∈ Metric.ball w0 (w0.im / 2), weierstrassE w j = ∑' v, mphi_wE_summand j v w :=
    fun w hw => mphi_weierstrassE_eq_tsum_summand j (hUH hw)
  exact (hdiff.congr heq).differentiableAt (hU.mem_nhds (Metric.mem_ball_self hρ0))

/-- `modularPhi` is holomorphic wherever the denominator `e₃ - e₂` does not vanish. -/
theorem mphi_differentiableOn_modularPhi {U : Set ℂ} (hU : U ⊆ {w : ℂ | 0 < w.im})
    (hne : ∀ w ∈ U, weierstrassE w 2 - weierstrassE w 1 ≠ 0) :
    DifferentiableOn ℂ modularPhi U := by
  have h := fun j => (mphi_differentiableOn_weierstrassE j).mono hU
  exact ((h 2).sub (h 0)).div ((h 2).sub (h 1)) hne

/-- `w ↦ e_j(w)` is holomorphic on `upperHalf`. -/
theorem mphi_differentiableOn_weierstrassE_upperHalf (j : Fin 3) :
    DifferentiableOn ℂ (fun w => weierstrassE w j) upperHalf :=
  mphi_differentiableOn_weierstrassE j

/-- `w ↦ e_j(w)` is analytic on `upperHalf`. -/
theorem mphi_analyticOnNhd_weierstrassE (j : Fin 3) :
    AnalyticOnNhd ℂ (fun w => weierstrassE w j) upperHalf :=
  (mphi_differentiableOn_weierstrassE j).analyticOnNhd isOpen_upperHalf

/-! ### Asymptotics at the cusps of `A` (`mphi_`)

With `q = e^{iπw}` the rows of `e₃ - e₂` are `τ(q^{k_n})` and those of `e₁ - e₂` are
`σ(q^{2|n|}) - ρ(q^{k_n})`, so `e₃ - e₂ = q G(q)` and `e₁ - e₂ = F(q)` with `F, G` holomorphic on
the unit disc, `G(0) = 16π²`, `F(0) = ∑_m 1/(m + 1/2)²`.  Hence `φ e^{iπw} → -F(0)/(16π²)` and
`φ'/φ → -iπ` as `Im w → ∞`; the cusps `0` and `1` are reduced to `∞` by `w ↦ -1/w` and
`w ↦ w - 1`. -/

/-! #### Row terms as a function of `q = e^{iπw}` -/

/-- `τ₀(y) = 4π² (1/(1 + y)² + 1/(1 - y)²)`. -/
def mphi_tau0 (y : ℂ) : ℂ := 4 * (π : ℂ) ^ 2 * (1 / (1 + y) ^ 2 + 1 / (1 - y) ^ 2)

/-- `τ(y) = y τ₀(y)`: the row difference `mphi_rowS (1/2 + ζ) - mphi_rowS ζ` as a function of
`y = e^{2πiζ}`. -/
def mphi_tau (y : ℂ) : ℂ := y * mphi_tau0 y

/-- For `Im ζ > 0`: `mphi_rowS (1/2 + ζ) - mphi_rowS ζ = τ(e^{2πiζ})`. -/
theorem mphi_rowDiff_of_im_pos {ζ : ℂ} (hζ : 0 < ζ.im) :
    mphi_rowS (1 / 2 + ζ) - mphi_rowS ζ = mphi_tau (cexp (2 * π * I * ζ)) := by
  have h1 : 0 < (1 / 2 + ζ).im := by simpa using hζ
  have hy : cexp (2 * π * I * (1 / 2 + ζ)) = -cexp (2 * π * I * ζ) := by
    rw [show 2 * π * I * (1 / 2 + ζ) = π * I + 2 * π * I * ζ by ring, Complex.exp_add,
      Complex.exp_pi_mul_I]
    ring
  rw [mphi_rowS_eq_of_im_pos h1, mphi_rowS_eq_of_im_pos hζ, hy, mphi_tau, mphi_tau0]
  ring

/-- For `Im ζ < 0`: `mphi_rowS (1/2 + ζ) - mphi_rowS ζ = τ(e^{-2πiζ})`. -/
theorem mphi_rowDiff_of_im_neg {ζ : ℂ} (hζ : ζ.im < 0) :
    mphi_rowS (1 / 2 + ζ) - mphi_rowS ζ = mphi_tau (cexp (2 * π * I * (-ζ))) := by
  have h1 : mphi_rowS (1 / 2 + ζ) = mphi_rowS (1 / 2 + -ζ) := by
    rw [← mphi_rowS_neg, ← mphi_rowS_add_one]
    congr 1
    ring
  rw [h1, ← mphi_rowS_neg ζ, mphi_rowDiff_of_im_pos (by simpa using hζ)]

/-- `k_n = |2n - 1|`: the `n`-th row of `e₃ - e₂` is `τ(q^{k_n})`, `q = e^{iπw}`. -/
def mphi_kIdx (n : ℤ) : ℕ := (2 * n - 1).natAbs

/-- `k_n = 1 - 2n` for `n ≤ 0`. -/
theorem mphi_kIdx_cast_of_nonpos {n : ℤ} (hn : n ≤ 0) : (mphi_kIdx n : ℂ) = 1 - 2 * n := by
  have : ((mphi_kIdx n : ℕ) : ℤ) = 1 - 2 * n := by
    rw [mphi_kIdx, Int.natCast_natAbs, abs_of_neg (by omega)]
    ring
  exact_mod_cast this

/-- `k_n = 2n - 1` for `n > 0`. -/
theorem mphi_kIdx_cast_of_pos {n : ℤ} (hn : 0 < n) : (mphi_kIdx n : ℂ) = 2 * n - 1 := by
  have : ((mphi_kIdx n : ℕ) : ℤ) = 2 * n - 1 := by
    rw [mphi_kIdx, Int.natCast_natAbs, abs_of_pos (by omega)]
  exact_mod_cast this

/-- The `n`-th row of `e₃ - e₂` is `τ(q^{k_n})`, `q = e^{iπw}`. -/
theorem mphi_rowTerm_eq {w : ℂ} (hw : 0 < w.im) (n : ℤ) :
    mphi_rowS ((1 + w) / 2 - n * w) - mphi_rowS (w / 2 - n * w) =
      mphi_tau (cexp (π * I * w) ^ mphi_kIdx n) := by
  rcases le_or_gt n 0 with hn | hn
  · have hζ : 0 < ((1 / 2 - (n : ℂ)) * w).im := by
      have : ((1 / 2 - (n : ℂ)) * w).im = (1 / 2 - n) * w.im := by simp
      rw [this]
      have : (n : ℝ) ≤ 0 := by exact_mod_cast hn
      nlinarith
    have := mphi_rowDiff_of_im_pos hζ
    rw [show (1 + w) / 2 - n * w = 1 / 2 + (1 / 2 - (n : ℂ)) * w by ring,
      show w / 2 - n * w = (1 / 2 - (n : ℂ)) * w by ring, this, ← Complex.exp_nat_mul,
      mphi_kIdx_cast_of_nonpos hn]
    congr 2
    ring
  · have hζ : ((1 / 2 - (n : ℂ)) * w).im < 0 := by
      have : ((1 / 2 - (n : ℂ)) * w).im = (1 / 2 - n) * w.im := by simp
      rw [this]
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have := mphi_rowDiff_of_im_neg hζ
    rw [show (1 + w) / 2 - n * w = 1 / 2 + (1 / 2 - (n : ℂ)) * w by ring,
      show w / 2 - n * w = (1 / 2 - (n : ℂ)) * w by ring, this, ← Complex.exp_nat_mul,
      mphi_kIdx_cast_of_pos hn]
    congr 2
    ring

/-- `e₃(w) - e₂(w) = ∑_{n ∈ ℤ} τ(q^{k_n})`, `q = e^{iπw}`. -/
theorem mphi_e32_hasSum {w : ℂ} (hw : 0 < w.im) :
    HasSum (fun n : ℤ => mphi_tau (cexp (π * I * w) ^ mphi_kIdx n))
      (weierstrassE w 2 - weierstrassE w 1) := by
  rw [weierstrassE_two_eq hw, weierstrassE_one_eq hw]
  have h := mphi_wp_sub_hasSum_rows hw ((1 + w) / 2) (w / 2)
  simp only [mphi_rowTerm_eq hw] at h
  exact h

/-! #### Bounds -/

/-- `‖τ₀(y)‖ ≤ 32π²` for `‖y‖ ≤ 1/2`. -/
theorem mphi_norm_tau0_le {y : ℂ} (hy : ‖y‖ ≤ 1 / 2) : ‖mphi_tau0 y‖ ≤ 32 * π ^ 2 := by
  have h1 : 1 / 2 ≤ ‖1 + y‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-y)
    simp only [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  have h2 : 1 / 2 ≤ ‖1 - y‖ := by
    have := norm_sub_norm_le (1 : ℂ) y
    simp only [norm_one] at this
    linarith
  have e1 : ‖1 / (1 + y) ^ 2‖ ≤ 4 := by
    rw [norm_div, norm_one, norm_pow, div_le_iff₀ (by positivity)]
    nlinarith
  have e2 : ‖1 / (1 - y) ^ 2‖ ≤ 4 := by
    rw [norm_div, norm_one, norm_pow, div_le_iff₀ (by positivity)]
    nlinarith
  unfold mphi_tau0
  rw [norm_mul]
  have : ‖(4 : ℂ) * (π : ℂ) ^ 2‖ = 4 * π ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [this]
  have := norm_add_le (1 / (1 + y) ^ 2) (1 / (1 - y) ^ 2)
  have hπ : 0 < π ^ 2 := by positivity
  nlinarith

/-- `τ₀(y) → 8π²` as `y → 0`. -/
theorem mphi_tendsto_tau0_zero : Tendsto mphi_tau0 (𝓝 0) (𝓝 (8 * (π : ℂ) ^ 2)) := by
  have hc : ContinuousAt mphi_tau0 0 := by
    unfold mphi_tau0
    fun_prop (disch := norm_num)
  have : mphi_tau0 0 = 8 * (π : ℂ) ^ 2 := by unfold mphi_tau0; ring
  rw [← this]
  exact hc.tendsto

/-! #### `q → 0` at `∞` -/

/-- `‖e^{iπw}‖ = e^{-π Im w}`. -/
theorem mphi_norm_q (w : ℂ) : ‖cexp (π * I * w)‖ = Real.exp (-π * w.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp

/-- `q = e^{iπw} → 0` as `Im w → ∞`. -/
theorem mphi_tendsto_q :
    Tendsto (fun w : ℂ => cexp (π * I * w)) (comap Complex.im atTop) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [mphi_norm_q]
  have : Tendsto (fun w : ℂ => -π * w.im) (comap Complex.im atTop) atBot := by
    have h : Tendsto (fun w : ℂ => π * w.im) (comap Complex.im atTop) atTop :=
      tendsto_comap.const_mul_atTop Real.pi_pos
    have h2 := tendsto_neg_atTop_atBot.comp h
    refine h2.congr fun w => ?_
    simp only [Function.comp_apply]
    ring
  exact Real.tendsto_exp_atBot.comp this

/-! #### Tannery -/

/-- The limits of the rows of `(e₃ - e₂)/q` as `q → 0`: `8π²` for `n = 0, 1`, else `0`. -/
def mphi_gLim (n : ℤ) : ℂ := if n = 0 ∨ n = 1 then 8 * (π : ℂ) ^ 2 else 0

/-- `∑_n mphi_gLim n = 16π²`. -/
theorem mphi_tsum_gLim : ∑' n : ℤ, mphi_gLim n = 16 * (π : ℂ) ^ 2 := by
  rw [tsum_eq_sum (s := {0, 1})]
  · simp [mphi_gLim]
    ring
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [mphi_gLim, hn.1, hn.2]

/-- `k_n ≥ 1`. -/
theorem mphi_kIdx_pos (n : ℤ) : 1 ≤ mphi_kIdx n := by
  unfold mphi_kIdx
  omega

/-- `|n| ≤ k_n`. -/
theorem mphi_natAbs_le_kIdx (n : ℤ) : n.natAbs ≤ mphi_kIdx n := by
  unfold mphi_kIdx
  omega

/-- `k_n = 1` exactly for `n = 0, 1`. -/
theorem mphi_kIdx_eq_one_iff (n : ℤ) : mphi_kIdx n = 1 ↔ (n = 0 ∨ n = 1) := by
  unfold mphi_kIdx
  omega

/-- `∑_{n ∈ ℤ} r^|n|` converges for `0 ≤ r < 1`. -/
theorem mphi_summable_pow_natAbs {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℤ => r ^ n.natAbs := by
  apply Summable.of_nat_of_neg_add_one
  · simpa using summable_geometric_of_lt_one hr0 hr1
  · have h := (summable_geometric_of_lt_one hr0 hr1).mul_left r
    refine h.congr fun n => ?_
    have : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    rw [this, pow_succ]
    ring

/-- `∑_{n ∈ ℤ} (1/2)^|n|` converges. -/
theorem mphi_summable_half_pow_natAbs :
    Summable fun n : ℤ => (1 / 2 : ℝ) ^ n.natAbs :=
  mphi_summable_pow_natAbs (by norm_num) (by norm_num)

/-- `τ(q^k)/q = q^{k-1} τ₀(q^k)`. -/
theorem mphi_tau_pow_div {q : ℂ} (hq : q ≠ 0) {k : ℕ} (hk : 1 ≤ k) :
    mphi_tau (q ^ k) / q = q ^ (k - 1) * mphi_tau0 (q ^ k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [mphi_tau, show j + 1 - 1 = j by omega, pow_succ]
  field_simp

/-- (∞) for `e₃ - e₂`: `(e₃(w) - e₂(w))/e^{iπw} → 16π²` as `Im w → ∞`, uniformly in `Re w`
(Tannery's theorem). -/
theorem mphi_e32_div_q_tendsto :
    Tendsto (fun w => (weierstrassE w 2 - weierstrassE w 1) /
      cexp (π * I * w)) (comap Complex.im atTop) (𝓝 (16 * (π : ℂ) ^ 2)) := by
  set F : Filter ℂ := comap Complex.im atTop with hF
  have hq := mphi_tendsto_q
  have hq0 : ∀ w : ℂ, cexp (π * I * w) ≠ 0 := fun w => Complex.exp_ne_zero _
  have hev_pos : ∀ᶠ w in F, 0 < w.im := tendsto_comap.eventually (eventually_gt_atTop 0)
  have hev_small : ∀ᶠ w in F, ‖cexp (π * I * w)‖ ≤ 1 / 2 := by
    have h := hq.norm
    rw [norm_zero] at h
    exact (h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun w hw => hw.le
  have hrepr : ∀ᶠ w in F, ∑' n : ℤ, mphi_tau (cexp (π * I * w) ^ mphi_kIdx n) / cexp (π * I * w) =
      (weierstrassE w 2 - weierstrassE w 1) / cexp (π * I * w) := by
    filter_upwards [hev_pos] with w hw
    rw [← (mphi_e32_hasSum hw).tsum_eq, tsum_div_const]
  have key : Tendsto
      (fun w => ∑' n : ℤ, mphi_tau (cexp (π * I * w) ^ mphi_kIdx n) / cexp (π * I * w)) F
      (𝓝 (∑' n : ℤ, mphi_gLim n)) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun n : ℤ => 64 * π ^ 2 * (1 / 2 : ℝ) ^ n.natAbs)
      (mphi_summable_half_pow_natAbs.mul_left _) (fun n => ?_) ?_
    · -- pointwise limits
      have hk := mphi_kIdx_pos n
      have h1 : ∀ w : ℂ, mphi_tau (cexp (π * I * w) ^ mphi_kIdx n) / cexp (π * I * w) =
          cexp (π * I * w) ^ (mphi_kIdx n - 1) * mphi_tau0 (cexp (π * I * w) ^ mphi_kIdx n) :=
        fun w => mphi_tau_pow_div (hq0 w) hk
      simp only [h1]
      have hpow : Tendsto (fun w => cexp (π * I * w) ^ mphi_kIdx n) F (𝓝 0) := by
        simpa [zero_pow (by omega : mphi_kIdx n ≠ 0)] using hq.pow (mphi_kIdx n)
      have ht := mphi_tendsto_tau0_zero.comp hpow
      by_cases hn : n = 0 ∨ n = 1
      · have hk1 : mphi_kIdx n = 1 := (mphi_kIdx_eq_one_iff n).mpr hn
        simp only [mphi_gLim, hn, ite_true]
        simp only [hk1, Nat.sub_self, pow_zero, one_mul]
        have ht1 : Tendsto (fun w => mphi_tau0 (cexp (π * I * w) ^ mphi_kIdx n)) F
            (𝓝 (8 * (π : ℂ) ^ 2)) := ht
        rw [hk1] at ht1
        exact ht1
      · have hk2 : 1 ≤ mphi_kIdx n - 1 := by
          have := (mphi_kIdx_eq_one_iff n).not.mpr hn
          omega
        simp only [mphi_gLim, hn, ite_false]
        have hp : Tendsto (fun w => cexp (π * I * w) ^ (mphi_kIdx n - 1)) F (𝓝 0) := by
          simpa [zero_pow (by omega : mphi_kIdx n - 1 ≠ 0)] using hq.pow (mphi_kIdx n - 1)
        simpa using hp.mul ht
    · -- the domination
      filter_upwards [hev_small] with w hw n
      have hk := mphi_kIdx_pos n
      rw [mphi_tau_pow_div (hq0 w) hk, norm_mul, norm_pow]
      have hqk : ‖cexp (π * I * w) ^ mphi_kIdx n‖ ≤ 1 / 2 := by
        rw [norm_pow]
        calc ‖cexp (π * I * w)‖ ^ mphi_kIdx n ≤ ‖cexp (π * I * w)‖ ^ 1 :=
              pow_le_pow_of_le_one (norm_nonneg _) (by linarith) hk
          _ ≤ 1 / 2 := by simpa using hw
      have hb := mphi_norm_tau0_le hqk
      have hp1 : ‖cexp (π * I * w)‖ ^ (mphi_kIdx n - 1) ≤ (1 / 2 : ℝ) ^ (mphi_kIdx n - 1) :=
        pow_le_pow_left₀ (norm_nonneg _) hw _
      have hp2 : (1 / 2 : ℝ) ^ (mphi_kIdx n - 1) ≤ 2 * (1 / 2 : ℝ) ^ n.natAbs := by
        have e : (1 / 2 : ℝ) ^ (mphi_kIdx n - 1) = 2 * (1 / 2 : ℝ) ^ mphi_kIdx n := by
          obtain ⟨j, hj⟩ : ∃ j, mphi_kIdx n = j + 1 := ⟨mphi_kIdx n - 1, by omega⟩
          rw [hj, show j + 1 - 1 = j by omega, pow_succ]
          ring
        rw [e]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) (mphi_natAbs_le_kIdx n)) (by norm_num)
      have hπ : 0 ≤ π ^ 2 := by positivity
      calc ‖cexp (π * I * w)‖ ^ (mphi_kIdx n - 1) * ‖mphi_tau0 (cexp (π * I * w) ^ mphi_kIdx n)‖
          ≤ (2 * (1 / 2 : ℝ) ^ n.natAbs) * (32 * π ^ 2) := by
            apply mul_le_mul (hp1.trans hp2) hb (norm_nonneg _) (by positivity)
        _ = 64 * π ^ 2 * (1 / 2 : ℝ) ^ n.natAbs := by ring
  rw [mphi_tsum_gLim] at key
  exact key.congr' hrepr

/-! #### `e₁ - e₂ → c₀ = ∑ 1/(m + 1/2)²` -/

/-- `σ(y) = 4π² y/(1 + y)²`: `mphi_rowS (1/2 + ζ) = σ(e^{2πiζ})` for `Im ζ > 0`. -/
def mphi_sig (y : ℂ) : ℂ := 4 * (π : ℂ) ^ 2 * (y / (1 + y) ^ 2)

/-- `ρ(y) = -4π² y/(1 - y)²`: `mphi_rowS ζ = ρ(e^{2πiζ})` for `Im ζ > 0`. -/
def mphi_rho (y : ℂ) : ℂ := -4 * (π : ℂ) ^ 2 * (y / (1 - y) ^ 2)

/-- For `Im ζ > 0`: `mphi_rowS (1/2 + ζ) = σ(e^{2πiζ})`. -/
theorem mphi_rowS_half_add_of_im_pos {ζ : ℂ} (hζ : 0 < ζ.im) :
    mphi_rowS (1 / 2 + ζ) = mphi_sig (cexp (2 * π * I * ζ)) := by
  have h1 : 0 < (1 / 2 + ζ).im := by simpa using hζ
  have hy : cexp (2 * π * I * (1 / 2 + ζ)) = -cexp (2 * π * I * ζ) := by
    rw [show 2 * π * I * (1 / 2 + ζ) = π * I + 2 * π * I * ζ by ring, Complex.exp_add,
      Complex.exp_pi_mul_I]
    ring
  rw [mphi_rowS_eq_of_im_pos h1, hy, mphi_sig]
  ring

/-- The `n`-th row of `e₁ - e₂`. -/
theorem mphi_rowTerm12_eq {w : ℂ} (hw : 0 < w.im) (n : ℤ) :
    mphi_rowS (1 / 2 - n * w) - mphi_rowS (w / 2 - n * w) =
      (if n = 0 then mphi_rowS (1 / 2) else mphi_sig (cexp (π * I * w) ^ (2 * n.natAbs))) -
        mphi_rho (cexp (π * I * w) ^ mphi_kIdx n) := by
  -- second part: `mphi_rowS ((1/2 - n) w) = ρ(q^{k_n})`
  have hB : mphi_rowS (w / 2 - n * w) = mphi_rho (cexp (π * I * w) ^ mphi_kIdx n) := by
    rcases le_or_gt n 0 with hn | hn
    · have hζ : 0 < ((1 / 2 - (n : ℂ)) * w).im := by
        have : ((1 / 2 - (n : ℂ)) * w).im = (1 / 2 - n) * w.im := by simp
        rw [this]
        have : (n : ℝ) ≤ 0 := by exact_mod_cast hn
        nlinarith
      rw [show w / 2 - n * w = (1 / 2 - (n : ℂ)) * w by ring, mphi_rowS_eq_of_im_pos hζ,
        ← Complex.exp_nat_mul, mphi_kIdx_cast_of_nonpos hn, mphi_rho]
      congr 3 <;> ring_nf
    · have hζ : 0 < (-((1 / 2 - (n : ℂ)) * w)).im := by
        have : (-((1 / 2 - (n : ℂ)) * w)).im = (n - 1 / 2) * w.im := by simp; ring
        rw [this]
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      rw [show w / 2 - n * w = (1 / 2 - (n : ℂ)) * w by ring, ← mphi_rowS_neg,
        mphi_rowS_eq_of_im_pos hζ, ← Complex.exp_nat_mul, mphi_kIdx_cast_of_pos hn, mphi_rho]
      congr 3 <;> ring_nf
  rw [hB]
  congr 1
  split_ifs with h0
  · subst h0
    simp
  · rcases lt_or_gt_of_ne h0 with hn | hn
    · have hζ : 0 < (-(n : ℂ) * w).im := by
        have : (-(n : ℂ) * w).im = -n * w.im := by simp
        rw [this]
        have : (n : ℝ) < 0 := by exact_mod_cast hn
        nlinarith
      rw [show 1 / 2 - n * w = 1 / 2 + (-(n : ℂ) * w) by ring, mphi_rowS_half_add_of_im_pos hζ,
        ← Complex.exp_nat_mul]
      have : ((2 * n.natAbs : ℕ) : ℂ) = -2 * n := by
        have h' : ((2 * n.natAbs : ℕ) : ℤ) = -2 * n := by
          push_cast
          rw [abs_of_neg hn]
          ring
        have h'' : ((2 * n.natAbs : ℕ) : ℂ) = (((2 * n.natAbs : ℕ) : ℤ) : ℂ) := by norm_cast
        rw [h'', h']
        push_cast
        ring
      rw [this]
      congr 2
      ring
    · have hζ : 0 < ((n : ℂ) * w).im := by
        have : ((n : ℂ) * w).im = n * w.im := by simp
        rw [this]
        have : (0 : ℝ) < n := by exact_mod_cast hn
        positivity
      rw [show 1 / 2 - n * w = -(-(1 / 2) + n * w) by ring, mphi_rowS_neg,
        show -(1 / 2) + (n : ℂ) * w = (1 / 2 + n * w) - 1 by ring]
      rw [← mphi_rowS_add_one (1 / 2 + (n : ℂ) * w - 1), sub_add_cancel,
        mphi_rowS_half_add_of_im_pos hζ, ← Complex.exp_nat_mul]
      have : ((2 * n.natAbs : ℕ) : ℂ) = 2 * n := by
        have h' : ((2 * n.natAbs : ℕ) : ℤ) = 2 * n := by
          push_cast
          rw [abs_of_pos hn]
        have h'' : ((2 * n.natAbs : ℕ) : ℂ) = (((2 * n.natAbs : ℕ) : ℤ) : ℂ) := by norm_cast
        rw [h'', h']
        push_cast
        ring
      rw [this]
      congr 2
      ring

/-- `e₁(w) - e₂(w)` summed row by row, in terms of `q = e^{iπw}`. -/
theorem mphi_e12_hasSum {w : ℂ} (hw : 0 < w.im) :
    HasSum (fun n : ℤ => (if n = 0 then mphi_rowS (1 / 2) else
        mphi_sig (cexp (π * I * w) ^ (2 * n.natAbs))) - mphi_rho (cexp (π * I * w) ^ mphi_kIdx n))
      (weierstrassE w 0 - weierstrassE w 1) := by
  rw [weierstrassE_zero_eq hw, weierstrassE_one_eq hw]
  have h := mphi_wp_sub_hasSum_rows hw (1 / 2) (w / 2)
  simp only [mphi_rowTerm12_eq hw] at h
  exact h

/-- `‖σ(y)‖ ≤ 16π² ‖y‖` for `‖y‖ ≤ 1/2`. -/
theorem mphi_norm_sig_le {y : ℂ} (hy : ‖y‖ ≤ 1 / 2) : ‖mphi_sig y‖ ≤ 16 * π ^ 2 * ‖y‖ := by
  have h1 : 1 / 2 ≤ ‖1 + y‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-y)
    simp only [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  unfold mphi_sig
  rw [norm_mul, norm_div, norm_pow]
  have : ‖(4 : ℂ) * (π : ℂ) ^ 2‖ = 4 * π ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [this, mul_div_assoc', div_le_iff₀ (by positivity)]
  have hπ : 0 < π ^ 2 := by positivity
  have h4 : (1 / 4 : ℝ) ≤ ‖1 + y‖ ^ 2 := by nlinarith
  have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 16 * π ^ 2 * ‖y‖)
  nlinarith [norm_nonneg y]

/-- `‖ρ(y)‖ ≤ 16π² ‖y‖` for `‖y‖ ≤ 1/2`. -/
theorem mphi_norm_rho_le {y : ℂ} (hy : ‖y‖ ≤ 1 / 2) : ‖mphi_rho y‖ ≤ 16 * π ^ 2 * ‖y‖ := by
  have h1 : 1 / 2 ≤ ‖1 - y‖ := by
    have := norm_sub_norm_le (1 : ℂ) y
    simp only [norm_one] at this
    linarith
  unfold mphi_rho
  rw [norm_mul, norm_div, norm_pow]
  have : ‖(-4 : ℂ) * (π : ℂ) ^ 2‖ = 4 * π ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [this, mul_div_assoc', div_le_iff₀ (by positivity)]
  have hπ : 0 < π ^ 2 := by positivity
  have h4 : (1 / 4 : ℝ) ≤ ‖1 - y‖ ^ 2 := by nlinarith
  have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 16 * π ^ 2 * ‖y‖)
  nlinarith [norm_nonneg y]

/-- `e₁(w) - e₂(w) → mphi_rowS (1/2)` as `Im w → ∞`, uniformly in `Re w` (Tannery's theorem). -/
theorem mphi_e12_tendsto :
    Tendsto (fun w => weierstrassE w 0 - weierstrassE w 1)
      (comap Complex.im atTop) (𝓝 (mphi_rowS (1 / 2))) := by
  set F : Filter ℂ := comap Complex.im atTop with hF
  have hq := mphi_tendsto_q
  have hev_pos : ∀ᶠ w in F, 0 < w.im := tendsto_comap.eventually (eventually_gt_atTop 0)
  have hev_small : ∀ᶠ w in F, ‖cexp (π * I * w)‖ ≤ 1 / 2 := by
    have h := hq.norm
    rw [norm_zero] at h
    exact (h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun w hw => hw.le
  set g : ℤ → ℂ := fun n => if n = 0 then mphi_rowS (1 / 2) else 0 with hg
  have hsum_g : ∑' n, g n = mphi_rowS (1 / 2) := by
    rw [tsum_eq_single 0]
    · simp [hg]
    · intro n hn
      simp [hg, hn]
  have key : Tendsto (fun w => ∑' n : ℤ, ((if n = 0 then mphi_rowS (1 / 2) else
      mphi_sig (cexp (π * I * w) ^ (2 * n.natAbs))) - mphi_rho (cexp (π * I * w) ^ mphi_kIdx n))) F
      (𝓝 (∑' n, g n)) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun n : ℤ => (if n = 0 then ‖mphi_rowS (1 / 2)‖ else 0) +
        32 * π ^ 2 * (1 / 2 : ℝ) ^ n.natAbs)
      ?_ (fun n => ?_) ?_
    · refine Summable.add ?_ (mphi_summable_half_pow_natAbs.mul_left _)
      exact summable_of_hasFiniteSupport ((Set.finite_singleton (0 : ℤ)).subset
        (fun n hn => by
          rw [Set.mem_singleton_iff]
          by_contra h
          exact hn (by simp [h])))
    · have hrho : Tendsto (fun w => mphi_rho (cexp (π * I * w) ^ mphi_kIdx n)) F (𝓝 0) := by
        have hpow : Tendsto (fun w => cexp (π * I * w) ^ mphi_kIdx n) F (𝓝 0) := by
          simpa [zero_pow (by have := mphi_kIdx_pos n; omega : mphi_kIdx n ≠ 0)] using
            hq.pow (mphi_kIdx n)
        have hc : ContinuousAt mphi_rho 0 := by unfold mphi_rho; fun_prop (disch := norm_num)
        have := hc.tendsto.comp hpow
        have h0' : mphi_rho 0 = 0 := by simp [mphi_rho]
        rw [h0'] at this
        exact this
      by_cases h0 : n = 0
      · subst h0
        simp only [ite_true, hg]
        have := (tendsto_const_nhds (x := mphi_rowS (1 / 2))).sub hrho
        rw [sub_zero] at this
        exact this
      · simp only [h0, ite_false, hg]
        have hpow : Tendsto (fun w => cexp (π * I * w) ^ (2 * n.natAbs)) F (𝓝 0) := by
          simpa [zero_pow (by omega : 2 * n.natAbs ≠ 0)] using hq.pow (2 * n.natAbs)
        have hc : ContinuousAt mphi_sig 0 := by unfold mphi_sig; fun_prop (disch := norm_num)
        have hs := hc.tendsto.comp hpow
        simp only [mphi_sig, zero_div, mul_zero] at hs
        simpa using hs.sub hrho
    · filter_upwards [hev_small] with w hw n
      have hqk : ∀ k : ℕ, ‖cexp (π * I * w) ^ k‖ ≤ (1 / 2 : ℝ) ^ k := fun k => by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hw _
      have hk := mphi_kIdx_pos n
      have hhalf : ∀ k : ℕ, 1 ≤ k → (1 / 2 : ℝ) ^ k ≤ 1 / 2 := fun k hk' => by
        calc (1 / 2 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ 1 :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) hk'
          _ = 1 / 2 := by norm_num
      have hr := mphi_norm_rho_le ((hqk _).trans (hhalf _ hk))
      have hr2 : ‖mphi_rho (cexp (π * I * w) ^ mphi_kIdx n)‖ ≤
          16 * π ^ 2 * (1 / 2 : ℝ) ^ n.natAbs := by
        refine hr.trans (mul_le_mul_of_nonneg_left ((hqk _).trans ?_) (by positivity))
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (mphi_natAbs_le_kIdx n)
      have hπ : 0 ≤ π ^ 2 * (1 / 2 : ℝ) ^ n.natAbs := by positivity
      by_cases h0 : n = 0
      · simp only [h0, ite_true]
        refine (norm_sub_le _ _).trans ?_
        rw [h0] at hr2
        simp only [Int.natAbs_zero, pow_zero, mul_one] at hr2 ⊢
        nlinarith [Real.pi_pos]
      · simp only [h0, ite_false, zero_add]
        have h2 : 1 ≤ 2 * n.natAbs := by omega
        have hs := mphi_norm_sig_le ((hqk _).trans (hhalf _ h2))
        have hs2 : ‖mphi_sig (cexp (π * I * w) ^ (2 * n.natAbs))‖ ≤
            16 * π ^ 2 * (1 / 2 : ℝ) ^ n.natAbs := by
          refine hs.trans (mul_le_mul_of_nonneg_left ((hqk _).trans ?_) (by positivity))
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        refine (norm_sub_le _ _).trans ?_
        linarith
  rw [hsum_g] at key
  refine key.congr' ?_
  filter_upwards [hev_pos] with w hw
  exact (mphi_e12_hasSum hw).tsum_eq

/-- `c₀ = mphi_rowS (1/2)` is a positive real. -/
theorem mphi_rowS_half_pos : ∃ c : ℝ, 0 < c ∧ mphi_rowS (1 / 2) = c := by
  have hs := mphi_rowS_summable (1 / 2)
  have hterm : ∀ m : ℤ, (1 : ℂ) / (1 / 2 + m) ^ 2 = ((1 / (1 / 2 + m) ^ 2 : ℝ) : ℂ) := by
    intro m; push_cast; ring
  simp only [hterm] at hs
  have hr : Summable fun m : ℤ => (1 / (1 / 2 + m) ^ 2 : ℝ) := Complex.summable_ofReal.mp hs
  refine ⟨∑' m : ℤ, (1 / (1 / 2 + m) ^ 2 : ℝ), ?_, ?_⟩
  · exact hr.tsum_pos (fun m => by positivity) 0 (by norm_num)
  · rw [mphi_rowS, Complex.ofReal_tsum]
    exact tsum_congr hterm

/-- (∞): `φ(w) e^{iπw} → -c₀/(16π²)` as `Im w → ∞`, uniformly in `Re w`. -/
theorem mphi_modularPhi_mul_q_tendsto :
    Tendsto (fun w => modularPhi w * cexp (π * I * w)) (comap Complex.im atTop)
      (𝓝 (-(mphi_rowS (1 / 2)) / (16 * (π : ℂ) ^ 2))) := by
  have h32 := mphi_e32_div_q_tendsto
  have h12 := mphi_e12_tendsto
  have hq := mphi_tendsto_q
  have hne : (16 * (π : ℂ) ^ 2) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 this)
  have hlim : Tendsto (fun w => cexp (π * I * w) -
      (weierstrassE w 0 - weierstrassE w 1) /
        ((weierstrassE w 2 - weierstrassE w 1) / cexp (π * I * w)))
      (comap Complex.im atTop) (𝓝 (0 - mphi_rowS (1 / 2) / (16 * (π : ℂ) ^ 2))) :=
    hq.sub (h12.div h32 hne)
  rw [zero_sub, ← neg_div] at hlim
  refine hlim.congr' ?_
  have hev : ∀ᶠ w in comap Complex.im atTop,
      (weierstrassE w 2 - weierstrassE w 1) / cexp (π * I * w) ≠ 0 :=
    h32.eventually_ne hne
  filter_upwards [hev] with w hw
  have hq0 : cexp (π * I * w) ≠ 0 := Complex.exp_ne_zero _
  have h32' : weierstrassE w 2 - weierstrassE w 1 ≠ 0 := by
    intro h; apply hw; rw [h, zero_div]
  rw [modularPhi]
  field_simp
  ring

/-! #### `‖φ‖ → ∞` at `∞` and the fourth conjunct of `eq14_20` -/

/-- `‖φ(w)‖ → ∞` as `Im w → ∞`, uniformly in `Re w`. -/
theorem mphi_norm_modularPhi_tendsto_atTop :
    Tendsto (fun w => ‖modularPhi w‖) (comap Complex.im atTop) atTop := by
  obtain ⟨c, hc, hc'⟩ := mphi_rowS_half_pos
  have hL : 0 < ‖-(mphi_rowS (1 / 2)) / (16 * (π : ℂ) ^ 2)‖ := by
    rw [hc']
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    exact norm_pos_iff.mpr (div_ne_zero (neg_ne_zero.mpr hc0)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hπ)))
  have h1 := mphi_modularPhi_mul_q_tendsto.norm
  have h2 : Tendsto (fun w => ‖cexp (π * I * w)‖) (comap Complex.im atTop) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun w => norm_pos_iff.mpr
      (Complex.exp_ne_zero _)⟩
    simpa using mphi_tendsto_q.norm
  have h3 := h2.inv_tendsto_nhdsGT_zero
  have h4 := h1.pos_mul_atTop hL h3
  refine h4.congr fun w => ?_
  simp only [Pi.inv_apply]
  rw [norm_mul, mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)),
    mul_one]

/-- Fourth conjunct of `eq14_20`. -/
theorem mphi_norm_modularPhi_half_tendsto :
    Tendsto (fun v : ℝ => ‖modularPhi ((1 / 2 : ℂ) + v * I)‖) atTop atTop := by
  have hmap : Tendsto (fun v : ℝ => (1 / 2 : ℂ) + v * I) atTop (comap Complex.im atTop) := by
    rw [tendsto_comap_iff]
    refine tendsto_id.congr fun v => ?_
    simp
  exact mphi_norm_modularPhi_tendsto_atTop.comp hmap

/-! #### The cusps `0` and `1` -/

/-- Key inequality: if `0 < |s| < N = s² + v²` (`s` the distance of `Re` to the cusp),
`v > 0` and `N ≤ 1/4`, then `(v/N)² ≥ (3/4)/N`. -/
theorem mphi_cusp_ineq {s v : ℝ} (hv : 0 < v) (hs : |s| < s ^ 2 + v ^ 2)
    (hN : s ^ 2 + v ^ 2 ≤ 1 / 4) : 3 / 4 / (s ^ 2 + v ^ 2) ≤ (v / (s ^ 2 + v ^ 2)) ^ 2 := by
  set N := s ^ 2 + v ^ 2 with hNdef
  have hNpos : 0 < N := by positivity
  have hs2 : s ^ 2 < N ^ 2 := by
    have h0 : 0 ≤ |s| := abs_nonneg s
    have := mul_lt_mul'' hs hs h0 h0
    rw [← sq, sq_abs] at this
    nlinarith
  have hv2 : 3 / 4 * N ≤ v ^ 2 := by nlinarith
  rw [div_pow, le_div_iff₀ (by positivity), div_mul_eq_mul_div, div_le_iff₀ hNpos]
  nlinarith

/-- `Im(-1/ζ) = Im ζ / |ζ|²`. -/
theorem mphi_im_neg_one_div (ζ : ℂ) : (-1 / ζ).im = ζ.im / (ζ.re ^ 2 + ζ.im ^ 2) := by
  rw [Complex.div_im]
  simp only [Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, neg_zero,
    zero_mul, zero_div, zero_sub, Complex.normSq_apply]
  ring_nf

/-- Near a cusp: if `ζ → 0` with `Im ζ > 0` and `|Re ζ| < |ζ|²`, then `Im(-1/ζ) → ∞`. -/
theorem mphi_tendsto_neg_inv_of_cusp {S : Set ℂ}
    (hS : ∀ ζ ∈ S, 0 < ζ.im ∧ |ζ.re| < ζ.re ^ 2 + ζ.im ^ 2) :
    Tendsto (fun ζ : ℂ => -1 / ζ) (𝓝[S] 0) (comap Complex.im atTop) := by
  rw [tendsto_comap_iff, Filter.tendsto_atTop]
  intro M
  -- choose `δ` with `δ ≤ 1/2` and `3/(4δ²) ≥ M²`
  set δ : ℝ := min (1 / 2) (1 / (2 * (|M| + 1))) with hδ
  have hδpos : 0 < δ := by positivity
  have hball : Metric.ball (0 : ℂ) δ ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 hδpos
  filter_upwards [inter_mem_nhdsWithin S hball] with ζ ⟨hζS, hζB⟩
  obtain ⟨hv, hs⟩ := hS ζ hζS
  simp only [Function.comp_apply, mphi_im_neg_one_div]
  have hN : ζ.re ^ 2 + ζ.im ^ 2 < δ ^ 2 := by
    rw [Metric.mem_ball, dist_zero_right] at hζB
    have h := Complex.sq_norm ζ
    rw [Complex.normSq_apply] at h
    have : ‖ζ‖ ^ 2 < δ ^ 2 := by
      exact pow_lt_pow_left₀ hζB (norm_nonneg _) (by norm_num)
    nlinarith
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ 1 / (2 * (|M| + 1)) := min_le_right _ _
  have hN4 : ζ.re ^ 2 + ζ.im ^ 2 ≤ 1 / 4 := by nlinarith
  have key := mphi_cusp_ineq hv hs hN4
  set N := ζ.re ^ 2 + ζ.im ^ 2 with hNdef
  have hNpos : 0 < N := by positivity
  -- `(3/4)/N ≥ M²`
  have hM : M ^ 2 ≤ 3 / 4 / N := by
    rw [le_div_iff₀ hNpos]
    have h1 : δ * (2 * (|M| + 1)) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hδ2
      exact hδ2
    have h1' : 0 ≤ δ * (2 * (|M| + 1)) := by positivity
    have h2 : N * (4 * (|M| + 1) ^ 2) < 1 := by
      have : δ ^ 2 * (4 * (|M| + 1) ^ 2) ≤ 1 := by
        have := mul_le_mul h1 h1 h1' (by norm_num)
        nlinarith
      have hpos : 0 < 4 * (|M| + 1) ^ 2 := by positivity
      nlinarith
    have h3 : M ^ 2 ≤ (|M| + 1) ^ 2 := by
      have := sq_abs M
      nlinarith [abs_nonneg M]
    nlinarith
  have hq : 0 ≤ ζ.im / N := by positivity
  exact le_of_sq_le_sq (le_trans hM key) hq

/-- `φ → 0` at the cusp `0` (second conjunct of `eq14_20`). -/
theorem mphi_modularPhi_tendsto_zero :
    Tendsto modularPhi (𝓝[modularRegionA] 0) (𝓝 0) := by
  have hcusp : Tendsto (fun w : ℂ => -1 / w) (𝓝[modularRegionA] 0)
      (comap Complex.im atTop) := by
    refine mphi_tendsto_neg_inv_of_cusp fun w hw => ?_
    obtain ⟨hu, -, hd, hv⟩ := hw
    refine ⟨hv, ?_⟩
    rw [abs_of_pos hu]
    have h := Complex.sq_norm (w - 1 / 2)
    rw [Complex.normSq_apply] at h
    have h2 : (1 / 2 : ℝ) ^ 2 < ‖w - 1 / 2‖ ^ 2 := pow_lt_pow_left₀ hd (by norm_num) (by norm_num)
    simp only [Complex.sub_re, Complex.sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
      Complex.one_re, Complex.one_im] at h
    nlinarith
  have hn := (mphi_norm_modularPhi_tendsto_atTop.comp hcusp).inv_tendsto_atTop
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine hn.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  obtain ⟨-, -, -, hv⟩ := hw
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_im] at hv; exact lt_irrefl 0 hv
  have hτ : 0 < (-1 / w).im := by
    rw [mphi_im_neg_one_div]
    have : 0 < w.re ^ 2 + w.im ^ 2 := by positivity
    positivity
  have h12 := eq14_12 hτ
  rw [show -1 / (-1 / w) = w by field_simp] at h12
  simp only [Pi.inv_apply, Function.comp_apply]
  rw [h12, norm_div, norm_one, one_div]

/-- `φ → 1` at the cusp `1` (third conjunct of `eq14_20`). -/
theorem mphi_modularPhi_tendsto_one :
    Tendsto modularPhi (𝓝[modularRegionA] 1) (𝓝 1) := by
  -- the reflected region `S = A - 1`
  set S : Set ℂ := (fun w => w - 1) '' modularRegionA with hSdef
  have hS : ∀ ζ ∈ S, 0 < ζ.im ∧ |ζ.re| < ζ.re ^ 2 + ζ.im ^ 2 := by
    rintro _ ⟨w, ⟨-, hu1, hd, hv⟩, rfl⟩
    refine ⟨by simpa using hv, ?_⟩
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    rw [abs_of_neg (by linarith)]
    have h := Complex.sq_norm (w - 1 / 2)
    rw [Complex.normSq_apply] at h
    have h2 : (1 / 2 : ℝ) ^ 2 < ‖w - 1 / 2‖ ^ 2 := pow_lt_pow_left₀ hd (by norm_num) (by norm_num)
    simp only [Complex.sub_re, Complex.sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
      Complex.one_re, Complex.one_im] at h
    nlinarith
  have hshift : Tendsto (fun w : ℂ => w - 1) (𝓝[modularRegionA] 1) (𝓝[S] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun w hw => ⟨w, hw, rfl⟩⟩
    have : Tendsto (fun w : ℂ => w - 1) (𝓝 1) (𝓝 (1 - 1)) := tendsto_id.sub tendsto_const_nhds
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hcusp := (mphi_tendsto_neg_inv_of_cusp hS).comp hshift
  -- limits of `e₁ - e₂` and `e₃ - e₂` along `τ = -1/(w-1)`
  have h12 := mphi_e12_tendsto.comp hcusp
  have h32 : Tendsto (fun w => weierstrassE w 2 - weierstrassE w 1)
      (comap Complex.im atTop) (𝓝 0) := by
    have := mphi_e32_div_q_tendsto.mul mphi_tendsto_q
    rw [mul_zero] at this
    refine this.congr fun w => ?_
    rw [div_mul_cancel₀ _ (Complex.exp_ne_zero _)]
  have h32' := h32.comp hcusp
  obtain ⟨c, hc, hc'⟩ := mphi_rowS_half_pos
  have hc0 : mphi_rowS (1 / 2) ≠ 0 := by rw [hc']; exact_mod_cast hc.ne'
  have hlim := h12.div (h12.sub h32') (by rw [sub_zero]; exact hc0)
  rw [sub_zero, div_self hc0] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  obtain ⟨-, -, -, hv⟩ := hw
  simp only [Pi.div_apply, Function.comp_apply]
  rw [show modularPhi w = modularPhi ((w - 1) + 1) by ring_nf]
  set ζ := w - 1 with hζ
  have hζim : 0 < ζ.im := by simpa [hζ] using hv
  have hζ0 : ζ ≠ 0 := fun h => by rw [h, Complex.zero_im] at hζim; exact lt_irrefl 0 hζim
  set τ := -1 / ζ with hτ
  have hτim : 0 < τ.im := by
    rw [hτ, mphi_im_neg_one_div]
    have : 0 < ζ.re ^ 2 + ζ.im ^ 2 := by positivity
    positivity
  have hτ0 : τ ≠ 0 := fun h => by rw [h, Complex.zero_im] at hτim; exact lt_irrefl 0 hτim
  have hζτ : -1 / τ = ζ := by rw [hτ]; field_simp
  obtain ⟨a0, a1, a2⟩ := mphi_weierstrassE_add_one hζim
  obtain ⟨b0, b1, b2⟩ := mphi_weierstrassE_neg_inv hτim
  rw [hζτ] at b0 b1 b2
  rw [modularPhi, a0, a1, a2, b0, b1, b2]
  have hτ2 : τ ^ 2 ≠ 0 := pow_ne_zero 2 hτ0
  rw [← mul_sub, ← mul_sub, mul_div_mul_left _ _ hτ2]
  congr 1
  ring

/-! #### `G(q) = ∑ q^{k_n - 1} τ₀(q^{k_n})`, holomorphic on the unit disc -/

/-- `G(q) = ∑_n q^{k_n - 1} τ₀(q^{k_n})`, so that `e₃ - e₂ = q G(q)`. -/
def mphi_Gq (q : ℂ) : ℂ := ∑' n : ℤ, q ^ (mphi_kIdx n - 1) * mphi_tau0 (q ^ mphi_kIdx n)

/-- `e₃ - e₂ = q G(q)`. -/
theorem mphi_e32_eq_q_mul_G {w : ℂ} (hw : 0 < w.im) :
    weierstrassE w 2 - weierstrassE w 1 =
      cexp (π * I * w) * mphi_Gq (cexp (π * I * w)) := by
  have hq0 := Complex.exp_ne_zero (π * I * w)
  rw [← (mphi_e32_hasSum hw).tsum_eq, mphi_Gq, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [← mphi_tau_pow_div hq0 (mphi_kIdx_pos n)]
  field_simp

/-- `‖τ₀(y)‖ ≤ 8π²/(1 - r)²` for `‖y‖ ≤ r < 1`. -/
theorem mphi_norm_tau0_le_r {r : ℝ} (hr1 : r < 1) {y : ℂ} (hy : ‖y‖ ≤ r) :
    ‖mphi_tau0 y‖ ≤ 8 * π ^ 2 / (1 - r) ^ 2 := by
  have h1 : 1 - r ≤ ‖1 + y‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-y)
    simp only [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  have h2 : 1 - r ≤ ‖1 - y‖ := by
    have := norm_sub_norm_le (1 : ℂ) y
    simp only [norm_one] at this
    linarith
  have hr : 0 < 1 - r := by linarith
  have e1 : ‖1 / (1 + y) ^ 2‖ ≤ 1 / (1 - r) ^ 2 := by
    rw [norm_div, norm_one, norm_pow]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hr.le h1 2)
  have e2 : ‖1 / (1 - y) ^ 2‖ ≤ 1 / (1 - r) ^ 2 := by
    rw [norm_div, norm_one, norm_pow]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hr.le h2 2)
  unfold mphi_tau0
  rw [norm_mul]
  have : ‖(4 : ℂ) * (π : ℂ) ^ 2‖ = 4 * π ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [this]
  have := norm_add_le (1 / (1 + y) ^ 2) (1 / (1 - y) ^ 2)
  have hπ : 0 < π ^ 2 := by positivity
  calc 4 * π ^ 2 * ‖1 / (1 + y) ^ 2 + 1 / (1 - y) ^ 2‖
      ≤ 4 * π ^ 2 * (1 / (1 - r) ^ 2 + 1 / (1 - r) ^ 2) := by gcongr; linarith
    _ = 8 * π ^ 2 / (1 - r) ^ 2 := by ring

/-- `G` is holomorphic on the disc `‖q‖ < r`, `r < 1` (Weierstrass M-test). -/
theorem mphi_differentiableOn_Gq {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    DifferentiableOn ℂ mphi_Gq (Metric.ball 0 r) := by
  refine differentiableOn_tsum_of_summable_norm
    (u := fun n : ℤ => 8 * π ^ 2 / (1 - r) ^ 2 / r * r ^ n.natAbs)
    ((mphi_summable_pow_natAbs hr0.le hr1).mul_left _) (fun n => ?_) Metric.isOpen_ball
    (fun n q hq => ?_)
  · -- each term is holomorphic on the disc
    intro q hq
    rw [Metric.mem_ball, dist_zero_right] at hq
    have hk : ‖q ^ mphi_kIdx n‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) (hq.trans hr1) (by have := mphi_kIdx_pos n; omega)
    have h1 : 1 + q ^ mphi_kIdx n ≠ 0 := by
      intro h
      have : q ^ mphi_kIdx n = -1 := by linear_combination h
      rw [this, norm_neg, norm_one] at hk
      exact lt_irrefl 1 hk
    have h2 : 1 - q ^ mphi_kIdx n ≠ 0 := by
      intro h
      have : q ^ mphi_kIdx n = 1 := by linear_combination -h
      rw [this, norm_one] at hk
      exact lt_irrefl 1 hk
    have h1' : (1 + q ^ mphi_kIdx n) ^ 2 ≠ 0 := pow_ne_zero 2 h1
    have h2' : (1 - q ^ mphi_kIdx n) ^ 2 ≠ 0 := pow_ne_zero 2 h2
    unfold mphi_tau0
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := assumption)
  · -- the M-test bound
    rw [Metric.mem_ball, dist_zero_right] at hq
    have hk := mphi_kIdx_pos n
    rw [norm_mul, norm_pow]
    have hqk : ‖q ^ mphi_kIdx n‖ ≤ r := by
      rw [norm_pow]
      calc ‖q‖ ^ mphi_kIdx n ≤ ‖q‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) (by linarith) hk
        _ ≤ r := by simpa using hq.le
    have ht := mphi_norm_tau0_le_r hr1 hqk
    have hp : ‖q‖ ^ (mphi_kIdx n - 1) ≤ r ^ n.natAbs / r := by
      rw [le_div_iff₀ hr0]
      calc ‖q‖ ^ (mphi_kIdx n - 1) * r ≤ r ^ (mphi_kIdx n - 1) * r := by
            gcongr
        _ = r ^ mphi_kIdx n := by
            rw [← pow_succ]
            congr 1
            omega
        _ ≤ r ^ n.natAbs := pow_le_pow_of_le_one hr0.le hr1.le (mphi_natAbs_le_kIdx n)
    calc ‖q‖ ^ (mphi_kIdx n - 1) * ‖mphi_tau0 (q ^ mphi_kIdx n)‖
        ≤ r ^ n.natAbs / r * (8 * π ^ 2 / (1 - r) ^ 2) :=
          mul_le_mul hp ht (norm_nonneg _) (by positivity)
      _ = 8 * π ^ 2 / (1 - r) ^ 2 / r * r ^ n.natAbs := by ring

/-- `G(0) = 16π²`. -/
theorem mphi_Gq_zero : mphi_Gq 0 = 16 * (π : ℂ) ^ 2 := by
  rw [mphi_Gq, tsum_eq_sum (s := {0, 1})]
  · simp [mphi_kIdx, mphi_tau0]
    ring
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    have : mphi_kIdx n - 1 ≠ 0 := by
      have := (mphi_kIdx_eq_one_iff n).not.mpr (by tauto)
      have := mphi_kIdx_pos n
      omega
    simp [zero_pow this]

/-! #### `F(q)`: `e₁ - e₂ = F(q)`, holomorphic on the unit disc -/

/-- `F(q)`, the row expansion of `e₁ - e₂` in `q = e^{iπw}`. -/
def mphi_Fq (q : ℂ) : ℂ :=
  ∑' n : ℤ, ((if n = 0 then mphi_rowS (1 / 2) else mphi_sig (q ^ (2 * n.natAbs))) -
    mphi_rho (q ^ mphi_kIdx n))

/-- `e₁(w) - e₂(w) = F(e^{iπw})`. -/
theorem mphi_e12_eq_F {w : ℂ} (hw : 0 < w.im) :
    weierstrassE w 0 - weierstrassE w 1 = mphi_Fq (cexp (π * I * w)) :=
  (mphi_e12_hasSum hw).tsum_eq.symm

/-- `‖σ(y)‖ ≤ 4π²/(1 - r)² ‖y‖` for `‖y‖ ≤ r < 1`. -/
theorem mphi_norm_sig_le_r {r : ℝ} (hr1 : r < 1) {y : ℂ} (hy : ‖y‖ ≤ r) :
    ‖mphi_sig y‖ ≤ 4 * π ^ 2 / (1 - r) ^ 2 * ‖y‖ := by
  have h1 : 1 - r ≤ ‖1 + y‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-y)
    simp only [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  have hr : 0 < 1 - r := by linarith
  unfold mphi_sig
  rw [norm_mul, norm_div, norm_pow]
  have : ‖(4 : ℂ) * (π : ℂ) ^ 2‖ = 4 * π ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [this]
  have h2 : ‖y‖ / ‖1 + y‖ ^ 2 ≤ ‖y‖ / (1 - r) ^ 2 :=
    div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (pow_le_pow_left₀ hr.le h1 2)
  calc 4 * π ^ 2 * (‖y‖ / ‖1 + y‖ ^ 2) ≤ 4 * π ^ 2 * (‖y‖ / (1 - r) ^ 2) := by gcongr
    _ = 4 * π ^ 2 / (1 - r) ^ 2 * ‖y‖ := by ring

/-- `‖ρ(y)‖ ≤ 4π²/(1 - r)² ‖y‖` for `‖y‖ ≤ r < 1`. -/
theorem mphi_norm_rho_le_r {r : ℝ} (hr1 : r < 1) {y : ℂ} (hy : ‖y‖ ≤ r) :
    ‖mphi_rho y‖ ≤ 4 * π ^ 2 / (1 - r) ^ 2 * ‖y‖ := by
  have h1 : 1 - r ≤ ‖1 - y‖ := by
    have := norm_sub_norm_le (1 : ℂ) y
    simp only [norm_one] at this
    linarith
  have hr : 0 < 1 - r := by linarith
  unfold mphi_rho
  rw [norm_mul, norm_div, norm_pow]
  have : ‖(-4 : ℂ) * (π : ℂ) ^ 2‖ = 4 * π ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [this]
  have h2 : ‖y‖ / ‖1 - y‖ ^ 2 ≤ ‖y‖ / (1 - r) ^ 2 :=
    div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (pow_le_pow_left₀ hr.le h1 2)
  calc 4 * π ^ 2 * (‖y‖ / ‖1 - y‖ ^ 2) ≤ 4 * π ^ 2 * (‖y‖ / (1 - r) ^ 2) := by gcongr
    _ = 4 * π ^ 2 / (1 - r) ^ 2 * ‖y‖ := by ring

/-- `1 + q^k ≠ 0` for `‖q‖ < 1`, `k ≠ 0`. -/
theorem mphi_one_add_pow_ne_zero {q : ℂ} (hq : ‖q‖ < 1) {k : ℕ} (hk : k ≠ 0) : 1 + q ^ k ≠ 0 := by
  intro h
  have hk1 : ‖q ^ k‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq hk
  have : q ^ k = -1 := by linear_combination h
  rw [this, norm_neg, norm_one] at hk1
  exact lt_irrefl 1 hk1

/-- `1 - q^k ≠ 0` for `‖q‖ < 1`, `k ≠ 0`. -/
theorem mphi_one_sub_pow_ne_zero {q : ℂ} (hq : ‖q‖ < 1) {k : ℕ} (hk : k ≠ 0) : 1 - q ^ k ≠ 0 := by
  intro h
  have hk1 : ‖q ^ k‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq hk
  have : q ^ k = 1 := by linear_combination -h
  rw [this, norm_one] at hk1
  exact lt_irrefl 1 hk1

/-- `F` is holomorphic on the disc `‖q‖ < r`, `r < 1` (Weierstrass M-test). -/
theorem mphi_differentiableOn_Fq {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    DifferentiableOn ℂ mphi_Fq (Metric.ball 0 r) := by
  refine differentiableOn_tsum_of_summable_norm
    (u := fun n : ℤ => (if n = 0 then ‖mphi_rowS (1 / 2)‖ else 0) +
      8 * π ^ 2 / (1 - r) ^ 2 * r ^ n.natAbs)
    ?_ (fun n => ?_) Metric.isOpen_ball (fun n q hq => ?_)
  · refine Summable.add ?_ ((mphi_summable_pow_natAbs hr0.le hr1).mul_left _)
    exact summable_of_hasFiniteSupport ((Set.finite_singleton (0 : ℤ)).subset
      (fun n hn => by
        rw [Set.mem_singleton_iff]
        by_contra h
        exact hn (by simp [h])))
  · intro q hq
    rw [Metric.mem_ball, dist_zero_right] at hq
    have hq1 : ‖q‖ < 1 := hq.trans hr1
    have hk : mphi_kIdx n ≠ 0 := by have := mphi_kIdx_pos n; omega
    have hr2 : (1 - q ^ mphi_kIdx n) ^ 2 ≠ 0 := pow_ne_zero 2 (mphi_one_sub_pow_ne_zero hq1 hk)
    apply DifferentiableAt.differentiableWithinAt
    split_ifs with h0
    · unfold mphi_rho
      fun_prop (disch := assumption)
    · have hn2 : 2 * n.natAbs ≠ 0 := by omega
      have hs2 : (1 + q ^ (2 * n.natAbs)) ^ 2 ≠ 0 :=
        pow_ne_zero 2 (mphi_one_add_pow_ne_zero hq1 hn2)
      unfold mphi_rho mphi_sig
      fun_prop (disch := assumption)
  · rw [Metric.mem_ball, dist_zero_right] at hq
    have hr : 0 < 1 - r := by linarith
    have hC : 0 ≤ 4 * π ^ 2 / (1 - r) ^ 2 := by positivity
    have hqk : ∀ k : ℕ, ‖q ^ k‖ ≤ r ^ k := fun k => by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hq.le _
    have hle : ∀ k : ℕ, 1 ≤ k → r ^ k ≤ r := fun k hk => by
      calc r ^ k ≤ r ^ 1 := pow_le_pow_of_le_one hr0.le hr1.le hk
        _ = r := pow_one r
    have hk := mphi_kIdx_pos n
    have hrho := mphi_norm_rho_le_r hr1 ((hqk _).trans (hle _ hk))
    have hrho2 : ‖mphi_rho (q ^ mphi_kIdx n)‖ ≤ 4 * π ^ 2 / (1 - r) ^ 2 * r ^ n.natAbs :=
      hrho.trans (mul_le_mul_of_nonneg_left ((hqk _).trans
        (pow_le_pow_of_le_one hr0.le hr1.le (mphi_natAbs_le_kIdx n))) hC)
    split_ifs with h0
    · refine (norm_sub_le _ _).trans ?_
      have e : 8 * π ^ 2 / (1 - r) ^ 2 * r ^ n.natAbs =
          4 * π ^ 2 / (1 - r) ^ 2 * r ^ n.natAbs + 4 * π ^ 2 / (1 - r) ^ 2 * r ^ n.natAbs := by
        ring
      have : 0 ≤ 4 * π ^ 2 / (1 - r) ^ 2 * r ^ n.natAbs := by positivity
      linarith
    · have h2 : 1 ≤ 2 * n.natAbs := by omega
      have hsig := mphi_norm_sig_le_r hr1 ((hqk _).trans (hle _ h2))
      have hsig2 : ‖mphi_sig (q ^ (2 * n.natAbs))‖ ≤ 4 * π ^ 2 / (1 - r) ^ 2 * r ^ n.natAbs :=
        hsig.trans (mul_le_mul_of_nonneg_left ((hqk _).trans
          (pow_le_pow_of_le_one hr0.le hr1.le (by omega))) hC)
      refine (norm_sub_le _ _).trans ?_
      have : 4 * π ^ 2 / (1 - r) ^ 2 * r ^ n.natAbs + 4 * π ^ 2 / (1 - r) ^ 2 * r ^ n.natAbs =
          8 * π ^ 2 / (1 - r) ^ 2 * r ^ n.natAbs := by ring
      linarith

/-- `F(0) = mphi_rowS (1/2)`. -/
theorem mphi_Fq_zero : mphi_Fq 0 = mphi_rowS (1 / 2) := by
  rw [mphi_Fq, tsum_eq_single 0]
  · simp [mphi_rho, mphi_kIdx]
  · intro n hn
    have hk : mphi_kIdx n ≠ 0 := by have := mphi_kIdx_pos n; omega
    have hn2 : 2 * n.natAbs ≠ 0 := by omega
    simp [hn, mphi_sig, mphi_rho, zero_pow hk, zero_pow hn2]

/-! #### `H(q) = q - F(q)/G(q)`, `φ = H(q)/q` near `∞`, and `φ'/φ → -iπ` -/

/-- `H(q) = q - F(q)/G(q)`, so that `φ(w) = H(q)/q` near `∞`. -/
def mphi_Hq (q : ℂ) : ℂ := q - mphi_Fq q / mphi_Gq q

/-- `G` does not vanish on a small disc around `0`. -/
theorem mphi_exists_ball_Gq_ne :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ q ∈ Metric.ball (0 : ℂ) ε, mphi_Gq q ≠ 0 := by
  have hc : ContinuousAt mphi_Gq 0 :=
    ((mphi_differentiableOn_Gq (r := 1 / 2) (by norm_num) (by norm_num)).continuousOn).continuousAt
      (Metric.ball_mem_nhds 0 (by norm_num))
  have hG0 : mphi_Gq 0 ≠ 0 := by
    rw [mphi_Gq_zero]
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 this)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hc.eventually_ne hG0)
  refine ⟨min ε (1 / 2), lt_min hε (by norm_num), (min_le_right _ _).trans_lt (by norm_num),
    fun q hq => hball q (Metric.ball_subset_ball (min_le_left _ _) hq)⟩

/-- `φ(w) = H(q)/q`, `q = e^{iπw}`, wherever `G(q) ≠ 0`. -/
theorem mphi_modularPhi_eq_H {w : ℂ} (hw : 0 < w.im) (hG : mphi_Gq (cexp (π * I * w)) ≠ 0) :
    modularPhi w = mphi_Hq (cexp (π * I * w)) / cexp (π * I * w) := by
  have hq0 := Complex.exp_ne_zero (π * I * w)
  have h32 := mphi_e32_eq_q_mul_G hw
  have h12 := mphi_e12_eq_F hw
  have h02 : weierstrassE w 2 - weierstrassE w 0 =
      cexp (π * I * w) * mphi_Gq (cexp (π * I * w)) - mphi_Fq (cexp (π * I * w)) := by
    rw [← h32, ← h12]; ring
  rw [modularPhi, h02, h32, mphi_Hq]
  field_simp

/-- (∞), derivative version: `φ'(w)/φ(w) → -iπ` as `Im w → ∞`. -/
theorem mphi_deriv_modularPhi_div_tendsto :
    Tendsto (fun w => deriv modularPhi w / modularPhi w)
      (comap Complex.im atTop) (𝓝 (-(π * I))) := by
  obtain ⟨ε, hε, hε1, hG⟩ := mphi_exists_ball_Gq_ne
  set qf : ℂ → ℂ := fun w => cexp (π * I * w) with hqf
  -- `H` is holomorphic on `ball 0 ε`
  have hHd : DifferentiableOn ℂ mphi_Hq (Metric.ball 0 ε) := by
    have h1 := mphi_differentiableOn_Fq hε hε1
    have h2 := mphi_differentiableOn_Gq hε hε1
    exact differentiableOn_id.sub (h1.div h2 hG)
  have hU : IsOpen {w : ℂ | 0 < w.im ∧ qf w ∈ Metric.ball (0 : ℂ) ε} := by
    refine (isOpen_lt continuous_const Complex.continuous_im).inter ?_
    exact Metric.isOpen_ball.preimage (by rw [hqf]; fun_prop)
  -- the derivative formula on `U`
  have hderiv : ∀ w, 0 < w.im → qf w ∈ Metric.ball (0 : ℂ) ε →
      deriv modularPhi w =
        π * I * (deriv mphi_Hq (qf w) * qf w - mphi_Hq (qf w)) / qf w := by
    intro w hw hwq
    have hq0 : qf w ≠ 0 := Complex.exp_ne_zero _
    have heq : modularPhi =ᶠ[𝓝 w] fun w' => mphi_Hq (qf w') / qf w' := by
      filter_upwards [hU.mem_nhds ⟨hw, hwq⟩] with w' ⟨hw', hwq'⟩
      exact mphi_modularPhi_eq_H hw' (hG _ hwq')
    have hq : HasDerivAt qf (qf w * (π * I)) w := by
      have := ((hasDerivAt_id w).const_mul ((π : ℂ) * I)).cexp
      simpa [hqf] using this
    have hH : HasDerivAt mphi_Hq (deriv mphi_Hq (qf w)) (qf w) :=
      (hHd.differentiableAt (Metric.isOpen_ball.mem_nhds hwq)).hasDerivAt
    have hcomp : HasDerivAt (fun w' => mphi_Hq (qf w') / qf w')
        ((deriv mphi_Hq (qf w) * (qf w * (π * I)) * qf w -
          mphi_Hq (qf w) * (qf w * (π * I))) / qf w ^ 2) w :=
      (hH.comp w hq).div hq hq0
    rw [heq.deriv_eq, hcomp.deriv]
    field_simp
  -- limits
  have hq := mphi_tendsto_q
  have hcH : ContinuousAt mphi_Hq 0 :=
    hHd.continuousOn.continuousAt (Metric.ball_mem_nhds 0 hε)
  have hcH' : ContinuousAt (deriv mphi_Hq) 0 :=
    (hHd.deriv Metric.isOpen_ball).continuousOn.continuousAt (Metric.ball_mem_nhds 0 hε)
  obtain ⟨c, hc, hc'⟩ := mphi_rowS_half_pos
  have hH0 : mphi_Hq 0 ≠ 0 := by
    rw [mphi_Hq, mphi_Fq_zero, mphi_Gq_zero, zero_sub, hc']
    have h1 : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    exact neg_ne_zero.mpr (div_ne_zero h2 (mul_ne_zero (by norm_num) (pow_ne_zero 2 h1)))
  have hlimH := hcH.tendsto.comp hq
  have hlimH' := hcH'.tendsto.comp hq
  have hlim : Tendsto (fun w => π * I * (qf w * deriv mphi_Hq (qf w) / mphi_Hq (qf w) - 1))
      (comap Complex.im atTop) (𝓝 (π * I * (0 * deriv mphi_Hq 0 / mphi_Hq 0 - 1))) :=
    tendsto_const_nhds.mul (((hq.mul hlimH').div hlimH hH0).sub tendsto_const_nhds)
  rw [zero_mul, zero_div, zero_sub, mul_neg_one] at hlim
  refine hlim.congr' ?_
  have hev_pos : ∀ᶠ w in comap Complex.im atTop, 0 < w.im :=
    tendsto_comap.eventually (eventually_gt_atTop 0)
  have hev_ball : ∀ᶠ w in comap Complex.im atTop, qf w ∈ Metric.ball (0 : ℂ) ε :=
    hq.eventually (Metric.ball_mem_nhds 0 hε)
  have hev_H : ∀ᶠ w in comap Complex.im atTop, mphi_Hq (qf w) ≠ 0 := hlimH.eventually_ne hH0
  filter_upwards [hev_pos, hev_ball, hev_H] with w hw hwq hHw
  have hq0 : qf w ≠ 0 := Complex.exp_ne_zero _
  have hphi : modularPhi w = mphi_Hq (qf w) / qf w := mphi_modularPhi_eq_H hw (hG _ hwq)
  rw [hderiv w hw hwq, hphi]
  field_simp

/-- The W3 reduction: given the conformality of `φ` on `A`, the remaining three conjuncts of
(14.20) are the cusp limits at `0`, `1` and the growth at `∞`. -/
theorem mphi_eq14_20_of_isConformalOnto
    (h : IsConformalOnto modularPhi modularRegionA upperHalf) :
    IsConformalOnto modularPhi modularRegionA upperHalf ∧
      Tendsto modularPhi (𝓝[modularRegionA] 0) (𝓝 0) ∧
      Tendsto modularPhi (𝓝[modularRegionA] 1) (𝓝 1) ∧
      Tendsto (fun v : ℝ => ‖modularPhi ((1 / 2 : ℂ) + v * I)‖) atTop atTop :=
  ⟨h, mphi_modularPhi_tendsto_zero, mphi_modularPhi_tendsto_one,
    mphi_norm_modularPhi_half_tendsto⟩

/-! ### W4: univalence of the modular function on `A` (abstract form)

A function `f` holomorphic on `ℍ`, real on the three sides of the region `A = modularRegionA`,
with the cusp limits `f → 0` at `0` and `f → 1` at `1`, and the uniform asymptotics
`f(w) e^{iπw} → -1/16`, `f'(w)/f(w) → -iπ` as `Im w → ∞` in the strip `0 ≤ Re w ≤ 1`, maps `A`
conformally onto `ℍ` (`mphi_isConformalOnto_of_W3`).

Route: the asymptotics give injectivity of `f` and `Im f > 0` on a high half-strip; the minimum
principle for `Im f` (through the compactness of `A ∩ f⁻¹(F)`) gives `f(A) ⊆ ℍ`; the growth of `f`
at `∞` gives properness of `f : A → ℍ`; a high value `y₀ ∈ ℍ` has at most one preimage, and it is
regular; and a proper holomorphic map with such a value is injective and onto
(`mphi_injOn_and_image_eq_of_proper`), because `ℍ` minus the countable set of critical values is
connected. -/

/-! #### Proper holomorphic maps into `ℍ` -/

/-- `ℍ` minus a countable set is preconnected (transport of
`Set.Countable.isPathConnected_compl_of_one_lt_rank` along the injective continuous map
`z ↦ Re z + i e^{Im z}` of `ℂ` onto `ℍ`). -/
theorem mphi_w4_isPreconnected_upperHalf_diff_countable {C : Set ℂ} (hC : C.Countable) :
    IsPreconnected (upperHalf \ C) := by
  set h : ℂ → ℂ := fun z => (z.re : ℂ) + (Real.exp z.im : ℂ) * I with hh
  have hinj : Function.Injective h := by
    intro z w hzw
    have hre := congrArg Complex.re hzw
    have him := congrArg Complex.im hzw
    simp only [hh, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] at hre him
    exact Complex.ext hre (Real.exp_injective him)
  have hrange : range h = upperHalf := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      show 0 < (h z).im
      simp only [hh, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        add_zero, zero_add]
      exact Real.exp_pos _
    · intro hy
      have hy' : 0 < y.im := hy
      refine ⟨(y.re : ℂ) + (Real.log y.im : ℂ) * I, ?_⟩
      have e1 : ((y.re : ℂ) + (Real.log y.im : ℂ) * I).re = y.re := by simp
      have e2 : ((y.re : ℂ) + (Real.log y.im : ℂ) * I).im = Real.log y.im := by simp
      simp only [hh, e1, e2, Real.exp_log hy']
      exact Complex.re_add_im y
  have hcont : Continuous h := by
    simp only [hh]
    fun_prop
  have hpre : (h ⁻¹' C).Countable := hC.preimage hinj
  have hpc : IsPathConnected (h ⁻¹' C)ᶜ :=
    hpre.isPathConnected_compl_of_one_lt_rank (by simp)
  have := (hpc.image hcont).isConnected.isPreconnected
  rwa [image_compl_preimage, hrange] at this

/-- Properness in sequential form, for pairs of sequences (as needed for the set of values with
two preimages): if `f` is continuous on the open set `A` and `A ∩ f⁻¹(K)` is compact for every
compact `K ⊆ ℍ`, then two sequences of `A` whose images tend to the same `y ∈ ℍ` have a common
subsequence converging to a pair of points of `A`, both mapped to `y`. -/
theorem mphi_w4_exists_subseq_of_proper {f : ℂ → ℂ} {A : Set ℂ} (hAo : IsOpen A)
    (hc : ContinuousOn f A)
    (hprop : ∀ K ⊆ upperHalf, IsCompact K → IsCompact (A ∩ f ⁻¹' K))
    {y : ℂ} (hy : y ∈ upperHalf) {a : ℕ → ℂ × ℂ} (ha : ∀ n, (a n).1 ∈ A ∧ (a n).2 ∈ A)
    (hlim1 : Tendsto (fun n => f (a n).1) atTop (𝓝 y))
    (hlim2 : Tendsto (fun n => f (a n).2) atTop (𝓝 y)) :
    ∃ q : ℂ × ℂ, q.1 ∈ A ∧ q.2 ∈ A ∧ f q.1 = y ∧ f q.2 = y ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (a ∘ ψ) atTop (𝓝 q) := by
  have hy' : 0 < y.im := hy
  have hball : closedBall y (y.im / 2) ⊆ upperHalf := by
    intro z hz
    show 0 < z.im
    have h1 : |z.im - y.im| ≤ ‖z - y‖ := by
      rw [← sub_im]
      exact abs_im_le_norm _
    rw [mem_closedBall, dist_eq_norm] at hz
    have := (abs_le.1 (h1.trans hz)).1
    linarith
  set K := A ∩ f ⁻¹' closedBall y (y.im / 2) with hK
  have hKc : IsCompact K := hprop _ hball (isCompact_closedBall _ _)
  have hr : 0 < y.im / 2 := by linarith
  have hev1 : ∀ᶠ n in atTop, f (a n).1 ∈ closedBall y (y.im / 2) :=
    hlim1 (closedBall_mem_nhds y hr)
  have hev2 : ∀ᶠ n in atTop, f (a n).2 ∈ closedBall y (y.im / 2) :=
    hlim2 (closedBall_mem_nhds y hr)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev1.and hev2)
  have hmem : ∀ n, a (n + N) ∈ K ×ˢ K := fun n =>
    ⟨⟨(ha _).1, (hN (n + N) (Nat.le_add_left _ _)).1⟩,
      ⟨(ha _).2, (hN (n + N) (Nat.le_add_left _ _)).2⟩⟩
  obtain ⟨q, hq, φ, hφ, hlim⟩ := (hKc.prod hKc).tendsto_subseq hmem
  have hq1 : q.1 ∈ A := hq.1.1
  have hq2 : q.2 ∈ A := hq.2.1
  have hshift : StrictMono fun n => φ n + N := fun m n hmn =>
    Nat.add_lt_add_right (hφ hmn) N
  have hsub : Tendsto (fun n => φ n + N) atTop atTop := hshift.tendsto_atTop
  have hl1 : Tendsto (fun n => (a (φ n + N)).1) atTop (𝓝 q.1) :=
    (continuous_fst.tendsto q).comp hlim
  have hl2 : Tendsto (fun n => (a (φ n + N)).2) atTop (𝓝 q.2) :=
    (continuous_snd.tendsto q).comp hlim
  have hf1 : f q.1 = y := by
    have h1 : Tendsto (fun n => f (a (φ n + N)).1) atTop (𝓝 (f q.1)) :=
      ((hc q.1 hq1).continuousAt (hAo.mem_nhds hq1)).tendsto.comp hl1
    exact tendsto_nhds_unique h1 (hlim1.comp hsub)
  have hf2 : f q.2 = y := by
    have h1 : Tendsto (fun n => f (a (φ n + N)).2) atTop (𝓝 (f q.2)) :=
      ((hc q.2 hq2).continuousAt (hAo.mem_nhds hq2)).tendsto.comp hl2
    exact tendsto_nhds_unique h1 (hlim2.comp hsub)
  exact ⟨q, hq1, hq2, hf1, hf2, fun n => φ n + N, hshift, hlim⟩

/-- **Core of W4.**  A proper holomorphic map of a preconnected open set `A` into `ℍ`, with a
non-critical point `a₁` and a value `y₀ ∈ ℍ` all of whose preimages are regular and which has at
most one preimage, is injective on `A` and maps `A` onto `ℍ`. -/
theorem mphi_injOn_and_image_eq_of_proper {f : ℂ → ℂ} {A : Set ℂ} (hAo : IsOpen A)
    (hAc : IsPreconnected A) (hd : DifferentiableOn ℂ f A) (hmaps : MapsTo f A upperHalf)
    (hprop : ∀ K ⊆ upperHalf, IsCompact K → IsCompact (A ∩ f ⁻¹' K))
    {a₁ : ℂ} (ha₁ : a₁ ∈ A) (ha₁d : deriv f a₁ ≠ 0)
    {y₀ : ℂ} (hy₀ : y₀ ∈ upperHalf) (hy₀reg : ∀ a ∈ A, f a = y₀ → deriv f a ≠ 0)
    (hy₀inj : ∀ a ∈ A, ∀ b ∈ A, f a = y₀ → f b = y₀ → a = b) :
    InjOn f A ∧ f '' A = upperHalf := by
  have hana : AnalyticOnNhd ℂ f A := hd.analyticOnNhd hAo
  have hdana : AnalyticOnNhd ℂ (deriv f) A := hana.deriv
  -- open mapping theorem
  have hopen : ∀ s ⊆ A, IsOpen s → IsOpen (f '' s) := by
    rcases hana.is_constant_or_isOpen hAc with ⟨c, hc⟩ | h
    · exfalso
      apply ha₁d
      have hev : f =ᶠ[𝓝 a₁] fun _ => c := by
        filter_upwards [hAo.mem_nhds ha₁] with z hz using hc z hz
      rw [hev.deriv_eq]
      simp
    · exact h
  -- critical points are isolated, hence countably many
  have hiso : ∀ a ∈ A, ∀ᶠ z in 𝓝[≠] a, deriv f z ≠ 0 := by
    intro a ha
    rcases (hdana a ha).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      exact ha₁d (hdana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hAc ha h ha₁)
    · exact h
  set Z : Set ℂ := {a | a ∈ A ∧ deriv f a = 0} with hZ
  have hZc : Z.Countable := by
    have : DiscreteTopology Z := by
      rw [discreteTopology_subtype_iff]
      intro x hx
      rw [inf_principal_eq_bot]
      filter_upwards [hiso x hx.1] with z hz hzZ using hz hzZ.2
    exact countable_coe_iff.1 countable_of_Lindelof_of_discrete
  set C : Set ℂ := f '' Z with hC
  have hCc : C.Countable := hZc.image f
  have hSpre : IsPreconnected (upperHalf \ C) :=
    mphi_w4_isPreconnected_upperHalf_diff_countable hCc
  -- the set of values with two distinct preimages
  set E : Set ℂ := {y | ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ f a = y ∧ f b = y} with hE
  have hEo : IsOpen E := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨a, ha, b, hb, hab, rfl, hfb⟩
    obtain ⟨Ua, Ub, hUao, hUbo, haUa, hbUb, hdisj⟩ := t2_separation hab
    have h1 : IsOpen (f '' (Ua ∩ A)) := hopen _ inter_subset_right (hUao.inter hAo)
    have h2 : IsOpen (f '' (Ub ∩ A)) := hopen _ inter_subset_right (hUbo.inter hAo)
    have hmem : f a ∈ f '' (Ua ∩ A) ∩ f '' (Ub ∩ A) :=
      ⟨⟨a, ⟨haUa, ha⟩, rfl⟩, ⟨b, ⟨hbUb, hb⟩, hfb⟩⟩
    refine Filter.mem_of_superset ((h1.inter h2).mem_nhds hmem) ?_
    rintro y' ⟨⟨a', ⟨ha'U, ha'⟩, rfl⟩, ⟨b', ⟨hb'U, hb'⟩, hb'y⟩⟩
    refine ⟨a', ha', b', hb', fun h => ?_, rfl, hb'y⟩
    rw [h] at ha'U
    exact Set.disjoint_left.1 hdisj ha'U hb'U
  -- `E` is relatively closed in `ℍ \ C`
  have hclE : closure E ∩ (upperHalf \ C) ⊆ E := by
    rintro y ⟨hyE, hyH, hyC⟩
    obtain ⟨u, huE, hu⟩ := mem_closure_iff_seq_limit.1 hyE
    choose a ha b hb hab hfa hfb using huE
    obtain ⟨q, hq1, hq2, hf1, hf2, ψ, hψ, hlim⟩ :=
      mphi_w4_exists_subseq_of_proper (a := fun n => (a n, b n)) hAo hd.continuousOn hprop hyH
        (fun n => ⟨ha n, hb n⟩) (by simpa [hfa] using hu) (by simpa [hfb] using hu)
    by_cases hqq : q.1 = q.2
    · exfalso
      -- `q.1` is regular, so `f` is injective near it
      have hreg : deriv f q.1 ≠ 0 := fun h0 => hyC ⟨q.1, ⟨hq1, h0⟩, hf1⟩
      have hstrict := ((hana q.1 hq1).hasStrictDerivAt).hasStrictFDerivAt_equiv hreg
      set e := hstrict.toOpenPartialHomeomorph f with he
      have hsrc : e.source ∈ 𝓝 q.1 :=
        e.open_source.mem_nhds hstrict.mem_toOpenPartialHomeomorph_source
      have hl1 : Tendsto (fun n => a (ψ n)) atTop (𝓝 q.1) :=
        (continuous_fst.tendsto q).comp hlim
      have hl2 : Tendsto (fun n => b (ψ n)) atTop (𝓝 q.1) := by
        have := (continuous_snd.tendsto q).comp hlim
        rw [← hqq] at this
        exact this
      have hev1 : ∀ᶠ n in atTop, a (ψ n) ∈ e.source := hl1 hsrc
      have hev2 : ∀ᶠ n in atTop, b (ψ n) ∈ e.source := hl2 hsrc
      obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
      apply hab (ψ n)
      apply e.injOn hn1 hn2
      rw [hstrict.toOpenPartialHomeomorph_coe]
      exact (hfa (ψ n)).trans (hfb (ψ n)).symm
    · exact ⟨q.1, hq1, q.2, hq2, hqq, hf1, hf2⟩
  -- `ℍ \ C` does not meet `E`
  have hy₀S : y₀ ∈ upperHalf \ C :=
    ⟨hy₀, by rintro ⟨a, ⟨ha, hda⟩, hfa⟩; exact hy₀reg a ha hfa hda⟩
  have hSE : ¬ ((upperHalf \ C) ∩ E).Nonempty := by
    intro hne
    obtain ⟨a, ha, b, hb, hab, hfa, hfb⟩ :=
      hSpre.subset_of_closure_inter_subset hEo hne hclE hy₀S
    exact hab (hy₀inj a ha b hb hfa hfb)
  -- hence `E ⊆ C`, and an open subset of a countable set is empty
  have hE0 : E = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := nonempty_iff_ne_empty.2 hne
    obtain ⟨y', hy'E, hy'C⟩ := (hCc.dense_compl ℝ).inter_open_nonempty E hEo ⟨y, hy⟩
    apply hSE
    refine ⟨y', ⟨?_, hy'C⟩, hy'E⟩
    obtain ⟨a, ha, -, -, -, rfl, -⟩ := hy'E
    exact hmaps ha
  refine ⟨fun a ha b hb hab => ?_, ?_⟩
  · by_contra hne
    have : f a ∈ E := ⟨a, ha, b, hb, hne, rfl, hab.symm⟩
    rw [hE0] at this
    exact this
  · refine subset_antisymm (image_subset_iff.2 hmaps) ?_
    refine isConnected_upperHalf.isPreconnected.subset_of_closure_inter_subset
      (hopen A subset_rfl hAo) ⟨f a₁, hmaps ha₁, a₁, ha₁, rfl⟩ ?_
    rintro y ⟨hycl, hyH⟩
    obtain ⟨u, huA, hu⟩ := mem_closure_iff_seq_limit.1 hycl
    choose a ha hfa using huA
    obtain ⟨q, hq1, -, hf1, -, -⟩ :=
      mphi_w4_exists_subseq_of_proper (a := fun n => (a n, a n)) hAo hd.continuousOn hprop hyH
        (fun n => ⟨ha n, ha n⟩) (by simpa [hfa] using hu) (by simpa [hfa] using hu)
    exact ⟨q.1, hq1, hf1⟩

/-! #### The high half-strip: injectivity and `Im f > 0` from the asymptotics at `∞` -/

/-- `G = -16 f e^{iπw}` has derivative `G · (f'/f + iπ)` at a point `w` where `f` is
differentiable and does not vanish. -/
theorem mphi_w4_hasDerivAt_G {f : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℂ f w) (hf0 : f w ≠ 0) :
    HasDerivAt (fun z => -16 * f z * cexp (π * I * z))
      ((-16 * f w * cexp (π * I * w)) * (deriv f w / f w + π * I)) w := by
  have h1 : HasDerivAt (fun z => cexp (π * I * z)) (cexp (π * I * w) * (π * I)) w := by
    have h := ((hasDerivAt_id w).const_mul ((π : ℂ) * I)).cexp
    simp only [id, mul_one] at h
    exact h
  have h2 := (hf.hasDerivAt.const_mul (-16 : ℂ)).mul h1
  refine h2.congr_deriv ?_
  field_simp
  ring

/-- `‖z‖ ≤ ‖z + 2n‖` for every integer `n` when `|Re z| < 1`. -/
theorem mphi_w4_norm_le_norm_add_two_int {z : ℂ} (hz : |z.re| < 1) (n : ℤ) :
    ‖z‖ ≤ ‖z + 2 * n‖ := by
  have key : 0 ≤ (n : ℝ) * (z.re + n) := by
    have h1 := (abs_lt.1 hz).1
    have h2 := (abs_lt.1 hz).2
    rcases lt_trichotomy n 0 with h | h | h
    · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.2 h
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · simp [h]
    · have : (1 : ℝ) ≤ n := by exact_mod_cast h
      exact mul_nonneg (by linarith) (by linarith)
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    normSq_apply, normSq_apply]
  simp only [add_re, add_im, mul_re, mul_im, intCast_re, intCast_im, re_ofNat, im_ofNat]
  nlinarith [key]

/-- The open half-strip `{w : 0 < Re w < 1, T < Im w}`. -/
def mphi_w4_halfStrip (T : ℝ) : Set ℂ := {w | 0 < w.re ∧ w.re < 1 ∧ T < w.im}

/-- The open half-strip `mphi_w4_halfStrip T` is convex. -/
theorem mphi_w4_convex_halfStrip (T : ℝ) : Convex ℝ (mphi_w4_halfStrip T) := by
  have h := ((convex_halfSpace_re_gt (0 : ℝ)).inter (convex_halfSpace_re_lt (1 : ℝ))).inter
    (convex_halfSpace_im_gt T)
  convert h using 1
  ext w
  simp [mphi_w4_halfStrip, and_assoc]

/-- The half-strip `{w : 0 ≤ Re w ≤ 1, T < Im w}`, with its two vertical sides. -/
def mphi_w4_halfStripC (T : ℝ) : Set ℂ := {w | 0 ≤ w.re ∧ w.re ≤ 1 ∧ T < w.im}

/-- The half-strip `mphi_w4_halfStripC T` is convex. -/
theorem mphi_w4_convex_halfStripC (T : ℝ) : Convex ℝ (mphi_w4_halfStripC T) := by
  have h := ((convex_halfSpace_re_ge (0 : ℝ)).inter (convex_halfSpace_re_le (1 : ℝ))).inter
    (convex_halfSpace_im_gt T)
  convert h using 1
  ext w
  simp [mphi_w4_halfStripC, and_assoc]

/-- Jordan's inequality in the form `2 min(u, 1 - u) ≤ sin (π u)` for `0 ≤ u ≤ 1`. -/
theorem mphi_w4_two_min_le_sin_pi_mul {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    2 * min u (1 - u) ≤ Real.sin (π * u) := by
  rcases le_total u (1 / 2) with h | h
  · have hj := Real.mul_le_sin (x := π * u) (by positivity) (by nlinarith [Real.pi_pos])
    have : 2 / π * (π * u) = 2 * u := by field_simp
    rw [this] at hj
    exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)).trans hj
  · have hj := Real.mul_le_sin (x := π * (1 - u)) (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos])
    have : 2 / π * (π * (1 - u)) = 2 * (1 - u) := by field_simp
    rw [this] at hj
    have hs : Real.sin (π * (1 - u)) = Real.sin (π * u) := by
      rw [mul_sub, mul_one, Real.sin_pi_sub]
    rw [hs] at hj
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)).trans hj

/-- If `‖-16 f(w) e^{iπw} - 1‖ < 1/4` on the half-strip `mphi_w4_halfStripC T`, then `f` has no
zero there. -/
theorem mphi_w4_f_ne_zero_of_asym {f : ℂ → ℂ} {T : ℝ}
    (hG : ∀ w ∈ mphi_w4_halfStripC T, ‖-16 * f w * cexp (π * I * w) - 1‖ < 1 / 4)
    {w : ℂ} (hw : w ∈ mphi_w4_halfStripC T) : f w ≠ 0 := by
  intro h0
  have := hG w hw
  rw [h0] at this
  norm_num at this

/-- If `‖-16 f(w) e^{iπw} - 1‖ < 1/4` on the half-strip `mphi_w4_halfStripC T`, then
`Re (-16 f(w) e^{iπw}) > 3/4` there. -/
theorem mphi_w4_G_re_pos_of_asym {f : ℂ → ℂ} {T : ℝ}
    (hG : ∀ w ∈ mphi_w4_halfStripC T, ‖-16 * f w * cexp (π * I * w) - 1‖ < 1 / 4)
    {w : ℂ} (hw : w ∈ mphi_w4_halfStripC T) :
    3 / 4 < (-16 * f w * cexp (π * I * w)).re := by
  have h := (abs_lt.1 ((abs_re_le_norm _).trans_lt (hG w hw))).1
  rw [sub_re, one_re] at h
  linarith

/-- For `f` holomorphic on `ℍ` with `‖-16 f(w) e^{iπw} - 1‖ < 1/4` on the half-strip
`mphi_w4_halfStripC T` (`T ≥ 0`), the function `G = -16 f e^{iπw}` has derivative
`G · (f'/f + iπ)` at every point of that half-strip. -/
theorem mphi_w4_hasDerivAt_G_of_asym {f : ℂ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hd : ∀ w, 0 < w.im → DifferentiableAt ℂ f w)
    (hG : ∀ w ∈ mphi_w4_halfStripC T, ‖-16 * f w * cexp (π * I * w) - 1‖ < 1 / 4)
    {w : ℂ} (hw : w ∈ mphi_w4_halfStripC T) :
    HasDerivAt (fun z => -16 * f z * cexp (π * I * z))
      ((-16 * f w * cexp (π * I * w)) * (deriv f w / f w + π * I)) w :=
  mphi_w4_hasDerivAt_G (hd w (by linarith [hw.2.2])) (mphi_w4_f_ne_zero_of_asym hG hw)

/-- Injectivity of `f` on the high half-strip.  `L = log G` (with `G = -16 f e^{iπw}`,
`Re G > 3/4`) has derivative `f'/f + iπ` of norm `< 1/10`, while `f(a) = f(b)` forces
`L(a) - L(b) = iπ (a - b + 2n)`, of norm `≥ π ‖a - b‖` because `|Re (a - b)| < 1`. -/
theorem mphi_w4_injOn_halfStrip_of_asym {f : ℂ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hd : ∀ w, 0 < w.im → DifferentiableAt ℂ f w)
    (hG : ∀ w ∈ mphi_w4_halfStripC T, ‖-16 * f w * cexp (π * I * w) - 1‖ < 1 / 4)
    (hD : ∀ w ∈ mphi_w4_halfStripC T, ‖deriv f w / f w + π * I‖ < 1 / 10) :
    InjOn f (mphi_w4_halfStrip T) := by
  set G : ℂ → ℂ := fun z => -16 * f z * cexp (π * I * z) with hGdef
  have hsub : mphi_w4_halfStrip T ⊆ mphi_w4_halfStripC T := fun w hw =>
    ⟨hw.1.le, hw.2.1.le, hw.2.2⟩
  have hslit : ∀ w ∈ mphi_w4_halfStrip T, G w ∈ slitPlane := fun w hw =>
    Or.inl (by linarith [mphi_w4_G_re_pos_of_asym hG (hsub hw)])
  have hGne : ∀ w ∈ mphi_w4_halfStrip T, G w ≠ 0 := fun w hw => slitPlane_ne_zero (hslit w hw)
  set L : ℂ → ℂ := fun z => Complex.log (G z) with hLdef
  have hL : ∀ w ∈ mphi_w4_halfStrip T, HasDerivAt L (deriv f w / f w + π * I) w := by
    intro w hw
    have h := (mphi_w4_hasDerivAt_G_of_asym hT hd hG (hsub hw)).clog (hslit w hw)
    refine h.congr_deriv ?_
    have := hGne w hw
    have hf0 := mphi_w4_f_ne_zero_of_asym hG (hsub hw)
    field_simp
  have hLd : ∀ w ∈ mphi_w4_halfStrip T, DifferentiableAt ℂ L w := fun w hw =>
    (hL w hw).differentiableAt
  have hLb : ∀ w ∈ mphi_w4_halfStrip T, ‖deriv L w‖ ≤ 1 / 10 := fun w hw => by
    rw [(hL w hw).deriv]
    exact (hD w (hsub hw)).le
  have hexpL : ∀ w ∈ mphi_w4_halfStrip T, cexp (L w - π * I * w) = -16 * f w := by
    intro w hw
    rw [exp_sub, hLdef, exp_log (hGne w hw), hGdef]
    field_simp
  intro a ha b hb hab
  have hmvt : ‖L a - L b‖ ≤ 1 / 10 * ‖a - b‖ :=
    (mphi_w4_convex_halfStrip T).norm_image_sub_le_of_norm_deriv_le hLd hLb hb ha
  have heq : cexp (L a - π * I * a) = cexp (L b - π * I * b) := by
    rw [hexpL a ha, hexpL b hb, hab]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 heq
  have hdiff : L a - L b = (π * I) * (a - b + 2 * n) := by linear_combination hn
  have hre : |(a - b).re| < 1 := by
    rw [sub_re, abs_lt]
    constructor <;> linarith [ha.1, ha.2.1, hb.1, hb.2.1]
  have hnorm := mphi_w4_norm_le_norm_add_two_int hre n
  have hpi : ‖(π : ℂ) * I‖ = π := by
    rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hle : π * ‖a - b‖ ≤ 1 / 10 * ‖a - b‖ := by
    calc π * ‖a - b‖ ≤ π * ‖a - b + 2 * n‖ := by gcongr
      _ = ‖L a - L b‖ := by rw [hdiff, norm_mul, hpi]
      _ ≤ 1 / 10 * ‖a - b‖ := hmvt
  have h0 : ‖a - b‖ = 0 := by
    nlinarith [Real.pi_gt_three, norm_nonneg (a - b)]
  exact sub_eq_zero.1 (norm_eq_zero.1 h0)

/-- `Im f > 0` on the open high half-strip when `f` is real on its two vertical sides.
`G = -16 f e^{iπw}` is real on those sides and `‖G'‖ ≤ 1/8`, so `|Im G| ≤ min(u, 1 - u)/8` at
`w = u + iv`, while `Re G > 3/4`; then `Im f = (e^{πv}/16) (Re G sin πu - Im G cos πu) > 0` by
Jordan's inequality. -/
theorem mphi_w4_im_pos_halfStrip_of_asym {f : ℂ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hd : ∀ w, 0 < w.im → DifferentiableAt ℂ f w)
    (hG : ∀ w ∈ mphi_w4_halfStripC T, ‖-16 * f w * cexp (π * I * w) - 1‖ < 1 / 4)
    (hD : ∀ w ∈ mphi_w4_halfStripC T, ‖deriv f w / f w + π * I‖ < 1 / 10)
    (hreal0 : ∀ v : ℝ, T < v → (f (v * I)).im = 0)
    (hreal1 : ∀ v : ℝ, T < v → (f (1 + v * I)).im = 0) :
    ∀ w ∈ mphi_w4_halfStrip T, 0 < (f w).im := by
  set G : ℂ → ℂ := fun z => -16 * f z * cexp (π * I * z) with hGdef
  have hGd : ∀ w ∈ mphi_w4_halfStripC T, DifferentiableAt ℂ G w := fun w hw =>
    (mphi_w4_hasDerivAt_G_of_asym hT hd hG hw).differentiableAt
  have hGb : ∀ w ∈ mphi_w4_halfStripC T, ‖deriv G w‖ ≤ 1 / 8 := by
    intro w hw
    rw [(mphi_w4_hasDerivAt_G_of_asym hT hd hG hw).deriv, norm_mul]
    have h1 : ‖G w‖ ≤ 5 / 4 := by
      have := norm_le_norm_add_norm_sub' (G w) 1  -- ‖G w‖ ≤ ‖1‖ + ‖G w - 1‖
      have h := hG w hw
      simp only [norm_one] at this
      show ‖G w‖ ≤ 5 / 4
      linarith
    have h2 := (hD w hw).le
    calc ‖G w‖ * ‖deriv f w / f w + π * I‖ ≤ 5 / 4 * (1 / 10) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
      _ ≤ 1 / 8 := by norm_num
  intro w hw
  set u := w.re with hu
  set v := w.im with hv
  have hwC : w ∈ mphi_w4_halfStripC T := ⟨hw.1.le, hw.2.1.le, hw.2.2⟩
  have h0C : (v : ℂ) * I ∈ mphi_w4_halfStripC T := ⟨by simp, by simp, by simpa using hw.2.2⟩
  have h1C : 1 + (v : ℂ) * I ∈ mphi_w4_halfStripC T := ⟨by simp, by simp, by simpa using hw.2.2⟩
  -- `G` is real on the two vertical sides
  have hG0 : (G ((v : ℂ) * I)).im = 0 := by
    have hc : cexp (π * I * ((v : ℂ) * I)) = ((Real.exp (-(π * v)) : ℝ) : ℂ) := by
      rw [ofReal_exp]
      congr 1
      push_cast
      ring_nf
      rw [I_sq]
      ring
    simp only [hGdef, hc, mul_im, ofReal_re, ofReal_im, mul_zero, hreal0 v hw.2.2]
    simp
  have hG1 : (G (1 + (v : ℂ) * I)).im = 0 := by
    have hc : cexp (π * I * (1 + (v : ℂ) * I)) = ((-Real.exp (-(π * v)) : ℝ) : ℂ) := by
      have e : (π : ℂ) * I * (1 + (v : ℂ) * I) = ((-(π * v) : ℝ) : ℂ) + π * I := by
        push_cast
        ring_nf
        rw [I_sq]
        ring
      rw [e, exp_add, exp_pi_mul_I, ← ofReal_exp]
      push_cast
      ring
    simp only [hGdef, hc, mul_im, ofReal_re, ofReal_im, mul_zero, hreal1 v hw.2.2]
    simp
  -- mean value inequality from both sides
  have hm0 : ‖G w - G ((v : ℂ) * I)‖ ≤ 1 / 8 * u := by
    have := (mphi_w4_convex_halfStripC T).norm_image_sub_le_of_norm_deriv_le hGd hGb h0C hwC
    have e : ‖w - (v : ℂ) * I‖ = u := by
      have : w - (v : ℂ) * I = (u : ℂ) := by
        apply Complex.ext <;> simp [hu, hv]
      rw [this, norm_real, Real.norm_of_nonneg hw.1.le]
    rwa [e] at this
  have hm1 : ‖G w - G (1 + (v : ℂ) * I)‖ ≤ 1 / 8 * (1 - u) := by
    have := (mphi_w4_convex_halfStripC T).norm_image_sub_le_of_norm_deriv_le hGd hGb h1C hwC
    have e : ‖w - (1 + (v : ℂ) * I)‖ = 1 - u := by
      have : w - (1 + (v : ℂ) * I) = ((u - 1 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hu, hv]
      rw [this, norm_real, Real.norm_of_nonpos (by linarith [hw.2.1])]
      ring
    rwa [e] at this
  have himG : |(G w).im| ≤ 1 / 8 * min u (1 - u) := by
    have a0 : |(G w).im| ≤ 1 / 8 * u := by
      have := (abs_im_le_norm (G w - G ((v : ℂ) * I))).trans hm0
      rwa [sub_im, hG0, sub_zero] at this
    have a1 : |(G w).im| ≤ 1 / 8 * (1 - u) := by
      have := (abs_im_le_norm (G w - G (1 + (v : ℂ) * I))).trans hm1
      rwa [sub_im, hG1, sub_zero] at this
    rcases min_choice u (1 - u) with h | h <;> rw [h] <;> assumption
  -- the formula `Im f = (e^{πv}/16) (Re G sin πu - Im G cos πu)`
  have hf : f w = -(1 / 16) * (G w * cexp (-(π * I * w))) := by
    simp only [hGdef]
    rw [mul_assoc (-16 * f w), ← exp_add, add_neg_cancel, exp_zero]
    ring
  have hre : (-(π * I * w)).re = π * v := by simp [hv]
  have him : (-(π * I * w)).im = -(π * u) := by simp [hu]
  have hformula : (f w).im = Real.exp (π * v) / 16 *
      ((G w).re * Real.sin (π * u) - (G w).im * Real.cos (π * u)) := by
    rw [hf]
    simp only [mul_im, mul_re, exp_re, exp_im, hre, him, Real.sin_neg, Real.cos_neg]
    simp
    ring
  rw [hformula]
  have hGre := mphi_w4_G_re_pos_of_asym hG hwC
  have hsin := mphi_w4_two_min_le_sin_pi_mul hw.1.le hw.2.1.le
  have hmin : 0 < min u (1 - u) := lt_min hw.1 (by linarith [hw.2.1])
  have hcos : |(G w).im * Real.cos (π * u)| ≤ |(G w).im| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hpos : 0 < (G w).re * Real.sin (π * u) - (G w).im * Real.cos (π * u) := by
    have h1 : (G w).im * Real.cos (π * u) ≤ 1 / 8 * min u (1 - u) :=
      (le_abs_self _).trans (hcos.trans himG)
    have h2 : 3 / 4 * (2 * min u (1 - u)) ≤ (G w).re * Real.sin (π * u) :=
      mul_le_mul hGre.le hsin (by linarith) (by linarith)
    linarith
  positivity

/-! #### The region `A`: topology, boundary, properness and the minimum principle -/

/-- The region `A = modularRegionA` is open. -/
theorem mphi_w4_isOpen_modularRegionA : IsOpen modularRegionA := by
  have h1 : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
  have h2 : IsOpen {w : ℂ | w.re < 1} := isOpen_lt continuous_re continuous_const
  have h3 : IsOpen {w : ℂ | 1 / 2 < ‖w - 1 / 2‖} := isOpen_lt continuous_const (by fun_prop)
  have h4 : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const continuous_im
  exact h1.inter (h2.inter (h3.inter h4))

/-- The region `A` lies in the upper half-plane. -/
theorem mphi_w4_modularRegionA_subset_upperHalf : modularRegionA ⊆ upperHalf :=
  fun _ hw => hw.2.2.2

/-- `‖w - 1/2‖² = (Re w - 1/2)² + (Im w)²`. -/
theorem mphi_w4_norm_sub_half_sq (w : ℂ) : ‖w - 1 / 2‖ ^ 2 = (w.re - 1 / 2) ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, normSq_apply]
  simp
  ring

/-- The region `A` is path connected: go vertically to height `2`, then horizontally to
`1/2 + 2i`. -/
theorem mphi_w4_isPathConnected_modularRegionA : IsPathConnected modularRegionA := by
  set p : ℂ := (1 / 2 : ℂ) + 2 * I with hp
  have hpA : p ∈ modularRegionA := by
    refine ⟨by simp [hp], by simp [hp]; norm_num, ?_, by simp [hp]⟩
    rw [← sq_lt_sq₀ (by norm_num) (norm_nonneg _), mphi_w4_norm_sub_half_sq]
    simp [hp]
    norm_num
  refine ⟨p, hpA, fun w hw => ?_⟩
  set q : ℂ := (w.re : ℂ) + 2 * I with hq
  -- vertical segment `w → q`
  have h1 : JoinedIn modularRegionA w q := by
    refine JoinedIn.of_segment_subset fun z hz => ?_
    rw [segment_eq_image'] at hz
    obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
    have hre : (w + (t : ℝ) • (q - w)).re = w.re := by simp [hq]
    have him : (w + (t : ℝ) • (q - w)).im = w.im + t * (2 - w.im) := by simp [hq]
    refine ⟨by rw [hre]; exact hw.1, by rw [hre]; exact hw.2.1, ?_, ?_⟩
    · rw [← sq_lt_sq₀ (by norm_num) (norm_nonneg _), mphi_w4_norm_sub_half_sq, hre, him]
      have hA := hw.2.2.1
      rw [← sq_lt_sq₀ (by norm_num) (norm_nonneg _), mphi_w4_norm_sub_half_sq] at hA
      have hw0 := hw.2.2.2
      rcases le_total w.im 2 with h | h
      · -- the height increases
        have : w.im ≤ w.im + t * (2 - w.im) := by nlinarith
        nlinarith
      · -- the height stays `≥ 2`
        have : 2 ≤ w.im + t * (2 - w.im) := by nlinarith
        nlinarith [sq_nonneg (w.re - 1 / 2)]
    · rw [him]
      have hw0 := hw.2.2.2
      rcases le_total w.im 2 with h | h <;> nlinarith
  -- horizontal segment `q → p`
  have h2 : JoinedIn modularRegionA q p := by
    refine JoinedIn.of_segment_subset fun z hz => ?_
    rw [segment_eq_image'] at hz
    obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
    have hre : (q + (t : ℝ) • (p - q)).re = w.re + t * (1 / 2 - w.re) := by simp [hq, hp]
    have him : (q + (t : ℝ) • (p - q)).im = 2 := by simp [hq, hp]
    have hw0 := hw.1
    have hw1 := hw.2.1
    refine ⟨by rw [hre]; nlinarith, by rw [hre]; nlinarith, ?_, by rw [him]; norm_num⟩
    rw [← sq_lt_sq₀ (by norm_num) (norm_nonneg _), mphi_w4_norm_sub_half_sq, him]
    nlinarith [sq_nonneg ((q + (t : ℝ) • (p - q)).re - 1 / 2)]
  exact (h1.trans h2).symm

/-- The region `A` is preconnected. -/
theorem mphi_w4_isPreconnected_modularRegionA : IsPreconnected modularRegionA :=
  mphi_w4_isPathConnected_modularRegionA.isConnected.isPreconnected

/-- The closure of `A` lies in `{0 ≤ Re w ≤ 1, ‖w - 1/2‖ ≥ 1/2, Im w ≥ 0}`. -/
theorem mphi_w4_closure_modularRegionA_subset :
    closure modularRegionA ⊆ {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1 ∧ 1 / 2 ≤ ‖w - 1 / 2‖ ∧ 0 ≤ w.im} := by
  apply closure_minimal
  · intro w hw
    exact ⟨hw.1.le, hw.2.1.le, hw.2.2.1.le, hw.2.2.2.le⟩
  · have h1 : IsClosed {w : ℂ | 0 ≤ w.re} := isClosed_le continuous_const continuous_re
    have h2 : IsClosed {w : ℂ | w.re ≤ 1} := isClosed_le continuous_re continuous_const
    have h3 : IsClosed {w : ℂ | 1 / 2 ≤ ‖w - 1 / 2‖} := isClosed_le continuous_const (by fun_prop)
    have h4 : IsClosed {w : ℂ | 0 ≤ w.im} := isClosed_le continuous_const continuous_im
    exact h1.inter (h2.inter (h3.inter h4))

/-- Boundary points of `A`: the cusps `0` and `1`, or a point of `ℍ` on one of the three sides
`Re w = 0`, `Re w = 1`, `‖w - 1/2‖ = 1/2`. -/
theorem mphi_w4_mem_closure_modularRegionA_cases {w : ℂ} (hw : w ∈ closure modularRegionA)
    (hwA : w ∉ modularRegionA) :
    w = 0 ∨ w = 1 ∨ (0 < w.im ∧ (w.re = 0 ∨ w.re = 1 ∨ ‖w - 1 / 2‖ = 1 / 2)) := by
  obtain ⟨h0, h1, h2, h3⟩ := mphi_w4_closure_modularRegionA_subset hw
  rcases h3.lt_or_eq with him | him
  · right; right
    refine ⟨him, ?_⟩
    by_contra hne
    push Not at hne
    exact hwA ⟨lt_of_le_of_ne h0 (Ne.symm hne.1), lt_of_le_of_ne h1 hne.2.1,
      lt_of_le_of_ne h2 (Ne.symm hne.2.2), him⟩
  · have hsq := h2
    rw [← sq_le_sq₀ (by norm_num) (norm_nonneg _), mphi_w4_norm_sub_half_sq, ← him] at hsq
    have hprod : w.re * (w.re - 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 hprod with h | h
    · left
      exact Complex.ext (by simp [h]) (by simp [← him])
    · right; left
      exact Complex.ext (by simp; linarith) (by simp [← him])

/-- **Compactness lemma.**  Let `f` be continuous on `ℍ`, real on the three sides of `A`, with the
cusp limits `0` at `0` and `1` at `1`.  If `F` is a closed set not meeting the real axis and
`Im w ≤ T` whenever `w ∈ A` and `f(w) ∈ F`, then `A ∩ f⁻¹(F)` is compact. -/
theorem mphi_w4_isCompact_inter_preimage {f : ℂ → ℂ} (hc : ContinuousOn f upperHalf)
    (hbd : ∀ w : ℂ, 0 < w.im → (w.re = 0 ∨ w.re = 1 ∨ ‖w - 1 / 2‖ = 1 / 2) → (f w).im = 0)
    (hcusp0 : Tendsto f (𝓝[modularRegionA] 0) (𝓝 0))
    (hcusp1 : Tendsto f (𝓝[modularRegionA] 1) (𝓝 1))
    {F : Set ℂ} (hF : IsClosed F) (hFr : ∀ y ∈ F, y.im ≠ 0) {T : ℝ}
    (hT : ∀ w ∈ modularRegionA, f w ∈ F → w.im ≤ T) :
    IsCompact (modularRegionA ∩ f ⁻¹' F) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · refine isClosed_of_closure_subset fun w hw => ?_
    have hwA : w ∈ closure modularRegionA := closure_mono inter_subset_left hw
    have : (𝓝[modularRegionA ∩ f ⁻¹' F] w).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hw
    have hevF : ∀ᶠ z in 𝓝[modularRegionA ∩ f ⁻¹' F] w, f z ∈ F :=
      eventually_nhdsWithin_of_forall fun z hz => hz.2
    by_cases hA : w ∈ modularRegionA
    · have hcont : ContinuousAt f w := hc.continuousAt (isOpen_upperHalf.mem_nhds hA.2.2.2)
      exact ⟨hA, hF.mem_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hevF⟩
    · exfalso
      rcases mphi_w4_mem_closure_modularRegionA_cases hwA hA with rfl | rfl | ⟨him, hcases⟩
      · exact hFr 0 (hF.mem_of_tendsto (hcusp0.mono_left (nhdsWithin_mono _ inter_subset_left))
          hevF) (by simp)
      · exact hFr 1 (hF.mem_of_tendsto (hcusp1.mono_left (nhdsWithin_mono _ inter_subset_left))
          hevF) (by simp)
      · have hcont : ContinuousAt f w := hc.continuousAt (isOpen_upperHalf.mem_nhds him)
        exact hFr (f w) (hF.mem_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hevF)
          (hbd w him hcases)
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + |T|)).subset ?_
    rintro w ⟨hwA, hwF⟩
    have h1 := hT w hwA hwF
    rw [mem_closedBall, dist_zero_right]
    calc ‖w‖ ≤ |w.re| + |w.im| := norm_le_abs_re_add_abs_im w
      _ ≤ 1 + |T| := by
        rw [abs_of_pos hwA.1, abs_of_pos hwA.2.2.2]
        linarith [le_abs_self T, hwA.2.1]

/-- **Properness** of `f : A → ℍ` from the growth `‖f(w)‖ → ∞` as `Im w → ∞` in `A` (with the
boundary and cusp hypotheses of the compactness lemma). -/
theorem mphi_w4_isCompact_inter_preimage_of_growth {f : ℂ → ℂ} (hc : ContinuousOn f upperHalf)
    (hbd : ∀ w : ℂ, 0 < w.im → (w.re = 0 ∨ w.re = 1 ∨ ‖w - 1 / 2‖ = 1 / 2) → (f w).im = 0)
    (hcusp0 : Tendsto f (𝓝[modularRegionA] 0) (𝓝 0))
    (hcusp1 : Tendsto f (𝓝[modularRegionA] 1) (𝓝 1))
    (hgrow : ∀ R : ℝ, ∃ T : ℝ, ∀ w ∈ modularRegionA, T < w.im → R < ‖f w‖)
    {K : Set ℂ} (hK : K ⊆ upperHalf) (hKc : IsCompact K) :
    IsCompact (modularRegionA ∩ f ⁻¹' K) := by
  obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall 0
  obtain ⟨T, hT⟩ := hgrow R
  refine mphi_w4_isCompact_inter_preimage hc hbd hcusp0 hcusp1 hKc.isClosed
    (fun y hy => (hK hy).ne') (T := T) fun w hwA hwK => ?_
  by_contra h
  have h1 := hT w hwA (lt_of_not_ge h)
  have h2 := hR hwK
  rw [mem_closedBall, dist_zero_right] at h2
  linarith

/-- **Minimum principle**: `Im f > 0` on `A`, given `Im f > 0` high up in `A` (for `f` holomorphic
on `ℍ`, with the boundary and cusp hypotheses of the compactness lemma). -/
theorem mphi_w4_im_pos_of_high {f : ℂ → ℂ} (hc : ContinuousOn f upperHalf)
    (hbd : ∀ w : ℂ, 0 < w.im → (w.re = 0 ∨ w.re = 1 ∨ ‖w - 1 / 2‖ = 1 / 2) → (f w).im = 0)
    (hcusp0 : Tendsto f (𝓝[modularRegionA] 0) (𝓝 0))
    (hcusp1 : Tendsto f (𝓝[modularRegionA] 1) (𝓝 1))
    (hd : DifferentiableOn ℂ f upperHalf) {T : ℝ}
    (hhigh : ∀ w ∈ modularRegionA, T < w.im → 0 < (f w).im) :
    ∀ w ∈ modularRegionA, 0 < (f w).im := by
  have hAo := mphi_w4_isOpen_modularRegionA
  have hAc := mphi_w4_isPreconnected_modularRegionA
  -- a high point of `A`
  set z : ℂ := (1 / 2 : ℂ) + ((max T 1 + 1 : ℝ) : ℂ) * I with hz
  have hzA : z ∈ modularRegionA := by
    have hm : 1 ≤ max T 1 := le_max_right _ _
    refine ⟨by simp [hz], by simp [hz]; norm_num, ?_, by simp [hz]; linarith⟩
    rw [← sq_lt_sq₀ (by norm_num) (norm_nonneg _), mphi_w4_norm_sub_half_sq]
    simp [hz]
    nlinarith
  have hzT : T < z.im := by
    simp [hz]
    linarith [le_max_left T 1]
  -- a global minimum of `Im f` on `A` has positive value (maximum modulus for `e^{i f}`)
  have hmin : ∀ w₁ ∈ modularRegionA, IsMinOn (fun w => (f w).im) modularRegionA w₁ →
      0 < (f w₁).im := by
    intro w₁ hw₁ hmin
    set g : ℂ → ℂ := fun w => cexp (I * f w) with hg
    have hgd : DifferentiableOn ℂ g modularRegionA :=
      ((hd.mono mphi_w4_modularRegionA_subset_upperHalf).const_mul I).cexp
    have hnorm : ∀ w, ‖g w‖ = Real.exp (-(f w).im) := fun w => by
      simp [hg, norm_exp]
    have hmax : IsMaxOn (norm ∘ g) modularRegionA w₁ := by
      intro w hw
      simp only [Set.mem_ofPred_eq, Function.comp_apply, hnorm]
      exact Real.exp_le_exp.2 (neg_le_neg (hmin hw))
    have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hAc hAo hgd hw₁ hmax hzA
    have : ‖g z‖ = ‖g w₁‖ := by rw [heq]; rfl
    rw [hnorm, hnorm] at this
    have := Real.exp_injective this
    have := hhigh z hzA hzT
    linarith
  -- first `Im f ≥ 0`: otherwise a sublevel set is compact and gives a global minimum
  have hnonneg : ∀ w ∈ modularRegionA, 0 ≤ (f w).im := by
    intro w₀ hw₀
    by_contra hneg
    push Not at hneg
    set F : Set ℂ := {y | y.im ≤ (f w₀).im} with hF
    have hFc : IsClosed F := isClosed_le continuous_im continuous_const
    have hK := mphi_w4_isCompact_inter_preimage hc hbd hcusp0 hcusp1 hFc
      (fun y hy => by have : y.im ≤ (f w₀).im := hy; exact (by linarith : y.im < 0).ne)
      (T := T) fun w hwA hwF => by
        by_contra h
        have h1 := hhigh w hwA (lt_of_not_ge h)
        have h2 : (f w).im ≤ (f w₀).im := hwF
        linarith
    have hne : (modularRegionA ∩ f ⁻¹' F).Nonempty :=
      ⟨w₀, hw₀, by show (f w₀).im ≤ (f w₀).im; exact le_rfl⟩
    have hcont : ContinuousOn (fun w => (f w).im) (modularRegionA ∩ f ⁻¹' F) :=
      continuous_im.comp_continuousOn (hc.mono fun w hw => hw.1.2.2.2)
    obtain ⟨w₁, hw₁, hw₁min⟩ := hK.exists_isMinOn hne hcont
    have hglob : IsMinOn (fun w => (f w).im) modularRegionA w₁ := by
      intro w hw
      by_cases hwF : f w ∈ F
      · exact hw₁min ⟨hw, hwF⟩
      · have h1 : (f w₀).im < (f w).im := lt_of_not_ge hwF
        have h2 : (f w₁).im ≤ (f w₀).im := hw₁.2
        show (f w₁).im ≤ (f w).im
        linarith
    have := hmin w₁ hw₁.1 hglob
    have h2 : (f w₁).im ≤ (f w₀).im := hw₁.2
    linarith
  -- then `Im f > 0`: a zero of `Im f` would be a global minimum
  intro w hw
  rcases (hnonneg w hw).lt_or_eq with h | h
  · exact h
  · have hglob : IsMinOn (fun w => (f w).im) modularRegionA w := fun w' hw' => by
      show (f w).im ≤ (f w').im
      rw [← h]
      exact hnonneg w' hw'
    exact hmin w hw hglob

/-- `f` is bounded on the low part `A ∩ {Im w ≤ T}`, for `f` continuous on `ℍ` with the cusp
limits `0` at `0` and `1` at `1`. -/
theorem mphi_w4_bounded_low {f : ℂ → ℂ} (hc : ContinuousOn f upperHalf)
    (hcusp0 : Tendsto f (𝓝[modularRegionA] 0) (𝓝 0))
    (hcusp1 : Tendsto f (𝓝[modularRegionA] 1) (𝓝 1)) (T : ℝ) :
    ∃ M : ℝ, ∀ w ∈ modularRegionA, w.im ≤ T → ‖f w‖ ≤ M := by
  by_contra hne
  push Not at hne
  choose w hwA hwT hwM using fun n : ℕ => hne n
  -- the points lie in a compact rectangle
  set S : Set ℂ := closure modularRegionA ∩ {z | z.im ≤ T} ∩ closedBall 0 (1 + |T|) with hS
  have hSc : IsCompact S := Metric.isCompact_of_isClosed_isBounded
    ((isClosed_closure.inter (isClosed_le continuous_im continuous_const)).inter
      isClosed_closedBall)
    (Metric.isBounded_closedBall.subset inter_subset_right)
  have hwS : ∀ n, w n ∈ S := fun n => by
    refine ⟨⟨subset_closure (hwA n), hwT n⟩, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    calc ‖w n‖ ≤ |(w n).re| + |(w n).im| := norm_le_abs_re_add_abs_im _
      _ ≤ 1 + |T| := by
        rw [abs_of_pos (hwA n).1, abs_of_pos (hwA n).2.2.2]
        linarith [le_abs_self T, (hwA n).2.1, hwT n]
  obtain ⟨w', hw'S, φ, hφ, hlim⟩ := hSc.tendsto_subseq hwS
  have hlimA : Tendsto (w ∘ φ) atTop (𝓝[modularRegionA] w') :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => hwA (φ n)⟩
  -- `f` has a limit at `w'` within `A`
  obtain ⟨L, hL⟩ : ∃ L, Tendsto f (𝓝[modularRegionA] w') (𝓝 L) := by
    by_cases him : 0 < w'.im
    · exact ⟨f w', (hc.continuousAt (isOpen_upperHalf.mem_nhds him)).tendsto.mono_left
        nhdsWithin_le_nhds⟩
    · have hw'A : w' ∉ modularRegionA := fun h => him h.2.2.2
      rcases mphi_w4_mem_closure_modularRegionA_cases hw'S.1.1 hw'A with rfl | rfl | ⟨h, -⟩
      · exact ⟨0, hcusp0⟩
      · exact ⟨1, hcusp1⟩
      · exact absurd h him
  have hconv := hL.comp hlimA
  have hev : ∀ᶠ n in atTop, ‖(f ∘ w ∘ φ) n‖ < ‖L‖ + 1 := by
    have := (continuous_norm.tendsto L).comp hconv
    exact this.eventually (gt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ n : ℕ in atTop, ‖L‖ + 1 ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  obtain ⟨n, h1, h2⟩ := (hev.and hev2).exists
  have h3 : (φ n : ℝ) ≥ n := by exact_mod_cast hφ.id_le n
  have h4 := hwM (φ n)
  simp only [Function.comp_apply] at h1
  linarith

/-! #### Assembly: the abstract W4 theorem -/

/-- The strip filter (`Im w → ∞` uniformly in `0 ≤ Re w ≤ 1`) in `ε`–`T` form. -/
theorem mphi_w4_exists_T_of_tendsto_strip {g : ℂ → ℂ} {c : ℂ}
    (h : Tendsto g (comap im atTop ⊓ 𝓟 {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1}) (𝓝 c)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ T : ℝ, ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → T < w.im → ‖g w - c‖ < ε := by
  have h1 : g ⁻¹' ball c ε ∈ comap im atTop ⊓ 𝓟 {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1} :=
    h (ball_mem_nhds c hε)
  rw [mem_inf_principal, mem_comap] at h1
  obtain ⟨t, ht, hsub⟩ := h1
  obtain ⟨T, hT⟩ := mem_atTop_sets.1 ht
  refine ⟨T, fun w h0 h1 hw => ?_⟩
  have h2 := hsub (hT w.im hw.le) ⟨h0, h1⟩
  rwa [mem_preimage, mem_ball, dist_eq_norm] at h2

/-- **W4, abstract form.**  `f` holomorphic on `ℍ`, real on the three sides of `A`, with the cusp
limits `0, 1` at `0, 1` and the uniform asymptotics at `∞`, maps `A` conformally onto `ℍ`. -/
theorem mphi_isConformalOnto_of_W3 {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f upperHalf)
    (hbd : ∀ w : ℂ, 0 < w.im → (w.re = 0 ∨ w.re = 1 ∨ ‖w - 1 / 2‖ = 1 / 2) → (f w).im = 0)
    (hcusp0 : Tendsto f (𝓝[modularRegionA] 0) (𝓝 0))
    (hcusp1 : Tendsto f (𝓝[modularRegionA] 1) (𝓝 1))
    (hasymG : Tendsto (fun w => f w * cexp (π * I * w))
      (comap im atTop ⊓ 𝓟 {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1}) (𝓝 (-1 / 16)))
    (hasymD : Tendsto (fun w => deriv f w / f w)
      (comap im atTop ⊓ 𝓟 {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1}) (𝓝 (-(π * I)))) :
    IsConformalOnto f modularRegionA upperHalf := by
  have hc : ContinuousOn f upperHalf := hd.continuousOn
  have hdAt : ∀ w, 0 < w.im → DifferentiableAt ℂ f w := fun w hw =>
    hd.differentiableAt (isOpen_upperHalf.mem_nhds hw)
  -- the threshold `T`
  obtain ⟨T₁, hT₁⟩ := mphi_w4_exists_T_of_tendsto_strip hasymG (ε := 1 / 64) (by norm_num)
  obtain ⟨T₂, hT₂⟩ := mphi_w4_exists_T_of_tendsto_strip hasymD (ε := 1 / 10) (by norm_num)
  set T : ℝ := max (max T₁ T₂) 0 with hTdef
  have hT0 : 0 ≤ T := le_max_right _ _
  have hTT₁ : T₁ ≤ T := (le_max_left _ _).trans (le_max_left _ _)
  have hTT₂ : T₂ ≤ T := (le_max_right _ _).trans (le_max_left _ _)
  have hG : ∀ w ∈ mphi_w4_halfStripC T, ‖-16 * f w * cexp (π * I * w) - 1‖ < 1 / 4 := by
    intro w hw
    have h := hT₁ w hw.1 hw.2.1 (lt_of_le_of_lt hTT₁ hw.2.2)
    have e : -16 * f w * cexp (π * I * w) - 1 = -16 * (f w * cexp (π * I * w) - -1 / 16) := by
      ring
    rw [e, norm_mul]
    have h16 : ‖(-16 : ℂ)‖ = 16 := by norm_num
    rw [h16]
    linarith
  have hD : ∀ w ∈ mphi_w4_halfStripC T, ‖deriv f w / f w + π * I‖ < 1 / 10 := by
    intro w hw
    have h := hT₂ w hw.1 hw.2.1 (lt_of_le_of_lt hTT₂ hw.2.2)
    rwa [sub_neg_eq_add] at h
  have hderiv_ne : ∀ w ∈ mphi_w4_halfStripC T, deriv f w ≠ 0 := by
    intro w hw h0
    have h := hD w hw
    rw [h0, zero_div, zero_add, norm_mul, norm_I, mul_one, norm_real,
      Real.norm_of_nonneg Real.pi_pos.le] at h
    linarith [Real.pi_gt_three]
  have hreal0 : ∀ v : ℝ, T < v → (f (v * I)).im = 0 := fun v hv =>
    hbd _ (by simp; linarith) (Or.inl (by simp))
  have hreal1 : ∀ v : ℝ, T < v → (f (1 + v * I)).im = 0 := fun v hv =>
    hbd _ (by simp; linarith) (Or.inr (Or.inl (by simp)))
  have hinjS := mphi_w4_injOn_halfStrip_of_asym hT0 hdAt hG hD
  have himS := mphi_w4_im_pos_halfStrip_of_asym hT0 hdAt hG hD hreal0 hreal1
  have hAS : ∀ w ∈ modularRegionA, T < w.im → w ∈ mphi_w4_halfStrip T := fun w hw hwT =>
    ⟨hw.1, hw.2.1, hwT⟩
  -- `Im f > 0` on `A`
  have himA := mphi_w4_im_pos_of_high hc hbd hcusp0 hcusp1 hd (T := T) fun w hw hwT =>
    himS w (hAS w hw hwT)
  have hmaps : MapsTo f modularRegionA upperHalf := fun w hw => himA w hw
  -- growth at `∞`, hence properness
  have hgrow : ∀ R : ℝ, ∃ T' : ℝ, ∀ w ∈ modularRegionA, T' < w.im → R < ‖f w‖ := by
    intro R
    refine ⟨max T (Real.log (64 * |R| / 3 + 1) / π), fun w hw hwT => ?_⟩
    have hwC : w ∈ mphi_w4_halfStripC T :=
      ⟨hw.1.le, hw.2.1.le, lt_of_le_of_lt (le_max_left _ _) hwT⟩
    have hG1 : 3 / 4 ≤ ‖-16 * f w * cexp (π * I * w)‖ := by
      have h1 := norm_sub_norm_le (1 : ℂ) (-16 * f w * cexp (π * I * w))
      have h2 := hG w hwC
      have h3 : ‖(1 : ℂ) - -16 * f w * cexp (π * I * w)‖ =
          ‖-16 * f w * cexp (π * I * w) - 1‖ := norm_sub_rev _ _
      rw [norm_one] at h1
      linarith
    have hnormE : ‖cexp (π * I * w)‖ = Real.exp (-(π * w.im)) := by
      rw [norm_exp]
      congr 1
      simp
    have hlog : Real.log (64 * |R| / 3 + 1) < π * w.im := by
      have h1 : Real.log (64 * |R| / 3 + 1) / π < w.im := lt_of_le_of_lt (le_max_right _ _) hwT
      rw [div_lt_iff₀ Real.pi_pos] at h1
      linarith [mul_comm w.im π]
    have hexp : 64 * |R| / 3 + 1 < Real.exp (π * w.im) := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < 64 * |R| / 3 + 1)]
      exact Real.exp_lt_exp.2 hlog
    have heq : ‖-16 * f w * cexp (π * I * w)‖ * Real.exp (π * w.im) / 16 = ‖f w‖ := by
      rw [norm_mul, norm_mul, hnormE]
      have h16 : ‖(-16 : ℂ)‖ = 16 := by norm_num
      rw [h16, mul_assoc, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
      ring
    rw [← heq]
    have hR : R ≤ |R| := le_abs_self R
    have hprod := mul_le_mul hG1 hexp.le (by positivity) (norm_nonneg _)
    linarith
  have hprop : ∀ K ⊆ upperHalf, IsCompact K → IsCompact (modularRegionA ∩ f ⁻¹' K) :=
    fun K hK hKc =>
      mphi_w4_isCompact_inter_preimage_of_growth hc hbd hcusp0 hcusp1 hgrow hK hKc
  -- a regular value with a single preimage
  obtain ⟨M, hM⟩ := mphi_w4_bounded_low hc hcusp0 hcusp1 T
  set y₀ : ℂ := ((max M 0 + 1 : ℝ) : ℂ) * I with hy₀
  have hy₀H : y₀ ∈ upperHalf := by
    show 0 < y₀.im
    simp [hy₀]
    positivity
  have hy₀norm : M < ‖y₀‖ := by
    rw [hy₀, norm_mul, norm_I, mul_one, norm_real, Real.norm_of_nonneg (by positivity)]
    linarith [le_max_left M 0]
  have hhigh₀ : ∀ a ∈ modularRegionA, f a = y₀ → a ∈ mphi_w4_halfStrip T := by
    intro a ha hfa
    refine hAS a ha (lt_of_not_ge fun h => ?_)
    have := hM a ha h
    rw [hfa] at this
    linarith
  have hy₀reg : ∀ a ∈ modularRegionA, f a = y₀ → deriv f a ≠ 0 := fun a ha hfa =>
    hderiv_ne a (let h := hhigh₀ a ha hfa; ⟨h.1.le, h.2.1.le, h.2.2⟩)
  have hy₀inj : ∀ a ∈ modularRegionA, ∀ b ∈ modularRegionA, f a = y₀ → f b = y₀ → a = b :=
    fun a ha b hb hfa hfb => hinjS (hhigh₀ a ha hfa) (hhigh₀ b hb hfb) (hfa.trans hfb.symm)
  -- a regular point
  set a₁ : ℂ := (1 / 2 : ℂ) + ((T + 1 : ℝ) : ℂ) * I with ha₁
  have ha₁A : a₁ ∈ modularRegionA := by
    refine ⟨by simp [ha₁], by simp [ha₁]; norm_num, ?_, by simp [ha₁]; linarith⟩
    rw [← sq_lt_sq₀ (by norm_num) (norm_nonneg _), mphi_w4_norm_sub_half_sq]
    simp [ha₁]
    nlinarith
  have ha₁d : deriv f a₁ ≠ 0 :=
    hderiv_ne a₁ ⟨ha₁A.1.le, ha₁A.2.1.le, by simp [ha₁]⟩
  obtain ⟨hinj, himg⟩ := mphi_injOn_and_image_eq_of_proper mphi_w4_isOpen_modularRegionA
    mphi_w4_isPreconnected_modularRegionA (hd.mono mphi_w4_modularRegionA_subset_upperHalf)
    hmaps hprop ha₁A ha₁d hy₀H hy₀reg hy₀inj
  exact ⟨hd.mono mphi_w4_modularRegionA_subset_upperHalf, hinj, himg⟩

/-! ### Assembly of (14.20) (`mphi_`): the hypotheses of `mphi_isConformalOnto_of_W3` for `φ` -/

/-- `∑_{m ∈ ℤ} 1/(1/2 + m)² = π²`: along `t ↦ 1/2 + it`, `t → 0⁺`, the row sum tends to
`mphi_rowS (1/2)` (dominated convergence, `|1/2 + m + it| ≥ |1/2 + m|`) and equals
`4π² e^{-2πt}/(1 + e^{-2πt})² → π²` (`mphi_rowS_half_I`). -/
theorem mphi_rowS_half_eq : mphi_rowS (1 / 2) = (π : ℂ) ^ 2 := by
  have hne : ∀ m : ℤ, (1 / 2 + (m : ℂ)) ≠ 0 := by
    intro m h
    have h' : (1 / 2 + (m : ℝ)) = 0 := by
      have := congrArg Complex.re h
      simpa using this
    have h2 : (2 * m + 1 : ℤ) = 0 := by
      have : (2 * (m : ℝ) + 1) = 0 := by linarith
      exact_mod_cast this
    omega
  have h1 : Tendsto (fun t : ℝ => mphi_rowS (1 / 2 + (t : ℂ) * I)) (𝓝[>] 0)
      (𝓝 (mphi_rowS (1 / 2))) := by
    unfold mphi_rowS
    refine tendsto_tsum_of_dominated_convergence
      (f := fun (t : ℝ) (m : ℤ) => (1 : ℂ) / (1 / 2 + (t : ℂ) * I + m) ^ 2)
      (g := fun m : ℤ => (1 : ℂ) / (1 / 2 + (m : ℂ)) ^ 2)
      (bound := fun m : ℤ => ‖(1 : ℂ) / (1 / 2 + (m : ℂ)) ^ 2‖)
      (summable_norm_iff.mpr (mphi_rowS_summable (1 / 2))) (fun m => ?_) ?_
    · have hc : ContinuousAt (fun t : ℝ => (1 : ℂ) / (1 / 2 + (t : ℂ) * I + m) ^ 2) 0 := by
        refine continuousAt_const.div (Continuous.continuousAt (by fun_prop)) ?_
        simpa using pow_ne_zero 2 (hne m)
      have h0 := hc.tendsto
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · refine Eventually.of_forall fun t m => ?_
      have hle : ‖(1 / 2 + (m : ℂ))‖ ≤ ‖1 / 2 + (t : ℂ) * I + m‖ := by
        have e : (1 / 2 + (m : ℂ)) = ((1 / 2 + m : ℝ) : ℂ) := by push_cast; ring
        have hre : (1 / 2 + (t : ℂ) * I + m).re = 1 / 2 + m := by simp
        rw [e, Complex.norm_real, Real.norm_eq_abs, ← hre]
        exact Complex.abs_re_le_norm _
      simp only [norm_div, norm_one, norm_pow]
      exact one_div_le_one_div_of_le (pow_pos (norm_pos_iff.mpr (hne m)) 2)
        (pow_le_pow_left₀ (norm_nonneg _) hle 2)
  have h2 : Tendsto (fun t : ℝ => mphi_rowS (1 / 2 + (t : ℂ) * I)) (𝓝[>] 0)
      (𝓝 ((π : ℂ) ^ 2)) := by
    have hden : ∀ t : ℝ, (1 + Real.exp (-2 * π * t)) ^ 2 ≠ 0 := fun t => by positivity
    have hcont : Continuous fun t : ℝ =>
        4 * π ^ 2 * (Real.exp (-2 * π * t) / (1 + Real.exp (-2 * π * t)) ^ 2) :=
      continuous_const.mul (Continuous.div (by fun_prop) (by fun_prop) hden)
    have hv : ((4 * π ^ 2 * (Real.exp (-2 * π * 0) / (1 + Real.exp (-2 * π * 0)) ^ 2) : ℝ) : ℂ) =
        (π : ℂ) ^ 2 := by
      rw [mul_zero, Real.exp_zero]
      push_cast
      ring
    have hlim := ((Complex.continuous_ofReal.comp hcont).continuousAt (x := 0)).tendsto
    simp only [Function.comp_apply] at hlim
    rw [hv] at hlim
    refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (mphi_rowS_half_I ht).symm
  exact tendsto_nhds_unique h1 h2

/-- (∞) for `φ` in the form required by `mphi_isConformalOnto_of_W3`: `φ(w) e^{iπw} → -1/16` as
`Im w → ∞` with `0 ≤ Re w ≤ 1` (`mphi_modularPhi_mul_q_tendsto` and `mphi_rowS_half_eq`). -/
theorem mphi_modularPhi_mul_q_tendsto_strip :
    Tendsto (fun w => modularPhi w * cexp (π * I * w))
      (comap Complex.im atTop ⊓ 𝓟 {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1}) (𝓝 (-1 / 16)) := by
  have h := mphi_modularPhi_mul_q_tendsto
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : -mphi_rowS (1 / 2) / (16 * (π : ℂ) ^ 2) = -1 / 16 := by
    rw [mphi_rowS_half_eq]
    field_simp
  rw [e] at h
  exact h.mono_left inf_le_left

/-- (∞), derivative version, in the form required by `mphi_isConformalOnto_of_W3`: `φ'/φ → -iπ`
as `Im w → ∞` with `0 ≤ Re w ≤ 1`. -/
theorem mphi_deriv_modularPhi_div_tendsto_strip :
    Tendsto (fun w => deriv modularPhi w / modularPhi w)
      (comap Complex.im atTop ⊓ 𝓟 {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1}) (𝓝 (-(π * I))) :=
  mphi_deriv_modularPhi_div_tendsto.mono_left inf_le_left

/-- `φ` is real on the three sides `Re w = 0`, `Re w = 1` and `|w - 1/2| = 1/2` of `A`, by
(14.13)–(14.15); a point `w` of the half-circle is `1/(1 - vI)` with `v = Im w / Re w > 0`. -/
theorem mphi_modularPhi_im_eq_zero_of_side {w : ℂ} (hw : 0 < w.im)
    (hside : w.re = 0 ∨ w.re = 1 ∨ ‖w - 1 / 2‖ = 1 / 2) : (modularPhi w).im = 0 := by
  rcases hside with h0 | h1 | hc
  · have e : w = (w.im : ℂ) * I := by
      apply Complex.ext <;> simp [h0]
    rw [e]
    exact (eq14_13_15 hw).1
  · have e : w = 1 + (w.im : ℂ) * I := by
      apply Complex.ext <;> simp [h1]
    rw [e]
    exact (eq14_13_15 hw).2.2.1
  · have hsq : (w.re - 1 / 2) ^ 2 + w.im ^ 2 = 1 / 4 := by
      have h := Complex.sq_norm (w - 1 / 2)
      rw [hc, Complex.normSq_apply] at h
      simp only [Complex.sub_re, Complex.sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
        Complex.one_re, Complex.one_im] at h
      nlinarith
    have hre : 0 < w.re := by nlinarith
    set v : ℝ := w.im / w.re with hv
    have hvpos : 0 < v := div_pos hw hre
    have hden : (1 - (v : ℂ) * I) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
    have e : w = 1 / (1 - (v : ℂ) * I) := by
      rw [eq_div_iff hden]
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im,
          Complex.one_im]
        rw [hv]
        field_simp
        nlinarith
      · simp only [Complex.mul_im, Complex.sub_re, Complex.one_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im,
          Complex.one_im]
        rw [hv]
        field_simp
        ring
    rw [e]
    exact (eq14_13_15 hvpos).2.2.2.2.1

/-- `φ` is holomorphic on `upperHalf`: there `e₃ - e₂ ≠ 0` (`mphi_weierstrassE_pairwise_ne`) and
`e₁, e₂, e₃` are holomorphic (`mphi_differentiableOn_weierstrassE`). -/
theorem mphi_differentiableOn_modularPhi_upperHalf : DifferentiableOn ℂ modularPhi upperHalf :=
  mphi_differentiableOn_modularPhi (fun _ hw => hw) fun _ hw =>
    sub_ne_zero.2 (mphi_weierstrassE_pairwise_ne hw).2.2.symm

/-- (14.20), first conjunct: `φ` maps `A` conformally onto `ℍ` (`mphi_isConformalOnto_of_W3`
applied to `φ`). -/
theorem mphi_isConformalOnto_modularPhi : IsConformalOnto modularPhi modularRegionA upperHalf :=
  mphi_isConformalOnto_of_W3 mphi_differentiableOn_modularPhi_upperHalf
    (fun _ hw hside => mphi_modularPhi_im_eq_zero_of_side hw hside)
    mphi_modularPhi_tendsto_zero mphi_modularPhi_tendsto_one
    mphi_modularPhi_mul_q_tendsto_strip mphi_deriv_modularPhi_div_tendsto_strip

/-- (14.20): `φ` maps `A` conformally onto the upper half-plane, with `0 ↦ 0`, `1 ↦ 1`,
`∞ ↦ ∞`; so `φ` is the analytic continuation by reflection of the conformal map `A → ℍ`
of §14.2.

Proved (2026-09-24): `φ` is holomorphic on `ℍ` (`e₁, e₂, e₃` are, and `e₃ ≠ e₂`), real on the three
sides of `A` ((14.13)–(14.15)), tends to `0` and `1` at the cusps (via `w ↦ -1/w` and `w ↦ w - 1`),
and `φ e^{iπw} → -1/16`, `φ'/φ → -iπ` as `Im w → ∞` (`q`-expansions of `e₃ - e₂` and `e₁ - e₂`,
`∑ 1/(m + 1/2)² = π²`); `mphi_isConformalOnto_of_W3` turns this boundary behaviour into univalence
of `φ` on `A` and `φ(A) = ℍ`. -/
theorem eq14_20_modularPhi_conformal :
    IsConformalOnto modularPhi modularRegionA upperHalf ∧
      Tendsto modularPhi (𝓝[modularRegionA] 0) (𝓝 0) ∧
      Tendsto modularPhi (𝓝[modularRegionA] 1) (𝓝 1) ∧
      Tendsto (fun v : ℝ => ‖modularPhi ((1 / 2 : ℂ) + v * I)‖) atTop atTop := by
  exact mphi_eq14_20_of_isConformalOnto mphi_isConformalOnto_modularPhi

/-! ## §14.2 The covering property of `φ` and (14.6)

Moved here (2026-09-25) from after `modularPhi_gamma2_invariant`, since the proofs use (14.11)–(14.20).
Helpers are prefixed `mcov_`. -/

/-- The modular function on `ℍ`. -/
def modularPhiH (τ : UpperHalfPlane) : ℂ := modularPhi τ

/-- (14.6)–(14.7): the Poincaré density `η(z) = |ψ'(z)|/Im ψ(z)` of `ℂ̄(0, 1, ∞)`, `ψ = φ⁻¹`;
equivalently `η(φ(w)) = 1/(|φ'(w)| Im w)`. -/
def puncturedSphereDensity (z : ℂ) : ℝ :=
  sSup {r : ℝ | ∃ w : ℂ, 0 < w.im ∧ modularPhi w = z ∧ r = 1 / (‖deriv modularPhi w‖ * w.im)}

/-- The Poincaré distance `δ(z₁, z₂)` in `ℂ̄(0, 1, ∞)`. -/
def puncturedSphereDist (z₁ z₂ : ℂ) : ℝ≥0∞ :=
  metricDist {z : ℂ | z ≠ 0 ∧ z ≠ 1} (fun z => ENNReal.ofReal (puncturedSphereDensity z)) z₁ z₂

section ModularCovering

open UpperHalfPlane Matrix
open scoped MatrixGroups

theorem mcov_gamma2_even01 {γ : SL(2, ℤ)} (h : γ ∈ CongruenceSubgroup.Gamma 2) : Even (γ 0 1) :=
  g2_even_of_zmod (CongruenceSubgroup.Gamma_mem.1 h).2.1

theorem mcov_gamma2_even10 {γ : SL(2, ℤ)} (h : γ ∈ CongruenceSubgroup.Gamma 2) : Even (γ 1 0) :=
  g2_even_of_zmod (CongruenceSubgroup.Gamma_mem.1 h).2.2.1

theorem mcov_gamma2_odd00 {γ : SL(2, ℤ)} (h : γ ∈ CongruenceSubgroup.Gamma 2) : Odd (γ 0 0) :=
  g2_odd_of_zmod (CongruenceSubgroup.Gamma_mem.1 h).1

theorem mcov_sl_det (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe γ
  rwa [Matrix.det_fin_two] at h

/-- `d ≡ a (mod 4)` for `γ ∈ Γ(2)` with `a ≡ 1`. -/
theorem mcov_gamma2_d_mod4 {γ : SL(2, ℤ)} (h : γ ∈ CongruenceSubgroup.Gamma 2) (h4 : γ 0 0 % 4 = 1) :
    γ 1 1 % 4 = 1 := by
  have hdet := mcov_sl_det γ
  obtain ⟨x, hx⟩ := mcov_gamma2_even01 h
  obtain ⟨y, hy⟩ := mcov_gamma2_even10 h
  obtain ⟨p, hp⟩ : ∃ p, γ 0 0 = 4 * p + 1 := ⟨γ 0 0 / 4, by omega⟩
  rw [hx, hy, hp] at hdet
  have : γ 1 1 = 1 + 4 * (x * y - p * γ 1 1) := by linear_combination hdet
  rw [this, Int.add_mul_emod_self_left]
  rfl

/-- `Γ(2)' = {γ ∈ Γ(2) : γ₀₀ ≡ 1 mod 4}`, the torsion-free index-2 subgroup (`Γ(2) = ±Γ(2)'`). -/
def mcov_gamma2' : Subgroup SL(2, ℤ) where
  carrier := {γ | γ ∈ CongruenceSubgroup.Gamma 2 ∧ γ 0 0 % 4 = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha4⟩ ⟨hb, hb4⟩
    refine ⟨mul_mem ha hb, ?_⟩
    obtain ⟨x, hx⟩ := mcov_gamma2_even01 ha
    obtain ⟨y, hy⟩ := mcov_gamma2_even10 hb
    obtain ⟨p, hp⟩ : ∃ p, a 0 0 = 4 * p + 1 := ⟨a 0 0 / 4, by omega⟩
    obtain ⟨q, hq⟩ : ∃ q, b 0 0 = 4 * q + 1 := ⟨b 0 0 / 4, by omega⟩
    have e : (a * b) 0 0 = a 0 0 * b 0 0 + a 0 1 * b 1 0 := by
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    rw [e, hx, hy, hp, hq, show (4 * p + 1) * (4 * q + 1) + (x + x) * (y + y) =
      1 + 4 * (4 * p * q + p + q + x * y) by ring, Int.add_mul_emod_self_left]
    rfl
  one_mem' := ⟨one_mem _, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha4⟩
    refine ⟨inv_mem ha, ?_⟩
    have e : (a⁻¹) 0 0 = a 1 1 := by
      simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    rw [e]
    exact mcov_gamma2_d_mod4 ha ha4

theorem mcov_gamma2'_le : mcov_gamma2' ≤ CongruenceSubgroup.Gamma 2 := fun _ h => h.1

theorem mcov_gamma4_le_gamma2' : CongruenceSubgroup.Gamma 4 ≤ mcov_gamma2' := by
  intro γ hγ
  obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
  have c : ∀ a b : ℤ, (a : ZMod 4) = (b : ZMod 4) → (a : ZMod 2) = (b : ZMod 2) := by
    intro a b h
    rw [ZMod.intCast_eq_intCast_iff'] at h ⊢
    push_cast at h ⊢
    omega
  refine ⟨CongruenceSubgroup.Gamma_mem.2 ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa using c (γ 0 0) 1 (by simpa using h00)
  · simpa using c (γ 0 1) 0 (by simpa using h01)
  · simpa using c (γ 1 0) 0 (by simpa using h10)
  · simpa using c (γ 1 1) 1 (by simpa using h11)
  · have := (ZMod.intCast_eq_intCast_iff' (γ 0 0) 1 4).1 (by simpa using h00)
    push_cast at this
    omega

instance : mcov_gamma2'.FiniteIndex := Subgroup.finiteIndex_of_le mcov_gamma4_le_gamma2'

abbrev mcov_G2 : Subgroup (GL (Fin 2) ℝ) := (mcov_gamma2' : Subgroup (GL (Fin 2) ℝ))

/-- No element `≠ 1` of `Γ(2)'` fixes a point of `ℍ`: a fixed point forces `(a + d)² < 4` if
`c ≠ 0`, impossible as `a + d ≡ 2 (mod 4)`; if `c = 0` then `a = d = 1` and `b = 0`. -/
theorem mcov_gamma2'_eq_one_of_smul_eq {γ : SL(2, ℤ)} (hγ : γ ∈ mcov_gamma2') {z : ℍ} (h : γ • z = z) :
    γ = 1 := by
  obtain ⟨hγ2, h4⟩ := hγ
  have hd4 := mcov_gamma2_d_mod4 hγ2 h4
  have hdet := mcov_sl_det γ
  have hz := congrArg (fun w : ℍ => (w : ℂ)) h
  simp only [UpperHalfPlane.coe_specialLinearGroup_apply, algebraMap_int_eq, eq_intCast,
    Complex.ofReal_intCast] at hz
  have hden : ((γ 1 0 : ℤ) : ℂ) * (z : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    have := ModularGroup.denom_apply γ z
    simpa [ModularGroup.denom_apply] using UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) z
  rw [div_eq_iff hden] at hz
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    Complex.add_im, Complex.mul_im, zero_mul, sub_zero, add_zero] at hre him
  set x := (z : ℂ).re
  set y := (z : ℂ).im
  have hy : 0 < y := z.im_pos
  set a := γ 0 0
  set b := γ 0 1
  set c := γ 1 0
  set d := γ 1 1
  by_cases hc : c = 0
  · -- `a d = 1`, `a ≡ 1 (4)` ⇒ `a = d = 1`, then `b = 0`
    rw [hc] at hdet him hre
    have had : a * d = 1 := by linarith
    have ha1 : a = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one had with h | h <;> omega
    have hd1 : d = 1 := by rw [ha1] at had; linarith
    have hb0 : b = 0 := by
      rw [ha1, hd1] at hre
      push_cast at hre
      have : (b : ℝ) = 0 := by linarith
      exact_mod_cast this
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [a, b, c, d, ha1, hb0, hc, hd1] at *
  · exfalso
    -- imaginary part: `a y = c (2 x y) + d y`, i.e. `a - d = 2 c x`
    have hx : (a : ℝ) - d = 2 * c * x := by
      have : ((a : ℝ) - d - 2 * c * x) * y = 0 := by linear_combination him
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
    -- real part and the determinant give `4 c² y² = 4 - (a + d)²`
    have hdetR : (a : ℝ) * d - b * c = 1 := by exact_mod_cast hdet
    have hkey : 4 * (c : ℝ) ^ 2 * y ^ 2 = 4 - ((a : ℝ) + d) ^ 2 := by
      linear_combination 4 * (c : ℝ) * hre + 4 * hdetR + ((a : ℝ) - d - 2 * c * x) * hx
    have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    have hpos : 0 < 4 * (c : ℝ) ^ 2 * y ^ 2 := by positivity
    have hlt : ((a + d : ℤ) : ℝ) ^ 2 < 4 := by push_cast; linarith
    have hltZ : (a + d) ^ 2 < 4 := by exact_mod_cast hlt
    have h1 : a + d ≤ 1 := by nlinarith
    have h2 : -1 ≤ a + d := by nlinarith
    omega

instance : IsCancelSMul mcov_G2 ℍ := isCancelSMul_iff_eq_one_of_smul_eq.2 fun g z h => by
  obtain ⟨g, γ, hγ, rfl⟩ := g
  have h1 : γ = 1 := mcov_gamma2'_eq_one_of_smul_eq hγ h
  subst h1
  ext1
  simp

theorem mcov_mem_orbit_G2_iff {e₁ e₂ : ℍ} :
    e₁ ∈ MulAction.orbit mcov_G2 e₂ ↔ ∃ γ ∈ mcov_gamma2', γ • e₂ = e₁ := by
  constructor
  · rintro ⟨⟨g, γ, hγ, rfl⟩, rfl⟩
    exact ⟨γ, hγ, rfl⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨⟨_, γ, hγ, rfl⟩, rfl⟩

/-- `Γ(2)`-orbits are `Γ(2)'`-orbits (`-1` acts trivially). -/
theorem mcov_mem_orbit_G2_iff_gamma2 {e₁ e₂ : ℍ} :
    e₁ ∈ MulAction.orbit mcov_G2 e₂ ↔ ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • e₂ = e₁ := by
  rw [mcov_mem_orbit_G2_iff]
  constructor
  · rintro ⟨γ, hγ, h⟩
    exact ⟨γ, hγ.1, h⟩
  · rintro ⟨γ, hγ, rfl⟩
    have hodd := mcov_gamma2_odd00 hγ
    rcases Int.emod_two_eq_zero_or_one (γ 0 0) with h | h
    · exact absurd (Int.odd_iff.1 hodd) (by omega)
    · by_cases h4 : γ 0 0 % 4 = 1
      · exact ⟨γ, ⟨hγ, h4⟩, rfl⟩
      · refine ⟨-γ, ⟨?_, ?_⟩, ModularGroup.SL_neg_smul γ e₂⟩
        · have hm1 : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma 2 := by
            rw [CongruenceSubgroup.Gamma_mem]
            simp
          simpa using mul_mem hm1 hγ
        · simp [Matrix.SpecialLinearGroup.coe_neg]
          omega

/-- the `Γ(2)` max-Im lemma, mirroring `ModularGroup.exists_max_im`. -/
theorem mcov_exists_max_im_gamma2 (z : ℍ) :
    ∃ g ∈ CongruenceSubgroup.Gamma 2,
      ∀ g' ∈ CongruenceSubgroup.Gamma 2, (g' • z).im ≤ (g • z).im := by
  let s : Set (Fin 2 → ℤ) :=
    {cd | ∃ g ∈ CongruenceSubgroup.Gamma 2, (g : Matrix (Fin 2) (Fin 2) ℤ) 1 = cd}
  have hs : s.Nonempty := ⟨_, 1, one_mem _, rfl⟩
  obtain ⟨p, ⟨g, hg, rfl⟩, hp⟩ :=
    Filter.Tendsto.exists_within_forall_le hs (ModularGroup.tendsto_normSq_coprime_pair z)
  refine ⟨g, hg, fun g' hg' => ?_⟩
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.im_smul_eq_div_normSq,
    div_le_div_iff_of_pos_left]
  · simpa [denom] using hp (g' 1) ⟨g', hg', rfl⟩
  · exact z.im_pos
  · exact normSq_denom_pos _ z.im_ne_zero
  · exact normSq_denom_pos _ z.im_ne_zero

/-- `(1 0; 2m 1)`, `w ↦ w/(2mw + 1)`. -/
def mcov_lowU (m : ℤ) : SL(2, ℤ) := ⟨!![1, 0; 2 * m, 1], by simp [Matrix.det_fin_two]⟩

theorem mcov_lowU_mem (m : ℤ) : mcov_lowU m ∈ CongruenceSubgroup.Gamma 2 := by
  rw [CongruenceSubgroup.Gamma_mem]
  refine ⟨by simp [mcov_lowU], by simp [mcov_lowU], ?_, by simp [mcov_lowU]⟩
  simp only [mcov_lowU, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one, Int.cast_mul, Int.cast_ofNat]
  rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]

theorem mcov_im_lowU_smul (m : ℤ) (z : ℍ) :
    (mcov_lowU m • z).im = z.im / Complex.normSq (2 * m * (z : ℂ) + 1) := by
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
  simp [mcov_lowU]

theorem mcov_T_zpow_mem (k : ℤ) : ModularGroup.T ^ (2 * k) ∈ CongruenceSubgroup.Gamma 2 :=
  CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma 2 (2 * k) (dvd_mul_right 2 k)

/-- every `τ ∈ ℍ` is `Γ(2)`-equivalent to a point of `F`. -/
theorem mcov_exists_gamma2_smul_mem_F (z : ℍ) : ∃ g ∈ CongruenceSubgroup.Gamma 2,
    |((g • z : ℍ) : ℂ).re| ≤ 1 ∧ 1 / 2 ≤ ‖((g • z : ℍ) : ℂ) - 1 / 2‖ ∧
      1 / 2 ≤ ‖((g • z : ℍ) : ℂ) + 1 / 2‖ := by
  obtain ⟨g₀, hg₀, hmax⟩ := mcov_exists_max_im_gamma2 z
  set n : ℤ := round (((g₀ • z : ℍ) : ℂ).re / 2) with hn
  set g := ModularGroup.T ^ (2 * (-n)) * g₀ with hg
  have hgΓ : g ∈ CongruenceSubgroup.Gamma 2 := mul_mem (mcov_T_zpow_mem _) hg₀
  have hgz : ((g • z : ℍ) : ℂ) = ((g₀ • z : ℍ) : ℂ) + (2 * (-n) : ℤ) := by
    rw [hg, mul_smul, ModularGroup.coe_T_zpow_smul_eq]
  have hmax' : ∀ g' ∈ CongruenceSubgroup.Gamma 2, (g' • z).im ≤ (g • z).im := by
    intro g' hg'
    have : (g • z).im = (g₀ • z).im := by
      simp only [UpperHalfPlane.im, hgz]
      simp
    rw [this]
    exact hmax g' hg'
  refine ⟨g, hgΓ, ?_, ?_, ?_⟩
  · rw [hgz]
    have h := abs_sub_round (((g₀ • z : ℍ) : ℂ).re / 2)
    rw [← hn] at h
    simp only [Complex.add_re, Complex.intCast_re]
    push_cast
    rw [abs_le] at h ⊢
    constructor <;> linarith [h.1, h.2]
  · by_contra hlt
    push Not at hlt
    have h1 := hmax' (mcov_lowU (-1) * g) (mul_mem (mcov_lowU_mem _) hgΓ)
    rw [mul_smul, mcov_im_lowU_smul] at h1
    set w : ℂ := ((g • z : ℍ) : ℂ)
    have hw : 0 < w.im := (g • z).im_pos
    have hns : Complex.normSq (2 * ((-1 : ℤ) : ℂ) * w + 1) < 1 := by
      have e : Complex.normSq (2 * ((-1 : ℤ) : ℂ) * w + 1) = 4 * ‖w - 1 / 2‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        simp
        ring
      rw [e]
      have : ‖w - 1 / 2‖ ^ 2 < (1 / 2) ^ 2 := by
        exact pow_lt_pow_left₀ hlt (norm_nonneg _) (by norm_num)
      linarith
    have hpos : 0 < Complex.normSq (2 * ((-1 : ℤ) : ℂ) * w + 1) :=
      Complex.normSq_pos.2 (fun h0 => by
        have := congrArg Complex.im h0
        simp at this
        linarith)
    have : w.im < w.im / Complex.normSq (2 * ((-1 : ℤ) : ℂ) * w + 1) := by
      rw [lt_div_iff₀ hpos]
      nlinarith
    exact absurd h1 (not_le.2 this)
  · by_contra hlt
    push Not at hlt
    have h1 := hmax' (mcov_lowU 1 * g) (mul_mem (mcov_lowU_mem _) hgΓ)
    rw [mul_smul, mcov_im_lowU_smul] at h1
    set w : ℂ := ((g • z : ℍ) : ℂ)
    have hw : 0 < w.im := (g • z).im_pos
    have hns : Complex.normSq (2 * ((1 : ℤ) : ℂ) * w + 1) < 1 := by
      have e : Complex.normSq (2 * ((1 : ℤ) : ℂ) * w + 1) = 4 * ‖w + 1 / 2‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        simp
        ring
      rw [e]
      have : ‖w + 1 / 2‖ ^ 2 < (1 / 2) ^ 2 := by
        exact pow_lt_pow_left₀ hlt (norm_nonneg _) (by norm_num)
      linarith
    have hpos : 0 < Complex.normSq (2 * ((1 : ℤ) : ℂ) * w + 1) :=
      Complex.normSq_pos.2 (fun h0 => by
        have := congrArg Complex.im h0
        simp at this
        linarith)
    have : w.im < w.im / Complex.normSq (2 * ((1 : ℤ) : ℂ) * w + 1) := by
      rw [lt_div_iff₀ hpos]
      nlinarith
    exact absurd h1 (not_le.2 this)

/-- `φ ∘ γ = φ` for `γ ∈ Γ(2)`, in the `ℍ`-action form. -/
theorem mcov_phi_smul {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma 2) (τ : ℍ) :
    modularPhi ((γ • τ : ℍ) : ℂ) = modularPhi τ := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simpa using modularPhi_gamma2_invariant hγ τ.im_pos

theorem mcov_norm_sub_half_sq (w : ℂ) : ‖w - 1 / 2‖ ^ 2 = (w.re - 1 / 2) ^ 2 + w.im ^ 2 :=
  mphi_w4_norm_sub_half_sq w

/-- the points of `F`: in `A`, in `A - 1`, or on a side where `φ` is real. -/
theorem mcov_F_cases {w : ℂ} (hw : 0 < w.im) (h1 : |w.re| ≤ 1) (h2 : 1 / 2 ≤ ‖w - 1 / 2‖)
    (h3 : 1 / 2 ≤ ‖w + 1 / 2‖) :
    w ∈ modularRegionA ∨ w + 1 ∈ modularRegionA ∨ (modularPhi w).im = 0 := by
  rw [abs_le] at h1
  have hw1 : 0 < (w + 1).im := by simpa using hw
  have e3 : ‖w + 1 / 2‖ = ‖(w + 1) - 1 / 2‖ := by ring_nf
  rcases lt_trichotomy w.re 0 with hre | hre | hre
  · rcases h1.1.lt_or_eq with hlt | heq
    · -- `-1 < Re w < 0`
      rcases h3.lt_or_eq with h3' | h3'
      · right; left
        refine ⟨by simp; linarith, by simp; linarith, by rw [← e3]; exact h3', hw1⟩
      · right; right
        have hs := mphi_modularPhi_im_eq_zero_of_side hw1 (Or.inr (Or.inr (by rw [← e3, h3'])))
        have h11 := eq14_11 hw
        rw [h11] at hs
        simpa using hs
    · -- `Re w = -1`
      right; right
      have hw2 : 0 < (w + 2).im := by simpa using hw
      have hs := mphi_modularPhi_im_eq_zero_of_side hw2 (Or.inr (Or.inl (by simp; linarith)))
      rwa [eq14_4 hw] at hs
  · right; right
    exact mphi_modularPhi_im_eq_zero_of_side hw (Or.inl hre)
  · rcases h1.2.lt_or_eq with hlt | heq
    · rcases h2.lt_or_eq with h2' | h2'
      · left
        exact ⟨hre, hlt, h2', hw⟩
      · right; right
        exact mphi_modularPhi_im_eq_zero_of_side hw (Or.inr (Or.inr h2'.symm))
    · right; right
      exact mphi_modularPhi_im_eq_zero_of_side hw (Or.inr (Or.inl heq))

theorem mcov_im_phi_pos_of_mem_A {w : ℂ} (hw : w ∈ modularRegionA) : 0 < (modularPhi w).im := by
  have h := mphi_isConformalOnto_modularPhi.2.2
  have : modularPhi w ∈ modularPhi '' modularRegionA := ⟨w, hw, rfl⟩
  rw [h] at this
  exact this

theorem mcov_phi_eq_one_sub {w : ℂ} (hw : 0 < w.im) : modularPhi w = 1 - modularPhi (w + 1) := by
  rw [eq14_11 hw]
  ring

/-- fiber = orbit over the non-real values. -/
theorem mcov_fiber_nonreal {u u' : ℍ} (h : modularPhiH u = modularPhiH u')
    (him : (modularPhiH u).im ≠ 0) : ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • u' = u := by
  obtain ⟨g, hg, hF⟩ := mcov_exists_gamma2_smul_mem_F u
  obtain ⟨g', hg', hF'⟩ := mcov_exists_gamma2_smul_mem_F u'
  set p : ℍ := g • u with hpdef
  set p' : ℍ := g' • u' with hp'def
  have hφ : modularPhi (p : ℂ) = modularPhi (p' : ℂ) := by
    rw [hpdef, hp'def, mcov_phi_smul hg, mcov_phi_smul hg']
    exact h
  have himp : (modularPhi (p : ℂ)).im ≠ 0 := by
    rw [hpdef, mcov_phi_smul hg]
    exact him
  suffices hpp : (p : ℂ) = (p' : ℂ) by
    refine ⟨g⁻¹ * g', mul_mem (inv_mem hg) hg', ?_⟩
    have : p = p' := UpperHalfPlane.ext hpp
    rw [mul_smul, ← hp'def, ← this, hpdef, inv_smul_smul]
  have hinjA := mphi_isConformalOnto_modularPhi.2.1
  rcases mcov_F_cases p.im_pos hF.1 hF.2.1 hF.2.2 with hA | hA | hr <;>
  rcases mcov_F_cases p'.im_pos hF'.1 hF'.2.1 hF'.2.2 with hA' | hA' | hr'
  · exact hinjA hA hA' hφ
  · exfalso
    have a := mcov_im_phi_pos_of_mem_A hA
    have b := mcov_im_phi_pos_of_mem_A hA'
    rw [hφ, mcov_phi_eq_one_sub p'.im_pos] at a
    simp at a
    linarith
  · exact absurd (hφ ▸ hr') himp
  · exfalso
    have a := mcov_im_phi_pos_of_mem_A hA
    have b := mcov_im_phi_pos_of_mem_A hA'
    rw [← hφ, mcov_phi_eq_one_sub p.im_pos] at b
    simp at b
    linarith
  · have e : modularPhi ((p : ℂ) + 1) = modularPhi ((p' : ℂ) + 1) := by
      rw [eq14_11 p.im_pos, eq14_11 p'.im_pos, hφ]
    have := hinjA hA hA' e
    simpa using this
  · exact absurd (hφ ▸ hr') himp
  · exact absurd hr himp
  · exact absurd hr himp
  · exact absurd hr himp

theorem mcov_quadLambda_pos' {ρ : ℝ} (hρ : 0 < ρ) : 0 < quadLambda ρ := by
  have h : quadLambda ρ = (⟨upperHalf, _, isTopQuad_upperHalf_lambda hρ⟩ : TopQuad).modulus := rfl
  rw [h]
  exact modulus_pos _

/-- `φ(iΛ(ρ)) = -ρ`. -/
theorem mcov_phi_I_quadLambda {ρ : ℝ} (hρ : 0 < ρ) :
    modularPhi ((quadLambda ρ : ℂ) * Complex.I) = -ρ := by
  have hv := mcov_quadLambda_pos' hρ
  have h19 := eq14_19 hv
  rw [lambdaInv_quadLambda hρ] at h19
  have him := (eq14_13_15 hv).1
  apply Complex.ext
  · simp only [Complex.neg_re, Complex.ofReal_re]
    linarith
  · simp [him]

theorem mcov_surj_modularPhi {z : ℂ} (hz : z ≠ 0 ∧ z ≠ 1) : ∃ τ : ℍ, modularPhiH τ = z := by
  have himg := mphi_isConformalOnto_modularPhi.2.2
  rcases lt_trichotomy z.im 0 with hlt | heq | hgt
  · -- lower half-plane: `1 - z = φ(w)`, `w ∈ A`, and `φ(w - 1) = 1 - φ(w)`
    have h1z : (1 - z) ∈ modularPhi '' modularRegionA := by
      rw [himg]
      show 0 < (1 - z).im
      simp
      linarith
    obtain ⟨w, hwA, hw⟩ := h1z
    have hw1 : 0 < (w - 1).im := by simpa using hwA.2.2.2
    refine ⟨⟨w - 1, hw1⟩, ?_⟩
    show modularPhi (w - 1) = z
    have := eq14_11 hw1
    rw [sub_add_cancel, hw] at this
    linear_combination this
  · -- real axis: `z = x`, `x ∉ {0, 1}`
    have hzx : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [heq])
    set x := z.re
    rcases lt_trichotomy x 0 with hx | hx | hx
    · -- `x < 0`: `φ(iΛ(-x)) = x`
      have hρ : 0 < -x := by linarith
      have hv := mcov_quadLambda_pos' hρ
      refine ⟨⟨(quadLambda (-x) : ℂ) * Complex.I, by simpa using hv⟩, ?_⟩
      show modularPhi _ = z
      rw [mcov_phi_I_quadLambda hρ, hzx]
      push_cast
      ring
    · exact absurd (hzx.trans (by rw [hx]; simp)) hz.1
    · rcases lt_trichotomy x 1 with hx1 | hx1 | hx1
      · -- `0 < x < 1`: `x = 1/(1 + ρ)`, `ρ = 1/x - 1`, `φ(-1/(iΛ(ρ) + 1)) = 1/φ(iΛ(ρ) + 1)`
        have hρ : 0 < 1 / x - 1 := by
          rw [sub_pos, lt_div_iff₀ hx]
          linarith
        have hv := mcov_quadLambda_pos' hρ
        set w : ℂ := (quadLambda (1 / x - 1) : ℂ) * Complex.I + 1 with hwdef
        have hw : 0 < w.im := by simpa [hwdef] using hv
        have hw' : 0 < (-1 / w).im := by
          have hne : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
          have e : (-1 / w).im = w.im / Complex.normSq w := by
            rw [Complex.div_im]
            simp
            ring
          rw [e]
          exact div_pos hw (Complex.normSq_pos.2 hne)
        refine ⟨⟨-1 / w, hw'⟩, ?_⟩
        show modularPhi (-1 / w) = z
        have hIv : 0 < ((quadLambda (1 / x - 1) : ℂ) * Complex.I).im := by simpa using hv
        rw [eq14_12 hw, hwdef, eq14_11 hIv, mcov_phi_I_quadLambda hρ, hzx]
        have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
        push_cast
        field_simp
        ring
      · exact absurd (hzx.trans (by rw [hx1]; simp)) hz.2
      · -- `x > 1`: `φ(iΛ(x - 1) + 1) = 1 - φ(iΛ(x-1)) = x`
        have hρ : 0 < x - 1 := by linarith
        have hv := mcov_quadLambda_pos' hρ
        have hIv : 0 < ((quadLambda (x - 1) : ℂ) * Complex.I).im := by simpa using hv
        refine ⟨⟨(quadLambda (x - 1) : ℂ) * Complex.I + 1, by simpa using hv⟩, ?_⟩
        show modularPhi _ = z
        rw [eq14_11 hIv, mcov_phi_I_quadLambda hρ, hzx]
        push_cast
        ring
  · -- upper half-plane: (14.20)
    have : z ∈ modularPhi '' modularRegionA := by rw [himg]; exact hgt
    obtain ⟨w, hwA, hw⟩ := this
    exact ⟨⟨w, hwA.2.2.2⟩, hw⟩

/-! ### analytic facts -/

theorem mcov_phiH_eq (τ : ℍ) : modularPhiH τ = modularPhi τ := rfl

theorem mcov_continuous_modularPhiH : Continuous modularPhiH :=
  mphi_differentiableOn_modularPhi_upperHalf.continuousOn.comp_continuous
    UpperHalfPlane.continuous_coe fun τ => τ.im_pos

/-- `φ` is not constant on `ℍ`: it maps `A` onto `ℍ`. -/
theorem mcov_modularPhi_not_const : ¬ ∃ c, ∀ w ∈ upperHalf, modularPhi w = c := by
  rintro ⟨c, hc⟩
  have himg := mphi_isConformalOnto_modularPhi.2.2
  have hsub : modularPhi '' modularRegionA ⊆ {c} := by
    rintro _ ⟨w, hw, rfl⟩
    exact hc w (mphi_w4_modularRegionA_subset_upperHalf hw)
  rw [himg] at hsub
  have h1 : Complex.I ∈ upperHalf := by simp [upperHalf]
  have h2 : 2 * Complex.I ∈ upperHalf := by simp [upperHalf]
  have e1 := hsub h1
  have e2 := hsub h2
  simp only [mem_singleton_iff] at e1 e2
  have : (2 : ℂ) * Complex.I = Complex.I := e2.trans e1.symm
  have := congrArg Complex.im this
  simp at this

theorem mcov_isOpenMap_modularPhiH : IsOpenMap modularPhiH := by
  have han : AnalyticOnNhd ℂ modularPhi upperHalf :=
    mphi_differentiableOn_modularPhi_upperHalf.analyticOnNhd isOpen_upperHalf
  rcases han.is_constant_or_isOpen isConnected_upperHalf.isPreconnected with h | h
  · exact absurd h mcov_modularPhi_not_const
  · intro s hs
    have hs' : IsOpen (((↑) : ℍ → ℂ) '' s) := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap s hs
    have hsub : ((↑) : ℍ → ℂ) '' s ⊆ upperHalf := by
      rintro _ ⟨τ, -, rfl⟩
      exact τ.im_pos
    have := h _ hsub hs'
    rwa [image_image] at this

theorem mcov_modularPhi_ne_zero_one (τ : ℍ) : modularPhiH τ ≠ 0 ∧ modularPhiH τ ≠ 1 := by
  obtain ⟨h01, h02, h12⟩ := mphi_weierstrassE_pairwise_ne τ.im_pos
  have hd : weierstrassE (τ : ℂ) 2 - weierstrassE (τ : ℂ) 1 ≠ 0 := sub_ne_zero.2 (Ne.symm h12)
  refine ⟨?_, ?_⟩
  · rw [mcov_phiH_eq, modularPhi, div_ne_zero_iff]
    exact ⟨sub_ne_zero.2 (Ne.symm h02), hd⟩
  · rw [mcov_phiH_eq, modularPhi, Ne, div_eq_one_iff_eq hd]
    intro h
    exact h01 (by linear_combination -h)

/-! ### the abstract closure argument -/

/-- If a continuous open `f : E → ℂ` has its fibers over non-real values inside a closed relation
`R`, then all its fibers are inside `R`. -/
theorem mcov_fiber_mem_of_nonreal {E : Type*} [TopologicalSpace E] {f : E → ℂ} (hc : Continuous f)
    (ho : IsOpenMap f) {R : Set (E × E)} (hR : IsClosed R)
    (h : ∀ u u', f u = f u' → (f u).im ≠ 0 → (u, u') ∈ R) {w w' : E} (hww : f w = f w') :
    (w, w') ∈ R := by
  rw [← hR.closure_eq, mem_closure_iff_nhds]
  intro t ht
  rw [nhds_prod_eq, Filter.mem_prod_iff] at ht
  obtain ⟨U, hU, V, hV, hUV⟩ := ht
  obtain ⟨U', hU'U, hU'o, hwU'⟩ := mem_nhds_iff.1 hU
  obtain ⟨V', hV'V, hV'o, hwV'⟩ := mem_nhds_iff.1 hV
  set W := U' ∩ f ⁻¹' (f '' V') with hW
  have hWo : IsOpen W := hU'o.inter ((ho V' hV'o).preimage hc)
  have hwW : w ∈ W := ⟨hwU', w', hwV', hww.symm⟩
  have hfWo : IsOpen (f '' W) := ho W hWo
  obtain ⟨ζ, hζW, hζ⟩ : ∃ ζ ∈ f '' W, ζ.im ≠ 0 := by
    by_cases hz : (f w).im = 0
    · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hfWo (f w) ⟨w, hwW, rfl⟩
      refine ⟨f w + ((ε / 2 : ℝ) : ℂ) * Complex.I, hball ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I,
          mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        linarith
      · simp [hz, hε.ne']
    · exact ⟨f w, ⟨w, hwW, rfl⟩, hz⟩
  obtain ⟨u, ⟨huU', v, hvV', hfv⟩, rfl⟩ := hζW
  exact ⟨(u, v), hUV ⟨hU'U huU', hV'V hvV'⟩, h u v hfv.symm hζ⟩

/-- the closed orbit relation (P02). -/
theorem mcov_isClosed_orbitRel : IsClosed {p : ℍ × ℍ | p.1 ∈ MulAction.orbit mcov_G2 p.2} := by
  have : T2Space (Quotient (MulAction.orbitRel mcov_G2 ℍ)) :=
    t2Space_of_properlyDiscontinuousSMul_of_t2Space
  have h : {p : ℍ × ℍ | p.1 ∈ MulAction.orbit mcov_G2 p.2} =
      {p : ℍ × ℍ | (Quotient.mk (MulAction.orbitRel mcov_G2 ℍ) p.1) =
        Quotient.mk (MulAction.orbitRel mcov_G2 ℍ) p.2} := by
    ext p
    simp only [mem_ofPred_eq, Quotient.eq, MulAction.orbitRel_apply]
  rw [h]
  exact isClosed_eq (continuous_quotient_mk'.comp continuous_fst)
    (continuous_quotient_mk'.comp continuous_snd)

/-- fiber = orbit. -/
theorem mcov_phiH_eq_iff {e₁ e₂ : ℍ} :
    modularPhiH e₁ = modularPhiH e₂ ↔ e₁ ∈ MulAction.orbit mcov_G2 e₂ := by
  constructor
  · intro h
    have := mcov_fiber_mem_of_nonreal mcov_continuous_modularPhiH mcov_isOpenMap_modularPhiH mcov_isClosed_orbitRel
      (fun u u' huu hne => mcov_mem_orbit_G2_iff_gamma2.2 (mcov_fiber_nonreal huu hne)) h
    exact this
  · intro h
    obtain ⟨γ, hγ, rfl⟩ := mcov_mem_orbit_G2_iff_gamma2.1 h
    rw [mcov_phiH_eq, mcov_phiH_eq, UpperHalfPlane.coe_specialLinearGroup_apply]
    simpa using modularPhi_gamma2_invariant hγ e₂.im_pos

/-! ### assembly -/

def mcov_S01 : Set ℂ := {z : ℂ | z ≠ 0 ∧ z ≠ 1}

theorem mcov_isOpen_S01 : IsOpen mcov_S01 := by
  have : mcov_S01 = {(0 : ℂ)}ᶜ ∩ {(1 : ℂ)}ᶜ := by ext z; simp [mcov_S01]
  rw [this]
  exact isOpen_compl_singleton.inter isOpen_compl_singleton

def mcov_phiS (τ : ℍ) : mcov_S01 := ⟨modularPhiH τ, mcov_modularPhi_ne_zero_one τ⟩

/-- §14.2: `φ` maps `ℍ` onto `ℂ ∖ {0, 1}` and is a covering map (`ℍ` is the universal covering of
`ℂ̄ ∖ {0, 1, ∞}`). -/
theorem modularPhi_covering :
    range modularPhiH = {z : ℂ | z ≠ 0 ∧ z ≠ 1} ∧
      IsCoveringMapOn modularPhiH {z : ℂ | z ≠ 0 ∧ z ≠ 1} := by
  have hsurj : Function.Surjective mcov_phiS := fun z => by
    obtain ⟨τ, hτ⟩ := mcov_surj_modularPhi z.2
    exact ⟨τ, Subtype.ext hτ⟩
  have hcont : Continuous mcov_phiS := mcov_continuous_modularPhiH.subtype_mk _
  have hopen : IsOpenMap mcov_phiS := by
    intro s hs
    have e : mcov_phiS '' s = Subtype.val ⁻¹' (modularPhiH '' s) := by
      ext z
      constructor
      · rintro ⟨τ, hτ, rfl⟩
        exact ⟨τ, hτ, rfl⟩
      · rintro ⟨τ, hτ, h⟩
        exact ⟨τ, hτ, Subtype.ext h⟩
    rw [e]
    exact (mcov_isOpenMap_modularPhiH s hs).preimage continuous_subtype_val
  have hq : Topology.IsQuotientMap mcov_phiS := hopen.isQuotientMap hcont hsurj
  have hfib : ∀ {e₁ e₂ : ℍ}, mcov_phiS e₁ = mcov_phiS e₂ ↔ e₁ ∈ MulAction.orbit mcov_G2 e₂ := by
    intro e₁ e₂
    rw [← mcov_phiH_eq_iff]
    exact Subtype.ext_iff
  have hcov : IsCoveringMap mcov_phiS :=
    (hq.isQuotientCoveringMap_of_properlyDiscontinuousSMul (G := mcov_G2) hfib).isCoveringMap
  refine ⟨?_, IsCoveringMapOn.of_isCoveringMap_subtype mcov_isOpen_S01
    (fun τ => mcov_modularPhi_ne_zero_one τ) hcov⟩
  ext z
  constructor
  · rintro ⟨τ, rfl⟩
    exact mcov_modularPhi_ne_zero_one τ
  · intro hz
    exact mcov_surj_modularPhi hz


/-- the Möbius map of `γ` as a `realMobius`. -/
abbrev mcov_mobOf (γ : SL(2, ℤ)) : ℂ → ℂ :=
  realMobius (γ 0 0 : ℝ) (γ 0 1 : ℝ) (γ 1 0 : ℝ) (γ 1 1 : ℝ)

theorem mcov_mobOf_det (γ : SL(2, ℤ)) :
    ((γ 0 0 : ℝ) * (γ 1 1 : ℝ) - (γ 0 1 : ℝ) * (γ 1 0 : ℝ)) = 1 := by
  exact_mod_cast mcov_sl_det γ

/-- `|φ'(γw)| Im(γw) = |φ'(w)| Im w` for `γ ∈ Γ(2)`. -/
theorem mcov_norm_deriv_mul_im_invariant {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma 2)
    {w : ℂ} (hw : 0 < w.im) :
    ‖deriv modularPhi (mcov_mobOf γ w)‖ * (mcov_mobOf γ w).im = ‖deriv modularPhi w‖ * w.im := by
  have hdet1 := mcov_mobOf_det γ
  have hdet : (0 : ℝ) < (γ 0 0 : ℝ) * (γ 1 1 : ℝ) - (γ 0 1 : ℝ) * (γ 1 0 : ℝ) := by
    rw [hdet1]; exact one_pos
  have hden := realMobius_den_ne_zero hdet hw
  have hM := hasDerivAt_realMobius (a := (γ 0 0 : ℝ)) (b := (γ 0 1 : ℝ)) hden
  rw [hdet1] at hM
  have hMw : mcov_mobOf γ w ∈ upperHalf := realMobius_mem_upperHalf hdet hw
  have hφd : DifferentiableAt ℂ modularPhi (mcov_mobOf γ w) :=
    (mphi_differentiableOn_modularPhi_upperHalf _ hMw).differentiableAt
      (isOpen_upperHalf.mem_nhds hMw)
  have heq : modularPhi ∘ mcov_mobOf γ =ᶠ[𝓝 w] modularPhi := by
    filter_upwards [isOpen_upperHalf.mem_nhds hw] with v hv
    have := modularPhi_gamma2_invariant hγ (w := v) hv
    simpa [mcov_mobOf, realMobius] using this
  have h1 : deriv (modularPhi ∘ mcov_mobOf γ) w = deriv modularPhi w := heq.deriv_eq
  have h2 : deriv (modularPhi ∘ mcov_mobOf γ) w =
      deriv modularPhi (mcov_mobOf γ w) * deriv (mcov_mobOf γ) w :=
    deriv_comp w hφd hM.differentiableAt
  rw [hM.deriv, h1] at h2
  rw [h2, im_realMobius, hdet1, norm_mul, norm_div, norm_pow, Complex.sq_norm]
  have hns : 0 < normSq ((γ 1 0 : ℝ) * w + (γ 1 1 : ℝ)) := normSq_pos.2 hden
  push_cast
  field_simp
  simp

/-- fiber = orbit in `ℂ`-form. -/
theorem mcov_fiber_gamma2 {w₁ w₂ : ℂ} (h₁ : 0 < w₁.im) (h₂ : 0 < w₂.im)
    (h : modularPhi w₁ = modularPhi w₂) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, w₁ = mcov_mobOf γ w₂ := by
  have h' := (mcov_phiH_eq_iff (e₁ := ⟨w₁, h₁⟩) (e₂ := ⟨w₂, h₂⟩)).1 h
  obtain ⟨γ, hγ, hγe⟩ := mcov_mem_orbit_G2_iff_gamma2.1 h'
  refine ⟨γ, hγ, ?_⟩
  have e := congrArg (fun τ : ℍ => (τ : ℂ)) hγe
  simp only [UpperHalfPlane.coe_specialLinearGroup_apply] at e
  rw [← e]
  simp [mcov_mobOf, realMobius]

/-- (14.6): `η` does not depend on the branch of `ψ = φ⁻¹`. -/
theorem eq14_6_well_defined {w₁ w₂ : ℂ} (h₁ : 0 < w₁.im) (h₂ : 0 < w₂.im)
    (h : modularPhi w₁ = modularPhi w₂) :
    1 / (‖deriv modularPhi w₁‖ * w₁.im) = 1 / (‖deriv modularPhi w₂‖ * w₂.im) ∧
      puncturedSphereDensity (modularPhi w₁) = 1 / (‖deriv modularPhi w₁‖ * w₁.im) := by
  have key : ∀ {u v : ℂ}, 0 < u.im → 0 < v.im → modularPhi u = modularPhi v →
      ‖deriv modularPhi u‖ * u.im = ‖deriv modularPhi v‖ * v.im := by
    intro u v hu hv huv
    obtain ⟨γ, hγ, rfl⟩ := mcov_fiber_gamma2 hu hv huv
    exact mcov_norm_deriv_mul_im_invariant hγ hv
  refine ⟨by rw [key h₁ h₂ h], ?_⟩
  have hS : {r : ℝ | ∃ w : ℂ, 0 < w.im ∧ modularPhi w = modularPhi w₁ ∧
      r = 1 / (‖deriv modularPhi w‖ * w.im)} = {1 / (‖deriv modularPhi w₁‖ * w₁.im)} := by
    ext r
    constructor
    · rintro ⟨w, hw, hφ, rfl⟩
      rw [mem_singleton_iff, key hw h₁ hφ]
    · rintro rfl
      exact ⟨w₁, h₁, rfl, rfl⟩
  rw [puncturedSphereDensity, hS, csSup_singleton]

end ModularCovering

end LiZhongQC
