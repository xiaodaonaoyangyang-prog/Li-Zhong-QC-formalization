import References.GardinerLakic2000.Ch02.S04_TeichmullerSpace

/-!
# Gardiner–Lakic 2000, Ch. 2 §2.5 Metrics of constant curvature

Source `teichmuller.txt`, lines 1384–1566 (Chapter 2, §2.5).

* Formula (2.5) (Gaussian curvature `κ(ρ) = −ρ⁻² Δ log ρ`, l. 1396) — `laplacianGL`, `gaussCurvature`
* Formulas (2.8)–(2.10) (the Poincaré densities of ℍ, of a simply connected Ω, of Δ; curvature −4, l. 1444–1462) —
  exists: `Gehring1978.hypDensity` (the density of a simply connected domain through a conformal map onto the
  disc, curvature −4, the same normalization)
* Formula (2.11) (the distance of a density, by piecewise smooth paths, l. 1478) — `pathDist`
* Formula (2.14) (`|A′|/(1 − |A|²) = 1/(1 − |z|²)`, l. 1502; cited at l. 1458) — exists:
  `LiZhongQC.poincareDensityDisc_invariant` (the same identity multiplied by 2 on both sides)
* Formula (2.16) (the distance on Δ, l. 1518) — exists: `LiZhongQC.discPoincareDist`
* Proposition 2 (l. 1523) — `prop2_2_a`, `prop2_2_b`, `prop2_2_c`, `prop2_2_d`
* Lemma 1 (the Schwarz–Pick lemma, l. 1542; cited in Ch. 11) — `lemma2_1_a`, `lemma2_1_b`
* Formula (2.18) (the Poincaré density of a hyperbolic surface as an extremal quantity, l. 1555–1563; used in §2.6,
  Ch. 3, Ch. 11) — `poincareDensityGL`, `eq2_18`

Not items: the conformal invariance of `κ` (l. 1400–1419) and the curvature `+4` of the spherical metric (2.7)
(l. 1421–1436), U−; the Remark after Proposition 2 on other simply connected domains (l. 1526, U−); the contraction
remark (l. 1553, U−). Modelling: (2.18) is read for plane domains (leader ruling A0.4(ii)) and taken as the
definition of the Poincaré density; `eq2_18` states that the infimum is attained by the universal coverings, which
is how the book defines the density (through `ℍ/Γ`). Lemma 1: "for every `p` and `q`" (l. 1546) reads `z`, `w`
[misprint; so also GL8:1514]. `hypDensityDisc` is the explicit density (2.10).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (unitDisc discPoincareDist)

/-- Helper (§2.5, l. 1400). The Laplacian `Δu = u_xx + u_yy` of a function of the plane. -/
def laplacianGL (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  iteratedFDeriv ℝ 2 u z ![1, 1] + iteratedFDeriv ℝ 2 u z ![I, I]

/-- **Formula (2.5)** (§2.5, l. 1396). The Gaussian curvature `κ(ρ) = −ρ⁻² Δ log ρ` of the metric `ρ |dz|`. -/
def gaussCurvature (ρ : ℂ → ℝ) (z : ℂ) : ℝ := -(ρ z)⁻¹ ^ 2 * laplacianGL (fun w => Real.log (ρ w)) z

/-- **Formula (2.10)** (§2.5, l. 1462), explicitly. The Poincaré density `1/(1 − |z|²)` of the unit disc (curvature
−4; it is `Gehring1978.hypDensity` of the disc). -/
def hypDensityDisc (z : ℂ) : ℝ := 1 / (1 - ‖z‖ ^ 2)

/-- **Formula (2.11)** (§2.5, l. 1468–1478). The distance of the metric `ρ |dz|` in `U`: the infimum of the lengths
`∫ ρ(α(t)) |α′(t)| dt` of the piecewise smooth paths `α : [0, 1] → U` from `a` to `b` (continuous, `C¹` off finitely
many parameters, of finite length).
**[CORRECTION/modelling]** (leader, 2026-10-05; found by -3c) The finite-length conjunct (`ρ(α)|α′|` interval
integrable) is required: a path that is `C¹` only off finitely many parameters can spiral into a point with infinite
length, and its interval integral is then the junk value `0`, which made the infimum `0` for all `a, b`. The book's
piecewise smooth paths (smooth on closed pieces) have finite length, so the infimum is unchanged on them. -/
def pathDist (ρ : ℂ → ℝ) (U : Set ℂ) (a b : ℂ) : ℝ :=
  sInf {ℓ | ∃ (α : ℝ → ℂ) (s : Finset ℝ), α 0 = a ∧ α 1 = b ∧ MapsTo α (Icc 0 1) U ∧ ContinuousOn α (Icc 0 1) ∧
    ContDiffOn ℝ 1 α (Icc 0 1 \ ↑s) ∧ IntervalIntegrable (fun t => ρ (α t) * ‖deriv α t‖) volume 0 1 ∧
    ℓ = ∫ t in (0 : ℝ)..1, ρ (α t) * ‖deriv α t‖}

/-- Helper (§2.5, (2.14)–(2.15)). A rotated Blaschke factor `v ↦ c B_a(v)` (`|c| = 1`, `a ∈ Δ`) is a holomorphic
self-map of `Δ` that preserves the density: `ρ(A v) |A′(v)| = ρ(v)`. -/
theorem gl2c_rb_props {c a : ℂ} (hc : ‖c‖ = 1) (ha : a ∈ unitDisc) :
    DifferentiableOn ℂ (fun v => c * LiZhongQC.blaschke a v) unitDisc ∧
      MapsTo (fun v => c * LiZhongQC.blaschke a v) unitDisc unitDisc ∧
      ∀ v ∈ unitDisc, hypDensityDisc (c * LiZhongQC.blaschke a v) *
        ‖deriv (fun v => c * LiZhongQC.blaschke a v) v‖ = hypDensityDisc v := by
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.1 ha
  refine ⟨(LiZhongQC.differentiableOn_blaschke ha1).const_mul c, fun v hv => ?_, fun v hv => ?_⟩
  · rw [LiZhongQC.unitDisc, mem_ball_zero_iff, norm_mul, hc, one_mul]
    exact LiZhongQC.blaschke_mem_unitDisc ha1 (mem_ball_zero_iff.1 hv)
  · have hv1 : ‖v‖ < 1 := mem_ball_zero_iff.1 hv
    rw [deriv_const_mul c (LiZhongQC.hasDerivAt_blaschke ha1 hv1).differentiableAt, norm_mul, hc, one_mul]
    have e : hypDensityDisc (c * LiZhongQC.blaschke a v) = hypDensityDisc (LiZhongQC.blaschke a v) := by
      simp only [hypDensityDisc, norm_mul, hc, one_mul]
    -- `l21a_density_blaschke` (below this block in the file), inline from the S14 identity
    have hρ : ∀ w : ℂ, hypDensityDisc w = LiZhongQC.poincareDensityDisc w / 2 := fun w => by
      show (1 / (1 - ‖w‖ ^ 2)) = 2 / (1 - ‖w‖ ^ 2) / 2
      ring
    rw [e, hρ, hρ, div_mul_eq_mul_div, div_eq_div_iff two_ne_zero two_ne_zero,
      LiZhongQC.poincareDensityDisc_pullback_blaschke ha1 hv1]

/-- Helper (§2.5). The inverse of `v ↦ c B_a(v)` on `Δ` is `y ↦ c̄ B_{−ca}(y)`. -/
theorem gl2c_rb_inv {c a : ℂ} (hc : ‖c‖ = 1) (ha : a ∈ unitDisc) {v : ℂ} (hv : v ∈ unitDisc) :
    conj c * LiZhongQC.blaschke (-(c * a)) (c * LiZhongQC.blaschke a v) = v := by
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.1 ha
  have hv1 : ‖v‖ < 1 := mem_ball_zero_iff.1 hv
  have hcc : conj c * c = 1 := by
    rw [Complex.conj_mul', hc]
    norm_num
  set B := LiZhongQC.blaschke a v
  -- `B_{−ca}(c B) = c B_{−a}(B)`, and `B_{−a}(B_a v) = v`
  have key : LiZhongQC.blaschke (-(c * a)) (c * B) = c * LiZhongQC.blaschke (-a) B := by
    unfold LiZhongQC.blaschke
    have hden : 1 - conj (-(c * a)) * (c * B) = 1 - conj (-a) * B := by
      rw [map_neg, map_mul, map_neg]
      linear_combination (conj a * B) * hcc
    rw [hden]
    ring
  rw [key, ← mul_assoc, hcc, one_mul]
  exact LiZhongQC.blaschke_neg_blaschke ha1 hv1

/-- Helper (§2.5). A rotation of `B_z` sends `w` to the pseudo-hyperbolic distance `|(z − w)/(1 − z̄w)| ≥ 0`. -/
theorem gl2c_normalize (z w : ℂ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ c * LiZhongQC.blaschke z w = (‖(z - w) / (1 - conj z * w)‖ : ℂ) := by
  have e : (z - w) / (1 - conj z * w) = -LiZhongQC.blaschke z w := by
    unfold LiZhongQC.blaschke
    ring
  by_cases h0 : LiZhongQC.blaschke z w = 0
  · refine ⟨1, norm_one, ?_⟩
    rw [h0, mul_zero, e, h0, neg_zero, norm_zero, Complex.ofReal_zero]
  · have hn : (‖LiZhongQC.blaschke z w‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 h0)
    refine ⟨conj (LiZhongQC.blaschke z w) / ‖LiZhongQC.blaschke z w‖, ?_, ?_⟩
    · rw [norm_div, RCLike.norm_conj, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 h0)]
    · rw [e, norm_neg, div_mul_eq_mul_div, Complex.conj_mul']
      field_simp

/-- Helper (§2.5). Transport of an admissible path by a density-preserving holomorphic self-map `A` of `Δ`: the image
path is admissible, and the length integrands agree off the exceptional parameters. -/
theorem gl2c_transport {A : ℂ → ℂ} (hA : DifferentiableOn ℂ A unitDisc) (hAm : MapsTo A unitDisc unitDisc)
    (hAρ : ∀ v ∈ unitDisc, hypDensityDisc (A v) * ‖deriv A v‖ = hypDensityDisc v)
    {α : ℝ → ℂ} {s : Finset ℝ} (hαm : MapsTo α (Icc 0 1) unitDisc) (hαc : ContinuousOn α (Icc 0 1))
    (hαd : ContDiffOn ℝ 1 α (Icc 0 1 \ ↑s)) :
    MapsTo (fun t => A (α t)) (Icc 0 1) unitDisc ∧ ContinuousOn (fun t => A (α t)) (Icc 0 1) ∧
      ContDiffOn ℝ 1 (fun t => A (α t)) (Icc 0 1 \ ↑s) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1 \ ↑s, hypDensityDisc (A (α t)) * ‖deriv (fun t => A (α t)) t‖ =
        hypDensityDisc (α t) * ‖deriv α t‖ := by
  have hAc : ContDiffOn ℝ 1 A unitDisc := (hA.contDiffOn isOpen_ball).restrict_scalars ℝ
  refine ⟨fun t ht => hAm (hαm ht), hA.continuousOn.comp hαc hαm, hAc.comp hαd fun t ht => hαm ht.1,
    fun t ht => ?_⟩
  have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht.1
  have hnhds : Icc (0 : ℝ) 1 \ ↑s ∈ 𝓝 t :=
    inter_mem (Icc_mem_nhds ht.1.1 ht.1.2) (s.finite_toSet.isClosed.isOpen_compl.mem_nhds ht.2)
  have hαt : HasDerivAt α (deriv α t) t :=
    ((hαd.differentiableOn one_ne_zero t ⟨htI, ht.2⟩).differentiableAt hnhds).hasDerivAt
  have hAt : HasDerivAt A (deriv A (α t)) (α t) :=
    (hA.differentiableAt (isOpen_ball.mem_nhds (hαm htI))).hasDerivAt
  have hcomp : HasDerivAt (fun t => A (α t)) (deriv A (α t) * deriv α t) t := hAt.comp t hαt
  rw [hcomp.deriv, norm_mul, ← mul_assoc, hAρ _ (hαm htI)]

/-- Helper. Two integrands that agree on `(0, 1)` off a finite set have the same integral over `[0, 1]`, and one is
integrable exactly when the other is. -/
theorem gl2c_integral_congr {f g : ℝ → ℝ} {s : Finset ℝ} (h : ∀ t ∈ Ioo (0 : ℝ) 1 \ ↑s, f t = g t) :
    (∫ t in (0 : ℝ)..1, f t) = (∫ t in (0 : ℝ)..1, g t) ∧
      (IntervalIntegrable f volume 0 1 ↔ IntervalIntegrable g volume 0 1) := by
  have hae : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) 1 → f t = g t := by
    filter_upwards [(s.finite_toSet.union (finite_singleton (1 : ℝ))).countable.ae_notMem volume] with t ht hti
    rw [uIoc_of_le zero_le_one] at hti
    refine h t ⟨⟨hti.1, lt_of_le_of_ne hti.2 fun h1 => ht (Or.inr h1)⟩, fun hs => ht (Or.inl hs)⟩
  have hae' : f =ᵐ[volume.restrict (uIoc (0 : ℝ) 1)] g := (ae_restrict_iff' measurableSet_uIoc).2 hae
  refine ⟨intervalIntegral.integral_congr_ae hae, ⟨fun hf => ?_, fun hg => ?_⟩⟩
  · exact intervalIntegrable_iff.2 ((intervalIntegrable_iff.1 hf).congr hae')
  · exact intervalIntegrable_iff.2 ((intervalIntegrable_iff.1 hg).congr hae'.symm)

/-- Helper (§2.5, (2.13)). `L(r) = ½ log((1 + r)/(1 − r))` has derivative `1/(1 − r²)` on `(−1, 1)`. -/
theorem gl2c_hasDerivAt_L {u : ℝ} (hu : |u| < 1) :
    HasDerivAt (fun r : ℝ => (1 / 2) * Real.log ((1 + r) / (1 - r))) (1 / (1 - u ^ 2)) u := by
  obtain ⟨h1, h2⟩ := abs_lt.1 hu
  have hp : 0 < 1 + u := by linarith
  have hm : 0 < 1 - u := by linarith
  have hq2 : 1 - u ^ 2 ≠ 0 := by nlinarith
  have hq : HasDerivAt (fun r : ℝ => (1 + r) / (1 - r)) ((1 * (1 - u) - (1 + u) * (-1)) / (1 - u) ^ 2) u :=
    ((hasDerivAt_id u).const_add 1).div ((hasDerivAt_id u).const_sub 1) hm.ne'
  have := (hq.log (div_pos hp hm).ne').const_mul (1 / 2)
  refine this.congr_deriv ?_
  field_simp
  ring

/-- Helper (§2.5). An admissible path is differentiable at the parameters of `(0, 1)` off `s`. -/
theorem gl2c_hasDerivAt_path {β : ℝ → ℂ} {s : Finset ℝ} (hβd : ContDiffOn ℝ 1 β (Icc 0 1 \ ↑s)) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1 \ ↑s) : HasDerivAt β (deriv β t) t := by
  have hnhds : Icc (0 : ℝ) 1 \ ↑s ∈ 𝓝 t :=
    inter_mem (Icc_mem_nhds ht.1.1 ht.1.2) (s.finite_toSet.isClosed.isOpen_compl.mem_nhds ht.2)
  exact ((hβd.differentiableOn one_ne_zero t ⟨Ioo_subset_Icc_self ht.1, ht.2⟩).differentiableAt hnhds).hasDerivAt

/-- Helper. The real part of a differentiable path is differentiable. -/
theorem gl2c_hasDerivAt_re {β : ℝ → ℂ} {β' : ℂ} {t : ℝ} (h : HasDerivAt β β' t) :
    HasDerivAt (fun t => (β t).re) β'.re t :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h

/-- Helper. The imaginary part of a differentiable path is differentiable. -/
theorem gl2c_hasDerivAt_im {β : ℝ → ℂ} {β' : ℂ} {t : ℝ} (h : HasDerivAt β β' t) :
    HasDerivAt (fun t => (β t).im) β'.im t :=
  Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h

/-- Helper (§2.5, (2.12)). For `b ∈ Δ`: `|Re v|/(1 − (Re b)²) ≤ ρ(b)|v|`. -/
theorem gl2c_re_bound {b : ℂ} (hb : ‖b‖ < 1) (v : ℂ) :
    |v.re| / (1 - b.re ^ 2) ≤ hypDensityDisc b * ‖v‖ := by
  have hpos : 0 < 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
  have hle2 : 1 - ‖b‖ ^ 2 ≤ 1 - b.re ^ 2 := by
    have := abs_re_le_norm b
    nlinarith [abs_nonneg b.re, sq_abs b.re]
  rw [hypDensityDisc, one_div_mul_eq_div]
  calc |v.re| / (1 - b.re ^ 2) ≤ ‖v‖ / (1 - b.re ^ 2) :=
        div_le_div_of_nonneg_right (abs_re_le_norm v) (hpos.le.trans hle2)
    _ ≤ ‖v‖ / (1 - ‖b‖ ^ 2) := div_le_div_of_nonneg_left (norm_nonneg _) hpos hle2

/-- Helper (§2.5). The equality case of `gl2c_re_bound`: `Re v/(1 − (Re b)²) = ρ(b)|v|` forces `v` real and `≥ 0`. -/
theorem gl2c_eq_pt {b : ℂ} (hb : ‖b‖ < 1) {v : ℂ} (h : v.re / (1 - b.re ^ 2) = hypDensityDisc b * ‖v‖) :
    v.im = 0 ∧ 0 ≤ v.re := by
  have hpos : 0 < 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
  have hle2 : 1 - ‖b‖ ^ 2 ≤ 1 - b.re ^ 2 := by
    have := abs_re_le_norm b
    nlinarith [abs_nonneg b.re, sq_abs b.re]
  have h1 : ‖v‖ / (1 - b.re ^ 2) ≤ ‖v‖ / (1 - ‖b‖ ^ 2) := div_le_div_of_nonneg_left (norm_nonneg _) hpos hle2
  rw [hypDensityDisc, one_div_mul_eq_div] at h
  have h2 : v.re / (1 - b.re ^ 2) ≤ ‖v‖ / (1 - b.re ^ 2) :=
    div_le_div_of_nonneg_right (re_le_norm v) (hpos.le.trans hle2)
  have h3 : v.re = ‖v‖ := by
    have : v.re / (1 - b.re ^ 2) = ‖v‖ / (1 - b.re ^ 2) := le_antisymm h2 (h ▸ h1)
    exact (div_left_inj' (hpos.trans_le hle2).ne').1 this
  have hn : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  refine ⟨?_, h3 ▸ norm_nonneg v⟩
  rw [← h3] at hn
  nlinarith

/-- Helper (§2.5, (2.12)). FTC for `L(Re β)` along an admissible path of finite length: the derivative
`Re β′/(1 − (Re β)²)` is integrable, integrates to `L(Re β(1)) − L(Re β(0))`, and is bounded by `ρ(β)|β′|`. -/
theorem gl2c_ftc_re {β : ℝ → ℂ} {s : Finset ℝ} (hβm : MapsTo β (Icc 0 1) unitDisc)
    (hβc : ContinuousOn β (Icc 0 1)) (hβd : ContDiffOn ℝ 1 β (Icc 0 1 \ ↑s))
    (hint : IntervalIntegrable (fun t => hypDensityDisc (β t) * ‖deriv β t‖) volume 0 1) :
    IntervalIntegrable (fun t => (deriv β t).re / (1 - (β t).re ^ 2)) volume 0 1 ∧
      (∫ t in (0 : ℝ)..1, (deriv β t).re / (1 - (β t).re ^ 2)) =
        (1 / 2) * Real.log ((1 + (β 1).re) / (1 - (β 1).re)) -
          (1 / 2) * Real.log ((1 + (β 0).re) / (1 - (β 0).re)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, |(deriv β t).re / (1 - (β t).re ^ 2)| ≤ hypDensityDisc (β t) * ‖deriv β t‖ := by
  set g' : ℝ → ℝ := fun t => (deriv β t).re / (1 - (β t).re ^ 2) with hg'def
  have hb1 : ∀ t ∈ Icc (0 : ℝ) 1, ‖β t‖ < 1 := fun t ht => mem_ball_zero_iff.1 (hβm ht)
  have hu1 : ∀ t ∈ Icc (0 : ℝ) 1, |(β t).re| < 1 := fun t ht => (abs_re_le_norm (β t)).trans_lt (hb1 t ht)
  -- `L(Re β)` has derivative `g'` off `s`
  have Hd : ∀ t ∈ Ioo (0 : ℝ) 1 \ ↑s,
      HasDerivAt (fun t => (1 / 2) * Real.log ((1 + (β t).re) / (1 - (β t).re))) (g' t) t := fun t ht => by
    have := (gl2c_hasDerivAt_L (hu1 t (Ioo_subset_Icc_self ht.1))).comp t
      (gl2c_hasDerivAt_re (gl2c_hasDerivAt_path hβd ht))
    refine this.congr_deriv ?_
    simp only [hg'def]
    ring
  have hgc : ContinuousOn (fun t => (1 / 2) * Real.log ((1 + (β t).re) / (1 - (β t).re))) (Icc 0 1) := by
    have huc : ContinuousOn (fun t => (β t).re) (Icc 0 1) := Complex.continuous_re.comp_continuousOn hβc
    refine continuousOn_const.mul (ContinuousOn.log ((continuousOn_const.add huc).div
      (continuousOn_const.sub huc) fun t ht => ?_) fun t ht => ?_)
    · have := abs_lt.1 (hu1 t ht)
      linarith
    · have := abs_lt.1 (hu1 t ht)
      exact (div_pos (by linarith) (by linarith)).ne'
  -- `|g'| ≤ ρ(β)|β′|` on `[0, 1]`, so `g'` is integrable
  have hle : ∀ t ∈ Icc (0 : ℝ) 1, |g' t| ≤ hypDensityDisc (β t) * ‖deriv β t‖ := fun t ht => by
    have hpos : 0 < 1 - (β t).re ^ 2 := by
      have := abs_lt.1 (hu1 t ht)
      nlinarith
    rw [hg'def, abs_div, abs_of_pos hpos]
    exact gl2c_re_bound (hb1 t ht) _
  have hg'int : IntervalIntegrable g' volume 0 1 := by
    refine hint.mono_fun ?_ ?_
    · have h1 : AEMeasurable (fun t => (deriv β t).re) (volume.restrict (uIoc (0 : ℝ) 1)) :=
        (Complex.measurable_re.comp (measurable_deriv β)).aemeasurable
      have h2 : AEMeasurable (fun t => (β t).re) (volume.restrict (uIoc (0 : ℝ) 1)) := by
        rw [uIoc_of_le zero_le_one]
        exact (Complex.continuous_re.comp_continuousOn (hβc.mono Ioc_subset_Icc_self)).aemeasurable
          measurableSet_Ioc
      exact (h1.div (aemeasurable_const.sub (h2.pow_const 2))).aestronglyMeasurable
    · rw [uIoc_of_le zero_le_one]
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
      have hti : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
      have hρ : 0 ≤ hypDensityDisc (β t) := by
        rw [hypDensityDisc]
        have := hb1 t hti
        have : 0 < 1 - ‖β t‖ ^ 2 := by nlinarith [norm_nonneg (β t)]
        positivity
      show ‖g' t‖ ≤ ‖hypDensityDisc (β t) * ‖deriv β t‖‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hρ (norm_nonneg _))]
      exact hle t hti
  exact ⟨hg'int, integral_eq_of_hasDerivAt_off_countable_of_le _ g' zero_le_one s.countable_toSet hgc Hd hg'int,
    hle⟩

/-- Helper. FTC on a sub-interval `[a, b] ⊆ [0, 1]` for a function continuous on `[0, 1]` and differentiable on
`(0, 1)` off a finite set, with derivative integrable on `[0, 1]`. -/
theorem gl2c_ftc_sub {p p' : ℝ → ℝ} {s : Finset ℝ} (hpc : ContinuousOn p (Icc 0 1))
    (hpd : ∀ t ∈ Ioo (0 : ℝ) 1 \ ↑s, HasDerivAt p (p' t) t) (hpi : IntervalIntegrable p' volume 0 1)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : ∫ t in a..b, p' t = p b - p a :=
  integral_eq_of_hasDerivAt_off_countable_of_le p p' hab s.countable_toSet (hpc.mono (Icc_subset_Icc ha hb))
    (fun t ht => hpd t ⟨⟨ha.trans_lt ht.1.1, ht.1.2.trans_le hb⟩, ht.2⟩)
    (hpi.mono_set (by rw [uIcc_of_le hab, uIcc_of_le zero_le_one]; exact Icc_subset_Icc ha hb))

/-- Helper (§2.5). Along an admissible path of finite length in `Δ`, `|β′|` is integrable (`ρ ≥ 1` on `Δ`), hence so
are `Re β′` and `Im β′`. -/
theorem gl2c_int_re_im {β : ℝ → ℂ} (hβm : MapsTo β (Icc 0 1) unitDisc)
    (hint : IntervalIntegrable (fun t => hypDensityDisc (β t) * ‖deriv β t‖) volume 0 1) :
    IntervalIntegrable (fun t => (deriv β t).re) volume 0 1 ∧
      IntervalIntegrable (fun t => (deriv β t).im) volume 0 1 := by
  have hle : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv β t‖ ≤ ‖hypDensityDisc (β t) * ‖deriv β t‖‖ := fun t ht => by
    have hb := mem_ball_zero_iff.1 (hβm ht)
    have hpos : 0 < 1 - ‖β t‖ ^ 2 := by nlinarith [norm_nonneg (β t)]
    have hρ : 1 ≤ hypDensityDisc (β t) := by
      rw [hypDensityDisc, le_div_iff₀ hpos]
      nlinarith [norm_nonneg (β t)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (zero_le_one.trans hρ) (norm_nonneg _))]
    nlinarith [norm_nonneg (deriv β t)]
  have hae : ∀ f : ℂ → ℝ, (∀ v, ‖f v‖ ≤ ‖v‖) → ∀ᵐ t ∂(volume.restrict (uIoc (0 : ℝ) 1)),
      ‖f (deriv β t)‖ ≤ ‖hypDensityDisc (β t) * ‖deriv β t‖‖ := fun f hf => by
    rw [uIoc_of_le zero_le_one]
    exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht =>
      (hf _).trans (hle t (Ioc_subset_Icc_self ht)))
  exact ⟨hint.mono_fun (Complex.measurable_re.comp (measurable_deriv β)).aestronglyMeasurable
      (hae _ fun v => by rw [Real.norm_eq_abs]; exact abs_re_le_norm v),
    hint.mono_fun (Complex.measurable_im.comp (measurable_deriv β)).aestronglyMeasurable
      (hae _ fun v => by rw [Real.norm_eq_abs]; exact abs_im_le_norm v)⟩

/-- Helper (§2.5, (2.12)). The length estimate. For an admissible path `β` in `Δ` of finite length,
`L(Re β(1)) − L(Re β(0)) ≤ ∫ ρ(β) |β′|` with `L(r) = ½ log((1 + r)/(1 − r))`, because
`ρ(β) |β′| ≥ (Re β)′/(1 − (Re β)²)`; the bound follows by FTC off the finite set `s`. -/
theorem gl2c_lower {β : ℝ → ℂ} {s : Finset ℝ} (hβm : MapsTo β (Icc 0 1) unitDisc)
    (hβc : ContinuousOn β (Icc 0 1)) (hβd : ContDiffOn ℝ 1 β (Icc 0 1 \ ↑s))
    (hint : IntervalIntegrable (fun t => hypDensityDisc (β t) * ‖deriv β t‖) volume 0 1) :
    (1 / 2) * Real.log ((1 + (β 1).re) / (1 - (β 1).re)) - (1 / 2) * Real.log ((1 + (β 0).re) / (1 - (β 0).re)) ≤
      ∫ t in (0 : ℝ)..1, hypDensityDisc (β t) * ‖deriv β t‖ := by
  obtain ⟨hi, he, hle⟩ := gl2c_ftc_re hβm hβc hβd hint
  rw [← he]
  exact intervalIntegral.integral_mono_on zero_le_one hi hint fun t ht => (le_abs_self _).trans (hle t ht)

/-- Helper (§2.5, after (2.13)). The equality case. An admissible path of finite length from `0` to a real `x` whose
length is `L(x)` traces exactly the segment `[0, x]`: equality forces `Im β ≡ 0` and `Re β` monotone. -/
theorem gl2c_eq_case {β : ℝ → ℂ} {s : Finset ℝ} (hβm : MapsTo β (Icc 0 1) unitDisc)
    (hβc : ContinuousOn β (Icc 0 1)) (hβd : ContDiffOn ℝ 1 β (Icc 0 1 \ ↑s))
    (hint : IntervalIntegrable (fun t => hypDensityDisc (β t) * ‖deriv β t‖) volume 0 1)
    {x : ℝ} (hβ0 : β 0 = 0) (hβ1 : β 1 = x)
    (heq : (∫ t in (0 : ℝ)..1, hypDensityDisc (β t) * ‖deriv β t‖) = (1 / 2) * Real.log ((1 + x) / (1 - x))) :
    β '' Icc 0 1 = (fun r : ℝ => (r : ℂ)) '' Icc 0 x := by
  have hb1 : ∀ t ∈ Icc (0 : ℝ) 1, ‖β t‖ < 1 := fun t ht => mem_ball_zero_iff.1 (hβm ht)
  have hρ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ hypDensityDisc (β t) * ‖deriv β t‖ := fun t ht => by
    have := hb1 t ht
    have : 0 < 1 - ‖β t‖ ^ 2 := by nlinarith [norm_nonneg (β t)]
    rw [hypDensityDisc]
    positivity
  have hx1 : |x| < 1 := by
    have := hb1 1 (right_mem_Icc.2 zero_le_one)
    rwa [hβ1, Complex.norm_real, Real.norm_eq_abs] at this
  obtain ⟨hxm, hxp⟩ := abs_lt.1 hx1
  -- `0 ≤ x`: the length is `≥ 0`
  have hx0 : 0 ≤ x := by
    by_contra hneg
    push Not at hneg
    have h1 := intervalIntegral.integral_nonneg (μ := volume) zero_le_one hρ0
    have h2 : (1 / 2) * Real.log ((1 + x) / (1 - x)) < 0 :=
      mul_neg_of_pos_of_neg one_half_pos (Real.log_neg (div_pos (by linarith) (by linarith))
        ((div_lt_one (by linarith)).2 (by linarith)))
    linarith
  -- the gap `ρ(β)|β′| − Re β′/(1 − (Re β)²)` is `≥ 0` with integral `0`, so it vanishes a.e.
  obtain ⟨hg'int, hftc, hle⟩ := gl2c_ftc_re hβm hβc hβd hint
  have hdiff : (∫ t in (0 : ℝ)..1, (hypDensityDisc (β t) * ‖deriv β t‖ -
      (deriv β t).re / (1 - (β t).re ^ 2))) = 0 := by
    rw [intervalIntegral.integral_sub hint hg'int, heq, hftc, hβ0, hβ1]
    simp
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] fun t => hypDensityDisc (β t) * ‖deriv β t‖ -
      (deriv β t).re / (1 - (β t).re ^ 2) :=
    (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht =>
      sub_nonneg.2 ((le_abs_self _).trans (hle t (Ioc_subset_Icc_self ht))))
  have hae0 :=
    (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae zero_le_one hnn (hint.sub hg'int)).1 hdiff
  have hpt : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), (deriv β t).im = 0 ∧ 0 ≤ (deriv β t).re := by
    filter_upwards [hae0, ae_restrict_mem measurableSet_Ioc] with t ht htI
    exact gl2c_eq_pt (hb1 t (Ioc_subset_Icc_self htI)) (sub_eq_zero.1 ht).symm
  -- FTC: `Im β ≡ 0` and `Re β` is monotone
  obtain ⟨hreint, himint⟩ := gl2c_int_re_im hβm hint
  have hrec : ContinuousOn (fun t => (β t).re) (Icc 0 1) := Complex.continuous_re.comp_continuousOn hβc
  have himc : ContinuousOn (fun t => (β t).im) (Icc 0 1) := Complex.continuous_im.comp_continuousOn hβc
  have hred : ∀ t ∈ Ioo (0 : ℝ) 1 \ ↑s, HasDerivAt (fun t => (β t).re) (deriv β t).re t :=
    fun t ht => gl2c_hasDerivAt_re (gl2c_hasDerivAt_path hβd ht)
  have himd : ∀ t ∈ Ioo (0 : ℝ) 1 \ ↑s, HasDerivAt (fun t => (β t).im) (deriv β t).im t :=
    fun t ht => gl2c_hasDerivAt_im (gl2c_hasDerivAt_path hβd ht)
  have him : ∀ t ∈ Icc (0 : ℝ) 1, (β t).im = 0 := fun t ht => by
    have e := gl2c_ftc_sub himc himd himint le_rfl ht.1 ht.2
    have h0 : (∫ u in (0 : ℝ)..t, (deriv β u).im) = 0 := by
      rw [intervalIntegral.integral_of_le ht.1]
      refine integral_eq_zero_of_ae ?_
      have := ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right ht.2) hpt
      filter_upwards [this] with u hu
      exact hu.1
    rw [h0, hβ0, Complex.zero_im, sub_zero] at e
    exact e.symm
  have hmono : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, a ≤ b → (β a).re ≤ (β b).re :=
    fun a ha b hb hab => by
      have e := gl2c_ftc_sub hrec hred hreint ha.1 hab hb.2
      have h0 : 0 ≤ ∫ u in a..b, (deriv β u).re := by
        rw [intervalIntegral.integral_of_le hab]
        refine integral_nonneg_of_ae ?_
        have := ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc ha.1 hb.2) hpt
        filter_upwards [this] with u hu
        exact hu.2
      linarith
  have hre : ∀ t ∈ Icc (0 : ℝ) 1, (β t).re ∈ Icc 0 x := fun t ht => by
    have h0 := hmono 0 (left_mem_Icc.2 zero_le_one) t ht ht.1
    have h1 := hmono t ht 1 (right_mem_Icc.2 zero_le_one) ht.2
    rw [hβ0, Complex.zero_re] at h0
    rw [hβ1, Complex.ofReal_re] at h1
    exact ⟨h0, h1⟩
  have hβre : ∀ t ∈ Icc (0 : ℝ) 1, β t = ((β t).re : ℂ) := fun t ht =>
    Complex.ext (by simp) (by simp [him t ht])
  ext v
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨(β t).re, hre t ht, (hβre t ht).symm⟩
  · rintro ⟨r, hr, rfl⟩
    have hsub := intermediate_value_Icc zero_le_one hrec
    rw [hβ0, hβ1, Complex.zero_re, Complex.ofReal_re] at hsub
    obtain ⟨t, ht, htr⟩ := hsub hr
    refine ⟨t, ht, ?_⟩
    simp only at htr ⊢
    rw [hβre t ht, htr]

/-- Helper (§2.5, (2.13)). The segment `t ↦ t x` (`0 ≤ x < 1`) has finite length `L(x) = ½ log((1 + x)/(1 − x))`. -/
theorem gl2c_segment_length {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    IntervalIntegrable (fun t : ℝ => hypDensityDisc ((t * x : ℝ) : ℂ) *
      ‖deriv (fun t : ℝ => ((t * x : ℝ) : ℂ)) t‖) volume 0 1 ∧
      (∫ t in (0 : ℝ)..1, hypDensityDisc ((t * x : ℝ) : ℂ) * ‖deriv (fun t : ℝ => ((t * x : ℝ) : ℂ)) t‖) =
        (1 / 2) * Real.log ((1 + x) / (1 - x)) := by
  have hd : ∀ t : ℝ, deriv (fun t : ℝ => ((t * x : ℝ) : ℂ)) t = x := fun t => by
    have h : HasDerivAt (fun t : ℝ => ((t * x : ℝ) : ℂ)) ((1 * x : ℝ) : ℂ) t :=
      ((hasDerivAt_id' t).mul_const x).ofReal_comp
    rw [h.deriv, one_mul]
  have hf : (fun t : ℝ => hypDensityDisc ((t * x : ℝ) : ℂ) * ‖deriv (fun t : ℝ => ((t * x : ℝ) : ℂ)) t‖) =
      fun t => x / (1 - (t * x) ^ 2) := by
    funext t
    rw [hd, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
    simp only [hypDensityDisc, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  rw [hf]
  have hsq : ∀ t ∈ uIcc (0 : ℝ) 1, (t * x) ^ 2 < 1 := fun t ht => by
    rw [uIcc_of_le zero_le_one] at ht
    have h1 : t * x ≤ x := by nlinarith [ht.2]
    have h2 : 0 ≤ t * x := mul_nonneg ht.1 hx0
    nlinarith
  have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => (1 / 2) * Real.log ((1 + t * x) / (1 - t * x)))
      (x / (1 - (t * x) ^ 2)) t := fun t ht => by
    have hu : |t * x| < 1 := by
      rw [← sq_lt_one_iff_abs_lt_one]
      exact hsq t ht
    have := (gl2c_hasDerivAt_L hu).comp t ((hasDerivAt_id' t).mul_const x)
    refine this.congr_deriv ?_
    ring
  have hcont : ContinuousOn (fun t : ℝ => x / (1 - (t * x) ^ 2)) (uIcc 0 1) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht => ?_
    have := hsq t ht
    linarith
  have hint : IntervalIntegrable (fun t : ℝ => x / (1 - (t * x) ^ 2)) volume 0 1 := hcont.intervalIntegrable
  refine ⟨hint, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint]
  simp

/-- Helper (§2.5, Proposition 2). The image of a real segment `[0, x]` (`0 ≤ x < 1`) under `y ↦ c B_a(y)` lies on a
circle orthogonal to the unit circle or on a diameter. -/
theorem gl2c_circle {c a : ℂ} (hc : ‖c‖ = 1) (ha : a ∈ unitDisc) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (∃ (c₀ : ℂ) (r : ℝ), 0 < r ∧ ‖c₀‖ ^ 2 = 1 + r ^ 2 ∧
        (fun y => c * LiZhongQC.blaschke a y) '' ((fun r : ℝ => (r : ℂ)) '' Icc 0 x) ⊆ sphere c₀ r) ∨
      ∃ θ : ℝ, (fun y => c * LiZhongQC.blaschke a y) '' ((fun r : ℝ => (r : ℂ)) '' Icc 0 x) ⊆
        {v : ℂ | ∃ s : ℝ, v = s * exp (θ * I)} := by
  -- `0 ≤ x` is not needed: the image of the whole real interval `(−1, 1)` lies on the circle or the line
  have _ := hx0
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.1 ha
  have hna : a.re ^ 2 + a.im ^ 2 < 1 := by
    have : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    nlinarith [norm_nonneg a]
  have hden : ∀ y ∈ Icc (0 : ℝ) x, (1 : ℂ) - conj a * y ≠ 0 := fun y hy =>
    LiZhongQC.blaschke_den_ne_zero ha1 (by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy.1]
      exact hy.2.trans_lt hx1)
  by_cases him : a.im = 0
  · -- `a` real: `B_a` maps reals to reals, so the image lies on the line `ℝ c`
    right
    refine ⟨Complex.arg c, ?_⟩
    rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
    have har : a = (a.re : ℂ) := Complex.ext rfl (by simp [him])
    refine ⟨(y - a.re) / (1 - a.re * y), ?_⟩
    have hc' : c = exp (arg c * I) := by
      have := Complex.norm_mul_exp_arg_mul_I c
      rw [hc, Complex.ofReal_one, one_mul] at this
      exact this.symm
    show c * LiZhongQC.blaschke a y = _
    unfold LiZhongQC.blaschke
    rw [har, Complex.conj_ofReal]
    simp only [Complex.ofReal_re]
    nth_rewrite 1 [hc']
    push_cast
    ring
  · -- otherwise the image lies on the circle `|v − c c₀| = |Im a + e|`, `c₀ = −Re a + e i`
    left
    set e : ℝ := -(1 + a.im ^ 2 - a.re ^ 2) / (2 * a.im) with hedef
    have hrel : 1 + a.im ^ 2 - a.re ^ 2 + 2 * a.im * e = 0 := by
      have : 2 * a.im * e = -(1 + a.im ^ 2 - a.re ^ 2) := by
        rw [hedef]
        field_simp
      linarith
    clear_value e
    set c₀ : ℂ := ((-a.re : ℝ) : ℂ) + (e : ℂ) * I with hc₀
    have hr : 0 < |a.im + e| := by
      refine abs_pos.2 fun h0 => ?_
      have : e = -a.im := by linarith
      rw [this] at hrel
      nlinarith
    refine ⟨c * c₀, |a.im + e|, hr, ?_, ?_⟩
    · rw [norm_mul, hc, one_mul, Complex.sq_norm, Complex.normSq_apply, sq_abs]
      simp only [hc₀, add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im]
      linear_combination (-1 : ℝ) * hrel
    · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      have hd := hden y hy
      have key : Complex.normSq ((y : ℂ) - a - (1 - conj a * y) * c₀) =
          (a.im + e) ^ 2 * Complex.normSq (1 - conj a * y) := by
        simp only [hc₀, Complex.normSq_apply, sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
          conj_re, conj_im, one_re, one_im, add_re, add_im]
        linear_combination (y ^ 2 * (1 - a.re ^ 2 - a.im ^ 2)) * hrel
      have hB : LiZhongQC.blaschke a y - c₀ = ((y : ℂ) - a - (1 - conj a * y) * c₀) / (1 - conj a * y) := by
        unfold LiZhongQC.blaschke
        rw [div_sub' hd]
      rw [mem_sphere, dist_eq_norm, ← mul_sub, norm_mul, hc, one_mul, hB, norm_div]
      have hpos : 0 < ‖(1 : ℂ) - conj a * y‖ := norm_pos_iff.2 hd
      rw [div_eq_iff hpos.ne']
      have hsq : ‖(y : ℂ) - a - (1 - conj a * y) * c₀‖ ^ 2 = (|a.im + e| * ‖(1 : ℂ) - conj a * y‖) ^ 2 := by
        rw [Complex.sq_norm, key, mul_pow, sq_abs, Complex.sq_norm]
      exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 hsq

/-- Helper (§2.5, (2.16)). The pseudo-hyperbolic distance `δ = |(z − w)/(1 − z̄w)|` is `|B_z(w)| < 1` on `Δ`. -/
theorem gl2c_delta_lt {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    ‖(z - w) / (1 - conj z * w)‖ = ‖LiZhongQC.blaschke z w‖ ∧ ‖(z - w) / (1 - conj z * w)‖ < 1 := by
  have e : ‖(z - w) / (1 - conj z * w)‖ = ‖LiZhongQC.blaschke z w‖ := by
    rw [show (z - w) / (1 - conj z * w) = -LiZhongQC.blaschke z w by unfold LiZhongQC.blaschke; ring, norm_neg]
  exact ⟨e, e ▸ LiZhongQC.blaschke_mem_unitDisc (mem_ball_zero_iff.1 hz) (mem_ball_zero_iff.1 hw)⟩

/-- Helper (§2.5). `|z − w| ≤ 4 d(z, w)` on `Δ` (`|z − w| ≤ 2δ` and `d = L(δ) ≥ δ/2`). -/
theorem gl2c_norm_sub_le {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    ‖z - w‖ ≤ 4 * discPoincareDist z w := by
  have hz1 := mem_ball_zero_iff.1 hz
  have hw1 := mem_ball_zero_iff.1 hw
  set δ := ‖(z - w) / (1 - conj z * w)‖ with hδ
  have hden : (1 : ℂ) - conj z * w ≠ 0 := LiZhongQC.blaschke_den_ne_zero hz1 hw1
  have hδ1 : δ < 1 := (gl2c_delta_lt hz hw).2
  have hδ0 : 0 ≤ δ := norm_nonneg _
  -- `|z − w| = δ |1 − z̄w| ≤ 2δ`
  have h1 : ‖z - w‖ ≤ 2 * δ := by
    have e : ‖z - w‖ = δ * ‖1 - conj z * w‖ := by
      rw [hδ, norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.2 hden)]
    have h2 : ‖1 - conj z * w‖ ≤ 2 := by
      calc ‖1 - conj z * w‖ ≤ ‖(1 : ℂ)‖ + ‖conj z * w‖ := norm_sub_le _ _
        _ ≤ 2 := by
          rw [norm_one, norm_mul, RCLike.norm_conj]
          nlinarith [norm_nonneg z, norm_nonneg w]
    rw [e]
    nlinarith [norm_nonneg (1 - conj z * w)]
  -- `δ ≤ log((1 + δ)/(1 − δ)) = 2 d(z, w)`, from `log y ≥ 1 − 1/y`
  have h2 : δ ≤ 2 * discPoincareDist z w := by
    show δ ≤ 2 * ((1 / 2) * Real.log ((1 + δ) / (1 - δ)))
    have hy : 0 < (1 + δ) / (1 - δ) := div_pos (by linarith) (by linarith)
    have hlog := Real.one_sub_inv_le_log_of_pos hy
    rw [inv_div] at hlog
    have h3 : (1 - δ) / (1 + δ) ≤ 1 - δ := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  linarith

/-- Helper (§2.5). `d(z, w) → 0` as `w → z ∈ Δ`. -/
theorem gl2c_tendsto_dist {z : ℂ} (hz : z ∈ unitDisc) : Tendsto (discPoincareDist z) (𝓝 z) (𝓝 0) := by
  have hz1 := mem_ball_zero_iff.1 hz
  have hd0 : (1 : ℂ) - conj z * z ≠ 0 := LiZhongQC.blaschke_den_ne_zero hz1 hz1
  have hδ : Tendsto (fun w => ‖(z - w) / (1 - conj z * w)‖) (𝓝 z) (𝓝 0) := by
    have h : ContinuousAt (fun w => (z - w) / (1 - conj z * w)) z :=
      (continuous_const.sub continuous_id).continuousAt.div
        (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt hd0
    have := h.tendsto.norm
    rwa [sub_self, zero_div, norm_zero] at this
  have hL : ContinuousAt (fun r : ℝ => (1 / 2) * Real.log ((1 + r) / (1 - r))) 0 := by
    refine continuousAt_const.mul (ContinuousAt.log ?_ (by norm_num))
    exact (continuousAt_const.add continuousAt_id).div (continuousAt_const.sub continuousAt_id) (by norm_num)
  have h := hL.tendsto.comp hδ
  have h0 : (1 / 2 : ℝ) * Real.log ((1 + 0) / (1 - 0)) = 0 := by simp
  rw [h0] at h
  exact h

/-- Helper (§2.5). The points of `Δ` within distance `1` of `z ∈ Δ` lie in a smaller closed disc. -/
theorem gl2c_bounded {z : ℂ} (hz : z ∈ unitDisc) :
    ∃ R < 1, ∀ w ∈ unitDisc, discPoincareDist z w ≤ 1 → ‖w‖ ≤ R := by
  have hz1 := mem_ball_zero_iff.1 hz
  have he : 1 < Real.exp 2 := by
    have := Real.add_one_le_exp 2
    linarith
  set τ : ℝ := (Real.exp 2 - 1) / (Real.exp 2 + 1) with hτ
  have hτ0 : 0 ≤ τ := div_nonneg (by linarith) (by linarith)
  have hτ1 : τ < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hz2 : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  set η : ℝ := (1 - τ ^ 2) * (1 - ‖z‖) ^ 2 / (1 - ‖z‖ ^ 2) with hη
  have hη0 : 0 < η := by
    have : 0 < 1 - ‖z‖ := by linarith
    have : 0 < 1 - τ ^ 2 := by nlinarith
    positivity
  refine ⟨Real.sqrt (1 - η), (Real.sqrt_lt' one_pos).2 (by linarith), fun w hw hd => ?_⟩
  have hw1 := mem_ball_zero_iff.1 hw
  obtain ⟨hδB, hδ1⟩ := gl2c_delta_lt hz hw
  set δ := ‖(z - w) / (1 - conj z * w)‖ with hδ
  have hδ0 : 0 ≤ δ := norm_nonneg _
  -- `d ≤ 1` gives `δ ≤ τ`
  have hδτ : δ ≤ τ := by
    have hy : 0 < (1 + δ) / (1 - δ) := div_pos (by linarith) (by linarith)
    have h2 : Real.log ((1 + δ) / (1 - δ)) ≤ 2 := by
      have : (1 / 2) * Real.log ((1 + δ) / (1 - δ)) ≤ 1 := hd
      linarith
    rw [Real.log_le_iff_le_exp hy, div_le_iff₀ (by linarith)] at h2
    rw [hτ, le_div_iff₀ (by linarith)]
    nlinarith
  -- `1 − |w|² = (1 − δ²)|1 − z̄w|²/(1 − |z|²) ≥ η`
  have hden : (1 : ℂ) - conj z * w ≠ 0 := LiZhongQC.blaschke_den_ne_zero hz1 hw1
  have hkey := LiZhongQC.one_sub_normSq_blaschke hz1 hw1
  rw [← Complex.sq_norm, ← hδB, ← Complex.sq_norm, ← Complex.sq_norm, ← Complex.sq_norm] at hkey
  have hlow : 1 - ‖z‖ ≤ ‖1 - conj z * w‖ := by
    have := norm_sub_norm_le (1 : ℂ) (conj z * w)
    rw [norm_one, norm_mul, RCLike.norm_conj] at this
    nlinarith [norm_nonneg z, norm_nonneg w]
  have hw2 : η ≤ 1 - ‖w‖ ^ 2 := by
    have hpos : 0 < ‖(1 : ℂ) - conj z * w‖ ^ 2 := by positivity
    have e : 1 - ‖w‖ ^ 2 = (1 - δ ^ 2) * ‖1 - conj z * w‖ ^ 2 / (1 - ‖z‖ ^ 2) := by
      field_simp
      field_simp at hkey
      linarith
    rw [e, hη]
    gcongr
    nlinarith
  rw [← abs_of_nonneg (norm_nonneg w)]
  exact Real.abs_le_sqrt (by linarith)

/-- **Proposition 2** (§2.5, l. 1523), the global form. The distance of the infinitesimal form (2.10) is (2.16). -/
theorem prop2_2_a {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    pathDist hypDensityDisc unitDisc z w = discPoincareDist z w := by
  -- normalize: `A = c B_z` sends `z ↦ 0`, `w ↦ δ = δ(z, w) ∈ [0, 1)`; its inverse is `A⁻¹ = c̄ B_{−cz}`
  obtain ⟨c, hc, hcw⟩ := gl2c_normalize z w
  set δ : ℝ := ‖(z - w) / (1 - conj z * w)‖
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hc' : ‖conj c‖ = 1 := by rw [RCLike.norm_conj, hc]
  have hcz : -(c * z) ∈ unitDisc := by
    rw [LiZhongQC.unitDisc, mem_ball_zero_iff, norm_neg, norm_mul, hc, one_mul]
    exact hz1
  obtain ⟨hAd, hAm, hAρ⟩ := gl2c_rb_props hc hz
  obtain ⟨hBd, hBm, hBρ⟩ := gl2c_rb_props hc' hcz
  set A : ℂ → ℂ := fun v => c * LiZhongQC.blaschke z v with hAdef
  set B : ℂ → ℂ := fun y => conj c * LiZhongQC.blaschke (-(c * z)) y
  have hBA : ∀ v ∈ unitDisc, B (A v) = v := fun v hv => gl2c_rb_inv hc hz hv
  have hAz : A z = 0 := by simp [hAdef]
  have hAw : A w = δ := hcw
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hδ1 : δ < 1 := by
    have := hAm hw
    rw [hAw, LiZhongQC.unitDisc, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs] at this
    exact (le_abs_self δ).trans_lt this
  have hdist : discPoincareDist z w = (1 / 2) * Real.log ((1 + δ) / (1 - δ)) := rfl
  rw [hdist]
  unfold pathDist
  refine IsLeast.csInf_eq ⟨?_, ?_⟩
  · -- the geodesic `t ↦ A⁻¹(t δ)` is admissible, of length `L(δ)`
    have hseg : MapsTo (fun t : ℝ => ((t * δ : ℝ) : ℂ)) (Icc 0 1) unitDisc := fun t ht => by
      rw [LiZhongQC.unitDisc, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg ht.1 hδ0)]
      nlinarith [ht.2]
    have hsd : ContDiff ℝ 1 (fun t : ℝ => ((t * δ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_id.mul contDiff_const)
    obtain ⟨hm, hcont, hd, hρ⟩ := gl2c_transport hBd hBm hBρ (s := ∅) hseg hsd.continuous.continuousOn
      hsd.contDiffOn
    obtain ⟨hlen, hint⟩ := gl2c_integral_congr hρ
    obtain ⟨hi0, hl0⟩ := gl2c_segment_length hδ0 hδ1
    refine ⟨fun t => B ((t * δ : ℝ) : ℂ), ∅, ?_, ?_, hm, hcont, hd, hint.2 hi0, ?_⟩
    · show B ((0 * δ : ℝ) : ℂ) = z
      rw [zero_mul, Complex.ofReal_zero, ← hAz, hBA z hz]
    · show B ((1 * δ : ℝ) : ℂ) = w
      rw [one_mul, ← hAw, hBA w hw]
    · rw [hlen, hl0]
  · -- every admissible path has length `≥ L(δ)`: transport by `A`, then the length estimate
    rintro ℓ ⟨α, s, h0, h1, hm, hcont, hd, hint, rfl⟩
    obtain ⟨hβm, hβc, hβd, hρ⟩ := gl2c_transport hAd hAm hAρ hm hcont hd
    obtain ⟨hl, hi⟩ := gl2c_integral_congr hρ
    have h := gl2c_lower hβm hβc hβd (hi.2 hint)
    rw [h0, h1, hAz, hAw, hl] at h
    simpa using h

/-- Helper (§2.5). `d(1 − |x|²) = −2 (Re w · Re + Im w · Im)` at `w`. -/
theorem gl2c_hasFDerivAt_q (w : ℂ) :
    HasFDerivAt (fun x : ℂ => 1 - ‖x‖ ^ 2) ((-2 : ℝ) • (w.re • reCLM + w.im • imCLM : ℂ →L[ℝ] ℝ)) w := by
  have h : HasFDerivAt (fun x : ℂ => 1 - ‖x‖ ^ 2) (0 - 2 • innerSL ℝ w ∘L ContinuousLinearMap.id ℝ ℂ) w :=
    (hasFDerivAt_const (1 : ℝ) w).sub (hasFDerivAt_id w).norm_sq
  refine h.congr_fderiv ?_
  ext v
  simp [innerSL_apply_apply, Complex.inner]
  ring

/-- Helper (§2.5). `d log ρ_Δ = (2/(1 − |w|²)) (Re w · Re + Im w · Im)` at `w ∈ Δ`, for `ρ_Δ = 1/(1 − |z|²)`. -/
theorem gl2c_hasFDerivAt_logDensity {w : ℂ} (hw : ‖w‖ < 1) :
    HasFDerivAt (fun x : ℂ => Real.log (hypDensityDisc x))
      ((2 / (1 - ‖w‖ ^ 2)) • (w.re • reCLM + w.im • imCLM : ℂ →L[ℝ] ℝ)) w := by
  have hq : (1 - ‖w‖ ^ 2) ≠ 0 := by nlinarith [norm_nonneg w]
  have e : (fun x : ℂ => Real.log (hypDensityDisc x)) = fun x => -Real.log (1 - ‖x‖ ^ 2) := by
    funext x
    simp [hypDensityDisc, Real.log_inv]
  rw [e]
  refine ((gl2c_hasFDerivAt_q w).log hq).neg.congr_fderiv ?_
  ext v
  simp
  ring

/-- **Proposition 2** (§2.5, l. 1523), the curvature. The Poincaré metric of the disc has curvature `−4`. -/
theorem prop2_2_b {z : ℂ} (hz : z ∈ unitDisc) : gaussCurvature hypDensityDisc z = -4 := by
  have hz' : ‖z‖ < 1 := by simpa [LiZhongQC.unitDisc] using hz
  have hq : (1 - ‖z‖ ^ 2) ≠ 0 := by nlinarith [norm_nonneg z]
  -- `d log ρ = (2/(1 − |x|²)) (Re x · Re + Im x · Im)` near `z`; differentiate once more at `z` (product rule)
  set φ : ℂ → ℝ := fun x => Real.log (hypDensityDisc x) with hφ
  set G : ℂ → ℂ →L[ℝ] ℝ := fun x => x.re • reCLM + x.im • imCLM with hGdef
  set F : ℂ → ℂ →L[ℝ] ℝ := fun x => (2 / (1 - ‖x‖ ^ 2)) • G x
  have hev : fderiv ℝ φ =ᶠ[𝓝 z] F := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz'] with x hx
    exact (gl2c_hasFDerivAt_logDensity hx).fderiv
  have hc : HasFDerivAt (fun x : ℂ => 2 / (1 - ‖x‖ ^ 2)) ((4 / (1 - ‖z‖ ^ 2) ^ 2) • G z) z := by
    have := ((hasDerivAt_inv hq).comp_hasFDerivAt z (gl2c_hasFDerivAt_q z)).const_mul 2
    simp only [div_eq_mul_inv]
    refine this.congr_fderiv ?_
    ext v
    simp [hGdef]
    ring
  set L : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := reCLM.smulRight reCLM + imCLM.smulRight imCLM
  have hLv : ∀ v w : ℂ, L v w = v.re * w.re + v.im * w.im := fun v w => rfl
  have hGv : ∀ v w : ℂ, G v w = v.re * w.re + v.im * w.im := fun v w => rfl
  have hL : HasFDerivAt G L z := by
    have e : G = fun x => L x := by
      funext x
      ext v
      rw [hLv, hGv]
    rw [e]
    exact L.hasFDerivAt
  have hF' : fderiv ℝ F z = (2 / (1 - ‖z‖ ^ 2)) • L + ((4 / (1 - ‖z‖ ^ 2) ^ 2) • G z).smulRight (G z) :=
    (hc.smul hL).fderiv
  have h2 : ∀ v : ℂ, iteratedFDeriv ℝ 2 φ z ![v, v] =
      2 / (1 - ‖z‖ ^ 2) * L v v + 4 / (1 - ‖z‖ ^ 2) ^ 2 * G z v * G z v := fun v => by
    rw [iteratedFDeriv_two_apply, hev.fderiv_eq]
    show fderiv ℝ F z v v = _
    rw [hF']
    rfl
  -- `Δ log ρ = 4/(1 − |z|²)²`
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  unfold gaussCurvature laplacianGL
  rw [← hφ, h2 1, h2 I, hLv, hLv, hGv, hGv]
  simp only [hypDensityDisc, one_re, one_im, I_re, I_im]
  field_simp
  rw [hn]
  ring

/-- **Proposition 2** (§2.5, l. 1523), completeness and topology. The metric (2.16) is complete on the disc and
induces the usual topology there. -/
theorem prop2_2_c :
    (∀ u : ℕ → ℂ, (∀ n, u n ∈ unitDisc) →
      (∀ ε > (0 : ℝ), ∃ N, ∀ m ≥ N, ∀ n ≥ N, discPoincareDist (u m) (u n) < ε) →
        ∃ z ∈ unitDisc, Tendsto u atTop (𝓝 z)) ∧
      ∀ z ∈ unitDisc, ∀ s : Set ℂ,
        s ∈ 𝓝 z ↔ ∃ r > (0 : ℝ), {w ∈ unitDisc | discPoincareDist z w < r} ⊆ s := by
  refine ⟨fun u hu hcau => ?_, fun z hz s => ⟨fun hs => ?_, ?_⟩⟩
  · -- a `d`-Cauchy sequence stays in a smaller closed disc and is Euclidean Cauchy (`|z − w| ≤ 4d`)
    obtain ⟨N, hN⟩ := hcau 1 one_pos
    obtain ⟨R, hR1, hR⟩ := gl2c_bounded (hu N)
    have hbd : ∀ n ≥ N, ‖u n‖ ≤ R := fun n hn => hR _ (hu n) (hN N le_rfl n hn).le
    have hc : CauchySeq u := by
      refine Metric.cauchySeq_iff.2 fun ε hε => ?_
      obtain ⟨M, hM⟩ := hcau (ε / 4) (by positivity)
      refine ⟨M, fun m hm n hn => ?_⟩
      rw [dist_eq_norm]
      calc ‖u m - u n‖ ≤ 4 * discPoincareDist (u m) (u n) := gl2c_norm_sub_le (hu m) (hu n)
        _ < 4 * (ε / 4) := by gcongr; exact hM m hm n hn
        _ = ε := by ring
    obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hc
    have hzR : ‖z‖ ≤ R := le_of_tendsto (hz.norm) (eventually_atTop.2 ⟨N, hbd⟩)
    exact ⟨z, mem_ball_zero_iff.2 (hzR.trans_lt hR1), hz⟩
  · -- a Euclidean ball `B(z, ε) ⊆ s` contains the `d`-ball of radius `ε/4`
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
    refine ⟨ε / 4, by positivity, fun w hwd => hball ?_⟩
    obtain ⟨hw, hd⟩ := hwd
    rw [mem_ball, dist_eq_norm, norm_sub_rev]
    calc ‖z - w‖ ≤ 4 * discPoincareDist z w := gl2c_norm_sub_le hz hw
      _ < 4 * (ε / 4) := by gcongr
      _ = ε := by ring
  · -- `d(z, ·)` is continuous at `z`, so the `d`-ball is a neighbourhood
    rintro ⟨r, hr, hsub⟩
    refine Filter.mem_of_superset ?_ hsub
    filter_upwards [isOpen_ball.mem_nhds hz, (gl2c_tendsto_dist hz).eventually (gt_mem_nhds hr)] with w hw hd
    exact ⟨hw, hd⟩

/-- **Proposition 2** (§2.5, l. 1523), geodesics. Two distinct points of the disc are joined by a unique geodesic
(a piecewise smooth path of length `d(z, w)`, unique up to reparametrization: all have the same image), and it lies
on a circle orthogonal to the unit circle or on a diameter. -/
theorem prop2_2_d {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hzw : z ≠ w) :
    ∃ σ : Set ℂ, ((∃ (c : ℂ) (r : ℝ), 0 < r ∧ ‖c‖ ^ 2 = 1 + r ^ 2 ∧ σ ⊆ sphere c r) ∨
        ∃ θ : ℝ, σ ⊆ {v : ℂ | ∃ s : ℝ, v = s * exp (θ * I)}) ∧
      (∃ (α : ℝ → ℂ) (s : Finset ℝ), α 0 = z ∧ α 1 = w ∧ MapsTo α (Icc 0 1) unitDisc ∧
        ContinuousOn α (Icc 0 1) ∧ ContDiffOn ℝ 1 α (Icc 0 1 \ ↑s) ∧ α '' Icc 0 1 = σ ∧
        (∫ t in (0 : ℝ)..1, hypDensityDisc (α t) * ‖deriv α t‖) = discPoincareDist z w) ∧
      ∀ (α : ℝ → ℂ) (s : Finset ℝ), α 0 = z → α 1 = w → MapsTo α (Icc 0 1) unitDisc → ContinuousOn α (Icc 0 1) →
        ContDiffOn ℝ 1 α (Icc 0 1 \ ↑s) →
          (∫ t in (0 : ℝ)..1, hypDensityDisc (α t) * ‖deriv α t‖) = discPoincareDist z w → α '' Icc 0 1 = σ := by
  -- normalize: `A = c B_z` sends `z ↦ 0`, `w ↦ δ = δ(z, w) ∈ (0, 1)`; its inverse is `A⁻¹ = c̄ B_{−cz}`
  obtain ⟨c, hc, hcw⟩ := gl2c_normalize z w
  set δ : ℝ := ‖(z - w) / (1 - conj z * w)‖ with hδdef
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
  have hc' : ‖conj c‖ = 1 := by rw [RCLike.norm_conj, hc]
  have hcz : -(c * z) ∈ unitDisc := by
    rw [LiZhongQC.unitDisc, mem_ball_zero_iff, norm_neg, norm_mul, hc, one_mul]
    exact hz1
  obtain ⟨hAd, hAm, hAρ⟩ := gl2c_rb_props hc hz
  obtain ⟨hBd, hBm, hBρ⟩ := gl2c_rb_props hc' hcz
  set A : ℂ → ℂ := fun v => c * LiZhongQC.blaschke z v with hAdef
  set B : ℂ → ℂ := fun y => conj c * LiZhongQC.blaschke (-(c * z)) y
  have hBA : ∀ v ∈ unitDisc, B (A v) = v := fun v hv => gl2c_rb_inv hc hz hv
  have hAz : A z = 0 := by simp [hAdef]
  have hAw : A w = δ := hcw
  have hδ1 : δ < 1 := by
    have := hAm hw
    rw [hAw, LiZhongQC.unitDisc, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs] at this
    exact (le_abs_self δ).trans_lt this
  have hδ0 : 0 < δ := by
    rw [hδdef]
    refine norm_pos_iff.2 (div_ne_zero (sub_ne_zero.2 hzw) ?_)
    have := LiZhongQC.blaschke_den_ne_zero hz1 hw1
    simpa using this
  have hdist : discPoincareDist z w = (1 / 2) * Real.log ((1 + δ) / (1 - δ)) := rfl
  set σ := B '' ((fun r : ℝ => (r : ℂ)) '' Icc 0 δ) with hσ
  refine ⟨σ, gl2c_circle hc' hcz hδ0.le hδ1, ?_, ?_⟩
  · -- the geodesic: `t ↦ A⁻¹(t δ)`
    have hseg : MapsTo (fun t : ℝ => ((t * δ : ℝ) : ℂ)) (Icc 0 1) unitDisc := fun t ht => by
      rw [LiZhongQC.unitDisc, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg ht.1 hδ0.le)]
      nlinarith [ht.2]
    have hsd : ContDiff ℝ 1 (fun t : ℝ => ((t * δ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_id.mul contDiff_const)
    obtain ⟨hm, hcont, hd, hρ⟩ := gl2c_transport hBd hBm hBρ (s := ∅) hseg hsd.continuous.continuousOn
      hsd.contDiffOn
    obtain ⟨hlen, -⟩ := gl2c_integral_congr hρ
    refine ⟨fun t => B ((t * δ : ℝ) : ℂ), ∅, ?_, ?_, hm, hcont, hd, ?_, ?_⟩
    · show B ((0 * δ : ℝ) : ℂ) = z
      rw [zero_mul, Complex.ofReal_zero, ← hAz, hBA z hz]
    · show B ((1 * δ : ℝ) : ℂ) = w
      rw [one_mul, ← hAw, hBA w hw]
    · have e : (fun t : ℝ => B ((t * δ : ℝ) : ℂ)) = (B ∘ fun r : ℝ => (r : ℂ)) ∘ fun t => t * δ := rfl
      rw [e, image_comp, image_mul_right_Icc zero_le_one hδ0.le, zero_mul, one_mul, image_comp]
    · rw [hlen, hdist]
      exact (gl2c_segment_length hδ0.le hδ1).2
  · intro α s h0 h1 hm hcont hd hlen
    obtain ⟨hβm, hβc, hβd, hρ⟩ := gl2c_transport hAd hAm hAρ hm hcont hd
    obtain ⟨hl, hi⟩ := gl2c_integral_congr hρ
    -- `α` has finite length (otherwise its integral would be `0 < d(z, w)`)
    have hint : IntervalIntegrable (fun t => hypDensityDisc (α t) * ‖deriv α t‖) volume 0 1 := by
      by_contra hni
      rw [intervalIntegral.integral_undef hni, hdist] at hlen
      have : 0 < (1 / 2) * Real.log ((1 + δ) / (1 - δ)) := by
        apply mul_pos one_half_pos
        apply Real.log_pos
        rw [one_lt_div (by linarith)]
        linarith
      linarith
    have himg := gl2c_eq_case hβm hβc hβd (hi.2 hint) (x := δ) (by simp [h0, hAz]) (by simp [h1, hAw])
      (by rw [hl, hlen, hdist])
    rw [hσ, ← himg, ← image_comp]
    exact image_congr fun t ht => (hBA (α t) (hm ht)).symm

/-- The Blaschke density identity at GL's normalization `ρ = 1/(1 − |z|²)`. -/
theorem l21a_density_blaschke {c z : ℂ} (hc : ‖c‖ < 1) (hz : ‖z‖ < 1) :
    hypDensityDisc (LiZhongQC.blaschke c z) * ‖deriv (LiZhongQC.blaschke c) z‖ = hypDensityDisc z := by
  have e := LiZhongQC.poincareDensityDisc_pullback_blaschke hc hz
  have hρ : ∀ w : ℂ, hypDensityDisc w = LiZhongQC.poincareDensityDisc w / 2 := fun w => by
    show (1 / (1 - ‖w‖ ^ 2)) = 2 / (1 - ‖w‖ ^ 2) / 2
    ring
  rw [hρ, hρ, div_mul_eq_mul_div, div_eq_div_iff two_ne_zero two_ne_zero]
  rw [e]

/-- **Lemma 1** (the Schwarz–Pick lemma, §2.5, l. 1542), infinitesimal form. For a holomorphic self-map `f` of the
disc, `ρ_Δ(f(z)) |f′(z)| ≤ ρ_Δ(z)`, and equality at one point forces `f` to be a Möbius transformation of the disc. -/
theorem lemma2_1_a {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hmaps : MapsTo f unitDisc unitDisc) :
    (∀ z ∈ unitDisc, hypDensityDisc (f z) * ‖deriv f z‖ ≤ hypDensityDisc z) ∧
      ((∃ z ∈ unitDisc, hypDensityDisc (f z) * ‖deriv f z‖ = hypDensityDisc z) →
        ∃ (θ : ℝ) (a : ℂ), a ∈ unitDisc ∧ ∀ z ∈ unitDisc, f z = exp (θ * I) * ((z - a) / (1 - conj a * z))) := by
  have hnorm : ∀ z ∈ unitDisc, ‖z‖ < 1 := fun z hz => mem_ball_zero_iff.1 hz
  have hpos1 : ∀ z ∈ unitDisc, (0 : ℝ) < 1 - ‖z‖ ^ 2 := fun z hz => by
    have h1 : ‖z‖ ^ 2 < (1 : ℝ) := by
      calc ‖z‖ ^ 2 < (1 : ℝ) ^ 2 := pow_lt_pow_left₀ (hnorm z hz) (norm_nonneg _) two_ne_zero
        _ = 1 := one_pow 2
    linarith
  constructor
  · intro z hz
    have h1 := hpos1 z hz
    have h2 := hpos1 (f z) (hmaps hz)
    have key := LiZhongQC.t203_mono_schwarz_pick hf hmaps hz
    show (1 / (1 - ‖f z‖ ^ 2)) * ‖deriv f z‖ ≤ 1 / (1 - ‖z‖ ^ 2)
    rw [one_div, one_div, mul_comm ((1 - ‖f z‖ ^ 2)⁻¹) _, ← div_eq_mul_inv, div_le_iff₀ h2,
      mul_comm ((1 - ‖z‖ ^ 2)⁻¹) _, ← div_eq_mul_inv, le_div_iff₀ h1]
    exact key
  · rintro ⟨a, ha, heq⟩
    have haN : ‖a‖ < 1 := hnorm a ha
    have hfaN : ‖f a‖ < 1 := hnorm (f a) (hmaps ha)
    have h1 := hpos1 a ha
    have h1' := hpos1 (f a) (hmaps ha)
    have hρ0 : hypDensityDisc (0 : ℂ) = 1 := by
      show 1 / (1 - ‖(0 : ℂ)‖ ^ 2) = 1
      simp
    have hρa : hypDensityDisc a ≠ 0 := (one_div_pos.2 h1).ne'
    -- the normalized map `g = M_{f a} ∘ f ∘ M_{-a}`
    set g := fun w => LiZhongQC.blaschke (f a) (f (LiZhongQC.blaschke (-a) w)) with hgdef
    have hnaN : ‖-a‖ < 1 := by rwa [norm_neg]
    have hb0 : LiZhongQC.blaschke (-a) 0 = a := by simp [LiZhongQC.blaschke]
    have hg0 : g 0 = 0 := by
      rw [hgdef]
      simp [LiZhongQC.blaschke]
    have hmap1 : MapsTo (LiZhongQC.blaschke (-a)) unitDisc unitDisc := fun w hw =>
      mem_ball_zero_iff.2 (LiZhongQC.blaschke_mem_unitDisc hnaN (hnorm w hw))
    have hmap2 : MapsTo (LiZhongQC.blaschke (f a)) unitDisc unitDisc := fun w hw =>
      mem_ball_zero_iff.2 (LiZhongQC.blaschke_mem_unitDisc hfaN (hnorm w hw))
    have hgdiff : DifferentiableOn ℂ g unitDisc :=
      (LiZhongQC.differentiableOn_blaschke hfaN).comp
        (hf.comp (LiZhongQC.differentiableOn_blaschke hnaN) hmap1)
        (fun w hw => hmaps (hmap1 hw))
    have hgmaps : MapsTo g unitDisc unitDisc := fun w hw => hmap2 (hmaps (hmap1 hw))
    -- the derivative at 0 and its norm
    have hB : HasDerivAt f (deriv f a) a :=
      (hf.differentiableAt (isOpen_ball.mem_nhds ha)).hasDerivAt
    have h1d : HasDerivAt (LiZhongQC.blaschke (-a)) (deriv (LiZhongQC.blaschke (-a)) 0) 0 :=
      ((LiZhongQC.differentiableOn_blaschke hnaN).differentiableAt
        (isOpen_ball.mem_nhds (mem_ball_self one_pos))).hasDerivAt
    have h2' : HasDerivAt f (deriv f a) (LiZhongQC.blaschke (-a) 0) := by
      rw [hb0]
      exact hB
    have h3' : HasDerivAt (LiZhongQC.blaschke (f a)) (deriv (LiZhongQC.blaschke (f a)) (f a))
        (f (LiZhongQC.blaschke (-a) 0)) := by
      rw [hb0]
      exact ((LiZhongQC.differentiableOn_blaschke hfaN).differentiableAt
        (isOpen_ball.mem_nhds (hmaps ha))).hasDerivAt
    have hge : g = LiZhongQC.blaschke (f a) ∘ f ∘ LiZhongQC.blaschke (-a) := rfl
    have hchain : deriv g 0 = deriv (LiZhongQC.blaschke (f a)) (f a) *
        (deriv f a * deriv (LiZhongQC.blaschke (-a)) 0) := by
      rw [hge]
      exact (h3'.comp 0 (h2'.comp 0 h1d)).deriv
    have hpb1 : ‖deriv (LiZhongQC.blaschke (-a)) 0‖ = (hypDensityDisc a)⁻¹ := by
      have e := l21a_density_blaschke hnaN (by simp : ‖(0 : ℂ)‖ < 1)
      rw [hb0, hρ0, mul_comm] at e
      exact eq_inv_of_mul_eq_one_left e
    have hpb3 : ‖deriv (LiZhongQC.blaschke (f a)) (f a)‖ = hypDensityDisc (f a) := by
      have e := l21a_density_blaschke hfaN hfaN
      have hbself : LiZhongQC.blaschke (f a) (f a) = 0 := by simp [LiZhongQC.blaschke]
      rw [hbself, hρ0, one_mul] at e
      exact e
    have hnormg : ‖deriv g 0‖ = 1 := by
      rw [hchain, norm_mul, norm_mul, hpb1, hpb3, ← mul_assoc, heq]
      exact mul_inv_cancel₀ hρa
    -- Schwarz' equality case: g is a rotation
    obtain ⟨C, hC1, hCe⟩ := affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div'
      (f := g) (c := (0 : ℂ)) (R₁ := 1) (R₂ := 1)
      hgdiff (by rw [hg0]; exact fun w hw => ball_subset_closedBall (hgmaps hw))
      ⟨0, mem_ball_self one_pos, by rw [dslope_same, hnormg]; norm_num⟩
    -- f on Δ through g: f z = M_{-f a} (C · M_a z)
    have hfg : ∀ z ∈ unitDisc, f z = LiZhongQC.blaschke (-f a) (C * LiZhongQC.blaschke a z) := by
      intro z hz
      have hzn := hnorm z hz
      have e1 : g (LiZhongQC.blaschke a z) = LiZhongQC.blaschke (f a) (f z) := by
        rw [hgdef]
        simp only []
        rw [LiZhongQC.blaschke_neg_blaschke haN hzn]
      have e2 : g (LiZhongQC.blaschke a z) = C * LiZhongQC.blaschke a z := by
        have hzz := hCe (mem_ball_zero_iff.2 (LiZhongQC.blaschke_mem_unitDisc haN hzn))
        rw [hg0] at hzz
        simp only [zero_add, sub_zero, smul_eq_mul] at hzz
        rw [hzz, mul_comm]
      have e3 := LiZhongQC.blaschke_neg_blaschke hfaN (hnorm (f z) (hmaps hz))
      rw [← e3, ← e1, e2]
    -- classification: the composition is a conformal automorphism, hence `c * M_{a'}`
    have hC1' : ‖C‖ = 1 := by rw [hC1]; norm_num
    have hCrot : LiZhongQC.IsConformalOnto (fun z => C * z) unitDisc unitDisc := by
      have hC0 : C ≠ 0 := norm_pos_iff.1 (hC1' ▸ one_pos)
      refine ⟨differentiableOn_id.const_mul C, fun z₁ _ z₂ _ h => mul_left_cancel₀ hC0 h, ?_⟩
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact mem_ball_zero_iff.2 (by rw [norm_mul, hC1', one_mul]; exact hnorm w hw)
      · intro hz
        refine ⟨C⁻¹ * z, mem_ball_zero_iff.2 ?_, ?_⟩
        · rw [norm_mul, norm_inv, hC1', inv_one, one_mul]
          exact hnorm z hz
        · show C * (C⁻¹ * z) = z
          rw [← mul_assoc, mul_inv_cancel₀ hC0, one_mul]
    have hnfaN : ‖-f a‖ < 1 := by rwa [norm_neg]
    have hHconf : LiZhongQC.IsConformalOnto (fun z => LiZhongQC.blaschke (-f a) (C * LiZhongQC.blaschke a z))
        unitDisc unitDisc :=
      (LiZhongQC.isConformalOnto_blaschke hnfaN).comp (hCrot.comp
        (LiZhongQC.isConformalOnto_blaschke haN))
    obtain ⟨c', a', hc'1, ha'1, heq'⟩ :=
      LiZhongQC.exists_rotation_blaschke_of_isConformalOnto_unitDisc hHconf
    -- the final form
    refine ⟨c'.arg, a', mem_ball_zero_iff.2 ha'1, fun z hz => ?_⟩
    have hzN := hnorm z hz
    have hc'eq : c' = exp (c'.arg * I) := by
      have h := Complex.norm_mul_exp_arg_mul_I c'
      rw [hc'1, Complex.ofReal_one, one_mul] at h
      exact h.symm
    calc f z = LiZhongQC.blaschke (-f a) (C * LiZhongQC.blaschke a z) := hfg z hz
      _ = c' * LiZhongQC.blaschke a' z := heq' hz
      _ = exp (c'.arg * I) * ((z - a') / (1 - conj a' * z)) := by rw [← hc'eq]; rfl

/-- The formula `r ↦ ½ log((1+r)/(1−r))` reflects the order on `[0, 1)`. -/
theorem l21b_halfLog_mono {r r' : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (hr' : 0 ≤ r') (hr1' : r' < 1) :
    (1 / 2) * Real.log ((1 + r') / (1 - r')) ≤ (1 / 2) * Real.log ((1 + r) / (1 - r)) ↔ r' ≤ r := by
  have hp1 : (0 : ℝ) < 1 - r := by linarith
  have hp1' : (0 : ℝ) < 1 - r' := by linarith
  have hmono : (1 + r') / (1 - r') ≤ (1 + r) / (1 - r) ↔ r' ≤ r := by
    rw [div_le_div_iff₀ hp1' hp1]
    constructor <;> intro h <;> nlinarith
  rw [mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 1 / 2),
    Real.log_le_log_iff (by positivity) (by positivity), hmono]

/-- The Blaschke normal form `g = M_{f z} ∘ f ∘ M_{-z}` of a disc self-map at `z`. -/
theorem l21b_normalized {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hmaps : MapsTo f unitDisc unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g unitDisc ∧ MapsTo g unitDisc unitDisc ∧ g 0 = 0 ∧
      (∀ w : ℂ, w ∈ unitDisc → g (LiZhongQC.blaschke z w) = LiZhongQC.blaschke (f z) (f w)) ∧
      ∀ u : ℂ, u ∈ unitDisc →
        f u = LiZhongQC.blaschke (-f z) (g (LiZhongQC.blaschke z u)) := by
  have hnorm : ∀ u ∈ unitDisc, ‖u‖ < 1 := fun u hu => mem_ball_zero_iff.1 hu
  have hzN := hnorm z hz
  have hfzN := hnorm (f z) (hmaps hz)
  have hnzN : ‖-z‖ < 1 := by rwa [norm_neg]
  set g := fun u => LiZhongQC.blaschke (f z) (f (LiZhongQC.blaschke (-z) u)) with hgdef
  have hmap1 : MapsTo (LiZhongQC.blaschke (-z)) unitDisc unitDisc := fun u hu =>
    mem_ball_zero_iff.2 (LiZhongQC.blaschke_mem_unitDisc hnzN (hnorm u hu))
  have hgmaps : MapsTo g unitDisc unitDisc := fun u hu =>
    mem_ball_zero_iff.2 (LiZhongQC.blaschke_mem_unitDisc hfzN (hnorm _ (hmaps (hmap1 hu))))
  have hg0 : g 0 = 0 := by
    rw [hgdef]
    simp [LiZhongQC.blaschke]
  have hgdiff : DifferentiableOn ℂ g unitDisc :=
    (LiZhongQC.differentiableOn_blaschke hfzN).comp
      (hf.comp (LiZhongQC.differentiableOn_blaschke hnzN) hmap1)
      (fun u hu => hmaps (hmap1 hu))
  refine ⟨g, hgdiff, hgmaps, hg0, fun w hw => ?_, fun u hu => ?_⟩
  · rw [hgdef]
    simp only []
    rw [LiZhongQC.blaschke_neg_blaschke hzN (hnorm w hw)]
  · have e1 : g (LiZhongQC.blaschke z u) = LiZhongQC.blaschke (f z) (f u) := by
      rw [hgdef]
      simp only []
      rw [LiZhongQC.blaschke_neg_blaschke hzN (hnorm u hu)]
    have e3 := LiZhongQC.blaschke_neg_blaschke hfzN (hnorm (f u) (hmaps hu))
    rw [← e3, ← e1]

/-- The Schwarz lemma through Blaschke factors: `f` contracts the pseudo-hyperbolic distance. -/
theorem l21b_pseudoHyp_le {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hmaps : MapsTo f unitDisc unitDisc) {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    ‖LiZhongQC.blaschke (f z) (f w)‖ ≤ ‖LiZhongQC.blaschke z w‖ := by
  obtain ⟨g, hgdiff, hgmaps, hg0, hgval, -⟩ := l21b_normalized hf hmaps hz
  have hgschwarz : ‖g (LiZhongQC.blaschke z w)‖ ≤ ‖LiZhongQC.blaschke z w‖ :=
    Complex.norm_le_norm_of_mapsTo_ball hgdiff
      (fun u hu => ball_subset_closedBall (hgmaps hu)) hg0
      (LiZhongQC.blaschke_mem_unitDisc (mem_ball_zero_iff.1 hz) (mem_ball_zero_iff.1 hw))
  rwa [hgval w hw] at hgschwarz

/-- The equality case of the pseudo-hyperbolic Schwarz lemma. -/
theorem l21b_automorphism_of_pseudoHyp_eq {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc)
    (hmaps : MapsTo f unitDisc unitDisc) {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc)
    (hzw : z ≠ w)
    (heq : ‖LiZhongQC.blaschke (f z) (f w)‖ = ‖LiZhongQC.blaschke z w‖) :
    ∃ (θ : ℝ) (a : ℂ), a ∈ unitDisc ∧ ∀ u ∈ unitDisc,
      f u = exp (θ * I) * ((u - a) / (1 - conj a * u)) := by
  have hnorm : ∀ u ∈ unitDisc, ‖u‖ < 1 := fun u hu => mem_ball_zero_iff.1 hu
  obtain ⟨g, hgdiff, hgmaps, hg0, hgval, hginv⟩ := l21b_normalized hf hmaps hz
  -- the Schwarz equality case at `ζ = blaschke z w ≠ 0`
  have hζ : LiZhongQC.blaschke z w ≠ 0 := by
    have hden := LiZhongQC.blaschke_den_ne_zero (hnorm z hz) (hnorm w hw)
    intro h0
    have h1 : LiZhongQC.blaschke z w = (w - z) / (1 - conj z * w) := rfl
    rw [h1, div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact hzw (sub_eq_zero.1 h0).symm
    · exact hden h0
  have hdslope : dslope g 0 (LiZhongQC.blaschke z w) =
      g (LiZhongQC.blaschke z w) / LiZhongQC.blaschke z w := by
    rw [dslope_of_ne _ hζ]
    simp only [slope, hg0, vsub_eq_sub, sub_zero, smul_eq_mul, div_eq_mul_inv]
    ring
  have hdslopeNorm : ‖dslope g 0 (LiZhongQC.blaschke z w)‖ = 1 / 1 := by
    rw [hdslope, norm_div, hgval w hw, heq, div_self (norm_ne_zero_iff.2 hζ)]
    norm_num
  obtain ⟨C, hC1, hCe⟩ := affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div'
    (f := g) (c := (0 : ℂ)) (R₁ := 1) (R₂ := 1)
    hgdiff (by rw [hg0]; exact fun u hu => ball_subset_closedBall (hgmaps hu))
    ⟨LiZhongQC.blaschke z w, mem_ball_zero_iff.2 (LiZhongQC.blaschke_mem_unitDisc (hnorm z hz) (hnorm w hw)),
      hdslopeNorm⟩
  have hC1' : ‖C‖ = 1 := by rw [hC1]; norm_num
  -- f = M_{-f z} ∘ (C ·) ∘ M_z is a conformal automorphism of the disc
  have hfu : ∀ u ∈ unitDisc, f u = LiZhongQC.blaschke (-f z) (C * LiZhongQC.blaschke z u) := by
    intro u hu
    rw [hginv u hu]
    have huu := hCe (mem_ball_zero_iff.2 (LiZhongQC.blaschke_mem_unitDisc (hnorm z hz) (hnorm u hu)))
    rw [hg0] at huu
    simp only [zero_add, sub_zero, smul_eq_mul] at huu
    rw [huu, mul_comm]
  have hCrot : LiZhongQC.IsConformalOnto (fun u => C * u) unitDisc unitDisc := by
    have hC0 : C ≠ 0 := norm_pos_iff.1 (hC1' ▸ one_pos)
    refine ⟨differentiableOn_id.const_mul C, fun z₁ _ z₂ _ h => mul_left_cancel₀ hC0 h, ?_⟩
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_ball_zero_iff.2 (by rw [norm_mul, hC1', one_mul]; exact hnorm x hx)
    · intro hu
      refine ⟨C⁻¹ * u, mem_ball_zero_iff.2 ?_, ?_⟩
      · rw [norm_mul, norm_inv, hC1', inv_one, one_mul]
        exact hnorm u hu
      · show C * (C⁻¹ * u) = u
        rw [← mul_assoc, mul_inv_cancel₀ hC0, one_mul]
  have hHconf : LiZhongQC.IsConformalOnto (fun u => LiZhongQC.blaschke (-f z) (C * LiZhongQC.blaschke z u))
      unitDisc unitDisc :=
    (LiZhongQC.isConformalOnto_blaschke (by rw [norm_neg]; exact hnorm (f z) (hmaps hz))).comp (hCrot.comp
      (LiZhongQC.isConformalOnto_blaschke (hnorm z hz)))
  obtain ⟨c', a', hc'1, ha'1, heq'⟩ :=
    LiZhongQC.exists_rotation_blaschke_of_isConformalOnto_unitDisc hHconf
  refine ⟨c'.arg, a', mem_ball_zero_iff.2 ha'1, fun u hu => ?_⟩
  have hc'eq : c' = exp (c'.arg * I) := by
    have h := Complex.norm_mul_exp_arg_mul_I c'
    rw [hc'1, Complex.ofReal_one, one_mul] at h
    exact h.symm
  calc f u = LiZhongQC.blaschke (-f z) (C * LiZhongQC.blaschke z u) := hfu u hu
    _ = c' * LiZhongQC.blaschke a' u := heq' hu
    _ = exp (c'.arg * I) * ((u - a') / (1 - conj a' * u)) := by rw [← hc'eq]; rfl

/-- **Lemma 1** (the Schwarz–Pick lemma, §2.5, l. 1542), global form. `d(f(z), f(w)) ≤ d(z, w)`, and equality for
two distinct points forces `f` to be a Möbius transformation of the disc. -/
theorem lemma2_1_b {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hmaps : MapsTo f unitDisc unitDisc) :
    (∀ z ∈ unitDisc, ∀ w ∈ unitDisc, discPoincareDist (f z) (f w) ≤ discPoincareDist z w) ∧
      ((∃ z ∈ unitDisc, ∃ w ∈ unitDisc, z ≠ w ∧ discPoincareDist (f z) (f w) = discPoincareDist z w) →
        ∃ (θ : ℝ) (a : ℂ), a ∈ unitDisc ∧ ∀ z ∈ unitDisc, f z = exp (θ * I) * ((z - a) / (1 - conj a * z))) := by
  have hnorm : ∀ u ∈ unitDisc, ‖u‖ < 1 := fun u hu => mem_ball_zero_iff.1 hu
  -- the distance is the arctanh-formula of the pseudo-hyperbolic distance
  have hdist : ∀ z w : ℂ, discPoincareDist z w =
      (1 / 2) * Real.log ((1 + ‖LiZhongQC.blaschke z w‖) / (1 - ‖LiZhongQC.blaschke z w‖)) := by
    intro z w
    have e : ‖(z - w) / (1 - conj z * w)‖ = ‖LiZhongQC.blaschke z w‖ := by
      simp only [LiZhongQC.blaschke, norm_div, norm_sub_rev z w]
    show (1 / 2) * Real.log ((1 + ‖(z - w) / (1 - conj z * w)‖) /
        (1 - ‖(z - w) / (1 - conj z * w)‖)) = _
    rw [e]
  constructor
  · intro z hz w hw
    rw [hdist, hdist]
    exact (l21b_halfLog_mono (norm_nonneg _) (LiZhongQC.blaschke_mem_unitDisc (hnorm z hz) (hnorm w hw))
      (norm_nonneg _) (LiZhongQC.blaschke_mem_unitDisc (hnorm (f z) (hmaps hz)) (hnorm (f w) (hmaps hw)))).2
      (l21b_pseudoHyp_le hf hmaps hz hw)
  · rintro ⟨z, hz, w, hw, hzw, heqD⟩
    rw [hdist, hdist] at heqD
    have hrr : ‖LiZhongQC.blaschke (f z) (f w)‖ = ‖LiZhongQC.blaschke z w‖ := by
      have hb1 := LiZhongQC.blaschke_mem_unitDisc (hnorm (f z) (hmaps hz)) (hnorm (f w) (hmaps hw))
      have hb2 := LiZhongQC.blaschke_mem_unitDisc (hnorm z hz) (hnorm w hw)
      have h1 := (l21b_halfLog_mono (norm_nonneg _) hb2 (norm_nonneg _) hb1).1 (le_of_eq heqD)
      have h2 := (l21b_halfLog_mono (norm_nonneg _) hb1 (norm_nonneg _) hb2).1 (le_of_eq heqD.symm)
      exact le_antisymm h1 h2
    exact l21b_automorphism_of_pseudoHyp_eq hf hmaps hz hw hzw hrr

/-- **Formula (2.18)** (§2.5, l. 1555–1563), as a definition (plane reading, leader ruling A0.4(ii)). The Poincaré
density of the plane domain `Ω` at `z₀`: `ρ(z₀) = inf 1/|g′(0)|` over the holomorphic maps `g` of the unit disc into
`Ω` with `g(0) = z₀`.
Modelling (leader fix 2026-10-05): the infimum is `sInf` of the set of values, and maps with `g′(0) = 0` are
excluded. In the book they contribute `1/0 = ∞` and never matter; in Lean `1/0 = 0`, and a bounded `⨅ g (_ : P g)`
in `ℝ` is `0` at every `g` failing `P`, so the earlier `⨅` form was identically `0`. Junk: `0` when `z₀ ∉ Ω` (empty
set). -/
def poincareDensityGL (Ω : Set ℂ) (z₀ : ℂ) : ℝ :=
  sInf {r : ℝ | ∃ g : ℂ → ℂ, DifferentiableOn ℂ g unitDisc ∧ MapsTo g unitDisc Ω ∧ g 0 = z₀ ∧ deriv g 0 ≠ 0 ∧
    r = 1 / ‖deriv g 0‖}

/-- Helper (§2.5, (2.18)). A covering map `Δ → Ω` is injective on an open neighbourhood (inside `Δ`) of each point
of `Δ`. -/
theorem gl2c_cov_injOn {Ω : Set ℂ} {g : ℂ → ℂ} (hmaps : MapsTo g unitDisc Ω)
    (hcov : IsCoveringMap (hmaps.restrict g unitDisc Ω)) {w : ℂ} (hw : w ∈ unitDisc) :
    ∃ U : Set ℂ, IsOpen U ∧ w ∈ U ∧ U ⊆ unitDisc ∧ InjOn g U := by
  obtain ⟨e, he, hfe⟩ := hcov.isLocalHomeomorph ⟨w, hw⟩
  refine ⟨Subtype.val '' e.source, (isOpen_ball.isOpenMap_subtype_val) _ e.open_source, ⟨_, he, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
  have : (hmaps.restrict g unitDisc Ω) a = (hmaps.restrict g unitDisc Ω) b := Subtype.ext hab
  rw [hfe] at this
  exact congrArg Subtype.val (e.injOn ha hb this)

/-- Helper (§2.5, (2.18)). A holomorphic map `h : Δ → Ω` with `h(0) = g(0)` lifts through a holomorphic covering
`g : Δ → Ω` to a holomorphic self-map `k` of `Δ` with `k(0) = 0` (Mathlib's lifting criterion; `Δ` is simply connected
and locally path connected; `k` is holomorphic because `g` is injective near each `k(z)`). -/
theorem gl2c_lift {Ω : Set ℂ} {g h : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) (hmaps : MapsTo g unitDisc Ω)
    (hcov : IsCoveringMap (hmaps.restrict g unitDisc Ω)) (hh : DifferentiableOn ℂ h unitDisc)
    (hhm : MapsTo h unitDisc Ω) (h0 : h 0 = g 0) :
    ∃ k : ℂ → ℂ, DifferentiableOn ℂ k unitDisc ∧ MapsTo k unitDisc unitDisc ∧ k 0 = 0 ∧
      ∀ z ∈ unitDisc, g (k z) = h z := by
  classical
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have := LiZhongQC.t1_simplyConnected_unitDisc
  have : LocallyPathConnectedSpace unitDisc := (isOpen_ball (x := (0 : ℂ)) (ε := 1)).locallyPathConnectedSpace
  let f : C(unitDisc, Ω) := ⟨hhm.restrict h unitDisc Ω, hh.continuousOn.mapsToRestrict hhm⟩
  obtain ⟨F, ⟨hF0, hFl⟩, -⟩ :=
    hcov.existsUnique_continuousMap_lifts f ⟨0, h0D⟩ ⟨0, h0D⟩ (Subtype.ext h0.symm)
  set k : ℂ → ℂ := fun z => if hz : z ∈ unitDisc then (F ⟨z, hz⟩ : ℂ) else 0 with hkdef
  have hkF : ∀ z (hz : z ∈ unitDisc), k z = F ⟨z, hz⟩ := fun z hz => by simp [hkdef, hz]
  have hgk : ∀ z ∈ unitDisc, g (k z) = h z := fun z hz => by
    rw [hkF z hz]
    exact congrArg Subtype.val (congrFun hFl ⟨z, hz⟩)
  have hkc : ContinuousOn k unitDisc := by
    rw [continuousOn_iff_continuous_domRestrict]
    have e : unitDisc.domRestrict k = fun x => (F x : ℂ) := by
      funext x
      exact hkF x x.2
    rw [e]
    exact continuous_subtype_val.comp F.continuous
  refine ⟨k, fun z hz => ?_, fun z hz => by rw [hkF z hz]; exact (F _).2, by rw [hkF 0 h0D, hF0], hgk⟩
  -- `k` is holomorphic: `g ∘ k = h` with `g` injective near `k z`
  obtain ⟨U, hUo, hkU, hUD, hinj⟩ := gl2c_cov_injOn hmaps hcov (hkF z hz ▸ (F ⟨z, hz⟩).2)
  have hzn : unitDisc ∈ 𝓝 z := isOpen_ball.mem_nhds hz
  refine (LiZhongQC.tor_h_differentiableAt_of_comp_eq hUo (hg.mono hUD) hinj hkU (hkc.continuousAt hzn)
    (hh.differentiableAt hzn) ?_).differentiableWithinAt
  filter_upwards [hzn] with w hw
  exact hgk w hw

/-- **Formula (2.18)** (§2.5, l. 1563). For a hyperbolic plane domain `Ω` (connected, with at least two finite
boundary points) the infimum in (2.18) is attained by every universal covering map `g : Δ → Ω` with `g(0) = z₀`:
`ρ_Ω(z₀) = 1/|g′(0)|`; this is the density induced by the uniformization `Ω = Δ/Γ` (curvature −4). -/
theorem eq2_18 {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsConnected Ω) (hhyp : (Ωᶜ).encard ≥ 2) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) (hmaps : MapsTo g unitDisc Ω) (hg0 : g 0 = z₀)
    (hcov : IsCoveringMap (hmaps.restrict g unitDisc Ω)) :
    poincareDensityGL Ω z₀ = 1 / ‖deriv g 0‖ := by
  -- the topology of `Ω` enters only through the covering `g`
  have _ := hΩ
  have _ := hc
  have _ := hhyp
  have _ := hz₀
  have h0D : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have h0n : unitDisc ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds h0D
  have hg' : deriv g 0 ≠ 0 := by
    obtain ⟨U, hUo, h0U, hUD, hinj⟩ := gl2c_cov_injOn hmaps hcov h0D
    exact LiZhongQC.deriv_ne_zero_of_injOn hUo (hg.mono hUD) hinj h0U
  refine IsLeast.csInf_eq ⟨⟨g, hg, hmaps, hg0, hg', rfl⟩, ?_⟩
  rintro r ⟨h, hh, hhm, hh0, hh', rfl⟩
  -- lift `h = g ∘ k` with `k(0) = 0`, so `h′(0) = g′(0) k′(0)` and `|k′(0)| ≤ 1` (Schwarz)
  obtain ⟨k, hk, hkm, hk0, hgk⟩ := gl2c_lift hg hmaps hcov hh hhm (hh0.trans hg0.symm)
  have hkd : DifferentiableAt ℂ k 0 := hk.differentiableAt h0n
  have hgd : DifferentiableAt ℂ g (k 0) := by
    rw [hk0]
    exact hg.differentiableAt h0n
  have hev : (g ∘ k) =ᶠ[𝓝 0] h := by
    filter_upwards [h0n] with z hz
    exact hgk z hz
  have hd : deriv h 0 = deriv g 0 * deriv k 0 := by
    rw [← hev.deriv_eq, deriv_comp _ hgd hkd, hk0]
  have hS := (lemma2_1_a hk hkm).1 0 h0D
  rw [hk0] at hS
  simp [hypDensityDisc] at hS
  rw [hd] at hh' ⊢
  have hk' : deriv k 0 ≠ 0 := right_ne_zero_of_mul hh'
  rw [norm_mul]
  apply one_div_le_one_div_of_le (mul_pos (norm_pos_iff.2 hg') (norm_pos_iff.2 hk'))
  calc ‖deriv g 0‖ * ‖deriv k 0‖ ≤ ‖deriv g 0‖ * 1 := by gcongr
    _ = ‖deriv g 0‖ := mul_one _

end GardinerLakic2000
