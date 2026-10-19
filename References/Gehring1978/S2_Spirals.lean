import LiZhongQC.Ch05.S19_Schwarzian

/-!
# Gehring 1978, §2 Spirals

F. W. Gehring, *Spirals and the universal Teichmüller space*, Acta Math. 141 (1978), §2; source `full.md` of
`Spirals and the universal Teichmüller space.pdf-602096dc…`, lines 91–437.

* Definition (open arc in `ℂ`, standing) — `IsOpenArc`
* Definition (spiral from `z₁` onto `z₂`, (2), (3); `b`-spiral, (4); §2) — `IsSpiral`, `IsBSpiral`
* Definition (curvature `k` and `dk/ds` of an analytic arc, used from the Example on) — `curvature`, `curvatureDeriv`
* Example, formula (5) (the logarithmic spiral `z = e^{(-a+i)t}`) — `eq5`
* Proposition 1 — `prop1`
* Proposition 2 — `prop2`
* Lemma 1 — `lemma1`
* Definition (analytic open arc with given endpoints; rectifiable arc; used in Lemmas 2–5) — `IsAnalyticArcParam`,
  `IsRectifiableArc`
* Lemma 2 — `lemma2`
* Lemma 3 — `lemma3`
* Lemma 4 — `lemma4`
* Lemma 5 — `lemma5`

Not items (DESIGN §3):
- the unnumbered claim of the Example that `e^{(-a+i)t}`, `t > 0`, is an `e^{2πa}`-spiral from `1` onto `0` (l. 121);
- the geometric fact before Lemma 1 (l. 149: the limit points of two disjoint `b`-spirals, `b ∈ (1, 2)`, coincide or
  are far apart), called there an immediate consequence of Lemma 1 and not cited later (U−);
- the sentence before Lemma 4 (l. 365) that Lemma 5 carries logarithmic spirals to spirals under nearly similar maps
  (informal, U−);
- Kneser's theorem, quoted inside the proof of Lemma 2 (l. 231);
- the exercise of Ahlfors' book quoted in the proof of Lemma 4 (l. 397).

**Conventions.**
- An open arc is the image of the open interval `(0, ∞)` under a topological embedding.
- An analytic open arc "from `p` to `q`" has a regular real-analytic embedding `z : (0, ∞) → ℂ` with `z(t) → p` as
  `t → 0` and `z(t) → q` as `t → ∞`. The arclength `s` is taken in the direction of increasing `t`.
- Curvature is signed: `k = Im(z''/z')/|z'|`, positive when the arc turns to the left.
- A hypothesis "for `z ∈ α`" on `k(z)` or `dk/ds(z)` is stated for every parameter `t > 0`. These quantities do not
  change under orientation preserving reparametrization, so this loses nothing.
-/

open Complex Set Metric Filter Topology
open scoped ENNReal NNReal Real

noncomputable section

namespace Gehring1978

open LiZhongQC

/-- **Definition** (§2, standing). An open arc in `ℂ`: the image of the open interval `(0, ∞)` (homeomorphic to every
open interval) under a topological embedding. -/
def IsOpenArc (α : Set ℂ) : Prop :=
  ∃ z : ℝ → ℂ, IsEmbedding ((Ioi (0 : ℝ)).domRestrict z) ∧ z '' Ioi 0 = α

/-- The curve (2) of the definition of a spiral: `z(t) = (z₁ - z₂) r(t) e^{it} + z₂`. -/
def spiralCurve (z₁ z₂ : ℂ) (r : ℝ → ℝ) (t : ℝ) : ℂ :=
  (z₁ - z₂) * (r t : ℂ) * cexp ((t : ℂ) * I) + z₂

/-- The function `r` gives the representation (2), (3) of `α` as a spiral from `z₁` onto `z₂`: `r` is positive and
continuous on `(0, ∞)`, `r(t) → 1` as `t → 0`, `r(t) → 0` as `t → ∞`, and `t ↦ z(t)` parametrizes `α` one-to-one. -/
def IsSpiralRep (α : Set ℂ) (z₁ z₂ : ℂ) (r : ℝ → ℝ) : Prop :=
  ContinuousOn r (Ioi 0) ∧ (∀ t ∈ Ioi (0 : ℝ), 0 < r t) ∧ Tendsto r (𝓝[>] 0) (𝓝 1) ∧ Tendsto r atTop (𝓝 0) ∧
    InjOn (spiralCurve z₁ z₂ r) (Ioi 0) ∧ spiralCurve z₁ z₂ r '' Ioi 0 = α

/-- **Definition** (§2). The open arc `α ⊆ ℂ` is a spiral from `z₁` onto `z₂`: it has a representation (2)
`z = z(t) = (z₁ - z₂) r(t) e^{it} + z₂`, `t ∈ (0, ∞)`, with `r` positive and continuous satisfying (3)
`lim_{t → 0} r(t) = 1`, `lim_{t → ∞} r(t) = 0`.
Modelling: "representation" is read as a one-to-one parametrization (`IsSpiralRep`), as the proof of Proposition 1
uses. -/
def IsSpiral (α : Set ℂ) (z₁ z₂ : ℂ) : Prop :=
  IsOpenArc α ∧ ∃ r : ℝ → ℝ, IsSpiralRep α z₁ z₂ r

/-- **Definition** (§2). For `b ∈ (1, ∞)`, `α` is a `b`-spiral from `z₁` onto `z₂`: a spiral from `z₁` onto `z₂`
whose representation (2) satisfies in addition (4) `|z(t₁) - z₂| ≤ b |z(t₂) - z₂|` for all `t₁, t₂ ∈ (0, ∞)` with
`|t₁ - t₂| ≤ 2π`.
Modelling: the standing `b ∈ (1, ∞)` of the definition is part of the predicate. -/
def IsBSpiral (α : Set ℂ) (z₁ z₂ : ℂ) (b : ℝ) : Prop :=
  1 < b ∧ IsOpenArc α ∧ ∃ r : ℝ → ℝ, IsSpiralRep α z₁ z₂ r ∧
    ∀ t₁ ∈ Ioi (0 : ℝ), ∀ t₂ ∈ Ioi (0 : ℝ), |t₁ - t₂| ≤ 2 * π →
      ‖spiralCurve z₁ z₂ r t₁ - z₂‖ ≤ b * ‖spiralCurve z₁ z₂ r t₂ - z₂‖

/-- **Definition** (§2, used from the Example on). The curvature `k = Im(z''/z')/|z'|` of a regular plane curve
`z = z(t)` at the point `z(t)`, with the sign taken for the direction of increasing `t` (positive when the curve turns
to the left). -/
def curvature (z : ℝ → ℂ) (t : ℝ) : ℝ :=
  (deriv (deriv z) t / deriv z t).im / ‖deriv z t‖

/-- **Definition** (§2, used from the Example on). The derivative `dk/ds` of the curvature with respect to arclength
`s`, taken in the direction of increasing `t` (`ds/dt = |z'(t)|`). -/
def curvatureDeriv (z : ℝ → ℂ) (t : ℝ) : ℝ :=
  deriv (curvature z) t / ‖deriv z t‖

/-- The logarithmic spiral `z(t) = e^{(-a+i)t}` of the Example of §2. -/
def logSpiral (a t : ℝ) : ℂ :=
  cexp ((-(a : ℂ) + I) * t)

/-- Helper for `eq5` (§2): the logarithmic spiral solves `z′ = (−a + i) z`. -/
theorem gs2_logSpiral_hasDerivAt (a s : ℝ) :
    HasDerivAt (logSpiral a) ((-(a : ℂ) + I) * logSpiral a s) s := by
  have h1 : HasDerivAt (fun y : ℂ => (-(a : ℂ) + I) * y) (-(a : ℂ) + I) (s : ℂ) := by
    simpa using (hasDerivAt_id (s : ℂ)).const_mul (-(a : ℂ) + I)
  exact (h1.cexp.comp_ofReal).congr_deriv (mul_comm _ _)

/-- Helper for `eq5` (§2): along the logarithmic spiral, `k = e^{at}/√(a² + 1)`, `|z| = e^{−at}` and
`|z′| = √(a² + 1) e^{−at}`. -/
theorem gs2_logSpiral_curv (a s : ℝ) :
    curvature (logSpiral a) s = Real.exp (a * s) / √(a ^ 2 + 1) ∧ ‖logSpiral a s‖ = Real.exp (-(a * s)) ∧
      ‖deriv (logSpiral a) s‖ = √(a ^ 2 + 1) * Real.exp (-(a * s)) := by
  have hd1 : deriv (logSpiral a) = fun s => (-(a : ℂ) + I) * logSpiral a s :=
    funext fun s => (gs2_logSpiral_hasDerivAt a s).deriv
  have hd1s : deriv (logSpiral a) s = (-(a : ℂ) + I) * logSpiral a s := (gs2_logSpiral_hasDerivAt a s).deriv
  have hd2 : deriv (deriv (logSpiral a)) s = (-(a : ℂ) + I) * ((-(a : ℂ) + I) * logSpiral a s) := by
    rw [hd1]
    exact ((gs2_logSpiral_hasDerivAt a s).const_mul (-(a : ℂ) + I)).deriv
  have hL : ‖logSpiral a s‖ = Real.exp (-(a * s)) := by
    show ‖cexp ((-(a : ℂ) + I) * s)‖ = _
    rw [Complex.norm_exp]
    congr 1
    simp
  have hw : ‖-(a : ℂ) + I‖ = √(a ^ 2 + 1) := by
    rw [show -(a : ℂ) + I = ((-a : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_add_mul_I]
    congr 1
    ring
  have hD : ‖deriv (logSpiral a) s‖ = √(a ^ 2 + 1) * Real.exp (-(a * s)) := by
    rw [hd1s, norm_mul, hw, hL]
  refine ⟨?_, hL, hD⟩
  have hLne : logSpiral a s ≠ 0 := Complex.exp_ne_zero _
  have hwne : (-(a : ℂ) + I) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have hsq : 0 < √(a ^ 2 + 1) := Real.sqrt_pos.2 (by positivity)
  show (deriv (deriv (logSpiral a)) s / deriv (logSpiral a) s).im / ‖deriv (logSpiral a) s‖ = _
  rw [hd2, hD, hd1s, mul_div_cancel_right₀ _ (mul_ne_zero hwne hLne), Real.exp_neg]
  have him : (-(a : ℂ) + I).im = 1 := by simp
  rw [him]
  field_simp

/-- **Example, formula (5)** (§2). For `a > 0` the analytic open arc `α : z = e^{(-a+i)t}`, `t ∈ (0, ∞)`, satisfies
`k(z) |z| = (a² + 1)^{-1/2}` and `(dk/ds)(z) |z|² = a (a² + 1)⁻¹` for all `z ∈ α`, where `k` is the curvature and `s`
the arclength of `α` taken in the direction from `1` to `0`.
Modelling: `z ∈ α` is `z = z(t)`, `t > 0`; the direction from `1` to `0` is that of increasing `t`. -/
theorem eq5 {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : 0 < t) :
    curvature (logSpiral a) t * ‖logSpiral a t‖ = (a ^ 2 + 1) ^ (-(1 / 2 : ℝ)) ∧
      curvatureDeriv (logSpiral a) t * ‖logSpiral a t‖ ^ 2 = a * (a ^ 2 + 1)⁻¹ := by
  have _ha := ha  -- not needed: (5) holds for every real `a`
  have _ht := ht  -- not needed: (5) holds at every parameter `t`
  obtain ⟨hk, hL, hD⟩ := gs2_logSpiral_curv a t
  have hsq : 0 < √(a ^ 2 + 1) := Real.sqrt_pos.2 (by positivity)
  have hE : 0 < Real.exp (a * t) := Real.exp_pos _
  constructor
  · rw [hk, hL, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.exp_neg]
    field_simp
  · have hk' : curvature (logSpiral a) = fun s => Real.exp (a * s) / √(a ^ 2 + 1) :=
      funext fun s => (gs2_logSpiral_curv a s).1
    have hderk : deriv (curvature (logSpiral a)) t = a * Real.exp (a * t) / √(a ^ 2 + 1) := by
      rw [hk']
      refine ((((hasDerivAt_id t).const_mul a).exp).div_const (√(a ^ 2 + 1))).deriv.trans ?_
      show Real.exp (a * t) * (a * 1) / √(a ^ 2 + 1) = a * Real.exp (a * t) / √(a ^ 2 + 1)
      ring
    show deriv (curvature (logSpiral a)) t / ‖deriv (logSpiral a) t‖ * ‖logSpiral a t‖ ^ 2 = _
    rw [hderk, hD, hL, Real.exp_neg]
    have hs2 : √(a ^ 2 + 1) ^ 2 = a ^ 2 + 1 := Real.sq_sqrt (by positivity)
    field_simp
    rw [hs2]

/-- Helper for `prop1` and `prop2` (§2): the distance of a point of the curve (2) to `z₂`. -/
theorem gs2_norm_spiral (z₁ z₂ : ℂ) (r : ℝ → ℝ) (t : ℝ) :
    ‖spiralCurve z₁ z₂ r t - z₂‖ = ‖z₁ - z₂‖ * |r t| := by
  show ‖(z₁ - z₂) * (r t : ℂ) * cexp ((t : ℂ) * I) + z₂ - z₂‖ = _
  rw [add_sub_cancel_right, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

/-- Helper for `prop1` (§2): after a full turn the curve (2) points in the same direction, so equal radii give equal
points. -/
theorem gs2_spiral_turn (z₁ z₂ : ℂ) (r : ℝ → ℝ) (t : ℝ) (h : r (t + 2 * π) = r t) :
    spiralCurve z₁ z₂ r (t + 2 * π) = spiralCurve z₁ z₂ r t := by
  show (z₁ - z₂) * (r (t + 2 * π) : ℂ) * cexp (((t + 2 * π : ℝ) : ℂ) * I) + z₂ =
    (z₁ - z₂) * (r t : ℂ) * cexp ((t : ℂ) * I) + z₂
  rw [h, Complex.ofReal_add, add_mul, Complex.exp_add,
    show ((2 * π : ℝ) : ℂ) * I = 2 * π * I by push_cast; ring, Complex.exp_two_pi_mul_I, mul_one]

/-- **Proposition 1** (§2). If `α` is a spiral from `z₁` onto `z₂` with the representation (2), then (6)
`|z(t + 2π) - z₂| < |z(t) - z₂|` for `t ∈ (0, ∞)`. -/
theorem prop1 {α : Set ℂ} {z₁ z₂ : ℂ} {r : ℝ → ℝ} (hα : IsOpenArc α) (hr : IsSpiralRep α z₁ z₂ r) {t : ℝ}
    (ht : 0 < t) :
    ‖spiralCurve z₁ z₂ r (t + 2 * π) - z₂‖ < ‖spiralCurve z₁ z₂ r t - z₂‖ := by
  have _hα := hα  -- not needed: the representation `hr` alone gives (6)
  obtain ⟨hrc, hrpos, -, hr0, hinj, -⟩ := hr
  have hπ := Real.pi_pos
  -- `z₁ ≠ z₂`: otherwise the curve is constant
  have hz : z₁ ≠ z₂ := by
    intro h
    have h1 : spiralCurve z₁ z₂ r 1 = spiralCurve z₁ z₂ r 2 := by
      show (z₁ - z₂) * ((r 1 : ℝ) : ℂ) * cexp (((1 : ℝ) : ℂ) * I) + z₂ =
        (z₁ - z₂) * ((r 2 : ℝ) : ℂ) * cexp (((2 : ℝ) : ℂ) * I) + z₂
      rw [h, sub_self, zero_mul, zero_mul, zero_mul, zero_mul]
    have := hinj (show (1 : ℝ) ∈ Ioi 0 by norm_num) (show (2 : ℝ) ∈ Ioi 0 by norm_num) h1
    norm_num at this
  have hz' : 0 < ‖z₁ - z₂‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  have hshift : ∀ s ∈ Ioi (0 : ℝ), s + 2 * π ∈ Ioi (0 : ℝ) := fun s hs => by
    rw [mem_Ioi] at hs ⊢
    linarith
  -- `r(s + 2π) − r(s)` never vanishes (injectivity on a ray)
  have hne : ∀ s ∈ Ioi (0 : ℝ), r (s + 2 * π) - r s ≠ 0 := by
    intro s hs h
    have := hinj (hshift s hs) hs (gs2_spiral_turn z₁ z₂ r s (by linarith))
    linarith
  have hgc : ContinuousOn (fun s => r (s + 2 * π) - r s) (Ioi 0) :=
    (hrc.comp (continuousOn_id.add continuousOn_const) hshift).sub hrc
  rw [gs2_norm_spiral, gs2_norm_spiral, abs_of_pos (hrpos _ (hshift t ht)), abs_of_pos (hrpos t ht)]
  by_contra hcon
  have hle := le_of_mul_le_mul_left (not_lt.1 hcon) hz'
  have hgt : 0 < r (t + 2 * π) - r t := lt_of_le_of_ne (by linarith) (Ne.symm (hne t ht))
  -- then `r(s + 2π) > r(s)` for every `s > 0` (intermediate values)
  have hall : ∀ s ∈ Ioi (0 : ℝ), 0 < r (s + 2 * π) - r s := by
    intro s hs
    by_contra hs'
    have hs'' : r (s + 2 * π) - r s < 0 := lt_of_le_of_ne (not_lt.1 hs') (hne s hs)
    have hsub : uIcc s t ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le (lt_inf_iff.2 ⟨hs, ht⟩) hx.1
    obtain ⟨c, hc, hc0⟩ := intermediate_value_uIcc (hgc.mono hsub)
      (Set.mem_uIcc.2 (Or.inl ⟨hs''.le, hgt.le⟩))
    exact hne c (hsub hc) hc0
  -- `r(2π(n + 1)) ≥ r(2π)`, against `r(t) → 0`
  have hiter : ∀ n : ℕ, r (2 * π) ≤ r (2 * π * (n + 1)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := hall (2 * π * (n + 1)) (by rw [mem_Ioi]; positivity)
      rw [show 2 * π * ((n + 1 : ℕ) + 1 : ℝ) = 2 * π * (n + 1) + 2 * π by push_cast; ring]
      linarith
  have h2π := hrpos (2 * π) (by rw [mem_Ioi]; positivity)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hr0.eventually (gt_mem_nhds h2π))
  obtain ⟨n, hn⟩ := exists_nat_ge N
  have h1 : N ≤ 2 * π * (n + 1) := by nlinarith [Real.pi_gt_three]
  linarith [hN _ h1, hiter n]

/-- Helper for `prop2` (§2): a similarity `f(z) = αz + β` carries the curve (2) for `z₁, z₂` to the curve (2) for
`f(z₁), f(z₂)`, with the same `r`. -/
theorem gs2_spiral_sim {f : ℂ → ℂ} {α β : ℂ} (hf : ∀ z, f z = α * z + β) (z₁ z₂ : ℂ) (r : ℝ → ℝ) (t : ℝ) :
    spiralCurve (f z₁) (f z₂) r t = f (spiralCurve z₁ z₂ r t) := by
  show (f z₁ - f z₂) * (r t : ℂ) * cexp ((t : ℂ) * I) + f z₂ =
    f ((z₁ - z₂) * (r t : ℂ) * cexp ((t : ℂ) * I) + z₂)
  simp only [hf]
  ring

/-- **Proposition 2** (§2). If `α` is a `b`-spiral from `z₁` onto `z₂` and `f` is a conformal similarity mapping, then
`f(α)` is a `b`-spiral from `f(z₁)` onto `f(z₂)`.
Modelling: a conformal similarity is `z ↦ az + c`, `a ≠ 0` (`LiZhongQC.IsSimilarity`). -/
theorem prop2 {α : Set ℂ} {z₁ z₂ : ℂ} {b : ℝ} (hα : IsBSpiral α z₁ z₂ b) {f : ℂ → ℂ} (hf : IsSimilarity f) :
    IsBSpiral (f '' α) (f z₁) (f z₂) b := by
  obtain ⟨c, d, hc0, hf'⟩ := hf
  obtain ⟨hb, ⟨z, hzemb, hzimg⟩, r, ⟨hrc, hrpos, hr1, hr0, hinj, himg⟩, hbound⟩ := hα
  have hfe : IsEmbedding f := by
    have h : f = (Homeomorph.addRight d) ∘ (Homeomorph.mulLeft₀ c hc0) := funext fun w => hf' w
    rw [h]
    exact (Homeomorph.addRight d).isEmbedding.comp (Homeomorph.mulLeft₀ c hc0).isEmbedding
  have hd : ∀ x, f x - f z₂ = c * (x - z₂) := fun x => by
    rw [hf', hf']
    ring
  refine ⟨hb, ⟨f ∘ z, hfe.comp hzemb, by rw [image_comp, hzimg]⟩, r, ⟨hrc, hrpos, hr1, hr0, ?_, ?_⟩, ?_⟩
  · intro s hs u hu h
    rw [gs2_spiral_sim hf', gs2_spiral_sim hf'] at h
    exact hinj hs hu (hfe.injective h)
  · rw [← himg, image_image]
    exact image_congr fun s _ => gs2_spiral_sim hf' z₁ z₂ r s
  · intro t₁ ht₁ t₂ ht₂ h
    rw [gs2_spiral_sim hf', gs2_spiral_sim hf', hd, hd, norm_mul, norm_mul]
    have := mul_le_mul_of_nonneg_left (hbound t₁ ht₁ t₂ ht₂ h) (norm_nonneg c)
    linarith

/-- **Lemma 1** (§2). Suppose that `α` is a `b`-spiral from `z₁` onto `z₂`, that `β` is a `b`-spiral from `w₁` onto
`w₂` and that `α ∩ β = ∅`. If `b ∈ (1, 2)`, then either `z₂ = w₂` or
`|z₂ - w₂| > b⁻¹ min(|z₁ - z₂|, |w₁ - w₂|)`. -/
theorem lemma1 {α β : Set ℂ} {z₁ z₂ w₁ w₂ : ℂ} {b : ℝ} (hα : IsBSpiral α z₁ z₂ b) (hβ : IsBSpiral β w₁ w₂ b)
    (hαβ : α ∩ β = ∅) (hb : b ∈ Ioo (1 : ℝ) 2) :
    z₂ = w₂ ∨ 1 / b * min ‖z₁ - z₂‖ ‖w₁ - w₂‖ < ‖z₂ - w₂‖ := by
  sorry

/-- **Definition** (§2, used in Lemmas 2–5). `z` is a regular analytic parametrization of an analytic open arc from
`p` to `q`: `z` is real-analytic on `(0, ∞)` with `z'(t) ≠ 0`, an embedding of `(0, ∞)`, `z(t) → p` as `t → 0` and
`z(t) → q` as `t → ∞`. The arc is `z((0, ∞))`; the direction from `p` to `q` is that of increasing `t`. -/
def IsAnalyticArcParam (z : ℝ → ℂ) (p q : ℂ) : Prop :=
  AnalyticOnNhd ℝ z (Ioi 0) ∧ (∀ t ∈ Ioi (0 : ℝ), deriv z t ≠ 0) ∧ IsEmbedding ((Ioi (0 : ℝ)).domRestrict z) ∧
    Tendsto z (𝓝[>] 0) (𝓝 p) ∧ Tendsto z atTop (𝓝 q)

/-- **Definition** (§2, used in Lemmas 2 and 3). A rectifiable open arc: an open arc of finite length, i.e. with an
embedding parametrization of bounded variation. The total variation of such a parametrization is Gehring's length
`l(α) = sup l(β)` over the closed subarcs `β ⊆ α` (proof of Lemma 2). -/
def IsRectifiableArc (α : Set ℂ) : Prop :=
  ∃ z : ℝ → ℂ, IsEmbedding ((Ioi (0 : ℝ)).domRestrict z) ∧ z '' Ioi 0 = α ∧ BoundedVariationOn z (Ioi 0)

/-- **Lemma 2** (§2). Suppose that `c, d ∈ (0, ∞)`, that `α` is an analytic open arc with `1` and `0` as endpoints,
and that `k(z) |z| ≥ c` and `(dk/ds)(z) |z|² ≥ d` for `z ∈ α`, where `s` is taken in the direction from `1` to `0`.
Then `α` is a rectifiable spiral from `1` onto `0`.
Modelling: `α = z((0, ∞))` for a regular analytic parametrization `z` from `1` to `0` (`IsAnalyticArcParam z 1 0`). -/
theorem lemma2 {c d : ℝ} (hc : 0 < c) (hd : 0 < d) {z : ℝ → ℂ} (hz : IsAnalyticArcParam z 1 0)
    (hk : ∀ t ∈ Ioi (0 : ℝ), c ≤ curvature z t * ‖z t‖)
    (hks : ∀ t ∈ Ioi (0 : ℝ), d ≤ curvatureDeriv z t * ‖z t‖ ^ 2) :
    IsRectifiableArc (z '' Ioi 0) ∧ IsSpiral (z '' Ioi 0) 1 0 := by
  sorry

/-- **Lemma 3** (§2). Suppose that `c₁, c₂, d₁, d₂ ∈ (0, ∞)` and `4π d₂ < c₁²`, that `α` is an analytic open arc with
`1` and `0` as endpoints, and that `c₁ ≤ k(z) |z| ≤ c₂` and `d₁ ≤ (dk/ds)(z) |z|² ≤ d₂` for `z ∈ α`, where `s` is taken
in the direction from `1` to `0`. Then `α` is a rectifiable `b`-spiral from `1` onto `0`, where
`b = c₁ c₂ / (c₁² - 4π d₂) > 1`.
Modelling: as in `lemma2`; `b > 1` is part of `IsBSpiral`. -/
theorem lemma3 {c₁ c₂ d₁ d₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hcd : 4 * π * d₂ < c₁ ^ 2) {z : ℝ → ℂ} (hz : IsAnalyticArcParam z 1 0)
    (hk : ∀ t ∈ Ioi (0 : ℝ), c₁ ≤ curvature z t * ‖z t‖ ∧ curvature z t * ‖z t‖ ≤ c₂)
    (hks : ∀ t ∈ Ioi (0 : ℝ), d₁ ≤ curvatureDeriv z t * ‖z t‖ ^ 2 ∧ curvatureDeriv z t * ‖z t‖ ^ 2 ≤ d₂) :
    IsRectifiableArc (z '' Ioi 0) ∧ IsBSpiral (z '' Ioi 0) 1 0 (c₁ * c₂ / (c₁ ^ 2 - 4 * π * d₂)) := by
  sorry

/-- **Lemma 4** (§2). Suppose that `α` is an analytic arc with the representation `z = z(t)` where `z'(t) ≠ 0`, and
suppose that `f` maps a neighborhood of `α` conformally into `ℂ`. Then `α* = f(α)` is an analytic arc with the
representation `w = f ∘ z(t)` and
`k*(f(z)) |f'(z)| - k(z) = Im((f''(z)/f'(z)) z'(t)/|z'(t)|)`,
`(dk*/ds*)(f(z)) |f'(z)|² - (dk/ds)(z) = Im(S_f(z) z'(t)²/|z'(t)|²)`,
where `k, k*` denote the curvatures and `s, s*` the arclengths of `α, α*` in the direction of increasing `t`.
Modelling: the parameter runs over an open interval `I`; "arc" is an embedding of `I`; the neighbourhood is an open
`U ⊇ α` on which `f` is holomorphic and injective. -/
theorem lemma4 {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I) {z : ℝ → ℂ} (hza : AnalyticOnNhd ℝ z I)
    (hz' : ∀ t ∈ I, deriv z t ≠ 0) (hze : IsEmbedding (I.domRestrict z)) {U : Set ℂ} (hU : IsOpen U)
    (hzU : z '' I ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hfi : InjOn f U) :
    (AnalyticOnNhd ℝ (f ∘ z) I ∧ (∀ t ∈ I, deriv (f ∘ z) t ≠ 0) ∧ IsEmbedding (I.domRestrict (f ∘ z))) ∧
      ∀ t ∈ I,
        curvature (f ∘ z) t * ‖deriv f (z t)‖ - curvature z t =
            (deriv (deriv f) (z t) / deriv f (z t) * (deriv z t / (‖deriv z t‖ : ℂ))).im ∧
          curvatureDeriv (f ∘ z) t * ‖deriv f (z t)‖ ^ 2 - curvatureDeriv z t =
            (schwarzian f (z t) * (deriv z t ^ 2 / (‖deriv z t‖ : ℂ) ^ 2)).im := by
  sorry

/-- **Lemma 5** (§2). Suppose that `b, c₁, c₂, d₁, d₂` and `α` are as in Lemma 3 and that `b* ∈ (b, ∞)`. Then there
exists `ε > 0`, depending only on `b*, c₁, c₂, d₁, d₂`, with the following property. If `f` maps a neighborhood of `α`
conformally into `ℂ`, if `f(z) → 1` and `0` as `z → 1` and `0` on `α`, and if (18)
`|z f'(z)/f(z) - 1| ≤ ε`, `|z² f''(z)/f(z)| ≤ ε`, `|z³ f'''(z)/f(z)| ≤ ε` for `z ∈ α`, then `α* = f(α)` is a
`b*`-spiral from `1` onto `0`.
Modelling: `ε` is chosen before the arc and the map (it depends only on `b*, c₁, c₂, d₁, d₂`); the arc is given by a
regular analytic parametrization as in `lemma3`; the neighbourhood is an open `U ⊇ α`. The quotients in (18) are
genuine: `f ∘ z` is an embedding of `(0, ∞)` (`f` is a homeomorphism of `U` onto `f(U)`) tending to `0` at `∞`, so it
does not take the value `0`. -/
theorem lemma5 {c₁ c₂ d₁ d₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hcd : 4 * π * d₂ < c₁ ^ 2) {b' : ℝ} (hb' : c₁ * c₂ / (c₁ ^ 2 - 4 * π * d₂) < b') :
    ∃ ε > (0 : ℝ), ∀ z : ℝ → ℂ, IsAnalyticArcParam z 1 0 →
      (∀ t ∈ Ioi (0 : ℝ), c₁ ≤ curvature z t * ‖z t‖ ∧ curvature z t * ‖z t‖ ≤ c₂) →
      (∀ t ∈ Ioi (0 : ℝ), d₁ ≤ curvatureDeriv z t * ‖z t‖ ^ 2 ∧ curvatureDeriv z t * ‖z t‖ ^ 2 ≤ d₂) →
      ∀ (U : Set ℂ) (f : ℂ → ℂ), IsOpen U → z '' Ioi 0 ⊆ U → DifferentiableOn ℂ f U → InjOn f U →
        Tendsto (f ∘ z) (𝓝[>] 0) (𝓝 1) → Tendsto (f ∘ z) atTop (𝓝 0) →
        (∀ t ∈ Ioi (0 : ℝ), ‖z t * deriv f (z t) / f (z t) - 1‖ ≤ ε ∧
          ‖z t ^ 2 * deriv (deriv f) (z t) / f (z t)‖ ≤ ε ∧
          ‖z t ^ 3 * deriv (deriv (deriv f)) (z t) / f (z t)‖ ≤ ε) →
        IsBSpiral (f '' (z '' Ioi 0)) 1 0 b' := by
  sorry

end Gehring1978
