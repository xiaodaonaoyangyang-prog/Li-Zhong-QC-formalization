import References.Pommerenke1992.Ch05.S02_JohnDomains

/-!
# Pommerenke 1992, Ch. 5 §5.3 Linearly Connected Domains

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §5.3; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 4400–4552.

* Definition (linearly connected domain, (5.3.1); cited at l. 4597) — `IsLinearlyConnectedWith`,
  `IsLinearlyConnected`
* Proposition 5.6 — `prop5_6`
* Theorem 5.7 — `thm5_7`
* Remark (the linearly invariant families (5.3.12), (5.3.13) and their order; cited at l. 7910) —
  `IsLinearlyInvariant`, `linearlyInvariantOrder`
* Unlabelled (§5.3, l. 4511: the family `S` is linearly invariant of order 2; used at l. 6890, "`β = 2` in the
  general case") — `classS_linearlyInvariant`
* Unlabelled (§5.3, l. 4513: (5.3.3) holds for every linearly invariant family of finite order; cited at l. 6890,
  "the remark following its proof") — `linearlyInvariant_eq5_3_3`
* Definition (`α`-close-to-convex function, (5.3.14)) — `IsAlphaCloseToConvex`
* Proposition 5.8 — `prop5_8`

Not items (DESIGN §3): the characterization for piecewise smooth curves (l. 4408, not cited); the consequences of
Proposition 5.6 at l. 4418 (finite values assumed once; `∞` finitely often, Pom64; bounded linearly connected domains
are Jordan domains; not cited); (5.3.5) and its equivalent (5.3.6) for the inverse function (not cited); the family
`𝔐` of the proof, (5.3.7)–(5.3.11) (proof steps).

**Conventions.** As in §5.2. A curve in `G` from `w₁` to `w₂` is a path (`Path w₁ w₂`) with range in `G`. Non-euclidean
segments between points of `𝔻̄` are written `τ((x₁, x₂))` for a conformal self-map `τ(z) = c(z - a)/(1 - āz)` of `𝔻`
and `-1 ≤ x₁ < x₂ ≤ 1`, as in Theorem 4.20. The continuous extension `F` of `f` takes values in `Ĉ` (Proposition 5.6).
A conformal self-map of `𝔻` in (5.3.13) is `τ(z) = c(z - a)/(1 - āz)`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsConformalOnto IsJordanCurve knHyp)
open LehtoVirtanen1973 (IsSimplyConnectedDomain)

/-- **Definition (5.3.1)** (§5.3; cited at l. 4597). The simply connected domain `G ⊆ ℂ` is linearly connected with
constant `M₁`: any two points `w₁, w₂ ∈ G` can be connected by a curve `A ⊆ G` with `diam A ≤ M₁ |w₁ - w₂|`. -/
def IsLinearlyConnectedWith (G : Set ℂ) (M₁ : ℝ) : Prop :=
  IsOpen G ∧ IsConnected G ∧ IsSimplyConnectedDomain (toExt G) ∧
    ∀ w₁ ∈ G, ∀ w₂ ∈ G, ∃ γ : Path w₁ w₂, range γ ⊆ G ∧
      Metric.ediam (range γ) ≤ ENNReal.ofReal (M₁ * ‖w₁ - w₂‖)

/-- **Definition** (§5.3). `G` is linearly connected: `IsLinearlyConnectedWith G M₁` for some `M₁`. -/
def IsLinearlyConnected (G : Set ℂ) : Prop :=
  ∃ M₁ : ℝ, IsLinearlyConnectedWith G M₁

/-- **Proposition 5.6** (§5.3). Let `f` map `𝔻` conformally onto a linearly connected domain `G`. Then `f` is continuous
in `𝔻̄` with values in `Ĉ` and (5.3.2) `diam f(S) ≤ M₂ |f(z₁) - f(z₂)|` for `z₁, z₂ ∈ 𝔻̄`, where `S` is the
non-euclidean segment from `z₁` to `z₂`.
Modelling: `S = τ((x₁, x₂))` (see the file header); (5.3.2) is stated when `f(z₁), f(z₂)` are finite (otherwise the
right-hand side is `∞`); `M₂` depends on `f`. -/
theorem prop5_6 {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc (f '' unitDisc))
    (hG : IsLinearlyConnected (f '' unitDisc)) :
    ∃ F : ℂ → ExtPlane, ContinuousOn F (closedBall 0 1) ∧ (∀ z ∈ unitDisc, F z = f z) ∧
      ∃ M₂ : ℝ, ∀ (c a : ℂ) (x₁ x₂ : ℝ), ‖c‖ = 1 → ‖a‖ < 1 → -1 ≤ x₁ → x₁ < x₂ → x₂ ≤ 1 →
        ∀ w₁ w₂ : ℂ, F (c * (x₁ - a) / (1 - conj a * x₁)) = w₁ → F (c * (x₂ - a) / (1 - conj a * x₂)) = w₂ →
          Metric.ediam (f '' ((fun x : ℝ => c * (x - a) / (1 - conj a * x)) '' Ioo x₁ x₂)) ≤
            ENNReal.ofReal (M₂ * ‖w₁ - w₂‖) := by
  sorry

/-- **Theorem 5.7** (§5.3). Let `f` map `𝔻` conformally onto a linearly connected domain. Then there exists `β < 2`
such that (5.3.3) `|f'(ρζ)| ≥ (1/8)|f'(rζ)|((1 - ρ)/(1 - r))^{β-1}` for `ζ ∈ 𝕋`, `0 ≤ r ≤ ρ < 1`, and (5.3.4)
`|f(ζ₁) - f(ζ₂)| ≥ M₃⁻¹ d_f(z)(|ζ₁ - ζ₂|/(1 - |z|))^β` for `ζ₁, ζ₂ ∈ I(z)`, `z ∈ 𝔻`.
Modelling: `f` on `𝕋` is its continuous extension `F` (Proposition 5.6); (5.3.4) is stated when `F(ζ₁), F(ζ₂)` are
finite; the OCR splits the display numbers "(3)" and (4). -/
theorem thm5_7 {f : ℂ → ℂ} {F : ℂ → ExtPlane} (hf : IsConformalOnto f unitDisc (f '' unitDisc))
    (hG : IsLinearlyConnected (f '' unitDisc)) (hFc : ContinuousOn F (closedBall 0 1))
    (hFf : ∀ z ∈ unitDisc, F z = f z) :
    ∃ β : ℝ, β < 2 ∧
      (∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r ρ : ℝ, 0 ≤ r → r ≤ ρ → ρ < 1 →
        1 / 8 * ‖deriv f (r * ζ)‖ * ((1 - ρ) / (1 - r)) ^ (β - 1) ≤ ‖deriv f (ρ * ζ)‖) ∧
      ∃ M₃ : ℝ, 0 < M₃ ∧ ∀ z ∈ unitDisc, ∀ ζ₁ ∈ arcI z, ∀ ζ₂ ∈ arcI z, ∀ w₁ w₂ : ℂ, F ζ₁ = w₁ → F ζ₂ = w₂ →
        M₃⁻¹ * distToBoundary f z * (‖ζ₁ - ζ₂‖ / (1 - ‖z‖)) ^ β ≤ ‖w₁ - w₂‖ := by
  sorry

/-- **Definition** (§5.3, Remark, (5.3.12), (5.3.13); cited at l. 7910). A family `𝔉` of analytic functions
`f(z) = z + a₂z² + ⋯` with `f'(z) ≠ 0` (`z ∈ 𝔻`) is linearly invariant: `f ∈ 𝔉`, `τ ∈ Möb(𝔻)` imply
`(f ∘ τ - f(τ(0)))/(τ'(0) f'(τ(0))) ∈ 𝔉`.
Modelling: membership up to equality on `𝔻`; `τ(z) = c(z - a)/(1 - āz)`, `τ'(0) = c(1 - |a|²)`. -/
def IsLinearlyInvariant (𝔉 : Set (ℂ → ℂ)) : Prop :=
  (∀ f ∈ 𝔉, DifferentiableOn ℂ f unitDisc ∧ f 0 = 0 ∧ deriv f 0 = 1 ∧ ∀ z ∈ unitDisc, deriv f z ≠ 0) ∧
    ∀ f ∈ 𝔉, ∀ c a : ℂ, ‖c‖ = 1 → ‖a‖ < 1 → ∃ g ∈ 𝔉, EqOn g
      (fun z => (f (c * (z - a) / (1 - conj a * z)) - f (-(c * a))) / (c * (1 - ‖a‖ ^ 2) * deriv f (-(c * a))))
      unitDisc

/-- **Definition** (§5.3, Remark). The order of the family `𝔉`: `sup {|a₂| : f ∈ 𝔉}`. -/
def linearlyInvariantOrder (𝔉 : Set (ℂ → ℂ)) : ℝ≥0∞ :=
  ⨆ f ∈ 𝔉, ENNReal.ofReal ‖sCoeff f 2‖

/-- Helper for `classS_linearlyInvariant` (§5.3). The Koebe function `k(z) = z/(1 − z)²` belongs to `S` and
`k''(0) = 4`, i.e. `a₂ = 2`. -/
theorem p53_koebe : knHyp LiZhongQC.koebeFn ∧ deriv (deriv LiZhongQC.koebeFn) 0 = 4 := by
  have hk : LiZhongQC.koebeFn = fun z : ℂ => z / (1 - z) ^ 2 := rfl
  have hne : ∀ z ∈ ball (0 : ℂ) 1, (1 - z) ^ 2 ≠ 0 := fun z hz =>
    pow_ne_zero 2 (LiZhongQC.kb_ka_one_sub_ne_zero (mem_ball_zero_iff.1 hz))
  -- `k'(z) = (1 + z)/(1 − z)³`
  have hd : ∀ z : ℂ, z ≠ 1 → HasDerivAt LiZhongQC.koebeFn ((1 + z) / (1 - z) ^ 3) z := fun z hz => by
    have h1 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
    rw [hk]
    have h := (hasDerivAt_id' z).fun_div (((hasDerivAt_id' z).const_sub 1).fun_pow 2) (pow_ne_zero 2 h1)
    convert h using 1
    field_simp
    ring
  have h01 : (0 : ℂ) ≠ 1 := zero_ne_one
  have hderiv0 : deriv LiZhongQC.koebeFn 0 = 1 := by
    rw [(hd 0 h01).deriv]
    norm_num
  refine ⟨⟨fun z hz => (hd z fun e => by rw [e, mem_ball_zero_iff, norm_one] at hz; exact lt_irrefl 1 hz)
      |>.differentiableAt.differentiableWithinAt, LiZhongQC.koebeFn_injOn, by simp [hk], hderiv0⟩, ?_⟩
  -- `k''(0) = 4`
  have hev : deriv LiZhongQC.koebeFn =ᶠ[𝓝 0] fun z => (1 + z) / (1 - z) ^ 3 := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (one_pos : (0 : ℝ) < 1))] with z hz
    exact (hd z fun e => by rw [e, mem_ball_zero_iff, norm_one] at hz; exact lt_irrefl 1 hz).deriv
  rw [hev.deriv_eq]
  have h3 := ((hasDerivAt_id' (0 : ℂ)).const_add 1).fun_div (((hasDerivAt_id' (0 : ℂ)).const_sub 1).fun_pow 3)
    (by norm_num)
  rw [h3.deriv]
  norm_num

/-- **Unlabelled claim** (§5.3, Remark, l. 4511; used at l. 6890, "`β = 2` in the general case"). The family `S` is
linearly invariant of order 2. -/
theorem classS_linearlyInvariant :
    IsLinearlyInvariant {f | knHyp f} ∧ linearlyInvariantOrder {f | knHyp f} = 2 := by
  refine ⟨⟨fun f hf => ⟨hf.diff, hf.zero, hf.one, fun z hz =>
    LiZhongQC.deriv_ne_zero_of_injOn isOpen_ball hf.diff hf.inj hz⟩, fun f hf c a hc ha => ?_⟩, ?_⟩
  · -- the Koebe transform of the rotation `c̄ f(c w)` at `-a`
    obtain ⟨hfd, hfi, hf0, hf1⟩ := hf
    have hcc : conj c * c = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
      norm_num
    have hc0 : c ≠ 0 := fun e => by rw [e, norm_zero] at hc; exact zero_ne_one hc
    have hrotD : ∀ w ∈ unitDisc, c * w ∈ unitDisc := fun w hw => by
      show c * w ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff, norm_mul, hc, one_mul]
      exact mem_ball_zero_iff.1 hw
    set fc : ℂ → ℂ := fun w => conj c * f (c * w) with hfc
    have hfcd : DifferentiableOn ℂ fc unitDisc := fun w hw =>
      ((hfd.differentiableAt (isOpen_ball.mem_nhds (hrotD w hw))).comp w
        ((differentiableAt_id).const_mul c)).const_mul (conj c) |>.differentiableWithinAt
    have hfci : InjOn fc unitDisc := fun w hw w' hw' e => by
      have e' : f (c * w) = f (c * w') := by
        have := congrArg (fun t => c * t) e
        simp only [hfc] at this
        rwa [← mul_assoc, ← mul_assoc, mul_comm c (conj c), hcc, one_mul, one_mul] at this
      exact mul_left_cancel₀ hc0 (hfi (hrotD w hw) (hrotD w' hw') e')
    have ha' : -a ∈ unitDisc := by
      show -a ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff, norm_neg]
      exact ha
    obtain ⟨hk, -, -⟩ := p92_1_koebeT hfcd hfci ha'
    refine ⟨koebeTransform fc (-a), hk, fun ζ hζ => ?_⟩
    -- `fc'(−a) = f'(−ca)`
    have hca : c * -a ∈ unitDisc := hrotD _ ha'
    have hder : deriv fc (-a) = deriv f (-(c * a)) := by
      have h0 := (hfd.differentiableAt (isOpen_ball.mem_nhds hca)).hasDerivAt.comp (-a)
        ((hasDerivAt_id' (-a)).const_mul c)
      have h : HasDerivAt fc (conj c * (deriv f (c * -a) * (c * 1))) (-a) := h0.const_mul (conj c)
      rw [h.deriv, mul_neg]
      linear_combination deriv f (-(c * a)) * hcc
    show (fc ((ζ + -a) / (1 + conj (-a) * ζ)) - fc (-a)) / (((1 - ‖-a‖ ^ 2 : ℝ) : ℂ) * deriv fc (-a)) =
      (f (c * (ζ - a) / (1 - conj a * ζ)) - f (-(c * a))) / (c * (1 - ‖a‖ ^ 2) * deriv f (-(c * a)))
    rw [hder, norm_neg]
    simp only [hfc, map_neg, neg_mul, ← sub_eq_add_neg, mul_neg]
    have hd0 : deriv f (-(c * a)) ≠ 0 :=
      LiZhongQC.deriv_ne_zero_of_injOn isOpen_ball hfd hfi (by rw [← mul_neg]; exact hca)
    have hs0 : (1 : ℂ) - ‖a‖ ^ 2 ≠ 0 := by
      have : (1 : ℝ) - ‖a‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg a]
      exact_mod_cast this
    rw [show c * (ζ - a) / (1 - conj a * ζ) = c * ((ζ - a) / (1 - conj a * ζ)) by ring]
    push_cast
    field_simp
    rw [hcc, one_mul]
  · -- the order is `sup |a₂| = 2`: Bieberbach, with equality for the Koebe function
    have hsc : ∀ f : ℂ → ℂ, sCoeff f 2 = deriv (deriv f) 0 / 2 := fun f => by
      show iteratedDeriv 2 f 0 / ((Nat.factorial 2 : ℕ) : ℂ) = _
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      norm_num
    apply le_antisymm
    · refine iSup₂_le fun f hf => ?_
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
      apply ENNReal.ofReal_le_ofReal
      rw [hsc, norm_div, Complex.norm_ofNat]
      have := LiZhongQC.koebe_bieberbach hf.diff hf.inj hf.zero hf.one
      linarith
    · obtain ⟨hk, hk2⟩ := p53_koebe
      refine le_iSup₂_of_le LiZhongQC.koebeFn hk ?_
      rw [hsc, hk2]
      norm_num

/-- **Unlabelled claim** (§5.3, Remark after the proof of Theorem 5.7, l. 4513; cited at l. 6890). For any linearly
invariant family `𝔉` of order `β < ∞`, (5.3.3) holds with a different constant:
`|f'(ρζ)| ≥ M⁻¹ |f'(rζ)|((1 - ρ)/(1 - r))^{β-1}` for `f ∈ 𝔉`, `ζ ∈ 𝕋`, `0 ≤ r ≤ ρ < 1`.
Modelling: `M` depends only on the order `β` (the proof gives `M = 2^{1+β}`). -/
theorem linearlyInvariant_eq5_3_3 (β : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ 𝔉 : Set (ℂ → ℂ), IsLinearlyInvariant 𝔉 → linearlyInvariantOrder 𝔉 = ENNReal.ofReal β →
      ∀ f ∈ 𝔉, ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ r ρ : ℝ, 0 ≤ r → r ≤ ρ → ρ < 1 →
        M⁻¹ * ‖deriv f (r * ζ)‖ * ((1 - ρ) / (1 - r)) ^ (β - 1) ≤ ‖deriv f (ρ * ζ)‖ := by
  sorry

/-- **Definition (5.3.14)** (§5.3). Let `0 ≤ α ≤ 1`. The function `f` is `α`-close-to-convex: analytic and univalent in
`𝔻` with (5.3.14) `|arg[f'(z)/h'(z)]| ≤ απ/2` (`z ∈ 𝔻`) for some convex univalent function `h`. -/
def IsAlphaCloseToConvex (f : ℂ → ℂ) (α : ℝ) : Prop :=
  0 ≤ α ∧ α ≤ 1 ∧ DifferentiableOn ℂ f unitDisc ∧ InjOn f unitDisc ∧
    ∃ h : ℂ → ℂ, IsConvexFunction h ∧ ∀ z ∈ unitDisc, |arg (deriv f z / deriv h z)| ≤ α * π / 2

/-- **Proposition 5.8** (§5.3). Let `0 ≤ α < 1`. If `f` is `α`-close-to-convex, then `f(𝔻)` is linearly connected. -/
theorem prop5_8 {f : ℂ → ℂ} {α : ℝ} (hα : α < 1) (hf : IsAlphaCloseToConvex f α) :
    IsLinearlyConnected (f '' unitDisc) := by
  sorry

end Pommerenke1992
