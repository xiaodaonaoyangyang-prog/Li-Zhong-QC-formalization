import References.Pommerenke1992.Ch05.S03_LinearlyConnectedDomains

/-!
# Pommerenke 1992, Ch. 5 §5.4 Quasidisks and Quasisymmetric Functions

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §5.4; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 4553–4765.

* Definition (quasicircle, quasidisk, (5.4.1); cited at l. 6618, 7016 and P2 l. 2748) — exists:
  `Pommerenke1992.IsQuasicircle` `Pommerenke1992.IsQuasidisk` (defined in §5.1 by the same condition)
* Theorem 5.9 — `thm5_9`
* Definition (quasisymmetric map of the unit circle into the plane, Väisälä's form (5.4.4); cited at l. 4782, 5180,
  7110) — `IsQuasisymmetricWith`, `IsQuasisymmetric`
* Formula (5.4.5) (cited in the proof of Proposition 5.12) — `eq5_4_5`
* Unlabelled (§5.4, l. 4630: a quasisymmetric map is continuous; it satisfies (5.1.1), and conversely (5.1.1) implies
  quasisymmetry (TuVä80); used for the Quasicircle Theorem, l. 3981, and at l. 4640) — `isQuasisymmetric_continuousOn`,
  `isQuasisymmetric_iff`
* Proposition 5.10 — `prop5_10`
* Theorem 5.11 — `thm5_11`
* Proposition 5.12 — `prop5_12`
* Corollary 5.13 — `cor5_13`
* Proposition 5.14 (Väi84) — `prop5_14`
* Proposition 4.12 (§4.3), the quasidisk form (leader decision Q5) — `prop4_12_quasidisk`

Not items (DESIGN §3): Lavrentiev domains ("are called", l. 4563; a forward reference, defined with §7.4,
l. 7004–7010); the characterization for piecewise smooth
curves and the example domain with (5.4.2), (5.4.3) (l. 4565–4577); the remarks after Theorem 5.9 (l. 4593; recalled
only by the exercise at P2 l. 3204, and covered by `thm5_5_ii`, `eq4_3_7` and `thm5_9`); the explicit function `λ`
(5.4.6) of the proof of Theorem 5.11 (not cited); (5.4.7), (5.4.9), (5.4.10) (proof steps).

**Conventions.** As in §5.2 and §5.3. A map `h` of `𝕋` is a function `ℂ → ℂ` read on `sphere 0 1`; "onto `𝕋`" is
`h '' 𝕋 = 𝕋`. The function `λ` of (5.4.4) is `lam : ℝ → ℝ` (`λ` is a Lean keyword), read on `[0, ∞)`. The
restriction of a conformal map `f` of `𝔻` to `𝕋` is its continuous extension `F` to `𝔻̄` (Theorem 2.6). The outer
domain of a Jordan curve `J ⊆ ℂ` is the subset `(ℂ ∖ (J ∪ inner domain)) ∪ {∞}` of `Ĉ`, and maps of `𝔻*` are
`LehtoVirtanen1973.IsConformalMap` maps of `Ĉ`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsConformalOnto IsJordanCurve IsJordanDomain)
open LehtoVirtanen1973 (IsSimplyConnectedDomain IsConformalMap)

/-- **Theorem 5.9** (§5.4). Let `f` map `𝔻` conformally onto `G`. Then the following conditions are equivalent:
(i) `G` is a quasidisk;
(ii) `G` is a linearly connected John domain;
(iii) `f` is continuous in `𝔻̄`, and if `I(z)` (`1/2 ≤ |z| < 1`) has the endpoints `e^{it₁}, e^{it₂}`
(`t₁ ≤ t₂ ≤ t₁ + π`), then `diam f(I(z)) ≤ M₂ d_f(z) ≤ M₃ |f(e^{it₁}) - f(e^{it₂})|`.
Modelling: `I(z) = arcI z` (5.2.4), with the endpoints `t₁,₂ = arg z ∓ π(1 - |z|)`; `f` on `𝕋` is its continuous
extension `F`; the constants `M₂, M₃` depend on `f`. -/
theorem thm5_9 {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc (f '' unitDisc)) :
    List.TFAE [IsQuasidisk (f '' unitDisc),
      IsLinearlyConnected (f '' unitDisc) ∧ IsJohnDomain (f '' unitDisc),
      ∃ F : ℂ → ℂ, ContinuousOn F (closedBall 0 1) ∧ EqOn F f unitDisc ∧ ∃ M₂ M₃ : ℝ,
        ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ < 1 →
          Metric.ediam (F '' arcI z) ≤ ENNReal.ofReal (M₂ * distToBoundary f z) ∧
          M₂ * distToBoundary f z ≤
            M₃ * ‖F (exp ((arg z - π * (1 - ‖z‖)) * I)) - F (exp ((arg z + π * (1 - ‖z‖)) * I))‖] := by
  sorry

/-- **Definition (5.4.4)** (§5.4; cited at l. 4782, 5180, 7110). The map `h` of `𝕋` into `ℂ` is quasisymmetric with
the function `λ`: `h` is injective, `λ(x)` (`0 ≤ x < +∞`) is strictly increasing and continuous with `λ(0) = 0`, and
`|(h(z₁) - h(z₂))/(h(z₂) - h(z₃))| ≤ λ(|(z₁ - z₂)/(z₂ - z₃)|)` for `z₁, z₂, z₃ ∈ 𝕋`.
Modelling: the inequality is required where it is defined, `z₂ ≠ z₃`. -/
def IsQuasisymmetricWith (h : ℂ → ℂ) (lam : ℝ → ℝ) : Prop :=
  InjOn h (sphere 0 1) ∧ StrictMonoOn lam (Ici 0) ∧ ContinuousOn lam (Ici 0) ∧ lam 0 = 0 ∧
    ∀ z₁ ∈ sphere (0 : ℂ) 1, ∀ z₂ ∈ sphere (0 : ℂ) 1, ∀ z₃ ∈ sphere (0 : ℂ) 1, z₂ ≠ z₃ →
      ‖h z₁ - h z₂‖ / ‖h z₂ - h z₃‖ ≤ lam (‖z₁ - z₂‖ / ‖z₂ - z₃‖)

/-- **Definition** (§5.4). `h` is a quasisymmetric map of `𝕋` into `ℂ`: `IsQuasisymmetricWith h λ` for some `λ`. -/
def IsQuasisymmetric (h : ℂ → ℂ) : Prop :=
  ∃ lam : ℝ → ℝ, IsQuasisymmetricWith h lam

/-- **Formula (5.4.5)** (§5.4; cited in the proof of Proposition 5.12). Reversing the roles of `z₁` and `z₃` in
(5.4.4): `1/λ(|(z₃ - z₂)/(z₂ - z₁)|) ≤ |(h(z₁) - h(z₂))/(h(z₂) - h(z₃))|`.
Modelling: for `z₁ ≠ z₂ ≠ z₃`, where both sides are defined. -/
theorem eq5_4_5 {h : ℂ → ℂ} {lam : ℝ → ℝ} (hh : IsQuasisymmetricWith h lam) {z₁ z₂ z₃ : ℂ}
    (h₁ : z₁ ∈ sphere (0 : ℂ) 1) (h₂ : z₂ ∈ sphere (0 : ℂ) 1) (h₃ : z₃ ∈ sphere (0 : ℂ) 1) (h₁₂ : z₁ ≠ z₂)
    (h₂₃ : z₂ ≠ z₃) :
    1 / lam (‖z₃ - z₂‖ / ‖z₂ - z₁‖) ≤ ‖h z₁ - h z₂‖ / ‖h z₂ - h z₃‖ := by
  obtain ⟨hinj, -, -, -, hqs⟩ := hh
  -- (5.4.4) at `(z₃, z₂, z₁)`
  have h31 := hqs z₃ h₃ z₂ h₂ z₁ h₁ h₁₂.symm
  have hA : 0 < ‖h z₂ - h z₃‖ := norm_pos_iff.2 (sub_ne_zero.2 fun e => h₂₃ (hinj h₂ h₃ e))
  have hB : 0 < ‖h z₁ - h z₂‖ := norm_pos_iff.2 (sub_ne_zero.2 fun e => h₁₂ (hinj h₁ h₂ e))
  rw [norm_sub_rev (h z₃) (h z₂), norm_sub_rev (h z₂) (h z₁)] at h31
  calc 1 / lam (‖z₃ - z₂‖ / ‖z₂ - z₁‖) ≤ 1 / (‖h z₂ - h z₃‖ / ‖h z₁ - h z₂‖) :=
        one_div_le_one_div_of_le (div_pos hA hB) h31
    _ = ‖h z₁ - h z₂‖ / ‖h z₂ - h z₃‖ := one_div_div _ _

/-- **Unlabelled claim** (§5.4, l. 4630; used in Proposition 5.10, where `h(𝕋)` is a Jordan curve). Since
`λ(x) → 0` as `x → 0`, it follows from (5.4.4) that a quasisymmetric map `h` is continuous. -/
theorem isQuasisymmetric_continuousOn {h : ℂ → ℂ} (hh : IsQuasisymmetric h) : ContinuousOn h (sphere 0 1) := by
  obtain ⟨lam, hinj, -, hcont, h0, hqs⟩ := hh
  intro z hz
  have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.1 hz
  -- the third point `-z`
  have hz' : -z ∈ sphere (0 : ℂ) 1 := by rw [mem_sphere_zero_iff_norm, norm_neg]; exact hz1
  have hzz : z ≠ -z := fun e => by
    have : z = 0 := by linear_combination e / 2
    rw [this, norm_zero] at hz1
    exact zero_ne_one hz1
  have hd : 0 < ‖z - -z‖ := norm_pos_iff.2 (sub_ne_zero.2 hzz)
  set c := ‖h z - h (-z)‖ with hcdef
  have hc : 0 < c := norm_pos_iff.2 (sub_ne_zero.2 fun e => hzz (hinj hz hz' e))
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  -- `λ` is continuous at `0` with `λ(0) = 0`
  obtain ⟨η, hη, hηb⟩ := Metric.continuousWithinAt_iff.1 (hcont 0 (mem_Ici.2 le_rfl)) (ε / (2 * c))
    (by positivity)
  refine ⟨η * ‖z - -z‖, mul_pos hη hd, fun {w} hw hwz => ?_⟩
  have ht0 : 0 ≤ ‖w - z‖ / ‖z - -z‖ := div_nonneg (norm_nonneg _) hd.le
  have htη : dist (‖w - z‖ / ‖z - -z‖) 0 < η := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht0, div_lt_iff₀ hd]
    rw [dist_eq_norm] at hwz
    exact hwz
  have hl := hηb (mem_Ici.2 ht0) htη
  rw [Real.dist_eq, h0, sub_zero] at hl
  have hq := hqs w hw z hz (-z) hz' hzz
  rw [div_le_iff₀ hc] at hq
  rw [dist_eq_norm]
  calc ‖h w - h z‖ ≤ lam (‖w - z‖ / ‖z - -z‖) * c := hq
    _ ≤ |lam (‖w - z‖ / ‖z - -z‖)| * c := by gcongr; exact le_abs_self _
    _ ≤ ε / (2 * c) * c := by gcongr
    _ < ε := by
      rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hc.ne']
      linarith

/-- **Unlabelled claim** (§5.4, l. 4630; used for the Quasicircle Theorem, l. 3981, "formally stronger (but
equivalent)", and at l. 4640). Another consequence of (5.4.4) is (5.1.1), which conversely implies (TuVä80) that `h`
is quasisymmetric: the two definitions of quasisymmetry agree. -/
theorem isQuasisymmetric_iff {h : ℂ → ℂ} : IsQuasisymmetric h ↔ IsQuasisymmetricA h := by
  sorry

/-- Helper for `prop5_10` (§5.4). Let `a ≠ b` and `z` be points of `𝕋`, and let `z` lie on the closed side of the line
through `a` and `b` that does not contain `0`: `φ(z) φ(0) ≤ 0` for `φ(w) = Im((w − a)(b̄ − ā))`. Then
`|z − a| ≤ |b − a|` (the chord from `a` to a point of the shorter arc is at most the chord `ab`). -/
theorem p54_chord {a b z : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hz : ‖z‖ = 1) (hab : a ≠ b)
    (hside : ((z - a) * conj (b - a)).im * ((0 - a) * conj (b - a)).im ≤ 0) : ‖z - a‖ ≤ ‖b - a‖ := by
  have haa : a * conj a = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]
    norm_num
  -- rotate `a` to `1`: `u = z ā`, `v = b ā`
  have hrot : ∀ w : ℂ, (w - a) * conj (b - a) = (w * conj a - 1) * conj (b * conj a - 1) := fun w => by
    simp only [map_sub, map_mul, Complex.conj_conj, map_one]
    linear_combination (1 - w * conj b) * haa
  have hnorm : ∀ w : ℂ, ‖w - a‖ = ‖w * conj a - 1‖ := fun w => by
    rw [← haa, ← sub_mul, norm_mul, Complex.norm_conj, ha, mul_one]
  rw [hrot, hrot] at hside
  rw [hnorm, hnorm]
  set u := z * conj a with hu
  set v := b * conj a with hv
  have hu1 : ‖u‖ = 1 := by rw [hu, norm_mul, Complex.norm_conj, hz, ha, one_mul]
  have hv1 : ‖v‖ = 1 := by rw [hv, norm_mul, Complex.norm_conj, hb, ha, one_mul]
  have hv1' : v ≠ 1 := fun h => hab (by
    have h' : b * conj a * a = 1 * a := by rw [← hv, h]
    rw [mul_assoc, mul_comm (conj a) a, haa, mul_one, one_mul] at h'
    exact h'.symm)
  have hx : u.re ^ 2 + u.im ^ 2 = 1 := by
    have h := Complex.sq_norm u
    rw [hu1, Complex.normSq_apply] at h
    nlinarith [h]
  have hp : v.re ^ 2 + v.im ^ 2 = 1 := by
    have h := Complex.sq_norm v
    rw [hv1, Complex.normSq_apply] at h
    nlinarith [h]
  have hpq : ¬ (v.re = 1 ∧ v.im = 0) := fun h => hv1' (Complex.ext (by simpa using h.1) (by simpa using h.2))
  have H : (u.im * (v.re - 1) - v.im * (u.re - 1)) * v.im ≤ 0 := by
    have e1 : ((u - 1) * conj (v - 1)).im = u.im * (v.re - 1) - v.im * (u.re - 1) := by
      simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
        Complex.one_re, Complex.one_im, map_sub, map_one]
      ring
    have e2 : ((0 - 1) * conj (v - 1)).im = v.im := by
      simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
        Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im, map_sub, map_one]
      ring
    have h0 : (0 : ℂ) * conj a = 0 := zero_mul _
    rw [h0] at hside
    rw [← e1, ← e2]
    exact hside
  -- in coordinates: `p ≤ x`
  set x := u.re
  set y := u.im
  set p := v.re
  set q := v.im
  have hp1 : p < 1 := by
    rcases lt_or_eq_of_le (show p ≤ 1 by nlinarith [sq_nonneg q]) with h | h
    · exact h
    · exact absurd ⟨h, by nlinarith [sq_nonneg q]⟩ hpq
  have hC : 0 ≤ q * y + (1 + p) * (x - 1) := by
    by_contra hC
    have hC' := not_le.1 hC
    have : 0 < (p - 1) * (q * y + (1 + p) * (x - 1)) := mul_pos_of_neg_of_neg (by linarith) hC'
    have e : (y * (p - 1) - q * (x - 1)) * q = (p - 1) * (q * y + (1 + p) * (x - 1)) := by
      linear_combination (-(x - 1)) * hp
    linarith
  have hpx : p ≤ x := by
    rcases eq_or_lt_of_le (show -1 ≤ p by nlinarith [sq_nonneg q]) with h | h
    · rw [← h]
      nlinarith [sq_nonneg y]
    · by_contra hlt'
      have hlt := not_le.1 hlt'
      have h1x : 0 < 1 - x := by linarith
      have h1p : 0 < 1 + p := by linarith
      have hqy : (1 - x) * (1 + p) ≤ q * y := by linarith
      have hsq : ((1 - x) * (1 + p)) ^ 2 ≤ (q * y) ^ 2 :=
        pow_le_pow_left₀ (mul_pos h1x h1p).le hqy 2
      have hprod : (q * y) ^ 2 = (1 - p ^ 2) * (1 - x ^ 2) := by
        have : q ^ 2 = 1 - p ^ 2 := by linarith
        have : y ^ 2 = 1 - x ^ 2 := by linarith
        rw [mul_pow]
        simp only [*]
      rw [hprod] at hsq
      have hpos : 0 < (1 - x) * (1 + p) := mul_pos h1x h1p
      have : (1 - x) * (1 + p) * ((1 - x) * (1 + p)) ≤ (1 - x) * (1 + p) * ((1 + x) * (1 - p)) := by
        nlinarith [hsq]
      have := le_of_mul_le_mul_left this hpos
      nlinarith [this]
  -- conclude with the norms
  have e3 : ‖u - 1‖ ^ 2 = 2 - 2 * x := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    nlinarith [hx]
  have e4 : ‖v - 1‖ ^ 2 = 2 - 2 * p := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    nlinarith [hp]
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero |>.1 (by rw [e3, e4]; linarith)

/-- Helper for `prop5_10` (§5.4). The line through two distinct points `a, b` of `𝕋` meets `𝕋` only at `a` and `b`:
if `z ∈ 𝕋` and `Im((z − a)(b̄ − ā)) = 0`, then `z = a` or `z = b`. -/
theorem p54_line {a b z : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hz : ‖z‖ = 1) (hab : a ≠ b)
    (hφ : ((z - a) * conj (b - a)).im = 0) : z = a ∨ z = b := by
  have haa : a * conj a = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]
    norm_num
  have hrot : (z - a) * conj (b - a) = (z * conj a - 1) * conj (b * conj a - 1) := by
    simp only [map_sub, map_mul, Complex.conj_conj, map_one]
    linear_combination (1 - z * conj b) * haa
  rw [hrot] at hφ
  set u := z * conj a with hu
  set v := b * conj a with hv
  have hu1 : ‖u‖ = 1 := by rw [hu, norm_mul, Complex.norm_conj, hz, ha, one_mul]
  have hv1 : ‖v‖ = 1 := by rw [hv, norm_mul, Complex.norm_conj, hb, ha, one_mul]
  have hx : u.re ^ 2 + u.im ^ 2 = 1 := by
    have h := Complex.sq_norm u
    rw [hu1, Complex.normSq_apply] at h
    nlinarith [h]
  have hp : v.re ^ 2 + v.im ^ 2 = 1 := by
    have h := Complex.sq_norm v
    rw [hv1, Complex.normSq_apply] at h
    nlinarith [h]
  have hv1' : v ≠ 1 := fun h => hab (by
    have h' : b * conj a * a = 1 * a := by rw [← hv, h]
    rw [mul_assoc, mul_comm (conj a) a, haa, mul_one, one_mul] at h'
    exact h'.symm)
  have e1 : ((u - 1) * conj (v - 1)).im = u.im * (v.re - 1) - v.im * (u.re - 1) := by
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
      Complex.one_re, Complex.one_im, map_sub, map_one]
    ring
  rw [e1] at hφ
  -- unrotate: `w = u a`
  have hback : ∀ w : ℂ, w * conj a * a = w := fun w => by rw [mul_assoc, mul_comm (conj a) a, haa, mul_one]
  set x := u.re
  set y := u.im
  set p := v.re
  set q := v.im
  have hp1 : p ≠ 1 := fun h => hv1' (Complex.ext (by simpa using h) (by
    show q = 0
    nlinarith [sq_nonneg q]))
  have key : (x - 1) * (p - 1) * (p - x) = 0 := by
    linear_combination (1 / 2) * ((p - 1) ^ 2 * hx - ((p - 1) * y + q * (x - 1)) * hφ - (x - 1) ^ 2 * hp)
  have hp1' : p - 1 ≠ 0 := sub_ne_zero.2 hp1
  rcases mul_eq_zero.1 key with h | h
  · rcases mul_eq_zero.1 h with h | h
    · -- `u = 1`, so `z = a`
      left
      have hx1 : x = 1 := by linarith
      have hy0 : y = 0 := by nlinarith [sq_nonneg y]
      have hu' : u = 1 := Complex.ext (by simpa using hx1) (by simpa using hy0)
      rw [← hback z, ← hu, hu', one_mul]
    · exact absurd h hp1'
  · -- `x = p`, then `y = q`, so `u = v` and `z = b`
    right
    have hxp : x = p := by linarith
    have hyq : y = q := by
      have : (y - q) * (p - 1) = 0 := by rw [hxp] at hφ; linear_combination hφ
      rcases mul_eq_zero.1 this with h' | h'
      · linarith
      · exact absurd h' hp1'
    have huv : u = v := Complex.ext hxp hyq
    rw [← hback z, ← hu, huv, hv, hback]

/-- **Proposition 5.10** (§5.4). If `h` is a quasisymmetric map of `𝕋` into `ℂ`, then `J = h(𝕋)` is a quasicircle. -/
theorem prop5_10 {h : ℂ → ℂ} (hh : IsQuasisymmetric h) : IsQuasicircle (h '' sphere 0 1) := by
  have hc : ContinuousOn h (sphere 0 1) := isQuasisymmetric_continuousOn hh
  obtain ⟨lam, hinj, hmono, -, -, hqs⟩ := hh
  refine ⟨max (2 * lam 1) 1, LiZhongQC.iod_isJordanCurve_image_sphere one_pos hc hinj, le_max_right _ _, ?_⟩
  intro z₁ z₂ hz₁ hz₂ hne
  obtain ⟨_, ⟨a, ha, rfl⟩, ha'⟩ := hz₁
  obtain ⟨_, ⟨b, hb, rfl⟩, hb'⟩ := hz₂
  have hza : h a = z₁ := OnePoint.coe_injective ha'
  have hzb : h b = z₂ := OnePoint.coe_injective hb'
  subst hza hzb
  have hab : a ≠ b := fun e => hne (by rw [e])
  have ha1 : ‖a‖ = 1 := mem_sphere_zero_iff_norm.1 ha
  have hb1 : ‖b‖ = 1 := mem_sphere_zero_iff_norm.1 hb
  -- the side function of the chord `ab`, and the side `σφ > 0` away from `0`
  set φ : ℂ → ℝ := fun w => ((w - a) * conj (b - a)).im with hφdef
  have hφc : Continuous φ := by
    simp only [hφdef]
    fun_prop
  set σ : ℝ := if φ 0 < 0 then 1 else -1 with hσdef
  have hσ0 : σ * φ 0 ≤ 0 := by
    simp only [hσdef]
    split_ifs with h0
    · linarith
    · linarith
  have hσσ : σ * σ = 1 := by
    simp only [hσdef]
    split_ifs <;> norm_num
  -- a point `m ∈ 𝕋` with `σφ(m) > 0`
  have hm : ∃ m ∈ sphere (0 : ℂ) 1, 0 < σ * φ m := by
    have haa : a * conj a = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha1]
      norm_num
    -- rotate `a` to `1`: `φ(w) = Im((w ā − 1) conj(v − 1))`, `v = b ā`
    have hrot : ∀ w : ℂ, φ w = ((w * conj a - 1) * conj (b * conj a - 1)).im := fun w => by
      simp only [hφdef]
      congr 1
      simp only [map_sub, map_mul, Complex.conj_conj, map_one]
      linear_combination (1 - w * conj b) * haa
    have hback : ∀ w : ℂ, w * a * conj a = w := fun w => by rw [mul_assoc, haa, mul_one]
    set v := b * conj a with hv
    have hv1 : ‖v‖ = 1 := by rw [hv, norm_mul, Complex.norm_conj, hb1, ha1, one_mul]
    have hvne : v ≠ 1 := fun h' => hab (by
      have h'' : b * conj a * a = 1 * a := by rw [← hv, h']
      rw [mul_assoc, mul_comm (conj a) a, haa, mul_one, one_mul] at h''
      exact h''.symm)
    have hpq : v.re ^ 2 + v.im ^ 2 = 1 := by
      have h' := Complex.sq_norm v
      rw [hv1, Complex.normSq_apply] at h'
      nlinarith [h']
    have hφ0 : φ 0 = v.im := by
      rw [hrot]
      simp
    by_cases hvm : v = -1
    · -- antipodal points: `m = i a`, and `σ = -1`
      refine ⟨I * a, by rw [mem_sphere_zero_iff_norm, norm_mul, Complex.norm_I, ha1, one_mul], ?_⟩
      have hσ : σ = -1 := by
        simp only [hσdef, hφ0, hvm, Complex.neg_im, Complex.one_im, neg_zero, lt_irrefl, ite_false]
      rw [hσ, hrot, hback, hvm]
      simp [Complex.mul_im]
    · -- otherwise `m = a (1 + v)/|1 + v|`, the midpoint of the shorter arc
      set r := ‖1 + v‖ with hrdef
      have hr : 0 < r := norm_pos_iff.2 fun h' => hvm (by linear_combination h')
      refine ⟨(1 + v) * ((r⁻¹ : ℝ) : ℂ) * a, ?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hr.le),
          ← hrdef, ha1, mul_one, mul_inv_cancel₀ hr.ne']
      have hr2 : r ^ 2 = 2 + 2 * v.re := by
        rw [hrdef, Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
        nlinarith [hpq]
      have hp1 : v.re < 1 := by
        rcases lt_or_eq_of_le (show v.re ≤ 1 by nlinarith [sq_nonneg v.im]) with h' | h'
        · exact h'
        · exact absurd (Complex.ext (by simpa using h') (by simp; nlinarith [sq_nonneg v.im])) hvne
      have hrlt : r < 2 := by nlinarith [hr2, hr]
      have hq0 : v.im ≠ 0 := fun hq => by
        have hp' : (v.re - 1) * (v.re + 1) = 0 := by
          rw [hq] at hpq
          linear_combination hpq
        rcases mul_eq_zero.1 hp' with e | e
        · linarith
        · exact hvm (Complex.ext (by simp; linarith) (by simpa using hq))
      have hφm : φ ((1 + v) * ((r⁻¹ : ℝ) : ℂ) * a) = v.im * (1 - 2 / r) := by
        rw [hrot, hback]
        simp only [Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.add_re,
          Complex.add_im, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, map_sub,
          map_one, Complex.conj_re, Complex.conj_im]
        field_simp
        ring
      rw [hφm]
      simp only [hσdef, hφ0]
      split_ifs with hq
      · have : (1 - 2 / r) < 0 := by rw [sub_neg, lt_div_iff₀ hr]; linarith
        nlinarith [mul_pos_of_neg_of_neg hq this]
      · have hqp : 0 < v.im := lt_of_le_of_ne (not_lt.1 hq) (Ne.symm hq0)
        have : (1 - 2 / r) < 0 := by rw [sub_neg, lt_div_iff₀ hr]; linarith
        nlinarith [mul_neg_of_pos_of_neg hqp this]
  obtain ⟨m, hmS, hmpos⟩ := hm
  -- the points of `𝕋` with `σφ > 0` lie in the closed ball of radius `|a − b|` about `a` and about `b`
  have hφa : φ a = 0 := by simp [hφdef]
  have hφb : φ b = 0 := by
    simp only [hφdef]
    rw [Complex.mul_conj]
    exact Complex.ofReal_im _
  have hside : ∀ w ∈ sphere (0 : ℂ) 1, 0 < σ * φ w → ‖w - a‖ ≤ ‖a - b‖ ∧ ‖w - b‖ ≤ ‖a - b‖ := by
    intro w hw hpos
    have hw1 : ‖w‖ = 1 := mem_sphere_zero_iff_norm.1 hw
    have hprod : φ w * φ 0 ≤ 0 := by
      have : φ w * φ 0 = (σ * φ w) * (σ * φ 0) := by
        rw [show (σ * φ w) * (σ * φ 0) = (σ * σ) * (φ w * φ 0) by ring, hσσ, one_mul]
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos hpos.le hσ0
    refine ⟨?_, ?_⟩
    · rw [norm_sub_rev a b]
      exact p54_chord ha1 hb1 hw1 hab hprod
    · -- the same with `a` and `b` exchanged: `φ_{ba} = -φ_{ab}`
      have hsw : ∀ v : ℂ, ((v - b) * conj (a - b)).im = -φ v := fun v => by
        simp only [hφdef, map_sub, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
          Complex.conj_im]
        ring
      have hprod' : ((w - b) * conj (a - b)).im * ((0 - b) * conj (a - b)).im ≤ 0 := by
        rw [hsw, hsw]
        linarith
      exact p54_chord hb1 ha1 hw1 hab.symm hprod'
  -- the bound on `h` along that side: `|h(w) − h(a)| ≤ λ(1) |h(a) − h(b)|`
  have hdab : 0 < ‖a - b‖ := norm_pos_iff.2 (sub_ne_zero.2 hab)
  have hl1 : ∀ w ∈ sphere (0 : ℂ) 1, ∀ c ∈ sphere (0 : ℂ) 1, ∀ d ∈ sphere (0 : ℂ) 1, c ≠ d →
      ‖w - c‖ ≤ ‖c - d‖ → ‖h w - h c‖ ≤ lam 1 * ‖h c - h d‖ := by
    intro w hw c hc' d hd hcd hle
    have hcd0 : 0 < ‖c - d‖ := norm_pos_iff.2 (sub_ne_zero.2 hcd)
    have hhcd : 0 < ‖h c - h d‖ := norm_pos_iff.2 (sub_ne_zero.2 fun e => hcd (hinj hc' hd e))
    have hq := hqs w hw c hc' d hd hcd
    have hmon : lam (‖w - c‖ / ‖c - d‖) ≤ lam 1 :=
      hmono.monotoneOn (mem_Ici.2 (div_nonneg (norm_nonneg _) hcd0.le)) (mem_Ici.2 zero_le_one)
        ((div_le_one hcd0).2 hle)
    rw [div_le_iff₀ hhcd] at hq
    exact hq.trans (mul_le_mul_of_nonneg_right hmon (norm_nonneg _))
  have hdiam : ∀ w ∈ sphere (0 : ℂ) 1, 0 < σ * φ w → ‖h w - h a‖ ≤ lam 1 * ‖h a - h b‖ := fun w hw hpos =>
    hl1 w hw a ha b hb hab (hside w hw hpos).1
  -- the closed sides are compact, so their images are closed in `ℂ̄`
  set Sp : Set ℂ := sphere (0 : ℂ) 1 ∩ {w | 0 ≤ σ * φ w} with hSp
  set Sn : Set ℂ := sphere (0 : ℂ) 1 ∩ {w | σ * φ w ≤ 0} with hSn
  have hSpc : IsCompact Sp :=
    (isCompact_sphere 0 1).inter_right (isClosed_le continuous_const (continuous_const.mul hφc))
  have hSnc : IsCompact Sn :=
    (isCompact_sphere 0 1).inter_right (isClosed_le (continuous_const.mul hφc) continuous_const)
  have hclosed : ∀ T ⊆ sphere (0 : ℂ) 1, IsCompact T → IsClosed (toExt (h '' T)) := fun T hT hTc =>
    ((hTc.image_of_continuousOn (hc.mono hT)).image OnePoint.continuous_coe).isClosed
  set S : Set ExtPlane := toExt (h '' sphere 0 1) \ {((h a : ℂ) : ExtPlane), ((h b : ℂ) : ExtPlane)} with hSdef
  have hmem : ∀ x ∈ S, ∃ w ∈ sphere (0 : ℂ) 1, w ≠ a ∧ w ≠ b ∧ x = ((h w : ℂ) : ExtPlane) := by
    rintro _ ⟨⟨_, ⟨w, hw, rfl⟩, rfl⟩, hx⟩
    refine ⟨w, hw, fun e => hx (by rw [e]; exact mem_insert _ _), fun e => hx (by
      rw [e]; exact mem_insert_of_mem _ rfl), rfl⟩
  have himg : ∀ T : Set ℂ, ∀ w ∈ sphere (0 : ℂ) 1, ((h w : ℂ) : ExtPlane) ∈ toExt (h '' T) →
      T ⊆ sphere (0 : ℂ) 1 → w ∈ T := by
    rintro T w hw ⟨_, ⟨w', hw', rfl⟩, e⟩ hT
    rw [hinj (hT hw') hw (OnePoint.coe_injective e)] at hw'
    exact hw'
  have hmS' : ((h m : ℂ) : ExtPlane) ∈ S := by
    refine ⟨⟨h m, ⟨m, hmS, rfl⟩, rfl⟩, ?_⟩
    rintro (e | e)
    · have := hinj hmS ha (OnePoint.coe_injective e)
      rw [this, hφa, mul_zero] at hmpos
      exact lt_irrefl 0 hmpos
    · have := hinj hmS hb (OnePoint.coe_injective (mem_singleton_iff.1 e))
      rw [this, hφb, mul_zero] at hmpos
      exact lt_irrefl 0 hmpos
  -- the component of `h(m)` lies in the image of the open side `σφ > 0`
  have hCsub : connectedComponentIn S ((h m : ℂ) : ExtPlane) ⊆
      toExt (h '' (sphere (0 : ℂ) 1 ∩ {w | 0 < σ * φ w})) := by
    have hpre : IsPreconnected (connectedComponentIn S ((h m : ℂ) : ExtPlane)) :=
      isPreconnected_connectedComponentIn
    have hU₁ : IsOpen (toExt (h '' Sn))ᶜ := (hclosed Sn inter_subset_left hSnc).isOpen_compl
    have hU₂ : IsOpen (toExt (h '' Sp))ᶜ := (hclosed Sp inter_subset_left hSpc).isOpen_compl
    have hcov : connectedComponentIn S ((h m : ℂ) : ExtPlane) ⊆ (toExt (h '' Sn))ᶜ ∪ (toExt (h '' Sp))ᶜ := by
      intro x hx
      obtain ⟨w, hw, hwa, hwb, rfl⟩ := hmem x (connectedComponentIn_subset _ _ hx)
      have hφw : φ w ≠ 0 := fun e => by
        rcases p54_line ha1 hb1 (mem_sphere_zero_iff_norm.1 hw) hab e with e' | e'
        · exact hwa e'
        · exact hwb e'
      have hσw : σ * φ w ≠ 0 := mul_ne_zero (by simp only [hσdef]; split_ifs <;> norm_num) hφw
      rcases lt_or_gt_of_ne hσw with hneg | hposw
      · right
        intro hin
        have := (himg Sp w hw hin inter_subset_left).2
        exact absurd this (not_le.2 hneg)
      · left
        intro hin
        have := (himg Sn w hw hin inter_subset_left).2
        exact absurd this (not_le.2 hposw)
    have hdis : connectedComponentIn S ((h m : ℂ) : ExtPlane) ∩ ((toExt (h '' Sn))ᶜ ∩ (toExt (h '' Sp))ᶜ) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
      obtain ⟨w, hw, -, -, rfl⟩ := hmem x (connectedComponentIn_subset _ _ hx.1)
      rcases le_total (σ * φ w) 0 with hle | hle
      · exact hx.2.1 ⟨h w, ⟨w, ⟨hw, hle⟩, rfl⟩, rfl⟩
      · exact hx.2.2 ⟨h w, ⟨w, ⟨hw, hle⟩, rfl⟩, rfl⟩
    rcases isPreconnected_iff_subset_of_disjoint.1 hpre _ _ hU₁ hU₂ hcov hdis with hsub | hsub
    · intro x hx
      obtain ⟨w, hw, -, -, rfl⟩ := hmem x (connectedComponentIn_subset _ _ hx)
      refine ⟨h w, ⟨w, ⟨hw, ?_⟩, rfl⟩, rfl⟩
      by_contra hle
      exact hsub hx ⟨h w, ⟨w, ⟨hw, (show σ * φ w ≤ 0 from not_lt.1 hle)⟩, rfl⟩, rfl⟩
    · exfalso
      exact hsub (mem_connectedComponentIn hmS') ⟨h m, ⟨m, ⟨hmS, hmpos.le⟩, rfl⟩, rfl⟩
  refine ⟨((h m : ℂ) : ExtPlane), hmS', ?_, ?_⟩
  · intro hinf
    obtain ⟨_, -, e⟩ := hCsub hinf
    exact OnePoint.coe_ne_infty _ e
  · refine Metric.ediam_le fun x hx y hy => ?_
    obtain ⟨_, ⟨w, ⟨hw, hwp⟩, rfl⟩, e⟩ := hCsub hx
    obtain ⟨_, ⟨w', ⟨hw', hwp'⟩, rfl⟩, e'⟩ := hCsub hy
    rw [← OnePoint.coe_injective e, ← OnePoint.coe_injective e', edist_dist, dist_eq_norm]
    apply ENNReal.ofReal_le_ofReal
    calc ‖h w - h w'‖ ≤ ‖h w - h a‖ + ‖h w' - h a‖ := by
          rw [norm_sub_rev (h w') (h a)]
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ lam 1 * ‖h a - h b‖ + lam 1 * ‖h a - h b‖ := add_le_add (hdiam w hw hwp) (hdiam w' hw' hwp')
      _ = 2 * lam 1 * ‖h a - h b‖ := by ring
      _ ≤ max (2 * lam 1) 1 * ‖h a - h b‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

/-- **Theorem 5.11** (§5.4). If `f` maps `𝔻` conformally onto a quasidisk, then `f` restricted to `𝕋` is
quasisymmetric.
Modelling: the restriction to `𝕋` is the continuous extension `F`. -/
theorem thm5_11 {f F : ℂ → ℂ} (hf : IsConformalOnto f unitDisc (f '' unitDisc)) (hG : IsQuasidisk (f '' unitDisc))
    (hFc : ContinuousOn F (closedBall 0 1)) (hFf : EqOn F f unitDisc) : IsQuasisymmetric F := by
  sorry

/-- **Proposition 5.12** (§5.4). If `h` and `h*` are quasisymmetric maps of `𝕋` onto the same Jordan curve, then
`φ = h*⁻¹ ∘ h` is a quasisymmetric map of `𝕋` onto `𝕋`.
Modelling: `h*⁻¹` is `Function.invFunOn h* 𝕋`. -/
theorem prop5_12 {h hs : ℂ → ℂ} (hh : IsQuasisymmetric h) (hhs : IsQuasisymmetric hs)
    (hJ : h '' sphere 0 1 = hs '' sphere 0 1) :
    IsQuasisymmetric (Function.invFunOn hs (sphere 0 1) ∘ h) ∧
      (Function.invFunOn hs (sphere 0 1) ∘ h) '' sphere 0 1 = sphere 0 1 := by
  sorry

/-- **Corollary 5.13** (§5.4). If `f` and `g` map `𝔻` and `𝔻*` conformally onto the inner and outer domains of a
quasicircle, then `φ = g⁻¹ ∘ f` is a quasisymmetric map of `𝕋` onto `𝕋`.
Modelling: `f`, `g` on `𝕋` are their continuous extensions `F`, `Gc` (Theorem 2.6); `φ` is characterized on `𝕋` by
`Gc ∘ φ = F`. -/
theorem cor5_13 {J : Set ℂ} (hJ : IsQuasicircle J) {f F : ℂ → ℂ} (hf : IsConformalOnto f unitDisc (innerDomain J))
    (hFc : ContinuousOn F (closedBall 0 1)) (hFf : EqOn F f unitDisc) {g : ExtPlane → ExtPlane}
    (hg : IsConformalMap g extDiscExterior)
    (hgG : g '' extDiscExterior = toExt {z | z ∉ J ∧ z ∉ innerDomain J} ∪ {extInf}) {Gc : ℂ → ExtPlane}
    (hGc : ContinuousOn Gc {z | 1 ≤ ‖z‖}) (hGg : ∀ z : ℂ, 1 < ‖z‖ → Gc z = g z) :
    ∃ φ : ℂ → ℂ, IsQuasisymmetric φ ∧ φ '' sphere 0 1 = sphere 0 1 ∧
      ∀ ζ ∈ sphere (0 : ℂ) 1, Gc (φ ζ) = (F ζ : ExtPlane) := by
  sorry

/-- **Proposition 5.14** (§5.4; Väi84; (5.4.8) cited at l. 5096, 5128, 7126). If `h` is a quasisymmetric map of `𝕋`
into `ℂ`, then, for `z_j ∈ 𝕋` (`j = 1, …, 4`),
`|h(z₁) - h(z₃)||h(z₂) - h(z₄)| / (|h(z₁) - h(z₄)||h(z₂) - h(z₃)|) ≤ λ*(|z₁ - z₃||z₂ - z₄| / (|z₁ - z₄||z₂ - z₃|))`,
where the function `λ*` depends only on `λ`.
Modelling: for `z₁ ≠ z₄`, `z₂ ≠ z₃`, where both sides are defined; `λ*` is increasing on `[0, ∞)`, as the book reads it
(l. 5099 bounds by `λ*(M₁)` for cross-ratios `≤ M₁`, l. 5171 uses `λ*(2)`; the proof's `λ*` is increasing). -/
theorem prop5_14 (lam : ℝ → ℝ) :
    ∃ lamStar : ℝ → ℝ, MonotoneOn lamStar (Ici 0) ∧ ∀ h : ℂ → ℂ, IsQuasisymmetricWith h lam →
      ∀ z₁ ∈ sphere (0 : ℂ) 1, ∀ z₂ ∈ sphere (0 : ℂ) 1, ∀ z₃ ∈ sphere (0 : ℂ) 1, ∀ z₄ ∈ sphere (0 : ℂ) 1,
        z₁ ≠ z₄ → z₂ ≠ z₃ →
          ‖h z₁ - h z₃‖ * ‖h z₂ - h z₄‖ / (‖h z₁ - h z₄‖ * ‖h z₂ - h z₃‖) ≤
            lamStar (‖z₁ - z₃‖ * ‖z₂ - z₄‖ / (‖z₁ - z₄‖ * ‖z₂ - z₃‖)) := by
  sorry

/-- **Proposition 4.12** (§4.3, l. 3445; proved in §8.6), the quasidisk form. There is a conformal map onto a
quasidisk that is nowhere isogonal, and thus nowhere conformal, on `𝕋`.
Modelling: the Jordan-domain form is `prop4_12` (§4.3); this form is stated here, where quasidisks are defined
(leader decision Q5). -/
theorem prop4_12_quasidisk :
    ∃ f : ℂ → ℂ, IsQuasidisk (f '' unitDisc) ∧ IsConformalOnto f unitDisc (f '' unitDisc) ∧
      ∀ ζ ∈ sphere (0 : ℂ) 1, ¬ IsIsogonalAt f ζ := by
  sorry

end Pommerenke1992
