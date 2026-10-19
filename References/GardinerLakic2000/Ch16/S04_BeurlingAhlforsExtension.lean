import References.GardinerLakic2000.Ch16.S03_SymmetricHomeomorphisms

/-!
# Gardiner–Lakic 2000, Ch. 16 §16.4 Beurling–Ahlfors extension

Source `teichmuller.txt`, lines 12085–12123 (Chapter 16, §16.4).

* Definition (the Beurling–Ahlfors extension `ex(h)`, (16.4), l. 12093) — exists: `LiZhongQC.beurlingAhlfors`
  (with parameter `r = 2`: `u = (1/2y) ∫_{x−y}^{x+y} h`, `v = (1/y)(∫_x^{x+y} h − ∫_{x−y}^x h)`)
* Unlabelled (properties (i), (ii): naturality for the affine group, l. 12104) — `para16_4_ex_natural`
* Unlabelled (local estimate of the dilatation; vanishing ratio distortion gives a vanishing Beltrami coefficient,
  l. 12118; used in Theorem 3, §16.6 and §16.8) — `para16_4_ex_local`
* Theorem 3 (l. 12120) — `thm16_3`

Not items: (16.5) and the reduction to one point (l. 12110–12116, the argument of [Ahl66b]); the misprint
"from `x − t` to `x`" (l. 12102) = `x − y` [misprint]. Modelling: the dilatation `K_z < 1 + ε` is read through the
complex dilatation, `|μ(z)| < ε` (the two are equivalent up to the choice of `ε`); the local statement is for an
increasing homeomorphism `h` of `ℝ` whose ratios on symmetric triples in `[x₀ − b, x₀ + b]` lie in
`[1/(1 + δ), 1 + δ]`. Theorem 3 [reading, E0.4] is the restriction of the bijection of Corollary 16.1: for
quasisymmetric `h` with `Φ(h) = P`, `h` is symmetric iff `P ∈ T₀(Δ)` (batch D's `IsInT0`); the manifold structure is
not captured.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (beurlingAhlfors complexDilatation qsRatio unitDiscOpens)

/-- **Unlabelled** (§16.4, l. 12104). (i) The extension of the identity is the identity; (ii) for continuous `h` and
real affine `A(x) = a x + b`, `B(x) = c x + d` (`a, c > 0`), `ex(A ∘ h ∘ B) = A ∘ ex(h) ∘ B` on `ℍ`. [modelling] `h`
is continuous (the book's `h` is a homeomorphism): for `h(x) = x⁻²` the integrals are the junk `0` and (ii) fails
with `a = c = b = 1`, `d = 0` at `z = i`. -/
theorem para16_4_ex_natural :
    (∀ z : ℂ, 0 < z.im → beurlingAhlfors id 2 z = z) ∧
    ∀ (h : ℝ → ℝ), Continuous h → ∀ (a b c d : ℝ), 0 < a → 0 < c → ∀ z : ℂ, 0 < z.im →
      beurlingAhlfors (fun x => a * h (c * x + d) + b) 2 z = a * beurlingAhlfors h 2 (c * z + d) + b := by
  refine ⟨fun z _ => ?_, fun h hh a b c d _ _ z _ => ?_⟩
  · -- (i): `∫₀¹ 2x = 2x`, `∫₀¹ 2ty = y`
    have e1 : ∫ t in (0 : ℝ)..1, (z.re + t * z.im + (z.re - t * z.im)) = 2 * z.re := by
      have : (fun t : ℝ => z.re + t * z.im + (z.re - t * z.im)) = fun _ => 2 * z.re := by
        funext t
        ring
      rw [this, intervalIntegral.integral_const]
      simp
    have e2 : ∫ t in (0 : ℝ)..1, (z.re + t * z.im - (z.re - t * z.im)) = z.im := by
      have : (fun t : ℝ => z.re + t * z.im - (z.re - t * z.im)) = fun t => 2 * z.im * t := by
        funext t
        ring
      rw [this, intervalIntegral.integral_const_mul, integral_id]
      ring
    simp only [beurlingAhlfors, id]
    rw [e1, e2]
    apply Complex.ext <;> simp
  · -- (ii): `c (x ± t y) + d = X ± t Y` with `X + iY = cz + d`, then linearity of the two integrals
    have e1 : ∀ t : ℝ, c * (z.re + t * z.im) + d = c * z.re + d + t * (c * z.im) := fun t => by ring
    have e2 : ∀ t : ℝ, c * (z.re - t * z.im) + d = c * z.re + d - t * (c * z.im) := fun t => by ring
    have hre : ((c : ℂ) * z + (d : ℂ)).re = c * z.re + d := by simp
    have him : ((c : ℂ) * z + (d : ℂ)).im = c * z.im := by simp
    simp only [beurlingAhlfors, hre, him, e1, e2]
    set X := c * z.re + d with hX
    set Y := c * z.im with hY
    have hu : IntervalIntegrable (fun t : ℝ => h (X + t * Y) + h (X - t * Y)) volume 0 1 :=
      ((hh.comp (continuous_const.add (continuous_id.mul continuous_const))).add
        (hh.comp (continuous_const.sub (continuous_id.mul continuous_const)))).intervalIntegrable _ _
    have eu : ∫ t in (0 : ℝ)..1, (a * h (X + t * Y) + b + (a * h (X - t * Y) + b)) =
        a * (∫ t in (0 : ℝ)..1, (h (X + t * Y) + h (X - t * Y))) + 2 * b := by
      have : (fun t : ℝ => a * h (X + t * Y) + b + (a * h (X - t * Y) + b)) =
          fun t => a * (h (X + t * Y) + h (X - t * Y)) + 2 * b := by
        funext t
        ring
      rw [this, intervalIntegral.integral_add (hu.const_mul a) intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp
    have ev : ∫ t in (0 : ℝ)..1, (a * h (X + t * Y) + b - (a * h (X - t * Y) + b)) =
        a * ∫ t in (0 : ℝ)..1, (h (X + t * Y) - h (X - t * Y)) := by
      have : (fun t : ℝ => a * h (X + t * Y) + b - (a * h (X - t * Y) + b)) =
          fun t => a * (h (X + t * Y) - h (X - t * Y)) := by
        funext t
        ring
      rw [this, intervalIntegral.integral_const_mul]
    rw [eu, ev]
    apply Complex.ext <;> simp
    ring

/-- Helper for `para16_4_ex_local` (§16.4). One subdivision step: for a symmetric triple `x − t, x, x + t` in
`[a, a + L]`, each half carries at most the fraction `(1 + δ)/(2 + δ)` of the increment over `[x − t, x + t]`. -/
theorem gl16_bal_halves {h : ℝ → ℝ} (hmono : StrictMono h) {a L δ : ℝ} (hδ : 0 ≤ δ)
    (hr : ∀ x t : ℝ, 0 < t → a ≤ x - t → x + t ≤ a + L →
      1 / (1 + δ) ≤ qsRatio h x t ∧ qsRatio h x t ≤ 1 + δ) {x t : ℝ} (ht : 0 < t) (hxl : a ≤ x - t)
    (hxr : x + t ≤ a + L) :
    h x - h (x - t) ≤ (1 + δ) / (2 + δ) * (h (x + t) - h (x - t)) ∧
      h (x + t) - h x ≤ (1 + δ) / (2 + δ) * (h (x + t) - h (x - t)) := by
  obtain ⟨h1, h2⟩ := hr x t ht hxl hxr
  have hLh : 0 < h x - h (x - t) := sub_pos.2 (hmono (by linarith))
  have hR : 0 < h (x + t) - h x := sub_pos.2 (hmono (by linarith))
  have hδ1 : 0 < 1 + δ := by linarith
  unfold LiZhongQC.qsRatio at h1 h2
  rw [div_le_iff₀ hLh] at h2
  rw [div_le_div_iff₀ hδ1 hLh, one_mul] at h1
  have h2δ : 0 < 2 + δ := by linarith
  constructor
  · rw [div_mul_eq_mul_div, le_div_iff₀ h2δ]
    nlinarith
  · rw [div_mul_eq_mul_div, le_div_iff₀ h2δ]
    nlinarith

/-- Helper for `para16_4_ex_local` (§16.4). The dyadic increments of `h` on `[a, a + L]`: if the ratios on all symmetric
triples in `[a, a + L]` lie in `[1/(1 + δ), 1 + δ]`, then every level-`n` dyadic interval carries at most the fraction
`ρⁿ`, `ρ = (1 + δ)/(2 + δ)`, of the total increment (each half gets at most `ρ` of its parent). -/
theorem gl16_bal_dyadic_inc {h : ℝ → ℝ} (hmono : StrictMono h) {a L δ : ℝ} (hL : 0 < L) (hδ : 0 ≤ δ)
    (hr : ∀ x t : ℝ, 0 < t → a ≤ x - t → x + t ≤ a + L →
      1 / (1 + δ) ≤ qsRatio h x t ∧ qsRatio h x t ≤ 1 + δ) (n k : ℕ) (hk : k < 2 ^ n) :
    h (a + (k + 1) * L / 2 ^ n) - h (a + k * L / 2 ^ n) ≤ ((1 + δ) / (2 + δ)) ^ n * (h (a + L) - h a) := by
  have hρ0 : 0 ≤ (1 + δ) / (2 + δ) := by positivity
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by
      rw [pow_zero] at hk
      omega
    subst hk0
    simp
  | succ n ih =>
    have h2 : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
    have hpow : (0 : ℝ) < 2 ^ n := by positivity
    have hkn : k < 2 * 2 ^ n := by rw [pow_succ] at hk; omega
    obtain ⟨j, hj⟩ := Nat.even_or_odd' k
    have hjn : j < 2 ^ n := by rcases hj with hj | hj <;> omega
    have hpar := ih j hjn
    set t : ℝ := L / 2 ^ (n + 1) with ht
    have htpos : 0 < t := by positivity
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjle : ((j : ℝ) + 1) ≤ 2 ^ n := by exact_mod_cast hjn
    have eA : a + (j : ℝ) * L / 2 ^ n = a + (2 * j + 1) * t - t := by
      rw [ht, h2]
      field_simp
      ring
    have eB : a + ((j : ℝ) + 1) * L / 2 ^ n = a + (2 * j + 1) * t + t := by
      rw [ht, h2]
      field_simp
      ring
    have hxl : a ≤ a + (2 * j + 1) * t - t := by nlinarith
    have hxr : a + (2 * j + 1) * t + t ≤ a + L := by
      rw [← eB]
      have : ((j : ℝ) + 1) * L / 2 ^ n ≤ L := by
        rw [div_le_iff₀ hpow]
        nlinarith
      linarith
    obtain ⟨hl, hr'⟩ := gl16_bal_halves hmono hδ hr htpos hxl hxr
    rw [eA, eB] at hpar
    have hstep : (1 + δ) / (2 + δ) * (h (a + (2 * j + 1) * t + t) - h (a + (2 * j + 1) * t - t)) ≤
        ((1 + δ) / (2 + δ)) ^ (n + 1) * (h (a + L) - h a) := by
      rw [pow_succ, mul_comm (((1 + δ) / (2 + δ)) ^ n), mul_assoc]
      exact mul_le_mul_of_nonneg_left hpar hρ0
    rcases hj with rfl | rfl
    · -- the left half of the parent
      have e1 : a + ((((2 * j : ℕ) : ℝ)) + 1) * L / 2 ^ (n + 1) = a + (2 * j + 1) * t := by
        rw [ht]
        push_cast
        ring
      have e2 : a + (((2 * j : ℕ) : ℝ)) * L / 2 ^ (n + 1) = a + (2 * j + 1) * t - t := by
        rw [ht]
        push_cast
        ring
      rw [e1, e2]
      exact hl.trans hstep
    · -- the right half of the parent
      have e1 : a + ((((2 * j + 1 : ℕ) : ℝ)) + 1) * L / 2 ^ (n + 1) = a + (2 * j + 1) * t + t := by
        rw [ht]
        push_cast
        ring
      have e2 : a + (((2 * j + 1 : ℕ) : ℝ)) * L / 2 ^ (n + 1) = a + (2 * j + 1) * t := by
        rw [ht]
        push_cast
        ring
      rw [e1, e2]
      exact hr'.trans hstep

/-- Helper for `para16_4_ex_local` (§16.4). Near-affinity: under the ratio condition of `gl16_bal_dyadic_inc`, `h`
differs from its chord on `[a, a + L]` by at most `D((2ρ)ⁿ − 1 + 2⁻ⁿ)`, `D = h(a + L) − h(a)` (telescoping the dyadic
bound at the level-`n` points, monotonicity between them). -/
theorem gl16_bal_near_affine {h : ℝ → ℝ} (hmono : StrictMono h) {a L δ : ℝ} (hL : 0 < L) (hδ : 0 ≤ δ)
    (hr : ∀ x t : ℝ, 0 < t → a ≤ x - t → x + t ≤ a + L →
      1 / (1 + δ) ≤ qsRatio h x t ∧ qsRatio h x t ≤ 1 + δ) (n : ℕ) :
    ∀ t ∈ Icc a (a + L), |h t - (h a + (t - a) / L * (h (a + L) - h a))| ≤
      (h (a + L) - h a) * ((2 * ((1 + δ) / (2 + δ))) ^ n - 1 + (1 / 2) ^ n) := by
  set ρ : ℝ := (1 + δ) / (2 + δ) with hρ
  set D : ℝ := h (a + L) - h a with hD
  have hD0 : 0 ≤ D := sub_nonneg.2 (hmono.monotone (by linarith))
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hρh : 1 / 2 ≤ ρ := by
    rw [hρ, div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith
  have hρn : (1 / 2 : ℝ) ^ n ≤ ρ ^ n := pow_le_pow_left₀ (by norm_num) hρh n
  have hhalf : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have h2ρ : (2 * ρ) ^ n = 2 ^ n * ρ ^ n := mul_pow 2 ρ n
  -- the dyadic points `P k = a + k L / 2ⁿ`
  have hinc : ∀ k : ℕ, k < 2 ^ n →
      h (a + ((k : ℝ) + 1) * L / 2 ^ n) - h (a + (k : ℝ) * L / 2 ^ n) ≤ ρ ^ n * D :=
    fun k hk => gl16_bal_dyadic_inc hmono hL hδ hr n k hk
  have hG : ∀ i j : ℕ, i ≤ j → j ≤ 2 ^ n →
      h (a + (j : ℝ) * L / 2 ^ n) - h (a + (i : ℝ) * L / 2 ^ n) ≤ ((j : ℝ) - i) * (ρ ^ n * D) := by
    intro i j hij hjN
    induction j, hij using Nat.le_induction with
    | base => simp
    | succ j hij ih =>
      have h1 := hinc j (by omega)
      have h2 := ih (by omega)
      push_cast
      linarith
  have hP0 : a + ((0 : ℕ) : ℝ) * L / 2 ^ n = a := by simp
  have hPN : a + (((2 ^ n : ℕ)) : ℝ) * L / 2 ^ n = a + L := by
    push_cast
    field_simp
  -- the chord at `P k` is `h a + (k / 2ⁿ) D`
  have hchord : ∀ k : ℕ, (a + (k : ℝ) * L / 2 ^ n - a) / L * D = (k : ℝ) * (1 / 2) ^ n * D := by
    intro k
    rw [one_div_pow]
    field_simp
    ring
  -- the deviation at the dyadic points
  have hdev : ∀ k : ℕ, k ≤ 2 ^ n →
      |h (a + (k : ℝ) * L / 2 ^ n) - (h a + (a + (k : ℝ) * L / 2 ^ n - a) / L * D)| ≤ D * ((2 * ρ) ^ n - 1) := by
    intro k hk
    have hkR : (k : ℝ) ≤ 2 ^ n := by exact_mod_cast hk
    have hup := hG 0 k (Nat.zero_le k) hk
    have hlo := hG k (2 ^ n) hk le_rfl
    rw [hP0] at hup
    rw [hPN] at hlo
    push_cast at hup hlo
    rw [hchord k, abs_le, h2ρ]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hd : 0 ≤ ρ ^ n - (1 / 2) ^ n := by linarith
    constructor
    · -- `h(P k) − chord ≥ −(2ⁿ − k)(ρⁿ − 2⁻ⁿ) D`
      have e : D = h (a + L) - h a := rfl
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hkR) hd) hD0, mul_nonneg hk0 hD0]
    · nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hkR) hd) hD0, mul_nonneg (mul_nonneg hk0 hd) hD0]
  intro t ht
  obtain ⟨ht1, ht2⟩ := ht
  have hR0 : 0 ≤ D * ((2 * ρ) ^ n - 1 + (1 / 2) ^ n) := by
    have : 1 ≤ (2 * ρ) ^ n := one_le_pow₀ (by linarith)
    have : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
    exact mul_nonneg hD0 (by linarith)
  rcases ht2.lt_or_eq with ht2 | rfl
  · -- `t ∈ [P k, P (k + 1)]` with `k = ⌊(t − a) 2ⁿ / L⌋`
    set s : ℝ := (t - a) * 2 ^ n / L with hs
    have hs0 : 0 ≤ s := by
      rw [hs]
      have : 0 ≤ t - a := by linarith
      positivity
    have hsN : s < 2 ^ n := by
      rw [hs, div_lt_iff₀ hL]
      nlinarith
    set k : ℕ := ⌊s⌋₊ with hk
    have hk1 : (k : ℝ) ≤ s := Nat.floor_le hs0
    have hk2 : s < (k : ℝ) + 1 := Nat.lt_floor_add_one s
    have hkN : k < 2 ^ n := by
      have : (k : ℝ) < 2 ^ n := lt_of_le_of_lt hk1 hsN
      exact_mod_cast this
    have hts : t = a + s * L / 2 ^ n := by
      rw [hs]
      field_simp
      ring
    have hPk : a + (k : ℝ) * L / 2 ^ n ≤ t := by
      rw [hts]
      have : (k : ℝ) * L / 2 ^ n ≤ s * L / 2 ^ n := by gcongr
      linarith
    have hPk1 : t ≤ a + ((k + 1 : ℕ) : ℝ) * L / 2 ^ n := by
      rw [hts]
      push_cast
      have : s * L / 2 ^ n ≤ ((k : ℝ) + 1) * L / 2 ^ n := by gcongr
      linarith
    have hd1 := hdev k hkN.le
    have hd2 := hdev (k + 1) hkN
    have hm1 : h (a + (k : ℝ) * L / 2 ^ n) ≤ h t := hmono.monotone hPk
    have hm2 : h t ≤ h (a + ((k + 1 : ℕ) : ℝ) * L / 2 ^ n) := hmono.monotone hPk1
    -- the chord moves by `D / 2ⁿ` between consecutive dyadic points
    have hc1 : (a + (k : ℝ) * L / 2 ^ n - a) / L * D ≤ (t - a) / L * D := by
      apply mul_le_mul_of_nonneg_right _ hD0
      exact div_le_div_of_nonneg_right (by linarith) hL.le
    have hc2 : (t - a) / L * D ≤ (a + ((k + 1 : ℕ) : ℝ) * L / 2 ^ n - a) / L * D := by
      apply mul_le_mul_of_nonneg_right _ hD0
      exact div_le_div_of_nonneg_right (by linarith) hL.le
    have hgap : (a + ((k + 1 : ℕ) : ℝ) * L / 2 ^ n - a) / L * D - (a + (k : ℝ) * L / 2 ^ n - a) / L * D =
        D * (1 / 2) ^ n := by
      rw [hchord, hchord]
      push_cast
      ring
    rw [abs_le] at hd1 hd2 ⊢
    constructor <;> nlinarith
  · -- `t = a + L`: the deviation is `0`
    have e : h (a + L) - (h a + (a + L - a) / L * D) = 0 := by
      field_simp
      rw [hD]
      ring
    rw [e, abs_zero]
    exact hR0

/-- Helper for `para16_4_ex_local` (§16.4). The local `∂̄`- and `∂`-estimates for the Beurling–Ahlfors extension
(`r = 2`): if `|h − (c₀ + c₁ t)| ≤ M` on `[x − y, x + y]`, then `|∂̄ ex(h)(z)| ≤ 8M/y` and `|∂ ex(h)(z) − c₁| ≤ 8M/y`
(the affine part contributes `∂ = c₁`, `∂̄ = 0`). **Duplicate note:** the `∂̄` half restates the content of
`GardinerLakic2000.gl18_ba_dzbar_le` (Ch18/S03, downstream of this file); leader ruling 2026-10-05 (cleanup list). -/
theorem gl16_bal_partials {h : ℝ → ℝ} (hh : Continuous h) {z : ℂ} (hz : 0 < z.im) {c₀ c₁ M : ℝ}
    (hM : ∀ t ∈ Icc (z.re - z.im) (z.re + z.im), |h t - (c₀ + c₁ * t)| ≤ M) :
    ‖LiZhongQC.dzbar (beurlingAhlfors h 2) z‖ ≤ 8 * M / z.im ∧
      ‖LiZhongQC.dz (beurlingAhlfors h 2) z - c₁‖ ≤ 8 * M / z.im := by
  have hzU : z ∈ LiZhongQC.upperHalf := hz
  -- `ex₂ = T ∘ ex₁` for the real-linear `T(w) = Re w + 2i Im w`
  have hcomp : beurlingAhlfors h 2 =
      (Complex.reCLM.smulRight (1 : ℂ) + (2 : ℝ) • Complex.imCLM.smulRight I : ℂ →L[ℝ] ℂ) ∘
        beurlingAhlfors h 1 := by
    funext w
    simp only [Function.comp_apply, beurlingAhlfors]
    simp [Complex.real_smul]
    ring
  set T : ℂ →L[ℝ] ℂ := Complex.reCLM.smulRight (1 : ℂ) + (2 : ℝ) • Complex.imCLM.smulRight I with hT
  have hTapp : ∀ w : ℂ, T w = (w.re : ℂ) + ((2 * w.im : ℝ) : ℂ) * I := by
    intro w
    simp [hT, Complex.real_smul]
    ring
  have hdiff : DifferentiableAt ℝ (beurlingAhlfors h 1) z :=
    ((LiZhongQC.ba_f1h_contDiffOn hh).contDiffAt (LiZhongQC.isOpen_upperHalf.mem_nhds hzU)).differentiableAt
      one_ne_zero
  have hfd : fderiv ℝ (beurlingAhlfors h 2) z = T.comp (fderiv ℝ (beurlingAhlfors h 1) z) := by
    rw [hcomp]
    exact (T.hasFDerivAt.comp z hdiff.hasFDerivAt).fderiv
  set p := fderiv ℝ (beurlingAhlfors h 1) z 1 with hp
  set q := fderiv ℝ (beurlingAhlfors h 1) z I with hq
  have hdzbar : LiZhongQC.dzbar (beurlingAhlfors h 2) z =
      (((p.re - 2 * q.im : ℝ) : ℂ) + ((2 * p.im + q.re : ℝ) : ℂ) * I) / 2 := by
    unfold LiZhongQC.dzbar
    rw [hfd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hTapp, hTapp, ← hp, ← hq]
    congr 1
    push_cast
    linear_combination (2 * (q.im : ℂ)) * Complex.I_sq
  have hdz : LiZhongQC.dz (beurlingAhlfors h 2) z - c₁ =
      (((p.re + 2 * q.im - 2 * c₁ : ℝ) : ℂ) + ((2 * p.im - q.re : ℝ) : ℂ) * I) / 2 := by
    unfold LiZhongQC.dz
    rw [hfd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hTapp, hTapp, ← hp, ← hq]
    push_cast
    linear_combination (-(q.im : ℂ)) * Complex.I_sq
  obtain ⟨h1, hI⟩ := LiZhongQC.ba_f1_partials hh hzU
  rw [← hp] at h1
  rw [← hq] at hI
  have hab : ∀ a b : ℝ, ((a : ℂ) + (b : ℂ) * I).re = a ∧ ((a : ℂ) + (b : ℂ) * I).im = b := fun a b => by simp
  have hpre : p.re = (h (z.re + z.im) - h (z.re - z.im)) / (2 * z.im) := by rw [h1]; exact (hab _ _).1
  have hpim : p.im = (h (z.re + z.im) - 2 * h z.re + h (z.re - z.im)) / (2 * z.im) := by rw [h1]; exact (hab _ _).2
  have hqre : q.re = (h (z.re + z.im) + h (z.re - z.im)) / (2 * z.im) -
      (∫ t in (z.re - z.im)..(z.re + z.im), h t) / (2 * z.im ^ 2) := by rw [hI]; exact (hab _ _).1
  have hqim : q.im = (h (z.re + z.im) - h (z.re - z.im)) / (2 * z.im) -
      ((∫ t in z.re..(z.re + z.im), h t) - ∫ t in (z.re - z.im)..z.re, h t) / (2 * z.im ^ 2) := by
    rw [hI]; exact (hab _ _).2
  rw [hdzbar, hdz, hpre, hpim, hqre, hqim]
  set x := z.re with hx
  set y := z.im with hy
  set R : ℝ → ℝ := fun t => h t - (c₀ + c₁ * t) with hR
  have hRc : Continuous R := hh.sub (by fun_prop)
  have hRb : ∀ t ∈ Icc (x - y) (x + y), |R t| ≤ M := hM
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hRb x ⟨by linarith, by linarith⟩)
  have hint : ∀ a b : ℝ, x - y ≤ a → a ≤ b → b ≤ x + y → |∫ t in a..b, R t| ≤ M * (b - a) := by
    intro a b ha hab hb
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := M) (f := R)
      fun t ht => by
        rw [Real.norm_eq_abs]
        rw [Set.uIoc_of_le hab] at ht
        exact hRb t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ b - a)] at this
  have hb : ∀ J : ℝ, |J| ≤ M * y → |J / y| ≤ M := fun J hJ => by
    rw [abs_div, abs_of_pos hz, div_le_iff₀ hz]
    exact hJ
  have hbp : |(∫ t in x..(x + y), R t) / y| ≤ M :=
    hb _ (by simpa using hint x (x + y) (by linarith) (by linarith) le_rfl)
  have hbm : |(∫ t in (x - y)..x, R t) / y| ≤ M :=
    hb _ (by simpa using hint (x - y) x le_rfl (by linarith) (by linarith))
  have hp' := hRb (x + y) ⟨by linarith, le_rfl⟩
  have hm' := hRb (x - y) ⟨le_rfl, by linarith⟩
  have h0' := hRb x ⟨by linarith, by linarith⟩
  -- the norm of `(U + W i)/2` from `|U| y + |W| y ≤ 16 M`
  have key : ∀ U W : ℝ, |U * y| + |W * y| ≤ 16 * M → ‖((U : ℂ) + (W : ℂ) * I) / 2‖ ≤ 8 * M / y := by
    intro U W hUW
    have hsum : |U| + |W| ≤ 16 * M / y := by
      rw [le_div_iff₀ hz, add_mul, ← abs_of_pos hz, ← abs_mul, ← abs_mul]
      exact hUW
    rw [norm_div, Complex.norm_ofNat]
    have hn : ‖(U : ℂ) + (W : ℂ) * I‖ ≤ |U| + |W| := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
    have h10 : 2 * (8 * M / y) = 16 * M / y := by ring
    linarith
  have hval : ∀ t, h t = c₀ + c₁ * t + R t := fun t => by simp only [hR]; ring
  have hsp : ∀ a b : ℝ, ∫ t in a..b, h t = c₀ * (b - a) + c₁ * (b ^ 2 - a ^ 2) / 2 + ∫ t in a..b, R t := by
    intro a b
    have hlin : Continuous fun t : ℝ => c₀ + c₁ * t := by fun_prop
    have hA : ∫ t in a..b, (c₀ + c₁ * t) = c₀ * (b - a) + c₁ * (b ^ 2 - a ^ 2) / 2 := by
      rw [intervalIntegral.integral_add (f := fun _ => c₀) (g := fun t => c₁ * t) intervalIntegrable_const
        ((by fun_prop : Continuous fun t : ℝ => c₁ * t).intervalIntegrable _ _), intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul, integral_id, smul_eq_mul]
      ring
    have e : (fun t => h t) = fun t => (c₀ + c₁ * t) + R t := by
      funext t
      exact hval t
    rw [e, intervalIntegral.integral_add (f := fun t => c₀ + c₁ * t) (g := R)
      (hlin.intervalIntegrable _ _) (hRc.intervalIntegrable _ _), hA]
  have hadd : ∫ t in (x - y)..(x + y), R t = (∫ t in (x - y)..x, R t) + ∫ t in x..(x + y), R t :=
    (intervalIntegral.integral_add_adjacent_intervals (hRc.intervalIntegrable _ _)
      (hRc.intervalIntegrable _ _)).symm
  have hy0 : y ≠ 0 := hz.ne'
  rw [hsp (x - y) (x + y), hsp x (x + y), hsp (x - y) x, hadd, hval (x + y), hval (x - y), hval x]
  set Ip := (∫ t in x..(x + y), R t) / y with hIp
  set Im := (∫ t in (x - y)..x, R t) / y with hIm
  have eIp : ∫ t in x..(x + y), R t = Ip * y := by rw [hIp]; field_simp
  have eIm : ∫ t in (x - y)..x, R t = Im * y := by rw [hIm]; field_simp
  rw [eIp, eIm]
  obtain ⟨a1, a2⟩ := abs_le.1 hp'
  obtain ⟨b1, b2⟩ := abs_le.1 hm'
  obtain ⟨d1, d2⟩ := abs_le.1 h0'
  obtain ⟨e1, e2⟩ := abs_le.1 hbp
  obtain ⟨f1, f2⟩ := abs_le.1 hbm
  constructor
  · refine key _ _ ?_
    have eU : ((c₀ + c₁ * (x + y) + R (x + y) - (c₀ + c₁ * (x - y) + R (x - y))) / (2 * y) -
        2 * ((c₀ + c₁ * (x + y) + R (x + y) - (c₀ + c₁ * (x - y) + R (x - y))) / (2 * y) -
          (c₀ * (x + y - x) + c₁ * ((x + y) ^ 2 - x ^ 2) / 2 + Ip * y -
            (c₀ * (x - (x - y)) + c₁ * (x ^ 2 - (x - y) ^ 2) / 2 + Im * y)) / (2 * y ^ 2))) * y =
        -(R (x + y) - R (x - y)) / 2 + (Ip - Im) := by
      field_simp
      ring
    have eW : (2 * ((c₀ + c₁ * (x + y) + R (x + y) - 2 * (c₀ + c₁ * x + R x) + (c₀ + c₁ * (x - y) + R (x - y))) /
          (2 * y)) + ((c₀ + c₁ * (x + y) + R (x + y) + (c₀ + c₁ * (x - y) + R (x - y))) / (2 * y) -
          (c₀ * (x + y - (x - y)) + c₁ * ((x + y) ^ 2 - (x - y) ^ 2) / 2 + (Im * y + Ip * y)) / (2 * y ^ 2))) *
        y = (R (x + y) - 2 * R x + R (x - y)) + (R (x + y) + R (x - y)) / 2 - (Ip + Im) / 2 := by
      field_simp
      ring
    rw [eU, eW]
    rcases abs_cases (-(R (x + y) - R (x - y)) / 2 + (Ip - Im)) with ⟨g1, -⟩ | ⟨g1, -⟩ <;>
    rcases abs_cases ((R (x + y) - 2 * R x + R (x - y)) + (R (x + y) + R (x - y)) / 2 - (Ip + Im) / 2) with
      ⟨g2, -⟩ | ⟨g2, -⟩ <;>
    · rw [g1, g2]
      linarith
  · refine key _ _ ?_
    have eU : ((c₀ + c₁ * (x + y) + R (x + y) - (c₀ + c₁ * (x - y) + R (x - y))) / (2 * y) +
        2 * ((c₀ + c₁ * (x + y) + R (x + y) - (c₀ + c₁ * (x - y) + R (x - y))) / (2 * y) -
          (c₀ * (x + y - x) + c₁ * ((x + y) ^ 2 - x ^ 2) / 2 + Ip * y -
            (c₀ * (x - (x - y)) + c₁ * (x ^ 2 - (x - y) ^ 2) / 2 + Im * y)) / (2 * y ^ 2)) - 2 * c₁) * y =
        3 * (R (x + y) - R (x - y)) / 2 - (Ip - Im) := by
      field_simp
      ring
    have eW : (2 * ((c₀ + c₁ * (x + y) + R (x + y) - 2 * (c₀ + c₁ * x + R x) + (c₀ + c₁ * (x - y) + R (x - y))) /
          (2 * y)) - ((c₀ + c₁ * (x + y) + R (x + y) + (c₀ + c₁ * (x - y) + R (x - y))) / (2 * y) -
          (c₀ * (x + y - (x - y)) + c₁ * ((x + y) ^ 2 - (x - y) ^ 2) / 2 + (Im * y + Ip * y)) / (2 * y ^ 2))) *
        y = (R (x + y) - 2 * R x + R (x - y)) - (R (x + y) + R (x - y)) / 2 + (Ip + Im) / 2 := by
      field_simp
      ring
    rw [eU, eW]
    rcases abs_cases (3 * (R (x + y) - R (x - y)) / 2 - (Ip - Im)) with ⟨g1, -⟩ | ⟨g1, -⟩ <;>
    rcases abs_cases ((R (x + y) - 2 * R x + R (x - y)) - (R (x + y) + R (x - y)) / 2 + (Ip + Im) / 2) with
      ⟨g2, -⟩ | ⟨g2, -⟩ <;>
    · rw [g1, g2]
      linarith

/-- Helper for `para16_4_ex_local` (§16.4). The dilatation estimate at one point: if `h` is within `η D` of its
chord on `[x − y, x + y]` (`D = h(x + y) − h(x − y) > 0`) and `32 η < 1`, then `|μ(z)| ≤ 16η/(1 − 16η)`. -/
theorem gl16_bal_mu_le {h : ℝ → ℝ} (hmono : StrictMono h) (hh : Continuous h) {z : ℂ} (hz : 0 < z.im) {η : ℝ}
    (hη : 0 ≤ η) (hη1 : 32 * η < 1)
    (hM : ∀ t ∈ Icc (z.re - z.im) (z.re + z.im),
      |h t - (h (z.re - z.im) + (t - (z.re - z.im)) / (2 * z.im) * (h (z.re + z.im) - h (z.re - z.im)))| ≤
        η * (h (z.re + z.im) - h (z.re - z.im))) :
    ‖complexDilatation (beurlingAhlfors h 2) z‖ ≤ 16 * η / (1 - 16 * η) := by
  set x := z.re with hx
  set y := z.im with hy
  set D := h (x + y) - h (x - y) with hD
  have hD0 : 0 < D := sub_pos.2 (hmono (by linarith))
  -- the chord is `c₀ + c₁ t` with slope `c₁ = D/2y > 0`
  set c₁ : ℝ := D / (2 * y) with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  have hM' : ∀ t ∈ Icc (z.re - z.im) (z.re + z.im), |h t - ((h (x - y) - (x - y) * c₁) + c₁ * t)| ≤ η * D := by
    intro t ht
    have e : (h (x - y) - (x - y) * c₁) + c₁ * t = h (x - y) + (t - (x - y)) / (2 * y) * D := by
      rw [hc₁]
      ring
    rw [e]
    exact hM t ht
  obtain ⟨hb1, hb2⟩ := gl16_bal_partials hh hz hM'
  have e8 : 8 * (η * D) / y = 16 * η * c₁ := by
    rw [hc₁]
    field_simp
    ring
  rw [e8] at hb1 hb2
  -- `|∂ ex(h)| ≥ c₁(1 − 16η) > 0`
  have hlow : c₁ * (1 - 16 * η) ≤ ‖LiZhongQC.dz (beurlingAhlfors h 2) z‖ := by
    have h1 := norm_sub_norm_le (c₁ : ℂ) (LiZhongQC.dz (beurlingAhlfors h 2) z)
    rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc₁0] at h1
    linarith
  have hpos : 0 < c₁ * (1 - 16 * η) := mul_pos hc₁0 (by linarith)
  rw [LiZhongQC.complexDilatation, norm_div]
  calc ‖LiZhongQC.dzbar (beurlingAhlfors h 2) z‖ / ‖LiZhongQC.dz (beurlingAhlfors h 2) z‖
      ≤ (16 * η * c₁) / (c₁ * (1 - 16 * η)) := div_le_div₀ (by positivity) hb1 hpos hlow
    _ = 16 * η / (1 - 16 * η) := by
      have h1 : (1 - 16 * η) ≠ 0 := by linarith
      field_simp

/-- Helper for `para16_4_ex_local` (§16.4). Part (a) (the localized Ahlfors computation): `ε > 0` gives `δ > 0`
such that the ratio condition with `δ` on `[x₀ − b, x₀ + b]` forces `|μ(z)| < ε` for `|x − x₀| < b/2`,
`0 < y < b/2` (`[x − y, x + y] ⊆ [x₀ − b, x₀ + b]`, then `gl16_bal_near_affine` and `gl16_bal_mu_le`). -/
theorem gl16_bal_local :
    ∀ ε > 0, ∃ δ > 0, ∀ (h : ℝ → ℝ), StrictMono h → Continuous h → ∀ (x₀ b : ℝ), 0 < b →
      (∀ x t : ℝ, 0 < t → x₀ - b ≤ x - t → x + t ≤ x₀ + b →
        1 / (1 + δ) ≤ qsRatio h x t ∧ qsRatio h x t ≤ 1 + δ) →
      ∀ z : ℂ, |z.re - x₀| < b / 2 → 0 < z.im → z.im < b / 2 →
        ‖complexDilatation (beurlingAhlfors h 2) z‖ < ε := by
  intro ε hε
  -- the target accuracy `η₀`, the level `n` and the ratio tolerance `δ`
  set η₀ : ℝ := min (1 / 64) (ε / 64) with hη₀
  have hη₀0 : 0 < η₀ := lt_min (by norm_num) (by positivity)
  have hη₀1 : η₀ ≤ 1 / 64 := min_le_left _ _
  have hη₀2 : η₀ ≤ ε / 64 := min_le_right _ _
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hη₀0) (by norm_num : (1 / 2 : ℝ) < 1)
  have hcont : ContinuousAt (fun δ : ℝ => (2 * ((1 + δ) / (2 + δ))) ^ n) 0 :=
    (continuousAt_const.mul ((continuousAt_const.add continuousAt_id).div
      (continuousAt_const.add continuousAt_id) (by norm_num))).pow n
  have hval : (fun δ : ℝ => (2 * ((1 + δ) / (2 + δ))) ^ n) 0 = 1 := by norm_num
  have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), (2 * ((1 + δ) / (2 + δ))) ^ n < 1 + η₀ / 2 := by
    have := hcont.eventually (gt_mem_nhds (show (fun δ : ℝ => (2 * ((1 + δ) / (2 + δ))) ^ n) 0 < 1 + η₀ / 2 by
      rw [hval]
      linarith))
    exact this
  obtain ⟨r, hr0, hr⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨r / 2, half_pos hr0, fun h hmono hh x₀ b hb hrat z hzx hz hzb => ?_⟩
  set δ : ℝ := r / 2 with hδ
  have hδ0 : 0 ≤ δ := (half_pos hr0).le
  have hδn : (2 * ((1 + δ) / (2 + δ))) ^ n < 1 + η₀ / 2 := hr (by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hδ0]
    exact half_lt_self hr0)
  -- the ratio condition on `[x − y, x + y]`
  obtain ⟨hzx1, hzx2⟩ := abs_lt.1 hzx
  have hL : 0 < 2 * z.im := by positivity
  have hr' : ∀ x t : ℝ, 0 < t → z.re - z.im ≤ x - t → x + t ≤ z.re - z.im + 2 * z.im →
      1 / (1 + δ) ≤ qsRatio h x t ∧ qsRatio h x t ≤ 1 + δ :=
    fun x t ht h1 h2 => hrat x t ht (by linarith) (by linarith)
  have hnear := gl16_bal_near_affine hmono hL hδ0 hr' n
  have e : z.re - z.im + 2 * z.im = z.re + z.im := by ring
  rw [e] at hnear
  -- the accuracy `η = (2ρ)ⁿ − 1 + 2⁻ⁿ` lies in `[0, η₀)`
  set η : ℝ := (2 * ((1 + δ) / (2 + δ))) ^ n - 1 + (1 / 2) ^ n with hηdef
  have h2ρ : 1 ≤ 2 * ((1 + δ) / (2 + δ)) := by
    rw [mul_div_assoc', le_div_iff₀ (by linarith)]
    linarith
  have hη0 : 0 ≤ η := by
    have := one_le_pow₀ (n := n) h2ρ
    have : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
    rw [hηdef]
    linarith
  have hηlt : η < η₀ := by
    rw [hηdef]
    linarith
  have hM : ∀ t ∈ Icc (z.re - z.im) (z.re + z.im),
      |h t - (h (z.re - z.im) + (t - (z.re - z.im)) / (2 * z.im) * (h (z.re + z.im) - h (z.re - z.im)))| ≤
        η * (h (z.re + z.im) - h (z.re - z.im)) := fun t ht => by
    rw [mul_comm η]
    exact hnear t ht
  have hmu := gl16_bal_mu_le hmono hh hz hη0 (by linarith) hM
  -- `16η/(1 − 16η) ≤ 16η₀/(1 − 16η₀) ≤ ε/3`
  have h1 : 16 * η / (1 - 16 * η) ≤ 16 * η₀ / (1 - 16 * η₀) :=
    div_le_div₀ (by positivity) (by linarith) (by linarith) (by linarith)
  have h2 : 16 * η₀ / (1 - 16 * η₀) ≤ ε / 3 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- **Unlabelled** (§16.4, l. 12118). If `h` satisfies an `M`-condition with `M < 1 + δ` on symmetric triples in an
interval of midpoint `x₀` and half-width `b`, then `K_z < 1 + ε` (read `|μ(z)| < ε`) for `|x − x₀| < b/2`,
`0 < y < b/2`. In particular, a homeomorphism with vanishing ratio distortion has an extension with vanishing
Beltrami coefficient near `ℝ`. -/
theorem para16_4_ex_local :
    (∀ ε > 0, ∃ δ > 0, ∀ (h : ℝ → ℝ), StrictMono h → Continuous h → ∀ (x₀ b : ℝ), 0 < b →
      (∀ x t : ℝ, 0 < t → x₀ - b ≤ x - t → x + t ≤ x₀ + b →
        1 / (1 + δ) ≤ qsRatio h x t ∧ qsRatio h x t ≤ 1 + δ) →
      ∀ z : ℂ, |z.re - x₀| < b / 2 → 0 < z.im → z.im < b / 2 → ‖complexDilatation (beurlingAhlfors h 2) z‖ < ε) ∧
    ∀ h : ℝ → ℝ, StrictMono h → Continuous h → (∀ x, h (x + 1) = h x + 1) →
      (∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧ ∀ x t : ℝ, 0 < t →
        1 / (1 + ε t) ≤ qsRatio h x t ∧ qsRatio h x t ≤ 1 + ε t) →
      ∀ ε > 0, ∃ η > 0, ∀ z : ℂ, 0 < z.im → z.im < η → ‖complexDilatation (beurlingAhlfors h 2) z‖ < ε := by
  refine ⟨gl16_bal_local, ?_⟩
  -- (b) from (a): for small `t` the distortion `ε(t)` is below `min δ (1/2)`; localize at `x₀ = Re z`, `b = t₀/2`
  intro h hmono hcont _hper hεh ε hε
  obtain ⟨e, he, hr⟩ := hεh
  obtain ⟨δ, hδ, hloc⟩ := gl16_bal_local ε hε
  have hm : 0 < min δ (1 / 2) := lt_min hδ (by norm_num)
  have hev : {t : ℝ | |e t| < min δ (1 / 2)} ∈ 𝓝[>] (0 : ℝ) := by
    have h1 := he (Metric.ball_mem_nhds (0 : ℝ) hm)
    refine Filter.mem_of_superset h1 fun t ht => ?_
    have h2 : dist (e t) 0 < min δ (1 / 2) := ht
    rwa [Real.dist_eq, sub_zero] at h2
  obtain ⟨t₀, ht₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have ht₀' : (0 : ℝ) < t₀ := ht₀
  refine ⟨t₀ / 4, by positivity, fun z hz hzη => ?_⟩
  refine hloc h hmono hcont z.re (t₀ / 2) (by positivity) (fun x t ht hxl hxr => ?_) z
    (by rw [sub_self, abs_zero]; positivity) hz (by linarith)
  have htt : t ∈ Ioo (0 : ℝ) t₀ := ⟨ht, by linarith⟩
  have hb : |e t| < min δ (1 / 2) := hsub htt
  have hb1 : e t < δ := lt_of_le_of_lt (le_abs_self _) (lt_of_lt_of_le hb (min_le_left _ _))
  have hb2 : -(1 / 2) < e t := by
    have := neg_abs_le (e t)
    have := lt_of_lt_of_le hb (min_le_right _ _)
    linarith
  obtain ⟨hq1, hq2⟩ := hr x t ht
  refine ⟨le_trans ?_ hq1, by linarith⟩
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

/-- **Theorem 3** (§16.4, l. 12120). The space `S` of symmetric homeomorphisms is isomorphic to
`PSL(2, ℝ) × T₀(Δ)`: under `h ↦ (A_h, Φ(h))`, a quasisymmetric `h` is symmetric iff `Φ(h) ∈ T₀(Δ)`. -/
theorem thm16_3 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : LiZhongQC.IsFuchsian Γ)
    {p : UpperHalfPlane → unitDiscOpens} (hp : LiZhongQC.IsUniformization Γ p) {h : ℂ → ℂ}
    (hh : Pommerenke1992.IsSensePreservingCircleHomeo h) (hq : Pommerenke1992.IsQuasisymmetricA h)
    {P : TeichSpace unitDiscOpens p} (hP : IsPhiQS p h P) :
    HasVanishingRatioDistortion h ↔ IsInT0 p P := by
  sorry

end GardinerLakic2000
