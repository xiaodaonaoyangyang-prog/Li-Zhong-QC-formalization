import References.GardinerLakic2000.Ch16.S05_Welding

/-!
# Gardiner–Lakic 2000, Ch. 16 §16.6 Zygmund spaces

Source `teichmuller.txt`, lines 12363–12535 (Chapter 16, §16.6).

* Definition 9 (the Zygmund space `Z`, (16.15), l. 12366) — exists: `GardinerLakic2000.IsZygmundBoundedVF` (batch A,
  the same condition with the reality condition `V(e^{ix})/(ie^{ix}) ∈ ℝ`)
* Definition 9 (the subspace `Z₀`, l. 12370) — `IsZygmundVanishingVF`
* Theorem 5 (l. 12383) — `thm16_5_a`, `thm16_5_b`
* Definition (the extension `Ṽ = A + iB` of (16.18), l. 12449) — exists: `LiZhongQC.beurlingAhlfors` (with
  parameter `r = 2`: the formula (16.4) applied to the vector field)
* Lemma 9 ((16.19), (16.20), l. 12482) — `lemma16_9`
* Theorem 6 (l. 12518) — `thm16_6`

Not items: the Remark (Reimann, l. 12384); (16.16), (16.17) and the variation formula for `w^{sμ}` (l. 12505; proof
of Theorem 5); the space `Π` of tangent quadratic polynomials and the identifications `Z ≅ Π ⊕ B`, `Z₀ ≅ Π ⊕ B₀`
(l. 12520–12532; the proof of Theorem 6); the closing Remark (l. 12534). Near miss: `GarnettMarshall2005.MemZygmund`
(complex-valued, no reality condition). Modelling [reading, E0.4]: Theorem 5 ("`Z` and `Z₀` are the tangent spaces to
QS and S") is: (a) if `h_s` (`|s| < s₀`) are quasisymmetric with `h₀ = id`, `h_s = id + sV + o(s)` uniformly on `S¹`
and `h_s` satisfying an `M_s`-condition with `M_s ≤ 1 + C|s|` (the proof's reading of a smooth curve in QS), then
`V ∈ Z`, and `V ∈ Z₀` if moreover `h_s` satisfies (16.1) at scale `t` with `M = 1 + |s| ε(t)`, `ε(t) → 0` uniformly
in `s` (**[CORRECTION/reading]** at `thm16_5_a`: symmetry of each `h_s` does not suffice); (b) conversely every
`V ∈ Z` (resp. `Z₀`) is the tangent vector of such a curve in QS (resp. S). Theorem 6 is the bijection of `QS mod S`
(left cosets `S ∘ h`) onto `AT(Δ)`
(batch D's `AsymTeichSpace` of `LiZhongQC.unitDiscOpens`) induced by `Φ`; the manifold and tangent-space clauses are
Theorem 5 and batch D's `thm14_6_b`, and the complex manifold structure is not captured.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (unitDiscOpens)

/-- **Definition 9** (`Z₀`, §16.6, l. 12370). `V ∈ Z` with `|V(e^{i(x+t)}) + V(e^{i(x−t)}) − 2V(e^{ix})| / t ≤ ε(t)`,
`ε(t) → 0` uniformly in `x`. -/
def IsZygmundVanishingVF (V : ℂ → ℂ) : Prop :=
  IsZygmundBoundedVF V ∧ ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧ ∀ θ t : ℝ, 0 < t →
    ‖V (exp ((θ + t) * I)) + V (exp ((θ - t) * I)) - 2 * V (exp (θ * I))‖ ≤ ε t * t

/-- Helper for `thm16_5_a` (§16.6, Z1). A sense-preserving circle homeomorphism maps `S¹` into `S¹`. -/
theorem gl16_zyg_norm_eq_one {h : ℂ → ℂ} (hh : Pommerenke1992.IsSensePreservingCircleHomeo h) (θ : ℝ) :
    ‖h (exp (θ * I))‖ = 1 ∧ Continuous fun θ : ℝ => h (exp (θ * I)) := by
  obtain ⟨u, hu, -, -, hhu⟩ := hh
  refine ⟨by rw [hhu θ, Complex.norm_exp_ofReal_mul_I], ?_⟩
  rw [show (fun θ : ℝ => h (exp (θ * I))) = fun θ => exp ((u θ : ℂ) * I) from funext hhu]
  exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hu).mul continuous_const)

/-- Helper for `thm16_5_a` (§16.6, Z3). A continuous `2π`-periodic function `ℝ → ℝ` is uniformly continuous. -/
theorem gl16_zyg_uniformContinuous {f : ℝ → ℝ} (hf : Continuous f) (hp : ∀ θ, f (θ + 2 * π) = f θ) :
    UniformContinuous f := by
  have hper : Function.Periodic f (2 * π) := hp
  have hπ := Real.pi_pos
  have hK : UniformContinuousOn f (Icc (-(2 * π)) (4 * π)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.uniformContinuousOn_iff.1 hK ε hε
  refine ⟨min δ₀ (2 * π), lt_min hδ₀ (by positivity), fun {a b} hab => ?_⟩
  set k : ℤ := ⌊a / (2 * π)⌋ with hk
  have h1 : (k : ℝ) ≤ a / (2 * π) := Int.floor_le _
  have h2 : a / (2 * π) < k + 1 := Int.lt_floor_add_one _
  have h2π : 0 < 2 * π := by positivity
  rw [le_div_iff₀ h2π] at h1
  rw [div_lt_iff₀ h2π] at h2
  have hab' : |a - b| < min δ₀ (2 * π) := by rwa [Real.dist_eq] at hab
  have hab1 := (abs_lt.1 (hab'.trans_le (min_le_right _ _)))
  have ha' : a - k * (2 * π) ∈ Icc (-(2 * π)) (4 * π) := ⟨by nlinarith, by nlinarith⟩
  have hb' : b - k * (2 * π) ∈ Icc (-(2 * π)) (4 * π) := ⟨by nlinarith, by nlinarith⟩
  have hd : dist (a - k * (2 * π)) (b - k * (2 * π)) < δ₀ := by
    rw [Real.dist_eq, show a - k * (2 * π) - (b - k * (2 * π)) = a - b by ring]
    exact hab'.trans_le (min_le_left _ _)
  have := hδ _ ha' _ hb' hd
  rwa [hper.sub_int_mul_eq, hper.sub_int_mul_eq] at this

/-- Helper for `thm16_5_a` (§16.6, Z5). `1/M ≤ N/D ≤ M` (`M > 0`) gives `|N − D| ≤ |M − 1| max(N, D)`. -/
theorem gl16_zyg_ratio {N D M : ℝ} (hN : 0 ≤ N) (hD : 0 ≤ D) (hM : 0 < M) (h1 : 1 / M ≤ N / D) (h2 : N / D ≤ M) :
    |N - D| ≤ |M - 1| * max N D := by
  rcases hD.eq_or_lt with hD0 | hDpos
  · rw [← hD0, div_zero] at h1
    have : 0 < 1 / M := by positivity
    linarith
  have hNM : N ≤ M * D := by rwa [div_le_iff₀ hDpos] at h2
  have hDM : D ≤ M * N := by
    rw [div_le_div_iff₀ hM hDpos, one_mul] at h1
    linarith [mul_comm N M]
  have h3 : (M - 1) * N ≤ |M - 1| * max N D :=
    mul_le_mul (le_abs_self _) (le_max_left _ _) hN (abs_nonneg _)
  have h4 : (M - 1) * D ≤ |M - 1| * max N D :=
    mul_le_mul (le_abs_self _) (le_max_right _ _) hD (abs_nonneg _)
  rw [abs_le]
  constructor <;> nlinarith

/-- Helper for `thm16_5_a` (§16.6, Z7). `‖Δ²V‖ ≤ |Δ²v| + 2|v(x)|(1 − cos t) + |sin t| |v(x + t) − v(x − t)|` for
`V(e^{iθ}) = i e^{iθ} v(θ)`. -/
theorem gl16_zyg_second_diff {V : ℂ → ℂ} {v : ℝ → ℝ} (hv : ∀ θ : ℝ, V (exp (θ * I)) = I * exp (θ * I) * v θ)
    (x t : ℝ) :
    ‖V (exp ((x + t) * I)) + V (exp ((x - t) * I)) - 2 * V (exp (x * I))‖ ≤
      |v (x + t) + v (x - t) - 2 * v x| + 2 * |v x| * (1 - Real.cos t) + |Real.sin t| * |v (x + t) - v (x - t)| := by
  rw [← Complex.ofReal_add, ← Complex.ofReal_sub, hv, hv, hv]
  set c := Real.cos t with hc
  set s := Real.sin t with hs
  set E := exp ((x : ℂ) * I) with hE
  have ep : exp (((x + t : ℝ) : ℂ) * I) = E * ((c : ℂ) + (s : ℂ) * I) := by
    rw [show ((x + t : ℝ) : ℂ) * I = (x : ℂ) * I + (t : ℂ) * I by push_cast; ring, Complex.exp_add,
      Complex.exp_mul_I (t : ℂ), ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have em : exp (((x - t : ℝ) : ℂ) * I) = E * ((c : ℂ) - (s : ℂ) * I) := by
    rw [show ((x - t : ℝ) : ℂ) * I = (x : ℂ) * I + ((-t : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_add,
      Complex.exp_mul_I ((-t : ℝ) : ℂ), ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
      Complex.ofReal_neg]
    ring
  rw [ep, em]
  set P := v (x + t)
  set Q := v (x - t)
  set R := v x
  have e : I * (E * ((c : ℂ) + (s : ℂ) * I)) * P + I * (E * ((c : ℂ) - (s : ℂ) * I)) * Q - 2 * (I * E * R) =
      I * E * (((c * (P + Q - 2 * R) + 2 * R * (c - 1) : ℝ) : ℂ) + ((s * (P - Q) : ℝ) : ℂ) * I) := by
    push_cast
    ring
  rw [e, norm_mul, norm_mul, Complex.norm_I, hE, Complex.norm_exp_ofReal_mul_I, one_mul, one_mul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_mul]
  have hc1 : c ≤ 1 := Real.cos_le_one t
  have hc2 : |c| ≤ 1 := Real.abs_cos_le_one t
  calc |c * (P + Q - 2 * R) + 2 * R * (c - 1)| + |s| * |P - Q|
      ≤ (|c| * |P + Q - 2 * R| + 2 * |R| * (1 - c)) + |s| * |P - Q| := by
        gcongr
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_nonpos (by linarith : c - 1 ≤ 0)]
        linarith
    _ ≤ |P + Q - 2 * R| + 2 * |R| * (1 - c) + |s| * |P - Q| := by
        gcongr
        calc |c| * |P + Q - 2 * R| ≤ 1 * |P + Q - 2 * R| := by gcongr
          _ = _ := one_mul _

/-- Helper for `thm16_5_a` (§16.6, Z6). The algebra behind Z6: for `W = c + i s` on the unit circle (`s ≠ 0`),
`Re(i(W²P − Q)/(W² − 1)) = c(P − Q)/(2s)`. -/
theorem gl16_zyg_re_alg {c s P Q : ℝ} (hcs : s ^ 2 + c ^ 2 = 1) (hs : s ≠ 0) :
    (I * (((c : ℂ) + (s : ℂ) * I) ^ 2 * P - Q) / (((c : ℂ) + (s : ℂ) * I) ^ 2 - 1)).re = c * (P - Q) / (2 * s) := by
  set W : ℂ := (c : ℂ) + (s : ℂ) * I with hW
  have hWre : (W ^ 2).re = c ^ 2 - s ^ 2 := by simp [hW, pow_two]
  have hWim : (W ^ 2).im = 2 * c * s := by simp [hW, pow_two]; ring
  have hb : W ^ 2 - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [Complex.sub_re, hWre, Complex.one_re, Complex.zero_re] at this
    have hs2 : s ^ 2 = 0 := by nlinarith
    exact hs (pow_eq_zero_iff two_ne_zero |>.1 hs2)
  set N : ℂ := ((c * (P - Q) : ℝ) : ℂ) + ((s * (P + Q) : ℝ) : ℂ) * I with hN
  have key : I * (W ^ 2 * P - Q) * ((2 * s : ℝ) : ℂ) = N * (W ^ 2 - 1) := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, hWre, hWim, hN, Complex.add_re,
        Complex.add_im]
      linear_combination (-c * (P - Q)) * hcs
    · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im, hWre, hWim, hN, Complex.add_re,
        Complex.add_im]
      linear_combination (-s * (P - Q)) * hcs
  have h2s : ((2 * s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero hs
  rw [div_eq_div_iff hb h2s |>.2 key, Complex.div_ofReal_re]
  simp [hN]

/-- Helper for `thm16_5_a` (§16.6, Z6). Cancelling `E = e^{ix}` in the two difference quotients. -/
theorem gl16_zyg_quot_aux {E W : ℂ} (hE : E ≠ 0) (P Q : ℂ) :
    (I * (E * W ^ 2) * P - I * E * Q) / (E * W ^ 2 - E) = I * (W ^ 2 * P - Q) / (W ^ 2 - 1) ∧
      (I * E * Q - I * (E * W ^ 2) * P) / (E - E * W ^ 2) = I * (W ^ 2 * P - Q) / (W ^ 2 - 1) := by
  constructor
  · rw [show I * (E * W ^ 2) * P - I * E * Q = E * (I * (W ^ 2 * P - Q)) by ring,
      show E * W ^ 2 - E = E * (W ^ 2 - 1) by ring, mul_div_mul_left _ _ hE]
  · rw [show I * E * Q - I * (E * W ^ 2) * P = E * -(I * (W ^ 2 * P - Q)) by ring,
      show E - E * W ^ 2 = E * -(W ^ 2 - 1) by ring, mul_div_mul_left _ _ hE, neg_div_neg_eq]

/-- Helper for `thm16_5_a` (§16.6, Z6). For a tangent field `V(e^{iθ}) = i e^{iθ} v(θ)` the first-order coefficient of
Z4 is `Δ²v(x, t) cos(t/2) / (2 sin(t/2))`. -/
theorem gl16_zyg_re_quot {V : ℂ → ℂ} {v : ℝ → ℝ} (hv : ∀ θ : ℝ, V (exp (θ * I)) = I * exp (θ * I) * v θ) {x t : ℝ}
    (ht : Real.sin (t / 2) ≠ 0) :
    ((V (exp ((x + t) * I)) - V (exp (x * I))) / (exp ((x + t) * I) - exp (x * I))).re -
        ((V (exp (x * I)) - V (exp ((x - t) * I))) / (exp (x * I) - exp ((x - t) * I))).re =
      (v (x + t) + v (x - t) - 2 * v x) * Real.cos (t / 2) / (2 * Real.sin (t / 2)) := by
  rw [← Complex.ofReal_add, ← Complex.ofReal_sub, hv, hv, hv]
  have hcs : Real.sin (t / 2) ^ 2 + Real.cos (t / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hE0 : exp ((x : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
  have ep : exp (((x + t : ℝ) : ℂ) * I) =
      exp ((x : ℂ) * I) * ((Real.cos (t / 2) : ℂ) + (Real.sin (t / 2) : ℂ) * I) ^ 2 := by
    rw [show ((x + t : ℝ) : ℂ) * I = (x : ℂ) * I + ((t / 2 : ℝ) : ℂ) * I + ((t / 2 : ℝ) : ℂ) * I by
      push_cast; ring, Complex.exp_add, Complex.exp_add, Complex.exp_mul_I ((t / 2 : ℝ) : ℂ), ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
    ring
  have em : exp (((x - t : ℝ) : ℂ) * I) =
      exp ((x : ℂ) * I) * ((Real.cos (t / 2) : ℂ) + ((-Real.sin (t / 2) : ℝ) : ℂ) * I) ^ 2 := by
    rw [show ((x - t : ℝ) : ℂ) * I = (x : ℂ) * I + ((-(t / 2) : ℝ) : ℂ) * I + ((-(t / 2) : ℝ) : ℂ) * I by
      push_cast; ring, Complex.exp_add, Complex.exp_add, Complex.exp_mul_I ((-(t / 2) : ℝ) : ℂ),
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    ring
  rw [ep, em, (gl16_zyg_quot_aux hE0 _ _).1, (gl16_zyg_quot_aux hE0 _ _).2, gl16_zyg_re_alg hcs ht,
    gl16_zyg_re_alg (s := -Real.sin (t / 2)) (by rw [neg_sq]; exact hcs) (neg_ne_zero.2 ht)]
  field_simp
  ring

/-- Helper for `thm16_5_a` (§16.6, Z2). The tangent vector of a curve of self-maps of `S¹` is bounded on `S¹`, and
continuous in the angle (a uniform limit of `(h_s − id)/s`). -/
theorem gl16_zyg_V_bdd_cont {s₀ : ℝ} (hs₀ : 0 < s₀) {hs : ℝ → ℂ → ℂ} {V : ℂ → ℂ}
    (hn : ∀ s, |s| < s₀ → ∀ θ : ℝ, ‖hs s (exp (θ * I))‖ = 1 ∧ Continuous fun θ : ℝ => hs s (exp (θ * I)))
    (htan : ∀ ε > 0, ∃ δ > 0, ∀ s, |s| < δ → ∀ z ∈ sphere (0 : ℂ) 1, ‖hs s z - z - s * V z‖ ≤ ε * |s|) :
    (∃ B : ℝ, ∀ θ : ℝ, ‖V (exp (θ * I))‖ ≤ B) ∧ Continuous fun θ : ℝ => V (exp (θ * I)) := by
  have hz : ∀ θ : ℝ, exp (θ * I) ∈ sphere (0 : ℂ) 1 := fun θ => by
    rw [mem_sphere_zero_iff_norm, Complex.norm_exp_ofReal_mul_I]
  refine ⟨?_, ?_⟩
  · obtain ⟨δ, hδ, hδs⟩ := htan 1 one_pos
    set s : ℝ := min δ s₀ / 2 with hsdef
    have hs0 : 0 < s := by positivity
    have hsδ : |s| < δ := by rw [abs_of_pos hs0]; linarith [min_le_left δ s₀]
    have hss₀ : |s| < s₀ := by rw [abs_of_pos hs0]; linarith [min_le_right δ s₀]
    refine ⟨(2 + s) / s, fun θ => ?_⟩
    have h1 := hδs s hsδ _ (hz θ)
    have h2 := (hn s hss₀ θ).1
    have h3 : ‖exp (θ * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
    rw [le_div_iff₀ hs0]
    have h4 : ‖(s : ℂ) * V (exp (θ * I))‖ ≤ 2 + s := by
      calc ‖(s : ℂ) * V (exp (θ * I))‖ = ‖(hs s (exp (θ * I)) - exp (θ * I)) -
            (hs s (exp (θ * I)) - exp (θ * I) - s * V (exp (θ * I)))‖ := by ring_nf
        _ ≤ ‖hs s (exp (θ * I)) - exp (θ * I)‖ +
            ‖hs s (exp (θ * I)) - exp (θ * I) - s * V (exp (θ * I))‖ := norm_sub_le _ _
        _ ≤ (‖hs s (exp (θ * I))‖ + ‖exp (θ * I)‖) + 1 * |s| := add_le_add (norm_sub_le _ _) h1
        _ = 2 + s := by rw [h2, h3, abs_of_pos hs0]; ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0] at h4
    linarith
  · -- a uniform limit along `σ n = s₀/(n + 2)`
    set σ : ℕ → ℝ := fun n => s₀ / ((n : ℝ) + 2) with hσ
    have hσ0 : ∀ n, 0 < σ n := fun n => by positivity
    have hσs : ∀ n, |σ n| < s₀ := fun n => by
      rw [abs_of_pos (hσ0 n), hσ, div_lt_iff₀ (by positivity)]
      nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have hσlim : Tendsto σ atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat s₀).comp (tendsto_add_atTop_nat 2)
      refine this.congr fun n => ?_
      simp only [Function.comp_apply, hσ]
      push_cast
      ring
    set F : ℕ → ℝ → ℂ := fun n θ => (hs (σ n) (exp (θ * I)) - exp (θ * I)) / (σ n : ℂ) with hF
    have hFc : ∀ n, Continuous (F n) := fun n =>
      ((hn _ (hσs n) 0).2.sub (by fun_prop)).div_const _
    have hU : TendstoUniformly F (fun θ => V (exp (θ * I))) atTop := by
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      obtain ⟨δ, hδ, hδs⟩ := htan (ε / 2) (half_pos hε)
      filter_upwards [hσlim.eventually (gt_mem_nhds hδ)] with n hn θ
      have h1 := hδs (σ n) (by rw [abs_of_pos (hσ0 n)]; exact hn) _ (hz θ)
      have hc : (σ n : ℂ) ≠ 0 := by exact_mod_cast (hσ0 n).ne'
      have e : V (exp (θ * I)) - F n θ =
          -((hs (σ n) (exp (θ * I)) - exp (θ * I) - σ n * V (exp (θ * I))) / σ n) := by
        simp only [hF]
        field_simp
        ring
      rw [dist_eq_norm, e, norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hσ0 n),
        div_lt_iff₀ (hσ0 n)]
      rw [abs_of_pos (hσ0 n)] at h1
      nlinarith [hσ0 n]
    exact hU.continuous (Frequently.of_forall hFc)

/-- Helper for `thm16_5_a` (§16.6, Z4). The first-order expansion of a perturbed chord: if `e(s)/s → 0` then
`(|A + sB + e(s)| − |A|)/s → (Re A Re B + Im A Im B)/|A|` as `s → 0`, `s ≠ 0` (`A ≠ 0`). -/
theorem gl16_zyg_chord_lim {A B : ℂ} (hA : A ≠ 0) {e : ℝ → ℂ}
    (he : Tendsto (fun s => e s / s) (𝓝[≠] 0) (𝓝 0)) :
    Tendsto (fun s : ℝ => (‖A + s * B + e s‖ - ‖A‖) / s) (𝓝[≠] 0)
      (𝓝 ((A.re * B.re + A.im * B.im) / ‖A‖)) := by
  set q : ℝ → ℝ := fun s => ‖A‖ ^ 2 + 2 * s * (A.re * B.re + A.im * B.im) + s ^ 2 * ‖B‖ ^ 2 with hq
  have hsq : ∀ s : ℝ, ‖A + s * B‖ ^ 2 = q s := fun s => by
    simp only [hq]
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    ring
  have hqe : ∀ s : ℝ, ‖A + s * B‖ = √(q s) := fun s => by rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  have hA0 : 0 < ‖A‖ := norm_pos_iff.2 hA
  have hq0 : q 0 = ‖A‖ ^ 2 := by simp [hq]
  have hqd : HasDerivAt q (2 * (A.re * B.re + A.im * B.im)) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).const_mul (2 * (A.re * B.re + A.im * B.im))).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (‖B‖ ^ 2))).const_add (‖A‖ ^ 2)
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)).congr_deriv ?_
    · simp only [hq, id, Pi.add_apply, Pi.pow_apply]
      ring
    · simp
  have hfd : HasDerivAt (fun s => √(q s)) (2 * (A.re * B.re + A.im * B.im) / (2 * √(q 0))) 0 :=
    hqd.sqrt (by rw [hq0]; positivity)
  rw [hq0, Real.sqrt_sq hA0.le] at hfd
  have hslope := hasDerivAt_iff_tendsto_slope.1 hfd
  have hlim1 : Tendsto (fun s : ℝ => (‖A + s * B‖ - ‖A‖) / s) (𝓝[≠] 0)
      (𝓝 ((A.re * B.re + A.im * B.im) / ‖A‖)) := by
    have e1 : (2 * (A.re * B.re + A.im * B.im) / (2 * ‖A‖)) = (A.re * B.re + A.im * B.im) / ‖A‖ := by
      field_simp
    rw [← e1]
    refine hslope.congr' (eventually_nhdsWithin_of_forall fun s _ => ?_)
    rw [slope_def_field]
    show (√(q s) - √(q 0)) / (s - 0) = (‖A + s * B‖ - ‖A‖) / s
    rw [hqe s, hq0, Real.sqrt_sq hA0.le, sub_zero]
  -- the perturbation is `o(s)`
  have hdiff : Tendsto (fun s : ℝ => (‖A + s * B + e s‖ - ‖A‖) / s - (‖A + s * B‖ - ‖A‖) / s) (𝓝[≠] 0)
      (𝓝 0) := by
    refine squeeze_zero_norm (fun s => ?_) (by simpa using he.norm)
    rw [← sub_div, show ‖A + s * B + e s‖ - ‖A‖ - (‖A + s * B‖ - ‖A‖) = ‖A + s * B + e s‖ - ‖A + s * B‖ by ring]
    simp only [norm_div, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_right (abs_norm_sub_norm_le _ _ |>.trans (by rw [add_sub_cancel_left])) (abs_nonneg _)
  simpa using hlim1.add hdiff

/-- Helper for `thm16_5_a` (§16.6, Z4). The first-order chord expansion ((16.16), (16.17) at fixed `x`, `t`): if the
two chords of `h_s` at scale `t` differ by at most `K|s|` times the larger one for small `s ≠ 0`, then the first-order
coefficient `Re((V₊ − V₀)/(z₊ − z₀)) − Re((V₀ − V₋)/(z₀ − z₋))` is at most `K` in absolute value. -/
theorem gl16_zyg_core {s₁ : ℝ} (hs₁ : 0 < s₁) {hs : ℝ → ℂ → ℂ} {V : ℂ → ℂ}
    (htan : ∀ ε > 0, ∃ δ > 0, ∀ s, |s| < δ → ∀ z ∈ sphere (0 : ℂ) 1, ‖hs s z - z - s * V z‖ ≤ ε * |s|)
    {x t K : ℝ} (ht : Real.sin (t / 2) ≠ 0)
    (hK : ∀ s, s ≠ 0 → |s| < s₁ →
      |‖hs s (exp ((x + t) * I)) - hs s (exp (x * I))‖ - ‖hs s (exp (x * I)) - hs s (exp ((x - t) * I))‖| ≤
        K * |s| * max ‖hs s (exp ((x + t) * I)) - hs s (exp (x * I))‖
          ‖hs s (exp (x * I)) - hs s (exp ((x - t) * I))‖) :
    |((V (exp ((x + t) * I)) - V (exp (x * I))) / (exp ((x + t) * I) - exp (x * I))).re -
        ((V (exp (x * I)) - V (exp ((x - t) * I))) / (exp (x * I) - exp ((x - t) * I))).re| ≤ K := by
  set zp := exp (((x : ℂ) + t) * I) with hzp
  set z0 := exp ((x : ℂ) * I) with hz0
  set zm := exp (((x : ℂ) - t) * I) with hzm
  have hsph : ∀ θ : ℝ, exp ((θ : ℂ) * I) ∈ sphere (0 : ℂ) 1 := fun θ => by
    rw [mem_sphere_zero_iff_norm, Complex.norm_exp_ofReal_mul_I]
  have hzp1 : zp ∈ sphere (0 : ℂ) 1 := by rw [hzp, ← Complex.ofReal_add]; exact hsph _
  have hz01 : z0 ∈ sphere (0 : ℂ) 1 := hsph x
  have hzm1 : zm ∈ sphere (0 : ℂ) 1 := by rw [hzm, ← Complex.ofReal_sub]; exact hsph _
  set Ap := zp - z0 with hAp
  set Am := z0 - zm with hAm
  set Bp := V zp - V z0 with hBp
  set Bm := V z0 - V zm with hBm
  -- the two chords have the common length `L = 2|sin(t/2)| > 0`
  have hzpe : zp = z0 * exp (I * t) := by rw [hzp, hz0, ← Complex.exp_add]; ring_nf
  have hzme : zm = z0 * (exp (I * t))⁻¹ := by
    rw [hzm, hz0, ← Complex.exp_neg, ← Complex.exp_add]
    ring_nf
  have hz0n : ‖z0‖ = 1 := mem_sphere_zero_iff_norm.1 hz01
  have hEn : ‖exp (I * t)‖ = 1 := by
    rw [show I * (t : ℂ) = (t : ℂ) * I by ring, Complex.norm_exp_ofReal_mul_I]
  have hE0 : exp (I * t) ≠ 0 := Complex.exp_ne_zero _
  have hApn : ‖Ap‖ = ‖2 * Real.sin (t / 2)‖ := by
    rw [hAp, hzpe, show z0 * exp (I * t) - z0 = z0 * (exp (I * t) - 1) by ring, norm_mul, hz0n, one_mul,
      Complex.norm_exp_I_mul_ofReal_sub_one]
  have hAmn : ‖Am‖ = ‖2 * Real.sin (t / 2)‖ := by
    rw [hAm, hzme, show z0 - z0 * (exp (I * t))⁻¹ = z0 * (exp (I * t))⁻¹ * (exp (I * t) - 1) by
      field_simp, norm_mul, norm_mul, hz0n, one_mul, norm_inv, hEn, inv_one, one_mul,
      Complex.norm_exp_I_mul_ofReal_sub_one]
  set L := ‖2 * Real.sin (t / 2)‖ with hL
  have hL0 : 0 < L := by
    rw [hL, norm_pos_iff]
    exact mul_ne_zero two_ne_zero ht
  have hAp0 : Ap ≠ 0 := by
    intro h
    rw [h, norm_zero] at hApn
    linarith
  have hAm0 : Am ≠ 0 := by
    intro h
    rw [h, norm_zero] at hAmn
    linarith
  -- the error terms are `o(s)`
  have herr : ∀ z ∈ sphere (0 : ℂ) 1, Tendsto (fun s : ℝ => (hs s z - z - s * V z) / s) (𝓝[≠] 0) (𝓝 0) := by
    intro z hz
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hδs⟩ := htan (ε / 2) (half_pos hε)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hδ)] with s hs0 hsδ
    have hs0' : s ≠ 0 := hs0
    have hsδ' : |s| < δ := by simpa [Real.dist_eq] using hsδ
    have h1 := hδs s hsδ' z hz
    rw [dist_zero_right, norm_div, Complex.norm_real, Real.norm_eq_abs, div_lt_iff₀ (abs_pos.2 hs0')]
    nlinarith [abs_pos.2 hs0']
  have hep : Tendsto (fun s : ℝ => ((hs s zp - zp - s * V zp) - (hs s z0 - z0 - s * V z0)) / s) (𝓝[≠] 0)
      (𝓝 0) := by
    simpa [sub_div] using (herr zp hzp1).sub (herr z0 hz01)
  have hem : Tendsto (fun s : ℝ => ((hs s z0 - z0 - s * V z0) - (hs s zm - zm - s * V zm)) / s) (𝓝[≠] 0)
      (𝓝 0) := by
    simpa [sub_div] using (herr z0 hz01).sub (herr zm hzm1)
  have hNp := gl16_zyg_chord_lim (B := Bp) hAp0 hep
  have hNm := gl16_zyg_chord_lim (B := Bm) hAm0 hem
  have eN : ∀ s : ℝ, Ap + s * Bp + ((hs s zp - zp - s * V zp) - (hs s z0 - z0 - s * V z0)) = hs s zp - hs s z0 :=
    fun s => by rw [hAp, hBp]; ring
  have eD : ∀ s : ℝ, Am + s * Bm + ((hs s z0 - z0 - s * V z0) - (hs s zm - zm - s * V zm)) = hs s z0 - hs s zm :=
    fun s => by rw [hAm, hBm]; ring
  simp only [eN, eD] at hNp hNm
  rw [hApn] at hNp
  rw [hAmn] at hNm
  set N : ℝ → ℝ := fun s => ‖hs s zp - hs s z0‖ with hN
  set D : ℝ → ℝ := fun s => ‖hs s z0 - hs s zm‖ with hD
  -- `(N − D)/s → L c`
  have hND := (hNp.sub hNm).congr fun s => show _ = (N s - D s) / s by simp only [hN, hD]; ring
  -- `N, D → L`
  have hNL : Tendsto N (𝓝[≠] 0) (𝓝 L) := by
    have h1 : Tendsto (fun s : ℝ => s * ((N s - L) / s) + L) (𝓝[≠] 0) (𝓝 (0 * _ + L)) :=
      ((tendsto_id.mono_left nhdsWithin_le_nhds).mul hNp).add_const L
    rw [zero_mul, zero_add] at h1
    refine h1.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_)
    field_simp [show s ≠ 0 from hs]
    ring
  have hDL : Tendsto D (𝓝[≠] 0) (𝓝 L) := by
    have h1 : Tendsto (fun s : ℝ => s * ((D s - L) / s) + L) (𝓝[≠] 0) (𝓝 (0 * _ + L)) :=
      ((tendsto_id.mono_left nhdsWithin_le_nhds).mul hNm).add_const L
    rw [zero_mul, zero_add] at h1
    refine h1.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_)
    field_simp [show s ≠ 0 from hs]
    ring
  have hmax : Tendsto (fun s => K * max (N s) (D s)) (𝓝[≠] 0) (𝓝 (K * L)) := by
    have := (hNL.max hDL).const_mul K
    rwa [max_self] at this
  -- the bound in the limit
  have hev : ∀ᶠ s in 𝓝[≠] (0 : ℝ), |(N s - D s) / s| ≤ K * max (N s) (D s) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hs₁)] with s hs0 hsb
    have hs0' : s ≠ 0 := hs0
    have hsb' : |s| < s₁ := by simpa [Real.dist_eq] using hsb
    have h1 := hK s hs0' hsb'
    rw [abs_div, div_le_iff₀ (abs_pos.2 hs0')]
    calc _ ≤ K * |s| * max _ _ := h1
      _ = _ := by ring
  have hlim := le_of_tendsto_of_tendsto hND.abs hmax hev
  -- identify the limit
  have hre : ∀ A B : ℂ, A ≠ 0 → (B / A).re = (A.re * B.re + A.im * B.im) / ‖A‖ ^ 2 := fun A B hA => by
    rw [Complex.div_re, Complex.sq_norm, ← add_div]
    ring
  have hc : (Ap.re * Bp.re + Ap.im * Bp.im) / L - (Am.re * Bm.re + Am.im * Bm.im) / L =
      L * ((Bp / Ap).re - (Bm / Am).re) := by
    rw [hre _ _ hAp0, hre _ _ hAm0, hApn, hAmn]
    field_simp
  rw [hc, abs_mul, abs_of_pos hL0] at hlim
  show |(Bp / Ap).re - (Bm / Am).re| ≤ K
  nlinarith

/-- Helper for `thm16_5_a` (§16.6, Z8). From the first-order coefficient bound to the second difference:
`|a cos(t/2)/(2 sin(t/2))| ≤ K` gives `|a| ≤ 2Kt` for `0 < t ≤ π/2` (`tan(t/2) ≤ t`). -/
theorem gl16_zyg_d2_le {a K t : ℝ} (ht : 0 < t) (ht2 : t ≤ π / 2)
    (h : |a * Real.cos (t / 2) / (2 * Real.sin (t / 2))| ≤ K) : |a| ≤ 2 * K * t := by
  have hπ := Real.pi_lt_d2
  have hs : 0 < Real.sin (t / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hs' : Real.sin (t / 2) ≤ t / 2 := Real.sin_le (by linarith)
  have hc : 1 / 2 ≤ Real.cos (t / 2) := by
    have := Real.one_sub_sq_div_two_le_cos (x := t / 2)
    nlinarith
  rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.sin (t / 2)),
    abs_of_pos (by linarith : (0 : ℝ) < Real.cos (t / 2)), div_le_iff₀ (by positivity)] at h
  have h1 : |a| / 2 ≤ |a| * Real.cos (t / 2) := by nlinarith [abs_nonneg a]
  have hK0 : 0 ≤ K := by
    by_contra hneg
    push Not at hneg
    nlinarith [mul_nonneg (abs_nonneg a) (by linarith : (0 : ℝ) ≤ Real.cos (t / 2))]
  have h2 : K * (2 * Real.sin (t / 2)) ≤ K * t := mul_le_mul_of_nonneg_left (by linarith) hK0
  linarith

/-- Helper for `thm16_5_a` (§16.6, Z8). The second difference of `V` on `S¹` is `2π`-periodic and even in `t`. -/
theorem gl16_zyg_d2V_periodic (V : ℂ → ℂ) (θ t : ℝ) (n : ℤ) :
    ‖V (exp ((θ + (t + n * (2 * π))) * I)) + V (exp ((θ - (t + n * (2 * π))) * I)) - 2 * V (exp (θ * I))‖ =
      ‖V (exp ((θ + t) * I)) + V (exp ((θ - t) * I)) - 2 * V (exp (θ * I))‖ ∧
    ‖V (exp ((θ + -t) * I)) + V (exp ((θ - -t) * I)) - 2 * V (exp (θ * I))‖ =
      ‖V (exp ((θ + t) * I)) + V (exp ((θ - t) * I)) - 2 * V (exp (θ * I))‖ := by
  have hp : ∀ u : ℂ, ∀ m : ℤ, exp (u + m * (2 * π) * I) = exp u := fun u m => by
    rw [Complex.exp_add, show (m : ℂ) * (2 * π) * I = m * (2 * π * I) by ring, Complex.exp_int_mul_two_pi_mul_I,
      mul_one]
  constructor
  · have e1 : ((θ : ℂ) + ((t : ℂ) + (n : ℂ) * (2 * π))) * I = ((θ : ℂ) + t) * I + (n : ℂ) * (2 * π) * I := by ring
    have e2 : ((θ : ℂ) - ((t : ℂ) + (n : ℂ) * (2 * π))) * I = ((θ : ℂ) - t) * I + ((-n : ℤ) : ℂ) * (2 * π) * I := by
      rw [Int.cast_neg]
      ring
    rw [e1, e2, hp, hp]
  · rw [show (θ : ℂ) + -t = θ - t by ring, show (θ : ℂ) - -t = θ + t by ring, add_comm (V (exp ((θ - t) * I)))]

/-- Helper for `thm16_5_a` (§16.6, Z8). The Zygmund bound from the first-order coefficient bound
`|Δ²v cos(t/2)/(2 sin(t/2))| ≤ K` on `0 < t < π` and `|v| ≤ B` (reduce `t` mod `2π`; small and large `t`). -/
theorem gl16_zyg_bounded {V : ℂ → ℂ} (hreal : ∀ θ : ℝ, (V (exp (θ * I)) / (I * exp (θ * I))).im = 0) {v : ℝ → ℝ}
    (hv : ∀ θ : ℝ, V (exp (θ * I)) = I * exp (θ * I) * v θ) {B K : ℝ} (hB : ∀ θ, |v θ| ≤ B)
    (hK : ∀ x t : ℝ, 0 < t → t < π →
      |(v (x + t) + v (x - t) - 2 * v x) * Real.cos (t / 2) / (2 * Real.sin (t / 2))| ≤ K) :
    IsZygmundBoundedVF V := by
  have hπ := Real.pi_pos
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 1 one_pos (by linarith [Real.pi_gt_three]))
  have hVn : ∀ θ : ℝ, ‖V (exp (θ * I))‖ ≤ B := fun θ => by
    rw [hv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    exact hB θ
  set M := 2 * K + 4 * B + 8 * B / π with hM
  -- the bound for `0 ≤ t ≤ π`
  have hsmall : ∀ θ t : ℝ, 0 ≤ t → t ≤ π →
      ‖V (exp ((θ + t) * I)) + V (exp ((θ - t) * I)) - 2 * V (exp (θ * I))‖ ≤ M * t := by
    intro θ t ht0 htπ
    have hall : ‖V (exp ((θ + t) * I)) + V (exp ((θ - t) * I)) - 2 * V (exp (θ * I))‖ ≤ 4 * B := by
      have h1 := hVn (θ + t)
      have h2 := hVn (θ - t)
      have h3 := hVn θ
      push_cast at h1 h2
      calc _ ≤ ‖V (exp ((θ + t) * I)) + V (exp ((θ - t) * I))‖ + ‖2 * V (exp (θ * I))‖ := norm_sub_le _ _
        _ ≤ (‖V (exp ((θ + t) * I))‖ + ‖V (exp ((θ - t) * I))‖) + 2 * ‖V (exp (θ * I))‖ := by
            rw [norm_mul, Complex.norm_two]
            exact add_le_add (norm_add_le _ _) le_rfl
        _ ≤ (B + B) + 2 * B := by gcongr
        _ = 4 * B := by ring
    rcases le_or_gt t (π / 2) with h2 | h2
    · rcases eq_or_lt_of_le ht0 with h0 | h0
      · rw [← h0]
        simp only [Complex.ofReal_zero, add_zero, sub_zero, mul_zero]
        ring_nf
        simp
      have hd2 := gl16_zyg_d2_le h0 h2 (hK θ t h0 (by linarith))
      have hsd := gl16_zyg_second_diff hv θ t
      have hc := Real.one_sub_sq_div_two_le_cos (x := t)
      have hsin : |Real.sin t| ≤ t := (Real.abs_sin_le_abs).trans (le_of_eq (abs_of_pos h0))
      have hv1 : |v (θ + t) - v (θ - t)| ≤ 2 * B := by
        have := hB (θ + t)
        have := hB (θ - t)
        rw [abs_le] at *
        constructor <;> linarith
      have hvx := hB θ
      have h1c : 1 - Real.cos t ≤ t := by nlinarith [Real.pi_lt_d2]
      have e1 : 2 * |v θ| * (1 - Real.cos t) ≤ 2 * B * t :=
        mul_le_mul (by linarith) h1c (by linarith [Real.cos_le_one t]) (by positivity)
      have e2 : |Real.sin t| * |v (θ + t) - v (θ - t)| ≤ t * (2 * B) := mul_le_mul hsin hv1 (abs_nonneg _) ht0
      calc _ ≤ _ := hsd
        _ ≤ 2 * K * t + 2 * B * t + t * (2 * B) := by linarith
        _ ≤ M * t := by
            rw [hM]
            have : 0 ≤ 8 * B / π * t := by positivity
            nlinarith
    · calc _ ≤ 4 * B := hall
        _ = 8 * B / π * (π / 2) := by field_simp; ring
        _ ≤ 8 * B / π * t := by gcongr
        _ ≤ M * t := by
            rw [hM]
            nlinarith
  refine ⟨hreal, M, fun θ t => ?_⟩
  -- reduce `t` to `t' ∈ [−π, π]` with `|t'| ≤ |t|`
  set n : ℤ := round (t / (2 * π)) with hn
  set t' := t - n * (2 * π) with ht'
  have h2π : 0 < 2 * π := by positivity
  have hr1 : |t / (2 * π) - n| ≤ 1 / 2 := abs_sub_round _
  have hr2 : |t / (2 * π) - n| ≤ |t / (2 * π) - ((0 : ℤ) : ℝ)| := round_le _ 0
  have et : t' = 2 * π * (t / (2 * π) - n) := by rw [ht']; field_simp
  have ht'π : |t'| ≤ π := by
    rw [et, abs_mul, abs_of_pos h2π]
    nlinarith
  have ht't : |t'| ≤ |t| := by
    rw [et, abs_mul, abs_of_pos h2π]
    rw [Int.cast_zero, sub_zero, abs_div, abs_of_pos h2π] at hr2
    calc 2 * π * |t / (2 * π) - n| ≤ 2 * π * (|t| / (2 * π)) := by gcongr
      _ = |t| := by field_simp
  have hM0 : 0 ≤ M := by positivity
  obtain ⟨hper, hneg⟩ := gl16_zyg_d2V_periodic V θ t' n
  rw [show ((t' : ℂ) + (n : ℂ) * (2 * (π : ℂ))) = (t : ℂ) by rw [ht']; push_cast; ring] at hper
  rw [hper]
  rcases le_total 0 t' with h | h
  · calc _ ≤ M * t' := hsmall θ t' h (by linarith [le_abs_self t'])
      _ = M * |t'| := by rw [abs_of_nonneg h]
      _ ≤ M * |t| := by gcongr
  · rw [← hneg]
    calc _ ≤ M * -t' := by
          have := hsmall θ (-t') (by linarith) (by linarith [neg_abs_le t'])
          push_cast at this
          exact this
      _ = M * |t'| := by rw [abs_of_nonpos h]
      _ ≤ M * |t| := by gcongr

/-- Helper for `thm16_5_a` (§16.6, Z9). The vanishing Zygmund condition from the same bound with `K = |ε(t)|`,
`ε(t) → 0`, and the uniform continuity of `v` (`ε'(t) = sup_x ‖Δ²V(x, t)‖/t`). -/
theorem gl16_zyg_vanishing {V : ℂ → ℂ} (hZ : IsZygmundBoundedVF V) {v : ℝ → ℝ}
    (hv : ∀ θ : ℝ, V (exp (θ * I)) = I * exp (θ * I) * v θ) {B : ℝ} (hB : ∀ θ, |v θ| ≤ B)
    (hvu : UniformContinuous v) {ε : ℝ → ℝ}
    (hε : Tendsto ε (𝓝[>] 0) (𝓝 0))
    (hK : ∀ x t : ℝ, 0 < t → t < π →
      |(v (x + t) + v (x - t) - 2 * v x) * Real.cos (t / 2) / (2 * Real.sin (t / 2))| ≤ |ε t|) :
    IsZygmundVanishingVF V := by
  obtain ⟨hreal, M, hM⟩ := hZ
  have hπ := Real.pi_pos
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set Δ : ℝ → ℝ → ℝ := fun θ t =>
    ‖V (exp ((θ + t) * I)) + V (exp ((θ - t) * I)) - 2 * V (exp (θ * I))‖ with hΔ
  have hbdd : ∀ t : ℝ, 0 < t → BddAbove (Set.range fun θ => Δ θ t / t) := fun t ht =>
    ⟨M, by
      rintro _ ⟨θ, rfl⟩
      rw [div_le_iff₀ ht]
      have := hM θ t
      rwa [abs_of_pos ht] at this⟩
  refine ⟨⟨hreal, M, hM⟩, fun t => ⨆ θ : ℝ, Δ θ t / t, ?_, fun θ t ht => ?_⟩
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro η hη
    obtain ⟨δ₁, hδ₁, hδ₁s⟩ := Metric.tendsto_nhdsWithin_nhds.1 hε (η / 8) (by positivity)
    obtain ⟨δ₂, hδ₂, hδ₂s⟩ := Metric.uniformContinuous_iff.1 hvu (η / 4) (by positivity)
    refine ⟨min (min δ₁ (δ₂ / 2)) (min (η / (4 * B + 1)) (π / 2)), by positivity, fun t ht htd => ?_⟩
    have ht0 : 0 < t := ht
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0] at htd
    have htδ₁ : t < δ₁ := htd.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have htδ₂ : t < δ₂ / 2 := htd.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have htη : t < η / (4 * B + 1) := htd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have htπ : t < π / 2 := htd.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hεt : |ε t| < η / 8 := by
      have := hδ₁s ht (by rwa [Real.dist_eq, sub_zero, abs_of_pos ht0])
      rwa [Real.dist_eq, sub_zero] at this
    have hBt : B * t ≤ η / 4 := by
      rw [lt_div_iff₀ (by positivity)] at htη
      nlinarith
    -- the pointwise bound
    have hpt : ∀ θ : ℝ, Δ θ t / t ≤ 3 * η / 4 := by
      intro θ
      have hd2 := gl16_zyg_d2_le ht0 htπ.le (hK θ t ht0 (by linarith))
      have hsd := gl16_zyg_second_diff hv θ t
      have hc := Real.one_sub_sq_div_two_le_cos (x := t)
      have hsin : |Real.sin t| ≤ t := (Real.abs_sin_le_abs).trans (le_of_eq (abs_of_pos ht0))
      have hdist : dist (θ + t) (θ - t) < δ₂ := by
        rw [Real.dist_eq, show θ + t - (θ - t) = 2 * t by ring, abs_of_pos (by positivity)]
        linarith
      have hv1 : |v (θ + t) - v (θ - t)| < η / 4 := by
        have := hδ₂s hdist
        rwa [Real.dist_eq] at this
      have hvx := hB θ
      have h1c : 2 * |v θ| * (1 - Real.cos t) ≤ B * t * t := by nlinarith [abs_nonneg (v θ)]
      rw [div_le_iff₀ ht0]
      calc Δ θ t ≤ _ := hsd
        _ ≤ 2 * |ε t| * t + B * t * t + t * (η / 4) := by
            gcongr
        _ ≤ 3 * η / 4 * t := by nlinarith [abs_nonneg (ε t)]
    have hnn : 0 ≤ ⨆ θ : ℝ, Δ θ t / t :=
      (div_nonneg (norm_nonneg _) ht0.le).trans (le_ciSup (hbdd t ht0) 0)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    exact (ciSup_le hpt).trans_lt (by linarith)
  · have := le_ciSup (hbdd t ht) θ
    rwa [div_le_iff₀ ht] at this

/-- **Theorem 5** (§16.6, l. 12383), first part. The tangent vector `V` of a smooth curve `h_s` in QS through the
identity is in `Z`; if the curve is tangent to S to first order, `V ∈ Z₀`.
**[CORRECTION/reading]** The vanishing part assumes (16.1) for `h_s` at scale `t` with `M = 1 + |s| ε(t)`,
`ε(t) → 0` uniformly in `s` (the proof's use of a smooth curve in S, l. 12420–12428); "each `h_s` symmetric" does not
suffice. Counterexample: `v = χ(θ) θ log|θ|` mollified at scale `e^{−1/√|s|}` gives symmetric `C^∞` diffeomorphisms
`h_s(e^{iθ}) = e^{i(θ + s v_s(θ))}` with `M_s ≤ 1 + C|s|` and `h_s = id + sV + o(s)`, `V = i z v`, while
`(v(2t) + v(0) − 2v(t))/t = 2 log 2`, so `V ∉ Z₀`. The book's step fails because the `o(s)` of (16.16) becomes
`o(s)/t` in (16.17), so `ε_s(t)` cannot be chosen before `t → 0`. Not vacuous: the flow of a `C²` field satisfies the
hypothesis with `ε(t) = Ct`. -/
theorem thm16_5_a {s₀ : ℝ} (hs₀ : 0 < s₀) {hs : ℝ → ℂ → ℂ} {V : ℂ → ℂ} {C : ℝ}
    (hqs : ∀ s, |s| < s₀ → Pommerenke1992.IsSensePreservingCircleHomeo (hs s) ∧ IsMCondition (hs s) (1 + C * |s|))
    (h0 : ∀ z ∈ sphere (0 : ℂ) 1, hs 0 z = z)
    (htan : ∀ ε > 0, ∃ δ > 0, ∀ s, |s| < δ → ∀ z ∈ sphere (0 : ℂ) 1, ‖hs s z - z - s * V z‖ ≤ ε * |s|)
    (hreal : ∀ θ : ℝ, (V (exp (θ * I)) / (I * exp (θ * I))).im = 0) :
    IsZygmundBoundedVF V ∧
      ((∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧ ∀ s, |s| < s₀ → ∀ x t : ℝ, 0 < t → t < 2 * π →
          1 / (1 + |s| * ε t) ≤
              ‖hs s (exp ((x + t) * I)) - hs s (exp (x * I))‖ / ‖hs s (exp (x * I)) - hs s (exp ((x - t) * I))‖ ∧
            ‖hs s (exp ((x + t) * I)) - hs s (exp (x * I))‖ / ‖hs s (exp (x * I)) - hs s (exp ((x - t) * I))‖ ≤
              1 + |s| * ε t) →
        IsZygmundVanishingVF V) := by
  -- `h0` follows from `htan` (at `s = 0`); it is not needed separately
  have _h0 := h0
  -- the angular representative `v` of the tangent field
  set v : ℝ → ℝ := fun θ => (V (exp (θ * I)) / (I * exp (θ * I))).re with hvdef
  have hv : ∀ θ : ℝ, V (exp (θ * I)) = I * exp (θ * I) * v θ := by
    intro θ
    have hne : I * exp (θ * I) ≠ 0 := mul_ne_zero I_ne_zero (Complex.exp_ne_zero _)
    have h1 : V (exp (θ * I)) / (I * exp (θ * I)) = (v θ : ℂ) := by
      apply Complex.ext
      · simp only [hvdef, Complex.ofReal_re]
      · simp only [hvdef, Complex.ofReal_im, hreal θ]
    rw [← h1, mul_div_cancel₀ _ hne]
  have hn : ∀ s, |s| < s₀ → ∀ θ : ℝ, ‖hs s (exp (θ * I))‖ = 1 ∧ Continuous fun θ : ℝ => hs s (exp (θ * I)) :=
    fun s hs' θ => gl16_zyg_norm_eq_one (hqs s hs').1 θ
  obtain ⟨⟨B, hB⟩, hVc⟩ := gl16_zyg_V_bdd_cont hs₀ hn htan
  have hvB : ∀ θ, |v θ| ≤ B := by
    intro θ
    have h1 := hB θ
    rwa [hv θ, norm_mul, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul, one_mul,
      Complex.norm_real, Real.norm_eq_abs] at h1
  -- `v` is uniformly continuous
  have hvu : UniformContinuous v := by
    refine gl16_zyg_uniformContinuous ?_ fun θ => ?_
    · refine Complex.continuous_re.comp (hVc.div (continuous_const.mul (by fun_prop)) fun θ => ?_)
      exact mul_ne_zero I_ne_zero (Complex.exp_ne_zero _)
    · have he : exp (((θ + 2 * π : ℝ) : ℂ) * I) = exp ((θ : ℂ) * I) := by
        rw [show (((θ + 2 * π : ℝ) : ℂ) * I) = (θ : ℂ) * I + 2 * π * I by push_cast; ring, Complex.exp_add,
          Complex.exp_two_pi_mul_I, mul_one]
      simp only [hvdef, he]
  -- the chord estimate at a fixed scale `0 < t < π`
  have hchord : ∀ x t : ℝ, 0 < t → t < π → ∀ K s₁ : ℝ, 0 < s₁ →
      (∀ s, s ≠ 0 → |s| < s₁ → ∃ M : ℝ, 0 < M ∧ |M - 1| ≤ K * |s| ∧
        1 / M ≤ ‖hs s (exp ((x + t) * I)) - hs s (exp (x * I))‖ /
          ‖hs s (exp (x * I)) - hs s (exp ((x - t) * I))‖ ∧
        ‖hs s (exp ((x + t) * I)) - hs s (exp (x * I))‖ / ‖hs s (exp (x * I)) - hs s (exp ((x - t) * I))‖ ≤ M) →
      |(v (x + t) + v (x - t) - 2 * v x) * Real.cos (t / 2) / (2 * Real.sin (t / 2))| ≤ K := by
    intro x t ht0 htπ K s₁ hs₁ H
    have hsin : Real.sin (t / 2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
    rw [← gl16_zyg_re_quot hv hsin]
    refine gl16_zyg_core hs₁ htan hsin fun s hs0 hs1 => ?_
    obtain ⟨M, hM, hMK, h1, h2⟩ := H s hs0 hs1
    calc _ ≤ |M - 1| * max ‖hs s (exp ((x + t) * I)) - hs s (exp (x * I))‖
          ‖hs s (exp (x * I)) - hs s (exp ((x - t) * I))‖ := gl16_zyg_ratio (norm_nonneg _) (norm_nonneg _) hM h1 h2
      _ ≤ _ := mul_le_mul_of_nonneg_right hMK (le_max_of_le_left (norm_nonneg _))
  -- `0 < t < π` avoids the multiples of `2π`
  have hnk : ∀ t : ℝ, 0 < t → t < π → ∀ k : ℤ, t ≠ 2 * π * k := by
    intro t ht0 htπ k hk
    rcases le_or_gt k 0 with hk0 | hk0
    · have : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
      nlinarith [Real.pi_pos]
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
      nlinarith [Real.pi_pos]
  -- a ratio bound `1 + K|s|` with `K ≥ 0` is admissible for `|s| < min s₀ (1/(K + 1))`
  have hsmall : ∀ K s : ℝ, 0 ≤ K → |s| < 1 / (K + 1) → K * |s| < 1 := by
    intro K s hK hs'
    have h1 : K * |s| ≤ K * (1 / (K + 1)) := mul_le_mul_of_nonneg_left hs'.le hK
    have h2 : K * (1 / (K + 1)) < 1 := by
      rw [mul_one_div, div_lt_one (by linarith)]
      linarith
    linarith
  -- the Zygmund bound
  have hZ : IsZygmundBoundedVF V := by
    refine gl16_zyg_bounded hreal hv hvB (K := |C|) fun x t ht0 htπ => ?_
    refine hchord x t ht0 htπ |C| (min s₀ (1 / (|C| + 1))) (lt_min hs₀ (by positivity)) fun s _ hs1 => ?_
    have hs₀' : |s| < s₀ := lt_of_lt_of_le hs1 (min_le_left _ _)
    have hpos : |C| * |s| < 1 := hsmall |C| s (abs_nonneg C) (lt_of_lt_of_le hs1 (min_le_right _ _))
    have hM : 0 < 1 + C * |s| := by
      have := mul_le_mul_of_nonneg_right (neg_abs_le C) (abs_nonneg s)
      linarith
    obtain ⟨h1, h2⟩ := (hqs s hs₀').2 x t (hnk t ht0 htπ)
    refine ⟨1 + C * |s|, hM, ?_, h1, h2⟩
    rw [add_sub_cancel_left, abs_mul, abs_abs]
  refine ⟨hZ, fun hF1 => ?_⟩
  obtain ⟨ε, hε, hF⟩ := hF1
  -- the vanishing part, with the common witness `|s| ε(t)`
  refine gl16_zyg_vanishing hZ hv hvB hvu hε fun x t ht0 htπ => ?_
  refine hchord x t ht0 htπ |ε t| (min s₀ (1 / (|ε t| + 1))) (lt_min hs₀ (by positivity)) fun s _ hs1 => ?_
  have hs₀' : |s| < s₀ := lt_of_lt_of_le hs1 (min_le_left _ _)
  have hpos : |ε t| * |s| < 1 := hsmall |ε t| s (abs_nonneg _) (lt_of_lt_of_le hs1 (min_le_right _ _))
  have hM : 0 < 1 + |s| * ε t := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le (ε t)) (abs_nonneg s)
    nlinarith [abs_nonneg s, abs_nonneg (ε t)]
  obtain ⟨h1, h2⟩ := hF s hs₀' x t ht0 (by linarith [Real.pi_pos])
  refine ⟨1 + |s| * ε t, hM, ?_, h1, h2⟩
  rw [add_sub_cancel_left, abs_mul, abs_abs, mul_comm]

/-- **Theorem 5** (§16.6, l. 12383), second part. Every `V ∈ Z` is the tangent vector at the identity of a smooth
curve in QS, and every `V ∈ Z₀` of a smooth curve in S. -/
theorem thm16_5_b {V : ℂ → ℂ} (hV : IsZygmundBoundedVF V) :
    ∃ (s₀ C : ℝ) (hs : ℝ → ℂ → ℂ), 0 < s₀ ∧
      (∀ s, |s| < s₀ → Pommerenke1992.IsSensePreservingCircleHomeo (hs s) ∧ IsMCondition (hs s) (1 + C * |s|) ∧
        (IsZygmundVanishingVF V → HasVanishingRatioDistortion (hs s))) ∧
      (∀ z ∈ sphere (0 : ℂ) 1, hs 0 z = z) ∧
      ∀ ε > 0, ∃ δ > 0, ∀ s, |s| < δ → ∀ z ∈ sphere (0 : ℂ) 1, ‖hs s z - z - s * V z‖ ≤ ε * |s| := by
  sorry

/-- **Lemma 9** (§16.6, l. 12482). If `|V(x + t) + V(x − t) − 2V(x)| / t ≤ C` for all `x − t, x, x + t` in an interval,
then for `a < b` in it `(1/(b − a)) |(1/(b − a)) ∫_a^b V − ½ V(a) − ½ V(b)| ≤ C/2`. -/
theorem lemma16_9 {V : ℝ → ℝ} (hV : Continuous V) {p q C : ℝ}
    (hC : ∀ x t : ℝ, 0 < t → p ≤ x - t → x + t ≤ q → |V (x + t) + V (x - t) - 2 * V x| / t ≤ C)
    {a b : ℝ} (ha : p ≤ a) (hab : a < b) (hb : b ≤ q) :
    (1 / (b - a)) * |(1 / (b - a)) * ∫ x in a..b, V x - V a / 2 - V b / 2| ≤ C / 2 := by
  -- note: the integrand is `V x − V a / 2 − V b / 2`; the constant part integrates to `(b − a)(V a + V b)/2`
  set m := (a + b) / 2 with hm
  set h := (b - a) / 2 with hh
  have hh0 : 0 < h := by rw [hh]; linarith
  have hL : 0 < b - a := by linarith
  have hLne : b - a ≠ 0 := hL.ne'
  set D : ℝ → ℝ := fun s => V (m + s) + V (m - s) - 2 * V m with hD
  -- `|D s| ≤ C s` on `(0, h]`
  have hDle : ∀ s ∈ Ioc (0 : ℝ) h, |D s| ≤ C * s := by
    intro s hs
    have h1 := hC m s hs.1 (by rw [hm]; linarith [hs.2, hh]) (by rw [hm]; linarith [hs.2, hh])
    rwa [div_le_iff₀ hs.1] at h1
  have hC0 : 0 ≤ C := by
    have h1 := hDle h ⟨hh0, le_rfl⟩
    have h2 := abs_nonneg (D h)
    nlinarith
  -- integrability
  have hcont : ∀ u v : ℝ, IntervalIntegrable V volume u v := fun u v => hV.intervalIntegrable u v
  have hI1 : IntervalIntegrable (fun s => V (m + s)) volume 0 h :=
    (hV.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun s => V (m - s)) volume 0 h :=
    (hV.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
  -- the constant part of the integrand
  have hI : ∫ x in a..b, (V x - V a / 2 - V b / 2) = (∫ x in a..b, V x) - (b - a) * (V a / 2 + V b / 2) := by
    rw [intervalIntegral.integral_sub ((hcont a b).sub intervalIntegrable_const) intervalIntegrable_const,
      intervalIntegral.integral_sub (hcont a b) intervalIntegrable_const, intervalIntegral.integral_const,
      intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul]
    ring
  -- the integral over `[a, b]` folded at the midpoint
  have hsplit : ∫ x in a..b, V x = ∫ s in (0 : ℝ)..h, (V (m + s) + V (m - s)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hcont a m) (hcont m b)]
    have e1 : ∫ x in m..b, V x = ∫ s in (0 : ℝ)..h, V (m + s) := by
      rw [intervalIntegral.integral_comp_add_left V m, show m + 0 = m by ring, show m + h = b by rw [hm, hh]; ring]
    have e2 : ∫ x in a..m, V x = ∫ s in (0 : ℝ)..h, V (m - s) := by
      rw [intervalIntegral.integral_comp_sub_left V m, show m - 0 = m by ring, show m - h = a by rw [hm, hh]; ring]
    rw [e1, e2, ← intervalIntegral.integral_add hI2 hI1]
    congr 1
    funext s
    ring
  have hDint : ∫ s in (0 : ℝ)..h, (V (m + s) + V (m - s)) = (∫ s in (0 : ℝ)..h, D s) + (b - a) * V m := by
    have e : (fun s => V (m + s) + V (m - s)) = fun s => D s + 2 * V m := by
      funext s
      simp only [hD]
      ring
    rw [e, intervalIntegral.integral_add ((hI1.add hI2).sub intervalIntegrable_const) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero, hh]
    ring
  have hends : V a + V b = D h + 2 * V m := by
    simp only [hD]
    rw [show m + h = b by rw [hm, hh]; ring, show m - h = a by rw [hm, hh]; ring]
    ring
  -- the bound on the folded integral
  have hIbound : |∫ s in (0 : ℝ)..h, D s| ≤ C * h ^ 2 / 2 := by
    have h1 : ‖∫ s in (0 : ℝ)..h, D s‖ ≤ ∫ s in (0 : ℝ)..h, C * s := by
      refine intervalIntegral.norm_integral_le_of_norm_le hh0.le ?_ ?_
      · refine Eventually.of_forall fun s hs => ?_
        rw [Real.norm_eq_abs]
        exact hDle s hs
      · exact (continuous_const.mul continuous_id).intervalIntegrable _ _
    rw [intervalIntegral.integral_const_mul, integral_id, Real.norm_eq_abs] at h1
    calc |∫ s in (0 : ℝ)..h, D s| ≤ C * ((h ^ 2 - 0 ^ 2) / 2) := h1
      _ = C * h ^ 2 / 2 := by ring
  have hQ : (1 / (b - a)) * ∫ x in a..b, (V x - V a / 2 - V b / 2) =
      (1 / (b - a)) * (∫ s in (0 : ℝ)..h, D s) - D h / 2 := by
    rw [hI, hsplit, hDint]
    calc (1 / (b - a)) * ((∫ s in (0 : ℝ)..h, D s) + (b - a) * V m - (b - a) * (V a / 2 + V b / 2))
        = (1 / (b - a)) * (∫ s in (0 : ℝ)..h, D s) + (1 / (b - a) * (b - a)) * (V m - (V a / 2 + V b / 2)) := by
          ring
      _ = (1 / (b - a)) * (∫ s in (0 : ℝ)..h, D s) + (V m - (V a / 2 + V b / 2)) := by
          rw [one_div_mul_cancel hLne, one_mul]
      _ = (1 / (b - a)) * (∫ s in (0 : ℝ)..h, D s) - D h / 2 := by linarith [hends]
  rw [hQ]
  have hDh : |D h| ≤ C * h := hDle h ⟨hh0, le_rfl⟩
  have hinv : 0 < 1 / (b - a) := one_div_pos.2 hL
  have habs : |(1 / (b - a)) * (∫ s in (0 : ℝ)..h, D s) - D h / 2| ≤
      (1 / (b - a)) * (C * h ^ 2 / 2) + C * h / 2 := by
    calc _ ≤ |(1 / (b - a)) * (∫ s in (0 : ℝ)..h, D s)| + |D h / 2| := abs_sub _ _
      _ = (1 / (b - a)) * |∫ s in (0 : ℝ)..h, D s| + |D h| / 2 := by
          rw [abs_mul, abs_of_pos hinv, abs_div, abs_two]
      _ ≤ (1 / (b - a)) * (C * h ^ 2 / 2) + C * h / 2 := by
          have := mul_le_mul_of_nonneg_left hIbound hinv.le
          linarith
  have hval : (1 / (b - a)) * ((1 / (b - a)) * (C * h ^ 2 / 2) + C * h / 2) = 3 * C / 8 := by
    rw [hh]
    field_simp
    ring
  calc (1 / (b - a)) * |(1 / (b - a)) * (∫ s in (0 : ℝ)..h, D s) - D h / 2|
      ≤ (1 / (b - a)) * ((1 / (b - a)) * (C * h ^ 2 / 2) + C * h / 2) :=
        mul_le_mul_of_nonneg_left habs hinv.le
    _ = 3 * C / 8 := hval
    _ ≤ C / 2 := by linarith

/-- **Theorem 6** (§16.6, l. 12518). `QS mod S` is the complex manifold `AT(Δ)`: `Φ` induces a bijection of the left
cosets `S ∘ h` of QS onto `AT(Δ)`. -/
theorem thm16_6 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : LiZhongQC.IsFuchsian Γ)
    {p : UpperHalfPlane → unitDiscOpens} (hp : LiZhongQC.IsUniformization Γ p) :
    (∀ a : AsymTeichSpace unitDiscOpens p, ∃ (h : ℂ → ℂ) (μ : beltramiBall unitDiscOpens),
      Pommerenke1992.IsSensePreservingCircleHomeo h ∧ Pommerenke1992.IsQuasisymmetricA h ∧ IsQCExtCoeff h μ.1 ∧
        Quot.mk (asymRel p) μ = a) ∧
    ∀ (h₁ h₂ : ℂ → ℂ) (μ₁ μ₂ : beltramiBall unitDiscOpens), Pommerenke1992.IsSensePreservingCircleHomeo h₁ →
      Pommerenke1992.IsSensePreservingCircleHomeo h₂ → IsQCExtCoeff h₁ μ₁.1 → IsQCExtCoeff h₂ μ₂.1 →
      (Quot.mk (asymRel p) μ₁ = Quot.mk (asymRel p) μ₂ ↔
        ∃ s : ℂ → ℂ, Pommerenke1992.IsSensePreservingCircleHomeo s ∧ HasVanishingRatioDistortion s ∧
          ∀ z ∈ sphere (0 : ℂ) 1, s (h₂ z) = h₁ z) := by
  sorry

end GardinerLakic2000
