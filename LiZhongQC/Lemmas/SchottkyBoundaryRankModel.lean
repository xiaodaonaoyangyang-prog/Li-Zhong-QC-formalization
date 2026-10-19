import LiZhongExternal.Classification.SchottkyClassification01
import Mathlib

/-!
# Boundary rank, B3: explicit circle-valued characters on the classification models

For the orientable model `Quot (OrientableRel p n)` (and the non-orientable one) and integer weights
`w i` on the `n` holes with `∑ w i = 0`, a continuous map to `AddCircle 1` which, along the free boundary
arc `h_i` of hole `i`, is the affine function `a i + w i * t`.

Construction: a real lift on the boundary parameter `u` (`u = N s`, `N = 4p+3n` resp. `2p+3n`), the sum of
clamped ramps `∑ j, w j * max 0 (min (u + 3 j + 2) 1)`, reduced to the window `(−1/2 − N, −1/2]`; it vanishes
on the `a`/`b` blocks and differs by the integer `w i` across the two copies of the spoke `c_i`.  It is
extended radially, `z ↦ ‖z‖ * Λ(arg z)`, to the closed disc, read in `AddCircle 1` and descended to the
quotient.
-/

open Complex Set Filter Topology LeanEval.Topology.ClassificationOfSurfaces

namespace LiZhongQC

/-- A continuous `1`-periodic function, read through `θ ↦ θ / (2π)`, is a continuous function on angles. -/
theorem s78rb_angle_lift (Λ : ℝ → ℝ) (hΛ : Continuous Λ) (hper : Function.Periodic Λ 1) :
    ∃ Θ : C(Real.Angle, ℝ), ∀ θ : ℝ, Θ (θ : Real.Angle) = Λ (θ / (2 * Real.pi)) := by
  have hφ : Function.Periodic (fun θ : ℝ => Λ (θ / (2 * Real.pi))) (2 * Real.pi) := by
    intro θ
    have h2 : (2 * Real.pi) ≠ 0 := by positivity
    simp only
    rw [add_div, div_self h2]
    exact hper _
  exact ⟨⟨fun θ : Real.Angle => hφ.lift θ,
    (hΛ.comp (continuous_id.div_const _)).quotient_liftOn' _⟩, fun θ => rfl⟩

/-- The angle of a boundary point of the disc. -/
theorem s78rb_arg_bdyPt (s : ℝ) :
    (arg ((ClosedUnitDisc.bdyPtOfReal s : ClosedUnitDisc) : ℂ) : Real.Angle) =
      ((2 * Real.pi * s : ℝ) : Real.Angle) := by
  have h : ((ClosedUnitDisc.bdyPtOfReal s : ClosedUnitDisc) : ℂ) =
      ((Real.Angle.cos ((2 * Real.pi * s : ℝ) : Real.Angle) : ℝ) : ℂ) +
        ((Real.Angle.sin ((2 * Real.pi * s : ℝ) : Real.Angle) : ℝ) : ℂ) * I := by
    show ((Real.fourierChar s : Circle) : ℂ) = _
    rw [Real.fourierChar_apply, exp_mul_I, Real.Angle.cos_coe, Real.Angle.sin_coe, ofReal_cos,
      ofReal_sin]
  rw [h]
  exact arg_cos_add_sin_mul_I_coe_angle _

/-- Boundary points of the disc have norm one. -/
theorem s78rb_norm_bdyPt (s : ℝ) :
    ‖((ClosedUnitDisc.bdyPtOfReal s : ClosedUnitDisc) : ℂ)‖ = 1 := by
  show ‖((Real.fourierChar s : Circle) : ℂ)‖ = 1
  rw [Real.fourierChar_apply]
  exact norm_exp_ofReal_mul_I _

/-- Radial extension: a continuous `1`-periodic function on the boundary parameter extends to a continuous
real function on the closed disc with the prescribed boundary values. -/
theorem s78rb_disc_extension (Λ : ℝ → ℝ) (hΛ : Continuous Λ) (hper : Function.Periodic Λ 1) :
    ∃ f : C(ClosedUnitDisc, ℝ), ∀ s : ℝ, f (ClosedUnitDisc.bdyPtOfReal s) = Λ s := by
  obtain ⟨Θ, hΘ⟩ := s78rb_angle_lift Λ hΛ hper
  obtain ⟨M, hM'⟩ := (isCompact_Icc (a := -Real.pi) (b := Real.pi)).exists_bound_of_continuousOn
    (hΛ.comp (continuous_id.div_const (2 * Real.pi))).continuousOn
  have hM : ∀ θ : Real.Angle, |Θ θ| ≤ M := by
    intro θ
    rw [← θ.coe_toReal, hΘ]
    exact hM' _ ⟨θ.neg_pi_lt_toReal.le, θ.toReal_le_pi⟩
  let g : ℂ → ℝ := fun z => ‖z‖ * Θ (arg z : Real.Angle)
  have hg : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z = 0
    · subst hz
      have hg0 : g 0 = 0 := by simp [g]
      rw [ContinuousAt, hg0]
      have hb : ∀ w : ℂ, ‖g w‖ ≤ ‖w‖ * M := by
        intro w
        simp only [g, norm_mul, Real.norm_eq_abs, abs_norm]
        exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      refine squeeze_zero_norm hb ?_
      have : Continuous fun w : ℂ => ‖w‖ * M := continuous_norm.mul continuous_const
      simpa using this.tendsto 0
    · exact continuous_norm.continuousAt.mul
        (Θ.continuous.continuousAt.comp (continuousAt_arg_coe_angle hz))
  refine ⟨⟨fun z => g z, hg.comp continuous_subtype_val⟩, fun s => ?_⟩
  show ‖((ClosedUnitDisc.bdyPtOfReal s : ClosedUnitDisc) : ℂ)‖ *
      Θ (arg ((ClosedUnitDisc.bdyPtOfReal s : ClosedUnitDisc) : ℂ) : Real.Angle) = Λ s
  rw [s78rb_norm_bdyPt, s78rb_arg_bdyPt, hΘ, one_mul]
  congr 1
  field_simp

/-- A circle-valued map on the disc that agrees on related points descends to the quotient. -/
theorem s78rb_descend (R : ClosedUnitDisc → ClosedUnitDisc → Prop) (f : C(ClosedUnitDisc, AddCircle (1 : ℝ)))
    (hf : ∀ x y, R x y → f x = f y) :
    ∃ χ : C(Quot R, AddCircle (1 : ℝ)), ∀ x, χ (Quot.mk R x) = f x :=
  ⟨⟨Quot.lift f hf, continuous_quot_lift _ f.continuous⟩, fun _ => rfl⟩

/-- The ramp sum: the boundary lift before reduction to the window. -/
theorem s78rb_ramp_continuous {n : ℕ} (w : Fin n → ℤ) :
    Continuous fun v : ℝ => ∑ j : Fin n, (w j : ℝ) * max 0 (min (v + 3 * (j : ℝ) + 2) 1) := by
  fun_prop

/-- The ramp sum vanishes to the left of all holes. -/
theorem s78rb_ramp_left {n : ℕ} (w : Fin n → ℤ) (v : ℝ) (hv : v ≤ -3 * (n : ℝ)) :
    ∑ j : Fin n, (w j : ℝ) * max 0 (min (v + 3 * (j : ℝ) + 2) 1) = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  have hj : ((j : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast (show (j : ℕ) + 1 ≤ n from j.isLt)
  have : v + 3 * (j : ℝ) + 2 ≤ 0 := by linarith
  rw [max_eq_left (le_trans (min_le_left _ _) this), mul_zero]

/-- The ramp sum vanishes to the right of all holes (where every ramp is `1`), since `∑ w = 0`. -/
theorem s78rb_ramp_right {n : ℕ} (w : Fin n → ℤ) (hw : ∑ i, w i = 0) (v : ℝ) (hv : -1 ≤ v) :
    ∑ j : Fin n, (w j : ℝ) * max 0 (min (v + 3 * (j : ℝ) + 2) 1) = 0 := by
  have h : ∀ j : Fin n, max 0 (min (v + 3 * (j : ℝ) + 2) 1) = 1 := by
    intro j
    have : (0 : ℝ) ≤ (j : ℝ) := by positivity
    rw [min_eq_right (by linarith), max_eq_right zero_le_one]
  simp only [h, mul_one]
  exact_mod_cast hw

/-- Value of the ramp sum on the hole block `i`, at parameter `v = t − (3 i + 2)` with `t ∈ [−1, 2]`:
the ramps `j < i` vanish, the ramps `j > i` are `1`, the ramp `i` is clamped `t`. -/
theorem s78rb_ramp_hole {n : ℕ} (w : Fin n → ℤ) (i : Fin n) (t : ℝ) (ht0 : -1 ≤ t) (ht1 : t ≤ 2) :
    ∑ j : Fin n, (w j : ℝ) * max 0 (min ((t - (3 * (i : ℝ) + 2)) + 3 * (j : ℝ) + 2) 1) =
      (w i : ℝ) * max 0 (min t 1) + ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), (w j : ℝ) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Finset.sum_filter,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  · rw [show t - (3 * (i : ℝ) + 2) + 3 * (i : ℝ) + 2 = t by ring]
  · rw [if_neg (lt_irrefl i), zero_add]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    rcases lt_or_gt_of_ne hji with h | h
    · have hlt : (j : ℝ) + 1 ≤ i := by exact_mod_cast (show (j : ℕ) + 1 ≤ i from h)
      have : t - (3 * (i : ℝ) + 2) + 3 * (j : ℝ) + 2 ≤ 0 := by linarith
      rw [max_eq_left (le_trans (min_le_left _ _) this), mul_zero, if_neg (not_lt.mpr h.le)]
    · have hlt : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show (i : ℕ) + 1 ≤ j from h)
      have : 1 ≤ t - (3 * (i : ℝ) + 2) + 3 * (j : ℝ) + 2 := by linarith
      rw [min_eq_right this, max_eq_right zero_le_one, mul_one, if_pos h]

/-- The reduced boundary lift: the ramp sum read in the window `(−1/2 − N, −1/2]`.  It is continuous and
`N`-periodic when the ramp sum vanishes on `(−∞, −3n] ∪ [−1, ∞)` and `N ≥ 3n`. -/
theorem s78rb_window_lift {n : ℕ} (w : Fin n → ℤ) (hw : ∑ i, w i = 0) (hn : 1 ≤ n) (N : ℝ) (hN : 0 < N)
    (h1N : 1 ≤ N) (hNn : 3 * (n : ℝ) ≤ N) :
    let G : ℝ → ℝ := fun v => ∑ j : Fin n, (w j : ℝ) * max 0 (min (v + 3 * (j : ℝ) + 2) 1)
    Continuous (fun u => G (toIocMod hN (-1 / 2 - N) u)) ∧
      Function.Periodic (fun u => G (toIocMod hN (-1 / 2 - N) u)) N ∧
      (∀ u, -3 * (n : ℝ) ≤ u → u ≤ 0 → G (toIocMod hN (-1 / 2 - N) u) = G u) ∧
      ∀ u, 0 ≤ u → u ≤ N - 3 * (n : ℝ) → G (toIocMod hN (-1 / 2 - N) u) = 0 := by
  intro G
  have hGc : Continuous G := s78rb_ramp_continuous w
  have hGl : ∀ v, v ≤ -3 * (n : ℝ) → G v = 0 := s78rb_ramp_left w
  have hGr : ∀ v, -1 ≤ v → G v = 0 := s78rb_ramp_right w hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro u
    by_cases hu : u ≡ (-1 / 2 - N) [PMOD N]
    · -- near the cut both one-sided values of the window reduction lie where the ramp sum vanishes
      obtain ⟨k, hk⟩ := AddCommGroup.modEq_iff_zsmul'.mp hu
      have hzero : ∀ᶠ v in 𝓝 u, G (toIocMod hN (-1 / 2 - N) v) = 0 := by
        have hev : ∀ᶠ v in 𝓝 u, |v - u| < 1 / 4 :=
          Filter.eventually_of_mem (Metric.ball_mem_nhds u (by norm_num : (0 : ℝ) < 1 / 4))
            fun v hv => by simpa [Real.dist_eq] using hv
        filter_upwards [hev] with v hv
        have hmem := toIocMod_mem_Ioc hN (-1 / 2 - N) v
        obtain ⟨m, hm⟩ : ∃ m : ℤ, toIocMod hN (-1 / 2 - N) v = v - m • N :=
          ⟨toIocDiv hN (-1 / 2 - N) v, rfl⟩
        rw [hm] at hmem ⊢
        rw [zsmul_eq_mul] at hmem ⊢
        rw [zsmul_eq_mul] at hk
        obtain ⟨hδ1, hδ2⟩ := abs_lt.mp hv
        -- with `d = −1 − k − m`, `v − m N = −1/2 + (v − u) + d N`, and the window forces `d ∈ {0, −1}`
        set d : ℤ := -1 - k - m with hd
        have hdR : (d : ℝ) = -1 - k - m := by rw [hd]; push_cast; ring
        have hr : v - (m : ℝ) * N = -1 / 2 + (v - u) + (d : ℝ) * N := by
          rw [hdR]; linear_combination (-1 : ℝ) * hk
        have hup : (d : ℝ) * N ≤ -(v - u) := by linarith [hmem.2]
        have hlo : -N - (v - u) < (d : ℝ) * N := by linarith [hmem.1]
        have hd1 : d ≤ 0 := by
          by_contra h
          have h' : (1 : ℝ) ≤ d := by exact_mod_cast (show (1 : ℤ) ≤ d by omega)
          nlinarith
        have hd2 : -1 ≤ d := by
          by_contra h
          have h' : (d : ℝ) ≤ -2 := by exact_mod_cast (show d ≤ -2 by omega)
          nlinarith
        rcases (show d = 0 ∨ d = -1 by omega) with h0 | h0
        · rw [hr, h0]
          apply hGr
          push_cast
          linarith
        · rw [hr, h0]
          apply hGl
          push_cast
          linarith
      exact (continuousAt_const (y := (0 : ℝ))).congr (hzero.mono fun v hv => hv.symm)
    · exact hGc.continuousAt.comp (continuousAt_toIocMod hN (-1 / 2 - N) hu)
  · intro u
    show G (toIocMod hN (-1 / 2 - N) (u + N)) = G (toIocMod hN (-1 / 2 - N) u)
    rw [toIocMod_add_right]
  · intro u hu0 hu1
    by_cases hu : u ≤ -1 / 2
    · rw [(toIocMod_eq_self hN).mpr ⟨by linarith, by linarith⟩]
    · have hred : toIocMod hN (-1 / 2 - N) u = u - N := by
        rw [← toIocMod_sub_zsmul hN _ u 1, one_zsmul]
        exact (toIocMod_eq_self hN).mpr ⟨by linarith, by linarith⟩
      rw [hred, hGl _ (by linarith), hGr _ (by linarith)]
  · intro u hu0 hu1
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hred : toIocMod hN (-1 / 2 - N) u = u - N := by
      rw [← toIocMod_sub_zsmul hN _ u 1, one_zsmul]
      exact (toIocMod_eq_self hN).mpr ⟨by linarith, by linarith⟩
    rw [hred, hGl _ (by linarith)]

/-- An integer is zero in `AddCircle 1`. -/
theorem s78rb_int_coe (k : ℤ) : (((k : ℝ)) : AddCircle (1 : ℝ)) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨k, by simp⟩

/-- The common construction.  `N` is the model's boundary length (`4p+3n` or `2p+3n`).  The relation's
pairs are of two kinds: two points of the zero region `u ∈ [0, N − 3n]`, or the two copies
`u = −(3i+x)`, `u = −(3i+3−x)` of a spoke.  Then the reduced ramp lift descends to a circle-valued map with
the prescribed values along the free arcs. -/
theorem s78rb_model_character {n : ℕ} (w : Fin n → ℤ) (hw : ∑ i, w i = 0) (hn : 1 ≤ n)
    (N : ℝ) (hNn : 3 * (n : ℝ) ≤ N) (R : ClosedUnitDisc → ClosedUnitDisc → Prop)
    (hR : ∀ x y, R x y →
      (∃ u v : ℝ, 0 ≤ u ∧ u ≤ N - 3 * n ∧ 0 ≤ v ∧ v ≤ N - 3 * n ∧
        x = ClosedUnitDisc.bdyPtOfReal (u / N) ∧ y = ClosedUnitDisc.bdyPtOfReal (v / N)) ∨
      (∃ (i : Fin n) (s : ℝ), 0 ≤ s ∧ s ≤ 1 ∧
        x = ClosedUnitDisc.bdyPtOfReal (-(3 * (i : ℝ) + s) / N) ∧
        y = ClosedUnitDisc.bdyPtOfReal (-(3 * (i : ℝ) + 3 - s) / N))) :
    ∃ χ : C(Quot R, AddCircle (1 : ℝ)), ∃ a : Fin n → ℝ,
      ∀ (i : Fin n) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
        χ (Quot.mk _ (ClosedUnitDisc.bdyPtOfReal ((t - (3 * (i : ℝ) + 2)) / N))) =
          ((a i + w i * t : ℝ) : AddCircle (1 : ℝ)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : 0 < N := by linarith
  have h1N : 1 ≤ N := by linarith
  obtain ⟨hc, hper, hval, hzero⟩ := s78rb_window_lift w hw hn N hN h1N (by linarith)
  set G : ℝ → ℝ := fun v => ∑ j : Fin n, (w j : ℝ) * max 0 (min (v + 3 * (j : ℝ) + 2) 1) with hG
  set H : ℝ → ℝ := fun u => G (toIocMod hN (-1 / 2 - N) u) with hH
  have hHc : Continuous H := hc
  have hval' : ∀ u, -3 * (n : ℝ) ≤ u → u ≤ 0 → H u = G u := hval
  have hzero' : ∀ u, 0 ≤ u → u ≤ N - 3 * (n : ℝ) → H u = 0 := hzero
  let Λ : ℝ → ℝ := fun s => H (N * s)
  have hΛc : Continuous Λ := hHc.comp (continuous_const.mul continuous_id)
  have hΛp : Function.Periodic Λ 1 := by
    intro s
    show H (N * (s + 1)) = H (N * s)
    rw [mul_add, mul_one]
    exact hper (N * s)
  obtain ⟨f, hf⟩ := s78rb_disc_extension Λ hΛc hΛp
  let f' : C(ClosedUnitDisc, AddCircle (1 : ℝ)) :=
    ⟨fun z => ((f z : ℝ) : AddCircle (1 : ℝ)), (AddCircle.continuous_mk' 1).comp f.continuous⟩
  have hf' : ∀ u : ℝ, f' (ClosedUnitDisc.bdyPtOfReal (u / N)) = ((H u : ℝ) : AddCircle (1 : ℝ)) := by
    intro u
    show ((f (ClosedUnitDisc.bdyPtOfReal (u / N)) : ℝ) : AddCircle (1 : ℝ)) = _
    rw [hf]
    show ((H (N * (u / N)) : ℝ) : AddCircle (1 : ℝ)) = _
    rw [mul_div_cancel₀ u hN.ne']
  have hcompat : ∀ x y, R x y → f' x = f' y := by
    intro x y hxy
    rcases hR x y hxy with ⟨u, v, hu0, hu1, hv0, hv1, rfl, rfl⟩ | ⟨i, s, hs0, hs1, rfl, rfl⟩
    · rw [hf', hf', hzero' u hu0 hu1, hzero' v hv0 hv1]
    · have hi : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast (show (i : ℕ) + 1 ≤ n from i.isLt)
      have hi0 : (0 : ℝ) ≤ (i : ℝ) := by positivity
      rw [hf', hf', hval' _ (by linarith) (by linarith), hval' _ (by linarith) (by linarith)]
      have e1 : -(3 * (i : ℝ) + s) = (2 - s) - (3 * (i : ℝ) + 2) := by ring
      have e2 : -(3 * (i : ℝ) + 3 - s) = (s - 1) - (3 * (i : ℝ) + 2) := by ring
      rw [e1, e2]
      simp only [hG]
      rw [s78rb_ramp_hole w i (2 - s) (by linarith) (by linarith),
        s78rb_ramp_hole w i (s - 1) (by linarith) (by linarith)]
      rw [min_eq_right (by linarith : (1 : ℝ) ≤ 2 - s), max_eq_right zero_le_one,
        max_eq_left (le_trans (min_le_left _ _) (by linarith : s - 1 ≤ 0)), mul_one, mul_zero,
        zero_add, AddCircle.coe_add, s78rb_int_coe, zero_add]
  obtain ⟨χ, hχ⟩ := s78rb_descend R f' hcompat
  refine ⟨χ, fun i => ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), (w j : ℝ), fun i t ht => ?_⟩
  have hi : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast (show (i : ℕ) + 1 ≤ n from i.isLt)
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := by positivity
  rw [hχ, hf', hval' _ (by linarith [ht.1, ht.2]) (by linarith [ht.1, ht.2])]
  simp only [hG]
  rw [s78rb_ramp_hole w i t (by linarith [ht.1]) (by linarith [ht.2]), min_eq_left ht.2,
    max_eq_right ht.1, add_comm]

/-- **B3, orientable model.**  Integer weights on the holes summing to zero give a continuous map
`Quot (OrientableRel p n) → AddCircle 1` which is affine of slope `w i` along the free arc of hole `i`. -/
theorem s78rb_orientable_character (p n : ℕ) (w : Fin n → ℤ) (hw : ∑ i, w i = 0) :
    ∃ χ : C(Quot (OrientableRel p n), AddCircle (1 : ℝ)), ∃ a : Fin n → ℝ,
      ∀ (i : Fin n) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
        χ (Quot.mk _ (ClosedUnitDisc.bdyPtOfReal ((t - (3 * (i : ℝ) + 2)) / (4 * p + 3 * n)))) =
          ((a i + w i * t : ℝ) : AddCircle (1 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨ContinuousMap.const _ 0, fun i => i.elim0, fun i => i.elim0⟩
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) ≤ p := by positivity
  refine s78rb_model_character w hw hn (4 * p + 3 * n) (by linarith) _ ?_
  intro x y hxy
  cases hxy with
  | a x i =>
      left
      have hi : ((i : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast (show (i : ℕ) + 1 ≤ p from i.isLt)
      have hi0 : (0 : ℝ) ≤ (i : ℝ) := by positivity
      exact ⟨4 * i + x, 4 * i + 3 - x, by linarith [x.2.1], by linarith [x.2.2], by linarith [x.2.2],
        by linarith [x.2.1], rfl, rfl⟩
  | b x i =>
      left
      have hi : ((i : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast (show (i : ℕ) + 1 ≤ p from i.isLt)
      have hi0 : (0 : ℝ) ≤ (i : ℝ) := by positivity
      exact ⟨4 * i + 1 + x, 4 * i + 4 - x, by linarith [x.2.1], by linarith [x.2.2],
        by linarith [x.2.2], by linarith [x.2.1], rfl, rfl⟩
  | c x i =>
      right
      exact ⟨i, x, x.2.1, x.2.2, rfl, rfl⟩

/-- **B3, non-orientable model.**  The same for `Quot (NonOrientableRel p n)`. -/
theorem s78rb_nonorientable_character (p n : ℕ) (w : Fin n → ℤ) (hw : ∑ i, w i = 0) :
    ∃ χ : C(Quot (NonOrientableRel p n), AddCircle (1 : ℝ)), ∃ a : Fin n → ℝ,
      ∀ (i : Fin n) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
        χ (Quot.mk _ (ClosedUnitDisc.bdyPtOfReal ((t - (3 * (i : ℝ) + 2)) / (2 * p + 3 * n)))) =
          ((a i + w i * t : ℝ) : AddCircle (1 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨ContinuousMap.const _ 0, fun i => i.elim0, fun i => i.elim0⟩
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) ≤ p := by positivity
  refine s78rb_model_character w hw hn (2 * p + 3 * n) (by linarith) _ ?_
  intro x y hxy
  cases hxy with
  | a x i =>
      left
      have hi : ((i : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast (show (i : ℕ) + 1 ≤ p from i.isLt)
      have hi0 : (0 : ℝ) ≤ (i : ℝ) := by positivity
      exact ⟨2 * i + x, 2 * i + 1 + x, by linarith [x.2.1], by linarith [x.2.2], by linarith [x.2.1],
        by linarith [x.2.2], rfl, rfl⟩
  | c x i =>
      right
      exact ⟨i, x, x.2.1, x.2.2, rfl, rfl⟩

end LiZhongQC
