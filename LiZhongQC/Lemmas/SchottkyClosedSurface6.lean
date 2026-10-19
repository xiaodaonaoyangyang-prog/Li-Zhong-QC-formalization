import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Tactic

namespace LiZhongQC

/-- The edge-coordinate profile of a petal: `0` before the first copy `[E, E+1]` of the glued edge,
rising to `1` on it, constant `1` on the edge between the two copies, falling back to `0` on the second
copy `[E+2, E+3]`, and `0` afterwards (on one period `[0, 4p)`). -/
noncomputable def s78dg_cs_prof (E : ℝ) (u : ℝ) : ℝ :=
  min 1 (max 0 (u - E)) - min 1 (max 0 (u - (E + 2)))

theorem s78dg_cs_prof_cont (E : ℝ) : Continuous (s78dg_cs_prof E) := by
  unfold s78dg_cs_prof; fun_prop

theorem s78dg_cs_prof_zero {E u : ℝ} (h : u ≤ E) : s78dg_cs_prof E u = 0 := by
  unfold s78dg_cs_prof
  rw [min_eq_right (by simp only [max_def]; split_ifs <;> linarith),
    min_eq_right (by simp only [max_def]; split_ifs <;> linarith)]
  simp only [max_def]
  split_ifs <;> linarith

theorem s78dg_cs_prof_rise {E u : ℝ} (h0 : E ≤ u) (h1 : u ≤ E + 1) : s78dg_cs_prof E u = u - E := by
  unfold s78dg_cs_prof
  simp only [min_def, max_def]
  split_ifs <;> linarith

theorem s78dg_cs_prof_mid {E u : ℝ} (h0 : E + 1 ≤ u) (h1 : u ≤ E + 2) : s78dg_cs_prof E u = 1 := by
  unfold s78dg_cs_prof
  simp only [min_def, max_def]
  split_ifs <;> linarith

theorem s78dg_cs_prof_fall {E u : ℝ} (h0 : E + 2 ≤ u) (h1 : u ≤ E + 3) :
    s78dg_cs_prof E u = 1 - (u - (E + 2)) := by
  unfold s78dg_cs_prof
  simp only [min_def, max_def]
  split_ifs <;> linarith

theorem s78dg_cs_prof_end {E u : ℝ} (h : E + 3 ≤ u) : s78dg_cs_prof E u = 0 := by
  unfold s78dg_cs_prof
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- The starting vertex (as a real number) of the first copy of the edge of petal `m`. -/
noncomputable def s78dg_cs_E (m : ℕ) : ℝ := ((4 * (m / 2) + m % 2 : ℕ) : ℝ)

/-- The coordinate along the petal `m`, extended periodically (with period `4p`). -/
noncomputable def s78dg_cs_G (p m : ℕ) (u : ℝ) : ℝ :=
  s78dg_cs_prof (s78dg_cs_E m) ((4 * p : ℝ) * Int.fract (u / (4 * p)))

theorem s78dg_cs_G_on_period (p m : ℕ) (hp : 1 ≤ p) {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 4 * p) :
    s78dg_cs_G p m u = s78dg_cs_prof (s78dg_cs_E m) u := by
  have hN : (0 : ℝ) < 4 * p := by positivity
  unfold s78dg_cs_G
  rw [Int.fract_eq_self.2 ⟨by positivity, (div_lt_one hN).2 h1⟩]
  congr 1
  field_simp

theorem s78dg_cs_G_periodic (p m : ℕ) (u : ℝ) :
    s78dg_cs_G p m (u + 4 * p) = s78dg_cs_G p m u := by
  unfold s78dg_cs_G
  by_cases hp : (p : ℝ) = 0
  · simp [hp]
  have : (u + 4 * p) / (4 * p) = u / (4 * p) + 1 := by field_simp
  rw [this, Int.fract_add_one]

theorem s78dg_cs_G_cont (p m : ℕ) (hp : 1 ≤ p) (hm : m < 2 * p) : Continuous (s78dg_cs_G p m) := by
  have hN : (0 : ℝ) < 4 * p := by positivity
  have hE : s78dg_cs_E m + 3 ≤ 4 * p := by
    unfold s78dg_cs_E
    have : 4 * (m / 2) + m % 2 + 3 ≤ 4 * p := by omega
    exact_mod_cast this
  let f : ℝ → ℝ := fun t => s78dg_cs_prof (s78dg_cs_E m) ((4 * p : ℝ) * t)
  have hf : Continuous (f ∘ Int.fract) := by
    refine ContinuousOn.comp_fract'' ?_ ?_
    · exact ((s78dg_cs_prof_cont _).comp (continuous_const.mul continuous_id)).continuousOn
    · simp only [f]
      have h0 : (0 : ℝ) ≤ s78dg_cs_E m := by unfold s78dg_cs_E; positivity
      rw [mul_zero, mul_one, s78dg_cs_prof_zero h0, s78dg_cs_prof_end hE]
  have : s78dg_cs_G p m = (f ∘ Int.fract) ∘ fun u => u / (4 * p) := by
    funext u; rfl
  rw [this]
  exact hf.comp (continuous_id.div_const _)

theorem s78dg_cs_G_on_period_le (p m : ℕ) (hp : 1 ≤ p) (hm : m < 2 * p) {u : ℝ} (h0 : 0 ≤ u)
    (h1 : u ≤ 4 * p) : s78dg_cs_G p m u = s78dg_cs_prof (s78dg_cs_E m) u := by
  rcases eq_or_lt_of_le h1 with h | h
  · have hE : s78dg_cs_E m + 3 ≤ 4 * p := by
      unfold s78dg_cs_E
      have : 4 * (m / 2) + m % 2 + 3 ≤ 4 * p := by omega
      exact_mod_cast this
    have hE0 : (0 : ℝ) ≤ s78dg_cs_E m := by unfold s78dg_cs_E; positivity
    have h2 : s78dg_cs_G p m (0 + 4 * p) = s78dg_cs_G p m 0 := s78dg_cs_G_periodic p m 0
    subst h
    rw [zero_add] at h2
    rw [h2, s78dg_cs_G_on_period p m hp le_rfl (by positivity), s78dg_cs_prof_zero hE0,
      s78dg_cs_prof_end hE]
  · exact s78dg_cs_G_on_period p m hp h0 h

theorem s78dg_cs_coe_one : ((1 : ℝ) : AddCircle (1 : ℝ)) = 0 :=
  (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨1, by simp⟩

theorem s78dg_cs_G_glue_a (p m : ℕ) (hp : 1 ≤ p) (hm : m < 2 * p) (i : Fin p) (x : ℝ) (h0 : 0 ≤ x)
    (h1 : x ≤ 1) :
    ((s78dg_cs_G p m (4 * (i : ℝ) + x) : ℝ) : AddCircle (1 : ℝ)) =
      ((s78dg_cs_G p m (4 * (i : ℝ) + 3 - x) : ℝ) : AddCircle (1 : ℝ)) := by
  have hi : (i : ℕ) < p := i.2
  have hi' : (4 * (i : ℝ) + 4 ≤ 4 * p) := by
    have : (i : ℝ) + 1 ≤ p := by exact_mod_cast hi
    linarith
  have hi0 : (0 : ℝ) ≤ 4 * (i : ℝ) := by positivity
  rw [s78dg_cs_G_on_period_le p m hp hm (by linarith) (by linarith),
    s78dg_cs_G_on_period_le p m hp hm (by linarith) (by linarith)]
  have hcases : m = 2 * (i : ℕ) ∨ 4 * (m / 2) + m % 2 + 3 ≤ 4 * (i : ℕ) ∨
      4 * (i : ℕ) + 4 ≤ 4 * (m / 2) + m % 2 ∨ 4 * (m / 2) + m % 2 = 4 * (i : ℕ) + 1 := by omega
  rcases hcases with h | h | h | h
  · have hE : s78dg_cs_E m = 4 * (i : ℝ) := by
      unfold s78dg_cs_E
      have : 4 * (m / 2) + m % 2 = 4 * (i : ℕ) := by omega
      rw [this]; push_cast; ring
    rw [hE, s78dg_cs_prof_rise (by linarith) (by linarith),
      s78dg_cs_prof_fall (by linarith) (by linarith)]
    congr 1; ring
  · have hE : s78dg_cs_E m + 3 ≤ 4 * (i : ℝ) := by
      unfold s78dg_cs_E; exact_mod_cast h
    rw [s78dg_cs_prof_end (by linarith), s78dg_cs_prof_end (by linarith)]
  · have hE : 4 * (i : ℝ) + 4 ≤ s78dg_cs_E m := by
      unfold s78dg_cs_E; exact_mod_cast h
    rw [s78dg_cs_prof_zero (by linarith), s78dg_cs_prof_zero (by linarith)]
  · have hE : s78dg_cs_E m = 4 * (i : ℝ) + 1 := by
      unfold s78dg_cs_E; rw [h]; push_cast; ring
    rw [s78dg_cs_prof_zero (by linarith), hE, s78dg_cs_prof_mid (by linarith) (by linarith)]
    rw [s78dg_cs_coe_one]; simp

theorem s78dg_cs_G_glue_b (p m : ℕ) (hp : 1 ≤ p) (hm : m < 2 * p) (i : Fin p) (x : ℝ) (h0 : 0 ≤ x)
    (h1 : x ≤ 1) :
    ((s78dg_cs_G p m (4 * (i : ℝ) + 1 + x) : ℝ) : AddCircle (1 : ℝ)) =
      ((s78dg_cs_G p m (4 * (i : ℝ) + 4 - x) : ℝ) : AddCircle (1 : ℝ)) := by
  have hi : (i : ℕ) < p := i.2
  have hi' : (4 * (i : ℝ) + 4 ≤ 4 * p) := by
    have : (i : ℝ) + 1 ≤ p := by exact_mod_cast hi
    linarith
  have hi0 : (0 : ℝ) ≤ 4 * (i : ℝ) := by positivity
  rw [s78dg_cs_G_on_period_le p m hp hm (by linarith) (by linarith),
    s78dg_cs_G_on_period_le p m hp hm (by linarith) (by linarith)]
  have hcases : m = 2 * (i : ℕ) + 1 ∨ 4 * (m / 2) + m % 2 + 3 ≤ 4 * (i : ℕ) + 1 ∨
      4 * (i : ℕ) + 4 ≤ 4 * (m / 2) + m % 2 ∨ 4 * (m / 2) + m % 2 = 4 * (i : ℕ) := by omega
  rcases hcases with h | h | h | h
  · have hE : s78dg_cs_E m = 4 * (i : ℝ) + 1 := by
      unfold s78dg_cs_E
      have : 4 * (m / 2) + m % 2 = 4 * (i : ℕ) + 1 := by omega
      rw [this]; push_cast; ring
    rw [hE, s78dg_cs_prof_rise (by linarith) (by linarith),
      s78dg_cs_prof_fall (by linarith) (by linarith)]
    congr 1; ring
  · have hE : s78dg_cs_E m + 3 ≤ 4 * (i : ℝ) + 1 := by
      unfold s78dg_cs_E; exact_mod_cast h
    rw [s78dg_cs_prof_end (by linarith), s78dg_cs_prof_end (by linarith)]
  · have hE : 4 * (i : ℝ) + 4 ≤ s78dg_cs_E m := by
      unfold s78dg_cs_E; exact_mod_cast h
    rw [s78dg_cs_prof_zero (by linarith), s78dg_cs_prof_zero (by linarith)]
  · have hE : s78dg_cs_E m = 4 * (i : ℝ) := by
      unfold s78dg_cs_E; rw [h]; push_cast; ring
    rw [hE, s78dg_cs_prof_mid (u := 4 * (i : ℝ) + 1 + x) (by linarith) (by linarith),
      s78dg_cs_prof_end (u := 4 * (i : ℝ) + 4 - x) (by linarith)]
    rw [s78dg_cs_coe_one]; simp

end LiZhongQC
