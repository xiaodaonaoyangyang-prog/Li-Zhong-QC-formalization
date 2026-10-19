import Mathlib

/-! Independent numerical Hurwitz step. Source-only candidate for Root compilation. -/

namespace LiZhongQC

/-- A positive integral lower bound on a branch order gives the reciprocal bound.
The positivity hypothesis excludes the zero-denominator convention. -/
theorem h84_reciprocal_le {k e : ℕ} (hk : 0 < k) (he : k ≤ e) :
    1 / (e : ℝ) ≤ 1 / (k : ℝ) := by
  exact one_div_le_one_div_of_le (by exact_mod_cast hk) (by exact_mod_cast he)

/-- Every genuine branch order contributes at least one half. -/
theorem h84_branch_term_half {e : ℕ} (he : 2 ≤ e) :
    (1 / 2 : ℝ) ≤ 1 - 1 / (e : ℝ) := by
  have h := h84_reciprocal_le (by norm_num : 0 < (2 : ℕ)) he
  norm_num at h
  simp only [one_div] at *
  linarith

/-- The (2,3,c) triangle is positive only for c at least seven. -/
theorem h84_two_three_defect {c : ℕ} (hc : 2 ≤ c)
    (hd : 0 < 1 - ((1 / 2 : ℝ) + 1 / 3 + 1 / (c : ℝ))) :
    (1 / 42 : ℝ) ≤ 1 - ((1 / 2 : ℝ) + 1 / 3 + 1 / (c : ℝ)) := by
  have hc7 : 7 ≤ c := by
    by_contra h
    have hc6 : c ≤ 6 := by omega
    have hc0 : (0 : ℝ) < c := by
      exact_mod_cast (show 0 < c by omega)
    have hrec : (1 / 6 : ℝ) ≤ 1 / (c : ℝ) :=
      one_div_le_one_div_of_le hc0 (by exact_mod_cast hc6)
    simp only [one_div] at *
    linarith
  have hrec := h84_reciprocal_le (by norm_num : 0 < (7 : ℕ)) hc7
  norm_num at hrec
  simp only [one_div] at *
  linarith

/-- The positive (2,b,c) defect is at least 1/42, without an ordering assumption. -/
theorem h84_two_branch_defect {b c : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 0 < 1 - ((1 / 2 : ℝ) + 1 / (b : ℝ) + 1 / (c : ℝ))) :
    (1 / 42 : ℝ) ≤ 1 - ((1 / 2 : ℝ) + 1 / (b : ℝ) + 1 / (c : ℝ)) := by
  have hb0 : (0 : ℝ) < b := by
    exact_mod_cast (show 0 < b by omega)
  have hc0 : (0 : ℝ) < c := by
    exact_mod_cast (show 0 < c by omega)
  have hb3 : 3 ≤ b := by
    by_contra h
    have hb2 : b = 2 := by omega
    have hrec : (0 : ℝ) < 1 / (c : ℝ) := one_div_pos.mpr hc0
    norm_num [hb2] at hd
    simp only [one_div] at *
    linarith
  have hc3 : 3 ≤ c := by
    by_contra h
    have hc2 : c = 2 := by omega
    have hrec : (0 : ℝ) < 1 / (b : ℝ) := one_div_pos.mpr hb0
    norm_num [hc2] at hd
    simp only [one_div] at *
    linarith
  by_cases hb_eq : b = 3
  · have hpos : 0 < 1 - ((1 / 2 : ℝ) + 1 / 3 + 1 / (c : ℝ)) := by
      simpa only [hb_eq, Nat.cast_ofNat] using hd
    have h := h84_two_three_defect hc hpos
    simpa only [hb_eq, Nat.cast_ofNat] using h
  by_cases hc_eq : c = 3
  · have hpos : 0 < 1 - ((1 / 2 : ℝ) + 1 / 3 + 1 / (b : ℝ)) := by
      norm_num [hc_eq] at hd
      simp only [one_div] at *
      linarith
    have h := h84_two_three_defect hb hpos
    norm_num [hc_eq]
    simp only [one_div] at *
    linarith
  have hb4 : 4 ≤ b := by omega
  have hc4 : 4 ≤ c := by omega
  have hbrec := h84_reciprocal_le (by norm_num : 0 < (4 : ℕ)) hb4
  have hcrec := h84_reciprocal_le (by norm_num : 0 < (4 : ℕ)) hc4
  have hbig : 5 ≤ b ∨ 5 ≤ c := by
    by_contra h
    have hb_eq4 : b = 4 := by omega
    have hc_eq4 : c = 4 := by omega
    norm_num [hb_eq4, hc_eq4] at hd
  rcases hbig with hb5 | hc5
  · have h := h84_reciprocal_le (by norm_num : 0 < (5 : ℕ)) hb5
    norm_num at h hcrec
    simp only [one_div] at *
    linarith
  · have h := h84_reciprocal_le (by norm_num : 0 < (5 : ℕ)) hc5
    norm_num at h hbrec
    simp only [one_div] at *
    linarith

/-- A positive three-branch defect is at least 1/42.
No branch ordering or artificial nonempty hypothesis is imposed. -/
theorem h84_triangle_defect {a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 0 < 1 - (1 / (a : ℝ) + 1 / (b : ℝ) + 1 / (c : ℝ))) :
    (1 / 42 : ℝ) ≤ 1 - (1 / (a : ℝ) + 1 / (b : ℝ) + 1 / (c : ℝ)) := by
  by_cases ha2 : a = 2
  · have hpos : 0 < 1 - ((1 / 2 : ℝ) + 1 / (b : ℝ) + 1 / (c : ℝ)) := by
      simpa only [ha2, Nat.cast_ofNat] using hd
    have h := h84_two_branch_defect hb hc hpos
    simpa only [ha2, Nat.cast_ofNat] using h
  by_cases hb2 : b = 2
  · have hpos : 0 < 1 - ((1 / 2 : ℝ) + 1 / (a : ℝ) + 1 / (c : ℝ)) := by
      norm_num [hb2] at hd
      simp only [one_div] at *
      linarith
    have h := h84_two_branch_defect ha hc hpos
    norm_num [hb2]
    simp only [one_div] at *
    linarith
  by_cases hc2 : c = 2
  · have hpos : 0 < 1 - ((1 / 2 : ℝ) + 1 / (a : ℝ) + 1 / (b : ℝ)) := by
      norm_num [hc2] at hd
      simp only [one_div] at *
      linarith
    have h := h84_two_branch_defect ha hb hpos
    norm_num [hc2]
    simp only [one_div] at *
    linarith
  have ha3 : 3 ≤ a := by omega
  have hb3 : 3 ≤ b := by omega
  have hc3 : 3 ≤ c := by omega
  have harec := h84_reciprocal_le (by norm_num : 0 < (3 : ℕ)) ha3
  have hbrec := h84_reciprocal_le (by norm_num : 0 < (3 : ℕ)) hb3
  have hcrec := h84_reciprocal_le (by norm_num : 0 < (3 : ℕ)) hc3
  have hbig : 4 ≤ a ∨ 4 ≤ b ∨ 4 ≤ c := by
    by_contra h
    have ha_eq : a = 3 := by omega
    have hb_eq : b = 3 := by omega
    have hc_eq : c = 3 := by omega
    norm_num [ha_eq, hb_eq, hc_eq] at hd
  rcases hbig with ha4 | hb4 | hc4
  · have h := h84_reciprocal_le (by norm_num : 0 < (4 : ℕ)) ha4
    norm_num at h hbrec hcrec
    simp only [one_div] at *
    linarith
  · have h := h84_reciprocal_le (by norm_num : 0 < (4 : ℕ)) hb4
    norm_num at h harec hcrec
    simp only [one_div] at *
    linarith
  · have h := h84_reciprocal_le (by norm_num : 0 < (4 : ℕ)) hc4
    norm_num at h harec hbrec
    simp only [one_div] at *
    linarith

/-- Four branches have defect at least 1/6 whenever their defect is positive. -/
theorem h84_four_branch_defect (e : Fin 4 → ℕ) (he : ∀ i, 2 ≤ e i)
    (hd : 0 < (∑ i, (1 - 1 / (e i : ℝ))) - 2) :
    (1 / 6 : ℝ) ≤ (∑ i, (1 - 1 / (e i : ℝ))) - 2 := by
  classical
  have hexists : ∃ i, 3 ≤ e i := by
    by_contra h
    have heq : ∀ i, e i = 2 := by
      intro i
      have hnot := (not_exists.mp h) i
      have htwo := he i
      omega
    have hsum : (∑ i, (1 - 1 / (e i : ℝ))) = 2 := by
      norm_num [heq]
    simp only [one_div] at *
    linarith
  obtain ⟨i, hi⟩ := hexists
  have hterm : (2 / 3 : ℝ) ≤ 1 - 1 / (e i : ℝ) := by
    have h := h84_reciprocal_le (by norm_num : 0 < (3 : ℕ)) hi
    norm_num at h
    simp only [one_div] at *
    linarith
  have hhalf : ∀ j, (1 / 2 : ℝ) ≤ 1 - 1 / (e j : ℝ) :=
    fun j => h84_branch_term_half (he j)
  have hsingle :
      (1 - 1 / (e i : ℝ)) - 1 / 2 ≤
        ∑ j, ((1 - 1 / (e j : ℝ)) - 1 / 2) :=
    Finset.single_le_sum
      (fun j _ => sub_nonneg.mpr (hhalf j)) (Finset.mem_univ i)
  have hconst : (∑ _j : Fin 4, (1 / 2 : ℝ)) = 2 := by norm_num
  have hsum :
      (∑ j, ((1 - 1 / (e j : ℝ)) - 1 / 2)) =
        (∑ j, (1 - 1 / (e j : ℝ))) - 2 := by
    rw [Finset.sum_sub_distrib, hconst]
  simp only [one_div] at *
  linarith

/-- Sharp positive orbifold defect bound for any natural genus and branch count.
The empty branch set is included; positivity itself excludes only the invalid cases. -/
theorem h84_defect_ge_one_div_42 {γ m : ℕ} (e : Fin m → ℕ)
    (he : ∀ i, 2 ≤ e i)
    (hd : 0 < 2 * (γ : ℝ) - 2 + ∑ i, (1 - 1 / (e i : ℝ))) :
    (1 / 42 : ℝ) ≤ 2 * (γ : ℝ) - 2 + ∑ i, (1 - 1 / (e i : ℝ)) := by
  classical
  have hhalf : (m : ℝ) / 2 ≤ ∑ i, (1 - 1 / (e i : ℝ)) := by
    calc
      (m : ℝ) / 2 = ∑ _i : Fin m, (1 / 2 : ℝ) := by
        simp [div_eq_mul_inv, nsmul_eq_mul]
      _ ≤ ∑ i, (1 - 1 / (e i : ℝ)) :=
        Finset.sum_le_sum (fun i _ => h84_branch_term_half (he i))
  have hupper : (∑ i, (1 - 1 / (e i : ℝ))) ≤ (m : ℝ) := by
    calc
      (∑ i, (1 - 1 / (e i : ℝ))) ≤ ∑ _i : Fin m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hi : 0 ≤ 1 / (e i : ℝ) := by positivity
        simp only [one_div] at *
        linarith
      _ = (m : ℝ) := by simp
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  by_cases hγ2 : 2 ≤ γ
  · have hγR : (2 : ℝ) ≤ γ := by exact_mod_cast hγ2
    simp only [one_div] at *
    linarith
  have hγcases : γ = 0 ∨ γ = 1 := by omega
  rcases hγcases with hγ0 | hγ1
  · have hγR : (γ : ℝ) = 0 := by exact_mod_cast hγ0
    have hm3 : 3 ≤ m := by
      have hmR : (2 : ℝ) < m := by
        simp only [one_div] at *
        linarith
      have hmNat : 2 < m := by exact_mod_cast hmR
      omega
    by_cases hm5 : 5 ≤ m
    · have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm5
      simp only [one_div] at *
      linarith
    have hmcases : m = 3 ∨ m = 4 := by omega
    rcases hmcases with hm3eq | hm4eq
    · subst m
      have hsum :
          (∑ i, (1 - 1 / (e i : ℝ))) =
            (1 - 1 / (e 0 : ℝ)) + (1 - 1 / (e 1 : ℝ)) +
              (1 - 1 / (e 2 : ℝ)) := Fin.sum_univ_three _
      have hpos :
          0 < 1 - (1 / (e 0 : ℝ) + 1 / (e 1 : ℝ) + 1 / (e 2 : ℝ)) := by
        simp only [one_div] at *
        linarith [hsum]
      have h := h84_triangle_defect (he 0) (he 1) (he 2) hpos
      simp only [one_div] at *
      linarith [hsum]
    · subst m
      have hpos : 0 < (∑ i, (1 - 1 / (e i : ℝ))) - 2 := by
        simp only [one_div] at *
        linarith
      have h := h84_four_branch_defect e he hpos
      simp only [one_div] at *
      linarith
  · have hγR : (γ : ℝ) = 1 := by exact_mod_cast hγ1
    have hmpos : 0 < m := by
      by_contra h
      have hmzero : m = 0 := by omega
      subst m
      have hzero : (∑ i : Fin 0, (1 - 1 / (e i : ℝ))) = 0 := by simp
      simp only [one_div] at *
      linarith
    have hmR : (1 : ℝ) ≤ m := by
      exact_mod_cast (show 1 ≤ m by omega)
    simp only [one_div] at *
    linarith

/-- The sharp defect occurs for the hyperbolic triangle orders 2, 3, 7. -/
theorem h84_triangle_bound_attained :
    1 - (1 / (2 : ℝ) + 1 / (3 : ℝ) + 1 / (7 : ℝ)) = 1 / 42 := by
  norm_num

/-- Numerical Riemann--Hurwitz closeout once the positive defect has been bounded. -/
theorem h84_real_order_bound {d n g : ℝ} (hd : (1 / 42 : ℝ) ≤ d)
    (hn : 0 < n) (hRH : 2 * g - 2 = n * d) :
    n ≤ 84 * (g - 1) := by
  have hmul := mul_le_mul_of_nonneg_left hd hn.le
  simp only [one_div] at *
  nlinarith

/-- The defect formula and a positive Riemann--Hurwitz identity imply the 84(g-1) bound.
This is only the independent numerical step, not a construction of the quotient/RH data. -/
theorem h84_hurwitz_order_bound {γ m g n : ℕ} (e : Fin m → ℕ)
    (he : ∀ i, 2 ≤ e i)
    (hd : 0 < 2 * (γ : ℝ) - 2 + ∑ i, (1 - 1 / (e i : ℝ)))
    (hn : 0 < n)
    (hRH : 2 * (g : ℝ) - 2 =
      (n : ℝ) * (2 * (γ : ℝ) - 2 + ∑ i, (1 - 1 / (e i : ℝ)))) :
    n ≤ 84 * (g - 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbound := h84_real_order_bound (h84_defect_ge_one_div_42 e he hd) hnR hRH
  have hprod :
      0 < (n : ℝ) * (2 * (γ : ℝ) - 2 + ∑ i, (1 - 1 / (e i : ℝ))) :=
    mul_pos hnR hd
  have hgR : (1 : ℝ) < g := by linarith
  have hgNat : 1 < g := by exact_mod_cast hgR
  have hcast : ((g - 1 : ℕ) : ℝ) = (g : ℝ) - 1 := by
    simp only [Nat.cast_sub (show 1 ≤ g by omega), Nat.cast_one]
  have hreal : (n : ℝ) ≤ (84 : ℝ) * ((g - 1 : ℕ) : ℝ) := by
    rw [hcast]
    exact hbound
  exact_mod_cast hreal

end LiZhongQC

