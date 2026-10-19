import LiZhongQC.Lemmas.SchottkyGenusBridge2

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Topology Metric

namespace LiZhongQC

/-- **The free arc of `Quot (NonOrientableRel p n)`, `n ≥ 1`, has no plane neighbourhood.** -/
theorem s78dg_nonorientable_free (p n : ℕ) (hn : 1 ≤ n)
    (U : Set (Quot (NonOrientableRel p n))) (hU : IsOpen U)
    (hq : Quot.mk (NonOrientableRel p n)
      (ClosedUnitDisc.bdyPtOfReal (-(3 / 2 : ℝ) / (2 * p + 3 * n))) ∈ U)
    (h : ↥U ≃ₜ EuclideanSpace ℝ (Fin 2)) : False := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpr : (0 : ℝ) ≤ p := by positivity
  set N : ℝ := 2 * p + 3 * n with hNdef
  have hN : 0 < N := by rw [hNdef]; linarith
  let T : Set ℝ := Set.Icc 0 (2 * p / N) ∪ ⋃ j : Fin n,
    (Set.Icc (-(3 * (j : ℝ) + 1) / N) (-(3 * (j : ℝ)) / N) ∪
      Set.Icc (-(3 * (j : ℝ) + 3) / N) (-(3 * (j : ℝ) + 2) / N))
  have hT : IsCompact T := by
    refine isCompact_Icc.union (isCompact_iUnion fun j => isCompact_Icc.union isCompact_Icc)
  refine s78dg_free_param _ T hT ?_ (-(3 / 2 : ℝ) / N) ?_ U hU hq h
  · intro x y hxy
    have hmem : ∀ {a b u : ℝ}, a ≤ u → u ≤ b → u / N ∈ Set.Icc (a / N) (b / N) :=
      fun h1 h2 => ⟨div_le_div_of_nonneg_right h1 hN.le, div_le_div_of_nonneg_right h2 hN.le⟩
    have hmem0 : ∀ {b u : ℝ}, 0 ≤ u → u ≤ b → u / N ∈ Set.Icc (0 : ℝ) (b / N) :=
      fun h1 h2 => ⟨div_nonneg h1 hN.le, div_le_div_of_nonneg_right h2 hN.le⟩
    cases hxy with
    | a x i =>
      have hi : ((i : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast i.2
      have hx0 := x.2.1
      have hx1 := x.2.2
      have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
      exact ⟨⟨_, Or.inl (hmem0 (by linarith) (by linarith)), rfl⟩,
        ⟨_, Or.inl (hmem0 (by linarith) (by linarith)), rfl⟩⟩
    | c x i =>
      have hx0 := x.2.1
      have hx1 := x.2.2
      exact ⟨⟨_, Or.inr (Set.mem_iUnion.2 ⟨i, Or.inl (hmem (by linarith) (by linarith))⟩), rfl⟩,
        ⟨_, Or.inr (Set.mem_iUnion.2 ⟨i, Or.inr (hmem (by linarith) (by linarith))⟩), rfl⟩⟩
  · intro t ht m hm
    rw [div_eq_iff hN.ne'] at hm
    have hmN : (m : ℝ) * N = -3 / 2 - t * N := by nlinarith [hm]
    have hp4 : (0 : ℝ) ≤ 2 * p := by linarith
    have hNge : (3 : ℝ) ≤ 3 * n := by linarith
    rcases ht with h | h
    · have h1 : 0 ≤ t * N := mul_nonneg h.1 hN.le
      have h2 : t * N ≤ 2 * p := (le_div_iff₀ hN).1 h.2
      exact s78dg_noint N (-3 / 2 - t * N) hN (by linarith) (by linarith) (by linarith) m hmN
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h
      have hj0 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
      have hj1 : ((j : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast j.2
      rcases hj with h | h
      · obtain ⟨h1, h2⟩ := s78dg_icc_mul hN h
        rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | h0
        · have : ((j : ℕ) : ℝ) = 0 := by rw [h0]; simp
          rw [this] at h1 h2
          exact s78dg_noint N (-3 / 2 - t * N) hN (by linarith) (by linarith) (by linarith) m hmN
        · have : (1 : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast h0
          exact s78dg_noint N (-3 / 2 - t * N) hN (by linarith) (by linarith) (by linarith) m hmN
      · obtain ⟨h1, h2⟩ := s78dg_icc_mul hN h
        exact s78dg_noint N (-3 / 2 - t * N) hN (by linarith) (by linarith) (by linarith) m hmN

/-- No surface without boundary is homeomorphic to a nonorientable polygon quotient with `n ≥ 1`. -/
theorem s78dg_no_nonorientable_boundary {S : Type*} [TopologicalSpace S]
    (hS : ∀ x : S, ∃ U : Set S, IsOpen U ∧ x ∈ U ∧ Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2)))
    (p n : ℕ) (hn : 1 ≤ n) (φ : S ≃ₜ Quot (NonOrientableRel p n)) : False := by
  let q₀ := Quot.mk (NonOrientableRel p n)
    (ClosedUnitDisc.bdyPtOfReal (-(3 / 2 : ℝ) / (2 * p + 3 * n)))
  obtain ⟨U, hU, hxU, ⟨h⟩⟩ := hS (φ.symm q₀)
  refine s78dg_nonorientable_free p n hn (φ '' U) (φ.isOpenMap U hU) ?_ ((φ.image U).symm.trans h)
  exact ⟨φ.symm q₀, hxU, φ.apply_symm_apply q₀⟩

end LiZhongQC
