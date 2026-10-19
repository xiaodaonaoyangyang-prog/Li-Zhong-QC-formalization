import LiZhongExternal.Classification.SchottkyClassification01
import LiZhongQC.Lemmas.SchottkyBoundaryRankEdge
import LiZhongQC.Lemmas.SchottkyBoundaryRankDisc

/-!
# Boundary rank, B2 (iii): the point decomposition of the non-orientable model

Every point of `Quot (NonOrientableRel p q)` without a Euclidean neighbourhood lies on a free (`h`) arc
or is one of finitely many vertices.  This is the hypothesis `hdec` of the assembly of the boundary
components of the core.
-/

open Set Function Topology Complex
open scoped Real

namespace LiZhongQC

/-! ## Point decomposition of the non-orientable model -/

open LeanEval.Topology.ClassificationOfSurfaces

/-- Numerical case distinction for a boundary parameter `u ∈ [0, 2p+3q)` of the non-orientable model:
a vertex, an `a`-edge (first or second copy), a `c`-edge (first or second copy), or the free arc. -/
theorem s78rb_nonor_cases (p q : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (huN : u < 2 * p + 3 * q) :
    (∃ k : ℕ, k < 2 * p + 3 * q ∧ u = k) ∨
    (∃ i : ℕ, i < p ∧ ∃ x ∈ Ioo (0 : ℝ) 1, u = 2 * i + x) ∨
    (∃ i : ℕ, i < p ∧ ∃ x ∈ Ioo (0 : ℝ) 1, u = 2 * i + 1 + x) ∨
    (∃ j : ℕ, j < q ∧ ∃ x ∈ Ioo (0 : ℝ) 1, u = 2 * p + 3 * q - 3 * j - x) ∨
    (∃ j : ℕ, j < q ∧ ∃ t ∈ Ioo (0 : ℝ) 1, u = 2 * p + 3 * q - 3 * j - 2 + t) ∨
    (∃ j : ℕ, j < q ∧ ∃ x ∈ Ioo (0 : ℝ) 1, u = 2 * p + 3 * q - 3 * j - 3 + x) := by
  set k : ℕ := ⌊u⌋₊ with hk
  have hk1 : (k : ℝ) ≤ u := Nat.floor_le hu0
  have hk2 : u < k + 1 := Nat.lt_floor_add_one u
  have hkN : k < 2 * p + 3 * q := by
    have : (k : ℝ) < 2 * p + 3 * q := lt_of_le_of_lt hk1 huN
    exact_mod_cast this
  rcases eq_or_lt_of_le (sub_nonneg.2 hk1) with h0 | hτ
  · left
    exact ⟨k, hkN, by linarith⟩
  right
  have hτ' : u - k ∈ Ioo (0 : ℝ) 1 := ⟨hτ, by linarith⟩
  by_cases hkp : k < 2 * p
  · obtain ⟨i, hi | hi⟩ := Nat.even_or_odd' k
    · left
      refine ⟨i, by omega, u - k, hτ', ?_⟩
      have : (k : ℝ) = 2 * i := by exact_mod_cast hi
      linarith
    · right; left
      refine ⟨i, by omega, u - k, hτ', ?_⟩
      have : (k : ℝ) = 2 * i + 1 := by exact_mod_cast hi
      linarith
  · obtain ⟨j, s, hj, hs, hks⟩ : ∃ j s : ℕ, j < q ∧ (s = 1 ∨ s = 2 ∨ s = 3) ∧
        k + 3 * j + s = 2 * p + 3 * q :=
      ⟨(2 * p + 3 * q - k - 1) / 3, (2 * p + 3 * q - k - 1) % 3 + 1, by omega, by omega, by omega⟩
    have hks' : (k : ℝ) + 3 * j + s = 2 * p + 3 * q := by exact_mod_cast hks
    rcases hs with rfl | rfl | rfl
    · right; right; left
      refine ⟨j, hj, 1 - (u - k), ⟨by linarith, by linarith⟩, ?_⟩
      push_cast at hks'
      linarith
    · right; right; right; left
      refine ⟨j, hj, u - k, hτ', ?_⟩
      push_cast at hks'
      linarith
    · right; right; right; right
      refine ⟨j, hj, u - k, hτ', ?_⟩
      push_cast at hks'
      linarith

theorem s78rb_bdy_surj (y : ClosedUnitDisc) (hy : ‖(y : ℂ)‖ = 1) :
    ∃ r : ℝ, y = ClosedUnitDisc.bdyPtOfReal r := by
  have hmem : (y : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm]; exact hy
  obtain ⟨θ, hθ⟩ := Circle.exp_surjective ⟨(y : ℂ), hmem⟩
  refine ⟨θ / (2 * π), ?_⟩
  apply Subtype.ext
  rw [s78rb_bdy_coe]
  have h1 : ((Circle.exp θ : Circle) : ℂ) = (y : ℂ) := congrArg Subtype.val hθ
  rw [← h1, Circle.coe_exp]
  congr 2
  have hpi : (2 * π) ≠ 0 := by positivity
  push_cast
  field_simp

theorem s78rb_nonorientable_decomp (p q : ℕ) (hp : 1 ≤ p) :
    ∃ V : Set (Quot (NonOrientableRel p q)), V.Finite ∧
      ∀ z : Quot (NonOrientableRel p q),
        (¬ ∃ U : Set (Quot (NonOrientableRel p q)), IsOpen U ∧ z ∈ U ∧
          Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))) →
        z ∈ (⋃ j : Fin q, (fun t : ℝ => (Quot.mk (NonOrientableRel p q)
          (ClosedUnitDisc.bdyPtOfReal ((t - (3 * ((j : ℕ) : ℝ) + 2)) / (2 * p + 3 * q))) :
            Quot (NonOrientableRel p q))) '' Icc 0 1) ∪ V := by
  have hN : (0 : ℝ) < 2 * p + 3 * q := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    linarith
  have hNne : (2 * (p : ℝ) + 3 * q) ≠ 0 := hN.ne'
  refine ⟨(fun k : ℕ => (Quot.mk (NonOrientableRel p q)
      (ClosedUnitDisc.bdyPtOfReal ((k : ℝ) / (2 * p + 3 * q))) : Quot (NonOrientableRel p q))) ''
        {k : ℕ | k < 2 * p + 3 * q}, (Set.finite_lt_nat _).image _, ?_⟩
  intro z hz
  by_contra hcon
  apply hz
  obtain ⟨y, rfl⟩ := Quot.exists_rep z
  have hcon1 : ∀ j : Fin q, ∀ t ∈ Icc (0 : ℝ) 1, Quot.mk (NonOrientableRel p q) y ≠
      Quot.mk (NonOrientableRel p q)
        (ClosedUnitDisc.bdyPtOfReal ((t - (3 * ((j : ℕ) : ℝ) + 2)) / (2 * p + 3 * q))) := by
    intro j t ht heq
    exact hcon (Or.inl (Set.mem_iUnion.2 ⟨j, t, ht, heq.symm⟩))
  have hcon2 : ∀ k : ℕ, k < 2 * p + 3 * q → Quot.mk (NonOrientableRel p q) y ≠
      Quot.mk (NonOrientableRel p q) (ClosedUnitDisc.bdyPtOfReal ((k : ℝ) / (2 * p + 3 * q))) := by
    intro k hk heq
    exact hcon (Or.inr ⟨k, hk, heq.symm⟩)
  have hR : ∀ x y, NonOrientableRel p q x y → ‖(x : ℂ)‖ = 1 ∧ ‖(y : ℂ)‖ = 1 := by
    intro x y h
    cases h <;> exact ⟨s78rb_bdy_norm _, s78rb_bdy_norm _⟩
  by_cases hlt : ‖(y : ℂ)‖ < 1
  · exact s78rb_euclid_disc_interior (NonOrientableRel p q) hR y hlt
  have hy1 : ‖(y : ℂ)‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp y.2) (not_lt.1 hlt)
  obtain ⟨r, rfl⟩ := s78rb_bdy_surj y hy1
  -- reduce to a parameter in `[0, N)`
  set N : ℝ := 2 * p + 3 * q with hNdef
  set u : ℝ := N * Int.fract r with hu
  have hf0 : 0 ≤ Int.fract r := Int.fract_nonneg r
  have hf1 : Int.fract r < 1 := Int.fract_lt_one r
  have hu0 : 0 ≤ u := mul_nonneg hN.le hf0
  have huN : u < N := by
    have := mul_lt_mul_of_pos_left hf1 hN
    simpa [hu] using this
  have hyu : ClosedUnitDisc.bdyPtOfReal r = ClosedUnitDisc.bdyPtOfReal (u / N) := by
    have e : u / N = r + ((-⌊r⌋ : ℤ) : ℝ) := by
      simp only [hu]
      field_simp
      rw [Int.fract]
      push_cast
      ring
    rw [e, s78rb_bdy_add_int]
  rw [hyu] at hcon1 hcon2 ⊢
  have hcon2' : ∀ k : ℕ, k < 2 * p + 3 * q → u ≠ k := by
    intro k hk hk'
    apply hcon2 k hk
    rw [← hk']
  have hbd : ∀ a b : ℝ, a = b + 1 → ClosedUnitDisc.bdyPtOfReal a = ClosedUnitDisc.bdyPtOfReal b := by
    intro a b hab
    have := s78rb_bdy_add_int b 1
    rw [Int.cast_one] at this
    rw [hab]; exact this
  rcases s78rb_nonor_cases p q u hu0 huN with ⟨k, hk, hku⟩ | ⟨i, hi, x, hx, hux⟩ |
    ⟨i, hi, x, hx, hux⟩ | ⟨j, hj, x, hx, hux⟩ | ⟨j, hj, t, ht, hut⟩ | ⟨j, hj, x, hx, hux⟩
  · exact absurd hku (hcon2' k hk)
  · -- first copy of an `a`-edge
    obtain ⟨U, hU, hmem, hh⟩ := (s78rb_euclid_nonorientable_edge p q x hx).1 ⟨i, hi⟩
    refine ⟨U, hU, ?_, hh⟩
    have e : ClosedUnitDisc.bdyPtOfReal (u / N) =
        ClosedUnitDisc.bdyPtOfReal ((2 * (i : ℝ) + x) / (2 * p + 3 * q)) := by
      rw [hux]
    rw [e]
    exact hmem
  · -- second copy of an `a`-edge: same class as the first copy
    obtain ⟨U, hU, hmem, hh⟩ := (s78rb_euclid_nonorientable_edge p q x hx).1 ⟨i, hi⟩
    refine ⟨U, hU, ?_, hh⟩
    have hrel : Quot.mk (NonOrientableRel p q)
          (ClosedUnitDisc.bdyPtOfReal ((2 * (i : ℝ) + x) / (2 * p + 3 * q))) =
        Quot.mk (NonOrientableRel p q)
          (ClosedUnitDisc.bdyPtOfReal ((2 * (i : ℝ) + 1 + x) / (2 * p + 3 * q))) :=
      Quot.sound (NonOrientableRel.a (p := p) (n := q) ⟨x, hx.1.le, hx.2.le⟩ ⟨i, hi⟩)
    have e : ClosedUnitDisc.bdyPtOfReal (u / N) =
        ClosedUnitDisc.bdyPtOfReal ((2 * (i : ℝ) + 1 + x) / (2 * p + 3 * q)) := by
      rw [hux]
    rw [e, ← hrel]
    exact hmem
  · -- first copy of a `c`-edge: `u = N - 3j - x`
    obtain ⟨U, hU, hmem, hh⟩ := (s78rb_euclid_nonorientable_edge p q x hx).2 ⟨j, hj⟩
    refine ⟨U, hU, ?_, hh⟩
    have e : ClosedUnitDisc.bdyPtOfReal (u / N) =
        ClosedUnitDisc.bdyPtOfReal (-(3 * (j : ℝ) + x) / (2 * p + 3 * q)) := by
      apply hbd
      rw [hux]
      field_simp
      ring
    rw [e]
    exact hmem
  · -- free arc
    exfalso
    have e : ClosedUnitDisc.bdyPtOfReal (u / N) =
        ClosedUnitDisc.bdyPtOfReal ((t - (3 * (j : ℝ) + 2)) / (2 * p + 3 * q)) := by
      apply hbd
      rw [hut]
      field_simp
      ring
    exact hcon1 ⟨j, hj⟩ t ⟨ht.1.le, ht.2.le⟩ (by rw [e])
  · -- second copy of a `c`-edge
    obtain ⟨U, hU, hmem, hh⟩ := (s78rb_euclid_nonorientable_edge p q x hx).2 ⟨j, hj⟩
    refine ⟨U, hU, ?_, hh⟩
    have hrel : Quot.mk (NonOrientableRel p q)
          (ClosedUnitDisc.bdyPtOfReal (-(3 * (j : ℝ) + x) / (2 * p + 3 * q))) =
        Quot.mk (NonOrientableRel p q)
          (ClosedUnitDisc.bdyPtOfReal (-(3 * (j : ℝ) + 3 - x) / (2 * p + 3 * q))) :=
      Quot.sound (NonOrientableRel.c (p := p) (n := q) ⟨x, hx.1.le, hx.2.le⟩ ⟨j, hj⟩)
    have e : ClosedUnitDisc.bdyPtOfReal (u / N) =
        ClosedUnitDisc.bdyPtOfReal (-(3 * (j : ℝ) + 3 - x) / (2 * p + 3 * q)) := by
      apply hbd
      rw [hux]
      field_simp
      ring
    rw [e, ← hrel]
    exact hmem

end LiZhongQC
