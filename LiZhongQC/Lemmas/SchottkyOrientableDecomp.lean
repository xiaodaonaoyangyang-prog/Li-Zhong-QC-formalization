import LiZhongQC.Lemmas.SchottkyBoundaryRankDisc
import LiZhongQC.Lemmas.SchottkyBoundaryRankEdge

open Complex Set LeanEval.Topology.ClassificationOfSurfaces

universe u

namespace LiZhongQC

/-- A real parameter in `[0, N)` is an integer vertex, a Euclidean point, or lies on a free arc. -/
theorem s78nm_orient_real (p q : ℕ) (hN : (0 : ℝ) < 4 * p + 3 * q) (u : ℝ) (hu0 : 0 ≤ u)
    (huN : u < 4 * p + 3 * q) :
    (∃ k : ℕ, k < 4 * p + 3 * q ∧ u = k) ∨
    (∃ U : Set (Quot (OrientableRel p q)), IsOpen U ∧
      Quot.mk _ (ClosedUnitDisc.bdyPtOfReal (u / (4 * p + 3 * q))) ∈ U ∧
      Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))) ∨
    (∃ j : Fin q, ∃ t ∈ Icc (0 : ℝ) 1,
      (Quot.mk _ (ClosedUnitDisc.bdyPtOfReal ((t - (3 * (j : ℝ) + 2)) / (4 * p + 3 * q))) :
        Quot (OrientableRel p q)) =
      Quot.mk _ (ClosedUnitDisc.bdyPtOfReal (u / (4 * p + 3 * q)))) := by
  set N : ℝ := 4 * p + 3 * q with hNdef
  set k : ℕ := ⌊u⌋₊ with hkdef
  have hk0 : (k : ℝ) ≤ u := Nat.floor_le hu0
  have hk1 : u < k + 1 := Nat.lt_floor_add_one u
  by_cases hint : u = k
  · left
    refine ⟨k, ?_, hint⟩
    have : (k : ℝ) < ((4 * p + 3 * q : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  right
  set f : ℝ := u - k with hfdef
  have hf0 : 0 < f := by
    rcases lt_or_eq_of_le hk0 with h | h
    · linarith
    · exact absurd h.symm hint
  have hf1 : f < 1 := by linarith
  have hfI : f ∈ Ioo (0 : ℝ) 1 := ⟨hf0, hf1⟩
  have hfI' : 1 - f ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hkN : k < 4 * p + 3 * q := by
    have : (k : ℝ) < ((4 * p + 3 * q : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have huk : u = k + f := by rw [hfdef]; ring
  obtain ⟨hE1, hE2, hE3⟩ := s78rb_euclid_orientable_edge p q f hfI
  obtain ⟨hE1', hE2', hE3'⟩ := s78rb_euclid_orientable_edge p q (1 - f) hfI'
  by_cases hk : k < 4 * p
  · left
    have hi : k / 4 < p := by omega
    have hkr : (k : ℝ) = 4 * ((k / 4 : ℕ) : ℝ) + ((k % 4 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod k 4).symm
    have hr : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rcases hr with hr | hr | hr | hr
    · have hu' : u = 4 * ((⟨k / 4, hi⟩ : Fin p) : ℝ) + f := by
        rw [huk, hkr, hr]; push_cast; ring
      obtain ⟨U, hU, hmem, hh⟩ := hE1 ⟨k / 4, hi⟩
      exact ⟨U, hU, by rw [hu']; exact hmem, hh⟩
    · have hu' : u = 4 * ((⟨k / 4, hi⟩ : Fin p) : ℝ) + 1 + f := by
        rw [huk, hkr, hr]; push_cast; ring
      obtain ⟨U, hU, hmem, hh⟩ := hE2 ⟨k / 4, hi⟩
      exact ⟨U, hU, by rw [hu']; exact hmem, hh⟩
    · have hu' : u = 4 * ((⟨k / 4, hi⟩ : Fin p) : ℝ) + 3 - (1 - f) := by
        rw [huk, hkr, hr]; push_cast; ring
      obtain ⟨U, hU, hmem, hh⟩ := hE1' ⟨k / 4, hi⟩
      refine ⟨U, hU, ?_, hh⟩
      rw [hu']
      have hrel := Quot.sound (OrientableRel.a (p := p) (n := q) ⟨1 - f, ⟨hfI'.1.le, hfI'.2.le⟩⟩
        ⟨k / 4, hi⟩)
      rw [← hrel]
      exact hmem
    · have hu' : u = 4 * ((⟨k / 4, hi⟩ : Fin p) : ℝ) + 4 - (1 - f) := by
        rw [huk, hkr, hr]; push_cast; ring
      obtain ⟨U, hU, hmem, hh⟩ := hE2' ⟨k / 4, hi⟩
      refine ⟨U, hU, ?_, hh⟩
      rw [hu']
      have hrel := Quot.sound (OrientableRel.b (p := p) (n := q) ⟨1 - f, ⟨hfI'.1.le, hfI'.2.le⟩⟩
        ⟨k / 4, hi⟩)
      rw [← hrel]
      exact hmem
  · have hk4 : 4 * p ≤ k := not_lt.mp hk
    set m' : ℕ := 4 * p + 3 * q - k - 1 with hm'def
    have hm1 : k + m' + 1 = 4 * p + 3 * q := by omega
    have hjq : m' / 3 < q := by omega
    have hmR : (m' : ℝ) = 3 * ((m' / 3 : ℕ) : ℝ) + ((m' % 3 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod m' 3).symm
    have hmN : (k : ℝ) + m' + 1 = N := by
      rw [hNdef]; exact_mod_cast hm1
    have hbd : ClosedUnitDisc.bdyPtOfReal (u / N) = ClosedUnitDisc.bdyPtOfReal (-(N - u) / N) := by
      have : u / N = -(N - u) / N + ((1 : ℤ) : ℝ) := by
        push_cast; field_simp; ring
      rw [this, s78rb_bdy_add_int]
    have hr : m' % 3 = 0 ∨ m' % 3 = 1 ∨ m' % 3 = 2 := by omega
    rcases hr with hr | hr | hr
    · left
      have hw : N - u = 3 * ((⟨m' / 3, hjq⟩ : Fin q) : ℝ) + (1 - f) := by
        rw [hmR, hr] at hmN
        simp only [Nat.cast_zero] at hmN
        show N - u = 3 * ((m' / 3 : ℕ) : ℝ) + (1 - f)
        rw [huk]
        linarith
      obtain ⟨U, hU, hmem, hh⟩ := hE3' ⟨m' / 3, hjq⟩
      refine ⟨U, hU, ?_, hh⟩
      rw [hbd, hw]
      exact hmem
    · right
      have hw : N - u = 3 * ((m' / 3 : ℕ) : ℝ) + 2 - f := by
        rw [hmR, hr] at hmN
        simp only [Nat.cast_one] at hmN
        rw [huk]
        linarith
      refine ⟨⟨m' / 3, hjq⟩, f, ⟨hf0.le, hf1.le⟩, ?_⟩
      rw [hbd, hw]
      congr 2
      show (f - (3 * ((m' / 3 : ℕ) : ℝ) + 2)) / N = -(3 * ((m' / 3 : ℕ) : ℝ) + 2 - f) / N
      ring
    · left
      have hw : N - u = 3 * ((⟨m' / 3, hjq⟩ : Fin q) : ℝ) + 3 - f := by
        rw [hmR, hr] at hmN
        show N - u = 3 * ((m' / 3 : ℕ) : ℝ) + 3 - f
        rw [huk]
        push_cast at hmN
        linarith
      obtain ⟨U, hU, hmem, hh⟩ := hE3 ⟨m' / 3, hjq⟩
      refine ⟨U, hU, ?_, hh⟩
      have hrel := Quot.sound (OrientableRel.c (p := p) (n := q) ⟨f, ⟨hf0.le, hf1.le⟩⟩
        ⟨m' / 3, hjq⟩)
      have heq : (Quot.mk _ (ClosedUnitDisc.bdyPtOfReal (u / N)) : Quot (OrientableRel p q)) =
          Quot.mk _ (ClosedUnitDisc.bdyPtOfReal (-(3 * ((⟨m' / 3, hjq⟩ : Fin q) : ℝ) + f) / N)) := by
        rw [hbd, hw]
        exact hrel.symm
      rw [heq]
      exact hmem


/-- **Point decomposition of the orientable model.**  Every point of `Quot (OrientableRel p q)` with
no open neighbourhood homeomorphic to the plane lies on a free arc `h_j` or is one of finitely many
vertices. -/
theorem s78nm_orientable_decomp (p q : ℕ) (hpq : 1 ≤ p ∨ 1 ≤ q) :
    ∃ V : Set (Quot (OrientableRel p q)), V.Finite ∧ ∀ z,
      (¬ ∃ U : Set (Quot (OrientableRel p q)), IsOpen U ∧ z ∈ U ∧
        Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))) →
      z ∈ (⋃ j : Fin q, (fun t : ℝ => (Quot.mk _ (ClosedUnitDisc.bdyPtOfReal
        ((t - (3 * (j : ℝ) + 2)) / (4 * p + 3 * q))) : Quot (OrientableRel p q))) '' Icc 0 1) ∪ V := by
  classical
  have hN : (0 : ℝ) < 4 * p + 3 * q := by
    rcases hpq with h | h
    · have : (1 : ℝ) ≤ p := by exact_mod_cast h
      positivity
    · have : (1 : ℝ) ≤ q := by exact_mod_cast h
      positivity
  have hR : ∀ x y : ClosedUnitDisc, OrientableRel p q x y → ‖(x : ℂ)‖ = 1 ∧ ‖(y : ℂ)‖ = 1 := by
    intro x y h
    cases h <;> exact ⟨s78rb_bdy_norm _, s78rb_bdy_norm _⟩
  refine ⟨Set.range (fun k : Fin (4 * p + 3 * q) =>
    (Quot.mk (OrientableRel p q) (ClosedUnitDisc.bdyPtOfReal (((k : ℕ) : ℝ) / (4 * p + 3 * q))))),
    Set.finite_range _, ?_⟩
  intro z hz
  obtain ⟨x, rfl⟩ := Quot.exists_rep z
  by_cases hx : ‖(x : ℂ)‖ < 1
  · exact (hz (s78rb_euclid_disc_interior (OrientableRel p q) hR x hx)).elim
  have hx1 : ‖(x : ℂ)‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp x.2) (not_lt.mp hx)
  have hθex : ∃ θ : ℝ, x = ClosedUnitDisc.bdyPtOfReal θ := by
    refine ⟨Complex.arg (x : ℂ) / (2 * Real.pi), Subtype.ext ?_⟩
    rw [s78rb_bdy_coe]
    have h2 : 2 * Real.pi * (Complex.arg (x : ℂ) / (2 * Real.pi)) = Complex.arg (x : ℂ) := by
      field_simp
    rw [h2]
    have := Complex.norm_mul_exp_arg_mul_I (x : ℂ)
    rw [hx1, Complex.ofReal_one, one_mul] at this
    exact this.symm
  obtain ⟨θ, hθ⟩ := hθex
  set N : ℝ := 4 * p + 3 * q with hNdef
  have hθ' : x = ClosedUnitDisc.bdyPtOfReal (Int.fract θ) := by
    rw [hθ]
    have := s78rb_bdy_add_int (Int.fract θ) ⌊θ⌋
    rw [Int.fract_add_floor] at this
    exact this
  have hu0 : 0 ≤ N * Int.fract θ := mul_nonneg hN.le (Int.fract_nonneg θ)
  have huN : N * Int.fract θ < N := by
    have := Int.fract_lt_one θ
    nlinarith
  have huq : (N * Int.fract θ) / N = Int.fract θ := by field_simp
  have hxq : (Quot.mk (OrientableRel p q) x : Quot (OrientableRel p q)) =
      Quot.mk _ (ClosedUnitDisc.bdyPtOfReal ((N * Int.fract θ) / N)) := by
    rw [huq, hθ']
  rcases s78nm_orient_real p q hN (N * Int.fract θ) hu0 huN with ⟨k, hk, hku⟩ | ⟨U, hU, hmem, hh⟩ |
      ⟨j, t, ht, heq⟩
  · right
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [hxq, hku]
  · have hex : ∃ U : Set (Quot (OrientableRel p q)), IsOpen U ∧
        (Quot.mk (OrientableRel p q) x) ∈ U ∧ Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2)) :=
      ⟨U, hU, by rw [hxq]; exact hmem, hh⟩
    exact (hz hex).elim
  · left
    refine mem_iUnion.mpr ⟨j, t, ht, ?_⟩
    rw [hxq]
    exact heq

end LiZhongQC
