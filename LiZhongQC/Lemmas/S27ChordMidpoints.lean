import LiZhongQC.Ch08.S30_ModularGroupDiscontinuity
import LiZhongQC.Lemmas.SchottkyClosedSurface12
import LiZhongQC.Lemmas.SchottkyClosedGenus

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Metric Filter Topology unitInterval
open scoped Manifold ContDiff

noncomputable section
namespace LiZhongQC

/-- Boundary points with the same exponential have the same fractional angle. -/
theorem s83sg_md_fract_eq {r r' : ℝ}
    (h : Complex.exp (((2 * Real.pi * r : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * Real.pi * r' : ℝ) : ℂ) * Complex.I)) : Int.fract r = Int.fract r' := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : (r : ℂ) = r' + n := by
    have : ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I = ((2 * Real.pi * r' : ℝ) : ℂ) * Complex.I +
        n * (2 * Real.pi * Complex.I) := hn
    push_cast at this
    have h3 : (2 * (Real.pi : ℂ) * Complex.I) * (r : ℂ) = (2 * (Real.pi : ℂ) * Complex.I) * (r' + n) := by
      linear_combination this
    exact mul_left_cancel₀ (by simp [hpi, Complex.I_ne_zero]) h3
  have h4 : r = r' + n := by exact_mod_cast h2
  rw [h4, Int.fract_add_intCast]

/-- The fractional angle of `a / N` for `0 ≤ a ≤ N`, tested against the open `a`-sides `Q`. -/
theorem s83sg_md_fract_div {a N m : ℝ} (hN : 0 < N) (hm : 0 ≤ m) (hNm : N = 4 * m + 4) (ha0 : 0 ≤ a) (haN : a ≤ N) :
    ((4 * m < N * Int.fract (a / N) ∧ N * Int.fract (a / N) < 4 * m + 1) ∨
      (4 * m + 2 < N * Int.fract (a / N) ∧ N * Int.fract (a / N) < 4 * m + 3)) ↔
    ((4 * m < a ∧ a < 4 * m + 1) ∨ (4 * m + 2 < a ∧ a < 4 * m + 3)) := by
  rcases lt_or_eq_of_le haN with h | h
  · rw [Int.fract_eq_self.2 ⟨by positivity, (div_lt_one hN).2 h⟩, mul_div_cancel₀ _ hN.ne']
  · subst h
    rw [div_self hN.ne', Int.fract_one, mul_zero]
    constructor
    · rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> linarith
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exfalso <;> linarith

theorem s83sg_md_coe (r : ℝ) :
    ((ClosedUnitDisc.bdyPtOfReal r : ClosedUnitDisc) : ℂ) =
      Complex.exp (((2 * Real.pi * r : ℝ) : ℂ) * Complex.I) := by
  simp [ClosedUnitDisc.bdyPtOfReal, Real.fourierChar_apply]

/-- **[m']** In the closed normal form `Q` the midpoints of the two sides `a_{g-1}`, `b_{g-1}` (first copies, boundary
angles `θ_j = 2π (4(g-1) + j + 1/2)/(4g)`, `j = 0, 1`) are different points.  Proof idea: the classes of boundary
points of the open sides of the last handle (`a`-sides, `b`-sides) are unions of whole classes, so the indicator
`z ↦ (1 if z in an open a-side, 2 if in an open b-side, 0 otherwise)` is constant on `EqvGen (OrientableRel g 0)`
(`s78dg_cs_eqv_boundary`, `Real.fourierChar` injectivity mod 1). -/
theorem s83sg_midpoints_distinct (g : ℕ) (hg : 1 < g) (z₁ z₂ : ClosedUnitDisc)
    (h₁ : (z₁ : ℂ) = Complex.exp (((2 * Real.pi * (4 * ((g : ℝ) - 1) + 0 + 1 / 2) / (4 * g) : ℝ) : ℂ) * Complex.I))
    (h₂ : (z₂ : ℂ) = Complex.exp (((2 * Real.pi * (4 * ((g : ℝ) - 1) + 1 + 1 / 2) / (4 * g) : ℝ) : ℂ) * Complex.I)) :
    Quot.mk (OrientableRel g 0) z₁ ≠ Quot.mk (OrientableRel g 0) z₂ := by
  classical
  have hg' : (2 : ℝ) ≤ g := by exact_mod_cast hg
  set m : ℝ := (g : ℝ) - 1 with hm
  have hm0 : 0 ≤ m := by rw [hm]; linarith
  have hNm : (4 * (g : ℝ) + 3 * ((0 : ℕ) : ℝ)) = 4 * m + 4 := by rw [hm]; push_cast; ring
  have hNpos : (0 : ℝ) < 4 * (g : ℝ) + 3 * ((0 : ℕ) : ℝ) := by rw [hNm]; linarith
  set N : ℝ := 4 * (g : ℝ) + 3 * ((0 : ℕ) : ℝ) with hN
  let Q : ℝ → Prop := fun a => (4 * m < a ∧ a < 4 * m + 1) ∨ (4 * m + 2 < a ∧ a < 4 * m + 3)
  let A : ClosedUnitDisc → Prop := fun z => ∃ r : ℝ,
    (z : ℂ) = Complex.exp (((2 * Real.pi * r : ℝ) : ℂ) * Complex.I) ∧
      ((4 * m < N * Int.fract r ∧ N * Int.fract r < 4 * m + 1) ∨
        (4 * m + 2 < N * Int.fract r ∧ N * Int.fract r < 4 * m + 3))
  have hA : ∀ (z : ClosedUnitDisc) (a : ℝ), 0 ≤ a → a ≤ N →
      (z : ℂ) = Complex.exp (((2 * Real.pi * (a / N) : ℝ) : ℂ) * Complex.I) → (A z ↔ Q a) := by
    intro z a ha0 haN hz
    refine Iff.trans ?_ (s83sg_md_fract_div hNpos hm0 hNm ha0 haN)
    constructor
    · rintro ⟨r', hr', hP⟩
      rw [s83sg_md_fract_eq (hz.symm.trans hr')]
      exact hP
    · intro h
      exact ⟨a / N, hz, h⟩
  have hrel : ∀ x y, OrientableRel g 0 x y → (A x ↔ A y) := by
    intro x y h
    have hj : ∀ i : Fin g, ((i : ℕ) : ℝ) = m ∨ ((i : ℕ) : ℝ) + 1 ≤ m := by
      intro i
      have := i.2
      rcases (by omega : (i : ℕ) = g - 1 ∨ (i : ℕ) + 1 ≤ g - 1) with h | h
      · left
        rw [hm, h]
        push_cast [Nat.cast_sub (by omega : 1 ≤ g)]
        ring
      · right
        rw [hm]
        have : ((i : ℕ) : ℝ) + 1 ≤ ((g - 1 : ℕ) : ℝ) := by exact_mod_cast h
        push_cast [Nat.cast_sub (by omega : 1 ≤ g)] at this
        linarith
    cases h with
    | a t i =>
      have ht := t.2
      rw [hA _ (4 * ((i : ℕ) : ℝ) + t) (by have := Nat.cast_nonneg (α := ℝ) (i : ℕ); linarith [ht.1])
        (by rcases hj i with h | h <;> rw [hNm] <;> linarith [ht.2]) (s83sg_md_coe _),
        hA _ (4 * ((i : ℕ) : ℝ) + 3 - t) (by have := Nat.cast_nonneg (α := ℝ) (i : ℕ); linarith [ht.2])
        (by rcases hj i with h | h <;> rw [hNm] <;> linarith [ht.1]) (s83sg_md_coe _)]
      rcases hj i with h | h
      · constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · refine Or.inr ⟨by linarith, by linarith⟩
          · exfalso; linarith [ht.2]
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exfalso; linarith [ht.2]
          · exact Or.inl ⟨by linarith, by linarith⟩
      · constructor <;> rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exfalso <;> linarith [ht.1, ht.2]
    | b t i =>
      have ht := t.2
      rw [hA _ (4 * ((i : ℕ) : ℝ) + 1 + t) (by have := Nat.cast_nonneg (α := ℝ) (i : ℕ); linarith [ht.1])
        (by rcases hj i with h | h <;> rw [hNm] <;> linarith [ht.2]) (s83sg_md_coe _),
        hA _ (4 * ((i : ℕ) : ℝ) + 4 - t) (by have := Nat.cast_nonneg (α := ℝ) (i : ℕ); linarith [ht.2])
        (by rcases hj i with h | h <;> rw [hNm] <;> linarith [ht.1]) (s83sg_md_coe _)]
      rcases hj i with h | h
      · constructor <;> rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exfalso <;> linarith [ht.1, ht.2]
      · constructor <;> rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exfalso <;> linarith [ht.1, ht.2]
    | c t i => exact absurd i.2 (Nat.not_lt_zero _)
  have heqv : ∀ x y, Relation.EqvGen (OrientableRel g 0) x y → (A x ↔ A y) := by
    intro x y h
    induction h with
    | rel a b hab => exact hrel a b hab
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  intro hq
  have hE := heqv _ _ (Quot.eqvGen_exact hq)
  have e1 : (z₁ : ℂ) = Complex.exp (((2 * Real.pi * ((4 * m + 1 / 2) / N) : ℝ) : ℂ) * Complex.I) := by
    rw [h₁]; congr 3; rw [hN, hm]; field_simp <;> push_cast <;> ring
  have e2 : (z₂ : ℂ) = Complex.exp (((2 * Real.pi * ((4 * m + 3 / 2) / N) : ℝ) : ℂ) * Complex.I) := by
    rw [h₂]; congr 3; rw [hN, hm]; field_simp <;> push_cast <;> ring
  have q1 : A z₁ ↔ Q (4 * m + 1 / 2) := hA z₁ _ (by linarith) (by rw [hNm]; linarith) e1
  have q2 : A z₂ ↔ Q (4 * m + 3 / 2) := hA z₂ _ (by linarith) (by rw [hNm]; linarith) e2
  have t1 : Q (4 * m + 1 / 2) := Or.inl ⟨by linarith, by linarith⟩
  have t2 : ¬ Q (4 * m + 3 / 2) := by
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith
  exact t2 (q2.1 (hE.1 (q1.2 t1)))

end LiZhongQC
