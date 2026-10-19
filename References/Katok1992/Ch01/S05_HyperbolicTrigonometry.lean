import References.Katok1992.Ch01.S04_HyperbolicArea

/-!
# Katok 1992, Ch. 1 §1.5 Hyperbolic trigonometry

S. Katok, *Fuchsian Groups* (1992), Chapter 1 *Hyperbolic Geometry*, §1.5; source `full.md` of
`Fuchsian groups (Katok, Svetlana) …-3766f6b7…`, lines 413–528.

* Helper (a point of ℍ as a point of ℂ̂; three points of ℍ not on one geodesic) — `toExtH`,
  `IsNondegenerateTriangle`
* Theorem 1.5.1 (l. 417–429) — `thm1_5_1_i`, `thm1_5_1_ii`, `thm1_5_1_iii`
* Theorem 1.5.2 (i) (the Sine Rule, l. 448; cited at l. 1853) — `thm1_5_2_i`
* Theorem 1.5.2 (ii) (the Cosine Rule I, l. 450) — `thm1_5_2_ii`
* Theorem 1.5.2 (iii) (the Cosine Rule II, l. 452) — `thm1_5_2_iii`
* Theorem 1.5.3 (Pythagorean Theorem, l. 525) — `thm1_5_3`

Not items (DESIGN §3): the angle of parallelism Π(a) (l. 415; a name for the third angle of Theorem 1.5.1, whose
well-definedness is that theorem); the Remark after Theorem 1.5.2 (l. 454; not cited); (1.5.1)–(1.5.4) (proof steps;
(1.5.3) is used only by Exercise 1.12); Figs. 5, 6; the exercises.

**Conventions.** [OCR] The tags of Theorem 1.5.1 are shifted by one display (as in Theorem 1.2.6): (i) is
`tan Π(a) = 1/sinh a`, (ii) `sin Π(a) = 1/cosh a`, (iii) `sec Π(a) = 1/tanh a` (the proof of (ii) at l. 433 derives
`cosh a = 1/sin Π(a)`). A triangle of §1.5.2 has vertices `A, B, C ∈ ℍ` (positive angles, finite sides, l. 444) not
on one geodesic; the sides are `a = ρ(B, C)`, `b = ρ(C, A)`, `c = ρ(A, B)`, and the opposite angles are
`α = hypAngle A B C`, `β = hypAngle B C A`, `γ = hypAngle C A B`.
-/

open Complex Set Metric Filter Topology
open scoped UpperHalfPlane MatrixGroups ComplexConjugate Real

noncomputable section

namespace Katok1992

open LiZhongQC (ExtPlane)

/-- Helper (§1.5). A point of ℍ as a point of the Riemann sphere `ℂ̂`. -/
def toExtH (z : ℍ) : ExtPlane := (((z : ℂ)) : ExtPlane)

/-- Helper (§1.5; l. 444). `A, B, C ∈ ℍ` do not lie on one geodesic (a triangle with positive angles). -/
def IsNondegenerateTriangle (A B C : ℍ) : Prop :=
  ¬ ∃ p ∈ pointsAtInfinity, ∃ q ∈ pointsAtInfinity, p ≠ q ∧ ({A, B, C} : Set ℍ) ⊆ geodArc p q

/-- Multiplying both vectors by a unit complex number does not change the angle. -/
theorem k92_angle_mul_unit (x y u : ℂ) (hu : ‖u‖ = 1) :
    InnerProductGeometry.angle (x * u) (y * u) = InnerProductGeometry.angle x y := by
  unfold InnerProductGeometry.angle
  rw [Complex.inner, Complex.inner, norm_mul, norm_mul, hu, mul_one, mul_one]
  congr 3
  have h1 : u * conj u = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    simp
  calc y * u * conj (x * u) = y * conj x * (u * conj u) := by rw [map_mul]; ring
    _ = y * conj x := by rw [h1, mul_one]

/-- The tangent direction at `i` towards a point `q` of ℍ is `i` times its Cayley image. -/
theorem k92_tangentDir_I (q : ℍ) :
    tangentDir UpperHalfPlane.I (toExtH q) = I * LiZhongQC.cayley (q : ℂ) := by
  unfold tangentDir toExtH LiZhongQC.cayley
  simp only [OnePoint.elim_some, UpperHalfPlane.coe_I, Complex.conj_I, sub_neg_eq_add]
  ring

/-- Auxiliary. For `q ∈ ℍ` and `w = cayley q`: `1 − |w|² > 0`, `cosh ρ(i, q) (1 − |w|²) = 1 + |w|²`,
`sinh ρ(i, q) (1 − |w|²) = 2|w|`. -/
theorem k92_cayley_facts (q : ℍ) :
    let w := LiZhongQC.cayley (q : ℂ)
    0 < 1 - ‖w‖ ^ 2 ∧ Real.cosh (dist UpperHalfPlane.I q) * (1 - ‖w‖ ^ 2) = 1 + ‖w‖ ^ 2 ∧
      Real.sinh (dist UpperHalfPlane.I q) * (1 - ‖w‖ ^ 2) = 2 * ‖w‖ := by
  intro w
  have hy := q.im_pos
  have hden : (q : ℂ) + I ≠ 0 := LiZhongQC.cayley_den_ne_zero hy
  have hkey := LiZhongQC.normSq_cayley_key (q : ℂ)
  have hnd : 0 < Complex.normSq ((q : ℂ) + I) := Complex.normSq_pos.2 hden
  have hw2 : ‖w‖ ^ 2 = Complex.normSq ((q : ℂ) - I) / Complex.normSq ((q : ℂ) + I) := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [w, LiZhongQC.cayley, Complex.normSq_div]
  have h1w : 1 - ‖w‖ ^ 2 = 4 * q.im / Complex.normSq ((q : ℂ) + I) := by
    rw [hw2, eq_div_iff hnd.ne', sub_mul, div_mul_cancel₀ _ hnd.ne', one_mul]
    simpa using hkey
  have hpos : 0 < 1 - ‖w‖ ^ 2 := by rw [h1w]; positivity
  have hcosh : Real.cosh (dist UpperHalfPlane.I q) * (1 - ‖w‖ ^ 2) = 1 + ‖w‖ ^ 2 := by
    rw [UpperHalfPlane.cosh_dist, h1w, hw2]
    have hd : dist ((UpperHalfPlane.I : ℍ) : ℂ) (q : ℂ) ^ 2 = Complex.normSq ((q : ℂ) - I) := by
      rw [Complex.dist_eq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_neg]
      simp
    rw [hd, UpperHalfPlane.I_im]
    have hk' : Complex.normSq ((q : ℂ) + I) - Complex.normSq ((q : ℂ) - I) = 4 * q.im := by simpa using hkey
    field_simp
    linear_combination (-2 : ℝ) * hk'
  refine ⟨hpos, hcosh, ?_⟩
  have hs0 : 0 ≤ Real.sinh (dist UpperHalfPlane.I q) := Real.sinh_nonneg_iff.2 dist_nonneg
  have hsq : (Real.sinh (dist UpperHalfPlane.I q) * (1 - ‖w‖ ^ 2)) ^ 2 = (2 * ‖w‖) ^ 2 := by
    have hc := Real.cosh_sq (dist UpperHalfPlane.I q)
    have : (Real.sinh (dist UpperHalfPlane.I q) * (1 - ‖w‖ ^ 2)) ^ 2 =
        (Real.cosh (dist UpperHalfPlane.I q) * (1 - ‖w‖ ^ 2)) ^ 2 - (1 - ‖w‖ ^ 2) ^ 2 := by
      rw [mul_pow, mul_pow, hc]; ring
    rw [this, hcosh]
    ring
  exact (pow_left_inj₀ (mul_nonneg hs0 hpos.le) (by positivity) two_ne_zero).1 hsq

/-- `cosh ρ(A, B) − 1 = 2 |α − β|² / ((1 − |α|²)(1 − |β|²))` in Cayley coordinates. -/
theorem k92_cosh_dist_cayley (A B : ℍ) :
    (Real.cosh (dist A B) - 1) * ((1 - ‖LiZhongQC.cayley (A : ℂ)‖ ^ 2) * (1 - ‖LiZhongQC.cayley (B : ℂ)‖ ^ 2)) =
      2 * ‖LiZhongQC.cayley (A : ℂ) - LiZhongQC.cayley (B : ℂ)‖ ^ 2 := by
  have hA := A.im_pos
  have hB := B.im_pos
  have hdA : (A : ℂ) + I ≠ 0 := LiZhongQC.cayley_den_ne_zero hA
  have hdB : (B : ℂ) + I ≠ 0 := LiZhongQC.cayley_den_ne_zero hB
  have hkA := LiZhongQC.normSq_cayley_key (A : ℂ)
  have hkB := LiZhongQC.normSq_cayley_key (B : ℂ)
  have hnA : 0 < Complex.normSq ((A : ℂ) + I) := Complex.normSq_pos.2 hdA
  have hnB : 0 < Complex.normSq ((B : ℂ) + I) := Complex.normSq_pos.2 hdB
  have hdiff : LiZhongQC.cayley (A : ℂ) - LiZhongQC.cayley (B : ℂ) =
      2 * I * ((A : ℂ) - B) / (((A : ℂ) + I) * ((B : ℂ) + I)) := by
    unfold LiZhongQC.cayley
    field_simp
    ring
  have h1 : ∀ q : ℍ, 1 - ‖LiZhongQC.cayley (q : ℂ)‖ ^ 2 = 4 * q.im / Complex.normSq ((q : ℂ) + I) := by
    intro q
    have hn : 0 < Complex.normSq ((q : ℂ) + I) := Complex.normSq_pos.2 (LiZhongQC.cayley_den_ne_zero q.im_pos)
    rw [← Complex.normSq_eq_norm_sq, LiZhongQC.cayley, Complex.normSq_div, eq_div_iff hn.ne', sub_mul,
      div_mul_cancel₀ _ hn.ne', one_mul]
    simpa using LiZhongQC.normSq_cayley_key (q : ℂ)
  rw [h1 A, h1 B, hdiff, ← Complex.normSq_eq_norm_sq, Complex.normSq_div, Complex.normSq_mul,
    Complex.normSq_mul, Complex.normSq_mul, UpperHalfPlane.cosh_dist, Complex.dist_eq,
    ← Complex.normSq_eq_norm_sq]
  have h2 : Complex.normSq (2 : ℂ) = 4 := by norm_num [Complex.normSq_apply]
  rw [h2, Complex.normSq_I]
  field_simp
  ring

/-- The Cosine Rule I with the vertex `C` at `i`. -/
theorem k92_cosine_rule_at_I (A B : ℍ) :
    Real.cosh (dist A B) = Real.cosh (dist B UpperHalfPlane.I) * Real.cosh (dist UpperHalfPlane.I A) -
      Real.sinh (dist B UpperHalfPlane.I) * Real.sinh (dist UpperHalfPlane.I A) *
        Real.cos (hypAngle UpperHalfPlane.I (toExtH A) (toExtH B)) := by
  set α := LiZhongQC.cayley (A : ℂ) with hα
  set β := LiZhongQC.cayley (B : ℂ) with hβ
  obtain ⟨hpa, hca, hsa⟩ := k92_cayley_facts A
  obtain ⟨hpb, hcb, hsb⟩ := k92_cayley_facts B
  have hcd := k92_cosh_dist_cayley A B
  have hang : hypAngle UpperHalfPlane.I (toExtH A) (toExtH B) = InnerProductGeometry.angle α β := by
    unfold hypAngle
    rw [k92_tangentDir_I, k92_tangentDir_I, mul_comm I, mul_comm I,
      k92_angle_mul_unit _ _ _ Complex.norm_I]
  rw [dist_comm B UpperHalfPlane.I, hang]
  simp only [← hα, ← hβ] at hca hsa hcb hsb hcd hpa hpb
  by_cases hα0 : α = 0
  · have hA : Real.sinh (dist UpperHalfPlane.I A) = 0 := by
      have := hsa
      rw [hα0, norm_zero, mul_zero] at this
      exact (mul_eq_zero.1 this).resolve_right (by norm_num)
    have hcA : Real.cosh (dist UpperHalfPlane.I A) = 1 := by
      have := hca
      rw [hα0, norm_zero] at this
      simpa using this
    have hcosAB : Real.cosh (dist A B) = Real.cosh (dist UpperHalfPlane.I B) := by
      have h1 := hcd
      have h2 := hcb
      rw [hα0, zero_sub, norm_neg, norm_zero] at h1
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, one_mul] at h1
      nlinarith
    rw [hA, hcA, hcosAB]
    ring
  by_cases hβ0 : β = 0
  · have hB : Real.sinh (dist UpperHalfPlane.I B) = 0 := by
      have := hsb
      rw [hβ0, norm_zero, mul_zero] at this
      exact (mul_eq_zero.1 this).resolve_right (by norm_num)
    have hcB : Real.cosh (dist UpperHalfPlane.I B) = 1 := by
      have := hcb
      rw [hβ0, norm_zero] at this
      simpa using this
    have hcosAB : Real.cosh (dist A B) = Real.cosh (dist UpperHalfPlane.I A) := by
      have h1 := hcd
      have h2 := hca
      rw [hβ0, sub_zero, norm_zero] at h1
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, mul_one] at h1
      nlinarith
    rw [hB, hcB, hcosAB]
    ring
  have hna : 0 < ‖α‖ := norm_pos_iff.2 hα0
  have hnb : 0 < ‖β‖ := norm_pos_iff.2 hβ0
  rw [InnerProductGeometry.cos_angle]
  have hsub : ‖α - β‖ ^ 2 = ‖α‖ ^ 2 - 2 * inner ℝ α β + ‖β‖ ^ 2 := norm_sub_sq_real α β
  rw [hsub] at hcd
  have eA : Real.cosh (dist UpperHalfPlane.I A) = (1 + ‖α‖ ^ 2) / (1 - ‖α‖ ^ 2) := by
    rw [eq_div_iff hpa.ne']; exact hca
  have eB : Real.cosh (dist UpperHalfPlane.I B) = (1 + ‖β‖ ^ 2) / (1 - ‖β‖ ^ 2) := by
    rw [eq_div_iff hpb.ne']; exact hcb
  have fA : Real.sinh (dist UpperHalfPlane.I A) = 2 * ‖α‖ / (1 - ‖α‖ ^ 2) := by
    rw [eq_div_iff hpa.ne']; exact hsa
  have fB : Real.sinh (dist UpperHalfPlane.I B) = 2 * ‖β‖ / (1 - ‖β‖ ^ 2) := by
    rw [eq_div_iff hpb.ne']; exact hsb
  have gAB : Real.cosh (dist A B) =
      1 + 2 * (‖α‖ ^ 2 - 2 * inner ℝ α β + ‖β‖ ^ 2) / ((1 - ‖α‖ ^ 2) * (1 - ‖β‖ ^ 2)) := by
    have hP : 0 < (1 - ‖α‖ ^ 2) * (1 - ‖β‖ ^ 2) := mul_pos hpa hpb
    rw [← hcd, mul_div_cancel_right₀ _ hP.ne']
    ring
  rw [eA, eB, fA, fB, gAB]
  field_simp
  ring

/-- The denominator `c z + d` of `g ∈ SL(2,ℝ)` at a point of ℍ is nonzero. -/
theorem k92_den_ne_zero (g : SL(2, ℝ)) (z : ℍ) : ((g 1 0 : ℝ) : ℂ) * z + ((g 1 1 : ℝ) : ℂ) ≠ 0 := by
  have := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ g) z
  simpa [UpperHalfPlane.denom] using this

/-- Auxiliary. The Möbius formula for the action of `SL(2,ℝ)` on ℍ. -/
theorem k92_coe_smul (g : SL(2, ℝ)) (z : ℍ) :
    ((g • z : ℍ) : ℂ) = (((g 0 0 : ℝ) : ℂ) * z + ((g 0 1 : ℝ) : ℂ)) / (((g 1 0 : ℝ) : ℂ) * z + ((g 1 1 : ℝ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

/-- Under `g ∈ SL(2,ℝ)` the tangent direction at `z` towards `x ∈ ℍ` is multiplied by the unit
`(c z̄ + d)/(c z + d)`. -/
theorem k92_tangentDir_smul (g : SL(2, ℝ)) (z x : ℍ) :
    tangentDir (g • z) (toExtH (g • x)) = tangentDir z (toExtH x) *
      ((((g 1 0 : ℝ) : ℂ) * conj (z : ℂ) + ((g 1 1 : ℝ) : ℂ)) / (((g 1 0 : ℝ) : ℂ) * z + ((g 1 1 : ℝ) : ℂ))) := by
  unfold tangentDir toExtH
  simp only [OnePoint.elim_some]
  rw [k92_coe_smul, k92_coe_smul]
  set a : ℂ := ((g 0 0 : ℝ) : ℂ)
  set b : ℂ := ((g 0 1 : ℝ) : ℂ)
  set c : ℂ := ((g 1 0 : ℝ) : ℂ)
  set d : ℂ := ((g 1 1 : ℝ) : ℂ)
  have hdet : a * d - b * c = 1 := by
    have h := g.prop
    rw [Matrix.det_fin_two] at h
    simp only [a, b, c, d]
    exact_mod_cast h
  have hz := k92_den_ne_zero g z
  have hx := k92_den_ne_zero g x
  have hzc : c * conj (z : ℂ) + d ≠ 0 := by
    intro h0
    apply hz
    have := congrArg conj h0
    simpa [a, b, c, d, map_add, map_mul, Complex.conj_ofReal] using this
  have hxz : (x : ℂ) - conj (z : ℂ) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp only [sub_im, conj_im, zero_im, UpperHalfPlane.coe_im] at this
    linarith [x.im_pos, z.im_pos]
  have hconj : conj ((a * z + b) / (c * z + d)) = (a * conj (z : ℂ) + b) / (c * conj (z : ℂ) + d) := by
    simp [a, b, c, d, map_div₀, map_add, map_mul, Complex.conj_ofReal]
  rw [hconj]
  have hgx : (a * x + b) / (c * x + d) - (a * conj (z : ℂ) + b) / (c * conj (z : ℂ) + d) =
      ((x : ℂ) - conj (z : ℂ)) / ((c * x + d) * (c * conj (z : ℂ) + d)) := by
    rw [div_sub_div _ _ hx hzc]
    congr 1
    linear_combination ((x : ℂ) - conj (z : ℂ)) * hdet
  have hgz : (a * x + b) / (c * x + d) - (a * z + b) / (c * z + d) =
      ((x : ℂ) - z) / ((c * x + d) * (c * z + d)) := by
    rw [div_sub_div _ _ hx hz]
    congr 1
    linear_combination ((x : ℂ) - z) * hdet
  have hz' : c * (z : ℂ) + d ≠ 0 := hz
  have hx' : c * (x : ℂ) + d ≠ 0 := hx
  rw [hgx, hgz]
  generalize c * (z : ℂ) + d = Q at hz' ⊢
  generalize c * (x : ℂ) + d = P at hx' ⊢
  generalize c * conj (z : ℂ) + d = Q' at hzc ⊢
  generalize (x : ℂ) - conj (z : ℂ) = Y at hxz ⊢
  field_simp

/-- `SL(2,ℝ)` preserves the angles `hypAngle` at points of ℍ between directions towards points of ℍ. -/
theorem k92_hypAngle_smul (g : SL(2, ℝ)) (z x y : ℍ) :
    hypAngle (g • z) (toExtH (g • x)) (toExtH (g • y)) = hypAngle z (toExtH x) (toExtH y) := by
  unfold hypAngle
  rw [k92_tangentDir_smul, k92_tangentDir_smul, k92_angle_mul_unit]
  have hz := k92_den_ne_zero g z
  rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.2 hz)]
  have : ((g 1 0 : ℝ) : ℂ) * conj (z : ℂ) + ((g 1 1 : ℝ) : ℂ) = conj (((g 1 0 : ℝ) : ℂ) * z + ((g 1 1 : ℝ) : ℂ)) := by
    simp [map_add, map_mul, Complex.conj_ofReal]
  rw [this, Complex.norm_conj]

/-- **Cosine Rule I** for arbitrary vertices, by moving `C` to `i`. -/
theorem k92_cosine_rule (A B C : ℍ) :
    Real.cosh (dist A B) = Real.cosh (dist B C) * Real.cosh (dist C A) -
      Real.sinh (dist B C) * Real.sinh (dist C A) * Real.cos (hypAngle C (toExtH A) (toExtH B)) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, ℝ) C UpperHalfPlane.I
  have h := k92_cosine_rule_at_I (g • A) (g • B)
  rw [← hg, dist_smul, dist_smul, dist_smul, k92_hypAngle_smul] at h
  exact h

/-- Algebraic core of the Sine Rule: `sin γ · sinh a · sinh b = √Δ` with
`Δ = 1 − cosh²a − cosh²b − cosh²c + 2 cosh a cosh b cosh c`, from the Cosine Rule at the vertex of `γ`. -/
theorem k92_sin_mul_sinh (a b c γ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hγ0 : 0 ≤ γ) (hγπ : γ ≤ π)
    (hcos : Real.cosh c = Real.cosh a * Real.cosh b - Real.sinh a * Real.sinh b * Real.cos γ) :
    Real.sin γ * (Real.sinh a * Real.sinh b) =
      √(1 - Real.cosh a ^ 2 - Real.cosh b ^ 2 - Real.cosh c ^ 2 +
        2 * Real.cosh a * Real.cosh b * Real.cosh c) := by
  have hsa : 0 ≤ Real.sinh a := Real.sinh_nonneg_iff.2 ha
  have hsb : 0 ≤ Real.sinh b := Real.sinh_nonneg_iff.2 hb
  have hsg : 0 ≤ Real.sin γ := Real.sin_nonneg_of_nonneg_of_le_pi hγ0 hγπ
  have hca := Real.cosh_sq a
  have hcb := Real.cosh_sq b
  have hsc := Real.sin_sq_add_cos_sq γ
  have hΔ : 1 - Real.cosh a ^ 2 - Real.cosh b ^ 2 - Real.cosh c ^ 2 +
      2 * Real.cosh a * Real.cosh b * Real.cosh c = (Real.sin γ * (Real.sinh a * Real.sinh b)) ^ 2 := by
    rw [hcos]
    linear_combination (Real.cosh b ^ 2 - 1) * hca + Real.sinh a ^ 2 * hcb -
      Real.sinh a ^ 2 * Real.sinh b ^ 2 * hsc
  rw [hΔ, Real.sqrt_sq (by positivity)]

/-- Algebra of the Sine Rule from the three relations `sin(angle) · sinh · sinh = D`. -/
theorem k92_sine_rule_alg {sa sb sc sα sβ sγ D : ℝ} (ha : 0 < sa) (hb : 0 < sb) (hc : 0 < sc)
    (hα : sα * (sb * sc) = D) (hβ : sβ * (sc * sa) = D) (hγ : sγ * (sa * sb) = D) :
    sa / sα = sb / sβ ∧ sb / sβ = sc / sγ := by
  by_cases hD : D = 0
  · have h1 : sα = 0 := by
      rw [hD] at hα
      exact (mul_eq_zero.1 hα).resolve_right (by positivity)
    have h2 : sβ = 0 := by
      rw [hD] at hβ
      exact (mul_eq_zero.1 hβ).resolve_right (by positivity)
    have h3 : sγ = 0 := by
      rw [hD] at hγ
      exact (mul_eq_zero.1 hγ).resolve_right (by positivity)
    simp [h1, h2, h3]
  · have e1 : sα = D / (sb * sc) := by rw [← hα]; field_simp
    have e2 : sβ = D / (sc * sa) := by rw [← hβ]; field_simp
    have e3 : sγ = D / (sa * sb) := by rw [← hγ]; field_simp
    rw [e1, e2, e3]
    constructor <;> field_simp

/-- Two-point form of distinctness: on a nondegenerate triangle the three vertices are distinct and the three
sides have positive `sinh`. -/
theorem k92_sinh_dist_pos {A B : ℍ} (h : A ≠ B) : 0 < Real.sinh (dist A B) :=
  Real.sinh_pos_iff.2 (dist_pos.2 h)

/-- `cayley z = 0` only at `z = i`. -/
theorem k92_cayley_eq_zero {z : ℍ} (h : LiZhongQC.cayley (z : ℂ) = 0) : z = UpperHalfPlane.I := by
  have hd : (z : ℂ) + I ≠ 0 := LiZhongQC.cayley_den_ne_zero z.im_pos
  unfold LiZhongQC.cayley at h
  rw [div_eq_zero_iff, sub_eq_zero] at h
  rcases h with h | h
  · exact UpperHalfPlane.ext h
  · exact absurd h hd

/-- The points `z ∈ ℍ` with `cayley z ∈ ℝ·u` (`u ≠ 0`) lie on one geodesic `geodArc p q` (the geodesic through `i`
with direction `u`): the imaginary axis if `u` is real, otherwise the semicircle `|z|² − 2m Re z − 1 = 0`,
`m = −Re u/Im u`. -/
theorem k92_geod_I {u : ℂ} (hu : u ≠ 0) :
    ∃ p ∈ pointsAtInfinity, ∃ q ∈ pointsAtInfinity, p ≠ q ∧
      ∀ z : ℍ, (∃ t : ℝ, LiZhongQC.cayley (z : ℂ) = t * u) → z ∈ geodArc p q := by
  -- the linear condition on `z`
  have hcond : ∀ z : ℍ, (∃ t : ℝ, LiZhongQC.cayley (z : ℂ) = t * u) →
      u.im * (Complex.normSq (z : ℂ) - 1) + 2 * u.re * z.re = 0 := by
    rintro z ⟨t, ht⟩
    have hd : (z : ℂ) + I ≠ 0 := LiZhongQC.cayley_den_ne_zero z.im_pos
    have hN : 0 < Complex.normSq ((z : ℂ) + I) := Complex.normSq_pos.2 hd
    have hc : LiZhongQC.cayley (z : ℂ) =
        ((Complex.normSq (z : ℂ) - 1 : ℝ) + (-2 * z.re : ℝ) * I) / (Complex.normSq ((z : ℂ) + I) : ℂ) := by
      unfold LiZhongQC.cayley
      rw [div_eq_div_iff hd (by exact_mod_cast hN.ne')]
      apply Complex.ext <;>
        simp [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] <;> ring
    rw [hc] at ht
    have hre := congrArg Complex.re ht
    have him := congrArg Complex.im ht
    simp only [Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at hre him
    field_simp at hre him
    have e1 : Complex.normSq (z : ℂ) - 1 = t * u.re * Complex.normSq ((z : ℂ) + I) := by linarith
    have e2 : -2 * z.re = t * u.im * Complex.normSq ((z : ℂ) + I) := by linarith
    rw [e1]
    linear_combination (-u.re) * e2
  by_cases him : u.im = 0
  · have hre : u.re ≠ 0 := fun h => hu (Complex.ext h him)
    refine ⟨OnePoint.infty, mem_insert _ _, ((0 : ℂ) : ExtPlane), mem_insert_of_mem _ ⟨0, by simp⟩,
      OnePoint.infty_ne_coe 0, fun z hz => ?_⟩
    have h := hcond z hz
    rw [him, zero_mul, zero_add] at h
    have hz0 : z.re = 0 := by
      rcases mul_eq_zero.1 h with h | h
      · exact absurd (by linarith : u.re = 0) hre
      · exact h
    show (z : ℂ).re = (0 : ℂ).re ∧ (0 : ℂ).im ≤ (z : ℂ).im
    simp [hz0, z.im_pos.le]
  · set m : ℝ := -u.re / u.im with hm
    set ρ : ℝ := √(m ^ 2 + 1) with hρ
    have hρ0 : 0 < ρ := Real.sqrt_pos.2 (by positivity)
    have hρ2 : ρ ^ 2 = m ^ 2 + 1 := Real.sq_sqrt (by positivity)
    refine ⟨(((m - ρ : ℝ) : ℂ) : ExtPlane), mem_insert_of_mem _ ⟨m - ρ, rfl⟩,
      (((m + ρ : ℝ) : ℂ) : ExtPlane), mem_insert_of_mem _ ⟨m + ρ, rfl⟩, ?_, fun z hz => ?_⟩
    · intro h
      have := OnePoint.coe_injective h
      have := congrArg Complex.re this
      simp at this
      linarith
    have h := hcond z hz
    have hcirc : Complex.normSq (z : ℂ) - 2 * m * z.re - 1 = 0 := by
      rw [hm]
      field_simp
      linear_combination h
    show z ∈ geodArcFinite ((m - ρ : ℝ) : ℂ) ((m + ρ : ℝ) : ℂ)
    have hne : ((m - ρ : ℝ) : ℂ).re ≠ ((m + ρ : ℝ) : ℂ).re := by simp; linarith
    have hcen : geodCentre ((m - ρ : ℝ) : ℂ) ((m + ρ : ℝ) : ℂ) = m := by
      have hρne : ρ ≠ 0 := hρ0.ne'
      unfold geodCentre
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.ofReal_re]
      field_simp
      ring_nf
      field_simp
    unfold geodArcFinite
    simp only [hne, ↓reduceIte]
    rw [hcen]
    have hzr : (z.re - m) ^ 2 + z.im ^ 2 = ρ ^ 2 := by
      rw [hρ2]
      have : Complex.normSq (z : ℂ) = z.re ^ 2 + z.im ^ 2 := by
        rw [Complex.normSq_apply]; simp [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring
      rw [this] at hcirc
      linear_combination hcirc
    refine ⟨?_, ?_, ?_⟩
    · rw [Complex.dist_eq, Complex.dist_eq]
      have h1 : ‖(z : ℂ) - (m : ℂ)‖ = ρ := by
        rw [← Real.sqrt_sq hρ0.le, ← hzr, Complex.norm_eq_sqrt_sq_add_sq]
        simp [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      have h2 : ‖((m - ρ : ℝ) : ℂ) - (m : ℂ)‖ = ρ := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        rw [show m - ρ - m = -ρ by ring, abs_neg, abs_of_pos hρ0]
      rw [h1, h2]
    · have : (z.re - m) ^ 2 ≤ ρ ^ 2 := by nlinarith [z.im_pos]
      have := abs_le_of_sq_le_sq' this hρ0.le
      simp only [Complex.ofReal_re]
      rw [min_eq_left (by linarith)]
      linarith [this.1]
    · have : (z.re - m) ^ 2 ≤ ρ ^ 2 := by nlinarith [z.im_pos]
      have := abs_le_of_sq_le_sq' this hρ0.le
      simp only [Complex.ofReal_re]
      rw [max_eq_right (by linarith)]
      linarith [this.2]

/-- An affine element of `SL(2,ℝ)` moving `C` to `i`: `z ↦ (z − Re C)/Im C`. -/
theorem k92_affine_SL (C : ℍ) : ∃ g : SL(2, ℝ), ∀ z : ℍ, ((g • z : ℍ) : ℂ) = ((z : ℂ) - C.re) / C.im := by
  have hy := C.im_pos
  have hs : 0 < √C.im := Real.sqrt_pos.2 hy
  have hss : √C.im * √C.im = C.im := Real.mul_self_sqrt hy.le
  have hdet : (!![(√C.im)⁻¹, -(C.re * (√C.im)⁻¹); 0, √C.im] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    field_simp
    ring
  set g : SL(2, ℝ) := ⟨!![(√C.im)⁻¹, -(C.re * (√C.im)⁻¹); 0, √C.im], hdet⟩ with hgdef
  refine ⟨g, fun z => ?_⟩
  rw [k92_coe_smul]
  have h00 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = (√C.im)⁻¹ := rfl
  have h01 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = -(C.re * (√C.im)⁻¹) := rfl
  have h10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := rfl
  have h11 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = √C.im := rfl
  rw [h00, h01, h10, h11]
  have hs' : (√C.im : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hy' : (C.im : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hss' : (√C.im : ℂ) * (√C.im : ℂ) = (C.im : ℂ) := by exact_mod_cast hss
  have hinv : ((√C.im : ℝ) : ℂ)⁻¹ * (√C.im : ℂ) = 1 := inv_mul_cancel₀ hs'
  push_cast
  rw [div_eq_div_iff (by simpa using hs') hy']
  linear_combination (-((z : ℂ) - C.re) * ((√C.im : ℝ) : ℂ)⁻¹) * hss' + (((z : ℂ) - C.re) * (√C.im : ℂ)) * hinv

/-- Transport of `geodArc` along the affine map `ζ ↦ Im C · ζ + Re C` (the inverse of `k92_affine_SL`). -/
theorem k92_geodArc_affine (C : ℍ) {g : SL(2, ℝ)} (hg : ∀ z : ℍ, ((g • z : ℍ) : ℂ) = ((z : ℂ) - C.re) / C.im)
    (p q : ExtPlane) {z : ℍ} (hz : g • z ∈ geodArc p q) :
    z ∈ geodArc (OnePoint.map (fun ζ : ℂ => (C.im : ℂ) * ζ + C.re) p)
      (OnePoint.map (fun ζ : ℂ => (C.im : ℂ) * ζ + C.re) q) := by
  have hy := C.im_pos
  have hre : (g • z).re = (z.re - C.re) / C.im := by
    rw [← UpperHalfPlane.coe_re, hg]
    simp [Complex.div_ofReal_re]
  have him : (g • z).im = z.im / C.im := by
    rw [← UpperHalfPlane.coe_im, hg]
    simp [Complex.div_ofReal_im]
  have hlin : ∀ a : ℂ, ((C.im : ℂ) * a + C.re).re = C.im * a.re + C.re ∧
      ((C.im : ℂ) * a + C.re).im = C.im * a.im := fun a => by simp
  have hfz : (z : ℂ) = (C.im : ℂ) * ((g • z : ℍ) : ℂ) + C.re := by
    rw [hg]
    have : (C.im : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    field_simp
    ring
  induction p using OnePoint.rec with
  | infty =>
    induction q using OnePoint.rec with
    | infty => exact absurd hz (by simp [geodArc])
    | coe b =>
      have hz' : (g • z).re = b.re ∧ b.im ≤ (g • z).im := hz
      show z.re = ((C.im : ℂ) * b + C.re).re ∧ ((C.im : ℂ) * b + C.re).im ≤ z.im
      rw [hre, him] at hz'
      obtain ⟨h1, h2⟩ := hz'
      rw [(hlin b).1, (hlin b).2]
      rw [div_eq_iff hy.ne'] at h1
      rw [le_div_iff₀ hy] at h2
      constructor <;> nlinarith
  | coe a =>
    induction q using OnePoint.rec with
    | infty =>
      have hz' : (g • z).re = a.re ∧ a.im ≤ (g • z).im := hz
      show z.re = ((C.im : ℂ) * a + C.re).re ∧ ((C.im : ℂ) * a + C.re).im ≤ z.im
      rw [hre, him] at hz'
      obtain ⟨h1, h2⟩ := hz'
      rw [(hlin a).1, (hlin a).2]
      rw [div_eq_iff hy.ne'] at h1
      rw [le_div_iff₀ hy] at h2
      constructor <;> nlinarith
    | coe b =>
      change g • z ∈ geodArcFinite a b at hz
      show z ∈ geodArcFinite ((C.im : ℂ) * a + C.re) ((C.im : ℂ) * b + C.re)
      unfold geodArcFinite at hz ⊢
      rw [(hlin a).1, (hlin b).1]
      by_cases hab : a.re = b.re
      · have hab' : C.im * a.re + C.re = C.im * b.re + C.re := by rw [hab]
        rw [ite_eq_left hab] at hz
        rw [ite_eq_left hab']
        obtain ⟨h1, h2, h3⟩ := hz
        change (g • z).re = a.re at h1
        change min a.im b.im ≤ (g • z).im at h2
        change (g • z).im ≤ max a.im b.im at h3
        rw [hre] at h1
        rw [him] at h2 h3
        rw [div_eq_iff hy.ne'] at h1
        rw [le_div_iff₀ hy] at h2
        rw [div_le_iff₀ hy] at h3
        refine ⟨?_, ?_, ?_⟩
        · show z.re = C.im * a.re + C.re
          linarith
        · show min ((C.im : ℂ) * a + C.re).im ((C.im : ℂ) * b + C.re).im ≤ z.im
          rw [(hlin a).2, (hlin b).2, ← mul_min_of_nonneg _ _ hy.le]
          linarith
        · show z.im ≤ max ((C.im : ℂ) * a + C.re).im ((C.im : ℂ) * b + C.re).im
          rw [(hlin a).2, (hlin b).2, ← mul_max_of_nonneg _ _ hy.le]
          linarith
      · have hab' : ¬ C.im * a.re + C.re = C.im * b.re + C.re := by
          intro h
          apply hab
          have : C.im * a.re = C.im * b.re := by linarith
          exact mul_left_cancel₀ hy.ne' this
        simp only [hab, ↓reduceIte] at hz
        simp only [hab', ↓reduceIte]
        obtain ⟨h1, h2, h3⟩ := hz
        change min a.re b.re ≤ (g • z).re at h2
        change (g • z).re ≤ max a.re b.re at h3
        rw [hre, le_div_iff₀ hy] at h2
        rw [hre, div_le_iff₀ hy] at h3
        have hcen : geodCentre ((C.im : ℂ) * a + C.re) ((C.im : ℂ) * b + C.re) =
            C.im * geodCentre a b + C.re := by
          have hd : b.re - a.re ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
          unfold geodCentre
          rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
            Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply, (hlin a).1, (hlin a).2,
            (hlin b).1, (hlin b).2]
          field_simp
          ring
        refine ⟨?_, ?_, ?_⟩
        · show dist (z : ℂ) ((geodCentre ((C.im : ℂ) * a + C.re) ((C.im : ℂ) * b + C.re) : ℝ) : ℂ) =
            dist ((C.im : ℂ) * a + C.re) ((geodCentre ((C.im : ℂ) * a + C.re) ((C.im : ℂ) * b + C.re) : ℝ) : ℂ)
          rw [hcen, hfz, Complex.dist_eq, Complex.dist_eq]
          have e1 : (C.im : ℂ) * ((g • z : ℍ) : ℂ) + C.re - ((C.im * geodCentre a b + C.re : ℝ) : ℂ) =
              (C.im : ℂ) * (((g • z : ℍ) : ℂ) - (geodCentre a b : ℂ)) := by push_cast; ring
          have e2 : (C.im : ℂ) * a + C.re - ((C.im * geodCentre a b + C.re : ℝ) : ℂ) =
              (C.im : ℂ) * (a - (geodCentre a b : ℂ)) := by push_cast; ring
          rw [e1, e2, norm_mul, norm_mul, ← Complex.dist_eq, ← Complex.dist_eq]
          change dist ((g • z : ℍ) : ℂ) (geodCentre a b : ℂ) = dist a (geodCentre a b : ℂ) at h1
          rw [h1]
        · show min (C.im * a.re + C.re) (C.im * b.re + C.re) ≤ z.re
          rw [min_add_add_right, ← mul_min_of_nonneg _ _ hy.le]
          linarith
        · show z.re ≤ max (C.im * a.re + C.re) (C.im * b.re + C.re)
          rw [max_add_add_right, ← mul_max_of_nonneg _ _ hy.le]
          linarith

/-- The image of a point at infinity under `ζ ↦ Im C · ζ + Re C` is a point at infinity. -/
theorem k92_map_pointsAtInfinity (C : ℍ) {p : ExtPlane} (hp : p ∈ pointsAtInfinity) :
    OnePoint.map (fun ζ : ℂ => (C.im : ℂ) * ζ + C.re) p ∈ pointsAtInfinity := by
  rcases hp with rfl | ⟨x, rfl⟩
  · exact mem_insert _ _
  · refine mem_insert_of_mem _ ⟨C.im * x + C.re, ?_⟩
    show (((C.im * x + C.re : ℝ) : ℂ) : ExtPlane) = (((C.im : ℂ) * x + C.re : ℂ) : ExtPlane)
    push_cast
    rfl

/-- **Collinearity.** If the angle at `C` between the directions towards `A` and `B` has sine `0`
(`A, B ≠ C`), then `A, B, C` lie on one geodesic. -/
theorem k92_collinear {A B C : ℍ} (hA : A ≠ C) (hB : B ≠ C)
    (h : Real.sin (hypAngle C (toExtH A) (toExtH B)) = 0) :
    ∃ p ∈ pointsAtInfinity, ∃ q ∈ pointsAtInfinity, p ≠ q ∧ ({A, B, C} : Set ℍ) ⊆ geodArc p q := by
  obtain ⟨g, hg⟩ := k92_affine_SL C
  have hy := C.im_pos
  have hgC : g • C = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    rw [hg, UpperHalfPlane.coe_I]
    have hy' : (C.im : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    rw [div_eq_iff hy']
    apply Complex.ext <;> simp [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  have hang := k92_hypAngle_smul g C A B
  rw [hgC] at hang
  set α := LiZhongQC.cayley ((g • A : ℍ) : ℂ) with hα
  set β := LiZhongQC.cayley ((g • B : ℍ) : ℂ) with hβ
  have hα0 : α ≠ 0 := fun h0 => hA (smul_left_cancel g ((k92_cayley_eq_zero h0).trans hgC.symm))
  have hβ0 : β ≠ 0 := fun h0 => hB (smul_left_cancel g ((k92_cayley_eq_zero h0).trans hgC.symm))
  have hangI : hypAngle UpperHalfPlane.I (toExtH (g • A)) (toExtH (g • B)) = InnerProductGeometry.angle α β := by
    unfold hypAngle
    rw [k92_tangentDir_I, k92_tangentDir_I, mul_comm I, mul_comm I, k92_angle_mul_unit _ _ _ Complex.norm_I]
  rw [hangI] at hang
  rw [← hang] at h
  have h0 := InnerProductGeometry.angle_nonneg α β
  have hπ := InnerProductGeometry.angle_le_pi α β
  obtain ⟨r, hr⟩ : ∃ r : ℝ, β = r * α := by
    by_cases hpi : InnerProductGeometry.angle α β = π
    · obtain ⟨-, r, -, hr⟩ := InnerProductGeometry.angle_eq_pi_iff.1 hpi
      exact ⟨r, by rw [hr, Complex.real_smul]⟩
    · have hlt : InnerProductGeometry.angle α β < π := lt_of_le_of_ne hπ hpi
      have hz : InnerProductGeometry.angle α β = 0 :=
        (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith) hlt).1 h
      obtain ⟨-, r, -, hr⟩ := InnerProductGeometry.angle_eq_zero_iff.1 hz
      exact ⟨r, by rw [hr, Complex.real_smul]⟩
  obtain ⟨p, hp, q, hq, hpq, hsub⟩ := k92_geod_I hα0
  have hAg := hsub (g • A) ⟨1, by rw [← hα]; simp⟩
  have hBg := hsub (g • B) ⟨r, hr⟩
  have hCg : g • C ∈ geodArc p q := by
    rw [hgC]
    refine hsub _ ⟨0, ?_⟩
    rw [Complex.ofReal_zero, zero_mul, UpperHalfPlane.coe_I]
    unfold LiZhongQC.cayley
    simp
  have hinj : Function.Injective (OnePoint.map (fun ζ : ℂ => (C.im : ℂ) * ζ + C.re)) := by
    have hy' : (C.im : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hf : Function.Injective (fun ζ : ℂ => (C.im : ℂ) * ζ + C.re) := fun a b hab =>
      mul_left_cancel₀ hy' (add_right_cancel hab)
    exact Option.map_injective hf
  refine ⟨_, k92_map_pointsAtInfinity C hp, _, k92_map_pointsAtInfinity C hq, fun he => hpq (hinj he), ?_⟩
  intro w hw
  rcases hw with hw | hw | hw <;> rw [hw]
  · exact k92_geodArc_affine C hg p q hAg
  · exact k92_geodArc_affine C hg p q hBg
  · exact k92_geodArc_affine C hg p q hCg

/-- The tangent direction at `C` towards a point `A ≠ C` of ℍ is nonzero. -/
theorem k92_tangentDir_ne_zero {A C : ℍ} (h : A ≠ C) : tangentDir C (toExtH A) ≠ 0 := by
  unfold tangentDir toExtH
  simp only [OnePoint.elim_some]
  have h1 : (A : ℂ) - C ≠ 0 := sub_ne_zero.2 (fun e => h (UpperHalfPlane.ext e))
  have h2 : (A : ℂ) - conj (C : ℂ) ≠ 0 := by
    intro e
    have := congrArg Complex.im e
    simp only [sub_im, conj_im, zero_im, UpperHalfPlane.coe_im] at this
    linarith [A.im_pos, C.im_pos]
  exact div_ne_zero (mul_ne_zero I_ne_zero h1) h2

/-- Any two points of ℍ lie on one geodesic. -/
theorem k92_two_points (P Q : ℍ) :
    ∃ p ∈ pointsAtInfinity, ∃ q ∈ pointsAtInfinity, p ≠ q ∧ ({P, Q} : Set ℍ) ⊆ geodArc p q := by
  by_cases hPQ : P = Q
  · refine ⟨OnePoint.infty, mem_insert _ _, (((P.re : ℝ) : ℂ) : ExtPlane), mem_insert_of_mem _ ⟨P.re, rfl⟩,
      OnePoint.infty_ne_coe _, ?_⟩
    rw [← hPQ, pair_eq_singleton, singleton_subset_iff]
    show P.re = ((P.re : ℝ) : ℂ).re ∧ ((P.re : ℝ) : ℂ).im ≤ P.im
    simp [P.im_pos.le]
  · have hsin : Real.sin (hypAngle Q (toExtH P) (toExtH P)) = 0 := by
      unfold hypAngle
      rw [InnerProductGeometry.angle_self (k92_tangentDir_ne_zero hPQ), Real.sin_zero]
    obtain ⟨p, hp, q, hq, hpq, hsub⟩ := k92_collinear hPQ hPQ hsin
    refine ⟨p, hp, q, hq, hpq, ?_⟩
    intro w hw
    rcases hw with hw | hw
    · exact hsub (by rw [hw]; exact mem_insert _ _)
    · exact hsub (by rw [hw]; exact mem_insert_of_mem _ (mem_insert_of_mem _ rfl))

/-- The vertices of a nondegenerate triangle are distinct. -/
theorem k92_nondeg_ne {A B C : ℍ} (h : IsNondegenerateTriangle A B C) : A ≠ B ∧ B ≠ C ∧ C ≠ A := by
  refine ⟨fun e => h ?_, fun e => h ?_, fun e => h ?_⟩
  · obtain ⟨p, hp, q, hq, hpq, hs⟩ := k92_two_points A C
    refine ⟨p, hp, q, hq, hpq, ?_⟩
    rw [← e, insert_eq_of_mem (mem_insert _ _)]
    exact hs
  · obtain ⟨p, hp, q, hq, hpq, hs⟩ := k92_two_points A B
    refine ⟨p, hp, q, hq, hpq, ?_⟩
    rw [← e]
    intro w hw
    rcases hw with hw | hw | hw
    · exact hs (by rw [hw]; exact mem_insert _ _)
    · exact hs (by rw [hw]; exact mem_insert_of_mem _ rfl)
    · exact hs (by rw [hw]; exact mem_insert_of_mem _ rfl)
  · obtain ⟨p, hp, q, hq, hpq, hs⟩ := k92_two_points A B
    refine ⟨p, hp, q, hq, hpq, ?_⟩
    rw [e]
    intro w hw
    rcases hw with hw | hw | hw
    · exact hs (by rw [hw]; exact mem_insert _ _)
    · exact hs (by rw [hw]; exact mem_insert_of_mem _ rfl)
    · exact hs (by rw [hw]; exact mem_insert _ _)

/-- Auxiliary. Angles `hypAngle` lie in `[0, π]`. -/
theorem k92_hypAngle_mem (z : ℍ) (p q : ExtPlane) : 0 ≤ hypAngle z p q ∧ hypAngle z p q ≤ π :=
  ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩

/-- Real Möbius maps send points at infinity to points at infinity. -/
theorem k92_mobius_pointsAtInfinity (g : SL(2, ℝ)) {p : ExtPlane} (hp : p ∈ pointsAtInfinity) :
    LiZhongQC.mobiusExt ((g 0 0 : ℝ) : ℂ) ((g 0 1 : ℝ) : ℂ) ((g 1 0 : ℝ) : ℂ) ((g 1 1 : ℝ) : ℂ) p ∈
      pointsAtInfinity := by
  rcases hp with rfl | ⟨x, rfl⟩
  · by_cases hc : ((g 1 0 : ℝ) : ℂ) = 0
    · rw [LiZhongQC.mobiusExt_infty_of_eq hc]; exact mem_insert _ _
    · rw [LiZhongQC.mobiusExt_infty_of_ne hc]
      exact mem_insert_of_mem _ ⟨g 0 0 / g 1 0, by push_cast; rfl⟩
  · by_cases hc : ((g 1 0 : ℝ) : ℂ) * (x : ℂ) + ((g 1 1 : ℝ) : ℂ) = 0
    · rw [LiZhongQC.mobiusExt_coe_of_eq_zero hc]; exact mem_insert _ _
    · rw [LiZhongQC.mobiusExt_coe hc]
      exact mem_insert_of_mem _ ⟨(g 0 0 * x + g 0 1) / (g 1 0 * x + g 1 1), by
        unfold LiZhongQC.mobiusFn; push_cast; rfl⟩

/-- The tangent-direction transformation of `k92_tangentDir_smul` for points at infinity. -/
theorem k92_tangentDir_smul_ext (g : SL(2, ℝ)) (z : ℍ) {p : ExtPlane} (hp : p ∈ pointsAtInfinity) :
    tangentDir (g • z)
        (LiZhongQC.mobiusExt ((g 0 0 : ℝ) : ℂ) ((g 0 1 : ℝ) : ℂ) ((g 1 0 : ℝ) : ℂ) ((g 1 1 : ℝ) : ℂ) p) =
      tangentDir z p *
        ((((g 1 0 : ℝ) : ℂ) * conj (z : ℂ) + ((g 1 1 : ℝ) : ℂ)) / (((g 1 0 : ℝ) : ℂ) * z + ((g 1 1 : ℝ) : ℂ))) := by
  have hz := k92_den_ne_zero g z
  set a : ℂ := ((g 0 0 : ℝ) : ℂ)
  set b : ℂ := ((g 0 1 : ℝ) : ℂ)
  set c : ℂ := ((g 1 0 : ℝ) : ℂ)
  set d : ℂ := ((g 1 1 : ℝ) : ℂ)
  have hdet : a * d - b * c = 1 := by
    have h := g.prop
    rw [Matrix.det_fin_two] at h
    simp only [a, b, c, d]
    exact_mod_cast h
  have hz' : c * (z : ℂ) + d ≠ 0 := hz
  have hzc : c * conj (z : ℂ) + d ≠ 0 := by
    intro h0
    apply hz'
    have := congrArg conj h0
    simpa [a, b, c, d, map_add, map_mul, Complex.conj_ofReal] using this
  have hgz : ((g • z : ℍ) : ℂ) = (a * z + b) / (c * z + d) := k92_coe_smul g z
  have hconj : conj ((a * z + b) / (c * z + d)) = (a * conj (z : ℂ) + b) / (c * conj (z : ℂ) + d) := by
    simp [a, b, c, d, map_div₀, map_add, map_mul, Complex.conj_ofReal]
  rcases hp with rfl | ⟨x, rfl⟩
  · by_cases hc : c = 0
    · rw [LiZhongQC.mobiusExt_infty_of_eq hc]
      have hd : d ≠ 0 := by
        intro hd0
        rw [hc, hd0] at hdet
        simp at hdet
      unfold tangentDir
      simp only [hc, zero_mul, zero_add, div_self hd, mul_one]
      rfl
    · rw [LiZhongQC.mobiusExt_infty_of_ne hc]
      unfold tangentDir
      simp only [OnePoint.elim_some]
      show I * (a / c - ((g • z : ℍ) : ℂ)) / (a / c - conj ((g • z : ℍ) : ℂ)) =
        I * ((c * conj (z : ℂ) + d) / (c * z + d))
      rw [hgz, hconj]
      have e1 : a / c - (a * z + b) / (c * z + d) = 1 / (c * (c * z + d)) := by
        rw [div_sub_div _ _ hc hz', div_eq_div_iff (mul_ne_zero hc hz') (mul_ne_zero hc hz')]
        linear_combination (c * (c * z + d)) * hdet
      have e2 : a / c - (a * conj (z : ℂ) + b) / (c * conj (z : ℂ) + d) = 1 / (c * (c * conj (z : ℂ) + d)) := by
        rw [div_sub_div _ _ hc hzc, div_eq_div_iff (mul_ne_zero hc hzc) (mul_ne_zero hc hzc)]
        linear_combination (c * (c * conj (z : ℂ) + d)) * hdet
      rw [e1, e2]
      field_simp
  · by_cases hx : c * (x : ℂ) + d = 0
    · rw [LiZhongQC.mobiusExt_coe_of_eq_zero hx]
      unfold tangentDir
      simp only [OnePoint.elim_some]
      show I = I * ((x : ℂ) - z) / ((x : ℂ) - conj (z : ℂ)) * ((c * conj (z : ℂ) + d) / (c * z + d))
      have hc : c ≠ 0 := by
        intro hc0
        rw [hc0, zero_mul, zero_add] at hx
        rw [hc0, hx] at hdet
        simp at hdet
      have hxz : (x : ℂ) - conj (z : ℂ) ≠ 0 := by
        intro h0
        have := congrArg Complex.im h0
        simp at this
        linarith [z.im_pos]
      have hxz' : (x : ℂ) - z ≠ 0 := by
        intro h0
        have := congrArg Complex.im h0
        simp at this
        linarith [z.im_pos]
      have hd : d = -(c * x) := by linear_combination hx
      have hzx : (z : ℂ) - x ≠ 0 := fun h0 => hxz' (by linear_combination -h0)
      have hzcx : conj (z : ℂ) - x ≠ 0 := fun h0 => hxz (by linear_combination -h0)
      have e : (c * conj (z : ℂ) + d) / (c * z + d) = (conj (z : ℂ) - x) / ((z : ℂ) - x) := by
        rw [hd, show c * conj (z : ℂ) + -(c * x) = c * (conj (z : ℂ) - x) by ring,
          show c * (z : ℂ) + -(c * x) = c * ((z : ℂ) - x) by ring, mul_div_mul_left _ _ hc]
      rw [e]
      field_simp
      ring
    · rw [LiZhongQC.mobiusExt_coe hx]
      unfold tangentDir LiZhongQC.mobiusFn
      simp only [OnePoint.elim_some]
      rw [hgz, hconj]
      have hxz : (x : ℂ) - conj (z : ℂ) ≠ 0 := by
        intro h0
        have := congrArg Complex.im h0
        simp at this
        linarith [z.im_pos]
      have hgx : (a * x + b) / (c * x + d) - (a * conj (z : ℂ) + b) / (c * conj (z : ℂ) + d) =
          ((x : ℂ) - conj (z : ℂ)) / ((c * x + d) * (c * conj (z : ℂ) + d)) := by
        rw [div_sub_div _ _ hx hzc]
        congr 1
        linear_combination ((x : ℂ) - conj (z : ℂ)) * hdet
      have hgz' : (a * x + b) / (c * x + d) - (a * z + b) / (c * z + d) =
          ((x : ℂ) - z) / ((c * x + d) * (c * z + d)) := by
        rw [div_sub_div _ _ hx hz']
        congr 1
        linear_combination ((x : ℂ) - z) * hdet
      rw [hgx, hgz']
      generalize c * (z : ℂ) + d = Q at hz' ⊢
      generalize c * (x : ℂ) + d = P at hx ⊢
      generalize c * conj (z : ℂ) + d = Q' at hzc ⊢
      generalize (x : ℂ) - conj (z : ℂ) = Y at hxz ⊢
      field_simp

/-- `SL(2,ℝ)` preserves angles between a direction towards a point of ℍ and one towards a point at infinity. -/
theorem k92_hypAngle_smul_ext (g : SL(2, ℝ)) (z x : ℍ) {p : ExtPlane} (hp : p ∈ pointsAtInfinity) :
    hypAngle (g • z) (toExtH (g • x))
        (LiZhongQC.mobiusExt ((g 0 0 : ℝ) : ℂ) ((g 0 1 : ℝ) : ℂ) ((g 1 0 : ℝ) : ℂ) ((g 1 1 : ℝ) : ℂ) p) =
      hypAngle z (toExtH x) p := by
  unfold hypAngle
  rw [k92_tangentDir_smul, k92_tangentDir_smul_ext g z hp, k92_angle_mul_unit]
  have hz := k92_den_ne_zero g z
  rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.2 hz)]
  have : ((g 1 0 : ℝ) : ℂ) * conj (z : ℂ) + ((g 1 1 : ℝ) : ℂ) =
      conj (((g 1 0 : ℝ) : ℂ) * z + ((g 1 1 : ℝ) : ℂ)) := by
    simp [map_add, map_mul, Complex.conj_ofReal]
  rw [this, Complex.norm_conj]

/-- Rotation about `i`: for every `θ` there is `R ∈ SL(2,ℝ)` fixing `i` with `cayley(R z) = e^{2iθ} cayley z`. -/
theorem k92_rotation (θ : ℝ) : ∃ R : SL(2, ℝ), R • UpperHalfPlane.I = UpperHalfPlane.I ∧
    ∀ z : ℍ, LiZhongQC.cayley ((R • z : ℍ) : ℂ) = Complex.exp (θ * I) ^ 2 * LiZhongQC.cayley (z : ℂ) := by
  have hdet : (!![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  set R : SL(2, ℝ) := ⟨!![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ], hdet⟩
  have h00 : (R : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = Real.cos θ := rfl
  have h01 : (R : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = Real.sin θ := rfl
  have h10 : (R : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -Real.sin θ := rfl
  have h11 : (R : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = Real.cos θ := rfl
  have hE : Complex.exp (θ * I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hcs : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  set c : ℂ := ((Real.cos θ : ℝ) : ℂ)
  set sn : ℂ := ((Real.sin θ : ℝ) : ℂ)
  set e : ℂ := c + sn * I with he
  set e' : ℂ := c - sn * I with he'
  have hee : e * e' = 1 := by
    rw [he, he']
    linear_combination hcs - sn ^ 2 * I_sq
  have he'0 : e' ≠ 0 := right_ne_zero_of_mul_eq_one hee
  have hq : e ^ 2 = e / e' := by
    rw [eq_div_iff he'0]
    linear_combination e * hee
  have key : ∀ z : ℍ, LiZhongQC.cayley ((R • z : ℍ) : ℂ) = Complex.exp (θ * I) ^ 2 * LiZhongQC.cayley (z : ℂ) := by
    intro z
    have hd := k92_den_ne_zero R z
    rw [h10, h11, Complex.ofReal_neg] at hd
    have hdz : (z : ℂ) + I ≠ 0 := LiZhongQC.cayley_den_ne_zero z.im_pos
    rw [k92_coe_smul, h00, h01, h10, h11, Complex.ofReal_neg, hE]
    unfold LiZhongQC.cayley
    have h1 : (c * z + sn) / (-sn * z + c) - I = e * ((z : ℂ) - I) / (-sn * z + c) := by
      rw [eq_div_iff hd, sub_mul, div_mul_cancel₀ _ hd, he]
      linear_combination sn * I_sq
    have h2 : (c * z + sn) / (-sn * z + c) + I = e' * ((z : ℂ) + I) / (-sn * z + c) := by
      rw [eq_div_iff hd, add_mul, div_mul_cancel₀ _ hd, he']
      linear_combination sn * I_sq
    rw [h1, h2, div_div_div_cancel_right₀ hd, hq, div_mul_div_comm]
  refine ⟨R, ?_, key⟩
  apply UpperHalfPlane.ext
  rw [k92_coe_smul, h00, h01, h10, h11, UpperHalfPlane.coe_I, Complex.ofReal_neg]
  have hd : -sn * I + c ≠ 0 := by
    have := k92_den_ne_zero R UpperHalfPlane.I
    rwa [h10, h11, UpperHalfPlane.coe_I, Complex.ofReal_neg] at this
  rw [div_eq_iff hd]
  linear_combination sn * I_sq

/-- The real inner product of `a + bi` and `c + di` is `ac + bd`. -/
theorem k92_inner_coords (a b c d : ℝ) :
    inner ℝ ((a : ℂ) + (b : ℂ) * I) ((c : ℂ) + (d : ℂ) * I) = a * c + b * d := by
  rw [Complex.inner]
  simp
  ring

/-- Auxiliary. `|a + bi| = √(a² + b²)`. -/
theorem k92_norm_coords (a b : ℝ) : ‖(a : ℂ) + (b : ℂ) * I‖ = √(a ^ 2 + b ^ 2) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp

/-- The angle of parallelism on the imaginary axis: `A = ik` (`k > 1`), right angle at `i` towards an ideal `C`. -/
theorem k92_parallel_axis {k : ℝ} (hk : 1 < k) (A : ℍ) (hA : (A : ℂ) = k * I) {C : ExtPlane}
    (hC : C ∈ pointsAtInfinity) (hB : hypAngle UpperHalfPlane.I (toExtH A) C = π / 2) :
    Real.cos (hypAngle A (toExtH UpperHalfPlane.I) C) = (k ^ 2 - 1) / (k ^ 2 + 1) := by
  have hk0 : 0 < k := by linarith
  set t : ℝ := (k - 1) / (k + 1) with ht
  have ht0 : 0 < t := div_pos (by linarith) (by linarith)
  have hd0 : tangentDir UpperHalfPlane.I (toExtH A) = ((0 : ℝ) : ℂ) + (t : ℂ) * I := by
    unfold tangentDir toExtH
    simp only [OnePoint.elim_some]
    rw [hA, UpperHalfPlane.coe_I, Complex.conj_I]
    have h1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : k + 1 ≠ 0)
    rw [mul_div_assoc, show (k : ℂ) * I - I = ((k : ℂ) - 1) * I by ring,
      show (k : ℂ) * I - -I = ((k : ℂ) + 1) * I by ring, mul_div_mul_right _ _ I_ne_zero, ht]
    push_cast
    ring
  -- `C` is `±1`
  have hx : ∃ x : ℝ, C = (((x : ℂ)) : ExtPlane) ∧ x ^ 2 = 1 := by
    rcases hC with rfl | ⟨x, rfl⟩
    · exfalso
      have h1 : tangentDir UpperHalfPlane.I OnePoint.infty = I := rfl
      unfold hypAngle at hB
      rw [hd0, h1] at hB
      have hc := InnerProductGeometry.cos_angle (((0 : ℝ) : ℂ) + (t : ℂ) * I) I
      rw [hB, Real.cos_pi_div_two, Complex.inner] at hc
      have hn : ‖((0 : ℝ) : ℂ) + (t : ℂ) * I‖ = t := by
        simp [abs_of_pos ht0]
      rw [hn, Complex.norm_I] at hc
      simp at hc
      have : t / t = 0 := by simpa using hc.symm
      rw [div_self ht0.ne'] at this
      exact one_ne_zero this
    · refine ⟨x, rfl, ?_⟩
      have hdx : tangentDir UpperHalfPlane.I (((x : ℂ)) : ExtPlane) =
          ((2 * x / (x ^ 2 + 1) : ℝ) : ℂ) + ((x ^ 2 - 1) / (x ^ 2 + 1) : ℝ) * I := by
        unfold tangentDir
        simp only [OnePoint.elim_some]
        rw [UpperHalfPlane.coe_I, Complex.conj_I]
        have h1 : (x : ℂ) + I ≠ 0 := fun h => by simpa using congrArg Complex.im h
        have h2 : ((x : ℂ) ^ 2 + 1) ≠ 0 := by exact_mod_cast (by positivity : x ^ 2 + 1 ≠ 0)
        push_cast
        rw [sub_neg_eq_add]
        field_simp
        ring_nf
        rw [I_sq]
        ring
      unfold hypAngle at hB
      rw [hd0, hdx] at hB
      have hc := InnerProductGeometry.cos_angle (((0 : ℝ) : ℂ) + (t : ℂ) * I)
        (((2 * x / (x ^ 2 + 1) : ℝ) : ℂ) + ((x ^ 2 - 1) / (x ^ 2 + 1) : ℝ) * I)
      rw [hB, Real.cos_pi_div_two, k92_inner_coords, k92_norm_coords, k92_norm_coords] at hc
      have hn0 : 0 < √((0 : ℝ) ^ 2 + t ^ 2) := Real.sqrt_pos.2 (by positivity)
      have hn1 : 0 < √((2 * x / (x ^ 2 + 1)) ^ 2 + ((x ^ 2 - 1) / (x ^ 2 + 1)) ^ 2) := by
        apply Real.sqrt_pos.2
        have : (2 * x / (x ^ 2 + 1)) ^ 2 + ((x ^ 2 - 1) / (x ^ 2 + 1)) ^ 2 = 1 := by
          field_simp; ring
        rw [this]; exact one_pos
      have h0 : 0 * (2 * x / (x ^ 2 + 1)) + t * ((x ^ 2 - 1) / (x ^ 2 + 1)) = 0 := by
        have := hc.symm
        rw [div_eq_zero_iff] at this
        rcases this with h | h
        · exact h
        · exact absurd h (by positivity)
      have h1 : (x ^ 2 - 1) / (x ^ 2 + 1) = 0 := by
        rw [zero_mul, zero_add] at h0
        exact (mul_eq_zero.1 h0).resolve_left ht0.ne'
      rw [div_eq_zero_iff] at h1
      rcases h1 with h1 | h1
      · linarith
      · exact absurd h1 (by positivity)
  obtain ⟨x, rfl, hx2⟩ := hx
  have hd1 : tangentDir A (toExtH UpperHalfPlane.I) = ((0 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
    unfold tangentDir toExtH
    simp only [OnePoint.elim_some]
    rw [hA, UpperHalfPlane.coe_I]
    have h1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : k + 1 ≠ 0)
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_div_assoc,
      show I - (k : ℂ) * I = (1 - (k : ℂ)) * I by ring,
      show I - (k : ℂ) * -I = ((k : ℂ) + 1) * I by ring, mul_div_mul_right _ _ I_ne_zero, ht]
    push_cast
    ring
  have hd2 : tangentDir A (((x : ℂ)) : ExtPlane) =
      ((2 * k * x / (x ^ 2 + k ^ 2) : ℝ) : ℂ) + ((x ^ 2 - k ^ 2) / (x ^ 2 + k ^ 2) : ℝ) * I := by
    unfold tangentDir
    simp only [OnePoint.elim_some]
    rw [hA, map_mul, Complex.conj_ofReal, Complex.conj_I]
    have h2 : ((x : ℂ) ^ 2 + (k : ℂ) ^ 2) ≠ 0 := by exact_mod_cast (by positivity : x ^ 2 + k ^ 2 ≠ 0)
    have h3 : (x : ℂ) - (k : ℂ) * -I ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith
    rw [div_eq_iff h3]
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring_nf
  unfold hypAngle
  rw [hd1, hd2, InnerProductGeometry.cos_angle, k92_inner_coords, k92_norm_coords, k92_norm_coords]
  have hn1 : √((0 : ℝ) ^ 2 + (-t) ^ 2) = t := by
    rw [show (0 : ℝ) ^ 2 + (-t) ^ 2 = t ^ 2 by ring, Real.sqrt_sq ht0.le]
  have hn2 : √((2 * k * x / (x ^ 2 + k ^ 2)) ^ 2 + ((x ^ 2 - k ^ 2) / (x ^ 2 + k ^ 2)) ^ 2) = 1 := by
    rw [show (2 * k * x / (x ^ 2 + k ^ 2)) ^ 2 + ((x ^ 2 - k ^ 2) / (x ^ 2 + k ^ 2)) ^ 2 = 1 by
      field_simp; ring, Real.sqrt_one]
  rw [hn1, hn2, hx2, ht]
  have hk1 : k - 1 ≠ 0 := by linarith
  have hk2 : k + 1 ≠ 0 := by linarith
  have hk3 : 1 + k ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The angle of parallelism at `i`: `B = i`, right angle at `i` towards `A` and an ideal `C`. -/
theorem k92_parallel_cos_I {A : ℍ} (hA : A ≠ UpperHalfPlane.I) {C : ExtPlane} (hC : C ∈ pointsAtInfinity)
    (hB : hypAngle UpperHalfPlane.I (toExtH A) C = π / 2) :
    Real.cos (hypAngle A (toExtH UpperHalfPlane.I) C) = Real.tanh (dist A UpperHalfPlane.I) := by
  set α := LiZhongQC.cayley (A : ℂ) with hα
  have hα0 : α ≠ 0 := fun h0 => hA (k92_cayley_eq_zero h0)
  have hα1 : ‖α‖ < 1 := mem_ball_zero_iff.1 (LiZhongQC.cayley_mem_unitDisc A.im_pos)
  have hr0 : 0 < ‖α‖ := norm_pos_iff.2 hα0
  obtain ⟨R, hRI, hRc⟩ := k92_rotation (-Complex.arg α / 2)
  have hrot : LiZhongQC.cayley ((R • A : ℍ) : ℂ) = (‖α‖ : ℂ) := by
    rw [hRc, ← hα]
    have h := Complex.norm_mul_exp_arg_mul_I α
    have h0 : (((-Complex.arg α / 2 : ℝ)) : ℂ) * I + ((-Complex.arg α / 2 : ℝ) : ℂ) * I +
        (Complex.arg α : ℂ) * I = 0 := by
      push_cast
      ring
    calc Complex.exp (((-Complex.arg α / 2 : ℝ) : ℂ) * I) ^ 2 * α =
          Complex.exp (((-Complex.arg α / 2 : ℝ) : ℂ) * I) ^ 2 * ((‖α‖ : ℂ) * Complex.exp (Complex.arg α * I)) := by
          rw [h]
      _ = (‖α‖ : ℂ) * Complex.exp ((((-Complex.arg α / 2 : ℝ)) : ℂ) * I + ((-Complex.arg α / 2 : ℝ) : ℂ) * I +
          (Complex.arg α : ℂ) * I) := by
          rw [Complex.exp_add, Complex.exp_add]; ring
      _ = (‖α‖ : ℂ) := by rw [h0, Complex.exp_zero, mul_one]
  set r := ‖α‖ with hr
  set k : ℝ := (1 + r) / (1 - r) with hk
  have hk1 : 1 < k := by rw [hk, lt_div_iff₀ (by linarith)]; linarith
  have hA2 : ((R • A : ℍ) : ℂ) = k * I := by
    have hd : ((R • A : ℍ) : ℂ) + I ≠ 0 := LiZhongQC.cayley_den_ne_zero (R • A).im_pos
    unfold LiZhongQC.cayley at hrot
    rw [div_eq_iff hd] at hrot
    have h1r : (1 : ℂ) - r ≠ 0 := by exact_mod_cast (by linarith : (1 : ℝ) - r ≠ 0)
    rw [hk]
    push_cast
    field_simp
    linear_combination hrot
  have hC1 := k92_mobius_pointsAtInfinity R hC
  have hB2 : hypAngle UpperHalfPlane.I (toExtH (R • A))
      (LiZhongQC.mobiusExt ((R 0 0 : ℝ) : ℂ) ((R 0 1 : ℝ) : ℂ) ((R 1 0 : ℝ) : ℂ) ((R 1 1 : ℝ) : ℂ) C) = π / 2 := by
    rw [← hRI, k92_hypAngle_smul_ext R _ A hC, hB]
  have hcos := k92_parallel_axis hk1 (R • A) hA2 hC1 hB2
  rw [show (toExtH UpperHalfPlane.I) = toExtH (R • UpperHalfPlane.I) by rw [hRI],
    k92_hypAngle_smul_ext R A UpperHalfPlane.I hC] at hcos
  rw [hcos]
  have hdist : dist A UpperHalfPlane.I = Real.log k := by
    rw [← dist_smul R A UpperHalfPlane.I, hRI, UpperHalfPlane.dist_of_re_eq]
    · have him : (R • A).im = k := by
        rw [← UpperHalfPlane.coe_im, hA2]; simp
      rw [him, UpperHalfPlane.I_im, Real.log_one, Real.dist_eq, sub_zero,
        abs_of_pos (Real.log_pos hk1)]
    · rw [← UpperHalfPlane.coe_re, hA2, ← UpperHalfPlane.coe_re, UpperHalfPlane.coe_I]
      simp
  rw [hdist, Real.tanh_eq_sinh_div_cosh, Real.sinh_log (by linarith), Real.cosh_log (by linarith)]
  have hk0 : k ≠ 0 := by linarith
  field_simp

/-- The angle of parallelism `Π(a)`: `cos Π(a) = tanh a` (Theorem 1.5.1, all three forms follow). -/
theorem k92_parallel_cos {A B : ℍ} {C : ExtPlane} (hAB : A ≠ B) (hC : C ∈ pointsAtInfinity)
    (hB : hypAngle B (toExtH A) C = π / 2) :
    Real.cos (hypAngle A (toExtH B) C) = Real.tanh (dist A B) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, ℝ) B UpperHalfPlane.I
  have hC1 := k92_mobius_pointsAtInfinity g hC
  have hB1 := k92_hypAngle_smul_ext g B A hC
  rw [hB, hg] at hB1
  have hA1 := k92_hypAngle_smul_ext g A B hC
  rw [hg] at hA1
  have hgA : g • A ≠ UpperHalfPlane.I := fun h => hAB (smul_left_cancel g (h.trans hg.symm))
  have key := k92_parallel_cos_I hgA hC1 hB1
  rw [hA1, ← hg, dist_smul] at key
  exact key

/-- Auxiliary. The angle of parallelism: `sin Π(a) = 1/cosh a` (Theorem 1.5.1 (ii)). -/
theorem k92_parallel_sin {A B : ℍ} {C : ExtPlane} (hAB : A ≠ B) (hC : C ∈ pointsAtInfinity)
    (hB : hypAngle B (toExtH A) C = π / 2) :
    Real.sin (hypAngle A (toExtH B) C) = 1 / Real.cosh (dist A B) := by
  rw [Real.sin_eq_sqrt_one_sub_cos_sq (k92_hypAngle_mem A _ _).1 (k92_hypAngle_mem A _ _).2,
    k92_parallel_cos hAB hC hB, Real.tanh_eq_sinh_div_cosh]
  have hc := Real.cosh_pos (dist A B)
  have hsq := Real.cosh_sq (dist A B)
  rw [show 1 - (Real.sinh (dist A B) / Real.cosh (dist A B)) ^ 2 = (1 / Real.cosh (dist A B)) ^ 2 by
    field_simp; linarith, Real.sqrt_sq (by positivity)]

/-- **Theorem 1.5.1 (i)** (§1.5; l. 417–421). Let `Δ` be a triangle with angles `0` and `π/2` and the finite side
`a`. Then for the third angle `Π(a)`, `tan Π(a) = 1/sinh a`.
Modelling: finite vertices `A ≠ B`, ideal vertex `C ∈ ℝ ∪ {∞}`, right angle at `B`, `Π(a)` the angle at `A`,
`a = ρ(A, B)`. -/
theorem thm1_5_1_i {A B : ℍ} {C : ExtPlane} (hAB : A ≠ B) (hC : C ∈ pointsAtInfinity)
    (hB : hypAngle B (toExtH A) C = π / 2) :
    Real.tan (hypAngle A (toExtH B) C) = 1 / Real.sinh (dist A B) := by
  rw [Real.tan_eq_sin_div_cos, k92_parallel_sin hAB hC hB, k92_parallel_cos hAB hC hB,
    Real.tanh_eq_sinh_div_cosh]
  have hc := (Real.cosh_pos (dist A B)).ne'
  have hs := (k92_sinh_dist_pos hAB).ne'
  field_simp

/-- **Theorem 1.5.1 (ii)** (§1.5; l. 423–425). In the setting of Theorem 1.5.1, `sin Π(a) = 1/cosh a`. -/
theorem thm1_5_1_ii {A B : ℍ} {C : ExtPlane} (hAB : A ≠ B) (hC : C ∈ pointsAtInfinity)
    (hB : hypAngle B (toExtH A) C = π / 2) :
    Real.sin (hypAngle A (toExtH B) C) = 1 / Real.cosh (dist A B) := by
  exact k92_parallel_sin hAB hC hB

/-- **Theorem 1.5.1 (iii)** (§1.5; l. 427–429). In the setting of Theorem 1.5.1, `sec Π(a) = 1/tanh a`. -/
theorem thm1_5_1_iii {A B : ℍ} {C : ExtPlane} (hAB : A ≠ B) (hC : C ∈ pointsAtInfinity)
    (hB : hypAngle B (toExtH A) C = π / 2) :
    1 / Real.cos (hypAngle A (toExtH B) C) = 1 / Real.tanh (dist A B) := by
  rw [k92_parallel_cos hAB hC hB]

/-- **Theorem 1.5.2 (i)** (the Sine Rule; §1.5; l. 448; cited at l. 1853).
`sinh a / sin α = sinh b / sin β = sinh c / sin γ`. -/
theorem thm1_5_2_i {A B C : ℍ} (h : IsNondegenerateTriangle A B C) :
    Real.sinh (dist B C) / Real.sin (hypAngle A (toExtH B) (toExtH C)) =
        Real.sinh (dist C A) / Real.sin (hypAngle B (toExtH C) (toExtH A)) ∧
      Real.sinh (dist C A) / Real.sin (hypAngle B (toExtH C) (toExtH A)) =
        Real.sinh (dist A B) / Real.sin (hypAngle C (toExtH A) (toExtH B)) := by
  obtain ⟨hAB, hBC, hCA⟩ := k92_nondeg_ne h
  have sγ := k92_sin_mul_sinh (dist B C) (dist C A) (dist A B) _ dist_nonneg dist_nonneg
    (k92_hypAngle_mem C _ _).1 (k92_hypAngle_mem C _ _).2 (k92_cosine_rule A B C)
  have sα := k92_sin_mul_sinh (dist C A) (dist A B) (dist B C) _ dist_nonneg dist_nonneg
    (k92_hypAngle_mem A _ _).1 (k92_hypAngle_mem A _ _).2 (k92_cosine_rule B C A)
  have sβ := k92_sin_mul_sinh (dist A B) (dist B C) (dist C A) _ dist_nonneg dist_nonneg
    (k92_hypAngle_mem B _ _).1 (k92_hypAngle_mem B _ _).2 (k92_cosine_rule C A B)
  have e1 : 1 - Real.cosh (dist C A) ^ 2 - Real.cosh (dist A B) ^ 2 - Real.cosh (dist B C) ^ 2 +
      2 * Real.cosh (dist C A) * Real.cosh (dist A B) * Real.cosh (dist B C) =
      1 - Real.cosh (dist B C) ^ 2 - Real.cosh (dist C A) ^ 2 - Real.cosh (dist A B) ^ 2 +
      2 * Real.cosh (dist B C) * Real.cosh (dist C A) * Real.cosh (dist A B) := by ring
  have e2 : 1 - Real.cosh (dist A B) ^ 2 - Real.cosh (dist B C) ^ 2 - Real.cosh (dist C A) ^ 2 +
      2 * Real.cosh (dist A B) * Real.cosh (dist B C) * Real.cosh (dist C A) =
      1 - Real.cosh (dist B C) ^ 2 - Real.cosh (dist C A) ^ 2 - Real.cosh (dist A B) ^ 2 +
      2 * Real.cosh (dist B C) * Real.cosh (dist C A) * Real.cosh (dist A B) := by ring
  rw [e1] at sα
  rw [e2] at sβ
  exact k92_sine_rule_alg (k92_sinh_dist_pos hBC) (k92_sinh_dist_pos hCA)
    (k92_sinh_dist_pos hAB) sα sβ sγ

/-- **Theorem 1.5.2 (ii)** (the Cosine Rule I; §1.5; l. 450). `cosh c = cosh a cosh b − sinh a sinh b cos γ`. -/
theorem thm1_5_2_ii {A B C : ℍ} (h : IsNondegenerateTriangle A B C) :
    Real.cosh (dist A B) = Real.cosh (dist B C) * Real.cosh (dist C A) -
      Real.sinh (dist B C) * Real.sinh (dist C A) * Real.cos (hypAngle C (toExtH A) (toExtH B)) := by
  -- The nondegeneracy hypothesis `h` is not needed: the Cosine Rule holds for every triple of points.
  have _ := h
  exact k92_cosine_rule A B C

/-- **Theorem 1.5.2 (iii)** (the Cosine Rule II; §1.5; l. 452).
`cosh c = (cos α cos β + cos γ)/(sin α sin β)`. -/
theorem thm1_5_2_iii {A B C : ℍ} (h : IsNondegenerateTriangle A B C) :
    Real.cosh (dist A B) =
      (Real.cos (hypAngle A (toExtH B) (toExtH C)) * Real.cos (hypAngle B (toExtH C) (toExtH A)) +
          Real.cos (hypAngle C (toExtH A) (toExtH B))) /
        (Real.sin (hypAngle A (toExtH B) (toExtH C)) * Real.sin (hypAngle B (toExtH C) (toExtH A))) := by
  obtain ⟨hAB, hBC, hCA⟩ := k92_nondeg_ne h
  have cγ := k92_cosine_rule A B C
  have cα := k92_cosine_rule B C A
  have cβ := k92_cosine_rule C A B
  have sγ := k92_sin_mul_sinh (dist B C) (dist C A) (dist A B) _ dist_nonneg dist_nonneg
    (k92_hypAngle_mem C _ _).1 (k92_hypAngle_mem C _ _).2 cγ
  have sα := k92_sin_mul_sinh (dist C A) (dist A B) (dist B C) _ dist_nonneg dist_nonneg
    (k92_hypAngle_mem A _ _).1 (k92_hypAngle_mem A _ _).2 cα
  have sβ := k92_sin_mul_sinh (dist A B) (dist B C) (dist C A) _ dist_nonneg dist_nonneg
    (k92_hypAngle_mem B _ _).1 (k92_hypAngle_mem B _ _).2 cβ
  have hsc := Real.cosh_sq (dist A B)
  set ca := Real.cosh (dist B C)
  set cb := Real.cosh (dist C A)
  set cc := Real.cosh (dist A B)
  set sa := Real.sinh (dist B C)
  set sb := Real.sinh (dist C A)
  set sc := Real.sinh (dist A B)
  set α := hypAngle A (toExtH B) (toExtH C)
  set β := hypAngle B (toExtH C) (toExtH A)
  set γ := hypAngle C (toExtH A) (toExtH B)
  have e1 : 1 - cb ^ 2 - cc ^ 2 - ca ^ 2 + 2 * cb * cc * ca = 1 - ca ^ 2 - cb ^ 2 - cc ^ 2 + 2 * ca * cb * cc := by
    ring
  have e2 : 1 - cc ^ 2 - ca ^ 2 - cb ^ 2 + 2 * cc * ca * cb = 1 - ca ^ 2 - cb ^ 2 - cc ^ 2 + 2 * ca * cb * cc := by
    ring
  rw [e1] at sα
  rw [e2] at sβ
  set Δ := 1 - ca ^ 2 - cb ^ 2 - cc ^ 2 + 2 * ca * cb * cc
  have hsa : 0 < sa := k92_sinh_dist_pos hBC
  have hsb : 0 < sb := k92_sinh_dist_pos hCA
  have hsc0 : 0 < sc := k92_sinh_dist_pos hAB
  have hγne : Real.sin γ ≠ 0 := fun h0 => h (k92_collinear hCA.symm hBC h0)
  have hγpos : 0 < Real.sin γ :=
    lt_of_le_of_ne (Real.sin_nonneg_of_nonneg_of_le_pi (k92_hypAngle_mem C _ _).1
      (k92_hypAngle_mem C _ _).2) (Ne.symm hγne)
  have hD : 0 < √Δ := by rw [← sγ]; positivity
  have hΔ : √Δ ^ 2 = Δ := Real.sq_sqrt (Real.sqrt_pos.1 hD).le
  have ecα : Real.cos α = (cb * cc - ca) / (sb * sc) := by
    rw [eq_div_iff (by positivity)]; linarith
  have ecβ : Real.cos β = (cc * ca - cb) / (sc * sa) := by
    rw [eq_div_iff (by positivity)]; linarith
  have ecγ : Real.cos γ = (ca * cb - cc) / (sa * sb) := by
    rw [eq_div_iff (by positivity)]; linarith
  have esα : Real.sin α = √Δ / (sb * sc) := by
    rw [eq_div_iff (by positivity)]; exact sα
  have esβ : Real.sin β = √Δ / (sc * sa) := by
    rw [eq_div_iff (by positivity)]; exact sβ
  rw [ecα, ecβ, ecγ, esα, esβ]
  have hΔpos : 0 < Δ := Real.sqrt_pos.1 hD
  have key : (cb * cc - ca) * (cc * ca - cb) + (ca * cb - cc) * sc ^ 2 = cc * Δ := by
    rw [show sc ^ 2 = cc ^ 2 - 1 by linarith]
    simp only [Δ]
    ring
  set D := √Δ
  have hR : ((cb * cc - ca) / (sb * sc) * ((cc * ca - cb) / (sc * sa)) + (ca * cb - cc) / (sa * sb)) /
      (D / (sb * sc) * (D / (sc * sa))) = ((cb * cc - ca) * (cc * ca - cb) + (ca * cb - cc) * sc ^ 2) / D ^ 2 := by
    field_simp
  rw [hR, hΔ, key]
  field_simp

/-- **Theorem 1.5.3** (Pythagorean Theorem; §1.5; l. 525). If `γ = π/2`, then `cosh c = cosh a cosh b`. -/
theorem thm1_5_3 {A B C : ℍ} (h : IsNondegenerateTriangle A B C)
    (hγ : hypAngle C (toExtH A) (toExtH B) = π / 2) :
    Real.cosh (dist A B) = Real.cosh (dist B C) * Real.cosh (dist C A) := by
  -- The nondegeneracy hypothesis `h` is not needed: this is the Cosine Rule with `cos γ = 0`.
  have _ := h
  rw [k92_cosine_rule A B C, hγ, Real.cos_pi_div_two, mul_zero, sub_zero]

end Katok1992
