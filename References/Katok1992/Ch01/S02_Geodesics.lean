import References.Katok1992.Ch01.S01_HyperbolicMetric

/-!
# Katok 1992, Ch. 1 §1.2 Geodesics

S. Katok, *Fuchsian Groups* (1992), Chapter 1 *Hyperbolic Geometry*, §1.2; source `full.md` of
`Fuchsian groups (Katok, Svetlana) …-3766f6b7…`, lines 176–277.

* Helper (the arc of the line or semicircle orthogonal to ℝ between two points of ℍ ∪ ℝ ∪ {∞}) — `geodArcFinite`,
  `geodCentre`, `geodArc`
* Theorem 1.2.1 (the geodesics are the semicircles and straight lines orthogonal to ℝ; cited in hint l. 3215) —
  `thm1_2_1_i`, `thm1_2_1_ii`
* Formula (1.2.1) (ρ(ia, ib) = ln(b/a); cited at l. 216, 274) — exists: `UpperHalfPlane.dist_of_re_eq` (for equal
  real parts the distance is |log Im z − log Im w|)
* Definition (the geodesic segment [z, w], l. 190; cited at l. 1303–1329, 1752) — `geodSegment`
* Corollary 1.2.2 (l. 190) — `cor1_2_2`
* Corollary 1.2.3 (l. 192; cited at l. 202) — `cor1_2_3`
* Theorem 1.2.4 (l. 200; cited at l. 286, and at l. 671 as "Theorem 1.2.5") — `thm1_2_4`
* Definition (the Riemann sphere, l. 204) — exists: `LiZhongQC.ExtPlane`
* Definition (the cross-ratio, l. 204–208) — `crossRatio`
* Theorem 1.2.5 (l. 210; cited at l. 286) — `thm1_2_5`
* Theorem 1.2.6 (i) (l. 222) — `thm1_2_6_i`
* Theorem 1.2.6 (ii) (l. 226; cited at l. 433, 1321) — exists: `UpperHalfPlane.cosh_dist`
* Theorem 1.2.6 (iii) (l. 230; cited at l. 294, 1935, 1993, 2207, the last two as "Theorem 1.2.8(iii)") — exists:
  `UpperHalfPlane.sinh_half_dist`
* Theorem 1.2.6 (iv) (l. 234) — exists: `UpperHalfPlane.cosh_half_dist`
* Theorem 1.2.6 (v) (l. 238; cited in hint l. 3219) — exists: `UpperHalfPlane.tanh_half_dist` (the quotient of the
  two distances is the modulus of the quotient)
* Definition (the unit disc 𝔘, l. 249) — exists: `LiZhongQC.unitDisc`
* Formula (1.2.2) (the map f(z) = (zi + 1)/(z + i), l. 255; cited at l. 1590, 2137) — `cayleyK`, `cayleyKInv`
* Unlabelled (§1.2, l. 258: f is a 1-1 map of ℍ onto 𝔘; cited at l. 1590, 2137) — `cayleyK_bijOn`
* Definition (ρ* on 𝔘, l. 260) — `rhoDisc`
* Formula (1.2.3) (ds = 2|dz|/(1 − |z|²), l. 267) — exists: `LiZhongQC.poincareDensityDisc`
* Unlabelled (§1.2, l. 264: ρ* is the metric derived from (1.2.3); used at l. 461–479, 1540, 2063) —
  `rhoDisc_eq_metricDist`
* Definition (the principal circle Σ, l. 272) — exists: `Metric.sphere`
* Definition (points at infinity, l. 272–274) — `pointsAtInfinity`
* Definition (the Euclidean closure ℍ̃ = ℍ ∪ ℝ ∪ {∞}, l. 276) — `closureH`
* Definition (the Euclidean closure 𝔘̃ = 𝔘 ∪ Σ, l. 276) — exists: `Metric.closedBall`

Not items (DESIGN §3): the path inequality in (1.2.1) (a proof step; its value is the item); the mapping of lines and
circles by Möbius maps and the invariance of the cross-ratio (quoted inside proofs); "ρ* is a metric on 𝔘" and "f is
an isometry of (ℍ, ρ) onto (𝔘, ρ)" (l. 258, 270; immediate from the definition of ρ*); geodesics of 𝔘 (Exercise
1.7); the characterization of the points at infinity by infinite distance (l. 274; heuristic, not cited); "ℍ̃, 𝔘̃
are the closures in ℂ̂" (l. 276; immediate); the exercises.

**Conventions.** Ideal points and polygon vertices live in `LiZhongQC.ExtPlane` = ℂ̂; ℝ ∪ {∞} is `pointsAtInfinity`.
The lines and semicircles orthogonal to ℝ are given explicitly by `geodArc`, so Theorem 1.2.1 is not definitional
(geodesics are metric, `IsGeodesic`). Katok's Cayley map `f(z) = (iz + 1)/(z + i)` is `i · LiZhongQC.cayley z`
(`i(z − i) = iz + 1`), a different function from the project's `cayley`, hence new. The disc metric is the project's
`LiZhongQC.poincareDensityDisc` (curvature `−1`, Katok's (1.2.3)), not Pommerenke's `hypDistD` (curvature `−4`).
[cit?] l. 671 cites "Theorem 1.2.5" for a content of Theorem 1.2.4.
-/

open Complex Set Metric Filter Topology
open scoped UpperHalfPlane MatrixGroups ComplexConjugate

noncomputable section

namespace Katok1992

open LiZhongQC (ExtPlane)

/-- Helper (§1.2). The real centre of the circle orthogonal to ℝ through `a` and `b` (`Re a ≠ Re b`):
`c = (|b|² − |a|²)/(2(Re b − Re a))`. -/
def geodCentre (a b : ℂ) : ℝ := (‖b‖ ^ 2 - ‖a‖ ^ 2) / (2 * (b.re - a.re))

/-- Helper (§1.2). For `a, b` in `ℍ ∪ ℝ` (`Im ≥ 0`), the points of ℍ on the closed arc between `a` and `b` of the
vertical line or of the circle centred on ℝ through `a` and `b`.
Modelling: vertical case `Re a = Re b`; otherwise the circle with centre `geodCentre a b`, between the real parts.
Junk for `Im a < 0` or `Im b < 0` (outside the book's discourse). -/
def geodArcFinite (a b : ℂ) : Set ℍ :=
  if a.re = b.re then {ξ | ξ.re = a.re ∧ min a.im b.im ≤ ξ.im ∧ ξ.im ≤ max a.im b.im}
  else {ξ | dist (ξ : ℂ) (geodCentre a b : ℂ) = dist a (geodCentre a b : ℂ) ∧
    min a.re b.re ≤ ξ.re ∧ ξ.re ≤ max a.re b.re}

/-- Helper (§1.2). The closed geodesic arc in ℍ between `p, q ∈ ℍ̃ ⊆ ℂ̂`: a segment, a ray, or a whole line or
semicircle orthogonal to ℝ when both `p, q ∈ ℝ ∪ {∞}`.
Modelling: `∞` with a finite `b` gives the vertical ray `{Re ξ = Re b, Im ξ ≥ Im b}`; `∞, ∞` gives `∅` (junk). -/
def geodArc (p q : ExtPlane) : Set ℍ :=
  p.elim (q.elim ∅ fun b => {ξ | ξ.re = b.re ∧ b.im ≤ ξ.im})
    (fun a => q.elim {ξ | ξ.re = a.re ∧ a.im ≤ ξ.im} fun b => geodArcFinite a b)

/-- **Definition** (points at infinity; §1.2, l. 272–274; cited at l. 947, 1802, 1943, 2235). The Euclidean boundary
`ℝ ∪ {∞}` of ℍ in the Riemann sphere `ℂ̂`. -/
def pointsAtInfinity : Set ExtPlane :=
  insert OnePoint.infty (range fun x : ℝ => (((x : ℂ)) : ExtPlane))

/-- **Definition** (§1.2, l. 276; cited at l. 919, 947). The Euclidean closure `ℍ̃ = ℍ ∪ ℝ ∪ {∞}` of ℍ in `ℂ̂`. -/
def closureH : Set ExtPlane := LiZhongQC.toExt LiZhongQC.upperHalf ∪ pointsAtInfinity

/-- Auxiliary (§1.2). On ℝ, `|a − x| + |x − b| = |a − b|` exactly for `x` between `a` and `b`. -/
theorem k92g_abs_add_abs_iff (a b x : ℝ) : |a - x| + |x - b| = |a - b| ↔ x ∈ uIcc a b := by
  have e : a - b = (a - x) + (x - b) := by ring
  rw [e, eq_comm, abs_add_eq_add_abs_iff, Set.mem_uIcc]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inr ⟨by linarith, by linarith⟩
    · exact Or.inl ⟨by linarith, by linarith⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inr ⟨by linarith, by linarith⟩
    · exact Or.inl ⟨by linarith, by linarith⟩

/-- Auxiliary (§1.2). For positive reals, `ln x` lies between `ln a` and `ln b` exactly when `x` lies between `a`
and `b`. -/
theorem k92g_log_mem_uIcc {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    Real.log x ∈ uIcc (Real.log a) (Real.log b) ↔ x ∈ uIcc a b := by
  simp only [Set.mem_uIcc, Real.log_le_log_iff ha hx, Real.log_le_log_iff hx hb, Real.log_le_log_iff hb hx,
    Real.log_le_log_iff hx ha]

/-- Auxiliary (§1.2). The equality case of `|ln Im z − ln Im ξ| ≤ ρ(z, ξ)`: equality forces `Re z = Re ξ`. -/
theorem k92g_re_eq_of_dist_eq {z ξ : ℍ} (h : dist z ξ = |Real.log z.im - Real.log ξ.im|) : z.re = ξ.re := by
  have ha := z.im_pos
  have hb := ξ.im_pos
  have hc := UpperHalfPlane.cosh_dist z ξ
  have hD : dist (z : ℂ) ξ ^ 2 = (z.re - ξ.re) ^ 2 + (z.im - ξ.im) ^ 2 := by
    rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have hch : Real.cosh |Real.log z.im - Real.log ξ.im| = (z.im / ξ.im + ξ.im / z.im) / 2 := by
    rw [Real.cosh_abs, Real.cosh_eq, neg_sub, Real.exp_sub, Real.exp_sub, Real.exp_log ha, Real.exp_log hb]
  rw [h, hch, hD] at hc
  have key : (z.im / ξ.im + ξ.im / z.im) / 2 -
      (1 + ((z.re - ξ.re) ^ 2 + (z.im - ξ.im) ^ 2) / (2 * z.im * ξ.im)) =
      -((z.re - ξ.re) ^ 2 / (2 * z.im * ξ.im)) := by
    field_simp
    ring
  rw [hc, sub_self, eq_comm, neg_eq_zero, div_eq_zero_iff] at key
  rcases key with h0 | h0
  · exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0)
  · exact absurd h0 (by positivity)

/-- Auxiliary (§1.2). On a vertical line `ρ(z, w) = |ln Im z − ln Im w|`, and `ρ(z, w) = ρ(z, ξ) + ρ(ξ, w)` holds
exactly for the points `ξ` of the vertical segment between `z` and `w`. -/
theorem k92g_vertical_iff {z w : ℍ} (h : z.re = w.re) (ξ : ℍ) :
    dist z w = dist z ξ + dist ξ w ↔ ξ.re = z.re ∧ ξ.im ∈ uIcc z.im w.im := by
  have hzw : dist z w = |Real.log z.im - Real.log w.im| := by
    rw [UpperHalfPlane.dist_of_re_eq h, Real.dist_eq]
  have h1 : |Real.log z.im - Real.log ξ.im| ≤ dist z ξ := by
    have := UpperHalfPlane.dist_log_im_le z ξ
    rwa [Real.dist_eq] at this
  have h2 : |Real.log ξ.im - Real.log w.im| ≤ dist ξ w := by
    have := UpperHalfPlane.dist_log_im_le ξ w
    rwa [Real.dist_eq] at this
  have h3 := abs_sub_le (Real.log z.im) (Real.log ξ.im) (Real.log w.im)
  rw [← k92g_log_mem_uIcc z.im_pos w.im_pos ξ.im_pos, ← k92g_abs_add_abs_iff]
  constructor
  · intro hd
    have e1 : dist z ξ = |Real.log z.im - Real.log ξ.im| := by linarith
    exact ⟨(k92g_re_eq_of_dist_eq e1).symm, by linarith⟩
  · rintro ⟨hre, habs⟩
    rw [hzw, UpperHalfPlane.dist_of_re_eq hre.symm, UpperHalfPlane.dist_of_re_eq (hre.trans h), Real.dist_eq,
      Real.dist_eq, habs]

/-- Auxiliary (§1.2). Two-distance rigidity on the imaginary axis: if `A ≠ B` and `X'` lie on the imaginary axis and
`X` has the same distances as `X'` to `A` and to `B`, then `X = X'`. -/
theorem k92g_rigid {A B X X' : ℍ} (hA : A.re = 0) (hB : B.re = 0) (hX' : X'.re = 0) (hAB : A ≠ B)
    (h1 : dist A X = dist A X') (h2 : dist B X = dist B X') : X = X' := by
  have key : ∀ P : ℍ, P.re = 0 → dist P X = dist P X' →
      (X.re ^ 2 + X.im ^ 2 + P.im ^ 2) * X'.im = (X'.im ^ 2 + P.im ^ 2) * X.im := by
    intro P hP h
    have hc := congrArg Real.cosh h
    rw [UpperHalfPlane.cosh_dist, UpperHalfPlane.cosh_dist] at hc
    have e : ∀ Q : ℍ, dist (P : ℂ) Q ^ 2 = Q.re ^ 2 + (P.im - Q.im) ^ 2 := fun Q => by
      rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply]
      simp only [sub_re, sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hP]
      ring
    rw [e, e, hX'] at hc
    have hc2 : (X.re ^ 2 + (P.im - X.im) ^ 2) / (2 * P.im * X.im) =
        (P.im - X'.im) ^ 2 / (2 * P.im * X'.im) := by
      have := add_left_cancel hc
      rwa [zero_pow two_ne_zero, zero_add] at this
    rw [div_eq_div_iff (by positivity) (by positivity)] at hc2
    have h2p : 2 * P.im ≠ 0 := by positivity
    apply mul_left_cancel₀ h2p
    linear_combination hc2
  have EA := key A hA h1
  have EB := key B hB h2
  have hab : A.im ≠ B.im := fun he =>
    hAB (UpperHalfPlane.ext (Complex.ext (by simp [hA, hB]) (by simpa using he)))
  have hab2 : A.im ^ 2 - B.im ^ 2 ≠ 0 := by
    have e : A.im ^ 2 - B.im ^ 2 = (A.im - B.im) * (A.im + B.im) := by ring
    rw [e]
    exact mul_ne_zero (sub_ne_zero.2 hab) (by positivity)
  have him : X.im = X'.im := by
    have e : (A.im ^ 2 - B.im ^ 2) * (X'.im - X.im) = 0 := by linear_combination EA - EB
    rcases mul_eq_zero.1 e with e | e
    · exact absurd e hab2
    · linarith
  have hre : X.re = 0 := by
    rw [← him] at EA
    have h0 : X.re ^ 2 * X.im = 0 := by linear_combination EA
    rcases mul_eq_zero.1 h0 with e | e
    · exact (pow_eq_zero_iff two_ne_zero).1 e
    · exact absurd e X.im_pos.ne'
  apply UpperHalfPlane.ext
  apply Complex.ext
  · rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_re, hre, hX']
  · rw [UpperHalfPlane.coe_im, UpperHalfPlane.coe_im, him]

/-- Auxiliary (§1.2). `x` lies between `a` and `b` in the `min`/`max` form of `geodArcFinite` exactly when
`x ∈ [[a, b]]`. -/
theorem k92g_mem_uIcc_iff {a b x : ℝ} : (min a b ≤ x ∧ x ≤ max a b) ↔ x ∈ uIcc a b := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab, Set.uIcc_of_le hab, Set.mem_Icc]
  · rw [min_eq_right hab, max_eq_left hab, Set.uIcc_of_ge hab, Set.mem_Icc]

/-- Auxiliary (§1.2). A real Möbius map `ξ ↦ (aξ + b)/(cξ + d)` with `ad − bc > 0` is the action of an element of
`SL(2,ℝ)` on ℍ. -/
theorem k92g_sl_of_det_pos {a b c d : ℝ} (h : 0 < a * d - b * c) :
    ∃ g : SL(2, ℝ), ∀ ξ : ℍ, ((g • ξ : ℍ) : ℂ) = ((a : ℂ) * ξ + b) / ((c : ℂ) * ξ + d) := by
  set s : ℝ := (√(a * d - b * c))⁻¹ with hs
  have hs0 : 0 < s := inv_pos.2 (Real.sqrt_pos.2 h)
  have hdet : (!![s * a, s * b; s * c, s * d] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    have h2 : s ^ 2 * (a * d - b * c) = 1 := by
      rw [hs, inv_pow, Real.sq_sqrt h.le, inv_mul_cancel₀ h.ne']
    linear_combination h2
  set g : SL(2, ℝ) := ⟨!![s * a, s * b; s * c, s * d], hdet⟩ with hgdef
  refine ⟨g, fun ξ => ?_⟩
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  have h00 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = s * a := rfl
  have h01 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = s * b := rfl
  have h10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = s * c := rfl
  have h11 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = s * d := rfl
  simp only [Algebra.algebraMap_self, RingHom.id_apply, h00, h01, h10, h11]
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  push_cast
  rw [show (s : ℂ) * a * ξ + s * b = s * (a * ξ + b) by ring,
    show (s : ℂ) * c * ξ + s * d = s * (c * ξ + d) by ring, mul_div_mul_left _ _ hs']

/-- Auxiliary (§1.2). The translation `ξ ↦ ξ − x` as an element of `SL(2,ℝ)`. -/
theorem k92g_line_chart (x : ℝ) : ∃ g : SL(2, ℝ), ∀ ξ : ℍ, (g • ξ).re = ξ.re - x ∧ (g • ξ).im = ξ.im := by
  obtain ⟨g, hg⟩ := k92g_sl_of_det_pos (a := 1) (b := -x) (c := 0) (d := 1) (by norm_num)
  refine ⟨g, fun ξ => ?_⟩
  have e : ((g • ξ : ℍ) : ℂ) = (ξ : ℂ) - x := by
    rw [hg]
    push_cast
    ring
  constructor
  · rw [← UpperHalfPlane.coe_re, e]
    simp
  · rw [← UpperHalfPlane.coe_im, e]
    simp

/-- Auxiliary (§1.2). For `a < b`, the element `ξ ↦ (ξ − a)/(b − ξ)` of `SL(2,ℝ)` carries the semicircle over
`[a, b]`, `(Re ξ − a)(b − Re ξ) = (Im ξ)²`, onto the imaginary axis, and along that semicircle `Im (g • ξ)`
increases with `Re ξ` (`Im (g • ξ)² = (Re ξ − a)/(b − Re ξ)`). -/
theorem k92g_semicircle_chart {a b : ℝ} (hab : a < b) : ∃ g : SL(2, ℝ),
    (∀ ξ : ℍ, (g • ξ).re = 0 ↔ (ξ.re - a) * (b - ξ.re) = ξ.im ^ 2) ∧
      ∀ ξ ξ' : ℍ, (ξ.re - a) * (b - ξ.re) = ξ.im ^ 2 → (ξ'.re - a) * (b - ξ'.re) = ξ'.im ^ 2 →
        (ξ.re ≤ ξ'.re ↔ (g • ξ).im ≤ (g • ξ').im) := by
  obtain ⟨g, hg⟩ := k92g_sl_of_det_pos (a := 1) (b := -a) (c := -1) (d := b) (by linarith)
  have e : ∀ ξ : ℍ, ((g • ξ : ℍ) : ℂ) = ((ξ : ℂ) - a) / (b - ξ) := fun ξ => by
    rw [hg]
    push_cast
    ring
  have hN : ∀ ξ : ℍ, Complex.normSq ((b : ℂ) - ξ) = (b - ξ.re) ^ 2 + ξ.im ^ 2 := fun ξ => by
    rw [Complex.normSq_apply]
    simp
    ring
  have hNpos : ∀ ξ : ℍ, 0 < (b - ξ.re) ^ 2 + ξ.im ^ 2 := fun ξ => by positivity
  have hre : ∀ ξ : ℍ, (g • ξ).re = ((ξ.re - a) * (b - ξ.re) - ξ.im ^ 2) / ((b - ξ.re) ^ 2 + ξ.im ^ 2) :=
    fun ξ => by
      rw [← UpperHalfPlane.coe_re, e, Complex.div_re, hN]
      simp
      ring
  have him : ∀ ξ : ℍ, (g • ξ).im = (b - a) * ξ.im / ((b - ξ.re) ^ 2 + ξ.im ^ 2) := fun ξ => by
    rw [← UpperHalfPlane.coe_im, e, Complex.div_im, hN]
    simp
    ring
  -- on the semicircle, `Im (g • ξ)² (b − Re ξ) = Re ξ − a` with `b − Re ξ > 0`
  have hcirc : ∀ ξ : ℍ, (ξ.re - a) * (b - ξ.re) = ξ.im ^ 2 →
      0 < b - ξ.re ∧ (g • ξ).im ^ 2 * (b - ξ.re) = ξ.re - a := fun ξ h => by
    have hy := ξ.im_pos
    have hbx : 0 < b - ξ.re := by nlinarith [pow_pos hy 2]
    refine ⟨hbx, ?_⟩
    have hN' : (b - ξ.re) ^ 2 + ξ.im ^ 2 = (b - ξ.re) * (b - a) := by rw [← h]; ring
    rw [him, hN', mul_comm (b - ξ.re) (b - a), mul_div_mul_left _ _ (sub_pos.2 hab).ne', div_pow, ← h,
      div_mul_eq_mul_div, div_eq_iff (by positivity)]
    ring
  refine ⟨g, fun ξ => ?_, fun ξ ξ' h h' => ?_⟩
  · rw [hre, div_eq_zero_iff, sub_eq_zero, or_iff_left (hNpos ξ).ne']
  · obtain ⟨hb, E⟩ := hcirc ξ h
    obtain ⟨hb', E'⟩ := hcirc ξ' h'
    have hu : 0 < (g • ξ).im := (g • ξ).im_pos
    have hu' : 0 < (g • ξ').im := (g • ξ').im_pos
    have key : (ξ.re - ξ'.re) * ((1 + (g • ξ).im ^ 2) * (1 + (g • ξ').im ^ 2)) =
        (b - a) * ((g • ξ).im ^ 2 - (g • ξ').im ^ 2) := by
      linear_combination (-(1 + (g • ξ').im ^ 2)) * E + (1 + (g • ξ).im ^ 2) * E'
    have hpos : 0 < (1 + (g • ξ).im ^ 2) * (1 + (g • ξ').im ^ 2) := by positivity
    constructor
    · intro hx
      by_contra hcon
      push Not at hcon
      have h1 : (g • ξ').im ^ 2 < (g • ξ).im ^ 2 := by nlinarith
      have h2 : 0 < (b - a) * ((g • ξ).im ^ 2 - (g • ξ').im ^ 2) := mul_pos (by linarith) (by linarith)
      have h3 : (ξ.re - ξ'.re) * ((1 + (g • ξ).im ^ 2) * (1 + (g • ξ').im ^ 2)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
      linarith
    · intro hle
      by_contra hcon
      push Not at hcon
      have h1 : (g • ξ).im ^ 2 ≤ (g • ξ').im ^ 2 := by nlinarith
      have h3 : 0 < (ξ.re - ξ'.re) * ((1 + (g • ξ).im ^ 2) * (1 + (g • ξ').im ^ 2)) := mul_pos (by linarith) hpos
      have h2 : (b - a) * ((g • ξ).im ^ 2 - (g • ξ').im ^ 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      linarith

/-- Auxiliary (§1.2). The vertical lines `geodArc ∞ x` and `geodArc x ∞` are `Re ξ = x`. -/
theorem k92g_geodArc_inf (x : ℝ) (ξ : ℍ) :
    (ξ ∈ geodArc OnePoint.infty (((x : ℂ)) : ExtPlane) ↔ ξ.re = x) ∧
      (ξ ∈ geodArc (((x : ℂ)) : ExtPlane) OnePoint.infty ↔ ξ.re = x) := by
  have hy := ξ.im_pos
  constructor
  · show ξ.re = ((x : ℂ)).re ∧ ((x : ℂ)).im ≤ ξ.im ↔ ξ.re = x
    simp only [ofReal_re, ofReal_im, hy.le, and_true]
  · show ξ.re = ((x : ℂ)).re ∧ ((x : ℂ)).im ≤ ξ.im ↔ ξ.re = x
    simp only [ofReal_re, ofReal_im, hy.le, and_true]

/-- Auxiliary (§1.2). For real `x ≠ y`, `geodArc x y` is the semicircle `(Re ξ − x)(y − Re ξ) = (Im ξ)²`. -/
theorem k92g_geodArc_real {x y : ℝ} (hxy : x ≠ y) (ξ : ℍ) :
    ξ ∈ geodArc (((x : ℂ)) : ExtPlane) (((y : ℂ)) : ExtPlane) ↔ (ξ.re - x) * (y - ξ.re) = ξ.im ^ 2 := by
  have hre : ((x : ℂ)).re ≠ ((y : ℂ)).re := by simpa using hxy
  have hc : geodCentre (x : ℂ) (y : ℂ) = (x + y) / 2 := by
    unfold geodCentre
    have : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, ofReal_re]
    field_simp
    ring
  have hd : dist (ξ : ℂ) (((x + y) / 2 : ℝ) : ℂ) ^ 2 = (ξ.re - (x + y) / 2) ^ 2 + ξ.im ^ 2 := by
    rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hd' : dist ((x : ℂ)) (((x + y) / 2 : ℝ) : ℂ) ^ 2 = ((x - y) / 2) ^ 2 := by
    rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hy := ξ.im_pos
  show ξ ∈ geodArcFinite (x : ℂ) (y : ℂ) ↔ _
  rw [geodArcFinite, ite_eq_right hre, hc]
  simp only [Set.mem_ofPred_eq, ofReal_re]
  constructor
  · rintro ⟨h1, -, -⟩
    have h2 := congrArg (· ^ 2) h1
    rw [hd, hd'] at h2
    linear_combination (-1 : ℝ) * h2
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, hd, hd']
      linear_combination (-1 : ℝ) * h
    · rcases le_total x y with hl | hl
      · rw [min_eq_left hl]
        nlinarith [pow_pos hy 2]
      · rw [min_eq_right hl]
        nlinarith [pow_pos hy 2]
    · rcases le_total x y with hl | hl
      · rw [max_eq_right hl]
        nlinarith [pow_pos hy 2]
      · rw [max_eq_left hl]
        nlinarith [pow_pos hy 2]

/-- Auxiliary (§1.2). The circle of centre `c ∈ ℝ` and radius `R ≥ 0` is the semicircle over `[c − R, c + R]`. -/
theorem k92g_dist_center_iff (c R : ℝ) (hR : 0 ≤ R) (ξ : ℍ) :
    dist (ξ : ℂ) (c : ℂ) = R ↔ (ξ.re - (c - R)) * ((c + R) - ξ.re) = ξ.im ^ 2 := by
  have hd : dist (ξ : ℂ) (c : ℂ) ^ 2 = (ξ.re - c) ^ 2 + ξ.im ^ 2 := by
    rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [← sq_eq_sq₀ dist_nonneg hR, hd]
  constructor <;> intro h <;> linear_combination (-1 : ℝ) * h

/-- Auxiliary (§1.2). `geodCentre a b` is equidistant from `a` and `b` (`Re a ≠ Re b`). -/
theorem k92g_geodCentre_dist {a b : ℂ} (h : a.re ≠ b.re) :
    dist b (geodCentre a b : ℂ) = dist a (geodCentre a b : ℂ) := by
  have hd : b.re - a.re ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have hc : geodCentre a b * (2 * (b.re - a.re)) = ‖b‖ ^ 2 - ‖a‖ ^ 2 := by
    unfold geodCentre
    exact div_mul_cancel₀ _ (mul_ne_zero two_ne_zero hd)
  rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, Complex.dist_eq, Complex.dist_eq, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at hc
  simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]
  linear_combination (-1 : ℝ) * hc

/-- Auxiliary (§1.2). Each line or semicircle `geodArc p q` orthogonal to ℝ (`p ≠ q ∈ ℝ ∪ {∞}`) is carried onto the
imaginary axis by an element of `SL(2,ℝ)`. -/
theorem k92g_chart {p q : ExtPlane} (hp : p ∈ pointsAtInfinity) (hq : q ∈ pointsAtInfinity) (hpq : p ≠ q) :
    ∃ g : SL(2, ℝ), ∀ ξ : ℍ, ξ ∈ geodArc p q ↔ (g • ξ).re = 0 := by
  rcases hp with rfl | ⟨x, rfl⟩ <;> rcases hq with rfl | ⟨y, rfl⟩
  · exact absurd rfl hpq
  · obtain ⟨g, hg⟩ := k92g_line_chart y
    exact ⟨g, fun ξ => (k92g_geodArc_inf y ξ).1.trans (by rw [(hg ξ).1, sub_eq_zero])⟩
  · obtain ⟨g, hg⟩ := k92g_line_chart x
    exact ⟨g, fun ξ => (k92g_geodArc_inf x ξ).2.trans (by rw [(hg ξ).1, sub_eq_zero])⟩
  · have hxy : x ≠ y := fun h => hpq (by rw [h])
    rcases lt_or_gt_of_ne hxy with h | h
    · obtain ⟨g, hg, -⟩ := k92g_semicircle_chart h
      exact ⟨g, fun ξ => (k92g_geodArc_real hxy ξ).trans (hg ξ).symm⟩
    · obtain ⟨g, hg, -⟩ := k92g_semicircle_chart h
      refine ⟨g, fun ξ => (k92g_geodArc_real hxy ξ).trans ?_⟩
      rw [hg ξ, show (ξ.re - x) * (y - ξ.re) = (ξ.re - y) * (x - ξ.re) by ring]

/-- Auxiliary (§1.2). The arc `geodArcFinite z w` lies on a line or semicircle `geodArc p q` orthogonal to ℝ, and an
element `g ∈ SL(2,ℝ)` carrying `geodArc p q` onto the imaginary axis carries the arc onto the segment of the axis
between `g • z` and `g • w`. -/
theorem k92g_segment_chart (z w : ℍ) :
    ∃ p ∈ pointsAtInfinity, ∃ q ∈ pointsAtInfinity, p ≠ q ∧ ∃ g : SL(2, ℝ),
      (∀ ξ : ℍ, ξ ∈ geodArc p q ↔ (g • ξ).re = 0) ∧ (g • z).re = 0 ∧ (g • w).re = 0 ∧
      ∀ ξ : ℍ, ξ ∈ geodArcFinite z w ↔ (g • ξ).re = 0 ∧ (g • ξ).im ∈ uIcc (g • z).im (g • w).im := by
  by_cases hzw : (z : ℂ).re = (w : ℂ).re
  · -- the vertical segment: translate `Re z` to `0`
    have hzw' : z.re = w.re := hzw
    obtain ⟨g, hg⟩ := k92g_line_chart z.re
    refine ⟨OnePoint.infty, mem_insert _ _, (((z.re : ℝ) : ℂ) : ExtPlane), mem_insert_of_mem _ ⟨z.re, rfl⟩,
      OnePoint.infty_ne_coe _, g, fun ξ => ?_, ?_, ?_, fun ξ => ?_⟩
    · rw [(k92g_geodArc_inf z.re ξ).1, (hg ξ).1, sub_eq_zero]
    · rw [(hg z).1, sub_self]
    · rw [(hg w).1, hzw', sub_self]
    · rw [geodArcFinite, ite_eq_left hzw, (hg ξ).1, (hg ξ).2, (hg z).2, (hg w).2, sub_eq_zero, ← k92g_mem_uIcc_iff]
      simp only [Set.mem_ofPred_eq, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  · -- the semicircle through `z` and `w`, centred at `c = geodCentre z w`
    obtain ⟨c, hc⟩ : ∃ c : ℝ, geodCentre (z : ℂ) (w : ℂ) = c := ⟨_, rfl⟩
    obtain ⟨R, hR⟩ : ∃ R : ℝ, dist (z : ℂ) (c : ℂ) = R := ⟨_, rfl⟩
    have hR0 : 0 < R := by
      have h1 : |((z : ℂ) - (c : ℂ)).im| ≤ ‖(z : ℂ) - (c : ℂ)‖ := Complex.abs_im_le_norm _
      simp only [sub_im, ofReal_im, sub_zero, UpperHalfPlane.coe_im] at h1
      rw [← hR, Complex.dist_eq]
      linarith [abs_of_pos z.im_pos, z.im_pos]
    obtain ⟨g, hre0, hmono⟩ := k92g_semicircle_chart (show c - R < c + R by linarith)
    have hon := k92g_dist_center_iff c R hR0.le
    have hzc : (z.re - (c - R)) * ((c + R) - z.re) = z.im ^ 2 := (hon z).1 hR
    have hwc : (w.re - (c - R)) * ((c + R) - w.re) = w.im ^ 2 := by
      refine (hon w).1 ?_
      rw [← hR, ← hc]
      exact k92g_geodCentre_dist hzw
    refine ⟨(((c - R : ℝ) : ℂ) : ExtPlane), mem_insert_of_mem _ ⟨c - R, rfl⟩, (((c + R : ℝ) : ℂ) : ExtPlane),
      mem_insert_of_mem _ ⟨c + R, rfl⟩, ?_, g, fun ξ => ?_, (hre0 z).2 hzc, (hre0 w).2 hwc, fun ξ => ?_⟩
    · intro h
      have := Complex.ofReal_injective (OnePoint.coe_injective h)
      linarith
    · rw [k92g_geodArc_real (by linarith), hre0]
    · rw [geodArcFinite, ite_eq_right hzw, hc, hR, ← k92g_mem_uIcc_iff]
      simp only [Set.mem_ofPred_eq, UpperHalfPlane.coe_re]
      rw [hon ξ, hre0 ξ]
      constructor
      · rintro ⟨hξ, h1, h2⟩
        refine ⟨hξ, ?_, ?_⟩
        · rcases min_le_iff.1 h1 with h1 | h1
          · exact min_le_iff.2 (Or.inl ((hmono z ξ hzc hξ).1 h1))
          · exact min_le_iff.2 (Or.inr ((hmono w ξ hwc hξ).1 h1))
        · rcases le_max_iff.1 h2 with h2 | h2
          · exact le_max_iff.2 (Or.inl ((hmono ξ z hξ hzc).1 h2))
          · exact le_max_iff.2 (Or.inr ((hmono ξ w hξ hwc).1 h2))
      · rintro ⟨hξ, h1, h2⟩
        refine ⟨hξ, ?_, ?_⟩
        · rcases min_le_iff.1 h1 with h1 | h1
          · exact min_le_iff.2 (Or.inl ((hmono z ξ hzc hξ).2 h1))
          · exact min_le_iff.2 (Or.inr ((hmono w ξ hwc hξ).2 h1))
        · rcases le_max_iff.1 h2 with h2 | h2
          · exact le_max_iff.2 (Or.inl ((hmono ξ z hξ hzc).2 h2))
          · exact le_max_iff.2 (Or.inr ((hmono ξ w hξ hwc).2 h2))

/-- Auxiliary (§1.2; the content of Corollary 1.2.3). `ρ(z, w) = ρ(z, ξ) + ρ(ξ, w)` if and only if `ξ` lies on the
arc `geodArcFinite z w` (also for `z = w`). -/
theorem k92g_between_iff (z w ξ : ℍ) :
    dist z w = dist z ξ + dist ξ w ↔ ξ ∈ geodArcFinite z w := by
  obtain ⟨p, -, q, -, -, g, -, hz, hw, hseg⟩ := k92g_segment_chart z w
  rw [hseg, ← dist_smul g z w, ← dist_smul g z ξ, ← dist_smul g ξ w,
    k92g_vertical_iff (hz.trans hw.symm), hz]

/-- Auxiliary (§1.2). The element `ξ ↦ −1/ξ` of `SL(2,ℝ)` preserves the imaginary axis and reverses it:
`i e^u ↦ i e^{−u}`. -/
theorem k92g_flip : ∃ s : SL(2, ℝ), (∀ ξ : ℍ, (s • ξ).re = 0 ↔ ξ.re = 0) ∧
    ∀ u : ℝ, s • UpperHalfPlane.mk ⟨0, Real.exp u⟩ (Real.exp_pos u) =
      UpperHalfPlane.mk ⟨0, Real.exp (-u)⟩ (Real.exp_pos (-u)) := by
  obtain ⟨s, hs⟩ := k92g_sl_of_det_pos (a := 0) (b := -1) (c := 1) (d := 0) (by norm_num)
  have e : ∀ ξ : ℍ, ((s • ξ : ℍ) : ℂ) = -1 / (ξ : ℂ) := fun ξ => by
    rw [hs]
    push_cast
    ring
  refine ⟨s, fun ξ => ?_, fun u => ?_⟩
  · have hn : 0 < Complex.normSq (ξ : ℂ) := Complex.normSq_pos.2 (UpperHalfPlane.ne_zero ξ)
    rw [← UpperHalfPlane.coe_re, e, Complex.div_re]
    simp only [neg_re, one_re, neg_im, one_im, neg_zero, zero_mul, zero_div, add_zero, UpperHalfPlane.coe_re]
    constructor
    · intro h
      rw [neg_one_mul, neg_div, neg_eq_zero, div_eq_zero_iff] at h
      exact h.resolve_right hn.ne'
    · intro h
      rw [h]
      simp
  · apply UpperHalfPlane.ext
    show ((s • UpperHalfPlane.mk ⟨0, Real.exp u⟩ (Real.exp_pos u) : ℍ) : ℂ) = ⟨0, Real.exp (-u)⟩
    rw [e, UpperHalfPlane.coe_mk]
    have he := Real.exp_pos u
    apply Complex.ext
    · simp only [Complex.div_re, Complex.normSq_mk, Complex.neg_re, Complex.one_re, Complex.neg_im,
        Complex.one_im]
      ring
    · simp only [Complex.div_im, Complex.normSq_mk, Complex.neg_re, Complex.one_re, Complex.neg_im,
        Complex.one_im]
      rw [Real.exp_neg]
      field_simp
      ring

/-- Auxiliary (§1.2). Normal form of a complete geodesic: an element `g ∈ SL(2,ℝ)` carrying a line or semicircle
`geodArc p q` orthogonal to ℝ onto the imaginary axis carries an isometric `γ : ℝ → ℍ` to the unit-speed upward
parametrization `g • γ(t) = i e^{c + t}` of the axis. -/
theorem k92g_normal_form {γ : ℝ → ℍ} (hγ : Isometry γ) :
    ∃ p ∈ pointsAtInfinity, ∃ q ∈ pointsAtInfinity, p ≠ q ∧ ∃ g : SL(2, ℝ),
      (∀ ξ : ℍ, ξ ∈ geodArc p q ↔ (g • ξ).re = 0) ∧
      ∃ c : ℝ, ∀ t : ℝ, g • γ t = UpperHalfPlane.mk ⟨0, Real.exp (c + t)⟩ (Real.exp_pos (c + t)) := by
  obtain ⟨p, hp, q, hq, hpq, g, hline, hz, hw, -⟩ := k92g_segment_chart (γ 0) (γ 1)
  have hd : ∀ s t : ℝ, dist (g • γ s) (g • γ t) = |s - t| := fun s t => by
    rw [dist_smul, hγ.dist_eq, Real.dist_eq]
  have hVd : ∀ u v : ℝ, dist (UpperHalfPlane.mk ⟨0, Real.exp u⟩ (Real.exp_pos u))
      (UpperHalfPlane.mk ⟨0, Real.exp v⟩ (Real.exp_pos v)) = |u - v| := fun u v => by
    rw [← Real.dist_eq]
    exact (UpperHalfPlane.isometry_vertical_line 0).dist_eq u v
  obtain ⟨a, ha⟩ : ∃ a : ℝ, Real.log (g • γ 0).im = a := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, Real.log (g • γ 1).im - a = σ := ⟨_, rfl⟩
  have hσ1 : |σ| = 1 := by
    have h01 := hd 0 1
    rw [UpperHalfPlane.dist_of_re_eq (hz.trans hw.symm), Real.dist_eq, ha] at h01
    rw [← hσ, abs_sub_comm, h01]
    norm_num
  have hpt : ∀ (t : ℝ) (ξ : ℍ), ξ.re = 0 → Real.log ξ.im = a + σ * t →
      ξ = UpperHalfPlane.mk ⟨0, Real.exp (a + σ * t)⟩ (Real.exp_pos _) := fun t ξ h0 hl => by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact h0
    · show ξ.im = Real.exp (a + σ * t)
      rw [← hl, Real.exp_log ξ.im_pos]
  have hA : g • γ 0 = UpperHalfPlane.mk ⟨0, Real.exp (a + σ * 0)⟩ (Real.exp_pos _) :=
    hpt 0 _ hz (by rw [ha]; ring)
  have hB : g • γ 1 = UpperHalfPlane.mk ⟨0, Real.exp (a + σ * 1)⟩ (Real.exp_pos _) :=
    hpt 1 _ hw (by rw [← hσ]; ring)
  have hAB : g • γ 0 ≠ g • γ 1 := fun h => by
    have h01 := hd 0 1
    rw [h, dist_self] at h01
    norm_num at h01
  have key : ∀ t : ℝ, g • γ t = UpperHalfPlane.mk ⟨0, Real.exp (a + σ * t)⟩ (Real.exp_pos _) := by
    intro t
    refine k92g_rigid (X' := UpperHalfPlane.mk ⟨0, Real.exp (a + σ * t)⟩ (Real.exp_pos _)) hz hw rfl hAB ?_ ?_
    · rw [hd, hA, hVd, show a + σ * 0 - (a + σ * t) = σ * (0 - t) by ring, abs_mul, hσ1, one_mul]
    · rw [hd, hB, hVd, show a + σ * 1 - (a + σ * t) = σ * (1 - t) by ring, abs_mul, hσ1, one_mul]
  rcases (abs_eq zero_le_one).1 hσ1 with h1 | h1
  · refine ⟨p, hp, q, hq, hpq, g, hline, a, fun t => ?_⟩
    rw [key t, h1, one_mul]
  · obtain ⟨s, hs_re, hs_V⟩ := k92g_flip
    refine ⟨p, hp, q, hq, hpq, s * g, fun ξ => ?_, -a, fun t => ?_⟩
    · rw [hline, mul_smul, hs_re]
    · rw [mul_smul, key t, hs_V, h1, show -(a + -1 * t) = -a + t by ring]

/-- Auxiliary (§1.2). The image of `[0, |a − b|]` under `s ↦ a + σ s`, for the sign `σ` of `b − a`, is `[[a, b]]`. -/
theorem k92g_affine_image (a b : ℝ) :
    ∃ σ : ℝ, |σ| = 1 ∧ (fun s => a + σ * s) '' Icc 0 |a - b| = uIcc a b ∧ a + σ * |a - b| = b := by
  rcases le_total a b with h | h
  · refine ⟨1, abs_one, ?_, ?_⟩
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h), Set.uIcc_of_le h]
      simp only [one_mul]
      rw [Set.image_const_add_Icc, add_zero, add_sub_cancel]
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
      ring
  · refine ⟨-1, by norm_num, ?_, ?_⟩
    · rw [abs_of_nonneg (sub_nonneg.2 h), Set.uIcc_of_ge h]
      simp only [neg_one_mul, ← sub_eq_add_neg]
      rw [Set.image_const_sub_Icc, sub_zero, sub_sub_cancel]
    · rw [abs_of_nonneg (sub_nonneg.2 h)]
      ring

/-- Auxiliary (§1.2). In a chart `g` of `geodArc p q`, the arc `geodArcFinite z w` is the image under `g⁻¹` of the
segment of the imaginary axis between `g • z` and `g • w`. -/
theorem k92g_arc_image {z w : ℍ} {g : SL(2, ℝ)} (hseg : ∀ ξ : ℍ, ξ ∈ geodArcFinite z w ↔
      (g • ξ).re = 0 ∧ (g • ξ).im ∈ uIcc (g • z).im (g • w).im) :
    (fun y : ℝ => g⁻¹ • UpperHalfPlane.mk ⟨0, Real.exp y⟩ (Real.exp_pos y)) ''
      uIcc (Real.log (g • z).im) (Real.log (g • w).im) = geodArcFinite z w := by
  ext ξ
  rw [hseg]
  constructor
  · rintro ⟨y, hy, rfl⟩
    dsimp only
    rw [smul_inv_smul]
    refine ⟨rfl, ?_⟩
    show Real.exp y ∈ uIcc (g • z).im (g • w).im
    exact (k92g_log_mem_uIcc (g • z).im_pos (g • w).im_pos (Real.exp_pos y)).1 (by rwa [Real.log_exp])
  · rintro ⟨h0, h1⟩
    refine ⟨Real.log (g • ξ).im, (k92g_log_mem_uIcc (g • z).im_pos (g • w).im_pos (g • ξ).im_pos).2 h1, ?_⟩
    show g⁻¹ • _ = ξ
    rw [inv_smul_eq_iff]
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact h0.symm
    · exact Real.exp_log (g • ξ).im_pos

/-- Auxiliary (§1.2). The arc `geodArcFinite z w` is a geodesic segment from `z` to `w`. -/
theorem k92g_isGeodesicSegment (z w : ℍ) : IsGeodesicSegment (geodArcFinite z w) z w := by
  obtain ⟨p, -, q, -, -, g, -, hz, hw, hseg⟩ := k92g_segment_chart z w
  have hd : dist z w = |Real.log (g • z).im - Real.log (g • w).im| := by
    rw [← dist_smul g, UpperHalfPlane.dist_of_re_eq (hz.trans hw.symm), Real.dist_eq]
  have hpt : ∀ ξ : ℍ, (g • ξ).re = 0 →
      g⁻¹ • UpperHalfPlane.mk ⟨0, Real.exp (Real.log (g • ξ).im)⟩ (Real.exp_pos _) = ξ := fun ξ h0 => by
    rw [inv_smul_eq_iff]
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact h0.symm
    · exact Real.exp_log (g • ξ).im_pos
  obtain ⟨σ, hσ1, himg, hσ⟩ := k92g_affine_image (Real.log (g • z).im) (Real.log (g • w).im)
  refine ⟨fun s => g⁻¹ • UpperHalfPlane.mk ⟨0, Real.exp (Real.log (g • z).im + σ * s)⟩ (Real.exp_pos _),
    ?_, ?_, fun s _ t _ => ?_, ?_⟩
  · show g⁻¹ • UpperHalfPlane.mk ⟨0, Real.exp (Real.log (g • z).im + σ * 0)⟩ (Real.exp_pos _) = z
    rw [mul_zero, add_zero]
    exact hpt z hz
  · show g⁻¹ • UpperHalfPlane.mk ⟨0, Real.exp (Real.log (g • z).im + σ * dist z w)⟩ (Real.exp_pos _) = w
    rw [hd, hσ]
    exact hpt w hw
  · show dist (g⁻¹ • UpperHalfPlane.mk ⟨0, Real.exp (Real.log (g • z).im + σ * s)⟩ (Real.exp_pos _))
      (g⁻¹ • UpperHalfPlane.mk ⟨0, Real.exp (Real.log (g • z).im + σ * t)⟩ (Real.exp_pos _)) = |s - t|
    rw [dist_smul, ← Real.dist_eq]
    refine ((UpperHalfPlane.isometry_vertical_line 0).dist_eq _ _).trans ?_
    rw [Real.dist_eq, Real.dist_eq, show Real.log (g • z).im + σ * s - (Real.log (g • z).im + σ * t) =
      σ * (s - t) by ring, abs_mul, hσ1, one_mul]
  · rw [← k92g_arc_image hseg, ← himg, hd, Set.image_image]

/-- Auxiliary (§1.2). A geodesic segment from `z` to `w` is the arc `geodArcFinite z w`. -/
theorem k92g_segment_unique {z w : ℍ} {S : Set ℍ} (hS : IsGeodesicSegment S z w) : S = geodArcFinite z w := by
  obtain ⟨γ, h0, h1, hiso, rfl⟩ := hS
  have htri : ∀ s ∈ Icc (0 : ℝ) (dist z w), dist z (γ s) = s ∧ dist (γ s) w = dist z w - s := fun s hs => by
    have hs0 : (0 : ℝ) ∈ Icc (0 : ℝ) (dist z w) := ⟨le_rfl, hs.1.trans hs.2⟩
    have hsd : dist z w ∈ Icc (0 : ℝ) (dist z w) := ⟨hs.1.trans hs.2, le_rfl⟩
    constructor
    · have e := hiso 0 hs0 s hs
      rw [h0] at e
      rw [e, zero_sub, abs_neg, abs_of_nonneg hs.1]
    · have e := hiso s hs (dist z w) hsd
      rw [h1] at e
      rw [e, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hs.2)]
  ext ξ
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨e1, e2⟩ := htri s hs
    rw [← k92g_between_iff, e1, e2]
    ring
  · intro hξ
    have hb := (k92g_between_iff z w ξ).2 hξ
    have hs : dist z ξ ∈ Icc (0 : ℝ) (dist z w) := ⟨dist_nonneg, by linarith [dist_nonneg (x := ξ) (y := w)]⟩
    obtain ⟨e1, e2⟩ := htri _ hs
    refine ⟨dist z ξ, hs, ?_⟩
    by_cases hzw : z = w
    · have hzw0 : dist z w = 0 := by rw [hzw, dist_self]
      have h00 : dist z ξ = 0 := le_antisymm (hs.2.trans_eq hzw0) dist_nonneg
      rw [h00, h0]
      exact dist_eq_zero.1 h00
    · obtain ⟨p, -, q, -, -, g, -, hz, hw, hseg⟩ := k92g_segment_chart z w
      have hξ0 := ((hseg ξ).1 hξ).1
      apply MulAction.injective g
      refine k92g_rigid hz hw hξ0 (fun h => hzw (MulAction.injective g h)) ?_ ?_
      · rw [dist_smul, dist_smul, e1]
      · rw [dist_smul, dist_smul, dist_comm w, dist_comm w, e2]
        linarith

/-- Auxiliary (§1.2). The Möbius formula for the action of `h ∈ SL(2,ℝ)` at the point `i e^y` of the imaginary
axis, and the nonvanishing of its denominator. -/
theorem k92g_smul_axis (h : SL(2, ℝ)) (y : ℝ) :
    ((h • UpperHalfPlane.mk ⟨0, Real.exp y⟩ (Real.exp_pos y) : ℍ) : ℂ) =
      (((h 0 0 : ℝ) : ℂ) * ((Real.exp y : ℂ) * I) + ((h 0 1 : ℝ) : ℂ)) /
        (((h 1 0 : ℝ) : ℂ) * ((Real.exp y : ℂ) * I) + ((h 1 1 : ℝ) : ℂ)) ∧
      ((h 1 0 : ℝ) : ℂ) * ((Real.exp y : ℂ) * I) + ((h 1 1 : ℝ) : ℂ) ≠ 0 := by
  have hV : ((UpperHalfPlane.mk ⟨0, Real.exp y⟩ (Real.exp_pos y) : ℍ) : ℂ) = (Real.exp y : ℂ) * I :=
    Complex.ext
      (by simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im]; ring)
      (by simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im]; ring)
  constructor
  · rw [UpperHalfPlane.coe_specialLinearGroup_apply, hV]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
  · intro hD
    have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
      have := h.2
      rw [Matrix.det_fin_two] at this
      exact this
    have hre := congrArg Complex.re hD
    have him := congrArg Complex.im hD
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.mul_im, Complex.zero_re, Complex.zero_im, mul_zero, zero_mul, mul_one,
      add_zero, zero_add, sub_self] at hre him
    have h10 : h 1 0 = 0 := (mul_eq_zero.1 him).resolve_right (Real.exp_pos y).ne'
    rw [hre, h10] at hdet
    simp at hdet

/-- Auxiliary (§1.2). A Lipschitz path from `z` to `w` tracing the arc `geodArcFinite z w`, of length `ρ(z, w)` for
the density `1/Im`. -/
theorem k92g_lrcurve (z w : ℍ) :
    ∃ γ : LiZhongQC.LRCurve, LiZhongQC.IsPathIn LiZhongQC.upperHalf z w γ ∧
      γ.closedTrace = (↑) '' geodArcFinite z w ∧
      γ.rhoLength (fun ζ => ENNReal.ofReal (1 / ζ.im)) = ENNReal.ofReal (dist z w) := by
  obtain ⟨p, -, q, -, -, g, -, hz, hw, hseg⟩ := k92g_segment_chart z w
  have himg := k92g_arc_image hseg
  obtain ⟨a, ha⟩ : ∃ a : ℝ, Real.log (g • z).im = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, Real.log (g • w).im = b := ⟨_, rfl⟩
  rw [ha, hb] at himg
  have hd : dist z w = |b - a| := by
    rw [← dist_smul g, UpperHalfPlane.dist_of_re_eq (hz.trans hw.symm), Real.dist_eq, ha, hb, abs_sub_comm]
  -- the points `V y = i e^y` of the axis, and `z = g⁻¹ • V a`, `w = g⁻¹ • V b`
  have hpt : ∀ (ξ : ℍ) (y : ℝ), (g • ξ).re = 0 → Real.log (g • ξ).im = y →
      g⁻¹ • UpperHalfPlane.mk ⟨0, Real.exp y⟩ (Real.exp_pos y) = ξ := fun ξ y h0 hy => by
    rw [inv_smul_eq_iff]
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact h0.symm
    · show Real.exp y = (g • ξ).im
      rw [← hy, Real.exp_log (g • ξ).im_pos]
  -- the path `F t = g⁻¹ • V (a + t (b − a))`, written out
  obtain ⟨u, hu⟩ : ∃ u : ℝ → ℂ, u = fun t => (Real.exp (a + t * (b - a)) : ℂ) * I := ⟨_, rfl⟩
  have hu' : ∀ t, u t = (Real.exp (a + t * (b - a)) : ℂ) * I := fun t => by rw [hu]
  obtain ⟨h, hh⟩ : ∃ h : SL(2, ℝ), h = g⁻¹ := ⟨_, rfl⟩
  have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    have := h.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hdetC : ((h 0 0 : ℝ) : ℂ) * ((h 1 1 : ℝ) : ℂ) - ((h 0 1 : ℝ) : ℂ) * ((h 1 0 : ℝ) : ℂ) = 1 := by
    exact_mod_cast hdet
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℂ, F = fun t => (((h 0 0 : ℝ) : ℂ) * u t + ((h 0 1 : ℝ) : ℂ)) /
      (((h 1 0 : ℝ) : ℂ) * u t + ((h 1 1 : ℝ) : ℂ)) := ⟨_, rfl⟩
  have hD : ∀ t, ((h 1 0 : ℝ) : ℂ) * u t + ((h 1 1 : ℝ) : ℂ) ≠ 0 := fun t => by
    rw [hu']
    exact (k92g_smul_axis h (a + t * (b - a))).2
  have hFP : ∀ t, F t = ((g⁻¹ • UpperHalfPlane.mk ⟨0, Real.exp (a + t * (b - a))⟩ (Real.exp_pos _) : ℍ) : ℂ) :=
    fun t => by
      rw [← hh, (k92g_smul_axis h (a + t * (b - a))).1, hF, ← hu']
  have hFpos : ∀ t, 0 < (F t).im := fun t => by
    rw [hFP]
    exact UpperHalfPlane.im_pos _
  -- the derivative
  have hud : ∀ t, HasDerivAt u (((b - a : ℝ) : ℂ) * u t) t := fun t => by
    have h1 : HasDerivAt (fun t : ℝ => a + t * (b - a)) (b - a) t := by
      simpa using ((hasDerivAt_id t).mul_const (b - a)).const_add a
    have h2 := (h1.exp.ofReal_comp).mul_const I
    rw [hu]
    convert h2 using 1
    push_cast
    ring
  have hFd : ∀ t, HasDerivAt F (((b - a : ℝ) : ℂ) * u t / (((h 1 0 : ℝ) : ℂ) * u t + ((h 1 1 : ℝ) : ℂ)) ^ 2) t :=
    fun t => by
      have hN := ((hud t).const_mul ((h 0 0 : ℝ) : ℂ)).add_const ((h 0 1 : ℝ) : ℂ)
      have hDd := ((hud t).const_mul ((h 1 0 : ℝ) : ℂ)).add_const ((h 1 1 : ℝ) : ℂ)
      have hq := hN.div hDd (hD t)
      rw [hF]
      convert hq using 1
      congr 1
      linear_combination (-(((b - a : ℝ) : ℂ) * u t)) * hdetC
  -- `‖F′‖ = |b − a| Im F`
  have hnorm : ∀ t, ‖((b - a : ℝ) : ℂ) * u t / (((h 1 0 : ℝ) : ℂ) * u t + ((h 1 1 : ℝ) : ℂ)) ^ 2‖ =
      |b - a| * (F t).im := fun t => by
    have hFim : (F t).im = (u t).im / Complex.normSq (((h 1 0 : ℝ) : ℂ) * u t + ((h 1 1 : ℝ) : ℂ)) := by
      rw [hF]
      show (LiZhongQC.mobiusFn ((h 0 0 : ℝ) : ℂ) ((h 0 1 : ℝ) : ℂ) ((h 1 0 : ℝ) : ℂ) ((h 1 1 : ℝ) : ℂ) (u t)).im = _
      rw [LiZhongQC.mobiusFn_im_real, hdet, one_mul]
    have hut : ‖u t‖ = (u t).im := by
      rw [hu']
      simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, add_zero]
    rw [hFim, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.sq_norm, hut]
    ring
  -- `Im F ≤ Im z · e^{|b − a|}` on `[0, 1]`
  have hz' : g⁻¹ • UpperHalfPlane.mk ⟨0, Real.exp a⟩ (Real.exp_pos a) = z := hpt z a hz ha
  have hw' : g⁻¹ • UpperHalfPlane.mk ⟨0, Real.exp b⟩ (Real.exp_pos b) = w := hpt w b hw hb
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, (F t).im ≤ z.im * Real.exp |b - a| := fun t ht => by
    rw [hFP]
    refine (UpperHalfPlane.im_le_im_mul_exp_dist _ z).trans ?_
    gcongr
    rw [← hz', dist_smul, ← Real.dist_eq]
    refine ((UpperHalfPlane.isometry_vertical_line 0).dist_eq _ _).trans_le ?_
    rw [Real.dist_eq, show a + t * (b - a) - a = t * (b - a) by ring, abs_mul, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (abs_nonneg _) ht.2
  set C : NNReal := ⟨|b - a| * (z.im * Real.exp |b - a|), by positivity⟩ with hC
  have hLip : LipschitzOnWith C F (Icc 0 1) := by
    refine (convex_Icc (0 : ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t _ => (hFd t).hasDerivWithinAt) fun t ht => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, hnorm t]
    exact mul_le_mul_of_nonneg_left (hbound t ht) (abs_nonneg _)
  refine ⟨⟨F, fun t _ => ⟨C, Ioo 0 1, self_mem_nhdsWithin, hLip.mono Ioo_subset_Icc_self⟩⟩, ⟨⟨C, hLip⟩, ?_, ?_, ?_⟩,
    ?_, ?_⟩
  · show F 0 = z
    rw [hFP, zero_mul, add_zero, hz']
  · show F 1 = w
    rw [hFP, one_mul, add_sub_cancel, hw']
  · rintro _ ⟨t, -, rfl⟩
    exact hFpos t
  · show F '' Icc 0 1 = _
    rw [← himg, ← Set.image_comp]
    have hseg01 : (fun t : ℝ => a + t * (b - a)) '' Icc 0 1 = uIcc a b := by
      rw [← segment_eq_uIcc, segment_eq_image']
      rfl
    rw [← hseg01, Set.image_image]
    exact Set.image_congr fun t _ => hFP t
  · show ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (1 / (F t).im) * ‖deriv F t‖ₑ = ENNReal.ofReal (dist z w)
    have hint : ∀ t ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (1 / (F t).im) * ‖deriv F t‖ₑ = ENNReal.ofReal |b - a| :=
      fun t _ => by
        have hne := (hFpos t).ne'
        rw [(hFd t).deriv, ← ofReal_norm, ← ENNReal.ofReal_mul (one_div_pos.2 (hFpos t)).le, hnorm t]
        congr 1
        field_simp
    rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo hint, MeasureTheory.setLIntegral_const,
      Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one, hd]

/-- **Theorem 1.2.1** (§1.2; l. 178), segment form. A geodesic segment joining two distinct points lies on a
semicircle or straight line orthogonal to ℝ. -/
theorem thm1_2_1_i {z w : ℍ} {S : Set ℍ} (hzw : z ≠ w) (hS : IsGeodesicSegment S z w) :
    ∃ p ∈ pointsAtInfinity, ∃ q ∈ pointsAtInfinity, p ≠ q ∧ S ⊆ geodArc p q := by
  -- `z ≠ w` is not needed: for `z = w` the segment `{z}` also lies on such a line
  have _ := hzw
  obtain ⟨p, hp, q, hq, hpq, g, hline, -, -, hseg⟩ := k92g_segment_chart z w
  refine ⟨p, hp, q, hq, hpq, ?_⟩
  rw [k92g_segment_unique hS]
  exact fun ξ hξ => (hline ξ).2 ((hseg ξ).1 hξ).1

/-- **Theorem 1.2.1** (§1.2; l. 178). The geodesics in ℍ are the semicircles and straight lines orthogonal to the
real axis. Modelling: a whole line or semicircle is `geodArc p q` with distinct `p, q ∈ ℝ ∪ {∞}`. -/
theorem thm1_2_1_ii (L : Set ℍ) :
    IsGeodesic L ↔ ∃ p ∈ pointsAtInfinity, ∃ q ∈ pointsAtInfinity, p ≠ q ∧ L = geodArc p q := by
  have hV : ∀ (g : SL(2, ℝ)) (ξ : ℍ), (g • ξ).re = 0 →
      UpperHalfPlane.mk ⟨0, Real.exp (Real.log (g • ξ).im)⟩ (Real.exp_pos _) = g • ξ := fun g ξ hξ => by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact hξ.symm
    · exact Real.exp_log (g • ξ).im_pos
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨p, hp, q, hq, hpq, g, hline, c, hc⟩ := k92g_normal_form hγ
    refine ⟨p, hp, q, hq, hpq, ?_⟩
    ext ξ
    rw [hline]
    constructor
    · rintro ⟨t, rfl⟩
      exact (congrArg UpperHalfPlane.re (hc t)).trans rfl
    · intro hξ
      refine ⟨Real.log (g • ξ).im - c, MulAction.injective g ?_⟩
      show g • _ = g • ξ
      rw [hc, add_sub_cancel]
      exact hV g ξ hξ
  · rintro ⟨p, hp, q, hq, hpq, rfl⟩
    obtain ⟨g, hg⟩ := k92g_chart hp hq hpq
    refine ⟨fun t => g⁻¹ • UpperHalfPlane.mk ⟨0, Real.exp t⟩ (Real.exp_pos t),
      (isometry_smul ℍ g⁻¹).comp (UpperHalfPlane.isometry_vertical_line 0), ?_⟩
    ext ξ
    rw [hg]
    constructor
    · intro hξ
      refine ⟨Real.log (g • ξ).im, ?_⟩
      show g⁻¹ • _ = ξ
      rw [hV g ξ hξ, inv_smul_smul]
    · rintro ⟨t, rfl⟩
      exact (congrArg UpperHalfPlane.re (smul_inv_smul g _)).trans rfl

/-- **Definition** (§1.2; l. 190; cited at l. 1303–1329, 1752). The geodesic segment `[z, w]`.
Modelling: the explicit arc `geodArcFinite z w` (`{z}` for `z = w`). -/
def geodSegment (z w : ℍ) : Set ℍ := geodArcFinite z w

/-- **Corollary 1.2.2** (§1.2; l. 190). Any two points `z, w ∈ ℍ` can be joined by a unique geodesic, and `ρ(z, w)`
is the hyperbolic length of the geodesic segment `[z, w]`.
Modelling: the length is `rhoLength` for the density `1/Im`, of a Lipschitz path tracing `[z, w]`. -/
theorem cor1_2_2 (z w : ℍ) :
    (∃! S : Set ℍ, IsGeodesicSegment S z w) ∧ IsGeodesicSegment (geodSegment z w) z w ∧
      ∃ γ : LiZhongQC.LRCurve, LiZhongQC.IsPathIn LiZhongQC.upperHalf z w γ ∧
        γ.closedTrace = (↑) '' geodSegment z w ∧
        γ.rhoLength (fun ζ => ENNReal.ofReal (1 / ζ.im)) = ENNReal.ofReal (dist z w) := by
  exact ⟨⟨geodSegment z w, k92g_isGeodesicSegment z w, fun _ hS => k92g_segment_unique hS⟩,
    k92g_isGeodesicSegment z w, k92g_lrcurve z w⟩

/-- **Corollary 1.2.3** (§1.2; l. 192; cited at l. 202). If `z ≠ w`, then `ρ(z, w) = ρ(z, ξ) + ρ(ξ, w)` if and only
if `ξ ∈ [z, w]`. -/
theorem cor1_2_3 {z w : ℍ} (hzw : z ≠ w) (ξ : ℍ) :
    dist z w = dist z ξ + dist ξ w ↔ ξ ∈ geodSegment z w := by
  -- `z ≠ w` is not needed: for `z = w` both sides say `ξ = z`
  have _ := hzw
  exact k92g_between_iff z w ξ

/-- Auxiliary. `T = ±g ∈ PSL(2,ℝ)` acts on ℍ as its lift `g ∈ SL(2,ℝ)`. -/
theorem k92_psl_smul_mk (g : SL(2, ℝ)) (z : ℍ) : ((g : PSL(2, ℝ))) • z = g • z := by
  show Matrix.ProjectiveSpecialLinearGroup.toPGL (g : PSL(2, ℝ)) • z = g • z
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, UpperHalfPlane.pglMk_smul]
  rfl

/-- Auxiliary. Every `T ∈ PSL(2,ℝ)` acts on ℍ by an isometry (Theorem 1.1.2 through a lift). -/
theorem k92_isometry_psl_smul (T : PSL(2, ℝ)) : Isometry fun z : ℍ => T • z := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective T
  have h : (fun z : ℍ => (QuotientGroup.mk g : PSL(2, ℝ)) • z) = fun z : ℍ => g • z :=
    funext fun z => k92_psl_smul_mk g z
  rw [h]
  exact isometry_smul ℍ g

/-- **Theorem 1.2.4** (§1.2; l. 200; cited at l. 286). Any transformation in `PSL(2,ℝ)` maps geodesics onto
geodesics. -/
theorem thm1_2_4 (T : PSL(2, ℝ)) {L : Set ℍ} (hL : IsGeodesic L) : IsGeodesic ((T • ·) '' L) := by
  obtain ⟨γ, hγ, rfl⟩ := hL
  exact ⟨fun t => T • γ t, (k92_isometry_psl_smul T).comp hγ, by rw [← range_comp]; rfl⟩

/-- **Definition** (§1.2; l. 204–208). The cross-ratio `(z₁, z₂; z₃, z₄) = (z₁ − z₂)(z₃ − z₄)/((z₂ − z₃)(z₄ − z₁))`
of distinct points of `ℂ̂`.
Modelling: when one point is `∞`, its two factors cancel (the limit), e.g. `(z₁, z₂; z₃, ∞) = −(z₁ − z₂)/(z₂ − z₃)`;
junk `0` when two points are `∞` (not distinct). -/
def crossRatio (z₁ z₂ z₃ z₄ : ExtPlane) : ℂ :=
  z₁.elim (z₂.elim 0 fun b => z₃.elim 0 fun c => z₄.elim 0 fun d => -(c - d) / (b - c))
    (fun a => z₂.elim (z₃.elim 0 fun c => z₄.elim 0 fun d => -(c - d) / (d - a))
      (fun b => z₃.elim (z₄.elim 0 fun d => -(a - b) / (d - a))
        (fun c => z₄.elim (-(a - b) / (b - c)) fun d => (a - b) * (c - d) / ((b - c) * (d - a)))))

/-- Auxiliary (§1.2). Along `t ↦ h • (i e^{c + t})` (`h ∈ SL(2,ℝ)`), the end points in `ℂ̂` are `h(0)` at `−∞` and
`h(∞)` at `+∞`. -/
theorem k92g_ends (h : SL(2, ℝ)) (c : ℝ) :
    Tendsto (fun t : ℝ => ((((h • UpperHalfPlane.mk ⟨0, Real.exp (c + t)⟩ (Real.exp_pos (c + t)) : ℍ) : ℂ)) :
        ExtPlane)) atBot
      (𝓝 (LiZhongQC.mobiusExt ((h 0 0 : ℝ) : ℂ) ((h 0 1 : ℝ) : ℂ) ((h 1 0 : ℝ) : ℂ) ((h 1 1 : ℝ) : ℂ)
        ((0 : ℂ) : ExtPlane))) ∧
    Tendsto (fun t : ℝ => ((((h • UpperHalfPlane.mk ⟨0, Real.exp (c + t)⟩ (Real.exp_pos (c + t)) : ℍ) : ℂ)) :
        ExtPlane)) atTop
      (𝓝 (LiZhongQC.mobiusExt ((h 0 0 : ℝ) : ℂ) ((h 0 1 : ℝ) : ℂ) ((h 1 0 : ℝ) : ℂ) ((h 1 1 : ℝ) : ℂ)
        LiZhongQC.extInf)) := by
  have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    have := h.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hdetC : ((h 0 0 : ℝ) : ℂ) * ((h 1 1 : ℝ) : ℂ) - ((h 0 1 : ℝ) : ℂ) * ((h 1 0 : ℝ) : ℂ) ≠ 0 := by
    have e : ((h 0 0 : ℝ) : ℂ) * ((h 1 1 : ℝ) : ℂ) - ((h 0 1 : ℝ) : ℂ) * ((h 1 0 : ℝ) : ℂ) = 1 := by
      exact_mod_cast hdet
    rw [e]
    exact one_ne_zero
  have hM := LiZhongQC.continuous_mobiusExt hdetC
  have hfun : (fun t : ℝ => ((((h • UpperHalfPlane.mk ⟨0, Real.exp (c + t)⟩ (Real.exp_pos (c + t)) : ℍ) : ℂ)) :
      ExtPlane)) = fun t : ℝ => LiZhongQC.mobiusExt ((h 0 0 : ℝ) : ℂ) ((h 0 1 : ℝ) : ℂ) ((h 1 0 : ℝ) : ℂ)
        ((h 1 1 : ℝ) : ℂ) ((((Real.exp (c + t) : ℂ) * I : ℂ)) : ExtPlane) := by
    funext t
    obtain ⟨e1, e2⟩ := k92g_smul_axis h (c + t)
    rw [LiZhongQC.mobiusExt_coe e2, e1]
    rfl
  rw [hfun]
  constructor
  · have h0 : Tendsto (fun t : ℝ => (Real.exp (c + t) : ℂ) * I) atBot (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => Real.exp (c + t)) atBot (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_atBot_add_const_left _ c tendsto_id)
      have h2 := ((Complex.continuous_ofReal.tendsto 0).comp h1).mul_const I
      simpa using h2
    exact (hM.tendsto _).comp ((OnePoint.continuous_coe.tendsto _).comp h0)
  · have hn : Tendsto (fun t : ℝ => (Real.exp (c + t) : ℂ) * I) atTop (Bornology.cobounded ℂ) := by
      rw [← tendsto_norm_atTop_iff_cobounded]
      have e : (fun t : ℝ => ‖(Real.exp (c + t) : ℂ) * I‖) = fun t => Real.exp (c + t) := by
        funext t
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
      rw [e]
      exact Real.tendsto_exp_atTop.comp (tendsto_atTop_add_const_left _ c tendsto_id)
    rw [Metric.cobounded_eq_cocompact, ← coclosedCompact_eq_cocompact] at hn
    exact (hM.tendsto _).comp (OnePoint.tendsto_coe_infty.comp hn)

/-- Auxiliary (§1.2). Invariance of the cross-ratio in the configuration of Theorem 1.2.5: for `h ∈ SL(2,ℝ)`,
`(h W, h 0; h Z, h ∞) = (W, 0; Z, ∞) = W/Z`. -/
theorem k92g_crossRatio (h : SL(2, ℝ)) (W Z : ℍ) :
    crossRatio ((((h • W : ℍ) : ℂ)) : ExtPlane)
        (LiZhongQC.mobiusExt ((h 0 0 : ℝ) : ℂ) ((h 0 1 : ℝ) : ℂ) ((h 1 0 : ℝ) : ℂ) ((h 1 1 : ℝ) : ℂ)
          ((0 : ℂ) : ExtPlane))
        ((((h • Z : ℍ) : ℂ)) : ExtPlane)
        (LiZhongQC.mobiusExt ((h 0 0 : ℝ) : ℂ) ((h 0 1 : ℝ) : ℂ) ((h 1 0 : ℝ) : ℂ) ((h 1 1 : ℝ) : ℂ)
          LiZhongQC.extInf) =
      (W : ℂ) / Z := by
  -- the entries of `h`
  obtain ⟨α, hα⟩ : ∃ α : ℝ, h 0 0 = α := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, h 0 1 = β := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, h 1 0 = γ := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, h 1 1 = δ := ⟨_, rfl⟩
  have hdet : (α : ℂ) * δ - β * γ = 1 := by
    have := h.2
    rw [Matrix.det_fin_two, hα, hβ, hγ, hδ] at this
    exact_mod_cast this
  have hden : ∀ ξ : ℍ, (γ : ℂ) * ξ + δ ≠ 0 := fun ξ hD => by
    have him := congrArg Complex.im hD
    have hre := congrArg Complex.re hD
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.zero_im, UpperHalfPlane.coe_im, Complex.add_re, Complex.mul_re, Complex.zero_re,
      sub_zero, UpperHalfPlane.coe_re] at him hre
    have hγ0 : γ = 0 := (mul_eq_zero.1 him).resolve_right ξ.im_pos.ne'
    rw [hγ0, zero_mul, zero_add] at hre
    rw [hγ0, hre] at hdet
    simp at hdet
  have hcoe : ∀ ξ : ℍ, ((h • ξ : ℍ) : ℂ) = ((α : ℂ) * ξ + β) / ((γ : ℂ) * ξ + δ) := fun ξ => by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, hα, hβ, hγ, hδ]
  rw [hcoe, hcoe, hα, hβ, hγ, hδ]
  have hW0 : (W : ℂ) ≠ 0 := UpperHalfPlane.ne_zero W
  have hZ0 : (Z : ℂ) ≠ 0 := UpperHalfPlane.ne_zero Z
  have hWd := hden W
  have hZd := hden Z
  -- the four differences of the cross-ratio, each a single fraction
  have eA0 : (δ : ℂ) ≠ 0 → ((α : ℂ) * W + β) / (γ * W + δ) - β / δ = W / (δ * (γ * W + δ)) := fun hδC => by
    rw [div_sub_div _ _ hWd hδC, div_eq_div_iff (mul_ne_zero hWd hδC) (mul_ne_zero hδC hWd)]
    linear_combination (W : ℂ) * (γ * W + δ) * δ * hdet
  have eB0 : (δ : ℂ) ≠ 0 → (β : ℂ) / δ - ((α : ℂ) * Z + β) / (γ * Z + δ) = -Z / (δ * (γ * Z + δ)) := fun hδC => by
    rw [div_sub_div _ _ hδC hZd, div_eq_div_iff (mul_ne_zero hδC hZd) (mul_ne_zero hδC hZd)]
    linear_combination (-(Z : ℂ)) * (δ * (γ * Z + δ)) * hdet
  have eBinf : (γ : ℂ) ≠ 0 → ((α : ℂ) * Z + β) / (γ * Z + δ) - α / γ = -1 / (γ * (γ * Z + δ)) := fun hγC => by
    rw [div_sub_div _ _ hZd hγC, div_eq_div_iff (mul_ne_zero hZd hγC) (mul_ne_zero hγC hZd)]
    linear_combination (-(γ * (γ * Z + δ))) * hdet
  have eAinf : (γ : ℂ) ≠ 0 → (α : ℂ) / γ - ((α : ℂ) * W + β) / (γ * W + δ) = 1 / (γ * (γ * W + δ)) := fun hγC => by
    rw [div_sub_div _ _ hγC hWd, div_eq_div_iff (mul_ne_zero hγC hWd) (mul_ne_zero hγC hWd)]
    linear_combination (γ * (γ * W + δ)) * hdet
  by_cases hδ0 : δ = 0
  · -- `h(0) = ∞`, `h(∞) = α/γ`
    have hγ0 : γ ≠ 0 := by
      rintro rfl
      rw [hδ0] at hdet
      simp at hdet
    have hγC : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ0
    rw [LiZhongQC.mobiusExt_coe_of_eq_zero (by rw [hδ0]; simp), LiZhongQC.mobiusExt_infty_of_ne hγC]
    show -(_ - _) / (_ - _) = _
    rw [eBinf hγC, eAinf hγC, hδ0, Complex.ofReal_zero, add_zero, add_zero]
    field_simp
  · have hδC : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ0
    rw [LiZhongQC.mobiusExt_coe (by simpa using hδC)]
    by_cases hγ0 : γ = 0
    · -- `h(0) = β/δ`, `h(∞) = ∞`
      rw [LiZhongQC.mobiusExt_infty_of_eq (by exact_mod_cast hγ0)]
      show -(_ - _) / (_ - _) = _
      simp only [LiZhongQC.mobiusFn, mul_zero, zero_add]
      rw [eA0 hδC, eB0 hδC, hγ0, Complex.ofReal_zero, zero_mul, zero_add, zero_mul, zero_add]
      field_simp
    · -- `h(0) = β/δ`, `h(∞) = α/γ`
      have hγC : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ0
      rw [LiZhongQC.mobiusExt_infty_of_ne hγC]
      show (_ - _) * (_ - _) / ((_ - _) * (_ - _)) = _
      simp only [LiZhongQC.mobiusFn, mul_zero, zero_add]
      rw [eA0 hδC, eBinf hγC, eB0 hδC, eAinf hγC]
      field_simp
      exact div_self (by rw [mul_comm]; exact hWd)

/-- **Theorem 1.2.5** (§1.2; l. 210; cited at l. 286). Let `z ≠ w` in ℍ, and let the geodesic joining them have end
points `z*, w* ∈ ℝ ∪ {∞}`, with `z` between `z*` and `w`. Then `ρ(z, w) = ln (w, z*; z, w*)`.
Modelling: the geodesic is an isometric `γ : ℝ → ℍ` tending to `z*` at `−∞` and to `w*` at `+∞` in `ℂ̂`, with
`z = γ s`, `w = γ t`, `s < t`; the cross-ratio is a positive real `r` and `ρ(z, w) = ln r` (no log of a complex). -/
theorem thm1_2_5 {z w : ℍ} (hzw : z ≠ w) {zs ws : ExtPlane} {γ : ℝ → ℍ} (hγ : Isometry γ)
    (hzs : Tendsto (fun t => (((γ t : ℂ)) : ExtPlane)) atBot (𝓝 zs))
    (hws : Tendsto (fun t => (((γ t : ℂ)) : ExtPlane)) atTop (𝓝 ws))
    {s t : ℝ} (hst : s < t) (hs : γ s = z) (ht : γ t = w) :
    ∃ r : ℝ, 0 < r ∧ crossRatio (((w : ℂ)) : ExtPlane) zs (((z : ℂ)) : ExtPlane) ws = r ∧
      dist z w = Real.log r := by
  -- `z ≠ w` follows from `s < t`
  have _ := hzw
  subst hs ht
  obtain ⟨-, -, -, -, -, g, -, c, hc⟩ := k92g_normal_form hγ
  have hγg : ∀ u, γ u = g⁻¹ • UpperHalfPlane.mk ⟨0, Real.exp (c + u)⟩ (Real.exp_pos (c + u)) := fun u => by
    rw [← hc u, inv_smul_smul]
  have hfun : (fun u => (((γ u : ℂ)) : ExtPlane)) = fun u => ((((g⁻¹ • UpperHalfPlane.mk ⟨0, Real.exp (c + u)⟩
      (Real.exp_pos (c + u)) : ℍ) : ℂ)) : ExtPlane) := funext fun u => by rw [hγg u]
  obtain ⟨h1, h2⟩ := k92g_ends g⁻¹ c
  rw [hfun] at hzs hws
  refine ⟨Real.exp (t - s), Real.exp_pos _, ?_, ?_⟩
  · have e : ∀ u : ℝ, ((UpperHalfPlane.mk ⟨0, Real.exp (c + u)⟩ (Real.exp_pos (c + u)) : ℍ) : ℂ) =
        (Real.exp (c + u) : ℂ) * I := fun u => Complex.ext
      (by simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring)
      (by simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring)
    rw [tendsto_nhds_unique hzs h1, tendsto_nhds_unique hws h2, hγg s, hγg t, k92g_crossRatio, e, e,
      mul_div_mul_right _ _ I_ne_zero, ← Complex.ofReal_div, ← Real.exp_sub, show c + t - (c + s) = t - s by ring]
  · rw [Real.log_exp, hγ.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.2 hst)]

/-- **Theorem 1.2.6 (i)** (§1.2; l. 222). For `z, w ∈ ℍ`,
`ρ(z, w) = ln ((|z − w̄| + |z − w|)/(|z − w̄| − |z − w|))`. (The denominator is positive on ℍ.) -/
theorem thm1_2_6_i (z w : ℍ) :
    dist z w = Real.log ((dist (z : ℂ) (conj (w : ℂ)) + dist (z : ℂ) w) /
      (dist (z : ℂ) (conj (w : ℂ)) - dist (z : ℂ) w)) := by
  set A := dist (z : ℂ) (conj (w : ℂ)) with hA
  set B := dist (z : ℂ) w with hB
  have hz := z.im_pos
  have hw := w.im_pos
  have hkey : A ^ 2 - B ^ 2 = 4 * z.im * w.im := by
    rw [hA, hB, Complex.dist_eq, Complex.dist_eq, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [sub_re, sub_im, conj_re, conj_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have hA0 : 0 ≤ A := dist_nonneg
  have hB0 : 0 ≤ B := dist_nonneg
  have hAB : B < A := by nlinarith
  have hE := UpperHalfPlane.exp_half_dist z w
  have hs : √(z.im * w.im) * √(z.im * w.im) = z.im * w.im := Real.mul_self_sqrt (by positivity)
  have hexp : Real.exp (dist z w) = (A + B) / (A - B) := by
    calc Real.exp (dist z w) = Real.exp (dist z w / 2) * Real.exp (dist z w / 2) := by
          rw [← Real.exp_add]; ring_nf
      _ = (B + A) ^ 2 / (4 * (√(z.im * w.im) * √(z.im * w.im))) := by
          rw [hE, ← hA, ← hB]; ring
      _ = (A + B) / (A - B) := by
          rw [hs, div_eq_div_iff (by positivity) (sub_pos.2 hAB).ne']
          linear_combination (A + B) * hkey
  rw [← hexp, Real.log_exp]

/-- **Formula (1.2.2)** (§1.2; l. 255; cited at l. 1590, 2137). The map `f(z) = (zi + 1)/(z + i)` of ℍ onto 𝔘.
Modelling: `f = i · LiZhongQC.cayley` (a different function from the project's Cayley map). -/
def cayleyK (z : ℂ) : ℂ := (z * I + 1) / (z + I)

/-- Helper (§1.2). The inverse `f⁻¹(w) = (1 − iw)/(w − i)` of Katok's Cayley map `cayleyK`. -/
def cayleyKInv (w : ℂ) : ℂ := (1 - I * w) / (w - I)

/-- Auxiliary. Katok's Cayley map is `i` times the project's: `f(z) = i (z − i)/(z + i)`. -/
theorem k92_cayleyK_eq (z : ℂ) : cayleyK z = I * LiZhongQC.cayley z := by
  unfold cayleyK LiZhongQC.cayley
  rw [mul_div_assoc']
  congr 1
  ring_nf
  rw [I_sq]
  ring

/-- Auxiliary. On the unit disc, `f⁻¹(w) = C⁻¹(−iw)` with the project's inverse Cayley map. -/
theorem k92_cayleyKInv_eq {w : ℂ} (hw : ‖w‖ < 1) : cayleyKInv w = LiZhongQC.cayleyInv (-I * w) := by
  have h1 : w - I ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h, Complex.norm_I] at hw
    exact lt_irrefl _ hw
  have h2 : (1 : ℂ) - -I * w ≠ 0 := by
    have : (1 : ℂ) - -I * w = I * (w - I) := by ring_nf; rw [I_sq]; ring
    rw [this]
    exact mul_ne_zero I_ne_zero h1
  unfold cayleyKInv LiZhongQC.cayleyInv
  rw [div_eq_div_iff h1 h2]
  ring_nf
  linear_combination (-w * I + 1) * I_sq

/-- **Unlabelled** (§1.2; l. 258; cited at l. 1590, 2137). `f` is a 1-1 map of ℍ onto 𝔘; its inverse on 𝔘 is
`cayleyKInv`. -/
theorem cayleyK_bijOn :
    BijOn cayleyK LiZhongQC.upperHalf LiZhongQC.unitDisc ∧
      InvOn cayleyKInv cayleyK LiZhongQC.upperHalf LiZhongQC.unitDisc := by
  have hnI : ∀ u : ℂ, ‖I * u‖ = ‖u‖ := fun u => by rw [norm_mul, Complex.norm_I, one_mul]
  have hnI' : ∀ u : ℂ, ‖-I * u‖ = ‖u‖ := fun u => by rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
  have hmaps : MapsTo cayleyK LiZhongQC.upperHalf LiZhongQC.unitDisc := fun z hz => by
    have h := LiZhongQC.cayley_mem_unitDisc (z := z) hz
    simp only [LiZhongQC.unitDisc, mem_ball_zero_iff] at h ⊢
    rw [k92_cayleyK_eq, hnI]
    exact h
  have hmaps' : MapsTo cayleyKInv LiZhongQC.unitDisc LiZhongQC.upperHalf := fun w hw => by
    have hw' : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
    rw [k92_cayleyKInv_eq hw']
    exact LiZhongQC.cayleyInv_mem_upperHalf (by rw [hnI']; exact hw')
  have hinv : InvOn cayleyKInv cayleyK LiZhongQC.upperHalf LiZhongQC.unitDisc := by
    refine ⟨fun z hz => ?_, fun w hw => ?_⟩
    · have hz' : 0 < z.im := hz
      have hc := LiZhongQC.cayley_mem_unitDisc hz'
      have hcK : ‖cayleyK z‖ < 1 := mem_ball_zero_iff.1 (hmaps hz)
      show cayleyKInv (cayleyK z) = z
      rw [k92_cayleyKInv_eq hcK, k92_cayleyK_eq, ← mul_assoc,
        show -I * I = 1 by ring_nf; rw [I_sq]; ring, one_mul, LiZhongQC.cayleyInv_cayley hz']
    · have hw' : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
      show cayleyK (cayleyKInv w) = w
      rw [k92_cayleyKInv_eq hw', k92_cayleyK_eq,
        LiZhongQC.cayley_cayleyInv (by rw [hnI']; exact hw'), ← mul_assoc,
        show I * -I = 1 by ring_nf; rw [I_sq]; ring, one_mul]
  exact ⟨hinv.bijOn hmaps hmaps', hinv⟩

/-- **Definition** (§1.2; l. 260). `ρ*(z, w) = ρ(f⁻¹z, f⁻¹w)` for `z, w ∈ 𝔘`.
Modelling: `f⁻¹z` read in ℍ through `UpperHalfPlane.ofComplex`; junk for `z ∉ 𝔘`, where no statement uses it. -/
def rhoDisc (z w : ℂ) : ℝ :=
  dist (UpperHalfPlane.ofComplex (cayleyKInv z)) (UpperHalfPlane.ofComplex (cayleyKInv w))

/-- **Unlabelled** (§1.2; l. 264–267; used at l. 461–479, 1540, 2063). `ρ*` is the metric derived from the
differential (1.2.3) `ds = 2|dz|/(1 − |z|²)`: the infimum of the lengths of the paths in 𝔘 for that density. -/
theorem rhoDisc_eq_metricDist {z w : ℂ} (hz : z ∈ LiZhongQC.unitDisc) (hw : w ∈ LiZhongQC.unitDisc) :
    ENNReal.ofReal (rhoDisc z w) =
      LiZhongQC.metricDist LiZhongQC.unitDisc (fun ζ => ENNReal.ofReal (LiZhongQC.poincareDensityDisc ζ)) z w := by
  obtain ⟨hbij, hinv⟩ := cayleyK_bijOn
  have hden : ∀ u : ℂ, 0 < u.im → u + I ≠ 0 := fun u hu => LiZhongQC.cayley_den_ne_zero hu
  have hconf : LiZhongQC.IsConformalOnto cayleyK LiZhongQC.upperHalf LiZhongQC.unitDisc := by
    refine ⟨fun u hu => ?_, hbij.injOn, hbij.image_eq⟩
    exact ((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => v * I + 1) u).div
      (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => v + I) u) (hden u hu)).differentiableWithinAt
  have hgmaps : MapsTo cayleyKInv LiZhongQC.unitDisc LiZhongQC.upperHalf := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := hbij.surjOn hv
    rw [hinv.1 hu]
    exact hu
  have hgd : DifferentiableOn ℂ cayleyKInv LiZhongQC.unitDisc := by
    intro v hv
    have hv' : ‖v‖ < 1 := mem_ball_zero_iff.1 hv
    have h1 : v - I ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      rw [h, Complex.norm_I] at hv'
      exact lt_irrefl _ hv'
    exact ((by fun_prop : DifferentiableAt ℂ (fun u : ℂ => 1 - I * u) v).div
      (by fun_prop : DifferentiableAt ℂ (fun u : ℂ => u - I) v) h1).differentiableWithinAt
  have hρ : ∀ u ∈ LiZhongQC.upperHalf, ENNReal.ofReal (LiZhongQC.poincareDensity LiZhongQC.upperHalf u) =
      ENNReal.ofReal (LiZhongQC.poincareDensityDisc (cayleyK u)) * ‖deriv cayleyK u‖ₑ := by
    intro u hu
    have hfu : ‖cayleyK u‖ < 1 := mem_ball_zero_iff.1 (hbij.mapsTo hu)
    have hpos : 0 ≤ LiZhongQC.poincareDensityDisc (cayleyK u) := by
      unfold LiZhongQC.poincareDensityDisc
      have : ‖cayleyK u‖ ^ 2 < 1 := by nlinarith [norm_nonneg (cayleyK u)]
      exact (div_pos two_pos (by linarith)).le
    rw [(LiZhongQC.poincareDensity_well_defined LiZhongQC.isOpen_upperHalf hconf hconf hu).2,
      ← ofReal_norm, ← ENNReal.ofReal_mul hpos]
    congr 1
    unfold LiZhongQC.poincareDensityDisc
    ring
  have hzu := hgmaps hz
  have hwu := hgmaps hw
  have key := LiZhongQC.metricDist_eq_of_isConformalOnto LiZhongQC.isOpen_upperHalf
    (show IsOpen LiZhongQC.unitDisc from Metric.isOpen_ball) hconf hgd
    hgmaps (fun v hv => hinv.2 hv) (fun u hu => hinv.1 hu)
    (ρ := fun u => ENNReal.ofReal (LiZhongQC.poincareDensity LiZhongQC.upperHalf u))
    (ρ' := fun ζ => ENNReal.ofReal (LiZhongQC.poincareDensityDisc ζ)) hρ hzu hwu
  rw [hinv.2 hz, hinv.2 hw] at key
  rw [← key]
  have hp := LiZhongQC.poincareDist_upperHalf (UpperHalfPlane.ofComplex (cayleyKInv z))
    (UpperHalfPlane.ofComplex (cayleyKInv w))
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hzu, UpperHalfPlane.ofComplex_apply_of_im_pos hwu] at hp
  unfold rhoDisc
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hzu, UpperHalfPlane.ofComplex_apply_of_im_pos hwu]
  exact hp.symm

end Katok1992
