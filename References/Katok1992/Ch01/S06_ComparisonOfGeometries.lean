import References.Katok1992.Ch01.S05_HyperbolicTrigonometry

/-!
# Katok 1992, Ch. 1 §1.6 Comparison between hyperbolic, spherical and Euclidean trigonometry

S. Katok, *Fuchsian Groups* (1992), Chapter 1 *Hyperbolic Geometry*, §1.6; source `full.md` of
`Fuchsian groups (Katok, Svetlana) …-3766f6b7…`, lines 529–584.

* Formula (1.6.1) (ℍ_r: ℍ with the metric ds = r|dz|/y, l. 531–535) — `distR`
* Helper (the angle of a spherical triangle at a vertex) — `sphAngle`
* Formula (1.6.2) (spherical trigonometry in the sphere S_r, l. 541–551; cited at l. 569) — `eq1_6_2_i`,
  `eq1_6_2_ii`, `eq1_6_2_iii`
* Formula (1.6.3) (hyperbolic trigonometry in ℍ_r, l. 555–567; cited at l. 569) — `eq1_6_3_i`, `eq1_6_3_ii`,
  `eq1_6_3_iii`

Not items (DESIGN §3): "ℍ_r is a model of a sphere of imaginary radius ir", the curvatures `±1/r²` of `S_r`, ℍ_r and
"the geodesics of `S_r` are great circles" (l. 537–539; heuristic, not cited); the substitution `r ↦ ir` (l. 553);
the Euclidean Sine Rule, Cosine Rule and `α + β + γ = π` (l. 569–584; a heuristic limit `r → ∞`, not cited, and in
Mathlib: `EuclideanGeometry.angle_add_angle_add_angle_eq_pi` and the law of cosines); the exercises.

**Conventions.** The distance of ℍ_r is `r · ρ` (lengths scale by `r`, angles are unchanged). `S_r` is the sphere of
radius `r` about `0` in `ℝ³` (`EuclideanSpace ℝ (Fin 3)`); a spherical triangle has linearly independent vertices
`u, v, w` (not on one great circle), sides `a = r ∠(v, w)`, `b = r ∠(w, u)`, `c = r ∠(u, v)` (great-circle
distances) and opposite angles `α, β, γ` at `u, v, w` (the angles between the tangent directions of the sides).
[OCR] (1.6.3)(iii) is printed `\cosh_{\overline{r}} …`; read as `cosh(c/r) = (cos α cos β + cos γ)/(sin α sin β)`,
the image of (1.6.2)(iii) under `r ↦ ir` and Theorem 1.5.2 (iii) for `r = 1`.
-/

open Complex Set Metric Filter Topology
open scoped UpperHalfPlane Real

noncomputable section

namespace Katok1992

/-- **Formula (1.6.1)** (§1.6; l. 531–535). The distance of ℍ_r, the upper half-plane with the metric
`ds = r √(dx² + dy²)/y`. Modelling: `r · ρ`. -/
def distR (r : ℝ) (z w : ℍ) : ℝ := r * dist z w

/-- Helper (§1.6). The angle at the vertex `u` of the spherical triangle `u v w`: the angle between the components of
`v` and `w` orthogonal to `u` (the tangent directions at `u` of the great-circle arcs towards `v` and `w`). -/
def sphAngle (u v w : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  InnerProductGeometry.angle (v - (inner ℝ v u / ‖u‖ ^ 2) • u) (w - (inner ℝ w u / ‖u‖ ^ 2) • u)

open InnerProductGeometry in
/-- `sin(angle x y) · r = |x − (⟪x,y⟫/r²) y|`-type identity: for `‖x‖ = ‖y‖ = r > 0`, the component of `x`
orthogonal to `y` has norm `r sin(angle x y)`. -/
theorem k92_sph_perp_norm {r : ℝ} (hr : 0 < r) {x y : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ = r)
    (hy : ‖y‖ = r) :
    Real.sin (angle y x) * r = ‖x - (inner ℝ x y / ‖y‖ ^ 2) • y‖ := by
  have hs := sin_angle_mul_norm_mul_norm y x
  rw [hx, hy, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hx, hy] at hs
  have hP2 : ‖x - (inner ℝ x y / ‖y‖ ^ 2) • y‖ ^ 2 = r ^ 2 - inner ℝ x y ^ 2 / r ^ 2 := by
    rw [@norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inner_smul_right, hy, hx]
    field_simp
    ring
  have hnn : 0 ≤ Real.sin (angle y x) * r := mul_nonneg (sin_angle_nonneg _ _) hr.le
  rw [← Real.sqrt_sq (norm_nonneg (x - (inner ℝ x y / ‖y‖ ^ 2) • y)), hP2, ← Real.sqrt_sq hnn]
  congr 1
  have h1 : (Real.sin (angle y x) * (r * r)) ^ 2 = r ^ 2 * r ^ 2 - inner ℝ y x * inner ℝ y x := by
    rw [hs, Real.sq_sqrt]
    have := abs_real_inner_le_norm y x
    rw [hx, hy] at this
    nlinarith [abs_nonneg (inner ℝ y x), sq_abs (inner ℝ y x)]
  rw [real_inner_comm x y] at h1
  have hr2 : r ^ 2 ≠ 0 := by positivity
  rw [eq_sub_iff_add_eq]
  field_simp
  linear_combination h1

open InnerProductGeometry in
/-- **Spherical Cosine Rule I** (vertex `w`), for any three points of the sphere of radius `r`. -/
theorem k92_sph_cos {r : ℝ} (hr : 0 < r) {u v w : EuclideanSpace ℝ (Fin 3)} (hu : ‖u‖ = r) (hv : ‖v‖ = r)
    (hw : ‖w‖ = r) :
    Real.cos (angle u v) = Real.cos (angle v w) * Real.cos (angle w u) +
      Real.sin (angle v w) * Real.sin (angle w u) * Real.cos (sphAngle w u v) := by
  set P := u - (inner ℝ u w / ‖w‖ ^ 2) • w with hP
  set Q := v - (inner ℝ v w / ‖w‖ ^ 2) • w with hQ
  have hsph : sphAngle w u v = angle P Q := rfl
  have hsP := k92_sph_perp_norm hr hu hw
  have hsQ' := k92_sph_perp_norm hr hv hw
  rw [angle_comm w v] at hsQ'
  have hc := cos_angle_mul_norm_mul_norm P Q
  have hPQ : inner ℝ P Q = inner ℝ u v - inner ℝ u w * inner ℝ v w / r ^ 2 := by
    rw [hP, hQ, inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_right,
      inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq, hw, real_inner_comm w u, real_inner_comm w v]
    simp only [RCLike.conj_to_real]
    have : r ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  have hkey : Real.sin (angle v w) * Real.sin (angle w u) * Real.cos (sphAngle w u v) =
      inner ℝ P Q / r ^ 2 := by
    rw [eq_div_iff (by positivity), hsph]
    calc Real.sin (angle v w) * Real.sin (angle w u) * Real.cos (angle P Q) * r ^ 2
        = (Real.sin (angle v w) * r) * (Real.sin (angle w u) * r) * Real.cos (angle P Q) := by ring
      _ = ‖Q‖ * ‖P‖ * Real.cos (angle P Q) := by rw [hsQ', hsP]
      _ = inner ℝ P Q := by rw [← hc]; ring
  rw [hkey, hPQ, cos_angle, cos_angle, cos_angle, hu, hv, hw, real_inner_comm u w]
  have : r ≠ 0 := hr.ne'
  field_simp
  ring

open InnerProductGeometry in
/-- Algebraic core of the spherical Sine Rule: `sin γ · sin a · sin b = √Δ`,
`Δ = 1 − cos²a − cos²b − cos²c + 2 cos a cos b cos c`, from the spherical Cosine Rule at the vertex of `γ`. -/
theorem k92_sph_sin_mul (a b c γ : ℝ) (ha0 : 0 ≤ a) (haπ : a ≤ π) (hb0 : 0 ≤ b) (hbπ : b ≤ π)
    (hγ0 : 0 ≤ γ) (hγπ : γ ≤ π)
    (hcos : Real.cos c = Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos γ) :
    Real.sin γ * (Real.sin a * Real.sin b) =
      √(1 - Real.cos a ^ 2 - Real.cos b ^ 2 - Real.cos c ^ 2 + 2 * Real.cos a * Real.cos b * Real.cos c) := by
  have hsa := Real.sin_nonneg_of_nonneg_of_le_pi ha0 haπ
  have hsb := Real.sin_nonneg_of_nonneg_of_le_pi hb0 hbπ
  have hsg := Real.sin_nonneg_of_nonneg_of_le_pi hγ0 hγπ
  have ha := Real.sin_sq_add_cos_sq a
  have hb := Real.sin_sq_add_cos_sq b
  have hg := Real.sin_sq_add_cos_sq γ
  have hΔ : 1 - Real.cos a ^ 2 - Real.cos b ^ 2 - Real.cos c ^ 2 + 2 * Real.cos a * Real.cos b * Real.cos c =
      (Real.sin γ * (Real.sin a * Real.sin b)) ^ 2 := by
    rw [hcos]
    linear_combination (-(1 - Real.cos b ^ 2)) * ha + (-(Real.sin a ^ 2)) * hb +
      (-(Real.sin a ^ 2 * Real.sin b ^ 2)) * hg
  rw [hΔ, Real.sqrt_sq (by positivity)]

open InnerProductGeometry in
/-- Linear independence of `![u, v, w]` as a coefficient statement. -/
theorem k92_li3 {u v w : EuclideanSpace ℝ (Fin 3)} (h : LinearIndependent ℝ ![u, v, w]) {a b c : ℝ}
    (habc : a • u + b • v + c • w = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  rw [Fintype.linearIndependent_iff] at h
  have := h ![a, b, c] (by simpa [Fin.sum_univ_three] using habc)
  exact ⟨this 0, this 1, this 2⟩

open InnerProductGeometry in
/-- Two vectors that are not proportional (`x ≠ 0` and `y ∉ ℝx`) make an angle with positive sine. -/
theorem k92_sin_angle_pos {x y : EuclideanSpace ℝ (Fin 3)}
    (h : ∀ a b : ℝ, a • x + b • y = 0 → a = 0 ∧ b = 0) : 0 < Real.sin (angle x y) := by
  rcases (sin_angle_nonneg x y).lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  have h0 := angle_nonneg x y
  have hπ := angle_le_pi x y
  have hcase : angle x y = 0 ∨ angle x y = π := by
    by_cases hp : angle x y = π
    · exact Or.inr hp
    · exact Or.inl ((Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [Real.pi_pos]) (lt_of_le_of_ne hπ hp)).1 heq.symm)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, y = r • x := by
    rcases hcase with hz | hp
    · obtain ⟨-, r, -, hr⟩ := angle_eq_zero_iff.1 hz; exact ⟨r, hr⟩
    · obtain ⟨-, r, -, hr⟩ := angle_eq_pi_iff.1 hp; exact ⟨r, hr⟩
  have := h r (-1) (by rw [hr]; simp)
  linarith [this.2]

open InnerProductGeometry in
/-- For linearly independent `u, v, w`, the spherical angle `sphAngle w u v` has positive sine. -/
theorem k92_sph_sin_pos {u v w : EuclideanSpace ℝ (Fin 3)}
    (H : ∀ a b c : ℝ, a • u + b • v + c • w = 0 → a = 0 ∧ b = 0 ∧ c = 0) :
    0 < Real.sin (sphAngle w u v) := by
  apply k92_sin_angle_pos
  intro a b hab
  have h := H a b (-(a * (inner ℝ u w / ‖w‖ ^ 2) + b * (inner ℝ v w / ‖w‖ ^ 2))) (by
    rw [← hab, smul_sub, smul_sub, smul_smul, smul_smul, neg_smul, add_smul]
    abel)
  exact ⟨h.1, h.2.1⟩

open InnerProductGeometry in
/-- **Spherical Sine Rule** (angles form) for linearly independent points of the sphere of radius `r`. -/
theorem k92_sph_sine {r : ℝ} (hr : 0 < r) {u v w : EuclideanSpace ℝ (Fin 3)} (hu : ‖u‖ = r) (hv : ‖v‖ = r)
    (hw : ‖w‖ = r) (hind : LinearIndependent ℝ ![u, v, w]) :
    Real.sin (InnerProductGeometry.angle v w) / Real.sin (sphAngle u v w) =
        Real.sin (InnerProductGeometry.angle w u) / Real.sin (sphAngle v w u) ∧
      Real.sin (InnerProductGeometry.angle w u) / Real.sin (sphAngle v w u) =
        Real.sin (InnerProductGeometry.angle u v) / Real.sin (sphAngle w u v) := by
  have H := fun a b c (h : a • u + b • v + c • w = 0) => k92_li3 hind h
  have hpa : 0 < Real.sin (angle v w) := k92_sin_angle_pos fun a b h => by
    have := H 0 a b (by rw [← h]; simp); exact ⟨this.2.1, this.2.2⟩
  have hpb : 0 < Real.sin (angle w u) := k92_sin_angle_pos fun a b h => by
    have := H b 0 a (by rw [← h]; simp; abel); exact ⟨this.2.2, this.1⟩
  have hpc : 0 < Real.sin (angle u v) := k92_sin_angle_pos fun a b h => by
    have := H a b 0 (by rw [← h]; simp); exact ⟨this.1, this.2.1⟩
  have sα := k92_sph_sin_mul (angle w u) (angle u v) (angle v w) (sphAngle u v w) (angle_nonneg _ _)
    (angle_le_pi _ _) (angle_nonneg _ _) (angle_le_pi _ _) (angle_nonneg _ _) (angle_le_pi _ _)
    (k92_sph_cos hr hv hw hu)
  have sβ := k92_sph_sin_mul (angle u v) (angle v w) (angle w u) (sphAngle v w u) (angle_nonneg _ _)
    (angle_le_pi _ _) (angle_nonneg _ _) (angle_le_pi _ _) (angle_nonneg _ _) (angle_le_pi _ _)
    (k92_sph_cos hr hw hu hv)
  have sγ := k92_sph_sin_mul (angle v w) (angle w u) (angle u v) (sphAngle w u v) (angle_nonneg _ _)
    (angle_le_pi _ _) (angle_nonneg _ _) (angle_le_pi _ _) (angle_nonneg _ _) (angle_le_pi _ _)
    (k92_sph_cos hr hu hv hw)
  set ca := Real.cos (angle v w)
  set cb := Real.cos (angle w u)
  set cc := Real.cos (angle u v)
  have e1 : 1 - cb ^ 2 - cc ^ 2 - ca ^ 2 + 2 * cb * cc * ca = 1 - ca ^ 2 - cb ^ 2 - cc ^ 2 + 2 * ca * cb * cc := by
    ring
  have e2 : 1 - cc ^ 2 - ca ^ 2 - cb ^ 2 + 2 * cc * ca * cb = 1 - ca ^ 2 - cb ^ 2 - cc ^ 2 + 2 * ca * cb * cc := by
    ring
  rw [e1] at sα
  rw [e2] at sβ
  exact k92_sine_rule_alg hpa hpb hpc sα sβ sγ

open InnerProductGeometry in
/-- **Spherical Cosine Rule II** (angles form) for linearly independent points of the sphere of radius `r`. -/
theorem k92_sph_cos2 {r : ℝ} (hr : 0 < r) {u v w : EuclideanSpace ℝ (Fin 3)} (hu : ‖u‖ = r) (hv : ‖v‖ = r)
    (hw : ‖w‖ = r) (hind : LinearIndependent ℝ ![u, v, w]) :
    Real.cos (InnerProductGeometry.angle u v) =
      (Real.cos (sphAngle u v w) * Real.cos (sphAngle v w u) + Real.cos (sphAngle w u v)) /
        (Real.sin (sphAngle u v w) * Real.sin (sphAngle v w u)) := by
  have H := fun a b c (h : a • u + b • v + c • w = 0) => k92_li3 hind h
  have hpa : 0 < Real.sin (angle v w) := k92_sin_angle_pos fun a b h => by
    have := H 0 a b (by rw [← h]; simp); exact ⟨this.2.1, this.2.2⟩
  have hpb : 0 < Real.sin (angle w u) := k92_sin_angle_pos fun a b h => by
    have := H b 0 a (by rw [← h]; simp; abel); exact ⟨this.2.2, this.1⟩
  have hpc : 0 < Real.sin (angle u v) := k92_sin_angle_pos fun a b h => by
    have := H a b 0 (by rw [← h]; simp); exact ⟨this.1, this.2.1⟩
  have hγpos : 0 < Real.sin (sphAngle w u v) := k92_sph_sin_pos H
  have cα := k92_sph_cos hr hv hw hu
  have cβ := k92_sph_cos hr hw hu hv
  have cγ := k92_sph_cos hr hu hv hw
  have sα := k92_sph_sin_mul (angle w u) (angle u v) (angle v w) (sphAngle u v w) (angle_nonneg _ _)
    (angle_le_pi _ _) (angle_nonneg _ _) (angle_le_pi _ _) (angle_nonneg _ _) (angle_le_pi _ _) cα
  have sβ := k92_sph_sin_mul (angle u v) (angle v w) (angle w u) (sphAngle v w u) (angle_nonneg _ _)
    (angle_le_pi _ _) (angle_nonneg _ _) (angle_le_pi _ _) (angle_nonneg _ _) (angle_le_pi _ _) cβ
  have sγ := k92_sph_sin_mul (angle v w) (angle w u) (angle u v) (sphAngle w u v) (angle_nonneg _ _)
    (angle_le_pi _ _) (angle_nonneg _ _) (angle_le_pi _ _) (angle_nonneg _ _) (angle_le_pi _ _) cγ
  have hsc := Real.sin_sq_add_cos_sq (angle u v)
  set ca := Real.cos (angle v w)
  set cb := Real.cos (angle w u)
  set cc := Real.cos (angle u v)
  set sa := Real.sin (angle v w)
  set sb := Real.sin (angle w u)
  set sc := Real.sin (angle u v)
  have e1 : 1 - cb ^ 2 - cc ^ 2 - ca ^ 2 + 2 * cb * cc * ca = 1 - ca ^ 2 - cb ^ 2 - cc ^ 2 + 2 * ca * cb * cc := by
    ring
  have e2 : 1 - cc ^ 2 - ca ^ 2 - cb ^ 2 + 2 * cc * ca * cb = 1 - ca ^ 2 - cb ^ 2 - cc ^ 2 + 2 * ca * cb * cc := by
    ring
  rw [e1] at sα
  rw [e2] at sβ
  set Δ := 1 - ca ^ 2 - cb ^ 2 - cc ^ 2 + 2 * ca * cb * cc
  have hD : 0 < √Δ := by rw [← sγ]; positivity
  have hΔ : √Δ ^ 2 = Δ := Real.sq_sqrt (Real.sqrt_pos.1 hD).le
  have ecα : Real.cos (sphAngle u v w) = (ca - cb * cc) / (sb * sc) := by
    rw [eq_div_iff (by positivity)]; linarith
  have ecβ : Real.cos (sphAngle v w u) = (cb - cc * ca) / (sc * sa) := by
    rw [eq_div_iff (by positivity)]; linarith
  have ecγ : Real.cos (sphAngle w u v) = (cc - ca * cb) / (sa * sb) := by
    rw [eq_div_iff (by positivity)]; linarith
  have esα : Real.sin (sphAngle u v w) = √Δ / (sb * sc) := by
    rw [eq_div_iff (by positivity)]; exact sα
  have esβ : Real.sin (sphAngle v w u) = √Δ / (sc * sa) := by
    rw [eq_div_iff (by positivity)]; exact sβ
  rw [ecα, ecβ, ecγ, esα, esβ]
  have hΔpos : 0 < Δ := Real.sqrt_pos.1 hD
  have key : (ca - cb * cc) * (cb - cc * ca) + (cc - ca * cb) * sc ^ 2 = cc * Δ := by
    rw [show sc ^ 2 = 1 - cc ^ 2 by linarith]
    simp only [Δ]
    ring
  set D := √Δ
  have hR : ((ca - cb * cc) / (sb * sc) * ((cb - cc * ca) / (sc * sa)) + (cc - ca * cb) / (sa * sb)) /
      (D / (sb * sc) * (D / (sc * sa))) = ((ca - cb * cc) * (cb - cc * ca) + (cc - ca * cb) * sc ^ 2) / D ^ 2 := by
    field_simp
  rw [hR, hΔ, key]
  field_simp

/-- **Formula (1.6.2) (i)** (the spherical Sine Rule; §1.6; l. 545).
`sin(a/r)/sin α = sin(b/r)/sin β = sin(c/r)/sin γ` for a spherical triangle in `S_r`. -/
theorem eq1_6_2_i {r : ℝ} (hr : 0 < r) {u v w : EuclideanSpace ℝ (Fin 3)} (hu : ‖u‖ = r) (hv : ‖v‖ = r)
    (hw : ‖w‖ = r) (hind : LinearIndependent ℝ ![u, v, w]) :
    Real.sin (r * InnerProductGeometry.angle v w / r) / Real.sin (sphAngle u v w) =
        Real.sin (r * InnerProductGeometry.angle w u / r) / Real.sin (sphAngle v w u) ∧
      Real.sin (r * InnerProductGeometry.angle w u / r) / Real.sin (sphAngle v w u) =
        Real.sin (r * InnerProductGeometry.angle u v / r) / Real.sin (sphAngle w u v) := by
  simp only [mul_div_cancel_left₀ _ hr.ne']
  exact k92_sph_sine hr hu hv hw hind

/-- **Formula (1.6.2) (ii)** (the spherical Cosine Rule I; §1.6; l. 547).
`cos(c/r) = cos(a/r) cos(b/r) + sin(a/r) sin(b/r) cos γ`. -/
theorem eq1_6_2_ii {r : ℝ} (hr : 0 < r) {u v w : EuclideanSpace ℝ (Fin 3)} (hu : ‖u‖ = r) (hv : ‖v‖ = r)
    (hw : ‖w‖ = r) (hind : LinearIndependent ℝ ![u, v, w]) :
    Real.cos (r * InnerProductGeometry.angle u v / r) =
      Real.cos (r * InnerProductGeometry.angle v w / r) * Real.cos (r * InnerProductGeometry.angle w u / r) +
        Real.sin (r * InnerProductGeometry.angle v w / r) * Real.sin (r * InnerProductGeometry.angle w u / r) *
          Real.cos (sphAngle w u v) := by
  -- The independence hypothesis `hind` is not needed: the rule holds for any three points of the sphere.
  have _ := hind
  simp only [mul_div_cancel_left₀ _ hr.ne']
  exact k92_sph_cos hr hu hv hw

/-- **Formula (1.6.2) (iii)** (the spherical Cosine Rule II; §1.6; l. 551).
`cos(c/r) = (cos α cos β + cos γ)/(sin α sin β)`. -/
theorem eq1_6_2_iii {r : ℝ} (hr : 0 < r) {u v w : EuclideanSpace ℝ (Fin 3)} (hu : ‖u‖ = r) (hv : ‖v‖ = r)
    (hw : ‖w‖ = r) (hind : LinearIndependent ℝ ![u, v, w]) :
    Real.cos (r * InnerProductGeometry.angle u v / r) =
      (Real.cos (sphAngle u v w) * Real.cos (sphAngle v w u) + Real.cos (sphAngle w u v)) /
        (Real.sin (sphAngle u v w) * Real.sin (sphAngle v w u)) := by
  simp only [mul_div_cancel_left₀ _ hr.ne']
  exact k92_sph_cos2 hr hu hv hw hind

/-- **Formula (1.6.3) (i)** (the Sine Rule in ℍ_r; §1.6; l. 561).
`sinh(a/r)/sin α = sinh(b/r)/sin β = sinh(c/r)/sin γ`. -/
theorem eq1_6_3_i {r : ℝ} (hr : 0 < r) {A B C : ℍ} (h : IsNondegenerateTriangle A B C) :
    Real.sinh (distR r B C / r) / Real.sin (hypAngle A (toExtH B) (toExtH C)) =
        Real.sinh (distR r C A / r) / Real.sin (hypAngle B (toExtH C) (toExtH A)) ∧
      Real.sinh (distR r C A / r) / Real.sin (hypAngle B (toExtH C) (toExtH A)) =
        Real.sinh (distR r A B / r) / Real.sin (hypAngle C (toExtH A) (toExtH B)) := by
  simp only [distR, mul_div_cancel_left₀ _ hr.ne']
  exact thm1_5_2_i h

/-- **Formula (1.6.3) (ii)** (the Cosine Rule I in ℍ_r; §1.6; l. 563).
`cosh(c/r) = cosh(a/r) cosh(b/r) − sinh(a/r) sinh(b/r) cos γ`. -/
theorem eq1_6_3_ii {r : ℝ} (hr : 0 < r) {A B C : ℍ} (h : IsNondegenerateTriangle A B C) :
    Real.cosh (distR r A B / r) = Real.cosh (distR r B C / r) * Real.cosh (distR r C A / r) -
      Real.sinh (distR r B C / r) * Real.sinh (distR r C A / r) *
        Real.cos (hypAngle C (toExtH A) (toExtH B)) := by
  simp only [distR, mul_div_cancel_left₀ _ hr.ne']
  exact thm1_5_2_ii h

/-- **Formula (1.6.3) (iii)** (the Cosine Rule II in ℍ_r; §1.6; l. 567, [OCR] reading in the module docstring).
`cosh(c/r) = (cos α cos β + cos γ)/(sin α sin β)`. -/
theorem eq1_6_3_iii {r : ℝ} (hr : 0 < r) {A B C : ℍ} (h : IsNondegenerateTriangle A B C) :
    Real.cosh (distR r A B / r) =
      (Real.cos (hypAngle A (toExtH B) (toExtH C)) * Real.cos (hypAngle B (toExtH C) (toExtH A)) +
          Real.cos (hypAngle C (toExtH A) (toExtH B))) /
        (Real.sin (hypAngle A (toExtH B) (toExtH C)) * Real.sin (hypAngle B (toExtH C) (toExtH A))) := by
  simp only [distR, mul_div_cancel_left₀ _ hr.ne']
  exact thm1_5_2_iii h

end Katok1992
