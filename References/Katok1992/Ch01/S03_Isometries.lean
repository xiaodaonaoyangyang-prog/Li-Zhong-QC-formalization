import References.Katok1992.Ch01.S02_Geodesics

/-!
# Katok 1992, Ch. 1 §1.3 Isometries

S. Katok, *Fuchsian Groups* (1992), Chapter 1 *Hyperbolic Geometry*, §1.3; source `full.md` of
`Fuchsian groups (Katok, Svetlana) …-3766f6b7…`, lines 278–337.

* Definition (S*L(2,ℝ) and PS*L(2,ℝ) = S*L(2,ℝ)/{±1}, l. 280; PS*L(2,ℤ) at l. 771) — `SStarL`, `PSStarL`
* Helper (the transformations of PSL(2,ℝ) as a subgroup of Isom(ℍ)) — `isomPSL`
* Theorem 1.3.1 (l. 284; cited at l. 707, hint l. 3327) — `thm1_3_1_i`, `thm1_3_1_ii`, `thm1_3_1_iii`
* Formula (1.3.2) (the orientation-reversing isometries z ↦ (a z̄ + b)/(c z̄ + d), ad − bc = −1, l. 309) — exists:
  `UpperHalfPlane.glAction` `UpperHalfPlane.coe_smul` `UpperHalfPlane.coe_J_smul` (Mathlib's GL(2,ℝ) action conjugates
  for negative determinant; J is z ↦ −z̄)
* Definition (orientation-preserving and orientation-reversing isometries, l. 312; cited at l. 715, 717, 2073) —
  `IsOrientationPreserving`, `IsOrientationReversing`
* Formula (1.3.3) (the inner product on the tangent space and its norm, l. 314–318; cited at l. 673) —
  `tangentInner`, `tangentNorm`
* Definition (the angle between two geodesics at a point, l. 326; cited at l. 385, 1687, 1820–1864) — `tangentDir`,
  `hypAngle`
* Definition (conformal and anti-conformal transformations, l. 328) — `IsConformalH`, `IsAntiConformalH`
* Theorem 1.3.2 (l. 330; cited at l. 385) — `thm1_3_2_i`, `thm1_3_2_ii`
* Theorem 1.3.3 (l. 336; cited at l. 829) — `thm1_3_3`

Not items (DESIGN §3): "PSL(2,ℝ) has index 2 in PS*L(2,ℝ)" (l. 280; immediate); (1.3.1) (a proof step); the action of
isometries on the tangent bundle, the polarization identity and the preservation of angles (l. 320–326; Exercise
1.2); "Euclidean discs = hyperbolic discs" (l. 334; Exercise 1.11); the exercises.

**Conventions.** Isom(ℍ) is `ℍ ≃ᵢ ℍ`. Angles are Euclidean angles (`InnerProductGeometry.angle`, in `[0, π]`) of the
initial tangent vectors, as the book states via Exercise 1.3; the tangent at `z` of the geodesic towards
`p ∈ ℍ̃ ∖ {z}` is `i (p − z)/(p − z̄)` (`i` for `p = ∞`), since `ξ ↦ (ξ − z)/(ξ − z̄)` sends `z` to `0`, geodesics
through `z` to diameters, and has derivative `1/(2i Im z)` at `z`. Conformality is oriented (a nonzero complex
derivative), unlike Mathlib's `ConformalAt`, which also admits orientation-reversing maps.
-/

open Complex Set Metric Filter Topology
open scoped UpperHalfPlane MatrixGroups ComplexConjugate

noncomputable section

namespace Katok1992

open LiZhongQC (ExtPlane)

/-- **Definition** (§1.3; l. 280). `S*L(2, R)`: the `2 × 2` matrices over `R` with `det = ±1`.
Modelling: the preimage of `{±1} = zpowers (−1)` under `det : GL(2, R) → Rˣ`; over a commutative ring `R`, since the
book also uses `R = ℤ` (l. 771). -/
def SStarL (R : Type*) [CommRing R] : Subgroup (GL (Fin 2) R) :=
  (Subgroup.zpowers (-1 : Rˣ)).comap Matrix.GeneralLinearGroup.det

/-- **Definition** (§1.3; l. 280). `PS*L(2, R) = S*L(2, R)/{±1₂}`.
Modelling: the quotient by the center of `S*L(2, R)`, which is `{±1₂}` for the book's rings `ℝ` and `ℤ`. -/
abbrev PSStarL (R : Type*) [CommRing R] : Type _ :=
  SStarL R ⧸ Subgroup.center (SStarL R)

/-- Helper (§1.3). The transformations of `PSL(2,ℝ)` in `Isom(ℍ)`: the subgroup they generate (by Theorem 1.3.1
(iii) it consists of them). -/
def isomPSL : Subgroup (ℍ ≃ᵢ ℍ) :=
  Subgroup.closure {φ | ∃ T : PSL(2, ℝ), ∀ z, φ z = T • z}

/-- Auxiliary (§1.3). A group acting on ℍ by isometries maps homomorphically into `Isom(ℍ)`. -/
theorem k92i_hom {G : Type*} [Group G] [MulAction G ℍ] (h : ∀ g : G, Isometry fun z : ℍ => g • z) :
    ∃ Φ : G →* (ℍ ≃ᵢ ℍ), ∀ g z, Φ g z = g • z := by
  refine ⟨{ toFun := fun g => { toEquiv := MulAction.toPerm g, isometry_toFun := h g }
            map_one' := ?_, map_mul' := ?_ }, fun g z => rfl⟩
  · exact IsometryEquiv.ext fun z => one_smul G z
  · intro a b
    exact IsometryEquiv.ext fun z => mul_smul a b z

/-- Auxiliary (§1.3). `J : z ↦ −z̄` is an isometry of ℍ. -/
theorem k92i_isometry_J : Isometry fun z : ℍ => UpperHalfPlane.J • z := by
  have him : ∀ z : ℍ, (UpperHalfPlane.J • z).im = z.im := fun z => by
    rw [← UpperHalfPlane.coe_im, UpperHalfPlane.coe_J_smul]
    simp
  refine Isometry.of_dist_eq fun z w => ?_
  rw [UpperHalfPlane.dist_eq, UpperHalfPlane.dist_eq, him, him, UpperHalfPlane.coe_J_smul,
    UpperHalfPlane.coe_J_smul, dist_neg_neg, Complex.dist_conj_conj]

/-- Auxiliary (§1.3). The real part of `J • X = −X̄`. -/
theorem k92i_J_re (X : ℍ) : (UpperHalfPlane.J • X).re = -X.re := by
  rw [← UpperHalfPlane.coe_re, UpperHalfPlane.coe_J_smul]
  simp

/-- Auxiliary (§1.3). The imaginary part of `J • X = −X̄`. -/
theorem k92i_J_im (X : ℍ) : (UpperHalfPlane.J • X).im = X.im := by
  rw [← UpperHalfPlane.coe_im, UpperHalfPlane.coe_J_smul]
  simp

/-- Auxiliary (§1.3). `J` is an involution of ℍ. -/
theorem k92i_JJ (z : ℍ) : UpperHalfPlane.J • UpperHalfPlane.J • z = z := by
  rw [← mul_smul, ← sq, UpperHalfPlane.J_sq, one_smul]

/-- Auxiliary (§1.3). An element of `S*L(2,ℝ)` has determinant `1` or `−1`. -/
theorem k92i_det (g : SStarL ℝ) :
    (g : GL (Fin 2) ℝ).det.val = 1 ∨ (g : GL (Fin 2) ℝ).det.val = -1 := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_comap.1 g.2)
  rcases Int.even_or_odd k with h | h
  · left
    rw [← hk, h.neg_one_zpow]
    rfl
  · right
    rw [← hk, h.neg_one_zpow]
    rfl

/-- Auxiliary (§1.3). A real matrix of determinant `±1` lies in `S*L(2,ℝ)`. -/
theorem k92i_mem (G : GL (Fin 2) ℝ) (h : G.det.val = 1 ∨ G.det.val = -1) : G ∈ SStarL ℝ := by
  rcases h with h | h
  · refine Subgroup.mem_comap.2 (Subgroup.mem_zpowers_iff.2 ⟨0, ?_⟩)
    ext
    simp [h]
  · refine Subgroup.mem_comap.2 (Subgroup.mem_zpowers_iff.2 ⟨1, ?_⟩)
    ext
    simp [h]

/-- Auxiliary (§1.3). A matrix of determinant `1` acts on ℍ as an element of `SL(2,ℝ)`, hence isometrically. -/
theorem k92i_isometry_of_det_one {G : GL (Fin 2) ℝ} (hG : G.det.val = 1) : Isometry fun z : ℍ => G • z := by
  have hdet : G.val.det = 1 := by rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact hG
  set s : SL(2, ℝ) := ⟨G.val, hdet⟩
  have hs : ∀ z : ℍ, G • z = s • z := fun z => by
    rw [MulAction.compHom_smul_def]
    congr 1
    ext i j
    rfl
  have : (fun z : ℍ => G • z) = fun z : ℍ => s • z := funext hs
  rw [this]
  exact isometry_smul ℍ s

/-- Auxiliary (§1.3). Every element of `S*L(2,ℝ)` acts on ℍ isometrically (determinant `−1`: through `J`). -/
theorem k92i_isometry_smul (g : SStarL ℝ) : Isometry fun z : ℍ => (g : GL (Fin 2) ℝ) • z := by
  rcases k92i_det g with h | h
  · exact k92i_isometry_of_det_one h
  · have h2 : (UpperHalfPlane.J * (g : GL (Fin 2) ℝ)).det.val = 1 := by
      rw [map_mul, Units.val_mul, h, UpperHalfPlane.det_J]
      norm_num
    have e : (fun z : ℍ => (g : GL (Fin 2) ℝ) • z) =
        fun z => UpperHalfPlane.J • ((UpperHalfPlane.J * (g : GL (Fin 2) ℝ)) • z) := funext fun z => by
      rw [← mul_smul, ← mul_assoc, ← sq, UpperHalfPlane.J_sq, one_mul]
    rw [e]
    exact k92i_isometry_J.comp (k92i_isometry_of_det_one h2)

/-- Auxiliary (§1.3). Points of ℍ are equal when their real and imaginary parts are. -/
theorem k92i_eq_iff {X Y : ℍ} : X = Y ↔ X.re = Y.re ∧ X.im = Y.im := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    exact UpperHalfPlane.ext (Complex.ext h1 h2)

/-- Auxiliary (§1.3). Equal distances from `P` (Theorem 1.2.6 (iii), via `cosh_dist`):
`|P − X|² Im X' = |P − X'|² Im X`. -/
theorem k92i_cosh_eq {P X X' : ℍ} (h : dist P X = dist P X') :
    (((P : ℂ).re - X.re) ^ 2 + (P.im - X.im) ^ 2) * X'.im =
      (((P : ℂ).re - X'.re) ^ 2 + (P.im - X'.im) ^ 2) * X.im := by
  have hc := congrArg Real.cosh h
  rw [UpperHalfPlane.cosh_dist, UpperHalfPlane.cosh_dist] at hc
  have e : ∀ Q : ℍ, dist (P : ℂ) Q ^ 2 = ((P : ℂ).re - Q.re) ^ 2 + (P.im - Q.im) ^ 2 := fun Q => by
    rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  rw [e, e] at hc
  have hc2 := add_left_cancel hc
  have hP := P.im_pos
  have hX := X.im_pos
  have hX' := X'.im_pos
  rw [div_eq_div_iff (by positivity) (by positivity)] at hc2
  have h2p : 2 * P.im ≠ 0 := by positivity
  apply mul_left_cancel₀ h2p
  linear_combination hc2

/-- Auxiliary (§1.3). The book's computation: equal distances to two points `A ≠ B` of the imaginary axis force
`X' = X` or `X' = −X̄` (1.3.1). -/
theorem k92i_two {A B X X' : ℍ} (hA : A.re = 0) (hB : B.re = 0) (hAB : A.im ≠ B.im)
    (h1 : dist A X = dist A X') (h2 : dist B X = dist B X') : X' = X ∨ X' = UpperHalfPlane.J • X := by
  have EA := k92i_cosh_eq h1
  have EB := k92i_cosh_eq h2
  rw [UpperHalfPlane.coe_re] at EA EB
  rw [hA] at EA
  rw [hB] at EB
  have hab2 : A.im ^ 2 - B.im ^ 2 ≠ 0 := by
    have e : A.im ^ 2 - B.im ^ 2 = (A.im - B.im) * (A.im + B.im) := by ring
    rw [e]
    exact mul_ne_zero (sub_ne_zero.2 hAB) (by have := A.im_pos; have := B.im_pos; positivity)
  have him : X'.im = X.im := by
    have e : (A.im ^ 2 - B.im ^ 2) * (X'.im - X.im) = 0 := by linear_combination EA - EB
    rcases mul_eq_zero.1 e with e | e
    · exact absurd e hab2
    · linarith
  have hre : (X'.re - X.re) * (X'.re + X.re) = 0 := by
    rw [him] at EA
    have h0 : ((X'.re - X.re) * (X'.re + X.re)) * X.im = 0 := by linear_combination -EA
    rcases mul_eq_zero.1 h0 with e | e
    · exact e
    · exact absurd e X.im_pos.ne'
  rcases mul_eq_zero.1 hre with e | e
  · left
    exact k92i_eq_iff.2 ⟨by linarith, him⟩
  · right
    exact k92i_eq_iff.2 ⟨by rw [k92i_J_re]; linarith, by rw [k92i_J_im]; exact him⟩

/-- Auxiliary (§1.3). Equal distances to two points `A ≠ B` of the imaginary axis and to `1 + i` force `X' = X`
(this replaces the book's continuity argument after (1.3.1)). -/
theorem k92i_three {A B X X' : ℍ} (hA : A.re = 0) (hB : B.re = 0) (hAB : A.im ≠ B.im)
    (h1 : dist A X = dist A X') (h2 : dist B X = dist B X')
    (h3 : dist (UpperHalfPlane.mk ⟨1, 1⟩ one_pos) X = dist (UpperHalfPlane.mk ⟨1, 1⟩ one_pos) X') : X' = X := by
  rcases k92i_two hA hB hAB h1 h2 with h | h
  · exact h
  · have E := k92i_cosh_eq h3
    have hC1 : ((UpperHalfPlane.mk ⟨1, 1⟩ one_pos : ℍ) : ℂ).re = 1 := rfl
    have hC2 : (UpperHalfPlane.mk ⟨1, 1⟩ one_pos : ℍ).im = 1 := rfl
    rw [h, k92i_J_re, k92i_J_im, hC1, hC2] at E
    have hx : X.re = 0 := by
      have h0 : (4 * X.re) * X.im = 0 := by linear_combination -E
      rcases mul_eq_zero.1 h0 with e | e
      · linarith
      · exact absurd e X.im_pos.ne'
    rw [h]
    exact k92i_eq_iff.2 ⟨by rw [k92i_J_re, hx]; ring, k92i_J_im X⟩

/-- Auxiliary (§1.3). An isometry fixing the imaginary axis pointwise is the identity or `J`. -/
theorem k92i_rigid_axis {ψ : ℍ → ℍ} (hψ : Isometry ψ)
    (hV : ∀ t : ℝ, ψ (UpperHalfPlane.mk ⟨0, Real.exp t⟩ (Real.exp_pos t)) =
      UpperHalfPlane.mk ⟨0, Real.exp t⟩ (Real.exp_pos t)) :
    (∀ z, ψ z = z) ∨ ∀ z, ψ z = UpperHalfPlane.J • z := by
  set A := UpperHalfPlane.mk ⟨0, Real.exp 0⟩ (Real.exp_pos 0)
  set B := UpperHalfPlane.mk ⟨0, Real.exp 1⟩ (Real.exp_pos 1)
  set C := UpperHalfPlane.mk ⟨1, 1⟩ one_pos
  have hA : A.re = 0 := rfl
  have hB : B.re = 0 := rfl
  have hAB : A.im ≠ B.im := fun h => by
    have : Real.exp 0 = Real.exp 1 := h
    exact absurd (Real.exp_injective this) (by norm_num)
  -- distances to a fixed point are preserved
  have hd : ∀ {χ : ℍ → ℍ}, Isometry χ → ∀ P, χ P = P → ∀ z, dist P z = dist P (χ z) :=
    fun hχ P hP z => by rw [← hχ.dist_eq P z, hP]
  have hJA : ∀ P : ℍ, P.re = 0 → UpperHalfPlane.J • P = P := fun P hP =>
    k92i_eq_iff.2 ⟨by rw [k92i_J_re, hP, neg_zero], k92i_J_im P⟩
  have fix3 : ∀ {χ : ℍ → ℍ}, Isometry χ → χ A = A → χ B = B → χ C = C → ∀ z, χ z = z :=
    fun hχ h1 h2 h3 z => k92i_three hA hB hAB (hd hχ A h1 z) (hd hχ B h2 z) (hd hχ C h3 z)
  rcases k92i_two hA hB hAB (hd hψ A (hV 0) C) (hd hψ B (hV 1) C) with hC | hC
  · exact Or.inl (fix3 hψ (hV 0) (hV 1) hC)
  · right
    have hχ : Isometry fun z => UpperHalfPlane.J • ψ z := k92i_isometry_J.comp hψ
    have key := fix3 hχ (by rw [hV 0, hJA A hA]) (by rw [hV 1, hJA B hB]) (by rw [hC, k92i_JJ])
    intro z
    have := congrArg (UpperHalfPlane.J • ·) (key z)
    simp only [k92i_JJ] at this
    exact this

/-- Auxiliary (§1.3). Classification of the isometries of ℍ: each is `z ↦ g • z` or `z ↦ g • (−z̄)` with
`g ∈ SL(2,ℝ)`. The isometric curve `t ↦ φ(i eᵗ)` is normalized onto the imaginary axis (`k92g_normal_form`). -/
theorem k92i_classify (φ : ℍ ≃ᵢ ℍ) :
    ∃ g : SL(2, ℝ), (∀ z, φ z = g • z) ∨ ∀ z, φ z = g • UpperHalfPlane.J • z := by
  have hγ : Isometry fun t : ℝ => φ (UpperHalfPlane.mk ⟨0, Real.exp t⟩ (Real.exp_pos t)) :=
    φ.isometry.comp (UpperHalfPlane.isometry_vertical_line 0)
  obtain ⟨-, -, -, -, -, g, -, c, hc⟩ := k92g_normal_form hγ
  obtain ⟨s, hs⟩ := k92g_sl_of_det_pos (a := 1) (b := 0) (c := 0) (d := Real.exp c)
    (by rw [one_mul, zero_mul, sub_zero]; exact Real.exp_pos c)
  have hV : ∀ t : ℝ, (s * g) • φ (UpperHalfPlane.mk ⟨0, Real.exp t⟩ (Real.exp_pos t)) =
      UpperHalfPlane.mk ⟨0, Real.exp t⟩ (Real.exp_pos t) := fun t => by
    rw [mul_smul, hc t]
    apply UpperHalfPlane.ext
    rw [hs, UpperHalfPlane.coe_mk, UpperHalfPlane.coe_mk, Complex.ofReal_one, Complex.ofReal_zero, one_mul,
      add_zero, zero_mul, zero_add, div_eq_iff (Complex.ofReal_ne_zero.2 (Real.exp_pos c).ne')]
    apply Complex.ext
    · simp
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, Real.exp_add]
      ring
  have hψ : Isometry fun z => (s * g) • φ z := (isometry_smul ℍ (s * g)).comp φ.isometry
  refine ⟨(s * g)⁻¹, ?_⟩
  rcases k92i_rigid_axis hψ hV with h | h
  · exact Or.inl fun z => eq_inv_smul_iff.2 (h z)
  · exact Or.inr fun z => eq_inv_smul_iff.2 (h z)

/-- Auxiliary (§1.3). A matrix acting trivially on ℍ is a positive-determinant scalar matrix. -/
theorem k92i_fix_scalar {G : GL (Fin 2) ℝ} (h : ∀ z : ℍ, G • z = z) :
    0 < G.det.val ∧ G 1 0 = 0 ∧ G 0 1 = 0 ∧ G 0 0 = G 1 1 := by
  by_cases hpos : 0 < G.det.val
  · have E : ∀ (x y : ℝ) (hy : 0 < y), G 0 0 * x + G 0 1 = G 1 0 * x ^ 2 + G 1 1 * x - G 1 0 * y ^ 2 ∧
        G 0 0 * y = 2 * G 1 0 * x * y + G 1 1 * y := fun x y hy => by
      set z : ℍ := UpperHalfPlane.mk ⟨x, y⟩ hy
      have hz : ((G • z : ℍ) : ℂ) = (z : ℂ) := by rw [h z]
      rw [UpperHalfPlane.coe_smul_of_det_pos hpos, div_eq_iff (UpperHalfPlane.denom_ne_zero G _)] at hz
      have h1 := congrArg Complex.re hz
      have h2 := congrArg Complex.im hz
      have hzc : (z : ℂ) = ⟨x, y⟩ := rfl
      simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hzc, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at h1 h2
      constructor
      · linear_combination h1
      · linear_combination h2
    obtain ⟨e1, e2⟩ := E 0 1 one_pos
    obtain ⟨e3, -⟩ := E 0 2 two_pos
    refine ⟨hpos, ?_, ?_, ?_⟩
    · linear_combination (e3 - e1) / 3
    · linear_combination (4 * e1 - e3) / 3
    · linear_combination e2
  · exfalso
    have E : ∀ (x y : ℝ) (hy : 0 < y), G 0 0 * x + G 0 1 = G 1 0 * x ^ 2 + G 1 1 * x + G 1 0 * y ^ 2 ∧
        G 0 0 * y = - (G 1 1 * y) := fun x y hy => by
      set z : ℍ := UpperHalfPlane.mk ⟨x, y⟩ hy
      have hz : ((G • z : ℍ) : ℂ) = (z : ℂ) := by rw [h z]
      rw [UpperHalfPlane.coe_smul] at hz
      simp only [UpperHalfPlane.σ, hpos, ↓reduceIte, Complex.conjCAE_apply] at hz
      have hq := congrArg (starRingEnd ℂ) hz
      rw [Complex.conj_conj, div_eq_iff (UpperHalfPlane.denom_ne_zero G _)] at hq
      have h1 := congrArg Complex.re hq
      have h2 := congrArg Complex.im hq
      have hzc : (z : ℂ) = ⟨x, y⟩ := rfl
      simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hzc, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
        Complex.conj_im] at h1 h2
      constructor
      · linear_combination h1
      · linear_combination h2
    obtain ⟨e1, -⟩ := E 0 1 one_pos
    obtain ⟨e3, -⟩ := E 0 2 two_pos
    obtain ⟨e5, e6⟩ := E 1 1 one_pos
    have hc : G 1 0 = 0 := by linear_combination (e1 - e3) / 3
    have hb : G 0 1 = 0 := by linear_combination (4 * e1 - e3) / 3
    have ha : G 0 0 = 0 := by linear_combination (e5 + e6 - hb + 2 * hc) / 2
    have hd0 : G.det.val = 0 := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
      change G 0 0 * G 1 1 - G 0 1 * G 1 0 = 0
      rw [ha, hb]
      ring
    exact G.det.ne_zero hd0

/-- Auxiliary (§1.3). No transformation of `PSL(2,ℝ)` acts as an orientation-reversing `z ↦ g • (−z̄)`. -/
theorem k92i_not_psl_J (g : SL(2, ℝ)) (T : PSL(2, ℝ)) : ¬ ∀ z : ℍ, T • z = g • UpperHalfPlane.J • z := by
  intro hT
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective T
  set G : GL (Fin 2) ℝ := UpperHalfPlane.J * (Matrix.SpecialLinearGroup.mapGL ℝ g)⁻¹ *
    Matrix.SpecialLinearGroup.mapGL ℝ h
  have hfix : ∀ z : ℍ, G • z = z := fun z => by
    have e := hT z
    rw [k92_psl_smul_mk] at e
    rw [mul_smul, mul_smul]
    change UpperHalfPlane.J • (Matrix.SpecialLinearGroup.mapGL ℝ g)⁻¹ • (h • z) = z
    rw [e]
    change UpperHalfPlane.J • (Matrix.SpecialLinearGroup.mapGL ℝ g)⁻¹ •
      (Matrix.SpecialLinearGroup.mapGL ℝ g) • UpperHalfPlane.J • z = z
    rw [inv_smul_smul, k92i_JJ]
  have hdet : G.det.val = -1 := by simp [G]
  have := (k92i_fix_scalar hfix).1
  rw [hdet] at this
  norm_num at this

/-- Auxiliary (§1.3). The center of `S*L(2,ℝ)` is the kernel of its action on ℍ. -/
theorem k92i_center (g : SStarL ℝ) :
    g ∈ Subgroup.center (SStarL ℝ) ↔ ∀ z : ℍ, (g : GL (Fin 2) ℝ) • z = z := by
  constructor
  · intro hg z
    have hcomm := Subgroup.mem_center_iff.1 hg
    set U : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 1; 0, 1] (by simp)
    set L : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 1, 1] (by simp)
    have hU := hcomm ⟨U, k92i_mem U (Or.inl (by simp [U]))⟩
    have hL := hcomm ⟨L, k92i_mem L (Or.inl (by simp [L]))⟩
    have eU : ∀ i j, (U * (g : GL (Fin 2) ℝ)) i j = ((g : GL (Fin 2) ℝ) * U) i j := fun i j =>
      congrArg (fun x : SStarL ℝ => (x : GL (Fin 2) ℝ) i j) hU
    have eL : ∀ i j, (L * (g : GL (Fin 2) ℝ)) i j = ((g : GL (Fin 2) ℝ) * L) i j := fun i j =>
      congrArg (fun x : SStarL ℝ => (x : GL (Fin 2) ℝ) i j) hL
    have e1 := eU 0 0
    have e2 := eU 0 1
    have e3 := eL 0 0
    simp [U, L, Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
    have had : (g : GL (Fin 2) ℝ) 1 1 = (g : GL (Fin 2) ℝ) 0 0 := by linarith
    have hdet : (g : GL (Fin 2) ℝ).det.val = (g : GL (Fin 2) ℝ) 0 0 ^ 2 := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, e1, e3, had]
      ring
    have hpos : 0 < (g : GL (Fin 2) ℝ).det.val := by
      rw [hdet]
      exact lt_of_le_of_ne (sq_nonneg _) fun h0 => (g : GL (Fin 2) ℝ).det.ne_zero (hdet.trans h0.symm)
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hpos, div_eq_iff (UpperHalfPlane.denom_ne_zero _ _)]
    simp only [UpperHalfPlane.num, UpperHalfPlane.denom, e1, e3, had]
    push_cast
    ring
  · intro h
    obtain ⟨-, hc, hb, had⟩ := k92i_fix_scalar h
    refine Subgroup.mem_center_iff.2 fun k => ?_
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc, hb, had] <;> ring

/-- Auxiliary (§1.3). `J : z ↦ −z̄` as an element of `Isom(ℍ)`. -/
theorem k92i_Jiso : ∃ Jφ : ℍ ≃ᵢ ℍ, ∀ z, Jφ z = UpperHalfPlane.J • z :=
  ⟨{ toEquiv := MulAction.toPerm UpperHalfPlane.J, isometry_toFun := k92i_isometry_J }, fun _ => rfl⟩

/-- **Theorem 1.3.1** (§1.3; l. 284), first claim. `Isom(ℍ)` is generated by the transformations (1.1.2) in
`PSL(2,ℝ)` together with `z ↦ −z̄`. -/
theorem thm1_3_1_i :
    Subgroup.closure ({φ : ℍ ≃ᵢ ℍ | ∃ T : PSL(2, ℝ), ∀ z, φ z = T • z} ∪
      {φ | ∀ z, (φ z : ℂ) = -conj (z : ℂ)}) = ⊤ := by
  obtain ⟨Ψ, hΨ⟩ := k92i_hom k92_isometry_psl_smul
  obtain ⟨Jφ, hJφ⟩ := k92i_Jiso
  have hPSL : ∀ g : SL(2, ℝ), Ψ (g : PSL(2, ℝ)) ∈ {φ : ℍ ≃ᵢ ℍ | ∃ T : PSL(2, ℝ), ∀ z, φ z = T • z} ∪
      {φ | ∀ z, (φ z : ℂ) = -conj (z : ℂ)} := fun g => Or.inl ⟨g, hΨ g⟩
  have hJ : Jφ ∈ {φ : ℍ ≃ᵢ ℍ | ∃ T : PSL(2, ℝ), ∀ z, φ z = T • z} ∪
      {φ | ∀ z, (φ z : ℂ) = -conj (z : ℂ)} := Or.inr fun z => by rw [hJφ, UpperHalfPlane.coe_J_smul]
  refine eq_top_iff.2 fun φ _ => ?_
  obtain ⟨g, hg | hg⟩ := k92i_classify φ
  · have e : φ = Ψ (g : PSL(2, ℝ)) := IsometryEquiv.ext fun z => by rw [hg, hΨ, k92_psl_smul_mk]
    rw [e]
    exact Subgroup.subset_closure (hPSL g)
  · have e : φ = Ψ (g : PSL(2, ℝ)) * Jφ := IsometryEquiv.ext fun z => by
      rw [hg, IsometryEquiv.mul_apply, hJφ, hΨ, k92_psl_smul_mk]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (hPSL g)) (Subgroup.subset_closure hJ)

/-- **Theorem 1.3.1** (§1.3; l. 284), second claim. `Isom(ℍ)` is isomorphic to `PS*L(2,ℝ)`.
Modelling: the natural isomorphism, `±g ↦ (z ↦ g • z)` (a matrix of determinant `−1` acts by (1.3.2)). -/
theorem thm1_3_1_ii :
    ∃ e : PSStarL ℝ ≃* (ℍ ≃ᵢ ℍ), ∀ (g : SStarL ℝ) (z : ℍ),
      e (QuotientGroup.mk g : PSStarL ℝ) z = (g : GL (Fin 2) ℝ) • z := by
  obtain ⟨Φ, hΦ⟩ := k92i_hom (G := SStarL ℝ) fun g => k92i_isometry_smul g
  have hker : Subgroup.center (SStarL ℝ) = Φ.ker := by
    ext g
    rw [k92i_center, MonoidHom.mem_ker]
    constructor
    · intro h
      exact IsometryEquiv.ext fun z => (hΦ g z).trans (h z)
    · intro h z
      have e := hΦ g z
      rw [h] at e
      exact e.symm
  have hsurj : Function.Surjective Φ := by
    intro φ
    obtain ⟨g, hg | hg⟩ := k92i_classify φ
    · refine ⟨⟨Matrix.SpecialLinearGroup.mapGL ℝ g, k92i_mem _ (Or.inl (by simp))⟩,
        IsometryEquiv.ext fun z => ?_⟩
      rw [hΦ, hg]
      rfl
    · refine ⟨⟨Matrix.SpecialLinearGroup.mapGL ℝ g * UpperHalfPlane.J, k92i_mem _ (Or.inr (by simp))⟩,
        IsometryEquiv.ext fun z => ?_⟩
      rw [hΦ, hg]
      show (Matrix.SpecialLinearGroup.mapGL ℝ g * UpperHalfPlane.J) • z = _
      rw [mul_smul]
      rfl
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivOfSurjective Φ hsurj),
    fun g z => hΦ g z⟩

/-- **Theorem 1.3.1** (§1.3; l. 284), third claim. `PSL(2,ℝ)` is a subgroup of `Isom(ℍ)` of index 2. -/
theorem thm1_3_1_iii :
    (isomPSL : Set (ℍ ≃ᵢ ℍ)) = {φ | ∃ T : PSL(2, ℝ), ∀ z, φ z = T • z} ∧ isomPSL.index = 2 := by
  obtain ⟨Ψ, hΨ⟩ := k92i_hom k92_isometry_psl_smul
  obtain ⟨Jφ, hJφ⟩ := k92i_Jiso
  have hS : {φ : ℍ ≃ᵢ ℍ | ∃ T : PSL(2, ℝ), ∀ z, φ z = T • z} = (Ψ.range : Set (ℍ ≃ᵢ ℍ)) := by
    ext φ
    constructor
    · rintro ⟨T, hT⟩
      exact ⟨T, IsometryEquiv.ext fun z => (hΨ T z).trans (hT z).symm⟩
    · rintro ⟨T, rfl⟩
      exact ⟨T, hΨ T⟩
  have hiso : isomPSL = Ψ.range := by
    rw [isomPSL, hS, Subgroup.closure_eq]
  -- `T • (−z̄)` with `T ∈ PSL(2,ℝ)` is never in the range
  have hnot : ∀ (g : SL(2, ℝ)) (φ : ℍ ≃ᵢ ℍ), (∀ z, φ z = g • UpperHalfPlane.J • z) → φ ∉ Ψ.range := by
    rintro g φ hφ ⟨T, rfl⟩
    exact k92i_not_psl_J g T fun z => (hΨ T z).symm.trans (hφ z)
  refine ⟨by rw [hiso, hS], ?_⟩
  rw [hiso, Subgroup.index_eq_two_iff]
  refine ⟨Jφ, fun b => ?_⟩
  obtain ⟨g, hg | hg⟩ := k92i_classify b
  · refine Or.inr ⟨⟨(g : PSL(2, ℝ)), IsometryEquiv.ext fun z => by rw [hΨ, k92_psl_smul_mk, hg]⟩, ?_⟩
    exact hnot g _ fun z => by rw [IsometryEquiv.mul_apply, hJφ, hg]
  · refine Or.inl ⟨⟨(g : PSL(2, ℝ)), IsometryEquiv.ext fun z => ?_⟩, hnot g b hg⟩
    rw [hΨ, k92_psl_smul_mk, IsometryEquiv.mul_apply, hJφ, hg, k92i_JJ]

/-- **Definition** (§1.3; l. 312). An isometry is orientation-preserving when it is given by a matrix of positive
determinant, i.e. it is in `PSL(2,ℝ)`. -/
def IsOrientationPreserving (φ : ℍ ≃ᵢ ℍ) : Prop :=
  ∃ g : GL (Fin 2) ℝ, 0 < g.det.val ∧ ∀ z, φ z = g • z

/-- **Definition** (§1.3; l. 312). An isometry is orientation-reversing when it is given by a matrix of negative
determinant, i.e. it is of the form (1.3.2). -/
def IsOrientationReversing (φ : ℍ ≃ᵢ ℍ) : Prop :=
  ∃ g : GL (Fin 2) ℝ, g.det.val < 0 ∧ ∀ z, φ z = g • z

/-- **Formula (1.3.3)** (§1.3; l. 314–317; cited at l. 673). The inner product on `T_z ℍ ≈ ℂ`:
`⟨ζ₁, ζ₂⟩ = (ξ₁ξ₂ + η₁η₂)/(Im z)²`. -/
def tangentInner (z : ℍ) (ζ₁ ζ₂ : ℂ) : ℝ := (ζ₁.re * ζ₂.re + ζ₁.im * ζ₂.im) / z.im ^ 2

/-- **Definition** (§1.3; l. 318). The norm `‖·‖` on `T_z ℍ` of the inner product (1.3.3). -/
def tangentNorm (z : ℍ) (ζ : ℂ) : ℝ := √(tangentInner z ζ ζ)

/-- Helper (§1.3). The tangent direction at `z` of the geodesic from `z` towards `p ∈ ℍ̃ ∖ {z}`:
`i (p − z)/(p − z̄)`, and `i` for `p = ∞`. -/
def tangentDir (z : ℍ) (p : ExtPlane) : ℂ :=
  p.elim I fun q => I * (q - z) / (q - conj (z : ℂ))

/-- **Definition** (§1.3; l. 326). The angle at `z` between the geodesics from `z` towards `p` and towards `q`
(`p, q ∈ ℍ̃ ∖ {z}`): the angle between their tangent vectors, which is the Euclidean angle (Exercise 1.3). -/
def hypAngle (z : ℍ) (p q : ExtPlane) : ℝ :=
  InnerProductGeometry.angle (tangentDir z p) (tangentDir z q)

/-- **Definition** (§1.3; l. 328). A transformation of ℍ is conformal: it preserves angles.
Modelling: it has a nonzero complex derivative at every point (read on `ℂ` through `UpperHalfPlane.ofComplex`). -/
def IsConformalH (φ : ℍ → ℍ) : Prop :=
  ∀ z : ℍ, ∃ c : ℂ, c ≠ 0 ∧ HasDerivAt (fun w => (φ (UpperHalfPlane.ofComplex w) : ℂ)) c z

/-- **Definition** (§1.3; l. 328). A transformation of ℍ is anti-conformal: it preserves the absolute values of
angles but changes their signs. Modelling: its complex conjugate has a nonzero complex derivative everywhere. -/
def IsAntiConformalH (φ : ℍ → ℍ) : Prop :=
  ∀ z : ℍ, ∃ c : ℂ, c ≠ 0 ∧ HasDerivAt (fun w => conj (φ (UpperHalfPlane.ofComplex w) : ℂ)) c z

/-- The Möbius quotient `num G / denom G` has derivative `det G / denom G z²` off the real axis. -/
theorem k92_hasDerivAt_num_div_denom (G : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (fun w => UpperHalfPlane.num G w / UpperHalfPlane.denom G w)
      ((G.det.val : ℂ) / UpperHalfPlane.denom G z ^ 2) z := by
  have hd := UpperHalfPlane.denom_ne_zero_of_im G hz
  have h1 : HasDerivAt (fun w => UpperHalfPlane.num G w) (G 0 0 : ℂ) z := by
    simpa [UpperHalfPlane.num] using ((hasDerivAt_id z).const_mul (G 0 0 : ℂ)).add_const (G 0 1 : ℂ)
  have h2 : HasDerivAt (fun w => UpperHalfPlane.denom G w) (G 1 0 : ℂ) z := by
    simpa [UpperHalfPlane.denom] using ((hasDerivAt_id z).const_mul (G 1 0 : ℂ)).add_const (G 1 1 : ℂ)
  convert h1.div h2 hd using 1
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom]
  push_cast
  ring

/-- **Theorem 1.3.2** (§1.3; l. 330; cited at l. 385), first claim. Any transformation of `PSL(2,ℝ)` is
conformal. -/
theorem thm1_3_2_i (T : PSL(2, ℝ)) : IsConformalH (T • ·) := by
  intro z
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective T
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ g with hG
  have hdet : G.det.val = 1 := by simp [hG]
  have hdpos : 0 < G.det.val := by rw [hdet]; exact one_pos
  refine ⟨(G.det.val : ℂ) / UpperHalfPlane.denom G z ^ 2,
    div_ne_zero (by rw [hdet]; exact one_ne_zero) (pow_ne_zero _ (UpperHalfPlane.denom_ne_zero G z)), ?_⟩
  have hev : (fun w => ((((g : PSL(2, ℝ))) • UpperHalfPlane.ofComplex w : ℍ) : ℂ)) =ᶠ[𝓝 (z : ℂ)]
      fun w => UpperHalfPlane.num G w / UpperHalfPlane.denom G w := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.im_pos] with w hw
    rw [k92_psl_smul_mk, MulAction.compHom_smul_def, UpperHalfPlane.coe_smul_of_det_pos hdpos,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  exact (k92_hasDerivAt_num_div_denom G z.im_ne_zero).congr_of_eventuallyEq hev

/-- **Theorem 1.3.2** (§1.3; l. 330), second claim. Any transformation of the form (1.3.2) is anti-conformal. -/
theorem thm1_3_2_ii (g : GL (Fin 2) ℝ) (hg : g.det.val = -1) : IsAntiConformalH (g • ·) := by
  intro z
  have hneg : ¬ 0 < g.det.val := by rw [hg]; norm_num
  refine ⟨(g.det.val : ℂ) / UpperHalfPlane.denom g z ^ 2,
    div_ne_zero (by rw [hg]; norm_num) (pow_ne_zero _ (UpperHalfPlane.denom_ne_zero g z)), ?_⟩
  have hev : (fun w => conj ((g • UpperHalfPlane.ofComplex w : ℍ) : ℂ)) =ᶠ[𝓝 (z : ℂ)]
      fun w => UpperHalfPlane.num g w / UpperHalfPlane.denom g w := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.im_pos] with w hw
    rw [UpperHalfPlane.coe_smul, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    simp only [UpperHalfPlane.σ, hneg, ↓reduceIte]
    simp
  exact (k92_hasDerivAt_num_div_denom g z.im_ne_zero).congr_of_eventuallyEq hev

/-- **Theorem 1.3.3** (§1.3; l. 336; cited at l. 829). The topology on ℍ induced by the hyperbolic metric is the
topology induced by the Euclidean metric.
Modelling: Mathlib's `MetricSpace ℍ` instance realizes this by construction (`replaceTopology`); stated here as the
book's theorem. -/
theorem thm1_3_3 :
    @UniformSpace.toTopologicalSpace ℍ PseudoMetricSpace.toUniformSpace =
      TopologicalSpace.induced ((↑) : ℍ → ℂ) inferInstance := by
  rfl

end Katok1992
