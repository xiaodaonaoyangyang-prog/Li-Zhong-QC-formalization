import References.Katok1992.Ch01.S06_ComparisonOfGeometries

/-!
# Katok 1992, Ch. 2 §2.1 The group PSL(2,ℝ)

S. Katok, *Fuchsian Groups* (1992), Chapter 2 *Fuchsian Groups*, §2.1; source `full.md` of
`Fuchsian groups (Katok, Svetlana) …-3766f6b7…`, lines 649–711.

* Definition (PSL(2,ℝ) as the transformations `z ↦ (az + b)/(cz + d)`, `ad − bc = 1`, l. 651–654) — exists:
  `Matrix.ProjectiveSpecialLinearGroup` `Katok1992.pslAction` (Mathlib's quotient of SL(2,ℝ) by its center, acting
  on ℍ by the Ch. 1 scoped instance)
* Definition (elliptic, parabolic, hyperbolic elements by the trace, l. 656–657) — `IsElliptic`, `IsParabolic`,
  `IsHyperbolic`
* Unlabelled (l. 659–660: normal forms of hyperbolic and elliptic matrices; cited at l. 2583) —
  `hyperbolic_conj_diag`, `hyperbolic_conj_diag_unique`, `elliptic_conj_rotation`, `elliptic_conj_rotation_unique`
* Definition (the action on `ℝ ∪ {∞}` and on `ℍ̃ = ℍ ∪ ℝ ∪ {∞}`, used from l. 663, stated at l. 919) —
  `pslActionBoundary`, `Hbar`
* Unlabelled (l. 661–667: fixed points by type; recalled at l. 899) — `fixedBy_of_isHyperbolic`,
  `fixedBy_of_isParabolic`, `fixedBy_of_isElliptic`
* Definition (the axis `C(T)`, l. 669; cited in Cor 2.3.4) — `axis`, `boundaryToExt`
* Definition (the unit tangent bundle `Sℍ`, l. 673) — `unitTangentBundle`
* Formula (2.1.1) (the action on `Sℍ` by `DT(ζ) = ζ/(cz + d)²`, l. 673–677; cited at l. 683, 1727) — `tangentMap`
* Theorem 2.1.1 (l. 681; cited at l. 1711) — `thm2_1_1`
* Definition (the topology of PSL(2,ℝ) as the quotient of `X ⊆ ℝ⁴` by `δ = −id`, l. 695–701) — exists:
  `QuotientGroup.instTopologicalSpace` `instTopologicalSpaceSubtype` (the quotient topology of SL(2,ℝ), whose
  topology is the subtype topology of the matrices ≅ ℝ⁴; the center is {±1})
* Definition (discrete subgroup, l. 709) — exists: `DiscreteTopology` (the induced topology is discrete)
* Unlabelled (l. 711: sequential criterion for discreteness; used at l. 915, 943, 963, 1053, 1099, 1121) —
  `discreteTopology_iff_tendsto_one`

Not items (DESIGN §3): "fixes ∞ iff c = 0, then `z ↦ az + b`" (l. 667; a computation inside proofs); "By Theorem
1.2.5, T maps C(T) onto itself" (l. 671; not cited, and the content is Theorem 1.2.4 [cit?]); `Sℍ ≅ ℍ × S¹` and the
action law on `Sℍ` (l. 673; not cited); the metric `dℓ` and volume `dv` on `Sℍ` (l. 693) and the norm `‖T‖`
(l. 703–707), used only in proofs and exercises (D-7); the terminology remark on hyperbolas/ellipses (l. 660); the
exercises.

**Conventions.** PSL(2,ℝ) is Mathlib's `PSL(2, ℝ)` with its quotient topology, acting on ℍ by `pslAction`
(Ch. 1). `Tr` is the Ch. 1 `|trace|` of a lift. `Id` is `1`, and `IsParabolic` excludes it (D-3: Theorem 2.3.3 (b)
fails otherwise; Mathlib's `Matrix.IsParabolic` also excludes scalars). ℍ̃ is the type `Hbar = ℍ ⊕ OnePoint ℝ`
(D-2), with fixed-point sets `MulAction.fixedBy Hbar T`. Statements about matrices use Mathlib's
`Matrix.IsHyperbolic` / `Matrix.IsElliptic` (discriminant `tr² − 4 det`, i.e. `|tr| > 2` / `|tr| < 2` on SL).
-/

open Complex Set Metric Filter Topology
open scoped UpperHalfPlane MatrixGroups

noncomputable section

namespace Katok1992

open LiZhongQC (ExtPlane)

/-- **Definition** (§2.1; l. 656). `T` is elliptic if `Tr(T) < 2`. -/
def IsElliptic (T : PSL(2, ℝ)) : Prop := Tr T < 2

/-- **Definition** (§2.1; l. 656). `T` is parabolic if `Tr(T) = 2`.
Modelling: `T ≠ Id` added (D-3). -/
def IsParabolic (T : PSL(2, ℝ)) : Prop := Tr T = 2 ∧ T ≠ 1

/-- **Definition** (§2.1; l. 656). `T` is hyperbolic if `Tr(T) > 2`. -/
def IsHyperbolic (T : PSL(2, ℝ)) : Prop := 2 < Tr T

/-- Auxiliary (§2.1). The discriminant of `g ∈ SL(2,ℝ)` is `tr² − 4`. -/
theorem k92n_discr (g : SL(2, ℝ)) :
    (g : Matrix (Fin 2) (Fin 2) ℝ).discr = (g 0 0 + g 1 1) ^ 2 - 4 := by
  rw [Matrix.discr_fin_two, Matrix.trace_fin_two, g.2]
  ring

/-- Auxiliary (§2.1). The discriminant is invariant under conjugation in SL(2,ℝ). -/
theorem k92n_discr_conj (P g : SL(2, ℝ)) :
    ((P * g * P⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).discr = (g : Matrix (Fin 2) (Fin 2) ℝ).discr := by
  have h1 : ((P⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) * (P : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [Matrix.discr_fin_two, Matrix.discr_fin_two, (P * g * P⁻¹ : SL(2, ℝ)).2, g.2,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, h1, Matrix.one_mul]

/-- Auxiliary (§2.1, l. 660). Diagonalization of a hyperbolic `g ∈ SL(2,ℝ)` (`|tr g| > 2`): the rows of `P` are left
eigenvectors, `(c, λ − a)` for `c ≠ 0`, and `(1, b/(a − d))`, `(0, 1)` for `c = 0`, normalized to `det P = 1`. -/
theorem k92n_hyp_diag (g : SL(2, ℝ)) (h : 4 < (g 0 0 + g 1 1) ^ 2) :
    ∃ l : ℝ, l ≠ 1 ∧ l ≠ -1 ∧ ∃ P : SL(2, ℝ),
      ((P * g * P⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![l, 0; 0, l⁻¹] := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2
    rwa [Matrix.det_fin_two] at this
  -- conjugating to `D` amounts to `P g = D P`
  have conj : ∀ (P : SL(2, ℝ)) (D : Matrix (Fin 2) (Fin 2) ℝ),
      (P : Matrix (Fin 2) (Fin 2) ℝ) * g = D * P → ((P * g * P⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = D :=
    fun P D hPD => by
      have h1 : (P : Matrix (Fin 2) (Fin 2) ℝ) * ((P⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hPD, Matrix.mul_assoc, h1,
        Matrix.mul_one]
  -- `l ≠ ±1` follows from `l + l⁻¹ = a + d`
  have hpm : ∀ l : ℝ, l + l⁻¹ = g 0 0 + g 1 1 → l ≠ 1 ∧ l ≠ -1 := fun l hl => by
    constructor <;> rintro rfl <;> norm_num at hl <;> rw [← hl] at h <;> norm_num at h
  rcases eq_or_ne (g 1 0) 0 with hc | hc
  · -- `c = 0`: `g = [[a, b], [0, a⁻¹]]`
    have hd : g 1 1 = (g 0 0)⁻¹ := by
      rw [hc, mul_zero, sub_zero] at hdet
      exact eq_inv_of_mul_eq_one_right hdet
    have ha0 : g 0 0 ≠ 0 := by
      intro h0
      rw [h0, zero_mul, hc, mul_zero, sub_zero] at hdet
      exact zero_ne_one hdet
    have had : g 0 0 - g 1 1 ≠ 0 := by
      intro h0
      have e : g 1 1 = g 0 0 := by linarith
      rw [hc, mul_zero, sub_zero, e] at hdet
      rw [e] at h
      nlinarith
    obtain ⟨hl1, hl2⟩ := hpm (g 0 0) (by rw [hd])
    refine ⟨g 0 0, hl1, hl2, ⟨!![1, g 0 1 / (g 0 0 - g 1 1); 0, 1], by simp⟩, conj _ _ ?_⟩
    rw [← hd]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc]
    field_simp
    ring
  · -- `c ≠ 0`: rows `(c, λ − a)` and `(c, λ⁻¹ − a)`, scaled to `det = 1`
    set t := g 0 0 + g 1 1
    have hD : 0 < t ^ 2 - 4 := by linarith
    set s := Real.sqrt (t ^ 2 - 4)
    have hs : s * s = t ^ 2 - 4 := Real.mul_self_sqrt hD.le
    have hs0 : 0 < s := Real.sqrt_pos.2 hD
    set l := (t + s) / 2
    set μ := (t - s) / 2
    have hlμ : l * μ = 1 := by
      simp only [l, μ]
      linear_combination (-1 / 4 : ℝ) * hs
    have hμ : μ = l⁻¹ := eq_inv_of_mul_eq_one_right hlμ
    have hl : l ^ 2 = t * l - 1 := by
      simp only [l]
      linear_combination (1 / 4 : ℝ) * hs
    have hm : μ ^ 2 = t * μ - 1 := by
      simp only [μ]
      linear_combination (1 / 4 : ℝ) * hs
    set δ := g 1 0 * (μ - l)
    have hδ : δ ≠ 0 := mul_ne_zero hc (by simp only [μ, l]; intro e; linarith)
    obtain ⟨hl1, hl2⟩ := hpm l (by rw [← hμ]; simp only [l, μ, t]; ring)
    refine ⟨l, hl1, hl2,
      ⟨!![g 1 0 / δ, (l - g 0 0) / δ; g 1 0, μ - g 0 0], ?_⟩, conj _ _ ?_⟩
    · rw [Matrix.det_fin_two_of]
      field_simp
      simp only [δ]
      ring
    · rw [← hμ]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · field_simp
        ring
      · field_simp
        linear_combination (-1 : ℝ) * hl - hdet
      · ring
      · linear_combination (-1 : ℝ) * hm - hdet

/-- **Unlabelled** (§2.1; l. 660; cited at l. 2583). A matrix of SL(2,ℝ) is hyperbolic iff it is conjugate in
SL(2,ℝ) to `diag(λ, 1/λ)`, `λ ≠ ±1`.
[CORRECTION] The book writes `λ ≠ 1`; in SL(2,ℝ) `λ < 0` occurs and `λ = −1` gives `−1`, not hyperbolic. -/
theorem hyperbolic_conj_diag (g : SL(2, ℝ)) :
    (g : Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic ↔ ∃ l : ℝ, l ≠ 1 ∧ l ≠ -1 ∧ ∃ P : SL(2, ℝ),
      ((P * g * P⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![l, 0; 0, l⁻¹] := by
  constructor
  · intro h
    have h' : 0 < (g 0 0 + g 1 1) ^ 2 - 4 := by rw [← k92n_discr]; exact h
    exact k92n_hyp_diag g (by linarith)
  · rintro ⟨l, hl1, hl2, P, hP⟩
    have hd := (P * g * P⁻¹ : SL(2, ℝ)).2
    rw [hP, Matrix.det_fin_two_of] at hd
    have hl0 : l ≠ 0 := by
      rintro rfl
      simp at hd
    show 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).discr
    rw [← k92n_discr_conj P g, hP, Matrix.discr_fin_two, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
    have e : (l + l⁻¹) ^ 2 - 4 * (l * l⁻¹ - 0 * 0) = (l - l⁻¹) ^ 2 := by
      field_simp
      ring
    rw [e]
    have hne : l - l⁻¹ ≠ 0 := by
      intro h0
      have : (l - 1) * (l + 1) = 0 := by
        field_simp at h0
        linear_combination h0
      rcases mul_eq_zero.1 this with h | h
      · exact hl1 (by linarith)
      · exact hl2 (by linarith)
    positivity

/-- The trace of a conjugate in `SL(2,ℝ)`. -/
theorem k92_trace_conj (R g : SL(2, ℝ)) :
    Matrix.trace ((R * g * R⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℝ) := by
  have h1 : ((R⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) * (R : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, h1, Matrix.one_mul]

/-- **Unlabelled** (§2.1; l. 660). Uniqueness of the diagonal form.
[CORRECTION] The book's "unique" holds only up to `λ ↔ λ⁻¹` (`diag(λ, 1/λ)`, `diag(1/λ, λ)` are conjugate). -/
theorem hyperbolic_conj_diag_unique (g P Q : SL(2, ℝ)) (l m : ℝ)
    (hP : ((P * g * P⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![l, 0; 0, l⁻¹])
    (hQ : ((Q * g * Q⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![m, 0; 0, m⁻¹]) :
    m = l ∨ m = l⁻¹ := by
  have htP := k92_trace_conj P g
  have htQ := k92_trace_conj Q g
  rw [hP, Matrix.trace_fin_two_of] at htP
  rw [hQ, Matrix.trace_fin_two_of] at htQ
  have hm : m ≠ 0 := by
    intro h0
    have hd := (Q * g * Q⁻¹ : SL(2, ℝ)).prop
    rw [hQ, Matrix.det_fin_two_of, h0] at hd
    simp at hd
  have hl : l ≠ 0 := by
    intro h0
    have hd := (P * g * P⁻¹ : SL(2, ℝ)).prop
    rw [hP, Matrix.det_fin_two_of, h0] at hd
    simp at hd
  have h : m + m⁻¹ = l + l⁻¹ := by rw [htP, htQ]
  have e : (m - l) * (m - l⁻¹) = m * (m + m⁻¹ - (l + l⁻¹)) := by
    field_simp
    ring
  rw [h, sub_self, mul_zero] at e
  rcases mul_eq_zero.1 e with h1 | h1
  · exact Or.inl (sub_eq_zero.1 h1)
  · exact Or.inr (sub_eq_zero.1 h1)

/-- Auxiliary (§2.1, l. 660). An elliptic `g ∈ SL(2,ℝ)` is conjugate to a rotation: `g` fixes `z₀ ∈ ℍ`
(`UpperHalfPlane.fixedPt`), `P = (toSL2R z₀)⁻¹` moves `z₀` to `i`, and the stabilizer of `i` consists of rotations
(`gl_smul_I_eq_I_iff_of_pos`); `sin θ ≠ 0` since `|tr| = 2|cos θ| < 2`. -/
theorem k92n_ell_rot (g : SL(2, ℝ)) (h : (g : Matrix (Fin 2) (Fin 2) ℝ).IsElliptic) :
    ∃ θ : ℝ, Real.sin θ ≠ 0 ∧ ∃ P : SL(2, ℝ),
      ((P * g * P⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := by
  have hell : (Matrix.SpecialLinearGroup.mapGL ℝ g).IsElliptic := h
  set z₀ := UpperHalfPlane.fixedPt _ hell
  have hpos : 0 < ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    simp
  have hz₀ : g • z₀ = z₀ := (UpperHalfPlane.gl_smul_eq_self_iff_eq_fixedPt hpos hell).2 rfl
  set hh := z₀.toSL2R
  -- `k = hh⁻¹ g hh` fixes `i`, hence is a rotation
  set k : SL(2, ℝ) := hh⁻¹ * g * hh
  have hk : k • UpperHalfPlane.I = UpperHalfPlane.I := by
    rw [mul_smul, mul_smul, UpperHalfPlane.toSL2R_smul_I, hz₀, inv_smul_eq_iff, UpperHalfPlane.toSL2R_smul_I]
  have hkpos : 0 < (Matrix.SpecialLinearGroup.mapGL ℝ k).det.val := by simp
  obtain ⟨h1, h2⟩ := (UpperHalfPlane.gl_smul_I_eq_I_iff_of_pos hkpos).1 hk
  have h1' : k 0 0 = k 1 1 := h1
  have h2' : k 0 1 = -k 1 0 := h2
  have hdet : k 0 0 * k 1 1 - k 0 1 * k 1 0 = 1 := by
    have := k.2
    rwa [Matrix.det_fin_two] at this
  have hsq : k 0 0 ^ 2 + k 0 1 ^ 2 = 1 := by
    linear_combination hdet + k 0 0 * h1' + k 0 1 * h2'
  set w : ℂ := ⟨k 0 0, k 0 1⟩
  have hw1 : ‖w‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, Real.sqrt_eq_one]
    linear_combination hsq
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hw1
    exact zero_ne_one hw1
  refine ⟨Complex.arg w, ?_, hh⁻¹, ?_⟩
  · -- `sin θ = 0` would make `k = ±1`, of discriminant `0`
    rw [Complex.sin_arg, hw1, div_one]
    intro h0
    have hd := k92n_discr_conj hh⁻¹ g
    rw [inv_inv, k92n_discr] at hd
    have hneg : (g : Matrix (Fin 2) (Fin 2) ℝ).discr < 0 := h
    have hk01 : k 0 1 = 0 := h0
    rw [← hd] at hneg
    change ((k : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + (k : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2 - 4 < 0 at hneg
    rw [← h1'] at hneg
    rw [hk01] at hsq
    nlinarith
  · rw [inv_inv, Complex.cos_arg hw0, Complex.sin_arg, hw1, div_one, div_one]
    change (k : Matrix (Fin 2) (Fin 2) ℝ) = _
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · show k 1 0 = -k 0 1
      rw [h2']
      ring
    · exact h1'.symm

/-- **Unlabelled** (§2.1; l. 660). A matrix of SL(2,ℝ) is elliptic iff it is conjugate in SL(2,ℝ) to a rotation
matrix `[[cos θ, sin θ], [−sin θ, cos θ]]`.
[CORRECTION] `θ ∉ πℤ` (`sin θ ≠ 0`) is needed: the rotations by `0`, `π` are `±1`. -/
theorem elliptic_conj_rotation (g : SL(2, ℝ)) :
    (g : Matrix (Fin 2) (Fin 2) ℝ).IsElliptic ↔ ∃ θ : ℝ, Real.sin θ ≠ 0 ∧ ∃ P : SL(2, ℝ),
      ((P * g * P⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := by
  constructor
  · exact k92n_ell_rot g
  · rintro ⟨θ, hθ, P, hP⟩
    show (g : Matrix (Fin 2) (Fin 2) ℝ).discr < 0
    rw [← k92n_discr_conj P g, hP, Matrix.discr_fin_two, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
    have e : (Real.cos θ + Real.cos θ) ^ 2 - 4 * (Real.cos θ * Real.cos θ - Real.sin θ * -Real.sin θ) =
        -4 * Real.sin θ ^ 2 := by
      ring
    rw [e]
    have : 0 < Real.sin θ ^ 2 := by positivity
    linarith

/-- Auxiliary (§2.1). If `M R(θ) = R(φ) M` with `M ∈ SL(2,ℝ)`, then `cos φ = cos θ` (trace) and `sin φ = sin θ`
(the `(2,1)` entry of `M R(θ) M⁻¹` is `−sin θ (M₁₀² + M₁₁²)`, whose sign is an SL-conjugacy invariant). -/
theorem k92n_rot_conj (M : SL(2, ℝ)) {θ φ : ℝ}
    (h : (M : Matrix (Fin 2) (Fin 2) ℝ) * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] =
      !![Real.cos φ, Real.sin φ; -Real.sin φ, Real.cos φ] * (M : Matrix (Fin 2) (Fin 2) ℝ)) :
    Real.cos φ = Real.cos θ ∧ Real.sin φ = Real.sin θ := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have := M.2
    rwa [Matrix.det_fin_two] at this
  have E : ∀ i j, ((M : Matrix (Fin 2) (Fin 2) ℝ) * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]) i j =
      (!![Real.cos φ, Real.sin φ; -Real.sin φ, Real.cos φ] * (M : Matrix (Fin 2) (Fin 2) ℝ)) i j := fun i j => by
    rw [h]
  have E00 := E 0 0
  have E01 := E 0 1
  have E10 := E 1 0
  have E11 := E 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at E00 E01 E10 E11
  have hc : Real.cos φ = Real.cos θ := by
    linear_combination (-(1 / 2 : ℝ)) * (M 1 1 * E00 - M 1 0 * E01 + M 0 0 * E11 - M 0 1 * E10) +
      (Real.cos θ - Real.cos φ) * hdet
  have hS1 : Real.sin φ = Real.sin θ * (M 1 0 ^ 2 + M 1 1 ^ 2) := by
    linear_combination (M 1 1 * E10 - M 1 0 * E11) - Real.sin φ * hdet
  have hsq : Real.sin φ ^ 2 = Real.sin θ ^ 2 := by
    have h1 := Real.sin_sq_add_cos_sq φ
    have h2 := Real.sin_sq_add_cos_sq θ
    rw [hc] at h1
    linarith
  refine ⟨hc, ?_⟩
  rw [hS1] at hsq ⊢
  have hK : 0 < M 1 0 ^ 2 + M 1 1 ^ 2 := by
    rcases eq_or_ne (M 1 0) 0 with h0 | h0
    · have : M 1 1 ≠ 0 := by
        intro h1
        rw [h0, h1] at hdet
        simp at hdet
      positivity
    · positivity
  have : Real.sin θ ^ 2 * ((M 1 0 ^ 2 + M 1 1 ^ 2) - 1) * ((M 1 0 ^ 2 + M 1 1 ^ 2) + 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.1 this with h0 | h0
  · rcases mul_eq_zero.1 h0 with h0 | h0
    · have : Real.sin θ = 0 := by simpa using h0
      rw [this]
      ring
    · rw [show M 1 0 ^ 2 + M 1 1 ^ 2 = 1 by linarith]
      ring
  · linarith

/-- Auxiliary (§2.1). Equal cosines and sines give angles equal modulo `2π`. -/
theorem k92n_angle_eq {θ φ : ℝ} (hc : Real.cos φ = Real.cos θ) (hs : Real.sin φ = Real.sin θ) :
    ∃ k : ℤ, φ = θ + 2 * Real.pi * k := by
  have he : Complex.exp (φ * I) = Complex.exp (θ * I) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, hc, hs]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp at this
  linarith

/-- **Unlabelled** (§2.1; l. 660). Uniqueness of the rotation form: `θ` is unique modulo `2π`. -/
theorem elliptic_conj_rotation_unique (g P Q : SL(2, ℝ)) (θ φ : ℝ)
    (hP : ((P * g * P⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ])
    (hQ : ((Q * g * Q⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos φ, Real.sin φ; -Real.sin φ, Real.cos φ]) :
    ∃ k : ℤ, φ = θ + 2 * Real.pi * k := by
  have e : (Q * P⁻¹) * (P * g * P⁻¹) = (Q * g * Q⁻¹) * (Q * P⁻¹) := by group
  have e2 := congrArg (fun x : SL(2, ℝ) => (x : Matrix (Fin 2) (Fin 2) ℝ)) e
  simp only [Matrix.SpecialLinearGroup.coe_mul] at e2
  rw [← Matrix.SpecialLinearGroup.coe_mul P, ← Matrix.SpecialLinearGroup.coe_mul (P * g), hP,
    ← Matrix.SpecialLinearGroup.coe_mul Q g, ← Matrix.SpecialLinearGroup.coe_mul (Q * g), hQ,
    ← Matrix.SpecialLinearGroup.coe_mul Q P⁻¹] at e2
  obtain ⟨hc, hs⟩ := k92n_rot_conj (Q * P⁻¹) e2
  exact k92n_angle_eq hc hs

/-- **Definition** (§2.1, l. 663; §2.4, l. 919). The action of PSL(2,ℝ) on `ℝ ∪ {∞} = OnePoint ℝ`.
Modelling: Mathlib's PSL action on `ℙ¹(ℝ)` transferred along `OnePoint.equivProjectivization` (Möbius maps,
`∞` at a pole). -/
scoped instance pslActionBoundary : MulAction PSL(2, ℝ) (OnePoint ℝ) :=
  (OnePoint.equivProjectivization ℝ).mulAction PSL(2, ℝ)

/-- **Definition** (§2.4, l. 919). The closed half-plane `ℍ̃ = ℍ ∪ ℝ ∪ {∞}` as a type, with Mathlib's `Sum`
action of PSL(2,ℝ). -/
abbrev Hbar : Type := ℍ ⊕ OnePoint ℝ

/-- Auxiliary (§2.1). `±g ∈ PSL(2,ℝ)` acts on `ℝ ∪ {∞}` as Mathlib's `GL(2,ℝ)` action of `g` on `OnePoint ℝ`
(both are transported from `ℙ¹(ℝ)` along `equivProjectivization`). -/
theorem k92n_bdry_smul (g : SL(2, ℝ)) (x : OnePoint ℝ) :
    ((g : PSL(2, ℝ)) • x : OnePoint ℝ) = (Matrix.SpecialLinearGroup.mapGL ℝ g) • x := by
  show (OnePoint.equivProjectivization ℝ).symm ((g : PSL(2, ℝ)) • (OnePoint.equivProjectivization ℝ) x) =
    (OnePoint.equivProjectivization ℝ).symm
      ((Matrix.SpecialLinearGroup.mapGL ℝ g) • (OnePoint.equivProjectivization ℝ) x)
  congr 1

/-- Auxiliary (§2.1). The fixed-point set in ℍ̃ of `±g`, through Mathlib's `GL(2,ℝ)` actions on ℍ and `OnePoint ℝ`. -/
theorem k92n_fixedBy (g : SL(2, ℝ)) :
    MulAction.fixedBy Hbar (g : PSL(2, ℝ)) =
      Sum.inl '' {z : ℍ | Matrix.SpecialLinearGroup.mapGL ℝ g • z = z} ∪
        Sum.inr '' {x : OnePoint ℝ | Matrix.SpecialLinearGroup.mapGL ℝ g • x = x} := by
  ext p
  rcases p with z | x
  · simp only [MulAction.mem_fixedBy, Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Sum.inl.injEq,
      reduceCtorEq, and_false, exists_false, or_false]
    constructor
    · intro h
      exact ⟨z, (k92_psl_smul_mk g z).symm.trans (Sum.inl.inj h), rfl⟩
    · rintro ⟨w, hw, rfl⟩
      show Sum.inl ((g : PSL(2, ℝ)) • w) = Sum.inl w
      rw [k92_psl_smul_mk]
      exact congrArg Sum.inl hw
  · simp only [MulAction.mem_fixedBy, Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Sum.inr.injEq,
      reduceCtorEq, and_false, exists_false, false_or]
    constructor
    · intro h
      exact ⟨x, (k92n_bdry_smul g x).symm.trans (Sum.inr.inj h), rfl⟩
    · rintro ⟨w, hw, rfl⟩
      show Sum.inr ((g : PSL(2, ℝ)) • w) = Sum.inr w
      rw [k92n_bdry_smul]
      exact congrArg Sum.inr hw

/-- Auxiliary (§2.1). `T` is the class of its representative, and `Tr T = |a + d|` for it. -/
theorem k92n_Tr_out (T : PSL(2, ℝ)) :
    ((Quotient.out T : SL(2, ℝ)) : PSL(2, ℝ)) = T ∧
      Tr T = |(Quotient.out T : SL(2, ℝ)) 0 0 + (Quotient.out T : SL(2, ℝ)) 1 1| := by
  refine ⟨QuotientGroup.out_eq' T, ?_⟩
  unfold Tr
  rw [Matrix.trace_fin_two]

/-- Auxiliary (§2.1). A central (scalar) matrix has discriminant `0`. -/
theorem k92n_discr_center {G : GL (Fin 2) ℝ} (h : G ∈ Subgroup.center (GL (Fin 2) ℝ)) :
    (G : Matrix (Fin 2) (Fin 2) ℝ).discr = 0 := by
  obtain ⟨r, hr⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 h
  rw [← hr, Matrix.discr_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp
  ring

/-- Auxiliary (§2.1). If `±g ≠ Id` in PSL(2,ℝ), then `g` is not central (not scalar) in GL(2,ℝ). -/
theorem k92n_not_center (g : SL(2, ℝ)) (hT : (g : PSL(2, ℝ)) ≠ 1) :
    Matrix.SpecialLinearGroup.mapGL ℝ g ∉ Subgroup.center (GL (Fin 2) ℝ) := by
  intro h
  obtain ⟨r, hr⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 h
  apply hT
  rw [QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff]
  have hg : (Matrix.scalar (Fin 2) r : Matrix (Fin 2) (Fin 2) ℝ) = g := hr
  refine ⟨r, ?_, hg⟩
  have hd := g.2
  rw [← hg] at hd
  simpa [Matrix.det_fin_two, sq] using hd

/-- Auxiliary (§2.1). A non-scalar matrix of positive determinant with `discr ≥ 0` has no fixed point in ℍ
(Mathlib: a fixed point in ℍ forces ellipticity). -/
theorem k92n_no_fix_H {G : GL (Fin 2) ℝ} (hdet : 0 < (G : Matrix (Fin 2) (Fin 2) ℝ).det)
    (hd : 0 ≤ (G : Matrix (Fin 2) (Fin 2) ℝ).discr) (hc : G ∉ Subgroup.center (GL (Fin 2) ℝ)) (z : ℍ) :
    G • z ≠ z := fun hz =>
  (not_lt.2 hd) (UpperHalfPlane.isElliptic_of_exists_smul_eq_self hdet hc ⟨z, hz⟩)

/-- Auxiliary (§2.1, l. 661–667). A hyperbolic `g ∈ SL(2,ℝ)` has exactly two fixed points in `ℝ ∪ {∞}`: for `c ≠ 0`
the two real roots of `c x² + (d − a) x − b` (discriminant `tr² − 4 > 0`), for `c = 0` the points `∞` and
`b/(d − a)`. -/
theorem k92n_hyp_bdry (g : SL(2, ℝ)) (h : 4 < (g 0 0 + g 1 1) ^ 2) :
    ∃ α β : OnePoint ℝ, α ≠ β ∧ ∀ x : OnePoint ℝ,
      Matrix.SpecialLinearGroup.mapGL ℝ g • x = x ↔ x = α ∨ x = β := by
  set G := Matrix.SpecialLinearGroup.mapGL ℝ g
  have hG : ∀ i j, (G : Matrix (Fin 2) (Fin 2) ℝ) i j = g i j := fun _ _ => rfl
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2
    rwa [Matrix.det_fin_two] at this
  have hinf : G • (OnePoint.infty : OnePoint ℝ) = OnePoint.infty ↔ g 1 0 = 0 := by
    rw [OnePoint.smul_infty_eq_self_iff, hG]
  have hfin : ∀ r : ℝ, G • (r : OnePoint ℝ) = r ↔ g 1 0 * (r * r) + (g 1 1 - g 0 0) * r + -g 0 1 = 0 := by
    intro r
    rw [← Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff]
    simp only [Matrix.GeneralLinearGroup.fixpointPolynomial, map_sub, map_add, map_mul, Polynomial.aeval_C,
      Polynomial.aeval_X_pow, Polynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply, hG]
    constructor <;> intro e <;> linear_combination e
  rcases eq_or_ne (g 1 0) 0 with hc | hc
  · -- `c = 0`: the fixed points are `∞` and `b/(d − a)`
    have hda : g 1 1 - g 0 0 ≠ 0 := by
      intro h0
      have e1 : g 1 1 = g 0 0 := by linarith
      rw [hc, mul_zero, sub_zero, e1] at hdet
      rw [e1] at h
      nlinarith
    refine ⟨OnePoint.infty, ((g 0 1 / (g 1 1 - g 0 0) : ℝ) : OnePoint ℝ), OnePoint.infty_ne_coe _, fun x => ?_⟩
    cases x with
    | infty => exact ⟨fun _ => Or.inl rfl, fun _ => hinf.2 hc⟩
    | coe r =>
      rw [hfin, hc]
      simp only [OnePoint.coe_ne_infty, false_or, OnePoint.coe_eq_coe, zero_mul, zero_add]
      rw [eq_div_iff hda]
      constructor <;> intro e <;> linear_combination e
  · -- `c ≠ 0`: the two real roots of `c x² + (d − a) x − b`
    have hD : 0 < discrim (g 1 0) (g 1 1 - g 0 0) (-g 0 1) := by
      rw [discrim]
      nlinarith
    set s := Real.sqrt (discrim (g 1 0) (g 1 1 - g 0 0) (-g 0 1))
    have hs : discrim (g 1 0) (g 1 1 - g 0 0) (-g 0 1) = s * s := (Real.mul_self_sqrt hD.le).symm
    have hs0 : 0 < s := Real.sqrt_pos.2 hD
    refine ⟨((-(g 1 1 - g 0 0) + s) / (2 * g 1 0) : ℝ), ((-(g 1 1 - g 0 0) - s) / (2 * g 1 0) : ℝ), ?_,
      fun x => ?_⟩
    · rw [Ne, OnePoint.coe_eq_coe, div_left_inj' (mul_ne_zero two_ne_zero hc)]
      intro e
      linarith
    cases x with
    | infty =>
      simp only [OnePoint.infty_ne_coe, or_self, iff_false]
      exact fun e => hc (hinf.1 e)
    | coe r =>
      rw [hfin, quadratic_eq_zero_iff hc hs]
      simp only [OnePoint.coe_eq_coe]

/-- **Unlabelled** (§2.1; l. 661–667). A hyperbolic `T` has exactly two fixed points in ℍ̃, both in `ℝ ∪ {∞}`. -/
theorem fixedBy_of_isHyperbolic {T : PSL(2, ℝ)} (hT : IsHyperbolic T) :
    ∃ α β : OnePoint ℝ, α ≠ β ∧ MulAction.fixedBy Hbar T = {Sum.inr α, Sum.inr β} := by
  obtain ⟨hgT, hTr⟩ := k92n_Tr_out T
  set g := (Quotient.out T : SL(2, ℝ))
  have h4 : 4 < (g 0 0 + g 1 1) ^ 2 := by
    have h2 : 2 < |g 0 0 + g 1 1| := hTr ▸ hT
    nlinarith [abs_nonneg (g 0 0 + g 1 1), sq_abs (g 0 0 + g 1 1)]
  obtain ⟨α, β, hαβ, hfix⟩ := k92n_hyp_bdry g h4
  have hd : 0 < ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).discr := by
    rw [show ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (g : Matrix (Fin 2) (Fin 2) ℝ) from rfl, k92n_discr]
    linarith
  have hc : Matrix.SpecialLinearGroup.mapGL ℝ g ∉ Subgroup.center (GL (Fin 2) ℝ) := fun h0 =>
    hd.ne' (k92n_discr_center h0)
  refine ⟨α, β, hαβ, ?_⟩
  rw [← hgT, k92n_fixedBy]
  ext p
  rcases p with z | x
  · simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Sum.inl.injEq, reduceCtorEq, and_false,
      exists_false, or_false, Set.mem_insert_iff, Set.mem_singleton_iff, or_self, iff_false, not_exists, not_and]
    rintro w hw rfl
    exact k92n_no_fix_H (by simp) hd.le hc w hw
  · simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Sum.inr.injEq, reduceCtorEq, and_false,
      exists_false, false_or, Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_right]
    exact hfix x

/-- **Unlabelled** (§2.1; l. 661–667). A parabolic `T` has exactly one fixed point in ℍ̃, in `ℝ ∪ {∞}`. -/
theorem fixedBy_of_isParabolic {T : PSL(2, ℝ)} (hT : IsParabolic T) :
    ∃ α : OnePoint ℝ, MulAction.fixedBy Hbar T = {Sum.inr α} := by
  obtain ⟨hgT, hTr⟩ := k92n_Tr_out T
  set g := (Quotient.out T : SL(2, ℝ))
  have hd : ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).discr = 0 := by
    rw [show ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (g : Matrix (Fin 2) (Fin 2) ℝ) from rfl, k92n_discr]
    have h2 : |g 0 0 + g 1 1| = 2 := hTr ▸ hT.1
    rw [← sq_abs, h2]
    norm_num
  have hc : Matrix.SpecialLinearGroup.mapGL ℝ g ∉ Subgroup.center (GL (Fin 2) ℝ) :=
    k92n_not_center g (by rw [hgT]; exact hT.2)
  have hpar : (Matrix.SpecialLinearGroup.mapGL ℝ g).IsParabolic :=
    ⟨fun hs => hc (Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2 hs), hd⟩
  refine ⟨(Matrix.SpecialLinearGroup.mapGL ℝ g).parabolicFixedPoint, ?_⟩
  rw [← hgT, k92n_fixedBy]
  ext p
  rcases p with z | x
  · simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Sum.inl.injEq, reduceCtorEq, and_false,
      exists_false, or_false, Set.mem_singleton_iff, iff_false, not_exists, not_and]
    rintro w hw rfl
    exact k92n_no_fix_H (by simp) hd.ge hc w hw
  · simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Sum.inr.injEq, reduceCtorEq, and_false,
      exists_false, false_or, Set.mem_singleton_iff, exists_eq_right]
    exact hpar.smul_eq_self_iff

/-- **Unlabelled** (§2.1; l. 661–667). An elliptic `T` has exactly one fixed point in ℍ̃, in ℍ.
Modelling: the complex-conjugate fixed point lies outside ℍ̃ and is not stated. -/
theorem fixedBy_of_isElliptic {T : PSL(2, ℝ)} (hT : IsElliptic T) :
    ∃ p : ℍ, MulAction.fixedBy Hbar T = {Sum.inl p} := by
  obtain ⟨hgT, hTr⟩ := k92n_Tr_out T
  set g := (Quotient.out T : SL(2, ℝ))
  have hell : (Matrix.SpecialLinearGroup.mapGL ℝ g).IsElliptic := by
    show ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).discr < 0
    rw [show ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (g : Matrix (Fin 2) (Fin 2) ℝ) from rfl, k92n_discr]
    have h2 : |g 0 0 + g 1 1| < 2 := hTr ▸ hT
    nlinarith [abs_nonneg (g 0 0 + g 1 1), sq_abs (g 0 0 + g 1 1)]
  have hpos : 0 < ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    simp
  refine ⟨UpperHalfPlane.fixedPt _ hell, ?_⟩
  rw [← hgT, k92n_fixedBy]
  ext p
  rcases p with z | x
  · simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Sum.inl.injEq, reduceCtorEq, and_false,
      exists_false, or_false, Set.mem_singleton_iff, exists_eq_right]
    exact UpperHalfPlane.gl_smul_eq_self_iff_eq_fixedPt hpos hell
  · simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Sum.inr.injEq, reduceCtorEq, and_false,
      exists_false, false_or, Set.mem_singleton_iff, iff_false, not_exists, not_and]
    rintro w hw rfl
    exact Matrix.GeneralLinearGroup.IsElliptic.smul_ne_self hell w hw

/-- Helper. The inclusion `ℝ ∪ {∞} → ℂ̂`. -/
def boundaryToExt : OnePoint ℝ → ExtPlane := OnePoint.map fun x : ℝ => (x : ℂ)

/-- **Definition** (§2.1; l. 669). The axis `C(T)`: the geodesic of ℍ joining the two fixed points of `T` in
`ℝ ∪ {∞}`.
Modelling: Ch. 1's `geodArc` between two distinct boundary fixed points (D-8); empty for parabolic and
elliptic `T`, all of ℍ (junk) for `T = 1`; used only for hyperbolic `T`. -/
def axis (T : PSL(2, ℝ)) : Set ℍ :=
  {z | ∃ α β : OnePoint ℝ, α ≠ β ∧ T • α = α ∧ T • β = β ∧ z ∈ geodArc (boundaryToExt α) (boundaryToExt β)}

/-- **Definition** (§2.1; l. 673). The unit tangent bundle `Sℍ = {(z, ζ) | z ∈ ℍ, ζ ∈ ℂ, |ζ| = Im z}`. -/
def unitTangentBundle : Set (ℍ × ℂ) := {p | ‖p.2‖ = p.1.im}

/-- **Formula (2.1.1)** (§2.1; l. 673–677). `T(z, ζ) = (T(z), ζ/(cz + d)²)`.
Modelling: computed on the lift `Quotient.out T`; `(cz + d)²` does not depend on the sign of the lift. -/
def tangentMap (T : PSL(2, ℝ)) (p : ℍ × ℂ) : ℍ × ℂ :=
  (T • p.1, p.2 / UpperHalfPlane.denom ((Quotient.out T : SL(2, ℝ)) : GL (Fin 2) ℝ) (p.1 : ℂ) ^ 2)

/-- Auxiliary (§2.1). The cocycle `(cz + d)` of a product: `j(gh, z) = j(g, hz) j(h, z)`. -/
theorem k92t_denom_mul (g h : SL(2, ℝ)) (z : ℍ) :
    UpperHalfPlane.denom ((g * h : SL(2, ℝ)) : GL (Fin 2) ℝ) z =
      UpperHalfPlane.denom (g : GL (Fin 2) ℝ) ((h • z : ℍ) : ℂ) * UpperHalfPlane.denom (h : GL (Fin 2) ℝ) z := by
  have hpos : 0 < ((h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by simp
  rw [map_mul, UpperHalfPlane.denom_cocycle _ _ z.im_ne_zero]
  congr 2
  exact (UpperHalfPlane.coe_smul_of_det_pos hpos z).symm

/-- Auxiliary (§2.1). Multiplying by a central `±1` changes neither the action nor `(cz + d)²`. -/
theorem k92t_center (g z : SL(2, ℝ)) (hz : z ∈ Subgroup.center SL(2, ℝ)) (w : ℍ) :
    (g * z) • w = g • w ∧
      UpperHalfPlane.denom ((g * z : SL(2, ℝ)) : GL (Fin 2) ℝ) w ^ 2 =
        UpperHalfPlane.denom (g : GL (Fin 2) ℝ) w ^ 2 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hd : UpperHalfPlane.denom (z : GL (Fin 2) ℝ) w = r := by
    simp [UpperHalfPlane.denom, ← hrz]
  have hzw : z • w = w := by
    have hpos : 0 < ((z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by simp
    apply UpperHalfPlane.ext
    show ((z : GL (Fin 2) ℝ) • w : ℍ) = (w : ℂ)
    rw [UpperHalfPlane.coe_smul_of_det_pos hpos]
    have hn : UpperHalfPlane.num (z : GL (Fin 2) ℝ) w = r * w := by
      simp [UpperHalfPlane.num, ← hrz]
    have hr0 : (r : ℂ) ≠ 0 := by
      intro h0
      rw [Complex.ofReal_eq_zero] at h0
      rw [h0] at hr2
      norm_num at hr2
    rw [hd, hn]
    field_simp
  refine ⟨by rw [mul_smul, hzw], ?_⟩
  rw [k92t_denom_mul, hzw, hd, mul_pow, ← Complex.ofReal_pow, hr2, Complex.ofReal_one, mul_one]

/-- Auxiliary (§2.1). `g(i, i) = (g i, i/(ci + d)²)` lies in the unit tangent bundle: `|i/(ci + d)²| = Im(g i)`. -/
theorem k92t_mem (g : SL(2, ℝ)) :
    ‖(I : ℂ) / UpperHalfPlane.denom (g : GL (Fin 2) ℝ) I ^ 2‖ = (g • UpperHalfPlane.I).im := by
  have h := UpperHalfPlane.im_smul_eq_div_normSq (g : GL (Fin 2) ℝ) UpperHalfPlane.I
  have hdet : (Matrix.GeneralLinearGroup.det (g : GL (Fin 2) ℝ) : ℝ) = 1 := by simp
  rw [show (g • UpperHalfPlane.I) = (g : GL (Fin 2) ℝ) • UpperHalfPlane.I from rfl, h, hdet, abs_one,
    UpperHalfPlane.I_im, UpperHalfPlane.coe_I, norm_div, norm_pow, Complex.norm_I, ← Complex.normSq_eq_norm_sq]
  ring

/-- Auxiliary (§2.1). `g ↦ g(i, i)` is continuous on SL(2,ℝ). -/
theorem k92t_cont : Continuous fun g : SL(2, ℝ) =>
    ((g • UpperHalfPlane.I : ℍ), (I : ℂ) / UpperHalfPlane.denom (g : GL (Fin 2) ℝ) I ^ 2) := by
  have c : ∀ i j : Fin 2, Continuous fun g : SL(2, ℝ) => g i j := fun i j =>
    (continuous_apply j).comp (Matrix.SpecialLinearGroup.continuous_apply id continuous_id i)
  have hd : Continuous fun g : SL(2, ℝ) => UpperHalfPlane.denom (g : GL (Fin 2) ℝ) I := by
    have e : (fun g : SL(2, ℝ) => UpperHalfPlane.denom (g : GL (Fin 2) ℝ) I) =
        fun g => ((g 1 0 : ℝ) : ℂ) * I + ((g 1 1 : ℝ) : ℂ) := funext fun g => rfl
    rw [e]
    exact ((Complex.continuous_ofReal.comp (c 1 0)).mul continuous_const).add
      (Complex.continuous_ofReal.comp (c 1 1))
  refine (continuous_id.smul continuous_const).prodMk (continuous_const.div (hd.pow 2) fun g => ?_)
  have := UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) UpperHalfPlane.I
  rw [UpperHalfPlane.coe_I] at this
  exact pow_ne_zero _ this

/-- Auxiliary (§2.1). If `g(i, i) = g'(i, i)`, then `g⁻¹g'` fixes `i` and has `j(·, i)² = 1`, so it is `±1`. -/
theorem k92t_inj {g g' : SL(2, ℝ)} (h₁ : g • UpperHalfPlane.I = g' • UpperHalfPlane.I)
    (h₂ : UpperHalfPlane.denom (g : GL (Fin 2) ℝ) I ^ 2 = UpperHalfPlane.denom (g' : GL (Fin 2) ℝ) I ^ 2) :
    g⁻¹ * g' ∈ Subgroup.center SL(2, ℝ) := by
  set h := g⁻¹ * g'
  have hg' : g' = g * h := by simp [h]
  have hI : h • UpperHalfPlane.I = UpperHalfPlane.I := by
    rw [mul_smul, ← h₁, inv_smul_smul]
  have hpos : 0 < (Matrix.GeneralLinearGroup.det (h : GL (Fin 2) ℝ) : ℝ) := by simp
  obtain ⟨e1, e2⟩ := (UpperHalfPlane.gl_smul_I_eq_I_iff_of_pos hpos).1 hI
  have e1' : h 0 0 = h 1 1 := e1
  have e2' : h 0 1 = -h 1 0 := e2
  have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    have := h.2
    rwa [Matrix.det_fin_two] at this
  -- `j(h, i)² = 1`
  have hsq : UpperHalfPlane.denom (h : GL (Fin 2) ℝ) I ^ 2 = 1 := by
    have hg0 := UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) UpperHalfPlane.I
    rw [UpperHalfPlane.coe_I] at hg0
    have := k92t_denom_mul g h UpperHalfPlane.I
    rw [hI, UpperHalfPlane.coe_I, ← hg'] at this
    rw [this, mul_pow] at h₂
    have h3 : UpperHalfPlane.denom (g : GL (Fin 2) ℝ) I ^ 2 *
        (UpperHalfPlane.denom (h : GL (Fin 2) ℝ) I ^ 2 - 1) = 0 := by linear_combination -h₂
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left (pow_ne_zero _ hg0))
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  have hden : UpperHalfPlane.denom (h : GL (Fin 2) ℝ) I = ((h 1 0 : ℝ) : ℂ) * I + ((h 1 1 : ℝ) : ℂ) := rfl
  rw [hden] at hre him
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im] at hre him
  have h10 : h 1 0 = 0 := by
    rw [← e1', e2'] at hdet
    nlinarith
  have h11 : h 1 1 ^ 2 = 1 := by
    rw [h10] at hre
    linear_combination hre
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨h 1 1, by simpa using h11, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp [e1']
  · simp [e2', h10]
  · simp [h10]
  · simp

/-- Auxiliary (§2.1). Every unit tangent vector `(z, ζ)` is `g(i, i)`: `g = toSL2R z · R(θ)` with the rotation
`R(θ)` about `i`, `e^{2iθ} = −iζ/Im z`. -/
theorem k92t_surj (z : ℍ) (ζ : ℂ) (h : ‖ζ‖ = z.im) :
    ∃ g : SL(2, ℝ), g • UpperHalfPlane.I = z ∧ (I : ℂ) / UpperHalfPlane.denom (g : GL (Fin 2) ℝ) I ^ 2 = ζ := by
  set w : ℂ := -I * ζ / z.im with hwdef
  have hy := z.im_pos
  have hw : ‖w‖ = 1 := by
    rw [hwdef, norm_div, norm_mul, norm_neg, Complex.norm_I, one_mul, h, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hy, div_self hy.ne']
  have hexp : Complex.exp (Complex.arg w * I) = w := by
    have := Complex.norm_mul_exp_arg_mul_I w
    rwa [hw, Complex.ofReal_one, one_mul] at this
  set θ := Complex.arg w / 2 with hθ
  set R : SL(2, ℝ) := ⟨!![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ], by
    rw [Matrix.det_fin_two_of]; nlinarith [Real.sin_sq_add_cos_sq θ]⟩
  have hRpos : 0 < (Matrix.GeneralLinearGroup.det (R : GL (Fin 2) ℝ) : ℝ) := by simp
  have hRI : R • UpperHalfPlane.I = UpperHalfPlane.I :=
    (UpperHalfPlane.gl_smul_I_eq_I_iff_of_pos hRpos).2 ⟨rfl, by show Real.sin θ = - -Real.sin θ; ring⟩
  set g₀ := z.toSL2R
  refine ⟨g₀ * R, by rw [mul_smul, hRI, UpperHalfPlane.toSL2R_smul_I], ?_⟩
  have hden := k92t_denom_mul g₀ R UpperHalfPlane.I
  rw [hRI, UpperHalfPlane.coe_I] at hden
  rw [hden]
  have hg₀ : UpperHalfPlane.denom (g₀ : GL (Fin 2) ℝ) I = ((1 / Real.sqrt z.im : ℝ) : ℂ) := by
    show ((g₀ 1 0 : ℝ) : ℂ) * I + ((g₀ 1 1 : ℝ) : ℂ) = _
    simp [g₀]
  have hR : UpperHalfPlane.denom (R : GL (Fin 2) ℝ) I = Complex.exp (((-θ : ℝ) : ℂ) * I) := by
    show ((R 1 0 : ℝ) : ℂ) * I + ((R 1 1 : ℝ) : ℂ) = _
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    simp [R]
    ring
  have hR2 : UpperHalfPlane.denom (R : GL (Fin 2) ℝ) I ^ 2 = w⁻¹ := by
    rw [hR, ← Complex.exp_nat_mul, ← hexp, ← Complex.exp_neg]
    congr 1
    rw [hθ]
    push_cast
    ring
  have hs : ((1 / Real.sqrt z.im : ℝ) : ℂ) ^ 2 = ((z.im : ℝ) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_pow, div_pow, Real.sq_sqrt hy.le, one_pow, one_div, Complex.ofReal_inv]
  rw [mul_pow, hg₀, hs, hR2, hwdef]
  have hy0 : ((z.im : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  have hζ : ζ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h
    exact hy.ne' h.symm
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Auxiliary (§2.1). `{T ∈ PSL(2,ℝ) | T i ∈ K}` is compact for compact `K ⊆ ℍ` (Mathlib's properness of
`g ↦ g i` on SL(2,ℝ), pushed to the quotient). -/
theorem k92t_proper {K : Set ℍ} (hK : IsCompact K) : IsCompact {T : PSL(2, ℝ) | T • UpperHalfPlane.I ∈ K} := by
  have hc : IsCompact ((fun g : SL(2, ℝ) => g • UpperHalfPlane.I) ⁻¹' K) :=
    UpperHalfPlane.isProperMap_smul_I.isCompact_preimage hK
  have e : {T : PSL(2, ℝ) | T • UpperHalfPlane.I ∈ K} =
      (QuotientGroup.mk : SL(2, ℝ) → PSL(2, ℝ)) '' ((fun g : SL(2, ℝ) => g • UpperHalfPlane.I) ⁻¹' K) := by
    ext T
    constructor
    · intro hT
      refine ⟨Quotient.out T, ?_, QuotientGroup.out_eq' T⟩
      show Quotient.out T • UpperHalfPlane.I ∈ K
      rw [← k92_psl_smul_mk, QuotientGroup.out_eq']
      exact hT
    · rintro ⟨g, hg, rfl⟩
      show (g : PSL(2, ℝ)) • UpperHalfPlane.I ∈ K
      rw [k92_psl_smul_mk]
      exact hg
  rw [e]
  exact hc.image QuotientGroup.continuous_mk

/-- **Theorem 2.1.1** (§2.1; l. 681; cited at l. 1711). There is a homeomorphism `PSL(2,ℝ) ≅ Sℍ` under which left
multiplication corresponds to the action on `Sℍ` induced by the action on ℍ. -/
theorem thm2_1_1 : ∃ Φ : PSL(2, ℝ) ≃ₜ unitTangentBundle,
    ∀ S T : PSL(2, ℝ), (Φ (S * T) : ℍ × ℂ) = tangentMap S (Φ T) := by
  -- `Φ(T) = T(i, i)`, computed on SL(2,ℝ) and constant on the cosets of the centre `{±1}`
  set f : SL(2, ℝ) → ℍ × ℂ := fun g =>
    ((g • UpperHalfPlane.I : ℍ), (I : ℂ) / UpperHalfPlane.denom (g : GL (Fin 2) ℝ) I ^ 2) with hfdef
  have hf_out : ∀ g : SL(2, ℝ), f (Quotient.out (g : PSL(2, ℝ))) = f g := fun g => by
    obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center SL(2, ℝ)) g
    obtain ⟨h1, h2⟩ := k92t_center g z z.2 UpperHalfPlane.I
    rw [hz, hfdef]
    simp only [h1, ← UpperHalfPlane.coe_I, h2]
  set F : PSL(2, ℝ) → ℍ × ℂ := fun T => f (Quotient.out T) with hFdef
  have hFmk : ∀ g : SL(2, ℝ), F g = f g := hf_out
  have hFmem : ∀ T, F T ∈ unitTangentBundle := fun T => k92t_mem (Quotient.out T)
  set F' : PSL(2, ℝ) → unitTangentBundle := fun T => ⟨F T, hFmem T⟩ with hF'def
  have hcont : Continuous F' := by
    refine Continuous.subtype_mk ?_ _
    rw [(QuotientGroup.isQuotientMap_mk (Subgroup.center SL(2, ℝ))).continuous_iff]
    have e : F ∘ (QuotientGroup.mk : SL(2, ℝ) → PSL(2, ℝ)) = f := funext hFmk
    rw [e]
    exact k92t_cont
  have hinj : Function.Injective F' := by
    intro S T hST
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective S
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective T
    have e := congrArg Subtype.val hST
    simp only [hF'def, hFmk, hfdef, Prod.mk.injEq] at e
    have hd : UpperHalfPlane.denom (g : GL (Fin 2) ℝ) I ^ 2 = UpperHalfPlane.denom (h : GL (Fin 2) ℝ) I ^ 2 := by
      have h0 := e.2
      have hg := UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) UpperHalfPlane.I
      have hh := UpperHalfPlane.denom_ne_zero (h : GL (Fin 2) ℝ) UpperHalfPlane.I
      rw [UpperHalfPlane.coe_I] at hg hh
      field_simp at h0
      exact h0.symm
    exact QuotientGroup.eq.2 (k92t_inj e.1 hd)
  have hsurj : Function.Surjective F' := by
    rintro ⟨⟨z, ζ⟩, hp⟩
    obtain ⟨g, hg1, hg2⟩ := k92t_surj z ζ hp
    exact ⟨g, Subtype.ext (by rw [hF'def]; simp only [hFmk, hfdef, hg1, hg2])⟩
  -- a continuous bijection with compact preimages of compacts is closed (Sℍ is Hausdorff, compactly generated)
  have hclosed : IsClosedMap F' := by
    refine (isProperMap_iff_isCompact_preimage.2 ⟨hcont, fun K hK => ?_⟩).isClosedMap
    have hK' : IsCompact (Prod.fst '' ((↑) '' K : Set (ℍ × ℂ))) :=
      (hK.image continuous_subtype_val).image continuous_fst
    refine (k92t_proper hK').of_isClosed_subset (hK.isClosed.preimage hcont) ?_
    intro T hT
    refine ⟨(F' T : ℍ × ℂ), ⟨F' T, hT, rfl⟩, ?_⟩
    show Quotient.out T • UpperHalfPlane.I = T • UpperHalfPlane.I
    conv_rhs => rw [← QuotientGroup.out_eq' T]
    rw [k92_psl_smul_mk]
  -- equivariance: `j(gh, i) = j(g, h i) j(h, i)`
  have key : ∀ S T : PSL(2, ℝ), F (S * T) = tangentMap S (F T) := by
    intro S T
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective S
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective T
    rw [← QuotientGroup.mk_mul, hFmk, hFmk]
    obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center SL(2, ℝ)) g
    have hg := UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) (h • UpperHalfPlane.I)
    have hh := UpperHalfPlane.denom_ne_zero (h : GL (Fin 2) ℝ) UpperHalfPlane.I
    rw [UpperHalfPlane.coe_I] at hh
    simp only [tangentMap, hfdef, hz, (k92t_center g z z.2 _).2, k92_psl_smul_mk, mul_smul]
    rw [← UpperHalfPlane.coe_I, k92t_denom_mul, UpperHalfPlane.coe_I]
    congr 1
    field_simp
  exact ⟨(Equiv.ofBijective F' ⟨hinj, hsurj⟩).toHomeomorphOfContinuousClosed hcont hclosed, key⟩

/-- **Unlabelled** (§2.1; l. 711, "as follows from Exercise 2.5"). Γ is discrete iff `T_n → Id`, `T_n ∈ Γ` implies
`T_n = Id` for large `n`.
Modelling: stated for subgroups of PSL(2,ℝ) (all later uses). -/
theorem discreteTopology_iff_tendsto_one (Γ : Subgroup PSL(2, ℝ)) :
    DiscreteTopology Γ ↔ ∀ T : ℕ → PSL(2, ℝ), (∀ n, T n ∈ Γ) → Tendsto T atTop (𝓝 1) →
      ∀ᶠ n in atTop, T n = 1 := by
  constructor
  · intro hd T hT hlim
    have hlim' : Tendsto (fun n => (⟨T n, hT n⟩ : Γ)) atTop (𝓝 1) := tendsto_subtype_rng.2 hlim
    have h1 : ({1} : Set Γ) ∈ 𝓝 (1 : Γ) := (isOpen_discrete _).mem_nhds rfl
    filter_upwards [hlim' h1] with n hn
    exact congrArg Subtype.val (Set.mem_singleton_iff.1 hn)
  · intro h
    -- PSL(2,ℝ) is first countable (a quotient of SL(2,ℝ) ⊆ ℝ⁴), so `1` would be a limit of `Tₙ ≠ 1` in Γ
    have hSL : FirstCountableTopology SL(2, ℝ) :=
      TopologicalSpace.firstCountableTopology_induced _ (Fin 2 → Fin 2 → ℝ)
        (fun g : SL(2, ℝ) => (g : Matrix (Fin 2) (Fin 2) ℝ))
    have hPSL : FirstCountableTopology PSL(2, ℝ) := inferInstance
    have hΓ : FirstCountableTopology Γ :=
      TopologicalSpace.firstCountableTopology_induced _ PSL(2, ℝ) (fun g : Γ => (g : PSL(2, ℝ)))
    rw [discreteTopology_iff_isOpen_singleton_one]
    by_contra hno
    have hfreq : ∃ᶠ x in 𝓝 (1 : Γ), x ≠ 1 := by
      rw [Filter.Frequently]
      intro hev
      apply hno
      rw [isOpen_iff_mem_nhds]
      intro x hx
      rw [Set.mem_singleton_iff.1 hx]
      filter_upwards [hev] with y hy
      exact not_not.1 hy
    have hne : (𝓝 (1 : Γ) ⊓ 𝓟 {x | x ≠ 1}).NeBot := Filter.frequently_iff_neBot.1 hfreq
    obtain ⟨x, hx⟩ := Filter.exists_seq_tendsto (𝓝 (1 : Γ) ⊓ 𝓟 {x | x ≠ 1})
    have hx1 : Tendsto x atTop (𝓝 1) := hx.mono_right inf_le_left
    have hx2 : ∀ᶠ n in atTop, x n ≠ 1 := tendsto_principal.1 (hx.mono_right inf_le_right)
    have hev := h (fun n => (x n : PSL(2, ℝ))) (fun n => (x n).2)
      (continuous_subtype_val.continuousAt.tendsto.comp hx1)
    obtain ⟨n, hn1, hn2⟩ := (hev.and hx2).exists
    exact hn2 (Subtype.ext hn1)

end Katok1992
