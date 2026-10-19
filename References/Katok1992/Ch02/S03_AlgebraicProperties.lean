import References.Katok1992.Ch02.S02_DiscreteAndProperlyDiscontinuousGroups

/-!
# Katok 1992, Ch. 2 §2.3 Algebraic properties of Fuchsian groups

S. Katok, *Fuchsian Groups* (1992), Chapter 2 *Fuchsian Groups*, §2.3; source `full.md` of
`Fuchsian groups (Katok, Svetlana) …-3766f6b7…`, lines 863–915.

* Definition (the centralizer `C_G(g)`, l. 865–869) — exists: `Subgroup.centralizer` `Subgroup.mem_centralizer_iff`
  (applied to the singleton {g})
* Lemma 2.3.1 (l. 871; cited at l. 1657) — exists: `MulAction.fixedBy_mem_fixedBy_of_commute` (for any action, here
  on Hbar: if T and S commute, S maps the fixed-point set of T onto itself)
* Theorem 2.3.2 (l. 889; cited at l. 903, 915, 3021) — `thm2_3_2`
* Theorem 2.3.3 (l. 891; cited at l. 2619) — `thm2_3_3_a`, `thm2_3_3_b`, `thm2_3_3_c`
* Corollary 2.3.4 (l. 893) — `cor2_3_4`
* Unlabelled (l. 895: `Tr(S⁻¹TS) = Tr(T)`; cited at l. 1021, 1594) — `tr_conj`
* Theorem 2.3.5 (l. 897; cited at l. 903, 929, 943) — `thm2_3_5`
* Theorem 2.3.6 (l. 901; cited at l. 945) — `thm2_3_6`
* Corollary 2.3.7 (l. 905; cited at l. 1709) — `cor2_3_7`
* Definition (the normalizer `N_G(H)`, l. 907–911) — exists: `Subgroup.normalizer` `Subgroup.mem_normalizer_iff`
* Theorem 2.3.8 (l. 913) — `thm2_3_8`

Not items (DESIGN §3): the centralizer computations for `z + 1`, `e^{iθ}z` (disc) and `μz` (l. 881–887; steps of the
proofs); "the type is invariant under conjugation" (l. 895; immediate from `tr_conj` and the definitions); the
exercises.

**Conventions.** As in §2.1–§2.2. Fixed-point sets are `MulAction.fixedBy Hbar T` on `ℍ̃ = ℍ ⊕ OnePoint ℝ`.
-/

open Complex Set Metric Filter Topology
open scoped UpperHalfPlane MatrixGroups

noncomputable section

namespace Katok1992

/-- Auxiliary (§2.3). A non-identity element of PSL(2,ℝ) is elliptic, parabolic or hyperbolic. -/
theorem k92f_trichotomy {T : PSL(2, ℝ)} (hT : T ≠ 1) : IsElliptic T ∨ IsParabolic T ∨ IsHyperbolic T := by
  rcases lt_trichotomy (Tr T) 2 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h, hT⟩)
  · exact Or.inr (Or.inr h)

/-- Auxiliary (§2.3). A hyperbolic element is not the identity (its fixed-point set is not all of ℍ̃). -/
theorem k92f_ne_one_of_hyp {T : PSL(2, ℝ)} (hT : IsHyperbolic T) : T ≠ 1 := by
  obtain ⟨α, β, -, hfix⟩ := fixedBy_of_isHyperbolic hT
  rintro rfl
  have : (Sum.inl UpperHalfPlane.I : Hbar) ∈ MulAction.fixedBy Hbar (1 : PSL(2, ℝ)) := by
    rw [MulAction.fixedBy_one_eq_univ]; trivial
  rw [hfix] at this
  rcases this with h | h <;> cases h

/-- Auxiliary (§2.3). An elliptic element is not the identity. -/
theorem k92f_ne_one_of_ell {T : PSL(2, ℝ)} (hT : IsElliptic T) : T ≠ 1 := by
  obtain ⟨p, hfix⟩ := fixedBy_of_isElliptic hT
  rintro rfl
  have : (Sum.inr OnePoint.infty : Hbar) ∈ MulAction.fixedBy Hbar (1 : PSL(2, ℝ)) := by
    rw [MulAction.fixedBy_one_eq_univ]; trivial
  rw [hfix] at this
  cases this

/-- Auxiliary (§2.3). The shape of the fixed-point set of a non-identity element determines its type: two boundary
points (hyperbolic), one boundary point (parabolic), one point of ℍ (elliptic). -/
theorem k92f_shape {U : PSL(2, ℝ)} (hU : U ≠ 1) :
    (IsHyperbolic U ↔ ∃ α β : OnePoint ℝ, α ≠ β ∧ MulAction.fixedBy Hbar U = {Sum.inr α, Sum.inr β}) ∧
      (IsParabolic U ↔ ∃ α : OnePoint ℝ, MulAction.fixedBy Hbar U = {Sum.inr α}) ∧
      (IsElliptic U ↔ ∃ p : ℍ, MulAction.fixedBy Hbar U = {Sum.inl p}) := by
  -- the three shapes are pairwise different
  have d1 : ∀ (α β γ : OnePoint ℝ), α ≠ β →
      ({Sum.inr α, Sum.inr β} : Set Hbar) ≠ {Sum.inr γ} := fun α β γ hαβ h => by
    have ha : (Sum.inr α : Hbar) ∈ ({Sum.inr γ} : Set Hbar) := h ▸ Set.mem_insert _ _
    have hb : (Sum.inr β : Hbar) ∈ ({Sum.inr γ} : Set Hbar) := h ▸ Set.mem_insert_of_mem _ rfl
    exact hαβ ((Sum.inr.inj (Set.mem_singleton_iff.1 ha)).trans (Sum.inr.inj (Set.mem_singleton_iff.1 hb)).symm)
  have d2 : ∀ (α β : OnePoint ℝ) (p : ℍ), ({Sum.inr α, Sum.inr β} : Set Hbar) ≠ {Sum.inl p} := fun α β p h => by
    have ha : (Sum.inr α : Hbar) ∈ ({Sum.inl p} : Set Hbar) := h ▸ Set.mem_insert _ _
    cases ha
  have d3 : ∀ (α : OnePoint ℝ) (p : ℍ), ({Sum.inr α} : Set Hbar) ≠ {Sum.inl p} := fun α p h => by
    have ha : (Sum.inr α : Hbar) ∈ ({Sum.inl p} : Set Hbar) := h ▸ Set.mem_singleton _
    cases ha
  rcases k92f_trichotomy hU with he | hp | hh
  · obtain ⟨p, hfix⟩ := fixedBy_of_isElliptic he
    have nH : ¬ IsHyperbolic U := fun h => lt_asymm h he
    have nP : ¬ IsParabolic U := fun h => (ne_of_lt he) h.1
    refine ⟨⟨fun h => absurd h nH, ?_⟩, ⟨fun h => absurd h nP, ?_⟩, ⟨fun _ => ⟨p, hfix⟩, fun _ => he⟩⟩
    · rintro ⟨α, β, -, h⟩; exact absurd (h.symm.trans hfix) (d2 α β p)
    · rintro ⟨α, h⟩; exact absurd (h.symm.trans hfix) (d3 α p)
  · obtain ⟨α, hfix⟩ := fixedBy_of_isParabolic hp
    have nH : ¬ IsHyperbolic U := fun h => (ne_of_gt h) hp.1
    have nE : ¬ IsElliptic U := fun h => (ne_of_lt h) hp.1
    refine ⟨⟨fun h => absurd h nH, ?_⟩, ⟨fun _ => ⟨α, hfix⟩, fun _ => hp⟩, ⟨fun h => absurd h nE, ?_⟩⟩
    · rintro ⟨β, γ, hβγ, h⟩; exact absurd (h.symm.trans hfix) (d1 β γ α hβγ)
    · rintro ⟨q, h⟩; exact absurd (hfix.symm.trans h) (d3 α q)
  · obtain ⟨α, β, hαβ, hfix⟩ := fixedBy_of_isHyperbolic hh
    have nP : ¬ IsParabolic U := fun h => (ne_of_gt hh) h.1
    have nE : ¬ IsElliptic U := fun h => lt_asymm h hh
    refine ⟨⟨fun _ => ⟨α, β, hαβ, hfix⟩, fun _ => hh⟩, ⟨fun h => absurd h nP, ?_⟩, ⟨fun h => absurd h nE, ?_⟩⟩
    · rintro ⟨γ, h⟩; exact absurd (hfix.symm.trans h) (d1 α β γ hαβ)
    · rintro ⟨q, h⟩; exact absurd (hfix.symm.trans h) (d2 α β q)

/-- Auxiliary (§2.3). If `Tr T > 0`, then `T²` has the same fixed points as `T`: by Cayley–Hamilton `t² = τ t − 1`,
so the fixed-point equations of `t²` are those of `t` multiplied by `τ ≠ 0`. -/
theorem k92f_fix_sq {T : PSL(2, ℝ)} (hT : 0 < Tr T) :
    MulAction.fixedBy Hbar (T * T) = MulAction.fixedBy Hbar T := by
  obtain ⟨hgT, hTr⟩ := k92n_Tr_out T
  set t := Quotient.out T
  have hτ : t 0 0 + t 1 1 ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hTr
    rw [hTr] at hT
    exact lt_irrefl _ hT
  have e10 : (t * t : SL(2, ℝ)) 1 0 = (t 0 0 + t 1 1) * t 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  have e01 : (t * t : SL(2, ℝ)) 0 1 = (t 0 0 + t 1 1) * t 0 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  have e00 : (t * t : SL(2, ℝ)) 0 0 = t 0 0 * t 0 0 + t 0 1 * t 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (t * t : SL(2, ℝ)) 1 1 = t 1 0 * t 0 1 + t 1 1 * t 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hG : ∀ (g : SL(2, ℝ)) (i j : Fin 2),
      ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = g i j :=
    fun _ _ _ => rfl
  have hpos : ∀ g : SL(2, ℝ), 0 < ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det := fun g => by simp
  have hpoly : ∀ (g : SL(2, ℝ)) (r : ℝ),
      (Matrix.SpecialLinearGroup.mapGL ℝ g) • (r : OnePoint ℝ) = r ↔ g 1 0 * r ^ 2 + (g 1 1 - g 0 0) * r - g 0 1 = 0 :=
    fun g r => by
      rw [← Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff]
      simp only [Matrix.GeneralLinearGroup.fixpointPolynomial, map_sub, map_add, map_mul, Polynomial.aeval_C,
        Polynomial.aeval_X_pow, Polynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply, hG]
  have hτC : ((t 0 0 + t 1 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hτ
  rw [← hgT, ← QuotientGroup.mk_mul, k92n_fixedBy, k92n_fixedBy]
  congr 2
  · ext z
    simp only [Set.mem_ofPred_eq]
    rw [UpperHalfPlane.gl_smul_eq_self_iff_quadratic (hpos _), UpperHalfPlane.gl_smul_eq_self_iff_quadratic (hpos _)]
    simp only [hG, e10, e01, e00, e11]
    have : ∀ w : ℂ, ((((t 0 0 + t 1 1) * t 1 0 : ℝ) : ℂ) * w + (((t 1 0 * t 0 1 + t 1 1 * t 1 1 : ℝ) : ℂ) -
        ((t 0 0 * t 0 0 + t 0 1 * t 1 0 : ℝ) : ℂ)) * z + -((((t 0 0 + t 1 1) * t 0 1 : ℝ) : ℂ))) =
        ((t 0 0 + t 1 1 : ℝ) : ℂ) * ((t 1 0 : ℂ) * w + ((t 1 1 : ℂ) - (t 0 0 : ℂ)) * z + -(t 0 1 : ℂ)) :=
      fun w => by push_cast; ring
    rw [this, mul_eq_zero, or_iff_right hτC]
  · ext x
    simp only [Set.mem_ofPred_eq]
    induction x using OnePoint.rec with
    | infty =>
      rw [OnePoint.smul_infty_eq_self_iff, OnePoint.smul_infty_eq_self_iff, hG, hG, e10, mul_eq_zero,
        or_iff_right hτ]
    | coe r =>
      rw [hpoly, hpoly, e10, e01, e00, e11]
      have : (t 0 0 + t 1 1) * t 1 0 * r ^ 2 + (t 1 0 * t 0 1 + t 1 1 * t 1 1 - (t 0 0 * t 0 0 + t 0 1 * t 1 0)) * r -
          (t 0 0 + t 1 1) * t 0 1 = (t 0 0 + t 1 1) * (t 1 0 * r ^ 2 + (t 1 1 - t 0 0) * r - t 0 1) := by ring
      rw [this, mul_eq_zero, or_iff_right hτ]

/-- Auxiliary. A two-element subset of a two-element set is the whole set. -/
theorem k92f_pair_sub {a b c d : Hbar} (hab : a ≠ b) (ha : a ∈ ({c, d} : Set Hbar)) (hb : b ∈ ({c, d} : Set Hbar)) :
    ({a, b} : Set Hbar) = {c, d} := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · rfl
  · exact Set.pair_comm _ _
  · exact absurd rfl hab

/-- Auxiliary. A two-point set `{inr α, inr β}` containing `c` is `{c, e}` for some `e ≠ c`. -/
theorem k92f_pair_other {α β : OnePoint ℝ} (hαβ : α ≠ β) {c : Hbar} (hc : c ∈ ({Sum.inr α, Sum.inr β} : Set Hbar)) :
    ∃ e : Hbar, ({Sum.inr α, Sum.inr β} : Set Hbar) = {c, e} ∧ e ≠ c := by
  rcases hc with rfl | rfl
  · exact ⟨Sum.inr β, rfl, fun h => hαβ (Sum.inr.inj h).symm⟩
  · exact ⟨Sum.inr α, Set.pair_comm _ _, fun h => hαβ (Sum.inr.inj h)⟩

/-- Auxiliary. Membership in the fixed-point set of `±g`, on ℍ and on `ℝ ∪ {∞}`. -/
theorem k92f_mem_fix (g : SL(2, ℝ)) :
    (∀ z : ℍ, (Sum.inl z : Hbar) ∈ MulAction.fixedBy Hbar (g : PSL(2, ℝ)) ↔
      Matrix.SpecialLinearGroup.mapGL ℝ g • z = z) ∧
    (∀ x : OnePoint ℝ, (Sum.inr x : Hbar) ∈ MulAction.fixedBy Hbar (g : PSL(2, ℝ)) ↔
      Matrix.SpecialLinearGroup.mapGL ℝ g • x = x) := by
  rw [k92n_fixedBy]
  constructor
  · intro z
    simp
  · intro x
    simp

/-- Auxiliary. Conjugation carries equal fixed-point sets to equal fixed-point sets. -/
theorem k92f_fix_conj {A B : PSL(2, ℝ)} (C : PSL(2, ℝ))
    (h : MulAction.fixedBy Hbar A = MulAction.fixedBy Hbar B) :
    MulAction.fixedBy Hbar (C * A * C⁻¹) = MulAction.fixedBy Hbar (C * B * C⁻¹) := by
  have e : ∀ D : PSL(2, ℝ), ∀ x : Hbar, x ∈ MulAction.fixedBy Hbar (C * D * C⁻¹) ↔
      C⁻¹ • x ∈ MulAction.fixedBy Hbar D := fun D x => by
    show (C * D * C⁻¹) • x = x ↔ D • C⁻¹ • x = C⁻¹ • x
    rw [mul_smul, mul_smul, ← eq_inv_smul_iff]
  ext x
  rw [e, e, h]

/-- Auxiliary. Two matrices of SL(2,ℝ) fixing `i` (rotations) commute. -/
theorem k92f_comm_of_fix_I {A B : SL(2, ℝ)} (hA : A • UpperHalfPlane.I = UpperHalfPlane.I)
    (hB : B • UpperHalfPlane.I = UpperHalfPlane.I) : A * B = B * A := by
  have hpos : ∀ g : SL(2, ℝ), 0 < (Matrix.GeneralLinearGroup.det (g : GL (Fin 2) ℝ) : ℝ) := fun g => by simp
  obtain ⟨a1, a2⟩ := (UpperHalfPlane.gl_smul_I_eq_I_iff_of_pos (hpos A)).1 hA
  obtain ⟨b1, b2⟩ := (UpperHalfPlane.gl_smul_I_eq_I_iff_of_pos (hpos B)).1 hB
  have a1' : A 0 0 = A 1 1 := a1
  have a2' : A 0 1 = -A 1 0 := a2
  have b1' : B 0 0 = B 1 1 := b1
  have b2' : B 0 1 = -B 1 0 := b2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, a1', a2', b1', b2'] <;> ring

/-- Auxiliary. Two diagonal matrices commute. -/
theorem k92f_comm_of_diag {A B : SL(2, ℝ)} (hA : A 1 0 = 0 ∧ A 0 1 = 0) (hB : B 1 0 = 0 ∧ B 0 1 = 0) :
    A * B = B * A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hA.1, hA.2, hB.1, hB.2] <;> ring

/-- Auxiliary. Two matrices `[[a, b], [0, a]]` commute. -/
theorem k92f_comm_of_upper {A B : SL(2, ℝ)} (hA : A 1 0 = 0 ∧ A 0 0 = A 1 1) (hB : B 1 0 = 0 ∧ B 0 0 = B 1 1) :
    A * B = B * A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hA.1, hA.2, hB.1, hB.2] <;> ring

/-- Auxiliary. A matrix whose only fixed point in ℍ̃ is `∞` is `[[a, b], [0, a]]`. -/
theorem k92f_fix_infty_only (g : SL(2, ℝ))
    (h : MulAction.fixedBy Hbar (g : PSL(2, ℝ)) = {Sum.inr OnePoint.infty}) : g 1 0 = 0 ∧ g 0 0 = g 1 1 := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2
    rwa [Matrix.det_fin_two] at this
  have hc : g 1 0 = 0 := by
    have h1 : (Sum.inr OnePoint.infty : Hbar) ∈ MulAction.fixedBy Hbar (g : PSL(2, ℝ)) := h ▸ Set.mem_singleton _
    rw [(k92f_mem_fix g).2, OnePoint.smul_infty_eq_self_iff] at h1
    exact h1
  refine ⟨hc, ?_⟩
  by_contra had
  -- otherwise `b/(d − a)` is a second fixed point
  rw [hc, mul_zero, sub_zero] at hdet
  have hd : g 1 1 ≠ 0 := fun h0 => by rw [h0, mul_zero] at hdet; exact zero_ne_one hdet
  set x₀ := g 0 1 / (g 1 1 - g 0 0)
  have hda : g 1 1 - g 0 0 ≠ 0 := sub_ne_zero.2 (Ne.symm had)
  have hfix : (Sum.inr (x₀ : OnePoint ℝ) : Hbar) ∈ MulAction.fixedBy Hbar (g : PSL(2, ℝ)) := by
    rw [(k92f_mem_fix g).2, OnePoint.smul_some_eq_ite]
    show (if g 1 0 * x₀ + g 1 1 = 0 then OnePoint.infty else (((g 0 0 * x₀ + g 0 1) / (g 1 0 * x₀ + g 1 1) : ℝ) :
      OnePoint ℝ)) = x₀
    rw [hc, zero_mul, zero_add, ite_eq_right hd, OnePoint.coe_eq_coe, div_eq_iff hd]
    simp only [x₀]
    field_simp
    ring
  rw [h] at hfix
  exact OnePoint.coe_ne_infty x₀ (Sum.inr.inj hfix)

/-- Auxiliary. `±g` fixes `0` and `∞` iff `g` is diagonal. -/
theorem k92f_fix_zero_infty (g : SL(2, ℝ)) :
    ((Sum.inr OnePoint.infty : Hbar) ∈ MulAction.fixedBy Hbar (g : PSL(2, ℝ)) ∧
      (Sum.inr ((0 : ℝ) : OnePoint ℝ) : Hbar) ∈ MulAction.fixedBy Hbar (g : PSL(2, ℝ))) ↔
      g 1 0 = 0 ∧ g 0 1 = 0 := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2
    rwa [Matrix.det_fin_two] at this
  rw [(k92f_mem_fix g).2, (k92f_mem_fix g).2, OnePoint.smul_infty_eq_self_iff, OnePoint.smul_some_eq_ite]
  show (g 1 0 = 0 ∧ (if g 1 0 * 0 + g 1 1 = 0 then OnePoint.infty else
      (((g 0 0 * 0 + g 0 1) / (g 1 0 * 0 + g 1 1) : ℝ) : OnePoint ℝ)) = ((0 : ℝ) : OnePoint ℝ)) ↔ _
  constructor
  · rintro ⟨hc, h0⟩
    refine ⟨hc, ?_⟩
    rw [hc, mul_zero, sub_zero] at hdet
    have hd : g 1 1 ≠ 0 := fun h => by rw [h, mul_zero] at hdet; exact zero_ne_one hdet
    rw [mul_zero, zero_add, ite_eq_right hd, OnePoint.coe_eq_coe, mul_zero, zero_add,
      div_eq_zero_iff] at h0
    exact h0.resolve_right hd
  · rintro ⟨hc, hb⟩
    refine ⟨hc, ?_⟩
    rw [hc, mul_zero, sub_zero] at hdet
    have hd : g 1 1 ≠ 0 := fun h => by rw [h, mul_zero] at hdet; exact zero_ne_one hdet
    rw [mul_zero, zero_add, ite_eq_right hd, OnePoint.coe_eq_coe, mul_zero, zero_add, hb, zero_div]

/-- Auxiliary (§1.2). The geodesic between two boundary points described explicitly: a vertical line `Re = x` (one
end `∞`) or the semicircle `(Re − x)(y − Re) = Im²` over `[x, y]`. -/
theorem k92f_geodArc_cases {α β : OnePoint ℝ} (h : α ≠ β) :
    (∃ x : ℝ, ({α, β} : Set (OnePoint ℝ)) = {OnePoint.infty, (x : OnePoint ℝ)} ∧
      ∀ ξ : ℍ, ξ ∈ geodArc (boundaryToExt α) (boundaryToExt β) ↔ ξ.re = x) ∨
    (∃ x y : ℝ, x ≠ y ∧ ({α, β} : Set (OnePoint ℝ)) = {(x : OnePoint ℝ), (y : OnePoint ℝ)} ∧
      ∀ ξ : ℍ, ξ ∈ geodArc (boundaryToExt α) (boundaryToExt β) ↔ (ξ.re - x) * (y - ξ.re) = ξ.im ^ 2) := by
  induction α using OnePoint.rec with
  | infty =>
    induction β using OnePoint.rec with
    | infty => exact absurd rfl h
    | coe y => exact Or.inl ⟨y, rfl, fun ξ => (k92g_geodArc_inf y ξ).1⟩
  | coe x =>
    induction β using OnePoint.rec with
    | infty => exact Or.inl ⟨x, Set.pair_comm _ _, fun ξ => (k92g_geodArc_inf x ξ).2⟩
    | coe y =>
      have hxy : x ≠ y := fun e => h (by rw [e])
      exact Or.inr ⟨x, y, hxy, rfl, fun ξ => k92g_geodArc_real hxy ξ⟩

/-- Auxiliary (§1.2). The geodesic between two boundary points does not depend on their order. -/
theorem k92f_geodArc_symm (α β : OnePoint ℝ) :
    geodArc (boundaryToExt α) (boundaryToExt β) = geodArc (boundaryToExt β) (boundaryToExt α) := by
  rcases eq_or_ne α β with rfl | h
  · rfl
  ext ξ
  rcases k92f_geodArc_cases h with ⟨x, hp, hx⟩ | ⟨x, y, hxy, hp, hx⟩
  · rcases k92f_geodArc_cases h.symm with ⟨x', hp', hx'⟩ | ⟨x', y', hxy', hp', hx'⟩
    · rw [hx, hx']
      rw [Set.pair_comm] at hp'
      rw [hp] at hp'
      have : (x : OnePoint ℝ) = x' := by
        have hmem : ((x : OnePoint ℝ)) ∈ ({OnePoint.infty, (x' : OnePoint ℝ)} : Set (OnePoint ℝ)) := hp' ▸ by simp
        rcases hmem with h0 | h0
        · exact absurd h0 (OnePoint.coe_ne_infty x)
        · exact h0
      rw [OnePoint.coe_eq_coe.1 this]
    · rw [Set.pair_comm, hp] at hp'
      have hmem : (OnePoint.infty : OnePoint ℝ) ∈ ({(x' : OnePoint ℝ), (y' : OnePoint ℝ)} : Set (OnePoint ℝ)) :=
        hp' ▸ by simp
      rcases hmem with h0 | h0 <;> exact absurd h0.symm (OnePoint.coe_ne_infty _)
  · rcases k92f_geodArc_cases h.symm with ⟨x', hp', hx'⟩ | ⟨x', y', hxy', hp', hx'⟩
    · rw [Set.pair_comm, hp'] at hp
      have hmem : (OnePoint.infty : OnePoint ℝ) ∈ ({(x : OnePoint ℝ), (y : OnePoint ℝ)} : Set (OnePoint ℝ)) :=
        hp ▸ by simp
      rcases hmem with h0 | h0 <;> exact absurd h0.symm (OnePoint.coe_ne_infty _)
    · rw [hx, hx']
      rw [Set.pair_comm, hp] at hp'
      rw [Set.pair_eq_pair_iff] at hp'
      rcases hp' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [OnePoint.coe_eq_coe.1 h1, OnePoint.coe_eq_coe.1 h2]
      · rw [OnePoint.coe_eq_coe.1 h1, OnePoint.coe_eq_coe.1 h2]
        constructor <;> intro e <;> linarith

/-- Auxiliary (§2.3, Lemma 2.3.1 and the classification of fixed points): commuting non-identity elements have the
same fixed-point set. -/
theorem k92f_fix_eq_of_commute {S T : PSL(2, ℝ)} (hS : S ≠ 1) (hT : T ≠ 1) (h : S * T = T * S) :
    MulAction.fixedBy Hbar S = MulAction.fixedBy Hbar T := by
  -- each maps the other's fixed-point set into itself (Lemma 2.3.1)
  have hmap : ∀ {A B : PSL(2, ℝ)}, A * B = B * A → ∀ x ∈ MulAction.fixedBy Hbar A,
      B • x ∈ MulAction.fixedBy Hbar A := fun {A B} hAB x hx => by
    show A • B • x = B • x
    rw [← mul_smul, hAB, mul_smul, hx]
  have hST := hmap h.symm
  have hTS := hmap h
  have hfixed : ∀ {A : PSL(2, ℝ)} {x : Hbar}, x ∈ MulAction.fixedBy Hbar A → A • x = x := fun hx => hx
  rcases k92f_trichotomy hT with hTe | hTp | hTh
  · -- `T` elliptic, `Fix T = {p}`: `S` fixes `p`, so `S` is elliptic with fixed point `p`
    obtain ⟨p, hp⟩ := (k92f_shape hT).2.2.1 hTe
    have hpS : (Sum.inl p : Hbar) ∈ MulAction.fixedBy Hbar S := by
      have := hST _ (hp ▸ Set.mem_singleton _)
      rw [hp] at this
      exact this
    rcases k92f_trichotomy hS with hSe | hSp | hSh
    · obtain ⟨q, hq⟩ := (k92f_shape hS).2.2.1 hSe
      rw [hq] at hpS ⊢
      rw [hp, Set.mem_singleton_iff.1 hpS]
    · obtain ⟨γ, hγ⟩ := (k92f_shape hS).2.1.1 hSp
      rw [hγ] at hpS
      cases hpS
    · obtain ⟨γ, δ, -, hγ⟩ := (k92f_shape hS).1.1 hSh
      rw [hγ] at hpS
      rcases hpS with h0 | h0 <;> cases h0
  · -- `T` parabolic, `Fix T = {α}`: `S` fixes `α`
    obtain ⟨α, hα⟩ := (k92f_shape hT).2.1.1 hTp
    have hαS : (Sum.inr α : Hbar) ∈ MulAction.fixedBy Hbar S := by
      have := hST _ (hα ▸ Set.mem_singleton _)
      rw [hα] at this
      exact this
    rcases k92f_trichotomy hS with hSe | hSp | hSh
    · obtain ⟨q, hq⟩ := (k92f_shape hS).2.2.1 hSe
      rw [hq] at hαS
      cases hαS
    · obtain ⟨γ, hγ⟩ := (k92f_shape hS).2.1.1 hSp
      rw [hγ] at hαS ⊢
      rw [hα, Set.mem_singleton_iff.1 hαS]
    · -- a hyperbolic `S` with `Fix S = {α, e}`: `T e` would be `α = T α` or `e ∈ Fix T`
      exfalso
      obtain ⟨γ, δ, hγδ, hγ⟩ := (k92f_shape hS).1.1 hSh
      rw [hγ] at hαS
      obtain ⟨e, he, heα⟩ := k92f_pair_other hγδ hαS
      rw [he] at hγ
      have hTe : T • e ∈ ({Sum.inr α, e} : Set Hbar) := hγ ▸ hTS e (hγ ▸ Set.mem_insert_of_mem _ rfl)
      have hαT : T • (Sum.inr α : Hbar) = Sum.inr α := hfixed (hα ▸ Set.mem_singleton _)
      rcases hTe with h0 | h0
      · exact heα (smul_left_cancel T (h0.trans hαT.symm))
      · have : e ∈ MulAction.fixedBy Hbar T := h0
        rw [hα] at this
        exact heα this
  · -- `T` hyperbolic, `Fix T = {α, β}`
    obtain ⟨α, β, hαβ, hab⟩ := (k92f_shape hT).1.1 hTh
    rcases k92f_trichotomy hS with hSe | hSp | hSh
    · -- `T` would fix the fixed point of `S` in ℍ
      exfalso
      obtain ⟨q, hq⟩ := (k92f_shape hS).2.2.1 hSe
      have h1 := hTS _ (hq ▸ Set.mem_singleton _)
      rw [hq] at h1
      have h2 : (Sum.inl q : Hbar) ∈ MulAction.fixedBy Hbar T := Set.mem_singleton_iff.1 h1
      rw [hab] at h2
      rcases h2 with h0 | h0 <;> cases h0
    · -- `Fix S = {γ}` with `γ ∈ Fix T = {γ, e}`: `S e` would be `γ = S γ` or `e ∈ Fix S`
      exfalso
      obtain ⟨γ, hγ⟩ := (k92f_shape hS).2.1.1 hSp
      have h1 := hTS _ (hγ ▸ Set.mem_singleton _)
      rw [hγ] at h1
      have h2 : (Sum.inr γ : Hbar) ∈ MulAction.fixedBy Hbar T := Set.mem_singleton_iff.1 h1
      rw [hab] at h2
      obtain ⟨e, he, heγ⟩ := k92f_pair_other hαβ h2
      rw [he] at hab
      have hSe : S • e ∈ ({Sum.inr γ, e} : Set Hbar) := hab ▸ hST e (hab ▸ Set.mem_insert_of_mem _ rfl)
      have hγS : S • (Sum.inr γ : Hbar) = Sum.inr γ := hfixed (hγ ▸ Set.mem_singleton _)
      rcases hSe with h0 | h0
      · exact heγ (smul_left_cancel S (h0.trans hγS.symm))
      · have : e ∈ MulAction.fixedBy Hbar S := h0
        rw [hγ] at this
        exact heγ this
    · -- both hyperbolic: `T` permutes `Fix S = {u, v}`; then `T` or `T²` fixes `u` and `v`
      obtain ⟨γ, δ, hγδ, hγ⟩ := (k92f_shape hS).1.1 hSh
      have huv : (Sum.inr γ : Hbar) ≠ Sum.inr δ := fun e => hγδ (Sum.inr.inj e)
      have huS : (Sum.inr γ : Hbar) ∈ MulAction.fixedBy Hbar S := by rw [hγ]; exact Set.mem_insert _ _
      have hvS : (Sum.inr δ : Hbar) ∈ MulAction.fixedBy Hbar S := by rw [hγ]; exact Set.mem_insert_of_mem _ rfl
      have hu := hTS _ huS
      have hv := hTS _ hvS
      rw [hγ] at hu hv
      have hT2 : MulAction.fixedBy Hbar (T * T) = MulAction.fixedBy Hbar T :=
        k92f_fix_sq (lt_trans two_pos hTh)
      have hboth : (Sum.inr γ : Hbar) ∈ MulAction.fixedBy Hbar T ∧ (Sum.inr δ : Hbar) ∈ MulAction.fixedBy Hbar T := by
        rcases hu with hu | hu
        · rcases hv with hv | hv
          · exact absurd (smul_left_cancel T (hv.trans hu.symm)) huv.symm
          · exact ⟨hu, hv⟩
        · have hu' : T • (Sum.inr γ : Hbar) = Sum.inr δ := Set.mem_singleton_iff.1 hu
          have hv' : T • (Sum.inr δ : Hbar) = Sum.inr γ := by
            rcases hv with hv | hv
            · exact hv
            · exact absurd (smul_left_cancel T (hv.trans hu'.symm)) huv.symm
          rw [← hT2]
          refine ⟨?_, ?_⟩
          · show (T * T) • (Sum.inr γ : Hbar) = Sum.inr γ
            rw [mul_smul, hu', hv']
          · show (T * T) • (Sum.inr δ : Hbar) = Sum.inr δ
            rw [mul_smul, hv', hu']
      rw [hγ, hab]
      rw [hab] at hboth
      exact k92f_pair_sub huv hboth.1 hboth.2

/-- Auxiliary (§2.3): non-identity elements with the same fixed-point set commute (conjugate the fixed points to
`i`, to `{0, ∞}` or to `∞`; the conjugates are rotations, diagonal, or upper triangular with equal diagonal). -/
theorem k92f_commute_of_fix_eq {S T : PSL(2, ℝ)} (hS : S ≠ 1) (hT : T ≠ 1)
    (h : MulAction.fixedBy Hbar S = MulAction.fixedBy Hbar T) : S * T = T * S := by
  -- only the type of `T` matters (`S` has the same fixed-point set)
  have _ := hS
  obtain ⟨hgS, -⟩ := k92n_Tr_out S
  obtain ⟨hgT, hTr⟩ := k92n_Tr_out T
  set s := Quotient.out S
  set t := Quotient.out T
  rw [← hgS, ← hgT] at h ⊢
  -- it suffices that some conjugates `P s P⁻¹`, `P t P⁻¹` commute
  suffices H : ∃ P : SL(2, ℝ), (P * s * P⁻¹) * (P * t * P⁻¹) = (P * t * P⁻¹) * (P * s * P⁻¹) by
    obtain ⟨P, hP⟩ := H
    have hst : s * t = t * s := by
      calc s * t = P⁻¹ * ((P * s * P⁻¹) * (P * t * P⁻¹)) * P := by group
        _ = P⁻¹ * ((P * t * P⁻¹) * (P * s * P⁻¹)) * P := by rw [hP]
        _ = t * s := by group
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hst]
  have hconj : ∀ P : SL(2, ℝ), MulAction.fixedBy Hbar ((P * s * P⁻¹ : SL(2, ℝ)) : PSL(2, ℝ)) =
      MulAction.fixedBy Hbar ((P * t * P⁻¹ : SL(2, ℝ)) : PSL(2, ℝ)) := fun P => by
    have := k92f_fix_conj (P : PSL(2, ℝ)) h
    rwa [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul] at this
  rcases k92f_trichotomy hT with hTe | hTp | hTh
  · -- elliptic: conjugate the common fixed point `p` to `i`; both conjugates are rotations
    obtain ⟨p, hp⟩ := (k92f_shape hT).2.2.1 hTe
    rw [← hgT] at hp
    have htp : t • p = p := ((k92f_mem_fix t).1 p).1 (hp ▸ Set.mem_singleton _)
    have hsp : s • p = p := ((k92f_mem_fix s).1 p).1 (h ▸ hp ▸ Set.mem_singleton _)
    refine ⟨p.toSL2R⁻¹, k92f_comm_of_fix_I ?_ ?_⟩
    · rw [mul_smul, mul_smul, inv_inv, UpperHalfPlane.toSL2R_smul_I, hsp, inv_smul_eq_iff,
        UpperHalfPlane.toSL2R_smul_I]
    · rw [mul_smul, mul_smul, inv_inv, UpperHalfPlane.toSL2R_smul_I, htp, inv_smul_eq_iff,
        UpperHalfPlane.toSL2R_smul_I]
  · -- parabolic: conjugate the fixed point `α` to `∞`; both conjugates are `[[a, b], [0, a]]`
    obtain ⟨α, hα⟩ := (k92f_shape hT).2.1.1 hTp
    rw [← hgT] at hα
    obtain ⟨P, hP⟩ : ∃ P : SL(2, ℝ), Matrix.SpecialLinearGroup.mapGL ℝ P • α = OnePoint.infty := by
      induction α using OnePoint.rec with
      | infty => exact ⟨1, by rw [map_one, one_smul]⟩
      | coe x =>
        refine ⟨⟨!![0, -1; 1, -x], by simp [Matrix.det_fin_two_of]⟩, ?_⟩
        have e : ((Matrix.SpecialLinearGroup.mapGL ℝ (⟨!![0, -1; 1, -x], by simp [Matrix.det_fin_two_of]⟩ :
            SL(2, ℝ)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * x + ((Matrix.SpecialLinearGroup.mapGL ℝ
            (⟨!![0, -1; 1, -x], by simp [Matrix.det_fin_two_of]⟩ : SL(2, ℝ)) : GL (Fin 2) ℝ) :
            Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 0 := by
          show (1 : ℝ) * x + -x = 0
          ring
        rw [OnePoint.smul_some_eq_ite, ite_eq_left e]
    have hfixP : MulAction.fixedBy Hbar ((P * t * P⁻¹ : SL(2, ℝ)) : PSL(2, ℝ)) = {Sum.inr OnePoint.infty} := by
      ext y
      rw [show ((P * t * P⁻¹ : SL(2, ℝ)) : PSL(2, ℝ)) = (P : PSL(2, ℝ)) * t * (P : PSL(2, ℝ))⁻¹ by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]]
      show ((P : PSL(2, ℝ)) * t * (P : PSL(2, ℝ))⁻¹) • y = y ↔ y ∈ ({Sum.inr OnePoint.infty} : Set Hbar)
      rw [mul_smul, mul_smul, ← eq_inv_smul_iff]
      have : (t : PSL(2, ℝ)) • ((P : PSL(2, ℝ))⁻¹ • y) = (P : PSL(2, ℝ))⁻¹ • y ↔
          (P : PSL(2, ℝ))⁻¹ • y ∈ MulAction.fixedBy Hbar (t : PSL(2, ℝ)) := Iff.rfl
      rw [this, hα, Set.mem_singleton_iff, Set.mem_singleton_iff, inv_smul_eq_iff]
      constructor <;> intro e <;> rw [e]
      · show Sum.inr ((P : PSL(2, ℝ)) • α) = Sum.inr OnePoint.infty
        rw [k92n_bdry_smul, hP]
      · show Sum.inr OnePoint.infty = Sum.inr ((P : PSL(2, ℝ)) • α)
        rw [k92n_bdry_smul, hP]
    exact ⟨P, k92f_comm_of_upper (k92f_fix_infty_only _ ((hconj P).trans hfixP))
      (k92f_fix_infty_only _ hfixP)⟩
  · -- hyperbolic: diagonalize `t`; the conjugate of `s` then fixes `0` and `∞` too, so it is diagonal
    have h2 : 2 < |t 0 0 + t 1 1| := hTr ▸ hTh
    have hhyp : (t : Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic := by
      show 0 < (t : Matrix (Fin 2) (Fin 2) ℝ).discr
      rw [k92n_discr]
      nlinarith [abs_nonneg (t 0 0 + t 1 1), sq_abs (t 0 0 + t 1 1)]
    obtain ⟨l, -, -, P, hP⟩ := (hyperbolic_conj_diag t).1 hhyp
    have hD : (P * t * P⁻¹ : SL(2, ℝ)) 1 0 = 0 ∧ (P * t * P⁻¹ : SL(2, ℝ)) 0 1 = 0 := by
      rw [hP]
      simp
    have hS' := (k92f_fix_zero_infty _).1 (by rw [hconj P]; exact (k92f_fix_zero_infty _).2 hD)
    exact ⟨P, k92f_comm_of_diag hS' hD⟩

/-- Auxiliary (§2.3, l. 897): the fixed-point set determines the type of a non-identity element. -/
theorem k92f_same_type {S T : PSL(2, ℝ)} (hS : S ≠ 1) (hT : T ≠ 1)
    (h : MulAction.fixedBy Hbar S = MulAction.fixedBy Hbar T) :
    (IsHyperbolic S ↔ IsHyperbolic T) ∧ (IsParabolic S ↔ IsParabolic T) ∧ (IsElliptic S ↔ IsElliptic T) := by
  obtain ⟨hS1, hS2, hS3⟩ := k92f_shape hS
  obtain ⟨hT1, hT2, hT3⟩ := k92f_shape hT
  rw [h] at hS1 hS2 hS3
  exact ⟨hS1.trans hT1.symm, hS2.trans hT2.symm, hS3.trans hT3.symm⟩

/-- Auxiliary (§2.1, l. 669). The axis of a hyperbolic `T` is the geodesic joining its two fixed points. -/
theorem k92f_axis {T : PSL(2, ℝ)} (hT : IsHyperbolic T) :
    ∃ α β : OnePoint ℝ, α ≠ β ∧ MulAction.fixedBy Hbar T = {Sum.inr α, Sum.inr β} ∧
      axis T = geodArc (boundaryToExt α) (boundaryToExt β) := by
  obtain ⟨α, β, hαβ, hfix⟩ := fixedBy_of_isHyperbolic hT
  refine ⟨α, β, hαβ, hfix, ?_⟩
  have hfx : ∀ γ : OnePoint ℝ, T • γ = γ ↔ γ = α ∨ γ = β := fun γ => by
    have e : (Sum.inr γ : Hbar) ∈ MulAction.fixedBy Hbar T ↔ T • γ = γ :=
      ⟨fun h => Sum.inr.inj h, fun h => congrArg Sum.inr h⟩
    rw [← e, hfix]
    simp
  ext z
  constructor
  · rintro ⟨γ, δ, hγδ, hγ, hδ, hz⟩
    rcases (hfx γ).1 hγ with rfl | rfl <;> rcases (hfx δ).1 hδ with rfl | rfl
    · exact absurd rfl hγδ
    · exact hz
    · rwa [k92f_geodArc_symm]
    · exact absurd rfl hγδ
  · intro hz
    exact ⟨α, β, hαβ, (hfx α).2 (Or.inl rfl), (hfx β).2 (Or.inr rfl), hz⟩

/-- Auxiliary (§1.2). A complete geodesic determines its (unordered) pair of end points. -/
theorem k92f_geodArc_ends {α β α' β' : OnePoint ℝ} (h : α ≠ β) (h' : α' ≠ β') :
    geodArc (boundaryToExt α) (boundaryToExt β) = geodArc (boundaryToExt α') (boundaryToExt β') ↔
      ({Sum.inr α, Sum.inr β} : Set Hbar) = {Sum.inr α', Sum.inr β'} := by
  have himg : ∀ a b : OnePoint ℝ, ({Sum.inr a, Sum.inr b} : Set Hbar) = Sum.inr '' {a, b} := fun a b => by
    rw [Set.image_pair]
  rw [himg, himg]
  constructor
  · intro he
    congr 1
    -- points of ℍ with prescribed real and imaginary parts
    have hpt : ∀ (r t : ℝ) (ht : 0 < t), ∃ ξ : ℍ, ξ.re = r ∧ ξ.im = t := fun r t ht =>
      ⟨UpperHalfPlane.mk ⟨r, t⟩ ht, rfl, rfl⟩
    rcases k92f_geodArc_cases h with ⟨x, hp, hx⟩ | ⟨x, y, hxy, hp, hx⟩ <;>
      rcases k92f_geodArc_cases h' with ⟨x', hp', hx'⟩ | ⟨x', y', hxy', hp', hx'⟩ <;> rw [hp, hp']
    · -- two vertical lines
      obtain ⟨ξ, hr, -⟩ := hpt x 1 one_pos
      have := (hx' ξ).1 (he ▸ (hx ξ).2 hr)
      rw [hr] at this
      rw [this]
    · -- a vertical line is not a semicircle: it contains points of arbitrarily large height
      exfalso
      obtain ⟨ξ, hr, hi⟩ := hpt x (|x - x'| + |y' - x| + 1) (by positivity)
      have := (hx' ξ).1 (he ▸ (hx ξ).2 hr)
      rw [hr, hi] at this
      have h1 : (x - x') * (y' - x) ≤ |x - x'| * |y' - x| := by
        rw [← abs_mul]; exact le_abs_self _
      nlinarith [abs_nonneg (x - x'), abs_nonneg (y' - x)]
    · exfalso
      obtain ⟨ξ, hr, hi⟩ := hpt x' (|x' - x| + |y - x'| + 1) (by positivity)
      have := (hx ξ).1 (he.symm ▸ (hx' ξ).2 hr)
      rw [hr, hi] at this
      have h1 : (x' - x) * (y - x') ≤ |x' - x| * |y - x'| := by
        rw [← abs_mul]; exact le_abs_self _
      nlinarith [abs_nonneg (x' - x), abs_nonneg (y - x')]
    · -- two semicircles agree at two interior abscissae, so `x + y = x' + y'` and `xy = x'y'`
      have key : ∀ t : ℝ, 0 < (t - x) * (y - t) → (t - x') * (y' - t) = (t - x) * (y - t) := fun t ht => by
        obtain ⟨ξ, hr, hi⟩ := hpt t (Real.sqrt ((t - x) * (y - t))) (Real.sqrt_pos.2 ht)
        have := (hx' ξ).1 (he ▸ (hx ξ).2 (by rw [hr, hi, Real.sq_sqrt ht.le]))
        rw [hr, hi, Real.sq_sqrt ht.le] at this
        exact this
      have hd : (y - x) ^ 2 > 0 := by
        have : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
        positivity
      have k1 := key ((x + y) / 2) (by nlinarith)
      have k2 := key ((3 * x + y) / 4) (by nlinarith)
      have hs : x + y = x' + y' := by
        have : (y - x) * ((x + y) - (x' + y')) = 0 := by linear_combination (-4) * (k1 - k2)
        rcases mul_eq_zero.1 this with h0 | h0
        · exact absurd (sub_eq_zero.1 h0).symm hxy
        · linarith
      have hp2 : x * y = x' * y' := by linear_combination k1 + ((x + y) / 2) * hs
      -- `x'` is a root of `X² − (x + y) X + xy`
      have r1 : (x' - x) * (x' - y) = 0 := by linear_combination (-x') * hs + hp2
      rw [Set.pair_eq_pair_iff]
      rcases mul_eq_zero.1 r1 with h0 | h0
      · have e1 : x = x' := (sub_eq_zero.1 h0).symm
        have e2 : y = y' := by linarith
        exact Or.inl ⟨by rw [e1], by rw [e2]⟩
      · have e1 : y = x' := (sub_eq_zero.1 h0).symm
        have e2 : x = y' := by linarith
        exact Or.inr ⟨by rw [e2], by rw [e1]⟩
  · intro he
    have he' := Set.image_injective.2 Sum.inr_injective he
    rw [Set.pair_eq_pair_iff] at he'
    rcases he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact k92f_geodArc_symm _ _

/-- **Theorem 2.3.2** (§2.3; l. 889). Two non-identity elements of PSL(2,ℝ) commute iff they have the same
fixed-point set. -/
theorem thm2_3_2 {S T : PSL(2, ℝ)} (hS : S ≠ 1) (hT : T ≠ 1) :
    S * T = T * S ↔ MulAction.fixedBy Hbar S = MulAction.fixedBy Hbar T := by
  exact ⟨k92f_fix_eq_of_commute hS hT, k92f_commute_of_fix_eq hS hT⟩

/-- **Theorem 2.3.3** (§2.3; l. 891), hyperbolic case. The centralizer of a hyperbolic `T` consists of the
hyperbolic elements with the same fixed-point set, together with `Id`. -/
theorem thm2_3_3_a {T : PSL(2, ℝ)} (hT : IsHyperbolic T) :
    (Subgroup.centralizer {T} : Set PSL(2, ℝ)) =
      {S | S = 1 ∨ (IsHyperbolic S ∧ MulAction.fixedBy Hbar S = MulAction.fixedBy Hbar T)} := by
  have hT1 : T ≠ 1 := k92f_ne_one_of_hyp hT
  ext S
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · intro h
    by_cases hS1 : S = 1
    · exact Or.inl hS1
    · have hfix := k92f_fix_eq_of_commute hS1 hT1 h
      exact Or.inr ⟨(k92f_same_type hS1 hT1 hfix).1.2 hT, hfix⟩
  · rintro (rfl | ⟨hS, hfix⟩)
    · simp
    · exact k92f_commute_of_fix_eq (k92f_ne_one_of_hyp hS) hT1 hfix

/-- **Theorem 2.3.3** (§2.3; l. 891), parabolic case. -/
theorem thm2_3_3_b {T : PSL(2, ℝ)} (hT : IsParabolic T) :
    (Subgroup.centralizer {T} : Set PSL(2, ℝ)) =
      {S | S = 1 ∨ (IsParabolic S ∧ MulAction.fixedBy Hbar S = MulAction.fixedBy Hbar T)} := by
  have hT1 : T ≠ 1 := hT.2
  ext S
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · intro h
    by_cases hS1 : S = 1
    · exact Or.inl hS1
    · have hfix := k92f_fix_eq_of_commute hS1 hT1 h
      exact Or.inr ⟨(k92f_same_type hS1 hT1 hfix).2.1.2 hT, hfix⟩
  · rintro (rfl | ⟨hS, hfix⟩)
    · simp
    · exact k92f_commute_of_fix_eq (hS.2) hT1 hfix

/-- **Theorem 2.3.3** (§2.3; l. 891), elliptic case. -/
theorem thm2_3_3_c {T : PSL(2, ℝ)} (hT : IsElliptic T) :
    (Subgroup.centralizer {T} : Set PSL(2, ℝ)) =
      {S | S = 1 ∨ (IsElliptic S ∧ MulAction.fixedBy Hbar S = MulAction.fixedBy Hbar T)} := by
  have hT1 : T ≠ 1 := k92f_ne_one_of_ell hT
  ext S
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · intro h
    by_cases hS1 : S = 1
    · exact Or.inl hS1
    · have hfix := k92f_fix_eq_of_commute hS1 hT1 h
      exact Or.inr ⟨(k92f_same_type hS1 hT1 hfix).2.2.2 hT, hfix⟩
  · rintro (rfl | ⟨hS, hfix⟩)
    · simp
    · exact k92f_commute_of_fix_eq (k92f_ne_one_of_ell hS) hT1 hfix

/-- **Corollary 2.3.4** (§2.3; l. 893). Two hyperbolic elements commute iff they have the same axes. -/
theorem cor2_3_4 {S T : PSL(2, ℝ)} (hT : IsHyperbolic T) (hS : IsHyperbolic S) :
    T * S = S * T ↔ axis T = axis S := by
  obtain ⟨α, β, hαβ, hfT, haT⟩ := k92f_axis hT
  obtain ⟨α', β', hαβ', hfS, haS⟩ := k92f_axis hS
  rw [haT, haS, k92f_geodArc_ends hαβ hαβ', ← hfT, ← hfS]
  exact thm2_3_2 (k92f_ne_one_of_hyp hT) (k92f_ne_one_of_hyp hS)

/-- The representative of `mk g` in `PSL(2,ℝ)` is `±g`. -/
theorem k92_out_mk (g : SL(2, ℝ)) :
    Quotient.out (g : PSL(2, ℝ)) = g ∨ Quotient.out (g : PSL(2, ℝ)) = -g := by
  have h : (Quotient.out (g : PSL(2, ℝ)))⁻¹ * g ∈ Subgroup.center SL(2, ℝ) := by
    rw [← QuotientGroup.eq]
    exact (QuotientGroup.out_eq' (g : PSL(2, ℝ))).symm ▸ rfl
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at h
  obtain ⟨r, hr, hrg⟩ := h
  have hr2 : (r - 1) * (r + 1) = 0 := by
    have : r ^ 2 = 1 := by simpa using hr
    linear_combination this
  set o := Quotient.out (g : PSL(2, ℝ))
  rcases mul_eq_zero.1 hr2 with h1 | h1
  · have hc : o⁻¹ * g = 1 := by
      apply Subtype.ext
      rw [← hrg, sub_eq_zero.1 h1, Matrix.SpecialLinearGroup.coe_one]
      simp
    exact Or.inl (inv_mul_eq_one.1 hc)
  · have hc : o⁻¹ * g = -1 := by
      apply Subtype.ext
      rw [← hrg, eq_neg_of_add_eq_zero_left h1, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have hg : g = -o := by
      rw [inv_mul_eq_iff_eq_mul] at hc
      rw [hc, mul_neg_one]
    right
    rw [hg, neg_neg]

/-- Auxiliary. `Tr(±g) = |tr g|` for `g ∈ SL(2,ℝ)` (independent of the representative). -/
theorem k92_Tr_mk (g : SL(2, ℝ)) : Tr (g : PSL(2, ℝ)) = |Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℝ)| := by
  unfold Tr
  rcases k92_out_mk g with h | h
  · rw [h]
  · rw [h, Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg, abs_neg]

/-- **Unlabelled** (§2.3; l. 895; cited at l. 1021, 1594). `Tr(S⁻¹TS) = Tr(T)`. -/
theorem tr_conj (S T : PSL(2, ℝ)) : Tr (S⁻¹ * T * S) = Tr T := by
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective S
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective T
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, k92_Tr_mk, k92_Tr_mk]
  have := k92_trace_conj s⁻¹ t
  rw [inv_inv] at this
  rw [this]

/-- Auxiliary (§2.3, Lemma 2.2.2 (i)). A group with an injective homomorphism `φ` into `(ℝ, +)` whose sublevel sets
`{|φ g| ≤ M}` are finite is cyclic: it is generated by an element of least `|φ|` (Euclid's algorithm). -/
theorem k92f_cyclic_of_real_hom {G : Type*} [Group G] (φ : G →* Multiplicative ℝ) (hinj : Function.Injective φ)
    (hfin : ∀ M : ℝ, {g : G | |Multiplicative.toAdd (φ g)| ≤ M}.Finite) : IsCyclic G := by
  set f : G → ℝ := fun g => Multiplicative.toAdd (φ g) with hfdef
  have hf_mul : ∀ g h : G, f (g * h) = f g + f h := fun g h => by simp [hfdef]
  have hf_zpow : ∀ (g : G) (k : ℤ), f (g ^ k) = k * f g := fun g k => by simp [hfdef]
  have hf0 : ∀ g : G, f g = 0 → g = 1 := fun g hg => hinj (by
    rw [map_one]
    exact Multiplicative.toAdd.injective (by simpa [hfdef] using hg))
  by_cases htriv : ∀ g : G, g = 1
  · exact ⟨⟨1, fun g => Subgroup.mem_zpowers_iff.2 ⟨0, by rw [zpow_zero, htriv g]⟩⟩⟩
  push Not at htriv
  obtain ⟨g₁, hg₁⟩ := htriv
  -- an element of least `|f|` among the non-identity ones
  obtain ⟨g₀, ⟨hg₀1, -⟩, hmin⟩ := Set.exists_min_image {g : G | g ≠ 1 ∧ |f g| ≤ |f g₁|} (fun g => |f g|)
    ((hfin |f g₁|).subset fun g hg => hg.2) ⟨g₁, hg₁, le_rfl⟩
  have hmin' : ∀ g : G, g ≠ 1 → |f g₀| ≤ |f g| := fun g hg => by
    by_cases hle : |f g| ≤ |f g₁|
    · exact hmin g ⟨hg, hle⟩
    · exact (hmin g₁ ⟨hg₁, le_rfl⟩).trans (le_of_lt (not_le.1 hle))
  have ha : f g₀ ≠ 0 := fun h => hg₀1 (hf0 g₀ h)
  refine ⟨⟨g₀, fun g => Subgroup.mem_zpowers_iff.2 ⟨⌊f g / f g₀⌋, ?_⟩⟩⟩
  -- the remainder `g g₀^(-k)` has `|f| < |f g₀|`, hence is `1`
  set k := ⌊f g / f g₀⌋
  have hr : f (g * g₀ ^ (-k)) = f g₀ * (f g / f g₀ - k) := by
    rw [hf_mul, hf_zpow]
    field_simp
    push_cast
    ring
  have hlt : |f (g * g₀ ^ (-k))| < |f g₀| := by
    rw [hr, abs_mul]
    have h1 : 0 ≤ f g / f g₀ - k := sub_nonneg.2 (Int.floor_le _)
    have h2 : f g / f g₀ - k < 1 := by
      have := Int.lt_floor_add_one (f g / f g₀)
      linarith
    rw [abs_of_nonneg h1]
    have : 0 < |f g₀| := abs_pos.2 ha
    nlinarith
  by_contra hne
  have h1 : g * g₀ ^ (-k) ≠ 1 := fun h => hne (by
    rw [mul_eq_one_iff_eq_inv, zpow_neg, inv_inv] at h
    exact h.symm)
  exact absurd (hmin' _ h1) (not_le.2 hlt)

/-- Auxiliary. PSL(2,ℝ) acts on ℍ by isometries. -/
theorem k92f_psl_dist (C : PSL(2, ℝ)) (x y : ℍ) : dist (C • x) (C • y) = dist x y := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective C
  rw [k92_psl_smul_mk, k92_psl_smul_mk, dist_smul]

/-- Auxiliary (§2.3). A Fuchsian group conjugate (by one `C`) to a group of scalings `z ↦ μ z`, `μ > 0`, is cyclic:
`T ↦ log μ` is an injective homomorphism into `ℝ` with finite sublevel sets (compact ∩ discrete). -/
theorem k92f_cyclic_of_scaling {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) (C : PSL(2, ℝ))
    (h : ∀ T ∈ Γ, ∃ μ : ℝ, 0 < μ ∧ ∀ z : ℍ, (((C * T * C⁻¹) • z : ℍ) : ℂ) = μ * z) : IsCyclic Γ := by
  -- the factor `μ(T)`, read off at `i`
  set μ : Γ → ℝ := fun T => ((C * T * C⁻¹) • UpperHalfPlane.I).im with hμdef
  have hμ : ∀ T : Γ, 0 < μ T ∧ ∀ z : ℍ, (((C * T * C⁻¹) • z : ℍ) : ℂ) = μ T * z := fun T => by
    obtain ⟨m, hm, hz⟩ := h T T.2
    have e : μ T = m := by
      simp only [hμdef]
      rw [← UpperHalfPlane.coe_im, hz, UpperHalfPlane.coe_I]
      simp
    rw [e]
    exact ⟨hm, hz⟩
  have hmul : ∀ T₁ T₂ : Γ, μ (T₁ * T₂) = μ T₁ * μ T₂ := fun T₁ T₂ => by
    have e : (C * ((T₁ * T₂ : Γ) : PSL(2, ℝ)) * C⁻¹) • UpperHalfPlane.I =
        (C * T₁ * C⁻¹) • (C * T₂ * C⁻¹) • UpperHalfPlane.I := by
      rw [← mul_smul]
      congr 1
      simp only [Subgroup.coe_mul]
      group
    show ((C * ((T₁ * T₂ : Γ) : PSL(2, ℝ)) * C⁻¹) • UpperHalfPlane.I).im = μ T₁ * μ T₂
    rw [e, ← UpperHalfPlane.coe_im, (hμ T₁).2, (hμ T₂).2, UpperHalfPlane.coe_I]
    simp
  have hone : μ 1 = 1 := by
    simp only [hμdef, OneMemClass.coe_one, mul_one, mul_inv_cancel, one_smul, UpperHalfPlane.I_im]
  let φ : Γ →* Multiplicative ℝ :=
    { toFun := fun T => Multiplicative.ofAdd (Real.log (μ T))
      map_one' := by rw [hone, Real.log_one, ofAdd_zero]
      map_mul' := fun T₁ T₂ => by
        rw [hmul, Real.log_mul (hμ T₁).1.ne' (hμ T₂).1.ne', ofAdd_add] }
  -- `ρ(T w, w) = |log μ(T)|` at `w = C⁻¹ i`
  have hdist : ∀ T : Γ, dist ((T : PSL(2, ℝ)) • (C⁻¹ • UpperHalfPlane.I)) (C⁻¹ • UpperHalfPlane.I) =
      |Real.log (μ T)| := fun T => by
    have hre : ((C * T * C⁻¹) • UpperHalfPlane.I).re = UpperHalfPlane.I.re := by
      rw [← UpperHalfPlane.coe_re, (hμ T).2, UpperHalfPlane.coe_I]
      simp
    rw [← k92f_psl_dist C, smul_inv_smul, ← mul_smul, ← mul_smul, UpperHalfPlane.dist_of_re_eq hre,
      UpperHalfPlane.I_im, Real.log_one, Real.dist_eq, sub_zero]
  refine k92f_cyclic_of_real_hom φ ((injective_iff_map_eq_one φ).2 fun T hT => ?_) fun M => ?_
  · -- `μ(T) = 1`: the conjugate `C T C⁻¹` fixes `i` and `2i`, so it is the identity
    have hlog : Real.log (μ T) = 0 := by
      have := congrArg Multiplicative.toAdd hT
      simpa [φ] using this
    have hμ1 : μ T = 1 := Real.eq_one_of_pos_of_log_eq_zero (hμ T).1 hlog
    have hfix : ∀ z : ℍ, (C * T * C⁻¹) • z = z := fun z => UpperHalfPlane.ext (by rw [(hμ T).2, hμ1]; simp)
    have h2 : UpperHalfPlane.I ≠ UpperHalfPlane.mk ⟨0, 2⟩ two_pos := by
      intro e
      have := congrArg UpperHalfPlane.im e
      norm_num at this
    have h1 := k92e_eq_one_of_two_fixed h2 (hfix _) (hfix _)
    apply Subtype.ext
    rw [OneMemClass.coe_one]
    calc (T : PSL(2, ℝ)) = C⁻¹ * (C * T * C⁻¹) * C := by group
      _ = 1 := by rw [h1]; group
  · -- finitely many `T` move `w` by at most `M`
    refine (k92e_finite_of_compact hΓ (k92e_compact_preimage (C⁻¹ • UpperHalfPlane.I)
      (isCompact_closedBall (C⁻¹ • UpperHalfPlane.I) M))).subset fun T hT => ?_
    show (T : PSL(2, ℝ)) • (C⁻¹ • UpperHalfPlane.I) ∈ Metric.closedBall (C⁻¹ • UpperHalfPlane.I) M
    rw [Metric.mem_closedBall, hdist]
    exact hT

/-- Auxiliary (§2.3). A Fuchsian group conjugate (by one `C`) to a group of translations `z ↦ z + b` is cyclic:
`T ↦ b` is an injective homomorphism into `ℝ` with finite sublevel sets. -/
theorem k92f_cyclic_of_translation {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) (C : PSL(2, ℝ))
    (h : ∀ T ∈ Γ, ∃ b : ℝ, ∀ z : ℍ, (((C * T * C⁻¹) • z : ℍ) : ℂ) = z + b) : IsCyclic Γ := by
  -- the translation length `b(T)`, read off at `i`
  set b : Γ → ℝ := fun T => ((C * T * C⁻¹) • UpperHalfPlane.I).re with hbdef
  have hb : ∀ T : Γ, ∀ z : ℍ, (((C * T * C⁻¹) • z : ℍ) : ℂ) = z + b T := fun T => by
    obtain ⟨m, hz⟩ := h T T.2
    have e : b T = m := by
      simp only [hbdef]
      rw [← UpperHalfPlane.coe_re, hz, UpperHalfPlane.coe_I]
      simp
    rw [e]
    exact hz
  have hadd : ∀ T₁ T₂ : Γ, b (T₁ * T₂) = b T₁ + b T₂ := fun T₁ T₂ => by
    have e : (C * ((T₁ * T₂ : Γ) : PSL(2, ℝ)) * C⁻¹) • UpperHalfPlane.I =
        (C * T₁ * C⁻¹) • (C * T₂ * C⁻¹) • UpperHalfPlane.I := by
      rw [← mul_smul]
      congr 1
      simp only [Subgroup.coe_mul]
      group
    show ((C * ((T₁ * T₂ : Γ) : PSL(2, ℝ)) * C⁻¹) • UpperHalfPlane.I).re = b T₁ + b T₂
    rw [e, ← UpperHalfPlane.coe_re, hb T₁, hb T₂, UpperHalfPlane.coe_I]
    simp
    ring
  have hzero : b 1 = 0 := by
    simp only [hbdef, OneMemClass.coe_one, mul_one, mul_inv_cancel, one_smul, UpperHalfPlane.I_re]
  let φ : Γ →* Multiplicative ℝ :=
    { toFun := fun T => Multiplicative.ofAdd (b T)
      map_one' := by rw [hzero, ofAdd_zero]
      map_mul' := fun T₁ T₂ => by rw [hadd, ofAdd_add] }
  -- `ρ(T w, w) = 2 arsinh(|b(T)|/2)` at `w = C⁻¹ i`
  have hdist : ∀ T : Γ, dist ((T : PSL(2, ℝ)) • (C⁻¹ • UpperHalfPlane.I)) (C⁻¹ • UpperHalfPlane.I) =
      2 * Real.arsinh (|b T| / 2) := fun T => by
    have him : ((C * T * C⁻¹) • UpperHalfPlane.I).im = 1 := by
      rw [← UpperHalfPlane.coe_im, hb T, UpperHalfPlane.coe_I]
      simp
    rw [← k92f_psl_dist C, smul_inv_smul, ← mul_smul, ← mul_smul, UpperHalfPlane.dist_eq, him,
      UpperHalfPlane.I_im, mul_one, Real.sqrt_one, mul_one, hb T, UpperHalfPlane.coe_I, Complex.dist_eq,
      add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
  refine k92f_cyclic_of_real_hom φ ((injective_iff_map_eq_one φ).2 fun T hT => ?_) fun M => ?_
  · -- `b(T) = 0`: the conjugate `C T C⁻¹` is the identity on ℍ
    have hb0 : b T = 0 := by
      have := congrArg Multiplicative.toAdd hT
      simpa [φ] using this
    have hfix : ∀ z : ℍ, (C * T * C⁻¹) • z = z := fun z => UpperHalfPlane.ext (by rw [hb T, hb0]; simp)
    have h2 : UpperHalfPlane.I ≠ UpperHalfPlane.mk ⟨0, 2⟩ two_pos := by
      intro e
      have := congrArg UpperHalfPlane.im e
      norm_num at this
    have h1 := k92e_eq_one_of_two_fixed h2 (hfix _) (hfix _)
    apply Subtype.ext
    rw [OneMemClass.coe_one]
    calc (T : PSL(2, ℝ)) = C⁻¹ * (C * T * C⁻¹) * C := by group
      _ = 1 := by rw [h1]; group
  · -- finitely many `T` move `w` by at most `2 arsinh(M/2)`
    refine (k92e_finite_of_compact hΓ (k92e_compact_preimage (C⁻¹ • UpperHalfPlane.I)
      (isCompact_closedBall (C⁻¹ • UpperHalfPlane.I) (2 * Real.arsinh (M / 2))))).subset fun T hT => ?_
    show (T : PSL(2, ℝ)) • (C⁻¹ • UpperHalfPlane.I) ∈
      Metric.closedBall (C⁻¹ • UpperHalfPlane.I) (2 * Real.arsinh (M / 2))
    rw [Metric.mem_closedBall, hdist]
    have hT' : |b T| ≤ M := hT
    gcongr

/-- Auxiliary. The Cayley identity `cay((cz + s)/(−sz + c)) = ((c + is)/(c − is)) cay(z)`, where
`cay(w) = (w − i)/(w + i)`. -/
theorem k92f_cay_id (c s z : ℂ) (h1 : -s * z + c ≠ 0) (h2 : c - I * s ≠ 0) (h3 : z + I ≠ 0) (h4 : c + I * s ≠ 0) :
    ((c * z + s) / (-s * z + c) - I) / ((c * z + s) / (-s * z + c) + I) =
      (c + I * s) / (c - I * s) * ((z - I) / (z + I)) := by
  have e1 : (c * z + s) / (-s * z + c) - I = (c + I * s) * (z - I) / (-s * z + c) := by
    rw [div_sub' h1, div_left_inj' h1]
    ring_nf
    rw [I_sq]
    ring
  have e2 : (c * z + s) / (-s * z + c) + I = (c - I * s) * (z + I) / (-s * z + c) := by
    rw [div_add' _ _ _ h1, div_left_inj' h1]
    ring_nf
    rw [I_sq]
    ring
  rw [e1, e2, div_div_div_cancel_right₀ h1]
  field_simp

/-- Auxiliary (§2.3). In the Cayley coordinate `(z − i)/(z + i)`, a matrix fixing `i` acts by a multiplication. -/
theorem k92f_rot_cay (R : SL(2, ℝ)) (hR : R • UpperHalfPlane.I = UpperHalfPlane.I) :
    ∃ κ : ℂ, ∀ z : ℍ, (((R • z : ℍ) : ℂ) - I) / (((R • z : ℍ) : ℂ) + I) = κ * (((z : ℂ) - I) / ((z : ℂ) + I)) := by
  have hpos : 0 < (Matrix.GeneralLinearGroup.det (R : GL (Fin 2) ℝ) : ℝ) := by simp
  obtain ⟨h1, h2⟩ := (UpperHalfPlane.gl_smul_I_eq_I_iff_of_pos hpos).1 hR
  have h1' : R 0 0 = R 1 1 := h1
  have h2' : R 0 1 = -R 1 0 := h2
  have hdet : R 0 0 * R 1 1 - R 0 1 * R 1 0 = 1 := by
    have := R.2
    rwa [Matrix.det_fin_two] at this
  have hne : ∀ σ : ℂ, σ = 1 ∨ σ = -1 → ((R 0 0 : ℝ) : ℂ) + σ * I * (R 0 1 : ℝ) ≠ 0 := by
    intro σ hσ h0
    have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    rcases hσ with rfl | rfl <;> simp at hre him <;> rw [← h1', h2'] at hdet <;> rw [hre] at hdet <;>
      nlinarith [sq_nonneg (R 1 0)]
  refine ⟨((R 0 0 : ℝ) + I * (R 0 1 : ℝ)) / ((R 0 0 : ℝ) - I * (R 0 1 : ℝ)), fun z => ?_⟩
  have hzi : (z : ℂ) + I ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    linarith [z.im_pos]
  have hden : UpperHalfPlane.denom (R : GL (Fin 2) ℝ) z = -((R 0 1 : ℝ) : ℂ) * z + (R 0 0 : ℝ) := by
    show ((R 1 0 : ℝ) : ℂ) * z + ((R 1 1 : ℝ) : ℂ) = _
    rw [← h1', show R 1 0 = -R 0 1 by rw [h2']; ring]
    push_cast
    ring
  have hRz : ((R • z : ℍ) : ℂ) = (((R 0 0 : ℝ) : ℂ) * z + (R 0 1 : ℝ)) / (-((R 0 1 : ℝ) : ℂ) * z + (R 0 0 : ℝ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, ← hden]
    rfl
  rw [hRz]
  refine k92f_cay_id _ _ _ (hden ▸ UpperHalfPlane.denom_ne_zero _ z) ?_ hzi ?_
  · have := hne (-1) (Or.inr rfl)
    rwa [show ((R 0 0 : ℝ) : ℂ) + -1 * I * (R 0 1 : ℝ) = (R 0 0 : ℝ) - I * (R 0 1 : ℝ) by ring] at this
  · have := hne 1 (Or.inl rfl)
    rwa [show ((R 0 0 : ℝ) : ℂ) + 1 * I * (R 0 1 : ℝ) = (R 0 0 : ℝ) + I * (R 0 1 : ℝ) by ring] at this

/-- Auxiliary. Conjugation moves a single fixed point: `Fix(C T C⁻¹) = {C α}` when `Fix T = {α}`. -/
theorem k92f_fix_conj_single {T : PSL(2, ℝ)} (C : PSL(2, ℝ)) {α : OnePoint ℝ}
    (h : MulAction.fixedBy Hbar T = {Sum.inr α}) :
    MulAction.fixedBy Hbar (C * T * C⁻¹) = {Sum.inr (C • α)} := by
  ext y
  show (C * T * C⁻¹) • y = y ↔ y ∈ ({Sum.inr (C • α)} : Set Hbar)
  rw [mul_smul, mul_smul, ← eq_inv_smul_iff]
  have : T • (C⁻¹ • y) = C⁻¹ • y ↔ C⁻¹ • y ∈ MulAction.fixedBy Hbar T := Iff.rfl
  rw [this, h, Set.mem_singleton_iff, Set.mem_singleton_iff, inv_smul_eq_iff]
  rfl

/-- Auxiliary. A lift of the identity of PSL(2,ℝ) is a scalar matrix `±1`. -/
theorem k92f_center_entries (d : SL(2, ℝ)) (h : (d : PSL(2, ℝ)) = 1) :
    d 1 0 = 0 ∧ d 0 1 = 0 ∧ d 0 0 = d 1 1 := by
  rw [QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff] at h
  obtain ⟨r, -, hr⟩ := h
  have e : ∀ i j, d i j = (Matrix.scalar (Fin 2) r : Matrix (Fin 2) (Fin 2) ℝ) i j := fun i j => by rw [hr]
  refine ⟨?_, ?_, ?_⟩
  · rw [e]; simp
  · rw [e]; simp
  · rw [e, e]; simp

/-- Auxiliary (§2.3, l. 897, elliptic case). A Fuchsian group fixing a point `p ∈ ℍ` is (finite) cyclic: it lies in
the compact stabilizer of `p`, and `T ↦ j(T, p)²` embeds it into `ℂˣ`. -/
theorem k92f_cyclic_of_fixed_point {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) (p : ℍ)
    (h : ∀ S ∈ Γ, S • p = p) : IsCyclic Γ := by
  -- Γ lies in the compact stabilizer of `p`, hence is finite
  have hfin : Finite Γ := by
    have := k92e_finite_of_compact hΓ (k92e_compact_preimage p (isCompact_singleton (x := p)))
    have huniv : {g : Γ | (g : PSL(2, ℝ)) ∈ {T : PSL(2, ℝ) | T • p ∈ ({p} : Set ℍ)}} = Set.univ :=
      Set.eq_univ_of_forall fun g => h g g.2
    rw [huniv] at this
    exact Set.finite_univ_iff.1 this
  -- conjugate `p` to `i`: the conjugates act by multiplications in the Cayley coordinate
  set C : PSL(2, ℝ) := ((p.toSL2R⁻¹ : SL(2, ℝ)) : PSL(2, ℝ)) with hCdef
  set cay : ℍ → ℂ := fun w => ((w : ℂ) - I) / ((w : ℂ) + I) with hcay
  have hCp : C • p = UpperHalfPlane.I := by
    rw [hCdef, k92_psl_smul_mk, inv_smul_eq_iff, UpperHalfPlane.toSL2R_smul_I]
  have hCI : ∀ T ∈ Γ, (C * T * C⁻¹) • UpperHalfPlane.I = UpperHalfPlane.I := fun T hT => by
    rw [mul_smul, mul_smul, ← hCp, inv_smul_smul, h T hT]
  have hκ : ∀ T ∈ Γ, ∃ κ : ℂ, ∀ z : ℍ, cay ((C * T * C⁻¹) • z) = κ * cay z := fun T hT => by
    obtain ⟨r, hr⟩ := QuotientGroup.mk_surjective (C * T * C⁻¹)
    have hrI : r • UpperHalfPlane.I = UpperHalfPlane.I := by rw [← k92_psl_smul_mk, hr]; exact hCI T hT
    obtain ⟨κ, hκ⟩ := k92f_rot_cay r hrI
    exact ⟨κ, fun z => by rw [← hr, hcay]; simp only; rw [k92_psl_smul_mk]; exact hκ z⟩
  set w₂ : ℍ := UpperHalfPlane.mk ⟨0, 2⟩ two_pos
  have hc2 : cay w₂ ≠ 0 := by
    simp only [hcay]
    rw [div_ne_zero_iff]
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩ <;> have := congrArg Complex.im h0 <;> simp [w₂] at this <;> norm_num at this
  set κ : Γ → ℂ := fun T => cay ((C * T * C⁻¹) • w₂) / cay w₂ with hκdef
  have hκT : ∀ T : Γ, ∀ z : ℍ, cay ((C * T * C⁻¹) • z) = κ T * cay z := fun T z => by
    obtain ⟨k, hk⟩ := hκ T T.2
    simp only [hκdef]
    rw [hk, hk, mul_div_assoc, div_self hc2, mul_one]
  have hmul : ∀ T₁ T₂ : Γ, κ (T₁ * T₂) = κ T₁ * κ T₂ := fun T₁ T₂ => by
    have e : (C * ((T₁ * T₂ : Γ) : PSL(2, ℝ)) * C⁻¹) • w₂ = (C * T₁ * C⁻¹) • (C * T₂ * C⁻¹) • w₂ := by
      rw [← mul_smul]
      congr 1
      simp only [Subgroup.coe_mul]
      group
    have := hκT (T₁ * T₂) w₂
    rw [e, hκT T₁, hκT T₂] at this
    exact mul_right_cancel₀ hc2 (this.symm.trans (mul_assoc _ _ _).symm)
  -- the Cayley coordinate is injective on ℍ
  have hcay_inj : ∀ a b : ℍ, cay a = cay b → a = b := fun a b hab => by
    have ha : (a : ℂ) + I ≠ 0 := fun h0 => by
      have := congrArg Complex.im h0; simp at this; linarith [a.im_pos]
    have hb : (b : ℂ) + I ≠ 0 := fun h0 => by
      have := congrArg Complex.im h0; simp at this; linarith [b.im_pos]
    simp only [hcay] at hab
    rw [div_eq_div_iff ha hb] at hab
    apply UpperHalfPlane.ext
    have : (2 * I) * ((a : ℂ) - b) = 0 := by linear_combination hab
    rcases mul_eq_zero.1 this with h0 | h0
    · simp at h0
    · exact sub_eq_zero.1 h0
  let φ : Γ →* ℂ :=
    { toFun := κ
      map_one' := by simp only [hκdef, OneMemClass.coe_one, mul_one, mul_inv_cancel, one_smul]; exact div_self hc2
      map_mul' := hmul }
  refine isCyclic_of_injective_ringHom φ fun T₁ T₂ he => ?_
  -- equal multipliers: `(C T₁ C⁻¹)⁻¹ (C T₂ C⁻¹)` fixes every point
  have hfix : ∀ z : ℍ, (C * T₁ * C⁻¹) • z = (C * T₂ * C⁻¹) • z := fun z =>
    hcay_inj _ _ (by rw [hκT, hκT]; exact congrArg (· * cay z) he)
  have h2 : UpperHalfPlane.I ≠ w₂ := by
    intro e
    have := congrArg UpperHalfPlane.im e
    norm_num [w₂] at this
  have hone := k92e_eq_one_of_two_fixed (T := (C * T₁ * C⁻¹)⁻¹ * (C * T₂ * C⁻¹)) h2
    (by rw [mul_smul, ← hfix, inv_smul_smul]) (by rw [mul_smul, ← hfix, inv_smul_smul])
  apply Subtype.ext
  have := inv_mul_eq_one.1 hone
  calc (T₁ : PSL(2, ℝ)) = C⁻¹ * (C * T₁ * C⁻¹) * C := by group
    _ = C⁻¹ * (C * T₂ * C⁻¹) * C := by rw [this]
    _ = T₂ := by group

/-- Auxiliary (§2.3, l. 897, hyperbolic case). A Fuchsian group whose non-identity elements all fix exactly
`α ≠ β ∈ ℝ ∪ {∞}` is cyclic: conjugated to diagonal form it embeds into `ℝ` by `T ↦ log μ²` with discrete image. -/
theorem k92f_cyclic_of_two_ends {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) (α β : OnePoint ℝ) (hαβ : α ≠ β)
    (h : ∀ S ∈ Γ, S ≠ 1 → MulAction.fixedBy Hbar S = {Sum.inr α, Sum.inr β}) : IsCyclic Γ := by
  by_cases htriv : ∀ S ∈ Γ, S = 1
  · exact ⟨⟨1, fun x => Subgroup.mem_zpowers_iff.2 ⟨0, Subtype.ext (by simp [htriv x x.2])⟩⟩⟩
  push Not at htriv
  obtain ⟨S₀, hS₀, hS₀1⟩ := htriv
  -- diagonalize a non-identity element `S₀`, hyperbolic by the shape of its fixed-point set
  have hS₀h : IsHyperbolic S₀ := (k92f_shape hS₀1).1.2 ⟨α, β, hαβ, h S₀ hS₀ hS₀1⟩
  obtain ⟨hg0, hTr0⟩ := k92n_Tr_out S₀
  set s₀ := Quotient.out S₀
  have hhyp : (s₀ : Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic := by
    have h2 : 2 < |s₀ 0 0 + s₀ 1 1| := hTr0 ▸ hS₀h
    show 0 < (s₀ : Matrix (Fin 2) (Fin 2) ℝ).discr
    rw [k92n_discr]
    nlinarith [abs_nonneg (s₀ 0 0 + s₀ 1 1), sq_abs (s₀ 0 0 + s₀ 1 1)]
  obtain ⟨l, -, -, P, hP⟩ := (hyperbolic_conj_diag s₀).1 hhyp
  have hD : (P * s₀ * P⁻¹ : SL(2, ℝ)) 1 0 = 0 ∧ (P * s₀ * P⁻¹ : SL(2, ℝ)) 0 1 = 0 := by
    rw [hP]
    simp
  have hmk : ∀ g : SL(2, ℝ), ((P * g * P⁻¹ : SL(2, ℝ)) : PSL(2, ℝ)) = (P : PSL(2, ℝ)) * g * (P : PSL(2, ℝ))⁻¹ :=
    fun g => by rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  refine k92f_cyclic_of_scaling hΓ (P : PSL(2, ℝ)) fun T hT => ?_
  obtain ⟨hgT, -⟩ := k92n_Tr_out T
  set t := Quotient.out T
  -- `d = P t P⁻¹` fixes `0` and `∞`, so it is diagonal and acts as `z ↦ d₀₀² z`
  have hd : (P * t * P⁻¹ : SL(2, ℝ)) 1 0 = 0 ∧ (P * t * P⁻¹ : SL(2, ℝ)) 0 1 = 0 := by
    apply (k92f_fix_zero_infty _).1
    by_cases hT1 : T = 1
    · rw [hmk, hgT, hT1, mul_one, mul_inv_cancel, MulAction.fixedBy_one_eq_univ]
      exact ⟨trivial, trivial⟩
    · have := k92f_fix_conj (P : PSL(2, ℝ)) ((h T hT hT1).trans (h S₀ hS₀ hS₀1).symm)
      rw [← hgT, ← hg0, ← hmk, ← hmk] at this
      rw [this]
      exact (k92f_fix_zero_infty _).2 hD
  set d := P * t * P⁻¹ with hddef
  have hdet : d 0 0 * d 1 1 = 1 := by
    have := d.2
    rw [Matrix.det_fin_two, hd.1, hd.2] at this
    linarith
  have hd0 : d 0 0 ≠ 0 := fun h0 => by rw [h0, zero_mul] at hdet; exact zero_ne_one hdet
  refine ⟨d 0 0 ^ 2, by positivity, fun z => ?_⟩
  rw [← hgT, ← hmk, k92_psl_smul_mk, UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [hd.1, hd.2, eq_inv_of_mul_eq_one_right hdet]
  have : ((d 0 0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd0
  push_cast
  field_simp
  ring

/-- Auxiliary (§2.3, l. 897, parabolic case). A Fuchsian group whose non-identity elements all fix exactly
`α ∈ ℝ ∪ {∞}` is cyclic: conjugated to translations it embeds into `ℝ` with discrete image. -/
theorem k92f_cyclic_of_one_end {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) (α : OnePoint ℝ)
    (h : ∀ S ∈ Γ, S ≠ 1 → MulAction.fixedBy Hbar S = {Sum.inr α}) : IsCyclic Γ := by
  -- conjugate `α` to `∞`
  obtain ⟨P, hP⟩ : ∃ P : SL(2, ℝ), Matrix.SpecialLinearGroup.mapGL ℝ P • α = OnePoint.infty := by
    induction α using OnePoint.rec with
    | infty => exact ⟨1, by rw [map_one, one_smul]⟩
    | coe x =>
      refine ⟨⟨!![0, -1; 1, -x], by simp [Matrix.det_fin_two_of]⟩, ?_⟩
      have e : ((Matrix.SpecialLinearGroup.mapGL ℝ (⟨!![0, -1; 1, -x], by simp [Matrix.det_fin_two_of]⟩ :
          SL(2, ℝ)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * x + ((Matrix.SpecialLinearGroup.mapGL ℝ
          (⟨!![0, -1; 1, -x], by simp [Matrix.det_fin_two_of]⟩ : SL(2, ℝ)) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 0 := by
        show (1 : ℝ) * x + -x = 0
        ring
      rw [OnePoint.smul_some_eq_ite, ite_eq_left e]
  have hmk : ∀ g : SL(2, ℝ), ((P * g * P⁻¹ : SL(2, ℝ)) : PSL(2, ℝ)) = (P : PSL(2, ℝ)) * g * (P : PSL(2, ℝ))⁻¹ :=
    fun g => by rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  refine k92f_cyclic_of_translation hΓ (P : PSL(2, ℝ)) fun T hT => ?_
  obtain ⟨hgT, -⟩ := k92n_Tr_out T
  set t := Quotient.out T
  -- `d = P t P⁻¹` is `[[a, b], [0, a]]`, acting as `z ↦ z + b/a`
  have hd : (P * t * P⁻¹ : SL(2, ℝ)) 1 0 = 0 ∧ (P * t * P⁻¹ : SL(2, ℝ)) 0 0 = (P * t * P⁻¹ : SL(2, ℝ)) 1 1 := by
    by_cases hT1 : T = 1
    · have := k92f_center_entries (P * t * P⁻¹) (by rw [hmk, hgT, hT1, mul_one, mul_inv_cancel])
      exact ⟨this.1, this.2.2⟩
    · apply k92f_fix_infty_only
      rw [hmk, hgT, k92f_fix_conj_single _ (h T hT hT1), k92n_bdry_smul, hP]
  rw [← hgT, ← hmk]
  set d := P * t * P⁻¹ with hddef
  have hdet : d 0 0 * d 0 0 = 1 := by
    have := d.2
    rw [Matrix.det_fin_two, hd.1, ← hd.2] at this
    linarith
  have hd0 : d 0 0 ≠ 0 := fun h0 => by rw [h0, zero_mul] at hdet; exact zero_ne_one hdet
  refine ⟨d 0 1 / d 0 0, fun z => ?_⟩
  rw [k92_psl_smul_mk, UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [hd.1, ← hd.2]
  have : ((d 0 0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd0
  push_cast
  rw [zero_mul, zero_add, add_div, mul_div_cancel_left₀ _ this]

/-- Auxiliary (§2.3, Corollary 2.3.7). `ℤ × ℤ` is not cyclic. -/
theorem k92f_not_cyclic_zz : ¬ IsCyclic (Multiplicative (ℤ × ℤ)) := by
  rintro ⟨g, hg⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg (Multiplicative.ofAdd (1, 0)))
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hg (Multiplicative.ofAdd (0, 1)))
  have hk' := congrArg Multiplicative.toAdd hk
  have hm' := congrArg Multiplicative.toAdd hm
  simp only [toAdd_zpow, toAdd_ofAdd, Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hk' hm'
  obtain ⟨h1, h2⟩ := hk'
  obtain ⟨-, h4⟩ := hm'
  have hb : (Multiplicative.toAdd g).2 = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · rw [h, zero_mul] at h1; exact absurd h1 zero_ne_one
    · exact h
  rw [hb, mul_zero] at h4
  exact zero_ne_one h4

/-- **Theorem 2.3.5** (§2.3; l. 897). A Fuchsian group all of whose non-identity elements have the same fixed-point
set is cyclic. -/
theorem thm2_3_5 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ)
    (h : ∀ S ∈ Γ, ∀ T ∈ Γ, S ≠ 1 → T ≠ 1 → MulAction.fixedBy Hbar S = MulAction.fixedBy Hbar T) :
    IsCyclic Γ := by
  by_cases htriv : ∀ S ∈ Γ, S = 1
  · exact ⟨⟨1, fun x => Subgroup.mem_zpowers_iff.2 ⟨0, Subtype.ext (by simp [htriv x x.2])⟩⟩⟩
  · push Not at htriv
    obtain ⟨S₀, hS₀, hS₀1⟩ := htriv
    have hall : ∀ S ∈ Γ, S ≠ 1 → MulAction.fixedBy Hbar S = MulAction.fixedBy Hbar S₀ :=
      fun S hS hS1 => h S hS S₀ hS₀ hS1 hS₀1
    -- the common fixed-point set is that of an elliptic, a parabolic or a hyperbolic element
    rcases k92f_trichotomy hS₀1 with he | hpa | hh
    · obtain ⟨p, hp⟩ := fixedBy_of_isElliptic he
      refine k92f_cyclic_of_fixed_point hΓ p fun S hS => ?_
      by_cases hS1 : S = 1
      · rw [hS1, one_smul]
      · have hmem : (Sum.inl p : Hbar) ∈ MulAction.fixedBy Hbar S := by
          rw [hall S hS hS1, hp]
          exact Set.mem_singleton _
        exact Sum.inl.inj hmem
    · obtain ⟨α, hα⟩ := fixedBy_of_isParabolic hpa
      exact k92f_cyclic_of_one_end hΓ α fun S hS hS1 => (hall S hS hS1).trans hα
    · obtain ⟨α, β, hαβ, hαβ'⟩ := fixedBy_of_isHyperbolic hh
      exact k92f_cyclic_of_two_ends hΓ α β hαβ fun S hS hS1 => (hall S hS hS1).trans hαβ'

/-- **Theorem 2.3.6** (§2.3; l. 901). Every abelian Fuchsian group is cyclic. -/
theorem thm2_3_6 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) (hab : ∀ a ∈ Γ, ∀ b ∈ Γ, a * b = b * a) :
    IsCyclic Γ := by
  -- commuting non-identity elements have the same fixed-point set (Theorem 2.3.2)
  exact thm2_3_5 hΓ fun S hS T hT hS1 hT1 => k92f_fix_eq_of_commute hS1 hT1 (hab S hS T hT)

/-- **Corollary 2.3.7** (§2.3; l. 905; cited at l. 1709). No Fuchsian group is isomorphic to `ℤ × ℤ`. -/
theorem cor2_3_7 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) : IsEmpty (Γ ≃* Multiplicative (ℤ × ℤ)) := by
  refine ⟨fun e => ?_⟩
  -- Γ would be abelian, hence cyclic (Theorem 2.3.6), and so would `ℤ × ℤ`
  have hab : ∀ a ∈ Γ, ∀ b ∈ Γ, a * b = b * a := fun a ha b hb => by
    have e1 : e (⟨a, ha⟩ * ⟨b, hb⟩) = e (⟨b, hb⟩ * ⟨a, ha⟩) := by rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val (e.injective e1)
  have hcyc : IsCyclic Γ := thm2_3_6 hΓ hab
  exact k92f_not_cyclic_zz (isCyclic_of_surjective e.toMonoidHom e.surjective)

/-- **Theorem 2.3.8** (§2.3; l. 913). The normalizer in PSL(2,ℝ) of a non-abelian Fuchsian group is Fuchsian. -/
theorem thm2_3_8 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) (hna : ¬ ∀ a ∈ Γ, ∀ b ∈ Γ, a * b = b * a) :
    IsFuchsian (Subgroup.normalizer (Γ : Set PSL(2, ℝ))) := by
  rw [IsFuchsian, discreteTopology_iff_tendsto_one]
  intro T hT hlim
  push Not at hna
  obtain ⟨a, ha, b, hb, hab⟩ := hna
  have ha1 : a ≠ 1 := by
    rintro rfl
    simp at hab
  have hb1 : b ≠ 1 := by
    rintro rfl
    simp at hab
  -- `Tₙ s Tₙ⁻¹ s⁻¹ ∈ Γ` tends to `1`, so eventually `Tₙ` commutes with `s` (Γ is discrete)
  have hcomm : ∀ s ∈ Γ, ∀ᶠ n in atTop, T n * s = s * T n := by
    intro s hs
    have hconv : Tendsto (fun n => T n * s * (T n)⁻¹ * s⁻¹) atTop (𝓝 1) := by
      have := ((hlim.mul (tendsto_const_nhds (x := s))).mul hlim.inv).mul (tendsto_const_nhds (x := s⁻¹))
      simpa using this
    have hmem : ∀ n, T n * s * (T n)⁻¹ * s⁻¹ ∈ Γ := fun n =>
      Γ.mul_mem ((Subgroup.mem_normalizer_iff.1 (hT n) s).1 hs) (Γ.inv_mem hs)
    filter_upwards [(discreteTopology_iff_tendsto_one Γ).1 hΓ _ hmem hconv] with n hn
    calc T n * s = (T n * s * (T n)⁻¹ * s⁻¹) * (s * T n) := by group
      _ = s * T n := by rw [hn, one_mul]
  -- a non-identity `Tₙ` commuting with `a` and `b` would give them the same fixed-point set
  filter_upwards [hcomm a ha, hcomm b hb] with n h1 h2
  by_contra hT1
  have e1 := k92f_fix_eq_of_commute hT1 ha1 h1
  have e2 := k92f_fix_eq_of_commute hT1 hb1 h2
  exact hab (k92f_commute_of_fix_eq ha1 hb1 (e1.symm.trans e2))

end Katok1992
