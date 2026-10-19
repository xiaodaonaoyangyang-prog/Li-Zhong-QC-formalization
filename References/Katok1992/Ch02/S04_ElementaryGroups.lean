import References.Katok1992.Ch02.S03_AlgebraicProperties

/-!
# Katok 1992, Ch. 2 §2.4 Elementary groups

S. Katok, *Fuchsian Groups* (1992), Chapter 2 *Fuchsian Groups*, §2.4; source `full.md` of
`Fuchsian groups (Katok, Svetlana) …-3766f6b7…`, lines 917–1133.

* Definition (the action on `ℍ̃ = ℍ ∪ ℝ ∪ {∞}`, l. 919) — exists: `Katok1992.pslActionBoundary` `Katok1992.Hbar`
  (defined in §2.1, where it is first used; the action on the Sum is Mathlib's)
* Definition (elementary subgroup, l. 921; cited throughout §2.4 and at l. 1776, 2120, 2343, 2583, 2653) —
  `IsElementary`
* Definition (the commutator `[g, h] = g h g⁻¹ h⁻¹`, l. 925) — exists: `commutatorElement` (the same word)
* Theorem 2.4.1 (l. 927; cited at l. 951) — `thm2_4_1`
* Corollary 2.4.2 (l. 931; cited at l. 937, 945, 1594) — `cor2_4_2`
* Theorem 2.4.3 (l. 935; cited at l. 1133) — `thm2_4_3`
* Theorem 2.4.4 (l. 949; cited at l. 963) — `thm2_4_4`
* Unlabelled (l. 959, Exercise 2.13 stated in the text; used at l. 985, 1127) — `exists_infinite_hyperbolic`
* Theorem 2.4.5 (l. 961) — `thm2_4_5`
* Theorem 2.4.6 (Jørgensen's inequality, "(2.5.1)" [label sic], l. 991–997; cited at l. 1127) — `thm2_4_6`,
  `thm2_4_6_sharp`
* Lemma 2.4.7 (l. 1001; cited at l. 1013, 1019) — `lemma2_4_7`, `conjSeq`
* Theorem 2.4.8 (l. 1119; cited at l. 3263, 3297 (hints)) — `thm2_4_8`

Not items (DESIGN §3): "an orbit lies wholly in ℍ or wholly in `ℝ ∪ {∞}`" (l. 923; immediate from the Sum action);
"`tr[g, h]` is well defined" (l. 925; absorbed by stating traces of words on SL(2,ℝ) lifts); (2.5.2), (2.5.3)
(l. 1016, 1030; inside the proof of Theorem 2.4.6, (2.5.3) is `conjSeq`); the exercises.

**Conventions.** As in §2.1–§2.3. `⟨T, S⟩` is `Subgroup.closure {T, S}`. Traces of words are taken on SL(2,ℝ) lifts
`T S : SL(2, ℝ)` with images `(T : PSL(2, ℝ))`; the expressions used are lift-independent (l. 925, 1019). The book
labels the displays of §2.4 "(2.5.1)–(2.5.3)" (sic); the names follow the theorem numbers.
-/

open Complex Set Metric Filter Topology
open scoped UpperHalfPlane MatrixGroups

noncomputable section

namespace Katok1992

/-- **Definition** (§2.4; l. 921). Γ ≤ PSL(2,ℝ) is elementary if some Γ-orbit in ℍ̃ is finite. -/
def IsElementary (Γ : Subgroup PSL(2, ℝ)) : Prop := ∃ x : Hbar, (MulAction.orbit Γ x).Finite

/-- Auxiliary (§2.4). A subgroup preserving a finite nonempty subset of `ℍ̃` is elementary: the orbit of a point of
the set stays in the set. -/
theorem k92el_of_finite_inv {Γ : Subgroup PSL(2, ℝ)} {F : Set Hbar} (hF : F.Finite) (hne : F.Nonempty)
    (h : ∀ T ∈ Γ, ∀ x ∈ F, T • x ∈ F) : IsElementary Γ := by
  obtain ⟨x, hx⟩ := hne
  refine ⟨x, hF.subset ?_⟩
  rintro _ ⟨⟨T, hT⟩, rfl⟩
  exact h T hT x hx

/-- Auxiliary (§2.4). If `T` and `S` map a finite nonempty set `F ⊆ ℍ̃` into itself, then `⟨T, S⟩` is elementary
(finite injective self-maps are bijective, so `T⁻¹`, `S⁻¹` and all words preserve `F`). -/
theorem k92el_closure_of_finite_inv {T S : PSL(2, ℝ)} {F : Set Hbar} (hF : F.Finite) (hne : F.Nonempty)
    (hT : ∀ x ∈ F, T • x ∈ F) (hS : ∀ x ∈ F, S • x ∈ F) : IsElementary (Subgroup.closure {T, S}) := by
  -- an injective self-map of the finite set `F` is onto, so its inverse also preserves `F`
  have hperm : ∀ U : PSL(2, ℝ), (∀ x ∈ F, U • x ∈ F) → ∀ x ∈ F, U⁻¹ • x ∈ F := fun U hU x hx => by
    obtain ⟨y, hy, rfl⟩ := ((hF.injOn_iff_bijOn_of_mapsTo hU).1 (MulAction.injective U).injOn).surjOn hx
    rwa [inv_smul_smul]
  refine k92el_of_finite_inv hF hne fun U hU => ?_
  induction hU using Subgroup.closure_induction with
  | mem U hU =>
    rcases hU with rfl | rfl
    · exact hT
    · exact hS
  | one =>
    intro x hx
    rwa [one_smul]
  | mul U V _ _ hU hV =>
    intro x hx
    rw [mul_smul]
    exact hU _ (hV x hx)
  | inv U _ hU => exact hperm U hU

/-- Auxiliary (§2.4). A non-zero power of a hyperbolic or parabolic element is not the identity and has the same
fixed points (it commutes with the element: Theorem 2.3.2). -/
theorem k92el_pow_fix {T : PSL(2, ℝ)} (hT : IsHyperbolic T ∨ IsParabolic T) {m : ℤ} (hm : m ≠ 0) :
    T ^ m ≠ 1 ∧ MulAction.fixedBy Hbar (T ^ m) = MulAction.fixedBy Hbar T := by
  obtain ⟨w, δ, hδ, hsep⟩ := k92e_pow_sep hT
  have hm1 : T ^ m ≠ 1 := fun h => by
    have := hsep m hm
    rw [h, one_smul, dist_self] at this
    linarith
  have hT1 : T ≠ 1 := by
    rcases hT with h | h
    · exact k92f_ne_one_of_hyp h
    · exact h.2
  exact ⟨hm1, k92f_fix_eq_of_commute hm1 hT1 ((Commute.refl T).zpow_left m).eq⟩

/-- Auxiliary (§2.4). An element mapping a finite set `F ⊆ ℍ̃` into itself has, at each point of `F`, a positive
power fixing that point (pigeonhole). -/
theorem k92el_pow_fix_of_finite_inv {T : PSL(2, ℝ)} {F : Set Hbar} (hF : F.Finite) (hT : ∀ x ∈ F, T • x ∈ F)
    {x : Hbar} (hx : x ∈ F) : ∃ m : ℕ, 0 < m ∧ T ^ m • x = x := by
  have hmaps : ∀ n : ℕ, T ^ n • x ∈ F := fun n => by
    induction n with
    | zero => rwa [pow_zero, one_smul]
    | succ n ih =>
      rw [pow_succ', mul_smul]
      exact hT _ ih
  -- `n ↦ Tⁿ x` takes values in the finite set `F`, so it is not injective
  obtain ⟨a, b, hab, he⟩ : ∃ a b : ℕ, a < b ∧ T ^ a • x = T ^ b • x := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective fun n : ℕ => T ^ n • x := fun a b h => by
      rcases lt_trichotomy a b with h' | h' | h'
      · exact absurd h (hcon a b h')
      · exact h'
      · exact absurd h.symm (hcon b a h')
    exact Set.infinite_range_of_injective hinj (hF.subset (range_subset_iff.2 hmaps))
  refine ⟨b - a, Nat.sub_pos_of_lt hab, ?_⟩
  have e : T ^ a • (T ^ (b - a) • x) = T ^ a • x := by
    rw [← mul_smul, ← pow_add, Nat.add_sub_cancel' hab.le, he]
  exact smul_left_cancel _ e

/-- Auxiliary (§2.4). A hyperbolic or parabolic element has no finite orbits besides its fixed points: a finite set it
maps into itself consists of fixed points. -/
theorem k92el_finite_inv_subset_fix {T : PSL(2, ℝ)} (hT : IsHyperbolic T ∨ IsParabolic T) {F : Set Hbar}
    (hF : F.Finite) (hinv : ∀ x ∈ F, T • x ∈ F) : F ⊆ MulAction.fixedBy Hbar T := by
  intro x hx
  obtain ⟨m, hm, hfix⟩ := k92el_pow_fix_of_finite_inv hF hinv hx
  have hfe := (k92el_pow_fix hT (m := (m : ℤ)) (by exact_mod_cast hm.ne')).2
  have hmem : x ∈ MulAction.fixedBy Hbar (T ^ (m : ℤ)) := by
    show T ^ (m : ℤ) • x = x
    rwa [zpow_natCast]
  rwa [hfe] at hmem

/-- Auxiliary (§2.4). An element of PSL(2,ℝ) fixing three distinct points of `ℍ̃` is the identity (a non-identity
element has at most two fixed points: Theorem 2.1.1's classification, `k92f_shape`). -/
theorem k92el_eq_one_of_three {T : PSL(2, ℝ)} {x y z : Hbar} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : T • x = x) (hy : T • y = y) (hz : T • z = z) : T = 1 := by
  by_contra hT
  -- the fixed-point set lies in a pair `{a, b}`
  obtain ⟨a, b, hab⟩ : ∃ a b : Hbar, MulAction.fixedBy Hbar T ⊆ {a, b} := by
    rcases k92f_trichotomy hT with h | h | h
    · obtain ⟨p, hp⟩ := fixedBy_of_isElliptic h
      exact ⟨Sum.inl p, Sum.inl p, by rw [hp]; exact subset_insert _ _⟩
    · obtain ⟨α, hα⟩ := fixedBy_of_isParabolic h
      exact ⟨Sum.inr α, Sum.inr α, by rw [hα]; exact subset_insert _ _⟩
    · obtain ⟨α, β, -, hαβ⟩ := fixedBy_of_isHyperbolic h
      exact ⟨Sum.inr α, Sum.inr β, hαβ.le⟩
  have hsub : ({x, y, z} : Set Hbar) ⊆ {a, b} := by
    rintro w (rfl | rfl | rfl)
    · exact hab hx
    · exact hab hy
    · exact hab hz
  have h3 : ({x, y, z} : Set Hbar).ncard = 3 := Set.ncard_eq_three.2 ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have h2 : ({a, b} : Set Hbar).ncard ≤ 2 := by
    refine (Set.ncard_insert_le a {b}).trans ?_
    rw [Set.ncard_singleton]
  have := Set.ncard_le_ncard hsub (toFinite _)
  omega

/-- Auxiliary (§2.4). The fixed-point set of a non-identity element is finite and nonempty. -/
theorem k92el_finite_fixedBy {T : PSL(2, ℝ)} (hT : T ≠ 1) :
    (MulAction.fixedBy Hbar T).Finite ∧ (MulAction.fixedBy Hbar T).Nonempty := by
  rcases k92f_trichotomy hT with h | h | h
  · obtain ⟨p, hp⟩ := fixedBy_of_isElliptic h
    rw [hp]
    exact ⟨finite_singleton _, singleton_nonempty _⟩
  · obtain ⟨α, hα⟩ := fixedBy_of_isParabolic h
    rw [hα]
    exact ⟨finite_singleton _, singleton_nonempty _⟩
  · obtain ⟨α, β, -, hαβ⟩ := fixedBy_of_isHyperbolic h
    rw [hαβ]
    exact ⟨toFinite _, insert_nonempty _ _⟩

/-- Auxiliary (§2.4). `Fix(C T C⁻¹) = C(Fix T)`. -/
theorem k92el_fixedBy_conj (C T : PSL(2, ℝ)) :
    MulAction.fixedBy Hbar (C * T * C⁻¹) = (C • ·) '' MulAction.fixedBy Hbar T := by
  ext y
  constructor
  · intro hy
    refine ⟨C⁻¹ • y, ?_, smul_inv_smul C y⟩
    have h1 : (C * T * C⁻¹) • y = y := hy
    rw [mul_smul, mul_smul] at h1
    show T • (C⁻¹ • y) = C⁻¹ • y
    exact eq_inv_smul_iff.2 h1
  · rintro ⟨z, hz, rfl⟩
    show (C * T * C⁻¹) • (C • z) = C • z
    rw [mul_smul, mul_smul, inv_smul_smul, show T • z = z from hz]

/-- Auxiliary (§2.4, proof of Lemma 2.4.7). If a conjugate `C T C⁻¹` of `T ≠ Id` maps `Fix T` into itself, it fixes
`Fix T` pointwise (a singleton is fixed; a hyperbolic conjugate cannot move its finite invariant set). -/
theorem k92el_conj_fix_of_preserve {T C : PSL(2, ℝ)} (hT : T ≠ 1)
    (h : ∀ x ∈ MulAction.fixedBy Hbar T, (C * T * C⁻¹) • x ∈ MulAction.fixedBy Hbar T) :
    MulAction.fixedBy Hbar T ⊆ MulAction.fixedBy Hbar (C * T * C⁻¹) := by
  have hTr : Tr (C * T * C⁻¹) = Tr T := by
    have := tr_conj C⁻¹ T
    rwa [inv_inv] at this
  have hC1 : C * T * C⁻¹ ≠ 1 := fun h1 => hT (by
    calc T = C⁻¹ * (C * T * C⁻¹) * C := by group
      _ = 1 := by rw [h1]; group)
  have hfin := (k92el_finite_fixedBy hT).1
  rcases k92f_trichotomy hT with he | hp | hh
  · -- a single fixed point is fixed by any element preserving it
    obtain ⟨p, hp⟩ := fixedBy_of_isElliptic he
    intro x hx
    have hx' := h x hx
    rw [hp, mem_singleton_iff] at hx hx'
    show (C * T * C⁻¹) • x = x
    rw [hx', hx]
  · exact k92el_finite_inv_subset_fix (Or.inr ⟨hTr.trans hp.1, hC1⟩) hfin h
  · exact k92el_finite_inv_subset_fix (Or.inl (show 2 < Tr (C * T * C⁻¹) by rw [hTr]; exact hh)) hfin h

/-- Helper (§2.4, proof of Theorem 2.4.1). The commutator trace of a rotation `r` about `i` and any `s`:
`tr(r s r⁻¹ s⁻¹) = 2 + r₁₀² ((s₀₀ − s₁₁)² + (s₀₁ + s₁₀)²)`. -/
theorem k92el_trace_comm_rot (r s : SL(2, ℝ)) (h00 : r 0 0 = r 1 1) (h01 : r 0 1 = -r 1 0) :
    Matrix.trace ((r * s * r⁻¹ * s⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      2 + (r 1 0) ^ 2 * ((s 0 0 - s 1 1) ^ 2 + (s 0 1 + s 1 0) ^ 2) := by
  have hr := r.2
  have hs := s.2
  rw [Matrix.det_fin_two] at hr hs
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [h00, h01] at *
  linear_combination (2 * (s 0 0 * s 1 1 - s 0 1 * s 1 0)) * hr + 2 * hs

/-- Helper. `±g` have the same image in PSL(2,ℝ). -/
theorem k92el_mk_neg (g : SL(2, ℝ)) : ((-g : SL(2, ℝ)) : PSL(2, ℝ)) = (g : PSL(2, ℝ)) := by
  have e : (-g)⁻¹ * g = -1 := by
    rw [inv_mul_eq_iff_eq_mul, neg_mul_neg, mul_one]
  rw [QuotientGroup.eq, e, Subgroup.mem_center_iff]
  intro x
  rw [mul_neg_one, neg_one_mul]

/-- Helper. Powers of a unipotent `[[1, b], [0, 1]]` are `[[1, n b], [0, 1]]`. -/
theorem k92el_unip_pow (u : SL(2, ℝ)) (h00 : u 0 0 = 1) (h10 : u 1 0 = 0) (h11 : u 1 1 = 1) (n : ℕ) :
    (u ^ n) 0 0 = 1 ∧ (u ^ n) 1 0 = 0 ∧ (u ^ n) 1 1 = 1 ∧ (u ^ n) 0 1 = n * u 0 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨a, b, c, d⟩ := ih
    rw [pow_succ]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [a, h00, d, h10]; ring
    · rw [b, c, h10]; ring
    · rw [b, c, h11]; ring
    · rw [a, d, h11]; push_cast; ring

/-- Auxiliary (§2.4, proof of Theorem 2.4.1). If `g` is elliptic with fixed point `p ∈ ℍ` and `h` does not fix `p`,
the commutator `[g, h]` is hyperbolic: after conjugating `p` to `i`,
`tr[g, h] = 2 + sin²θ ((a − d)² + (b + c)²) > 2`. -/
theorem k92el_comm_hyp {g h : PSL(2, ℝ)} (hg : IsElliptic g) {p : ℍ} (hp : g • p = p) (hh : h • p ≠ p) :
    IsHyperbolic (g * h * g⁻¹ * h⁻¹) := by
  -- conjugate `p` to `i`
  set C : PSL(2, ℝ) := (p.toSL2R : PSL(2, ℝ))
  have hCi : C • UpperHalfPlane.I = p := by rw [k92_psl_smul_mk, UpperHalfPlane.toSL2R_smul_I]
  have hTr : Tr (g * h * g⁻¹ * h⁻¹) =
      Tr ((C⁻¹ * g * C) * (C⁻¹ * h * C) * (C⁻¹ * g * C)⁻¹ * (C⁻¹ * h * C)⁻¹) := by
    rw [← tr_conj C (g * h * g⁻¹ * h⁻¹)]
    congr 1
    group
  have hgi : (C⁻¹ * g * C) • UpperHalfPlane.I = UpperHalfPlane.I := by
    rw [mul_smul, mul_smul, hCi, hp, ← hCi, inv_smul_smul]
  have hhi : (C⁻¹ * h * C) • UpperHalfPlane.I ≠ UpperHalfPlane.I := fun he => hh (by
    rw [mul_smul, mul_smul, hCi, inv_smul_eq_iff, hCi] at he
    exact he)
  have hge : IsElliptic (C⁻¹ * g * C) := by
    unfold IsElliptic
    rw [tr_conj]
    exact hg
  -- lifts: `r` is a rotation about `i`, `s` does not fix `i`
  obtain ⟨r, hr⟩ := QuotientGroup.mk_surjective (C⁻¹ * g * C)
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (C⁻¹ * h * C)
  have hpos : ∀ t : SL(2, ℝ), 0 < (Matrix.GeneralLinearGroup.det
      (Matrix.SpecialLinearGroup.mapGL ℝ t) : ℝ) := fun t => by simp
  have hri : Matrix.SpecialLinearGroup.mapGL ℝ r • UpperHalfPlane.I = UpperHalfPlane.I := by
    have := hgi
    rw [← hr, k92_psl_smul_mk] at this
    exact this
  obtain ⟨h00, h01⟩ := (UpperHalfPlane.gl_smul_I_eq_I_iff_of_pos (hpos r)).1 hri
  have h00' : r 0 0 = r 1 1 := h00
  have h01' : r 0 1 = -r 1 0 := h01
  have hsi : ¬ (s 0 0 = s 1 1 ∧ s 0 1 = -s 1 0) := fun hs' => hhi (by
    rw [← hs, k92_psl_smul_mk]
    exact (UpperHalfPlane.gl_smul_I_eq_I_iff_of_pos (hpos s)).2 hs')
  -- `r` elliptic: `|2 r₁₁| < 2`, so `r₁₀ ≠ 0` (else `r₁₁² = 1`)
  have hc : r 1 0 ≠ 0 := by
    intro h0
    have hdet := r.2
    rw [Matrix.det_fin_two, h01', h0, h00'] at hdet
    have hTrr := hge
    rw [IsElliptic, ← hr, k92_Tr_mk, Matrix.trace_fin_two] at hTrr
    change |r 0 0 + r 1 1| < 2 at hTrr
    rw [h00'] at hTrr
    have hlt := abs_lt.1 hTrr
    nlinarith [hlt.1, hlt.2]
  -- `tr[r, s] = 2 + r₁₀² ((s₀₀ − s₁₁)² + (s₀₁ + s₁₀)²) > 2`
  have e : (C⁻¹ * g * C) * (C⁻¹ * h * C) * (C⁻¹ * g * C)⁻¹ * (C⁻¹ * h * C)⁻¹ =
      ((r * s * r⁻¹ * s⁻¹ : SL(2, ℝ)) : PSL(2, ℝ)) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hr, hs]
  have hQ : 0 < (s 0 0 - s 1 1) ^ 2 + (s 0 1 + s 1 0) ^ 2 := by
    by_contra hQ
    push Not at hQ
    apply hsi
    have ha : (s 0 0 - s 1 1) ^ 2 = 0 := by nlinarith [sq_nonneg (s 0 0 - s 1 1), sq_nonneg (s 0 1 + s 1 0)]
    have hb : (s 0 1 + s 1 0) ^ 2 = 0 := by nlinarith [sq_nonneg (s 0 0 - s 1 1), sq_nonneg (s 0 1 + s 1 0)]
    constructor
    · linarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 ha]
    · linarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 hb]
  have hpos2 : 0 < r 1 0 ^ 2 * ((s 0 0 - s 1 1) ^ 2 + (s 0 1 + s 1 0) ^ 2) := by positivity
  rw [IsHyperbolic, hTr, e, k92_Tr_mk, k92el_trace_comm_rot r s h00' h01', abs_of_pos (by linarith)]
  linarith

/-- Auxiliary (§2.4, proof of Theorem 2.4.4). If `f` is parabolic with fixed point `α` and `g` does not fix `α`, some
`fⁿ g` is hyperbolic: after conjugating `f` to a translation `z ↦ z + b`, `tr(fⁿ g) = a + d + n b c` with `c ≠ 0`. -/
theorem k92el_hyp_of_par {f g : PSL(2, ℝ)} (hf : IsParabolic f) {α : OnePoint ℝ}
    (hα : MulAction.fixedBy Hbar f = {Sum.inr α}) (hg : g • (Sum.inr α : Hbar) ≠ Sum.inr α) :
    ∃ n : ℤ, IsHyperbolic (f ^ n * g) := by
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
  set C : PSL(2, ℝ) := (P : PSL(2, ℝ))
  have hCα : C • α = OnePoint.infty := by rw [k92n_bdry_smul, hP]
  -- `f' = C f C⁻¹` fixes only `∞`: a lift is `±[[1, b], [0, 1]]`, `b ≠ 0`
  obtain ⟨d, hd⟩ := QuotientGroup.mk_surjective (C * f * C⁻¹)
  have hfixd : MulAction.fixedBy Hbar (d : PSL(2, ℝ)) = {Sum.inr OnePoint.infty} := by
    rw [hd, k92f_fix_conj_single C hα, hCα]
  obtain ⟨hd10, hd0011⟩ := k92f_fix_infty_only d hfixd
  have hdet : d 0 0 * d 1 1 = 1 := by
    have := d.2
    rw [Matrix.det_fin_two, hd10] at this
    linarith
  obtain ⟨u, hu, hu00, hu10, hu11⟩ : ∃ u : SL(2, ℝ), (u : PSL(2, ℝ)) = C * f * C⁻¹ ∧
      u 0 0 = 1 ∧ u 1 0 = 0 ∧ u 1 1 = 1 := by
    have hsq : d 1 1 * d 1 1 = 1 := by
      rw [hd0011] at hdet
      exact hdet
    rcases mul_self_eq_one_iff.1 hsq with h1 | h1
    · exact ⟨d, hd, by rw [hd0011, h1], hd10, h1⟩
    · refine ⟨-d, by rw [k92el_mk_neg, hd], ?_, ?_, ?_⟩
      · show -(d 0 0) = 1
        rw [hd0011, h1]; norm_num
      · show -(d 1 0) = 0
        rw [hd10, neg_zero]
      · show -(d 1 1) = 1
        rw [h1]; norm_num
  have hb : u 0 1 ≠ 0 := by
    intro hb0
    apply hf.2
    have hu1 : u = 1 := by
      ext i j
      fin_cases i <;> fin_cases j
      · exact hu00
      · exact hb0
      · exact hu10
      · exact hu11
    have : C * f * C⁻¹ = 1 := by rw [← hu, hu1]; rfl
    calc f = C⁻¹ * (C * f * C⁻¹) * C := by group
      _ = 1 := by rw [this]; group
  -- `g' = C g C⁻¹` does not fix `∞`: a lift `e` has `e₁₀ ≠ 0`
  obtain ⟨e, he⟩ := QuotientGroup.mk_surjective (C * g * C⁻¹)
  have he10 : e 1 0 ≠ 0 := by
    intro h0
    apply hg
    have hinf : (e : PSL(2, ℝ)) • (OnePoint.infty : OnePoint ℝ) = OnePoint.infty := by
      rw [k92n_bdry_smul, OnePoint.smul_infty_eq_self_iff]
      exact h0
    rw [he, ← hCα, mul_smul, mul_smul, inv_smul_smul, smul_left_cancel_iff] at hinf
    rw [Sum.smul_inr, hinf]
  -- `tr(f'ⁿ g') = e₀₀ + e₁₁ + n b e₁₀`, which is large for large `n`
  obtain ⟨n, hn⟩ := exists_nat_gt ((2 + |e 0 0 + e 1 1|) / |u 0 1 * e 1 0|)
  refine ⟨n, ?_⟩
  obtain ⟨p00, p10, p11, p01⟩ := k92el_unip_pow u hu00 hu10 hu11 n
  have htr : Tr (f ^ (n : ℤ) * g) = |e 0 0 + e 1 1 + n * (u 0 1 * e 1 0)| := by
    have e1 : f ^ (n : ℤ) * g = C⁻¹ * (((u ^ n * e : SL(2, ℝ)) : PSL(2, ℝ))) * C := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_pow, hu, he, conj_pow, zpow_natCast]
      group
    rw [e1, tr_conj, k92_Tr_mk, Matrix.trace_fin_two]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, p00, p10, p11, p01]
    congr 1
    ring
  have hpos : 0 < |u 0 1 * e 1 0| := abs_pos.2 (mul_ne_zero hb he10)
  rw [IsHyperbolic, htr]
  have h1 : 2 + |e 0 0 + e 1 1| < n * |u 0 1 * e 1 0| := by
    rwa [div_lt_iff₀ hpos] at hn
  have h2 : (n : ℝ) * |u 0 1 * e 1 0| = |n * (u 0 1 * e 1 0)| := by
    rw [abs_mul (n : ℝ), Nat.abs_cast]
  have h3 := abs_sub_abs_le_abs_sub (n * (u 0 1 * e 1 0)) (-(e 0 0 + e 1 1))
  rw [abs_neg, sub_neg_eq_add] at h3
  have h4 : |e 0 0 + e 1 1 + n * (u 0 1 * e 1 0)| = |n * (u 0 1 * e 1 0) + (e 0 0 + e 1 1)| := by
    rw [add_comm]
  linarith

/-- Auxiliary (§2.4). A subgroup of a Fuchsian group is Fuchsian. -/
theorem k92el_fuchsian_mono {Γ Δ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) (h : Δ ≤ Γ) : IsFuchsian Δ := by
  unfold IsFuchsian at *
  exact DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion h)
    (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective h)

/-- **Theorem 2.4.1** (§2.4; l. 927). If Γ contains besides `Id` only elliptic elements, then all elements of Γ
have the same fixed point, and Γ is abelian and elementary.
[CORRECTION] The book also says "hence Γ is a cyclic group": false without discreteness (the image of `SO(2)`, the
rotations about `i`, is not cyclic); for Fuchsian Γ it is Corollary 2.4.2. -/
theorem thm2_4_1 {Γ : Subgroup PSL(2, ℝ)} (hΓ : ∀ T ∈ Γ, T ≠ 1 → IsElliptic T) :
    (∃ p : ℍ, ∀ T ∈ Γ, T • p = p) ∧ (∀ a ∈ Γ, ∀ b ∈ Γ, a * b = b * a) ∧ IsElementary Γ := by
  -- every element fixes the fixed point `p` of one non-identity element `g` (else `[g, h] ∈ Γ` is hyperbolic)
  have hfix : ∃ p : ℍ, ∀ T ∈ Γ, T • p = p := by
    by_cases htriv : ∀ T ∈ Γ, T = 1
    · exact ⟨UpperHalfPlane.I, fun T hT => by rw [htriv T hT, one_smul]⟩
    push Not at htriv
    obtain ⟨g, hgΓ, hg1⟩ := htriv
    have hge := hΓ g hgΓ hg1
    obtain ⟨p, hp⟩ := fixedBy_of_isElliptic hge
    have hgp : g • p = p := by
      have hmem : (Sum.inl p : Hbar) ∈ MulAction.fixedBy Hbar g := by rw [hp]; rfl
      have h' : g • (Sum.inl p : Hbar) = Sum.inl p := hmem
      rw [Sum.smul_inl] at h'
      exact Sum.inl_injective h'
    refine ⟨p, fun h hhΓ => ?_⟩
    by_contra hne
    have hc := k92el_comm_hyp hge hgp hne
    have hmem : g * h * g⁻¹ * h⁻¹ ∈ Γ :=
      Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hgΓ hhΓ) (Γ.inv_mem hgΓ)) (Γ.inv_mem hhΓ)
    have he := hΓ _ hmem (k92f_ne_one_of_hyp hc)
    exact absurd hc (not_lt.2 he.le)
  obtain ⟨p, hp⟩ := hfix
  -- elements fixing `p`: identity, or elliptic with fixed-point set `{p}`
  have hset : ∀ T ∈ Γ, T ≠ 1 → MulAction.fixedBy Hbar T = {Sum.inl p} := fun T hT hT1 => by
    obtain ⟨q, hq⟩ := fixedBy_of_isElliptic (hΓ T hT hT1)
    have hmem : (Sum.inl p : Hbar) ∈ MulAction.fixedBy Hbar T := by
      show T • (Sum.inl p : Hbar) = Sum.inl p
      rw [Sum.smul_inl, hp T hT]
    rw [hq] at hmem ⊢
    rw [hmem]
  refine ⟨⟨p, hp⟩, fun a ha b hb => ?_, k92el_of_finite_inv (F := {Sum.inl p}) (finite_singleton _)
    (singleton_nonempty _) fun T hT x hx => ?_⟩
  · by_cases ha1 : a = 1
    · rw [ha1, one_mul, mul_one]
    by_cases hb1 : b = 1
    · rw [hb1, one_mul, mul_one]
    exact k92f_commute_of_fix_eq ha1 hb1 ((hset a ha ha1).trans (hset b hb hb1).symm)
  · rw [mem_singleton_iff] at hx ⊢
    rw [hx, Sum.smul_inl, hp T hT]

/-- **Corollary 2.4.2** (§2.4; l. 931). A Fuchsian group containing besides `Id` only elliptic elements is finite
cyclic. -/
theorem cor2_4_2 {Γ : Subgroup PSL(2, ℝ)} (hF : IsFuchsian Γ) (hΓ : ∀ T ∈ Γ, T ≠ 1 → IsElliptic T) :
    Finite Γ ∧ IsCyclic Γ := by
  obtain ⟨⟨p, hp⟩, -, -⟩ := thm2_4_1 hΓ
  refine ⟨?_, k92f_cyclic_of_fixed_point hF p hp⟩
  have hfin := k92e_finite_of_compact hF (k92e_compact_preimage p (isCompact_singleton (x := p)))
  have huniv : (Set.univ : Set Γ) ⊆ {g : Γ | (g : PSL(2, ℝ)) ∈ {T : PSL(2, ℝ) | T • p ∈ ({p} : Set ℍ)}} :=
    fun g _ => mem_singleton_iff.2 (hp g g.2)
  exact Set.finite_univ_iff.1 (hfin.subset huniv)

/-- Auxiliary (§2.4). In a discrete group, a sequence of elements converging to an element of the group is eventually
equal to it (`y⁻¹ xₙ → Id` in Γ). -/
theorem k92el_eventually_eq {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) {x : ℕ → PSL(2, ℝ)} (hx : ∀ n, x n ∈ Γ)
    {y : PSL(2, ℝ)} (hy : y ∈ Γ) (hlim : Tendsto x atTop (𝓝 y)) : ∀ᶠ n in atTop, x n = y := by
  have h1 : Tendsto (fun n => y⁻¹ * x n) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := y⁻¹)).mul hlim
    rwa [inv_mul_cancel] at this
  filter_upwards [(discreteTopology_iff_tendsto_one Γ).1 hΓ _ (fun n => Γ.mul_mem (Γ.inv_mem hy) (hx n)) h1]
    with n hn
  calc x n = y * (y⁻¹ * x n) := by group
    _ = y := by rw [hn, mul_one]

/-- Auxiliary (§2.4). In a discrete group, a sequence of elements converging in PSL(2,ℝ) is eventually constant
(`xₙ⁻¹ xₙ₊₁ → Id` in Γ); the limit need not be known to lie in Γ. -/
theorem k92el_eventually_succ {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) {x : ℕ → PSL(2, ℝ)} (hx : ∀ n, x n ∈ Γ)
    {y : PSL(2, ℝ)} (hlim : Tendsto x atTop (𝓝 y)) : ∀ᶠ n in atTop, x (n + 1) = x n := by
  have h1 : Tendsto (fun n => (x n)⁻¹ * x (n + 1)) atTop (𝓝 1) := by
    have := hlim.inv.mul (hlim.comp (tendsto_add_atTop_nat 1))
    rwa [inv_mul_cancel] at this
  filter_upwards [(discreteTopology_iff_tendsto_one Γ).1 hΓ _
    (fun n => Γ.mul_mem (Γ.inv_mem (hx n)) (hx (n + 1))) h1] with n hn
  calc x (n + 1) = x n * ((x n)⁻¹ * x (n + 1)) := by group
    _ = x n := by rw [hn, mul_one]

/-- Auxiliary (§2.4). Two distinct points of `ℝ ∪ {∞}` can be moved to `∞` and `0` by an element of PSL(2,ℝ). -/
theorem k92el_to_infty_zero {α β : OnePoint ℝ} (hαβ : α ≠ β) :
    ∃ R : PSL(2, ℝ), R • (Sum.inr α : Hbar) = (Sum.inr OnePoint.infty : Hbar) ∧
      R • (Sum.inr β : Hbar) = (Sum.inr ((0 : ℝ) : OnePoint ℝ) : Hbar) := by
  -- move `α` to `∞`
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
  -- `β` goes to a real point `b`; the translation `z ↦ z − b` moves it to `0` and fixes `∞`
  have hβ : Matrix.SpecialLinearGroup.mapGL ℝ P • β ≠ OnePoint.infty := fun h =>
    hαβ (smul_left_cancel _ (hP.trans h.symm))
  obtain ⟨b, hb⟩ := OnePoint.ne_infty_iff_exists.1 hβ
  set U : SL(2, ℝ) := ⟨!![1, -b; 0, 1], by simp [Matrix.det_fin_two_of]⟩ with hUdef
  refine ⟨((U * P : SL(2, ℝ)) : PSL(2, ℝ)), ?_, ?_⟩
  · rw [Sum.smul_inr, k92n_bdry_smul, map_mul, mul_smul, hP, OnePoint.smul_infty_eq_self_iff.2 rfl]
  · have e : ((Matrix.SpecialLinearGroup.mapGL ℝ U : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * b +
        ((Matrix.SpecialLinearGroup.mapGL ℝ U : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ≠ 0 := by
      show (0 : ℝ) * b + 1 ≠ 0
      norm_num
    rw [Sum.smul_inr, k92n_bdry_smul, map_mul, mul_smul, ← hb, OnePoint.smul_some_eq_ite, ite_eq_right e]
    show (Sum.inr (((1 * b + -b) / (0 * b + 1) : ℝ) : OnePoint ℝ) : Hbar) = Sum.inr ((0 : ℝ) : OnePoint ℝ)
    norm_num

/-- Auxiliary (§2.4). A lift of an element interchanging `∞` and `0` has zero diagonal (`g(∞) = g₀₀/g₁₀ = 0`,
`g(0) = g₀₁/g₁₁ = ∞`). -/
theorem k92el_swap_shape (g : SL(2, ℝ))
    (h1 : (g : PSL(2, ℝ)) • (Sum.inr OnePoint.infty : Hbar) = (Sum.inr ((0 : ℝ) : OnePoint ℝ) : Hbar))
    (h2 : (g : PSL(2, ℝ)) • (Sum.inr ((0 : ℝ) : OnePoint ℝ) : Hbar) = (Sum.inr OnePoint.infty : Hbar)) :
    g 0 0 = 0 ∧ g 1 1 = 0 := by
  rw [Sum.smul_inr, k92n_bdry_smul] at h1 h2
  have h1' := Sum.inr_injective h1
  have h2' := Sum.inr_injective h2
  rw [OnePoint.smul_infty_eq_ite] at h1'
  rw [OnePoint.smul_some_eq_ite] at h2'
  have e : ∀ i j, ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = g i j :=
    fun i j => rfl
  simp only [e] at h1' h2'
  constructor
  · by_cases h10 : g 1 0 = 0
    · rw [ite_eq_left h10] at h1'
      exact absurd h1' (OnePoint.infty_ne_coe _)
    · rw [ite_eq_right h10] at h1'
      have := OnePoint.coe_injective h1'
      rwa [div_eq_zero_iff, or_iff_left h10] at this
  · by_cases h11 : g 1 0 * 0 + g 1 1 = 0
    · simpa using h11
    · rw [ite_eq_right h11] at h2'
      exact absurd h2' (OnePoint.coe_ne_infty _)

/-- Helper. A sequence in SL(2,ℝ) converges if its four entries converge. -/
theorem k92el_sl_tendsto {x : ℕ → SL(2, ℝ)} {L : SL(2, ℝ)} (h00 : Tendsto (fun n => x n 0 0) atTop (𝓝 (L 0 0)))
    (h01 : Tendsto (fun n => x n 0 1) atTop (𝓝 (L 0 1))) (h10 : Tendsto (fun n => x n 1 0) atTop (𝓝 (L 1 0)))
    (h11 : Tendsto (fun n => x n 1 1) atTop (𝓝 (L 1 1))) : Tendsto x atTop (𝓝 L) := by
  refine Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing.tendsto_nhds_iff.2 ?_
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  fin_cases i <;> fin_cases j
  exacts [h00, h01, h10, h11]

/-- Helper. Powers of a diagonal `diag(p, q)` are `diag(pⁿ, qⁿ)`. -/
theorem k92el_diag_pow (D : SL(2, ℝ)) (h01 : D 0 1 = 0) (h10 : D 1 0 = 0) (n : ℕ) :
    (D ^ n) 0 0 = D 0 0 ^ n ∧ (D ^ n) 0 1 = 0 ∧ (D ^ n) 1 0 = 0 ∧ (D ^ n) 1 1 = D 1 1 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨a, b, c, d⟩ := ih
    rw [pow_succ]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [a, b, h10]; ring
    · rw [a, b, h01]; ring
    · rw [c, d, h10]; ring
    · rw [c, d, h01]; ring

/-- Auxiliary (§2.4, proof of Theorem 2.4.3; used in Theorem 2.4.8). In a discrete group, an element `g` fixing one
fixed point `x` of a hyperbolic `h` (`Fix h = {x, y}`) also fixes the other. Move `x, y` to `∞, 0`: then
`h = diag(l, l⁻¹)` with `|l| < 1` (after replacing `h` by `h⁻¹`) and `g = [[a, b], [0, d]]`, so
`hⁿ g h⁻ⁿ = [[a, b l²ⁿ], [0, d]]` converges; it is eventually constant, so `g` commutes with `h`. -/
theorem k92el_share_one {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) {h g : PSL(2, ℝ)} (hh : h ∈ Γ) (hg : g ∈ Γ)
    (hyp : IsHyperbolic h) {x y : Hbar} (hfix : MulAction.fixedBy Hbar h = {x, y}) (hgx : g • x = x) :
    g • y = y := by
  by_cases hg1 : g = 1
  · rw [hg1, one_smul]
  -- `x, y` are boundary points `α ≠ β`
  obtain ⟨a, b, hab, hfab⟩ := fixedBy_of_isHyperbolic hyp
  obtain ⟨α, β, hαβ, rfl, rfl⟩ : ∃ α β : OnePoint ℝ, α ≠ β ∧ x = Sum.inr α ∧ y = Sum.inr β := by
    have e : ({x, y} : Set Hbar) = {Sum.inr a, Sum.inr b} := hfix.symm.trans hfab
    have hx : x ∈ ({Sum.inr a, Sum.inr b} : Set Hbar) := by rw [← e]; exact Or.inl rfl
    have hy : y ∈ ({Sum.inr a, Sum.inr b} : Set Hbar) := by rw [← e]; exact Or.inr rfl
    have hxy : x ≠ y := by
      rintro rfl
      have ha : (Sum.inr a : Hbar) ∈ ({x, x} : Set Hbar) := by rw [e]; exact Or.inl rfl
      have hb : (Sum.inr b : Hbar) ∈ ({x, x} : Set Hbar) := by rw [e]; exact Or.inr rfl
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_self] at ha hb
      exact hab (Sum.inr_injective (ha.trans hb.symm))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact ⟨a, b, hab, rfl, rfl⟩
    · exact ⟨b, a, hab.symm, rfl, rfl⟩
    · exact absurd rfl hxy
  have hhα : h • (Sum.inr α : Hbar) = Sum.inr α := by
    have : (Sum.inr α : Hbar) ∈ MulAction.fixedBy Hbar h := by rw [hfix]; exact Or.inl rfl
    exact this
  have hhβ : h • (Sum.inr β : Hbar) = Sum.inr β := by
    have : (Sum.inr β : Hbar) ∈ MulAction.fixedBy Hbar h := by rw [hfix]; exact Or.inr rfl
    exact this
  have hh1 : h ≠ 1 := k92f_ne_one_of_hyp hyp
  -- conjugate `α, β` to `∞, 0`
  obtain ⟨R, hRα, hRβ⟩ := k92el_to_infty_zero hαβ
  have hconj : ∀ A : PSL(2, ℝ), ∀ p q : Hbar, R • p = q → A • p = p → (R * A * R⁻¹) • q = q :=
    fun A p q hpq hA => by rw [← hpq, mul_smul, mul_smul, inv_smul_smul, hA]
  -- `R h R⁻¹ = ±diag(l, l⁻¹)` with `|l| ≠ 1`
  obtain ⟨h₁, hh₁⟩ := QuotientGroup.mk_surjective (R * h * R⁻¹)
  obtain ⟨h₁10, h₁01⟩ := (k92f_fix_zero_infty h₁).1
    ⟨by rw [MulAction.mem_fixedBy, hh₁]; exact hconj h _ _ hRα hhα,
      by rw [MulAction.mem_fixedBy, hh₁]; exact hconj h _ _ hRβ hhβ⟩
  obtain ⟨l, h₁00⟩ : ∃ l, h₁ 0 0 = l := ⟨_, rfl⟩
  have hdet₁ : l * h₁ 1 1 = 1 := by
    have := h₁.2
    rw [Matrix.det_fin_two, h₁10, h₁00] at this
    linarith
  have h₁11 : h₁ 1 1 = l⁻¹ := eq_inv_of_mul_eq_one_right hdet₁
  have hl1 : |l| ≠ 1 := by
    intro hl
    have htr : Tr (R * h * R⁻¹) = Tr h := by simpa using tr_conj R⁻¹ h
    rw [← hh₁, k92_Tr_mk, Matrix.trace_fin_two, h₁00, h₁11] at htr
    rw [IsHyperbolic, ← htr] at hyp
    rcases (abs_eq zero_le_one).1 hl with e | e
    · rw [e] at hyp; norm_num at hyp
    · rw [e] at hyp; norm_num at hyp
  -- choose `K ∈ {h, h⁻¹}` whose conjugate is `D = diag(m, m⁻¹)` with `|m| < 1`
  obtain ⟨K, hKΓ, hK1, hKfix, D, m, hDK, hm, hD00, hD01, hD10, hD11⟩ : ∃ K ∈ Γ, K ≠ 1 ∧
      MulAction.fixedBy Hbar K = MulAction.fixedBy Hbar h ∧ ∃ D : SL(2, ℝ), ∃ m : ℝ,
      (D : PSL(2, ℝ)) = R * K * R⁻¹ ∧ |m| < 1 ∧ D 0 0 = m ∧ D 0 1 = 0 ∧ D 1 0 = 0 ∧ D 1 1 = m⁻¹ := by
    rcases lt_or_gt_of_ne hl1 with hlt | hgt
    · exact ⟨h, hh, hh1, rfl, h₁, l, hh₁, hlt, h₁00, h₁01, h₁10, h₁11⟩
    · refine ⟨h⁻¹, Γ.inv_mem hh, inv_ne_one.2 hh1, MulAction.fixedBy_inv Hbar h, h₁⁻¹, l⁻¹, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [QuotientGroup.mk_inv, hh₁]
        group
      · rw [abs_inv]
        exact inv_lt_one_of_one_lt₀ hgt
      · simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, h₁11]
      · simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, h₁01]
      · simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, h₁10]
      · simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, h₁00]
  have hm0 : m ≠ 0 := by
    intro e
    have := D.2
    rw [Matrix.det_fin_two, hD00, hD01, e] at this
    norm_num at this
  -- `R g R⁻¹` fixes `∞`: a lift `g₁` is upper triangular
  obtain ⟨g₁, hg₁⟩ := QuotientGroup.mk_surjective (R * g * R⁻¹)
  have hg₁10 : g₁ 1 0 = 0 := by
    have h1 := hconj g _ _ hRα hgx
    rw [← hg₁, Sum.smul_inr, k92n_bdry_smul] at h1
    exact OnePoint.smul_infty_eq_self_iff.1 (Sum.inr_injective h1)
  have hgdet : g₁ 0 0 * g₁ 1 1 = 1 := by
    have := g₁.2
    rw [Matrix.det_fin_two, hg₁10] at this
    linarith
  -- `Dⁿ g₁ D⁻ⁿ = [[g₀₀, m²ⁿ g₀₁], [0, g₁₁]]` converges to `diag(g₀₀, g₁₁)`
  have hDi01 : (D⁻¹) 0 1 = 0 := by simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hD01]
  have hDi10 : (D⁻¹) 1 0 = 0 := by simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hD10]
  have hDi00 : (D⁻¹) 0 0 = m⁻¹ := by simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hD11]
  have hDi11 : (D⁻¹) 1 1 = m := by simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hD00]
  have hx : ∀ n : ℕ, (D ^ n * g₁ * D⁻¹ ^ n) 0 0 = g₁ 0 0 ∧ (D ^ n * g₁ * D⁻¹ ^ n) 0 1 = m ^ n * g₁ 0 1 * m ^ n ∧
      (D ^ n * g₁ * D⁻¹ ^ n) 1 0 = 0 ∧ (D ^ n * g₁ * D⁻¹ ^ n) 1 1 = g₁ 1 1 := fun n => by
    obtain ⟨p00, p01, p10, p11⟩ := k92el_diag_pow D hD01 hD10 n
    obtain ⟨q00, q01, q10, q11⟩ := k92el_diag_pow D⁻¹ hDi01 hDi10 n
    have hmm : m ^ n * m⁻¹ ^ n = 1 := by rw [← mul_pow, mul_inv_cancel₀ hm0, one_pow]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, p00, p01, p10, p11, q00,
      q01, q10, q11, hD00, hD11, hDi00, hDi11, hg₁10]
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination g₁ 0 0 * hmm
    · ring
    · ring
    · linear_combination g₁ 1 1 * hmm
  set L : SL(2, ℝ) := ⟨!![g₁ 0 0, 0; 0, g₁ 1 1], by simp [Matrix.det_fin_two_of, hgdet]⟩ with hLdef
  have hlimSL : Tendsto (fun n : ℕ => D ^ n * g₁ * D⁻¹ ^ n) atTop (𝓝 L) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hm
    have h01 : Tendsto (fun n : ℕ => m ^ n * g₁ 0 1 * m ^ n) atTop (𝓝 0) := by
      have := (hpow.mul (tendsto_const_nhds (x := g₁ 0 1))).mul hpow
      rwa [zero_mul, zero_mul] at this
    refine k92el_sl_tendsto ?_ ?_ ?_ ?_
    · exact (tendsto_const_nhds (x := g₁ 0 0)).congr fun n => (hx n).1.symm
    · exact h01.congr fun n => (hx n).2.1.symm
    · exact (tendsto_const_nhds (x := (0 : ℝ))).congr fun n => (hx n).2.2.1.symm
    · exact (tendsto_const_nhds (x := g₁ 1 1)).congr fun n => (hx n).2.2.2.symm
  -- pulled back by `R`, these are `Kⁿ g K⁻ⁿ ∈ Γ`, which converge
  have hy : ∀ n : ℕ, R⁻¹ * ((D ^ n * g₁ * D⁻¹ ^ n : SL(2, ℝ)) : PSL(2, ℝ)) * R = K ^ n * g * K⁻¹ ^ n := fun n => by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow,
      QuotientGroup.mk_inv, hDK, hg₁, show (R * K * R⁻¹)⁻¹ = R * K⁻¹ * R⁻¹ by group, conj_pow, conj_pow]
    group
  have hconv : Tendsto (fun n : ℕ => R⁻¹ * ((D ^ n * g₁ * D⁻¹ ^ n : SL(2, ℝ)) : PSL(2, ℝ)) * R) atTop
      (𝓝 (R⁻¹ * (L : PSL(2, ℝ)) * R)) :=
    (tendsto_const_nhds.mul ((QuotientGroup.continuous_mk.tendsto L).comp hlimSL)).mul tendsto_const_nhds
  have hyΓ : ∀ n : ℕ, K ^ n * g * K⁻¹ ^ n ∈ Γ := fun n =>
    Γ.mul_mem (Γ.mul_mem (Γ.pow_mem hKΓ n) hg) (Γ.pow_mem (Γ.inv_mem hKΓ) n)
  -- eventually constant, so `g` commutes with `K`
  obtain ⟨n, hn⟩ := (k92el_eventually_succ hΓ hyΓ (hconv.congr hy)).exists
  have e1 : K ^ n * (K * g * K⁻¹) * K⁻¹ ^ n = K ^ n * g * K⁻¹ ^ n := by
    rw [← hn]
    group
  have e2 : K * g * K⁻¹ = g := mul_left_cancel (mul_right_cancel e1)
  have hcomm : g * K = K * g := by
    calc g * K = K * g * K⁻¹ * K := by rw [e2]
      _ = K * g := by group
  have hfixg := k92f_fix_eq_of_commute hg1 hK1 hcomm
  have : (Sum.inr β : Hbar) ∈ MulAction.fixedBy Hbar g := by
    rw [hfixg, hKfix, hfix]
    exact Or.inr rfl
  exact this

/-- Auxiliary (§2.4, proof of Theorem 2.4.3, Cases 1 and 3). If a finite Γ-orbit contains a point of `ℍ`, or has
more than two points, then every non-identity element of Γ is elliptic: hyperbolic and parabolic elements fix every
point of a finite invariant set (`k92el_finite_inv_subset_fix`), and their fixed points are at most two, all on the
boundary. -/
theorem k92el_all_elliptic {Γ : Subgroup PSL(2, ℝ)} {x : Hbar} (hfin : (MulAction.orbit Γ x).Finite)
    (hx : (∃ p : ℍ, x = Sum.inl p) ∨ 2 < (MulAction.orbit Γ x).ncard) : ∀ T ∈ Γ, T ≠ 1 → IsElliptic T := by
  intro T hT hT1
  -- the orbit is a finite set mapped into itself by `T`
  have hinv : ∀ y ∈ MulAction.orbit Γ x, T • y ∈ MulAction.orbit Γ x := fun y hy => by
    obtain ⟨γ, rfl⟩ := hy
    exact ⟨⟨T, hT⟩ * γ, mul_smul _ _ _⟩
  have hx0 : x ∈ MulAction.orbit Γ x := MulAction.mem_orbit_self x
  rcases k92f_trichotomy hT1 with h | h | h
  · exact h
  · -- parabolic: the orbit lies in `Fix T = {α}`
    exfalso
    obtain ⟨α, hα⟩ := fixedBy_of_isParabolic h
    have hsub := k92el_finite_inv_subset_fix (Or.inr h) hfin hinv
    rw [hα] at hsub
    rcases hx with ⟨p, rfl⟩ | hx
    · exact Sum.inl_ne_inr (hsub hx0)
    · have := Set.ncard_le_ncard hsub (Set.finite_singleton _)
      rw [Set.ncard_singleton] at this
      omega
  · -- hyperbolic: the orbit lies in `Fix T = {α, β}`
    exfalso
    obtain ⟨α, β, -, hαβ⟩ := fixedBy_of_isHyperbolic h
    have hsub := k92el_finite_inv_subset_fix (Or.inl h) hfin hinv
    rw [hαβ] at hsub
    rcases hx with ⟨p, rfl⟩ | hx
    · rcases hsub hx0 with h' | h'
      · exact Sum.inl_ne_inr h'
      · exact Sum.inl_ne_inr h'
    · have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 := Set.ncard_insert_le (Sum.inr α : Hbar) {Sum.inr β}
      rw [Set.ncard_singleton] at h2
      omega

/-- Auxiliary (§2.4, proof of Theorem 2.4.3, Case 2, `|orbit| = 1`). A Fuchsian group fixing a boundary point `α` is
cyclic. Its non-identity elements are parabolic or hyperbolic (elliptic ones fix no boundary point). If one of them,
`h`, is hyperbolic with `Fix h = {α, β}`, then every element fixes `β` too (`k92el_share_one`), so all fix exactly
`{α, β}` (`k92f_cyclic_of_two_ends`); otherwise all are parabolic fixing `α` (`k92f_cyclic_of_one_end`). -/
theorem k92el_fix_one_cyclic {Γ : Subgroup PSL(2, ℝ)} (hF : IsFuchsian Γ) {α : OnePoint ℝ}
    (hT : ∀ T ∈ Γ, T • (Sum.inr α : Hbar) = Sum.inr α) : IsCyclic Γ := by
  -- non-identity elements fix the boundary point `α`, so none is elliptic
  have hnell : ∀ T ∈ Γ, ¬ IsElliptic T := fun T hTΓ he => by
    obtain ⟨p, hp⟩ := fixedBy_of_isElliptic he
    have h1 : (Sum.inr α : Hbar) ∈ MulAction.fixedBy Hbar T := hT T hTΓ
    rw [hp] at h1
    exact Sum.inr_ne_inl h1
  by_cases hhyp : ∃ h ∈ Γ, IsHyperbolic h
  · -- a hyperbolic `h` with `Fix h = {α, β}`: every element fixes `β` too (I0e)
    obtain ⟨h, hh, hyp⟩ := hhyp
    obtain ⟨a, b, hab, hfix⟩ := fixedBy_of_isHyperbolic hyp
    have hαfix : (Sum.inr α : Hbar) ∈ MulAction.fixedBy Hbar h := hT h hh
    obtain ⟨β, hαβ, hfix'⟩ : ∃ β : OnePoint ℝ, α ≠ β ∧ MulAction.fixedBy Hbar h = {Sum.inr α, Sum.inr β} := by
      rw [hfix] at hαfix
      rcases hαfix with e | e
      · obtain rfl := Sum.inr_injective e
        exact ⟨b, hab, hfix⟩
      · obtain rfl := Sum.inr_injective (Set.mem_singleton_iff.1 e)
        exact ⟨a, hab.symm, by rw [hfix, Set.pair_comm]⟩
    refine k92f_cyclic_of_two_ends hF α β hαβ fun T hTΓ hT1 => ?_
    have h1 : (Sum.inr α : Hbar) ∈ MulAction.fixedBy Hbar T := hT T hTΓ
    have h2 : (Sum.inr β : Hbar) ∈ MulAction.fixedBy Hbar T := k92el_share_one hF hh hTΓ hyp hfix' (hT T hTΓ)
    rcases k92f_trichotomy hT1 with he | hp | hy
    · exact absurd he (hnell T hTΓ)
    · -- a parabolic element has only one fixed point
      obtain ⟨γ, hγ⟩ := fixedBy_of_isParabolic hp
      rw [hγ] at h1 h2
      exact absurd (Sum.inr_injective ((Set.mem_singleton_iff.1 h1).trans (Set.mem_singleton_iff.1 h2).symm)) hαβ
    · obtain ⟨γ, δ, hγδ, hfixT⟩ := fixedBy_of_isHyperbolic hy
      rw [hfixT] at h1 h2 ⊢
      refine (Set.eq_of_subset_of_ncard_le (Set.insert_subset_iff.2 ⟨h1, Set.singleton_subset_iff.2 h2⟩) ?_
        (Set.toFinite _)).symm
      rw [Set.ncard_pair (fun e => hγδ (Sum.inr_injective e)), Set.ncard_pair (fun e => hαβ (Sum.inr_injective e))]
  · -- no hyperbolic element: every `T ≠ Id` is parabolic with `Fix T = {α}`
    push Not at hhyp
    refine k92f_cyclic_of_one_end hF α fun T hTΓ hT1 => ?_
    rcases k92f_trichotomy hT1 with he | hp | hy
    · exact absurd he (hnell T hTΓ)
    · obtain ⟨γ, hγ⟩ := fixedBy_of_isParabolic hp
      have h1 : (Sum.inr α : Hbar) ∈ MulAction.fixedBy Hbar T := hT T hTΓ
      rw [hγ, Set.mem_singleton_iff] at h1
      rw [hγ, h1]
    · exact absurd hy (hhyp T hTΓ)

/-- Helper. `±A ∈ PSL(2,ℝ)` acts on `ℍ` by `z ↦ (a z + b)/(c z + d)`. -/
theorem k92el_act (A : SL(2, ℝ)) (z : ℍ) :
    (((A : PSL(2, ℝ)) • z : ℍ) : ℂ) = ((A 0 0 : ℂ) * z + A 0 1) / ((A 1 0 : ℂ) * z + A 1 1) := by
  rw [k92_psl_smul_mk, UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]

/-- Auxiliary (§2.4, proof of Theorem 2.4.3, Case 2, `|orbit| = 2`). If `g ≠ Id` fixes the distinct boundary points
`α, β` and `S` interchanges them, one conjugation `R` makes `g` a dilation `z ↦ kz` (`k > 0`, `k ≠ 1`) and `S` the
map `z ↦ −1/z`: move `α, β` to `∞, 0` (`k92el_to_infty_zero`); then `g = diag(l, l⁻¹)`, `S = [[0, b], [−b⁻¹, 0]]`
(`k92el_swap_shape`), and a further diagonal conjugation `diag(t, t⁻¹)`, `t² = |b|⁻¹`, normalizes `S`. -/
theorem k92el_conj_pair {α β : OnePoint ℝ} (hαβ : α ≠ β) {g S : PSL(2, ℝ)} (hg : g ≠ 1)
    (hgα : g • (Sum.inr α : Hbar) = Sum.inr α) (hgβ : g • (Sum.inr β : Hbar) = Sum.inr β)
    (hSα : S • (Sum.inr α : Hbar) = Sum.inr β) (hSβ : S • (Sum.inr β : Hbar) = Sum.inr α) :
    ∃ k : ℝ, 0 < k ∧ k ≠ 1 ∧ ∃ R : PSL(2, ℝ), (∀ z : ℍ, (((R * g * R⁻¹) • z : ℍ) : ℂ) = k * z) ∧
      (∀ z : ℍ, (((R * S * R⁻¹) • z : ℍ) : ℂ) = -1 / z) := by
  obtain ⟨R₀, hRα, hRβ⟩ := k92el_to_infty_zero hαβ
  have hconj : ∀ A : PSL(2, ℝ), ∀ p q p' q' : Hbar, R₀ • p = q → R₀ • p' = q' → A • p = p' →
      (R₀ * A * R₀⁻¹) • q = q' := fun A p q p' q' hpq hpq' hA => by
    rw [← hpq, mul_smul, mul_smul, inv_smul_smul, hA, hpq']
  -- `R₀ g R₀⁻¹ = ±diag(l, l⁻¹)`
  obtain ⟨g₁, hg₁⟩ := QuotientGroup.mk_surjective (R₀ * g * R₀⁻¹)
  obtain ⟨hg10, hg01⟩ := (k92f_fix_zero_infty g₁).1
    ⟨by rw [MulAction.mem_fixedBy, hg₁]; exact hconj g _ _ _ _ hRα hRα hgα,
      by rw [MulAction.mem_fixedBy, hg₁]; exact hconj g _ _ _ _ hRβ hRβ hgβ⟩
  have hgdet : g₁ 0 0 * g₁ 1 1 = 1 := by
    have := g₁.2
    rw [Matrix.det_fin_two, hg10] at this
    linarith
  have hg0 : g₁ 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hgdet
  -- `R₀ S R₀⁻¹` interchanges `∞, 0`: a lift is `[[0, b], [c, 0]]` with `b c = −1`
  obtain ⟨s₁, hs₁⟩ := QuotientGroup.mk_surjective (R₀ * S * R₀⁻¹)
  obtain ⟨hs00, hs11⟩ := k92el_swap_shape s₁ (by rw [hs₁]; exact hconj S _ _ _ _ hRα hRβ hSα)
    (by rw [hs₁]; exact hconj S _ _ _ _ hRβ hRα hSβ)
  have hsdet : s₁ 0 1 * s₁ 1 0 = -1 := by
    have := s₁.2
    rw [Matrix.det_fin_two, hs00, hs11] at this
    linarith
  have hb0 : s₁ 0 1 ≠ 0 := left_ne_zero_of_mul (by rw [hsdet]; norm_num)
  -- the normalizing dilation `E = diag(t, t⁻¹)`, `t² = |b|⁻¹`
  obtain ⟨t, ht0, ht2⟩ : ∃ t : ℝ, 0 < t ∧ t ^ 2 * |s₁ 0 1| = 1 := by
    refine ⟨Real.sqrt (|s₁ 0 1|⁻¹), Real.sqrt_pos.2 (inv_pos.2 (abs_pos.2 hb0)), ?_⟩
    rw [Real.sq_sqrt (inv_nonneg.2 (abs_nonneg _)), inv_mul_cancel₀ (abs_ne_zero.2 hb0)]
  set E : SL(2, ℝ) := ⟨!![t, 0; 0, t⁻¹], by simp [Matrix.det_fin_two_of, ht0.ne']⟩ with hEdef
  have hE : ∀ w : ℍ, (((E : PSL(2, ℝ)) • w : ℍ) : ℂ) = (t : ℂ) ^ 2 * w := fun w => by
    rw [k92el_act]
    show ((t : ℂ) * w + ((0 : ℝ) : ℂ)) / (((0 : ℝ) : ℂ) * w + ((t⁻¹ : ℝ) : ℂ)) = (t : ℂ) ^ 2 * w
    have ht : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    push_cast
    rw [zero_mul, zero_add, add_zero, div_inv_eq_mul]
    ring
  have hEi : ∀ w : ℍ, (((E : PSL(2, ℝ))⁻¹ • w : ℍ) : ℂ) = w / (t : ℂ) ^ 2 := fun w => by
    have h := hE ((E : PSL(2, ℝ))⁻¹ • w)
    rw [smul_inv_smul] at h
    have ht : (t : ℂ) ^ 2 ≠ 0 := by exact_mod_cast pow_ne_zero 2 ht0.ne'
    rw [eq_div_iff ht, h]
    ring
  have hg' : ∀ w : ℍ, (((g₁ : PSL(2, ℝ)) • w : ℍ) : ℂ) = ((g₁ 0 0 : ℝ) : ℂ) ^ 2 * w := fun w => by
    rw [k92el_act, hg10, hg01, eq_inv_of_mul_eq_one_right hgdet]
    push_cast
    rw [zero_mul, zero_add, add_zero, div_inv_eq_mul]
    ring
  have hs' : ∀ w : ℍ, (((s₁ : PSL(2, ℝ)) • w : ℍ) : ℂ) = -((s₁ 0 1 : ℝ) : ℂ) ^ 2 / w := fun w => by
    have hc : s₁ 1 0 = -(s₁ 0 1)⁻¹ := by
      field_simp
      linear_combination hsdet
    rw [k92el_act, hs00, hs11, hc]
    have hw : (w : ℂ) ≠ 0 := w.ne_zero
    have hb : ((s₁ 0 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb0
    push_cast
    rw [zero_mul, zero_add, add_zero]
    have hden : -((s₁ 0 1 : ℝ) : ℂ)⁻¹ * w ≠ 0 := mul_ne_zero (neg_ne_zero.2 (inv_ne_zero hb)) hw
    rw [div_eq_div_iff hden hw, show -((s₁ 0 1 : ℝ) : ℂ) ^ 2 * (-((s₁ 0 1 : ℝ) : ℂ)⁻¹ * w) =
      ((s₁ 0 1 : ℝ) : ℂ) * (((s₁ 0 1 : ℝ) : ℂ) * ((s₁ 0 1 : ℝ) : ℂ)⁻¹) * w by ring, mul_inv_cancel₀ hb, mul_one]
  refine ⟨g₁ 0 0 ^ 2, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hg0)), ?_, (E : PSL(2, ℝ)) * R₀, ?_, ?_⟩
  · -- `k ≠ 1`: otherwise `g₁ = ±Id`, so `g = Id`
    intro hk
    apply hg
    have hpm : g₁ 0 0 = 1 ∨ g₁ 0 0 = -1 := mul_self_eq_one_iff.1 (by rw [← sq]; exact hk)
    have hg₁1 : (g₁ : PSL(2, ℝ)) = 1 := by
      rcases hpm with e | e
      · have h11 : g₁ 1 1 = 1 := by rw [e, one_mul] at hgdet; exact hgdet
        have : g₁ = 1 := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [e, h11, hg10, hg01]
        rw [this, QuotientGroup.mk_one]
      · have h11 : g₁ 1 1 = -1 := by rw [e] at hgdet; linarith
        have : g₁ = -1 := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [e, h11, hg10, hg01]
        rw [this, k92el_mk_neg, QuotientGroup.mk_one]
    calc g = R₀⁻¹ * (R₀ * g * R₀⁻¹) * R₀ := by group
      _ = 1 := by rw [← hg₁, hg₁1]; group
  · intro z
    have e : (E : PSL(2, ℝ)) * R₀ * g * ((E : PSL(2, ℝ)) * R₀)⁻¹ =
        (E : PSL(2, ℝ)) * (g₁ : PSL(2, ℝ)) * (E : PSL(2, ℝ))⁻¹ := by
      rw [hg₁]
      group
    have ht : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    rw [e, mul_smul, mul_smul, hE, hg', hEi]
    push_cast
    field_simp
  · intro z
    have e : (E : PSL(2, ℝ)) * R₀ * S * ((E : PSL(2, ℝ)) * R₀)⁻¹ =
        (E : PSL(2, ℝ)) * (s₁ : PSL(2, ℝ)) * (E : PSL(2, ℝ))⁻¹ := by
      rw [hs₁]
      group
    have hz : (z : ℂ) ≠ 0 := z.ne_zero
    have ht : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have h4 : ((t : ℂ) ^ 2) ^ 2 * ((s₁ 0 1 : ℝ) : ℂ) ^ 2 = 1 := by
      have : (t ^ 2) ^ 2 * s₁ 0 1 ^ 2 = 1 := by
        calc (t ^ 2) ^ 2 * s₁ 0 1 ^ 2 = (t ^ 2 * |s₁ 0 1|) ^ 2 := by rw [mul_pow, sq_abs]
          _ = 1 := by rw [ht2, one_pow]
      exact_mod_cast this
    rw [e, mul_smul, mul_smul, hE, hs', hEi]
    field_simp
    linear_combination -h4

/-- Auxiliary (§2.4, proof of Theorem 2.4.3, Case 2, `|orbit| = 2`). A Fuchsian group each of whose elements fixes or
interchanges the distinct boundary points `α, β` is cyclic or conjugate to `⟨z ↦ kz, z ↦ −1/z⟩` (`k > 1`). The
stabilizer Γ₀ of `α` is cyclic (`k92el_fix_one_cyclic`). If Γ = Γ₀, or Γ₀ = {Id} (then Γ = {Id, S}), Γ is cyclic.
Otherwise Γ = ⟨g₀, S⟩ for a generator `g₀` of Γ₀ and any interchanging `S`, and `k92el_conj_pair` normalizes the pair
(`g₀⁻¹` when `k < 1`). -/
theorem k92el_fix_two {Γ : Subgroup PSL(2, ℝ)} (hF : IsFuchsian Γ) {α β : OnePoint ℝ} (hαβ : α ≠ β)
    (hT : ∀ T ∈ Γ, (T • (Sum.inr α : Hbar) = Sum.inr α ∧ T • (Sum.inr β : Hbar) = Sum.inr β) ∨
      (T • (Sum.inr α : Hbar) = Sum.inr β ∧ T • (Sum.inr β : Hbar) = Sum.inr α)) :
    IsCyclic Γ ∨ ∃ k : ℝ, 1 < k ∧ ∃ g h R : PSL(2, ℝ),
      (∀ z : ℍ, ((g • z : ℍ) : ℂ) = k * z) ∧ (∀ z : ℍ, ((h • z : ℍ) : ℂ) = -1 / z) ∧
      Γ.map (MulAut.conj R).toMonoidHom = Subgroup.closure {g, h} := by
  have hne : (Sum.inr α : Hbar) ≠ Sum.inr β := fun e => hαβ (Sum.inr_injective e)
  by_cases hsw : ∃ S ∈ Γ, S • (Sum.inr α : Hbar) = Sum.inr β
  swap
  · -- no element interchanges `α, β`: Γ fixes `α`
    push Not at hsw
    refine Or.inl (k92el_fix_one_cyclic hF (α := α) fun T hTΓ => ?_)
    rcases hT T hTΓ with h | h
    · exact h.1
    · exact absurd h.1 (hsw T hTΓ)
  obtain ⟨S, hSΓ, hSα⟩ := hsw
  have hSβ : S • (Sum.inr β : Hbar) = Sum.inr α := by
    rcases hT S hSΓ with h | h
    · exact absurd (h.1.symm.trans hSα) hne
    · exact h.2
  -- the stabilizer Γ₀ of `α` in Γ fixes `β` too, and is cyclic
  set Γ₀ : Subgroup PSL(2, ℝ) := Γ ⊓ MulAction.stabilizer PSL(2, ℝ) (Sum.inr α : Hbar) with hΓ₀
  have hfixα : ∀ T ∈ Γ₀, T • (Sum.inr α : Hbar) = Sum.inr α := fun T hT₀ => hT₀.2
  have hfixβ : ∀ T ∈ Γ₀, T • (Sum.inr β : Hbar) = Sum.inr β := fun T hT₀ => by
    rcases hT T hT₀.1 with h | h
    · exact h.2
    · exact absurd ((hfixα T hT₀).symm.trans h.1) hne
  have hmem₀ : ∀ T ∈ Γ, T • (Sum.inr α : Hbar) = Sum.inr α → T ∈ Γ₀ := fun T hTΓ hTα => ⟨hTΓ, hTα⟩
  -- every element of Γ lies in Γ₀ or in S Γ₀
  have hsplit : ∀ T ∈ Γ, T ∈ Γ₀ ∨ S⁻¹ * T ∈ Γ₀ := fun T hTΓ => by
    rcases hT T hTΓ with h | h
    · exact Or.inl (hmem₀ T hTΓ h.1)
    · refine Or.inr (hmem₀ _ (Γ.mul_mem (Γ.inv_mem hSΓ) hTΓ) ?_)
      rw [mul_smul, h.1, inv_smul_eq_iff, hSα]
  have : IsCyclic Γ₀ := k92el_fix_one_cyclic (k92el_fuchsian_mono hF inf_le_left) hfixα
  obtain ⟨⟨g₀, hg₀⟩, hgen⟩ := IsCyclic.exists_generator (α := Γ₀)
  have hpow : ∀ T ∈ Γ₀, ∃ n : ℤ, T = g₀ ^ n := fun T hT₀ => by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨T, hT₀⟩)
    exact ⟨n, by simpa using (congrArg Subtype.val hn).symm⟩
  by_cases hg₀1 : g₀ = 1
  · -- Γ₀ is trivial: Γ = {Id, S} is cyclic
    left
    refine ⟨⟨⟨S, hSΓ⟩, fun x => ?_⟩⟩
    rcases hsplit x x.2 with h | h
    · obtain ⟨n, hn⟩ := hpow _ h
      rw [hg₀1, one_zpow] at hn
      exact Subgroup.mem_zpowers_iff.2 ⟨0, Subtype.ext (by simp [hn])⟩
    · obtain ⟨n, hn⟩ := hpow _ h
      rw [hg₀1, one_zpow, inv_mul_eq_one] at hn
      exact Subgroup.mem_zpowers_iff.2 ⟨1, Subtype.ext (by simp [hn])⟩
  -- otherwise normalize `g₀` and `S` simultaneously
  obtain ⟨k, hk0, hk1, R, hRg, hRS⟩ := k92el_conj_pair hαβ hg₀1 (hfixα g₀ hg₀) (hfixβ g₀ hg₀) hSα hSβ
  -- choose the generator `g₁ ∈ {g₀, g₀⁻¹}` with factor `> 1`
  obtain ⟨g₁, k', hg₁Γ, hk', hzp, hRg'⟩ : ∃ g₁ : PSL(2, ℝ), ∃ k' : ℝ, g₁ ∈ Γ ∧ 1 < k' ∧
      (∀ T ∈ Γ₀, ∃ n : ℤ, T = g₁ ^ n) ∧ ∀ z : ℍ, (((R * g₁ * R⁻¹) • z : ℍ) : ℂ) = k' * z := by
    rcases lt_or_gt_of_ne hk1 with hlt | hgt
    · refine ⟨g₀⁻¹, k⁻¹, Γ.inv_mem hg₀.1, one_lt_inv_iff₀.2 ⟨hk0, hlt⟩, fun T hT₀ => ?_, fun z => ?_⟩
      · obtain ⟨n, hn⟩ := hpow T hT₀
        exact ⟨-n, by rw [hn, inv_zpow', neg_neg]⟩
      · have h := hRg ((R * g₀⁻¹ * R⁻¹) • z)
        rw [← mul_smul, show R * g₀ * R⁻¹ * (R * g₀⁻¹ * R⁻¹) = 1 by group, one_smul] at h
        have hk0' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
        rw [h, Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hk0', one_mul]
    · exact ⟨g₀, k, hg₀.1, hgt, hpow, hRg⟩
  right
  refine ⟨k', hk', R * g₁ * R⁻¹, R * S * R⁻¹, R, hRg', hRS, ?_⟩
  -- Γ = ⟨g₁, S⟩
  have hΓeq : Γ = Subgroup.closure {g₁, S} := by
    apply le_antisymm
    · intro T hTΓ
      have hg₁c : g₁ ∈ Subgroup.closure {g₁, S} := Subgroup.subset_closure (Set.mem_insert _ _)
      have hSc : S ∈ Subgroup.closure {g₁, S} := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      rcases hsplit T hTΓ with h | h
      · obtain ⟨n, hn⟩ := hzp T h
        rw [hn]
        exact Subgroup.zpow_mem _ hg₁c n
      · obtain ⟨n, hn⟩ := hzp _ h
        have e : T = S * g₁ ^ n := by rw [← hn]; group
        rw [e]
        exact Subgroup.mul_mem _ hSc (Subgroup.zpow_mem _ hg₁c n)
    · rw [Subgroup.closure_le]
      exact Set.insert_subset_iff.2 ⟨hg₁Γ, Set.singleton_subset_iff.2 hSΓ⟩
  rw [hΓeq, MonoidHom.map_closure, Set.image_pair]
  rfl

/-- **Theorem 2.4.3** (§2.4; l. 935). An elementary Fuchsian group is cyclic or conjugate in PSL(2,ℝ) to the group
generated by `g(z) = kz` (`k > 1`) and `h(z) = −1/z`.
Modelling: `g`, `h` are pinned by their action (the action is faithful). -/
theorem thm2_4_3 {Γ : Subgroup PSL(2, ℝ)} (hF : IsFuchsian Γ) (hE : IsElementary Γ) :
    IsCyclic Γ ∨ ∃ k : ℝ, 1 < k ∧ ∃ g h R : PSL(2, ℝ),
      (∀ z : ℍ, ((g • z : ℍ) : ℂ) = k * z) ∧ (∀ z : ℍ, ((h • z : ℍ) : ℂ) = -1 / z) ∧
      Γ.map (MulAut.conj R).toMonoidHom = Subgroup.closure {g, h} := by
  obtain ⟨x, hfin⟩ := hE
  by_cases hA : (∃ p : ℍ, x = Sum.inl p) ∨ 2 < (MulAction.orbit Γ x).ncard
  · -- Cases 1 and 3: a finite orbit meeting ℍ, or with three or more points; only elliptic elements (Cor. 2.4.2)
    exact Or.inl (cor2_4_2 hF (k92el_all_elliptic hfin hA)).2
  push Not at hA
  obtain ⟨hx, hle⟩ := hA
  -- Case 2: the finite orbit lies in `ℝ ∪ {∞}` and has one or two points
  obtain ⟨α, rfl⟩ : ∃ α : OnePoint ℝ, x = Sum.inr α := by
    rcases x with p | α
    · exact absurd rfl (hx p)
    · exact ⟨α, rfl⟩
  set O := MulAction.orbit Γ (Sum.inr α : Hbar) with hOdef
  have hαO : (Sum.inr α : Hbar) ∈ O := MulAction.mem_orbit_self _
  have hmaps : ∀ T ∈ Γ, ∀ y ∈ O, T • y ∈ O := fun T hT y hy => by
    obtain ⟨γ, rfl⟩ := hy
    exact ⟨⟨T, hT⟩ * γ, mul_smul _ _ _⟩
  have hpos : 0 < O.ncard := (Set.ncard_pos hfin).2 ⟨_, hαO⟩
  rcases (show O.ncard = 1 ∨ O.ncard = 2 by omega) with h1 | h2
  · -- one point: Γ fixes `α`
    obtain ⟨y, hy⟩ := Set.ncard_eq_one.1 h1
    refine Or.inl (k92el_fix_one_cyclic hF (α := α) fun T hT => ?_)
    have hT' := hmaps T hT _ hαO
    rw [hy] at hT' hαO
    rw [Set.mem_singleton_iff.1 hT', Set.mem_singleton_iff.1 hαO]
  · -- two points `α ≠ β`: every element fixes or interchanges them
    obtain ⟨y, z, hyz, hO⟩ := Set.ncard_eq_two.1 h2
    obtain ⟨w, hwO, hwα⟩ : ∃ w ∈ O, w ≠ (Sum.inr α : Hbar) := by
      by_cases hy : y = Sum.inr α
      · exact ⟨z, by rw [hO]; simp, fun h => hyz (hy.trans h.symm)⟩
      · exact ⟨y, by rw [hO]; simp, hy⟩
    obtain ⟨β, hβO, hαβ⟩ : ∃ β : OnePoint ℝ, (Sum.inr β : Hbar) ∈ O ∧ α ≠ β := by
      obtain ⟨γ, rfl⟩ := hwO
      refine ⟨(γ : PSL(2, ℝ)) • α, ⟨γ, rfl⟩, fun h => hwα ?_⟩
      show (Sum.inr ((γ : PSL(2, ℝ)) • α) : Hbar) = Sum.inr α
      rw [← h]
    have hne : (Sum.inr α : Hbar) ≠ Sum.inr β := fun h => hαβ (Sum.inr_injective h)
    have hO2 : O = {Sum.inr α, Sum.inr β} := by
      refine (Set.eq_of_subset_of_ncard_le ?_ ?_ hfin).symm
      · rintro w (rfl | rfl)
        exacts [hαO, hβO]
      · rw [h2, Set.ncard_pair hne]
    refine k92el_fix_two hF hαβ fun T hT => ?_
    have hA := hmaps T hT _ hαO
    have hB := hmaps T hT _ hβO
    rw [hO2] at hA hB
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact absurd (MulAction.injective T (hA.trans hB.symm)) hne
    · exact Or.inl ⟨hA, hB⟩
    · exact Or.inr ⟨hA, hB⟩
    · exact absurd (MulAction.injective T (hA.trans hB.symm)) hne

/-- **Theorem 2.4.4** (§2.4; l. 949). A non-elementary subgroup of PSL(2,ℝ) contains a hyperbolic element. -/
theorem thm2_4_4 {Γ : Subgroup PSL(2, ℝ)} (hΓ : ¬ IsElementary Γ) : ∃ T ∈ Γ, IsHyperbolic T := by
  by_contra hno
  push Not at hno
  apply hΓ
  by_cases hell : ∀ T ∈ Γ, T ≠ 1 → IsElliptic T
  · exact (thm2_4_1 hell).2.2
  push Not at hell
  obtain ⟨f, hfΓ, hf1, hfe⟩ := hell
  -- a parabolic `f ∈ Γ`: every element fixes its fixed point (else some `fⁿ g ∈ Γ` is hyperbolic)
  have hfp : IsParabolic f := by
    rcases k92f_trichotomy hf1 with h | h | h
    · exact absurd h hfe
    · exact h
    · exact absurd h (hno f hfΓ)
  obtain ⟨α, hα⟩ := fixedBy_of_isParabolic hfp
  refine k92el_of_finite_inv (F := {Sum.inr α}) (finite_singleton _) (singleton_nonempty _) fun g hg x hx => ?_
  rw [mem_singleton_iff] at hx ⊢
  rw [hx]
  by_contra hne
  obtain ⟨n, hn⟩ := k92el_hyp_of_par hfp hα hne
  exact hno _ (Γ.mul_mem (Γ.zpow_mem hfΓ n) hg) hn

/-- Auxiliary (§2.4, Exercise 2.13). A non-elementary subgroup contains, for every finite `F ⊆ ℍ̃`, a hyperbolic element
whose fixed points avoid `F`: a conjugate `g h g⁻¹` of a hyperbolic `h ∈ Γ` (Theorem 2.4.4), where `g ∈ Γ` with
`g(Fix h) ∩ F = ∅` exists by B. H. Neumann's lemma (`Subgroup.exists_finiteIndex_of_leftCoset_cover`), the
stabilizers of the fixed points of `h` having infinite index (their orbits are infinite). -/
theorem k92el_hyp_avoiding {Γ : Subgroup PSL(2, ℝ)} (hΓ : ¬ IsElementary Γ) {F : Set Hbar} (hF : F.Finite) :
    ∃ T ∈ Γ, IsHyperbolic T ∧ Disjoint (MulAction.fixedBy Hbar T) F := by
  classical
  obtain ⟨h, hhΓ, hh⟩ := thm2_4_4 hΓ
  obtain ⟨α, β, -, hfix⟩ := fixedBy_of_isHyperbolic hh
  -- the stabilizers in Γ have infinite index (orbits are infinite)
  have hinf : ∀ x : Hbar, ¬ (MulAction.stabilizer Γ x).FiniteIndex := fun x hfi => hΓ
    ⟨x, Set.finite_of_ncard_ne_zero (by rw [← MulAction.index_stabilizer]; exact hfi.index_ne_zero)⟩
  by_contra hno
  push Not at hno
  -- every `γ ∈ Γ` sends `α` or `β` into `F`, so Γ is a finite union of cosets of the two stabilizers
  set a : Bool → Hbar := fun b => if b then Sum.inr α else Sum.inr β with hadef
  set g : Hbar × Bool → Γ := fun i => if hi : ∃ g₀ : Γ, g₀ • a i.2 = i.1 then hi.choose else 1 with hgdef
  open scoped Pointwise in
  have hcovers : ⋃ i ∈ hF.toFinset ×ˢ (Finset.univ : Finset Bool),
      g i • (MulAction.stabilizer Γ (a i.2) : Set Γ) = Set.univ := by
    refine Set.eq_univ_of_forall fun γ => ?_
    have hγh : (γ : PSL(2, ℝ)) * h * (γ : PSL(2, ℝ))⁻¹ ∈ Γ := Γ.mul_mem (Γ.mul_mem γ.2 hhΓ) (Γ.inv_mem γ.2)
    have hyp : IsHyperbolic ((γ : PSL(2, ℝ)) * h * (γ : PSL(2, ℝ))⁻¹) := by
      have := tr_conj (γ : PSL(2, ℝ))⁻¹ h
      rw [inv_inv] at this
      rw [IsHyperbolic, this]
      exact hh
    obtain ⟨y, hy, hyF⟩ := Set.not_disjoint_iff.1 (hno _ hγh hyp)
    rw [k92el_fixedBy_conj, hfix] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    -- `z = a b` for some `b`
    obtain ⟨b, rfl⟩ : ∃ b : Bool, a b = z := by
      rcases hz with rfl | rfl
      · exact ⟨true, rfl⟩
      · exact ⟨false, rfl⟩
    have hex : ∃ g₀ : Γ, g₀ • a b = (γ : PSL(2, ℝ)) • a b := ⟨γ, rfl⟩
    refine Set.mem_biUnion (x := ((γ : PSL(2, ℝ)) • a b, b)) ?_ ?_
    · exact Finset.mem_product.2 ⟨hF.mem_toFinset.2 hyF, Finset.mem_univ _⟩
    · rw [mem_leftCoset_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff, mul_smul]
      have hg : g ((γ : PSL(2, ℝ)) • a b, b) • a b = (γ : PSL(2, ℝ)) • a b := by
        simp only [hgdef, dite_eq_left hex]
        exact hex.choose_spec
      rw [inv_smul_eq_iff, hg]
      rfl
  obtain ⟨k, -, hk⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover hcovers
  exact hinf _ hk

/-- **Unlabelled** (§2.4; l. 959, the content of Exercise 2.13). A non-elementary subgroup contains infinitely many
hyperbolic elements, no two of which have a common fixed point. -/
theorem exists_infinite_hyperbolic {Γ : Subgroup PSL(2, ℝ)} (hΓ : ¬ IsElementary Γ) :
    ∃ s : Set PSL(2, ℝ), s ⊆ Γ ∧ s.Infinite ∧ (∀ T ∈ s, IsHyperbolic T) ∧
      s.Pairwise fun T S => Disjoint (MulAction.fixedBy Hbar T) (MulAction.fixedBy Hbar S) := by
  -- choose hyperbolic elements one by one, each avoiding the fixed points of the earlier ones
  obtain ⟨f, hf, hr⟩ := exists_seq_of_forall_finset_exists (fun T => T ∈ Γ ∧ IsHyperbolic T)
    (fun T S => Disjoint (MulAction.fixedBy Hbar T) (MulAction.fixedBy Hbar S)) fun s hs => by
      have hfin : (⋃ x ∈ s, MulAction.fixedBy Hbar x).Finite :=
        s.finite_toSet.biUnion fun x hx => (k92el_finite_fixedBy (k92f_ne_one_of_hyp (hs x hx).2)).1
      obtain ⟨T, hT, hTh, hdisj⟩ := k92el_hyp_avoiding hΓ hfin
      exact ⟨T, ⟨hT, hTh⟩, fun x hx => (hdisj.mono_right (subset_biUnion_of_mem (u := fun x =>
        MulAction.fixedBy Hbar x) hx)).symm⟩
  have hinj : Function.Injective f := by
    intro m n hmn
    by_contra hne
    have hne' : (MulAction.fixedBy Hbar (f m)).Nonempty := (k92el_finite_fixedBy (k92f_ne_one_of_hyp (hf m).2)).2
    rcases lt_or_gt_of_ne hne with h | h
    · have := hr m n h
      rw [hmn] at this
      exact hne'.ne_empty (disjoint_self.1 (hmn ▸ this))
    · have := hr n m h
      rw [hmn] at this hne'
      exact hne'.ne_empty (disjoint_self.1 this)
  refine ⟨range f, ?_, infinite_range_of_injective hinj, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact (hf n).1
  · rintro _ ⟨n, rfl⟩
    exact (hf n).2
  · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ hmn
    rcases lt_or_gt_of_ne (fun h : m = n => hmn (h ▸ rfl)) with h | h
    · exact hr m n h
    · exact (hr n m h).symm

/-- Auxiliary (§2.4). Continuous even functions of SL(2,ℝ) lifts descend to PSL(2,ℝ): along `Tₙ → T₀`,
`f(out Tₙ) → f(out T₀)`. -/
theorem k92el_tendsto_even {f : SL(2, ℝ) → ℝ} (hf : Continuous f) (hneg : ∀ g, f (-g) = f g)
    {T : ℕ → PSL(2, ℝ)} {T₀ : PSL(2, ℝ)} (hT : Tendsto T atTop (𝓝 T₀)) :
    Tendsto (fun n => f (Quotient.out (T n))) atTop (𝓝 (f (Quotient.out T₀))) := by
  -- `f` is constant on the fibres `{g, −g}`, so it factors through PSL(2,ℝ)
  have hcomp : (fun T : PSL(2, ℝ) => f (Quotient.out T)) ∘ (QuotientGroup.mk : SL(2, ℝ) → PSL(2, ℝ)) = f :=
    funext fun g => by
      rcases k92_out_mk g with h | h
      · simp only [Function.comp_apply, h]
      · simp only [Function.comp_apply, h, hneg]
  have hF : Continuous fun T : PSL(2, ℝ) => f (Quotient.out T) := by
    rw [(QuotientGroup.isQuotientMap_mk (Subgroup.center SL(2, ℝ))).continuous_iff, hcomp]
    exact hf
  exact (hF.tendsto T₀).comp hT

/-- Helper (§2.4, proof of Theorem 2.4.5). For `D = diag(l, l⁻¹)` and any `s`: `tr(D s D⁻¹ s⁻¹) = 2 − bc (l − l⁻¹)²`,
and the off-diagonal entries of `D s D⁻¹ s⁻¹` multiply to `−(1 + bc) bc (l − l⁻¹)²` (`bc = s₀₁ s₁₀`). -/
theorem k92el_comm_diag (D s : SL(2, ℝ)) {l : ℝ} (hl : l ≠ 0)
    (hD : (D : Matrix (Fin 2) (Fin 2) ℝ) = !![l, 0; 0, l⁻¹]) :
    Matrix.trace ((D * s * D⁻¹ * s⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = 2 - s 0 1 * s 1 0 * (l - l⁻¹) ^ 2 ∧
      (D * s * D⁻¹ * s⁻¹ : SL(2, ℝ)) 0 1 * (D * s * D⁻¹ * s⁻¹ : SL(2, ℝ)) 1 0 =
        -((1 + s 0 1 * s 1 0) * (s 0 1 * s 1 0) * (l - l⁻¹) ^ 2) := by
  have hs := s.2
  rw [Matrix.det_fin_two] at hs
  have hm : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
  set m := l⁻¹
  have hD00 : D 0 0 = l := by rw [hD]; rfl
  have hD01 : D 0 1 = 0 := by rw [hD]; rfl
  have hD10 : D 1 0 = 0 := by rw [hD]; rfl
  have hD11 : D 1 1 = m := by rw [hD]; rfl
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, hD00, hD01, hD10, hD11]
  constructor
  · linear_combination (2 * s 0 0 * s 1 1 - 2 * s 0 1 * s 1 0) * hm + 2 * hs
  · linear_combination (-(s 0 1 * s 1 0) * (l - m) ^ 2 * (s 0 0 * s 1 1)) * hm + (-(s 0 1 * s 1 0) * (l - m) ^ 2) * hs

/-- Auxiliary (§2.4, proof of Theorem 2.4.5). In a subgroup without elliptic elements, a sequence `gₙ → Id` eventually
shares a fixed point with any given hyperbolic `h`: after diagonalizing `h`, `bₙcₙ ≤ 0` from `tr[h, gₙ] ≥ 2` and
`bₙcₙ ≥ 0` from `tr[h, [h, gₙ]] ≥ 2`, so `bₙcₙ = 0`. -/
theorem k92el_eventually_common_fix {Γ : Subgroup PSL(2, ℝ)} (hΓ : ∀ T ∈ Γ, ¬ IsElliptic T) {h : PSL(2, ℝ)}
    (hh : h ∈ Γ) (hyp : IsHyperbolic h) {g : ℕ → PSL(2, ℝ)} (hg : ∀ n, g n ∈ Γ)
    (hlim : Tendsto g atTop (𝓝 1)) : ∀ᶠ n in atTop, ∃ x ∈ MulAction.fixedBy Hbar h, g n • x = x := by
  -- diagonalize `h`: `P t P⁻¹ = diag(l, l⁻¹)`
  obtain ⟨ht, hTr⟩ := k92n_Tr_out h
  set t := Quotient.out h
  have hhyp' : (t : Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic := by
    have h2 : 2 < |t 0 0 + t 1 1| := hTr ▸ hyp
    show 0 < (t : Matrix (Fin 2) (Fin 2) ℝ).discr
    rw [k92n_discr]
    nlinarith [abs_nonneg (t 0 0 + t 1 1), sq_abs (t 0 0 + t 1 1)]
  obtain ⟨l, hl1, hlm1, P, hP⟩ := (hyperbolic_conj_diag t).1 hhyp'
  set D : SL(2, ℝ) := P * t * P⁻¹ with hDdef
  have hl0 : l ≠ 0 := by
    rintro rfl
    have := D.2
    rw [hP] at this
    simp [Matrix.det_fin_two_of] at this
  set C : PSL(2, ℝ) := (P : PSL(2, ℝ))
  have hDh : (D : PSL(2, ℝ)) = C * h * C⁻¹ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ht]
  set κ := (l - l⁻¹) ^ 2 with hκdef
  have hκ : 0 < κ := by
    have : l - l⁻¹ ≠ 0 := by
      intro h0
      have hll : l * l = 1 := by
        have := mul_inv_cancel₀ hl0
        rw [sub_eq_zero] at h0
        rw [← h0] at this
        exact this
      rcases mul_self_eq_one_iff.1 hll with h1 | h1
      · exact hl1 h1
      · exact hlm1 h1
    positivity
  -- the conjugated sequence `C gₙ C⁻¹ → 1` and its lifts `sₙ`
  have hg'lim : Tendsto (fun n => C * g n * C⁻¹) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := C)).mul hlim |>.mul (tendsto_const_nhds (x := C⁻¹))
    rwa [mul_one, mul_inv_cancel] at this
  set s : ℕ → SL(2, ℝ) := fun n => Quotient.out (C * g n * C⁻¹)
  have hs : ∀ n, (s n : PSL(2, ℝ)) = C * g n * C⁻¹ := fun n => QuotientGroup.out_eq' _
  -- `bₙcₙ → 0`
  have hbc : Tendsto (fun n => s n 0 1 * s n 1 0) atTop (𝓝 0) := by
    have hcont : Continuous fun x : SL(2, ℝ) => x 0 1 * x 1 0 := by fun_prop
    have := k92el_tendsto_even hcont (fun x => by simp [Matrix.SpecialLinearGroup.coe_neg]) hg'lim
    have h1 : (Quotient.out (1 : PSL(2, ℝ))) 0 1 * (Quotient.out (1 : PSL(2, ℝ))) 1 0 = 0 := by
      rcases k92_out_mk 1 with h | h
      · rw [QuotientGroup.mk_one] at h
        rw [h]; simp
      · rw [QuotientGroup.mk_one] at h
        rw [h]; simp [Matrix.SpecialLinearGroup.coe_neg]
    rwa [h1] at this
  -- eventually `2 − bₙcₙ κ > 0`, `1 + bₙcₙ > 0` and `2 + (1 + bₙcₙ) bₙcₙ κ² > 0`
  have hev1 : ∀ᶠ n in atTop, 0 < 2 - s n 0 1 * s n 1 0 * κ := by
    have : Tendsto (fun n => 2 - s n 0 1 * s n 1 0 * κ) atTop (𝓝 (2 - 0 * κ)) :=
      tendsto_const_nhds.sub (hbc.mul_const κ)
    rw [zero_mul, sub_zero] at this
    exact this.eventually (lt_mem_nhds two_pos)
  have hev2 : ∀ᶠ n in atTop, 0 < 1 + s n 0 1 * s n 1 0 := by
    have : Tendsto (fun n => 1 + s n 0 1 * s n 1 0) atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add hbc
    rw [add_zero] at this
    exact this.eventually (lt_mem_nhds one_pos)
  have hev3 : ∀ᶠ n in atTop, 0 < 2 + (1 + s n 0 1 * s n 1 0) * (s n 0 1 * s n 1 0) * κ ^ 2 := by
    have : Tendsto (fun n => 2 + (1 + s n 0 1 * s n 1 0) * (s n 0 1 * s n 1 0) * κ ^ 2) atTop
        (𝓝 (2 + (1 + 0) * 0 * κ ^ 2)) :=
      tendsto_const_nhds.add (((tendsto_const_nhds.add hbc).mul hbc).mul_const _)
    rw [mul_zero, zero_mul, add_zero] at this
    exact this.eventually (lt_mem_nhds two_pos)
  filter_upwards [hev1, hev2, hev3] with n h1 h2 h3
  -- the commutator `k = h gₙ h⁻¹ gₙ⁻¹ ∈ Γ` is conjugate to the class of `D sₙ D⁻¹ sₙ⁻¹`
  have hk : h * g n * h⁻¹ * (g n)⁻¹ ∈ Γ :=
    Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hh (hg n)) (Γ.inv_mem hh)) (Γ.inv_mem (hg n))
  have ek : h * g n * h⁻¹ * (g n)⁻¹ = C⁻¹ * ((D * s n * D⁻¹ * (s n)⁻¹ : SL(2, ℝ)) : PSL(2, ℝ)) * C := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hDh, hs]
    group
  obtain ⟨tr1, prod1⟩ := k92el_comm_diag D (s n) hl0 hP
  -- no elliptic elements: `|tr k| ≥ 2`, so `bₙcₙ ≤ 0`
  have hbc_le : s n 0 1 * s n 1 0 ≤ 0 := by
    have hT := not_lt.1 (hΓ _ hk)
    rw [ek, tr_conj, k92_Tr_mk, tr1, abs_of_pos h1] at hT
    exact nonpos_of_mul_nonpos_left (by linarith) hκ
  -- the second commutator `h k h⁻¹ k⁻¹ ∈ Γ`: `bₙcₙ ≥ 0`
  set s' : SL(2, ℝ) := D * s n * D⁻¹ * (s n)⁻¹ with hs'def
  have hm : h * (h * g n * h⁻¹ * (g n)⁻¹) * h⁻¹ * (h * g n * h⁻¹ * (g n)⁻¹)⁻¹ ∈ Γ :=
    Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hh hk) (Γ.inv_mem hh)) (Γ.inv_mem hk)
  have em : h * (h * g n * h⁻¹ * (g n)⁻¹) * h⁻¹ * (h * g n * h⁻¹ * (g n)⁻¹)⁻¹ =
      C⁻¹ * ((D * s' * D⁻¹ * s'⁻¹ : SL(2, ℝ)) : PSL(2, ℝ)) * C := by
    rw [ek]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hDh]
    group
  obtain ⟨tr2, -⟩ := k92el_comm_diag D s' hl0 hP
  have hbc_ge : 0 ≤ s n 0 1 * s n 1 0 := by
    have hT := not_lt.1 (hΓ _ hm)
    rw [em, tr_conj, k92_Tr_mk, tr2, prod1] at hT
    have e2 : 2 - -((1 + s n 0 1 * s n 1 0) * (s n 0 1 * s n 1 0) * (l - l⁻¹) ^ 2) * (l - l⁻¹) ^ 2 =
        2 + (1 + s n 0 1 * s n 1 0) * (s n 0 1 * s n 1 0) * κ ^ 2 := by
      rw [hκdef]; ring
    rw [e2, abs_of_pos h3] at hT
    have h4 : 0 ≤ (1 + s n 0 1 * s n 1 0) * (s n 0 1 * s n 1 0) :=
      nonneg_of_mul_nonneg_left (show 0 ≤ (1 + s n 0 1 * s n 1 0) * (s n 0 1 * s n 1 0) * κ ^ 2 by linarith)
        (pow_pos hκ 2)
    exact (mul_nonneg_iff_of_pos_left h2).1 h4
  have hbc0 : s n 0 1 * s n 1 0 = 0 := le_antisymm hbc_le hbc_ge
  -- so `sₙ` fixes `0` or `∞`, which `D` fixes too
  have hD10 : D 1 0 = 0 := by rw [hP]; rfl
  have hD01 : D 0 1 = 0 := by rw [hP]; rfl
  obtain ⟨hDinf, hD0⟩ := (k92f_fix_zero_infty D).2 ⟨hD10, hD01⟩
  obtain ⟨y, hyD, hys⟩ : ∃ y : Hbar, (D : PSL(2, ℝ)) • y = y ∧ (s n : PSL(2, ℝ)) • y = y := by
    rcases mul_eq_zero.1 hbc0 with h01 | h10
    · refine ⟨Sum.inr ((0 : ℝ) : OnePoint ℝ), hD0, ?_⟩
      have hdet := (s n).2
      rw [Matrix.det_fin_two, h01, zero_mul, sub_zero] at hdet
      have h11 : s n 1 1 ≠ 0 := fun h0 => by rw [h0, mul_zero] at hdet; exact zero_ne_one hdet
      rw [Sum.smul_inr, k92n_bdry_smul, OnePoint.smul_some_eq_ite]
      have e1 : ((Matrix.SpecialLinearGroup.mapGL ℝ (s n) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * 0 +
          ((Matrix.SpecialLinearGroup.mapGL ℝ (s n) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ≠ 0 := by
        show s n 1 0 * 0 + s n 1 1 ≠ 0
        rw [mul_zero, zero_add]
        exact h11
      rw [ite_eq_right e1]
      congr 2
      show (s n 0 0 * 0 + s n 0 1) / (s n 1 0 * 0 + s n 1 1) = 0
      rw [h01]
      simp
    · refine ⟨Sum.inr OnePoint.infty, hDinf, ?_⟩
      rw [Sum.smul_inr, k92n_bdry_smul, OnePoint.smul_infty_eq_self_iff.2 h10]
  refine ⟨C⁻¹ • y, ?_, ?_⟩
  · show h • (C⁻¹ • y) = C⁻¹ • y
    have e : h = C⁻¹ * (D : PSL(2, ℝ)) * C := by rw [hDh]; group
    rw [e, mul_smul, mul_smul, smul_inv_smul, hyD]
  · have e : g n = C⁻¹ * (s n : PSL(2, ℝ)) * C := by rw [hs]; group
    rw [e, mul_smul, mul_smul, smul_inv_smul, hys]

/-- **Theorem 2.4.5** (§2.4; l. 961). A subgroup of PSL(2,ℝ) without elliptic elements is elementary or discrete. -/
theorem thm2_4_5 {Γ : Subgroup PSL(2, ℝ)} (hΓ : ∀ T ∈ Γ, ¬ IsElliptic T) : IsElementary Γ ∨ IsFuchsian Γ := by
  by_cases hE : IsElementary Γ
  · exact Or.inl hE
  right
  -- three hyperbolic elements of Γ with pairwise disjoint fixed-point sets (Exercise 2.13)
  obtain ⟨s, hsΓ, hsinf, hshyp, hsdisj⟩ := exists_infinite_hyperbolic hE
  obtain ⟨h₁, h₁s⟩ := hsinf.nonempty
  obtain ⟨h₂, h₂s, h₂ne⟩ := (hsinf.sdiff (finite_singleton h₁)).nonempty
  obtain ⟨h₃, h₃s, h₃ne⟩ := (hsinf.sdiff (toFinite {h₁, h₂})).nonempty
  have h21 : h₂ ≠ h₁ := h₂ne
  have h31 : h₃ ≠ h₁ := fun h => h₃ne (Or.inl h)
  have h32 : h₃ ≠ h₂ := fun h => h₃ne (Or.inr h)
  rw [IsFuchsian, discreteTopology_iff_tendsto_one]
  intro g hg hlim
  filter_upwards [k92el_eventually_common_fix hΓ (hsΓ h₁s) (hshyp h₁ h₁s) hg hlim,
    k92el_eventually_common_fix hΓ (hsΓ h₂s) (hshyp h₂ h₂s) hg hlim,
    k92el_eventually_common_fix hΓ (hsΓ h₃s) (hshyp h₃ h₃s) hg hlim] with n e₁ e₂ e₃
  obtain ⟨x₁, hx₁, f₁⟩ := e₁
  obtain ⟨x₂, hx₂, f₂⟩ := e₂
  obtain ⟨x₃, hx₃, f₃⟩ := e₃
  -- the three common fixed points are distinct, so `gₙ = Id`
  have d12 : x₁ ≠ x₂ := fun h => (hsdisj h₂s h₁s h21).ne_of_mem hx₂ (h ▸ hx₁) rfl
  have d13 : x₁ ≠ x₃ := fun h => (hsdisj h₃s h₁s h31).ne_of_mem hx₃ (h ▸ hx₁) rfl
  have d23 : x₂ ≠ x₃ := fun h => (hsdisj h₃s h₂s h32).ne_of_mem hx₃ (h ▸ hx₂) rfl
  exact k92el_eq_one_of_three d12 d13 d23 f₁ f₂ f₃

/-- Auxiliary (§2.4, Lemma 2.4.7 for any sequence satisfying (2.5.3)). If `T ≠ Id`, `σ 0 = S`,
`σ (r + 1) = σ r · T · (σ r)⁻¹` and `σ n = T` for some `n`, then `⟨T, S⟩` is elementary. This restates the first half of
`lemma2_4_7`, which (with `conjSeq`) sits below Theorem 2.4.6 in this file, by the same proof. -/
theorem k92el_seq_elem {T S : PSL(2, ℝ)} (hT : T ≠ 1) {σ : ℕ → PSL(2, ℝ)} (h0 : σ 0 = S)
    (hs : ∀ r, σ (r + 1) = σ r * T * (σ r)⁻¹) (h : ∃ n, σ n = T) : IsElementary (Subgroup.closure {T, S}) := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨hFfin, hFne⟩ := k92el_finite_fixedBy hT
  set F := MulAction.fixedBy Hbar T with hFdef
  -- `σ (r + 1) = σ r T (σ r)⁻¹`, so `Fix(σ (r + 1)) = σ r F`
  have hfixr : ∀ r, MulAction.fixedBy Hbar (σ (r + 1)) = (σ r • ·) '' F := fun r => by
    rw [hs r]
    exact k92el_fixedBy_conj _ _
  -- downward induction: `σ r F = F` for all `r ≤ n`
  have hstep : ∀ r, (σ (r + 1) • ·) '' F = F → (σ r • ·) '' F = F := fun r hr => by
    have hpres : ∀ x ∈ F, (σ r * T * (σ r)⁻¹) • x ∈ F := fun x hx => by
      rw [← hs r, ← hr]
      exact ⟨x, hx, rfl⟩
    have hsub : F ⊆ (σ r • ·) '' F := by
      rw [← hfixr r, hs r]
      exact k92el_conj_fix_of_preserve hT hpres
    refine (Set.eq_of_subset_of_ncard_le hsub ?_ (hFfin.image _)).symm
    rw [Set.ncard_image_of_injective _ (MulAction.injective _)]
  have hall : ∀ k, k ≤ n → (σ (n - k) • ·) '' F = F := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.sub_zero, hn]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        show T • y ∈ F
        rw [show T • y = y from hy]
        exact hy
      · intro hx
        exact ⟨x, hx, hx⟩
    | succ k ih =>
      intro hk
      have := ih (Nat.le_of_succ_le hk)
      rw [show n - k = n - (k + 1) + 1 by omega] at this
      exact hstep _ this
  have hS : (S • ·) '' F = F := by
    have := hall n le_rfl
    rwa [Nat.sub_self, h0] at this
  -- ⟨T, S⟩ preserves the finite set `F`
  have hTF : ∀ x ∈ F, T • x ∈ F := fun x hx => by
    rw [show T • x = x from hx]
    exact hx
  refine k92el_closure_of_finite_inv hFfin hFne hTF fun x hx => ?_
  rw [← hS]
  exact ⟨x, hx, rfl⟩

/-- Auxiliary (§2.4). `⟨Id, S⟩` is elementary: it preserves the fixed-point set of `S` (any point if `S = Id`). -/
theorem k92el_elem_one (S : PSL(2, ℝ)) : IsElementary (Subgroup.closure {(1 : PSL(2, ℝ)), S}) := by
  by_cases hS : S = 1
  · subst hS
    refine k92el_closure_of_finite_inv (F := {Sum.inl UpperHalfPlane.I}) (Set.finite_singleton _)
      (Set.singleton_nonempty _) (fun x hx => ?_) (fun x hx => ?_)
    · rwa [one_smul]
    · rwa [one_smul]
  · obtain ⟨hfin, hne⟩ := k92el_finite_fixedBy hS
    refine k92el_closure_of_finite_inv hfin hne (fun x hx => ?_) (fun x hx => ?_)
    · rwa [one_smul]
    · rw [show S • x = x from hx]
      exact hx

/-- Auxiliary (§2.4, proof of Theorem 2.4.6, Cases 2 and 3: the estimate). Complex sequences `a, b, c, d` with
`a d − b c = 1`, following the entries of `Mₙ₊₁ = Mₙ diag(u, u⁻¹) Mₙ⁻¹`, with
`μ = |u − u⁻¹|² (1 + |b₀c₀|) < 1`: then `|bₙcₙ| ≤ μⁿ|b₀c₀|`, so `aₙ → u`, `dₙ → u⁻¹`, and the ratios of `bₙu⁻ⁿ`
and of `cₙuⁿ` tend to `|u − u⁻¹| < 1`, so `bₙu⁻ⁿ → 0` and `cₙuⁿ → 0`. -/
theorem k92el_jorg_core {u : ℂ} (hu : u ≠ 0) {a b c d : ℕ → ℂ} (hdet : ∀ n, a n * d n - b n * c n = 1)
    (ha : ∀ n, a (n + 1) = a n * d n * u - b n * c n * u⁻¹) (hb : ∀ n, b (n + 1) = a n * b n * (u⁻¹ - u))
    (hc : ∀ n, c (n + 1) = c n * d n * (u - u⁻¹)) (hd : ∀ n, d (n + 1) = a n * d n * u⁻¹ - b n * c n * u)
    (hμ : ‖u - u⁻¹‖ ^ 2 * (1 + ‖b 0 * c 0‖) < 1) :
    Tendsto a atTop (𝓝 u) ∧ Tendsto d atTop (𝓝 u⁻¹) ∧ Tendsto (fun n => b n * u⁻¹ ^ n) atTop (𝓝 0) ∧
      Tendsto (fun n => c n * u ^ n) atTop (𝓝 0) := by
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ, μ = ‖u - u⁻¹‖ ^ 2 * (1 + ‖b 0 * c 0‖) := ⟨_, rfl⟩
  rw [← hμdef] at hμ
  have hκ0 : 0 ≤ ‖u - u⁻¹‖ ^ 2 := by positivity
  have hμ0 : 0 ≤ μ := by rw [hμdef]; positivity
  have hκμ : ‖u - u⁻¹‖ ^ 2 ≤ μ := by
    rw [hμdef]
    exact le_mul_of_one_le_right hκ0 (by linarith [norm_nonneg (b 0 * c 0)])
  -- `bₙ₊₁cₙ₊₁ = −(1 + bₙcₙ) bₙcₙ (u − u⁻¹)²`
  have hp : ∀ n, b (n + 1) * c (n + 1) = -((1 + b n * c n) * (b n * c n) * (u - u⁻¹) ^ 2) := fun n => by
    rw [hb, hc]
    linear_combination (-(b n * c n) * (u - u⁻¹) ^ 2) * hdet n
  -- `|bₙcₙ| ≤ μⁿ |b₀c₀|`
  have hbound : ∀ n, ‖b n * c n‖ ≤ μ ^ n * ‖b 0 * c 0‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hle : ‖b n * c n‖ ≤ ‖b 0 * c 0‖ :=
        ih.trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hμ0 hμ.le))
      rw [hp, norm_neg, norm_mul, norm_mul, norm_pow]
      calc ‖1 + b n * c n‖ * ‖b n * c n‖ * ‖u - u⁻¹‖ ^ 2
          ≤ (1 + ‖b 0 * c 0‖) * ‖b n * c n‖ * ‖u - u⁻¹‖ ^ 2 := by
            gcongr
            calc ‖1 + b n * c n‖ ≤ ‖(1 : ℂ)‖ + ‖b n * c n‖ := norm_add_le _ _
              _ ≤ 1 + ‖b 0 * c 0‖ := by rw [norm_one]; linarith
        _ = μ * ‖b n * c n‖ := by rw [hμdef]; ring
        _ ≤ μ * (μ ^ n * ‖b 0 * c 0‖) := by gcongr
        _ = μ ^ (n + 1) * ‖b 0 * c 0‖ := by ring
  have hpc : Tendsto (fun n => b n * c n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) hbound ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hμ0 hμ).mul_const ‖b 0 * c 0‖
  -- `aₙ₊₁ = (1 + bₙcₙ) u − bₙcₙ u⁻¹ → u` and `dₙ₊₁ = (1 + bₙcₙ) u⁻¹ − bₙcₙ u → u⁻¹`
  have ha' : Tendsto a atTop (𝓝 u) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    have e : ∀ n, (1 + b n * c n) * u - b n * c n * u⁻¹ = a (n + 1) := fun n => by
      rw [ha]
      linear_combination -u * hdet n
    have := ((tendsto_const_nhds (x := (1 : ℂ))).add hpc).mul (tendsto_const_nhds (x := u)) |>.sub
      (hpc.mul (tendsto_const_nhds (x := u⁻¹)))
    rw [add_zero, one_mul, zero_mul, sub_zero] at this
    exact this.congr e
  have hd' : Tendsto d atTop (𝓝 u⁻¹) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    have e : ∀ n, (1 + b n * c n) * u⁻¹ - b n * c n * u = d (n + 1) := fun n => by
      rw [hd]
      linear_combination -u⁻¹ * hdet n
    have := ((tendsto_const_nhds (x := (1 : ℂ))).add hpc).mul (tendsto_const_nhds (x := u⁻¹)) |>.sub
      (hpc.mul (tendsto_const_nhds (x := u)))
    rw [add_zero, one_mul, zero_mul, sub_zero] at this
    exact this.congr e
  -- `|u − u⁻¹| < ρ < 1`; the ratios of `bₙu⁻ⁿ` and `cₙuⁿ` tend to `|u − u⁻¹|`
  have hρ : ‖u - u⁻¹‖ < 1 := by
    have h1 : ‖u - u⁻¹‖ ^ 2 < 1 := hκμ.trans_lt hμ
    nlinarith [norm_nonneg (u - u⁻¹)]
  obtain ⟨ρ, hρ1, hρ'⟩ : ∃ ρ : ℝ, ρ < 1 ∧ ‖u - u⁻¹‖ < ρ := ⟨(1 + ‖u - u⁻¹‖) / 2, by linarith, by linarith⟩
  refine ⟨ha', hd', ?_, ?_⟩
  · refine (summable_of_ratio_norm_eventually_le hρ1 ?_).tendsto_atTop_zero
    have hf : Tendsto (fun n => ‖a n * u⁻¹ * (u⁻¹ - u)‖) atTop (𝓝 ‖u - u⁻¹‖) := by
      have := ((ha'.mul_const u⁻¹).mul_const (u⁻¹ - u)).norm
      rwa [mul_inv_cancel₀ hu, one_mul, norm_sub_rev] at this
    filter_upwards [hf.eventually (eventually_le_nhds hρ')] with n hn
    show ‖b (n + 1) * u⁻¹ ^ (n + 1)‖ ≤ ρ * ‖b n * u⁻¹ ^ n‖
    have e : b (n + 1) * u⁻¹ ^ (n + 1) = (a n * u⁻¹ * (u⁻¹ - u)) * (b n * u⁻¹ ^ n) := by
      rw [hb, pow_succ]
      ring
    rw [e, norm_mul]
    exact mul_le_mul_of_nonneg_right hn (norm_nonneg _)
  · refine (summable_of_ratio_norm_eventually_le hρ1 ?_).tendsto_atTop_zero
    have hf : Tendsto (fun n => ‖d n * u * (u - u⁻¹)‖) atTop (𝓝 ‖u - u⁻¹‖) := by
      have := ((hd'.mul_const u).mul_const (u - u⁻¹)).norm
      rwa [inv_mul_cancel₀ hu, one_mul] at this
    filter_upwards [hf.eventually (eventually_le_nhds hρ')] with n hn
    show ‖c (n + 1) * u ^ (n + 1)‖ ≤ ρ * ‖c n * u ^ n‖
    have e : c (n + 1) * u ^ (n + 1) = (d n * u * (u - u⁻¹)) * (c n * u ^ n) := by
      rw [hc, pow_succ]
      ring
    rw [e, norm_mul]
    exact mul_le_mul_of_nonneg_right hn (norm_nonneg _)

/-- Auxiliary (§2.4, proof of Theorem 2.4.6, Cases 2 and 3). An element of SL(2,ℝ) with `tr² ≠ 4` is diagonalizable
over `ℂ`: `Q g Q⁻¹ = diag(u, u⁻¹)` with `u + u⁻¹ = tr g` (its eigenvalues are distinct; the columns of `Q⁻¹` are
eigenvectors). -/
theorem k92el_cdiag (g : SL(2, ℝ)) (hg : (g 0 0 + g 1 1) ^ 2 ≠ 4) :
    ∃ u : ℂ, u ≠ 0 ∧ u + u⁻¹ = ((g 0 0 + g 1 1 : ℝ) : ℂ) ∧ ∃ Q Q' : Matrix (Fin 2) (Fin 2) ℂ, Q' * Q = 1 ∧
      Q * (g : Matrix (Fin 2) (Fin 2) ℝ).map Complex.ofReal * Q' = !![u, 0; 0, u⁻¹] := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2
    rwa [Matrix.det_fin_two] at this
  have hdetC : (g 0 0 : ℂ) * g 1 1 - g 0 1 * g 1 0 = 1 := by exact_mod_cast hdet
  -- it suffices to find eigenvalues `u v` and an eigenvector matrix `Q'` with an inverse up to the scalar `c`
  suffices key : ∃ u v c : ℂ, c ≠ 0 ∧ u * v = 1 ∧ u + v = ((g 0 0 + g 1 1 : ℝ) : ℂ) ∧
      ∃ Q' N : Matrix (Fin 2) (Fin 2) ℂ, Q' * N = c • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
        (g : Matrix (Fin 2) (Fin 2) ℝ).map Complex.ofReal * Q' = Q' * !![u, 0; 0, v] by
    obtain ⟨u, v, c, hc, huv, hsum, Q', N, hQN, heig⟩ := key
    have hv : v = u⁻¹ := eq_inv_of_mul_eq_one_right huv
    have hu : u ≠ 0 := left_ne_zero_of_mul_eq_one huv
    have hQ'Q : Q' * (c⁻¹ • N) = 1 := by
      rw [Matrix.mul_smul, hQN, smul_smul, inv_mul_cancel₀ hc, one_smul]
    refine ⟨u, hu, hv ▸ hsum, c⁻¹ • N, Q', hQ'Q, ?_⟩
    rw [Matrix.mul_assoc, heig, ← Matrix.mul_assoc, mul_eq_one_comm.1 hQ'Q, Matrix.one_mul, hv]
  by_cases hr : g 1 0 = 0
  · -- upper triangular: eigenvalues `g₀₀ ≠ g₁₁`, eigenvectors `(1, 0)` and `(g₀₁, g₁₁ − g₀₀)`
    have hps : g 1 1 - g 0 0 ≠ 0 := by
      intro e
      apply hg
      have h1 : g 1 1 = g 0 0 := by linarith
      rw [hr, mul_zero, sub_zero] at hdet
      rw [h1] at hdet ⊢
      nlinarith [hdet]
    have hrC : (g 1 0 : ℂ) = 0 := by exact_mod_cast hr
    refine ⟨g 0 0, g 1 1, g 1 1 - g 0 0, by exact_mod_cast hps, ?_, by push_cast; ring,
      !![1, (g 0 1 : ℂ); 0, (g 1 1 : ℂ) - g 0 0], !![(g 1 1 : ℂ) - g 0 0, -(g 0 1 : ℂ); 0, 1], ?_, ?_⟩
    · rw [hrC, mul_zero, sub_zero] at hdetC
      exact hdetC
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hrC] <;> ring
  · -- `g₁₀ ≠ 0`: eigenvalues `(t ± w)/2` with `w² = t² − 4 ≠ 0`, eigenvectors `(λ − g₁₁, g₁₀)`
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_eq_mul_self (((g 0 0 + g 1 1 : ℝ) : ℂ) ^ 2 - 4)
    have hw0 : w ≠ 0 := by
      rintro rfl
      apply hg
      have : (((g 0 0 + g 1 1) ^ 2 : ℝ) : ℂ) = ((4 : ℝ) : ℂ) := by
        have hw' := hw
        push_cast at hw' ⊢
        linear_combination hw'
      exact_mod_cast this
    have hrC : (g 1 0 : ℂ) ≠ 0 := by exact_mod_cast hr
    set t : ℂ := ((g 0 0 + g 1 1 : ℝ) : ℂ) with htdef
    have ht : t = (g 0 0 : ℂ) + g 1 1 := by rw [htdef]; push_cast; ring
    have hqu : ((t + w) / 2) ^ 2 - t * ((t + w) / 2) + 1 = 0 := by linear_combination (-1 / 4 : ℂ) * hw
    have hqv : ((t - w) / 2) ^ 2 - t * ((t - w) / 2) + 1 = 0 := by linear_combination (-1 / 4 : ℂ) * hw
    refine ⟨(t + w) / 2, (t - w) / 2, (g 1 0 : ℂ) * w, mul_ne_zero hrC hw0,
      by linear_combination (1 / 4 : ℂ) * hw, by ring,
      !![(t + w) / 2 - g 1 1, (t - w) / 2 - g 1 1; (g 1 0 : ℂ), (g 1 0 : ℂ)],
      !![(g 1 0 : ℂ), -((t - w) / 2 - g 1 1); -(g 1 0 : ℂ), (t + w) / 2 - g 1 1], ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination -hqu - hdetC - ((t + w) / 2) * ht
      · linear_combination -hqv - hdetC - ((t - w) / 2) * ht
      · ring
      · ring

/-- Helper. The sequence (2.5.3) stays in `⟨T, S⟩`. -/
theorem k92el_seq_mem {T S : PSL(2, ℝ)} {σ : ℕ → PSL(2, ℝ)} (h0 : σ 0 = S)
    (hs : ∀ r, σ (r + 1) = σ r * T * (σ r)⁻¹) (n : ℕ) : σ n ∈ Subgroup.closure {T, S} := by
  have hT : T ∈ Subgroup.closure {T, S} := Subgroup.subset_closure (Set.mem_insert _ _)
  induction n with
  | zero =>
    rw [h0]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  | succ n ih =>
    rw [hs]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ih hT) (Subgroup.inv_mem _ ih)

/-- Auxiliary (§2.4, proof of Theorem 2.4.6, Case 1: `T` parabolic). If `T` is parabolic, `⟨T, S⟩` discrete and the
Jørgensen quantity `< 1`, the sequence (2.5.3) reaches `T`. Normalize `T = ±[[1, β], [0, 1]]`: the quantity is `β²c²`
(`c = S₁₀`), `βcₙ₊₁ = −(βcₙ)²` tends to `0`, so `Sₙ₊₁ = [[1 − βaₙcₙ, βaₙ²], [−βcₙ², 1 + βaₙcₙ]] → T`, and
discreteness gives `Sₙ = T` (`k92el_eventually_eq`). -/
theorem k92el_jorg_par (T S : SL(2, ℝ)) (hT : IsParabolic (T : PSL(2, ℝ)))
    (hd : IsFuchsian (Subgroup.closure {(T : PSL(2, ℝ)), (S : PSL(2, ℝ))}))
    (hμ : |trSq (T : PSL(2, ℝ)) - 4| +
      |Matrix.trace ((T * S * T⁻¹ * S⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) - 2| < 1)
    {σ : ℕ → PSL(2, ℝ)} (h0 : σ 0 = S) (hs : ∀ r, σ (r + 1) = σ r * T * (σ r)⁻¹) : ∃ n, σ n = T := by
  -- conjugate the fixed point `α` of `T` to `∞`: `P T P⁻¹ = ±u`, `u = [[1, β], [0, 1]]`
  obtain ⟨α, hα⟩ := fixedBy_of_isParabolic hT
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
  have hCα : (P : PSL(2, ℝ)) • α = OnePoint.infty := by rw [k92n_bdry_smul, hP]
  obtain ⟨d, hdd⟩ := QuotientGroup.mk_surjective ((P : PSL(2, ℝ)) * (T : PSL(2, ℝ)) * (P : PSL(2, ℝ))⁻¹)
  have hfixd : MulAction.fixedBy Hbar (d : PSL(2, ℝ)) = {Sum.inr OnePoint.infty} := by
    rw [hdd, k92f_fix_conj_single _ hα, hCα]
  obtain ⟨hd10, hd0011⟩ := k92f_fix_infty_only d hfixd
  have hdet : d 0 0 * d 1 1 = 1 := by
    have := d.2
    rw [Matrix.det_fin_two, hd10] at this
    linarith
  obtain ⟨u, hu, hu00, hu10, hu11⟩ : ∃ u : SL(2, ℝ),
      (u : PSL(2, ℝ)) = (P : PSL(2, ℝ)) * (T : PSL(2, ℝ)) * (P : PSL(2, ℝ))⁻¹ ∧ u 0 0 = 1 ∧ u 1 0 = 0 ∧ u 1 1 = 1 := by
    have hsq : d 1 1 * d 1 1 = 1 := by
      rw [hd0011] at hdet
      exact hdet
    rcases mul_self_eq_one_iff.1 hsq with h1 | h1
    · exact ⟨d, hdd, by rw [hd0011, h1], hd10, h1⟩
    · refine ⟨-d, by rw [k92el_mk_neg, hdd], ?_, ?_, ?_⟩
      · show -(d 0 0) = 1
        rw [hd0011, h1]; norm_num
      · show -(d 1 0) = 0
        rw [hd10, neg_zero]
      · show -(d 1 1) = 1
        rw [h1]; norm_num
  have hb : u 0 1 ≠ 0 := by
    intro hb0
    apply hT.2
    have hu1 : u = 1 := by
      ext i j
      fin_cases i <;> fin_cases j
      · exact hu00
      · exact hb0
      · exact hu10
      · exact hu11
    have : (P : PSL(2, ℝ)) * (T : PSL(2, ℝ)) * (P : PSL(2, ℝ))⁻¹ = 1 := by rw [← hu, hu1]; rfl
    calc (T : PSL(2, ℝ)) = (P : PSL(2, ℝ))⁻¹ * ((P : PSL(2, ℝ)) * (T : PSL(2, ℝ)) * (P : PSL(2, ℝ))⁻¹) * P := by group
      _ = 1 := by rw [this]; group
  have hpm : P * T * P⁻¹ = u ∨ P * T * P⁻¹ = -u := by
    have e : ((P * T * P⁻¹ : SL(2, ℝ)) : PSL(2, ℝ)) = (u : PSL(2, ℝ)) := by
      rw [hu, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h1 := k92_out_mk (P * T * P⁻¹)
    have h2 := k92_out_mk u
    rw [e] at h1
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact Or.inl (h1.symm.trans h2)
    · exact Or.inr (h1.symm.trans h2)
    · exact Or.inr (by rw [← h2, h1, neg_neg])
    · exact Or.inl (neg_inj.1 (h1.symm.trans h2))
  -- the quantity is `β² c²`, `c = (P S P⁻¹)₁₀`
  have hconj' : ∀ X : SL(2, ℝ), P * T * P⁻¹ * X * (P * T * P⁻¹)⁻¹ = u * X * u⁻¹ := fun X => by
    rcases hpm with e | e
    · rw [e]
    · rw [e, inv_neg, neg_mul, neg_mul_neg]
  have hcomm : ∀ X : SL(2, ℝ), Matrix.trace ((u * X * u⁻¹ * X⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      2 + u 0 1 ^ 2 * X 1 0 ^ 2 := fun X => by
    have hX := X.2
    rw [Matrix.det_fin_two] at hX
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, hu00, hu10, hu11]
    linear_combination 2 * hX
  have htr : Matrix.trace ((T * S * T⁻¹ * S⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      2 + u 0 1 ^ 2 * (P * S * P⁻¹) 1 0 ^ 2 := by
    rw [← k92_trace_conj P, show P * (T * S * T⁻¹ * S⁻¹) * P⁻¹ =
      P * T * P⁻¹ * (P * S * P⁻¹) * (P * T * P⁻¹)⁻¹ * (P * S * P⁻¹)⁻¹ by group, hconj', hcomm]
  have hβc : |u 0 1 * (P * S * P⁻¹) 1 0| < 1 := by
    have h1 : trSq (T : PSL(2, ℝ)) = 4 := by rw [trSq, hT.1]; norm_num
    rw [h1, sub_self, abs_zero, zero_add, htr, add_sub_cancel_left, ← mul_pow] at hμ
    exact (sq_lt_one_iff_abs_lt_one _).1 ((le_abs_self _).trans_lt hμ)
  -- lifts `mₙ = P Sₙ P⁻¹` of the sequence (2.5.3), with `mₙ₊₁ = mₙ u mₙ⁻¹`
  obtain ⟨m, hm0, hms⟩ : ∃ m : ℕ → SL(2, ℝ), m 0 = P * S * P⁻¹ ∧ ∀ r, m (r + 1) = m r * u * (m r)⁻¹ :=
    ⟨fun n => Nat.rec (motive := fun _ => SL(2, ℝ)) (P * S * P⁻¹) (fun _ X => X * u * X⁻¹) n, rfl, fun _ => rfl⟩
  have hmσ : ∀ n, (P : PSL(2, ℝ))⁻¹ * (m n : PSL(2, ℝ)) * P = σ n := by
    intro n
    induction n with
    | zero =>
      rw [hm0, h0, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      group
    | succ n ih =>
      rw [hms, hs, ← ih, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hu]
      group
  have hstep : ∀ X : SL(2, ℝ), (X * u * X⁻¹) 0 0 = 1 - X 0 0 * (u 0 1 * X 1 0) ∧
      (X * u * X⁻¹) 0 1 = u 0 1 * X 0 0 ^ 2 ∧ (X * u * X⁻¹) 1 0 = -(u 0 1 * X 1 0 ^ 2) ∧
      (X * u * X⁻¹) 1 1 = 1 + X 0 0 * (u 0 1 * X 1 0) := fun X => by
    have hX := X.2
    rw [Matrix.det_fin_two] at hX
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, hu00, hu10, hu11]
    exact ⟨by linear_combination hX, by ring, by ring, by linear_combination hX⟩
  -- `eₙ = β cₙ` satisfies `eₙ₊₁ = −eₙ²`, so `eₙ → 0`
  have he_rec : ∀ n, u 0 1 * m (n + 1) 1 0 = -(u 0 1 * m n 1 0) ^ 2 := fun n => by
    rw [hms, (hstep (m n)).2.2.1]
    ring
  have ha_rec : ∀ n, m (n + 1) 0 0 = 1 - m n 0 0 * (u 0 1 * m n 1 0) := fun n => by
    rw [hms, (hstep (m n)).1]
  have hβc' : |u 0 1 * m 0 1 0| < 1 := by rw [hm0]; exact hβc
  have he_le : ∀ n, |u 0 1 * m n 1 0| ≤ |u 0 1 * m 0 1 0| := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [he_rec, abs_neg, abs_pow, sq]
      have h1 : |u 0 1 * m n 1 0| < 1 := ih.trans_lt hβc'
      calc |u 0 1 * m n 1 0| * |u 0 1 * m n 1 0| ≤ 1 * |u 0 1 * m n 1 0| :=
            mul_le_mul_of_nonneg_right h1.le (abs_nonneg _)
        _ ≤ |u 0 1 * m 0 1 0| := by rw [one_mul]; exact ih
  have he : Tendsto (fun n => u 0 1 * m n 1 0) atTop (𝓝 0) := by
    refine (summable_of_ratio_norm_eventually_le hβc' (Filter.Eventually.of_forall fun n => ?_)).tendsto_atTop_zero
    simp only [Real.norm_eq_abs]
    rw [he_rec, abs_neg, abs_pow, sq]
    exact mul_le_mul_of_nonneg_right (he_le n) (abs_nonneg _)
  -- `aₙ` stays bounded, so `aₙ eₙ → 0` and `aₙ₊₁ = 1 − aₙeₙ → 1`
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((tendsto_zero_iff_norm_tendsto_zero.1 he).eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  have hB : ∀ k, |m (N + k) 0 0| ≤ max |m N 0 0| 2 := by
    intro k
    induction k with
    | zero => exact le_max_left _ _
    | succ k ih =>
      rw [← add_assoc, ha_rec]
      have h1 := norm_sub_le (1 : ℝ) (m (N + k) 0 0 * (u 0 1 * m (N + k) 1 0))
      simp only [Real.norm_eq_abs, abs_one, abs_mul] at h1
      have h2 : |u 0 1 * m (N + k) 1 0| ≤ 1 / 2 := by
        have := hN (N + k) (by omega)
        rwa [Real.norm_eq_abs] at this
      have h3 : |m (N + k) 0 0| * |u 0 1 * m (N + k) 1 0| ≤ max |m N 0 0| 2 * (1 / 2) :=
        mul_le_mul ih h2 (abs_nonneg _) (by positivity)
      have h4 : (2 : ℝ) ≤ max |m N 0 0| 2 := le_max_right _ _
      rw [abs_mul] at h3
      linarith
  have hae : Tendsto (fun n => m n 0 0 * (u 0 1 * m n 1 0)) atTop (𝓝 0) := by
    have hb' : Tendsto (fun n => max |m N 0 0| 2 * |u 0 1 * m n 1 0|) atTop (𝓝 0) := by
      have := (tendsto_zero_iff_norm_tendsto_zero.1 he).const_mul (max |m N 0 0| 2)
      simp only [Real.norm_eq_abs, mul_zero] at this
      exact this
    refine squeeze_zero_norm' ?_ hb'
    rw [Filter.eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hB k) (abs_nonneg _)
  have ha1 : Tendsto (fun n => m n 0 0) atTop (𝓝 1) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub hae
    rw [sub_zero] at this
    exact this.congr fun n => (ha_rec n).symm
  have hc : Tendsto (fun n => m n 1 0) atTop (𝓝 0) := by
    have := he.div_const (u 0 1)
    rw [zero_div] at this
    exact this.congr fun n => mul_div_cancel_left₀ _ hb
  -- so `mₙ₊₁ → u`, hence `Sₙ₊₁ → T`, and discreteness gives `Sₙ₊₁ = T`
  have hlim : Tendsto (fun n => m (n + 1)) atTop (𝓝 u) := by
    refine k92el_sl_tendsto ?_ ?_ ?_ ?_
    · rw [hu00]
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub hae
      rw [sub_zero] at this
      exact this.congr fun n => by rw [hms, (hstep (m n)).1]
    · have := (ha1.pow 2).const_mul (u 0 1)
      rw [one_pow, mul_one] at this
      exact this.congr fun n => by rw [hms, (hstep (m n)).2.1]
    · rw [hu10]
      have := ((hc.pow 2).const_mul (u 0 1)).neg
      rw [zero_pow two_ne_zero, mul_zero, neg_zero] at this
      exact this.congr fun n => by rw [hms, (hstep (m n)).2.2.1]
    · rw [hu11]
      have := (tendsto_const_nhds (x := (1 : ℝ))).add hae
      rw [add_zero] at this
      exact this.congr fun n => by rw [hms, (hstep (m n)).2.2.2]
  have hlimσ : Tendsto (fun n => σ (n + 1)) atTop (𝓝 (T : PSL(2, ℝ))) := by
    have h1 := ((tendsto_const_nhds (x := (P : PSL(2, ℝ))⁻¹)).mul
      ((QuotientGroup.continuous_mk.tendsto u).comp hlim)).mul (tendsto_const_nhds (x := (P : PSL(2, ℝ))))
    have e : (P : PSL(2, ℝ))⁻¹ * (u : PSL(2, ℝ)) * P = T := by
      rw [hu]
      group
    rw [e] at h1
    exact h1.congr fun n => hmσ (n + 1)
  obtain ⟨n, hn⟩ := (k92el_eventually_eq hd (fun n => k92el_seq_mem h0 hs (n + 1))
    (Subgroup.subset_closure (Set.mem_insert _ _)) hlimσ).exists
  exact ⟨n + 1, hn⟩

/-- Auxiliary (§2.4, proof of Theorem 2.4.6, Cases 2 and 3: `T` hyperbolic or elliptic). Diagonalize `T` over `ℂ`
(`k92el_cdiag`); the quantity becomes `|u − u⁻¹|² (1 + |b₀c₀|)` for the entries of `Q S Q⁻¹`, and by
`k92el_jorg_core` the conjugates `T⁻ʲ S₂ⱼ Tʲ` (entries `a₂ⱼ, b₂ⱼu⁻²ʲ, c₂ⱼu²ʲ, d₂ⱼ` in the diagonal frame) tend to
`T`; discreteness gives `S₂ⱼ = T` (`k92el_eventually_eq`). -/
theorem k92el_jorg_diag (T S : SL(2, ℝ)) (hT : IsHyperbolic (T : PSL(2, ℝ)) ∨ IsElliptic (T : PSL(2, ℝ)))
    (hd : IsFuchsian (Subgroup.closure {(T : PSL(2, ℝ)), (S : PSL(2, ℝ))}))
    (hμ : |trSq (T : PSL(2, ℝ)) - 4| +
      |Matrix.trace ((T * S * T⁻¹ * S⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) - 2| < 1)
    {σ : ℕ → PSL(2, ℝ)} (h0 : σ 0 = S) (hs : ∀ r, σ (r + 1) = σ r * T * (σ r)⁻¹) : ∃ n, σ n = T := by
  -- `tr² ≠ 4`
  have htr4 : (T 0 0 + T 1 1) ^ 2 ≠ 4 := by
    have h := k92_Tr_mk T
    rw [Matrix.trace_fin_two] at h
    intro e
    rcases hT with hh | he
    · rw [IsHyperbolic, h] at hh
      nlinarith [sq_abs (T 0 0 + T 1 1), abs_nonneg (T 0 0 + T 1 1)]
    · rw [IsElliptic, h] at he
      nlinarith [sq_abs (T 0 0 + T 1 1), abs_nonneg (T 0 0 + T 1 1)]
  obtain ⟨u, hu0, hsum, Q, Q', hQ'Q, hdiag⟩ := k92el_cdiag T htr4
  have hQQ' : Q * Q' = 1 := mul_eq_one_comm.1 hQ'Q
  have huu : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
  -- the complexified conjugation `φ M = Q M Q'`
  obtain ⟨φ, hφ⟩ : ∃ φ : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℂ,
      ∀ M, φ M = Q * M.map Complex.ofReal * Q' := ⟨_, fun _ => rfl⟩
  have hmap : ∀ M N : Matrix (Fin 2) (Fin 2) ℝ,
      (M * N).map Complex.ofReal = M.map Complex.ofReal * N.map Complex.ofReal :=
    fun M N => Matrix.map_mul (f := Complex.ofRealHom)
  have hφmul : ∀ M N, φ (M * N) = φ M * φ N := fun M N => by
    rw [hφ, hφ, hφ, hmap]
    calc Q * (M.map Complex.ofReal * N.map Complex.ofReal) * Q'
        = Q * M.map Complex.ofReal * (Q' * Q) * N.map Complex.ofReal * Q' := by
          rw [hQ'Q, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = Q * M.map Complex.ofReal * Q' * (Q * N.map Complex.ofReal * Q') := by simp only [Matrix.mul_assoc]
  have hφone : φ 1 = 1 := by
    rw [hφ, Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one, Matrix.mul_one, hQQ']
  have hφdet : ∀ X : SL(2, ℝ), (φ X).det = 1 := fun X => by
    have hQdet : Q'.det * Q.det = 1 := by rw [← Matrix.det_mul, hQ'Q, Matrix.det_one]
    have hXdet : ((X : Matrix (Fin 2) (Fin 2) ℝ).map Complex.ofReal).det = 1 := by
      have h := (Complex.ofRealHom.map_det (X : Matrix (Fin 2) (Fin 2) ℝ)).symm
      rw [X.2, map_one] at h
      exact h
    rw [hφ, Matrix.det_mul, Matrix.det_mul, hXdet]
    linear_combination hQdet
  have hφinv : ∀ X : SL(2, ℝ), φ ((X⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = (φ X).adjugate := fun X => by
    have hBA : φ ((X⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) * φ X = 1 := by
      rw [← hφmul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, hφone]
    calc φ ((X⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)
        = φ ((X⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) * (φ X * (φ X).adjugate) := by
          rw [Matrix.mul_adjugate, hφdet X, one_smul, Matrix.mul_one]
      _ = (φ X).adjugate := by rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
  have hφT : φ T = !![u, 0; 0, u⁻¹] := by rw [hφ]; exact hdiag
  -- the quantity becomes `|u − u⁻¹|² (1 + |b₀c₀|)` for `φ S = [[a₀, b₀], [c₀, d₀]]`
  have hq1 : |trSq (T : PSL(2, ℝ)) - 4| = ‖u - u⁻¹‖ ^ 2 := by
    have h : trSq (T : PSL(2, ℝ)) = (T 0 0 + T 1 1) ^ 2 := by rw [trSq, k92_Tr_mk, Matrix.trace_fin_two, sq_abs]
    have hsum' : u + u⁻¹ = (T 0 0 : ℂ) + T 1 1 := by rw [hsum]; push_cast; ring
    have hc : (((T 0 0 + T 1 1) ^ 2 - 4 : ℝ) : ℂ) = (u - u⁻¹) ^ 2 := by
      push_cast
      rw [← hsum']
      linear_combination 4 * huu
    rw [h, ← Real.norm_eq_abs, ← Complex.norm_real, hc, norm_pow]
  have hcomm : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, M.det = 1 →
      Matrix.trace (!![u, 0; 0, u⁻¹] * M * (!![u, 0; 0, u⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).adjugate * M.adjugate) =
        2 - M 0 1 * M 1 0 * (u - u⁻¹) ^ 2 := fun M hM => by
    rw [Matrix.det_fin_two] at hM
    simp only [Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination 2 * (M 0 0 * M 1 1 - M 0 1 * M 1 0) * huu + 2 * hM
  have hq2 : |Matrix.trace ((T * S * T⁻¹ * S⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) - 2| =
      ‖φ S 0 1 * φ S 1 0‖ * ‖u - u⁻¹‖ ^ 2 := by
    have htrφ : ∀ M : Matrix (Fin 2) (Fin 2) ℝ, ((Matrix.trace M : ℝ) : ℂ) = Matrix.trace (φ M) := fun M => by
      rw [hφ, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQ'Q, Matrix.one_mul]
      simp [Matrix.trace_fin_two]
    have e : φ ((T * S * T⁻¹ * S⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![u, 0; 0, u⁻¹] * φ S * (!![u, 0; 0, u⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).adjugate * (φ S).adjugate := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, hφmul, hφinv, hφT]
    have hc : ((Matrix.trace ((T * S * T⁻¹ * S⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) - 2 : ℝ) : ℂ) =
        -(φ S 0 1 * φ S 1 0 * (u - u⁻¹) ^ 2) := by
      push_cast
      rw [htrφ, e, hcomm _ (hφdet S)]
      ring
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hc, norm_neg, norm_mul, norm_pow]
  have hμ' : ‖u - u⁻¹‖ ^ 2 * (1 + ‖φ S 0 1 * φ S 1 0‖) < 1 := by
    rw [hq1, hq2] at hμ
    calc ‖u - u⁻¹‖ ^ 2 * (1 + ‖φ S 0 1 * φ S 1 0‖)
        = ‖u - u⁻¹‖ ^ 2 + ‖φ S 0 1 * φ S 1 0‖ * ‖u - u⁻¹‖ ^ 2 := by ring
      _ < 1 := hμ
  -- lifts `sₙ` of the sequence (2.5.3); the entries of `φ sₙ` follow `k92el_jorg_core`
  obtain ⟨s, hs0, hss⟩ : ∃ s : ℕ → SL(2, ℝ), s 0 = S ∧ ∀ r, s (r + 1) = s r * T * (s r)⁻¹ :=
    ⟨fun n => Nat.rec (motive := fun _ => SL(2, ℝ)) S (fun _ X => X * T * X⁻¹) n, rfl, fun _ => rfl⟩
  have hsσ : ∀ n, (s n : PSL(2, ℝ)) = σ n := by
    intro n
    induction n with
    | zero => rw [hs0, h0]
    | succ n ih => rw [hss, hs, ← ih, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hrec : ∀ n, φ (s (n + 1) : Matrix (Fin 2) (Fin 2) ℝ) =
      φ (s n) * !![u, 0; 0, u⁻¹] * (φ (s n)).adjugate := fun n => by
    rw [hss, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hφmul, hφmul, hφinv, hφT]
  have hstep : ∀ M : Matrix (Fin 2) (Fin 2) ℂ,
      (M * !![u, 0; 0, u⁻¹] * M.adjugate) 0 0 = M 0 0 * M 1 1 * u - M 0 1 * M 1 0 * u⁻¹ ∧
      (M * !![u, 0; 0, u⁻¹] * M.adjugate) 0 1 = M 0 0 * M 0 1 * (u⁻¹ - u) ∧
      (M * !![u, 0; 0, u⁻¹] * M.adjugate) 1 0 = M 1 0 * M 1 1 * (u - u⁻¹) ∧
      (M * !![u, 0; 0, u⁻¹] * M.adjugate) 1 1 = M 0 0 * M 1 1 * u⁻¹ - M 0 1 * M 1 0 * u := fun M => by
    simp only [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    exact ⟨by ring, by ring, by ring, by ring⟩
  obtain ⟨ha, hd', hb, hc⟩ := k92el_jorg_core hu0 (a := fun n => φ (s n) 0 0) (b := fun n => φ (s n) 0 1)
    (c := fun n => φ (s n) 1 0) (d := fun n => φ (s n) 1 1)
    (fun n => by
      have := hφdet (s n)
      rwa [Matrix.det_fin_two] at this)
    (fun n => by rw [hrec]; exact (hstep _).1)
    (fun n => by rw [hrec]; exact (hstep _).2.1)
    (fun n => by rw [hrec]; exact (hstep _).2.2.1)
    (fun n => by rw [hrec]; exact (hstep _).2.2.2)
    (by rw [hs0]; exact hμ')
  -- `φ (T⁻ʲ S₂ⱼ Tʲ) = [[a₂ⱼ, b₂ⱼu⁻²ʲ], [c₂ⱼu²ʲ, d₂ⱼ]] → diag(u, u⁻¹) = φ T`
  have hDpow : ∀ (x y : ℂ) (j : ℕ), (!![x, 0; 0, y] : Matrix (Fin 2) (Fin 2) ℂ) ^ j = !![x ^ j, 0; 0, y ^ j] := by
    intro x y j
    induction j with
    | zero =>
      ext i k
      fin_cases i <;> fin_cases k <;> simp
    | succ j ih =>
      rw [pow_succ, ih]
      ext i k
      fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]
  have hφpow : ∀ (X : SL(2, ℝ)) (j : ℕ), φ ((X ^ j : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = (φ X) ^ j := by
    intro X j
    induction j with
    | zero => rw [pow_zero, pow_zero, Matrix.SpecialLinearGroup.coe_one, hφone]
    | succ j ih => rw [pow_succ, pow_succ, Matrix.SpecialLinearGroup.coe_mul, hφmul, ih]
  have hφTi : φ ((T⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![u⁻¹, 0; 0, u] := by
    rw [hφinv, hφT, Matrix.adjugate_fin_two]
    simp
  have h1 : ∀ j : ℕ, u⁻¹ ^ j * u ^ j = 1 := fun j => by rw [← mul_pow, inv_mul_cancel₀ hu0, one_pow]
  have h2 : ∀ j : ℕ, u ^ j * u⁻¹ ^ j = 1 := fun j => by rw [← mul_pow, mul_inv_cancel₀ hu0, one_pow]
  have hXφ : ∀ j : ℕ, φ ((T⁻¹ ^ j * s (2 * j) * T ^ j : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![φ (s (2 * j)) 0 0, φ (s (2 * j)) 0 1 * u⁻¹ ^ (2 * j); φ (s (2 * j)) 1 0 * u ^ (2 * j),
        φ (s (2 * j)) 1 1] := fun j => by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hφmul, hφmul, hφpow, hφpow, hφTi,
      hφT, hDpow, hDpow]
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one]
    · linear_combination φ (s (2 * j)) 0 0 * h1 j
    · ring
    · ring
    · linear_combination φ (s (2 * j)) 1 1 * h2 j
  have h2j : Tendsto (fun j : ℕ => 2 * j) atTop atTop :=
    Filter.tendsto_atTop_mono (fun j => (show j ≤ 2 * j by omega)) Filter.tendsto_id
  have hφX : Tendsto (fun j : ℕ => φ ((T⁻¹ ^ j * s (2 * j) * T ^ j : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) atTop
      (𝓝 !![u, 0; 0, u⁻¹]) := by
    rw [tendsto_congr hXφ]
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun k => ?_
    fin_cases i <;> fin_cases k
    · simpa [Function.comp_def] using ha.comp h2j
    · simpa [Function.comp_def] using hb.comp h2j
    · simpa [Function.comp_def] using hc.comp h2j
    · simpa [Function.comp_def] using hd'.comp h2j
  -- back in SL(2,ℝ): `T⁻ʲ S₂ⱼ Tʲ → T`
  have hback : ∀ M : Matrix (Fin 2) (Fin 2) ℝ, M.map Complex.ofReal = Q' * φ M * Q := fun M => by
    rw [hφ]
    simp only [← Matrix.mul_assoc]
    rw [hQ'Q, Matrix.one_mul, Matrix.mul_assoc, hQ'Q, Matrix.mul_one]
  have hlimC : Tendsto (fun j : ℕ => ((T⁻¹ ^ j * s (2 * j) * T ^ j : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).map
      Complex.ofReal) atTop (𝓝 ((T : Matrix (Fin 2) (Fin 2) ℝ).map Complex.ofReal)) := by
    rw [tendsto_congr fun j => hback _, hback, hφT]
    exact (tendsto_const_nhds.mul hφX).mul tendsto_const_nhds
  have hlimSL : Tendsto (fun j : ℕ => T⁻¹ ^ j * s (2 * j) * T ^ j) atTop (𝓝 T) := by
    have hent : ∀ i k, Tendsto (fun j : ℕ => (T⁻¹ ^ j * s (2 * j) * T ^ j : SL(2, ℝ)) i k) atTop (𝓝 (T i k)) :=
      fun i k => by
        have := (Complex.continuous_re.tendsto _).comp (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hlimC i) k)
        simpa [Function.comp_def] using this
    exact k92el_sl_tendsto (hent 0 0) (hent 0 1) (hent 1 0) (hent 1 1)
  -- discreteness: `T⁻ʲ S₂ⱼ Tʲ = T` for some `j`, so `S₂ⱼ = T`
  have hTc : (T : PSL(2, ℝ)) ∈ Subgroup.closure {(T : PSL(2, ℝ)), (S : PSL(2, ℝ))} :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hXmem : ∀ j : ℕ, ((T⁻¹ ^ j * s (2 * j) * T ^ j : SL(2, ℝ)) : PSL(2, ℝ)) ∈
      Subgroup.closure {(T : PSL(2, ℝ)), (S : PSL(2, ℝ))} := fun j => by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow, QuotientGroup.mk_inv,
      hsσ]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.inv_mem _ hTc) j)
      (k92el_seq_mem h0 hs _)) (Subgroup.pow_mem _ hTc j)
  obtain ⟨j, hj⟩ := (k92el_eventually_eq hd hXmem hTc
    ((QuotientGroup.continuous_mk.tendsto T).comp hlimSL)).exists
  refine ⟨2 * j, ?_⟩
  rw [← hsσ]
  have e : ((T⁻¹ ^ j * s (2 * j) * T ^ j : SL(2, ℝ)) : PSL(2, ℝ)) = (T : PSL(2, ℝ)) := hj
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow,
    QuotientGroup.mk_inv] at e
  calc ((s (2 * j) : SL(2, ℝ)) : PSL(2, ℝ)) = (T : PSL(2, ℝ)) ^ j *
      ((T : PSL(2, ℝ))⁻¹ ^ j * (s (2 * j) : PSL(2, ℝ)) * (T : PSL(2, ℝ)) ^ j) * (T : PSL(2, ℝ))⁻¹ ^ j := by group
    _ = T := by rw [e]; group

/-- **Theorem 2.4.6** (Jørgensen's inequality; §2.4; l. 991–995, display "(2.5.1)" [label sic]). If `⟨T, S⟩` is
discrete and non-elementary, then `|tr²(T) − 4| + |tr(TST⁻¹S⁻¹) − 2| ≥ 1`.
Modelling: `T S` are SL(2,ℝ) lifts; `tr²(T)` is Ch. 1's `trSq`, the commutator trace is taken on the lifts. -/
theorem thm2_4_6 (T S : SL(2, ℝ))
    (hd : IsFuchsian (Subgroup.closure {(T : PSL(2, ℝ)), (S : PSL(2, ℝ))}))
    (hne : ¬ IsElementary (Subgroup.closure {(T : PSL(2, ℝ)), (S : PSL(2, ℝ))})) :
    1 ≤ |trSq (T : PSL(2, ℝ)) - 4| +
      |Matrix.trace ((T * S * T⁻¹ * S⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) - 2| := by
  by_contra hlt
  push Not at hlt
  have hT1 : (T : PSL(2, ℝ)) ≠ 1 := by
    intro h1
    apply hne
    rw [h1]
    exact k92el_elem_one _
  -- the sequence (2.5.3): `S₀ = S`, `Sᵣ₊₁ = Sᵣ T Sᵣ⁻¹`
  obtain ⟨σ, h0, hs⟩ : ∃ σ : ℕ → PSL(2, ℝ), σ 0 = S ∧ ∀ r, σ (r + 1) = σ r * T * (σ r)⁻¹ :=
    ⟨fun n => Nat.rec (motive := fun _ => PSL(2, ℝ)) (S : PSL(2, ℝ)) (fun _ X => X * (T : PSL(2, ℝ)) * X⁻¹) n,
      rfl, fun _ => rfl⟩
  -- if the quantity is `< 1`, then `Sₙ = T` for some `n`, and `⟨T, S⟩` is elementary (Lemma 2.4.7)
  apply hne
  rcases k92f_trichotomy hT1 with he | hp | hh
  · exact k92el_seq_elem hT1 h0 hs (k92el_jorg_diag T S (Or.inr he) hd hlt h0 hs)
  · exact k92el_seq_elem hT1 h0 hs (k92el_jorg_par T S hp hd hlt h0 hs)
  · exact k92el_seq_elem hT1 h0 hs (k92el_jorg_diag T S (Or.inl hh) hd hlt h0 hs)

/-- Auxiliary (§2.4, the sharpness example). `⟨z + 1, −1/z⟩` is Fuchsian: it lies in the modular group (Example A of
§2.2, `exampleA_isFuchsian`). -/
theorem k92el_sharp_fuchsian {T S : SL(2, ℝ)} (hT : (T : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 1; 0, 1])
    (hS : (S : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; 1, 0]) :
    IsFuchsian (Subgroup.closure {(T : PSL(2, ℝ)), (S : PSL(2, ℝ))}) := by
  -- both generators are images of integer matrices, so the group lies in the modular group
  have hmem : ∀ (A : SL(2, ℤ)) (U : SL(2, ℝ)), (U : Matrix (Fin 2) (Fin 2) ℝ) = (A : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.castRingHom ℝ) → (U : PSL(2, ℝ)) ∈ modularGroup := fun A U h => by
    refine ⟨A, ?_⟩
    show ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A : SL(2, ℝ)) : PSL(2, ℝ)) = U
    congr 1
    exact Subtype.ext h.symm
  refine k92el_fuchsian_mono exampleA_isFuchsian (Subgroup.closure_le _ |>.2 ?_)
  rintro _ (rfl | rfl)
  · refine hmem ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩ T ?_
    rw [hT]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · refine hmem ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩ S ?_
    rw [hS]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- Auxiliary (§2.4, the sharpness example). `⟨z + 1, −1/z⟩` is non-elementary: a finite orbit would be fixed by a
power of the parabolic `z ↦ z + 1` (so it is `{∞}`) and by a power of its conjugate `z ↦ z/(1 − z)` (so it is `{0}`). -/
theorem k92el_sharp_nonelem {T S : SL(2, ℝ)} (hT : (T : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 1; 0, 1])
    (hS : (S : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; 1, 0]) :
    ¬ IsElementary (Subgroup.closure {(T : PSL(2, ℝ)), (S : PSL(2, ℝ))}) := by
  rintro ⟨x, hx⟩
  set Γ := Subgroup.closure {(T : PSL(2, ℝ)), (S : PSL(2, ℝ))}
  -- the finite orbit is preserved by all of Γ
  have hinv : ∀ U ∈ Γ, ∀ y ∈ MulAction.orbit Γ x, U • y ∈ MulAction.orbit Γ x := fun U hU y hy => by
    obtain ⟨g, rfl⟩ := hy
    exact ⟨⟨U, hU⟩ * g, mul_smul _ _ _⟩
  have hxO : x ∈ MulAction.orbit Γ x := MulAction.mem_orbit_self x
  -- a parabolic `V ∈ Γ` fixing `y` forces `x = y`
  have key : ∀ V ∈ Γ, ∀ y : Hbar, IsParabolic V → V • y = y → x = y := fun V hV y hpar hy => by
    obtain ⟨α, hα⟩ := fixedBy_of_isParabolic hpar
    have hxV := k92el_finite_inv_subset_fix (Or.inr hpar) hx (hinv V hV) hxO
    have hyV : y ∈ MulAction.fixedBy Hbar V := hy
    rw [hα] at hxV hyV
    rw [mem_singleton_iff] at hxV hyV
    rw [hxV, hyV]
  -- `T(z) = z + 1` (fixing `∞`) and `S T S⁻¹ = [[1, 0], [−1, 1]]` (fixing `0`) are parabolic
  set U : SL(2, ℝ) := S * T * S⁻¹ with hUdef
  have hU : (U : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; -1, 1] := by
    simp only [hUdef, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, hT, hS]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  have hpar : ∀ W : SL(2, ℝ), (W : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 → (W : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 →
      (W 0 1 ≠ 0 ∨ W 1 0 ≠ 0) → IsParabolic (W : PSL(2, ℝ)) := fun W h00 h11 hne => by
    refine ⟨by rw [k92_Tr_mk, Matrix.trace_fin_two, h00, h11]; norm_num, fun h1 => ?_⟩
    obtain ⟨h10, h01, -⟩ := k92f_center_entries W h1
    rcases hne with h | h
    · exact h h01
    · exact h h10
  have hTpar : IsParabolic (T : PSL(2, ℝ)) :=
    hpar T (by rw [hT]; rfl) (by rw [hT]; rfl) (Or.inl (by rw [hT]; simp))
  have hUpar : IsParabolic (U : PSL(2, ℝ)) :=
    hpar U (by rw [hU]; rfl) (by rw [hU]; rfl) (Or.inr (by rw [hU]; simp))
  have hTΓ : (T : PSL(2, ℝ)) ∈ Γ := Subgroup.subset_closure (Or.inl rfl)
  have hSΓ : (S : PSL(2, ℝ)) ∈ Γ := Subgroup.subset_closure (Or.inr rfl)
  have hUΓ : (U : PSL(2, ℝ)) ∈ Γ := by
    rw [hUdef, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact Γ.mul_mem (Γ.mul_mem hSΓ hTΓ) (Γ.inv_mem hSΓ)
  have hTinf : (T : PSL(2, ℝ)) • (Sum.inr OnePoint.infty : Hbar) = Sum.inr OnePoint.infty := by
    rw [Sum.smul_inr, k92n_bdry_smul, OnePoint.smul_infty_eq_self_iff.2 (by show T 1 0 = 0; rw [hT]; rfl)]
  have hU0 : (U : PSL(2, ℝ)) • (Sum.inr ((0 : ℝ) : OnePoint ℝ) : Hbar) = Sum.inr ((0 : ℝ) : OnePoint ℝ) := by
    rw [Sum.smul_inr, k92n_bdry_smul, OnePoint.smul_some_eq_ite]
    have e1 : ((Matrix.SpecialLinearGroup.mapGL ℝ U : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * 0 +
        ((Matrix.SpecialLinearGroup.mapGL ℝ U : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ≠ 0 := by
      show U 1 0 * 0 + U 1 1 ≠ 0
      rw [hU]
      simp
    rw [ite_eq_right e1]
    congr 2
    show (U 0 0 * 0 + U 0 1) / (U 1 0 * 0 + U 1 1) = 0
    rw [hU]
    simp
  have h1 := key _ hTΓ _ hTpar hTinf
  have h2 := key _ hUΓ _ hUpar hU0
  rw [h1] at h2
  exact OnePoint.infty_ne_coe 0 (Sum.inr_injective h2)

/-- Auxiliary (§2.4, the sharpness example). `tr² T = 4` and `T S T⁻¹ S⁻¹ = [[2, 1], [1, 1]]` has trace `3`. -/
theorem k92el_sharp_trace {T S : SL(2, ℝ)} (hT : (T : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 1; 0, 1])
    (hS : (S : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; 1, 0]) :
    |trSq (T : PSL(2, ℝ)) - 4| +
      |Matrix.trace ((T * S * T⁻¹ * S⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) - 2| = 1 := by
  have e1 : trSq (T : PSL(2, ℝ)) = 4 := by
    rw [trSq, k92_Tr_mk, Matrix.trace_fin_two, hT]
    norm_num
  have e2 : Matrix.trace ((T * S * T⁻¹ * S⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = 3 := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, hT, hS]
    simp [Matrix.trace_fin_two, Matrix.adjugate_fin_two]
    norm_num
  rw [e1, e2]
  norm_num

/-- **Theorem 2.4.6** (§2.4; l. 997). "The lower bound is best possible": equality occurs (the book's example is
`z + 1`, `−1/z`, l. 1115). -/
theorem thm2_4_6_sharp : ∃ T S : SL(2, ℝ),
    IsFuchsian (Subgroup.closure {(T : PSL(2, ℝ)), (S : PSL(2, ℝ))}) ∧
    ¬ IsElementary (Subgroup.closure {(T : PSL(2, ℝ)), (S : PSL(2, ℝ))}) ∧
    |trSq (T : PSL(2, ℝ)) - 4| +
      |Matrix.trace ((T * S * T⁻¹ * S⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) - 2| = 1 := by
  -- `T(z) = z + 1`, `S(z) = −1/z` (l. 1115)
  exact ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩, ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩,
    k92el_sharp_fuchsian rfl rfl, k92el_sharp_nonelem rfl rfl, k92el_sharp_trace rfl rfl⟩

/-- Helper ((2.5.3), §2.4, l. 1001). `S₀ = S`, `S_{r+1} = S_r T S_r⁻¹`. -/
def conjSeq (T S : PSL(2, ℝ)) : ℕ → PSL(2, ℝ)
  | 0 => S
  | r + 1 => conjSeq T S r * T * (conjSeq T S r)⁻¹

/-- **Lemma 2.4.7** (§2.4; l. 1001). If `T ≠ Id` and `S_n = T` for some `n`, then `⟨T, S⟩` is elementary and
`S₂ = T`. -/
theorem lemma2_4_7 {T S : PSL(2, ℝ)} (hT : T ≠ 1) (h : ∃ n, conjSeq T S n = T) :
    IsElementary (Subgroup.closure {T, S}) ∧ conjSeq T S 2 = T := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨hFfin, hFne⟩ := k92el_finite_fixedBy hT
  set F := MulAction.fixedBy Hbar T with hFdef
  -- `S_{r+1} = S_r T S_r⁻¹`, so `Fix(S_{r+1}) = S_r F`
  have hfixr : ∀ r, MulAction.fixedBy Hbar (conjSeq T S (r + 1)) = (conjSeq T S r • ·) '' F :=
    fun r => k92el_fixedBy_conj _ _
  -- downward induction: `S_r F = F` for all `r ≤ n`
  have hstep : ∀ r, (conjSeq T S (r + 1) • ·) '' F = F → (conjSeq T S r • ·) '' F = F := fun r hr => by
    have hpres : ∀ x ∈ F, (conjSeq T S r * T * (conjSeq T S r)⁻¹) • x ∈ F := fun x hx => by
      rw [← hr]
      exact ⟨x, hx, rfl⟩
    have hsub : F ⊆ (conjSeq T S r • ·) '' F := by
      rw [← hfixr r]
      exact k92el_conj_fix_of_preserve hT hpres
    refine (Set.eq_of_subset_of_ncard_le hsub ?_ (hFfin.image _)).symm
    rw [Set.ncard_image_of_injective _ (MulAction.injective _)]
  have hall : ∀ k, k ≤ n → (conjSeq T S (n - k) • ·) '' F = F := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.sub_zero, hn]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        show T • y ∈ F
        rw [show T • y = y from hy]
        exact hy
      · intro hx
        exact ⟨x, hx, hx⟩
    | succ k ih =>
      intro hk
      have := ih (Nat.le_of_succ_le hk)
      rw [show n - k = n - (k + 1) + 1 by omega] at this
      exact hstep _ this
  have h0 : (S • ·) '' F = F := by
    have := hall n le_rfl
    rwa [Nat.sub_self] at this
  -- ⟨T, S⟩ preserves the finite set `F`
  have hTF : ∀ x ∈ F, T • x ∈ F := fun x hx => by
    rw [show T • x = x from hx]
    exact hx
  refine ⟨k92el_closure_of_finite_inv hFfin hFne hTF fun x hx => ?_, ?_⟩
  · rw [← h0]
    exact ⟨x, hx, rfl⟩
  · -- `Fix(S₁) = S F = F = Fix T`, so `S₁` commutes with `T` and `S₂ = T`
    have hS1 : conjSeq T S 1 ≠ 1 := by
      show S * T * S⁻¹ ≠ 1
      intro h1
      apply hT
      calc T = S⁻¹ * (S * T * S⁻¹) * S := by group
        _ = 1 := by rw [h1]; group
    have hfix1 : MulAction.fixedBy Hbar (conjSeq T S 1) = F := by
      rw [hfixr 0]
      exact h0
    have hc := k92f_commute_of_fix_eq hS1 hT hfix1
    show conjSeq T S 1 * T * (conjSeq T S 1)⁻¹ = T
    rw [hc, mul_inv_cancel_right]

/-- Auxiliary (§2.4, proof of Theorem 2.4.8). `Tₙ → Id` gives `Tr Tₙ → 2` (`Tr` lifts to the continuous even
function `|tr|`, `k92el_tendsto_even`). -/
theorem k92el_tr_tendsto {T : ℕ → PSL(2, ℝ)} (hT : Tendsto T atTop (𝓝 1)) :
    Tendsto (fun n => Tr (T n)) atTop (𝓝 2) := by
  have hc : Continuous fun g : SL(2, ℝ) => |Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℝ)| :=
    continuous_abs.comp (Continuous.matrix_trace continuous_subtype_val)
  have hn : ∀ g : SL(2, ℝ), |Matrix.trace ((-g : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)| =
      |Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℝ)| := fun g => by
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg, abs_neg]
  have h : Tendsto (fun n => Tr (T n)) atTop (𝓝 (Tr 1)) := k92el_tendsto_even hc hn hT
  have h1 : Tr 1 = 2 := by
    rw [← QuotientGroup.mk_one, k92_Tr_mk]
    simp
  rwa [h1] at h

/-- Auxiliary (§2.4, proof of Theorem 2.4.8). Along `Tₙ → Id`, the Jørgensen quantity of the lifts of `Tₙ` and `S`
tends to `0` (both terms are continuous even functions of the lift of `Tₙ`, vanishing at `±Id`). -/
theorem k92el_jorg_tendsto (S : PSL(2, ℝ)) {T : ℕ → PSL(2, ℝ)} (hT : Tendsto T atTop (𝓝 1)) :
    Tendsto (fun n => |trSq ((Quotient.out (T n) : SL(2, ℝ)) : PSL(2, ℝ)) - 4| +
      |Matrix.trace ((Quotient.out (T n) * Quotient.out S * (Quotient.out (T n))⁻¹ * (Quotient.out S)⁻¹ :
        SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) - 2|) atTop (𝓝 0) := by
  set s := Quotient.out S with hsdef
  set f : SL(2, ℝ) → ℝ := fun g => |Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 - 4| +
    |Matrix.trace ((g * s * g⁻¹ * s⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) - 2| with hfdef
  have hc : Continuous f := by
    have hw : Continuous fun g : SL(2, ℝ) => g * s * g⁻¹ * s⁻¹ := by fun_prop
    exact (continuous_abs.comp (((Continuous.matrix_trace continuous_subtype_val).pow 2).sub
      continuous_const)).add (continuous_abs.comp ((Continuous.matrix_trace (continuous_subtype_val.comp hw)).sub
      continuous_const))
  have hn : ∀ g, f (-g) = f g := fun g => by
    simp only [hfdef, Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg, neg_sq, inv_neg, neg_mul, mul_neg,
      neg_neg]
  have h := k92el_tendsto_even hc hn hT
  have h1 : f (Quotient.out (1 : PSL(2, ℝ))) = 0 := by
    have h1' : f 1 = 0 := by
      simp only [hfdef, one_mul, inv_one, mul_one, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
        Matrix.trace_one]
      norm_num
    have := k92_out_mk 1
    rw [QuotientGroup.mk_one] at this
    rcases this with e | e
    · rw [e, h1']
    · rw [e, hn, h1']
  have e : ∀ n, |trSq ((Quotient.out (T n) : SL(2, ℝ)) : PSL(2, ℝ)) - 4| +
      |Matrix.trace ((Quotient.out (T n) * Quotient.out S * (Quotient.out (T n))⁻¹ * (Quotient.out S)⁻¹ :
        SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) - 2| = f (Quotient.out (T n)) := fun n => by
    simp only [hfdef, hsdef, trSq, k92_Tr_mk, sq_abs]
  rw [h1] at h
  exact h.congr fun n => (e n).symm

/-- Auxiliary (§2.4, proof of Theorem 2.4.8). An element interchanging two distinct boundary points has `Tr = 0`:
conjugated so that they are `∞, 0`, its lift has zero diagonal (`k92el_to_infty_zero`, `k92el_swap_shape`). -/
theorem k92el_swap_tr_zero {T : PSL(2, ℝ)} {α β : OnePoint ℝ} (hαβ : α ≠ β)
    (h1 : T • (Sum.inr α : Hbar) = Sum.inr β) (h2 : T • (Sum.inr β : Hbar) = Sum.inr α) : Tr T = 0 := by
  obtain ⟨R, hRα, hRβ⟩ := k92el_to_infty_zero hαβ
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (R * T * R⁻¹)
  have h0 := k92el_swap_shape g (by rw [hg, ← hRα, mul_smul, mul_smul, inv_smul_smul, h1, hRβ])
    (by rw [hg, ← hRβ, mul_smul, mul_smul, inv_smul_smul, h2, hRα])
  have hc : Tr (R * T * R⁻¹) = Tr T := by simpa using tr_conj R⁻¹ T
  rw [← hc, ← hg, k92_Tr_mk, Matrix.trace_fin_two, h0.1, h0.2, add_zero, abs_zero]

/-- Auxiliary (§2.4, proof of Theorem 2.4.8). If `⟨T, S⟩` is discrete and elementary, `S` hyperbolic and `Tr T ≠ 0`,
then `T` fixes both fixed points of `S`: a finite orbit lies in `Fix S` (`k92el_finite_inv_subset_fix`); `T`
preserves it, cannot interchange the two points (`k92el_swap_tr_zero`), and fixing one fixes the other
(`k92el_share_one`). -/
theorem k92el_fix_pair_of_elem {T S : PSL(2, ℝ)} (hd : IsFuchsian (Subgroup.closure {T, S}))
    (he : IsElementary (Subgroup.closure {T, S})) (hS : IsHyperbolic S) (hT : Tr T ≠ 0) :
    MulAction.fixedBy Hbar S ⊆ MulAction.fixedBy Hbar T := by
  obtain ⟨α, β, hαβ, hfix⟩ := fixedBy_of_isHyperbolic hS
  obtain ⟨x, hfin⟩ := he
  set O := MulAction.orbit (Subgroup.closure {T, S}) x with hOdef
  have hTc : T ∈ Subgroup.closure {T, S} := Subgroup.subset_closure (Set.mem_insert _ _)
  have hSc : S ∈ Subgroup.closure {T, S} := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hinv : ∀ U ∈ Subgroup.closure {T, S}, ∀ y ∈ O, U • y ∈ O := fun U hU y hy => by
    obtain ⟨γ, rfl⟩ := hy
    exact ⟨⟨U, hU⟩ * γ, mul_smul _ _ _⟩
  -- the orbit lies in `Fix S = {α, β}`
  have hsub : ∀ y ∈ O, y = Sum.inr α ∨ y = Sum.inr β := fun y hy => by
    have := k92el_finite_inv_subset_fix (Or.inl hS) hfin (hinv S hSc) hy
    rwa [hfix] at this
  have hxO : x ∈ O := MulAction.mem_orbit_self x
  -- fixing one fixed point of `S` forces fixing the other (I0e)
  have hone : ∀ {y z : Hbar}, MulAction.fixedBy Hbar S = {y, z} → T • y = y →
      MulAction.fixedBy Hbar S ⊆ MulAction.fixedBy Hbar T := fun {y z} hyz hy => by
    have hz := k92el_share_one hd hSc hTc hS hyz hy
    rw [hyz]
    rintro w (rfl | rfl)
    exacts [hy, hz]
  have hne : (Sum.inr α : Hbar) ≠ Sum.inr β := fun e => hαβ (Sum.inr_injective e)
  rcases hsub x hxO with rfl | rfl
  · -- `T α ∈ {α, β}`; `T α = β` forces `T β = α` (injectivity), an interchange, so `Tr T = 0`
    rcases hsub _ (hinv T hTc _ hxO) with h1 | h1
    · exact hone hfix h1
    · have hβO : (Sum.inr β : Hbar) ∈ O := h1 ▸ hinv T hTc _ hxO
      rcases hsub _ (hinv T hTc _ hβO) with h2 | h2
      · exact absurd (k92el_swap_tr_zero hαβ h1 h2) hT
      · exact absurd (MulAction.injective T (h1.trans h2.symm)) hne
  · rcases hsub _ (hinv T hTc _ hxO) with h1 | h1
    · have hαO : (Sum.inr α : Hbar) ∈ O := h1 ▸ hinv T hTc _ hxO
      rcases hsub _ (hinv T hTc _ hαO) with h2 | h2
      · exact absurd (MulAction.injective T (h2.trans h1.symm)) hne
      · exact absurd (k92el_swap_tr_zero hαβ h2 h1) hT
    · exact hone (by rw [hfix, Set.pair_comm]) h1

/-- **Theorem 2.4.8** (§2.4; l. 1119). A non-elementary Γ ≤ PSL(2,ℝ) is discrete iff `⟨T, S⟩` is discrete for all
`T, S ∈ Γ`. -/
theorem thm2_4_8 {Γ : Subgroup PSL(2, ℝ)} (hΓ : ¬ IsElementary Γ) :
    IsFuchsian Γ ↔ ∀ T ∈ Γ, ∀ S ∈ Γ, IsFuchsian (Subgroup.closure {T, S}) := by
  constructor
  · -- discreteness passes to subgroups
    intro hF T hT S hS
    exact k92el_fuchsian_mono hF
      ((Subgroup.closure_le Γ).2 (Set.insert_subset_iff.2 ⟨hT, Set.singleton_subset_iff.2 hS⟩))
  · intro h
    -- two hyperbolic elements of Γ without common fixed points (Exercise 2.13)
    obtain ⟨s, hsΓ, hsinf, hhyp, hdisj⟩ := exists_infinite_hyperbolic hΓ
    obtain ⟨S₁, h₁, S₂, h₂, h12⟩ := hsinf.nontrivial
    obtain ⟨a, b, hab, hfix₁⟩ := fixedBy_of_isHyperbolic (hhyp S₁ h₁)
    obtain ⟨c, d, -, hfix₂⟩ := fixedBy_of_isHyperbolic (hhyp S₂ h₂)
    rw [IsFuchsian, discreteTopology_iff_tendsto_one]
    intro T hTΓ hlim
    -- for large `n` the quantity of `(Tₙ, S)` is `< 1`, so `⟨Tₙ, S⟩` is elementary (Theorem 2.4.6) and `Tₙ` fixes
    -- both fixed points of `S`
    have key : ∀ S ∈ s, ∀ᶠ n in atTop, MulAction.fixedBy Hbar S ⊆ MulAction.fixedBy Hbar (T n) := fun S hS => by
      filter_upwards [(k92el_jorg_tendsto S hlim).eventually (eventually_lt_nhds one_pos),
        (k92el_tr_tendsto hlim).eventually_ne two_ne_zero] with n hn htr
      have hd := h (T n) (hTΓ n) S (hsΓ hS)
      refine k92el_fix_pair_of_elem hd ?_ (hhyp S hS) htr
      by_contra hne
      have hJ := thm2_4_6 (Quotient.out (T n)) (Quotient.out S)
        (by rwa [(k92n_Tr_out (T n)).1, (k92n_Tr_out S).1]) (by rwa [(k92n_Tr_out (T n)).1, (k92n_Tr_out S).1])
      linarith
    -- so `Tₙ` fixes the three distinct points `a, b, c` and is the identity
    filter_upwards [key S₁ h₁, key S₂ h₂] with n hn₁ hn₂
    have hc₂ : (Sum.inr c : Hbar) ∈ MulAction.fixedBy Hbar S₂ := by
      rw [hfix₂]
      exact Or.inl rfl
    have hc₁ : (Sum.inr c : Hbar) ∉ MulAction.fixedBy Hbar S₁ := fun hc =>
      Set.disjoint_left.1 (hdisj h₁ h₂ h12) hc hc₂
    rw [hfix₁] at hn₁ hc₁
    have hab' : (Sum.inr a : Hbar) ≠ Sum.inr b := fun e => hab (Sum.inr_injective e)
    have hac : (Sum.inr a : Hbar) ≠ Sum.inr c := fun e => hc₁ (by rw [← e]; simp)
    have hbc : (Sum.inr b : Hbar) ≠ Sum.inr c := fun e => hc₁ (by rw [← e]; simp)
    exact k92el_eq_one_of_three hab' hac hbc (hn₁ (by simp)) (hn₁ (by simp)) (hn₂ hc₂)

end Katok1992
