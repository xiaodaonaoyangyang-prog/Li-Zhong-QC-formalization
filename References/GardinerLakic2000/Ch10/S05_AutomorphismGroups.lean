import References.GardinerLakic2000.Ch10.S04_DiscretenessOfOrbits

/-!
# Gardiner–Lakic 2000, Ch. 10 §10.5 Automorphism groups

Source `teichmuller.txt`, lines 8219–8272 (Chapter 10, §10.5).

* Lemma 3 (l. 8224) — `lemma10_3`
* Theorem 5 (l. 8227) — `thm10_5`

Not items: "the isotropy group of `τ` is isomorphic to `N(Γ^τ)/Γ^τ`" (l. 8220, the proof outline); the Remark
(l. 8229); the area formula, (10.11) (Gauss–Bonnet) and the Hurwitz bound (10.12) (l. 8241–8269, a remark after the
proof, not cited). Modelling: `N(Γ)` is the normalizer of `Γ` in SL(2,ℝ); "`Γ` is not cyclic" is read modulo `±1` (no
`g` with every element of `Γ` equal to `±gⁿ`); near miss `Katok1992.thm2_3_8` (non-abelian, PSL(2,ℝ)). "`N(Γ)/Γ` is
finite" is "`Γ` has finite index in `N(Γ)`".
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (IsFuchsian fuchsianLimitSet)

/-- Helper (§10.5). The center of `SL(2,ℝ)` is `{±1}`. -/
theorem gl105_center {z : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hz : z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : z = 1 ∨ z = -1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  have hr2 : r * r = 1 := by
    rw [← sq]
    simpa using hr
  rcases mul_self_eq_one_iff.1 hr2 with h | h
  · left
    ext i j
    rw [← hrz, h]
    fin_cases i <;> fin_cases j <;> simp
  · right
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_neg, ← hrz, h]
    fin_cases i <;> fin_cases j <;> simp

/-- Helper (§10.5). Two elements of `SL(2,ℝ)` with the same image in `PSL(2,ℝ)` agree up to sign. -/
theorem gl105_mk_eq {a b : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h : (a : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℝ) = b) : b = a ∨ b = -a := by
  rcases gl105_center (QuotientGroup.eq.1 h) with h1 | h1
  · left
    calc b = a * (a⁻¹ * b) := by group
      _ = a := by rw [h1, mul_one]
  · right
    calc b = a * (a⁻¹ * b) := by group
      _ = -a := by rw [h1, mul_neg, mul_one]

/-- Helper (§10.5). The image in `PSL(2,ℝ)` of a Fuchsian subgroup of `SL(2,ℝ)` (properly discontinuous on `ℍ`) is
discrete in Katok's sense: the finitely many elements moving `i` by at most `1` bound `ρ(S i, i) + ρ(S(2i), 2i)` away
from `0` (`Katok1992.k92e_discrete_of_sep`). -/
theorem gl105_image_fuchsian {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) :
    Katok1992.IsFuchsian
      (Γ.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) ℝ)))) := by
  set s₂ : UpperHalfPlane := UpperHalfPlane.mk ⟨0, 2⟩ two_pos
  have hne : UpperHalfPlane.I ≠ s₂ := fun h => by
    have := congrArg UpperHalfPlane.im h
    norm_num [s₂] at this
  set C : Set UpperHalfPlane := Metric.closedBall UpperHalfPlane.I 1
  have hS := hΓ C (isCompact_closedBall _ _)
  have hfin : {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ | (γ ∈ Γ ∧ ((fun x => γ • x) '' C ∩ C).Nonempty) ∧
      (γ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℝ) ≠ 1}.Finite := hS.subset fun γ hγ => by exact hγ.1
  set f : Matrix.SpecialLinearGroup (Fin 2) ℝ → ℝ :=
    fun γ => dist (γ • UpperHalfPlane.I) UpperHalfPlane.I + dist (γ • s₂) s₂
  obtain ⟨δ, hδ, hδle⟩ := Katok1992.k92e_finite_pos hfin f fun γ hγ => by
    -- a non-identity element moves `i` or `2i`
    by_contra hle
    push Not at hle
    have h1 : dist (γ • UpperHalfPlane.I) UpperHalfPlane.I = 0 :=
      le_antisymm (by linarith [dist_nonneg (x := γ • s₂) (y := s₂)]) dist_nonneg
    have h2 : dist (γ • s₂) s₂ = 0 :=
      le_antisymm (by linarith [dist_nonneg (x := γ • UpperHalfPlane.I) (y := UpperHalfPlane.I)]) dist_nonneg
    refine hγ.2 (Katok1992.k92e_eq_one_of_two_fixed hne ?_ ?_)
    · rw [Katok1992.k92_psl_smul_mk]
      exact dist_eq_zero.1 h1
    · rw [Katok1992.k92_psl_smul_mk]
      exact dist_eq_zero.1 h2
  refine Katok1992.k92e_discrete_of_sep UpperHalfPlane.I s₂ (lt_min hδ one_pos) fun T hT hT1 => ?_
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hT
  rw [QuotientGroup.mk'_apply] at hT1 ⊢
  rw [Katok1992.k92_psl_smul_mk, Katok1992.k92_psl_smul_mk]
  by_cases hfar : dist (γ • UpperHalfPlane.I) UpperHalfPlane.I ≤ 1
  · have hmem : ((fun x => γ • x) '' C ∩ C).Nonempty :=
      ⟨γ • UpperHalfPlane.I, ⟨UpperHalfPlane.I, mem_closedBall_self zero_le_one, rfl⟩, mem_closedBall.2 hfar⟩
    exact (min_le_left _ _).trans (hδle γ ⟨⟨hγ, hmem⟩, hT1⟩)
  · push Not at hfar
    exact (min_le_right _ _).trans (hfar.le.trans (le_add_of_nonneg_right dist_nonneg))

/-- **Lemma 3** (§10.5, l. 8224). If a Fuchsian group `Γ` is not cyclic, its normalizer `N(Γ)` is also Fuchsian. -/
theorem lemma10_3 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hnc : ¬ ∃ g : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ γ ∈ Γ, ∃ k : ℤ, γ = g ^ k ∨ γ = -(g ^ k)) :
    IsFuchsian (Subgroup.normalizer (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ))) := by
  set q := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) ℝ)) with hq
  set Γ' := Γ.map q
  have hΓ' : Katok1992.IsFuchsian Γ' := gl105_image_fuchsian hΓ
  -- `Γ'` is not abelian: otherwise it is cyclic (Katok Theorem 2.3.6), and then `Γ = ±⟨g⟩`
  have hna : ¬ ∀ a ∈ Γ', ∀ b ∈ Γ', a * b = b * a := by
    intro hab
    obtain ⟨⟨g, hg⟩⟩ := Katok1992.thm2_3_6 hΓ' hab
    obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℝ)
    refine hnc ⟨g₀, fun γ hγ => ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨q γ, Subgroup.mem_map_of_mem q hγ⟩)
    have e : ((g₀ ^ k : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℝ) =
        γ := by
      rw [QuotientGroup.mk_zpow, hg₀]
      exact congrArg Subtype.val hk
    exact ⟨k, gl105_mk_eq e⟩
  -- Katok Theorem 2.3.8: the normalizer of `Γ'` is Fuchsian
  have hN := Katok1992.thm2_3_8 hΓ' hna
  -- `q` maps `N(Γ)` into `N(Γ')`
  have hqN : ∀ n ∈ Subgroup.normalizer (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)),
      q n ∈ Subgroup.normalizer (Γ' : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℝ)) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro h
    obtain ⟨h₀, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) ℝ)) h
    constructor
    · rintro ⟨γ, hγ, hγh⟩
      refine ⟨n * γ * n⁻¹, (hn γ).1 hγ, ?_⟩
      rw [map_mul, map_mul, map_inv, hγh]
    · rintro ⟨γ', hγ', he⟩
      refine ⟨n⁻¹ * γ' * n, ?_, ?_⟩
      · have := (hn (n⁻¹ * γ' * n)).2
        apply this
        simpa [mul_assoc] using hγ'
      · rw [map_mul, map_mul, map_inv, he]
        group
  -- properly discontinuous: compact `C ⊆ B̄(i, r)`; `n C ∩ C ≠ ∅` forces `ρ(n i, i) ≤ 2r`, and only finitely many
  -- elements of `N(Γ')` do that; the fibres of `q` are `{±a}`
  intro C hC
  obtain ⟨r, hr⟩ := hC.isBounded.subset_closedBall UpperHalfPlane.I
  have hfin2 := (Katok1992.k92e_finite_of_compact hN (Katok1992.k92e_compact_preimage UpperHalfPlane.I
    (isCompact_closedBall UpperHalfPlane.I (2 * r)))).image Subtype.val
  refine (hfin2.preimage' (f := q) fun T _ => ?_).subset ?_
  · obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) ℝ)) T
    refine (Set.toFinite ({a, -a} : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ))).subset fun b hb => ?_
    rcases gl105_mk_eq hb.symm with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro n ⟨hn, c, ⟨c', hc', hcc'⟩, hc⟩
    refine ⟨⟨q n, hqN n hn⟩, ?_, rfl⟩
    have hcc : n • c' = c := hcc'
    have h1 : dist (n • c') UpperHalfPlane.I ≤ r := by rw [hcc]; exact mem_closedBall.1 (hr hc)
    have h2 : dist c' UpperHalfPlane.I ≤ r := mem_closedBall.1 (hr hc')
    have key : n • UpperHalfPlane.I ∈ closedBall UpperHalfPlane.I (2 * r) := by
      rw [mem_closedBall]
      calc dist (n • UpperHalfPlane.I) UpperHalfPlane.I ≤ dist (n • UpperHalfPlane.I) (n • c') +
            dist (n • c') UpperHalfPlane.I := dist_triangle _ _ _
        _ = dist UpperHalfPlane.I c' + dist (n • c') UpperHalfPlane.I := by rw [dist_smul]
        _ ≤ r + r := by rw [dist_comm] at h2; linarith
        _ = 2 * r := by ring
    rw [← Katok1992.k92_psl_smul_mk] at key
    exact key

/-- **Theorem 5** (§10.5, l. 8227). If `Γ` is a finitely generated Fuchsian group whose limit set has more than two
points, then `N(Γ)/Γ` is finite. -/
theorem thm10_5 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfg : Group.FG Γ)
    (hΛ : 2 < (fuchsianLimitSet Γ).encard) :
    (Γ.subgroupOf (Subgroup.normalizer (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)))).FiniteIndex := by
  sorry

end GardinerLakic2000
