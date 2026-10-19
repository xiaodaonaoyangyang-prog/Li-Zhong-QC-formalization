import LiZhongQC.Ch11.S36_Hamilton

/-! E1 independent source-only producer. No compiler run; no new global definitions. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- E1: enumerate the countable group and close finite prefixes together with its finite
ineffective kernel. No stage is asserted to act freely. -/
theorem s36e_fg_exhaustion (hΓ : IsFuchsian Γ) :
    ∃ H : ℕ → Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ),
      Monotone H ∧ (∀ i, H i ≤ Γ) ∧ (∀ i, (H i).FG) ∧
      (∀ γ ∈ Γ, ∃ i, γ ∈ H i) ∧
      (∀ i, Γ ⊓ Subgroup.zpowers (-1) ≤ H i) := by
  classical
  have : Countable Γ := (h36p_countable hΓ).to_subtype
  obtain ⟨e, he⟩ := exists_surjective_nat Γ
  let K : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    Γ ⊓ Subgroup.zpowers (-1)
  have hKfin : (K : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)).Finite := by
    letI : Finite ↥(Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)) :=
      finite_zpowers.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, by simp⟩)
    letI : Finite K := Finite.of_injective _
      (Subgroup.inclusion_injective
        (show K ≤ Subgroup.zpowers (-1) from inf_le_right))
    exact Set.toFinite _
  let A : ℕ → Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) := fun n =>
    (fun j : ℕ => (e j).val) '' {j | j ≤ n} ∪ K
  let H : ℕ → Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    fun n => Subgroup.closure (A n)
  have hAf : ∀ n, (A n).Finite := fun n =>
    ((Set.finite_le_nat n).image (fun j : ℕ => (e j).val)).union hKfin
  have hsub : ∀ n, H n ≤ Γ := by
    intro n
    apply (Subgroup.closure_le Γ).2
    intro γ hγ
    rcases hγ with hγ | hγ
    · obtain ⟨j, hj, rfl⟩ := hγ
      exact (e j).property
    · exact hγ.1
  have hmono : Monotone H := by
    intro i j hij
    apply Subgroup.closure_mono
    intro γ hγ
    rcases hγ with hγ | hγ
    · obtain ⟨k, hk, hkeq⟩ := hγ
      exact Or.inl ⟨k, hk.trans hij, hkeq⟩
    · exact Or.inr hγ
  refine ⟨H, hmono, hsub, ?_, ?_, ?_⟩
  · intro n
    exact (Subgroup.fg_iff (H n)).2 ⟨A n, rfl, hAf n⟩
  · intro γ hγ
    obtain ⟨j, hj⟩ := he ⟨γ, hγ⟩
    refine ⟨j, Subgroup.subset_closure ?_⟩
    exact Or.inl ⟨j, (by change j ≤ j; exact le_rfl), congrArg Subtype.val hj⟩
  · intro n γ hγ
    apply Subgroup.subset_closure
    exact Or.inr hγ

/-- Membership in a monotone exhaustive chain holds eventually at every ambient element. -/
theorem s36e_mem_eventually
    (H : ℕ → Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hmono : Monotone H) (hcover : ∀ γ ∈ Γ, ∃ i, γ ∈ H i)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) :
    ∀ᶠ i in atTop, γ ∈ H i := by
  obtain ⟨i, hi⟩ := hcover γ hγ
  exact Filter.eventually_atTop.2 ⟨i, fun j hij => hmono hij hi⟩

end LiZhongQC
