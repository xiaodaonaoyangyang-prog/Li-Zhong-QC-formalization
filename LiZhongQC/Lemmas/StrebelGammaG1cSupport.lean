import LiZhongQC.Ch11.S36_Hamilton
import LiZhongQC.Lemmas.SelbergLemma

/-! G1c support package 001. Source-pinned, uncompiled; installed imports only. -/

/- BEGIN StrebelGammaG1cBasic.lean -/
/-!
# G1c: independent subgroup restrictions (source-only candidate)

No new definitions, structures, instances or attributes. No compiler has been run.
These lemmas do not depend on G1b, a pending G1c interface, or the open book theorem.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

variable {Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Proper discontinuity restricts to every subgroup. -/
theorem s36c_fuchsian_subgroup (hΓ : IsFuchsian Γ) (hle : Δ ≤ Γ) :
    IsFuchsian Δ := by
  intro C hC
  exact (hΓ C hC).subset fun γ hγ => ⟨hle hγ.1, hγ.2⟩

/-- Restrict a compatible coefficient without changing any of its values. -/
theorem s36c_compatible_subgroup (hle : Δ ≤ Γ) {μ : ℂ → ℂ}
    (hμ : IsGammaCompatible Γ μ) : IsGammaCompatible Δ μ := by
  intro γ hγ
  exact hμ γ (hle hγ)

/-- The same BeltramiH element is a coefficient for the subgroup. -/
theorem s36c_beltrami_restrict (hle : Δ ≤ Γ) (μ : BeltramiGamma Γ) :
    ∃ μΔ : BeltramiGamma Δ, μΔ.1 = μ.1 := by
  exact ⟨⟨μ.1, s36c_compatible_subgroup hle μ.2⟩, rfl⟩

/-- Boundary equivalence survives restriction because the normalized maps are unchanged. -/
theorem s36c_teich_restrict (μ ν : BeltramiGamma Γ) (μΔ νΔ : BeltramiGamma Δ)
    (hμ : μΔ.1 = μ.1) (hν : νΔ.1 = ν.1) (hrel : teichSetoidGamma Γ ν μ) :
    teichSetoidGamma Δ νΔ μΔ := by
  intro x
  change fMuSym νΔ.1.1 x = fMuSym μΔ.1.1 x
  rw [hμ, hν]
  exact hrel x

/-- Restriction leaves exactly the frozen invFunOn expression, not merely an a.e. map. -/
theorem s36c_comparison_map_restrict (μ ν : BeltramiGamma Γ) (μΔ νΔ : BeltramiGamma Δ)
    (hμ : μΔ.1 = μ.1) (hν : νΔ.1 = ν.1) :
    (Function.invFunOn (fMuSym νΔ.1.1) upperHalf ∘ fMuSym μΔ.1.1) =
      (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) := by
  rw [hμ, hν]

/-- Automorphy restricts; finiteness on the new domain is a separate, explicit input. -/
theorem s36c_automorphic_restrict (hle : Δ ≤ Γ) {F E : Set ℂ} {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) (hE : phiArea φ E < ⊤) :
    φ ∈ integrableAutomorphicQD Δ E := by
  exact ⟨hφ.1, hE, fun γ hγ z hz => hφ.2.2 γ (hle hγ) z hz⟩

/-- A fixed-point element of a properly discontinuous group has finite order. -/
theorem s36c_fixed_has_finite_order (hΓ : IsFuchsian Γ)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ)
    (τ : UpperHalfPlane) (hfix : γ • τ = τ) : IsOfFinOrder γ := by
  have hfin := hΓ {τ} isCompact_singleton
  have hpow : ∀ n : ℕ, (γ ^ n) • τ = τ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, hfix, ih]
  apply finite_powers.mp
  refine hfin.subset ?_
  intro δ hδ
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff δ γ).mp hδ
  refine ⟨Γ.pow_mem hγ n, ?_⟩
  refine ⟨τ, ?_, Set.mem_singleton τ⟩
  exact ⟨τ, Set.mem_singleton τ, hpow n⟩

/-- The actual torsion-free Selberg subgroup satisfies the weaker central convention. -/
theorem s36c_free_of_no_torsion (hΓ : IsFuchsian Γ)
    (htor : ∀ γ ∈ Γ, IsOfFinOrder γ → γ = 1) : ActsFreely Γ := by
  intro γ hγ τ hfix
  exact Or.inl (htor γ hγ (s36c_fixed_has_finite_order hΓ hγ τ hfix))

/-- Cancel a nonzero finite covering degree in ENNReal, including an infinite right side. -/
theorem s36c_cancel_degree {d : ℕ} (hd : d ≠ 0) {a b : ℝ≥0∞}
    (h : (d : ℝ≥0∞) * a ≤ (d : ℝ≥0∞) * b) : a ≤ b := by
  exact (ENNReal.mul_le_mul_iff_right (by exact_mod_cast hd)
    (ENNReal.natCast_ne_top d)).mp h

end LiZhongQC
end -- original noncomputable section
/- END StrebelGammaG1cBasic.lean -/

/- BEGIN StrebelGammaG1cGroups.lean -/
/-! G1c group producers. Source-only candidate; no compiler has been run. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

variable {Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Saturate a genuine Selberg subgroup by the ineffective kernel already in Gamma.
The output ActsFreely allows ±I; it never asserts that Gamma itself is torsion-free. -/
theorem s36c_selberg_effective (hΓ : IsFuchsian Γ) (hfg : Γ.FG) :
    ∃ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ),
      Δ ≤ Γ ∧ Δ.relIndex Γ ≠ 0 ∧ Δ.FG ∧ IsFuchsian Δ ∧ ActsFreely Δ ∧
      Γ ⊓ Subgroup.zpowers (-1) ≤ Δ := by
  classical
  obtain ⟨H, hHΓ, hHi, hHfg, hHtor⟩ := sel_selberg hfg
  let C : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    Γ ⊓ Subgroup.zpowers (-1)
  have hCcent : C ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) ℝ) := by
    intro c hc
    apply Subgroup.mem_center_iff.mpr
    intro a
    rcases h36p_a_mem_zpowers hc.2 with h | h
    · simp [h]
    · simp [h]
  letI : C.Normal := Subgroup.normal_of_le_center hCcent
  let L : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ) := H ⊔ C
  have hHL : H ≤ L := le_sup_left
  have hLΓ : L ≤ Γ := sup_le hHΓ inf_le_left
  have hLi : L.relIndex Γ ≠ 0 :=
    ne_zero_of_dvd_ne_zero hHi (Subgroup.relIndex_dvd_of_le_left Γ hHL)
  have hLH : IsFuchsian L := s36c_fuchsian_subgroup hΓ hLΓ
  have hfree : ActsFreely L := by
    intro γ hγ τ hfix
    obtain ⟨a, ha, c, hc, hac⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := H) (t := C)).mp hγ
    rcases h36p_a_mem_zpowers hc.2 with hc1 | hcm
    · have hγa : γ = a := by simpa [hc1] using hac.symm
      have hfixa : a • τ = τ := hγa ▸ hfix
      have ha1 : a = 1 := hHtor a ha
        (s36c_fixed_has_finite_order hΓ (hHΓ ha) τ hfixa)
      exact Or.inl (hγa.trans ha1)
    · have hγa : γ = -a := by simpa [hcm] using hac.symm
      have hfixa : a • τ = τ := by
        apply UpperHalfPlane.ext
        rw [← h36p_m_coe a τ, ← h36p_a_m_neg a]
        rw [h36p_m_coe (-a) τ, ← hγa, hfix]
      have ha1 : a = 1 := hHtor a ha
        (s36c_fixed_has_finite_order hΓ (hHΓ ha) τ hfixa)
      exact Or.inr (hγa.trans (congrArg Neg.neg ha1))
  exact ⟨L, hLΓ, hLi, sel_fg_of_relIndex hfg hLΓ hLi, hLH, hfree, le_sup_right⟩

/-- Enumerate right cosets of the actual finite-index subgroup. No normality is assumed. -/
theorem s36c_right_representatives (hle : Δ ≤ Γ) (hi : Δ.relIndex Γ ≠ 0) :
    ∃ (d : ℕ) (T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℝ),
      d = Δ.relIndex Γ ∧ d ≠ 0 ∧ (∀ i, T i ∈ Γ) ∧
      ∀ γ ∈ Γ, ∃! i : Fin d, ∃ δ ∈ Δ, γ = δ * T i := by
  classical
  let K : Subgroup Γ := Δ.subgroupOf Γ
  letI : K.FiniteIndex := ⟨hi⟩
  letI : Fintype (Γ ⧸ K) := Fintype.ofFinite (Γ ⧸ K)
  let d : ℕ := Fintype.card (Γ ⧸ K)
  let e : Fin d ≃ (Γ ⧸ K) := (Fintype.equivFin (Γ ⧸ K)).symm
  let T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    fun i => (((e i).out : Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹
  have hd : d = Δ.relIndex Γ := by
    change Fintype.card (Γ ⧸ K) = Nat.card (Γ ⧸ K)
    exact Nat.card_eq_fintype_card.symm
  have hT : ∀ i, T i ∈ Γ := fun i => Γ.inv_mem (e i).out.property
  have hsep : ∀ i j : Fin d, T i * (T j)⁻¹ ∈ Δ → i = j := by
    intro i j hij
    have hmem : (e i).out⁻¹ * (e j).out ∈ K := by
      change (((e i).out : Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ *
        (((e j).out : Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ Δ
      simpa only [T, inv_inv] using hij
    have heq : (QuotientGroup.mk (e i).out : Γ ⧸ K) = QuotientGroup.mk (e j).out :=
      QuotientGroup.eq.mpr hmem
    apply e.injective
    simpa only [Quotient.out_eq'] using heq
  refine ⟨d, T, hd, hd.symm ▸ hi, hT, ?_⟩
  intro γ hγ
  let a : Γ := ⟨γ, hγ⟩
  let q : Γ ⧸ K := QuotientGroup.mk a⁻¹
  let i : Fin d := e.symm q
  have heiq : e i = q := e.apply_symm_apply q
  have hq : (QuotientGroup.mk (e i).out : Γ ⧸ K) = QuotientGroup.mk a⁻¹ := by
    exact (show (QuotientGroup.mk (e i).out : Γ ⧸ K) = e i from
      Quotient.out_eq' (e i)).trans heiq
  have hmem : (e i).out⁻¹ * a⁻¹ ∈ K := QuotientGroup.eq.mp hq
  have hδ : γ * (T i)⁻¹ ∈ Δ := by
    have hh := K.inv_mem hmem
    change ((((e i).out : Γ)⁻¹ * a⁻¹)⁻¹ : Γ).val ∈ Δ at hh
    simpa only [mul_inv_rev, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, a, T] using hh
  refine ⟨i, ⟨γ * (T i)⁻¹, hδ, by group⟩, ?_⟩
  intro j hj
  obtain ⟨δ, hδΔ, hγδ⟩ := hj
  apply hsep j i
  have heq : T j * (T i)⁻¹ = δ⁻¹ * (γ * (T i)⁻¹) := by
    rw [hγδ]
    group
  rw [heq]
  exact Δ.mul_mem (Δ.inv_mem hδΔ) hδ

end LiZhongQC
end -- original noncomputable section
/- END StrebelGammaG1cGroups.lean -/
