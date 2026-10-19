import LiZhongQC.Lemmas.FoundationQuotient

/- Source: F1BMinimalCycles.lean -/
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

/-- Approved F1 B3 contract, including fixed points and the zero-vertex case.
Source-only proof; no compiler has been started. -/
theorem ft1gb_minimal_cycles (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ∃ (N : ℕ) (r : Fin N → Fin n) (ell : Fin N → ℕ),
      (∀ j, 0 < ell j ∧ (σ ^ ell j) (r j) = r j ∧
        ∀ k : ℕ, 0 < k → k < ell j → (σ ^ k) (r j) ≠ r j) ∧
      ∀ i : Fin n, ∃! p : Σ j : Fin N, Fin (ell j),
        i = (σ ^ (p.2 : ℕ)) (r p.1) := by
  classical
  let s : Setoid (Fin n) := Equiv.Perm.SameCycle.setoid σ
  let Q : Type := Quotient s
  let prj : Fin n → Q := Quotient.mk s
  letI : Fintype Q := Fintype.ofFinite Q
  let e : Fin (Fintype.card Q) ≃ Q := (Fintype.equivFin Q).symm
  let r : Fin (Fintype.card Q) → Fin n := fun j => (e j).out
  let ell : Fin (Fintype.card Q) → ℕ := fun j =>
    Function.minimalPeriod (σ : Fin n → Fin n) (r j)
  have hr : ∀ j, prj (r j) = e j := fun j => Quotient.out_eq (e j)
  have hper : ∀ x : Fin n, Function.IsPeriodicPt (σ : Fin n → Fin n) (orderOf σ) x := by
    intro x
    change ((σ : Fin n → Fin n)^[orderOf σ]) x = x
    rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
    rfl
  have hpos : ∀ j, 0 < ell j := fun j =>
    (hper (r j)).minimalPeriod_pos (orderOf_pos σ)
  have hpi : ∀ (x : Fin n) (k : ℕ), prj ((σ ^ k) x) = prj x := by
    intro x k
    apply Quotient.sound
    exact Equiv.Perm.sameCycle_pow_left.2 (Equiv.Perm.SameCycle.refl σ x)
  refine ⟨Fintype.card Q, r, ell, ?_, ?_⟩
  · intro j
    refine ⟨hpos j, ?_, ?_⟩
    · have hp : ((σ : Fin n → Fin n)^[ell j]) (r j) = r j :=
        Function.isPeriodicPt_minimalPeriod (σ : Fin n → Fin n) (r j)
      simpa only [Equiv.Perm.coe_pow] using hp
    · intro k hk hkell heq
      have hp : Function.IsPeriodicPt (σ : Fin n → Fin n) k (r j) := by
        simp only [Equiv.Perm.coe_pow] at heq
        exact heq
      exact (not_le_of_gt hkell) (hp.minimalPeriod_le hk)
  · intro x
    let j : Fin (Fintype.card Q) := e.symm (prj x)
    have hj : prj (r j) = prj x := (hr j).trans (e.apply_symm_apply (prj x))
    have hsame : σ.SameCycle (r j) x := Quotient.exact hj
    obtain ⟨k, hk⟩ := hsame.exists_nat_pow_eq
    have hmod : (σ ^ (k % ell j)) (r j) = x := by
      simp only [Equiv.Perm.coe_pow]
      change ((σ : Fin n → Fin n)^[k % ell j]) (r j) = x
      rw [Function.iterate_mod_minimalPeriod_eq]
      simpa only [Equiv.Perm.coe_pow] using hk
    refine ⟨⟨j, ⟨k % ell j, Nat.mod_lt _ (hpos j)⟩⟩, hmod.symm, ?_⟩
    intro p hp
    rcases p with ⟨j', k'⟩
    have hj' : j' = j := by
      apply e.injective
      calc
        e j' = prj (r j') := (hr j').symm
        _ = prj ((σ ^ (k' : ℕ)) (r j')) := (hpi _ _).symm
        _ = prj x := congrArg prj hp.symm
        _ = e j := (e.apply_symm_apply (prj x)).symm
    subst j'
    have hk' : k' = (⟨k % ell j, Nat.mod_lt _ (hpos j)⟩ : Fin (ell j)) := by
      apply Fin.ext
      apply Function.iterate_injOn_Iio_minimalPeriod (f := (σ : Fin n → Fin n)) (x := r j)
        k'.isLt (Nat.mod_lt _ (hpos j))
      simpa only [Equiv.Perm.coe_pow] using hp.symm.trans hmod.symm
    cases hk'
    rfl

end LiZhongQC
end -- source noncomputable section

/- Source: F1BBoundedInvariant.lean -/
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Approved F1 B5. Compact extrema after triangular conjugation eliminate a noncentral
element with a bounded invariant set. Source-only, not compiled. -/
theorem ft1gb_bounded_invariant_trivial (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {U : Set UpperHalfPlane} (hUn : U.Nonempty) (hUb : Bornology.IsBounded U)
    (hUi : ∀ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' U = U) :
    ∀ γ ∈ Γ, γ = 1 ∨ γ = -1 := by
  -- The compact-extrema argument below is valid without discreteness.
  -- The approved Fuchsian hypothesis is retained unchanged.
  have _hΓ := hΓ
  intro γ hγ
  by_cases hell : |γ 0 0 + γ 1 1| < 2
  · obtain ⟨τ, hτ⟩ := s27g_elliptic_fixed hell
    exact hfree γ hγ τ hτ
  obtain ⟨A, hA⟩ := s30l_exists_fix_infty (le_of_not_gt hell)
  let δ : Matrix.SpecialLinearGroup (Fin 2) ℝ := A * γ * A⁻¹
  have hδ10 : δ 1 0 = 0 := hA
  have hdet : δ 0 0 * δ 1 1 = 1 := by
    have hd := hnf_sl2_det δ
    simpa only [hδ10, mul_zero, sub_zero] using hd
  have hd0 : δ 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  have hdetC : (δ 0 0 : ℂ) * (δ 1 1 : ℂ) = 1 := by exact_mod_cast hdet
  have haff : ∀ τ : UpperHalfPlane, ((δ • τ : UpperHalfPlane) : ℂ) =
      (δ 0 0 : ℂ) ^ 2 * (τ : ℂ) + ((δ 0 0 * δ 0 1 : ℝ) : ℂ) := by
    intro τ
    rw [h36t_coe_smul, hδ10]
    simp only [Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_mul]
    apply (div_eq_iff (show (δ 1 1 : ℂ) ≠ 0 by exact_mod_cast hd0)).2
    calc
      (δ 0 0 : ℂ) * (τ : ℂ) + δ 0 1 =
          ((δ 0 0 : ℂ) * (τ : ℂ) + δ 0 1) * 1 := (mul_one _).symm
      _ = ((δ 0 0 : ℂ) * (τ : ℂ) + δ 0 1) * ((δ 0 0 : ℂ) * δ 1 1) := by rw [hdetC]
      _ = ((δ 0 0 : ℂ) ^ 2 * (τ : ℂ) + (δ 0 0 : ℂ) * δ 0 1) * δ 1 1 := by ring
  have him : ∀ τ : UpperHalfPlane, (δ • τ).im = (δ 0 0) ^ 2 * τ.im := by
    intro τ
    have hh := congrArg Complex.im (haff τ)
    rw [show (δ 0 0 : ℂ) ^ 2 = ((δ 0 0 ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.add_im,
      Complex.im_ofReal_mul, Complex.ofReal_im, add_zero] at hh
    exact hh
  have hre : ∀ τ : UpperHalfPlane, (δ • τ).re =
      (δ 0 0) ^ 2 * τ.re + δ 0 0 * δ 0 1 := by
    intro τ
    have hh := congrArg Complex.re (haff τ)
    rw [show (δ 0 0 : ℂ) ^ 2 = ((δ 0 0 ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.add_re,
      Complex.re_ofReal_mul, Complex.ofReal_re] at hh
    exact hh
  have hK : IsCompact (closure U) := hUb.isCompact_closure
  have hKn : (closure U).Nonempty := hUn.mono subset_closure
  have hγK : (fun τ : UpperHalfPlane => γ • τ) '' closure U = closure U := by
    have h1 : (fun τ : UpperHalfPlane => γ • τ) '' closure U =
        closure ((fun τ : UpperHalfPlane => γ • τ) '' U) :=
      (Homeomorph.smul γ : UpperHalfPlane ≃ₜ UpperHalfPlane).image_closure U
    rw [h1, hUi γ hγ]
  let V : Set UpperHalfPlane := (fun τ : UpperHalfPlane => A • τ) '' closure U
  have hV : IsCompact V := hK.image (continuous_const_smul A)
  have hVn : V.Nonempty := hKn.image _
  have hδV : (fun τ : UpperHalfPlane => δ • τ) '' V = V := by
    change (fun τ : UpperHalfPlane => δ • τ) ''
      ((fun τ : UpperHalfPlane => A • τ) '' closure U) =
        (fun τ : UpperHalfPlane => A • τ) '' closure U
    rw [← Set.image_comp]
    have he : (fun τ : UpperHalfPlane => δ • (A • τ)) =
        (fun τ : UpperHalfPlane => A • (γ • τ)) := by
      funext τ
      simp only [δ, mul_smul, inv_smul_smul]
    change (fun τ : UpperHalfPlane => δ • (A • τ)) '' closure U = _
    rw [he, show (fun τ : UpperHalfPlane => A • (γ • τ)) =
      (fun τ : UpperHalfPlane => A • τ) ∘ (fun τ : UpperHalfPlane => γ • τ) from rfl, Set.image_comp, hγK]
  have hmaps : ∀ τ ∈ V, δ • τ ∈ V := fun τ hτ =>
    hδV ▸ mem_image_of_mem (fun x : UpperHalfPlane => δ • x) hτ
  obtain ⟨p, hp, hpmax⟩ := hV.exists_isMaxOn hVn UpperHalfPlane.continuous_im.continuousOn
  obtain ⟨q, hq, hqmin⟩ := hV.exists_isMinOn hVn UpperHalfPlane.continuous_im.continuousOn
  have hle : (δ 0 0) ^ 2 * p.im ≤ p.im := by
    have h := hpmax (hmaps p hp)
    rw [Set.mem_setOf_eq, him] at h
    exact h
  have hge : q.im ≤ (δ 0 0) ^ 2 * q.im := by
    have h := hqmin (hmaps q hq)
    rw [Set.mem_setOf_eq, him] at h
    exact h
  have hscale : (δ 0 0) ^ 2 = 1 := by
    have hp0 : 0 < p.im := p.im_pos
    have hq0 : 0 < q.im := q.im_pos
    nlinarith
  obtain ⟨p', hp', hpmax'⟩ := hV.exists_isMaxOn hVn UpperHalfPlane.continuous_re.continuousOn
  obtain ⟨q', hq', hqmin'⟩ := hV.exists_isMinOn hVn UpperHalfPlane.continuous_re.continuousOn
  have hle' : p'.re + δ 0 0 * δ 0 1 ≤ p'.re := by
    have h := hpmax' (hmaps p' hp')
    rw [Set.mem_setOf_eq, hre, hscale, one_mul] at h
    exact h
  have hge' : q'.re ≤ q'.re + δ 0 0 * δ 0 1 := by
    have h := hqmin' (hmaps q' hq')
    rw [Set.mem_setOf_eq, hre, hscale, one_mul] at h
    exact h
  have hshift : δ 0 0 * δ 0 1 = 0 := by linarith
  have hfix : δ • UpperHalfPlane.I = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    rw [haff]
    have hscaleC : (δ 0 0 : ℂ) ^ 2 = 1 := by exact_mod_cast hscale
    rw [hscaleC, hshift, Complex.ofReal_zero, one_mul, add_zero]
  apply hfree γ hγ (A⁻¹ • UpperHalfPlane.I)
  have hh := congrArg (fun τ : UpperHalfPlane => A⁻¹ • τ) hfix
  simpa only [δ, mul_smul, inv_smul_smul] using hh

end LiZhongQC
end -- source noncomputable section

/- Source: F1BExteriorStabilizers.lean -/
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Approved F1 B7 contract; source-only proof, not yet compiled. -/
theorem ft1gb_exterior_stabilizers {U : Set UpperHalfPlane}
    (hUi : ∀ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' U = U)
    (N : ℕ) (W : Fin N → Set UpperHalfPlane) (ρ : Fin N → ℝ → UpperHalfPlane)
    (h : Fin N → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hW : ∀ j, IsOpen (W j) ∧ IsConnected (W j) ∧ Disjoint U (W j) ∧
      frontier (W j) = Set.range (ρ j) ∧
      (∀ x ∈ W j, connectedComponentIn Uᶜ x = W j) ∧
      ∀ V : Set UpperHalfPlane, IsOpen V → IsConnected V → Disjoint U V →
        frontier V = Set.range (ρ j) → V = W j)
    (hperiod : ∀ j, h j ∈ Γ ∧ ∀ t : ℝ, ρ j (t + 1) = h j • ρ j t)
    (hprimitive : ∀ i j γ, γ ∈ Γ →
      (((fun τ : UpperHalfPlane => γ • τ) '' Set.range (ρ i)) ∩ Set.range (ρ j)).Nonempty →
      i = j ∧ ∃ k : ℤ, γ = h i ^ k ∨ γ = -h i ^ k) :
    (∀ j, (fun τ : UpperHalfPlane => h j • τ) '' W j = W j) ∧
    ∀ i j γ, γ ∈ Γ →
      (((fun τ : UpperHalfPlane => γ • τ) '' W i) ∩ W j).Nonempty →
      i = j ∧ ∃ k : ℤ, γ = h i ^ k ∨ γ = -h i ^ k := by
  have hsub : ∀ j, W j ⊆ Uᶜ := by
    intro j x hx hxU
    exact Set.disjoint_left.1 (hW j).2.2.1 hxU hx
  have hcomp : ∀ γ ∈ Γ,
      (Homeomorph.smul γ : UpperHalfPlane ≃ₜ UpperHalfPlane) '' Uᶜ = Uᶜ := by
    intro γ hγ
    rw [Homeomorph.image_compl]
    change ((fun τ : UpperHalfPlane => γ • τ) '' U)ᶜ = Uᶜ
    rw [hUi γ hγ]
  have himg_disj : ∀ γ ∈ Γ, ∀ j,
      Disjoint U ((fun τ : UpperHalfPlane => γ • τ) '' W j) := by
    intro γ hγ j
    apply Set.disjoint_left.2
    intro x hxU hxW
    obtain ⟨y, hyW, rfl⟩ := hxW
    have hyU : y ∈ U := by
      have hy := mem_image_of_mem (fun τ : UpperHalfPlane => γ⁻¹ • τ) hxU
      rw [hUi γ⁻¹ (Γ.inv_mem hγ)] at hy
      simpa only [inv_smul_smul] using hy
    exact Set.disjoint_left.1 (hW j).2.2.1 hyU hyW
  have hcc : ∀ γ ∈ Γ, ∀ j, ∀ x ∈ W j,
      connectedComponentIn Uᶜ (γ • x) =
        (fun τ : UpperHalfPlane => γ • τ) '' W j := by
    intro γ hγ j x hx
    have he := (Homeomorph.smul γ : UpperHalfPlane ≃ₜ UpperHalfPlane).image_connectedComponentIn
      (hsub j hx)
    rw [(hW j).2.2.2.2.1 x hx, hcomp γ hγ] at he
    exact he.symm
  constructor
  · intro j
    let e : UpperHalfPlane ≃ₜ UpperHalfPlane := Homeomorph.smul (h j)
    have hline : e '' Set.range (ρ j) = Set.range (ρ j) := by
      ext x
      constructor
      · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
        exact ⟨t + 1, (hperiod j).2 t⟩
      · rintro ⟨t, rfl⟩
        refine ⟨ρ j (t - 1), ⟨t - 1, rfl⟩, ?_⟩
        have hp := (hperiod j).2 (t - 1)
        rw [sub_add_cancel] at hp
        exact hp.symm
    have hfr : frontier (e '' W j) = Set.range (ρ j) := by
      rw [← e.image_frontier, (hW j).2.2.2.1, hline]
    exact (hW j).2.2.2.2.2 (e '' W j)
      (e.isOpenMap _ (hW j).1) (e.isConnected_image.2 (hW j).2.1)
      (himg_disj (h j) (hperiod j).1 j) hfr
  · intro i j γ hγ hint
    obtain ⟨x, hxi, hxj⟩ := hint
    obtain ⟨y, hy, rfl⟩ := hxi
    have heq : (fun τ : UpperHalfPlane => γ • τ) '' W i = W j :=
      (hcc γ hγ i y hy).symm.trans ((hW j).2.2.2.2.1 _ hxj)
    let e : UpperHalfPlane ≃ₜ UpperHalfPlane := Homeomorph.smul γ
    have hfr : e '' Set.range (ρ i) = Set.range (ρ j) := by
      rw [← (hW i).2.2.2.1, e.image_frontier]
      change frontier ((fun τ : UpperHalfPlane => γ • τ) '' W i) = _
      rw [heq, (hW j).2.2.2.1]
    apply hprimitive i j γ hγ
    refine ⟨ρ j 0, ?_, mem_range_self 0⟩
    change ρ j 0 ∈ e '' Set.range (ρ i)
    rw [hfr]
    exact mem_range_self 0

end LiZhongQC
end -- source noncomputable section
