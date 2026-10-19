import LiZhongQC.Lemmas.F1CuspFamilySupport

/-! D1 G1 producer: the compact doubled period strip for a cyclic parabolic group.
In the cusp coordinate A the powers of π₀ act on the whole sphere as integer
translations; the limit set is the single cusp point A ∞. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- G1. Explicit compact period strip for a cyclic parabolic group, doubled
across the real boundary. Infinity in this coordinate is a limit point. The two
high half-strips produce upper and lower cusp ends. -/
theorem s36d1_parabolic_core (hΓ : IsFuchsian Γ)
    (A π₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hπ : π₀ ∈ Γ)
    (htrans : ∀ τ : UpperHalfPlane, π₀ • (A • τ) = A • ((1 : ℝ) +ᵥ τ))
    (hcyc : ∀ γ ∈ Γ, ∃ t : ℤ, γ = π₀ ^ t ∨ γ = -π₀ ^ t) :
    ∃ L : Set ExtPlane, IsCompact L ∧ L ⊆ (fuchsianLimitSet Γ)ᶜ ∧
      (∀ p : ExtPlane, p ∉ fuchsianLimitSet Γ → ∃ γ ∈ Γ,
      mobiusSL (slRealToComplex γ) p ∈ L ∨
      ∃ τ : UpperHalfPlane, 2 < τ.im ∧
        (mobiusSL (slRealToComplex γ) p = (((A • τ : UpperHalfPlane) : ℂ) : ExtPlane) ∨
         mobiusSL (slRealToComplex γ) p = ((conj ((A • τ : UpperHalfPlane) : ℂ) : ℂ) : ExtPlane))) := by
  classical
  -- The limit set is at most the cusp point A ∞, and A ∞ is a genuine limit point.
  have hlim : fuchsianLimitSet Γ ⊆ {mobiusSL (slRealToComplex A) extInf} := by
    refine (h36q_limitSet_subset_closure_fix hΓ).trans ?_
    rw [← closure_singleton (x := mobiusSL (slRealToComplex A) extInf)]
    refine closure_mono ?_
    rintro y ⟨-, γ, hγ, h1, h2, hfix⟩
    obtain ⟨k, hk⟩ := hcyc γ hγ
    have hk0 : k ≠ 0 := by
      rintro rfl
      rcases hk with h | h
      · exact h1 (by simpa using h)
      · exact h2 (by simpa using h)
    exact ft1e_fix_unique htrans hk0 hk hfix
  have hξ : mobiusSL (slRealToComplex A) extInf ∈ fuchsianLimitSet Γ :=
    ft1fas_parabolic_endpoint_limit hΓ A π₀ hπ htrans
  -- Real Möbius denominators vanish only at real points.
  have hden : ∀ q : ℂ, q.im ≠ 0 → (A 1 0 : ℂ) * q + A 1 1 ≠ 0 := by
    intro q hq h0
    have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe A
      rwa [Matrix.det_fin_two] at h
    have h1 : A 1 0 * q.im = 0 := by
      have h := congrArg Complex.im h0
      simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, zero_im] at h
      exact h
    have h2 : A 1 0 * q.re + A 1 1 = 0 := by
      have h := congrArg Complex.re h0
      simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, zero_re] at h
      exact h
    have hc : A 1 0 = 0 := (mul_eq_zero.1 h1).resolve_right hq
    rw [hc, zero_mul, zero_add] at h2
    rw [hc, h2, mul_zero, mul_zero, sub_zero] at hdet
    exact zero_ne_one hdet
  -- In the coordinate A, the powers of π₀ act on the whole plane by integer translation.
  have hshift : ∀ (k : ℤ) (q : ℂ), mobiusSL (slRealToComplex (π₀ ^ k))
      (mobiusSL (slRealToComplex A) (q : ExtPlane)) =
      mobiusSL (slRealToComplex A) ((q + (k : ℂ) : ℂ) : ExtPlane) := by
    intro k q
    obtain ⟨δ, hδ⟩ : ∃ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ, δ = A⁻¹ * π₀ ^ k * A := ⟨_, rfl⟩
    have hδτ : ∀ τ : UpperHalfPlane, δ • τ = (k : ℝ) +ᵥ τ := by
      intro τ
      rw [hδ, mul_smul, mul_smul, ft1e_zpow_smul htrans k τ, inv_smul_smul]
    obtain ⟨h10, h11, h01⟩ := ft1e_translation_entries hδτ
    have hdet : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe δ
      rwa [Matrix.det_fin_two] at h
    have h00 : δ 0 0 ≠ 0 := by
      intro h0
      rw [h10, mul_zero, sub_zero, h0, zero_mul] at hdet
      exact zero_ne_one hdet
    have h00C : (δ 0 0 : ℂ) ≠ 0 := by exact_mod_cast h00
    have hdenδ : (δ 1 0 : ℂ) * q + δ 1 1 ≠ 0 := by
      rw [h10, h11, Complex.ofReal_zero, zero_mul, zero_add]
      exact h00C
    have hmc : mobiusSL (slRealToComplex δ) (q : ExtPlane) = ((h36p_m δ q : ℂ) : ExtPlane) :=
      s36x_msl_coe δ hdenδ
    have hmδ : mobiusSL (slRealToComplex δ) (q : ExtPlane) = ((q + (k : ℂ) : ℂ) : ExtPlane) := by
      rw [hmc]
      congr 1
      show ((δ 0 0 : ℂ) * q + δ 0 1) / ((δ 1 0 : ℂ) * q + δ 1 1) = q + (k : ℂ)
      rw [h10, h11, h01, Complex.ofReal_zero, zero_mul, zero_add, div_eq_iff h00C,
        Complex.ofReal_mul]
      push_cast
      ring
    have hπk : π₀ ^ k = A * δ * A⁻¹ := by
      rw [hδ]
      group
    rw [hπk, k24_slReal_mul, k24_slReal_mul, k24_mobiusSL_mul, k24_mobiusSL_mul, k24_slReal_inv,
      k24_mobiusSL_inv_apply, hmδ]
  -- The compact core: the A-image of the closed period strip of height two on both sides.
  let Q : Set ℂ := (fun x : ℝ × ℝ => (x.1 : ℂ) + (x.2 : ℂ) * I) '' (Icc (0 : ℝ) 1 ×ˢ Icc (-2 : ℝ) 2)
  have hQ : IsCompact Q := (isCompact_Icc.prod isCompact_Icc).image
    ((Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have hQmem : ∀ q : ℂ, q.re ∈ Icc (0 : ℝ) 1 → q.im ∈ Icc (-2 : ℝ) 2 → q ∈ Q :=
    fun q h1 h2 => ⟨(q.re, q.im), ⟨h1, h2⟩, Complex.re_add_im q⟩
  refine ⟨(k24_mobiusSLHomeo (slRealToComplex A)) '' (((↑) : ℂ → ExtPlane) '' Q),
    (hQ.image OnePoint.continuous_coe).image (k24_mobiusSLHomeo (slRealToComplex A)).continuous,
    ?_, ?_⟩
  · rintro _ ⟨_, ⟨q, -, rfl⟩, rfl⟩ hql
    have h : mobiusSL (slRealToComplex A) (q : ExtPlane) = mobiusSL (slRealToComplex A) extInf :=
      Set.mem_singleton_iff.1 (hlim hql)
    have h' : (k24_mobiusSLHomeo (slRealToComplex A)) (q : ExtPlane) =
        (k24_mobiusSLHomeo (slRealToComplex A)) extInf := h
    exact OnePoint.coe_ne_infty q ((k24_mobiusSLHomeo (slRealToComplex A)).injective h')
  · intro p hp
    obtain ⟨y, rfl⟩ : ∃ y : ExtPlane, p = mobiusSL (slRealToComplex A) y :=
      ⟨mobiusSL (slRealToComplex A)⁻¹ p, by
        rw [← k24_mobiusSL_mul, mul_inv_cancel, k24_mobiusSL_one]⟩
    induction y using OnePoint.rec with
    | infty => exact (hp hξ).elim
    | coe q =>
      obtain ⟨t, ht⟩ : ∃ t : ℤ, t = ⌊q.re⌋ := ⟨_, rfl⟩
      have hf1 := Int.floor_le q.re
      have hf2 := Int.lt_floor_add_one q.re
      rw [← ht] at hf1 hf2
      refine ⟨π₀ ^ (-t), zpow_mem hπ _, ?_⟩
      rw [hshift (-t) q]
      obtain ⟨q', hq'⟩ : ∃ q' : ℂ, q' = q + ((-t : ℤ) : ℂ) := ⟨_, rfl⟩
      rw [← hq']
      have hre : q'.re ∈ Icc (0 : ℝ) 1 := by
        have hr : q'.re = q.re - t := by
          rw [hq', Complex.add_re, Complex.intCast_re, Int.cast_neg, sub_eq_add_neg]
        rw [hr]
        constructor <;> linarith
      by_cases him : |q'.im| ≤ 2
      · left
        refine ⟨(q' : ExtPlane), ⟨q', hQmem q' hre ⟨?_, ?_⟩, rfl⟩, rfl⟩
        · linarith [neg_abs_le q'.im]
        · linarith [le_abs_self q'.im]
      · right
        rcases lt_abs.1 (not_le.1 him) with hup | hlo
        · have hpos : 0 < q'.im := by linarith
          refine ⟨UpperHalfPlane.mk q' hpos, hup, Or.inl ?_⟩
          have h1 : mobiusSL (slRealToComplex A) (q' : ExtPlane) = ((h36p_m A q' : ℂ) : ExtPlane) :=
            s36x_msl_coe A (hden q' hpos.ne')
          have h2 : h36p_m A q' = ((A • UpperHalfPlane.mk q' hpos : UpperHalfPlane) : ℂ) :=
            h36p_m_coe A (UpperHalfPlane.mk q' hpos)
          rw [h1, h2]
        · have hpos : 0 < (conj q').im := by
            rw [Complex.conj_im]
            linarith
          refine ⟨UpperHalfPlane.mk (conj q') hpos, ?_, Or.inr ?_⟩
          · show 2 < (conj q').im
            rw [Complex.conj_im]
            exact hlo
          have hne : q'.im ≠ 0 := by
            intro h0
            rw [h0, neg_zero] at hlo
            norm_num at hlo
          have h1 : mobiusSL (slRealToComplex A) (q' : ExtPlane) = ((h36p_m A q' : ℂ) : ExtPlane) :=
            s36x_msl_coe A (hden q' hne)
          have h2 : h36p_m A (conj (conj q')) = conj (h36p_m A (conj q')) :=
            b33_e_mobius_conj A (conj q')
          have h3 : h36p_m A (conj q') =
              ((A • UpperHalfPlane.mk (conj q') hpos : UpperHalfPlane) : ℂ) :=
            h36p_m_coe A (UpperHalfPlane.mk (conj q') hpos)
          rw [h1, ← h3, ← h2, Complex.conj_conj]

end LiZhongQC
