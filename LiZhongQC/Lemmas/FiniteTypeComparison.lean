import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller
import LiZhongQC.Lemmas.UniformizedUniqueness
import LiZhongQC.Ch08.S29_TeichmullerMetric
import LiZhongQC.Lemmas.UniformizedTeichmuller
import LiZhongQC.Lemmas.FiniteTypeCover
import LiZhongQC.Lemmas.FiniteTypeComparisonZero
import LiZhongQC.Lemmas.FiniteTypeComparisonBoundary
import LiZhongQC.Lemmas.S32wThm323
import LiZhongQC.Lemmas.S32wThm324

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

section
variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
  [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

/-- **The comparison inequality for all non-exceptional finite types** (unnormalized form of L32329 for a given
admissible Teichmüller map `h` and `a ≃ h`): the area of `r` is finite and, if it is `1`, `K[h] ≤ ∬ D[a] dA_r`. -/
theorem s82cmp_core_all {g n m : ℕ} (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) (Y : FiniteTypeRS.{u} g n m)
    (a : S₀ ≃ₜ Y.carrier) (ha : IsQCRS a) {h : S₀ ≃ₜ Y.carrier} {r : S₀ → ℂ → ℂ}
    {r' : Y.carrier → ℂ → ℂ} {k : ℝ} (hh : IsAdmissibleTeichmullerMap F₀ h r r' k) (hk : 0 < k)
    (hhom : ContinuousMap.Homotopic (h : C(S₀, Y.carrier)) (a : C(S₀, Y.carrier))) :
    quadDiffNorm r < ⊤ ∧ (quadDiffNorm r = 1 → maxDilatationRS h ≤ surfaceIntegral r
      (fun x z => ENNReal.ofReal (dilatationQuotient (localMapExprAt a x z) z))) := by
  by_cases hm : m = 0
  · subst hm
    exact s82cmp_core_zero hex F₀ Y a ha hh hk hhom
  · exact s82cmp_core_boundary hm hex F₀ Y a ha hh hk hhom

theorem s82cmp_extremal_comparison {g n m : ℕ} (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) (Y : FiniteTypeRS.{u} g n m) (a : S₀ ≃ₜ Y.carrier) (ha : IsQCRS a) :
    ∃ h : S₀ ≃ₜ Y.carrier, IsQCRS h ∧
      ContinuousMap.Homotopic (h : C(S₀, Y.carrier)) (a : C(S₀, Y.carrier)) ∧
      (∀ b : S₀ ≃ₜ Y.carrier, IsQCRS b →
        ContinuousMap.Homotopic (h : C(S₀, Y.carrier)) (b : C(S₀, Y.carrier)) →
          maxDilatationRS h ≤ maxDilatationRS b) ∧
      (IsBiholomorphic h ∨ ∃ (r : S₀ → ℂ → ℂ) (r' : Y.carrier → ℂ → ℂ) (k : ℝ), 0 < k ∧
        IsAdmissibleTeichmullerMap F₀ h r r' k ∧ quadDiffNorm r = 1 ∧
        maxDilatationRS h ≤ surfaceIntegral r
          (fun x z => ENNReal.ofReal (dilatationQuotient (localMapExprAt a x z) z))) := by
  classical
  obtain ⟨f₀, hFf, hcase⟩ := s32w_thm32_4 hex F₀ Y.structure' a ha
  have hext : IsQCRS f₀ ∧ ∀ b : S₀ ≃ₜ Y.carrier, IsQCRS b →
      ContinuousMap.Homotopic (f₀ : C(S₀, Y.carrier)) (b : C(S₀, Y.carrier)) →
        maxDilatationRS f₀ ≤ maxDilatationRS b := by
    letI : Nonempty S₀ := ConnectedSpace.toNonempty
    rcases hcase with hb | ⟨q, q', k, hq⟩
    · have h1 : IsKQCRS f₀ 1 := (isKQCRS_one_iff f₀).2 hb
      refine ⟨⟨1, h1⟩, fun b hb' _ => ?_⟩
      exact (by simpa using maxDilatationRS_le h1 : maxDilatationRS f₀ ≤ 1).trans
        (s29_m_one_le_maxDilatationRS hb')
    · exact ⟨hq.2.qc, fun b hb' hbh => (s32w_thm32_3_uniqueness_gnm hex F₀ Y.structure' hq hb' hbh).1⟩
  refine ⟨f₀, hext.1, hFf.symm, hext.2, ?_⟩
  rcases hcase with hb | ⟨q, q', k, hq⟩
  · exact Or.inl hb
  · by_cases hk : k = 0
    · left
      have hmax : maxDilatationRS f₀ = 1 := by
        have := (teichmullerMap_beltrami hq.2).2
        rw [hk] at this
        simpa using this
      exact (isKQCRS_one_iff f₀).1 (utm_isKQCRS_one_of_maxDil hq.2.qc hmax)
    · right
      have hk0 : 0 < k := lt_of_le_of_ne hq.2.k_nonneg (Ne.symm hk)
      have hN0 : quadDiffNorm q ≠ 0 := s26_quadDiffNorm_pos hq.2.initial hq.2.initial_ne
      have hNt : quadDiffNorm q ≠ ⊤ :=
        (s82cmp_core_all hex F₀ Y f₀ hq.2.qc hq hk0 (ContinuousMap.Homotopic.refl _)).1.ne
      set N := (quadDiffNorm q).toReal with hNdef
      have hNpos : 0 < N := ENNReal.toReal_pos hN0 hNt
      have hc : 0 < N⁻¹ := inv_pos.2 hNpos
      have e : (((N⁻¹ : ℝ) : ℂ) • q) = ((N⁻¹ : ℝ) • q) := by
        funext x z; simp [Complex.real_smul]
      have hq1 : IsAdmissibleTeichmullerMap F₀ f₀ (((N⁻¹ : ℝ) : ℂ) • q) (((N⁻¹ : ℝ) : ℂ) • q') k := by
        refine ⟨?_, s29_e12_teichMap_smul hq.2 hc⟩
        rw [e]
        exact (admissibleQDInterior F₀).smul_mem _ hq.1
      have hnorm : quadDiffNorm (((N⁻¹ : ℝ) : ℂ) • q) = 1 := by
        rw [s82cmp_quadDiffNorm_smul q hc, ENNReal.ofReal_inv_of_pos hNpos,
          ENNReal.ofReal_toReal hNt]
        exact ENNReal.inv_mul_cancel hN0 hNt
      refine ⟨_, _, k, hk0, hq1, hnorm, ?_⟩
      exact (s82cmp_core_all hex F₀ Y a ha hq1 hk0 hFf.symm).2 hnorm

end


end LiZhongQC
