import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller
import LiZhongQC.Lemmas.UniformizedUniqueness
import LiZhongQC.Ch08.S29_TeichmullerMetric
import LiZhongQC.Lemmas.UniformizedTeichmuller
import LiZhongQC.Lemmas.FiniteTypeCover
import LiZhongQC.Lemmas.FiniteTypeComparisonEven
import LiZhongQC.Lemmas.FiniteTypeComparisonOdd

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

section
variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
  [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

/-- **The comparison inequality for surfaces without boundary** (`m = 0`, non-exceptional): the area of `r` is
finite and, if it is `1`, `K[h] ≤ ∬ D[a] dA_r`. -/
theorem s82cmp_core_zero {g n : ℕ} (hex : ¬ IsExceptionalType g n 0)
    (F₀ : FiniteTypeStructure S₀ g n 0) (Y : FiniteTypeRS.{u} g n 0)
    (a : S₀ ≃ₜ Y.carrier) (ha : IsQCRS a) {h : S₀ ≃ₜ Y.carrier} {r : S₀ → ℂ → ℂ}
    {r' : Y.carrier → ℂ → ℂ} {k : ℝ} (hh : IsAdmissibleTeichmullerMap F₀ h r r' k) (hk : 0 < k)
    (hhom : ContinuousMap.Homotopic (h : C(S₀, Y.carrier)) (a : C(S₀, Y.carrier))) :
    quadDiffNorm r < ⊤ ∧ (quadDiffNorm r = 1 → maxDilatationRS h ≤ surfaceIntegral r
      (fun x z => ENNReal.ofReal (dilatationQuotient (localMapExprAt a x z) z))) := by
  classical
  obtain ⟨k', rfl | rfl⟩ := Nat.even_or_odd' n
  · rcases Nat.eq_zero_or_pos k' with rfl | hk'
    · -- closed case
      obtain ⟨hcS, -⟩ := s82cmp_type_zero F₀
      haveI : CompactSpace S₀ := hcS
      refine ⟨(quadDiffNorm_finite hh.2.initial).1, fun hn1 => ?_⟩
      exact s82cmp_core_closed (by simpa using hex) F₀ Y a ha hh hk hhom hn1
    · by_cases hg0 : g = 0
      · subst hg0
        rcases Nat.lt_or_ge k' 3 with hlt | hge
        · have : k' = 1 ∨ k' = 2 := by omega
          rcases this with rfl | rfl
          · exact (hex (by simp [IsExceptionalType])).elim
          · exact s82cmp_core_g0n4 F₀ Y a ha hh hhom
        · exact s82cmp_core_even hk' (by omega) F₀ Y a ha hh hhom
      · exact s82cmp_core_even hk' (by omega) F₀ Y a ha hh hhom
  · exact s82cmp_core_odd hex F₀ Y a ha hh hhom

end

end LiZhongQC
