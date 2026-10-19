import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller
import LiZhongQC.Lemmas.UniformizedUniqueness
import LiZhongQC.Ch08.S29_TeichmullerMetric
import LiZhongQC.Lemmas.UniformizedTeichmuller
import LiZhongQC.Lemmas.FiniteTypeCover
import LiZhongQC.Lemmas.BranchedLiftBook
import LiZhongQC.Lemmas.SchottkyBranchedFinal

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]




section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

/-- **The comparison inequality for surfaces of type `(g, 2n', 0)`** (with `(g, n') ≠ (0, 2)`): finiteness of the
area of the initial differential, and Teichmüller's main inequality, by lifting to the branched double cover. -/
theorem s82cmp_core_even {g n' : ℕ} (hn : 0 < n') (hĝ : 3 ≤ 2 * g + n')
    (F₀ : FiniteTypeStructure S₀ g (2 * n') 0) (Y : FiniteTypeRS.{u} g (2 * n') 0)
    (a : S₀ ≃ₜ Y.carrier) (ha : IsQCRS a) {h : S₀ ≃ₜ Y.carrier} {r : S₀ → ℂ → ℂ}
    {r' : Y.carrier → ℂ → ℂ} {k : ℝ} (hh : IsAdmissibleTeichmullerMap F₀ h r r' k)
    (hhom : ContinuousMap.Homotopic (h : C(S₀, Y.carrier)) (a : C(S₀, Y.carrier))) :
    quadDiffNorm r < ⊤ ∧ (quadDiffNorm r = 1 → maxDilatationRS h ≤ surfaceIntegral r
      (fun x z => ENNReal.ofReal (dilatationQuotient (localMapExprAt a x z) z))) := by
  classical
  haveI : Nonempty S₀ := ConnectedSpace.toNonempty
  haveI : Nonempty Y.carrier := ConnectedSpace.toNonempty
  obtain ⟨X', pr, hgen, hdiff, hsurj, hfib, hfibP, -⟩ := s82bc_exists_branched_double_cover
    (X := F₀.X.carrier) (g := g) (n := n') (Or.inr hn.ne') F₀.genus F₀.P F₀.card_P
  have hpr₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr ∧ Function.Surjective pr ∧
      (∀ x ∉ F₀.P, (pr ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ F₀.P, (pr ⁻¹' {x}).ncard = 1 :=
    ⟨hdiff, hsurj, hfib, hfibP⟩
  obtain ⟨X₁', pr₁, hd1, hs1, hf1, hfP1, f₀', f', qtil, qtil', -, hrelf, hT, hQ', -, hhom', hpb, -⟩ :=
    s82lc_lift_teichmullerMap_double_cover_ext F₀ Y.structure' hpr₀ hh ha hhom
  have hpr₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₁ ∧ Function.Surjective pr₁ ∧
      (∀ x ∉ Y.structure'.P, (pr₁ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ Y.structure'.P, (pr₁ ⁻¹' {x}).ncard = 1 :=
    ⟨hd1, hs1, hf1, hfP1⟩
  obtain ⟨-, hloc0, -⟩ := s82lc_local_form hpr₀
  obtain ⟨-, hloc1, -⟩ := s82lc_local_form hpr₁
  have hrange0 : Set.range F₀.ι = (↑F₀.P : Set F₀.X.carrier)ᶜ := by rw [F₀.range_ι]; simp
  have hrange1 : Set.range Y.structure'.ι = (↑Y.structure'.P : Set Y.structure'.X.carrier)ᶜ := by
    rw [Y.structure'.range_ι]; simp
  have hloc0' : ∀ y, pr y ∈ Set.range F₀.ι → ∃ e : OpenPartialHomeomorph X'.carrier F₀.X.carrier,
      y ∈ e.source ∧ EqOn pr e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target :=
    fun y hy => hloc0 y (by rwa [hrange0] at hy)
  have hloc1' : ∀ y, pr₁ y ∈ Set.range Y.structure'.ι →
      ∃ e : OpenPartialHomeomorph X₁'.carrier Y.structure'.X.carrier,
      y ∈ e.source ∧ EqOn pr₁ e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target :=
    fun y hy => hloc1 y (by rwa [hrange1] at hy)
  have hr : IsHolQuadDiff r := hh.2.initial
  have hq : IsHolQuadDiff qtil := hT.initial
  -- pointwise dilatation densities
  have hU : ∀ y s, pr y = F₀.ι s →
      ENNReal.ofReal (dilatationQuotient (localMapExpr f' y) (chartAt ℂ y y)) =
        ENNReal.ofReal (dilatationQuotient (localMapExpr a s) (chartAt ℂ s s)) := by
    intro y s hs
    rw [s82cmp_D_lift F₀.embedding F₀.holomorphic Y.structure'.embedding Y.structure'.holomorphic
      hdiff.continuous hd1.continuous hloc0' hloc1' f'.continuous hrelf hs]
  -- the cover integrals
  have hnorm : quadDiffNorm qtil = 2 * quadDiffNorm r :=
    s82cmp_cover_integral F₀ hdiff.continuous hfib hfibP hloc0 hr hq hpb (fun _ => 1) (fun _ => 1)
      (fun _ _ _ => rfl)
  have hDil := s82cmp_cover_integral F₀ hdiff.continuous hfib hfibP hloc0 hr hq hpb
    (fun s => ENNReal.ofReal (dilatationQuotient (localMapExpr a s) (chartAt ℂ s s)))
    (fun y => ENNReal.ofReal (dilatationQuotient (localMapExpr f' y) (chartAt ℂ y y))) hU
  have hfin : quadDiffNorm qtil < ⊤ := (quadDiffNorm_finite hq).1
  have hr_fin : quadDiffNorm r < ⊤ := by
    rw [hnorm] at hfin
    exact lt_of_le_of_lt (by
      calc quadDiffNorm r = 1 * quadDiffNorm r := (one_mul _).symm
        _ ≤ 2 * quadDiffNorm r := by gcongr; norm_num) hfin
  refine ⟨hr_fin, fun hn1 => ?_⟩
  have hqn : quadDiffNorm qtil = 2 := by rw [hnorm, hn1, mul_one]
  have hc : (0 : ℝ) < 1 / 2 := by norm_num
  have hT2 := s29_e12_teichMap_smul hT hc
  have hnorm2 : quadDiffNorm (((1 / 2 : ℝ) : ℂ) • qtil) = 1 := by
    rw [s82cmp_quadDiffNorm_smul qtil hc, hqn, one_div, ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_ofNat]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have hgenus1 : HasGenus X₁'.carrier (2 * g + n' - 1) :=
    hasGenus_of_homeomorph (X := X₁') hgen f₀'
  have key := s82cmp_closed_core (g := 2 * g + n' - 1) (by omega) hgen hgenus1 hT2 f' hQ' hhom' hnorm2
  rw [s82cmp_surfaceIntegral_smul qtil _ hc, s82cmp_surfaceIntegral_Dil f' qtil, hDil] at key
  rw [s82cmp_surfaceIntegral_Dil a r]
  have hmax : maxDilatationRS h = ENNReal.ofReal ((1 + k) / (1 - k)) :=
    (teichmullerMap_beltrami hh.2).2
  rw [hmax]
  refine key.trans (le_of_eq ?_)
  rw [← mul_assoc, one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

end

end LiZhongQC
