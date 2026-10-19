import LiZhongQC.Lemmas.D0OrdinaryStabilizer

/-! Spherical transfer of the actual D0 ordinary stabilizer, for D1 I. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- The affine D0 stabilizer theorem also holds at every ordinary real spherical
point, including infinity. Normalize the point to zero and transport the group,
freeness and ordinary locus through the same real Mobius transformation. -/
theorem s36d1_spherical_stabilizer (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {a : ExtPlane} (ha : a ∈ ordinarySet Γ)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ)
    (hfix : mobiusSL (slRealToComplex γ) a = a) : γ = 1 ∨ γ = -1 := by
  obtain ⟨H, hH⟩ := h36q_d_exists_base ha.1
  let Δ := conjGroup Γ H⁻¹
  have hΔ : IsFuchsian Δ := s30l_isFuchsian_conj hΓ H⁻¹
  have hΔfree : ActsFreely Δ := by
    intro δ hδ τ hδτ
    obtain ⟨g, hg, rfl⟩ := s30l_mem_conjGroup.mp hδ
    have hgτ : g • (H • τ) = H • τ := by
      have hh := congrArg (fun σ : UpperHalfPlane => H • σ) hδτ
      simpa only [mul_smul, inv_inv, smul_inv_smul] using hh
    rcases hfree g hg (H • τ) hgτ with heq | heq
    · left
      simp [heq]
    · right
      simp [heq]
  have htransport : mobiusSL (slRealToComplex H) '' fuchsianLimitSet Δ ⊆
      fuchsianLimitSet Γ := by
    change mobiusSL (slRealToComplex H) ''
      limitSet (Δ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ))) ⊆
      limitSet (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)))
    apply k24_c_limitSet_image_subset (k24_mobiusSLHomeo (slRealToComplex H)).continuous
      (k24_mobiusSLHomeo (slRealToComplex H)).injective
    intro g hg
    obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨g', hg', rfl⟩ := s30l_mem_conjGroup.mp hδ
    refine ⟨slRealToComplex g', Subgroup.mem_map_of_mem _ hg', ?_⟩
    intro p
    change mobiusSL (slRealToComplex H)
      (mobiusSL (slRealToComplex (H⁻¹ * g' * (H⁻¹)⁻¹)) p) =
      mobiusSL (slRealToComplex g') (mobiusSL (slRealToComplex H) p)
    rw [inv_inv, k24_slReal_mul, k24_slReal_mul, k24_slReal_inv,
      k24_mobiusSL_mul, k24_mobiusSL_mul, k24_mobiusSL_apply_inv]
  have hzero : ((0 : ℂ) : ExtPlane) ∉ fuchsianLimitSet Δ := by
    intro hz
    exact ha.2 (htransport ⟨((0 : ℂ) : ExtPlane), hz, hH⟩)
  let δ := H⁻¹ * γ * H
  have hδmem : δ ∈ Δ := by
    apply s30l_mem_conjGroup.mpr
    exact ⟨γ, hγ, by change H⁻¹ * γ * H = H⁻¹ * γ * (H⁻¹)⁻¹; rw [inv_inv]⟩
  have hδfix : mobiusSL (slRealToComplex δ) ((0 : ℂ) : ExtPlane) =
      ((0 : ℂ) : ExtPlane) := by
    change mobiusSL (slRealToComplex (H⁻¹ * γ * H)) ((0 : ℂ) : ExtPlane) = _
    rw [k24_slReal_mul, k24_slReal_mul, k24_mobiusSL_mul, k24_mobiusSL_mul,
      k24_slReal_inv, hH, hfix, ← hH, k24_mobiusSL_inv_apply]
  have hden : (δ 1 0 : ℂ) * 0 + δ 1 1 ≠ 0 := by
    intro hd
    have hi : mobiusSL (slRealToComplex δ) ((0 : ℂ) : ExtPlane) = extInf :=
      s36x_msl_inf δ hd
    exact OnePoint.coe_ne_infty (0 : ℂ) (hδfix.symm.trans hi)
  have haff : h36p_m δ 0 = 0 := by
    have hc : mobiusSL (slRealToComplex δ) ((0 : ℂ) : ExtPlane) =
        ((h36p_m δ 0 : ℂ) : ExtPlane) := s36x_msl_coe δ hden
    exact OnePoint.coe_injective (hc.symm.trans hδfix)
  have hδsign := s36d0_ordinary_stabilizer hΔ hΔfree hzero hδmem hden haff
  have hback : H * δ * H⁻¹ = γ := by
    dsimp only [δ]
    group
  rcases hδsign with heq | heq
  · left
    rw [← hback, heq]
    simp
  · right
    rw [← hback, heq]
    simp

end LiZhongQC
