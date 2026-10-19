import LiZhongQC.Lemmas.FinitePunctureCompactification

open Complex Set Metric Filter Topology
open scoped Manifold ContDiff
noncomputable section
namespace LiZhongQC
universe u

/-- The inverse of an injective holomorphic surface coordinate on an open set
is holomorphic throughout its image. Generalizes the punctured-unit-disc
specialization s30l_psi_mdiff, using the same proved planar inverse theorem. -/
theorem s31eg_coordinate_inverse {S : Type u} [TopologicalSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] [Nonempty S]
    {U : Set S} {φ : S → ℂ} (hUo : IsOpen U) (hinj : InjOn φ U)
    (hmd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) φ U) {w₀ : ℂ} (hw₀ : w₀ ∈ φ '' U) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Function.invFunOn φ U) w₀ := by
  obtain ⟨x₀, hx₀, rfl⟩ := hw₀
  let χ := chartAt ℂ x₀
  let O : Set ℂ := χ '' (U ∩ χ.source)
  have hOo : IsOpen O :=
    χ.isOpen_image_of_subset_source (hUo.inter χ.open_source) inter_subset_right
  have hOmem : χ x₀ ∈ O := ⟨x₀, ⟨hx₀, mem_chart_source ℂ x₀⟩, rfl⟩
  let g : ℂ → ℂ := fun c => φ (χ.symm c)
  have hgd : DifferentiableOn ℂ g O := by
    rintro _ ⟨y, ⟨hyU, hys⟩, rfl⟩
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) φ (χ.symm (χ y)) := by
      rw [χ.left_inv hys]
      exact (hmd y hyU).mdifferentiableAt (hUo.mem_nhds hyU)
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) χ.symm (χ y) :=
      mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ x₀) (χ.map_source hys)
    exact (mdifferentiableAt_iff_differentiableAt.1
      (h1.comp (χ y) h2)).differentiableWithinAt
  have hginj : InjOn g O := by
    rintro _ ⟨y₁, ⟨hy₁U, hy₁s⟩, rfl⟩ _ ⟨y₂, ⟨hy₂U, hy₂s⟩, rfl⟩ h
    change φ (χ.symm (χ y₁)) = φ (χ.symm (χ y₂)) at h
    rw [χ.left_inv hy₁s, χ.left_inv hy₂s] at h
    rw [hinj hy₁U hy₂U h]
  have hconf : IsConformalOnto g O (g '' O) := ⟨hgd, hginj, rfl⟩
  have hVo : IsOpen (g '' O) := hconf.isOpen hOo
  have hgc : g (χ x₀) = φ x₀ := by
    change φ (χ.symm (χ x₀)) = φ x₀
    rw [χ.left_inv (mem_chart_source ℂ x₀)]
  have heq : Function.invFunOn φ U =ᶠ[𝓝 (φ x₀)]
      fun w => χ.symm (Function.invFunOn g O w) := by
    have hmem : g '' O ∈ 𝓝 (φ x₀) := hVo.mem_nhds ⟨χ x₀, hOmem, hgc⟩
    filter_upwards [hmem] with w hw
    obtain ⟨c, ⟨y, ⟨hyU, hys⟩, rfl⟩, rfl⟩ := hw
    rw [hginj.leftInvOn_invFunOn ⟨y, ⟨hyU, hys⟩, rfl⟩, χ.left_inv hys]
    change Function.invFunOn φ U (φ (χ.symm (χ y))) = y
    rw [χ.left_inv hys]
    exact hinj.leftInvOn_invFunOn hyU
  have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Function.invFunOn g O) (φ x₀) := by
    rw [← hgc]
    exact mdifferentiableAt_iff_differentiableAt.2
      (hconf.differentiableAt_invFunOn hOo hOmem)
  have h3 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) χ.symm (Function.invFunOn g O (φ x₀)) := by
    have he : Function.invFunOn g O (φ x₀) = χ x₀ := by
      rw [← hgc]
      exact hginj.leftInvOn_invFunOn hOmem
    rw [he]
    exact mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ x₀)
      (χ.map_source (mem_chart_source ℂ x₀))
  exact (h3.comp (φ x₀) h2).congr_of_eventuallyEq heq

end LiZhongQC

