import LiZhongQC.Lemmas.S22gbTransfer

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u

section GaussBonnetCancel

variable {S : Type u} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S] [CompactSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- The cross terms of a smooth partition of unity cancel pointwise on the surface, once every
term is divided by the area density: this is the chart-invariant form of `∑ dρᵢ = 0`. -/
theorem s22gb_cancel {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) {q : S → ℂ → ℂ}
    (hq : IsDiffFamily 1 0 q) {α : S → ℂ → ℂ → ℝ}
    (hα : ∀ (x : S) (z : ℂ), z ∈ (chartAt ℂ x).target →
      AnalyticAt ℂ (q x) z → q x z ≠ 0 →
      ∀ ψ : ℂ → ℂ, AnalyticAt ℂ ψ z → deriv ψ z ≠ 0 → ψ z ∈ upperHalf →
        (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z] (fun w => (chartAt ℂ x).symm w) →
        α x =ᶠ[𝓝 z] s22cd_canonicalGauge ψ (q x))
    (hsm : ∀ (x : S) (z : ℂ), z ∈ (chartAt ℂ x).target → MeromorphicAt (q x) z →
      meromorphicOrderAt (q x) z = 0 → ∀ v : ℂ, ContDiffAt ℝ 1 (fun w => α x w v) z)
    {ι : Type*} [Fintype ι] (ρ : ι → S → ℝ)
    (hρs : ∀ i, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) (ρ i))
    (hρsum : ∀ y, ∑ i, ρ i y = 1)
    (xs : ι → S) (Dom : ι → Set ℂ) (ψs : ι → ℂ → ℂ)
    (hDo : ∀ i, IsOpen (Dom i)) (hDt : ∀ i, Dom i ⊆ (chartAt ℂ (xs i)).target)
    (hψan : ∀ i, ∀ z ∈ Dom i, AnalyticAt ℂ (ψs i) z)
    (hψd : ∀ i, ∀ z ∈ Dom i, deriv (ψs i) z ≠ 0)
    (hψH : ∀ i, ∀ z ∈ Dom i, ψs i z ∈ upperHalf)
    (hψe : ∀ i, ∀ z ∈ Dom i,
      s22gm_projectionExtension p (ψs i z) = (chartAt ℂ (xs i)).symm z)
    (hts : ∀ i, tsupport (ρ i) ⊆ (chartAt ℂ (xs i)).symm '' Dom i)
    (A : Set S)
    (hAreg : ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ A →
      MeromorphicAt (q x) z ∧ meromorphicOrderAt (q x) z = 0)
    (W : ι → ℂ → ℝ)
    (hW : ∀ i z, W i z = fderiv ℝ (fun w => ρ i ((chartAt ℂ (xs i)).symm w)) z 1 *
        α (xs i) z I - fderiv ℝ (fun w => ρ i ((chartAt ℂ (xs i)).symm w)) z I * α (xs i) z 1)
    (y : S) (hy : y ∈ A) :
    ∑ i, ((chartAt ℂ (xs i)).symm '' Dom i).indicator
      (fun y' => W i (chartAt ℂ (xs i) y') / s22gc_areaDensity (ψs i) (chartAt ℂ (xs i) y')) y = 0 := by
  classical
  set c : ℂ := chartAt ℂ y y with hc
  have hct : c ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source (mem_chart_source ℂ y)
  have hcs : (chartAt ℂ y).symm c = y := (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  obtain ⟨hmy, hoy⟩ := hAreg y c hct (by rw [hcs]; exact hy)
  obtain ⟨ψy, hψyan, hψyd, hψyH, hψye⟩ := s22gb_local_lift hp y hct
  have hDy : 0 < s22gc_areaDensity ψy c := s22gc_areaDensity_pos hψyd (show 0 < (ψy c).im from hψyH)
  -- the chart-`y` wedge of each partition function
  set Wy : ι → ℝ := fun i =>
    fderiv ℝ (fun w => ρ i ((chartAt ℂ y).symm w)) c 1 * α y c I -
      fderiv ℝ (fun w => ρ i ((chartAt ℂ y).symm w)) c I * α y c 1 with hWy
  have hterm : ∀ i, ((chartAt ℂ (xs i)).symm '' Dom i).indicator
      (fun y' => W i (chartAt ℂ (xs i) y') / s22gc_areaDensity (ψs i) (chartAt ℂ (xs i) y')) y =
        Wy i / s22gc_areaDensity ψy c := by
    intro i
    by_cases hyi : y ∈ (chartAt ℂ (xs i)).symm '' Dom i
    · rw [indicator_of_mem hyi]
      obtain ⟨z0, hz0, hz0y⟩ := hyi
      have hz0t : z0 ∈ (chartAt ℂ (xs i)).target := hDt i hz0
      have hchart : chartAt ℂ (xs i) y = z0 := by
        rw [← hz0y]; exact (chartAt ℂ (xs i)).right_inv hz0t
      have hysrc : (chartAt ℂ (xs i)).symm z0 ∈ (chartAt ℂ y).source := by
        rw [hz0y]; exact mem_chart_source ℂ y
      have hτ : (chartAt ℂ y ∘ (chartAt ℂ (xs i)).symm) z0 = c := by
        simp only [Function.comp_apply, hz0y, hc]
      obtain ⟨hm, ho⟩ := hAreg (xs i) z0 hz0t (by rw [hz0y]; exact hy)
      have hex : (fun w => s22gm_projectionExtension p (ψs i w)) =ᶠ[𝓝 z0]
          fun w => (chartAt ℂ (xs i)).symm w := by
        filter_upwards [(hDo i).mem_nhds hz0] with w hw
        exact hψe i w hw
      have key := s22gb_invariance hp hq hα hsm (ρ i) (hρs i) (xs i) y hz0t hysrc hm ho
        (by rw [hτ]; exact hmy) (by rw [hτ]; exact hoy) (hψan i z0 hz0) (hψH i z0 hz0) hex
        (by rw [hτ]; exact hψyan) (by rw [hτ]; exact hψyH) (by rw [hτ]; exact hψye)
      rw [hτ] at key
      obtain ⟨k1, k2⟩ := key
      have hane : deriv (chartAt ℂ y ∘ (chartAt ℂ (xs i)).symm) z0 ≠ 0 := by
        have hux : (chartAt ℂ (xs i)).symm z0 ∈ (chartAt ℂ (xs i)).source :=
          (chartAt ℂ (xs i)).map_target hz0t
        have := Jacobians.Dolbeault.transition_deriv_ne_zero hux hysrc
        rwa [(chartAt ℂ (xs i)).right_inv hz0t] at this
      have hn : 0 < ‖deriv (chartAt ℂ y ∘ (chartAt ℂ (xs i)).symm) z0‖ ^ 2 :=
        pow_pos (norm_pos_iff.2 hane) 2
      rw [hchart, hW i z0, k1, k2]
      field_simp
      rfl
    · rw [indicator_of_notMem hyi]
      have hy0 : y ∉ tsupport (ρ i) := fun h => hyi (hts i h)
      have hev : ∀ᶠ y' in 𝓝 y, ρ i y' = 0 := by
        have := (isClosed_tsupport (ρ i)).isOpen_compl.mem_nhds hy0
        filter_upwards [this] with y' hy'
        exact image_eq_zero_of_notMem_tsupport hy'
      have hev2 : (fun w => ρ i ((chartAt ℂ y).symm w)) =ᶠ[𝓝 c] fun _ => 0 := by
        have h2 := ((chartAt ℂ y).continuousAt_symm hct).eventually
          (show ∀ᶠ y' in 𝓝 ((chartAt ℂ y).symm c), ρ i y' = 0 by rw [hcs]; exact hev)
        filter_upwards [h2] with w hw
        exact hw
      have hf0 : fderiv ℝ (fun w => ρ i ((chartAt ℂ y).symm w)) c = 0 := by
        rw [hev2.fderiv_eq]
        simp
      simp only [hWy, hf0, ContinuousLinearMap.zero_apply, zero_mul, sub_zero, zero_div]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_div]
  have hsum0 : ∑ i, fderiv ℝ (fun w => ρ i ((chartAt ℂ y).symm w)) c = 0 := by
    have hd : ∀ i ∈ (Finset.univ : Finset ι),
        DifferentiableAt ℝ (fun w => ρ i ((chartAt ℂ y).symm w)) c :=
      fun i _ => (s22gb_rho_contDiffAt (ρ i) (hρs i) y hct).differentiableAt (by simp)
    rw [← fderiv_fun_sum hd]
    have : (fun w => ∑ i ∈ (Finset.univ : Finset ι), ρ i ((chartAt ℂ y).symm w)) =
        fun _ => (1 : ℝ) := funext fun w => hρsum _
    rw [this]
    simp
  have e1 : ∑ i, fderiv ℝ (fun w => ρ i ((chartAt ℂ y).symm w)) c 1 = 0 := by
    have := congrArg (fun L : ℂ →L[ℝ] ℝ => L 1) hsum0
    simpa using this
  have e2 : ∑ i, fderiv ℝ (fun w => ρ i ((chartAt ℂ y).symm w)) c I = 0 := by
    have := congrArg (fun L : ℂ →L[ℝ] ℝ => L I) hsum0
    simpa using this
  have : ∑ i, Wy i = 0 := by
    simp only [hWy, Finset.sum_sub_distrib, ← Finset.sum_mul, e1, e2, zero_mul, sub_zero]
  rw [this, zero_div]

end GaussBonnetCancel

end LiZhongQC
