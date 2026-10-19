import LiZhongQC.Lemmas.S22gbTensor

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u

section GaussBonnetInv

variable {S : Type u} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S] [CompactSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- A smooth function on the surface is smooth in every chart. -/
theorem s22gb_rho_contDiffAt (ρ : S → ℝ) (hρ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) ρ) (y : S)
    {ξ : ℂ} (hξ : ξ ∈ (chartAt ℂ y).target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun w => ρ ((chartAt ℂ y).symm w)) ξ := by
  have hs : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (chartAt ℂ y).symm ξ :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞))
      (x := y) ξ hξ).contMDiffAt ((chartAt ℂ y).open_target.mem_nhds hξ)
  exact contMDiffAt_iff_contDiffAt.mp (hρ.contMDiffAt.comp ξ hs)

/-- A real-linear functional on `ℂ` is determined by its values on `1` and `I`. -/
theorem s22gb_clm_expand (L : ℂ →L[ℝ] ℝ) (a : ℂ) : L a = a.re * L 1 + a.im * L I := by
  have h : a = (a.re : ℝ) • (1 : ℂ) + (a.im : ℝ) • I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [h]
  rw [map_add, map_smul, map_smul]
  simp

/-- Rotation-scaling algebra for the wedge product. -/
theorem s22gb_wedge_algebra (a : ℂ) (L : ℂ →L[ℝ] ℝ) (A1 AI B1 BI : ℝ)
    (h1 : B1 = a.re * A1 + a.im * AI) (hI : BI = (-a.im) * A1 + a.re * AI) :
    L (a * 1) * BI - L (a * I) * B1 = ‖a‖ ^ 2 * (L 1 * AI - L I * A1) := by
  have e1 := s22gb_clm_expand L a
  have e2 := s22gb_clm_expand L (a * I)
  have hn : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [mul_one, e1, e2, h1, hI, hn]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    sub_zero, zero_add]
  ring

/-- The derivative of a function read in two charts. -/
theorem s22gb_fderiv_transition (ρ : S → ℝ)
    (hρ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) ρ) (x y : S) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) (hzy : (chartAt ℂ x).symm z ∈ (chartAt ℂ y).source)
    (w' : ℂ) :
    fderiv ℝ (fun w => ρ ((chartAt ℂ x).symm w)) z w' =
      fderiv ℝ (fun w => ρ ((chartAt ℂ y).symm w))
        ((chartAt ℂ y ∘ (chartAt ℂ x).symm) z) (deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) z * w') := by
  set τ : ℂ → ℂ := chartAt ℂ y ∘ (chartAt ℂ x).symm with hτ
  set u := (chartAt ℂ x).symm z with hu
  have hux : u ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
  have hzc : chartAt ℂ x u = z := (chartAt ℂ x).right_inv hz
  have hτan : AnalyticAt ℂ τ z := by
    have := Jacobians.Dolbeault.transition_analyticAt_of_mem hux hzy
    rwa [hzc] at this
  have hτy : τ z ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hzy
  have hρy : DifferentiableAt ℝ (fun w => ρ ((chartAt ℂ y).symm w)) (τ z) :=
    ((s22gb_rho_contDiffAt ρ hρ y hτy).differentiableAt (by simp))
  have hτf : HasFDerivAt τ ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv τ z)).restrictScalars ℝ) z :=
    hτan.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hcomp := HasFDerivAt.comp z hρy.hasFDerivAt hτf
  have hev : (fun w => ρ ((chartAt ℂ x).symm w)) =ᶠ[𝓝 z]
      ((fun w => ρ ((chartAt ℂ y).symm w)) ∘ τ) := by
    filter_upwards [((chartAt ℂ x).continuousAt_symm hz).preimage_mem_nhds
      ((chartAt ℂ y).open_source.mem_nhds hzy)] with w hw
    simp only [Function.comp_apply, hτ]
    rw [(chartAt ℂ y).left_inv hw]
  rw [hev.fderiv_eq, hcomp.fderiv]
  simp [mul_comm]

/-- Chart invariance of the wedge `dρ ∧ α` and of the area density: both transform with the
factor `‖τ'‖²`, so their ratio does not depend on the chart. -/
theorem s22gb_invariance {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) {q : S → ℂ → ℂ}
    (hq : IsDiffFamily 1 0 q) {α : S → ℂ → ℂ → ℝ}
    (hα : ∀ (x : S) (z : ℂ), z ∈ (chartAt ℂ x).target →
      AnalyticAt ℂ (q x) z → q x z ≠ 0 →
      ∀ ψ : ℂ → ℂ, AnalyticAt ℂ ψ z → deriv ψ z ≠ 0 → ψ z ∈ upperHalf →
        (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z] (fun w => (chartAt ℂ x).symm w) →
        α x =ᶠ[𝓝 z] s22cd_canonicalGauge ψ (q x))
    (hsm : ∀ (x : S) (z : ℂ), z ∈ (chartAt ℂ x).target → MeromorphicAt (q x) z →
      meromorphicOrderAt (q x) z = 0 → ∀ v : ℂ, ContDiffAt ℝ 1 (fun w => α x w v) z)
    (ρ : S → ℝ) (hρ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) ρ)
    (x y : S) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target)
    (hzy : (chartAt ℂ x).symm z ∈ (chartAt ℂ y).source)
    (hm : MeromorphicAt (q x) z) (ho : meromorphicOrderAt (q x) z = 0)
    (hmy : MeromorphicAt (q y) ((chartAt ℂ y ∘ (chartAt ℂ x).symm) z))
    (hoy : meromorphicOrderAt (q y) ((chartAt ℂ y ∘ (chartAt ℂ x).symm) z) = 0)
    {ψx ψy : ℂ → ℂ} (hψx : AnalyticAt ℂ ψx z) (hHx : ψx z ∈ upperHalf)
    (hex : (fun w => s22gm_projectionExtension p (ψx w)) =ᶠ[𝓝 z] fun w => (chartAt ℂ x).symm w)
    (hψy : AnalyticAt ℂ ψy ((chartAt ℂ y ∘ (chartAt ℂ x).symm) z))
    (hHy : ψy ((chartAt ℂ y ∘ (chartAt ℂ x).symm) z) ∈ upperHalf)
    (hey : (fun w => s22gm_projectionExtension p (ψy w)) =ᶠ[𝓝 ((chartAt ℂ y ∘ (chartAt ℂ x).symm) z)]
      fun w => (chartAt ℂ y).symm w) :
    (fderiv ℝ (fun w => ρ ((chartAt ℂ x).symm w)) z 1 * α x z I -
        fderiv ℝ (fun w => ρ ((chartAt ℂ x).symm w)) z I * α x z 1) =
      ‖deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) z‖ ^ 2 *
        (fderiv ℝ (fun w => ρ ((chartAt ℂ y).symm w)) ((chartAt ℂ y ∘ (chartAt ℂ x).symm) z) 1 *
            α y ((chartAt ℂ y ∘ (chartAt ℂ x).symm) z) I -
          fderiv ℝ (fun w => ρ ((chartAt ℂ y).symm w)) ((chartAt ℂ y ∘ (chartAt ℂ x).symm) z) I *
            α y ((chartAt ℂ y ∘ (chartAt ℂ x).symm) z) 1) ∧
    s22gc_areaDensity ψx z =
      s22gc_areaDensity ψy ((chartAt ℂ y ∘ (chartAt ℂ x).symm) z) *
        ‖deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) z‖ ^ 2 := by
  set τ : ℂ → ℂ := chartAt ℂ y ∘ (chartAt ℂ x).symm with hτ
  set u := (chartAt ℂ x).symm z with hu
  have hux : u ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
  have hzc : chartAt ℂ x u = z := (chartAt ℂ x).right_inv hz
  have hτan : AnalyticAt ℂ τ z := by
    have := Jacobians.Dolbeault.transition_analyticAt_of_mem hux hzy
    rwa [hzc] at this
  refine ⟨?_, ?_⟩
  · set a := deriv τ z with ha
    have t1 := s22gb_tensor_law hp hq hα hsm x y hz hzy hm ho hmy hoy 1
    have tI := s22gb_tensor_law hp hq hα hsm x y hz hzy hm ho hmy hoy I
    rw [← hτ, ← ha] at t1 tI
    simp only [mul_one, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, zero_add] at t1 tI
    rw [s22gb_fderiv_transition ρ hρ x y hz hzy 1, s22gb_fderiv_transition ρ hρ x y hz hzy I,
      ← hτ, ← ha]
    have := s22gb_wedge_algebra a (fderiv ℝ (fun w => ρ ((chartAt ℂ y).symm w)) (τ z))
      (α y (τ z) 1) (α y (τ z) I) (α x z 1) (α x z I) (by linarith [t1]) (by linarith [tI])
    exact this
  · have hlift : s22gc_areaDensity ψx z = s22gc_areaDensity (ψy ∘ τ) z := by
      refine s22gc_lift_areaDensity_eq hp (ψ := ψy ∘ τ) (χ := ψx) (hψy.comp hτan).differentiableAt
        hψx.continuousAt hHy hHx ?_
      have h1 := hτan.continuousAt.tendsto.eventually hey
      filter_upwards [h1, ((chartAt ℂ x).continuousAt_symm hz).preimage_mem_nhds
        ((chartAt ℂ y).open_source.mem_nhds hzy), hex] with w a b c
      have : (chartAt ℂ y).symm (τ w) = (chartAt ℂ x).symm w := (chartAt ℂ y).left_inv b
      exact (a.trans this).trans c.symm
    rw [hlift, s22gc_areaDensity_comp hψy.differentiableAt hτan.differentiableAt]

end GaussBonnetInv

end LiZhongQC
