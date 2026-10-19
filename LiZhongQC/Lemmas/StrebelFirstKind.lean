import LiZhongQC.Ch11.S36_Hamilton
import LiZhongQC.Lemmas.HyperbolicSurfaceArea
import LiZhongQC.Lemmas.UniformizedUniqueness
import LiZhongQC.Lemmas.SchottkyDirectD3a
import LiZhongQC.Lemmas.StrebelGammaTransport
import LiZhongQC.Lemmas.StrebelSurfaceLambda
import LiZhongQC.Lemmas.StrebelGammaMapFacts

/-!
Shared chart measurability and the existing finite-surface-to-G1a transport argument.
The original frozen str_g1a still requires the actual ft_foundation producer; this
module proves only the reusable implication from that explicit finite-surface data.
No foundation stub and no original book statement is declared here.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

/-- A function that is Borel in every chart on a Lindelöf surface is measurable. -/
theorem str_measurable_borel {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [MeasurableSpace S]
    [BorelSpace S] [Nonempty S] (hL : IsLindelof (univ : Set S)) {U : S → ℝ≥0∞}
    (hU : s26v_IsBorelInCharts U) : Measurable U := by
  obtain ⟨x, P, hP, -, hPm⟩ := str_exists_partition hL (fun s => (chartAt ℂ s).source)
    (fun s => (chartAt ℂ s).open_source) (fun s => mem_chart_source ℂ s) (fun s => subset_rfl)
  intro B hB
  have hcov : U ⁻¹' B = ⋃ i, (P i ∩ U ⁻¹' B) := by
    ext s
    have : s ∈ ⋃ i, P i := by rw [hP.2.2]; exact mem_univ s
    obtain ⟨i, hi⟩ := mem_iUnion.1 this
    simp only [mem_preimage, mem_iUnion, mem_inter_iff]
    exact ⟨fun h => ⟨i, hi, h⟩, fun h => by
      rcases h with ⟨j, hj, hU⟩
      exact hU⟩
  rw [hcov]
  refine MeasurableSet.iUnion fun i => ?_
  obtain ⟨g, hg, hgU⟩ := hU (x i)
  have hsub : P i ⊆ (chartAt ℂ (x i)).source := (hP.1 i).1
  have hr : Measurable (fun s : (chartAt ℂ (x i)).source => chartAt ℂ (x i) s) :=
    (continuousOn_iff_continuous_restrict.1 (chartAt ℂ (x i)).continuousOn).measurable
  have hsrc : MeasurableSet (chartAt ℂ (x i)).source := (chartAt ℂ (x i)).open_source.measurableSet
  have hT : MeasurableSet ({s : (chartAt ℂ (x i)).source | chartAt ℂ (x i) s ∈ g ⁻¹' B} ∩
      Subtype.val ⁻¹' P i) :=
    (hr (hg hB)).inter (measurable_subtype_coe (hPm i))
  have himg := hsrc.subtype_image hT
  convert himg using 1
  ext s
  constructor
  · rintro ⟨hs, hUB⟩
    refine ⟨⟨s, hsub hs⟩, ⟨?_, hs⟩, rfl⟩
    have := hgU (chartAt ℂ (x i) s) ((chartAt ℂ (x i)).map_source (hsub hs))
    rw [(chartAt ℂ (x i)).left_inv (hsub hs)] at this
    show g (chartAt ℂ (x i) s) ∈ B
    rw [← this]; exact hUB
  · rintro ⟨⟨s', hs0⟩, ⟨hgB, hs'⟩, rfl⟩
    refine ⟨hs', ?_⟩
    have := hgU (chartAt ℂ (x i) s') ((chartAt ℂ (x i)).map_source hs0)
    rw [(chartAt ℂ (x i)).left_inv hs0] at this
    show U s' ∈ B
    rw [this]; exact hgB

/-- Transport the finite-surface lambda inequality to the supplied group fundamental domain.
The existence input is exactly the output of the frozen first-kind foundation theorem. -/
theorem str_g1a_of_foundation {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ)
    (hfoundation : ∃ (g n : ℕ) (S : Type) (_ : TopologicalSpace S) (_ : ChartedSpace ℂ S)
      (_ : T2Space S) (_ : ConnectedSpace S) (_ : IsManifold 𝓘(ℂ) ω S) (p : UpperHalfPlane → S),
      IsUniformization Γ p ∧ IsFiniteType S g n 0 ∧ ¬ IsExceptionalType g n 0)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (μ ν : BeltramiGamma Γ)
    (hrel : teichSetoidGamma Γ ν μ) {φ : ℂ → ℂ}
    (hφ : φ ∈ integrableAutomorphicQD Γ F) :
    phiArea φ F ≤ ∫⁻ z in F, ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal
      (lambdaStretchPlane φ φ (Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1) z) := by
  classical
  obtain ⟨g₀, n, S, _, _, _, _, _, p, hp, hft, hex⟩ := hfoundation
  obtain ⟨F₀⟩ := hft
  letI : MeasurableSpace S := borel S
  haveI : BorelSpace S := ⟨rfl⟩
  have : Nonempty S := ⟨p UpperHalfPlane.I⟩
  obtain ⟨K, hgK, hgimg, hcomm⟩ := str_g_facts μ ν hrel
  set g := Function.invFunOn (fMuSym ν.1.1) upperHalf ∘ fMuSym μ.1.1 with hg
  obtain ⟨h, hhK, hhom, hh⟩ := str_descend hp hgK hgimg hcomm
  have hφd := hφ.1
  have hφΓ := hφ.2.2
  obtain ⟨q, hqH, hqφ⟩ := utm_x_descent hp hφd hφΓ
  have hq : q ∈ admissibleQDInterior F₀ := s82dx_integrable_admissible F₀ hp hΓ hF hφ hqH hqφ
  have hFH : F ⊆ upperHalf := hF.1
  by_cases hq0 : q = 0
  · -- `φ = 0` on `ℍ`
    have hφ0 : ∀ z ∈ F, φ z = 0 := fun z hz => by
      rw [← hqφ z (hFH hz)]
      simp [utm_liftQD, hq0]
    have : phiArea φ F = 0 := by
      unfold phiArea
      refine (setLIntegral_congr_fun hF.2.1 (g := fun _ => (0 : ℝ≥0∞))
        (fun z hz => by simp [hφ0 z hz])).trans (by simp)
    rw [this]; exact bot_le
  have hsurf := str_surface_lambda hex F₀ hq hqH hq0 ⟨K, hhK⟩ hhom
  have hL : IsLindelof (univ : Set S) := by
    have h1 := (isLindelof_univ (X := UpperHalfPlane)).image hp.1.continuous
    rwa [image_univ, Function.Surjective.range_eq hp.2.2.1] at h1
  have hmeas : Measurable (s26v_lam q h) := str_measurable_borel hL (s26v_lam_borel hqH h)
  have hT1 := str_surfaceIntegral_eq hp hΓ hF hqH hφd hφΓ hqφ (U := fun _ => 1) measurable_const
  have hT2 := str_surfaceIntegral_eq hp hΓ hF hqH hφd hφΓ hqφ (U := s26v_lam q h) hmeas
  have hnorm : quadDiffNorm q = phiArea φ F := by
    simp only [quadDiffNorm, phiArea]
    rw [hT1]
    simp
  rw [← hnorm]
  refine hsurf.trans (le_of_eq ?_)
  rw [str_surfaceIntegral_lam hqH h, hT2]
  refine setLIntegral_congr_fun hF.2.1 (fun z hz => ?_)
  rw [str_lambda hp hqH hqφ hgK hgimg h hh (hFH hz), mul_comm]

end LiZhongQC
