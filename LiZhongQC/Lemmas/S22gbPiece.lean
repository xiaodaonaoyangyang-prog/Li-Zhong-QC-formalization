import LiZhongQC.Lemmas.S22gbAssembly
import LiZhongQC.Lemmas.S22gbStrips

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u

section GaussBonnetPiece

variable {S : Type u} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S] [CompactSpace S] [IsManifold 𝓘(ℂ) ω S]

theorem s22gb_rectO_isOpen (p q : ℂ) : IsOpen (wv_rectO p q) := by
  have : wv_rectO p q = Complex.re ⁻¹' Ioo p.re q.re ∩ Complex.im ⁻¹' Ioo p.im q.im := by
    ext z
    simp [wv_rectO, Complex.mem_reProdIm]
  rw [this]
  exact (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)

theorem s22gb_rectK_measurable (p q : ℂ) : MeasurableSet (wv_rectK p q) :=
  (wv_isCompact_rectK p q).isClosed.measurableSet

/-- Sets that differ by a null set have the same integral. -/
theorem s22gb_ae_eq_of_null {s t : Set ℂ} (hst : s ⊆ t) (h0 : volume (t \ s) = 0) :
    s =ᵐ[volume] t := by
  rw [ae_eq_set]
  refine ⟨by simp [Set.diff_eq_empty.2 hst], h0⟩

/-- Stokes value of a piece that sees no singularity: it vanishes. -/
theorem s22gb_piece_full {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) {q : S → ℂ → ℂ}
    {α : S → ℂ → ℂ → ℝ}
    (hα : ∀ (x : S) (z : ℂ), z ∈ (chartAt ℂ x).target →
      AnalyticAt ℂ (q x) z → q x z ≠ 0 →
      ∀ ψ : ℂ → ℂ, AnalyticAt ℂ ψ z → deriv ψ z ≠ 0 → ψ z ∈ upperHalf →
        (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z] (fun w => (chartAt ℂ x).symm w) →
        α x =ᶠ[𝓝 z] s22cd_canonicalGauge ψ (q x))
    (hsm : ∀ (x : S) (z : ℂ), z ∈ (chartAt ℂ x).target → MeromorphicAt (q x) z →
      meromorphicOrderAt (q x) z = 0 → ∀ v : ℂ, ContDiffAt ℝ 1 (fun w => α x w v) z)
    (ρ : S → ℝ) (hρ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) ρ) (x : S) {a b : ℂ}
    (hre : a.re ≤ b.re) (him : a.im ≤ b.im) {ψ : ℂ → ℂ}
    (hlift : ∀ z ∈ wv_rectK a b, z ∈ (chartAt ℂ x).target ∧ AnalyticAt ℂ ψ z ∧
      deriv ψ z ≠ 0 ∧ ψ z ∈ upperHalf ∧
      (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z] fun w => (chartAt ℂ x).symm w)
    (hreg : ∀ z ∈ wv_rectK a b, MeromorphicAt (q x) z ∧ meromorphicOrderAt (q x) z = 0)
    (hρ0 : ∀ z ∈ wv_rectF a b, ρ ((chartAt ℂ x).symm z) = 0) :
    (∫ z in wv_rectO a b, (ρ ((chartAt ℂ x).symm z) * s22gc_areaDensity ψ z +
      (fderiv ℝ (fun w => ρ ((chartAt ℂ x).symm w)) z 1 * α x z I -
        fderiv ℝ (fun w => ρ ((chartAt ℂ x).symm w)) z I * α x z 1))) = 0 := by
  have hu : ∀ z ∈ wv_rectK a b, ContDiffAt ℝ 1 (fun w => ρ ((chartAt ℂ x).symm w)) z := fun z hz =>
    ((s22gb_rho_contDiffAt ρ hρ x (hlift z hz).1).of_le (by exact_mod_cast le_top))
  have hst := s22gb_rect_stokes (fun w => ρ ((chartAt ℂ x).symm w)) (α x) a b hre him hu
    (fun z hz => hsm x z (hlift z hz).1 (hreg z hz).1 (hreg z hz).2 1)
    (fun z hz => hsm x z (hlift z hz).1 (hreg z hz).1 (hreg z hz).2 I)
  have hbd : s22cd_rectBoundary (fun ζ v => ρ ((chartAt ℂ x).symm ζ) * α x ζ v) a b = 0 :=
    s22cd_rectBoundary_zero (fun ζ hζ v => by simp [hρ0 ζ hζ])
  rw [hbd] at hst
  have hO : wv_rectO a b ⊆ wv_rectK a b := fun z hz => by
    rw [s22gb_mem_rectO] at hz
    rw [s22gb_mem_rectK hre him]
    exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2.1.le, hz.2.2.le⟩
  have hae : wv_rectO a b =ᵐ[volume] wv_rectK a b :=
    s22gb_ae_eq_of_null hO (s22gb_frame_null a b hre him)
  rw [← hst, ← setIntegral_congr_set hae]
  refine setIntegral_congr_fun (s22gb_rectO_isOpen a b).measurableSet fun z hz => ?_
  obtain ⟨ht, han, hd, hH, he⟩ := hlift z (hO hz)
  have hE := s22gb_exterior_eq hp hα hsm x ht (hreg z (hO hz)).1 (hreg z (hO hz)).2 han hd hH he
  show _ = ρ ((chartAt ℂ x).symm z) * (fderiv ℝ (fun w => α x w I) z 1 -
      fderiv ℝ (fun w => α x w 1) z I) + _
  rw [hE]

/-- Stokes value of a piece around a hole: minus the boundary period of the gauge. -/
theorem s22gb_piece_hole {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) {q : S → ℂ → ℂ}
    {α : S → ℂ → ℂ → ℝ}
    (hα : ∀ (x : S) (z : ℂ), z ∈ (chartAt ℂ x).target →
      AnalyticAt ℂ (q x) z → q x z ≠ 0 →
      ∀ ψ : ℂ → ℂ, AnalyticAt ℂ ψ z → deriv ψ z ≠ 0 → ψ z ∈ upperHalf →
        (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z] (fun w => (chartAt ℂ x).symm w) →
        α x =ᶠ[𝓝 z] s22cd_canonicalGauge ψ (q x))
    (hsm : ∀ (x : S) (z : ℂ), z ∈ (chartAt ℂ x).target → MeromorphicAt (q x) z →
      meromorphicOrderAt (q x) z = 0 → ∀ v : ℂ, ContDiffAt ℝ 1 (fun w => α x w v) z)
    (ρ : S → ℝ) (hρ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) ρ) (x : S) {a b c d : ℂ}
    (h1 : a.re < c.re) (h2 : c.re < d.re) (h3 : d.re < b.re)
    (h4 : a.im < c.im) (h5 : c.im < d.im) (h6 : d.im < b.im) {ψ : ℂ → ℂ}
    (hlift : ∀ z ∈ wv_rectK a b, z ∈ (chartAt ℂ x).target ∧ AnalyticAt ℂ ψ z ∧
      deriv ψ z ≠ 0 ∧ ψ z ∈ upperHalf ∧
      (fun w => s22gm_projectionExtension p (ψ w)) =ᶠ[𝓝 z] fun w => (chartAt ℂ x).symm w)
    (hreg : ∀ z ∈ wv_rectK a b \ wv_rectO c d,
      MeromorphicAt (q x) z ∧ meromorphicOrderAt (q x) z = 0)
    (hρ0 : ∀ z ∈ wv_rectF a b, ρ ((chartAt ℂ x).symm z) = 0)
    (hρ1 : ∀ z ∈ wv_rectF c d, ρ ((chartAt ℂ x).symm z) = 1) :
    (∫ z in wv_rectO a b \ wv_rectK c d, (ρ ((chartAt ℂ x).symm z) * s22gc_areaDensity ψ z +
      (fderiv ℝ (fun w => ρ ((chartAt ℂ x).symm w)) z 1 * α x z I -
        fderiv ℝ (fun w => ρ ((chartAt ℂ x).symm w)) z I * α x z 1))) =
      -s22cd_rectBoundary (α x) c d := by
  have hab1 : a.re ≤ b.re := by linarith
  have hab2 : a.im ≤ b.im := by linarith
  have hKsub : ∀ z, z ∈ wv_rectK a b \ wv_rectO c d → z ∈ wv_rectK a b := fun z hz => hz.1
  have hu : ∀ z ∈ wv_rectK a b \ wv_rectO c d,
      ContDiffAt ℝ 1 (fun w => ρ ((chartAt ℂ x).symm w)) z := fun z hz =>
    ((s22gb_rho_contDiffAt ρ hρ x (hlift z hz.1).1).of_le (by exact_mod_cast le_top))
  have hst := s22gb_annulus_stokes (fun w => ρ ((chartAt ℂ x).symm w)) (α x) h1 h2 h3 h4 h5 h6 hu
    (fun z hz => hsm x z (hlift z hz.1).1 (hreg z hz).1 (hreg z hz).2 1)
    (fun z hz => hsm x z (hlift z hz.1).1 (hreg z hz).1 (hreg z hz).2 I) hρ0 hρ1
  have hOK : ∀ (p q : ℂ), p.re ≤ q.re → p.im ≤ q.im → wv_rectO p q ⊆ wv_rectK p q := by
    intro p q hre him z hz
    rw [s22gb_mem_rectO] at hz
    rw [s22gb_mem_rectK hre him]
    exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2.1.le, hz.2.2.le⟩
  have hsub : wv_rectO a b \ wv_rectK c d ⊆ wv_rectK a b \ wv_rectO c d := by
    intro z hz
    exact ⟨hOK a b hab1 hab2 hz.1, fun h => hz.2 (hOK c d h2.le h5.le h)⟩
  have hnull : volume ((wv_rectK a b \ wv_rectO c d) \ (wv_rectO a b \ wv_rectK c d)) = 0 := by
    refine measure_mono_null ?_ (measure_union_null (s22gb_frame_null a b hab1 hab2)
      (s22gb_frame_null c d h2.le h5.le))
    intro z hz
    by_cases hzO : z ∈ wv_rectO a b
    · right
      have : z ∈ wv_rectK c d := by
        by_contra hn
        exact hz.2 ⟨hzO, hn⟩
      exact ⟨this, hz.1.2⟩
    · left
      exact ⟨hz.1.1, hzO⟩
  have hae := s22gb_ae_eq_of_null hsub hnull
  rw [← hst, setIntegral_congr_set hae]
  refine setIntegral_congr_fun ((s22gb_rectK_measurable a b).diff
    (s22gb_rectO_isOpen c d).measurableSet) fun z hz => ?_
  obtain ⟨ht, han, hd, hH, he⟩ := hlift z hz.1
  have hE := s22gb_exterior_eq hp hα hsm x ht (hreg z hz).1 (hreg z hz).2 han hd hH he
  rw [hE]

end GaussBonnetPiece

end LiZhongQC
