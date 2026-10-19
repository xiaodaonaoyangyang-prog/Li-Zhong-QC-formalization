import LiZhongQC.Lemmas.StrebelGammaG1cSupport
import LiZhongQC.Lemmas.S36G1dDomains

/-! G1c finite coset tiling producers. Source-only candidate, not compiled. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

variable {Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Uniqueness in a right transversal compares representatives after a subgroup multiplier. -/
theorem s36c_right_coset_index {d : ℕ}
    (T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℝ) (hT : ∀ i, T i ∈ Γ)
    (hcos : ∀ γ ∈ Γ, ∃! i : Fin d, ∃ δ ∈ Δ, γ = δ * T i)
    {i j : Fin d} {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hδ : δ ∈ Δ) (heq : δ * T i = T j) : i = j := by
  exact s36e_countable_right_coset_index T hT hcos hδ heq

/-- A.e. uniqueness modulo sign becomes true coset uniqueness when Delta contains Gamma's kernel. -/
theorem s36c_signed_coset_rigidity (hle : Δ ≤ Γ)
    (hker : Γ ⊓ Subgroup.zpowers (-1) ≤ Δ)
    {d : ℕ} (T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hT : ∀ i, T i ∈ Γ)
    (hcos : ∀ γ ∈ Γ, ∃! i : Fin d, ∃ δ ∈ Δ, γ = δ * T i)
    {i j : Fin d} {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hδ : δ ∈ Δ)
    (heq : (T j)⁻¹ * δ = (T i)⁻¹ ∨ (T j)⁻¹ * δ = -((T i)⁻¹)) :
    i = j ∧ (δ = 1 ∨ δ = -1) := by
  exact s36e_countable_signed_coset_rigidity hle hker T hT hcos hδ heq

/-- Gamma's a.e. uniqueness simultaneously separates the finite tiles and their Delta translates. -/
theorem s36c_ae_tile_rigidity (hΓ : IsFuchsian Γ) (hle : Δ ≤ Γ)
    (hker : Γ ⊓ Subgroup.zpowers (-1) ≤ Δ)
    {d : ℕ} (T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hT : ∀ i, T i ∈ Γ)
    (hcos : ∀ γ ∈ Γ, ∃! i : Fin d, ∃ δ ∈ Δ, γ = δ * T i)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) :
    ∀ᵐ z ∂(volume.restrict upperHalf), ∀ (i j : Fin d),
      ∀ δ ∈ Δ, z ∈ h36p_m (T i) '' F →
      h36p_m δ z ∈ h36p_m (T j) '' F → i = j ∧ (δ = 1 ∨ δ = -1) := by
  exact s36e_countable_ae_tile_rigidity hΓ hle hker T hT hcos hF

/-- Distinct right-coset tiles have null intersection, even with elliptic points in Gamma. -/
theorem s36c_tiles_null_inter (hΓ : IsFuchsian Γ) (hle : Δ ≤ Γ)
    (hker : Γ ⊓ Subgroup.zpowers (-1) ≤ Δ)
    {d : ℕ} (T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hT : ∀ i, T i ∈ Γ)
    (hcos : ∀ γ ∈ Γ, ∃! i : Fin d, ∃ δ ∈ Δ, γ = δ * T i)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (i j : Fin d) (hij : i ≠ j) :
    volume ((h36p_m (T i) '' F) ∩ (h36p_m (T j) '' F)) = 0 := by
  exact s36e_countable_tiles_null_inter hΓ hle hker T hT hcos hF i j hij

/-- The finite union of right-coset tiles meets every Delta orbit. -/
theorem s36c_tiles_cover (hle : Δ ≤ Γ)
    {d : ℕ} (T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hcos : ∀ γ ∈ Γ, ∃! i : Fin d, ∃ δ ∈ Δ, γ = δ * T i)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (τ : UpperHalfPlane) :
    ∃ δ ∈ Δ, ((δ • τ : UpperHalfPlane) : ℂ) ∈ ⋃ i : Fin d, h36p_m (T i) '' F := by
  exact s36e_countable_tiles_cover hle T hcos hF τ

/-- A Mobius image of an open subset of the upper half-plane is open in the plane. -/
theorem s36c_mobius_image_open (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ upperHalf) :
    IsOpen (h36p_m γ '' U) := by
  rw [h36p_a_image_eq γ hUH, inter_comm]
  have hc : ContinuousOn (h36p_m γ⁻¹) upperHalf := by
    intro z hz
    exact (h36p_m_hasDerivAt γ⁻¹ hz).continuousAt.continuousWithinAt
  exact hc.isOpen_inter_preimage isOpen_upperHalf hU

/-- A finite right transversal tiles a fundamental domain for Delta.
The full central kernel condition prevents coincident tiles coming from opposite signs. -/
theorem s36c_fundamental_tiling (hΓ : IsFuchsian Γ) (hle : Δ ≤ Γ)
    (hker : Γ ⊓ Subgroup.zpowers (-1) ≤ Δ)
    {d : ℕ} (T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hT : ∀ i, T i ∈ Γ)
    (hcos : ∀ γ ∈ Γ, ∃! i : Fin d, ∃ δ ∈ Δ, γ = δ * T i)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) :
    IsFundamentalDomainH Δ (⋃ i : Fin d, h36p_m (T i) '' F) ∧
      (∀ i, MeasurableSet (h36p_m (T i) '' F)) ∧
      (∀ i j : Fin d, i ≠ j →
        volume ((h36p_m (T i) '' F) ∩ (h36p_m (T j) '' F)) = 0) := by
  exact s36e_countable_fundamental_tiling hΓ hle hker T hT hcos hF

/-- Exact scaling for any nonnegative invariant density, with no finiteness assumption on its integral.
All outer integral terms are parenthesized so the scalar never enters an unintended binder. -/
theorem s36c_density_scaling (hΓ : IsFuchsian Γ) (hle : Δ ≤ Γ)
    (hker : Γ ⊓ Subgroup.zpowers (-1) ≤ Δ)
    {d : ℕ} (T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hT : ∀ i, T i ∈ Γ)
    (hcos : ∀ γ ∈ Γ, ∃! i : Fin d, ∃ δ ∈ Δ, γ = δ * T i)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (W : ℂ → ℝ≥0∞)
    (hW : ∀ γ ∈ Γ, ∀ᵐ z ∂(volume.restrict upperHalf),
      W (h36p_m γ z) * ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4) = W z) :
    (∫⁻ z in ⋃ i : Fin d, h36p_m (T i) '' F, W z) =
      (d : ℝ≥0∞) * (∫⁻ z in F, W z) := by
  obtain ⟨hE, hm, hd⟩ := s36c_fundamental_tiling hΓ hle hker T hT hcos hF
  have htile : ∀ i : Fin d, (∫⁻ z in h36p_m (T i) '' F, W z) = ∫⁻ z in F, W z := by
    intro i
    rw [h36p_b_lintegral_image (T i) hF.2.1 hF.1]
    exact lintegral_congr_ae (ae_restrict_of_ae_restrict_of_subset hF.1 (hW (T i) (hT i)))
  calc (∫⁻ z in ⋃ i : Fin d, h36p_m (T i) '' F, W z)
      = ∑' i : Fin d, ∫⁻ z in h36p_m (T i) '' F, W z :=
        lintegral_iUnion₀ (fun i => (hm i).nullMeasurableSet) (fun i j hij => hd i j hij) W
    _ = ∑' _i : Fin d, ∫⁻ z in F, W z := tsum_congr htile
    _ = (d : ℝ≥0∞) * (∫⁻ z in F, W z) := by
      simp [tsum_fintype, nsmul_eq_mul]

/-- Exact area scaling and its finite-norm consequence use the installed one-tile equality. -/
theorem s36c_area_scaling (hΓ : IsFuchsian Γ) (hle : Δ ≤ Γ)
    (hker : Γ ⊓ Subgroup.zpowers (-1) ≤ Δ)
    {d : ℕ} (T : Fin d → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hT : ∀ i, T i ∈ Γ)
    (hcos : ∀ γ ∈ Γ, ∃! i : Fin d, ∃ δ ∈ Δ, γ = δ * T i)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    {φ : ℂ → ℂ} (hφ : φ ∈ integrableAutomorphicQD Γ F) :
    phiArea φ (⋃ i : Fin d, h36p_m (T i) '' F) = (d : ℝ≥0∞) * phiArea φ F ∧
      phiArea φ (⋃ i : Fin d, h36p_m (T i) '' F) < ⊤ := by
  obtain ⟨hE, hm, hd⟩ := s36c_fundamental_tiling hΓ hle hker T hT hcos hF
  have harea : phiArea φ (⋃ i : Fin d, h36p_m (T i) '' F) =
      (d : ℝ≥0∞) * phiArea φ F := by
    change (∫⁻ z in ⋃ i : Fin d, h36p_m (T i) '' F, ENNReal.ofReal ‖φ z‖) =
      (d : ℝ≥0∞) * (∫⁻ z in F, ENNReal.ofReal ‖φ z‖)
    calc (∫⁻ z in ⋃ i : Fin d, h36p_m (T i) '' F, ENNReal.ofReal ‖φ z‖)
        = ∑' i : Fin d, ∫⁻ z in h36p_m (T i) '' F, ENNReal.ofReal ‖φ z‖ :=
          lintegral_iUnion₀ (fun i => (hm i).nullMeasurableSet)
            (fun i j hij => hd i j hij) (fun z => ENNReal.ofReal ‖φ z‖)
      _ = ∑' _i : Fin d, ∫⁻ z in F, ENNReal.ofReal ‖φ z‖ :=
        tsum_congr fun i => h36p_lintegral_image_m hφ (hT i) hF.2.1 hF.1
      _ = (d : ℝ≥0∞) * (∫⁻ z in F, ENNReal.ofReal ‖φ z‖) := by
        simp [tsum_fintype, nsmul_eq_mul]
  refine ⟨harea, ?_⟩
  rw [harea]
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top d) hφ.2.1

end LiZhongQC
