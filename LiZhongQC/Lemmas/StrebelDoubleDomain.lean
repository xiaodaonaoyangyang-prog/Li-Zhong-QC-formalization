import LiZhongQC.Ch11.S36_Hamilton

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- The limit set of a Fuchsian group lies in `ℝ̂` (a limit point is a limit of `γₙ i`, and a subsequence of `γₙ`
converges to a real attracting point away from a real repelling point). -/
theorem s36a_limit_real (hΓ : IsFuchsian Γ) : fuchsianLimitSet Γ ⊆ extRealLine := by
  intro p hp
  obtain ⟨γs, hinj, hlim⟩ := k22_t_limitSet_subset_orbitLim (k24_c_I_not_mem_limitSet hΓ) hp
  choose γr hγrΓ hγr using fun n => Subgroup.mem_map.1 (γs n).2
  have hnorm := k24_c_norm_tendsto hΓ (fun n => (γs n : Matrix.SpecialLinearGroup (Fin 2) ℂ))
    (Subtype.val_injective.comp hinj) (fun n => (γs n).2)
  have hreal : ∀ n (i j : Fin 2), ((γs n : Matrix.SpecialLinearGroup (Fin 2) ℂ) i j).im = 0 := by
    intro n i j
    rw [← hγr n, k24_c_map_apply, Complex.ofReal_im]
  obtain ⟨φ, a, b, hφ, hA, -, haR, hbR⟩ :=
    k22_convergence_real (fun n => (γs n : Matrix.SpecialLinearGroup (Fin 2) ℂ)) hnorm hreal
  have hIb : ((Complex.I : ℂ) : ExtPlane) ≠ b := by
    rintro rfl
    rcases hbR with ⟨z, hz, hzI⟩ | h
    · rw [OnePoint.coe_injective hzI] at hz
      simp at hz
    · exact OnePoint.coe_ne_infty _ h
  have hta : Tendsto (fun n => mobiusSL (γs (φ n) : Matrix.SpecialLinearGroup (Fin 2) ℂ)
      ((Complex.I : ℂ) : ExtPlane)) atTop (𝓝 a) := by
    rw [tendsto_def]
    intro U hU
    have h1 := hA {((Complex.I : ℂ) : ExtPlane)} isCompact_singleton
      (fun h => hIb (mem_singleton_iff.1 h).symm) U hU
    filter_upwards [h1] with n hn
    exact hn ⟨_, mem_singleton _, rfl⟩
  have hp' := hlim.comp hφ.tendsto_atTop
  rw [tendsto_nhds_unique hp' hta]
  exact haR

/-- The real Möbius action on `ℂ̄` at a finite point with non-vanishing denominator. -/
theorem s36a_mext (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (h : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0) :
    mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ) (z : ExtPlane) = ((h36p_m γ z : ℂ) : ExtPlane) := by
  rw [k24_c_mobiusSL_map, mobiusExt_coe h]
  rfl

/-- The real Möbius action on `ℂ̄` at a pole. -/
theorem s36a_mext0 (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (h : (γ 1 0 : ℂ) * z + γ 1 1 = 0) :
    mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ) (z : ExtPlane) = extInf := by
  rw [k24_c_mobiusSL_map, mobiusExt_coe_of_eq_zero h]

/-- The real Möbius action on `ℂ̄` at `∞`. -/
theorem s36a_mextinf (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (γ 1 0 ≠ 0 → mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ) extInf =
      ((((γ 0 0 / γ 1 0 : ℝ)) : ℂ) : ExtPlane)) ∧
    (γ 1 0 = 0 → mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ) extInf = extInf) := by
  constructor
  · intro h
    rw [k24_c_mobiusSL_map, mobiusExt_infty_of_ne (by exact_mod_cast h)]
    push_cast
    rfl
  · intro h
    rw [k24_c_mobiusSL_map, mobiusExt_infty_of_eq (by exact_mod_cast h)]

/-- Entries of the inverse in `SL(2, ℝ)`. -/
theorem s36a_inv_entries (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 = γ 1 1 ∧
      (γ⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 = -γ 1 0 := by
  constructor <;> simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

/-- Consequences of the description of `Ω'(E)`: it contains `ℍ ∪ 𝕃`, is `conj`-invariant and `Γ`-invariant (with
non-vanishing denominators). -/
theorem s36a_omega (hΓ : IsFuchsian Γ) {E : Finset ℝ} {Ω : Set ℂ}
    (hΩ : ∀ z : ℂ, z ∈ Ω ↔ ((z : ExtPlane) ∉ fuchsianLimitSet Γ ∧
      (∀ γ ∈ Γ, ∀ s ∈ E, (γ 1 0 : ℝ) * s + γ 1 1 ≠ 0 → z ≠ h36p_m γ (s : ℂ)) ∧
      (∀ γ ∈ Γ, (γ 1 0 : ℝ) ≠ 0 → z ≠ ((γ 0 0 / γ 1 0 : ℝ) : ℂ)))) :
    (∀ z : ℂ, z.im ≠ 0 → z ∈ Ω) ∧ (∀ z ∈ Ω, conj z ∈ Ω) ∧
      ∀ γ ∈ Γ, ∀ z ∈ Ω, (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 ∧ h36p_m γ z ∈ Ω := by
  have hΛR := s36a_limit_real hΓ
  have hreal_m : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (s : ℝ), (h36p_m γ (s : ℂ)).im = 0 := by
    intro γ s
    show (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (s : ℂ)).im = 0
    rw [b33_e_mobius_real]
    exact Complex.ofReal_im _
  have h1 : ∀ z : ℂ, z.im ≠ 0 → z ∈ Ω := by
    intro z hz
    rw [hΩ]
    refine ⟨fun h => ?_, fun γ _ s _ _ h => ?_, fun γ _ _ h => ?_⟩
    · rcases hΛR h with ⟨w, hw, hwz⟩ | h'
      · rw [OnePoint.coe_injective hwz] at hw
        exact hz hw
      · exact OnePoint.coe_ne_infty _ h'
    · apply hz
      rw [h]
      exact hreal_m γ s
    · apply hz
      rw [h]
      exact Complex.ofReal_im _
  have hconjm : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w : ℂ), h36p_m γ (conj w) = conj (h36p_m γ w) :=
    fun γ w => b33_e_mobius_conj γ w
  refine ⟨h1, fun z hz => ?_, fun γ hγ z hz => ?_⟩
  · by_cases him : z.im = 0
    · rw [Complex.conj_eq_iff_im.2 him]
      exact hz
    · exact h1 _ (by rw [Complex.conj_im]; exact neg_ne_zero.2 him)
  obtain ⟨hzΛ, hzE, hzI⟩ := (hΩ z).1 hz
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rwa [Matrix.det_fin_two] at this
  have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := by
    intro h0
    have hc : γ 1 0 ≠ 0 := by
      intro hc
      rw [hc] at h0
      simp only [Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_eq_zero] at h0
      rw [hc, h0] at hdet
      simp at hdet
    obtain ⟨hi0, hi1⟩ := s36a_inv_entries γ
    refine hzI γ⁻¹ (Γ.inv_mem hγ) (by rw [hi1]; exact neg_ne_zero.2 hc) ?_
    rw [hi0, hi1]
    have hc' : (γ 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
    push_cast
    field_simp
    linear_combination h0
  refine ⟨hden, ?_⟩
  by_cases him : z.im = 0
  swap
  · refine h1 _ ?_
    rcases lt_or_gt_of_ne him with hlt | hgt
    · have hcz : conj z ∈ upperHalf := by
        show 0 < (conj z).im
        rw [Complex.conj_im]
        linarith
      have h2 := h36p_m_mem γ hcz
      rw [hconjm] at h2
      have : 0 < (conj (h36p_m γ z)).im := h2
      rw [Complex.conj_im] at this
      linarith
    · exact ne_of_gt (h36p_m_mem γ hgt)
  -- `z` is an ordinary real point; `γ z` is again ordinary, and off the removed orbits
  set M : Matrix.SpecialLinearGroup (Fin 2) ℝ →*
      Matrix.SpecialLinearGroup (Fin 2) ℂ := Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) with hM
  have hEz : mobiusSL (M γ) (z : ExtPlane) = ((h36p_m γ z : ℂ) : ExtPlane) := s36a_mext γ hden
  have hback : ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ w : ExtPlane,
      ((h36p_m γ z : ℂ) : ExtPlane) = mobiusSL (M δ) w → (z : ExtPlane) = mobiusSL (M (γ⁻¹ * δ)) w := by
    intro δ w h
    rw [map_mul, map_inv, k22_t_mobiusSL_mul, ← h, ← hEz, k22_t_mobiusSL_inv_apply]
  rw [hΩ]
  refine ⟨fun hw => ?_, fun δ hδ s hs hds hw => ?_, fun δ hδ hδ0 hw => ?_⟩
  · rw [← hEz] at hw
    exact hzΛ (k22_t_mem_limitSet_of_smul (Subgroup.mem_map_of_mem _ hγ) hw)
  · have hds' : (δ 1 0 : ℂ) * (s : ℂ) + δ 1 1 ≠ 0 := by exact_mod_cast hds
    have h2 := hback δ ((s : ℂ) : ExtPlane) (by rw [hw, s36a_mext δ hds'])
    by_cases h0 : ((γ⁻¹ * δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) * (s : ℂ) +
        (γ⁻¹ * δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 = 0
    · rw [s36a_mext0 _ h0] at h2
      exact OnePoint.coe_ne_infty _ h2
    · rw [s36a_mext _ h0] at h2
      refine hzE (γ⁻¹ * δ) (Γ.mul_mem (Γ.inv_mem hγ) hδ) s hs ?_ (OnePoint.coe_injective h2)
      exact_mod_cast h0
  · have h2 := hback δ extInf (by rw [hw, (s36a_mextinf δ).1 hδ0])
    by_cases h0 : (γ⁻¹ * δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 = 0
    · rw [(s36a_mextinf _).2 h0] at h2
      exact OnePoint.coe_ne_infty _ h2
    · rw [(s36a_mextinf _).1 h0] at h2
      exact hzI (γ⁻¹ * δ) (Γ.mul_mem (Γ.inv_mem hγ) hδ) h0 (OnePoint.coe_injective h2)

end LiZhongQC
