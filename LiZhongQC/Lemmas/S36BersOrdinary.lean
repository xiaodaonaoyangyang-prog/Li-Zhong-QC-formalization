import LiZhongQC.Ch11.S36_Hamilton
import LiZhongQC.ClusterSets

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- The limit set of a Fuchsian group is closed (it is the orbit-limit set of the ordinary point `i`). -/
theorem s36x_limitSet_closed (hΓ : IsFuchsian Γ) : IsClosed (fuchsianLimitSet Γ) := by
  have hI := k24_c_I_not_mem_limitSet hΓ
  have e : fuchsianLimitSet Γ =
      k22_t_orbitLim (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ))) ((Complex.I : ℂ) : ExtPlane) :=
    Set.Subset.antisymm (k22_t_limitSet_subset_orbitLim hI) (k22_t_orbitLim_subset _)
  rw [e]
  exact k22_t_orbitLim_closed ⟨_, hI⟩ _

/-- The action on `ℂ̄` of a real matrix agrees with `h36p_m` off the pole. -/
theorem s36x_msl_coe (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {w : ℂ} (hw : (γ 1 0 : ℂ) * w + γ 1 1 ≠ 0) :
    mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ) (w : ExtPlane) = ((h36p_m γ w : ℂ) : ExtPlane) := by
  have e : mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ) =
      mobiusExt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) := by
    simp [mobiusSL, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [e, mobiusExt_coe hw]
  rfl

/-- At the pole the action is `∞`. -/
theorem s36x_msl_inf (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {w : ℂ} (hw : (γ 1 0 : ℂ) * w + γ 1 1 = 0) :
    mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ) (w : ExtPlane) = extInf := by
  have e : mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ) =
      mobiusExt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) := by
    simp [mobiusSL, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [e, mobiusExt_coe_of_eq_zero hw]

/-- Discontinuity of `Γ` on a compact set of ordinary points (`k24_c_core`), indexed by `Γ`. -/
theorem s36x_fin (hΓ : IsFuchsian Γ) {C : Set ExtPlane} (hC : IsCompact C)
    (hCΛ : ∀ p ∈ C, p ∉ fuchsianLimitSet Γ) :
    {γ : Γ | (mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ.1) '' C ∩ C).Nonempty}.Finite := by
  have h := k24_c_core hΓ C hC (fun p hp => hCΛ p hp)
  have hinj : Function.Injective (fun γ : Γ => Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ.1) := by
    intro g h e
    apply Subtype.ext
    ext i j
    have := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) ℂ => (M : Matrix (Fin 2) (Fin 2) ℂ) i j) e
    simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply] using this
  refine (h.preimage hinj.injOn).subset ?_
  intro γ hγ
  exact ⟨⟨γ.1, γ.2, rfl⟩, hγ⟩

/-- Only finitely many `γ ∈ Γ` move a point of a compact set `K` of ordinary points to a given `p ∈ ℂ̄`. -/
theorem s36x_hit_fin (hΓ : IsFuchsian Γ) {K : Set ℂ} (hK : IsCompact K)
    (hKΩ : ∀ w ∈ K, ((w : ℂ) : ExtPlane) ∉ fuchsianLimitSet Γ) (p : ExtPlane) :
    {γ : Γ | ∃ w ∈ K, mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ.1) (w : ExtPlane) = p}.Finite := by
  by_cases hp : p ∈ fuchsianLimitSet Γ
  · convert Set.finite_empty
    ext γ
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    rintro ⟨w, hw, e⟩
    exact hKΩ w hw (k22_t_mem_limitSet_of_smul (Subgroup.mem_map_of_mem _ γ.2) (e ▸ hp))
  · have hC : IsCompact (((↑) : ℂ → ExtPlane) '' K ∪ {p}) := (hK.image OnePoint.continuous_coe).union isCompact_singleton
    refine (s36x_fin hΓ hC ?_).subset ?_
    · rintro q (⟨w, hw, rfl⟩ | hq)
      · exact hKΩ w hw
      · rw [mem_singleton_iff.1 hq]
        exact hp
    · rintro γ ⟨w, hw, e⟩
      exact ⟨p, ⟨(w : ExtPlane), Or.inl ⟨w, hw, rfl⟩, e⟩, Or.inr rfl⟩

/-- `h36p_m γ` has derivative `1/(cz + d)²` off the pole. -/
theorem s36x_m_hasDerivAt (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0) :
    HasDerivAt (h36p_m γ) (1 / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2) z := by
  have hdetC : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast b33_d_det γ
  exact k24_d_deriv hdetC hz

/-- `h36p_m γ` is injective off the pole. -/
theorem s36x_m_injOn (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    InjOn (h36p_m γ) {z : ℂ | (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0} := by
  intro z₁ h₁ z₂ h₂ h
  have hdet : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast b33_d_det γ
  simp only [h36p_m] at h
  rw [div_eq_div_iff h₁ h₂] at h
  linear_combination h - (z₁ - z₂) * hdet

end LiZhongQC
