import LiZhongQC.Lemmas.FoundationQuotient
import LiZhongQC.Lemmas.S36BersOrdinary
import LiZhongQC.Lemmas.StrebelDoubleDomain

/-! D0-O source candidate, uncompiled; frozen statement from iface_v2. -/
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- D0-O. Removing finitely many real pole orbits and the orbit of infinity from
the ordinary locus leaves an open affine domain. Use s36x_hit_fin and s36x_fin;
do not reprove proper discontinuity. -/
theorem s36d0_domain_open (hΓ : IsFuchsian Γ) {E : Finset ℝ}
    (hE : ∀ e ∈ E, (((e : ℂ)) : ExtPlane) ∉ fuchsianLimitSet Γ) {Ω : Set ℂ}
    (hΩ : ∀ z : ℂ, z ∈ Ω ↔ ((z : ExtPlane) ∉ fuchsianLimitSet Γ ∧
      (∀ γ ∈ Γ, ∀ s ∈ E, (γ 1 0 : ℝ) * s + γ 1 1 ≠ 0 → z ≠ h36p_m γ (s : ℂ)) ∧
      (∀ γ ∈ Γ, (γ 1 0 : ℝ) ≠ 0 → z ≠ ((γ 0 0 / γ 1 0 : ℝ) : ℂ)))) :
    IsOpen Ω := by
  classical
  -- hE is part of the frozen geometric contract; openness also holds when
  -- some removed poles lie in the limit set, since those orbits miss Ω.
  have _hE := hE
  let M : Matrix.SpecialLinearGroup (Fin 2) ℝ →* Matrix.SpecialLinearGroup (Fin 2) ℂ :=
    Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)
  let P : Set ExtPlane := insert extInf ((fun t : ℝ => ((t : ℂ) : ExtPlane)) '' (E : Set ℝ))
  have hP : P.Finite := (E.finite_toSet.image _).insert _
  have hact := (s36a_omega hΓ hΩ).2.2
  have hdescription : ∀ z : ℂ, z ∈ Ω ↔
      (z : ExtPlane) ∉ fuchsianLimitSet Γ ∧
        ∀ γ ∈ Γ, mobiusSL (M γ) (z : ExtPlane) ∉ P := by
    intro z
    constructor
    · intro hz
      refine ⟨((hΩ z).1 hz).1, ?_⟩
      intro γ hγ hp
      obtain ⟨hden, hγz⟩ := hact γ hγ z hz
      have hm := s36a_mext γ hden
      change mobiusSL (M γ) (z : ExtPlane) = ((h36p_m γ z : ℂ) : ExtPlane) at hm
      change mobiusSL (M γ) (z : ExtPlane) ∈
        insert extInf ((fun t : ℝ => ((t : ℂ) : ExtPlane)) '' (E : Set ℝ)) at hp
      rcases hp with hp | hp
      · exact OnePoint.coe_ne_infty _ (hm.symm.trans hp)
      · obtain ⟨t, ht, he⟩ := hp
        have he' : h36p_m γ z = (t : ℂ) := OnePoint.coe_injective (hm.symm.trans he.symm)
        have hne := ((hΩ _).1 hγz).2.1 1 (one_mem Γ) t ht (by simp)
        exact hne (he'.trans (h36p_a_m_one _).symm)
    · rintro ⟨hord, havoid⟩
      refine (hΩ z).2 ⟨hord, ?_, ?_⟩
      · intro γ hγ t ht hden he
        have hden' : (γ 1 0 : ℂ) * (t : ℂ) + γ 1 1 ≠ 0 := by exact_mod_cast hden
        have hf : mobiusSL (M γ) ((t : ℂ) : ExtPlane) = (z : ExtPlane) := by
          rw [s36a_mext γ hden', ← he]
        apply havoid γ⁻¹ (inv_mem hγ)
        have hi : mobiusSL (M γ⁻¹) (z : ExtPlane) = ((t : ℂ) : ExtPlane) := by
          rw [← hf]
          rw [map_inv]
          exact k22_t_mobiusSL_inv_apply _ _
        rw [hi]
        exact Or.inr ⟨t, ht, rfl⟩
      · intro γ hγ hc he
        have hf : mobiusSL (M γ) extInf = (z : ExtPlane) := by
          rw [(s36a_mextinf γ).1 hc, ← he]
        apply havoid γ⁻¹ (inv_mem hγ)
        have hi : mobiusSL (M γ⁻¹) (z : ExtPlane) = extInf := by
          rw [← hf]
          rw [map_inv]
          exact k22_t_mobiusSL_inv_apply _ _
        rw [hi]
        exact Or.inl rfl
  refine isOpen_iff_mem_nhds.2 ?_
  intro z hz
  obtain ⟨hzord, hzavoid⟩ := (hdescription z).1 hz
  have hO : IsOpen {w : ℂ | (w : ExtPlane) ∉ fuchsianLimitSet Γ} :=
    (s36x_limitSet_closed hΓ).isOpen_compl.preimage OnePoint.continuous_coe
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 hO z hzord
  let r : ℝ := ρ / 2
  have hr : 0 < r := half_pos hρ
  have hKr : ∀ w ∈ closedBall z r, (w : ExtPlane) ∉ fuchsianLimitSet Γ := by
    intro w hw
    exact hρsub (closedBall_subset_ball (half_lt_self hρ) hw)
  let Bad : Set Γ := ⋃ p ∈ P,
    {γ : Γ | ∃ w ∈ closedBall z r, mobiusSL (M γ.1) (w : ExtPlane) = p}
  have hBad : Bad.Finite := hP.biUnion fun p _ =>
    s36x_hit_fin hΓ (isCompact_closedBall z r) hKr p
  let U : Set ℂ := ball z r ∩ ⋂ γ ∈ Bad,
    (fun w : ℂ => mobiusSL (M γ.1) (w : ExtPlane)) ⁻¹' Pᶜ
  have hU : IsOpen U := isOpen_ball.inter (hBad.isOpen_biInter fun γ _ =>
    hP.isClosed.isOpen_compl.preimage ((k22_t_continuous _).comp OnePoint.continuous_coe))
  have hzU : z ∈ U := by
    refine ⟨mem_ball_self hr, ?_⟩
    exact mem_iInter.2 fun γ => mem_iInter.2 fun _ => hzavoid γ.1 γ.2
  apply Filter.mem_of_superset (hU.mem_nhds hzU)
  intro w hw
  refine (hdescription w).2 ⟨hKr w (ball_subset_closedBall hw.1), ?_⟩
  intro γ hγ hp
  have hB : (⟨γ, hγ⟩ : Γ) ∈ Bad :=
    mem_iUnion.2 ⟨mobiusSL (M γ) (w : ExtPlane),
      mem_iUnion.2 ⟨hp, w, ball_subset_closedBall hw.1, rfl⟩⟩
  exact (mem_iInter.1 (mem_iInter.1 hw.2 ⟨γ, hγ⟩) hB) hp

end LiZhongQC
