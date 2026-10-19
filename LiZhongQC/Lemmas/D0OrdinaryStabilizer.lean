import LiZhongQC.Lemmas.FoundationQuotient
import LiZhongQC.Lemmas.S36BersOrdinary
import LiZhongQC.Lemmas.StrebelDoubleDomain

/-! Approved D0-F source candidate. Finite-stabilizer averaging avoids a new
hyperbolic/parabolic normal-form foundation. Uncompiled; no new public defs. -/
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- D0-F. An ordinary affine point has no nontrivial stabilizer when the action
on the upper half-plane is free up to sign. Off the real axis use the upper
half-plane or conjugation. On the real axis a nontrivial real-fixed Mobius
element is parabolic or hyperbolic, and its fixed point is a limit point. -/
theorem s36d0_ordinary_stabilizer (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {z : ℂ} (hz : (z : ExtPlane) ∉ fuchsianLimitSet Γ)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ)
    (hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0) (hfix : h36p_m γ z = z) :
    γ = 1 ∨ γ = -1 := by
  classical
  have hupper : ∀ w ∈ upperHalf, h36p_m γ w = w → γ = 1 ∨ γ = -1 := by
    intro w hw he
    apply hfree γ hγ (⟨w, hw⟩ : UpperHalfPlane)
    apply UpperHalfPlane.ext
    rw [← h36p_m_coe]
    exact he
  by_cases him : z.im = 0
  swap
  · rcases lt_or_gt_of_ne him with hneg | hpos
    · apply hupper (conj z) (by
        change 0 < (conj z).im
        rw [Complex.conj_im]
        linarith)
      rw [show h36p_m γ (conj z) = conj (h36p_m γ z) from b33_e_mobius_conj γ z, hfix]
    · exact hupper z hpos hfix
  -- At a real ordinary point the stabilizer is finite. Average its local
  -- Mobius maps. Their derivatives are positive real numbers, so the average
  -- has a local inverse. Invariance then yields a fixed upper-half-plane point.
  let M : Matrix.SpecialLinearGroup (Fin 2) ℝ →* Matrix.SpecialLinearGroup (Fin 2) ℂ :=
    Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)
  let H : Subgroup Γ :=
    { carrier := {δ | mobiusSL (M δ.1) (z : ExtPlane) = (z : ExtPlane)}
      one_mem' := by
        change mobiusSL (M 1) (z : ExtPlane) = (z : ExtPlane)
        rw [map_one, k22_t_mobiusSL_one]
      mul_mem' := by
        intro δ η hδ hη
        have hδ' : mobiusSL (M δ.1) (z : ExtPlane) = (z : ExtPlane) := hδ
        have hη' : mobiusSL (M η.1) (z : ExtPlane) = (z : ExtPlane) := hη
        change mobiusSL (M (δ.1 * η.1)) (z : ExtPlane) = (z : ExtPlane)
        rw [map_mul, k22_t_mobiusSL_mul, hη', hδ']
      inv_mem' := by
        intro δ hδ
        have hδ' : mobiusSL (M δ.1) (z : ExtPlane) = (z : ExtPlane) := hδ
        change mobiusSL (M δ.1⁻¹) (z : ExtPlane) = (z : ExtPlane)
        have he := congrArg (mobiusSL ((M δ.1)⁻¹)) hδ'
        rw [k22_t_mobiusSL_inv_apply] at he
        rw [map_inv]
        exact he.symm }
  have hfinite : (H : Set Γ).Finite := by
    have hf := s36x_fin hΓ (C := {(z : ExtPlane)}) isCompact_singleton (by
      intro p hp
      rw [mem_singleton_iff.1 hp]
      exact hz)
    refine hf.subset ?_
    intro δ hδ
    exact ⟨(z : ExtPlane), ⟨(z : ExtPlane), rfl, hδ⟩, rfl⟩
  letI : Fintype H := hfinite.fintype
  have hδfix : ∀ δ : H, mobiusSL (M δ.1.1) (z : ExtPlane) = (z : ExtPlane) :=
    fun δ => δ.property
  have hδden : ∀ δ : H, (δ.1.1 1 0 : ℂ) * z + δ.1.1 1 1 ≠ 0 := by
    intro δ he
    have h0 := hδfix δ
    rw [s36x_msl_inf δ.1.1 he] at h0
    exact OnePoint.coe_ne_infty z h0.symm
  let F : ℂ → ℂ := fun w => ∑ δ : H, h36p_m δ.1.1 w
  let D : ℂ := ∑ δ : H, 1 / ((δ.1.1 1 0 : ℂ) * z + δ.1.1 1 1) ^ 2
  have hdδ : ∀ δ : H, HasStrictDerivAt (h36p_m δ.1.1)
      (1 / ((δ.1.1 1 0 : ℂ) * z + δ.1.1 1 1) ^ 2) z := by
    intro δ
    have hd := hδden δ
    have hdet : (δ.1.1 0 0 : ℂ) * δ.1.1 1 1 -
        δ.1.1 0 1 * δ.1.1 1 0 = 1 := by exact_mod_cast b33_d_det δ.1.1
    change HasStrictDerivAt
      (fun w : ℂ => ((δ.1.1 0 0 : ℂ) * w + δ.1.1 0 1) /
        ((δ.1.1 1 0 : ℂ) * w + δ.1.1 1 1)) _ z
    refine ((((hasStrictDerivAt_id z).const_mul (δ.1.1 0 0 : ℂ)).add_const (δ.1.1 0 1 : ℂ)).div
      (((hasStrictDerivAt_id z).const_mul (δ.1.1 1 0 : ℂ)).add_const (δ.1.1 1 1 : ℂ)) hd).congr_deriv ?_
    try simp only [id]
    congr 1
    linear_combination hdet
  have hFD : HasStrictDerivAt F D z :=
    HasStrictDerivAt.fun_sum (fun δ _ => hdδ δ)
  have hzreal : z = (z.re : ℂ) := Complex.ext rfl (by simpa using him)
  have hrealden : ∀ δ : H, δ.1.1 1 0 * z.re + δ.1.1 1 1 ≠ 0 := by
    intro δ he
    apply hδden δ
    rw [hzreal]
    exact_mod_cast he
  have hDreal : D = ((∑ δ : H, 1 / (δ.1.1 1 0 * z.re + δ.1.1 1 1) ^ 2 : ℝ) : ℂ) := by
    dsimp only [D]
    push_cast
    apply Finset.sum_congr rfl
    intro δ _
    rw [hzreal]
    simp only [Complex.ofReal_re]
  have hDpos : 0 < ∑ δ : H, 1 / (δ.1.1 1 0 * z.re + δ.1.1 1 1) ^ 2 :=
    Finset.sum_pos (fun δ _ => div_pos zero_lt_one (sq_pos_of_ne_zero (hrealden δ)))
      ⟨1, Finset.mem_univ _⟩
  have hD : D ≠ 0 := by
    rw [hDreal]
    exact Complex.ofReal_ne_zero.2 hDpos.ne'
  have hγH : (⟨γ, hγ⟩ : Γ) ∈ H := by
    change mobiusSL (M γ) (z : ExtPlane) = (z : ExtPlane)
    rw [s36x_msl_coe γ hden, hfix]
  let γH : H := ⟨⟨γ, hγ⟩, hγH⟩
  have hFinv : ∀ w ∈ upperHalf, F (h36p_m γ w) = F w := by
    intro w hw
    change (∑ δ : H, h36p_m δ.1.1 (h36p_m γ w)) =
      ∑ δ : H, h36p_m δ.1.1 w
    calc (∑ δ : H, h36p_m δ.1.1 (h36p_m γ w))
        = ∑ δ : H, h36p_m (δ.1.1 * γ) w := by
          apply Finset.sum_congr rfl
          intro δ _
          exact (h36p_b_m_mul δ.1.1 γ hw).symm
      _ = ∑ δ : H, h36p_m δ.1.1 w :=
        Equiv.sum_comp (Equiv.mulRight γH) (fun δ : H => h36p_m δ.1.1 w)
  let invF : ℂ → ℂ := hFD.localInverse F D z hD
  have hleft : ∀ᶠ w in 𝓝 z, invF (F w) = w := hFD.eventually_left_inverse hD
  have hγlim : Tendsto (h36p_m γ) (𝓝 z) (𝓝 z) := by
    simpa only [hfix] using (s36x_m_hasDerivAt γ hden).continuousAt.tendsto
  have hboth : ∀ᶠ w in 𝓝[upperHalf] z,
      invF (F w) = w ∧ invF (F (h36p_m γ w)) = h36p_m γ w :=
    (hleft.and (hγlim.eventually hleft)).filter_mono nhdsWithin_le_nhds
  have hzcl : z ∈ closure upperHalf := by
    change z ∈ closure {w : ℂ | 0 < w.im}
    rw [Complex.closure_setOfPred_lt_im]
    exact le_of_eq him.symm
  letI : (𝓝[upperHalf] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hzcl
  obtain ⟨w, hw, h1, h2⟩ :=
    (eventually_mem_nhdsWithin.and hboth).exists
  apply hupper w hw
  calc h36p_m γ w = invF (F (h36p_m γ w)) := h2.symm
    _ = invF (F w) := congrArg invF (hFinv w hw)
    _ = w := h1

end LiZhongQC
