import LiZhongQC.Lemmas.S36G1dExhaustion

/-!
E3 independent producer, using only installed S36 and the source-only E1 module.
No G1c/G1b/target stub is imported. No compiler run.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

open scoped Classical in
/-- A subgroup theta series is the indicated subseries of the ambient theta series. -/
theorem s36e_theta_indicator
    {Λ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΛ : Λ ≤ Γ)
    (f : ℂ → ℂ) (z : ℂ) :
    h36p_theta Λ f z =
      ∑' γ : Γ, if γ.val ∈ Λ then
        f (h36p_m γ.val z) / ((γ.val 1 0 : ℂ) * z + γ.val 1 1) ^ 4 else 0 := by
  classical
  let S : Set Γ := {γ | γ.val ∈ Λ}
  let e : Λ ≃ S :=
    { toFun := fun γ => ⟨⟨γ.val, hΛ γ.property⟩, γ.property⟩
      invFun := fun γ => ⟨γ.val.val, γ.property⟩
      left_inv := by intro γ; rfl
      right_inv := by intro γ; rfl }
  calc
    h36p_theta Λ f z =
        ∑' γ : S, f (h36p_m γ.val.val z) /
          ((γ.val.val 1 0 : ℂ) * z + γ.val.val 1 1) ^ 4 := by
      change (∑' γ : Λ, f (h36p_m γ.val z) /
        ((γ.val 1 0 : ℂ) * z + γ.val 1 1) ^ 4) = _
      exact e.tsum_eq (fun γ : S => f (h36p_m γ.val.val z) /
        ((γ.val.val 1 0 : ℂ) * z + γ.val.val 1 1) ^ 4)
    _ = ∑' γ : Γ, S.indicator (fun γ : Γ =>
        f (h36p_m γ.val z) / ((γ.val 1 0 : ℂ) * z + γ.val 1 1) ^ 4) γ :=
      tsum_subtype S (fun γ : Γ =>
        f (h36p_m γ.val z) / ((γ.val 1 0 : ℂ) * z + γ.val 1 1) ^ 4)
    _ = _ := rfl

/-- A subgroup theta norm is bounded by the ambient absolute theta series, without
any convergence premise; the ENNReal tsum bound remains valid at infinity. -/
theorem s36e_theta_enorm_le
    {Λ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΛ : Λ ≤ Γ)
    (f : ℂ → ℂ) (z : ℂ) :
    ‖h36p_theta Λ f z‖ₑ ≤
      ∑' γ : Γ, ‖f (h36p_m γ.val z) /
        ((γ.val 1 0 : ℂ) * z + γ.val 1 1) ^ 4‖ₑ := by
  classical
  rw [s36e_theta_indicator hΛ]
  refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum ?_)
  intro γ
  by_cases hγ : γ.val ∈ Λ
  · simp only [if_pos hγ, le_refl]
  · simp only [if_neg hγ, enorm_zero, zero_le]

/-- Tannery applied to the installed summable local theta majorant gives pointwise
convergence along every monotone exhaustive subgroup chain. -/
theorem s36e_theta_tendsto (hΓ : IsFuchsian Γ)
    (H : ℕ → Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hsub : ∀ i, H i ≤ Γ) (hmono : Monotone H)
    (hcover : ∀ γ ∈ Γ, ∃ i, γ ∈ H i)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalf)
    (hfA : phiArea f upperHalf < ⊤) {z : ℂ} (hz : z ∈ upperHalf) :
    Tendsto (fun i => h36p_theta (H i) f z) atTop (𝓝 (h36p_theta Γ f z)) := by
  classical
  let T : Γ → ℂ := fun γ =>
    f (h36p_m γ.val z) / ((γ.val 1 0 : ℂ) * z + γ.val 1 1) ^ 4
  obtain ⟨u, hu, hle⟩ := h36p_b_local hΓ hf hfA hz
  have hzB : z ∈ ball z (z.im / 4) := mem_ball_self (by
    have hzpos : 0 < z.im := hz
    positivity)
  have hsum : Summable (fun γ : Γ => ‖T γ‖) :=
    hu.of_norm_bounded (fun γ => by simpa only [norm_norm] using hle γ z hzB)
  have hpoint : ∀ γ : Γ, Tendsto
      (fun i => if γ.val ∈ H i then T γ else 0) atTop (𝓝 (T γ)) := by
    intro γ
    apply tendsto_const_nhds.congr'
    filter_upwards [s36e_mem_eventually H hmono hcover γ.property] with i hi
    simp only [if_pos hi]
  have hbound : ∀ᶠ i in atTop, ∀ γ : Γ,
      ‖if γ.val ∈ H i then T γ else 0‖ ≤ ‖T γ‖ := by
    apply Filter.Eventually.of_forall
    intro i γ
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (T γ)
  have hlim := tendsto_tsum_of_dominated_convergence hsum hpoint hbound
  have heq : ∀ i, h36p_theta (H i) f z =
      ∑' γ : Γ, if γ.val ∈ H i then T γ else 0 :=
    fun i => s36e_theta_indicator (hsub i) f z
  have hΓeq : h36p_theta Γ f z = ∑' γ : Γ, T γ := rfl
  simpa only [← heq, ← hΓeq] using hlim

/-- E3: the subgroup Poincare sums converge in L1 on every fixed ambient fundamental
domain, hence this applies separately to F and to g(F). -/
theorem s36e_theta_L1_fixed (hΓ : IsFuchsian Γ)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    (H : ℕ → Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hsub : ∀ i, H i ≤ Γ) (hmono : Monotone H)
    (hcover : ∀ γ ∈ Γ, ∃ i, γ ∈ H i)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalf)
    (hfA : phiArea f upperHalf < ⊤) :
    Tendsto (fun i => phiArea (h36p_theta (H i) f - h36p_theta Γ f) F)
      atTop (𝓝 0) := by
  classical
  have : Countable Γ := (h36p_countable hΓ).to_subtype
  let T : Γ → ℂ → ℂ := fun γ z =>
    f (h36p_m γ.val z) / ((γ.val 1 0 : ℂ) * z + γ.val 1 1) ^ 4
  let B : ℂ → ℝ≥0∞ := fun z => 2 * ∑' γ : Γ, ‖T γ z‖ₑ
  have hTm : ∀ γ : Γ, AEMeasurable (fun z => ‖T γ z‖ₑ) (volume.restrict F) :=
    fun γ => ((h36p_b_term_diff hf γ.val).continuousOn.mono hF.1).aestronglyMeasurable
      hF.2.1 |>.enorm
  have hBfin : (∫⁻ z in F, B z) ≠ ⊤ := by
    change (∫⁻ z in F, (2 : ℝ≥0∞) * ∑' γ : Γ, ‖T γ z‖ₑ) ≠ ⊤
    rw [lintegral_const_mul' _ _ (by norm_num), lintegral_tsum hTm]
    have heq := h36p_b_sum_lintegral hΓ hF hf
    change (∑' γ : Γ, ∫⁻ z in F, ‖T γ z‖ₑ) =
      (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * phiArea f upperHalf at heq
    rw [heq]
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hfA.ne)
  have hIm : ∀ i, AEMeasurable
      (fun z => ENNReal.ofReal ‖h36p_theta (H i) f z - h36p_theta Γ f z‖)
      (volume.restrict F) := by
    intro i
    have hHi : IsFuchsian (H i) := fun C hC =>
      (hΓ C hC).subset (fun γ hγ => ⟨hsub i hγ.1, hγ.2⟩)
    exact (((h36p_b_theta_diff hHi hf hfA).sub
      (h36p_b_theta_diff hΓ hf hfA)).continuousOn.mono hF.1).aestronglyMeasurable
        hF.2.1 |>.aemeasurable.norm.ennreal_ofReal
  have hbound : ∀ i, (fun z => ENNReal.ofReal
      ‖h36p_theta (H i) f z - h36p_theta Γ f z‖) ≤ᵐ[volume.restrict F] B := by
    intro i
    apply Filter.Eventually.of_forall
    intro z
    change ENNReal.ofReal ‖h36p_theta (H i) f z - h36p_theta Γ f z‖ ≤ B z
    rw [ofReal_norm]
    calc ‖h36p_theta (H i) f z - h36p_theta Γ f z‖ₑ
        ≤ ‖h36p_theta (H i) f z‖ₑ + ‖h36p_theta Γ f z‖ₑ := enorm_sub_le
      _ ≤ (∑' γ : Γ, ‖T γ z‖ₑ) + ∑' γ : Γ, ‖T γ z‖ₑ :=
        add_le_add (s36e_theta_enorm_le (hsub i) f z) enorm_tsum_le_tsum_enorm
      _ = B z := by
        change _ = (2 : ℝ≥0∞) * ∑' γ : Γ, ‖T γ z‖ₑ
        exact (two_mul _).symm
  have hlim : ∀ᵐ z ∂(volume.restrict F), Tendsto
      (fun i => ENNReal.ofReal ‖h36p_theta (H i) f z - h36p_theta Γ f z‖)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    filter_upwards [ae_restrict_mem hF.2.1] with z hz
    have hzH := hF.1 hz
    have hp := s36e_theta_tendsto hΓ H hsub hmono hcover hf hfA hzH
    have hn : Tendsto (fun i => ‖h36p_theta (H i) f z - h36p_theta Γ f z‖)
        atTop (𝓝 (0 : ℝ)) := by
      have hc : Tendsto (fun _ : ℕ => h36p_theta Γ f z)
          atTop (𝓝 (h36p_theta Γ f z)) := tendsto_const_nhds
      simpa only [sub_self, norm_zero] using (hp.sub hc).norm
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hn
  have hres := tendsto_lintegral_of_dominated_convergence' B hIm hbound hBfin hlim
  change Tendsto (fun i => ∫⁻ z in F,
    ENNReal.ofReal ‖h36p_theta (H i) f z - h36p_theta Γ f z‖) atTop (𝓝 0)
  simpa only [lintegral_zero] using hres

end LiZhongQC
