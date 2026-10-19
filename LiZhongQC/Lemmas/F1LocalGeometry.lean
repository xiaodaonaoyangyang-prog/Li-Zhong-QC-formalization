import LiZhongQC.Lemmas.FoundationQuotient

/-!
Source-only proofs for the four approved F1 local geometric contracts.
The approved interface is F1LocalGeometryIface.lean, MD5 6f145c2f5aa70dcd319fe38342986dfb.
No compiler has been run on this file. These estimates do not construct the end decomposition.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

/-- The upper-half-plane argument is strictly between zero and pi. -/
theorem ft1g_arg_bounds (τ : UpperHalfPlane) :
    0 < Complex.arg (τ : ℂ) ∧ Complex.arg (τ : ℂ) < Real.pi := by
  have hnonneg : 0 ≤ Complex.arg (τ : ℂ) := Complex.arg_nonneg_iff.2 τ.im_pos.le
  have hne : Complex.arg (τ : ℂ) ≠ 0 := by
    intro hzero
    have heq := Complex.norm_mul_sin_arg (τ : ℂ)
    rw [hzero, Real.sin_zero, mul_zero] at heq
    exact τ.im_pos.ne' heq.symm
  exact ⟨lt_of_le_of_ne hnonneg (Ne.symm hne),
    Complex.arg_lt_pi_iff.2 (Or.inr τ.im_pos.ne')⟩

/-- The argument has no branch cut on the upper half-plane. -/
theorem ft1g_arg_continuous :
    Continuous (fun τ : UpperHalfPlane => Complex.arg (τ : ℂ)) := by
  apply continuous_iff_continuousAt.2
  intro τ
  apply (Complex.continuousAt_arg ?_).comp UpperHalfPlane.continuous_coe.continuousAt
  exact Complex.mem_slitPlane_iff.2 (Or.inr τ.im_pos.ne')

/-- A compact fundamental boundary segment stays uniformly away from both real rays,
and the same angular bounds hold for all positive dilates. This is the uniform-small-angle
step for a hyperbolically periodic boundary, before choosing a precisely invariant sector. -/
theorem ft1g_compact_angular_margin (K : Set UpperHalfPlane) (hK : IsCompact K) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi / 2 ∧
      ∀ τ ∈ K, ∀ a : ℝ, 0 < a →
        θ ≤ Complex.arg ((a : ℂ) * (τ : ℂ)) ∧
        Complex.arg ((a : ℂ) * (τ : ℂ)) ≤ Real.pi - θ := by
  have hcont : Continuous (fun τ : UpperHalfPlane =>
      min (Complex.arg (τ : ℂ)) (Real.pi - Complex.arg (τ : ℂ))) :=
    ft1g_arg_continuous.min (continuous_const.sub ft1g_arg_continuous)
  obtain ⟨a, ha, hbound⟩ := hK.exists_forall_le' hcont.continuousOn
    (a := (0 : ℝ)) (fun τ _ => lt_min (ft1g_arg_bounds τ).1
      (sub_pos.2 (ft1g_arg_bounds τ).2))
  let θ : ℝ := min (a / 2) (Real.pi / 4)
  have hθ : 0 < θ := lt_min (by linarith) (by positivity)
  have hθa : θ ≤ a := (min_le_left _ _).trans (by linarith)
  have hθπ : θ < Real.pi / 2 :=
    lt_of_le_of_lt (min_le_right _ _) (by have := Real.pi_pos; linarith)
  refine ⟨θ, hθ, hθπ, ?_⟩
  intro τ hτ b hb
  rw [Complex.arg_real_mul _ hb]
  have hlow : a ≤ Complex.arg (τ : ℂ) := (hbound τ hτ).trans (min_le_left _ _)
  have hhigh : a ≤ Real.pi - Complex.arg (τ : ℂ) := (hbound τ hτ).trans (min_le_right _ _)
  exact ⟨hθa.trans hlow, by linarith⟩

/-- A continuous periodic boundary has a uniform positive angular margin. Scaling
periodicity is checked on the entire real parameter, not just on the integer orbit. -/
theorem ft1g_periodic_angular_margin (ρ : ℝ → UpperHalfPlane) (hρ : Continuous ρ)
    (lam : ℝ) (hlam : 1 < lam)
    (hperiod : ∀ t : ℝ, ((ρ (t + 1) : UpperHalfPlane) : ℂ) = (lam : ℂ) * (ρ t : ℂ)) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi / 2 ∧
      ∀ t : ℝ, θ ≤ Complex.arg (ρ t : ℂ) ∧ Complex.arg (ρ t : ℂ) ≤ Real.pi - θ := by
  have hper : Function.Periodic (fun t : ℝ => Complex.arg (ρ t : ℂ)) 1 := by
    intro t
    change Complex.arg (ρ (t + 1) : ℂ) = Complex.arg (ρ t : ℂ)
    rw [hperiod, Complex.arg_real_mul _ (by linarith : 0 < lam)]
  obtain ⟨θ, hθ, hθπ, hbound⟩ :=
    ft1g_compact_angular_margin (ρ '' Icc 0 1) (isCompact_Icc.image hρ)
  refine ⟨θ, hθ, hθπ, ?_⟩
  intro t
  have hfloor := Int.floor_le t
  have hfloor' := Int.lt_floor_add_one t
  have hu : t - (⌊t⌋ : ℤ) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hb := hbound (ρ (t - (⌊t⌋ : ℤ))) ⟨t - (⌊t⌋ : ℤ), hu, rfl⟩ 1 one_pos
  have heq : Complex.arg (ρ (t - (⌊t⌋ : ℤ)) : ℂ) = Complex.arg (ρ t : ℂ) := by
    simpa only [mul_one] using hper.sub_int_mul_eq (x := t) (⌊t⌋ : ℤ)
  simpa only [Complex.ofReal_one, one_mul, heq] using hb

/-- A closed annular angular band is compact in the upper half-plane: the angular
margin supplies a positive imaginary lower bound, which Euclidean boundedness alone lacks. -/
theorem ft1g_annular_band_compact (lam θ : ℝ) (hlam : 1 < lam)
    (hθ : 0 < θ) (hθπ : θ < Real.pi / 2) :
    IsCompact {τ : UpperHalfPlane | 1 ≤ ‖(τ : ℂ)‖ ∧ ‖(τ : ℂ)‖ ≤ lam ∧
      θ ≤ Complex.arg (τ : ℂ) ∧ Complex.arg (τ : ℂ) ≤ Real.pi - θ} := by
  -- A sine minimum supplies the missing distance from the real axis.
  obtain ⟨δ, hδ, hsin⟩ := (isCompact_Icc : IsCompact (Icc θ (Real.pi - θ))).exists_forall_le'
    Real.continuous_sin.continuousOn (a := (0 : ℝ)) (fun t ht =>
      Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hθ ht.1) (by linarith [ht.2]))
  have hcompact : IsCompact {τ : UpperHalfPlane | ‖(τ : ℂ)‖ ≤ lam ∧ δ ≤ τ.im} := by
    rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff]
    have heq : ((↑) : UpperHalfPlane → ℂ) '' {τ : UpperHalfPlane | ‖(τ : ℂ)‖ ≤ lam ∧ δ ≤ τ.im} =
        closedBall (0 : ℂ) lam ∩ {z : ℂ | δ ≤ z.im} := by
      ext z
      constructor
      · rintro ⟨τ, hτ, rfl⟩
        exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hτ.1, hτ.2⟩
      · intro hz
        have hzpos : 0 < z.im := hδ.trans_le hz.2
        refine ⟨⟨z, hzpos⟩, ?_, rfl⟩
        exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hz.1, hz.2⟩
    rw [heq]
    exact (isCompact_closedBall (0 : ℂ) lam).inter_right
      (isClosed_le continuous_const Complex.continuous_im)
  have hncont : Continuous (fun τ : UpperHalfPlane => ‖(τ : ℂ)‖) :=
    continuous_norm.comp UpperHalfPlane.continuous_coe
  have hclosed : IsClosed {τ : UpperHalfPlane | 1 ≤ ‖(τ : ℂ)‖ ∧ ‖(τ : ℂ)‖ ≤ lam ∧
      θ ≤ Complex.arg (τ : ℂ) ∧ Complex.arg (τ : ℂ) ≤ Real.pi - θ} :=
    (isClosed_le continuous_const hncont).inter ((isClosed_le hncont continuous_const).inter
      ((isClosed_le continuous_const ft1g_arg_continuous).inter
        (isClosed_le ft1g_arg_continuous continuous_const)))
  refine hcompact.of_isClosed_subset hclosed ?_
  intro τ hτ
  refine ⟨hτ.2.1, ?_⟩
  have hs := hsin (Complex.arg (τ : ℂ)) hτ.2.2
  have hs0 : 0 ≤ Real.sin (Complex.arg (τ : ℂ)) := (hδ.trans_le hs).le
  have heq := Complex.norm_mul_sin_arg (τ : ℂ)
  have hmul := mul_le_mul_of_nonneg_right hτ.1 hs0
  rw [one_mul, heq] at hmul
  exact hs.trans hmul

/-- A nonzero upper-half-plane point can be moved into one closed multiplicative
fundamental annulus. Endpoints may be identified; this is for compactness, not uniqueness. -/
theorem ft1g_scale_to_annulus (lam : ℝ) (hlam : 1 < lam) (τ : UpperHalfPlane) :
    ∃ k : ℤ, 1 ≤ ‖(lam : ℂ) ^ k * (τ : ℂ)‖ ∧
      ‖(lam : ℂ) ^ k * (τ : ℂ)‖ ≤ lam := by
  have hlam0 : 0 < lam := lt_trans zero_lt_one hlam
  have hnorm : 0 < ‖(τ : ℂ)‖ := norm_pos_iff.2 τ.ne_zero
  obtain ⟨n, hn, hn'⟩ := exists_mem_Ico_zpow hnorm hlam
  have hpow : 0 < lam ^ n := zpow_pos hlam0 n
  refine ⟨-n, ?_, ?_⟩
  · rw [norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0,
      zpow_neg, inv_mul_eq_div]
    exact (one_le_div₀ hpow).2 hn
  · rw [norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0,
      zpow_neg, inv_mul_eq_div]
    apply (div_le_iff₀ hpow).2
    have hb : ‖(τ : ℂ)‖ ≤ lam ^ n * lam := by
      simpa only [zpow_add_one₀ hlam0.ne'] using hn'.le
    simpa only [mul_comm] using hb

end LiZhongQC
