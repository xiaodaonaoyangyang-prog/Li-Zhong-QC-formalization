import LiZhongQC.Lemmas.S36BersRepairBase
import LiZhongQC.Lemmas.S36BersOrdinary

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Möbius change of variables on a measurable set avoiding the pole. -/
theorem s36x_lintegral_image (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {E : Set ℂ} (hE : MeasurableSet E)
    (hEd : ∀ z ∈ E, (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0) (G : ℂ → ℝ≥0∞) :
    ∫⁻ w in h36p_m γ '' E, G w =
      ∫⁻ z in E, G (h36p_m γ z) * ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hE
    (fun z hz => ((s36x_m_hasDerivAt γ (hEd z hz)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
    ((s36x_m_injOn γ).mono fun z hz => hEd z hz)]
  refine setLIntegral_congr_fun hE fun z _ => ?_
  simp only [det_restrictScalars_toSpanSingleton]
  rw [mul_comm, abs_of_nonneg (sq_nonneg _)]
  congr 2
  rw [norm_div, norm_one, norm_pow]
  ring

/-- **Multiplicity of the translates** of a measurable set `E` inside a compact set `K` of ordinary points:
`Σ_γ ∬_{γ(E)} g ≤ N ∬ g` over the `γ` without pole on `K`. -/
theorem s36x_mult (hΓ : IsFuchsian Γ) {K : Set ℂ} (hK : IsCompact K)
    (hKΩ : ∀ w ∈ K, ((w : ℂ) : ExtPlane) ∉ fuchsianLimitSet Γ) {E : Set ℂ} (hEm : MeasurableSet E) (hEK : E ⊆ K)
    (Bad : Finset Γ) (hBad : ∀ γ : Γ, γ ∉ Bad → ∀ w ∈ K, (γ.1 1 0 : ℂ) * w + γ.1 1 1 ≠ 0)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    ∃ N : ℕ, ∑' γ : {γ : Γ // γ ∉ Bad}, ∫⁻ x in h36p_m γ.1.1 '' E, g x ≤ N * ∫⁻ x, g x := by
  classical
  letI : Countable Γ := (h36p_countable hΓ).to_subtype
  have hS := s36x_fin hΓ (hK.image OnePoint.continuous_coe) (by rintro p ⟨w, hw, rfl⟩; exact hKΩ w hw)
  set S₀ := {γ : Γ | (mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ.1) ''
    (((↑) : ℂ → ExtPlane) '' K) ∩ (((↑) : ℂ → ExtPlane) '' K)).Nonempty} with hS₀
  refine ⟨S₀.ncard, ?_⟩
  set A : {γ : Γ // γ ∉ Bad} → Set ℂ := fun γ => h36p_m γ.1.1 '' E with hAdef
  have hA : ∀ γ, MeasurableSet (A γ) := fun γ =>
    hEm.image_of_continuousOn_injOn
      (fun z hz => (s36x_m_hasDerivAt γ.1.1 (hBad γ.1 γ.2 z (hEK hz))).continuousAt.continuousWithinAt)
      ((s36x_m_injOn γ.1.1).mono fun z hz => hBad γ.1 γ.2 z (hEK hz))
  calc ∑' γ : {γ : Γ // γ ∉ Bad}, ∫⁻ x in h36p_m γ.1.1 '' E, g x
      = ∑' γ, ∫⁻ x, (A γ).indicator g x := by
        congr 1
        ext γ
        rw [lintegral_indicator (hA γ)]
    _ = ∫⁻ x, ∑' γ, (A γ).indicator g x :=
        (lintegral_tsum fun γ => (hg.indicator (hA γ)).aemeasurable).symm
    _ ≤ ∫⁻ x, (S₀.ncard : ℝ≥0∞) * g x := lintegral_mono fun x => ?_
    _ = (S₀.ncard : ℝ≥0∞) * ∫⁻ x, g x := lintegral_const_mul _ hg
  have e : ∀ γ, (A γ).indicator g x = (A γ).indicator (fun _ => (1 : ℝ≥0∞)) x * g x := fun γ => by
    by_cases h : x ∈ A γ
    · simp [indicator_of_mem h]
    · simp [indicator_of_notMem h]
  simp only [e]
  rw [ENNReal.tsum_mul_right]
  refine mul_le_mul_left ?_ _
  by_cases hT : ∃ γ₁, x ∈ A γ₁
  · obtain ⟨γ₁, hx₁⟩ := hT
    obtain ⟨w₁, hw₁, hxw₁⟩ := hx₁
    set Tx : Set {γ : Γ // γ ∉ Bad} := {γ | x ∈ A γ} with hTx
    set f : {γ : Γ // γ ∉ Bad} → Γ := fun γ => γ₁.1⁻¹ * γ.1 with hf
    have hmap : ∀ γ ∈ Tx, f γ ∈ S₀ := by
      rintro γ ⟨w, hw, hxw⟩
      refine ⟨(w₁ : ExtPlane), ⟨(w : ExtPlane), ⟨w, hEK hw, rfl⟩, ?_⟩, ⟨w₁, hEK hw₁, rfl⟩⟩
      simp only [hf, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, k22_t_mobiusSL_mul]
      rw [s36x_msl_coe γ.1.1 (hBad γ.1 γ.2 w (hEK hw)), hxw, ← hxw₁,
        ← s36x_msl_coe γ₁.1.1 (hBad γ₁.1 γ₁.2 w₁ (hEK hw₁)), k22_t_mobiusSL_inv_apply]
    have hinj : InjOn f Tx := fun γ _ γ' _ h => Subtype.ext (mul_left_cancel h)
    have hfinT : Tx.Finite := Set.Finite.of_finite_image (hS.subset (by rintro _ ⟨γ, hγ, rfl⟩; exact hmap γ hγ)) hinj
    have hcard : Tx.ncard ≤ S₀.ncard := Set.ncard_le_ncard_of_injOn f hmap hinj hS
    have hzero : ∀ γ ∉ hfinT.toFinset, (A γ).indicator (fun _ => (1 : ℝ≥0∞)) x = 0 := by
      intro γ hγ
      have hn : x ∉ A γ := by
        intro hx
        exact hγ (hfinT.mem_toFinset.2 hx)
      exact indicator_of_notMem hn _
    rw [tsum_eq_sum (s := hfinT.toFinset) hzero]
    have hone : ∀ γ ∈ hfinT.toFinset, (A γ).indicator (fun _ => (1 : ℝ≥0∞)) x = 1 := by
      intro γ hγ
      exact indicator_of_mem (show x ∈ A γ from hfinT.mem_toFinset.1 hγ)
        (fun _ : ℂ => (1 : ℝ≥0∞))
    calc ∑ γ ∈ hfinT.toFinset, (A γ).indicator (fun _ => (1 : ℝ≥0∞)) x
        = (hfinT.toFinset.card : ℝ≥0∞) := by
          simp only [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (S₀.ncard : ℝ≥0∞) := by
        have hc : hfinT.toFinset.card ≤ S₀.ncard := by
          simpa only [Set.ncard_eq_toFinset_card Tx hfinT] using hcard
        exact_mod_cast hc
  · push Not at hT
    simp [indicator_of_notMem (hT _)]

/-- The 4-pole kernel is dominated on all of `ℂ` by an integrable function (`s36b_pf4` on the closed upper
half-plane, and the symmetry `|k(ζ̄)| = |k(ζ)|`). -/
theorem s36x_k_bound {a b c t : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hta : t ≠ a) (htb : t ≠ b)
    (htc : t ≠ c) :
    ∃ G : ℂ → ℝ, Integrable G ∧ ∀ ζ : ℂ, ‖1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))‖ ≤ G ζ := by
  have hab' : (a : ℂ) ≠ b := by exact_mod_cast hab
  have hac' : (a : ℂ) ≠ c := by exact_mod_cast hac
  have hbc' : (b : ℂ) ≠ c := by exact_mod_cast hbc
  have hat' : (a : ℂ) ≠ t := by exact_mod_cast hta.symm
  have hbt' : (b : ℂ) ≠ t := by exact_mod_cast htb.symm
  have hct' : (c : ℂ) ≠ t := by exact_mod_cast htc.symm
  set G : ℂ → ℝ := fun ζ =>
    2 * ‖((a : ℂ) - -I) ^ 2 / (((a : ℂ) - b) * ((a : ℂ) - c) * ((a : ℂ) - t))‖ * (((1 + ‖ζ‖) ^ 2)⁻¹ * ‖ζ - a‖⁻¹) +
    2 * ‖((b : ℂ) - -I) ^ 2 / (((b : ℂ) - a) * ((b : ℂ) - c) * ((b : ℂ) - t))‖ * (((1 + ‖ζ‖) ^ 2)⁻¹ * ‖ζ - b‖⁻¹) +
    2 * ‖((c : ℂ) - -I) ^ 2 / (((c : ℂ) - a) * ((c : ℂ) - b) * ((c : ℂ) - t))‖ * (((1 + ‖ζ‖) ^ 2)⁻¹ * ‖ζ - c‖⁻¹) +
    2 * ‖((t : ℂ) - -I) ^ 2 / (((t : ℂ) - a) * ((t : ℂ) - b) * ((t : ℂ) - c))‖ * (((1 + ‖ζ‖) ^ 2)⁻¹ * ‖ζ - t‖⁻¹)
    with hG
  have hG0 : ∀ ζ, 0 ≤ G ζ := fun ζ => by simp only [hG]; positivity
  have hGc : ∀ ζ, G (conj ζ) = G ζ := fun ζ => by
    have hs : ∀ s : ℝ, ‖conj ζ - s‖ = ‖ζ - s‖ := fun s => by
      calc ‖conj ζ - s‖ = ‖conj (ζ - (s : ℂ))‖ := by rw [map_sub, Complex.conj_ofReal]
        _ = ‖ζ - s‖ := Complex.norm_conj _
    simp only [hG, Complex.norm_conj, hs]
  have hup : ∀ ζ : ℂ, 0 ≤ ζ.im → ‖1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))‖ ≤ G ζ := by
    intro ζ him
    by_cases hp : ζ = a ∨ ζ = b ∨ ζ = c ∨ ζ = t
    · rcases hp with h | h | h | h <;> simp [h, hG0]
    · push Not at hp
      obtain ⟨h1, h2, h3, h4⟩ := hp
      have hqI : ζ ≠ -I := by
        intro h
        rw [h] at him
        norm_num at him
      rw [s36b_pf4 hab' hac' hat' hbc' hbt' hct' hqI h1 h2 h3 h4]
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add ?_ ?_)) ?_)) ?_) <;>
      (rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (s36b_term_le _ him) (norm_nonneg _)).trans_eq (by ring))
  refine ⟨G, ((((s36b_prof_integrable _).const_mul _).add ((s36b_prof_integrable _).const_mul _)).add
      ((s36b_prof_integrable _).const_mul _)).add ((s36b_prof_integrable _).const_mul _), fun ζ => ?_⟩
  by_cases him : 0 ≤ ζ.im
  · exact hup ζ him
  · have h1 := hup (conj ζ) (by rw [Complex.conj_im]; linarith)
    have e := s36b_kernel_conj a b c t ζ
    simp only at e
    rw [e, Complex.norm_conj, hGc] at h1
    exact h1

/-- The entries of `γ⁻¹`. -/
theorem s36x_inv_entries (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    γ⁻¹ 0 0 = γ 1 1 ∧ γ⁻¹ 0 1 = -γ 0 1 ∧ γ⁻¹ 1 0 = -γ 1 0 ∧ γ⁻¹ 1 1 = γ 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

/-- On `Ω'`, no term of the Poincaré series has its pole: `cz + d ≠ 0` (the orbit of `∞` is removed). -/
theorem s36x_den_ne {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) {z : ℂ}
    (hinf : ∀ γ ∈ Γ, (γ 1 0 : ℝ) ≠ 0 → z ≠ ((γ 0 0 / γ 1 0 : ℝ) : ℂ)) :
    (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := by
  intro h0
  have hdet := b33_d_det γ
  obtain ⟨e00, -, e10, -⟩ := s36x_inv_entries γ
  by_cases hc : γ 1 0 = 0
  · rw [hc] at h0 hdet
    simp only [Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_eq_zero] at h0
    rw [h0] at hdet
    simp at hdet
  · apply hinf γ⁻¹ (Γ.inv_mem hγ) (by rw [e10]; exact neg_ne_zero.2 hc)
    rw [e00, e10]
    have hc' : (γ 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
    rw [Complex.ofReal_div, Complex.ofReal_neg, eq_div_iff (neg_ne_zero.2 hc')]
    linear_combination -h0

/-- On `Ω'`, no term of the Poincaré series hits a pole of the kernel. -/
theorem s36x_pole_ne {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) {z : ℂ} {P : Finset ℝ}
    (hd : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0)
    (hpole : ∀ γ ∈ Γ, ∀ s ∈ P, (γ 1 0 : ℝ) * s + γ 1 1 ≠ 0 → z ≠ h36p_m γ (s : ℂ)) :
    ∀ s ∈ P, h36p_m γ z ≠ (s : ℂ) := by
  intro s hs h
  have hdetC : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast b33_d_det γ
  obtain ⟨e00, e01, e10, e11⟩ := s36x_inv_entries γ
  have hm : ((γ 0 0 : ℂ) * z + γ 0 1) = s * ((γ 1 0 : ℂ) * z + γ 1 1) := by
    simp only [h36p_m] at h
    rw [div_eq_iff hd] at h
    exact h
  have hden : (γ⁻¹ 1 0 : ℝ) * s + γ⁻¹ 1 1 ≠ 0 := by
    rw [e10, e11]
    intro h0
    have h0' : (-(γ 1 0 : ℂ)) * s + γ 0 0 = 0 := by exact_mod_cast h0
    exact one_ne_zero (by linear_combination ((γ 1 1 : ℂ) + (γ 1 0 : ℂ) * z) * h0' - (γ 1 0 : ℂ) * hm - hdetC)
  apply hpole γ⁻¹ (Γ.inv_mem hγ) s hs hden
  have hden' : ((γ⁻¹ 1 0 : ℝ) : ℂ) * s + ((γ⁻¹ 1 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hden
  simp only [h36p_m]
  rw [eq_div_iff hden', e00, e01, e10, e11]
  push_cast
  linear_combination hm

/-- Cocycle identity for one term of a Poincaré series: `f(δγz) j(δ, γz)⁻⁴ j(γ, z)⁻⁴ = f((δγ)z) j(δγ, z)⁻⁴`
(no condition on `j(δ, γz)`; both sides vanish when it is `0`). -/
theorem s36x_term_mul (f : ℂ → ℂ) (δ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ}
    (hd : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0) :
    f (h36p_m δ (h36p_m γ z)) / ((δ 1 0 : ℂ) * h36p_m γ z + δ 1 1) ^ 4 / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 =
      f (h36p_m (δ * γ) z) / (((δ * γ) 1 0 : ℂ) * z + (δ * γ) 1 1) ^ 4 := by
  have hmD : h36p_m γ z * ((γ 1 0 : ℂ) * z + γ 1 1) = (γ 0 0 : ℂ) * z + γ 0 1 := div_mul_cancel₀ _ hd
  have eD : (((δ * γ) 1 0 : ℝ) : ℂ) * z + ((δ * γ) 1 1 : ℝ) =
      ((δ 1 0 : ℂ) * h36p_m γ z + δ 1 1) * ((γ 1 0 : ℂ) * z + γ 1 1) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    linear_combination (-(δ 1 0 : ℂ)) * hmD
  have eN : (((δ * γ) 0 0 : ℝ) : ℂ) * z + ((δ * γ) 0 1 : ℝ) =
      ((δ 0 0 : ℂ) * h36p_m γ z + δ 0 1) * ((γ 1 0 : ℂ) * z + γ 1 1) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    linear_combination (-(δ 0 0 : ℂ)) * hmD
  have hm : h36p_m (δ * γ) z = h36p_m δ (h36p_m γ z) := by
    show ((((δ * γ) 0 0 : ℝ) : ℂ) * z + ((δ * γ) 0 1 : ℝ)) / ((((δ * γ) 1 0 : ℝ) : ℂ) * z + ((δ * γ) 1 1 : ℝ)) = _
    rw [eN, eD, mul_div_mul_right _ _ hd]
    rfl
  rw [hm, eD, mul_pow, div_div]

/-- Reindexing the theta series under a group element, away from its affine pole.
This isolates the finite algebra from the analytic convergence proof. -/
theorem s36x_theta_reindex (f : ℂ → ℂ)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) {z : ℂ}
    (hd : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0) :
    h36p_theta Γ f (h36p_m γ z) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 =
      h36p_theta Γ f z := by
  change (∑' δ : Γ, f (h36p_m δ.1 (h36p_m γ z)) /
      ((δ.1 1 0 : ℂ) * h36p_m γ z + δ.1 1 1) ^ 4) /
        ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 =
      ∑' δ : Γ, f (h36p_m δ.1 z) / ((δ.1 1 0 : ℂ) * z + δ.1 1 1) ^ 4
  rw [← tsum_div_const]
  calc
    (∑' δ : Γ, (f (h36p_m δ.1 (h36p_m γ z)) /
        ((δ.1 1 0 : ℂ) * h36p_m γ z + δ.1 1 1) ^ 4) /
          ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4) =
        ∑' δ : Γ, f (h36p_m (δ.1 * γ) z) /
          (((δ.1 * γ) 1 0 : ℂ) * z + (δ.1 * γ) 1 1) ^ 4 := by
      exact tsum_congr (fun δ => s36x_term_mul f δ.1 γ hd)
    _ = ∑' δ : Γ, f (h36p_m δ.1 z) /
        ((δ.1 1 0 : ℂ) * z + δ.1 1 1) ^ 4 := by
      exact (Equiv.mulRight (⟨γ, hγ⟩ : Γ)).tsum_eq
        (fun δ : Γ => f (h36p_m δ.1 z) /
          ((δ.1 1 0 : ℂ) * z + δ.1 1 1) ^ 4)

/-- **(X) The Poincaré series of a 4-pole kernel is holomorphic and automorphic on `Ω'({a,b,c,t})`** (精英下属4):
locally uniform convergence near every ordinary point off the pole orbits (proper discontinuity on `Ω`); the
automorphy is a reindexing of the series. -/
theorem s36x_theta_mero (hΓ : IsFuchsian Γ) {a b c t : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hta : t ≠ a) (htb : t ≠ b) (htc : t ≠ c) {Ω : Set ℂ}
    (hΩ : ∀ z : ℂ, z ∈ Ω ↔ ((z : ExtPlane) ∉ fuchsianLimitSet Γ ∧
      (∀ γ ∈ Γ, ∀ s ∈ ({a, b, c, t} : Finset ℝ), (γ 1 0 : ℝ) * s + γ 1 1 ≠ 0 → z ≠ h36p_m γ (s : ℂ)) ∧
      (∀ γ ∈ Γ, (γ 1 0 : ℝ) ≠ 0 → z ≠ ((γ 0 0 / γ 1 0 : ℝ) : ℂ)))) :
    DifferentiableOn ℂ (h36p_theta Γ (fun ζ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t)))) Ω ∧
      ∀ γ ∈ Γ, ∀ z ∈ Ω,
        h36p_theta Γ (fun ζ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))) (h36p_m γ z) /
          ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 =
        h36p_theta Γ (fun ζ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t))) z := by
  classical
  set k : ℂ → ℂ := fun ζ => 1 / ((ζ - a) * (ζ - b) * (ζ - c) * (ζ - t)) with hkdef
  set T : Γ → ℂ → ℂ := fun γ w => k (h36p_m γ.1 w) / ((γ.1 1 0 : ℂ) * w + γ.1 1 1) ^ 4 with hTdef
  have hθ : h36p_theta Γ k = fun w => ∑' γ, T γ w := rfl
  have hkd : ∀ ζ : ℂ, ζ ≠ a → ζ ≠ b → ζ ≠ c → ζ ≠ t → DifferentiableAt ℂ k ζ := fun ζ h1 h2 h3 h4 =>
    (differentiableAt_const _).div (by fun_prop) (mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.2 h1)
      (sub_ne_zero.2 h2)) (sub_ne_zero.2 h3)) (sub_ne_zero.2 h4))
  have hTd : ∀ γ : Γ, ∀ w : ℂ, (γ.1 1 0 : ℂ) * w + γ.1 1 1 ≠ 0 → h36p_m γ.1 w ≠ a → h36p_m γ.1 w ≠ b →
      h36p_m γ.1 w ≠ c → h36p_m γ.1 w ≠ t → DifferentiableAt ℂ (T γ) w := by
    intro γ w hd h1 h2 h3 h4
    exact ((hkd _ h1 h2 h3 h4).comp w (s36x_m_hasDerivAt γ.1 hd).differentiableAt).div (by fun_prop)
      (pow_ne_zero _ hd)
  refine ⟨fun z₀ hz₀ => (?_ : DifferentiableAt ℂ _ z₀).differentiableWithinAt, ?_⟩
  · obtain ⟨hΛ, hpole, hinf⟩ := (hΩ z₀).1 hz₀
    have hT0 : ∀ γ : Γ, DifferentiableAt ℂ (T γ) z₀ := by
      intro γ
      have hd := s36x_den_ne γ.2 hinf
      have hp := s36x_pole_ne γ.2 hd hpole
      exact hTd γ z₀ hd (hp a (by simp)) (hp b (by simp)) (hp c (by simp)) (hp t (by simp))
    -- a compact disc of ordinary points
    have hcl := s36x_limitSet_closed hΓ
    have hopen : IsOpen (((↑) : ℂ → ExtPlane) ⁻¹' (fuchsianLimitSet Γ)ᶜ) :=
      hcl.isOpen_compl.preimage OnePoint.continuous_coe
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 hopen z₀ hΛ
    set r : ℝ := ρ / 3 with hr
    have hr0 : 0 < r := by positivity
    have hKΩ : ∀ w ∈ closedBall z₀ (2 * r), ((w : ℂ) : ExtPlane) ∉ fuchsianLimitSet Γ := fun w hw =>
      hρsub (closedBall_subset_ball (by rw [hr]; linarith) hw)
    have hKc : IsCompact (closedBall z₀ (2 * r)) := isCompact_closedBall _ _
    -- the finitely many terms with a pole over the disc
    set P : Set ExtPlane := {extInf, ((a : ℂ) : ExtPlane), ((b : ℂ) : ExtPlane), ((c : ℂ) : ExtPlane),
      ((t : ℂ) : ExtPlane)} with hPdef
    have hBadfin : {γ : Γ | ∃ w ∈ closedBall z₀ (2 * r),
        mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ.1) (w : ExtPlane) ∈ P}.Finite := by
      refine ((Set.toFinite P).biUnion fun p _ => s36x_hit_fin hΓ hKc hKΩ p).subset ?_
      rintro γ ⟨w, hw, hp⟩
      exact mem_biUnion hp ⟨w, hw, rfl⟩
    set Bad := hBadfin.toFinset with hBad
    have hgood : ∀ γ : Γ, γ ∉ Bad → ∀ w ∈ closedBall z₀ (2 * r), (γ.1 1 0 : ℂ) * w + γ.1 1 1 ≠ 0 ∧
        h36p_m γ.1 w ≠ a ∧ h36p_m γ.1 w ≠ b ∧ h36p_m γ.1 w ≠ c ∧ h36p_m γ.1 w ≠ t := by
      intro γ hγ w hw
      have hγ' : ¬ ∃ w ∈ closedBall z₀ (2 * r),
          mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ.1) (w : ExtPlane) ∈ P := fun h =>
        hγ (hBadfin.mem_toFinset.2 h)
      have hd : (γ.1 1 0 : ℂ) * w + γ.1 1 1 ≠ 0 := by
        intro h0
        exact hγ' ⟨w, hw, by rw [s36x_msl_inf γ.1 h0]; simp [hPdef]⟩
      have hm : ∀ s : ℝ, ((s : ℂ) : ExtPlane) ∈ P → h36p_m γ.1 w ≠ s := by
        intro s hs h
        exact hγ' ⟨w, hw, by rw [s36x_msl_coe γ.1 hd, h]; exact hs⟩
      exact ⟨hd, hm a (by simp [hPdef]), hm b (by simp [hPdef]), hm c (by simp [hPdef]), hm t (by simp [hPdef])⟩
    have hTU : ∀ γ : Γ, γ ∉ Bad → DifferentiableOn ℂ (T γ) (ball z₀ (2 * r)) := fun γ hγ w hw => by
      obtain ⟨hd, h1, h2, h3, h4⟩ := hgood γ hγ w (ball_subset_closedBall hw)
      exact (hTd γ w hd h1 h2 h3 h4).differentiableWithinAt
    -- the summable majorant (area mean value + multiplicity)
    obtain ⟨G, hG, hGle⟩ := s36x_k_bound hab hac hbc hta htb htc
    have hkint : ∫⁻ ζ, ENNReal.ofReal ‖k ζ‖ < ⊤ :=
      (lintegral_mono fun ζ => ENNReal.ofReal_le_ofReal (hGle ζ)).trans_lt hG.lintegral_lt_top
    have hkm : Measurable fun ζ => ENNReal.ofReal ‖k ζ‖ := by
      simp only [hkdef]
      fun_prop
    obtain ⟨N, hN⟩ := s36x_mult hΓ hKc hKΩ measurableSet_ball ball_subset_closedBall Bad
      (fun γ hγ w hw => (hgood γ hγ w hw).1) (fun ζ => ENNReal.ofReal ‖k ζ‖) hkm
    set s : ℝ := r / 2 with hs
    have hs0 : 0 < s := by positivity
    set u : {γ : Γ // γ ∉ Bad} → ℝ := fun γ =>
      (∫⁻ x in h36p_m γ.1.1 '' ball z₀ (2 * r), ENNReal.ofReal ‖k x‖).toReal / (π * s ^ 2) with hu
    have hsum : ∑' γ : {γ : Γ // γ ∉ Bad}, ∫⁻ x in h36p_m γ.1.1 '' ball z₀ (2 * r), ENNReal.ofReal ‖k x‖ ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) hkint.ne) hN
    have husum : Summable u := (ENNReal.summable_toReal hsum).div_const _
    have hTle : ∀ γ : {γ : Γ // γ ∉ Bad}, ∀ w ∈ ball z₀ r, ‖T γ.1 w‖ ≤ u γ := by
      intro γ w hw
      have hsub : closedBall w s ⊆ ball z₀ (2 * r) := by
        intro ζ hζ
        rw [Metric.mem_closedBall] at hζ
        rw [Metric.mem_ball] at hw ⊢
        calc dist ζ z₀ ≤ dist ζ w + dist w z₀ := dist_triangle _ _ _
          _ < 2 * r := by rw [hs] at hζ; linarith
      have hmv := h36p_meanvalue (hTU γ.1 γ.2) hs0 hsub
      have h2 : ∫⁻ z in ball w s, ENNReal.ofReal ‖T γ.1 z‖ ≤ ∫⁻ z in ball z₀ (2 * r), ENNReal.ofReal ‖T γ.1 z‖ :=
        lintegral_mono_set (ball_subset_closedBall.trans hsub)
      have h3 : ∫⁻ z in ball z₀ (2 * r), ENNReal.ofReal ‖T γ.1 z‖ =
          ∫⁻ x in h36p_m γ.1.1 '' ball z₀ (2 * r), ENNReal.ofReal ‖k x‖ := by
        rw [s36x_lintegral_image γ.1.1 measurableSet_ball
          (fun z hz => (hgood γ.1 γ.2 z (ball_subset_closedBall hz)).1)]
        refine setLIntegral_congr_fun measurableSet_ball fun z _ => ?_
        simp only [hTdef]
        rw [h36p_b_norm_term, ENNReal.ofReal_mul (norm_nonneg _)]
      have hfin : ∫⁻ x in h36p_m γ.1.1 '' ball z₀ (2 * r), ENNReal.ofReal ‖k x‖ ≠ ⊤ :=
        ne_top_of_le_ne_top hkint.ne (setLIntegral_le_lintegral _ _)
      have h4 := hmv.trans (h2.trans h3.le)
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_toReal hfin,
        ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg] at h4
      simp only [hu]
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hsumm : ∀ w ∈ ball z₀ r, Summable (fun γ : Γ => T γ w) := fun w hw =>
      (Finset.summable_compl_iff Bad).1 (Summable.of_norm_bounded husum fun γ => hTle γ w hw)
    have hdec : ∀ w ∈ ball z₀ r, h36p_theta Γ k w =
        (∑ γ ∈ Bad, T γ w) + ∑' γ : {γ : Γ // γ ∉ Bad}, T γ.1 w :=
      fun w hw => ((hsumm w hw).sum_add_tsum_subtype_compl Bad).symm
    have hD2 : DifferentiableOn ℂ (fun w => ∑' γ : {γ : Γ // γ ∉ Bad}, T γ.1 w) (ball z₀ r) :=
      differentiableOn_tsum_of_summable_norm husum
        (fun γ => (hTU γ.1 γ.2).mono (ball_subset_ball (by linarith))) isOpen_ball (fun γ w hw => hTle γ w hw)
    have hD1 : DifferentiableAt ℂ (fun w => ∑ γ ∈ Bad, T γ w) z₀ := DifferentiableAt.fun_sum fun γ _ => hT0 γ
    have hD := hD1.add (hD2.differentiableAt (ball_mem_nhds z₀ hr0))
    exact hD.congr_of_eventuallyEq (Filter.eventually_of_mem (ball_mem_nhds z₀ hr0) hdec)
  · intro γ hγ z hz
    obtain ⟨-, -, hinf⟩ := (hΩ z).1 hz
    have hd := s36x_den_ne hγ hinf
    exact s36x_theta_reindex k hγ hd

end LiZhongQC
