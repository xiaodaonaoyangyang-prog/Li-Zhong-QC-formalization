import LiZhongQC.Lemmas.FoundationQuotient
import LiZhongQC.Lemmas.FoundationCuspEnds

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- A precisely invariant end containing a whole lower horizontal strip forces the
entire group into its cyclic stabilizer. This discharges the lower-side alternative. -/
theorem ft1gc_lower_strip_elementary
    (π₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (W : Set UpperHalfPlane)
    (δ : ℝ) (hδ : 0 < δ)
    (hstrip : {τ : UpperHalfPlane | τ.im < δ} ⊆ W)
    (hprec : ∀ γ ∈ Γ, ∀ τ : UpperHalfPlane,
      τ ∈ W → γ • τ ∈ W → ∃ k : ℤ, γ = π₀ ^ k ∨ γ = -π₀ ^ k) :
    ∀ γ ∈ Γ, ∃ k : ℤ, γ = π₀ ^ k ∨ γ = -π₀ ^ k := by
  intro γ hγ
  obtain ⟨x, hx⟩ : ∃ x : ℝ, γ 1 0 * x + γ 1 1 ≠ 0 := by
    by_cases hd : γ 1 1 = 0
    · have hc : γ 1 0 ≠ 0 := by
        intro hc
        have hdet := hnf_sl2_det γ
        rw [hc, hd] at hdet
        norm_num at hdet
      exact ⟨1, by simpa only [mul_one, hd, add_zero] using hc⟩
    · exact ⟨0, by simpa only [mul_zero, zero_add] using hd⟩
  let b : ℝ := γ 1 0 * x + γ 1 1
  have hb : 0 < b ^ 2 := sq_pos_of_ne_zero hx
  let y : ℝ := min (δ / 2) (δ * b ^ 2 / 2)
  have hy : 0 < y := lt_min (by positivity) (by positivity)
  have hyδ : y < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hyb : y < δ * b ^ 2 :=
    lt_of_le_of_lt (min_le_right _ _) (by have := mul_pos hδ hb; linarith)
  let τ : UpperHalfPlane := ⟨(x : ℂ) + (y : ℂ) * I, by simpa using hy⟩
  have hτim : τ.im = y := by
    change ((x : ℂ) + (y : ℂ) * I).im = y
    simp
  have hden : Complex.normSq ((γ 1 0 : ℂ) * (τ : ℂ) + γ 1 1) =
      b ^ 2 + (γ 1 0 * y) ^ 2 := by
    simp [τ, b, Complex.normSq_apply] <;> ring
  have hdenpos : 0 < b ^ 2 + (γ 1 0 * y) ^ 2 :=
    add_pos_of_pos_of_nonneg hb (sq_nonneg _)
  have him : (γ • τ).im < δ := by
    have hcoe : (γ • τ).im = ((γ • τ : UpperHalfPlane) : ℂ).im := rfl
    rw [hcoe, h36t_coe_smul, utm_im_mobius (hnf_sl2_det γ), hden]
    change τ.im / (b ^ 2 + (γ 1 0 * y) ^ 2) < δ
    rw [hτim]
    apply (div_lt_iff₀ hdenpos).2
    nlinarith [mul_nonneg hδ.le (sq_nonneg (γ 1 0 * y))]
  exact hprec γ hγ τ (hstrip (by change τ.im < δ; rw [hτim]; exact hyδ)) (hstrip him)

end LiZhongQC
end -- source noncomputable section

/- Source: FoundationPeriodicBands.lean -/
/-! Source-only quantitative input to the approved parabolic side-collar contract. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

/-- A continuous translation-periodic upper-half-plane curve has a uniform strictly
positive lower height and a finite upper height. No injectivity or properness is needed
for this quantitative lemma; those are used only in the subsequent separation step. -/
theorem ft1gc_parabolic_boundary_band (ρ : ℝ → UpperHalfPlane) (hρ : Continuous ρ)
    (hperiod : ∀ t : ℝ, ρ (t + 1) = (1 : ℝ) +ᵥ ρ t) :
    ∃ δ Y : ℝ, 0 < δ ∧ δ < Y ∧ 1 < Y ∧ ∀ t : ℝ, δ < (ρ t).im ∧ (ρ t).im < Y := by
  have hcont : Continuous (fun t : ℝ => (ρ t).im) := UpperHalfPlane.continuous_im.comp hρ
  obtain ⟨a, ha, hlow⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_forall_le'
    hcont.continuousOn (a := (0 : ℝ)) (fun t _ => (ρ t).im_pos)
  obtain ⟨M, hM⟩ := ((isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).image hcont).isBounded.bddAbove
  let δ : ℝ := a / 2
  let Y : ℝ := max M (max a 1) + 1
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hδY : δ < Y := by
    have h1 := le_max_left a (1 : ℝ)
    have h2 := le_max_right M (max a 1)
    dsimp only [δ, Y]
    linarith
  have hY : 1 < Y := by
    have h1 := le_max_right a (1 : ℝ)
    have h2 := le_max_right M (max a 1)
    dsimp only [Y]
    linarith
  have hper : Function.Periodic (fun t : ℝ => (ρ t).im) 1 := by
    intro t
    show (ρ (t + 1)).im = (ρ t).im
    rw [hperiod, UpperHalfPlane.vadd_im]
  refine ⟨δ, Y, hδ, hδY, hY, ?_⟩
  intro t
  have hu : t - (⌊t⌋ : ℤ) ∈ Icc (0 : ℝ) 1 := by
    have hl := Int.floor_le t
    have hh := Int.lt_floor_add_one t
    exact ⟨by linarith, by linarith⟩
  have heq : (ρ (t - (⌊t⌋ : ℤ))).im = (ρ t).im := by
    simpa only [mul_one] using hper.sub_int_mul_eq (x := t) (⌊t⌋ : ℤ)
  have hl := hlow _ hu
  have hh : (ρ (t - (⌊t⌋ : ℤ))).im ≤ M := hM ⟨t - (⌊t⌋ : ℤ), hu, rfl⟩
  rw [heq] at hl hh
  have hMY : M < Y := lt_of_le_of_lt (le_max_left M (max a 1)) (lt_add_one _)
  exact ⟨by dsimp only [δ]; linarith, hh.trans_lt hMY⟩

/-- The horizontal coordinate of a translation-periodic boundary differs from its
parameter by a bounded periodic function; in particular its two ends escape in opposite
real directions. -/
theorem ft1gc_parabolic_real_ends (ρ : ℝ → UpperHalfPlane) (hρ : Continuous ρ)
    (hperiod : ∀ t : ℝ, ρ (t + 1) = (1 : ℝ) +ᵥ ρ t) :
    Tendsto (fun t : ℝ => (ρ t).re) atTop atTop ∧
      Tendsto (fun t : ℝ => (ρ t).re) atBot atBot := by
  have hc : Continuous (fun t : ℝ => (ρ t).re - t) :=
    (UpperHalfPlane.continuous_re.comp hρ).sub continuous_id
  have hp : Function.Periodic (fun t : ℝ => (ρ t).re - t) 1 := by
    intro t
    show (ρ (t + 1)).re - (t + 1) = (ρ t).re - t
    rw [hperiod, UpperHalfPlane.vadd_re]
    ring
  have hb := hp.isBounded_of_continuous one_ne_zero hc
  obtain ⟨a, ha⟩ := hb.bddBelow
  obtain ⟨b, hb⟩ := hb.bddAbove
  constructor
  · apply Filter.tendsto_atTop.2
    intro c
    filter_upwards [eventually_ge_atTop (c - a)] with t ht
    have hlow := ha ⟨t, rfl⟩
    linarith
  · apply Filter.tendsto_atBot.2
    intro c
    filter_upwards [eventually_le_atBot (c - b)] with t ht
    have hhigh := hb ⟨t, rfl⟩
    linarith

/-- The logarithmic radius of a multiplicatively periodic curve differs from
`t * log lam` by a bounded periodic function. This keeps the endpoint proof separate
from the later Jordan-side identification. -/
theorem ft1gc_hyperbolic_log_drift (ρ : ℝ → UpperHalfPlane) (hρ : Continuous ρ)
    (lam : ℝ) (hlam : 1 < lam)
    (hperiod : ∀ t : ℝ, (ρ (t + 1) : ℂ) = (lam : ℂ) * (ρ t : ℂ)) :
    ∃ a b : ℝ, ∀ t : ℝ,
      a ≤ Real.log ‖(ρ t : ℂ)‖ - t * Real.log lam ∧
      Real.log ‖(ρ t : ℂ)‖ - t * Real.log lam ≤ b := by
  have hlam0 : 0 < lam := lt_trans zero_lt_one hlam
  have hnorm : Continuous (fun t : ℝ => ‖(ρ t : ℂ)‖) :=
    continuous_norm.comp (UpperHalfPlane.continuous_coe.comp hρ)
  have hlog : Continuous (fun t : ℝ => Real.log ‖(ρ t : ℂ)‖) :=
    hnorm.log (fun t => norm_ne_zero_iff.2 (ρ t).ne_zero)
  have hc : Continuous (fun t : ℝ => Real.log ‖(ρ t : ℂ)‖ - t * Real.log lam) :=
    hlog.sub (continuous_id.mul continuous_const)
  have hp : Function.Periodic (fun t : ℝ => Real.log ‖(ρ t : ℂ)‖ - t * Real.log lam) 1 := by
    intro t
    show Real.log ‖(ρ (t + 1) : ℂ)‖ - (t + 1) * Real.log lam =
      Real.log ‖(ρ t : ℂ)‖ - t * Real.log lam
    rw [hperiod, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0,
      Real.log_mul hlam0.ne' (norm_ne_zero_iff.2 (ρ t).ne_zero)]
    ring
  have hb := hp.isBounded_of_continuous one_ne_zero hc
  obtain ⟨a, ha⟩ := hb.bddBelow
  obtain ⟨b, hb⟩ := hb.bddAbove
  exact ⟨a, b, fun t => ⟨ha ⟨t, rfl⟩, hb ⟨t, rfl⟩⟩⟩

end LiZhongQC
end -- source noncomputable section

/- Source: FoundationCuspTransitionCore.lean -/
/-!
Source-only normalized matrix core for the approved cusp-transition contract.
The endpoint wrapper will reuse ft2c_conj_T from FoundationCuspEnds after its import
is approved/registered. This file assumes those explicit normalization equalities,
not the coefficient estimate it proves. No new definitions or instances.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Transport a primitive stabilizer through a signed unit-translation normalization. -/
theorem ft1gc_transport_stabilizer
    (A π₀ T : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hconj : A⁻¹ * π₀ * A = T ∨ A⁻¹ * π₀ * A = -T)
    (hstab : ∀ β ∈ Γ, (A⁻¹ * β * A) 1 0 = 0 →
      ∃ k : ℤ, β = π₀ ^ k ∨ β = -π₀ ^ k) :
    ∀ β ∈ conjGroup Γ A⁻¹, β 1 0 = 0 → ∃ k : ℤ, β = T ^ k ∨ β = -T ^ k := by
  intro β hβ hc
  obtain ⟨γ, hγ, rfl⟩ := s30l_mem_conjGroup.1 hβ
  rw [inv_inv] at hc ⊢
  obtain ⟨k, hk⟩ := hstab γ hγ hc
  have hpow : A⁻¹ * π₀ ^ k * A = (A⁻¹ * π₀ * A) ^ k := by
    have heq := map_zpow (MulAut.conj A⁻¹) π₀ k
    simp only [MulAut.conj_apply, inv_inv] at heq
    exact heq
  have hneg : (-T) ^ k = T ^ k ∨ (-T) ^ k = -T ^ k := by
    rcases Int.even_or_odd k with he | ho
    · exact Or.inl (he.neg_zpow T)
    · exact Or.inr (ho.neg_zpow T)
  rcases hk with rfl | rfl
  · rw [hpow]
    rcases hconj with ht | ht
    · exact ⟨k, Or.inl (by rw [ht])⟩
    · rw [ht]
      exact ⟨k, hneg⟩
  · rw [mul_neg, neg_mul, hpow]
    rcases hconj with ht | ht
    · exact ⟨k, Or.inr (by rw [ht])⟩
    · rw [ht]
      rcases hneg with hn | hn
      · exact ⟨k, Or.inr (by rw [hn])⟩
      · exact ⟨k, Or.inl (by rw [hn, neg_neg])⟩

/-- The distinct-cusp coefficient estimate from an explicit signed normalization.
The single-cusp Shimizu theorem is applied to M T M^-1, whose lower-left coefficient
is minus the square of that of M. -/
theorem ft1gc_cusp_transition_normalized (hΓ : IsFuchsian Γ)
    (A₀ A₁ π₀ π₁ T : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hπ₀ : π₀ ∈ Γ) (hπ₁ : π₁ ∈ Γ)
    (hT : T 0 0 = 1 ∧ T 0 1 = 1 ∧ T 1 0 = 0 ∧ T 1 1 = 1)
    (hconj₀ : A₀⁻¹ * π₀ * A₀ = T ∨ A₀⁻¹ * π₀ * A₀ = -T)
    (hconj₁ : A₁⁻¹ * π₁ * A₁ = T ∨ A₁⁻¹ * π₁ * A₁ = -T)
    (hstab₀ : ∀ β ∈ Γ, (A₀⁻¹ * β * A₀) 1 0 = 0 →
      ∃ k : ℤ, β = π₀ ^ k ∨ β = -π₀ ^ k)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hγ : γ ∈ Γ)
    (hc : (A₀⁻¹ * γ * A₁) 1 0 ≠ 0) :
    1 ≤ |(A₀⁻¹ * γ * A₁) 1 0| ∧
      ∀ τ : UpperHalfPlane, 1 < τ.im → (A₀⁻¹ • (γ • (A₁ • τ))).im ≤ 1 := by
  let G := conjGroup Γ A₀⁻¹
  have hG : IsFuchsian G := s30l_isFuchsian_conj hΓ A₀⁻¹
  obtain ⟨Gpm, hpm, hGpm⟩ := s30l_pm_group G
  have hTraw : A₀⁻¹ * π₀ * A₀ ∈ G := by
    exact s30l_mem_conjGroup.2 ⟨π₀, hπ₀, by rw [inv_inv]⟩
  have hTmem : T ∈ Gpm := by
    apply (hpm T).2
    rcases hconj₀ with heq | heq
    · exact Or.inl (heq ▸ hTraw)
    · exact Or.inr (heq ▸ hTraw)
  have hstabG := ft1gc_transport_stabilizer A₀ π₀ T hconj₀ hstab₀
  have hstabpm : ∀ β ∈ Gpm, β 1 0 = 0 → ∃ k : ℤ, β = T ^ k ∨ β = -T ^ k := by
    intro β hβ hb
    rcases (hpm β).1 hβ with hβG | hβG
    · exact hstabG β hβG hb
    · obtain ⟨k, hk | hk⟩ := hstabG (-β) hβG (by
        simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, hb, neg_zero])
      · exact ⟨k, Or.inr (neg_eq_iff_eq_neg.1 hk)⟩
      · exact ⟨k, Or.inl (neg_inj.1 hk)⟩
  let M := A₀⁻¹ * γ * A₁
  let D := M * T * M⁻¹
  have hraw : A₀⁻¹ * (γ * π₁ * γ⁻¹) * A₀ ∈ G := by
    exact s30l_mem_conjGroup.2
      ⟨γ * π₁ * γ⁻¹, Γ.mul_mem (Γ.mul_mem hγ hπ₁) (Γ.inv_mem hγ), by rw [inv_inv]⟩
  have heq : M * (A₁⁻¹ * π₁ * A₁) * M⁻¹ = A₀⁻¹ * (γ * π₁ * γ⁻¹) * A₀ := by
    dsimp only [M]
    group
  have hDmem : D ∈ Gpm := by
    apply (hpm D).2
    rcases hconj₁ with ht | ht
    · left
      change M * T * M⁻¹ ∈ G
      rw [ht] at heq
      rw [heq]
      exact hraw
    · right
      change -(M * T * M⁻¹) ∈ G
      rw [ht] at heq
      simp only [mul_neg, neg_mul] at heq
      rw [heq]
      exact hraw
  have hDc : D 1 0 = -(M 1 0 ^ 2) := (conj_translation_entries hT M).2.2.1
  have hDc0 : D 1 0 ≠ 0 := by
    rw [hDc]
    exact neg_ne_zero.2 (pow_ne_zero 2 hc)
  have hnot : ∀ k : ℤ, D ≠ T ^ k ∧ D ≠ -T ^ k := by
    intro k
    have hk0 : (T ^ k) 1 0 = 0 := (s30l_zpow_entries hT k).2.2.1
    constructor
    · intro he
      exact hDc0 (by rw [he, hk0])
    · intro he
      exact hDc0 (by rw [he]; simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, hk0, neg_zero])
  have hbound := (parabolic_horoball_disjoint (hGpm hG) hTmem hT hstabpm hDmem hnot).1
  rw [hDc, abs_neg, abs_pow, sq_abs] at hbound
  have hMc : 1 ≤ |M 1 0| := by
    by_contra hlt
    push_neg at hlt
    nlinarith [sq_abs (M 1 0), abs_nonneg (M 1 0)]
  refine ⟨hMc, ?_⟩
  intro τ hτ
  have hfirst := s30l_im_smul_le hMc τ
  have hinv : 1 / τ.im ≤ 1 := (div_le_iff₀ τ.im_pos).2 (by simpa only [one_mul] using hτ.le)
  have htotal := hfirst.trans hinv
  simpa only [M, mul_smul] using htotal

/-- Distinct width-one cusp coordinates have transition coefficient of magnitude at
least one. Same-fixed-point transitions are explicitly excluded by the nonzero coefficient. -/
theorem ft1gc_cusp_transition_bound (hΓ : IsFuchsian Γ)
    (A₀ A₁ π₀ π₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hπ₀ : π₀ ∈ Γ) (hπ₁ : π₁ ∈ Γ)
    (htrans₀ : ∀ τ : UpperHalfPlane, π₀ • (A₀ • τ) = A₀ • ((1 : ℝ) +ᵥ τ))
    (htrans₁ : ∀ τ : UpperHalfPlane, π₁ • (A₁ • τ) = A₁ • ((1 : ℝ) +ᵥ τ))
    (hstab₀ : ∀ β ∈ Γ, (A₀⁻¹ * β * A₀) 1 0 = 0 →
      ∃ k : ℤ, β = π₀ ^ k ∨ β = -π₀ ^ k)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hγ : γ ∈ Γ)
    (hc : (A₀⁻¹ * γ * A₁) 1 0 ≠ 0) :
    1 ≤ |(A₀⁻¹ * γ * A₁) 1 0| ∧
      ∀ τ : UpperHalfPlane, 1 < τ.im → (A₀⁻¹ • (γ • (A₁ • τ))).im ≤ 1 := by
  obtain ⟨T₀, hT₀, hconj₀⟩ := ft2c_conj_T htrans₀
  obtain ⟨T₁, hT₁, hconj₁⟩ := ft2c_conj_T htrans₁
  have hT : T₁ = T₀ := s30l_eq_of_entries
    (hT₁.1.trans hT₀.1.symm) (hT₁.2.1.trans hT₀.2.1.symm)
    (hT₁.2.2.1.trans hT₀.2.2.1.symm) (hT₁.2.2.2.trans hT₀.2.2.2.symm)
  subst T₁
  exact ft1gc_cusp_transition_normalized hΓ A₀ A₁ π₀ π₁ T₀ hπ₀ hπ₁ hT₀
    hconj₀ hconj₁ hstab₀ γ hγ hc

end LiZhongQC
