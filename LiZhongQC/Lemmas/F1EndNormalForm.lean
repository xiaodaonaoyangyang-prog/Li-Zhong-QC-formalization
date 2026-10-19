import LiZhongQC.Lemmas.FoundationQuotient
import LiZhongQC.Lemmas.F1NormalFormAlgebra
import LiZhongQC.Lemmas.FoundationParabolicCollar
import LiZhongQC.Lemmas.FoundationHyperbolicCollar

/- Source: F1ParabolicCoordinate.lean (md5 65b53587887828b30549ab024f57c0be) -/
/-! Algebraic normalization of the actual parabolic period, without extracting
an unproved primitive root. Source-only candidate; no compiler invoked. -/
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC

/-- Normalize h itself or h inverse to translation by +1. -/
theorem ft1fn_parabolic_coordinate
    {h : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hh : IsParabolic h) :
    ∃ (A π₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ),
      (π₀ = h ∨ π₀ = h⁻¹) ∧
      ∀ τ : UpperHalfPlane, π₀ • (A • τ) = A • ((1 : ℝ) +ᵥ τ) := by
  obtain ⟨A₀, hc⟩ := s30l_exists_fix_infty (show 2 ≤ |h 0 0 + h 1 1| from hh.1.ge)
  let g : Matrix.SpecialLinearGroup (Fin 2) ℝ := A₀ * h * A₀⁻¹
  have hgc : g 1 0 = 0 := hc
  have hdet : g 0 0 * g 1 1 = 1 := by
    have hd := hnf_sl2_det g
    simpa only [hgc, mul_zero, sub_zero] using hd
  have htr : |g 0 0 + g 1 1| = 2 := by
    dsimp only [g]
    rw [s27g_trace_conj]
    exact hh.1
  have hsum : (g 0 0 + g 1 1) ^ 2 = 4 := by
    have he := sq_abs (g 0 0 + g 1 1)
    rw [htr] at he
    nlinarith
  have hda : g 1 1 = g 0 0 := by
    have hs : (g 0 0 - g 1 1) ^ 2 = 0 := by nlinarith
    have he := (pow_eq_zero_iff two_ne_zero).1 hs
    linarith
  have hsq : g 0 0 ^ 2 = 1 := by rw [hda] at hdet; nlinarith
  have ha : g 0 0 ≠ 0 := by intro he; rw [he] at hsq; norm_num at hsq
  have hb : g 0 1 ≠ 0 := by
    intro hb0
    have hpm : g 0 0 = 1 ∨ g 0 0 = -1 := by
      have he : (g 0 0 - 1) * (g 0 0 + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 he with he | he
      · left; linarith
      · right; linarith
    have hgpm : g = 1 ∨ g = -1 := by
      rcases hpm with hp | hm
      · left
        exact s30l_eq_of_entries (by simp [hp]) (by simp [hb0])
          (by simp [hgc]) (by simp [hda, hp])
      · right
        exact s30l_eq_of_entries (by simp [hm, Matrix.SpecialLinearGroup.coe_neg])
          (by simp [hb0]) (by simp [hgc])
          (by simp [hda, hm, Matrix.SpecialLinearGroup.coe_neg])
    have hback : h = A₀⁻¹ * g * A₀ := by dsimp only [g]; group
    rcases hgpm with he | he
    · apply hh.2.1
      rw [hback, he]
      group
    · apply hh.2.2
      rw [hback, he]
      simp
  let t : ℝ := g 0 0 * g 0 1
  have ht : t ≠ 0 := mul_ne_zero ha hb
  have hgtrans : ∀ τ : UpperHalfPlane, g • τ = t +ᵥ τ := by
    intro τ
    apply UpperHalfPlane.ext
    rw [h36t_coe_smul, hgc, hda]
    change ((g 0 0 : ℂ) * (τ : ℂ) + g 0 1) / ((0 : ℂ) * τ + g 0 0) =
      (t : ℂ) + (τ : ℂ)
    simp only [zero_mul, zero_add]
    have haC : (g 0 0 : ℂ) ≠ 0 := by exact_mod_cast ha
    have hsC : (g 0 0 : ℂ) ^ 2 = 1 := by exact_mod_cast hsq
    rw [div_eq_iff haC]
    dsimp only [t]
    push_cast
    linear_combination -(g 0 1 : ℂ) * hsC
  let r : ℝ := Real.sqrt |t|
  have hr : 0 < r := Real.sqrt_pos.2 (abs_pos.2 ht)
  have hr2 : r ^ 2 = |t| := Real.sq_sqrt (abs_nonneg t)
  let D : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    ⟨!![r, 0; 0, r⁻¹], by
      rw [Matrix.det_fin_two_of]
      simp [hr.ne']⟩
  have hD : ∀ τ : UpperHalfPlane, ((D • τ : UpperHalfPlane) : ℂ) = ((|t| : ℝ) : ℂ) * (τ : ℂ) := by
    intro τ
    rw [h36t_coe_smul]
    change ((r : ℂ) * (τ : ℂ) + 0) / ((0 : ℂ) * τ + (r⁻¹ : ℝ)) = ((|t| : ℝ) : ℂ) * (τ : ℂ)
    simp only [add_zero, zero_mul, zero_add, Complex.ofReal_inv, div_inv_eq_mul]
    have hrC : (r : ℂ) ^ 2 = ((|t| : ℝ) : ℂ) := by exact_mod_cast hr2
    calc (r : ℂ) * (τ : ℂ) * r = (r : ℂ) ^ 2 * (τ : ℂ) := by ring
      _ = ((|t| : ℝ) : ℂ) * (τ : ℂ) := by rw [hrC]
  let A : Matrix.SpecialLinearGroup (Fin 2) ℝ := A₀⁻¹ * D
  let u : ℝ := t / |t|
  have hAu : ∀ τ : UpperHalfPlane, h • (A • τ) = A • (u +ᵥ τ) := by
    intro τ
    have he : h • (A₀⁻¹ • (D • τ)) = A₀⁻¹ • (g • (D • τ)) := by
      simp only [g, mul_smul, inv_smul_smul]
    change h • ((A₀⁻¹ * D) • τ) = (A₀⁻¹ * D) • (u +ᵥ τ)
    rw [mul_smul, mul_smul, he]
    apply congrArg (fun v : UpperHalfPlane => A₀⁻¹ • v)
    rw [hgtrans]
    apply UpperHalfPlane.ext
    change (t : ℂ) + ((D • τ : UpperHalfPlane) : ℂ) = ((D • (u +ᵥ τ) : UpperHalfPlane) : ℂ)
    rw [hD, hD]
    change (t : ℂ) + ((|t| : ℝ) : ℂ) * (τ : ℂ) = ((|t| : ℝ) : ℂ) * ((u : ℂ) + (τ : ℂ))
    have habs : ((|t| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_ne_zero.2 ht)
    dsimp only [u]
    rw [Complex.ofReal_div, mul_add, mul_div_cancel₀ _ habs]
  rcases lt_or_gt_of_ne ht with htneg | htpos
  · have hu : u = -1 := by
      dsimp only [u]
      rw [abs_of_neg htneg]
      field_simp
    refine ⟨A, h⁻¹, Or.inr rfl, ?_⟩
    intro τ
    have he : h • (A • ((1 : ℝ) +ᵥ τ)) = A • τ := by
      rw [hAu, hu, ← add_vadd]
      simp
    calc h⁻¹ • (A • τ) = h⁻¹ • (h • (A • ((1 : ℝ) +ᵥ τ))) := by rw [he]
      _ = A • ((1 : ℝ) +ᵥ τ) := inv_smul_smul _ _
  · have hu : u = 1 := by
      dsimp only [u]
      rw [abs_of_pos htpos, div_self htpos.ne']
    refine ⟨A, h, Or.inl rfl, ?_⟩
    intro τ
    simpa only [hu] using hAu τ

end LiZhongQC
end -- source noncomputable section

/- Source: F1HalfTurn.lean (md5 6fd57a8aae562137dde5cf026321aabf) -/
/-! Coordinate algebra for the negative hyperbolic collar. The half-turn
z -> -lam/z preserves the closed radial period annulus. Source-only. -/
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC

/-- A real SL2 half-turn, with its action, involution, norm and angle formulas. -/
theorem ft1fn_halfturn_exists (lam : ℝ) (hlam : 0 < lam) :
    ∃ J : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (∀ τ : UpperHalfPlane, ((J • τ : UpperHalfPlane) : ℂ) = -(lam : ℂ) / (τ : ℂ)) ∧
      (∀ τ : UpperHalfPlane, J • (J • τ) = τ) ∧
      (∀ τ : UpperHalfPlane, ‖((J • τ : UpperHalfPlane) : ℂ)‖ = lam / ‖(τ : ℂ)‖) ∧
      (∀ τ : UpperHalfPlane, arg ((J • τ : UpperHalfPlane) : ℂ) = Real.pi - arg (τ : ℂ)) := by
  let r : ℝ := Real.sqrt lam
  have hr : 0 < r := Real.sqrt_pos.2 hlam
  have hr2 : r ^ 2 = lam := Real.sq_sqrt hlam.le
  let J : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    ⟨!![0, -r; r⁻¹, 0], by
      rw [Matrix.det_fin_two_of]
      simp [hr.ne']⟩
  have hformula : ∀ τ : UpperHalfPlane,
      ((J • τ : UpperHalfPlane) : ℂ) = -(lam : ℂ) / (τ : ℂ) := by
    intro τ
    rw [h36t_coe_smul]
    change ((0 : ℂ) * (τ : ℂ) + (-r : ℝ)) / ((r⁻¹ : ℝ) * (τ : ℂ) + 0) = _
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hr2C : (r : ℂ) ^ 2 = (lam : ℂ) := by exact_mod_cast hr2
    simp only [zero_mul, zero_add, add_zero, Complex.ofReal_neg, Complex.ofReal_inv]
    have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
    rw [← hr2C]
    field_simp
    try ring
  have hJJ : ∀ τ : UpperHalfPlane, J • (J • τ) = τ := by
    intro τ
    apply UpperHalfPlane.ext
    rw [hformula, hformula]
    have hlamP : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
    have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
    field_simp
  refine ⟨J, hformula, hJJ, ?_, ?_⟩
  · intro τ
    rw [hformula, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam]
  · intro τ
    have hi : ((τ : ℂ)⁻¹).im < 0 := by
      rw [Complex.inv_im]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos τ.im_pos) τ.normSq_pos
    have hπ : arg (τ : ℂ) ≠ Real.pi := by
      intro he
      exact τ.im_pos.ne' (Complex.arg_eq_pi_iff.1 he).2
    rw [hformula, div_eq_mul_inv, neg_mul, ← mul_neg,
      Complex.arg_real_mul _ hlam, Complex.arg_neg_eq_arg_add_pi_of_im_neg hi,
      Complex.arg_inv, if_neg hπ]
    ring

/-- The half-turn carries a negative-side collar and its compact residual
to the required positive-side collar, with the same angle and radial period. -/
theorem ft1fn_halfturn_collar (lam θ : ℝ) (hlam : 1 < lam)
    (J : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hJJ : ∀ τ : UpperHalfPlane, J • (J • τ) = τ)
    (hnorm : ∀ τ : UpperHalfPlane, ‖((J • τ : UpperHalfPlane) : ℂ)‖ = lam / ‖(τ : ℂ)‖)
    (harg : ∀ τ : UpperHalfPlane, arg ((J • τ : UpperHalfPlane) : ℂ) = Real.pi - arg (τ : ℂ))
    (W : Set UpperHalfPlane)
    (hin : {τ : UpperHalfPlane | Real.pi - θ < arg (τ : ℂ)} ⊆ W)
    (hout : W ⊆ {τ : UpperHalfPlane | θ < arg (τ : ℂ)})
    (hK : IsCompact (closure W ∩ {τ : UpperHalfPlane | 1 ≤ ‖(τ : ℂ)‖ ∧
      ‖(τ : ℂ)‖ ≤ lam ∧ arg (τ : ℂ) ≤ Real.pi - θ})) :
    {τ : UpperHalfPlane | arg (τ : ℂ) < θ} ⊆ (fun τ => J • τ) ⁻¹' W ∧
      (fun τ : UpperHalfPlane => J • τ) ⁻¹' W ⊆ {τ | arg (τ : ℂ) < Real.pi - θ} ∧
      IsCompact (closure ((fun τ : UpperHalfPlane => J • τ) ⁻¹' W) ∩
        {τ : UpperHalfPlane | 1 ≤ ‖(τ : ℂ)‖ ∧ ‖(τ : ℂ)‖ ≤ lam ∧ θ ≤ arg (τ : ℂ)}) := by
  have hlamP : 0 < lam := lt_trans zero_lt_one hlam
  have hband : ∀ τ : UpperHalfPlane,
      (1 ≤ ‖((J • τ : UpperHalfPlane) : ℂ)‖ ∧ ‖((J • τ : UpperHalfPlane) : ℂ)‖ ≤ lam) ↔
        (1 ≤ ‖(τ : ℂ)‖ ∧ ‖(τ : ℂ)‖ ≤ lam) := by
    intro τ
    have hn : 0 < ‖(τ : ℂ)‖ := norm_pos_iff.2 τ.ne_zero
    rw [hnorm, le_div_iff₀ hn, div_le_iff₀ hn, one_mul]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by nlinarith⟩
  refine ⟨?_, ?_, ?_⟩
  · intro τ hτ
    have hτ' : arg (τ : ℂ) < θ := hτ
    apply hin
    change Real.pi - θ < arg ((J • τ : UpperHalfPlane) : ℂ)
    rw [harg]
    linarith
  · intro τ hτ
    have he := hout hτ
    change θ < arg ((J • τ : UpperHalfPlane) : ℂ) at he
    rw [harg] at he
    change arg (τ : ℂ) < Real.pi - θ
    linarith
  · let K : Set UpperHalfPlane := closure W ∩ {τ : UpperHalfPlane | 1 ≤ ‖(τ : ℂ)‖ ∧
        ‖(τ : ℂ)‖ ≤ lam ∧ arg (τ : ℂ) ≤ Real.pi - θ}
    have he : closure ((fun τ : UpperHalfPlane => J • τ) ⁻¹' W) ∩
        {τ : UpperHalfPlane | 1 ≤ ‖(τ : ℂ)‖ ∧ ‖(τ : ℂ)‖ ≤ lam ∧ θ ≤ arg (τ : ℂ)} =
        (fun τ : UpperHalfPlane => J • τ) ⁻¹' K := by
      have hclJ : closure ((fun τ : UpperHalfPlane => J • τ) ⁻¹' W) =
          (fun τ : UpperHalfPlane => J • τ) ⁻¹' closure W :=
        ((Homeomorph.smul J).preimage_closure W).symm
      rw [hclJ]
      ext τ
      change (J • τ ∈ closure W ∧ 1 ≤ ‖(τ : ℂ)‖ ∧ ‖(τ : ℂ)‖ ≤ lam ∧ θ ≤ arg (τ : ℂ)) ↔
        (J • τ ∈ closure W ∧ 1 ≤ ‖((J • τ : UpperHalfPlane) : ℂ)‖ ∧
          ‖((J • τ : UpperHalfPlane) : ℂ)‖ ≤ lam ∧ arg ((J • τ : UpperHalfPlane) : ℂ) ≤ Real.pi - θ)
      constructor
      · rintro ⟨hc, h1, h2, ha⟩
        obtain ⟨h1', h2'⟩ := (hband τ).2 ⟨h1, h2⟩
        exact ⟨hc, h1', h2', by rw [harg]; linarith⟩
      · rintro ⟨hc, h1, h2, ha⟩
        obtain ⟨h1', h2'⟩ := (hband τ).1 ⟨h1, h2⟩
        exact ⟨hc, h1', h2', by rw [harg] at ha; linarith⟩
    have hi : (fun τ : UpperHalfPlane => J • τ) ⁻¹' K = (fun τ : UpperHalfPlane => J • τ) '' K := by
      ext τ
      constructor
      · intro hτ
        exact ⟨J • τ, hτ, hJJ τ⟩
      · rintro ⟨σ, hσ, rfl⟩
        change J • (J • σ) ∈ K
        rwa [hJJ]
    rw [he, hi]
    exact hK.image (continuous_const_smul J)

/-- Reversing the actual hyperbolic generator and adjoining the half-turn to
its coordinate keeps the positive multiplier lam. -/
theorem ft1fn_halfturn_coordinate
    (B h J : Matrix.SpecialLinearGroup (Fin 2) ℝ) (lam : ℝ) (hlam : 0 < lam)
    (hscale : ∀ τ : UpperHalfPlane, ((B⁻¹ • (h • (B • τ)) : UpperHalfPlane) : ℂ) =
      (lam : ℂ) * (τ : ℂ))
    (hformula : ∀ τ : UpperHalfPlane, ((J • τ : UpperHalfPlane) : ℂ) = -(lam : ℂ) / (τ : ℂ))
    (hJJ : ∀ τ : UpperHalfPlane, J • (J • τ) = τ) :
    ∀ τ : UpperHalfPlane, (((B * J)⁻¹ • (h⁻¹ • ((B * J) • τ)) : UpperHalfPlane) : ℂ) =
      (lam : ℂ) * (τ : ℂ) := by
  have hlamP : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hJinv : ∀ τ : UpperHalfPlane, J⁻¹ • τ = J • τ := by
    intro τ
    calc J⁻¹ • τ = J⁻¹ • (J • (J • τ)) := by rw [hJJ]
      _ = J • τ := inv_smul_smul _ _
  have hInv : ∀ τ : UpperHalfPlane,
      ((B⁻¹ • (h⁻¹ • (B • τ)) : UpperHalfPlane) : ℂ) = (lam : ℂ)⁻¹ * (τ : ℂ) := by
    intro τ
    have he := hscale (B⁻¹ • (h⁻¹ • (B • τ)))
    simp only [smul_inv_smul, inv_smul_smul] at he
    calc ((B⁻¹ • (h⁻¹ • (B • τ)) : UpperHalfPlane) : ℂ)
        = (lam : ℂ)⁻¹ * ((lam : ℂ) * ((B⁻¹ • (h⁻¹ • (B • τ)) : UpperHalfPlane) : ℂ)) := by
          field_simp
      _ = (lam : ℂ)⁻¹ * (τ : ℂ) := by rw [← he]
  intro τ
  simp only [mul_inv_rev, mul_smul]
  rw [hJinv, hformula, hInv, hformula]
  field_simp

end LiZhongQC
end -- source noncomputable section

/- Source: EndNormalFormBody.lean (md5 980b120f8af7314d1e8fa638c95405ac) -/
/-! Assembly of the approved `ft1fas_end_normal_form`: split the actual period into the
parabolic and hyperbolic cases, transport the periodic boundary and the exterior through
the normalizing coordinate, and let the oriented collar select the side. No new definitions. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Conjugation commutes with integer powers, in the coordinate direction used below. -/
theorem ft1fen_conj_zpow (A g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (k : ℤ) :
    (A⁻¹ * g * A) ^ k = A⁻¹ * g ^ k * A := by
  have heq := map_zpow (MulAut.conj A⁻¹) g k
  simp only [MulAut.conj_apply, inv_inv] at heq
  exact heq.symm

/-- Transport an embedded proper boundary and its open connected side through the
coordinate `τ ↦ M • τ`: the new curve is `M⁻¹ • ρ` and the new side is the preimage. -/
theorem ft1fen_coord_transport (M : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ρ : ℝ → UpperHalfPlane) (hρ : Topology.IsEmbedding ρ)
    (hproper : ∀ L : Set UpperHalfPlane, IsCompact L → IsCompact (ρ ⁻¹' L))
    (W : Set UpperHalfPlane) (hWo : IsOpen W) (hWc : IsConnected W)
    (hfront : frontier W = Set.range ρ) :
    Topology.IsEmbedding (fun t : ℝ => M⁻¹ • ρ t) ∧
      (∀ L : Set UpperHalfPlane, IsCompact L →
        IsCompact ((fun t : ℝ => M⁻¹ • ρ t) ⁻¹' L)) ∧
      IsOpen ((fun τ : UpperHalfPlane => M • τ) ⁻¹' W) ∧
      IsConnected ((fun τ : UpperHalfPlane => M • τ) ⁻¹' W) ∧
      frontier ((fun τ : UpperHalfPlane => M • τ) ⁻¹' W) =
        Set.range (fun t : ℝ => M⁻¹ • ρ t) := by
  refine ⟨(Homeomorph.smul M⁻¹).isEmbedding.comp hρ, ?_, hWo.preimage (continuous_const_smul M),
    (Homeomorph.smul M).isConnected_preimage.2 hWc, ?_⟩
  · intro L hL
    have hpre : (fun τ : UpperHalfPlane => M⁻¹ • τ) ⁻¹' L =
        (fun τ : UpperHalfPlane => M • τ) '' L := by
      ext τ
      constructor
      · intro hτ
        exact ⟨M⁻¹ • τ, hτ, smul_inv_smul M τ⟩
      · rintro ⟨σ, hσ, rfl⟩
        change M⁻¹ • M • σ ∈ L
        rwa [inv_smul_smul]
    change IsCompact (ρ ⁻¹' ((fun τ : UpperHalfPlane => M⁻¹ • τ) ⁻¹' L))
    rw [hpre]
    exact hproper _ (hL.image (continuous_const_smul M))
  · have hf := (Homeomorph.smul M).preimage_frontier W
    change frontier ((Homeomorph.smul M) ⁻¹' W) = _
    rw [← hf, hfront]
    ext τ
    constructor
    · rintro ⟨t, ht⟩
      change ρ t = M • τ at ht
      refine ⟨t, ?_⟩
      change M⁻¹ • ρ t = τ
      rw [ht, inv_smul_smul]
    · rintro ⟨t, rfl⟩
      refine ⟨t, ?_⟩
      change ρ t = M • (M⁻¹ • ρ t)
      rw [smul_inv_smul]

/-- Reversing the parameter of an embedded proper curve keeps it embedded and proper,
with the same range. -/
theorem ft1fen_reverse (ρ : ℝ → UpperHalfPlane) (hρ : Topology.IsEmbedding ρ)
    (hproper : ∀ L : Set UpperHalfPlane, IsCompact L → IsCompact (ρ ⁻¹' L)) :
    Topology.IsEmbedding (fun t : ℝ => ρ (-t)) ∧
      (∀ L : Set UpperHalfPlane, IsCompact L → IsCompact ((fun t : ℝ => ρ (-t)) ⁻¹' L)) ∧
      Set.range (fun t : ℝ => ρ (-t)) = Set.range ρ := by
  refine ⟨hρ.comp (Homeomorph.neg ℝ).isEmbedding, ?_, ?_⟩
  · intro L hL
    have hc := (hproper L hL).neg
    have he : (fun t : ℝ => ρ (-t)) ⁻¹' L = -(ρ ⁻¹' L) := by
      ext t
      rw [Set.mem_neg]
      rfl
    rw [he]
    exact hc
  · ext τ
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨-t, rfl⟩
    · rintro ⟨t, rfl⟩
      refine ⟨-t, ?_⟩
      change ρ (-(-t)) = ρ t
      rw [neg_neg]

/-- Normalize an actual primitive periodic exterior. The lower parabolic side gives
the genuine elementary alternative; other outputs retain orientation and compact period residuals.
Equality of the signed cyclic subgroups records primitivity after normalization. -/
theorem ft1fas_end_normal_form (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (ρ : ℝ → UpperHalfPlane) (hρ : Topology.IsEmbedding ρ)
    (hproper : ∀ L : Set UpperHalfPlane, IsCompact L → IsCompact (ρ ⁻¹' L))
    (W : Set UpperHalfPlane) (hWo : IsOpen W) (hWc : IsConnected W)
    (hfront : frontier W = Set.range ρ)
    (h₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hh₀ : h₀ ∈ Γ)
    (h1 : h₀ ≠ 1) (hm1 : h₀ ≠ -1)
    (hperiod : ∀ t : ℝ, ρ (t + 1) = h₀ • ρ t)
    (hWinv : (fun τ : UpperHalfPlane => h₀ • τ) '' W = W)
    (hprec : ∀ γ ∈ Γ, ((fun τ : UpperHalfPlane => γ • τ) '' W ∩ W).Nonempty →
      ∃ k : ℤ, γ = h₀ ^ k ∨ γ = -h₀ ^ k) :
    (∃ A π₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ, π₀ ∈ Γ ∧
      (∀ τ : UpperHalfPlane, π₀ • (A • τ) = A • ((1 : ℝ) +ᵥ τ)) ∧
      ∀ γ ∈ Γ, ∃ k : ℤ, γ = π₀ ^ k ∨ γ = -π₀ ^ k) ∨
    (∃ (A π₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (δ Y : ℝ),
      π₀ ∈ Γ ∧ 0 < δ ∧ δ < Y ∧ 1 < Y ∧
      (∀ τ : UpperHalfPlane, π₀ • (A • τ) = A • ((1 : ℝ) +ᵥ τ)) ∧
      (∀ β : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        (∃ k : ℤ, β = h₀ ^ k ∨ β = -h₀ ^ k) ↔
        (∃ k : ℤ, β = π₀ ^ k ∨ β = -π₀ ^ k)) ∧
      (∀ β ∈ Γ, (A⁻¹ * β * A) 1 0 = 0 → ∃ k : ℤ, β = π₀ ^ k ∨ β = -π₀ ^ k) ∧
      {τ : UpperHalfPlane | Y < τ.im} ⊆ (fun τ => A • τ) ⁻¹' W ∧
      (fun τ : UpperHalfPlane => A • τ) ⁻¹' W ⊆ {τ | δ < τ.im} ∧
      IsCompact ((fun τ : UpperHalfPlane => A • τ) ⁻¹' closure W ∩
        {τ | 0 ≤ τ.re ∧ τ.re ≤ 1 ∧ τ.im ≤ Y})) ∨
    (∃ (B h : Matrix.SpecialLinearGroup (Fin 2) ℝ) (lam θ : ℝ),
      h ∈ Γ ∧ 1 < lam ∧ 0 < θ ∧ θ < Real.pi / 2 ∧
      (∀ τ : UpperHalfPlane, ((B⁻¹ • (h • (B • τ)) : UpperHalfPlane) : ℂ) =
        (lam : ℂ) * (τ : ℂ)) ∧
      (∀ β : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        (∃ k : ℤ, β = h₀ ^ k ∨ β = -h₀ ^ k) ↔
        (∃ k : ℤ, β = h ^ k ∨ β = -h ^ k)) ∧
      {τ : UpperHalfPlane | arg (τ : ℂ) < θ} ⊆ (fun τ => B • τ) ⁻¹' W ∧
      (fun τ : UpperHalfPlane => B • τ) ⁻¹' W ⊆ {τ | arg (τ : ℂ) < Real.pi - θ} ∧
      IsCompact ((fun τ : UpperHalfPlane => B • τ) ⁻¹' closure W ∩
        {τ | 1 ≤ ‖(τ : ℂ)‖ ∧ ‖(τ : ℂ)‖ ≤ lam ∧ θ ≤ arg (τ : ℂ)})) := by
  -- Discreteness and the setwise invariance of `W` are not needed separately: the
  -- periodic boundary and precise invariance carry all the information used. The
  -- statement remains true without these two hypotheses.
  have _hΓ := hΓ
  have _hWinv := hWinv
  rcases isParabolic_or_isHyperbolic_of_actsFreely hfree hh₀ h1 hm1 with hpar | hhyp
  · -- Parabolic period: normalize the actual element `h₀` (or its inverse) to `τ ↦ τ + 1`.
    obtain ⟨A, π₀, hπ₀h, htrans⟩ := ft1fn_parabolic_coordinate hpar
    have hπ₀Γ : π₀ ∈ Γ := by
      rcases hπ₀h with hπ | hπ
      · rw [hπ]
        exact hh₀
      · rw [hπ]
        exact Γ.inv_mem hh₀
    have hcyc : ∀ β : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        (∃ k : ℤ, β = h₀ ^ k ∨ β = -h₀ ^ k) ↔ (∃ k : ℤ, β = π₀ ^ k ∨ β = -π₀ ^ k) := by
      intro β
      rcases hπ₀h with hπ | hπ
      · rw [hπ]
      · rw [hπ]
        exact ft1fn_signed_cyclic_inv h₀ β
    -- A boundary parametrization with period `π₀`, reversing the parameter if `π₀ = h₀⁻¹`.
    obtain ⟨σ, hσ, hσp, hσr, hσper⟩ : ∃ σ : ℝ → UpperHalfPlane, Topology.IsEmbedding σ ∧
        (∀ L : Set UpperHalfPlane, IsCompact L → IsCompact (σ ⁻¹' L)) ∧
        Set.range σ = Set.range ρ ∧ ∀ t : ℝ, σ (t + 1) = π₀ • σ t := by
      rcases hπ₀h with hπ | hπ
      · rw [hπ]
        exact ⟨ρ, hρ, hproper, rfl, hperiod⟩
      · rw [hπ]
        obtain ⟨hr1, hr2, hr3⟩ := ft1fen_reverse ρ hρ hproper
        exact ⟨fun t => ρ (-t), hr1, hr2, hr3, fun t => ft1fn_reverse_period ρ h₀ hperiod t⟩
    obtain ⟨hρ', hpr', hWo', hWc', hfr'⟩ :=
      ft1fen_coord_transport A σ hσ hσp W hWo hWc (hfront.trans hσr.symm)
    have hper' : ∀ t : ℝ, (fun t : ℝ => A⁻¹ • σ t) (t + 1) =
        (1 : ℝ) +ᵥ (fun t : ℝ => A⁻¹ • σ t) t := by
      intro t
      change A⁻¹ • σ (t + 1) = (1 : ℝ) +ᵥ A⁻¹ • σ t
      have hA := htrans (A⁻¹ • σ t)
      rw [smul_inv_smul] at hA
      rw [hσper, hA, inv_smul_smul]
    have hcl : (fun τ : UpperHalfPlane => A • τ) ⁻¹' closure W =
        closure ((fun τ : UpperHalfPlane => A • τ) ⁻¹' W) :=
      (Homeomorph.smul A).preimage_closure W
    obtain ⟨δ, Y, hδ, hδY, hY, hside⟩ := ft1gc_parabolic_side_collar (fun t => A⁻¹ • σ t)
      hρ' hpr' hper' ((fun τ : UpperHalfPlane => A • τ) ⁻¹' W) hWo' hWc' hfr'
    rcases hside with ⟨hhigh, hlow, hcpt⟩ | ⟨hstrip, -⟩
    · -- Upper side: a genuine cusp end.
      right
      left
      refine ⟨A, π₀, δ, Y, hπ₀Γ, hδ, hδY, hY, htrans, hcyc, ?_, hhigh, hlow, ?_⟩
      · intro β hβ hc
        exact (hcyc β).1 (ft1fn_high_cusp_stabilizer W A h₀ Y hhigh hprec β hβ hc)
      · rw [hcl]
        exact hcpt
    · -- Lower side: the whole group is cyclic (elementary alternative).
      left
      have hall : ∀ γ ∈ Γ, ∃ k : ℤ, γ = h₀ ^ k ∨ γ = -h₀ ^ k := by
        have hconj := ft1gc_lower_strip_elementary (Γ := conjGroup Γ A⁻¹) (A⁻¹ * h₀ * A)
          ((fun τ : UpperHalfPlane => A • τ) ⁻¹' W) δ hδ hstrip (by
            intro β hβ τ hτ hβτ
            obtain ⟨γ, hγ, rfl⟩ := s30l_mem_conjGroup.1 hβ
            have he : A • ((A⁻¹ * γ * A⁻¹⁻¹) • τ) = γ • (A • τ) := by
              rw [inv_inv]
              simp only [mul_smul, smul_inv_smul]
            have hγτ : γ • (A • τ) ∈ W := by
              have h2 : A • ((A⁻¹ * γ * A⁻¹⁻¹) • τ) ∈ W := hβτ
              rwa [he] at h2
            have hτW : A • τ ∈ W := hτ
            obtain ⟨k, hk⟩ := hprec γ hγ ⟨γ • (A • τ), ⟨A • τ, hτW, rfl⟩, hγτ⟩
            refine ⟨k, ?_⟩
            rw [inv_inv, ft1fen_conj_zpow]
            rcases hk with hk | hk
            · left
              rw [hk]
            · right
              rw [hk, mul_neg, neg_mul])
        intro γ hγ
        obtain ⟨k, hk⟩ := hconj (A⁻¹ * γ * A) (s30l_mem_conjGroup.2 ⟨γ, hγ, by rw [inv_inv]⟩)
        refine ⟨k, ?_⟩
        rw [ft1fen_conj_zpow] at hk
        rcases hk with hk | hk
        · left
          calc γ = A * (A⁻¹ * γ * A) * A⁻¹ := by group
            _ = A * (A⁻¹ * h₀ ^ k * A) * A⁻¹ := by rw [hk]
            _ = h₀ ^ k := by group
        · right
          calc γ = A * (A⁻¹ * γ * A) * A⁻¹ := by group
            _ = A * (-(A⁻¹ * h₀ ^ k * A)) * A⁻¹ := by rw [hk]
            _ = -(A * (A⁻¹ * h₀ ^ k * A) * A⁻¹) := by rw [mul_neg, neg_mul]
            _ = -h₀ ^ k := by group
      exact ⟨A, π₀, hπ₀Γ, htrans, fun γ hγ => (hcyc γ).1 (hall γ hγ)⟩
  · -- Hyperbolic period: normalize `h₀` itself to a dilation by `lam > 1`.
    obtain ⟨B, lam, hlam, hscale⟩ := ft1fn_hyperbolic_coordinate hhyp
    obtain ⟨hρ', hpr', hWo', hWc', hfr'⟩ :=
      ft1fen_coord_transport B ρ hρ hproper W hWo hWc hfront
    have hper' : ∀ t : ℝ, (((fun t : ℝ => B⁻¹ • ρ t) (t + 1) : UpperHalfPlane) : ℂ) =
        (lam : ℂ) * (((fun t : ℝ => B⁻¹ • ρ t) t : UpperHalfPlane) : ℂ) := by
      intro t
      change ((B⁻¹ • ρ (t + 1) : UpperHalfPlane) : ℂ) =
        (lam : ℂ) * ((B⁻¹ • ρ t : UpperHalfPlane) : ℂ)
      have hB := hscale (B⁻¹ • ρ t)
      rw [smul_inv_smul] at hB
      rw [hperiod, hB]
    have hcl : (fun τ : UpperHalfPlane => B • τ) ⁻¹' closure W =
        closure ((fun τ : UpperHalfPlane => B • τ) ⁻¹' W) :=
      (Homeomorph.smul B).preimage_closure W
    obtain ⟨θ, hθ, hθπ, hside⟩ := ft1gc_hyperbolic_side_collar (fun t => B⁻¹ • ρ t)
      hρ' hpr' lam hlam hper' ((fun τ : UpperHalfPlane => B • τ) ⁻¹' W) hWo' hWc' hfr'
    right
    right
    rcases hside with ⟨hin, hout, hcpt⟩ | ⟨hin, hout, hcpt⟩
    · -- Positive side: the collar output directly.
      refine ⟨B, h₀, lam, θ, hh₀, hlam, hθ, hθπ, hscale, fun β => Iff.rfl, hin, hout, ?_⟩
      rw [hcl]
      exact hcpt
    · -- Negative side: flip by the half-turn `z ↦ -lam/z` and reverse the generator.
      obtain ⟨J, hJf, hJJ, hJn, hJa⟩ := ft1fn_halfturn_exists lam (by linarith)
      obtain ⟨hin2, hout2, hcpt2⟩ := ft1fn_halfturn_collar lam θ hlam J hJJ hJn hJa
        ((fun τ : UpperHalfPlane => B • τ) ⁻¹' W) hin hout hcpt
      have hpre : (fun τ : UpperHalfPlane => J • τ) ⁻¹'
          ((fun τ : UpperHalfPlane => B • τ) ⁻¹' W) =
          (fun τ : UpperHalfPlane => (B * J) • τ) ⁻¹' W := by
        ext τ
        simp only [Set.mem_preimage, mul_smul]
      have hcl2 : (fun τ : UpperHalfPlane => (B * J) • τ) ⁻¹' closure W =
          closure ((fun τ : UpperHalfPlane => (B * J) • τ) ⁻¹' W) :=
        (Homeomorph.smul (B * J)).preimage_closure W
      refine ⟨B * J, h₀⁻¹, lam, θ, Γ.inv_mem hh₀, hlam, hθ, hθπ,
        ft1fn_halfturn_coordinate B h₀ J lam (by linarith) hscale hJf hJJ,
        ft1fn_signed_cyclic_inv h₀, ?_, ?_, ?_⟩
      · rw [← hpre]
        exact hin2
      · rw [← hpre]
        exact hout2
      · rw [hcl2, ← hpre]
        exact hcpt2

end LiZhongQC
end -- source noncomputable section
