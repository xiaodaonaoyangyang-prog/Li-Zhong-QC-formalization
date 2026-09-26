import Mathlib

open MeasureTheory ENNReal Complex Filter
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Bridge: for `1 < p`, `(eLpNorm ω (ENNReal.ofReal p) μ) ^ p = ∫⁻ x, ‖ω x‖ₑ ^ p ∂μ`. -/
theorem enn_pow_eLpNorm_eq_lintegral {p : ℝ} (hp : 1 < p) (f : α → ℂ)
    (hf : AEStronglyMeasurable f μ) :
    (eLpNorm f (ENNReal.ofReal p) μ) ^ p = ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  have hp0 : (0:ℝ) ≤ p := hp.le.trans' (by norm_num)
  have hpne0 : ENNReal.ofReal p ≠ 0 := by
    simp only [Ne, ENNReal.ofReal_eq_zero, not_le]
    linarith
  have hpnetop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne0 hpnetop hf, ENNReal.toReal_ofReal hp0,
    ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (by linarith : p ≠ 0), ENNReal.rpow_one]

/-- Bridge to the real Bochner integral: `∫ ‖f x‖ ^ p ∂μ = ((eLpNorm f p μ) ^ p).toReal`. -/
theorem integral_norm_rpow_eq_toReal_pow {p : ℝ} (hp : 1 < p) {f : α → ℂ}
    (hf : AEStronglyMeasurable f μ) :
    ∫ x, (‖f x‖ : ℝ) ^ p ∂μ = ((eLpNorm f (ENNReal.ofReal p) μ) ^ p).toReal := by
  have hp0 : (0:ℝ) ≤ p := by linarith
  rw [enn_pow_eLpNorm_eq_lintegral hp f hf]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)
    (by fun_prop)]
  congr 1
  refine lintegral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f x)) hp0]

/-- Pointwise algebra for the closed-form dual witness: with `c := ‖z‖ ^ (p-2) / N ^ (p-1)` and
`g := conj z * c`, we have `z * g = ‖z‖^p / N^(p-1)` (as a nonneg real cast to `ℂ`) and
`‖g‖ = ‖z‖^(p-1) / N^(p-1)`. -/
theorem witness_pointwise {p N : ℝ} (hp1 : 1 < p) (hN : 0 < N) (z : ℂ) :
    z * ((starRingEnd ℂ) z * ((‖z‖ ^ (p - 2) / N ^ (p - 1) : ℝ) : ℂ)) =
      ((‖z‖ ^ p / N ^ (p - 1) : ℝ) : ℂ) ∧
    ‖(starRingEnd ℂ) z * ((‖z‖ ^ (p - 2) / N ^ (p - 1) : ℝ) : ℂ)‖ =
      ‖z‖ ^ (p - 1) / N ^ (p - 1) := by
  have hNp1 : (0:ℝ) < N ^ (p - 1) := Real.rpow_pos_of_pos hN _
  rcases eq_or_lt_of_le (norm_nonneg z) with hz0 | hz0
  · -- z = 0
    have hz : z = 0 := norm_eq_zero.mp hz0.symm
    subst hz
    have h1 : (0:ℝ) ^ p = 0 := Real.zero_rpow (by linarith)
    have h2 : (0:ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
    simp [h1, h2]
  · -- z ≠ 0
    have step : ∀ a : ℝ, ‖z‖ * ‖z‖ ^ a = ‖z‖ ^ (a + 1) := by
      intro a
      rw [show (a + 1) = 1 + a from by ring, Real.rpow_add hz0, Real.rpow_one]
    have e1 : ‖z‖ * ‖z‖ ^ (p - 2) = ‖z‖ ^ (p - 1) := by
      rw [step (p - 2), show (p - 2) + 1 = p - 1 from by ring]
    have e2 : ‖z‖ ^ 2 * ‖z‖ ^ (p - 2) = ‖z‖ ^ p := by
      rw [pow_two, mul_assoc, e1, step (p - 1), show (p - 1) + 1 = p from by ring]
    have hconj : z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hcnn : (0:ℝ) ≤ ‖z‖ ^ (p - 2) / N ^ (p - 1) :=
      div_nonneg (Real.rpow_nonneg (norm_nonneg z) _) hNp1.le
    constructor
    · calc z * ((starRingEnd ℂ) z * ((‖z‖ ^ (p - 2) / N ^ (p - 1) : ℝ) : ℂ))
          = (z * (starRingEnd ℂ) z) * ((‖z‖ ^ (p - 2) / N ^ (p - 1) : ℝ) : ℂ) := by ring
        _ = ((‖z‖ ^ 2 : ℝ) : ℂ) * ((‖z‖ ^ (p - 2) / N ^ (p - 1) : ℝ) : ℂ) := by rw [hconj]
        _ = ((‖z‖ ^ 2 * (‖z‖ ^ (p - 2) / N ^ (p - 1)) : ℝ) : ℂ) := by push_cast; ring
        _ = ((‖z‖ ^ p / N ^ (p - 1) : ℝ) : ℂ) := by
              congr 1
              field_simp
              linarith [e2]
    · rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hcnn]
      field_simp
      linarith [e1]

/-- **Draft 1, proved.** The explicit converse-Hölder witness on a simple function. -/
theorem exists_dualWitness_simpleFunc {p q : ℝ} (hpq : p.HolderConjugate q)
    {ω : MeasureTheory.SimpleFunc α ℂ}
    (hω0 : eLpNorm ω (ENNReal.ofReal p) μ ≠ 0) (hωtop : eLpNorm ω (ENNReal.ofReal p) μ ≠ ⊤) :
    ∃ g : α → ℂ, eLpNorm g (ENNReal.ofReal q) μ = 1 ∧
      ∫ x, ω x * g x ∂μ = (eLpNorm ω (ENNReal.ofReal p) μ).toReal := by
  have hp1 : (1:ℝ) < p := hpq.lt
  have hq1 : (1:ℝ) < q := hpq.symm.lt
  have hq0 : q ≠ 0 := by linarith
  set N : ℝ := (eLpNorm ω (ENNReal.ofReal p) μ).toReal with hN_def
  have hNpos : 0 < N := ENNReal.toReal_pos hω0 hωtop
  have hNeq : ENNReal.ofReal N = eLpNorm ω (ENNReal.ofReal p) μ := ENNReal.ofReal_toReal hωtop
  set g : α → ℂ := fun x => (starRingEnd ℂ) (ω x) * ((‖ω x‖ ^ (p - 2) / N ^ (p - 1) : ℝ) : ℂ)
    with hg_def
  have hpw := fun x => witness_pointwise (z := ω x) hp1 hNpos
  refine ⟨g, ?_, ?_⟩
  · -- eLpNorm g q μ = 1
    have hgnorm : ∀ x, ‖g x‖ₑ = ‖ω x‖ₑ ^ (p - 1) / (ENNReal.ofReal N) ^ (p - 1) := by
      intro x
      rw [← ofReal_norm, (hpw x).2, ← ofReal_norm,
        ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hNpos _),
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith),
        ENNReal.ofReal_rpow_of_nonneg hNpos.le (by linarith)]
    have hstep : (eLpNorm g (ENNReal.ofReal q) μ) ^ q = ∫⁻ x, ‖g x‖ₑ ^ q ∂μ :=
      enn_pow_eLpNorm_eq_lintegral hq1 g
        (ω.map (fun z => (starRingEnd ℂ) z * ((‖z‖ ^ (p - 2) / N ^ (p - 1) : ℝ) : ℂ))).aestronglyMeasurable
    have hq0' : (0:ℝ) ≤ q := by linarith
    have hNofReal_ne0 : ENNReal.ofReal N ≠ 0 := by
      simp only [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hNpos
    have hNp_ne_top : ENNReal.ofReal N ^ p ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_ne_zero hNofReal_ne0 ENNReal.ofReal_ne_top
    have hNp_ne0 : ENNReal.ofReal N ^ p ≠ 0 :=
      (ENNReal.rpow_pos (by positivity) ENNReal.ofReal_ne_top).ne'
    have hint : ∫⁻ x, ‖g x‖ₑ ^ q ∂μ = 1 := by
      have hrw : ∀ x, ‖g x‖ₑ ^ q = ‖ω x‖ₑ ^ p / (ENNReal.ofReal N) ^ p := by
        intro x
        rw [hgnorm, ENNReal.div_rpow_of_nonneg _ _ hq0', ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          hpq.sub_one_mul_conj]
      simp_rw [hrw, ENNReal.div_eq_inv_mul]
      rw [MeasureTheory.lintegral_const_mul _ (by fun_prop),
        ← enn_pow_eLpNorm_eq_lintegral hp1 ω (SimpleFunc.aestronglyMeasurable ω), ← hNeq]
      exact ENNReal.inv_mul_cancel hNp_ne0 hNp_ne_top
    rw [hint] at hstep
    have h1 : (1 : ℝ≥0∞) = (1 : ℝ≥0∞) ^ q := by rw [ENNReal.one_rpow]
    rw [h1] at hstep
    exact ENNReal.rpow_left_injective hq0 hstep
  · -- ∫ ω * g = N
    have hprod : ∀ x, ω x * g x = ((‖ω x‖ ^ p / N ^ (p - 1) : ℝ) : ℂ) := fun x => (hpw x).1
    simp_rw [hprod]
    rw [integral_complex_ofReal]
    norm_cast
    have hint2 : ∫ x, ‖ω x‖ ^ p / N ^ (p - 1) ∂μ = N ^ p / N ^ (p - 1) := by
      simp_rw [div_eq_mul_inv]
      rw [MeasureTheory.integral_mul_const,
        integral_norm_rpow_eq_toReal_pow hp1 (SimpleFunc.aestronglyMeasurable ω)]
      congr 1
      rw [hN_def, ENNReal.toReal_rpow]
    rw [hint2, ← Real.rpow_sub hNpos, show p - (p - 1) = 1 from by ring, Real.rpow_one]

/-- Bundled version of `exists_dualWitness_simpleFunc`: the witness is itself a genuine
`SimpleFunc` (needed to plug into `eLpNorm_le_of_forall_dual_simpleFunc_le`'s `hbound`, which
quantifies over bundled simple functions). Internal helper, not part of the frozen interface. -/
theorem exists_dualWitness_simpleFunc_bundled {p q : ℝ} (hpq : p.HolderConjugate q)
    {ω : MeasureTheory.SimpleFunc α ℂ}
    (hω0 : eLpNorm ω (ENNReal.ofReal p) μ ≠ 0) (hωtop : eLpNorm ω (ENNReal.ofReal p) μ ≠ ⊤) :
    ∃ g : MeasureTheory.SimpleFunc α ℂ, eLpNorm (g : α → ℂ) (ENNReal.ofReal q) μ = 1 ∧
      ∫ x, ω x * g x ∂μ = (eLpNorm ω (ENNReal.ofReal p) μ).toReal := by
  have hp1 : (1:ℝ) < p := hpq.lt
  have hq1 : (1:ℝ) < q := hpq.symm.lt
  have hq0 : q ≠ 0 := by linarith
  set N : ℝ := (eLpNorm ω (ENNReal.ofReal p) μ).toReal with hN_def
  have hNpos : 0 < N := ENNReal.toReal_pos hω0 hωtop
  have hNeq : ENNReal.ofReal N = eLpNorm ω (ENNReal.ofReal p) μ := ENNReal.ofReal_toReal hωtop
  set g : MeasureTheory.SimpleFunc α ℂ :=
    ω.map (fun z => (starRingEnd ℂ) z * ((‖z‖ ^ (p - 2) / N ^ (p - 1) : ℝ) : ℂ)) with hg_def
  have hgcoe : (g : α → ℂ) =
      fun x => (starRingEnd ℂ) (ω x) * ((‖ω x‖ ^ (p - 2) / N ^ (p - 1) : ℝ) : ℂ) :=
    MeasureTheory.SimpleFunc.coe_map _ ω
  have hpw := fun x => witness_pointwise (z := ω x) hp1 hNpos
  refine ⟨g, ?_, ?_⟩
  · -- eLpNorm g q μ = 1
    have hgnorm : ∀ x, ‖(g : α → ℂ) x‖ₑ = ‖ω x‖ₑ ^ (p - 1) / (ENNReal.ofReal N) ^ (p - 1) := by
      intro x
      rw [hgcoe, ← ofReal_norm, (hpw x).2, ← ofReal_norm,
        ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hNpos _),
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith),
        ENNReal.ofReal_rpow_of_nonneg hNpos.le (by linarith)]
    have hstep : (eLpNorm (g : α → ℂ) (ENNReal.ofReal q) μ) ^ q =
        ∫⁻ x, ‖(g : α → ℂ) x‖ₑ ^ q ∂μ :=
      enn_pow_eLpNorm_eq_lintegral hq1 g g.aestronglyMeasurable
    have hq0' : (0:ℝ) ≤ q := by linarith
    have hNofReal_ne0 : ENNReal.ofReal N ≠ 0 := by
      simp only [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hNpos
    have hNp_ne_top : ENNReal.ofReal N ^ p ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_ne_zero hNofReal_ne0 ENNReal.ofReal_ne_top
    have hNp_ne0 : ENNReal.ofReal N ^ p ≠ 0 :=
      (ENNReal.rpow_pos (by positivity) ENNReal.ofReal_ne_top).ne'
    have hint : ∫⁻ x, ‖(g : α → ℂ) x‖ₑ ^ q ∂μ = 1 := by
      have hrw : ∀ x, ‖(g : α → ℂ) x‖ₑ ^ q = ‖ω x‖ₑ ^ p / (ENNReal.ofReal N) ^ p := by
        intro x
        rw [hgnorm, ENNReal.div_rpow_of_nonneg _ _ hq0', ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          hpq.sub_one_mul_conj]
      simp_rw [hrw, ENNReal.div_eq_inv_mul]
      rw [MeasureTheory.lintegral_const_mul _ (by fun_prop),
        ← enn_pow_eLpNorm_eq_lintegral hp1 ω (SimpleFunc.aestronglyMeasurable ω), ← hNeq]
      exact ENNReal.inv_mul_cancel hNp_ne0 hNp_ne_top
    rw [hint] at hstep
    have h1 : (1 : ℝ≥0∞) = (1 : ℝ≥0∞) ^ q := by rw [ENNReal.one_rpow]
    rw [h1] at hstep
    exact ENNReal.rpow_left_injective hq0 hstep
  · -- ∫ ω * g = N
    have hprod : ∀ x, ω x * (g : α → ℂ) x = ((‖ω x‖ ^ p / N ^ (p - 1) : ℝ) : ℂ) := by
      intro x; rw [hgcoe]; exact (hpw x).1
    simp_rw [hprod]
    rw [integral_complex_ofReal]
    norm_cast
    have hint2 : ∫ x, ‖ω x‖ ^ p / N ^ (p - 1) ∂μ = N ^ p / N ^ (p - 1) := by
      simp_rw [div_eq_mul_inv]
      rw [MeasureTheory.integral_mul_const,
        integral_norm_rpow_eq_toReal_pow hp1 (SimpleFunc.aestronglyMeasurable ω)]
      congr 1
      rw [hN_def, ENNReal.toReal_rpow]
    rw [hint2, ← Real.rpow_sub hNpos, show p - (p - 1) = 1 from by ring, Real.rpow_one]

/-- **Draft 2.** The converse-Hölder / duality bound consumed downstream. -/
theorem eLpNorm_le_of_forall_dual_simpleFunc_le {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : α → ℂ} (hf : MemLp f (ENNReal.ofReal p) μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ g : MeasureTheory.SimpleFunc α ℂ, eLpNorm g (ENNReal.ofReal q) μ ≤ 1 →
      ‖∫ x, f x * g x ∂μ‖ ≤ C) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C := by
  have hp1 : (1:ℝ) < p := hpq.lt
  have hq1 : (1:ℝ) < q := hpq.symm.lt
  rw [← ENNReal.toReal_le_toReal hf.eLpNorm_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hC]
  by_contra hlt
  push Not at hlt
  set δ : ℝ := ((eLpNorm f (ENNReal.ofReal p) μ).toReal - C) / 2 with hδ_def
  have hδpos : 0 < δ := by rw [hδ_def]; linarith
  have hδne0 : ENNReal.ofReal δ ≠ 0 := by
    simp only [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hδpos
  obtain ⟨s, hs_lt, hs_mem⟩ := hf.exists_simpleFunc_eLpNorm_sub_lt ENNReal.ofReal_ne_top hδne0
  have hfsne_top : eLpNorm (f - (s : α → ℂ)) (ENNReal.ofReal p) μ ≠ ⊤ := hs_lt.ne_top
  have hfs_toreal_lt : (eLpNorm (f - (s : α → ℂ)) (ENNReal.ofReal p) μ).toReal < δ := by
    have := (ENNReal.toReal_lt_toReal hfsne_top ENNReal.ofReal_ne_top).mpr hs_lt
    rwa [ENNReal.toReal_ofReal hδpos.le] at this
  have hp1e : (1:ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1.le
  by_cases hs0 : eLpNorm (s : α → ℂ) (ENNReal.ofReal p) μ = 0
  · -- degenerate: s ≈ 0
    have heq : f = (f - (s:α→ℂ)) + (s:α→ℂ) := by funext x; simp
    have htri : eLpNorm f (ENNReal.ofReal p) μ ≤
        eLpNorm (f - (s:α→ℂ)) (ENNReal.ofReal p) μ + eLpNorm (s:α→ℂ) (ENNReal.ofReal p) μ := by
      conv_lhs => rw [heq]
      exact eLpNorm_add_le hp1e
    rw [hs0, add_zero] at htri
    have hcontra : (eLpNorm f (ENNReal.ofReal p) μ).toReal < δ :=
      lt_of_le_of_lt (ENNReal.toReal_mono hfsne_top htri) hfs_toreal_lt
    have hXnn : (0:ℝ) ≤ (eLpNorm f (ENNReal.ofReal p) μ).toReal := ENNReal.toReal_nonneg
    linarith
  · -- generic: use the bundled witness for s
    obtain ⟨g, hgq, hgint⟩ := exists_dualWitness_simpleFunc_bundled hpq hs0 hs_mem.eLpNorm_ne_top
    have hgle1 : eLpNorm (g : α → ℂ) (ENNReal.ofReal q) μ ≤ 1 := le_of_eq hgq
    have hb := hbound g hgle1
    have hgmem : MemLp (g : α → ℂ) (ENNReal.ofReal q) μ :=
      memLp_iff.mpr (by rw [hgq]; exact one_lt_top)
    have hHT : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) 1 :=
      ⟨by rw [inv_one]; exact hpq.inv_add_inv_ennreal⟩
    have hfs_mem : MemLp (f - (s:α→ℂ)) (ENNReal.ofReal p) μ := hf.sub hs_mem
    have hintsub : ∫ x, f x * g x ∂μ - ∫ x, (s x : ℂ) * g x ∂μ = ∫ x, (f x - s x) * g x ∂μ := by
      have h := MeasureTheory.integral_sub (hf.integrable_mul hgmem) (hs_mem.integrable_mul hgmem)
      simpa [Pi.mul_apply, sub_mul] using h.symm
    have hdiffbound : ‖∫ x, f x * g x ∂μ - ∫ x, (s x : ℂ) * g x ∂μ‖ ≤
        (eLpNorm (f - (s:α→ℂ)) (ENNReal.ofReal p) μ).toReal := by
      rw [hintsub]
      calc ‖∫ x, (f x - s x) * g x ∂μ‖
          ≤ ∫ x, ‖(f x - s x) * g x‖ ∂μ := norm_integral_le_integral_norm _
        _ = ∫ x, ‖(f - (s:α→ℂ)) x‖ * ‖g x‖ ∂μ := by
              congr 1; funext x; rw [norm_mul]; congr 1
        _ ≤ (∫ x, ‖(f - (s:α→ℂ)) x‖ ^ p ∂μ) ^ (1/p) * (∫ x, ‖g x‖ ^ q ∂μ) ^ (1/q) :=
              integral_mul_norm_le_Lp_mul_Lq hpq hfs_mem hgmem
        _ = (eLpNorm (f - (s:α→ℂ)) (ENNReal.ofReal p) μ).toReal *
              (eLpNorm (g:α→ℂ) (ENNReal.ofReal q) μ).toReal := by
              have hpow_toreal : ∀ (X : ℝ≥0∞) (y : ℝ), 0 < y → ((X ^ y).toReal) ^ (1/y) = X.toReal :=
                fun X y hy => by
                  rw [← ENNReal.toReal_rpow, ← Real.rpow_mul ENNReal.toReal_nonneg, mul_one_div,
                    div_self hy.ne', Real.rpow_one]
              rw [integral_norm_rpow_eq_toReal_pow hp1 hfs_mem.aestronglyMeasurable,
                integral_norm_rpow_eq_toReal_pow hq1 hgmem.aestronglyMeasurable,
                hpow_toreal _ p (by linarith), hpow_toreal _ q (by linarith)]
        _ = (eLpNorm (f - (s:α→ℂ)) (ENNReal.ofReal p) μ).toReal := by rw [hgq]; simp
    have hkey : (eLpNorm (s:α→ℂ) (ENNReal.ofReal p) μ).toReal ≤ C + δ := by
      have hnorm_eq : ‖∫ x, (s x:ℂ) * g x ∂μ‖ = (eLpNorm (s:α→ℂ) (ENNReal.ofReal p) μ).toReal := by
        rw [hgint, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
      have htri2 : ‖∫ x, (s x:ℂ) * g x ∂μ‖ ≤
          ‖∫ x, f x * g x ∂μ‖ + ‖(∫ x, f x * g x ∂μ) - ∫ x, (s x:ℂ) * g x ∂μ‖ := by
        calc ‖∫ x, (s x:ℂ) * g x ∂μ‖
            = ‖(∫ x, f x * g x ∂μ) - ((∫ x, f x * g x ∂μ) - ∫ x, (s x:ℂ) * g x ∂μ)‖ := by
              congr 1; ring
          _ ≤ _ := norm_sub_le _ _
      linarith [hnorm_eq, htri2, hb, hdiffbound, hfs_toreal_lt]
    have hftri : (eLpNorm f (ENNReal.ofReal p) μ).toReal ≤
        (eLpNorm (s:α→ℂ) (ENNReal.ofReal p) μ).toReal +
          (eLpNorm (f - (s:α→ℂ)) (ENNReal.ofReal p) μ).toReal := by
      have heq : f = (s:α→ℂ) + (f - (s:α→ℂ)) := by funext x; simp
      have hadd : eLpNorm ((s:α→ℂ) + (f - (s:α→ℂ))) (ENNReal.ofReal p) μ ≤
          eLpNorm (s:α→ℂ) (ENNReal.ofReal p) μ + eLpNorm (f - (s:α→ℂ)) (ENNReal.ofReal p) μ :=
        eLpNorm_add_le hp1e
      rw [← heq] at hadd
      calc (eLpNorm f (ENNReal.ofReal p) μ).toReal
          ≤ (eLpNorm (s:α→ℂ) (ENNReal.ofReal p) μ +
              eLpNorm (f-(s:α→ℂ)) (ENNReal.ofReal p) μ).toReal :=
            ENNReal.toReal_mono (by finiteness) hadd
        _ = _ := ENNReal.toReal_add hs_mem.eLpNorm_ne_top hfsne_top
    linarith [hkey, hftri, hfs_toreal_lt]

end LiZhongQC

