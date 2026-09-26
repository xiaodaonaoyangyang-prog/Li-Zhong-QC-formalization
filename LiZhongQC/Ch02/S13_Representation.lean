import LiZhongQC.Ch02.S12_Existence
import LiZhongQC.Ch01.S05_ExtremalProblems
import LiZhongQC.Ch03.S14_PoincareMetric

/-!
# §13 表示定理与相似原理 — The representation theorem and the similarity principle

* Theorem 13.1 (series representation (13.2) of the global homeomorphic solution)
                                                          — `thm13_1_representation`
* Lemma 13.1 (chain rule for generalized derivatives)     — `lemma13_1_chain_rule`
* (13.5)–(13.7) (derivatives and complex characteristic of the inverse)
* Theorem 13.2 (similarity principle)                     — `thm13_2_similarity`
* consequences: maximum principle, isolated zeros, open mapping for generalized solutions
* Theorem 13.3 (boundary correspondence), Theorems 13.4, 13.5 (uniqueness)
* §13.4 Hölder continuity of quasiconformal maps          — `qc_holder`
* §13.5 quasiconformal extension across an arc, reflection
* Theorem 13.6 (measurable Riemann mapping theorem)       — `thm13_6_riemann_mapping`
* Theorem 13.7 (existence and uniqueness of normalized solutions in the plane)
* Theorem 13.8 (Ahlfors–Bers: dependence on parameters)

## What is proved here

Everything: this file is `sorry`-free (2026-09-24).  At the end of the file also live, moved here because their
proofs use §11–§13: Theorems 10.1 and 10.2 (⇐) of §10, the remark after Theorem 12.2 (`thm12_2_unique`), and
Theorem 13.8 (both halves).  Two §13.5 statements were CORRECTED (user-approved, 2026-09-24; see their docstrings):
`qc_reflection_extension` assumes `f z → ∞`, and `qc_extension_across_arc` takes `γ` an open line segment (the
book's arbitrary Jordan arc makes it false) with the book's homeomorphic-extension hypotheses made explicit.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC


/-! ## §13.1 The representation theorem -/

/-- The terms `μ, μH(μ), μH(μH(μ)), …` of the series (13.1). -/
def beltramiIter (μ : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => μ
  | n + 1 => fun z => μ z * hilbertH (beltramiIter μ n) z

/-- Unfolding equation for `beltramiIter` at a successor, isolated as its own top-level `rfl`
lemma: using `show`/defeq directly against this pattern-match inline (inside a larger proof
context) hit the project's recurring pathological `whnf` slowdown; a standalone lemma referenced
via `rw` is fast and avoids it. -/
theorem rep_beltramiIter_succ (μ : ℂ → ℂ) (n : ℕ) :
    beltramiIter μ (n + 1) = fun z => μ z * hilbertH (beltramiIter μ n) z := rfl

theorem rep_beltramiCoeff_meas {μ : ℂ → ℂ} {k : ℝ} (hμ : IsCompactBeltramiCoeff μ k) :
    AEStronglyMeasurable μ volume := by
  have := hμ.1.1
  rwa [Measure.restrict_univ] at this

theorem rep_beltramiCoeff_bound {μ : ℂ → ℂ} {k : ℝ} (hμ : IsCompactBeltramiCoeff μ k) :
    ∀ᵐ z, ‖μ z‖ ≤ k := by
  have := hμ.1.2
  rwa [Measure.restrict_univ] at this

theorem rep_beltramiCoeff_hasCompactSupport {μ : ℂ → ℂ} {k : ℝ} (hμ : IsCompactBeltramiCoeff μ k) :
    HasCompactSupport μ := by
  obtain ⟨R, hR⟩ := hμ.2
  have hbdd : Bornology.IsBounded (Function.support μ) := by
    apply Bornology.IsBounded.subset (isBounded_closedBall (x := (0:ℂ)) (r := R))
    intro z hz
    by_contra hzn
    exact hz (hR z (by simpa [mem_closedBall_zero_iff, not_le] using hzn))
  exact hbdd.isCompact_closure

theorem rep_memLp_beltramiCoeff {μ : ℂ → ℂ} {k : ℝ} (hμ : IsCompactBeltramiCoeff μ k) {p : ℝ}
    (hp : 2 < p) : MemLp μ (ENNReal.ofReal p) := by
  exact (rep_beltramiCoeff_hasCompactSupport hμ).memLp_of_bound (rep_beltramiCoeff_meas hμ) k
    (rep_beltramiCoeff_bound hμ)

theorem rep_support_subset {μ : ℂ → ℂ} (n : ℕ) :
    Function.support (beltramiIter μ n) ⊆ tsupport μ := by
  cases n with
  | zero => exact subset_tsupport μ
  | succ n =>
    intro z hz
    rw [Function.mem_support] at hz
    apply subset_tsupport μ
    rw [Function.mem_support]
    intro hμz
    apply hz
    rw [rep_beltramiIter_succ]
    show μ z * hilbertH (beltramiIter μ n) z = 0
    rw [hμz, zero_mul]

theorem rep_memLp_iter {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hμ : IsCompactBeltramiCoeff μ k)
    {p : ℝ} (hp : 2 < p) (n : ℕ) : MemLp (beltramiIter μ n) (ENNReal.ofReal p) := by
  induction n with
  | zero => exact rep_memLp_beltramiCoeff hμ hp
  | succ n ih =>
    have hp1 : 1 < p := by linarith
    have hH : MemLp (hilbertH (beltramiIter μ n)) (ENNReal.ofReal p) :=
      hilbertH_memLp hp1 ih
    rw [rep_beltramiIter_succ]
    have hmeas : AEStronglyMeasurable (fun z => μ z * hilbertH (beltramiIter μ n) z) volume :=
      (rep_beltramiCoeff_meas hμ).mul hH.aestronglyMeasurable
    apply MemLp.of_le_mul hH hmeas
    filter_upwards [rep_beltramiCoeff_bound hμ] with z hz
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)

/-- Extracted inductive step of `rep_eLpNorm_iter_le` (as a standalone top-level lemma: a small
`calc` chain nested inside an `induction ... with` combinator hit a pathological `isDefEq`/`whnf`
slowdown when written inline, a recurring pattern in this project; extraction fixes it). -/
theorem rep_eLpNorm_iter_step {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hμ : IsCompactBeltramiCoeff μ k)
    {p : ℝ} (hp : 2 < p) {n : ℕ} {B : ℝ≥0∞}
    (ih : eLpNorm (beltramiIter μ n) (ENNReal.ofReal p) ≤ (ENNReal.ofReal (k * hilbertNorm p)) ^ n * B) :
    eLpNorm (beltramiIter μ (n + 1)) (ENNReal.ofReal p) ≤
      (ENNReal.ofReal (k * hilbertNorm p)) ^ (n + 1) * B := by
  rw [rep_beltramiIter_succ]
  have hp1 : 1 < p := by linarith
  have hstep1 : eLpNorm (fun z => μ z * hilbertH (beltramiIter μ n) z) (ENNReal.ofReal p) ≤
      ENNReal.ofReal k * eLpNorm (hilbertH (beltramiIter μ n)) (ENNReal.ofReal p) := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ ?_ _
    · exact (rep_beltramiCoeff_meas hμ).mul
        (hilbertH_memLp hp1 (rep_memLp_iter hk₀ hμ hp n)).aestronglyMeasurable
    filter_upwards [rep_beltramiCoeff_bound hμ] with z hz
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
  have hstep2 : eLpNorm (hilbertH (beltramiIter μ n)) (ENNReal.ofReal p) ≤
      ENNReal.ofReal (hilbertNorm p) * eLpNorm (beltramiIter μ n) (ENNReal.ofReal p) :=
    eq11_16_eLpNorm hp1 (rep_memLp_iter hk₀ hμ hp n)
  have hcomb : eLpNorm (fun z => μ z * hilbertH (beltramiIter μ n) z) (ENNReal.ofReal p) ≤
      ENNReal.ofReal k * (ENNReal.ofReal (hilbertNorm p) *
        eLpNorm (beltramiIter μ n) (ENNReal.ofReal p)) :=
    hstep1.trans (mul_le_mul_right hstep2 _)
  have heq : ENNReal.ofReal k * (ENNReal.ofReal (hilbertNorm p) *
      eLpNorm (beltramiIter μ n) (ENNReal.ofReal p)) =
      ENNReal.ofReal (k * hilbertNorm p) * eLpNorm (beltramiIter μ n) (ENNReal.ofReal p) := by
    rw [← mul_assoc, ENNReal.ofReal_mul hk₀]
  rw [heq] at hcomb
  have h1 := hcomb.trans (mul_le_mul_right ih (ENNReal.ofReal (k * hilbertNorm p)))
  have h2 : ENNReal.ofReal (k * hilbertNorm p) *
      ((ENNReal.ofReal (k * hilbertNorm p)) ^ n * B) =
      (ENNReal.ofReal (k * hilbertNorm p)) ^ (n + 1) * B := by
    rw [pow_succ]; ring
  rwa [h2] at h1

theorem rep_eLpNorm_iter_le {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hμ : IsCompactBeltramiCoeff μ k)
    {p : ℝ} (hp : 2 < p) (n : ℕ) :
    eLpNorm (beltramiIter μ n) (ENNReal.ofReal p) ≤
      (ENNReal.ofReal (k * hilbertNorm p)) ^ n * eLpNorm μ (ENNReal.ofReal p) := by
  induction n with
  | zero => simp [beltramiIter]
  | succ n ih => exact rep_eLpNorm_iter_step hk₀ hμ hp ih

/-- The uniform support radius: every `beltramiIter μ n` vanishes outside `closedBall 0 R`. -/
theorem rep_iter_supp_bound {μ : ℂ → ℂ} {k : ℝ} (hμ : IsCompactBeltramiCoeff μ k) :
    ∃ R : ℝ, 0 < R ∧ ∀ n : ℕ, ∀ z : ℂ, R < ‖z‖ → beltramiIter μ n z = 0 := by
  obtain ⟨R₀, hR₀⟩ := (rep_beltramiCoeff_hasCompactSupport hμ).isCompact.isBounded.subset_closedBall
    (0 : ℂ)
  refine ⟨max R₀ 1, by positivity, fun n z hz => ?_⟩
  by_contra hne
  have hzsupp : z ∈ Function.support (beltramiIter μ n) := hne
  have := rep_support_subset n hzsupp
  have hz' := hR₀ this
  rw [mem_closedBall_zero_iff] at hz'
  have : R₀ ≤ max R₀ 1 := le_max_left _ _
  linarith

/-- Extracted per-`(n, z)` step of `rep_cauchyT_iter_bound` (top-level, as with
`rep_eLpNorm_iter_step`: the inline version hit the same pathological slowdown once enough
`have`s had accumulated in the surrounding proof). -/
theorem rep_cauchyT_bound_step {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hμ : IsCompactBeltramiCoeff μ k)
    {p : ℝ} (hp : 2 < p) {R : ℝ} (hRsupp : ∀ (n : ℕ) (z : ℂ), R < ‖z‖ → beltramiIter μ n z = 0)
    {M₁ : ℝ}
    (hM₁ : ∀ ω : ℂ → ℂ, MemLp ω (ENNReal.ofReal p) → (∀ z, R < ‖z‖ → ω z = 0) → ∀ z,
      ‖cauchyT ω z‖ ≤ M₁ * (eLpNorm ω (ENNReal.ofReal p)).toReal)
    (n : ℕ) (z : ℂ) :
    ‖cauchyT (beltramiIter μ n) z‖ ≤
      (max M₁ 0 * (eLpNorm μ (ENNReal.ofReal p)).toReal) * (k * hilbertNorm p) ^ n := by
  set r : ℝ := k * hilbertNorm p with hrdef
  have hr0 : 0 ≤ r := mul_nonneg hk₀ (hilbertNorm_nonneg p)
  set M₁' : ℝ := max M₁ 0 with hM₁'def
  have hM₁'nn : 0 ≤ M₁' := le_max_right _ _
  have hbound1 : ‖cauchyT (beltramiIter μ n) z‖ ≤
      M₁ * (eLpNorm (beltramiIter μ n) (ENNReal.ofReal p)).toReal :=
    hM₁ (beltramiIter μ n) (rep_memLp_iter hk₀ hμ hp n) (hRsupp n) z
  have hnormnn : 0 ≤ (eLpNorm (beltramiIter μ n) (ENNReal.ofReal p)).toReal := ENNReal.toReal_nonneg
  have hbound1' : ‖cauchyT (beltramiIter μ n) z‖ ≤
      M₁' * (eLpNorm (beltramiIter μ n) (ENNReal.ofReal p)).toReal :=
    hbound1.trans (mul_le_mul_of_nonneg_right (le_max_left M₁ 0) hnormnn)
  have hle : eLpNorm (beltramiIter μ n) (ENNReal.ofReal p) ≤
      (ENNReal.ofReal r) ^ n * eLpNorm μ (ENNReal.ofReal p) := rep_eLpNorm_iter_le hk₀ hμ hp n
  have hfin2 : ((ENNReal.ofReal r) ^ n * eLpNorm μ (ENNReal.ofReal p)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (rep_memLp_beltramiCoeff hμ hp).eLpNorm_ne_top
  have htoreal : (eLpNorm (beltramiIter μ n) (ENNReal.ofReal p)).toReal ≤
      ((ENNReal.ofReal r) ^ n * eLpNorm μ (ENNReal.ofReal p)).toReal :=
    ENNReal.toReal_mono hfin2 hle
  have hrw : ((ENNReal.ofReal r) ^ n * eLpNorm μ (ENNReal.ofReal p)).toReal =
      r ^ n * (eLpNorm μ (ENNReal.ofReal p)).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr0]
  rw [hrw] at htoreal
  have hfinal : ‖cauchyT (beltramiIter μ n) z‖ ≤
      M₁' * (r ^ n * (eLpNorm μ (ENNReal.ofReal p)).toReal) :=
    hbound1'.trans (mul_le_mul_of_nonneg_left htoreal hM₁'nn)
  have heq : M₁' * (r ^ n * (eLpNorm μ (ENNReal.ofReal p)).toReal) =
      (M₁' * (eLpNorm μ (ENNReal.ofReal p)).toReal) * r ^ n := by ring
  rwa [heq] at hfinal

/-- **First conjunct of Theorem 13.1**: `‖T(β_n)‖_∞ ≤ C r^n` for a fixed `C, r < 1`. -/
theorem rep_cauchyT_iter_bound {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hμ : IsCompactBeltramiCoeff μ k)
    {p : ℝ} (hp : 2 < p) (hkp : k * hilbertNorm p < 1) :
    ∃ C r : ℝ, r < 1 ∧ ∀ n z, ‖cauchyT (beltramiIter μ n) z‖ ≤ C * r ^ n := by
  obtain ⟨R, hR, hRsupp⟩ := rep_iter_supp_bound hμ
  obtain ⟨M₁, hM₁⟩ := lemma11_1 hp hR
  refine ⟨max M₁ 0 * (eLpNorm μ (ENNReal.ofReal p)).toReal, k * hilbertNorm p, hkp, ?_⟩
  intro n z
  exact rep_cauchyT_bound_step hk₀ hμ hp hRsupp hM₁ n z

/-! ## The general-`p` additivity helper for `hilbertH`

`hilbertH_add_ae`/`hilbertH_smul_ae` (S11) are unconditional only at `p = 2`. The general-`p`
subtraction `hilbertH_sub_ae_of_smooth_bound` (S11) is conditional on a smooth bound
(`zygmund_calderon`); negation and addition at general `p` are derived from it here, combined with
`offsupp_hilbertH_ae_zero_of_eq_zero` (S11, `hilbertH 0 =ᵐ 0`). Conditional on the same wall,
exactly as `phiMap_sub_bound` (S12) is. -/

theorem rep_hilbertH_neg_ae {p A : ℝ} (hp : 1 < p)
    (hbound : ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal A * eLpNorm φ (ENNReal.ofReal p) volume)
    {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p)) :
    hilbertH (fun z => -ω z) =ᵐ[volume] fun z => -hilbertH ω z := by
  have hmemzero : MemLp (fun _ : ℂ => (0:ℂ)) (ENNReal.ofReal p) := memLp_iff.mpr (by simp)
  have hsub := hilbertH_sub_ae_of_smooth_bound hp hbound hmemzero hω
  have heqfun : (fun z => (0:ℂ) - ω z) = fun z => -ω z := by funext z; ring
  rw [heqfun] at hsub
  have hmemzero2 : MemLp (fun _ : ℂ => (0:ℂ)) 2 volume := memLp_iff.mpr (by simp)
  have hzero : hilbertH (fun _ : ℂ => (0:ℂ)) =ᵐ[volume] 0 :=
    offsupp_hilbertH_ae_zero_of_eq_zero hmemzero2 rfl
  filter_upwards [hsub, hzero] with z hz1 hz2
  rw [hz1, hz2]
  simp

theorem rep_hilbertH_add_ae_of_smooth_bound {p A : ℝ} (hp : 1 < p)
    (hbound : ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal A * eLpNorm φ (ENNReal.ofReal p) volume)
    {ω₁ ω₂ : ℂ → ℂ} (hω₁ : MemLp ω₁ (ENNReal.ofReal p)) (hω₂ : MemLp ω₂ (ENNReal.ofReal p)) :
    hilbertH (fun z => ω₁ z + ω₂ z) =ᵐ[volume]
      fun z => hilbertH ω₁ z + hilbertH ω₂ z := by
  have hω₂' : MemLp (fun z => -ω₂ z) (ENNReal.ofReal p) := hω₂.neg
  have hsub := hilbertH_sub_ae_of_smooth_bound hp hbound hω₁ hω₂'
  have heqfun : (fun z => ω₁ z - (-ω₂ z)) = fun z => ω₁ z + ω₂ z := by funext z; ring
  rw [heqfun] at hsub
  have hneg := rep_hilbertH_neg_ae hp hbound hω₂
  filter_upwards [hsub, hneg] with z hz1 hz2
  rw [hz1, hz2]
  ring

/-- Extracted successor step of `rep_hilbertH_sum_range_ae` (top-level, matching the recurring
project fix for `calc`/`induction` slowdowns). -/
theorem rep_hilbertH_sum_range_step {p A : ℝ} (hp : 1 < p)
    (hbound : ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal A * eLpNorm φ (ENNReal.ofReal p) volume)
    {f : ℕ → ℂ → ℂ} (hf : ∀ n, MemLp (f n) (ENNReal.ofReal p)) {N : ℕ}
    (ih : hilbertH (fun z => ∑ n ∈ Finset.range N, f n z) =ᵐ[volume]
      fun z => ∑ n ∈ Finset.range N, hilbertH (f n) z) :
    hilbertH (fun z => ∑ n ∈ Finset.range (N + 1), f n z) =ᵐ[volume]
      fun z => ∑ n ∈ Finset.range (N + 1), hilbertH (f n) z := by
  have heq1 : (fun z => ∑ n ∈ Finset.range (N + 1), f n z) =
      fun z => (∑ n ∈ Finset.range N, f n z) + f N z := by
    funext z; rw [Finset.sum_range_succ]
  rw [heq1]
  have hSmem : MemLp (fun z => ∑ n ∈ Finset.range N, f n z) (ENNReal.ofReal p) :=
    memLp_finsetSum (Finset.range N) (fun n _ => hf n)
  have hadd := rep_hilbertH_add_ae_of_smooth_bound hp hbound hSmem (hf N)
  have heq2 : (fun z => ∑ n ∈ Finset.range (N + 1), hilbertH (f n) z) =
      fun z => (∑ n ∈ Finset.range N, hilbertH (f n) z) + hilbertH (f N) z := by
    funext z; rw [Finset.sum_range_succ]
  rw [heq2]
  filter_upwards [hadd, ih] with z hz1 hz2
  rw [hz1, hz2]

theorem rep_hilbertH_sum_range_ae {p A : ℝ} (hp : 1 < p)
    (hbound : ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal A * eLpNorm φ (ENNReal.ofReal p) volume)
    {f : ℕ → ℂ → ℂ} (hf : ∀ n, MemLp (f n) (ENNReal.ofReal p)) (N : ℕ) :
    hilbertH (fun z => ∑ n ∈ Finset.range N, f n z) =ᵐ[volume]
      fun z => ∑ n ∈ Finset.range N, hilbertH (f n) z := by
  induction N with
  | zero =>
    have hmemzero2 : MemLp (fun _ : ℂ => (0:ℂ)) 2 volume := memLp_iff.mpr (by simp)
    have hz := offsupp_hilbertH_ae_zero_of_eq_zero hmemzero2 rfl
    simp only [Finset.range_zero, Finset.sum_empty]
    exact hz
  | succ N ih => exact rep_hilbertH_sum_range_step hp hbound hf ih

/-! ## The partial-sum identity: `neumannIter μ μ N = ∑_{n<N} beltramiIter μ n` -/

theorem rep_neumannIter_succ (μ h : ℂ → ℂ) (n : ℕ) :
    neumannIter μ h (n + 1) = fun z => μ z * hilbertH (neumannIter μ h n) z + h z := rfl

/-- Extracted successor step (top-level, same reason as the other extractions above). -/
theorem rep_neumann_partial_sum_step {μ : ℂ → ℂ} {k A : ℝ} (hk₀ : 0 ≤ k)
    (hμ : IsCompactBeltramiCoeff μ k) {p : ℝ} (hp : 2 < p)
    (hbound : ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal A * eLpNorm φ (ENNReal.ofReal p) volume)
    {N : ℕ}
    (ih : neumannIter μ μ N =ᵐ[volume] fun z => ∑ n ∈ Finset.range (N + 1), beltramiIter μ n z) :
    neumannIter μ μ (N + 1) =ᵐ[volume]
      fun z => ∑ n ∈ Finset.range (N + 1 + 1), beltramiIter μ n z := by
  have hp1 : 1 < p := by linarith
  have hHeq : hilbertH (neumannIter μ μ N) =
      hilbertH (fun z => ∑ n ∈ Finset.range (N + 1), beltramiIter μ n z) :=
    hilbertH_congr_ae ih
  have hSum := rep_hilbertH_sum_range_ae hp1 hbound (fun n => rep_memLp_iter hk₀ hμ hp n) (N + 1)
  rw [rep_neumannIter_succ]
  have heqrhs : (fun z => ∑ n ∈ Finset.range (N + 1 + 1), beltramiIter μ n z) =
      fun z => (∑ n ∈ Finset.range (N + 1), beltramiIter μ (n + 1) z) + μ z := by
    funext z
    rw [Finset.sum_range_succ']
    rfl
  rw [heqrhs]
  filter_upwards [hSum] with z hz
  rw [hHeq, hz, Finset.mul_sum]
  have hterm : ∀ n ∈ Finset.range (N + 1), μ z * hilbertH (beltramiIter μ n) z =
      beltramiIter μ (n + 1) z := by
    intro n _
    rw [rep_beltramiIter_succ]
  rw [Finset.sum_congr rfl hterm]

theorem rep_neumann_partial_sum {μ : ℂ → ℂ} {k A : ℝ} (hk₀ : 0 ≤ k)
    (hμ : IsCompactBeltramiCoeff μ k) {p : ℝ} (hp : 2 < p)
    (hbound : ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal A * eLpNorm φ (ENNReal.ofReal p) volume) (N : ℕ) :
    neumannIter μ μ N =ᵐ[volume] fun z => ∑ n ∈ Finset.range (N + 1), beltramiIter μ n z := by
  induction N with
  | zero =>
    refine Eventually.of_forall (fun z => ?_)
    show neumannIter μ μ 0 z = ∑ n ∈ Finset.range (0 + 1), beltramiIter μ n z
    rw [Finset.sum_range_one]
    rfl
  | succ N ih => exact rep_neumann_partial_sum_step hk₀ hμ hp hbound ih

/-! ## `cauchyT`'s finite additivity over `beltramiIter`, and the final assembly -/

theorem rep_cauchyT_sum_range_step {p : ℝ} (hp : 2 < p) {R : ℝ} (hR : 0 < R)
    {f : ℕ → ℂ → ℂ} (hf : ∀ n, MemLp (f n) (ENNReal.ofReal p))
    (hfsupp : ∀ (n : ℕ) (z : ℂ), R < ‖z‖ → f n z = 0) {N : ℕ}
    (ih : cauchyT (fun z => ∑ n ∈ Finset.range N, f n z) = fun z => ∑ n ∈ Finset.range N, cauchyT (f n) z) :
    cauchyT (fun z => ∑ n ∈ Finset.range (N + 1), f n z) =
      fun z => ∑ n ∈ Finset.range (N + 1), cauchyT (f n) z := by
  have heq1 : (fun z => ∑ n ∈ Finset.range (N + 1), f n z) =
      fun z => (∑ n ∈ Finset.range N, f n z) + f N z := by
    funext z; rw [Finset.sum_range_succ]
  rw [heq1]
  have hSmem : MemLp (fun z => ∑ n ∈ Finset.range N, f n z) (ENNReal.ofReal p) :=
    memLp_finsetSum (Finset.range N) (fun n _ => hf n)
  have hSsupp : ∀ z : ℂ, R < ‖z‖ → (∑ n ∈ Finset.range N, f n z) = 0 := by
    intro z hz
    apply Finset.sum_eq_zero
    intro n _
    exact hfsupp n z hz
  have hadd := cauchyT_add hp hR hSmem (hf N) hSsupp (hfsupp N)
  rw [hadd]
  have heq2 : (fun z => ∑ n ∈ Finset.range (N + 1), cauchyT (f n) z) =
      fun z => (∑ n ∈ Finset.range N, cauchyT (f n) z) + cauchyT (f N) z := by
    funext z; rw [Finset.sum_range_succ]
  rw [heq2, ih]

theorem rep_cauchyT_sum_range {p : ℝ} (hp : 2 < p) {R : ℝ} (hR : 0 < R)
    {f : ℕ → ℂ → ℂ} (hf : ∀ n, MemLp (f n) (ENNReal.ofReal p))
    (hfsupp : ∀ (n : ℕ) (z : ℂ), R < ‖z‖ → f n z = 0) (N : ℕ) :
    cauchyT (fun z => ∑ n ∈ Finset.range N, f n z) = fun z => ∑ n ∈ Finset.range N, cauchyT (f n) z := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    funext z
    unfold cauchyT
    simp
  | succ N ih => exact rep_cauchyT_sum_range_step hp hR hf hfsupp ih

theorem rep_tendstoUniformly_unshift {F : ℕ → ℂ → ℂ} {L : ℂ → ℂ}
    (h : TendstoUniformly (fun M => F (M + 1)) L atTop) : TendstoUniformly F L atTop := by
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h ε hε)
  rw [Filter.eventually_atTop]
  refine ⟨N + 1, fun n hn x => ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hthis := hN (N + m) (by omega) x
  have heq2 : N + 1 + m = (N + m) + 1 := by ring
  rw [heq2]
  exact hthis

/-- **Second conjunct of Theorem 13.1**: the partial sums of `T` applied to the series terms
converge uniformly to `T(ω)`. -/
theorem rep_cauchyT_sum_tendstoUniformly {μ : ℂ → ℂ} {k A : ℝ} (hk₀ : 0 ≤ k)
    (hμ : IsCompactBeltramiCoeff μ k) {p : ℝ} (hp : 2 < p) (hkp : k * hilbertNorm p < 1)
    (hbound : ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal A * eLpNorm φ (ENNReal.ofReal p) volume)
    {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p))
    (hsol : ω =ᵐ[volume] fun z => μ z * hilbertH ω z + μ z) :
    TendstoUniformly (fun N z => ∑ n ∈ Finset.range N, cauchyT (beltramiIter μ n) z)
      (fun z => cauchyT ω z) atTop := by
  apply rep_tendstoUniformly_unshift
  obtain ⟨R, hR, hRsupp⟩ := rep_iter_supp_bound hμ
  have hμsupp : ∀ z : ℂ, R < ‖z‖ → μ z = 0 := hRsupp 0
  have hωae : ∀ᵐ z, R < ‖z‖ → ω z = 0 := by
    filter_upwards [hsol] with z hz hzR
    rw [hz, hμsupp z hzR]; ring
  set ω' : ℂ → ℂ := (closedBall (0:ℂ) R).indicator ω with hω'def
  have hω'ae : ω' =ᵐ[volume] ω := by
    filter_upwards [hωae] with z hz
    by_cases hzmem : z ∈ closedBall (0:ℂ) R
    · rw [hω'def, Set.indicator_of_mem hzmem]
    · rw [hω'def, Set.indicator_of_notMem hzmem]
      rw [mem_closedBall_zero_iff, not_le] at hzmem
      exact (hz hzmem).symm
  have hω'mem : MemLp ω' (ENNReal.ofReal p) := hω.indicator measurableSet_closedBall
  have hω'supp : ∀ z : ℂ, R < ‖z‖ → ω' z = 0 := by
    intro z hz
    rw [hω'def]
    apply Set.indicator_of_notMem
    rw [mem_closedBall_zero_iff, not_le]
    exact hz
  have hcauchyTeq : cauchyT ω' = cauchyT ω := cauchyT_congr_ae hω'ae
  obtain ⟨M₂, hM₂⟩ := lemma11_1 hp hR
  have hβmem : ∀ n, MemLp (beltramiIter μ n) (ENNReal.ofReal p) := fun n => rep_memLp_iter hk₀ hμ hp n
  have hSmem : ∀ N, MemLp (fun z => ∑ n ∈ Finset.range N, beltramiIter μ n z) (ENNReal.ofReal p) :=
    fun N => memLp_finsetSum (Finset.range N) (fun n _ => hβmem n)
  have hSsupp : ∀ N, ∀ z : ℂ, R < ‖z‖ → (∑ n ∈ Finset.range N, beltramiIter μ n z) = 0 := by
    intro N z hz
    exact Finset.sum_eq_zero (fun n _ => hRsupp n z hz)
  set M₂' : ℝ := max M₂ 0 with hM₂'def
  have hM₂'nn : 0 ≤ M₂' := le_max_right _ _
  have hLpconv : Tendsto (fun N =>
      (eLpNorm (fun w => (∑ n ∈ Finset.range (N+1), beltramiIter μ n w) - ω' w)
        (ENNReal.ofReal p)).toReal) atTop (𝓝 0) := by
    have hstep1 : Tendsto (fun N => eLpNorm (fun z => neumannIter μ μ N z - ω z)
        (ENNReal.ofReal p)) atTop (𝓝 0) :=
      eq12_2_neumann hk₀ hμ.1 hp hkp (rep_memLp_beltramiCoeff hμ hp) hω hsol
    have hcongrN : ∀ N, eLpNorm (fun w => (∑ n ∈ Finset.range (N+1), beltramiIter μ n w) - ω' w)
        (ENNReal.ofReal p) = eLpNorm (fun z => neumannIter μ μ N z - ω z) (ENNReal.ofReal p) := by
      intro N
      apply eLpNorm_congr_ae
      filter_upwards [rep_neumann_partial_sum hk₀ hμ hp hbound N, hω'ae] with z hz1 hz2
      rw [hz2]
      congr 1
      exact hz1.symm
    have hstep2 : Tendsto (fun N => eLpNorm (fun w => (∑ n ∈ Finset.range (N+1), beltramiIter μ n w) - ω' w)
        (ENNReal.ofReal p)) atTop (𝓝 0) := by
      have heq2 : (fun N => eLpNorm (fun w => (∑ n ∈ Finset.range (N+1), beltramiIter μ n w) - ω' w)
          (ENNReal.ofReal p)) = fun N => eLpNorm (fun z => neumannIter μ μ N z - ω z) (ENNReal.ofReal p) :=
        funext hcongrN
      rw [heq2]; exact hstep1
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hstep2
  have hbtendsto : Tendsto (fun N => M₂' *
      (eLpNorm (fun w => (∑ n ∈ Finset.range (N+1), beltramiIter μ n w) - ω' w)
        (ENNReal.ofReal p)).toReal) atTop (𝓝 0) := by
    have := hLpconv.const_mul M₂'
    simpa using this
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hev : ∀ᶠ N in atTop, M₂' *
      (eLpNorm (fun w => (∑ n ∈ Finset.range (N+1), beltramiIter μ n w) - ω' w)
        (ENNReal.ofReal p)).toReal < ε := (tendsto_order.mp hbtendsto).2 ε hε
  filter_upwards [hev] with N hN x
  rw [dist_comm, dist_eq_norm]
  have hsumeq := rep_cauchyT_sum_range hp hR hβmem hRsupp (N + 1)
  have hdiffmem : MemLp (fun w => (∑ n ∈ Finset.range (N+1), beltramiIter μ n w) - ω' w)
      (ENNReal.ofReal p) := (hSmem (N+1)).sub hω'mem
  have hdiffsupp : ∀ z : ℂ, R < ‖z‖ →
      (∑ n ∈ Finset.range (N+1), beltramiIter μ n z) - ω' z = 0 := by
    intro z hz
    rw [hSsupp (N+1) z hz, hω'supp z hz, sub_zero]
  have hsub := cauchyT_sub hp hR (hSmem (N+1)) hω'mem (hSsupp (N+1)) hω'supp
  have hM₂x := hM₂ (fun w => (∑ n ∈ Finset.range (N+1), beltramiIter μ n w) - ω' w)
    hdiffmem hdiffsupp x
  have hM₂x' : ‖cauchyT (fun w => (∑ n ∈ Finset.range (N+1), beltramiIter μ n w) - ω' w) x‖ ≤
      M₂' * (eLpNorm (fun w => (∑ n ∈ Finset.range (N+1), beltramiIter μ n w) - ω' w)
        (ENNReal.ofReal p)).toReal :=
    hM₂x.trans (mul_le_mul_of_nonneg_right (le_max_left M₂ 0) ENNReal.toReal_nonneg)
  have hgoal : (∑ n ∈ Finset.range (N+1), cauchyT (beltramiIter μ n) x) - cauchyT ω x =
      cauchyT (fun w => (∑ n ∈ Finset.range (N+1), beltramiIter μ n w) - ω' w) x := by
    rw [hsub]
    dsimp only
    rw [← congrFun hsumeq x, congrFun hcauchyTeq x]
  show ‖(∑ n ∈ Finset.range (N+1), cauchyT (beltramiIter μ n) x) - cauchyT ω x‖ < ε
  rw [hgoal]
  exact hM₂x'.trans_lt hN

/-- **Theorem 13.1** (表示定理): for `μ` with bounded support and `‖μ‖_∞ < 1`, the global
homeomorphic solution `w = z + T(ω)` of the Beltrami equation has the representation (13.2)
`w(z) = z + T(μ) + T(μH(μ)) + T(μH(μH(μ))) + ⋯`, the series converging absolutely and uniformly
in the whole plane.

Proved: the geometric term bound (`rep_cauchyT_iter_bound`, via Lemma 11.1 and the L^p-norm
recursion from (11.16)) and the uniform convergence of the partial sums to `T(ω)`
(`rep_cauchyT_sum_tendstoUniformly`, via the Neumann series (12.2) applied at `h := μ`, the
partial-sum identity `neumannIter μ μ N = ∑_{n≤N} beltramiIter μ n`, and Lemma 11.1 again on the
L^p-vanishing remainder). Tainted by `zygmund_calderon` alone, through `eq11_16`/`eq12_2_neumann`
and the general-`p` additivity helper above. -/
theorem thm13_1_representation {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμ : IsCompactBeltramiCoeff μ k) {p : ℝ} (hp : 2 < p) (hkp : k * hilbertNorm p < 1)
    {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p))
    (hsol : ω =ᵐ[volume] fun z => μ z * hilbertH ω z + μ z) :
    (∃ C r : ℝ, r < 1 ∧ ∀ n z, ‖cauchyT (beltramiIter μ n) z‖ ≤ C * r ^ n) ∧
      TendstoUniformly (fun N z => z + ∑ n ∈ Finset.range N, cauchyT (beltramiIter μ n) z)
        (fun z => z + cauchyT ω z) atTop := by
  have hp1 : 1 < p := by linarith
  obtain ⟨A, hA0, hbound⟩ := zygmund_calderon hp1
  refine ⟨rep_cauchyT_iter_bound hk₀ hμ hp hkp, ?_⟩
  have hconv := rep_cauchyT_sum_tendstoUniformly hk₀ hμ hp hkp hbound hω hsol
  rw [Metric.tendstoUniformly_iff] at hconv ⊢
  intro ε hε
  filter_upwards [hconv ε hε] with N hN
  intro x
  have hNx := hN x
  rw [dist_eq_norm] at hNx
  rw [dist_eq_norm, add_sub_add_left_eq_sub]
  exact hNx

/-! ## §13.2 The similarity principle -/

/-- `w` is an `L_p` generalized (not necessarily homeomorphic) solution in `D` of the Beltrami
equation `∂_{z̄} w = μ ∂_z w`. -/
def IsGenSolution (w μ : ℂ → ℂ) (D : Set ℂ) (p : ℝ≥0∞) : Prop :=
  ∃ g h : ℂ → ℂ, HasGenPartials w g h D p ∧ ∀ᵐ z ∂(volume.restrict D), genDzbar g h z = μ z * genDz g h z

/-! ### Lemma 13.1 track — helpers of piece P -/


/-- **P1.** Both line derivatives of an A.C.L. map exist a.e. (the proof of `thm9_2_partials_ae`
with `thm9_1_isACL hf` replaced by `hacl`; it only uses `acl_ae_rect` and the rational cover). -/
theorem cr_p_partials_ae_of_isACL {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hacl : IsACL f D) :
    ∀ᵐ z ∂(volume.restrict D), DifferentiableAt ℝ (fun t : ℝ => f (z + t)) 0 ∧
      DifferentiableAt ℝ (fun t : ℝ => f (z + t * I)) 0 :=
  ae_restrict_of_forall_openRect hD fun a b c d hab hcd hR =>
    acl_ae_rect hacl.1 hab hcd hR (hacl.2 a b c d hab hcd hR).2 (hacl.2 a b c d hab hcd hR).1

/-- **P2.** A homeomorphism of an open set with `L_p` generalized partials (`p ≥ 1`) is
`ℝ`-differentiable a.e., and there `f'(z) 1 = fx z`, `f'(z) I = fy z`
(`lemma9_2_isACL_of_genPartials`, P1, `lemma9_1_menchoff`, `partialX_eq_of_differentiableAt`). -/
theorem cr_p_differentiable_ae {f fx fy : ℂ → ℂ} {D D' : Set ℂ} (hD : IsOpen D) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hf : IsHomeomorphOnto f D D') (hfd : HasGenPartials f fx fy D p) :
    ∀ᵐ z ∂(volume.restrict D),
      DifferentiableAt ℝ f z ∧ fderiv ℝ f z 1 = fx z ∧ fderiv ℝ f z I = fy z := by
  obtain ⟨hacl, hpx, hpy⟩ := lemma9_2_isACL_of_genPartials hD hp hfd
  have hdiff := lemma9_1_menchoff hD hf (cr_p_partials_ae_of_isACL hD hacl)
  filter_upwards [hdiff, hpx, hpy] with z hz hzx hzy
  refine ⟨hz, ?_, ?_⟩
  · rw [← partialX_eq_of_differentiableAt hz]
    exact hzx
  · rw [← partialY_eq_of_differentiableAt hz]
    exact hzy

/-- **P3 (Lusin's property (N)).** A homeomorphism of an open set with `L_p` generalized partials,
`p ≥ 2`, maps null sets to null sets (the generalized `ac_n_volume_image_null` of S09: A.C.L. and
the a.e. identification of the classical partials from `lemma9_2_isACL_of_genPartials`, local `L²`
from local `L^p` on the finite measure of a compact set). -/
theorem cr_p_volume_image_null {f fx fy : ℂ → ℂ} {D D' : Set ℂ} (hD : IsOpen D) {p : ℝ}
    (hp : 2 ≤ p) (hf : IsHomeomorphOnto f D D')
    (hfd : HasGenPartials f fx fy D (ENNReal.ofReal p)) {E : Set ℂ} (hED : E ⊆ D)
    (hE : volume E = 0) : volume (f '' E) = 0 := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have h2le : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal hp
  obtain ⟨hacl, hpx, hpy⟩ := lemma9_2_isACL_of_genPartials hD hp1 hfd
  have hcontinv : ContinuousOn (Function.invFunOn f D) (f '' D) := by
    rw [hf.2.2.1]
    exact hf.2.2.2
  have hL2 : ∀ C ⊆ D, IsCompact C →
      MemLp (partialX f) 2 (volume.restrict C) ∧ MemLp (partialY f) 2 (volume.restrict C) := by
    intro C hCD hC
    haveI : IsFiniteMeasure (volume.restrict C) :=
      isFiniteMeasure_restrict.2 hC.measure_lt_top.ne
    obtain ⟨hx, hy⟩ := hfd.1 C hCD hC
    have hpxC : partialX f =ᵐ[volume.restrict C] fx :=
      ae_restrict_of_ae_restrict_of_subset hCD hpx
    have hpyC : partialY f =ᵐ[volume.restrict C] fy :=
      ae_restrict_of_ae_restrict_of_subset hCD hpy
    exact ⟨MemLp.ae_eq hpxC.symm (hx.mono_exponent h2le),
      MemLp.ae_eq hpyC.symm (hy.mono_exponent h2le)⟩
  exact ac_n_volume_image_null hD hacl hf.2.1 hcontinv hL2 hED hE

/-- **P4.** Pull-back of a.e. statements through `f`: if the inverse `φ` of `f` has `L_p`
generalized partials on the open `D'` (`p ≥ 2`) and `P` holds a.e. on `f '' C`, then `P ∘ f` holds
a.e. on the compact `C ⊆ D` (the exceptional set is `φ '' N` with `N ⊆ f '' C` null: P3 for `φ`). -/
theorem cr_p_ae_comp {f fix fiy : ℂ → ℂ} {D D' : Set ℂ} (_hD : IsOpen D) (hD' : IsOpen D')
    {p : ℝ} (hp : 2 ≤ p) (hf : IsHomeomorphOnto f D D')
    (hfi : HasGenPartials (Function.invFunOn f D) fix fiy D' (ENNReal.ofReal p))
    {C : Set ℂ} (hC : IsCompact C) (hCD : C ⊆ D) {P : ℂ → Prop}
    (hP : ∀ᵐ w ∂(volume.restrict (f '' C)), P w) :
    ∀ᵐ z ∂(volume.restrict C), P (f z) := by
  have hT : IsCompact (f '' C) := hC.image_of_continuousOn (hf.1.mono hCD)
  have hN0 : volume {w | ¬ (w ∈ f '' C → P w)} = 0 := by
    have h1 : ∀ᵐ w ∂volume, w ∈ f '' C → P w :=
      (ae_restrict_iff' hT.isClosed.measurableSet).1 hP
    rwa [ae_iff] at h1
  have hNsub : {w | ¬ (w ∈ f '' C → P w)} ⊆ D' := by
    intro w hw
    rw [mem_setOf_eq] at hw
    push Not at hw
    rw [← hf.2.2.1]
    exact image_mono hCD hw.1
  have himg : volume (Function.invFunOn f D '' {w | ¬ (w ∈ f '' C → P w)}) = 0 :=
    cr_p_volume_image_null hD' hp (isHomeomorphOnto_invFunOn hf) hfi hNsub hN0
  have hgoal : volume {z | ¬ (z ∈ C → P (f z))} = 0 := by
    refine measure_mono_null (fun z hz => ?_) himg
    rw [mem_setOf_eq] at hz
    push Not at hz
    refine ⟨f z, ?_, hf.2.1.leftInvOn_invFunOn (hCD hz.1)⟩
    rw [mem_setOf_eq]
    push Not
    exact ⟨mem_image_of_mem f hz.1, hz.2⟩
  have : ∀ᵐ z ∂volume, z ∈ C → P (f z) := by rwa [ae_iff]
  exact (ae_restrict_iff' hC.isClosed.measurableSet).2 this



/-! ### Lemma 13.1 track — helpers of piece C -/


/-- A real-linear map of `ℂ` is determined by its values at `1` and `I`. -/
theorem cr_c_clm_apply (A : ℂ →L[ℝ] ℂ) (ζ : ℂ) :
    A ζ = (ζ.re : ℂ) * A 1 + (ζ.im : ℂ) * A I := by
  conv_lhs => rw [← Complex.re_add_im ζ]
  rw [show ((ζ.re : ℂ) + (ζ.im : ℂ) * I) = ζ.re • (1 : ℂ) + ζ.im • I by
    simp [Complex.real_smul]]
  rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

/-- **C1.** Inverse bound for real-linear maps of `ℂ`: if `B ∘ A = id` then
`‖B 1‖ |det A| ≤ ‖A 1‖ + ‖A I‖` and likewise for `B I`.  (With `A 1 = a + c I`, `A I = b + d I`,
`det A = a d − b c`, one has `A (d − c I) = det A` and `A (−b + a I) = (det A) I`, so
`(det A) · B 1 = d − c I` and `(det A) · B I = −b + a I` by `ℝ`-linearity of `B`.) -/
theorem cr_c_inverse_bound {A B : ℂ →L[ℝ] ℂ} (hBA : B.comp A = ContinuousLinearMap.id ℝ ℂ) :
    ‖B 1‖ * |A.det| ≤ ‖A 1‖ + ‖A I‖ ∧ ‖B I‖ * |A.det| ≤ ‖A 1‖ + ‖A I‖ := by
  obtain ⟨a, c, hA1⟩ : ∃ a c : ℝ, A 1 = (a : ℂ) + (c : ℂ) * I :=
    ⟨(A 1).re, (A 1).im, (Complex.re_add_im (A 1)).symm⟩
  obtain ⟨b, d, hAI⟩ : ∃ b d : ℝ, A I = (b : ℂ) + (d : ℂ) * I :=
    ⟨(A I).re, (A I).im, (Complex.re_add_im (A I)).symm⟩
  have hdet : A.det = a * d - b * c := by
    show LinearMap.det (A : ℂ →ₗ[ℝ] ℂ) = _
    rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
      Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousLinearMap.coe_coe]
    rw [hA1, hAI]
    simp
  have hBapply : ∀ ζ : ℂ, B (A ζ) = ζ := by
    intro ζ
    have h := congrArg (fun L : ℂ →L[ℝ] ℂ => L ζ) hBA
    simpa using h
  -- `A (d − c I) = det A` and `A (−b + a I) = (det A) I`
  have h1 : A ((d : ℂ) - (c : ℂ) * I) = ((A.det : ℝ) : ℂ) := by
    rw [cr_c_clm_apply, hA1, hAI, hdet]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    push_cast
    ring
  have h2 : A (-(b : ℂ) + (a : ℂ) * I) = ((A.det : ℝ) : ℂ) * I := by
    rw [cr_c_clm_apply, hA1, hAI, hdet]
    simp only [Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    push_cast
    ring
  have hsmul1 : B (((A.det : ℝ) : ℂ)) = ((A.det : ℝ) : ℂ) * B 1 := by
    conv_lhs => rw [show ((A.det : ℝ) : ℂ) = (A.det : ℝ) • (1 : ℂ) from by
      simp [Complex.real_smul]]
    rw [map_smul, Complex.real_smul]
  have hsmul2 : B (((A.det : ℝ) : ℂ) * I) = ((A.det : ℝ) : ℂ) * B I := by
    conv_lhs => rw [show ((A.det : ℝ) : ℂ) * I = (A.det : ℝ) • I from by
      simp [Complex.real_smul]]
    rw [map_smul, Complex.real_smul]
  have hkey1 : ((A.det : ℝ) : ℂ) * B 1 = (d : ℂ) - (c : ℂ) * I := by
    rw [← hsmul1, ← h1, hBapply]
  have hkey2 : ((A.det : ℝ) : ℂ) * B I = -(b : ℂ) + (a : ℂ) * I := by
    rw [← hsmul2, ← h2, hBapply]
  have hn1 : ‖B 1‖ * |A.det| = ‖(d : ℂ) - (c : ℂ) * I‖ := by
    rw [← hkey1, norm_mul, norm_real, Real.norm_eq_abs, mul_comm]
  have hn2 : ‖B I‖ * |A.det| = ‖-(b : ℂ) + (a : ℂ) * I‖ := by
    rw [← hkey2, norm_mul, norm_real, Real.norm_eq_abs, mul_comm]
  have hfin1 : ‖(d : ℂ) - (c : ℂ) * I‖ ≤ |d| + |c| := by
    calc ‖(d : ℂ) - (c : ℂ) * I‖ ≤ ‖(d : ℂ)‖ + ‖(c : ℂ) * I‖ := norm_sub_le _ _
      _ = |d| + |c| := by simp
  have hfin2 : ‖-(b : ℂ) + (a : ℂ) * I‖ ≤ |b| + |a| := by
    calc ‖-(b : ℂ) + (a : ℂ) * I‖ ≤ ‖-(b : ℂ)‖ + ‖(a : ℂ) * I‖ := norm_add_le _ _
      _ = |b| + |a| := by simp
  rw [hA1, hAI]
  have haa : |a| ≤ ‖(a : ℂ) + (c : ℂ) * I‖ := by
    simpa using Complex.abs_re_le_norm ((a : ℂ) + (c : ℂ) * I)
  have hcc : |c| ≤ ‖(a : ℂ) + (c : ℂ) * I‖ := by
    simpa using Complex.abs_im_le_norm ((a : ℂ) + (c : ℂ) * I)
  have hbb : |b| ≤ ‖(b : ℂ) + (d : ℂ) * I‖ := by
    simpa using Complex.abs_re_le_norm ((b : ℂ) + (d : ℂ) * I)
  have hdd : |d| ≤ ‖(b : ℂ) + (d : ℂ) * I‖ := by
    simpa using Complex.abs_im_le_norm ((b : ℂ) + (d : ℂ) * I)
  exact ⟨by rw [hn1]; linarith, by rw [hn2]; linarith⟩

/-- Auxiliary for **C2**: the transfer inequality in a single direction `e` (`e = 1` gives the
`x`-partial, `e = I` the `y`-partial). -/
theorem cr_c_transfer_dir {f fx fy fe fix fiy : ℂ → ℂ} {D D' : Set ℂ} {p : ℝ} {e : ℂ}
    (hp : 2 ≤ p) (hD : IsOpen D) (hD' : IsOpen D') (hf : IsHomeomorphOnto f D D')
    (hfd : HasGenPartials f fx fy D (ENNReal.ofReal p))
    (hfi : HasGenPartials (Function.invFunOn f D) fix fiy D' (ENNReal.ofReal p))
    (hfe : ∀ᵐ z ∂(volume.restrict D), DifferentiableAt ℝ f z ∧ fderiv ℝ f z e = fe z)
    (hbd : ∀ A B : ℂ →L[ℝ] ℂ, B.comp A = ContinuousLinearMap.id ℝ ℂ →
      ‖B e‖ * |A.det| ≤ ‖A 1‖ + ‖A I‖)
    {C : Set ℂ} (hC : IsCompact C) (hCD : C ⊆ D) {h : ℂ → ℝ≥0∞}
    (hh : AEMeasurable h (volume.restrict (f '' C))) :
    (∫⁻ z in C, h (f z) * ‖fe z‖ₑ) ≤ ∫⁻ w in f '' C, h w * (‖fix w‖ₑ + ‖fiy w‖ₑ) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hφhomeo : IsHomeomorphOnto (Function.invFunOn f D) D' D := isHomeomorphOnto_invFunOn hf
  have hT : IsCompact (f '' C) := hC.image_of_continuousOn (hf.1.mono hCD)
  have hTmeas : MeasurableSet (f '' C) := hT.isClosed.measurableSet
  have hCmeas : MeasurableSet C := hC.isClosed.measurableSet
  have hTD' : f '' C ⊆ D' := by
    rw [← hf.2.2.1]
    exact image_mono hCD
  have hleft : ∀ z ∈ D, Function.invFunOn f D (f z) = z := fun z hz =>
    hf.2.1.leftInvOn_invFunOn hz
  have hright : ∀ w ∈ D', f (Function.invFunOn f D w) = w := by
    intro w hw
    rw [← hf.2.2.1] at hw
    exact Function.invFunOn_eq hw
  -- the bad set of `C` (no derivative, or the wrong one) and a measurable null hull of its image
  have hZnull : volume {z | ¬ (z ∈ C → DifferentiableAt ℝ f z ∧ fderiv ℝ f z e = fe z)} = 0 := by
    have h1 : ∀ᵐ z ∂volume, z ∈ C → (DifferentiableAt ℝ f z ∧ fderiv ℝ f z e = fe z) :=
      (ae_restrict_iff' hCmeas).1 (ae_restrict_of_ae_restrict_of_subset hCD hfe)
    rwa [ae_iff] at h1
  have hZD : {z | ¬ (z ∈ C → DifferentiableAt ℝ f z ∧ fderiv ℝ f z e = fe z)} ⊆ D := by
    intro z hz
    rw [mem_setOf_eq] at hz
    push Not at hz
    exact hCD hz.1
  set Z : Set ℂ := {z | ¬ (z ∈ C → DifferentiableAt ℝ f z ∧ fderiv ℝ f z e = fe z)} with hZdef
  have hfZ : volume (f '' Z) = 0 := cr_p_volume_image_null hD hp hf hfd hZD hZnull
  set M : Set ℂ := toMeasurable volume (f '' Z) with hMdef
  have hMmeas : MeasurableSet M := by
    rw [hMdef]
    exact measurableSet_toMeasurable _ _
  have hMnull : volume M = 0 := by
    rw [hMdef, measure_toMeasurable]
    exact hfZ
  have hfZM : f '' Z ⊆ M := by
    rw [hMdef]
    exact subset_toMeasurable _ _
  -- the good measurable subset `S` of `f '' C`
  set S : Set ℂ :=
    (f '' C ∩ {w | DifferentiableAt ℝ (Function.invFunOn f D) w}) \ M with hSdef
  have hSmeas : MeasurableSet S := by
    rw [hSdef]
    exact (hTmeas.inter (measurableSet_of_differentiableAt ℝ (Function.invFunOn f D))).diff hMmeas
  have hST : S ⊆ f '' C := fun w hw => hw.1.1
  have hSD' : S ⊆ D' := hST.trans hTD'
  have hkey : ∀ w ∈ S, Function.invFunOn f D w ∈ C ∧ f (Function.invFunOn f D w) = w ∧
      DifferentiableAt ℝ (Function.invFunOn f D) w ∧
      DifferentiableAt ℝ f (Function.invFunOn f D w) ∧
      fderiv ℝ f (Function.invFunOn f D w) e = fe (Function.invFunOn f D w) := by
    intro w hw
    obtain ⟨z0, hz0C, rfl⟩ : ∃ z ∈ C, f z = w := hw.1.1
    have hinv : Function.invFunOn f D (f z0) = z0 := hleft z0 (hCD hz0C)
    have hz0Z : z0 ∉ Z := fun hcon => hw.2 (hfZM (mem_image_of_mem f hcon))
    rw [hZdef, mem_setOf_eq, not_not] at hz0Z
    obtain ⟨hd1, hd2⟩ := hz0Z hz0C
    refine ⟨by rw [hinv]; exact hz0C, by rw [hinv], hw.1.2, ?_, ?_⟩
    · rw [hinv]; exact hd1
    · rw [hinv]; exact hd2
  have hφSC : Function.invFunOn f D '' S ⊆ C := by
    rintro z ⟨w, hw, rfl⟩
    exact (hkey w hw).1
  -- `C` is covered by `φ '' S` up to a null set
  have hB1null :
      volume {z | ¬ (z ∈ C → DifferentiableAt ℝ (Function.invFunOn f D) (f z))} = 0 := by
    have hae := cr_p_ae_comp hD hD' hp hf hfi hC hCD
      (P := fun w => DifferentiableAt ℝ (Function.invFunOn f D) w)
      (by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hTD'
          (cr_p_differentiable_ae hD' hp1 hφhomeo hfi)] with w hw
        exact hw.1)
    rwa [ae_restrict_iff' hCmeas, ae_iff] at hae
  have hB2null : volume {z | ¬ (z ∈ C → f z ∉ M)} = 0 := by
    have hae := cr_p_ae_comp hD hD' hp hf hfi hC hCD (P := fun w => w ∉ M)
      (by
        refine ae_restrict_of_ae ?_
        rw [ae_iff]
        simpa using hMnull)
    rwa [ae_restrict_iff' hCmeas, ae_iff] at hae
  have hCdiff : volume (C \ Function.invFunOn f D '' S) = 0 := by
    refine measure_mono_null ?_ (measure_union_null hB1null hB2null)
    intro z hz
    rw [mem_union]
    by_contra hcon
    push Not at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    simp only [mem_setOf_eq] at hc1 hc2
    have hzC : z ∈ C := hz.1
    have hd1 : DifferentiableAt ℝ (Function.invFunOn f D) (f z) := by
      by_contra hcc
      exact hc1 ⟨hzC, hcc⟩
    have hd2 : f z ∉ M := fun hcc => hc2 ⟨hzC, hcc⟩
    exact hz.2 ⟨f z, ⟨⟨mem_image_of_mem f hzC, hd1⟩, hd2⟩, hleft z (hCD hzC)⟩
  -- the change of variables for `φ` on `S`
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas
    (fun w hw => ((hkey w hw).2.2.1).hasFDerivAt.hasFDerivWithinAt)
    (hφhomeo.2.1.mono hSD') (fun z => h (f z) * ‖fe z‖ₑ)
  -- the pointwise bound on `S`
  have hφae : ∀ᵐ w ∂(volume.restrict S), fderiv ℝ (Function.invFunOn f D) w 1 = fix w ∧
      fderiv ℝ (Function.invFunOn f D) w I = fiy w := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hSD'
      (cr_p_differentiable_ae hD' hp1 hφhomeo hfi)] with w hw
    exact ⟨hw.2.1, hw.2.2⟩
  have hbound : ∀ᵐ w ∂volume, w ∈ S →
      ENNReal.ofReal |(fderiv ℝ (Function.invFunOn f D) w).det| *
        (h (f (Function.invFunOn f D w)) * ‖fe (Function.invFunOn f D w)‖ₑ) ≤
        h w * (‖fix w‖ₑ + ‖fiy w‖ₑ) := by
    refine (ae_restrict_iff' hSmeas).1 ?_
    filter_upwards [hφae, self_mem_ae_restrict hSmeas] with w hw hwS
    obtain ⟨-, hfz, hdφ, hdf, hfee⟩ := hkey w hwS
    have hBA : (fderiv ℝ f (Function.invFunOn f D w)).comp
        (fderiv ℝ (Function.invFunOn f D) w) = ContinuousLinearMap.id ℝ ℂ := by
      have heq : (fun x => f (Function.invFunOn f D x)) =ᶠ[𝓝 w] id := by
        filter_upwards [hD'.mem_nhds (hSD' hwS)] with x hx
        exact hright x hx
      exact (hdf.hasFDerivAt.comp w hdφ.hasFDerivAt).unique
        ((hasFDerivAt_id w).congr_of_eventuallyEq heq)
    have hb := hbd (fderiv ℝ (Function.invFunOn f D) w)
      (fderiv ℝ f (Function.invFunOn f D w)) hBA
    rw [hfz, ← hfee, ← hw.1, ← hw.2]
    calc ENNReal.ofReal |(fderiv ℝ (Function.invFunOn f D) w).det| *
            (h w * ‖fderiv ℝ f (Function.invFunOn f D w) e‖ₑ)
        = h w * (ENNReal.ofReal |(fderiv ℝ (Function.invFunOn f D) w).det| *
            ‖fderiv ℝ f (Function.invFunOn f D w) e‖ₑ) := by ring
      _ ≤ h w * (‖fderiv ℝ (Function.invFunOn f D) w 1‖ₑ +
            ‖fderiv ℝ (Function.invFunOn f D) w I‖ₑ) := by
          gcongr
          rw [← ofReal_norm (fderiv ℝ f (Function.invFunOn f D w) e),
            ← ENNReal.ofReal_mul (abs_nonneg _),
            ← ofReal_norm (fderiv ℝ (Function.invFunOn f D) w 1),
            ← ofReal_norm (fderiv ℝ (Function.invFunOn f D) w I),
            ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (by rw [mul_comm]; exact hb)
  -- measurability of the majorant
  obtain ⟨hfixLp, hfiyLp⟩ := hfi.1 (f '' C) hTD' hT
  have hrestr : volume.restrict S ≤ volume.restrict (f '' C) := Measure.restrict_mono_set volume hST
  have hgmeas : AEMeasurable (fun w => h w * (‖fix w‖ₑ + ‖fiy w‖ₑ)) (volume.restrict S) :=
    (hh.mono_measure hrestr).mul
      (((hfixLp.aestronglyMeasurable.aemeasurable).mono_measure hrestr).enorm.add
        ((hfiyLp.aestronglyMeasurable.aemeasurable).mono_measure hrestr).enorm)
  calc (∫⁻ z in C, h (f z) * ‖fe z‖ₑ)
      = ∫⁻ z in Function.invFunOn f D '' S, h (f z) * ‖fe z‖ₑ :=
        setLIntegral_congr (ae_eq_set.2 ⟨hCdiff, by
          rw [diff_eq_empty.2 hφSC, measure_empty]⟩)
    _ = ∫⁻ w in S, ENNReal.ofReal |(fderiv ℝ (Function.invFunOn f D) w).det| *
          (h (f (Function.invFunOn f D w)) * ‖fe (Function.invFunOn f D w)‖ₑ) := hcv
    _ ≤ ∫⁻ w in S, h w * (‖fix w‖ₑ + ‖fiy w‖ₑ) := setLIntegral_mono_ae hgmeas hbound
    _ ≤ ∫⁻ w in f '' C, h w * (‖fix w‖ₑ + ‖fiy w‖ₑ) := lintegral_mono_set hST

/-- **C2 (CORE).** The transfer inequality: for a homeomorphism `f` of the open `D` onto the open
`D'` with `L_p` generalized partials (`p ≥ 2`) whose inverse has `L_p` generalized partials
`fix, fiy` on `D'`, every compact `C ⊆ D` and every `h ≥ 0` a.e.-measurable on `f '' C`,
`∫_C h(f z) |fx z| ≤ ∫_{f '' C} h(w) (|fix w| + |fiy w|)`, and the same with `fy`. -/
theorem cr_c_transfer {f fx fy fix fiy : ℂ → ℂ} {D D' : Set ℂ} {p : ℝ} (hp : 2 ≤ p)
    (hD : IsOpen D) (hD' : IsOpen D') (hf : IsHomeomorphOnto f D D')
    (hfd : HasGenPartials f fx fy D (ENNReal.ofReal p))
    (hfi : HasGenPartials (Function.invFunOn f D) fix fiy D' (ENNReal.ofReal p))
    {C : Set ℂ} (hC : IsCompact C) (hCD : C ⊆ D) {h : ℂ → ℝ≥0∞}
    (hh : AEMeasurable h (volume.restrict (f '' C))) :
    (∫⁻ z in C, h (f z) * ‖fx z‖ₑ) ≤ ∫⁻ w in f '' C, h w * (‖fix w‖ₑ + ‖fiy w‖ₑ) ∧
      (∫⁻ z in C, h (f z) * ‖fy z‖ₑ) ≤ ∫⁻ w in f '' C, h w * (‖fix w‖ₑ + ‖fiy w‖ₑ) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hP2 := cr_p_differentiable_ae hD hp1 hf hfd
  constructor
  · exact cr_c_transfer_dir hp hD hD' hf hfd hfi (hP2.mono fun z hz => ⟨hz.1, hz.2.1⟩)
      (fun _ _ hBA => (cr_c_inverse_bound hBA).1) hC hCD hh
  · exact cr_c_transfer_dir hp hD hD' hf hfd hfi (hP2.mono fun z hz => ⟨hz.1, hz.2.2⟩)
      (fun _ _ hBA => (cr_c_inverse_bound hBA).2) hC hCD hh



/-! ### Lemma 13.1 track — helpers of piece A -/


/-- **A1.** Real-linear maps of `ℂ` in Wirtinger form. -/
theorem cr_a_clm_apply (L : ℂ →L[ℝ] ℂ) (ζ : ℂ) :
    L ζ = (L 1 - I * L I) / 2 * ζ + (L 1 + I * L I) / 2 * conj ζ := by
  have hL : L ζ = (ζ.re : ℂ) * L 1 + (ζ.im : ℂ) * L I := by
    conv_lhs => rw [← Complex.re_add_im ζ]
    rw [show (ζ.re : ℂ) + ζ.im * I = ζ.re • (1 : ℂ) + ζ.im • I by simp, map_add, map_smul,
      map_smul, Complex.real_smul, Complex.real_smul]
  rw [hL]
  apply Complex.ext <;> simp <;> ring

/-- **A2.** Chain rule (13.3)/(13.4) for the `x`- and `y`-partials of a composition of
`ℝ`-differentiable maps, in terms of `genDz`/`genDzbar` of the partials of `g`. -/
theorem cr_a_fderiv_comp {g f : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g (f z))
    (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ (fun w => g (f w)) z 1 =
        genDz (fun w => fderiv ℝ g w 1) (fun w => fderiv ℝ g w I) (f z) * fderiv ℝ f z 1 +
          genDzbar (fun w => fderiv ℝ g w 1) (fun w => fderiv ℝ g w I) (f z) *
            conj (fderiv ℝ f z 1) ∧
      fderiv ℝ (fun w => g (f w)) z I =
        genDz (fun w => fderiv ℝ g w 1) (fun w => fderiv ℝ g w I) (f z) * fderiv ℝ f z I +
          genDzbar (fun w => fderiv ℝ g w 1) (fun w => fderiv ℝ g w I) (f z) *
            conj (fderiv ℝ f z I) := by
  rw [fderiv_fun_comp z hg hf]
  simp only [ContinuousLinearMap.comp_apply, genDz, genDzbar]
  exact ⟨cr_a_clm_apply (fderiv ℝ g (f z)) (fderiv ℝ f z 1),
    cr_a_clm_apply (fderiv ℝ g (f z)) (fderiv ℝ f z I)⟩

/-- **A3.** A `C¹` cutoff equal to `1` near the compact `C`, supported in the open `U ⊇ C`. -/
theorem cr_a_exists_cutoff {C U : Set ℂ} (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ ψ : ℂ → ℝ, ContDiff ℝ 1 ψ ∧ (∀ᶠ z in 𝓝ˢ C, ψ z = 1) ∧ tsupport ψ ⊆ U ∧
      HasCompactSupport ψ ∧ ∀ z, ψ z ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨L, hL, hCL, hLU⟩ := exists_compact_between hC hU hCU
  obtain ⟨f, hf1, hf0, hf01⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (modelWithCornersSelf ℝ ℂ) (n := ⊤) hC.isClosed hCL
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑f) := contMDiff_iff_contDiff.1 f.contMDiff
  have hsupp : Function.support (⇑f) ⊆ L := by
    intro x hx
    by_contra hxL
    exact hx (hf0 x hxL)
  have htsupp : tsupport (⇑f) ⊆ L := closure_minimal hsupp hL.isClosed
  refine ⟨⇑f, hsmooth.of_le (by simp), hf1, htsupp.trans hLU, ?_, hf01⟩
  exact hL.of_isClosed_subset (isClosed_tsupport _) htsupp

/-- **A4.** Gluing: a `C¹` cutoff supported in the open `U` times a map that is `C¹` on `U` is
`C¹` on every set (it vanishes off `tsupport ψ`). -/
theorem cr_a_contDiffOn_cutoff_mul {F : ℂ → ℂ} {ψ : ℂ → ℝ} {U D : Set ℂ} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) (hψ : ContDiff ℝ 1 ψ) (hsupp : tsupport ψ ⊆ U) :
    ContDiffOn ℝ 1 (fun z => (ψ z : ℂ) * F z) D := by
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  by_cases hxU : x ∈ U
  · refine ⟨U, hU, hxU, ?_⟩
    have hψC : ContDiffOn ℝ 1 (fun z => (ψ z : ℂ)) (D ∩ U) :=
      (Complex.ofRealCLM.contDiff.comp hψ).contDiffOn
    exact hψC.mul (hF.mono inter_subset_right)
  · refine ⟨(tsupport ψ)ᶜ, (isClosed_tsupport ψ).isOpen_compl, fun h => hxU (hsupp h), ?_⟩
    refine (contDiffOn_const (c := (0 : ℂ))).congr ?_
    intro z hz
    simp [image_eq_zero_of_notMem_tsupport hz.2]

/-- **A5.** Where the cutoff is `1` near `z`, the derivative of the product is that of `F`. -/
theorem cr_a_fderiv_cutoff_mul {F : ℂ → ℂ} {ψ : ℂ → ℝ} {z : ℂ} (hψ : ∀ᶠ w in 𝓝 z, ψ w = 1) :
    fderiv ℝ (fun w => (ψ w : ℂ) * F w) z = fderiv ℝ F z := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hψ] with w hw
  simp [hw]



/-! ### Lemma 13.1 track — helpers of piece D -/

/-- The generalized `∂_w` of a `C¹` map, built from its `x`- and `y`-partials. -/
def cr_d_Gz (g : ℂ → ℂ) : ℂ → ℂ :=
  genDz (fun w => fderiv ℝ g w 1) (fun w => fderiv ℝ g w I)

/-- The generalized `∂_w̄` of a `C¹` map, built from its `x`- and `y`-partials. -/
def cr_d_Gzb (g : ℂ → ℂ) : ℂ → ℂ :=
  genDzbar (fun w => fderiv ℝ g w 1) (fun w => fderiv ℝ g w I)

/-- **D1.** The chain-rule identities for the witnesses are pointwise algebra. -/
theorem cr_d_witness_algebra (f fx fy gx gy : ℂ → ℂ) (z : ℂ) :
    genDz (fun z => genDz gx gy (f z) * fx z + genDzbar gx gy (f z) * conj (fx z))
        (fun z => genDz gx gy (f z) * fy z + genDzbar gx gy (f z) * conj (fy z)) z =
      genDz gx gy (f z) * genDz fx fy z + genDzbar gx gy (f z) * conj (genDzbar fx fy z) ∧
    genDzbar (fun z => genDz gx gy (f z) * fx z + genDzbar gx gy (f z) * conj (fx z))
        (fun z => genDz gx gy (f z) * fy z + genDzbar gx gy (f z) * conj (fy z)) z =
      genDz gx gy (f z) * genDzbar fx fy z + genDzbar gx gy (f z) * conj (genDz fx fy z) := by
  simp only [genDz, genDzbar, map_add, map_mul, map_sub, map_div₀, Complex.conj_I, map_ofNat]
  constructor <;> ring

/-- **D2.** The transfer inequality followed by Hölder: for `h` a.e.-strongly measurable on `f '' C`,
`∫_C ‖h (f z)‖ ‖fx z‖ ≤ ‖h‖_{L^q(f '' C)} · ‖ |fix| + |fiy| ‖_{L^p(f '' C)}`, `q = p/(p-1)`. -/
theorem cr_d_transfer_holder {f fx fy fix fiy : ℂ → ℂ} {D D' : Set ℂ} {p : ℝ} (hp : 2 ≤ p)
    (hD : IsOpen D) (hD' : IsOpen D') (hf : IsHomeomorphOnto f D D')
    (hfd : HasGenPartials f fx fy D (ENNReal.ofReal p))
    (hfi : HasGenPartials (Function.invFunOn f D) fix fiy D' (ENNReal.ofReal p))
    {C : Set ℂ} (hC : IsCompact C) (hCD : C ⊆ D) {h : ℂ → ℂ}
    (hh : AEStronglyMeasurable h (volume.restrict (f '' C))) :
    (∫⁻ z in C, ‖h (f z)‖ₑ * ‖fx z‖ₑ) ≤
        eLpNorm h (ENNReal.ofReal (p / (p - 1))) (volume.restrict (f '' C)) *
          eLpNorm (fun w => ‖fix w‖ + ‖fiy w‖) (ENNReal.ofReal p) (volume.restrict (f '' C)) ∧
      (∫⁻ z in C, ‖h (f z)‖ₑ * ‖fy z‖ₑ) ≤
        eLpNorm h (ENNReal.ofReal (p / (p - 1))) (volume.restrict (f '' C)) *
          eLpNorm (fun w => ‖fix w‖ + ‖fiy w‖) (ENNReal.ofReal p) (volume.restrict (f '' C)) := by
  have hp1 : 1 < p := by linarith
  have hpq : (p / (p - 1)).HolderConjugate p := (Real.HolderConjugate.conjExponent hp1).symm
  have hqpos : 0 < p / (p - 1) := div_pos (by linarith) (by linarith)
  have hppos : 0 < p := by linarith
  have hsub : f '' C ⊆ D' := hf.2.2.1 ▸ image_mono hCD
  have hcpt : IsCompact (f '' C) := hC.image_of_continuousOn (hf.1.mono hCD)
  obtain ⟨hfix, hfiy⟩ := hfi.1 (f '' C) hsub hcpt
  have hS : AEMeasurable (fun w => ‖fix w‖ₑ + ‖fiy w‖ₑ) (volume.restrict (f '' C)) :=
    hfix.aestronglyMeasurable.enorm.add hfiy.aestronglyMeasurable.enorm
  have hpt : ∀ w, ‖(‖fix w‖ + ‖fiy w‖ : ℝ)‖ₑ = ‖fix w‖ₑ + ‖fiy w‖ₑ := by
    intro w
    rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
      ofReal_norm, ofReal_norm]
  have hholder : (∫⁻ w in f '' C, ‖h w‖ₑ * (‖fix w‖ₑ + ‖fiy w‖ₑ)) ≤
      eLpNorm h (ENNReal.ofReal (p / (p - 1))) (volume.restrict (f '' C)) *
        eLpNorm (fun w => ‖fix w‖ + ‖fiy w‖) (ENNReal.ofReal p) (volume.restrict (f '' C)) := by
    have key := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (f '' C)) hpq hh.enorm hS
    simp only [Pi.mul_apply] at key
    have hSm : AEStronglyMeasurable (fun w => ‖fix w‖ + ‖fiy w‖) (volume.restrict (f '' C)) :=
      hfix.aestronglyMeasurable.norm.add hfiy.aestronglyMeasurable.norm
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hqpos).ne' ENNReal.ofReal_ne_top hh,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hppos).ne' ENNReal.ofReal_ne_top hSm,
      ENNReal.toReal_ofReal hqpos.le, ENNReal.toReal_ofReal hppos.le]
    simp only [hpt]
    exact key
  obtain ⟨h1, h2⟩ := cr_c_transfer hp hD hD' hf hfd hfi hC hCD (h := fun w => ‖h w‖ₑ) hh.enorm
  exact ⟨h1.trans hholder, h2.trans hholder⟩

/-- **D3.** If `hₙ → 0` in `L^q(f '' C)` then `∫_C ‖hₙ (f z)‖ ‖fx z‖ → 0` (and with `fy`). -/
theorem cr_d_term3_tendsto {f fx fy fix fiy : ℂ → ℂ} {D D' : Set ℂ} {p : ℝ} (hp : 2 ≤ p)
    (hD : IsOpen D) (hD' : IsOpen D') (hf : IsHomeomorphOnto f D D')
    (hfd : HasGenPartials f fx fy D (ENNReal.ofReal p))
    (hfi : HasGenPartials (Function.invFunOn f D) fix fiy D' (ENNReal.ofReal p))
    {C : Set ℂ} (hC : IsCompact C) (hCD : C ⊆ D) {h : ℕ → ℂ → ℂ}
    (hh : ∀ n, AEStronglyMeasurable (h n) (volume.restrict (f '' C)))
    (hconv : Tendsto (fun n => eLpNorm (h n) (ENNReal.ofReal (p / (p - 1))) (volume.restrict (f '' C)))
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ z in C, ‖h n (f z)‖ₑ * ‖fx z‖ₑ) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫⁻ z in C, ‖h n (f z)‖ₑ * ‖fy z‖ₑ) atTop (𝓝 0) := by
  have hsub : f '' C ⊆ D' := by
    rw [← hf.2.2.1]
    exact fun w ⟨z, hz, hzw⟩ => ⟨z, hCD hz, hzw⟩
  have hfC : IsCompact (f '' C) := hC.image_of_continuousOn (hf.1.mono hCD)
  obtain ⟨hfix, hfiy⟩ := hfi.1 (f '' C) hsub hfC
  have hE : eLpNorm (fun w => ‖fix w‖ + ‖fiy w‖) (ENNReal.ofReal p)
      (volume.restrict (f '' C)) ≠ ⊤ :=
    (hfix.norm.add hfiy.norm).eLpNorm_ne_top
  have hlim : Tendsto (fun n =>
      eLpNorm (h n) (ENNReal.ofReal (p / (p - 1))) (volume.restrict (f '' C)) *
        eLpNorm (fun w => ‖fix w‖ + ‖fiy w‖) (ENNReal.ofReal p) (volume.restrict (f '' C)))
      atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const hconv (Or.inr hE)
    rwa [zero_mul] at this
  exact ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
      (fun n => (cr_d_transfer_holder hp hD hD' hf hfd hfi hC hCD (hh n)).1),
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
      (fun n => (cr_d_transfer_holder hp hD hD' hf hfd hfi hC hCD (hh n)).2)⟩

/-- Helper for D3': `‖(a - I b)/2‖ ≤ ‖a‖ + ‖b‖`. -/
theorem cr_d_d3_norm_sub_half_le (a b : ℂ) : ‖(a - I * b) / 2‖ ≤ ‖a‖ + ‖b‖ := by
  have h1 : ‖a - I * b‖ ≤ ‖a‖ + ‖b‖ := by
    calc ‖a - I * b‖ ≤ ‖a‖ + ‖I * b‖ := norm_sub_le _ _
      _ = ‖a‖ + ‖b‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  rw [norm_div, Complex.norm_two]
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  linarith

/-- Helper for D3': `‖(a + I b)/2‖ ≤ ‖a‖ + ‖b‖`. -/
theorem cr_d_d3_norm_add_half_le (a b : ℂ) : ‖(a + I * b) / 2‖ ≤ ‖a‖ + ‖b‖ := by
  have h1 : ‖a + I * b‖ ≤ ‖a‖ + ‖b‖ := by
    calc ‖a + I * b‖ ≤ ‖a‖ + ‖I * b‖ := norm_add_le _ _
      _ = ‖a‖ + ‖b‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  rw [norm_div, Complex.norm_two]
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  linarith

/-- **D3'.** The generalized Wirtinger derivatives of `C¹` approximants of `g` converge to
`genDz gx gy`, `genDzbar gx gy` in `L^q` on compacts of `G`, and each term is a.e.-strongly
measurable there. -/
theorem cr_d_genDz_approx_tendsto {gx gy : ℂ → ℂ} {G : Set ℂ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    (hG : IsOpen G)
    (hgL : ∀ K ⊆ G, IsCompact K → MemLp gx q (volume.restrict K) ∧ MemLp gy q (volume.restrict K))
    {gn : ℕ → ℂ → ℂ} (hgn : ∀ n, ContDiffOn ℝ 1 (gn n) G)
    (hconv : ∀ K ⊆ G, IsCompact K →
      Tendsto (fun n => eLpNorm (fun w => fderiv ℝ (gn n) w 1 - gx w) q (volume.restrict K))
          atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun w => fderiv ℝ (gn n) w I - gy w) q (volume.restrict K))
          atTop (𝓝 0))
    {K : Set ℂ} (hK : IsCompact K) (hKG : K ⊆ G) :
    (∀ n, AEStronglyMeasurable (fun w => cr_d_Gz (gn n) w - genDz gx gy w) (volume.restrict K)) ∧
      (∀ n, AEStronglyMeasurable (fun w => cr_d_Gzb (gn n) w - genDzbar gx gy w)
        (volume.restrict K)) ∧
      Tendsto (fun n => eLpNorm (fun w => cr_d_Gz (gn n) w - genDz gx gy w) q (volume.restrict K))
        atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun w => cr_d_Gzb (gn n) w - genDzbar gx gy w) q (volume.restrict K))
        atTop (𝓝 0) := by
  -- measurability of the partials of the approximants on `K`
  have hm1 : ∀ n, AEStronglyMeasurable (fun w => fderiv ℝ (gn n) w 1) (volume.restrict K) :=
    fun n =>
      ((((hgn n).continuousOn_fderiv_of_isOpen hG le_rfl).clm_apply
        (continuousOn_const (c := (1 : ℂ)))).mono hKG).aestronglyMeasurable
        hK.isClosed.measurableSet
  have hm2 : ∀ n, AEStronglyMeasurable (fun w => fderiv ℝ (gn n) w I) (volume.restrict K) :=
    fun n =>
      ((((hgn n).continuousOn_fderiv_of_isOpen hG le_rfl).clm_apply
        (continuousOn_const (c := I))).mono hKG).aestronglyMeasurable
        hK.isClosed.measurableSet
  obtain ⟨hgx, hgy⟩ := hgL K hKG hK
  have hd1 : ∀ n, AEStronglyMeasurable (fun w => fderiv ℝ (gn n) w 1 - gx w) (volume.restrict K) :=
    fun n => (hm1 n).sub hgx.aestronglyMeasurable
  have hd2 : ∀ n, AEStronglyMeasurable (fun w => fderiv ℝ (gn n) w I - gy w) (volume.restrict K) :=
    fun n => (hm2 n).sub hgy.aestronglyMeasurable
  -- pointwise identities
  have hpt1 : ∀ n w, cr_d_Gz (gn n) w - genDz gx gy w =
      ((fderiv ℝ (gn n) w 1 - gx w) - I * (fderiv ℝ (gn n) w I - gy w)) / 2 := by
    intro n w
    simp only [cr_d_Gz, genDz]
    ring
  have hpt2 : ∀ n w, cr_d_Gzb (gn n) w - genDzbar gx gy w =
      ((fderiv ℝ (gn n) w 1 - gx w) + I * (fderiv ℝ (gn n) w I - gy w)) / 2 := by
    intro n w
    simp only [cr_d_Gzb, genDzbar]
    ring
  -- measurability of the differences
  have hmeasA : ∀ n, AEStronglyMeasurable (fun w => cr_d_Gz (gn n) w - genDz gx gy w)
      (volume.restrict K) := fun n =>
    (((hd1 n).sub ((hd2 n).const_mul I)).div₀ aestronglyMeasurable_const).congr
      (Filter.Eventually.of_forall fun w => (hpt1 n w).symm)
  have hmeasB : ∀ n, AEStronglyMeasurable (fun w => cr_d_Gzb (gn n) w - genDzbar gx gy w)
      (volume.restrict K) := fun n =>
    (((hd1 n).add ((hd2 n).const_mul I)).div₀ aestronglyMeasurable_const).congr
      (Filter.Eventually.of_forall fun w => (hpt2 n w).symm)
  -- the sum of the two error norms tends to `0`
  obtain ⟨hc1, hc2⟩ := hconv K hKG hK
  have hsum : Tendsto (fun n =>
      eLpNorm (fun w => fderiv ℝ (gn n) w 1 - gx w) q (volume.restrict K) +
        eLpNorm (fun w => fderiv ℝ (gn n) w I - gy w) q (volume.restrict K)) atTop (𝓝 0) := by
    have := hc1.add hc2
    rwa [add_zero] at this
  -- the bounds
  have hboundA : ∀ n, eLpNorm (fun w => cr_d_Gz (gn n) w - genDz gx gy w) q (volume.restrict K) ≤
      eLpNorm (fun w => fderiv ℝ (gn n) w 1 - gx w) q (volume.restrict K) +
        eLpNorm (fun w => fderiv ℝ (gn n) w I - gy w) q (volume.restrict K) := by
    intro n
    have htri := eLpNorm_add_le (f := fun w => ‖fderiv ℝ (gn n) w 1 - gx w‖)
      (g := fun w => ‖fderiv ℝ (gn n) w I - gy w‖) (μ := volume.restrict K) hq
    rw [eLpNorm_norm _ (hd1 n), eLpNorm_norm _ (hd2 n)] at htri
    refine le_trans ?_ htri
    refine eLpNorm_mono_real (hmeasA n) fun w => ?_
    show ‖cr_d_Gz (gn n) w - genDz gx gy w‖ ≤
      ‖fderiv ℝ (gn n) w 1 - gx w‖ + ‖fderiv ℝ (gn n) w I - gy w‖
    rw [hpt1 n w]
    exact cr_d_d3_norm_sub_half_le _ _
  have hboundB : ∀ n, eLpNorm (fun w => cr_d_Gzb (gn n) w - genDzbar gx gy w) q
      (volume.restrict K) ≤
      eLpNorm (fun w => fderiv ℝ (gn n) w 1 - gx w) q (volume.restrict K) +
        eLpNorm (fun w => fderiv ℝ (gn n) w I - gy w) q (volume.restrict K) := by
    intro n
    have htri := eLpNorm_add_le (f := fun w => ‖fderiv ℝ (gn n) w 1 - gx w‖)
      (g := fun w => ‖fderiv ℝ (gn n) w I - gy w‖) (μ := volume.restrict K) hq
    rw [eLpNorm_norm _ (hd1 n), eLpNorm_norm _ (hd2 n)] at htri
    refine le_trans ?_ htri
    refine eLpNorm_mono_real (hmeasB n) fun w => ?_
    show ‖cr_d_Gzb (gn n) w - genDzbar gx gy w‖ ≤
      ‖fderiv ℝ (gn n) w 1 - gx w‖ + ‖fderiv ℝ (gn n) w I - gy w‖
    rw [hpt2 n w]
    exact cr_d_d3_norm_add_half_le _ _
  refine ⟨hmeasA, hmeasB, ?_, ?_⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le) hboundA
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le) hboundB

/-- **D4 helper.** `L¹` membership of `Gz (f z) * fz z + Gzb (f z) * conj (fz z)` from the a.e.-strong
measurability of the three factors and the finiteness of the two product integrals. -/
theorem cr_d_d4_memLp_of_bounds {f Gz Gzb fz : ℂ → ℂ} {μ : Measure ℂ}
    (hGz : AEStronglyMeasurable (fun z => Gz (f z)) μ)
    (hGzb : AEStronglyMeasurable (fun z => Gzb (f z)) μ)
    (hfz : AEStronglyMeasurable fz μ)
    (h1 : (∫⁻ z, ‖Gz (f z)‖ₑ * ‖fz z‖ₑ ∂μ) < ⊤)
    (h2 : (∫⁻ z, ‖Gzb (f z)‖ₑ * ‖fz z‖ₑ ∂μ) < ⊤) :
    MemLp (fun z => Gz (f z) * fz z + Gzb (f z) * conj (fz z)) 1 μ := by
  have hm : AEStronglyMeasurable (fun z => Gz (f z) * fz z + Gzb (f z) * conj (fz z)) μ :=
    (hGz.mul hfz).add (hGzb.mul (Complex.continuous_conj.comp_aestronglyMeasurable hfz))
  refine memLp_iff.mpr ?_
  rw [eLpNorm_one_eq_lintegral_enorm hm]
  calc (∫⁻ z, ‖Gz (f z) * fz z + Gzb (f z) * conj (fz z)‖ₑ ∂μ)
      ≤ ∫⁻ z, ‖Gz (f z)‖ₑ * ‖fz z‖ₑ + ‖Gzb (f z)‖ₑ * ‖fz z‖ₑ ∂μ := by
        refine lintegral_mono fun z => ?_
        calc ‖Gz (f z) * fz z + Gzb (f z) * conj (fz z)‖ₑ
            ≤ ‖Gz (f z) * fz z‖ₑ + ‖Gzb (f z) * conj (fz z)‖ₑ := enorm_add_le _ _
          _ = ‖Gz (f z)‖ₑ * ‖fz z‖ₑ + ‖Gzb (f z)‖ₑ * ‖fz z‖ₑ := by
            rw [enorm_mul, enorm_mul, RCLike.enorm_conj]
    _ = (∫⁻ z, ‖Gz (f z)‖ₑ * ‖fz z‖ₑ ∂μ) + ∫⁻ z, ‖Gzb (f z)‖ₑ * ‖fz z‖ₑ ∂μ :=
        lintegral_add_left' (hGz.enorm.mul hfz.enorm) _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨h1, h2⟩



/-- **D4 helper.** Pull-back of a.e.-strong measurability through `f` on a compact `C ⊆ D`
(via the strongly measurable representative and P4). -/
theorem cr_d_d4_aestronglyMeasurable_comp {f fix fiy : ℂ → ℂ} {D D' : Set ℂ} {p : ℝ} (hp : 2 ≤ p)
    (hD : IsOpen D) (hD' : IsOpen D') (hf : IsHomeomorphOnto f D D')
    (hfi : HasGenPartials (Function.invFunOn f D) fix fiy D' (ENNReal.ofReal p))
    {C : Set ℂ} (hC : IsCompact C) (hCD : C ⊆ D) {H : ℂ → ℂ}
    (hH : AEStronglyMeasurable H (volume.restrict (f '' C))) :
    AEStronglyMeasurable (fun z => H (f z)) (volume.restrict C) := by
  have hfm : AEMeasurable f (volume.restrict C) :=
    (hf.1.mono hCD).aemeasurable hC.isClosed.measurableSet
  have hae : ∀ᵐ z ∂(volume.restrict C), H (f z) = hH.mk H (f z) :=
    cr_p_ae_comp hD hD' hp hf hfi hC hCD (P := fun w => H w = hH.mk H w) hH.ae_eq_mk
  have hm : AEStronglyMeasurable (hH.mk H ∘ f) (volume.restrict C) :=
    hH.stronglyMeasurable_mk.aestronglyMeasurable.comp_aemeasurable hfm
  exact hm.congr (hae.mono fun z hz => hz.symm)

/-- **D4.** The witnesses are in `L¹` on every compact subset of `D`. -/
theorem cr_d_memLp_witness {f fx fy gx gy fix fiy : ℂ → ℂ} {D D' G : Set ℂ} {p : ℝ} (hp : 2 ≤ p)
    (hD : IsOpen D) (hD' : IsOpen D') (hf : IsHomeomorphOnto f D D')
    (hfd : HasGenPartials f fx fy D (ENNReal.ofReal p))
    (hfi : HasGenPartials (Function.invFunOn f D) fix fiy D' (ENNReal.ofReal p))
    (hDG : closure D' ⊆ G)
    (hgL : ∀ K ⊆ G, IsCompact K → MemLp gx (ENNReal.ofReal (p / (p - 1))) (volume.restrict K) ∧
      MemLp gy (ENNReal.ofReal (p / (p - 1))) (volume.restrict K))
    {C : Set ℂ} (hC : IsCompact C) (hCD : C ⊆ D) :
    MemLp (fun z => genDz gx gy (f z) * fx z + genDzbar gx gy (f z) * conj (fx z)) 1
        (volume.restrict C) ∧
      MemLp (fun z => genDz gx gy (f z) * fy z + genDzbar gx gy (f z) * conj (fy z)) 1
        (volume.restrict C) := by
  have hfC : f '' C ⊆ D' := by
    rw [← hf.2.2.1]
    exact Set.image_mono hCD
  have hsubG : f '' C ⊆ G := (hfC.trans subset_closure).trans hDG
  have hcpt : IsCompact (f '' C) := hC.image_of_continuousOn (hf.1.mono hCD)
  obtain ⟨hgx, hgy⟩ := hgL (f '' C) hsubG hcpt
  have hGzL : MemLp (genDz gx gy) (ENNReal.ofReal (p / (p - 1))) (volume.restrict (f '' C)) := by
    have : genDz gx gy = fun w => (2⁻¹ : ℂ) * (gx w - I * gy w) := by
      funext w
      simp only [genDz]
      ring
    rw [this]
    exact (hgx.sub (hgy.const_mul I)).const_mul _
  have hGzbL : MemLp (genDzbar gx gy) (ENNReal.ofReal (p / (p - 1)))
      (volume.restrict (f '' C)) := by
    have : genDzbar gx gy = fun w => (2⁻¹ : ℂ) * (gx w + I * gy w) := by
      funext w
      simp only [genDzbar]
      ring
    rw [this]
    exact (hgx.add (hgy.const_mul I)).const_mul _
  have hfin : eLpNorm (fun w => ‖fix w‖ + ‖fiy w‖) (ENNReal.ofReal p)
      (volume.restrict (f '' C)) < ⊤ := by
    obtain ⟨hfix, hfiy⟩ := hfi.1 (f '' C) hfC hcpt
    exact (hfix.norm.add hfiy.norm).eLpNorm_lt_top
  have hGzc := cr_d_d4_aestronglyMeasurable_comp hp hD hD' hf hfi hC hCD hGzL.aestronglyMeasurable
  have hGzbc := cr_d_d4_aestronglyMeasurable_comp hp hD hD' hf hfi hC hCD hGzbL.aestronglyMeasurable
  have hTz := cr_d_transfer_holder hp hD hD' hf hfd hfi hC hCD hGzL.aestronglyMeasurable
  have hTzb := cr_d_transfer_holder hp hD hD' hf hfd hfi hC hCD hGzbL.aestronglyMeasurable
  have hfx : AEStronglyMeasurable fx (volume.restrict C) :=
    (hfd.1 C hCD hC).1.aestronglyMeasurable
  have hfy : AEStronglyMeasurable fy (volume.restrict C) :=
    (hfd.1 C hCD hC).2.aestronglyMeasurable
  have hfinz := ENNReal.mul_lt_top hGzL.eLpNorm_lt_top hfin
  have hfinzb := ENNReal.mul_lt_top hGzbL.eLpNorm_lt_top hfin
  exact ⟨cr_d_d4_memLp_of_bounds hGzc hGzbc hfx (hTz.1.trans_lt hfinz) (hTzb.1.trans_lt hfinzb),
    cr_d_d4_memLp_of_bounds hGzc hGzbc hfy (hTz.2.trans_lt hfinz) (hTzb.2.trans_lt hfinzb)⟩

/-- Helper for D5a: an eventually-bounded factor times an `L^p`-small sequence has integral
tending to `0` on the compact `C` (via `L^p ⊆ L^1` on the finite measure). -/
theorem cr_d_d5ab_bounded_mul_tendsto {p : ℝ≥0∞} (hp : 1 ≤ p) {C : Set ℂ} (hC : IsCompact C)
    {a e : ℕ → ℂ → ℂ} {M : ℝ}
    (hbound : ∀ᶠ m in atTop, ∀ z ∈ C, ‖a m z‖ ≤ M)
    (he : ∀ m, AEStronglyMeasurable (e m) (volume.restrict C))
    (hconv : Tendsto (fun m => eLpNorm (e m) p (volume.restrict C)) atTop (𝓝 0)) :
    Tendsto (fun m => ∫⁻ z in C, ‖a m z‖ₑ * ‖e m z‖ₑ) atTop (𝓝 0) := by
  set c : ℝ≥0∞ := (volume.restrict C) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) with hc
  have hexp : 0 ≤ 1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal := by
    simp only [ENNReal.toReal_one, div_one]
    by_cases hpt : p = ⊤
    · subst hpt; simp
    · have h1 : (1 : ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono hpt hp
      exact sub_nonneg.2 (div_le_one_of_le₀ h1 (by linarith))
  have hc_ne : c ≠ ⊤ := by
    rw [hc, Measure.restrict_apply_univ]
    exact ENNReal.rpow_ne_top_of_nonneg hexp hC.measure_lt_top.ne
  have hlim : Tendsto (fun m => ENNReal.ofReal M * (eLpNorm (e m) p (volume.restrict C) * c))
      atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.mul_const hconv (Or.inr hc_ne)
    rw [zero_mul] at h1
    have h2 : Tendsto (fun m => ENNReal.ofReal M * (eLpNorm (e m) p (volume.restrict C) * c))
        atTop (𝓝 (ENNReal.ofReal M * 0)) :=
      ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at h2
    exact h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hbound] with m hm
  calc (∫⁻ z in C, ‖a m z‖ₑ * ‖e m z‖ₑ)
      ≤ ∫⁻ z in C, ENNReal.ofReal M * ‖e m z‖ₑ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hC.isClosed.measurableSet] with z hz
        refine mul_le_mul_left ?_ _
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hm z hz)
    _ = ENNReal.ofReal M * ∫⁻ z in C, ‖e m z‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal M * eLpNorm (e m) 1 (volume.restrict C) := by
        rw [eLpNorm_one_eq_lintegral_enorm (he m)]
    _ ≤ ENNReal.ofReal M * (eLpNorm (e m) p (volume.restrict C) * c) :=
        mul_le_mul_right (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp (he m)) _

/-- **D5a.** Error term (1): a bounded factor times the `L¹` error of the approximants' partials. -/
theorem cr_d_term1_tendsto {fx fy : ℂ → ℂ} {D : Set ℂ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hD : IsOpen D)
    {fm : ℕ → ℂ → ℂ} (hfm : ∀ m, ContDiffOn ℝ 1 (fm m) D)
    (hfL : ∀ C ⊆ D, IsCompact C → MemLp fx p (volume.restrict C) ∧ MemLp fy p (volume.restrict C))
    (hconv : ∀ C ⊆ D, IsCompact C →
      Tendsto (fun m => eLpNorm (fun z => fderiv ℝ (fm m) z 1 - fx z) p (volume.restrict C))
          atTop (𝓝 0) ∧
        Tendsto (fun m => eLpNorm (fun z => fderiv ℝ (fm m) z I - fy z) p (volume.restrict C))
          atTop (𝓝 0))
    {C K : Set ℂ} (hC : IsCompact C) (hCD : C ⊆ D) (hK : IsCompact K) {H : ℂ → ℂ}
    (hH : ContinuousOn H K) (hmaps : ∀ᶠ m in atTop, ∀ z ∈ C, fm m z ∈ K) :
    Tendsto (fun m => ∫⁻ z in C, ‖H (fm m z)‖ₑ * ‖fderiv ℝ (fm m) z 1 - fx z‖ₑ) atTop (𝓝 0) ∧
      Tendsto (fun m => ∫⁻ z in C, ‖H (fm m z)‖ₑ * ‖fderiv ℝ (fm m) z I - fy z‖ₑ) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hH
  have hbound : ∀ᶠ m in atTop, ∀ z ∈ C, ‖H (fm m z)‖ ≤ M :=
    hmaps.mono fun m hm z hz => hM _ (hm z hz)
  have hcont : ∀ m, ContinuousOn (fderiv ℝ (fm m)) D := fun m =>
    (hfm m).continuousOn_fderiv_of_isOpen hD le_rfl
  have he1 : ∀ m, AEStronglyMeasurable (fun z => fderiv ℝ (fm m) z 1 - fx z)
      (volume.restrict C) := fun m =>
    (((hcont m).clm_apply continuousOn_const).mono hCD).aestronglyMeasurable
      hC.isClosed.measurableSet |>.sub (hfL C hCD hC).1.aestronglyMeasurable
  have heI : ∀ m, AEStronglyMeasurable (fun z => fderiv ℝ (fm m) z I - fy z)
      (volume.restrict C) := fun m =>
    (((hcont m).clm_apply continuousOn_const).mono hCD).aestronglyMeasurable
      hC.isClosed.measurableSet |>.sub (hfL C hCD hC).2.aestronglyMeasurable
  exact ⟨cr_d_d5ab_bounded_mul_tendsto hp hC hbound he1 (hconv C hCD hC).1,
    cr_d_d5ab_bounded_mul_tendsto hp hC hbound heI (hconv C hCD hC).2⟩

/-- Helper for D5b: a uniformly-small factor times a fixed function with finite `L¹` norm has
integral tending to `0` on the compact `C`. -/
theorem cr_d_d5ab_small_mul_tendsto {C : Set ℂ} (hC : IsCompact C)
    {a : ℕ → ℂ → ℂ} {w : ℂ → ℂ} (hI : (∫⁻ z in C, ‖w z‖ₑ) ≠ ⊤)
    (hsmall : ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop, ∀ z ∈ C, ‖a m z‖ ≤ η) :
    Tendsto (fun m => ∫⁻ z in C, ‖a m z‖ₑ * ‖w z‖ₑ) atTop (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  obtain ⟨n, hn, hnε⟩ := ENNReal.exists_nnreal_pos_mul_lt hI hε.ne'
  filter_upwards [hsmall (n : ℝ) (NNReal.coe_pos.2 hn)] with m hm
  calc (∫⁻ z in C, ‖a m z‖ₑ * ‖w z‖ₑ)
      ≤ ∫⁻ z in C, (n : ℝ≥0∞) * ‖w z‖ₑ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hC.isClosed.measurableSet] with z hz
        refine mul_le_mul_left ?_ _
        rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal (hm z hz)
    _ = (n : ℝ≥0∞) * ∫⁻ z in C, ‖w z‖ₑ := lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ ≤ ε := hnε.le

/-- **D5b.** Error term (2): uniform continuity of the factor along the uniformly convergent
approximants, times the `L¹` norm of the partials. -/
theorem cr_d_term2_tendsto {f fx fy : ℂ → ℂ} {D : Set ℂ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hD : IsOpen D)
    {fm : ℕ → ℂ → ℂ}
    (hfL : ∀ C ⊆ D, IsCompact C → MemLp fx p (volume.restrict C) ∧ MemLp fy p (volume.restrict C))
    (hunif : TendstoLocallyUniformlyOn fm f atTop D)
    {C K : Set ℂ} (hC : IsCompact C) (hCD : C ⊆ D) (hK : IsCompact K) {H : ℂ → ℂ}
    (hH : ContinuousOn H K) (hfK : ∀ z ∈ C, f z ∈ K)
    (hmaps : ∀ᶠ m in atTop, ∀ z ∈ C, fm m z ∈ K) :
    Tendsto (fun m => ∫⁻ z in C, ‖H (fm m z) - H (f z)‖ₑ * ‖fx z‖ₑ) atTop (𝓝 0) ∧
      Tendsto (fun m => ∫⁻ z in C, ‖H (fm m z) - H (f z)‖ₑ * ‖fy z‖ₑ) atTop (𝓝 0) := by
  haveI : IsFiniteMeasure (volume.restrict C) := isFiniteMeasure_restrict.2 hC.measure_lt_top.ne
  have hIx : (∫⁻ z in C, ‖fx z‖ₑ) ≠ ⊤ := by
    have := ((hfL C hCD hC).1.mono_exponent hp).eLpNorm_lt_top
    rw [eLpNorm_one_eq_lintegral_enorm (hfL C hCD hC).1.aestronglyMeasurable] at this
    exact this.ne
  have hIy : (∫⁻ z in C, ‖fy z‖ₑ) ≠ ⊤ := by
    have := ((hfL C hCD hC).2.mono_exponent hp).eLpNorm_lt_top
    rw [eLpNorm_one_eq_lintegral_enorm (hfL C hCD hC).2.aestronglyMeasurable] at this
    exact this.ne
  have hU : TendstoUniformlyOn fm f atTop C :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).1 hunif C hCD hC
  have hsmall : ∀ η : ℝ, 0 < η → ∀ᶠ m in atTop, ∀ z ∈ C, ‖H (fm m z) - H (f z)‖ ≤ η := by
    intro η hη
    obtain ⟨δ, hδ, hδH⟩ :=
      Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hH) η hη
    filter_upwards [hmaps, Metric.tendstoUniformlyOn_iff.1 hU δ hδ] with m hm hd z hz
    rw [← dist_eq_norm]
    refine (hδH _ (hm z hz) _ (hfK z hz) ?_).le
    rw [dist_comm]
    exact hd z hz
  exact ⟨cr_d_d5ab_small_mul_tendsto hC hIx hsmall, cr_d_d5ab_small_mul_tendsto hC hIy hsmall⟩

/-- **D5.** The diagonal choice for the `k`-th approximant: a cutoff `ψ` equal to `1` near the
`k`-th compact `lemma92Exhaust D k` of the exhaustion of `D`, and an index `m` such that
`ψ · (gₖ ∘ fₘ)` is `C¹` on `D`, `gₖ` is differentiable along `fₘ`, `gₖ ∘ fₘ` is `1/(k+1)`-close to
`gₖ ∘ f`, and the two `m`-dependent error terms are `≤ 1/(k+1)` for `H ∈ {∂_w gₖ, ∂_w̄ gₖ}`. -/
theorem cr_d_exists_approx {f fx fy : ℂ → ℂ} {D D' G : Set ℂ} {p : ℝ} (hp : 2 ≤ p)
    (hD : IsOpen D) (hG : IsOpen G) (hf : IsHomeomorphOnto f D D')
    (hfd : HasGenPartials f fx fy D (ENNReal.ofReal p)) (hDG : closure D' ⊆ G)
    {gn : ℕ → ℂ → ℂ} (hgn : ∀ n, ContDiffOn ℝ 1 (gn n) G)
    {fm : ℕ → ℂ → ℂ} (hfm : ∀ m, ContDiffOn ℝ 1 (fm m) D)
    (hfunif : TendstoLocallyUniformlyOn fm f atTop D)
    (hfconv : ∀ C ⊆ D, IsCompact C →
      Tendsto (fun m => eLpNorm (fun z => fderiv ℝ (fm m) z 1 - fx z) (ENNReal.ofReal p)
          (volume.restrict C)) atTop (𝓝 0) ∧
        Tendsto (fun m => eLpNorm (fun z => fderiv ℝ (fm m) z I - fy z) (ENNReal.ofReal p)
          (volume.restrict C)) atTop (𝓝 0))
    (k : ℕ) :
    ∃ ψ : ℂ → ℝ, ∃ m : ℕ,
      ContDiffOn ℝ 1 (fun z => (ψ z : ℂ) * gn k (fm m z)) D ∧
        (∀ᶠ z in 𝓝ˢ (lemma92Exhaust D k), ψ z = 1) ∧
        (∀ z ∈ lemma92Exhaust D k, DifferentiableAt ℝ (gn k) (fm m z)) ∧
        (∀ z ∈ lemma92Exhaust D k, dist (gn k (f z)) (gn k (fm m z)) ≤ 1 / ((k : ℝ) + 1)) ∧
        ∀ H ∈ ({cr_d_Gz (gn k), cr_d_Gzb (gn k)} : Set (ℂ → ℂ)),
          (∫⁻ z in lemma92Exhaust D k, ‖H (fm m z)‖ₑ * ‖fderiv ℝ (fm m) z 1 - fx z‖ₑ) ≤
              ENNReal.ofReal (1 / ((k : ℝ) + 1)) ∧
            (∫⁻ z in lemma92Exhaust D k, ‖H (fm m z)‖ₑ * ‖fderiv ℝ (fm m) z I - fy z‖ₑ) ≤
              ENNReal.ofReal (1 / ((k : ℝ) + 1)) ∧
            (∫⁻ z in lemma92Exhaust D k, ‖H (fm m z) - H (f z)‖ₑ * ‖fx z‖ₑ) ≤
              ENNReal.ofReal (1 / ((k : ℝ) + 1)) ∧
            (∫⁻ z in lemma92Exhaust D k, ‖H (fm m z) - H (f z)‖ₑ * ‖fy z‖ₑ) ≤
              ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
  -- the `k`-th compact of the exhaustion
  have hCk : IsCompact (lemma92Exhaust D k) := isCompact_lemma92Exhaust D k
  have hCkD : lemma92Exhaust D k ⊆ D := lemma92Exhaust_subset D k
  have hk1 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  -- a compact neighbourhood `U` of `C_k` inside `D`
  obtain ⟨U, hUc, hCkU, hUD⟩ := exists_compact_between hCk hD hCkD
  have hCkU' : lemma92Exhaust D k ⊆ U := hCkU.trans interior_subset
  -- `f '' U` is compact and contained in `G`
  have hfU_compact : IsCompact (f '' U) := hUc.image_of_continuousOn (hf.1.mono hUD)
  have hfUG : f '' U ⊆ G := by
    intro w hw
    apply hDG
    apply subset_closure
    rw [← hf.2.2.1]
    exact image_mono hUD hw
  -- a compact neighbourhood `K` of `f '' U` inside `G`
  obtain ⟨K, hK, hfUK, hKG⟩ := exists_compact_between hfU_compact hG hfUG
  have hfUK' : ∀ z ∈ U, f z ∈ K := fun z hz => interior_subset (hfUK (mem_image_of_mem f hz))
  have hfK : ∀ z ∈ lemma92Exhaust D k, f z ∈ K := fun z hz => hfUK' z (hCkU' hz)
  -- the cutoff
  obtain ⟨ψ, hψ, hψ1, hsupp, -, -⟩ := cr_a_exists_cutoff hCk isOpen_interior hCkU
  -- uniform convergence of `fm` on `U` and on `C_k`
  have hunifU : TendstoUniformlyOn fm f atTop U :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).1 hfunif U hUD hUc
  have hunifC : TendstoUniformlyOn fm f atTop (lemma92Exhaust D k) := hunifU.mono hCkU'
  -- (a) eventually `fm m` maps `U` into `interior K`
  obtain ⟨δ, hδ, hthick⟩ := hfU_compact.exists_thickening_subset_open isOpen_interior hfUK
  have ha : ∀ᶠ m in atTop, ∀ z ∈ U, fm m z ∈ interior K := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunifU δ hδ] with m hm z hz
    refine hthick (mem_thickening_iff.2 ⟨f z, mem_image_of_mem f hz, ?_⟩)
    rw [dist_comm]
    exact hm z hz
  have hmapsC : ∀ᶠ m in atTop, ∀ z ∈ lemma92Exhaust D k, fm m z ∈ K := by
    filter_upwards [ha] with m hm z hz
    exact interior_subset (hm z (hCkU' hz))
  -- (b) uniform continuity of `gn k` on `K`
  have hgnK : ContinuousOn (gn k) K := (hgn k).continuousOn.mono hKG
  obtain ⟨η, hη, hηK⟩ :=
    Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hgnK) _ hk1
  have hb : ∀ᶠ m in atTop, ∀ z ∈ lemma92Exhaust D k,
      dist (gn k (f z)) (gn k (fm m z)) ≤ 1 / ((k : ℝ) + 1) := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunifC η hη, hmapsC] with m hm hm' z hz
    exact le_of_lt (hηK (f z) (hfK z hz) (fm m z) (hm' z hz) (hm z hz))
  -- (c) continuity of the Wirtinger derivatives of `gn k` on `K`
  have hfd_cont : ContinuousOn (fun w => fderiv ℝ (gn k) w) K :=
    ((hgn k).continuousOn_fderiv_of_isOpen hG le_rfl).mono hKG
  have h1c : ContinuousOn (fun w => fderiv ℝ (gn k) w 1) K :=
    hfd_cont.clm_apply continuousOn_const
  have hIc : ContinuousOn (fun w => fderiv ℝ (gn k) w I) K :=
    hfd_cont.clm_apply continuousOn_const
  have hGz_cont : ContinuousOn (cr_d_Gz (gn k)) K := by
    show ContinuousOn (fun w => (fderiv ℝ (gn k) w 1 - I * fderiv ℝ (gn k) w I) / 2) K
    exact (h1c.sub ((continuousOn_const (c := I)).mul hIc)).div_const 2
  have hGzb_cont : ContinuousOn (cr_d_Gzb (gn k)) K := by
    show ContinuousOn (fun w => (fderiv ℝ (gn k) w 1 + I * fderiv ℝ (gn k) w I) / 2) K
    exact (h1c.add ((continuousOn_const (c := I)).mul hIc)).div_const 2
  -- the eight error terms tend to zero
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 (by linarith)
  have hT1 := cr_d_term1_tendsto hp1 hD hfm hfd.1 hfconv hCk hCkD hK hGz_cont hmapsC
  have hT1' := cr_d_term1_tendsto hp1 hD hfm hfd.1 hfconv hCk hCkD hK hGzb_cont hmapsC
  have hT2 := cr_d_term2_tendsto hp1 hD hfd.1 hfunif hCk hCkD hK hGz_cont hfK hmapsC
  have hT2' := cr_d_term2_tendsto hp1 hD hfd.1 hfunif hCk hCkD hK hGzb_cont hfK hmapsC
  have hε : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / ((k : ℝ) + 1)) := ENNReal.ofReal_pos.2 hk1
  have e1 := ENNReal.tendsto_nhds_zero.1 hT1.1 _ hε
  have e2 := ENNReal.tendsto_nhds_zero.1 hT1.2 _ hε
  have e3 := ENNReal.tendsto_nhds_zero.1 hT1'.1 _ hε
  have e4 := ENNReal.tendsto_nhds_zero.1 hT1'.2 _ hε
  have e5 := ENNReal.tendsto_nhds_zero.1 hT2.1 _ hε
  have e6 := ENNReal.tendsto_nhds_zero.1 hT2.2 _ hε
  have e7 := ENNReal.tendsto_nhds_zero.1 hT2'.1 _ hε
  have e8 := ENNReal.tendsto_nhds_zero.1 hT2'.2 _ hε
  -- choose `m`
  obtain ⟨m, hma, hmb, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    (ha.and (hb.and (e1.and (e2.and (e3.and (e4.and (e5.and (e6.and (e7.and e8))))))))).exists
  have hmK : ∀ z ∈ U, fm m z ∈ K := fun z hz => interior_subset (hma z hz)
  refine ⟨ψ, m, ?_, hψ1, ?_, hmb, ?_⟩
  · -- `C¹` on `D`
    have hF : ContDiffOn ℝ 1 (fun z => gn k (fm m z)) (interior U) :=
      (hgn k).comp ((hfm m).mono (interior_subset.trans hUD))
        (fun z hz => hKG (hmK z (interior_subset hz)))
    exact cr_a_contDiffOn_cutoff_mul isOpen_interior hF hψ hsupp
  · -- differentiability of `gn k` along `fm m`
    intro z hz
    exact ((hgn k).differentiableOn one_ne_zero).differentiableAt
      (hG.mem_nhds (hKG (hmK z (hCkU' hz))))
  · -- the eight estimates
    intro H hH
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hH
    rcases hH with rfl | rfl
    · exact ⟨h1, h2, h5, h6⟩
    · exact ⟨h3, h4, h7, h8⟩

/-- **D6 helper.** `cr_d_Gz g` is (globally) measurable: `fderiv` is measurable. -/
theorem cr_d_d6_measurable_Gz (g : ℂ → ℂ) : Measurable (cr_d_Gz g) := by
  show Measurable (fun w => (fderiv ℝ g w 1 - I * fderiv ℝ g w I) / 2)
  exact ((measurable_fderiv_apply_const ℝ g 1).sub
    (measurable_const.mul (measurable_fderiv_apply_const ℝ g I))).div_const 2

/-- **D6 helper.** `cr_d_Gzb g` is (globally) measurable. -/
theorem cr_d_d6_measurable_Gzb (g : ℂ → ℂ) : Measurable (cr_d_Gzb g) := by
  show Measurable (fun w => (fderiv ℝ g w 1 + I * fderiv ℝ g w I) / 2)
  exact ((measurable_fderiv_apply_const ℝ g 1).add
    (measurable_const.mul (measurable_fderiv_apply_const ℝ g I))).div_const 2

/-- **D6 helper.** The pointwise six-term estimate behind the partials' convergence. -/
theorem cr_d_d6_pointwise (a a' A b b' B d x : ℂ) :
    ‖a * d + b * conj d - (A * x + B * conj x)‖ₑ ≤
      (‖a‖ₑ * ‖d - x‖ₑ + ‖a - a'‖ₑ * ‖x‖ₑ + ‖a' - A‖ₑ * ‖x‖ₑ) +
        (‖b‖ₑ * ‖d - x‖ₑ + ‖b - b'‖ₑ * ‖x‖ₑ + ‖b' - B‖ₑ * ‖x‖ₑ) := by
  have h : a * d + b * conj d - (A * x + B * conj x) =
      (a * (d - x) + (a - a') * x + (a' - A) * x) +
        (b * conj (d - x) + (b - b') * conj x + (b' - B) * conj x) := by
    simp only [map_sub]; ring
  have e1 : ‖b * conj (d - x)‖ₑ = ‖b‖ₑ * ‖d - x‖ₑ := by rw [enorm_mul, RCLike.enorm_conj]
  have e2 : ‖(b - b') * conj x‖ₑ = ‖b - b'‖ₑ * ‖x‖ₑ := by rw [enorm_mul, RCLike.enorm_conj]
  have e3 : ‖(b' - B) * conj x‖ₑ = ‖b' - B‖ₑ * ‖x‖ₑ := by rw [enorm_mul, RCLike.enorm_conj]
  rw [h]
  refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (enorm_add_le _ _).trans
      (add_le_add ((enorm_add_le _ _).trans (add_le_add ?_ ?_)) ?_) <;>
      simp only [enorm_mul, le_refl]
  · refine (enorm_add_le _ _).trans
      (add_le_add ((enorm_add_le _ _).trans (add_le_add e1.le e2.le)) e3.le)

/-- **D6 helper.** Splitting a sum of six `ℝ≥0∞`-valued integrands, five of them a.e.-measurable. -/
theorem cr_d_d6_lintegral_add6 {μ : Measure ℂ} {a1 a2 a3 b1 b2 b3 : ℂ → ℝ≥0∞}
    (h1 : AEMeasurable a1 μ) (h2 : AEMeasurable a2 μ) (h3 : AEMeasurable a3 μ)
    (h4 : AEMeasurable b1 μ) (h5 : AEMeasurable b2 μ) :
    ∫⁻ z, (a1 z + a2 z + a3 z) + (b1 z + b2 z + b3 z) ∂μ =
      ∫⁻ z, a1 z ∂μ + ∫⁻ z, a2 z ∂μ + ∫⁻ z, a3 z ∂μ + ∫⁻ z, b1 z ∂μ + ∫⁻ z, b2 z ∂μ +
        ∫⁻ z, b3 z ∂μ := by
  have h123 : AEMeasurable (fun z => a1 z + a2 z + a3 z) μ := (h1.add h2).add h3
  have h12 : AEMeasurable (fun z => a1 z + a2 z) μ := h1.add h2
  have h45 : AEMeasurable (fun z => b1 z + b2 z) μ := h4.add h5
  rw [lintegral_add_left' h123, lintegral_add_left' h12,
    lintegral_add_left' h1, lintegral_add_left' h45, lintegral_add_left' h4]
  ring

/-- **D6 helper.** Pull-back of a.e.-strong measurability on `f '' C` through `f` (P4 with a
measurable modification). -/
theorem cr_d_d6_aemeas_comp {f fix fiy : ℂ → ℂ} {D D' : Set ℂ} (hD : IsOpen D) (hD' : IsOpen D')
    {p : ℝ} (hp : 2 ≤ p) (hf : IsHomeomorphOnto f D D')
    (hfi : HasGenPartials (Function.invFunOn f D) fix fiy D' (ENNReal.ofReal p))
    {C : Set ℂ} (hC : IsCompact C) (hCD : C ⊆ D) {h : ℂ → ℂ}
    (hh : AEStronglyMeasurable h (volume.restrict (f '' C))) :
    AEStronglyMeasurable (fun z => h (f z)) (volume.restrict C) := by
  have hfm : AEMeasurable f (volume.restrict C) :=
    (hf.1.mono hCD).aemeasurable hC.isClosed.measurableSet
  have h1 : AEStronglyMeasurable (fun z => hh.mk h (f z)) (volume.restrict C) :=
    hh.stronglyMeasurable_mk.aestronglyMeasurable.comp_aemeasurable hfm
  refine h1.congr ?_
  have := cr_p_ae_comp hD hD' hp hf hfi hC hCD (P := fun w => h w = hh.mk h w) hh.ae_eq_mk
  filter_upwards [this] with z hz
  exact hz.symm

/-- **D6 helper.** Locally uniform convergence of the cut-off diagonal approximants to `g ∘ f`. -/
theorem cr_d_d6_unif {f g : ℂ → ℂ} {D D' G : Set ℂ} (hD : IsOpen D) (hG : IsOpen G)
    (hf : IsHomeomorphOnto f D D') (hDG : closure D' ⊆ G)
    {gn : ℕ → ℂ → ℂ} (hgunif : TendstoLocallyUniformlyOn gn g atTop G)
    {ψ : ℕ → ℂ → ℝ} {fm : ℕ → ℂ → ℂ} {m : ℕ → ℕ}
    (hψ1 : ∀ k, ∀ᶠ z in 𝓝ˢ (lemma92Exhaust D k), ψ k z = 1)
    (hdist : ∀ k, ∀ z ∈ lemma92Exhaust D k,
      dist (gn k (f z)) (gn k (fm (m k) z)) ≤ 1 / ((k : ℝ) + 1)) :
    TendstoLocallyUniformlyOn (fun k z => (ψ k z : ℂ) * gn k (fm (m k) z)) (g ∘ f) atTop D := by
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).2 fun C hCD hC => ?_
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  have hsubD' : f '' C ⊆ D' := by rw [← hf.2.2.1]; exact image_mono hCD
  have hsubG : f '' C ⊆ G := fun w hw => hDG (subset_closure (hsubD' hw))
  have hcpt : IsCompact (f '' C) := hC.image_of_continuousOn (hf.1.mono hCD)
  have h1 := Metric.tendstoUniformlyOn_iff.1
    ((tendstoLocallyUniformlyOn_iff_forall_isCompact hG).1 hgunif (f '' C) hsubG hcpt) (ε / 2)
    (by positivity)
  obtain ⟨δ, hδ, -, hev⟩ := lemma92_eventually hD hC hCD
  have h2 : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < ε / 2 :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds (by positivity))
  filter_upwards [h1, hev, h2] with k hk1 hk2 hk3
  intro z hz
  have hzk : z ∈ lemma92Exhaust D k := hk2.2 (self_subset_cthickening C hz)
  have hψ : ψ k z = 1 := (hψ1 k).self_of_nhdsSet z hzk
  calc dist ((g ∘ f) z) ((fun k z => (ψ k z : ℂ) * gn k (fm (m k) z)) k z)
      = dist (g (f z)) (gn k (fm (m k) z)) := by simp [hψ]
    _ ≤ dist (g (f z)) (gn k (f z)) + dist (gn k (f z)) (gn k (fm (m k) z)) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 :=
        add_lt_add (hk1 (f z) (mem_image_of_mem f hz)) ((hdist k z hzk).trans_lt hk3)
    _ = ε := by ring

/-- **D6 helper.** The abstract squeeze for one partial derivative: the six-term decomposition,
four `≤ 1/(k+1)` terms and two terms tending to `0` give `L¹` convergence on `C`. -/
theorem cr_d_d6_partial_tendsto {C : Set ℂ} (hC : IsCompact C) {f fζ Gz Gzb : ℂ → ℂ} (ζ : ℂ)
    {Fk fm' Gk Gbk : ℕ → ℂ → ℂ}
    (hderiv : ∀ᶠ k in atTop, ∀ z ∈ C, fderiv ℝ (Fk k) z ζ =
      Gk k (fm' k z) * fderiv ℝ (fm' k) z ζ + Gbk k (fm' k z) * conj (fderiv ℝ (fm' k) z ζ))
    (hb1 : ∀ᶠ k in atTop, (∫⁻ z in C, ‖Gk k (fm' k z)‖ₑ * ‖fderiv ℝ (fm' k) z ζ - fζ z‖ₑ) ≤
      ENNReal.ofReal (1 / ((k : ℝ) + 1)))
    (hb2 : ∀ᶠ k in atTop, (∫⁻ z in C, ‖Gbk k (fm' k z)‖ₑ * ‖fderiv ℝ (fm' k) z ζ - fζ z‖ₑ) ≤
      ENNReal.ofReal (1 / ((k : ℝ) + 1)))
    (hb3 : ∀ᶠ k in atTop, (∫⁻ z in C, ‖Gk k (fm' k z) - Gk k (f z)‖ₑ * ‖fζ z‖ₑ) ≤
      ENNReal.ofReal (1 / ((k : ℝ) + 1)))
    (hb4 : ∀ᶠ k in atTop, (∫⁻ z in C, ‖Gbk k (fm' k z) - Gbk k (f z)‖ₑ * ‖fζ z‖ₑ) ≤
      ENNReal.ofReal (1 / ((k : ℝ) + 1)))
    (hT1 : Tendsto (fun k => ∫⁻ z in C, ‖Gk k (f z) - Gz (f z)‖ₑ * ‖fζ z‖ₑ) atTop (𝓝 0))
    (hT2 : Tendsto (fun k => ∫⁻ z in C, ‖Gbk k (f z) - Gzb (f z)‖ₑ * ‖fζ z‖ₑ) atTop (𝓝 0))
    (hm1 : ∀ k, AEMeasurable (fun z => ‖Gk k (fm' k z)‖ₑ * ‖fderiv ℝ (fm' k) z ζ - fζ z‖ₑ)
      (volume.restrict C))
    (hm2 : ∀ k, AEMeasurable (fun z => ‖Gk k (fm' k z) - Gk k (f z)‖ₑ * ‖fζ z‖ₑ)
      (volume.restrict C))
    (hm3 : ∀ k, AEMeasurable (fun z => ‖Gk k (f z) - Gz (f z)‖ₑ * ‖fζ z‖ₑ) (volume.restrict C))
    (hm4 : ∀ k, AEMeasurable (fun z => ‖Gbk k (fm' k z)‖ₑ * ‖fderiv ℝ (fm' k) z ζ - fζ z‖ₑ)
      (volume.restrict C))
    (hm5 : ∀ k, AEMeasurable (fun z => ‖Gbk k (fm' k z) - Gbk k (f z)‖ₑ * ‖fζ z‖ₑ)
      (volume.restrict C))
    (hmeas : ∀ k, AEStronglyMeasurable
      (fun z => fderiv ℝ (Fk k) z ζ - (Gz (f z) * fζ z + Gzb (f z) * conj (fζ z)))
      (volume.restrict C)) :
    Tendsto (fun k => eLpNorm
      (fun z => fderiv ℝ (Fk k) z ζ - (Gz (f z) * fζ z + Gzb (f z) * conj (fζ z))) 1
      (volume.restrict C)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim : Tendsto (fun k : ℕ => 4 * ENNReal.ofReal (1 / ((k : ℝ) + 1)) +
      ((∫⁻ z in C, ‖Gk k (f z) - Gz (f z)‖ₑ * ‖fζ z‖ₑ) +
        ∫⁻ z in C, ‖Gbk k (f z) - Gzb (f z)‖ₑ * ‖fζ z‖ₑ)) atTop (𝓝 0) := by
    have h4 := ENNReal.Tendsto.const_mul h0 (Or.inr (by simp : (4 : ℝ≥0∞) ≠ ⊤))
    have := h4.add (hT1.add hT2)
    simp only [mul_zero, add_zero] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hderiv, hb1, hb2, hb3, hb4] with k hk1 hk2 hk3 hk4 hk5
  rw [eLpNorm_one_eq_lintegral_enorm (hmeas k)]
  calc (∫⁻ z in C, ‖fderiv ℝ (Fk k) z ζ - (Gz (f z) * fζ z + Gzb (f z) * conj (fζ z))‖ₑ)
      ≤ ∫⁻ z in C, (‖Gk k (fm' k z)‖ₑ * ‖fderiv ℝ (fm' k) z ζ - fζ z‖ₑ +
          ‖Gk k (fm' k z) - Gk k (f z)‖ₑ * ‖fζ z‖ₑ + ‖Gk k (f z) - Gz (f z)‖ₑ * ‖fζ z‖ₑ) +
          (‖Gbk k (fm' k z)‖ₑ * ‖fderiv ℝ (fm' k) z ζ - fζ z‖ₑ +
          ‖Gbk k (fm' k z) - Gbk k (f z)‖ₑ * ‖fζ z‖ₑ +
            ‖Gbk k (f z) - Gzb (f z)‖ₑ * ‖fζ z‖ₑ) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hC.isClosed.measurableSet] with z hz
        rw [hk1 z hz]
        exact cr_d_d6_pointwise _ _ _ _ _ _ _ _
    _ = _ := cr_d_d6_lintegral_add6 (hm1 k) (hm2 k) (hm3 k) (hm4 k) (hm5 k)
    _ ≤ ENNReal.ofReal (1 / ((k : ℝ) + 1)) + ENNReal.ofReal (1 / ((k : ℝ) + 1)) +
          (∫⁻ z in C, ‖Gk k (f z) - Gz (f z)‖ₑ * ‖fζ z‖ₑ) + ENNReal.ofReal (1 / ((k : ℝ) + 1)) +
          ENNReal.ofReal (1 / ((k : ℝ) + 1)) +
          ∫⁻ z in C, ‖Gbk k (f z) - Gzb (f z)‖ₑ * ‖fζ z‖ₑ :=
        add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hk2 hk4) le_rfl) hk3) hk5)
          le_rfl
    _ = _ := by ring

/-- **D6.** `g ∘ f` has `L¹` generalized partials `u, v`. -/
theorem cr_d_hasGenPartials {f g fx fy gx gy fix fiy : ℂ → ℂ} {D D' G : Set ℂ} {p : ℝ}
    (hp : 2 < p) (hD : IsOpen D) (hD' : IsOpen D') (hG : IsOpen G)
    (hf : IsHomeomorphOnto f D D') (hfd : HasGenPartials f fx fy D (ENNReal.ofReal p))
    (hfi : HasGenPartials (Function.invFunOn f D) fix fiy D' (ENNReal.ofReal p))
    (hDG : closure D' ⊆ G) (hg : HasGenPartials g gx gy G (ENNReal.ofReal (p / (p - 1)))) :
    HasGenPartials (g ∘ f)
      (fun z => genDz gx gy (f z) * fx z + genDzbar gx gy (f z) * conj (fx z))
      (fun z => genDz gx gy (f z) * fy z + genDzbar gx gy (f z) * conj (fy z)) D 1 := by
  have hp2 : 2 ≤ p := hp.le
  have hp1 : 1 < p := by linarith
  have hq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (p / (p - 1)) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by rw [le_div_iff₀ (by linarith)]; linarith)
  obtain ⟨hgL, gn, hgn, hgunif, hgconv⟩ := id hg
  obtain ⟨hfL, fm, hfm, hfunif, hfconv⟩ := id hfd
  choose ψ m hψm using cr_d_exists_approx hp2 hD hG hf hfd hDG hgn hfm hfunif hfconv
  refine ⟨fun C hCD hC => cr_d_memLp_witness hp2 hD hD' hf hfd hfi hDG hgL hC hCD,
    fun k z => (ψ k z : ℂ) * gn k (fm (m k) z), fun k => (hψm k).1,
    cr_d_d6_unif hD hG hf hDG hgunif (fun k => (hψm k).2.1) (fun k => (hψm k).2.2.2.1), ?_⟩
  intro C hCD hC
  have hcpt : IsCompact (f '' C) := hC.image_of_continuousOn (hf.1.mono hCD)
  have hsubD' : f '' C ⊆ D' := by rw [← hf.2.2.1]; exact image_mono hCD
  have hsubG : f '' C ⊆ G := fun w hw => hDG (subset_closure (hsubD' hw))
  obtain ⟨hmz, hmzb, hcz, hczb⟩ := cr_d_genDz_approx_tendsto hq hG hgL hgn hgconv hcpt hsubG
  have hT1 := cr_d_term3_tendsto hp2 hD hD' hf hfd hfi hC hCD
    (h := fun n w => cr_d_Gz (gn n) w - genDz gx gy w) hmz hcz
  have hT2 := cr_d_term3_tendsto hp2 hD hD' hf hfd hfi hC hCD
    (h := fun n w => cr_d_Gzb (gn n) w - genDzbar gx gy w) hmzb hczb
  obtain ⟨δ, hδ, -, hev⟩ := lemma92_eventually hD hC hCD
  have hCk : ∀ᶠ k : ℕ in atTop, C ⊆ lemma92Exhaust D k := by
    filter_upwards [hev] with k hk
    exact (self_subset_cthickening C).trans hk.2
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hfC : AEMeasurable f (volume.restrict C) := (hf.1.mono hCD).aemeasurable hCm
  have hfmC : ∀ k, AEMeasurable (fm (m k)) (volume.restrict C) := fun k =>
    ((hfm (m k)).continuousOn.mono hCD).aemeasurable hCm
  have hfxC : AEStronglyMeasurable fx (volume.restrict C) :=
    (hfL C hCD hC).1.aestronglyMeasurable
  have hfyC : AEStronglyMeasurable fy (volume.restrict C) :=
    (hfL C hCD hC).2.aestronglyMeasurable
  have hgxy := hgL (f '' C) hsubG hcpt
  have hGzC : AEStronglyMeasurable (fun z => genDz gx gy (f z)) (volume.restrict C) := by
    refine cr_d_d6_aemeas_comp hD hD' hp2 hf hfi hC hCD (h := genDz gx gy) ?_
    have : genDz gx gy = fun w => (2⁻¹ : ℂ) * (gx w - I * gy w) := by
      funext w
      simp only [genDz]
      ring
    rw [this]
    exact ((hgxy.1.aestronglyMeasurable.sub
      (hgxy.2.aestronglyMeasurable.const_mul I)).const_mul _)
  have hGzbC : AEStronglyMeasurable (fun z => genDzbar gx gy (f z)) (volume.restrict C) := by
    refine cr_d_d6_aemeas_comp hD hD' hp2 hf hfi hC hCD (h := genDzbar gx gy) ?_
    have : genDzbar gx gy = fun w => (2⁻¹ : ℂ) * (gx w + I * gy w) := by
      funext w
      simp only [genDzbar]
      ring
    rw [this]
    exact ((hgxy.1.aestronglyMeasurable.add
      (hgxy.2.aestronglyMeasurable.const_mul I)).const_mul _)
  have hFkm : ∀ (k : ℕ) (ζ : ℂ), AEStronglyMeasurable
      (fun z => fderiv ℝ (fun w => (ψ k w : ℂ) * gn k (fm (m k) w)) z ζ) (volume.restrict C) :=
    fun k ζ => (measurable_fderiv_apply_const ℝ _ ζ).aestronglyMeasurable
  have hmeasx : ∀ k, AEStronglyMeasurable (fun z =>
      fderiv ℝ (fun w => (ψ k w : ℂ) * gn k (fm (m k) w)) z 1 -
        (genDz gx gy (f z) * fx z + genDzbar gx gy (f z) * conj (fx z))) (volume.restrict C) :=
    fun k => (hFkm k 1).sub ((hGzC.mul hfxC).add
      (hGzbC.mul (Complex.continuous_conj.comp_aestronglyMeasurable hfxC)))
  have hmeasy : ∀ k, AEStronglyMeasurable (fun z =>
      fderiv ℝ (fun w => (ψ k w : ℂ) * gn k (fm (m k) w)) z I -
        (genDz gx gy (f z) * fy z + genDzbar gx gy (f z) * conj (fy z))) (volume.restrict C) :=
    fun k => (hFkm k I).sub ((hGzC.mul hfyC).add
      (hGzbC.mul (Complex.continuous_conj.comp_aestronglyMeasurable hfyC)))
  have hGzf : ∀ k, AEStronglyMeasurable (fun z => cr_d_Gz (gn k) (f z) - genDz gx gy (f z))
      (volume.restrict C) :=
    fun k => cr_d_d6_aemeas_comp hD hD' hp2 hf hfi hC hCD (hmz k)
  have hGzbf : ∀ k, AEStronglyMeasurable (fun z => cr_d_Gzb (gn k) (f z) - genDzbar gx gy (f z))
      (volume.restrict C) :=
    fun k => cr_d_d6_aemeas_comp hD hD' hp2 hf hfi hC hCD (hmzb k)
  have hderiv : ∀ᶠ k : ℕ in atTop, ∀ z ∈ C,
      fderiv ℝ (fun w => (ψ k w : ℂ) * gn k (fm (m k) w)) z 1 =
          cr_d_Gz (gn k) (fm (m k) z) * fderiv ℝ (fm (m k)) z 1 +
            cr_d_Gzb (gn k) (fm (m k) z) * conj (fderiv ℝ (fm (m k)) z 1) ∧
        fderiv ℝ (fun w => (ψ k w : ℂ) * gn k (fm (m k) w)) z I =
          cr_d_Gz (gn k) (fm (m k) z) * fderiv ℝ (fm (m k)) z I +
            cr_d_Gzb (gn k) (fm (m k) z) * conj (fderiv ℝ (fm (m k)) z I) := by
    filter_upwards [hCk] with k hk z hz
    have hzk : z ∈ lemma92Exhaust D k := hk hz
    rw [cr_a_fderiv_cutoff_mul (eventually_nhdsSet_iff_forall.1 (hψm k).2.1 z hzk)]
    exact cr_a_fderiv_comp ((hψm k).2.2.1 z hzk)
      ((hfm (m k)).differentiableOn_one.differentiableAt (hD.mem_nhds (hCD hz)))
  have hbz := fun k => (hψm k).2.2.2.2 (cr_d_Gz (gn k)) (by simp)
  have hbzb := fun k => (hψm k).2.2.2.2 (cr_d_Gzb (gn k)) (by simp)
  have hmGz := fun k => cr_d_d6_measurable_Gz (gn k)
  have hmGzb := fun k => cr_d_d6_measurable_Gzb (gn k)
  refine ⟨?_, ?_⟩
  · refine cr_d_d6_partial_tendsto hC 1
      (Fk := fun k z => (ψ k z : ℂ) * gn k (fm (m k) z)) (fm' := fun k => fm (m k))
      (Gk := fun k => cr_d_Gz (gn k)) (Gbk := fun k => cr_d_Gzb (gn k))
      (hderiv.mono fun k hk z hz => (hk z hz).1) ?_ ?_ ?_ ?_ hT1.1 hT2.1 ?_ ?_ ?_ ?_ ?_ hmeasx
    · filter_upwards [hCk] with k hk
      exact (lintegral_mono_set hk).trans (hbz k).1
    · filter_upwards [hCk] with k hk
      exact (lintegral_mono_set hk).trans (hbzb k).1
    · filter_upwards [hCk] with k hk
      exact (lintegral_mono_set hk).trans (hbz k).2.2.1
    · filter_upwards [hCk] with k hk
      exact (lintegral_mono_set hk).trans (hbzb k).2.2.1
    · intro k
      exact ((hmGz k).comp_aemeasurable' (hfmC k)).enorm.mul
        ((measurable_fderiv_apply_const ℝ (fm (m k)) 1).aemeasurable.sub hfxC.aemeasurable).enorm
    · intro k
      exact (((hmGz k).comp_aemeasurable' (hfmC k)).sub
        ((hmGz k).comp_aemeasurable' hfC)).enorm.mul hfxC.enorm
    · intro k
      exact (hGzf k).enorm.mul hfxC.enorm
    · intro k
      exact ((hmGzb k).comp_aemeasurable' (hfmC k)).enorm.mul
        ((measurable_fderiv_apply_const ℝ (fm (m k)) 1).aemeasurable.sub hfxC.aemeasurable).enorm
    · intro k
      exact (((hmGzb k).comp_aemeasurable' (hfmC k)).sub
        ((hmGzb k).comp_aemeasurable' hfC)).enorm.mul hfxC.enorm
  · refine cr_d_d6_partial_tendsto hC I
      (Fk := fun k z => (ψ k z : ℂ) * gn k (fm (m k) z)) (fm' := fun k => fm (m k))
      (Gk := fun k => cr_d_Gz (gn k)) (Gbk := fun k => cr_d_Gzb (gn k))
      (hderiv.mono fun k hk z hz => (hk z hz).2) ?_ ?_ ?_ ?_ hT1.2 hT2.2 ?_ ?_ ?_ ?_ ?_ hmeasy
    · filter_upwards [hCk] with k hk
      exact (lintegral_mono_set hk).trans (hbz k).2.1
    · filter_upwards [hCk] with k hk
      exact (lintegral_mono_set hk).trans (hbzb k).2.1
    · filter_upwards [hCk] with k hk
      exact (lintegral_mono_set hk).trans (hbz k).2.2.2
    · filter_upwards [hCk] with k hk
      exact (lintegral_mono_set hk).trans (hbzb k).2.2.2
    · intro k
      exact ((hmGz k).comp_aemeasurable' (hfmC k)).enorm.mul
        ((measurable_fderiv_apply_const ℝ (fm (m k)) I).aemeasurable.sub hfyC.aemeasurable).enorm
    · intro k
      exact (((hmGz k).comp_aemeasurable' (hfmC k)).sub
        ((hmGz k).comp_aemeasurable' hfC)).enorm.mul hfyC.enorm
    · intro k
      exact (hGzf k).enorm.mul hfyC.enorm
    · intro k
      exact ((hmGzb k).comp_aemeasurable' (hfmC k)).enorm.mul
        ((measurable_fderiv_apply_const ℝ (fm (m k)) I).aemeasurable.sub hfyC.aemeasurable).enorm
    · intro k
      exact (((hmGzb k).comp_aemeasurable' (hfmC k)).sub
        ((hmGzb k).comp_aemeasurable' hfC)).enorm.mul hfyC.enorm

/-- **Lemma 13.1** (chain rule (13.3), (13.4) for generalized derivatives).  Let `f` be a
homeomorphism of `D` onto `D'` such that `f` and `f⁻¹` have `L_p` generalized derivatives
(`p > 2`), and let `g` have `L_q` generalized derivatives on `G ⊇ D̄'`, `1/p + 1/q = 1`.
Then `g ∘ f` has `L₁` generalized derivatives in `D` and the chain rule holds a.e.

Proved (2026-09-22): the witnesses are `u = ∂_w g∘f · f_x + ∂_w̄ g∘f · conj f_x` and likewise `v`;
`g ∘ f` is approximated by cutoffs times `gₙ ∘ f_m` (`C¹` approximants of `g` and `f`, diagonal choice of
`m`), and the `L¹` convergence of the partials rests on the transfer inequality
`∫_C h(f z)|f_x| ≤ ∫_{f(C)} h (|∂_x f⁻¹| + |∂_y f⁻¹|)` (`cr_c_transfer`: change of variables for `f⁻¹` on
its set of differentiability, Lusin's property (N) for `f⁻¹` from the generalized
`ac_n_volume_image_null`, Menchoff) and Hölder. -/
theorem lemma13_1_chain_rule {f g fx fy gx gy fix fiy : ℂ → ℂ} {D D' G : Set ℂ} {p : ℝ}
    (hp : 2 < p) (hD : IsOpen D) (hG : IsOpen G) (hf : IsHomeomorphOnto f D D')
    (hfd : HasGenPartials f fx fy D (ENNReal.ofReal p))
    (hfi : HasGenPartials (Function.invFunOn f D) fix fiy D' (ENNReal.ofReal p))
    (hDG : closure D' ⊆ G) (hg : HasGenPartials g gx gy G (ENNReal.ofReal (p / (p - 1)))) :
    ∃ u v : ℂ → ℂ, HasGenPartials (g ∘ f) u v D 1 ∧
      ∀ᵐ z ∂(volume.restrict D),
        genDz u v z = genDz gx gy (f z) * genDz fx fy z + genDzbar gx gy (f z) * conj (genDzbar fx fy z) ∧
        genDzbar u v z = genDz gx gy (f z) * genDzbar fx fy z + genDzbar gx gy (f z) * conj (genDz fx fy z) := by
  have hD' : IsOpen D' := by
    rw [← hf.2.2.1]; exact isOpen_image_of_continuousOn_injOn hD hf.1 hf.2.1
  exact ⟨_, _, cr_d_hasGenPartials hp hD hD' hG hf hfd hfi hDG hg,
    Filter.Eventually.of_forall fun z => cr_d_witness_algebra f fx fy gx gy z⟩

/-! ### (13.5)–(13.7) track — helpers -/

/-- **E1 (algebra of (13.5)–(13.7)).** If `f` is `ℝ`-differentiable at `z`, `φ` at `f z`, and
`φ'(f z) ∘ f'(z) = id`, then the Wirtinger coefficients of `φ'(f z)` are those of `f'(z)⁻¹`:
`∂_w φ = conj (∂_z f) / J_f`, `∂_w̄ φ = −∂_z̄ f / J_f`, and `μ_φ (f z) = −μ_f z · ∂_z f / conj (∂_z f)`.
(From `B ∘ A = id` with `A ζ = a ζ + b ζ̄`, `B ζ = a' ζ + b' ζ̄`: `a' a + b' b̄ = 1`, `a' b + b' ā = 0`, hence
`a' J = ā`, `b' J = −b` with `J = |a|² − |b|² = det A ≠ 0` because `det B · det A = 1`.) -/
theorem ie_wirtinger_of_comp_eq_id {f φ : ℂ → ℂ} {z : ℂ} (hfz : DifferentiableAt ℝ f z)
    (hφ : DifferentiableAt ℝ φ (f z))
    (hBA : (fderiv ℝ φ (f z)).comp (fderiv ℝ f z) = ContinuousLinearMap.id ℝ ℂ) :
    dz φ (f z) = conj (dz f z) / jacobian f z ∧
      dzbar φ (f z) = -dzbar f z / jacobian f z ∧
      complexDilatation φ (f z) = -complexDilatation f z * (dz f z / conj (dz f z)) := by
  -- J ≠ 0 from det B · det A = 1
  have hdet : (fderiv ℝ φ (f z)).det * (fderiv ℝ f z).det = 1 := by
    have h' : ((fderiv ℝ φ (f z)).comp (fderiv ℝ f z)).det = (ContinuousLinearMap.id ℝ ℂ).det := by
      rw [hBA]
    rwa [ContinuousLinearMap.det, ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
      LinearMap.det_comp, ContinuousLinearMap.coe_id, LinearMap.det_id] at h'
  have hJne : jacobian f z ≠ 0 := by
    have h := right_ne_zero_of_mul_eq_one hdet
    rw [← det_fderiv_eq_jacobian hfz]
    exact h
  have hJc : (jacobian f z : ℂ) ≠ 0 := by exact_mod_cast hJne
  -- J as a complex expression
  have hJ' : dz f z * conj (dz f z) - dzbar f z * conj (dzbar f z) = (jacobian f z : ℂ) := by
    rw [Complex.mul_conj, Complex.mul_conj, jacobian, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq]
    push_cast; ring
  -- key identity from B ∘ A = id
  have hkey : ∀ ζ : ℂ,
      dz φ (f z) * (dz f z * ζ + dzbar f z * conj ζ) +
        dzbar φ (f z) * conj (dz f z * ζ + dzbar f z * conj ζ) = ζ := by
    intro ζ
    have h := congrArg (fun T : ℂ →L[ℝ] ℂ => T ζ) hBA
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
    rw [fderiv_eq_dz_dzbar hfz, fderiv_eq_dz_dzbar hφ] at h
    exact h
  set a := dz f z with ha_def
  set b := dzbar f z with hb_def
  set a' := dz φ (f z) with ha'_def
  set b' := dzbar φ (f z) with hb'_def
  have h1 : a' * (a + b) + b' * (conj a + conj b) = 1 := by
    have := hkey 1
    simp only [mul_one, map_one, map_add] at this
    linear_combination this
  have hI : a' * (a * I - b * I) + b' * (-(conj a * I) + conj b * I) = I := by
    have := hkey I
    simp only [map_add, map_mul, map_neg, Complex.conj_I, mul_neg, neg_neg] at this
    linear_combination this
  have e1 : a' * a + b' * conj b = 1 := by
    linear_combination (1 / 2 : ℂ) * h1 + (-I / 2) * hI +
      ((a' * a - a' * b - b' * conj a + b' * conj b - 1) / 2) * Complex.I_sq
  have e2 : a' * b + b' * conj a = 0 := by
    linear_combination (1 / 2 : ℂ) * h1 + (I / 2) * hI -
      ((a' * a - a' * b - b' * conj a + b' * conj b - 1) / 2) * Complex.I_sq
  have ha' : a' * (jacobian f z : ℂ) = conj a := by
    rw [← hJ']; linear_combination (conj a) * e1 - (conj b) * e2
  have hb' : b' * (jacobian f z : ℂ) = -b := by
    rw [← hJ']; linear_combination (-b) * e1 + a * e2
  have ha'e : a' = conj a / (jacobian f z : ℂ) := by rw [eq_div_iff hJc]; exact ha'
  have hb'e : b' = -b / (jacobian f z : ℂ) := by rw [eq_div_iff hJc]; exact hb'
  refine ⟨ha'e, hb'e, ?_⟩
  show b' / a' = -(b / a) * (a / conj a)
  rw [ha'e, hb'e]
  by_cases ha : a = 0
  · simp [ha]
  · have hca : conj a ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr ha
    field_simp

/-- (13.5)–(13.7): for a quasiconformal map `f`, almost everywhere
`(∂_w f⁻¹)∘f = conj(∂_z f)/J_f`, `(∂_{w̄} f⁻¹)∘f = -∂_{z̄} f/J_f`, and
`μ_{f⁻¹}(f(z)) = -μ_f(z) ∂_z f / conj(∂_z f)`.

Proved (2026-09-22): a.e. both `f` (Theorem 9.3) and `f⁻¹` (Theorem 9.3 for the `K`-q.c. inverse,
`thm7_2_inv`, transported through Lusin's property (N)) are differentiable at corresponding points; the chain
rule for `f⁻¹ ∘ f = id` makes the derivatives inverse to each other, and the formulas are the algebra of
inverting a real-linear map in Wirtinger form (`ie_wirtinger_of_comp_eq_id`). -/
theorem eq13_5_7_inverse {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) :
    ∀ᵐ z ∂(volume.restrict D),
      dz (Function.invFunOn f D) (f z) = conj (dz f z) / jacobian f z ∧
      dzbar (Function.invFunOn f D) (f z) = -dzbar f z / jacobian f z ∧
      complexDilatation (Function.invFunOn f D) (f z) =
        -complexDilatation f z * (dz f z / conj (dz f z)) := by
  set φ : ℂ → ℂ := Function.invFunOn f D with hφdef
  have hD : IsOpen D := hf.1
  have hφ : IsKQC φ (f '' D) K := thm7_2_inv hf
  have hD' : IsOpen (f '' D) := hφ.1
  have hleft : LeftInvOn φ f D := hf.2.2.1.2.1.leftInvOn_invFunOn
  -- Step 1: `f` is differentiable a.e. on `D`.
  have step1 : ∀ᵐ z ∂(volume.restrict D), DifferentiableAt ℝ f z := thm9_3_differentiable_ae hf
  -- Step 2: `φ` is differentiable at `f z` for a.e. `z ∈ D`.
  have step2 : ∀ᵐ z ∂(volume.restrict D), DifferentiableAt ℝ φ (f z) := by
    have hφae : ∀ᵐ w ∂(volume.restrict (f '' D)), DifferentiableAt ℝ φ w :=
      thm9_3_differentiable_ae hφ
    rw [ae_restrict_iff' hD'.measurableSet, ae_iff] at hφae
    set N : Set ℂ := {w | ¬ (w ∈ f '' D → DifferentiableAt ℝ φ w)} with hNdef
    have hNsub : N ⊆ f '' D := fun w hw => by
      by_contra h
      exact hw (fun h' => absurd h' h)
    have hφN : volume (φ '' N) = 0 := ac_n_volume_image_null_of_isKQC hφ hNsub hφae
    rw [ae_restrict_iff' hD.measurableSet, ae_iff]
    refine measure_mono_null ?_ hφN
    intro z hz
    simp only [Set.mem_setOf_eq, Classical.not_imp] at hz
    obtain ⟨hzD, hnd⟩ := hz
    refine ⟨f z, ?_, hleft hzD⟩
    simp only [hNdef, Set.mem_setOf_eq, Classical.not_imp]
    exact ⟨⟨z, hzD, rfl⟩, hnd⟩
  -- Step 3: chain rule at a.e. point, then the algebra of E1.
  filter_upwards [step1, step2, ae_restrict_mem hD.measurableSet] with z hfz hφz hzD
  have hid : φ ∘ f =ᶠ[𝓝 z] id :=
    Filter.eventually_of_mem (hD.mem_nhds hzD) fun w hw => hleft hw
  have h1 : HasFDerivAt (φ ∘ f) ((fderiv ℝ φ (f z)).comp (fderiv ℝ f z)) z :=
    hφz.hasFDerivAt.comp z hfz.hasFDerivAt
  have h2 : HasFDerivAt (φ ∘ f) (ContinuousLinearMap.id ℝ ℂ) z :=
    (hasFDerivAt_id z).congr_of_eventuallyEq hid
  have hBA : (fderiv ℝ φ (f z)).comp (fderiv ℝ f z) = ContinuousLinearMap.id ℝ ℂ :=
    h1.unique h2
  exact ie_wirtinger_of_comp_eq_id hfz hφz hBA

/-! ### Similarity-principle track — helpers of piece A -/


/-! ### Generic support/measure helpers -/

/-- Off the support, the derivative vanishes. -/
theorem sp_fderiv_eq_zero_of_notMem_tsupport {u : ℂ → ℂ} {z : ℂ} (hz : z ∉ tsupport u) (v : ℂ) :
    fderiv ℝ u z v = 0 := by
  have h : u =ᶠ[𝓝 z] fun _ => (0 : ℂ) :=
    Filter.eventuallyEq_of_mem ((isClosed_tsupport u).isOpen_compl.mem_nhds hz)
      fun w hw => image_eq_zero_of_notMem_tsupport hw
  rw [h.fderiv_eq]
  simp

/-- A directional derivative of a compactly supported function has compact support. -/
theorem sp_hasCompactSupport_fderiv {u : ℂ → ℂ} (hu : HasCompactSupport u) (v : ℂ) :
    HasCompactSupport (fun z => fderiv ℝ u z v) :=
  HasCompactSupport.intro hu.isCompact fun _ hx => sp_fderiv_eq_zero_of_notMem_tsupport hx v

/-- `tsupport` of a directional derivative is contained in that of the function. -/
theorem sp_tsupport_fderiv_subset {u : ℂ → ℂ} (v : ℂ) :
    tsupport (fun z => fderiv ℝ u z v) ⊆ tsupport u :=
  closure_minimal (fun z hz => by
    by_contra hzu
    exact hz (sp_fderiv_eq_zero_of_notMem_tsupport hzu v)) (isClosed_tsupport u)

/-- For an integrand supported in `S ⊆ D`, the integral over `D` is the integral over the plane. -/
theorem sp_setIntegral_eq_integral {h : ℂ → ℂ} {D S : Set ℂ} (hD : MeasurableSet D) (hSD : S ⊆ D)
    (h0 : ∀ z ∉ S, h z = 0) : ∫ z in D, h z = ∫ z, h z := by
  rw [setIntegral_eq_of_subset_of_ae_diff_eq_zero hD.nullMeasurableSet hSD
      (Eventually.of_forall fun z hz => h0 z hz.2),
    setIntegral_eq_integral_of_forall_compl_eq_zero h0]

/-! ### The Wirtinger bracket -/

/-- `β(u,v) = u_z̄ v_z − u_z v_z̄`, built from partial derivatives `(ux,uy)` of `u` and `(vx,vy)`
of `v`. -/
def sp_beta (ux uy vx vy : ℂ → ℂ) (z : ℂ) : ℂ :=
  genDzbar ux uy z * genDz vx vy z - genDz ux uy z * genDzbar vx vy z

/-- The bracket in terms of the real partial derivatives. -/
theorem sp_beta_eq (ux uy vx vy : ℂ → ℂ) (z : ℂ) :
    sp_beta ux uy vx vy z = I / 2 * (uy z * vx z - ux z * vy z) := by
  simp only [sp_beta, genDz, genDzbar]
  ring

/-- The bracket is a derivation in its first (differentiated) argument. -/
theorem sp_beta_mul {a b vx vy : ℂ → ℂ} {z : ℂ} (ha : DifferentiableAt ℝ a z)
    (hb : DifferentiableAt ℝ b z) :
    sp_beta (fun w => fderiv ℝ (fun t => a t * b t) w 1)
        (fun w => fderiv ℝ (fun t => a t * b t) w I) vx vy z =
      b z * sp_beta (fun w => fderiv ℝ a w 1) (fun w => fderiv ℝ a w I) vx vy z +
        a z * sp_beta (fun w => fderiv ℝ b w 1) (fun w => fderiv ℝ b w I) vx vy z := by
  simp only [sp_beta_eq, fderiv_fun_mul ha hb, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  ring

/-- Chain rule for the directional derivatives of `ψ ∘ h`. -/
theorem sp_psiX_comp {ψ h : ℂ → ℂ} {z : ℂ} (hψ : DifferentiableAt ℝ ψ (h z))
    (hh : DifferentiableAt ℝ h z) (v : ℂ) :
    fderiv ℝ (fun t => ψ (h t)) z v = fderiv ℝ ψ (h z) (fderiv ℝ h z v) := by
  rw [fderiv_fun_comp z hψ hh]
  rfl

/-- A `C²` cutoff equal to `1` near a compact set and supported in an open neighbourhood. -/
theorem sp_e_exists_cutoff {C U : Set ℂ} (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ 2 χ ∧ (∀ᶠ z in 𝓝ˢ C, χ z = 1) ∧ tsupport χ ⊆ U ∧
      HasCompactSupport χ ∧ ∀ z, χ z ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨L, hL, hCL, hLU⟩ := exists_compact_between hC hU hCU
  obtain ⟨F, hF1, hF0, hF01⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ ℂ) (n := ⊤) hC.isClosed hCL
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑F) := contMDiff_iff_contDiff.1 F.contMDiff
  have hsupp : Function.support (⇑F) ⊆ L := by
    intro x hx
    by_contra hxL
    exact hx (hF0 x hxL)
  have htsupp : tsupport (⇑F) ⊆ L := closure_minimal hsupp hL.isClosed
  exact ⟨⇑F, hsmooth.of_le (WithTop.coe_le_coe.2 le_top), hF1, htsupp.trans hLU,
    hL.of_isClosed_subset (isClosed_tsupport _) htsupp, hF01⟩

/-! ### Gluing and the integral of a derivative -/

/-- A `C^n` function supported in the open set `U` times a function that is `C^n` on `U` is
globally `C^n`. -/
theorem sp_contDiff_mul {F ψ : ℂ → ℂ} {U : Set ℂ} {n : WithTop ℕ∞} (hU : IsOpen U)
    (hF : ContDiffOn ℝ n F U) (hψ : ContDiff ℝ n ψ) (hsupp : tsupport ψ ⊆ U) :
    ContDiff ℝ n (fun z => ψ z * F z) := by
  rw [← contDiffOn_univ]
  apply contDiffOn_of_locally_contDiffOn
  intro x _
  by_cases hxU : x ∈ U
  · exact ⟨U, hU, hxU,
      (hψ.contDiffOn.mono inter_subset_right).mul (hF.mono inter_subset_right)⟩
  · refine ⟨(tsupport ψ)ᶜ, (isClosed_tsupport ψ).isOpen_compl, fun h => hxU (hsupp h), ?_⟩
    refine (contDiffOn_const (c := (0 : ℂ))).congr ?_
    intro z hz
    simp [image_eq_zero_of_notMem_tsupport hz.2]

/-- Helper: the integral of `∂_x w` along a full horizontal line of a big square vanishes,
because `w` is zero at both endpoints. -/
theorem sp_a_inner_x {w : ℂ → ℂ} (hw : ContDiff ℝ 1 w) {R : ℝ} (hR : 0 < R)
    (hw0 : ∀ z : ℂ, R ≤ |z.re| → w z = 0) (y : ℝ) :
    (∫ x in Ioo (-R) R, fderiv ℝ w ((x : ℂ) + (y : ℂ) * I) 1) = 0 := by
  have hcont1 : Continuous fun z => fderiv ℝ w z 1 :=
    (hw.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hline : Continuous fun t : ℝ => (t : ℂ) + (y : ℂ) * I := by fun_prop
  have hcomp : Continuous fun t : ℝ => fderiv ℝ w ((t : ℂ) + (y : ℂ) * I) 1 :=
    hcont1.comp hline
  have hderiv : ∀ x : ℝ, HasDerivAt (fun t : ℝ => w ((t : ℂ) + (y : ℂ) * I))
      (fderiv ℝ w ((x : ℂ) + (y : ℂ) * I) 1) x := fun x => by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) + (y : ℂ) * I) 1 x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).add_const ((y : ℂ) * I)
    exact (hw.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt x h1
  have hend : ∀ t : ℝ, R ≤ |t| → w ((t : ℂ) + (y : ℂ) * I) = 0 := fun t ht => by
    refine hw0 _ ?_
    have hre : ((t : ℂ) + (y : ℂ) * I).re = t := by simp
    rw [hre]
    exact ht
  have hRle : (-R : ℝ) ≤ R := by linarith
  have hFTC : (∫ t in (-R)..R, fderiv ℝ w ((t : ℂ) + (y : ℂ) * I) 1)
      = w ((R : ℂ) + (y : ℂ) * I) - w (((-R : ℝ) : ℂ) + (y : ℂ) * I) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
      (hcomp.intervalIntegrable _ _)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hRle, hFTC,
    hend R (by rw [abs_of_pos hR]), hend (-R) (by rw [abs_neg, abs_of_pos hR]), sub_zero]

/-- Helper: the integral of `∂_y w` along a full vertical line of a big square vanishes. -/
theorem sp_a_inner_y {w : ℂ → ℂ} (hw : ContDiff ℝ 1 w) {R : ℝ} (hR : 0 < R)
    (hw0 : ∀ z : ℂ, R ≤ |z.im| → w z = 0) (x : ℝ) :
    (∫ y in Ioo (-R) R, fderiv ℝ w ((x : ℂ) + (y : ℂ) * I) I) = 0 := by
  have hcontI : Continuous fun z => fderiv ℝ w z I :=
    (hw.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hline : Continuous fun t : ℝ => (x : ℂ) + (t : ℂ) * I := by fun_prop
  have hcomp : Continuous fun t : ℝ => fderiv ℝ w ((x : ℂ) + (t : ℂ) * I) I :=
    hcontI.comp hline
  have hderiv : ∀ y : ℝ, HasDerivAt (fun t : ℝ => w ((x : ℂ) + (t : ℂ) * I))
      (fderiv ℝ w ((x : ℂ) + (y : ℂ) * I) I) y := fun y => by
    have h1 : HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * I) I y := by
      simpa using (((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (x : ℂ)
    exact (hw.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt y h1
  have hend : ∀ t : ℝ, R ≤ |t| → w ((x : ℂ) + (t : ℂ) * I) = 0 := fun t ht => by
    refine hw0 _ ?_
    have him : ((x : ℂ) + (t : ℂ) * I).im = t := by simp
    rw [him]
    exact ht
  have hRle : (-R : ℝ) ≤ R := by linarith
  have hFTC : (∫ t in (-R)..R, fderiv ℝ w ((x : ℂ) + (t : ℂ) * I) I)
      = w ((x : ℂ) + (R : ℂ) * I) - w ((x : ℂ) + ((-R : ℝ) : ℂ) * I) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcomp.intervalIntegrable _ _)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hRle, hFTC,
    hend R (by rw [abs_of_pos hR]), hend (-R) (by rw [abs_neg, abs_of_pos hR]), sub_zero]

/-- The integral of a partial derivative of a `C¹` compactly supported function vanishes. -/
theorem sp_integral_fderiv_eq_zero {w : ℂ → ℂ} (hw : ContDiff ℝ 1 w) (hcw : HasCompactSupport w) :
    (∫ z, fderiv ℝ w z 1) = 0 ∧ (∫ z, fderiv ℝ w z I) = 0 := by
  obtain ⟨r, hr⟩ := hcw.isCompact.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨R, hR, hball⟩ : ∃ R : ℝ, 0 < R ∧ tsupport w ⊆ ball (0 : ℂ) R := by
    refine ⟨|r| + 1, by have := abs_nonneg r; linarith, fun z hz => ?_⟩
    have h1 := hr hz
    rw [mem_closedBall, dist_zero_right] at h1
    rw [mem_ball, dist_zero_right]
    have h2 := le_abs_self r
    linarith
  have hnorm : ∀ z ∈ tsupport w, ‖z‖ < R := by
    intro z hz
    have h := hball hz
    rwa [mem_ball, dist_zero_right] at h
  have hwre : ∀ z : ℂ, R ≤ |z.re| → w z = 0 := by
    intro z hz
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    exact absurd (hz.trans (Complex.abs_re_le_norm z)) (not_le.2 (hnorm z hmem))
  have hwim : ∀ z : ℂ, R ≤ |z.im| → w z = 0 := by
    intro z hz
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    exact absurd (hz.trans (Complex.abs_im_le_norm z)) (not_le.2 (hnorm z hmem))
  have hTsub : tsupport w ⊆ openRect (-R) R (-R) R := by
    intro z hz
    have h1 := hnorm z hz
    have h2 : |z.re| < R := lt_of_le_of_lt (Complex.abs_re_le_norm z) h1
    have h3 : |z.im| < R := lt_of_le_of_lt (Complex.abs_im_le_norm z) h1
    rw [abs_lt] at h2 h3
    exact ⟨h2.1, h2.2, h3.1, h3.2⟩
  have hcont1 : Continuous fun z => fderiv ℝ w z 1 :=
    (hw.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcontI : Continuous fun z => fderiv ℝ w z I :=
    (hw.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hio1 : IntegrableOn (fun z => fderiv ℝ w z 1) (openRect (-R) R (-R) R) :=
    (hcont1.integrable_of_hasCompactSupport (sp_hasCompactSupport_fderiv hcw 1)).integrableOn
  have hioI : IntegrableOn (fun z => fderiv ℝ w z I) (openRect (-R) R (-R) R) :=
    (hcontI.integrable_of_hasCompactSupport (sp_hasCompactSupport_fderiv hcw I)).integrableOn
  have key1 : (∫ z, fderiv ℝ w z 1) = ∫ z in openRect (-R) R (-R) R, fderiv ℝ w z 1 :=
    (sp_setIntegral_eq_integral (h := fun z => fderiv ℝ w z 1)
      (measurableSet_openRect (-R) R (-R) R) hTsub
      (fun z hz => sp_fderiv_eq_zero_of_notMem_tsupport hz 1)).symm
  have keyI : (∫ z, fderiv ℝ w z I) = ∫ z in openRect (-R) R (-R) R, fderiv ℝ w z I :=
    (sp_setIntegral_eq_integral (h := fun z => fderiv ℝ w z I)
      (measurableSet_openRect (-R) R (-R) R) hTsub
      (fun z hz => sp_fderiv_eq_zero_of_notMem_tsupport hz I)).symm
  have hzx : ∀ y : ℝ, (∫ x in Ioo (-R) R, fderiv ℝ w ((x : ℂ) + (y : ℂ) * I) 1) = 0 :=
    fun y => sp_a_inner_x hw hR hwre y
  have hzy : ∀ x : ℝ, (∫ y in Ioo (-R) R, fderiv ℝ w ((x : ℂ) + (y : ℂ) * I) I) = 0 :=
    fun x => sp_a_inner_y hw hR hwim x
  refine ⟨?_, ?_⟩
  · rw [key1, setIntegral_openRect_symm hio1]
    simp only [hzx, integral_zero]
  · rw [keyI, setIntegral_openRect hioI]
    simp only [hzy, integral_zero]

/-! ### Two limit lemmas -/

/-- Helper: a pointwise inequality on `K` between two a.e.-strongly measurable functions upgrades
to an a.e. inequality for `volume.restrict K`.  No measurability of `K` is needed: if the two
functions agree a.e. with measurable ones, the bad set meets `K` in a `volume.restrict K`-null
set, and `Measure.le_restrict_apply` propagates that to the whole bad set. -/
theorem sp_b_ae_restrict_le_of_forall_mem {K : Set ℂ} {F G : ℂ → ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict K))
    (hG : AEStronglyMeasurable G (volume.restrict K)) (h : ∀ z ∈ K, F z ≤ G z) :
    ∀ᵐ z ∂(volume.restrict K), F z ≤ G z := by
  obtain ⟨F', hF'm, hFF'⟩ := hF
  obtain ⟨G', hG'm, hGG'⟩ := hG
  have hSm : MeasurableSet {z : ℂ | G' z < F' z} :=
    measurableSet_lt hG'm.measurable hF'm.measurable
  have hFn : volume.restrict K {z : ℂ | ¬ F z = F' z} = 0 := ae_iff.1 hFF'
  have hGn : volume.restrict K {z : ℂ | ¬ G z = G' z} = 0 := ae_iff.1 hGG'
  have hsub : {z : ℂ | G' z < F' z} ∩ K ⊆
      {z : ℂ | ¬ F z = F' z} ∪ {z : ℂ | ¬ G z = G' z} := by
    rintro z ⟨hz1, hz2⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
    have hle := h z hz2
    rw [hcon.1, hcon.2] at hle
    exact absurd hle (not_le.2 hz1)
  have hnull : volume.restrict K ({z : ℂ | G' z < F' z} ∩ K) = 0 :=
    measure_mono_null hsub (measure_union_null hFn hGn)
  have hle1 : volume ({z : ℂ | G' z < F' z} ∩ K) ≤
      volume.restrict K ({z : ℂ | G' z < F' z} ∩ K) := by
    have h2 := Measure.le_restrict_apply (μ := (volume : Measure ℂ)) K
      ({z : ℂ | G' z < F' z} ∩ K)
    rwa [Set.inter_assoc, Set.inter_self] at h2
  have hvol : volume ({z : ℂ | G' z < F' z} ∩ K) = 0 :=
    le_antisymm (le_trans hle1 hnull.le) (by simp)
  have hzero : volume.restrict K {z : ℂ | G' z < F' z} = 0 := by
    rw [Measure.restrict_apply hSm]; exact hvol
  filter_upwards [hFF', hGG', compl_mem_ae_iff.2 hzero] with z e1 e2 e3
  rw [e1, e2]
  exact not_lt.1 e3

/-- Uniform convergence of the first factor against a fixed integrable second factor. -/
theorem sp_tendsto_integral_mul_of_uniform {K : Set ℂ} {a : ℕ → ℂ → ℂ} {a₀ b : ℂ → ℂ}
    (hb : IntegrableOn b K) (hai : ∀ n, IntegrableOn (fun z => a n z * b z) K)
    (ha₀i : IntegrableOn (fun z => a₀ z * b z) K)
    (hunif : TendstoUniformlyOn a a₀ atTop K) :
    Tendsto (fun n => ∫ z in K, a n z * b z) atTop (𝓝 (∫ z in K, a₀ z * b z)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = ∫ z in K, ‖b z‖ := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hCdef]; exact integral_nonneg fun z => norm_nonneg _
  have hC1 : C + 1 ≠ 0 := ne_of_gt (by linarith)
  obtain ⟨δ, hδdef⟩ : ∃ d : ℝ, d = ε / (C + 1) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδdef]; exact div_pos hε (by linarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hunif δ hδ0)
  refine ⟨N, fun n hn => ?_⟩
  have hpt : ∀ z ∈ K, ‖a n z * b z - a₀ z * b z‖ ≤ δ * ‖b z‖ := by
    intro z hz
    have h1 : ‖a n z - a₀ z‖ ≤ δ := by
      have h2 := hN n hn z hz
      rw [dist_comm, dist_eq_norm] at h2
      exact h2.le
    have h3 : a n z * b z - a₀ z * b z = (a n z - a₀ z) * b z := by ring
    rw [h3, norm_mul]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have hae : ∀ᵐ z ∂(volume.restrict K), ‖a n z * b z - a₀ z * b z‖ ≤ δ * ‖b z‖ :=
    sp_b_ae_restrict_le_of_forall_mem ((hai n).sub' ha₀i).aestronglyMeasurable.norm
      (hb.aestronglyMeasurable.norm.const_mul δ) hpt
  have hbound : ‖∫ z in K, (a n z * b z - a₀ z * b z)‖ ≤ ∫ z in K, δ * ‖b z‖ :=
    norm_integral_le_of_norm_le (hb.norm.const_mul δ) hae
  have hfin : (∫ z in K, δ * ‖b z‖) < ε := by
    rw [integral_const_mul, ← hCdef]
    have h4 : δ * (C + 1) = ε := by rw [hδdef]; field_simp
    nlinarith [hδ0, hC0]
  rw [dist_eq_norm, ← integral_sub (hai n) ha₀i]
  exact lt_of_le_of_lt hbound hfin

/-- `L²` convergence of the first factor against a fixed `L²` second factor. -/
theorem sp_tendsto_integral_mul_of_L2 {K : Set ℂ} {a : ℕ → ℂ → ℂ} {a₀ b : ℂ → ℂ}
    (ha : ∀ n, MemLp (a n) 2 (volume.restrict K)) (ha₀ : MemLp a₀ 2 (volume.restrict K))
    (hb : MemLp b 2 (volume.restrict K))
    (hlim : Tendsto (fun n => eLpNorm (fun z => a n z - a₀ z) 2 (volume.restrict K)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z in K, a n z * b z) atTop (𝓝 (∫ z in K, a₀ z * b z)) := by
  refine tendsto_integral_of_L1' (fun z => a₀ z * b z)
    (Eventually.of_forall fun n => (ha n).integrable_mul hb) ?_
  have key : ∀ n, eLpNorm ((fun z => a n z * b z) - fun z => a₀ z * b z) 1
      (volume.restrict K) ≤ eLpNorm (fun z => a n z - a₀ z) 2 (volume.restrict K) *
        eLpNorm b 2 (volume.restrict K) := by
    intro n
    have hfun : ((fun z => a n z * b z) - fun z => a₀ z * b z) =
        fun z => (a n z - a₀ z) * b z := by
      funext z; simp [sub_mul]
    rw [hfun]
    have h5 : eLpNorm (fun z => (a n z - a₀ z) * b z) 1 (volume.restrict K) ≤
        (1 : ℝ≥0) * eLpNorm (fun z => a n z - a₀ z) 2 (volume.restrict K) *
          eLpNorm b 2 (volume.restrict K) :=
      haveI : ENNReal.HolderTriple 2 2 1 := ⟨by rw [inv_one, ENNReal.inv_two_add_inv_two]⟩
      eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := 2) (q := 2) (r := 1)
        (μ := volume.restrict K) (f := fun z => a n z - a₀ z) (g := b)
        (fun x y => x * y) 1 (by fun_prop) ((ha n).sub ha₀).aestronglyMeasurable
        hb.aestronglyMeasurable (Eventually.of_forall fun z => by simp)
    rw [ENNReal.coe_one, one_mul] at h5
    exact h5
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using ENNReal.Tendsto.mul_const hlim (Or.inr hb.eLpNorm_ne_top))
    (fun n => by simp) key

/-! ### Integration by parts -/

/-- Auxiliary: a function integrable on a measurable set and vanishing off it is integrable. -/
theorem sp_ibp_integrable_of_support {f : ℂ → ℂ} {S : Set ℂ} (hSm : MeasurableSet S)
    (hint : IntegrableOn f S) (h0 : ∀ z ∉ S, f z = 0) : Integrable f := by
  have hfeq : f = S.indicator f := by
    funext z
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, h0 z hz]
  rw [hfeq]
  exact (integrable_indicator_iff hSm).2 hint

/-- Auxiliary: integration by parts in the single direction `e`, with the vanishing of the
integral of `∂_e` of a `C¹` compactly supported function supplied as `hzero`. -/
theorem sp_ibp_dir {v vw : ℂ → ℂ} {D : Set ℂ} {e : ℂ} (hD : IsOpen D)
    (hzero : ∀ w : ℂ → ℂ, ContDiff ℝ 1 w → HasCompactSupport w → (∫ z, fderiv ℝ w z e) = 0)
    {vn : ℕ → ℂ → ℂ} (hvnC1 : ∀ n, ContDiffOn ℝ 1 (vn n) D)
    (hvnU : TendstoLocallyUniformlyOn vn v atTop D)
    (hvw : ∀ C ⊆ D, IsCompact C → MemLp vw 2 (volume.restrict C))
    (hconv : ∀ C ⊆ D, IsCompact C →
      Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (vn n) z e - vw z) 2 (volume.restrict C))
        atTop (𝓝 0))
    {ψ : ℂ → ℂ} (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ D) :
    (∫ z in D, fderiv ℝ ψ z e * v z) = -∫ z in D, ψ z * vw z := by
  have hKc : IsCompact (tsupport ψ) := hcψ.isCompact
  have hKm : MeasurableSet (tsupport ψ) := hKc.isClosed.measurableSet
  have hDm : MeasurableSet D := hD.measurableSet
  haveI : IsFiniteMeasure (volume.restrict (tsupport ψ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
  have hψ0 : ∀ z ∉ tsupport ψ, ψ z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hdψ0 : ∀ z ∉ tsupport ψ, fderiv ℝ ψ z e = 0 := fun z hz =>
    sp_fderiv_eq_zero_of_notMem_tsupport hz e
  have hdψc : Continuous (fun z => fderiv ℝ ψ z e) :=
    ((hψ.fderiv_right (m := 0) (by norm_num)).continuous).clm_apply continuous_const
  have hdψcs : HasCompactSupport (fun z => fderiv ℝ ψ z e) := sp_hasCompactSupport_fderiv hcψ e
  have hdψs : tsupport (fun z => fderiv ℝ ψ z e) ⊆ D := (sp_tsupport_fderiv_subset e).trans hsψ
  have hvc : ContinuousOn v D :=
    hvnU.continuousOn (Filter.Frequently.of_forall fun n => (hvnC1 n).continuousOn)
  -- the integration-by-parts identity for the (genuinely `C¹`) approximants
  have key : ∀ n : ℕ, (∫ z in tsupport ψ, vn n z * fderiv ℝ ψ z e)
      = -∫ z in tsupport ψ, fderiv ℝ (vn n) z e * ψ z := by
    intro n
    have hFc : ContinuousOn (vn n) D := (hvnC1 n).continuousOn
    have hdFc : ContinuousOn (fun z => fderiv ℝ (vn n) z e) D :=
      ((hvnC1 n).continuousOn_fderiv_of_isOpen hD le_rfl).clm_apply continuousOn_const
    have hw1 : ContDiff ℝ 1 (fun z => ψ z * vn n z) := sp_contDiff_mul hD (hvnC1 n) hψ hsψ
    have hwcs : HasCompactSupport (fun z => ψ z * vn n z) :=
      HasCompactSupport.intro hKc fun x hx => by rw [hψ0 x hx, zero_mul]
    have hzeroW : (∫ z, fderiv ℝ (fun z => ψ z * vn n z) z e) = 0 := hzero _ hw1 hwcs
    -- the pointwise product rule, valid at every point of the plane
    have hprod : ∀ z : ℂ, fderiv ℝ (fun w => ψ w * vn n w) z e
        = fderiv ℝ ψ z e * vn n z + ψ z * fderiv ℝ (vn n) z e := by
      intro z
      by_cases hz : z ∈ D
      · have h1 : DifferentiableAt ℝ ψ z := hψ.differentiable one_ne_zero z
        have h2 : DifferentiableAt ℝ (vn n) z :=
          ((hvnC1 n).differentiableOn one_ne_zero).differentiableAt (hD.mem_nhds hz)
        have hmul := fderiv_mul (𝕜 := ℝ) (c := ψ) (d := vn n) h1 h2
        have hfun : (fun w => ψ w * vn n w) = ψ * vn n := rfl
        rw [hfun, hmul]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring
      · have hzK : z ∉ tsupport ψ := fun h => hz (hsψ h)
        have hev : (fun w => ψ w * vn n w) =ᶠ[𝓝 z] fun _ => (0 : ℂ) :=
          Filter.eventuallyEq_of_mem ((isClosed_tsupport ψ).isOpen_compl.mem_nhds hzK)
            fun w hw => by rw [hψ0 w hw, zero_mul]
        rw [hev.fderiv_eq]
        simp [hdψ0 z hzK, hψ0 z hzK]
    have hc1 : ContDiff ℝ 0 (fun z => fderiv ℝ ψ z e * vn n z) :=
      sp_contDiff_mul hD (contDiffOn_zero.2 hFc) (contDiff_zero.2 hdψc) hdψs
    have hc2 : ContDiff ℝ 0 (fun z => ψ z * fderiv ℝ (vn n) z e) :=
      sp_contDiff_mul hD (contDiffOn_zero.2 hdFc) (contDiff_zero.2 hψ.continuous) hsψ
    have hs1 : HasCompactSupport (fun z => fderiv ℝ ψ z e * vn n z) :=
      HasCompactSupport.intro hKc fun x hx => by rw [hdψ0 x hx, zero_mul]
    have hs2 : HasCompactSupport (fun z => ψ z * fderiv ℝ (vn n) z e) :=
      HasCompactSupport.intro hKc fun x hx => by rw [hψ0 x hx, zero_mul]
    have hi1 : Integrable (fun z => fderiv ℝ ψ z e * vn n z) :=
      (contDiff_zero.1 hc1).integrable_of_hasCompactSupport hs1
    have hi2 : Integrable (fun z => ψ z * fderiv ℝ (vn n) z e) :=
      (contDiff_zero.1 hc2).integrable_of_hasCompactSupport hs2
    have hsplit : (∫ z, fderiv ℝ ψ z e * vn n z) + (∫ z, ψ z * fderiv ℝ (vn n) z e) = 0 := by
      have h0 : (∫ z, (fderiv ℝ ψ z e * vn n z + ψ z * fderiv ℝ (vn n) z e))
          = ∫ z, fderiv ℝ (fun w => ψ w * vn n w) z e :=
        integral_congr_ae (Eventually.of_forall fun z => (hprod z).symm)
      rw [integral_add hi1 hi2] at h0
      rw [h0]
      exact hzeroW
    have e1 : (∫ z, fderiv ℝ ψ z e * vn n z) = ∫ z in tsupport ψ, fderiv ℝ ψ z e * vn n z :=
      (sp_setIntegral_eq_integral hKm (subset_refl _)
        (fun x hx => by rw [hdψ0 x hx, zero_mul])).symm
    have e2 : (∫ z, ψ z * fderiv ℝ (vn n) z e)
        = ∫ z in tsupport ψ, ψ z * fderiv ℝ (vn n) z e :=
      (sp_setIntegral_eq_integral hKm (subset_refl _)
        (fun x hx => by rw [hψ0 x hx, zero_mul])).symm
    rw [e1, e2] at hsplit
    have c1 : (∫ z in tsupport ψ, vn n z * fderiv ℝ ψ z e)
        = ∫ z in tsupport ψ, fderiv ℝ ψ z e * vn n z :=
      integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
    have c2 : (∫ z in tsupport ψ, fderiv ℝ (vn n) z e * ψ z)
        = ∫ z in tsupport ψ, ψ z * fderiv ℝ (vn n) z e :=
      integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
    rw [c1, c2]
    linear_combination hsplit
  -- the uniform limit of the first factor
  have hL1 : Tendsto (fun n => ∫ z in tsupport ψ, vn n z * fderiv ℝ ψ z e) atTop
      (𝓝 (∫ z in tsupport ψ, v z * fderiv ℝ ψ z e)) := by
    have hbint : IntegrableOn (fun z => fderiv ℝ ψ z e) (tsupport ψ) :=
      (hdψc.integrable_of_hasCompactSupport hdψcs).integrableOn
    have hai : ∀ n, IntegrableOn (fun z => vn n z * fderiv ℝ ψ z e) (tsupport ψ) := by
      intro n
      have hc1 : ContDiff ℝ 0 (fun z => fderiv ℝ ψ z e * vn n z) :=
        sp_contDiff_mul hD (contDiffOn_zero.2 (hvnC1 n).continuousOn)
          (contDiff_zero.2 hdψc) hdψs
      have hs1 : HasCompactSupport (fun z => fderiv ℝ ψ z e * vn n z) :=
        HasCompactSupport.intro hKc fun x hx => by rw [hdψ0 x hx, zero_mul]
      have hint : Integrable (fun z => fderiv ℝ ψ z e * vn n z) :=
        (contDiff_zero.1 hc1).integrable_of_hasCompactSupport hs1
      have heq : (fun z => vn n z * fderiv ℝ ψ z e)
          = fun z => fderiv ℝ ψ z e * vn n z := funext fun z => mul_comm _ _
      rw [heq]
      exact hint.integrableOn
    have hcont : ContinuousOn (fun z => v z * fderiv ℝ ψ z e) (tsupport ψ) :=
      (hvc.mono hsψ).mul hdψc.continuousOn
    exact sp_tendsto_integral_mul_of_uniform hbint hai (hcont.integrableOn_compact hKc)
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hD).1 hvnU _ hsψ hKc)
  -- the `L²` limit of the derivatives
  have hL2 : Tendsto (fun n => ∫ z in tsupport ψ, fderiv ℝ (vn n) z e * ψ z) atTop
      (𝓝 (∫ z in tsupport ψ, vw z * ψ z)) := by
    refine sp_tendsto_integral_mul_of_L2 (fun n => ?_) (hvw _ hsψ hKc) ?_ (hconv _ hsψ hKc)
    · have hdFc : ContinuousOn (fun z => fderiv ℝ (vn n) z e) (tsupport ψ) :=
        (((hvnC1 n).continuousOn_fderiv_of_isOpen hD le_rfl).clm_apply
          continuousOn_const).mono hsψ
      obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hdFc
      exact MemLp.of_bound (hdFc.aestronglyMeasurable hKm) C ((ae_restrict_mem hKm).mono hC)
    · exact (hψ.continuous.memLp_of_hasCompactSupport (μ := volume) hcψ).restrict _
  have hlim : Tendsto (fun n => ∫ z in tsupport ψ, vn n z * fderiv ℝ ψ z e) atTop
      (𝓝 (-∫ z in tsupport ψ, vw z * ψ z)) := by
    have hfun : (fun n => ∫ z in tsupport ψ, vn n z * fderiv ℝ ψ z e)
        = fun n => -∫ z in tsupport ψ, fderiv ℝ (vn n) z e * ψ z := funext key
    rw [hfun]
    exact hL2.neg
  have hKeq : (∫ z in tsupport ψ, v z * fderiv ℝ ψ z e)
      = -∫ z in tsupport ψ, vw z * ψ z := tendsto_nhds_unique hL1 hlim
  have d1 : (∫ z in D, fderiv ℝ ψ z e * v z) = ∫ z in tsupport ψ, v z * fderiv ℝ ψ z e := by
    have h0 : ∀ z ∉ tsupport ψ, fderiv ℝ ψ z e * v z = 0 := fun z hz => by
      rw [hdψ0 z hz, zero_mul]
    rw [sp_setIntegral_eq_integral hDm hsψ h0,
      ← sp_setIntegral_eq_integral hKm (subset_refl _) h0]
    exact integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
  have d2 : (∫ z in D, ψ z * vw z) = ∫ z in tsupport ψ, vw z * ψ z := by
    have h0 : ∀ z ∉ tsupport ψ, ψ z * vw z = 0 := fun z hz => by rw [hψ0 z hz, zero_mul]
    rw [sp_setIntegral_eq_integral hDm hsψ h0,
      ← sp_setIntegral_eq_integral hKm (subset_refl _) h0]
    exact integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
  rw [d1, d2, hKeq]

/-- Integration by parts against a `C¹` test function compactly supported in `D`. -/
theorem sp_ibp {v vx vy : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hv : HasGenPartials v vx vy D 2)
    {ψ : ℂ → ℂ} (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ D) :
    ((∫ z in D, fderiv ℝ ψ z 1 * v z) = -∫ z in D, ψ z * vx z) ∧
      ((∫ z in D, fderiv ℝ ψ z I * v z) = -∫ z in D, ψ z * vy z) := by
  obtain ⟨hloc, vn, hvnC1, hvnU, hvnConv⟩ := hv
  refine ⟨?_, ?_⟩
  · exact sp_ibp_dir hD (fun w hw hcw => (sp_integral_fderiv_eq_zero hw hcw).1) hvnC1 hvnU
      (fun C hC hCc => (hloc C hC hCc).1) (fun C hC hCc => (hvnConv C hC hCc).1) hψ hcψ hsψ
  · exact sp_ibp_dir hD (fun w hw hcw => (sp_integral_fderiv_eq_zero hw hcw).2) hvnC1 hvnU
      (fun C hC hCc => (hloc C hC hCc).2) (fun C hC hCc => (hvnConv C hC hCc).2) hψ hcψ hsψ

/-- The bracket of a `C²` function compactly supported in `D` against a function with `L²`
generalized partial derivatives integrates to zero. -/
theorem sp_integral_beta_eq_zero {v vx vy : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hv : HasGenPartials v vx vy D 2) {u : ℂ → ℂ} (hu : ContDiff ℝ 2 u) (hcu : HasCompactSupport u)
    (hsu : tsupport u ⊆ D) :
    ∫ z in D, sp_beta (fun w => fderiv ℝ u w 1) (fun w => fderiv ℝ u w I) vx vy z = 0 := by
  have hKc : IsCompact (tsupport u) := hcu.isCompact
  have hKm : MeasurableSet (tsupport u) := hKc.isClosed.measurableSet
  have hfd : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (m := 1) (by norm_num)
  have hux : ContDiff ℝ 1 (fun w => fderiv ℝ u w 1) := hfd.clm_apply contDiff_const
  have huy : ContDiff ℝ 1 (fun w => fderiv ℝ u w I) := hfd.clm_apply contDiff_const
  have hcux : HasCompactSupport (fun w => fderiv ℝ u w 1) := sp_hasCompactSupport_fderiv hcu 1
  have hcuy : HasCompactSupport (fun w => fderiv ℝ u w I) := sp_hasCompactSupport_fderiv hcu I
  have hsux : tsupport (fun w => fderiv ℝ u w 1) ⊆ D := (sp_tsupport_fderiv_subset 1).trans hsu
  have hsuy : tsupport (fun w => fderiv ℝ u w I) ⊆ D := (sp_tsupport_fderiv_subset I).trans hsu
  have hA := (sp_ibp hD hv huy hcuy hsuy).1
  have hB := (sp_ibp hD hv hux hcux hsux).2
  -- symmetry of the second derivatives
  have hsym : ∀ z : ℂ, fderiv ℝ (fun w => fderiv ℝ u w I) z 1
      = fderiv ℝ (fun w => fderiv ℝ u w 1) z I := by
    intro z
    have hsymm : IsSymmSndFDerivAt ℝ u z :=
      ContDiffAt.isSymmSndFDerivAt (n := 2) hu.contDiffAt (by simp)
    have h1 : DifferentiableAt ℝ (fderiv ℝ u) z := hfd.differentiable one_ne_zero z
    have e1 : fderiv ℝ (fun w => fderiv ℝ u w 1) z I = fderiv ℝ (fderiv ℝ u) z I 1 := by
      rw [fderiv_clm_apply h1 (differentiableAt_const _)]; simp
    have e2 : fderiv ℝ (fun w => fderiv ℝ u w I) z 1 = fderiv ℝ (fderiv ℝ u) z 1 I := by
      rw [fderiv_clm_apply h1 (differentiableAt_const _)]; simp
    rw [e1, e2]
    exact (hsymm I 1).symm
  have hEq : (∫ z in D, fderiv ℝ u z 1 * vy z) = ∫ z in D, fderiv ℝ u z I * vx z := by
    have h1 : (∫ z in D, fderiv ℝ (fun w => fderiv ℝ u w I) z 1 * v z)
        = -∫ z in D, fderiv ℝ u z I * vx z := hA
    have h2 : (∫ z in D, fderiv ℝ (fun w => fderiv ℝ u w 1) z I * v z)
        = -∫ z in D, fderiv ℝ u z 1 * vy z := hB
    have h3 : (∫ z in D, fderiv ℝ (fun w => fderiv ℝ u w I) z 1 * v z)
        = ∫ z in D, fderiv ℝ (fun w => fderiv ℝ u w 1) z I * v z :=
      integral_congr_ae (Eventually.of_forall fun z => by
        show fderiv ℝ (fun w => fderiv ℝ u w I) z 1 * v z
          = fderiv ℝ (fun w => fderiv ℝ u w 1) z I * v z
        rw [hsym z])
    rw [h3, h2] at h1
    exact neg_inj.1 h1
  -- integrability of the two products
  have hvxL : MemLp vx 2 (volume.restrict (tsupport u)) := (hv.1 (tsupport u) hsu hKc).1
  have hvyL : MemLp vy 2 (volume.restrict (tsupport u)) := (hv.1 (tsupport u) hsu hKc).2
  have huxL : MemLp (fun w => fderiv ℝ u w 1) 2 (volume.restrict (tsupport u)) :=
    (hux.continuous.memLp_of_hasCompactSupport (μ := volume) hcux).restrict _
  have huyL : MemLp (fun w => fderiv ℝ u w I) 2 (volume.restrict (tsupport u)) :=
    (huy.continuous.memLp_of_hasCompactSupport (μ := volume) hcuy).restrict _
  have hint1 : IntegrableOn (fun z => fderiv ℝ u z I * vx z) (tsupport u) :=
    huyL.integrable_mul hvxL
  have hint2 : IntegrableOn (fun z => fderiv ℝ u z 1 * vy z) (tsupport u) :=
    huxL.integrable_mul hvyL
  have hI1 : IntegrableOn (fun z => fderiv ℝ u z I * vx z) D :=
    (sp_ibp_integrable_of_support hKm hint1
      (fun z hz => by rw [sp_fderiv_eq_zero_of_notMem_tsupport hz I, zero_mul])).integrableOn
  have hI2 : IntegrableOn (fun z => fderiv ℝ u z 1 * vy z) D :=
    (sp_ibp_integrable_of_support hKm hint2
      (fun z hz => by rw [sp_fderiv_eq_zero_of_notMem_tsupport hz 1, zero_mul])).integrableOn
  have hstep : (∫ z in D, sp_beta (fun w => fderiv ℝ u w 1) (fun w => fderiv ℝ u w I) vx vy z)
      = ∫ z in D, I / 2 * (fderiv ℝ u z I * vx z - fderiv ℝ u z 1 * vy z) :=
    integral_congr_ae (Eventually.of_forall fun z =>
      sp_beta_eq (fun w => fderiv ℝ u w 1) (fun w => fderiv ℝ u w I) vx vy z)
  rw [hstep, integral_const_mul, integral_sub hI1 hI2, hEq]
  simp

/-! ### The mollifier approximants -/

/-- The mollifier approximants of §9 are `C²`. -/
theorem sp_m_contDiff2 {D : Set ℂ} {f : ℂ → ℂ} (hf : ContinuousOn f D) (n : ℕ) :
    ContDiff ℝ 2 (lemma92Approx D f n) :=
  (lemma92Bump n).hasCompactSupport_normed.contDiff_convolution_left (n := 2) _
    ((lemma92Bump n).contDiff_normed (μ := volume) (n := 2))
    (integrable_indicator_lemma92Exhaust hf n).locallyIntegrable

/-- The partial derivatives of the mollifier approximants converge in `L²` on compact subsets. -/
theorem sp_m_tendsto {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hf : IsACL f D)
    (hloc : ∀ C ⊆ D, IsCompact C → MemLp (partialX f) 2 (volume.restrict C) ∧
      MemLp (partialY f) 2 (volume.restrict C))
    {C : Set ℂ} (hCD : C ⊆ D) (hC : IsCompact C) :
    Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (lemma92Approx D f n) z 1 - partialX f z) 2
        (volume.restrict C)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (lemma92Approx D f n) z I - partialY f z) 2
        (volume.restrict C)) atTop (𝓝 0) := by
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hp' : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  obtain ⟨δ, hδ, hδD, hev⟩ := lemma92_eventually hD hC hCD
  have hKc : IsCompact (cthickening δ C) := hC.cthickening
  have hKD : cthickening δ C ⊆ D := (cthickening_mono (by linarith) C).trans hδD
  have hb : Tendsto (fun n => (lemma92Bump n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsq : ∀ z ∈ C, closedRect (z.re - δ) (z.re + δ) (z.im - δ) (z.im + δ) ⊆ D := by
    intro z hz w hw
    apply hδD
    refine mem_cthickening_of_dist_le w z (2 * δ) C hz ?_
    rw [dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    obtain ⟨h1, h2, h3, h4⟩ := hw
    rw [sub_re, sub_im]
    have e1 : |w.re - z.re| ≤ δ := abs_le.2 ⟨by linarith, by linarith⟩
    have e2 : |w.im - z.im| ≤ δ := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hsqint : ∀ z ∈ C,
      IntegrableOn (partialX f) (closedRect (z.re - δ) (z.re + δ) (z.im - δ) (z.im + δ)) ∧
      IntegrableOn (partialY f) (closedRect (z.re - δ) (z.re + δ) (z.im - δ) (z.im + δ)) := by
    intro z hz
    have hRc := isCompact_closedRect (z.re - δ) (z.re + δ) (z.im - δ) (z.im + δ)
    haveI : IsFiniteMeasure
        (volume.restrict (closedRect (z.re - δ) (z.re + δ) (z.im - δ) (z.im + δ))) :=
      isFiniteMeasure_restrict.2 hRc.measure_lt_top.ne
    exact ⟨(hloc _ (hsq z hz) hRc).1.integrable hp, (hloc _ (hsq z hz) hRc).2.integrable hp⟩
  have hψ : ∀ (n : ℕ) (z : ℂ), ContDiff ℝ 1 fun w => (lemma92Bump n).normed volume (z - w) :=
    fun n z => ((lemma92Bump n).contDiff_normed (μ := volume) (n := 1)).comp
      (contDiff_const.sub contDiff_id)
  refine ⟨?_, ?_⟩
  · have hG : MemLp ((cthickening δ C).indicator (partialX f)) 2 volume :=
      (memLp_indicator_iff_restrict hKc.measurableSet).2 (hloc _ hKD hKc).1
    refine (tendsto_eLpNorm_convolution_normed_sub hb hp hp' hG hC.measure_lt_top.ne).congr' ?_
    filter_upwards [hev] with n hn
    obtain ⟨hnδ, hnK⟩ := hn
    refine eLpNorm_congr_ae ((ae_restrict_iff' hC.measurableSet).2
      (Eventually.of_forall fun z hz => ?_))
    have hibp := lemma92_ibp_horizontal hf (a := z.re - δ) (b := z.re + δ) (c := z.im - δ)
      (d := z.im + δ) (by linarith) (by linarith) (hsq z hz) (hsqint z hz).1 (hψ n z)
      (fun y => lemma92Bump_normed_eq_zero (hnδ.le.trans (by
        calc δ = |(z - (((z.re - δ : ℝ) : ℂ) + (y : ℂ) * I)).re| := by simp [abs_of_pos hδ]
          _ ≤ _ := Complex.abs_re_le_norm _)))
      (fun y => lemma92Bump_normed_eq_zero (hnδ.le.trans (by
        calc δ = |(z - (((z.re + δ : ℝ) : ℂ) + (y : ℂ) * I)).re| := by simp [abs_of_pos hδ]
          _ ≤ _ := Complex.abs_re_le_norm _)))
    beta_reduce
    rw [indicator_of_mem (self_subset_cthickening C hz),
      ← fderiv_lemma92Approx_eq hf.1 hnδ hnK hz 1 hibp]
  · have hG : MemLp ((cthickening δ C).indicator (partialY f)) 2 volume :=
      (memLp_indicator_iff_restrict hKc.measurableSet).2 (hloc _ hKD hKc).2
    refine (tendsto_eLpNorm_convolution_normed_sub hb hp hp' hG hC.measure_lt_top.ne).congr' ?_
    filter_upwards [hev] with n hn
    obtain ⟨hnδ, hnK⟩ := hn
    refine eLpNorm_congr_ae ((ae_restrict_iff' hC.measurableSet).2
      (Eventually.of_forall fun z hz => ?_))
    have hibp := lemma92_ibp_vertical hf (a := z.re - δ) (b := z.re + δ) (c := z.im - δ)
      (d := z.im + δ) (by linarith) (by linarith) (hsq z hz) (hsqint z hz).2 (hψ n z)
      (fun x => lemma92Bump_normed_eq_zero (hnδ.le.trans (by
        calc δ = |(z - ((x : ℂ) + ((z.im - δ : ℝ) : ℂ) * I)).im| := by simp [abs_of_pos hδ]
          _ ≤ _ := Complex.abs_im_le_norm _)))
      (fun x => lemma92Bump_normed_eq_zero (hnδ.le.trans (by
        calc δ = |(z - ((x : ℂ) + ((z.im + δ : ℝ) : ℂ) * I)).im| := by simp [abs_of_pos hδ]
          _ ≤ _ := Complex.abs_im_le_norm _)))
    beta_reduce
    rw [indicator_of_mem (self_subset_cthickening C hz),
      ← fderiv_lemma92Approx_eq hf.1 hnδ hnK hz I hibp]

/-! ### The Weyl lemma -/

/-- Chain rule for a reflected real-valued mollifier `y ↦ (u (z - y) : ℂ)`. -/
theorem sp_w_fderiv_shift {u : ℂ → ℝ} (hu : Differentiable ℝ u) (z : ℂ) (y v : ℂ) :
    fderiv ℝ (fun y : ℂ => ((u (z - y) : ℝ) : ℂ)) y v = -((fderiv ℝ u (z - y) v : ℝ) : ℂ) := by
  have h1 : HasFDerivAt (fun y : ℂ => z - y) (-ContinuousLinearMap.id ℝ ℂ) y := by
    simpa using (hasFDerivAt_id y).const_sub z
  have h2 : HasFDerivAt (fun y : ℂ => ((u (z - y) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ u (z - y)).comp (-ContinuousLinearMap.id ℝ ℂ))) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y (((hu (z - y)).hasFDerivAt).comp y h1)
  rw [h2.fderiv]
  simp

/-- Assembling the two directional integral formulas into a `∂_w̄` identity. -/
theorem sp_w_dzbar_combine {G ψ Fn : ℂ → ℂ} {z : ℂ} (hGint : Integrable G volume)
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ)
    (hder : ∀ v : ℂ, fderiv ℝ Fn z v = -∫ y, fderiv ℝ ψ y v * G y) :
    dzbar Fn z = -∫ y, dzbar ψ y * G y := by
  have hcf : ∀ v : ℂ, Continuous fun y => fderiv ℝ ψ y v := fun v =>
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint : ∀ v : ℂ, Integrable (fun y => fderiv ℝ ψ y v * G y) volume := by
    intro v
    obtain ⟨c, hc⟩ := (hcf v).bounded_above_of_compact_support (sp_hasCompactSupport_fderiv hcψ v)
    exact hGint.bdd_mul (hcf v).aestronglyMeasurable (Eventually.of_forall hc)
  have hsum : ((∫ y, fderiv ℝ ψ y 1 * G y) + I * ∫ y, fderiv ℝ ψ y I * G y)
      = 2 * ∫ y, dzbar ψ y * G y := by
    rw [← integral_const_mul I fun y => fderiv ℝ ψ y I * G y,
      ← integral_add (hint 1) ((hint I).const_mul I), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show _ = 2 * ((fderiv ℝ ψ y 1 + I * fderiv ℝ ψ y I) / 2 * G y)
    ring
  show (fderiv ℝ Fn z 1 + I * fderiv ℝ Fn z I) / 2 = _
  rw [hder 1, hder I]
  linear_combination -hsum / 2

/-- Step 1 of Weyl's lemma: the `∂_w̄` of every mollifier approximant vanishes wherever the
mollification ball stays inside the exhaustion set. -/
theorem sp_w_dzbar_approx_eq_zero {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : ContinuousOn F U)
    (hweak : ∀ ψ : ℂ → ℂ, ContDiff ℝ 2 ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ w in U, F w * dzbar ψ w = 0) {n : ℕ} {z : ℂ}
    (hball : closedBall z (1 / ((n : ℝ) + 1)) ⊆ lemma92Exhaust U n) :
    dzbar (lemma92Approx U F n) z = 0 := by
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℂ → ℂ,
      ψ = fun y : ℂ => ((((lemma92Bump n).normed volume) (z - y) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hρD : Differentiable ℝ ((lemma92Bump n).normed volume) :=
    ((lemma92Bump n).contDiff_normed (μ := volume) (n := 1)).differentiable one_ne_zero
  have hshift : ContDiff ℝ 1 (fun y : ℂ => z - y) := contDiff_const.sub contDiff_id
  have hshift2 : ContDiff ℝ 2 (fun y : ℂ => z - y) := contDiff_const.sub contDiff_id
  have hψ1 : ContDiff ℝ 1 ψ := by
    rw [hψdef]
    exact (Complex.ofRealCLM.contDiff.comp
      ((lemma92Bump n).contDiff_normed (μ := volume) (n := 1))).comp hshift
  have hψ2 : ContDiff ℝ 2 ψ := by
    rw [hψdef]
    exact (Complex.ofRealCLM.contDiff.comp
      ((lemma92Bump n).contDiff_normed (μ := volume) (n := 2))).comp hshift2
  have hψder : ∀ y v : ℂ, fderiv ℝ ψ y v
      = -((fderiv ℝ ((lemma92Bump n).normed volume) (z - y) v : ℝ) : ℂ) := by
    rw [hψdef]
    exact sp_w_fderiv_shift hρD z
  have hψ0 : ∀ y ∉ closedBall z (1 / ((n : ℝ) + 1)), ψ y = 0 := by
    intro y hy
    rw [mem_closedBall, not_le] at hy
    have h : 1 / ((n : ℝ) + 1) ≤ ‖z - y‖ := by
      rw [norm_sub_rev, ← dist_eq_norm]
      exact hy.le
    rw [hψdef]
    simp [lemma92Bump_normed_eq_zero h]
  have hcψ : HasCompactSupport ψ := HasCompactSupport.intro (isCompact_closedBall z _) hψ0
  have hsψ : tsupport ψ ⊆ closedBall z (1 / ((n : ℝ) + 1)) := by
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    by_contra h
    exact hy (hψ0 y h)
  have hballU : closedBall z (1 / ((n : ℝ) + 1)) ⊆ U := hball.trans (lemma92Exhaust_subset U n)
  have hdz0 : ∀ y ∉ closedBall z (1 / ((n : ℝ) + 1)), dzbar ψ y = 0 := by
    intro y hy
    have h : y ∉ tsupport ψ := fun h' => hy (hsψ h')
    show (fderiv ℝ ψ y 1 + I * fderiv ℝ ψ y I) / 2 = 0
    rw [sp_fderiv_eq_zero_of_notMem_tsupport h 1, sp_fderiv_eq_zero_of_notMem_tsupport h I]
    ring
  have hw : ∫ y, F y * dzbar ψ y = 0 := by
    rw [← sp_setIntegral_eq_integral (h := fun y => F y * dzbar ψ y) hU.measurableSet hballU
      fun y hy => by rw [hdz0 y hy, mul_zero]]
    exact hweak ψ hψ2 hcψ (hsψ.trans hballU)
  have hderaux : ∀ v : ℂ, fderiv ℝ (lemma92Approx U F n) z v
      = ∫ y, fderiv ℝ ((lemma92Bump n).normed volume) (z - y) v •
          (lemma92Exhaust U n).indicator F y := by
    intro v
    rw [fderiv_lemma92Approx_apply hF n z v,
      ← integral_sub_left_eq_self
        (fun y => fderiv ℝ ((lemma92Bump n).normed volume) (z - y) v •
          (lemma92Exhaust U n).indicator F y) volume z]
    simp
  have hder : ∀ v : ℂ, fderiv ℝ (lemma92Approx U F n) z v
      = -∫ y, fderiv ℝ ψ y v * (lemma92Exhaust U n).indicator F y := by
    intro v
    rw [hderaux v, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show fderiv ℝ ((lemma92Bump n).normed volume) (z - y) v •
      (lemma92Exhaust U n).indicator F y = -(fderiv ℝ ψ y v * (lemma92Exhaust U n).indicator F y)
    rw [Complex.real_smul, ← neg_mul]
    congr 1
    rw [hψder y v, neg_neg]
  rw [sp_w_dzbar_combine (integrable_indicator_lemma92Exhaust hF n) hψ1 hcψ hder]
  have hGF : ∀ y, dzbar ψ y * (lemma92Exhaust U n).indicator F y = F y * dzbar ψ y := by
    intro y
    by_cases hy : y ∈ closedBall z (1 / ((n : ℝ) + 1))
    · rw [Set.indicator_of_mem (hball hy)]; ring
    · rw [hdz0 y hy]; ring
  rw [integral_congr_ae (Eventually.of_forall hGF), hw, neg_zero]

/-- **Weyl's lemma.**  A continuous function on an open set whose distributional `∂_w̄` vanishes is
holomorphic. -/
theorem sp_w_weyl {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : ContinuousOn F U)
    (hweak : ∀ ψ : ℂ → ℂ, ContDiff ℝ 2 ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ w in U, F w * dzbar ψ w = 0) :
    DifferentiableOn ℂ F U := by
  have step : ∀ C : Set ℂ, IsCompact C → C ⊆ U →
      ∀ᶠ n : ℕ in atTop, ∀ z ∈ C, DifferentiableAt ℂ (lemma92Approx U F n) z := by
    intro C hC hCU
    obtain ⟨δ, hδ, hδU, hev⟩ := lemma92_eventually hU hC hCU
    filter_upwards [hev] with n hn z hz
    obtain ⟨hnδ, hnK⟩ := hn
    have hball : closedBall z (1 / ((n : ℝ) + 1)) ⊆ lemma92Exhaust U n := fun y hy =>
      hnK (mem_cthickening_of_dist_le y z δ C hz ((mem_closedBall.1 hy).trans hnδ.le))
    exact cauchyRiemann_iff.2
      ⟨(contDiff_lemma92Approx hF n).differentiable one_ne_zero z,
        sp_w_dzbar_approx_eq_zero hU hF hweak hball⟩
  intro z₀ hz₀
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  have hCU : closedBall z₀ (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
  have hVC : ball z₀ (r / 2) ⊆ closedBall z₀ (r / 2) := ball_subset_closedBall
  have hdiff : ∀ᶠ n : ℕ in atTop, DifferentiableOn ℂ (lemma92Approx U F n) (ball z₀ (r / 2)) := by
    filter_upwards [step (closedBall z₀ (r / 2)) (isCompact_closedBall _ _) hCU] with n hn z hz
    exact (hn z (hVC hz)).differentiableWithinAt
  have hFV : DifferentiableOn ℂ F (ball z₀ (r / 2)) :=
    ((tendstoLocallyUniformlyOn_lemma92Approx hU hF).mono (hVC.trans hCU)).differentiableOn
      hdiff isOpen_ball
  exact (hFV.differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_self (by linarith)))).differentiableWithinAt

/-! ### Change of variables -/

/-- The first order expansion `g'(w) v = ∂_w g · v + ∂_{w̄} g · v̄`, with no differentiability
hypothesis: at a point of non-differentiability all three derivatives vanish. -/
theorem sp_c_fderiv_eq_dz_dzbar (g : ℂ → ℂ) (w v : ℂ) :
    fderiv ℝ g w v = dz g w * v + dzbar g w * conj v := by
  by_cases hg : DifferentiableAt ℝ g w
  · exact fderiv_eq_dz_dzbar hg v
  · have h0 : fderiv ℝ g w = 0 := fderiv_zero_of_not_differentiableAt hg
    simp [dz, dzbar, h0]

/-- At a point where the generalized partials are the genuine ones, the formal derivatives of `f`
are the generalized ones. -/
theorem sp_c_dz_eq_genDz {f fx fy : ℂ → ℂ} {z : ℂ} (hx : fderiv ℝ f z 1 = fx z)
    (hy : fderiv ℝ f z I = fy z) :
    dz f z = genDz fx fy z ∧ dzbar f z = genDzbar fx fy z := by
  constructor
  · simp only [dz, genDz, hx, hy]
  · simp only [dzbar, genDzbar, hx, hy]

/-- At such a point the Beltrami bound `‖μ‖ ≤ k < 1` forces `J_f ≥ 0`. -/
theorem sp_c_jacobian_nonneg {f fx fy μ : ℂ → ℂ} {z : ℂ} {k : ℝ} (hk : k < 1)
    (hx : fderiv ℝ f z 1 = fx z) (hy : fderiv ℝ f z I = fy z) (hzμ : ‖μ z‖ ≤ k)
    (hzb : genDzbar fx fy z = μ z * genDz fx fy z) : 0 ≤ jacobian f z := by
  obtain ⟨hdzv, hdzbv⟩ := sp_c_dz_eq_genDz hx hy
  have hnorm : ‖dzbar f z‖ = ‖μ z‖ * ‖dz f z‖ := by
    rw [hdzbv, hzb, norm_mul, ← hdzv]
  have h1 : ‖dzbar f z‖ ≤ ‖dz f z‖ := by
    rw [hnorm]
    nlinarith [norm_nonneg (dz f z), norm_nonneg (μ z), hk.le, hzμ]
  have h2 : (0 : ℝ) ≤ ‖dzbar f z‖ := norm_nonneg _
  show (0 : ℝ) ≤ ‖dz f z‖ ^ 2 - ‖dzbar f z‖ ^ 2
  nlinarith [h1, h2]

/-- Change of variables through an `L²` generalized homeomorphic solution. -/
theorem sp_c_change_of_variables {f fx fy μ : ℂ → ℂ} {D : Set ℂ} {k : ℝ} (hk : k < 1)
    (hD : IsOpen D) (hμ : ∀ᵐ z ∂(volume.restrict D), ‖μ z‖ ≤ k)
    (hfh : IsHomeomorphOnto f D (f '' D)) (hfd : HasGenPartials f fx fy D 2)
    (hfb : ∀ᵐ z ∂(volume.restrict D), genDzbar fx fy z = μ z * genDz fx fy z) (G : ℂ → ℂ) :
    ∫ w in f '' D, G w = ∫ z in D, (jacobian f z : ℂ) * G (f z) := by
  -- `f` is differentiable a.e. in `D`, with the generalized partials as its partials
  have hae := cr_p_differentiable_ae hD (by norm_num : (1 : ℝ≥0∞) ≤ 2) hfh hfd
  set S : Set ℂ := D ∩ {z | DifferentiableAt ℝ f z} with hSdef
  have hSD : S ⊆ D := inter_subset_left
  have hSm : MeasurableSet S := hD.measurableSet.inter (measurableSet_of_differentiableAt ℝ f)
  -- `S` has full measure in `D`
  have hnull : volume (D \ S) = 0 := by
    have h := (ae_restrict_iff' hD.measurableSet).1 hae
    rw [ae_iff] at h
    refine measure_mono_null (fun z hz => ?_) h
    rw [mem_setOf_eq]
    intro hcon
    refine hz.2 ?_
    rw [hSdef]
    exact ⟨hz.1, (hcon hz.1).1⟩
  have hSae : S =ᵐ[volume] D :=
    ae_eq_set.2 ⟨by rw [diff_eq_empty.2 hSD, measure_empty], hnull⟩
  -- Lusin's property (N) transports this to the images
  have hfd' : HasGenPartials f fx fy D (ENNReal.ofReal 2) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact hfd
  have himg_null : volume (f '' D \ f '' S) = 0 :=
    measure_mono_null (Set.subset_image_diff f D S)
      (cr_p_volume_image_null hD (le_refl (2 : ℝ)) hfh hfd' diff_subset hnull)
  have himgae : f '' S =ᵐ[volume] f '' D :=
    ae_eq_set.2 ⟨by rw [diff_eq_empty.2 (image_mono hSD), measure_empty], himg_null⟩
  -- the two integrands agree a.e. on `S`
  have hkey : ∀ᵐ z ∂volume, z ∈ S →
      |(fderiv ℝ f z).det| • G (f z) = (jacobian f z : ℂ) * G (f z) := by
    have h1 : ∀ᵐ z ∂(volume.restrict D),
        |(fderiv ℝ f z).det| • G (f z) = (jacobian f z : ℂ) * G (f z) := by
      filter_upwards [hae, hμ, hfb] with z hz hzμ hzb
      obtain ⟨hd, hx, hy⟩ := hz
      have hdet : (fderiv ℝ f z).det = jacobian f z := det_fderiv_eq_jacobian hd
      rw [hdet, abs_of_nonneg (sp_c_jacobian_nonneg hk hx hy hzμ hzb), Complex.real_smul]
    filter_upwards [(ae_restrict_iff' hD.measurableSet).1 h1] with z hz hzS
    exact hz (hSD hzS)
  calc ∫ w in f '' D, G w
      = ∫ w in f '' S, G w := (setIntegral_congr_set himgae).symm
    _ = ∫ z in S, |(fderiv ℝ f z).det| • G (f z) :=
        integral_image_eq_integral_abs_det_fderiv_smul volume hSm
          (fun z hz => hz.2.hasFDerivAt.hasFDerivWithinAt) (hfh.2.1.mono hSD) G
    _ = ∫ z in S, (jacobian f z : ℂ) * G (f z) := setIntegral_congr_ae hSm hkey
    _ = ∫ z in D, (jacobian f z : ℂ) * G (f z) := setIntegral_congr_set hSae

/-- The chain rule in bracket form: `∂_w̄ψ(f z) · J_f(z) = β(ψ∘f, f)(z)`. -/
theorem sp_chain_algebra {f fx fy ψ : ℂ → ℂ} {z : ℂ} (hfz : DifferentiableAt ℝ f z)
    (hx : fderiv ℝ f z 1 = fx z) (hy : fderiv ℝ f z I = fy z) :
    (jacobian f z : ℂ) * dzbar ψ (f z) =
      sp_beta (fun w => fderiv ℝ ψ (f w) (fx w)) (fun w => fderiv ℝ ψ (f w) (fy w)) fx fy z := by
  -- the partial derivatives of `f` in terms of `p = ∂_z f`, `q = ∂_{z̄} f`
  have hfxv : fx z = dz f z + dzbar f z := by
    rw [← hx, fderiv_eq_dz_dzbar hfz]
    simp
  have hfyv : fy z = I * (dz f z - dzbar f z) := by
    rw [← hy, fderiv_eq_dz_dzbar hfz, Complex.conj_I]
    ring
  have hcx : conj (fx z) = conj (dz f z) + conj (dzbar f z) := by
    rw [hfxv, map_add]
  have hcy : conj (fy z) = -(I * (conj (dz f z) - conj (dzbar f z))) := by
    rw [hfyv, map_mul, map_sub, Complex.conj_I]
    ring
  -- the Jacobian as `p p̄ - q q̄`
  have hJ : ((jacobian f z : ℝ) : ℂ) =
      dz f z * conj (dz f z) - dzbar f z * conj (dzbar f z) := by
    have h1 : dz f z * conj (dz f z) = ((‖dz f z‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.sq_norm]
    have h2 : dzbar f z * conj (dzbar f z) = ((‖dzbar f z‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.sq_norm]
    have h3 : jacobian f z = ‖dz f z‖ ^ 2 - ‖dzbar f z‖ ^ 2 := rfl
    rw [h1, h2, h3]
    push_cast
    ring
  -- the two directional derivatives of `ψ` at `f z`
  have hΨx : fderiv ℝ ψ (f z) (fx z) = dz ψ (f z) * fx z + dzbar ψ (f z) * conj (fx z) :=
    sp_c_fderiv_eq_dz_dzbar ψ (f z) (fx z)
  have hΨy : fderiv ℝ ψ (f z) (fy z) = dz ψ (f z) * fy z + dzbar ψ (f z) * conj (fy z) :=
    sp_c_fderiv_eq_dz_dzbar ψ (f z) (fy z)
  simp only [sp_beta_eq]
  rw [hΨx, hΨy, hJ, hcx, hcy, hfxv, hfyv]
  linear_combination (dzbar ψ (f z) *
    (dz f z * conj (dz f z) - dzbar f z * conj (dzbar f z))) * Complex.I_sq

/-! ### Convergence of the pulled-back partial derivatives -/

/-- The formal `x`-partial of `ψ ∘ h`, built from a partial derivative `hx` of `h`. -/
def sp_psiX (ψ h hx : ℂ → ℂ) : ℂ → ℂ := fun z => fderiv ℝ ψ (h z) (hx z)

/-- A sequence of extended nonnegative reals which is, for every `ε > 0`, eventually bounded by
`C * ε` tends to `0`. -/
theorem sp_f1_tendsto_zero_of_le_const_mul {u : ℕ → ℝ≥0∞} {C : ℝ} (hC : 0 < C)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, u m ≤ ENNReal.ofReal (C * ε)) :
    Tendsto u atTop (𝓝 0) := by
  have hC0 : C ≠ 0 := ne_of_gt hC
  rw [ENNReal.tendsto_nhds_zero]
  intro t ht
  obtain ⟨r, hr, hrt⟩ : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ t := by
    rcases eq_or_ne t ⊤ with h' | h'
    · exact ⟨1, one_pos, by simp [h']⟩
    · exact ⟨t.toReal, ENNReal.toReal_pos ht.ne' h', le_of_eq (ENNReal.ofReal_toReal h')⟩
  filter_upwards [h (r / C) (by positivity)] with m hm
  refine hm.trans (le_trans (le_of_eq ?_) hrt)
  congr 1
  field_simp

/-- Multiplying an `L²` function by a bounded a.e.-measurable function stays in `L²`. -/
theorem sp_f1_memLp_mul {L : Set ℂ} {a u : ℂ → ℂ} {M : ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict L)) (haM : ∀ z, ‖a z‖ ≤ M)
    (hu : MemLp u 2 (volume.restrict L)) (c : ℂ) :
    MemLp (fun z => c * a z * u z) 2 (volume.restrict L) := by
  refine MemLp.mono' (hu.norm.const_mul (‖c‖ * M)) ((ha.const_mul c).mul hu.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => ?_)
  simp only [norm_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (haM z) (norm_nonneg c))
    (norm_nonneg _)

/-- `L²` bound for a product with a bounded function. -/
theorem sp_f1_eLpNorm_mul_le {L : Set ℂ} {a u : ℂ → ℂ} {M : ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict L)) (haM : ∀ z, ‖a z‖ ≤ M)
    (hu : AEStronglyMeasurable u (volume.restrict L)) (c : ℂ) :
    eLpNorm (fun z => c * a z * u z) 2 (volume.restrict L)
      ≤ ENNReal.ofReal (‖c‖ * M) * eLpNorm u 2 (volume.restrict L) := by
  have hM0 : (0 : ℝ) ≤ M := (norm_nonneg (a 0)).trans (haM 0)
  have hcM : (0 : ℝ) ≤ ‖c‖ * M := mul_nonneg (norm_nonneg c) hM0
  have hm : AEStronglyMeasurable (fun z => c * a z * u z) (volume.restrict L) :=
    (ha.const_mul c).mul hu
  refine le_trans (eLpNorm_mono_ae_real (g := fun z => ‖c‖ * M * ‖u z‖) hm
    (Filter.Eventually.of_forall fun z => ?_)) ?_
  · simp only [norm_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (haM z) (norm_nonneg c))
      (norm_nonneg _)
  · have h2 := eLpNorm_const_smul_le (c := ‖c‖ * M) (f := fun z => ‖u z‖) (p := 2)
      (μ := volume.restrict L)
    rw [Real.enorm_eq_ofReal hcM, eLpNorm_norm _ hu] at h2
    exact h2

/-- Post-composition with a continuous map preserves uniform convergence on a compact set. -/
theorem sp_e_unif_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : ℂ → E}
    (hΦ : Continuous Φ) {L : Set ℂ} (hL : IsCompact L) {fm : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hf : ContinuousOn f L) (hlim : TendstoUniformlyOn fm f atTop L) :
    TendstoUniformlyOn (fun m z => Φ (fm m z)) (fun z => Φ (f z)) atTop L := by
  set K : Set ℂ := cthickening 1 (f '' L) with hKdef
  have hKc : IsCompact K := (hL.image_of_continuousOn hf).cthickening
  have hΦK : UniformContinuousOn Φ K := hKc.uniformContinuousOn_of_continuous hΦ.continuousOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.1 hΦK ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.1 hlim) (min δ 1) (lt_min hδ one_pos)] with
    m hm z hz
  have h1 := hm z hz
  have hfz : f z ∈ K := self_subset_cthickening _ ⟨z, hz, rfl⟩
  have hfmz : fm m z ∈ K := by
    apply mem_cthickening_of_dist_le (fm m z) (f z) 1 (f '' L) ⟨z, hz, rfl⟩
    rw [dist_comm]
    exact (h1.trans_le (min_le_right _ _)).le
  exact hδε (f z) hfz (fm m z) hfmz (h1.trans_le (min_le_left _ _))

/-- The formal partials of `ψ ∘ h` are in `L²` on compact sets. -/
theorem sp_e_psiX_memLp {ψ h hx : ℂ → ℂ} {L : Set ℂ} (hL : IsCompact L) (hψ : ContDiff ℝ 2 ψ)
    (hh : ContinuousOn h L) (hxL : MemLp hx 2 (volume.restrict L)) :
    MemLp (sp_psiX ψ h hx) 2 (volume.restrict L) := by
  have hLm : MeasurableSet L := hL.isClosed.measurableSet
  have hcf : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by simp)
  have hmeas : AEStronglyMeasurable (fun z => fderiv ℝ ψ (h z)) (volume.restrict L) :=
    (hcf.comp_continuousOn hh).aestronglyMeasurable hLm
  have hae : AEStronglyMeasurable (sp_psiX ψ h hx) (volume.restrict L) := by
    have h2 : AEStronglyMeasurable (fun z => fderiv ℝ ψ (h z) (hx z)) (volume.restrict L) :=
      ContinuousLinearMap.aestronglyMeasurable_comp₂
        (ContinuousLinearMap.id ℝ (ℂ →L[ℝ] ℂ)) hmeas hxL.aestronglyMeasurable
    exact h2
  obtain ⟨M, hM⟩ := (hL.image_of_continuousOn hh).exists_bound_of_continuousOn hcf.continuousOn
  refine MemLp.mono' (hxL.norm.const_mul (max M 0)) hae ?_
  filter_upwards [ae_restrict_mem hLm] with z hz
  have h1 : ‖fderiv ℝ ψ (h z)‖ ≤ max M 0 := (hM (h z) ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  calc ‖sp_psiX ψ h hx z‖ = ‖fderiv ℝ ψ (h z) (hx z)‖ := rfl
    _ ≤ ‖fderiv ℝ ψ (h z)‖ * ‖hx z‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ max M 0 * ‖hx z‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

/-- `L²` convergence of the formal partials of `ψ ∘ fₘ` to those of `ψ ∘ f`. -/
theorem sp_e_psiX_tendsto {ψ f fx : ℂ → ℂ} {fm fxm : ℕ → ℂ → ℂ} {L : Set ℂ} (hL : IsCompact L)
    (hψ : ContDiff ℝ 2 ψ) (hf : ContinuousOn f L) (hunif : TendstoUniformlyOn fm f atTop L)
    (hfmc : ∀ m, ContinuousOn (fm m) L)
    (hfx : MemLp fx 2 (volume.restrict L)) (hfxm : ∀ m, MemLp (fxm m) 2 (volume.restrict L))
    (hconv : Tendsto (fun m => eLpNorm (fun z => fxm m z - fx z) 2 (volume.restrict L)) atTop
      (𝓝 0)) :
    Tendsto (fun m => eLpNorm (fun z => sp_psiX ψ (fm m) (fxm m) z - sp_psiX ψ f fx z) 2
      (volume.restrict L)) atTop (𝓝 0) := by
  have hLm : MeasurableSet L := hL.isClosed.measurableSet
  have hcf : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by simp)
  have hDunif : TendstoUniformlyOn (fun m z => fderiv ℝ ψ (fm m z))
      (fun z => fderiv ℝ ψ (f z)) atTop L := sp_e_unif_comp hcf hL hf hunif
  obtain ⟨M, hM⟩ := (hL.image_of_continuousOn hf).exists_bound_of_continuousOn hcf.continuousOn
  have hM0 : (0 : ℝ) ≤ max M 0 := le_max_right _ _
  have hMb : ∀ z ∈ L, ‖fderiv ℝ ψ (f z)‖ ≤ max M 0 := fun z hz =>
    (hM (f z) ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  have hB0 : (0 : ℝ) ≤ (eLpNorm fx 2 (volume.restrict L)).toReal := ENNReal.toReal_nonneg
  have hBev : ∀ᶠ m in atTop, eLpNorm (fxm m) 2 (volume.restrict L)
      ≤ ENNReal.ofReal ((eLpNorm fx 2 (volume.restrict L)).toReal + 1) := by
    filter_upwards [ENNReal.tendsto_nhds_zero.1 hconv 1 one_pos] with m hm
    have h2 := eLpNorm_add_le (μ := volume.restrict L) (p := 2)
      (f := fun z => fxm m z - fx z) (g := fx) (by norm_num)
    have heq : ((fun z => fxm m z - fx z) + fx) = fxm m := by funext z; simp
    rw [heq] at h2
    refine h2.trans ?_
    rw [ENNReal.ofReal_add hB0 zero_le_one, ENNReal.ofReal_toReal hfx.eLpNorm_ne_top,
      ENNReal.ofReal_one, add_comm (eLpNorm fx 2 (volume.restrict L)) 1]
    exact add_le_add hm le_rfl
  refine sp_f1_tendsto_zero_of_le_const_mul
    (C := (eLpNorm fx 2 (volume.restrict L)).toReal + 1 + max M 0 + 1) (by linarith) ?_
  intro ε hε
  filter_upwards [hBev, (Metric.tendstoUniformlyOn_iff.1 hDunif) ε hε,
    ENNReal.tendsto_nhds_zero.1 hconv (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)] with
    m hmB hmU hmC
  have hptw : ∀ z ∈ L, ‖sp_psiX ψ (fm m) (fxm m) z - sp_psiX ψ f fx z‖
      ≤ ε * ‖fxm m z‖ + max M 0 * ‖fxm m z - fx z‖ := by
    intro z hz
    have hsplit : sp_psiX ψ (fm m) (fxm m) z - sp_psiX ψ f fx z
        = (fderiv ℝ ψ (fm m z) - fderiv ℝ ψ (f z)) (fxm m z)
          + fderiv ℝ ψ (f z) (fxm m z - fx z) := by
      show fderiv ℝ ψ (fm m z) (fxm m z) - fderiv ℝ ψ (f z) (fx z) = _
      rw [ContinuousLinearMap.sub_apply, map_sub]
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      have hd : ‖fderiv ℝ ψ (fm m z) - fderiv ℝ ψ (f z)‖ ≤ ε := by
        have hdz := hmU z hz
        rw [dist_eq_norm, norm_sub_rev] at hdz
        exact hdz.le
      exact mul_le_mul_of_nonneg_right hd (norm_nonneg _)
    · exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hMb z hz) (norm_nonneg _))
  have hmeas1 : AEStronglyMeasurable (fun z => ε * ‖fxm m z‖) (volume.restrict L) :=
    (hfxm m).aestronglyMeasurable.norm.const_mul ε
  have hmeas2 : AEStronglyMeasurable (fun z => max M 0 * ‖fxm m z - fx z‖)
      (volume.restrict L) := (((hfxm m).sub hfx).aestronglyMeasurable.norm).const_mul _
  have hstep : eLpNorm (fun z => sp_psiX ψ (fm m) (fxm m) z - sp_psiX ψ f fx z) 2
        (volume.restrict L)
      ≤ eLpNorm (fun z => ε * ‖fxm m z‖) 2 (volume.restrict L)
        + eLpNorm (fun z => max M 0 * ‖fxm m z - fx z‖) 2 (volume.restrict L) := by
    refine le_trans (eLpNorm_mono_ae_real
      (g := fun z => ε * ‖fxm m z‖ + max M 0 * ‖fxm m z - fx z‖) ?_ ?_) ?_
    · exact ((sp_e_psiX_memLp hL hψ (hfmc m) (hfxm m)).sub
        (sp_e_psiX_memLp hL hψ hf hfx)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hLm] with z hz using hptw z hz
    · exact eLpNorm_add_le (μ := volume.restrict L) (p := 2)
        (f := fun z => ε * ‖fxm m z‖) (g := fun z => max M 0 * ‖fxm m z - fx z‖)
        (by norm_num)
  have hA : eLpNorm (fun z => ε * ‖fxm m z‖) 2 (volume.restrict L)
      ≤ ENNReal.ofReal ε * eLpNorm (fxm m) 2 (volume.restrict L) := by
    have h3 := eLpNorm_const_smul_le (c := ε) (f := fun z => ‖fxm m z‖) (p := 2)
      (μ := volume.restrict L)
    rw [Real.enorm_eq_ofReal hε.le, eLpNorm_norm _ (hfxm m).aestronglyMeasurable] at h3
    exact h3
  have hBb : eLpNorm (fun z => max M 0 * ‖fxm m z - fx z‖) 2 (volume.restrict L)
      ≤ ENNReal.ofReal (max M 0) * eLpNorm (fun z => fxm m z - fx z) 2 (volume.restrict L) := by
    have h3 := eLpNorm_const_smul_le (c := max M 0) (f := fun z => ‖fxm m z - fx z‖) (p := 2)
      (μ := volume.restrict L)
    rw [Real.enorm_eq_ofReal hM0,
      eLpNorm_norm (fun z => fxm m z - fx z) ((hfxm m).sub hfx).aestronglyMeasurable] at h3
    exact h3
  refine hstep.trans (le_trans (add_le_add (hA.trans (mul_le_mul_right hmB _))
    (hBb.trans (mul_le_mul_right hmC _))) ?_)
  rw [← ENNReal.ofReal_mul hε.le, ← ENNReal.ofReal_mul hM0,
    ← ENNReal.ofReal_add (mul_nonneg hε.le (by linarith)) (mul_nonneg hM0 hε.le)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hexp : ((eLpNorm fx 2 (volume.restrict L)).toReal + 1 + max M 0 + 1) * ε
      = ε * ((eLpNorm fx 2 (volume.restrict L)).toReal + 1) + max M 0 * ε + ε := by ring
  linarith

/-- Limit of the bracket integrals under `L²` convergence of the first pair of partials. -/
theorem sp_e_beta_tendsto {L : Set ℂ} {vx vy ux uy a : ℂ → ℂ} {uxm uym : ℕ → ℂ → ℂ}
    (hvx : MemLp vx 2 (volume.restrict L)) (hvy : MemLp vy 2 (volume.restrict L))
    (hux : MemLp ux 2 (volume.restrict L)) (huy : MemLp uy 2 (volume.restrict L))
    (huxm : ∀ m, MemLp (uxm m) 2 (volume.restrict L))
    (huym : ∀ m, MemLp (uym m) 2 (volume.restrict L))
    (haM : ∃ M : ℝ, ∀ z, ‖a z‖ ≤ M) (ha : AEStronglyMeasurable a (volume.restrict L))
    (hx : Tendsto (fun m => eLpNorm (fun z => uxm m z - ux z) 2 (volume.restrict L)) atTop (𝓝 0))
    (hy : Tendsto (fun m => eLpNorm (fun z => uym m z - uy z) 2 (volume.restrict L)) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ z in L, a z * sp_beta (uxm m) (uym m) vx vy z) atTop
      (𝓝 (∫ z in L, a z * sp_beta ux uy vx vy z)) := by
  obtain ⟨M, hM⟩ := haM
  have hmul : ∀ u : ℂ → ℂ, MemLp u 2 (volume.restrict L) →
      MemLp (fun z => I / 2 * a z * u z) 2 (volume.restrict L) :=
    fun u hu => sp_f1_memLp_mul ha hM hu (I / 2)
  have hint : ∀ p q : ℂ → ℂ, MemLp p 2 (volume.restrict L) → MemLp q 2 (volume.restrict L) →
      (∫ z in L, a z * sp_beta p q vx vy z)
        = (∫ z in L, I / 2 * a z * q z * vx z) - ∫ z in L, I / 2 * a z * p z * vy z := by
    intro p q hp hq
    have hfun : (fun z => a z * sp_beta p q vx vy z)
        = fun z => I / 2 * a z * q z * vx z - I / 2 * a z * p z * vy z := by
      funext z
      rw [sp_beta_eq]
      ring
    rw [hfun]
    exact integral_sub ((hmul q hq).integrable_mul hvx) ((hmul p hp).integrable_mul hvy)
  have hlimY : Tendsto (fun m => eLpNorm
      (fun z => I / 2 * a z * uym m z - I / 2 * a z * uy z) 2 (volume.restrict L)) atTop
      (𝓝 0) := by
    have hbd : ∀ m, eLpNorm (fun z => I / 2 * a z * uym m z - I / 2 * a z * uy z) 2
        (volume.restrict L)
        ≤ ENNReal.ofReal (‖(I / 2 : ℂ)‖ * M)
          * eLpNorm (fun z => uym m z - uy z) 2 (volume.restrict L) := by
      intro m
      have heq : (fun z => I / 2 * a z * uym m z - I / 2 * a z * uy z)
          = fun z => I / 2 * a z * (uym m z - uy z) := by funext z; ring
      rw [heq]
      exact sp_f1_eLpNorm_mul_le ha hM ((huym m).sub huy).aestronglyMeasurable (I / 2)
    have h3 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (‖(I / 2 : ℂ)‖ * M)) hy
      (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at h3
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun m => by simp) hbd
  have hlimX : Tendsto (fun m => eLpNorm
      (fun z => I / 2 * a z * uxm m z - I / 2 * a z * ux z) 2 (volume.restrict L)) atTop
      (𝓝 0) := by
    have hbd : ∀ m, eLpNorm (fun z => I / 2 * a z * uxm m z - I / 2 * a z * ux z) 2
        (volume.restrict L)
        ≤ ENNReal.ofReal (‖(I / 2 : ℂ)‖ * M)
          * eLpNorm (fun z => uxm m z - ux z) 2 (volume.restrict L) := by
      intro m
      have heq : (fun z => I / 2 * a z * uxm m z - I / 2 * a z * ux z)
          = fun z => I / 2 * a z * (uxm m z - ux z) := by funext z; ring
      rw [heq]
      exact sp_f1_eLpNorm_mul_le ha hM ((huxm m).sub hux).aestronglyMeasurable (I / 2)
    have h3 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (‖(I / 2 : ℂ)‖ * M)) hx
      (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at h3
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun m => by simp) hbd
  have h1 := sp_tendsto_integral_mul_of_L2 (K := L) (a := fun m z => I / 2 * a z * uym m z)
    (a₀ := fun z => I / 2 * a z * uy z) (b := vx)
    (fun m => hmul _ (huym m)) (hmul _ huy) hvx hlimY
  have h2 := sp_tendsto_integral_mul_of_L2 (K := L) (a := fun m z => I / 2 * a z * uxm m z)
    (a₀ := fun z => I / 2 * a z * ux z) (b := vy)
    (fun m => hmul _ (huxm m)) (hmul _ hux) hvy hlimX
  rw [hint ux uy hux huy]
  exact Filter.Tendsto.congr (fun m => (hint (uxm m) (uym m) (huxm m) (huym m)).symm) (h1.sub h2)

/-! ### The main identity -/

/-- Restricting an integral to a subset off which the integrand vanishes. -/
theorem sp_f2_setIntegral_subset {h : ℂ → ℂ} {A B : Set ℂ} (hA : MeasurableSet A) (hBA : B ⊆ A)
    (h0 : ∀ z ∈ A, z ∉ B → h z = 0) : ∫ z in A, h z = ∫ z in B, h z :=
  setIntegral_eq_of_subset_of_ae_diff_eq_zero hA.nullMeasurableSet hBA
    (Eventually.of_forall fun z hz => h0 z hz.1 hz.2)

/-- The `tsupport` of a product is contained in that of the left factor. -/
theorem sp_f2_tsupport_mul_subset {p q : ℂ → ℂ} : tsupport (fun z => p z * q z) ⊆ tsupport p :=
  closure_mono fun z hz => by
    simp only [Function.mem_support] at hz ⊢
    intro h
    exact hz (by rw [h, zero_mul])

/-- A continuous function on a compact set is bounded there. -/
theorem sp_f2_bound_of_continuousOn {L : Set ℂ} (hL : IsCompact L) {b : ℂ → ℂ}
    (hb : ContinuousOn b L) : ∃ M : ℝ, ∀ z ∈ L, ‖b z‖ ≤ M := by
  obtain ⟨M, hM⟩ := (hL.image_of_continuousOn hb.norm).bddAbove
  exact ⟨M, fun z hz => hM (mem_image_of_mem _ hz)⟩

/-- A continuous function on a compact set is in `L²` there. -/
theorem sp_f2_memLp_of_continuousOn {L : Set ℂ} (hL : IsCompact L) {b : ℂ → ℂ}
    (hb : ContinuousOn b L) : MemLp b 2 (volume.restrict L) := by
  haveI : IsFiniteMeasure (volume.restrict L) :=
    isFiniteMeasure_restrict.2 hL.measure_lt_top.ne
  have hmeas : MeasurableSet L := hL.isClosed.measurableSet
  obtain ⟨M, hM⟩ := sp_f2_bound_of_continuousOn hL hb
  refine MemLp.of_bound (hb.aestronglyMeasurable hmeas) M ?_
  rw [ae_restrict_iff' hmeas]
  exact Eventually.of_forall hM

/-- A directional derivative of a `C²` function is continuous. -/
theorem sp_f2_continuous_fderiv {u : ℂ → ℂ} (hu : ContDiff ℝ 2 u) (v : ℂ) :
    Continuous (fun z => fderiv ℝ u z v) :=
  (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- The bracket vanishes wherever its first pair of arguments does. -/
theorem sp_f2_beta_eq_zero_of_fst {ux uy vx vy : ℂ → ℂ} {z : ℂ} (hx : ux z = 0) (hy : uy z = 0) :
    sp_beta ux uy vx vy z = 0 := by
  simp only [sp_beta_eq, hx, hy, zero_mul, sub_self, mul_zero]

/-- Integrability of a bounded factor against a bracket of `L²` data on a compact set. -/
theorem sp_f2_integrableOn_mul_beta {L : Set ℂ} (hL : IsCompact L) {a ux uy vx vy : ℂ → ℂ}
    (ha : ContinuousOn a L) (hux : MemLp ux 2 (volume.restrict L))
    (huy : MemLp uy 2 (volume.restrict L)) (hvx : MemLp vx 2 (volume.restrict L))
    (hvy : MemLp vy 2 (volume.restrict L)) :
    IntegrableOn (fun z => a z * sp_beta ux uy vx vy z) L := by
  have hmeas : MeasurableSet L := hL.isClosed.measurableSet
  obtain ⟨M, hM⟩ := sp_f2_bound_of_continuousOn hL ha
  have h1 : Integrable (fun z => uy z * vx z - ux z * vy z) (volume.restrict L) :=
    (huy.integrable_mul hvx).sub (hux.integrable_mul hvy)
  have h2 : Integrable (fun z => I / 2 * a z * (uy z * vx z - ux z * vy z))
      (volume.restrict L) := by
    refine h1.bdd_mul (aestronglyMeasurable_const.mul (ha.aestronglyMeasurable hmeas))
      (c := ‖I / 2‖ * M) ?_
    rw [ae_restrict_iff' hmeas]
    filter_upwards with z hz
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hM z hz) (norm_nonneg _)
  refine h2.congr (Eventually.of_forall fun z => ?_)
  simp only [sp_beta_eq]
  ring

/-- The heart of the similarity principle: the bracket of a test function pulled back by `f`
against `g` integrates to zero. -/
theorem sp_e_integral_eq_zero {f fx fy g gx gy μ ψ : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hfh : IsHomeomorphOnto f D (f '' D)) (hfd : HasGenPartials f fx fy D 2)
    (hgd : HasGenPartials g gx gy D 2)
    (hfb : ∀ᵐ z ∂(volume.restrict D), genDzbar fx fy z = μ z * genDz fx fy z)
    (hgb : ∀ᵐ z ∂(volume.restrict D), genDzbar gx gy z = μ z * genDz gx gy z)
    (hψ : ContDiff ℝ 2 ψ) (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ f '' D) :
    ∫ z in D, g z *
        sp_beta (fun w => fderiv ℝ ψ (f w) (fx w)) (fun w => fderiv ℝ ψ (f w) (fy w)) fx fy z
      = 0 := by
  classical
  have hDmeas : MeasurableSet D := hD.measurableSet
  have hfc : ContinuousOn f D := hfh.1
  have hgc : ContinuousOn g D := by
    obtain ⟨-, gn', hgn', hconv, -⟩ := hgd
    exact hconv.continuousOn (Filter.Frequently.of_forall fun n => (hgn' n).continuousOn)
  have hinv : ∀ z ∈ D, Function.invFunOn f D (f z) = z := fun z hz =>
    hfh.2.1.leftInvOn_invFunOn hz
  -- the ACL information and the local `L²` bounds for the classical partial derivatives
  obtain ⟨haclf, hfpx, hfpy⟩ :=
    lemma9_2_isACL_of_genPartials hD (by norm_num : (1 : ℝ≥0∞) ≤ 2) hfd
  obtain ⟨haclg, hgpx, hgpy⟩ :=
    lemma9_2_isACL_of_genPartials hD (by norm_num : (1 : ℝ≥0∞) ≤ 2) hgd
  have hflocP : ∀ C ⊆ D, IsCompact C → MemLp (partialX f) 2 (volume.restrict C) ∧
      MemLp (partialY f) 2 (volume.restrict C) := by
    intro C hCD hC
    have h1 : partialX f =ᵐ[volume.restrict C] fx := ae_restrict_of_ae_restrict_of_subset hCD hfpx
    have h2 : partialY f =ᵐ[volume.restrict C] fy := ae_restrict_of_ae_restrict_of_subset hCD hfpy
    exact ⟨(hfd.1 C hCD hC).1.ae_eq h1.symm, (hfd.1 C hCD hC).2.ae_eq h2.symm⟩
  have hglocP : ∀ C ⊆ D, IsCompact C → MemLp (partialX g) 2 (volume.restrict C) ∧
      MemLp (partialY g) 2 (volume.restrict C) := by
    intro C hCD hC
    have h1 : partialX g =ᵐ[volume.restrict C] gx := ae_restrict_of_ae_restrict_of_subset hCD hgpx
    have h2 : partialY g =ᵐ[volume.restrict C] gy := ae_restrict_of_ae_restrict_of_subset hCD hgpy
    exact ⟨(hgd.1 C hCD hC).1.ae_eq h1.symm, (hgd.1 C hCD hC).2.ae_eq h2.symm⟩
  -- the compact set `K = φ '' (tsupport ψ) ⊆ D`
  set K : Set ℂ := Function.invFunOn f D '' tsupport ψ with hKdef
  have hKcpt : IsCompact K := hcψ.isCompact.image_of_continuousOn (hfh.2.2.2.mono hsψ)
  have hKD : K ⊆ D := by
    intro x hx
    rw [hKdef] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨z, hz, rfl⟩ := hsψ hw
    rw [hinv z hz]
    exact hz
  have hout : ∀ z ∈ D, z ∉ K → f z ∉ tsupport ψ := by
    intro z hz hzK hfz
    apply hzK
    rw [hKdef]
    have hmem : Function.invFunOn f D (f z) ∈ Function.invFunOn f D '' tsupport ψ :=
      mem_image_of_mem _ hfz
    rwa [hinv z hz] at hmem
  -- the cutoff function
  obtain ⟨cut, hcut2, hcut1, hcutsupp, hcutc, hcut01⟩ := sp_e_exists_cutoff hKcpt hD hKD
  set L : Set ℂ := tsupport cut with hLdef
  have hLcpt : IsCompact L := hcutc.isCompact
  have hLD : L ⊆ D := hcutsupp
  have hLmeas : MeasurableSet L := hLcpt.isClosed.measurableSet
  have hKmeas : MeasurableSet K := hKcpt.isClosed.measurableSet
  have hcutnear : ∀ z ∈ K, ∀ᶠ w in 𝓝 z, cut w = 1 := eventually_nhdsSet_iff_forall.1 hcut1
  have hKL : K ⊆ L := by
    intro z hz
    rw [hLdef]
    refine subset_closure ?_
    simp only [Function.mem_support]
    have h1 : cut z = 1 := (hcutnear z hz).self_of_nhds
    rw [h1]
    exact one_ne_zero
  set cc : ℂ → ℂ := fun z => ((cut z : ℝ) : ℂ) with hccdef
  have hcc2 : ContDiff ℝ 2 cc := Complex.ofRealCLM.contDiff.comp hcut2
  have hcccont : Continuous cc := hcc2.continuous
  have hcc0 : ∀ z ∉ L, cc z = 0 := by
    intro z hz
    simp only [hccdef, image_eq_zero_of_notMem_tsupport hz, Complex.ofReal_zero]
  have hcccs : HasCompactSupport cc := HasCompactSupport.intro hLcpt hcc0
  have hccsupp : tsupport cc ⊆ L :=
    closure_minimal (fun z hz => by
      by_contra hzL
      exact hz (hcc0 z hzL)) hLcpt.isClosed
  have hccbd : ∀ z, ‖cc z‖ ≤ 1 := by
    intro z
    have h01 := hcut01 z
    simp only [hccdef, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg h01.1]
    exact h01.2
  have hccK : ∀ z ∈ K, cc z = 1 := by
    intro z hz
    simp only [hccdef, (hcutnear z hz).self_of_nhds, Complex.ofReal_one]
  have hdcc : ∀ z ∈ K, ∀ v : ℂ, fderiv ℝ cc z v = 0 := by
    intro z hz v
    have h1 : cc =ᶠ[𝓝 z] fun _ => (1 : ℂ) := by
      filter_upwards [hcutnear z hz] with w hw
      simp only [hccdef, hw, Complex.ofReal_one]
    rw [h1.fderiv_eq]
    simp
  -- the mollifier approximants
  set fm : ℕ → ℂ → ℂ := lemma92Approx D f with hfmdef
  set gm : ℕ → ℂ → ℂ := lemma92Approx D g with hgmdef
  have hfm2 : ∀ m, ContDiff ℝ 2 (fm m) := fun m => sp_m_contDiff2 hfc m
  have hgm2 : ∀ n, ContDiff ℝ 2 (gm n) := fun n => sp_m_contDiff2 hgc n
  have hunifL : TendstoUniformlyOn fm f atTop L :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).1
      (tendstoLocallyUniformlyOn_lemma92Approx hD hfc) L hLD hLcpt
  have hunifK : TendstoUniformlyOn gm g atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).1
      (tendstoLocallyUniformlyOn_lemma92Approx hD hgc) K hKD hKcpt
  have hconvfx : Tendsto (fun m => eLpNorm (fun z => fderiv ℝ (fm m) z 1 - fx z) 2
      (volume.restrict L)) atTop (𝓝 0) := by
    have hx : partialX f =ᵐ[volume.restrict L] fx := ae_restrict_of_ae_restrict_of_subset hLD hfpx
    have heq : ∀ m, eLpNorm (fun z => fderiv ℝ (fm m) z 1 - partialX f z) 2 (volume.restrict L)
        = eLpNorm (fun z => fderiv ℝ (fm m) z 1 - fx z) 2 (volume.restrict L) := by
      intro m
      refine eLpNorm_congr_ae ?_
      filter_upwards [hx] with z hz
      rw [hz]
    have h : Tendsto (fun m => eLpNorm (fun z => fderiv ℝ (fm m) z 1 - partialX f z) 2
        (volume.restrict L)) atTop (𝓝 0) := (sp_m_tendsto hD haclf hflocP hLD hLcpt).1
    exact h.congr heq
  have hconvfy : Tendsto (fun m => eLpNorm (fun z => fderiv ℝ (fm m) z I - fy z) 2
      (volume.restrict L)) atTop (𝓝 0) := by
    have hy : partialY f =ᵐ[volume.restrict L] fy := ae_restrict_of_ae_restrict_of_subset hLD hfpy
    have heq : ∀ m, eLpNorm (fun z => fderiv ℝ (fm m) z I - partialY f z) 2 (volume.restrict L)
        = eLpNorm (fun z => fderiv ℝ (fm m) z I - fy z) 2 (volume.restrict L) := by
      intro m
      refine eLpNorm_congr_ae ?_
      filter_upwards [hy] with z hz
      rw [hz]
    have h : Tendsto (fun m => eLpNorm (fun z => fderiv ℝ (fm m) z I - partialY f z) 2
        (volume.restrict L)) atTop (𝓝 0) := (sp_m_tendsto hD haclf hflocP hLD hLcpt).2
    exact h.congr heq
  have hconvgx : Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (gm n) z 1 - gx z) 2
      (volume.restrict L)) atTop (𝓝 0) := by
    have hx : partialX g =ᵐ[volume.restrict L] gx := ae_restrict_of_ae_restrict_of_subset hLD hgpx
    have heq : ∀ n, eLpNorm (fun z => fderiv ℝ (gm n) z 1 - partialX g z) 2 (volume.restrict L)
        = eLpNorm (fun z => fderiv ℝ (gm n) z 1 - gx z) 2 (volume.restrict L) := by
      intro n
      refine eLpNorm_congr_ae ?_
      filter_upwards [hx] with z hz
      rw [hz]
    have h : Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (gm n) z 1 - partialX g z) 2
        (volume.restrict L)) atTop (𝓝 0) := (sp_m_tendsto hD haclg hglocP hLD hLcpt).1
    exact h.congr heq
  have hconvgy : Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (gm n) z I - gy z) 2
      (volume.restrict L)) atTop (𝓝 0) := by
    have hy : partialY g =ᵐ[volume.restrict L] gy := ae_restrict_of_ae_restrict_of_subset hLD hgpy
    have heq : ∀ n, eLpNorm (fun z => fderiv ℝ (gm n) z I - partialY g z) 2 (volume.restrict L)
        = eLpNorm (fun z => fderiv ℝ (gm n) z I - gy z) 2 (volume.restrict L) := by
      intro n
      refine eLpNorm_congr_ae ?_
      filter_upwards [hy] with z hz
      rw [hz]
    have h : Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (gm n) z I - partialY g z) 2
        (volume.restrict L)) atTop (𝓝 0) := (sp_m_tendsto hD haclg hglocP hLD hLcpt).2
    exact h.congr heq
  -- the `C²` test functions
  set A : ℕ → ℂ → ℂ := fun n z => cc z * gm n z with hAdef
  set Psi : ℂ → ℂ := fun z => ψ (f z) with hPsidef
  set Psim : ℕ → ℂ → ℂ := fun m z => ψ (fm m z) with hPsimdef
  have hA2 : ∀ n, ContDiff ℝ 2 (A n) := fun n => hcc2.mul (hgm2 n)
  have hAcont : ∀ n, Continuous (A n) := fun n => (hA2 n).continuous
  have hA0 : ∀ n, ∀ z ∉ L, A n z = 0 := by
    intro n z hz
    simp only [hAdef, hcc0 z hz, zero_mul]
  have hAcs : ∀ n, HasCompactSupport (A n) := fun n => HasCompactSupport.intro hLcpt (hA0 n)
  have hAsupp : ∀ n, tsupport (A n) ⊆ L := fun n =>
    (sp_f2_tsupport_mul_subset (p := cc) (q := gm n)).trans hccsupp
  have hAbd : ∀ n, ∃ M : ℝ, ∀ z, ‖A n z‖ ≤ M := fun n =>
    (hAcont n).bounded_above_of_compact_support (hAcs n)
  have hPsim2 : ∀ m, ContDiff ℝ 2 (Psim m) := fun m => hψ.comp (hfm2 m)
  have hPsimcont : ∀ m, Continuous (Psim m) := fun m => (hPsim2 m).continuous
  have hPsicont : ContinuousOn Psi D := hψ.continuous.comp_continuousOn hfc
  have hPsi0 : ∀ z ∈ D, z ∉ K → Psi z = 0 := by
    intro z hz hzK
    simp only [hPsidef]
    exact image_eq_zero_of_notMem_tsupport (hout z hz hzK)
  obtain ⟨Mp, hMp⟩ := hψ.continuous.bounded_above_of_compact_support hcψ
  -- the brackets
  set BA : ℕ → ℂ → ℂ := fun n z => sp_beta (fun w => fderiv ℝ (A n) w 1)
    (fun w => fderiv ℝ (A n) w I) fx fy z with hBAdef
  set BP : ℕ → ℂ → ℂ := fun m z => sp_beta (sp_psiX ψ (fm m) (fun w => fderiv ℝ (fm m) w 1))
    (sp_psiX ψ (fm m) (fun w => fderiv ℝ (fm m) w I)) fx fy z with hBPdef
  set BQ : ℂ → ℂ := fun z => sp_beta (sp_psiX ψ f fx) (sp_psiX ψ f fy) fx fy z with hBQdef
  set Bcc : ℂ → ℂ := fun z => sp_beta (fun w => fderiv ℝ cc w 1) (fun w => fderiv ℝ cc w I)
    fx fy z with hBccdef
  set Bg : ℕ → ℂ → ℂ := fun n z => sp_beta (fun w => fderiv ℝ (gm n) w 1)
    (fun w => fderiv ℝ (gm n) w I) fx fy z with hBgdef
  -- the `L²` data on the compact sets `L` and `K`
  have hfxL : MemLp fx 2 (volume.restrict L) := (hfd.1 L hLD hLcpt).1
  have hfyL : MemLp fy 2 (volume.restrict L) := (hfd.1 L hLD hLcpt).2
  have hgxL : MemLp gx 2 (volume.restrict L) := (hgd.1 L hLD hLcpt).1
  have hgyL : MemLp gy 2 (volume.restrict L) := (hgd.1 L hLD hLcpt).2
  have hfxK : MemLp fx 2 (volume.restrict K) := (hfd.1 K hKD hKcpt).1
  have hfyK : MemLp fy 2 (volume.restrict K) := (hfd.1 K hKD hKcpt).2
  have hdA : ∀ (n : ℕ) (v : ℂ), MemLp (fun w => fderiv ℝ (A n) w v) 2 (volume.restrict L) :=
    fun n v => sp_f2_memLp_of_continuousOn hLcpt (sp_f2_continuous_fderiv (hA2 n) v).continuousOn
  have hdfm : ∀ (m : ℕ) (v : ℂ), MemLp (fun w => fderiv ℝ (fm m) w v) 2 (volume.restrict L) :=
    fun m v => sp_f2_memLp_of_continuousOn hLcpt (sp_f2_continuous_fderiv (hfm2 m) v).continuousOn
  have hdgm : ∀ (n : ℕ) (v : ℂ), MemLp (fun w => fderiv ℝ (gm n) w v) 2 (volume.restrict L) :=
    fun n v => sp_f2_memLp_of_continuousOn hLcpt (sp_f2_continuous_fderiv (hgm2 n) v).continuousOn
  have hpsiXL : MemLp (sp_psiX ψ f fx) 2 (volume.restrict L) :=
    sp_e_psiX_memLp hLcpt hψ (hfc.mono hLD) hfxL
  have hpsiYL : MemLp (sp_psiX ψ f fy) 2 (volume.restrict L) :=
    sp_e_psiX_memLp hLcpt hψ (hfc.mono hLD) hfyL
  have hpsiXK : MemLp (sp_psiX ψ f fx) 2 (volume.restrict K) :=
    sp_e_psiX_memLp hKcpt hψ (hfc.mono hKD) hfxK
  have hpsiYK : MemLp (sp_psiX ψ f fy) 2 (volume.restrict K) :=
    sp_e_psiX_memLp hKcpt hψ (hfc.mono hKD) hfyK
  have hpsiXm : ∀ m, MemLp (sp_psiX ψ (fm m) (fun w => fderiv ℝ (fm m) w 1)) 2
      (volume.restrict L) := fun m =>
    sp_e_psiX_memLp hLcpt hψ (hfm2 m).continuous.continuousOn (hdfm m 1)
  have hpsiYm : ∀ m, MemLp (sp_psiX ψ (fm m) (fun w => fderiv ℝ (fm m) w I)) 2
      (volume.restrict L) := fun m =>
    sp_e_psiX_memLp hLcpt hψ (hfm2 m).continuous.continuousOn (hdfm m I)
  -- the vanishing of the brackets
  have hBA0 : ∀ n, ∀ z ∉ L, BA n z = 0 := fun n z hz =>
    sp_f2_beta_eq_zero_of_fst
      (sp_fderiv_eq_zero_of_notMem_tsupport (fun hmem => hz (hAsupp n hmem)) 1)
      (sp_fderiv_eq_zero_of_notMem_tsupport (fun hmem => hz (hAsupp n hmem)) I)
  have hBQ0 : ∀ z ∈ D, z ∉ K → BQ z = 0 := fun z hz hzK =>
    sp_f2_beta_eq_zero_of_fst
      (sp_fderiv_eq_zero_of_notMem_tsupport (hout z hz hzK) (fx z))
      (sp_fderiv_eq_zero_of_notMem_tsupport (hout z hz hzK) (fy z))
  have hBcc0 : ∀ z ∈ K, Bcc z = 0 := fun z hz =>
    sp_f2_beta_eq_zero_of_fst (hdcc z hz 1) (hdcc z hz I)
  -- STEP 1: the bracket of the `C²` test function `(cc · gₙ) · (ψ ∘ fₘ)` integrates to zero
  have step1 : ∀ n m, (∫ z in D, sp_beta (fun w => fderiv ℝ (fun t => A n t * Psim m t) w 1)
      (fun w => fderiv ℝ (fun t => A n t * Psim m t) w I) fx fy z) = 0 := by
    intro n m
    refine sp_integral_beta_eq_zero hD hfd ((hA2 n).mul (hPsim2 m))
      (HasCompactSupport.intro hLcpt (fun z hz => by simp only [hA0 n z hz, zero_mul])) ?_
    exact (sp_f2_tsupport_mul_subset (p := A n) (q := Psim m)).trans ((hAsupp n).trans hLD)
  -- STEP 2: the pointwise expansion of the bracket
  have hBPeq : ∀ m z, sp_beta (fun w => fderiv ℝ (Psim m) w 1)
      (fun w => fderiv ℝ (Psim m) w I) fx fy z = BP m z := by
    intro m z
    have hchain : ∀ v : ℂ, (fun w => fderiv ℝ (Psim m) w v)
        = sp_psiX ψ (fm m) (fun w => fderiv ℝ (fm m) w v) := by
      intro v
      funext w
      exact sp_psiX_comp (ψ := ψ) (h := fm m) (hψ.differentiable (by norm_num) _)
        ((hfm2 m).differentiable (by norm_num) w) v
    have hBP : BP m z = sp_beta (sp_psiX ψ (fm m) (fun w => fderiv ℝ (fm m) w 1))
        (sp_psiX ψ (fm m) (fun w => fderiv ℝ (fm m) w I)) fx fy z := rfl
    rw [hBP, hchain 1, hchain I]
  have step2 : ∀ n m z, sp_beta (fun w => fderiv ℝ (fun t => A n t * Psim m t) w 1)
      (fun w => fderiv ℝ (fun t => A n t * Psim m t) w I) fx fy z
      = Psim m z * BA n z + A n z * BP m z := by
    intro n m z
    have h1 : sp_beta (fun w => fderiv ℝ (fun t => A n t * Psim m t) w 1)
        (fun w => fderiv ℝ (fun t => A n t * Psim m t) w I) fx fy z
        = Psim m z * BA n z + A n z * sp_beta (fun w => fderiv ℝ (Psim m) w 1)
          (fun w => fderiv ℝ (Psim m) w I) fx fy z :=
      sp_beta_mul ((hA2 n).differentiable (by norm_num) z)
        ((hPsim2 m).differentiable (by norm_num) z)
    rw [h1, hBPeq m z]
  -- STEP 3: everything happens on the compact set `L`
  have step3 : ∀ n m, (∫ z in L, Psim m z * BA n z) + (∫ z in L, A n z * BP m z) = 0 := by
    intro n m
    have hint1 : IntegrableOn (fun z => Psim m z * BA n z) L :=
      sp_f2_integrableOn_mul_beta hLcpt (hPsimcont m).continuousOn (hdA n 1) (hdA n I) hfxL hfyL
    have hint2 : IntegrableOn (fun z => A n z * BP m z) L :=
      sp_f2_integrableOn_mul_beta hLcpt (hAcont n).continuousOn (hpsiXm m) (hpsiYm m) hfxL hfyL
    have hDL : (∫ z in D, (Psim m z * BA n z + A n z * BP m z))
        = ∫ z in L, (Psim m z * BA n z + A n z * BP m z) := by
      refine sp_f2_setIntegral_subset hDmeas hLD (fun z _ hz => ?_)
      rw [hBA0 n z hz, hA0 n z hz, mul_zero, zero_mul, add_zero]
    have hDD : (∫ z in D, sp_beta (fun w => fderiv ℝ (fun t => A n t * Psim m t) w 1)
        (fun w => fderiv ℝ (fun t => A n t * Psim m t) w I) fx fy z)
        = ∫ z in D, (Psim m z * BA n z + A n z * BP m z) := by
      refine setIntegral_congr_fun hDmeas (fun z _ => ?_)
      exact step2 n m z
    rw [← integral_add hint1 hint2, ← hDL, ← hDD]
    exact step1 n m
  -- STEP 4: let `m → ∞` for a fixed `n`
  have step4 : ∀ n, (∫ z in L, Psi z * BA n z) + (∫ z in L, A n z * BQ z) = 0 := by
    intro n
    have hlim1 : Tendsto (fun m => ∫ z in L, Psim m z * BA n z) atTop
        (𝓝 (∫ z in L, Psi z * BA n z)) := by
      refine sp_tendsto_integral_mul_of_uniform ?_ (fun m => ?_) ?_
        (sp_e_unif_comp hψ.continuous hLcpt (hfc.mono hLD) hunifL)
      · have h := sp_f2_integrableOn_mul_beta hLcpt (a := fun _ => (1 : ℂ)) continuousOn_const
          (hdA n 1) (hdA n I) hfxL hfyL
        simpa using h
      · exact sp_f2_integrableOn_mul_beta hLcpt (hPsimcont m).continuousOn (hdA n 1) (hdA n I)
          hfxL hfyL
      · exact sp_f2_integrableOn_mul_beta hLcpt (hPsicont.mono hLD) (hdA n 1) (hdA n I) hfxL hfyL
    have hlim2 : Tendsto (fun m => ∫ z in L, A n z * BP m z) atTop
        (𝓝 (∫ z in L, A n z * BQ z)) := by
      refine sp_e_beta_tendsto (L := L) (vx := fx) (vy := fy) (ux := sp_psiX ψ f fx)
        (uy := sp_psiX ψ f fy) (uxm := fun m => sp_psiX ψ (fm m) (fun w => fderiv ℝ (fm m) w 1))
        (uym := fun m => sp_psiX ψ (fm m) (fun w => fderiv ℝ (fm m) w I)) (a := A n)
        hfxL hfyL hpsiXL hpsiYL hpsiXm hpsiYm (hAbd n) (hAcont n).aestronglyMeasurable ?_ ?_
      · exact sp_e_psiX_tendsto hLcpt hψ (hfc.mono hLD) hunifL
          (fun m => (hfm2 m).continuous.continuousOn) hfxL (fun m => hdfm m 1) hconvfx
      · exact sp_e_psiX_tendsto hLcpt hψ (hfc.mono hLD) hunifL
          (fun m => (hfm2 m).continuous.continuousOn) hfyL (fun m => hdfm m I) hconvfy
    refine tendsto_nhds_unique (hlim1.add hlim2) ?_
    simp only [step3 n]
    exact tendsto_const_nhds
  -- STEP 5(a): the second integral tends to the left-hand side of the goal
  have hJ2 : ∀ n, (∫ z in L, A n z * BQ z) = ∫ z in K, gm n z * BQ z := by
    intro n
    have h1 : (∫ z in L, A n z * BQ z) = ∫ z in L, gm n z * BQ z := by
      refine setIntegral_congr_fun hLmeas (fun z hz => ?_)
      by_cases hzK : z ∈ K
      · simp only [hAdef, hccK z hzK, one_mul]
      · rw [hBQ0 z (hLD hz) hzK, mul_zero, mul_zero]
    rw [h1]
    refine sp_f2_setIntegral_subset hLmeas hKL (fun z hz hzK => ?_)
    rw [hBQ0 z (hLD hz) hzK, mul_zero]
  have hlimJ2 : Tendsto (fun n => ∫ z in L, A n z * BQ z) atTop
      (𝓝 (∫ z in D, g z * BQ z)) := by
    have hKint : (∫ z in K, g z * BQ z) = ∫ z in D, g z * BQ z := by
      refine (sp_f2_setIntegral_subset hDmeas hKD (fun z hz hzK => ?_)).symm
      rw [hBQ0 z hz hzK, mul_zero]
    have hlim : Tendsto (fun n => ∫ z in K, gm n z * BQ z) atTop
        (𝓝 (∫ z in K, g z * BQ z)) := by
      refine sp_tendsto_integral_mul_of_uniform ?_ (fun n => ?_) ?_ hunifK
      · have h := sp_f2_integrableOn_mul_beta hKcpt (a := fun _ => (1 : ℂ)) continuousOn_const
          hpsiXK hpsiYK hfxK hfyK
        simpa using h
      · exact sp_f2_integrableOn_mul_beta hKcpt (hgm2 n).continuous.continuousOn hpsiXK hpsiYK
          hfxK hfyK
      · exact sp_f2_integrableOn_mul_beta hKcpt (hgc.mono hKD) hpsiXK hpsiYK hfxK hfyK
    rw [hKint] at hlim
    exact hlim.congr fun n => (hJ2 n).symm
  -- STEP 5(b): the first integral tends to zero
  have hJ1 : ∀ n, (∫ z in L, Psi z * BA n z) = ∫ z in L, Psi z * cc z * Bg n z := by
    intro n
    refine setIntegral_congr_fun hLmeas (fun z hz => ?_)
    have hexp : BA n z = gm n z * Bcc z + cc z * Bg n z :=
      sp_beta_mul (a := cc) (b := gm n) (vx := fx) (vy := fy)
        (hcc2.differentiable (by norm_num) z) ((hgm2 n).differentiable (by norm_num) z)
    have hz1 : Psi z * (gm n z * Bcc z) = 0 := by
      by_cases hzK : z ∈ K
      · rw [hBcc0 z hzK, mul_zero, mul_zero]
      · rw [hPsi0 z (hLD hz) hzK, zero_mul]
    rw [hexp, mul_add, hz1, zero_add]
    ring
  have hlimJ1 : Tendsto (fun n => ∫ z in L, Psi z * BA n z) atTop (𝓝 0) := by
    have hbd : ∃ M : ℝ, ∀ z, ‖Psi z * cc z‖ ≤ M := by
      refine ⟨Mp, fun z => ?_⟩
      have h1 : ‖Psi z‖ ≤ Mp := hMp (f z)
      calc ‖Psi z * cc z‖ = ‖Psi z‖ * ‖cc z‖ := norm_mul _ _
        _ ≤ Mp * 1 := mul_le_mul h1 (hccbd z) (norm_nonneg _) (le_trans (norm_nonneg _) h1)
        _ = Mp := mul_one Mp
    have hmeas : AEStronglyMeasurable (fun z => Psi z * cc z) (volume.restrict L) :=
      ((hPsicont.mono hLD).mul hcccont.continuousOn).aestronglyMeasurable hLmeas
    have hlim := sp_e_beta_tendsto (L := L) (vx := fx) (vy := fy) (ux := gx) (uy := gy)
      (uxm := fun n w => fderiv ℝ (gm n) w 1) (uym := fun n w => fderiv ℝ (gm n) w I)
      (a := fun z => Psi z * cc z) hfxL hfyL hgxL hgyL (fun n => hdgm n 1) (fun n => hdgm n I)
      hbd hmeas hconvgx hconvgy
    have hlim2 : Tendsto (fun n => ∫ z in L, Psi z * BA n z) atTop
        (𝓝 (∫ z in L, Psi z * cc z * sp_beta gx gy fx fy z)) :=
      hlim.congr fun n => (hJ1 n).symm
    have hzero : (∫ z in L, Psi z * cc z * sp_beta gx gy fx fy z) = 0 := by
      refine integral_eq_zero_of_ae ?_
      have hf1 : ∀ᵐ z ∂(volume.restrict L), genDzbar fx fy z = μ z * genDz fx fy z :=
        ae_restrict_of_ae_restrict_of_subset hLD hfb
      have hg1 : ∀ᵐ z ∂(volume.restrict L), genDzbar gx gy z = μ z * genDz gx gy z :=
        ae_restrict_of_ae_restrict_of_subset hLD hgb
      filter_upwards [hf1, hg1] with z h1 h2
      simp only [Pi.zero_apply, sp_beta, h1, h2]
      ring
    rwa [hzero] at hlim2
  -- putting the two limits together
  have hfinal : (0 : ℂ) = 0 + ∫ z in D, g z * BQ z := by
    refine tendsto_nhds_unique ?_ (hlimJ1.add hlimJ2)
    simp only [step4]
    exact tendsto_const_nhds
  rw [zero_add] at hfinal
  have hgoal : (∫ z in D, g z * sp_beta (fun w => fderiv ℝ ψ (f w) (fx w))
      (fun w => fderiv ℝ ψ (f w) (fy w)) fx fy z) = ∫ z in D, g z * BQ z := rfl
  exact hgoal.trans hfinal.symm

/-! ### The targets -/

-- (the first target follows)

/-- §13.2: if `g` is any `L₂` generalized solution and `f` an `L₂` generalized homeomorphic
solution of the same Beltrami equation in `D`, then `g ∘ f⁻¹` is holomorphic in `f(D)`.

Proved (2026-09-22) by a weak-formulation argument that never uses the derivatives of `f⁻¹`: for a `C²`
test function `ψ` on `f(D)`, the change of variables through `f` (Lusin's property (N) for `W^{1,2}`
homeomorphisms) turns `∫ (g∘f⁻¹) ∂_w̄ψ` into `∫_D g · (Ψ_z̄ f_z − Ψ_z f_z̄)` with `Ψ = ψ∘f`, which vanishes by
the integration-by-parts identity `∫ β(u, f) = 0` for `C²_c` functions `u` (`sp_a_integral_beta_eq_zero`)
applied to smooth approximants and the two Beltrami equations; then a Weyl lemma by mollification
(`sp_w_differentiableOn_of_weak`). -/
theorem similarity_comp_inv_holomorphic {f g μ : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) {k : ℝ}
    (hk : k < 1) (hμ : IsBeltramiCoeff μ D k) (hf : IsGenHomeoSolution f μ D 2)
    (hg : IsGenSolution g μ D 2) :
    DifferentiableOn ℂ (g ∘ Function.invFunOn f D) (f '' D) := by
  obtain ⟨hfh, fx, fy, hfd, hfb⟩ := hf
  obtain ⟨gx, gy, hgd, hgb⟩ := hg
  have hU : IsOpen (f '' D) := isOpen_image_of_continuousOn_injOn hD hfh.1 hfh.2.1
  have hgc : ContinuousOn g D := by
    obtain ⟨-, gn, hgnC1, hgnU, -⟩ := id hgd
    exact hgnU.continuousOn (Filter.Frequently.of_forall fun n => (hgnC1 n).continuousOn)
  have hleft : ∀ z ∈ D, Function.invFunOn f D (f z) = z := hfh.2.1.leftInvOn_invFunOn
  have hmaps : MapsTo (Function.invFunOn f D) (f '' D) D := by
    rintro w ⟨z, hz, rfl⟩
    rw [hleft z hz]
    exact hz
  have hFc : ContinuousOn (g ∘ Function.invFunOn f D) (f '' D) := hgc.comp hfh.2.2.2 hmaps
  refine sp_w_weyl hU hFc ?_
  intro ψ hψ hcψ hsψ
  rw [sp_c_change_of_variables hk hD hμ.2 hfh hfd hfb
    (fun w => (g ∘ Function.invFunOn f D) w * dzbar ψ w)]
  have key : ∫ z in D, (jacobian f z : ℂ) * ((g ∘ Function.invFunOn f D) (f z) * dzbar ψ (f z))
      = ∫ z in D, g z * sp_beta (fun w => fderiv ℝ ψ (f w) (fx w))
          (fun w => fderiv ℝ ψ (f w) (fy w)) fx fy z := by
    refine setIntegral_congr_ae hD.measurableSet ?_
    filter_upwards [(ae_restrict_iff' hD.measurableSet).1
      (cr_p_differentiable_ae hD (by norm_num : (1 : ℝ≥0∞) ≤ 2) hfh hfd)] with z hz hzD
    obtain ⟨hdz, hx, hy⟩ := hz hzD
    rw [Function.comp_apply, hleft z hzD, ← sp_chain_algebra hdz hx hy]
    ring
  rw [key]
  exact sp_e_integral_eq_zero hD hfh hfd hgd hfb hgb hψ hcψ hsψ

/-! ### same_dilatation_conformal — helpers -/

-- (the target follows)

/-- §13.2: two quasiconformal maps with the same complex characteristic differ by a conformal
map: `g = φ ∘ f`.

Proved (2026-09-22): `φ := g ∘ f⁻¹` is holomorphic on `f(D)` by the similarity principle
(`similarity_comp_inv_holomorphic`), injective because `f` and `g` are, and maps `f(D)` onto `g(D)`. -/
theorem same_dilatation_conformal {f g μ : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) {k : ℝ}
    (hk : k < 1) (hμ : IsBeltramiCoeff μ D k) (hf : IsGenHomeoSolution f μ D 2)
    (hg : IsGenHomeoSolution g μ D 2) :
    ∃ φ : ℂ → ℂ, IsConformalOnto φ (f '' D) (g '' D) ∧ ∀ z ∈ D, g z = φ (f z) := by
  have hfi : InjOn f D := hf.1.2.1
  have hleft : ∀ z ∈ D, Function.invFunOn f D (f z) = z := hfi.leftInvOn_invFunOn
  refine ⟨g ∘ Function.invFunOn f D,
    ⟨similarity_comp_inv_holomorphic hD hk hμ hf hg.2, ?_, ?_⟩, ?_⟩
  · intro w₁ hw₁ w₂ hw₂ h
    obtain ⟨z₁, hz₁, rfl⟩ := hw₁
    obtain ⟨z₂, hz₂, rfl⟩ := hw₂
    simp only [Function.comp_apply, hleft z₁ hz₁, hleft z₂ hz₂] at h
    exact congrArg f (hg.1.2.1 hz₁ hz₂ h)
  · apply Set.Subset.antisymm
    · rintro w ⟨v, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, by rw [Function.comp_apply, hleft z hz]⟩
    · rintro w ⟨z, hz, rfl⟩
      exact ⟨f z, ⟨z, hz, rfl⟩, by rw [Function.comp_apply, hleft z hz]⟩
  · intro z hz
    rw [Function.comp_apply, hleft z hz]

/-- **Theorem 13.2** (相似原理, similarity principle).  Let `w` be any `L₂` generalized solution of
`∂_{z̄} w = μ ∂_z w` in `D`, and `χ` the global homeomorphic solution of the equation with
coefficient `μ` extended by `0` outside `D`.  Then `w = φ ∘ χ` for a holomorphic `φ` on `χ(D)`.

Proved (2026-09-22): restrict `χ` to `D` (where `D.indicator μ = μ`) and apply
`similarity_comp_inv_holomorphic`; `φ := w ∘ χ⁻¹`.  The hypotheses `hDb` and `hχs` are not needed. -/
theorem thm13_2_similarity {w χ μ : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) {k : ℝ} (hk : k < 1) (hμ : IsBeltramiCoeff μ D k)
    (hw : IsGenSolution w μ D 2) (hχ : IsGenHomeoSolution χ (D.indicator μ) univ 2)
    (hχs : χ '' univ = univ) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ (χ '' D) ∧ ∀ z ∈ D, w z = φ (χ z) := by
  obtain ⟨hχh, cx, cy, hcd, hcb⟩ := hχ
  have hinj : InjOn χ D := hχh.2.1.mono (subset_univ D)
  have hleft : ∀ z ∈ D, Function.invFunOn χ D (χ z) = z := hinj.leftInvOn_invFunOn
  have heq : ∀ v ∈ χ '' D, Function.invFunOn χ D v = Function.invFunOn χ univ v := by
    rintro v ⟨z, hz, rfl⟩
    rw [hleft z hz]
    exact hχh.2.1 (mem_univ z) (mem_univ _) (Function.invFunOn_eq ⟨z, mem_univ z, rfl⟩).symm
  have hχhD : IsHomeomorphOnto χ D (χ '' D) := by
    refine ⟨hχh.1.mono (subset_univ D), hinj, rfl, ?_⟩
    exact (hχh.2.2.2.mono (image_mono (subset_univ D))).congr heq
  have hcdD : HasGenPartials χ cx cy D 2 := by
    obtain ⟨hloc, cn, hcnC1, hcnU, hcnConv⟩ := hcd
    exact ⟨fun C _ hCc => hloc C (subset_univ _) hCc, cn, fun n => (hcnC1 n).mono (subset_univ _),
      hcnU.mono (subset_univ _), fun C _ hCc => hcnConv C (subset_univ _) hCc⟩
  have hcbD : ∀ᵐ z ∂(volume.restrict D), genDzbar cx cy z = μ z * genDz cx cy z := by
    have h1 : ∀ᵐ z ∂(volume.restrict D), genDzbar cx cy z = (D.indicator μ) z * genDz cx cy z := by
      rw [Measure.restrict_univ] at hcb
      exact ae_restrict_of_ae hcb
    filter_upwards [h1, ae_restrict_mem hD.measurableSet] with z hz hzD
    rwa [Set.indicator_of_mem hzD] at hz
  refine ⟨w ∘ Function.invFunOn χ D, ?_, ?_⟩
  · exact similarity_comp_inv_holomorphic hD hk hμ ⟨hχhD, cx, cy, hcdD, hcbD⟩ hw
  · intro z hz
    rw [Function.comp_apply, hleft z hz]

/-! ### Consequences of Theorem 13.2 — helpers -/


/-! ### Restriction helpers -/

/-- A Beltrami coefficient restricts to a subdomain. -/
theorem gs_isBeltramiCoeff_mono {μ : ℂ → ℂ} {D D' : Set ℂ} {k : ℝ} (hμ : IsBeltramiCoeff μ D k)
    (hD' : D' ⊆ D) : IsBeltramiCoeff μ D' k := by
  have hle : volume.restrict D' ≤ volume.restrict D := Measure.restrict_mono hD' le_rfl
  exact ⟨hμ.1.mono_measure hle, hμ.2.filter_mono (ae_mono hle)⟩

/-- A generalized solution restricts to a subdomain. -/
theorem gs_isGenSolution_mono {w μ : ℂ → ℂ} {D D' : Set ℂ} {p : ℝ≥0∞} (hw : IsGenSolution w μ D p)
    (hD' : D' ⊆ D) : IsGenSolution w μ D' p := by
  obtain ⟨g, h, ⟨hloc, fn, hfnC1, hfnU, hfnConv⟩, hbe⟩ := hw
  refine ⟨g, h, ⟨fun C hCD' hCc => hloc C (hCD'.trans hD') hCc, fn,
    fun n => (hfnC1 n).mono hD', hfnU.mono hD',
    fun C hCD' hCc => hfnConv C (hCD'.trans hD') hCc⟩, ?_⟩
  exact hbe.filter_mono (ae_mono (Measure.restrict_mono hD' le_rfl))

/-- A generalized solution is continuous. -/
theorem gs_continuousOn {w μ : ℂ → ℂ} {D : Set ℂ} {p : ℝ≥0∞} (hw : IsGenSolution w μ D p) :
    ContinuousOn w D := by
  obtain ⟨g, h, ⟨-, fn, hfnC1, hfnU, -⟩, -⟩ := hw
  exact hfnU.continuousOn (Filter.Frequently.of_forall fun n => (hfnC1 n).continuousOn)

/-- The indicator of a ball inside `D` is a compactly supported Beltrami coefficient. -/
theorem gs_indicator_isCompactBeltramiCoeff {μ : ℂ → ℂ} {D : Set ℂ} {k : ℝ} (hk₀ : 0 ≤ k)
    (hμ : IsBeltramiCoeff μ D k) {z₀ : ℂ} {r : ℝ} (hBD : ball z₀ r ⊆ D) :
    IsCompactBeltramiCoeff ((ball z₀ r).indicator μ) k := by
  have hB : IsBeltramiCoeff μ (ball z₀ r) k := gs_isBeltramiCoeff_mono hμ hBD
  refine ⟨⟨?_, ?_⟩, ⟨‖z₀‖ + r, fun z hz => ?_⟩⟩
  · rw [Measure.restrict_univ, aestronglyMeasurable_indicator_iff measurableSet_ball]
    exact hB.1
  · rw [Measure.restrict_univ]
    filter_upwards [(ae_restrict_iff' measurableSet_ball).1 hB.2] with z hz
    by_cases hzB : z ∈ ball z₀ r
    · rw [Set.indicator_of_mem hzB]
      exact hz hzB
    · rw [Set.indicator_of_notMem hzB, norm_zero]
      exact hk₀
  · refine Set.indicator_of_notMem (fun hzB => ?_) _
    rw [mem_ball, dist_eq_norm] at hzB
    have h1 : ‖z‖ - ‖z₀‖ ≤ ‖z - z₀‖ := norm_sub_norm_le z z₀
    linarith

/-! ### The local representation -/

/-- **Local representation.**  Near every point of `D` a generalized solution factors as `φ ∘ χ`
with `χ` a homeomorphism of the plane and `φ` holomorphic. -/
theorem gs_local_repr {w μ : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμ : IsBeltramiCoeff μ D k) (hw : IsGenSolution w μ D 2) {z₀ : ℂ} (hz₀ : z₀ ∈ D) :
    ∃ (r : ℝ) (χ φ : ℂ → ℂ), 0 < r ∧ ball z₀ r ⊆ D ∧ Continuous χ ∧ Function.Injective χ ∧
      IsOpenMap χ ∧ DifferentiableOn ℂ φ (χ '' ball z₀ r) ∧
      ∀ z ∈ ball z₀ r, w z = φ (χ z) := by
  obtain ⟨r, hr, hBD⟩ := Metric.isOpen_iff.1 hD z₀ hz₀
  have hνc : IsCompactBeltramiCoeff ((ball z₀ r).indicator μ) k :=
    gs_indicator_isCompactBeltramiCoeff hk₀ hμ hBD
  obtain ⟨χ, hχKQC, hχsurj, hχdilat, -⟩ := thm12_2 hk₀ hk hνc
  have hhom : IsHomeomorphOnto χ univ (χ '' univ) := hχKQC.2.2.1
  have hcont : Continuous χ := continuousOn_univ.1 hhom.1
  have hinj : Function.Injective χ := Set.injOn_univ.1 hhom.2.1
  have hopen : IsOpenMap χ := fun V hV =>
    isOpen_image_of_continuousOn_injOn hV hcont.continuousOn fun _ _ _ _ hxy => hinj hxy
  have hχgen : IsGenHomeoSolution χ ((ball z₀ r).indicator μ) univ 2 := by
    obtain ⟨hh, g, h, hgp, hbe⟩ := (thm10_2_genHomeoSolution_of_isKQC hχKQC).2
    refine ⟨hh, g, h, hgp, ?_⟩
    rw [Measure.restrict_univ] at hbe ⊢
    filter_upwards [hbe, hχdilat] with z h1 h2
    rw [h1, h2]
  obtain ⟨φ, hφ, hrepr⟩ :=
    thm13_2_similarity (D := ball z₀ r) isOpen_ball Metric.isBounded_ball hk
      (gs_isBeltramiCoeff_mono hμ hBD) (gs_isGenSolution_mono hw hBD) hχgen hχsurj
  exact ⟨r, χ, φ, hr, hBD, hcont, hinj, hopen, hφ, hrepr⟩

/-! ### Globalization -/

/-- A generalized solution on a connected domain that is constant near one point is constant. -/
theorem gs_const_of_eventually_const {w μ : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hDc : IsConnected D) {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : IsBeltramiCoeff μ D k)
    (hw : IsGenSolution w μ D 2) {z₁ : ℂ} (hz₁ : z₁ ∈ D) (hconst : ∀ᶠ z in 𝓝 z₁, w z = w z₁) :
    ∀ z ∈ D, w z = w z₁ := by
  obtain ⟨T, hTmem⟩ : ∃ T : Set ℂ, ∀ z : ℂ, z ∈ T ↔ ∀ᶠ y in 𝓝 z, w y = w z₁ :=
    ⟨{z : ℂ | ∀ᶠ y in 𝓝 z, w y = w z₁}, fun _ => Iff.rfl⟩
  -- `T` is open: the witnessing open set for `z` works for each of its own points.
  have hTopen : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨V, hVsub, hVopen, hzV⟩ := _root_.eventually_nhds_iff.mp ((hTmem z).mp hz)
    rw [_root_.mem_nhds_iff]
    exact ⟨V, fun y hy =>
      (hTmem y).mpr (_root_.eventually_nhds_iff.mpr ⟨V, hVsub, hVopen, hy⟩), hVopen, hzV⟩
  -- `D \ T` is open: via the local representation and the identity theorem.
  have hDTopen : IsOpen (D \ T) := by
    rw [Metric.isOpen_iff]
    rintro z ⟨hzD, hzT⟩
    obtain ⟨r, χ, φ, hr, hBD, hχc, -, hχo, hφ, hrep⟩ := gs_local_repr hD hk₀ hk hμ hw hzD
    refine ⟨r, hr, fun y hy => ⟨hBD hy, fun hyT => hzT ?_⟩⟩
    have hUopen : IsOpen (χ '' ball z r) := hχo _ Metric.isOpen_ball
    have hUconn : IsPreconnected (χ '' ball z r) :=
      isPreconnected_ball.image χ hχc.continuousOn
    obtain ⟨W, hWsub, hWopen, hyW⟩ := _root_.eventually_nhds_iff.mp ((hTmem y).mp hyT)
    have hW'open : IsOpen (W ∩ ball z r) := hWopen.inter Metric.isOpen_ball
    have hev : ∀ᶠ u in 𝓝 (χ y), φ u = w z₁ :=
      _root_.eventually_nhds_iff.mpr
        ⟨χ '' (W ∩ ball z r), by
          rintro _ ⟨v, hv, rfl⟩
          rw [← hrep v hv.2]
          exact hWsub v hv.1, hχo _ hW'open, ⟨y, ⟨hyW, hy⟩, rfl⟩⟩
    have hana : AnalyticOnNhd ℂ φ (χ '' ball z r) := hφ.analyticOnNhd hUopen
    have heq : EqOn φ (fun _ => w z₁) (χ '' ball z r) :=
      AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hana analyticOnNhd_const hUconn
        (z₀ := χ y) ⟨y, hy, rfl⟩ hev
    refine (hTmem z).mpr (_root_.eventually_nhds_iff.mpr
      ⟨ball z r, fun v hv => ?_, Metric.isOpen_ball, mem_ball_self hr⟩)
    rw [hrep v hv]
    exact heq ⟨v, hv, rfl⟩
  -- `D ⊆ T` by preconnectedness of `D`.
  have hsub : D ⊆ T := by
    by_contra hcon
    obtain ⟨z, hzD, hzT⟩ := Set.not_subset.mp hcon
    have hcover : D ⊆ T ∪ (D \ T) := by
      intro u hu
      by_cases h : u ∈ T
      · exact Or.inl h
      · exact Or.inr ⟨hu, h⟩
    obtain ⟨u, _huD, huT, huDT⟩ :=
      hDc.isPreconnected T (D \ T) hTopen hDTopen hcover ⟨z₁, hz₁, (hTmem z₁).mpr hconst⟩
        ⟨z, hzD, hzD, hzT⟩
    exact absurd huT huDT.2
  exact fun z hzD => ((hTmem z).mp (hsub hzD)).self_of_nhds

/-! ### The three consequences of Theorem 13.2 -/

/-- Helper: a Beltrami coefficient on a nonempty open set forces `0 ≤ k`, since `‖μ z‖ ≤ k`
a.e. on a set of positive measure. -/
theorem gs_t_nonneg_of_isBeltramiCoeff {μ : ℂ → ℂ} {D : Set ℂ} {k : ℝ} (hD : IsOpen D)
    (hDne : D.Nonempty) (hμ : IsBeltramiCoeff μ D k) : 0 ≤ k := by
  by_contra hkneg0
  have hkneg : k < 0 := not_le.mp hkneg0
  have h0 : (volume.restrict D) {z : ℂ | ¬ ‖μ z‖ ≤ k} = 0 := ae_iff.mp hμ.2
  have huniv : {z : ℂ | ¬ ‖μ z‖ ≤ k} = Set.univ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, not_le]
    exact hkneg.trans_le (norm_nonneg _)
  rw [huniv, Measure.restrict_apply_univ] at h0
  exact (hD.measure_pos volume hDne).ne' h0

-- (the target follows)

/-- Consequence of Theorem 13.2: the maximum modulus principle for generalized solutions.

Proved (2026-09-22) from the similarity principle: near a point the solution is `φ ∘ χ` with `φ`
holomorphic (`gs_local_repr`), so the maximum modulus principle makes `φ` constant there, and a
connectedness argument (`gs_const_of_eventually_const`) propagates it to `D`. -/
theorem genSolution_maximum_principle {w μ : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hDc : IsConnected D) {k : ℝ} (hk : k < 1) (hμ : IsBeltramiCoeff μ D k)
    (hw : IsGenSolution w μ D 2) {z₀ : ℂ} (hz₀ : z₀ ∈ D) (hmax : IsMaxOn (fun z => ‖w z‖) D z₀) :
    ∃ c : ℂ, ∀ z ∈ D, w z = c := by
  have hk₀ : 0 ≤ k := gs_t_nonneg_of_isBeltramiCoeff hD hDc.nonempty hμ
  obtain ⟨r, χ, φ, hr, hBD, hχc, hχinj, hχopen, hφ, hrep⟩ := gs_local_repr hD hk₀ hk hμ hw hz₀
  have hz₀r : z₀ ∈ ball z₀ r := Metric.mem_ball_self hr
  have hO : IsOpen (χ '' ball z₀ r) := hχopen _ Metric.isOpen_ball
  have hP : IsPreconnected (χ '' ball z₀ r) := isPreconnected_ball.image χ hχc.continuousOn
  have hmem : χ z₀ ∈ χ '' ball z₀ r := ⟨z₀, hz₀r, rfl⟩
  have hmaxφ : IsMaxOn (norm ∘ φ) (χ '' ball z₀ r) (χ z₀) := by
    rintro v ⟨y, hy, rfl⟩
    have h1 : ‖w y‖ ≤ ‖w z₀‖ := hmax (hBD hy)
    have h2 : ‖φ (χ y)‖ ≤ ‖φ (χ z₀)‖ := by
      rw [← hrep y hy, ← hrep z₀ hz₀r]; exact h1
    exact h2
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hP hO hφ hmem hmaxφ
  refine ⟨w z₀, gs_const_of_eventually_const hD hDc hk₀ hk hμ hw hz₀ ?_⟩
  filter_upwards [Metric.isOpen_ball.mem_nhds hz₀r] with y hy
  have : φ (χ y) = φ (χ z₀) := heq ⟨y, hy, rfl⟩
  rw [hrep y hy, hrep z₀ hz₀r, this]

/-- Consequence of Theorem 13.2: the zeros of a non-trivial generalized solution are isolated.

Proved (2026-09-22): locally `w = φ ∘ χ` with `φ` holomorphic and `χ` a homeomorphism of the
plane (`gs_local_repr`), so the principle of isolated zeros for `φ` transfers to `w`; if `φ`
vanished near a point, `w` would vanish identically on `D`. -/
theorem genSolution_isolated_zeros {w μ : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D)
    {k : ℝ} (hk : k < 1) (hμ : IsBeltramiCoeff μ D k) (hw : IsGenSolution w μ D 2)
    (hne : ∃ z ∈ D, w z ≠ 0) : ∀ z₀ ∈ D, ∀ᶠ z in 𝓝[≠] z₀, w z ≠ 0 := by
  have hk₀ : 0 ≤ k := gs_t_nonneg_of_isBeltramiCoeff hD hDc.nonempty hμ
  intro z₀ hz₀
  obtain ⟨r, χ, φ, hr, hBD, hχc, hχinj, hχopen, hφ, hrep⟩ := gs_local_repr hD hk₀ hk hμ hw hz₀
  have hz₀r : z₀ ∈ ball z₀ r := Metric.mem_ball_self hr
  have hO : IsOpen (χ '' ball z₀ r) := hχopen _ Metric.isOpen_ball
  have hmem : χ z₀ ∈ χ '' ball z₀ r := ⟨z₀, hz₀r, rfl⟩
  have hA : AnalyticOnNhd ℂ φ (χ '' ball z₀ r) := hφ.analyticOnNhd hO
  rcases (hA _ hmem).eventually_eq_zero_or_eventually_ne_zero with hzero | hnz
  · exfalso
    have hw0 : w z₀ = 0 := by
      rw [hrep z₀ hz₀r]; exact hzero.self_of_nhds
    have hpb : ∀ᶠ y in 𝓝 z₀, φ (χ y) = 0 := (hχc.tendsto z₀).eventually hzero
    have hconst : ∀ᶠ z in 𝓝 z₀, w z = w z₀ := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz₀r, hpb] with y hy hy2
      rw [hrep y hy, hy2, hw0]
    have hall := gs_const_of_eventually_const hD hDc hk₀ hk hμ hw hz₀ hconst
    obtain ⟨z, hzD, hzne⟩ := hne
    exact hzne (by rw [hall z hzD, hw0])
  · have hχtend : Filter.Tendsto χ (𝓝[≠] z₀) (𝓝[≠] (χ z₀)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((hχc.tendsto z₀).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      intro hcon
      exact hy (hχinj hcon)
    have h1 : ∀ᶠ y in 𝓝[≠] z₀, φ (χ y) ≠ 0 := hχtend.eventually hnz
    have h2 : ∀ᶠ y in 𝓝[≠] z₀, y ∈ ball z₀ r :=
      nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hz₀r)
    filter_upwards [h1, h2] with y hy1 hy2
    rw [hrep y hy2]
    exact hy1

/-- Consequence of Theorem 13.2: a non-constant generalized solution is an open map.

Proved (2026-09-22): locally `w = φ ∘ χ` (`gs_local_repr`); the open mapping theorem for the
holomorphic `φ` (`AnalyticOnNhd.is_constant_or_isOpen`) applies because `w` is not constant on
the connected `D`, and `χ` is an open map. -/
theorem genSolution_open_mapping {w μ : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D)
    {k : ℝ} (hk : k < 1) (hμ : IsBeltramiCoeff μ D k) (hw : IsGenSolution w μ D 2)
    (hnc : ¬ ∃ c : ℂ, ∀ z ∈ D, w z = c) : ∀ U ⊆ D, IsOpen U → IsOpen (w '' U) := by
  have hk₀ : 0 ≤ k := gs_t_nonneg_of_isBeltramiCoeff hD hDc.nonempty hμ
  intro U hUD hUopen
  rw [isOpen_iff_mem_nhds]
  rintro v ⟨z, hzU, rfl⟩
  obtain ⟨r, χ, φ, hr, hBD, hχc, hχinj, hχopen, hφ, hrep⟩ :=
    gs_local_repr hD hk₀ hk hμ hw (hUD hzU)
  have hzr : z ∈ ball z r := Metric.mem_ball_self hr
  have hO : IsOpen (χ '' ball z r) := hχopen _ Metric.isOpen_ball
  have hP : IsPreconnected (χ '' ball z r) := isPreconnected_ball.image χ hχc.continuousOn
  have hA : AnalyticOnNhd ℂ φ (χ '' ball z r) := hφ.analyticOnNhd hO
  rcases hA.is_constant_or_isOpen hP with ⟨c, hc⟩ | hopen
  · exfalso
    refine hnc ⟨w z, gs_const_of_eventually_const hD hDc hk₀ hk hμ hw (hUD hzU) ?_⟩
    filter_upwards [Metric.isOpen_ball.mem_nhds hzr] with y hy
    rw [hrep y hy, hrep z hzr, hc _ ⟨y, hy, rfl⟩, hc _ ⟨z, hzr, rfl⟩]
  · have hVopen : IsOpen (U ∩ ball z r) := hUopen.inter Metric.isOpen_ball
    have hVsub : U ∩ ball z r ⊆ ball z r := Set.inter_subset_right
    have himg : IsOpen (φ '' (χ '' (U ∩ ball z r))) :=
      hopen _ (Set.image_mono hVsub) (hχopen _ hVopen)
    have heq : w '' (U ∩ ball z r) = φ '' (χ '' (U ∩ ball z r)) := by
      rw [Set.image_image]
      exact Set.image_congr fun y hy => hrep y (hVsub hy)
    have hopenwV : IsOpen (w '' (U ∩ ball z r)) := by rw [heq]; exact himg
    have hmemwV : w z ∈ w '' (U ∩ ball z r) := ⟨z, ⟨hzU, hzr⟩, rfl⟩
    exact Filter.mem_of_superset (hopenwV.mem_nhds hmemwV)
      (Set.image_mono Set.inter_subset_left)

/-! ## §13.3 Boundary correspondence and uniqueness -/

/-! ### Theorem 13.4 — helpers -/


/-! ### The `ExtPlane` ↔ `ℂ` convergence bridge -/

/-- The trace of the extended-plane neighbourhood filter at a finite point. -/
theorem uq_nhdsWithin_toExt_coe (Ω : Set ℂ) (z₀ : ℂ) :
    𝓝[toExt Ω] ((z₀ : ℂ) : ExtPlane) = Filter.map ((↑) : ℂ → ExtPlane) (𝓝[Ω] z₀) := by
  exact OnePoint.nhdsWithin_coe_image Ω z₀

/-- The trace of the extended-plane neighbourhood filter at infinity. -/
theorem uq_nhdsWithin_toExt_extInf (Ω : Set ℂ) :
    𝓝[toExt Ω] (extInf : ExtPlane)
      = Filter.map ((↑) : ℂ → ExtPlane) (Filter.comap norm atTop ⊓ 𝓟 Ω) := by
  have hpure : pure (extInf : ExtPlane) ⊓ 𝓟 (toExt Ω) = ⊥ := by
    rw [← Filter.empty_mem_iff_bot]
    refine Filter.mem_inf_of_inter (s := ({extInf} : Set ExtPlane)) (t := toExt Ω)
      (mem_pure.2 rfl) (Filter.mem_principal_self _) ?_
    rintro p ⟨hp1, hp2⟩
    rw [mem_singleton_iff] at hp1
    exact absurd (hp1 ▸ hp2) OnePoint.infty_notMem_image_coe
  rw [nhdsWithin, OnePoint.nhds_infty_eq, show 𝓟 (toExt Ω)
      = Filter.map ((↑) : ℂ → ExtPlane) (𝓟 Ω) from (Filter.map_principal).symm,
    inf_sup_right, ← Filter.map_inf OnePoint.coe_injective]
  rw [show Filter.map ((↑) : ℂ → ExtPlane) (𝓟 Ω) = 𝓟 (toExt Ω) from Filter.map_principal,
    hpure, sup_bot_eq, comap_norm_atTop, cobounded_eq_cocompact, ← coclosedCompact_eq_cocompact]

/-- Continuity of the extension at a finite boundary point gives a limit of the map itself. -/
theorem uq_tendsto_of_continuousWithinAt_coe {φ : ℂ → ℂ} {Ω : Set ℂ} {Φ : ExtPlane → ExtPlane}
    {z₀ w₀ : ℂ} (hΦ : ∀ z ∈ Ω, Φ (z : ExtPlane) = ((φ z : ℂ) : ExtPlane))
    (hcont : ContinuousWithinAt Φ (closure (toExt Ω)) ((z₀ : ℂ) : ExtPlane))
    (hval : Φ ((z₀ : ℂ) : ExtPlane) = ((w₀ : ℂ) : ExtPlane)) :
    Tendsto φ (𝓝[Ω] z₀) (𝓝 w₀) := by
  have h1 := hcont.mono (subset_closure : toExt Ω ⊆ closure (toExt Ω))
  rw [ContinuousWithinAt, hval, uq_nhdsWithin_toExt_coe, tendsto_map'_iff] at h1
  have h2 : Tendsto (fun z => ((φ z : ℂ) : ExtPlane)) (𝓝[Ω] z₀) (𝓝 ((w₀ : ℂ) : ExtPlane)) := by
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz using hΦ z hz
  exact (OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff).2 h2

/-- Continuity of the extension at infinity gives blow-up of the map itself. -/
theorem uq_tendsto_norm_atTop_of_continuousWithinAt_extInf {φ : ℂ → ℂ} {Ω : Set ℂ}
    {Φ : ExtPlane → ExtPlane} (hΦ : ∀ z ∈ Ω, Φ (z : ExtPlane) = ((φ z : ℂ) : ExtPlane))
    (hcont : ContinuousWithinAt Φ (closure (toExt Ω)) extInf) (hval : Φ extInf = extInf) :
    Tendsto (fun w => ‖φ w‖) (Filter.comap norm atTop ⊓ 𝓟 Ω) atTop := by
  have h1 := hcont.mono (subset_closure : toExt Ω ⊆ closure (toExt Ω))
  rw [ContinuousWithinAt, hval, uq_nhdsWithin_toExt_extInf, tendsto_map'_iff] at h1
  have h2 : Tendsto (((↑) : ℂ → ExtPlane) ∘ φ)
      (Filter.comap norm atTop ⊓ 𝓟 Ω) (𝓝 (extInf : ExtPlane)) := by
    refine h1.congr' ?_
    filter_upwards [Filter.mem_inf_of_right (Filter.mem_principal_self Ω)] with z hz using hΦ z hz
  rw [tendsto_norm_atTop_iff_cobounded]
  have h3 := Filter.tendsto_comap_iff.2 h2
  rwa [OnePoint.comap_coe_nhds_infty, coclosedCompact_eq_cocompact,
    ← cobounded_eq_cocompact] at h3

/-! ### Automorphisms of the upper half-plane -/

/-- An automorphism of `upperHalf` whose extension fixes `0`, `∞` and one more real point is the
identity. -/
theorem uq_upperHalf_eq_id_of_fixed {G : ℂ → ℂ} {Ĝ : ExtPlane → ExtPlane}
    (hG : IsConformalOnto G upperHalf upperHalf)
    (hGe : IsHomeoExtension G upperHalf upperHalf Ĝ)
    (h0 : Ĝ (((0 : ℂ)) : ExtPlane) = (((0 : ℂ)) : ExtPlane)) (hinf : Ĝ extInf = extInf)
    {t : ℝ} (ht : t ≠ 0) (htfix : Ĝ ((((t : ℝ) : ℂ)) : ExtPlane) = ((((t : ℝ) : ℂ)) : ExtPlane)) :
    ∀ z ∈ upperHalf, G z = z := by
  have hmem : ∀ x : ℝ, ((((x : ℝ) : ℂ)) : ExtPlane) ∈ closure (toExt upperHalf) := by
    intro x
    rw [scExt_closure_toExt_upperHalf]
    exact Or.inl ⟨((x : ℝ) : ℂ), by simp, rfl⟩
  have hmeminf : (extInf : ExtPlane) ∈ closure (toExt upperHalf) := by
    rw [scExt_closure_toExt_upperHalf]; exact Or.inr rfl
  have hG0 : Tendsto G (𝓝[upperHalf] (0 : ℂ)) (𝓝 0) := by
    refine uq_tendsto_of_continuousWithinAt_coe (w₀ := 0) hGe.1 ?_ h0
    have := hGe.2.1 _ (hmem 0)
    simpa using this
  have hGinf : Tendsto (fun w => ‖G w‖) (Filter.comap norm atTop ⊓ 𝓟 upperHalf) atTop :=
    uq_tendsto_norm_atTop_of_continuousWithinAt_extInf hGe.1 (hGe.2.1 _ hmeminf) hinf
  obtain ⟨lam, hlam, heq⟩ := upperHalf_automorphism_eq_dilate hG hG0 hGinf
  -- the third fixed point forces `lam = 1`
  have hGt : Tendsto G (𝓝[upperHalf] ((t : ℝ) : ℂ)) (𝓝 (((t : ℝ) : ℂ))) :=
    uq_tendsto_of_continuousWithinAt_coe hGe.1 (hGe.2.1 _ (hmem t)) htfix
  have hGt' : Tendsto G (𝓝[upperHalf] ((t : ℝ) : ℂ)) (𝓝 ((lam : ℂ) * ((t : ℝ) : ℂ))) := by
    have hc : Tendsto (fun z : ℂ => (lam : ℂ) * z) (𝓝[upperHalf] ((t : ℝ) : ℂ))
        (𝓝 ((lam : ℂ) * ((t : ℝ) : ℂ))) :=
      ((continuous_const.mul continuous_id).tendsto _).mono_left nhdsWithin_le_nhds
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz using (heq z hz).symm
  have hne : (𝓝[upperHalf] (((t : ℝ) : ℂ))).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, scExt_closure_upperHalf]
    simp
  have hlam1 : lam = 1 := by
    have := tendsto_nhds_unique hGt hGt'
    have h2 : ((t : ℝ) : ℂ) = (lam : ℂ) * ((t : ℝ) : ℂ) := this
    have htC : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht
    have h3 : ((lam : ℂ) - 1) * ((t : ℝ) : ℂ) = 0 := by linear_combination -h2
    have h4 : (lam : ℂ) - 1 = 0 := (mul_eq_zero.1 h3).resolve_right htC
    have h5 : (lam : ℂ) = 1 := by linear_combination h4
    exact_mod_cast h5
  intro z hz
  rw [heq z hz, hlam1]
  simp

/-! ### Transport of Jordan domains and the uniformizer -/

/-- Case split on `ℂ̄ = ℂ ∪ {∞}`. -/
theorem uq_j_eq_infty_or_coe (p : ExtPlane) : p = extInf ∨ ∃ z : ℂ, p = (z : ExtPlane) := by
  induction p using OnePoint.rec with
  | infty => exact Or.inl rfl
  | coe z => exact Or.inr ⟨z, rfl⟩

/-- A subset of the sphere avoiding `∞` is the extension of its finite part. -/
theorem uq_j_toExt_preimage_coe {S : Set ExtPlane} (h : extInf ∉ S) :
    toExt (((↑) : ℂ → ExtPlane) ⁻¹' S) = S := by
  ext y
  induction y using OnePoint.rec with
  | infty => exact iff_of_false (extInf_notMem_toExt _) h
  | coe z => rw [coe_mem_toExt_iff, mem_preimage]

/-- The determinant of `z ↦ 1/(z - w₀)`. -/
theorem uq_j_inv_det (w₀ : ℂ) : (0 : ℂ) * (-w₀) - 1 * 1 ≠ 0 := by norm_num

/-- The Möbius homeomorphism `z ↦ 1/(z - w₀)` of `ℂ̄` sends `w₀` to `∞`. -/
theorem uq_j_mobiusInv_apply_self (w₀ : ℂ) :
    mobiusHomeomorph 0 1 1 (-w₀) (uq_j_inv_det w₀) ((w₀ : ℂ) : ExtPlane) = extInf := by
  rw [mobiusHomeomorph_apply]
  exact mobiusExt_coe_of_eq_zero (by ring)

/-- Away from `w₀` the homeomorphism `z ↦ 1/(z - w₀)` is given by `mobiusFn`. -/
theorem uq_j_mobiusInv_coe {w₀ z : ℂ} (h : z ≠ w₀) :
    mobiusHomeomorph 0 1 1 (-w₀) (uq_j_inv_det w₀) ((z : ℂ) : ExtPlane)
      = ((mobiusFn 0 1 1 (-w₀) z : ℂ) : ExtPlane) := by
  have hden : (1 : ℂ) * z + (-w₀) ≠ 0 := by
    rw [show (1 : ℂ) * z + (-w₀) = z - w₀ by ring]
    exact sub_ne_zero.mpr h
  rw [mobiusHomeomorph_apply]
  exact mobiusExt_coe hden

/-- A homeomorphism of the sphere carries Jordan curves to Jordan curves. -/
theorem uq_isJordanCurve_image (e : ExtPlane ≃ₜ ExtPlane) {C : Set ExtPlane}
    (hC : IsJordanCurve C) : IsJordanCurve (e '' C) := by
  obtain ⟨γ, hγc, hγi, hγr⟩ := hC
  exact ⟨e ∘ γ, e.continuous.comp hγc, e.injective.comp hγi, by rw [range_comp, hγr]⟩

/-- A homeomorphism of the sphere carries Jordan domains to Jordan domains. -/
theorem uq_isJordanDomain_image (e : ExtPlane ≃ₜ ExtPlane) {D D' : Set ℂ}
    (hD : IsJordanDomain D) (h : e '' toExt D = toExt D') : IsJordanDomain D' := by
  obtain ⟨hDo, hDc, hDJ⟩ := hD
  have hopen : IsOpen (toExt D') := by
    rw [← h]; exact e.isOpenMap _ (OnePoint.isOpen_image_coe.2 hDo)
  have hD'o : IsOpen D' := OnePoint.isOpen_image_coe.1 hopen
  refine ⟨hD'o, ?_, ?_⟩
  · have h0 : IsConnected (toExt D) := hDc.image _ OnePoint.continuous_coe.continuousOn
    have h1 : IsConnected (toExt D') := by
      rw [← h]; exact h0.image _ e.continuous.continuousOn
    refine ⟨?_, ?_⟩
    · obtain ⟨p, hp⟩ := h1.nonempty
      obtain ⟨z, hz, -⟩ := hp
      exact ⟨z, hz⟩
    · exact (OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image).1 h1.2
  · rw [← h, ← e.image_frontier]
    exact uq_isJordanCurve_image e hDJ

/-- The extended closure of a Jordan domain is not the whole sphere. -/
theorem uq_exists_notMem_closure {Ω : Set ℂ} (hΩ : IsJordanDomain Ω) :
    ∃ p : ExtPlane, p ∉ closure (toExt Ω) := by
  obtain ⟨hΩo, hΩc, hΩJ⟩ := hΩ
  by_contra hcon
  push Not at hcon
  have hclosure : closure (toExt Ω) = univ := eq_univ_of_forall hcon
  have hopen : IsOpen (toExt Ω) := isOpen_toExt_iff.mpr hΩo
  -- the boundary curve is the whole complement of `Ω`
  have hfr : frontier (toExt Ω) = (toExt Ω)ᶜ := by
    rw [hopen.frontier_eq, hclosure, ← compl_eq_univ_diff]
  obtain ⟨z₀, hz₀⟩ := hΩc.nonempty
  have hz₀fr : ((z₀ : ℂ) : ExtPlane) ∉ frontier (toExt Ω) := by
    rw [hfr]
    simp only [mem_compl_iff, not_not]
    exact coe_mem_toExt_iff.mpr hz₀
  -- push `z₀` to `∞` by a Möbius homeomorphism
  have hinfJ : extInf ∉
      (mobiusHomeomorph 0 1 1 (-z₀) (uq_j_inv_det z₀)) '' frontier (toExt Ω) := by
    rintro ⟨q, hq, hqe⟩
    rw [← uq_j_mobiusInv_apply_self z₀] at hqe
    exact hz₀fr ((mobiusHomeomorph 0 1 1 (-z₀) (uq_j_inv_det z₀)).injective hqe ▸ hq)
  obtain ⟨C₃, hC₃eq⟩ : ∃ C : Set ℂ,
      toExt C = (mobiusHomeomorph 0 1 1 (-z₀) (uq_j_inv_det z₀)) '' frontier (toExt Ω) :=
    ⟨_, uq_j_toExt_preimage_coe hinfJ⟩
  have hC₃J : IsJordanCurve (toExt C₃) := by
    rw [hC₃eq]; exact uq_isJordanCurve_image _ hΩJ
  -- the Jordan curve theorem for `C₃`
  obtain ⟨A, B, hA, hB, hAc, hBc, hAB, hAC, hBC, huniv, hAb, -⟩ :=
    jordan_curve_theorem_complex_bounded hC₃J
  have hcover : ∀ z : ℂ, z ∈ A ∨ z ∈ B ∨ z ∈ C₃ := by
    intro z
    have hz : z ∈ A ∪ B ∪ C₃ := huniv ▸ mem_univ z
    rcases hz with (h | h) | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h)]
  have hcompl : C₃ᶜ = A ∪ B := by
    ext z
    constructor
    · intro hz
      rcases hcover z with h | h | h
      exacts [Or.inl h, Or.inr h, absurd h hz]
    · rintro (h | h)
      exacts [Set.disjoint_left.1 hAC h, Set.disjoint_left.1 hBC h]
  have hBcompl : Bᶜ = A ∪ C₃ := by
    ext z
    constructor
    · intro hz
      rcases hcover z with h | h | h
      exacts [Or.inl h, absurd h hz, Or.inr h]
    · rintro (h | h)
      exacts [fun hzB => Set.disjoint_left.1 hAB h hzB, fun hzB => Set.disjoint_left.1 hBC hzB h]
  -- the image of `Ω` is the whole complement of the curve, hence connected …
  have himgΩ : (toExt C₃)ᶜ = (mobiusHomeomorph 0 1 1 (-z₀) (uq_j_inv_det z₀)) '' toExt Ω := by
    rw [hC₃eq, hfr,
      Set.image_compl_eq (mobiusHomeomorph 0 1 1 (-z₀) (uq_j_inv_det z₀)).bijective, compl_compl]
  have hconn : IsConnected ((toExt C₃)ᶜ) := by
    rw [himgΩ]
    exact (hΩc.image _ OnePoint.continuous_coe.continuousOn).image _
      (mobiusHomeomorph 0 1 1 (-z₀) (uq_j_inv_det z₀)).continuous.continuousOn
  -- … yet it splits into two disjoint nonempty open pieces
  have hsplit : (toExt C₃)ᶜ = toExt A ∪ (toExt B ∪ {extInf}) := by
    rw [compl_toExt, hcompl, toExt_union, union_assoc]
  have hAopen : IsOpen (toExt A) := isOpen_toExt_iff.mpr hA
  have hBopen : IsOpen (toExt B ∪ {extInf}) := by
    have hmem : extInf ∈ toExt B ∪ {extInf} := Or.inr rfl
    have hpre : ((↑) : ℂ → ExtPlane) ⁻¹' (toExt B ∪ {extInf}) = B := by
      ext z
      simp only [mem_preimage, mem_union, coe_mem_toExt_iff, mem_singleton_iff]
      exact ⟨fun h => h.elim id fun h' => absurd h' (OnePoint.coe_ne_infty z), Or.inl⟩
    rw [OnePoint.isOpen_iff_of_mem hmem, hpre]
    refine ⟨hB.isClosed_compl, Metric.isCompact_of_isClosed_isBounded hB.isClosed_compl ?_⟩
    rw [hBcompl]
    exact hAb.union (isCompact_of_isJordanCurve_toExt hC₃J).isBounded
  obtain ⟨a, ha⟩ := hAc.nonempty
  have hne1 : ((toExt C₃)ᶜ ∩ toExt A).Nonempty :=
    ⟨(a : ExtPlane), by rw [hsplit]; exact Or.inl (coe_mem_toExt_iff.mpr ha),
      coe_mem_toExt_iff.mpr ha⟩
  have hne2 : ((toExt C₃)ᶜ ∩ (toExt B ∪ {extInf})).Nonempty :=
    ⟨extInf, extInf_mem_compl_toExt C₃, Or.inr rfl⟩
  obtain ⟨y, -, hyA, hyB⟩ :=
    hconn.isPreconnected (toExt A) (toExt B ∪ {extInf}) hAopen hBopen hsplit.subset hne1 hne2
  rcases hyB with hyB | hyB
  · obtain ⟨z, hzA, rfl⟩ := hyA
    exact Set.disjoint_left.1 hAB hzA (coe_mem_toExt_iff.mp hyB)
  · rw [mem_singleton_iff] at hyB
    subst hyB
    exact extInf_notMem_toExt A hyA

/-- The Möbius homeomorphism `z ↦ 1/(z - w₀)` transports `toExt U` to the extension of the image
of `U`, provided `w₀ ∉ U`. -/
theorem uq_j_image_toExt {w₀ : ℂ} {U : Set ℂ} (hU : ∀ z ∈ U, z ≠ w₀) :
    (mobiusHomeomorph 0 1 1 (-w₀) (uq_j_inv_det w₀)) '' toExt U
      = toExt (mobiusFn 0 1 1 (-w₀) '' U) := by
  ext y
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [uq_j_mobiusInv_coe (hU z hz)]
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨(z : ExtPlane), ⟨z, hz, rfl⟩, uq_j_mobiusInv_coe (hU z hz)⟩

/-- `z ↦ 1/(z - w₀)` maps a set avoiding `w₀` conformally onto its image. -/
theorem uq_j_isConformalOnto_mobiusInv {w₀ : ℂ} {U : Set ℂ} (hU : ∀ z ∈ U, z ≠ w₀) :
    IsConformalOnto (mobiusFn 0 1 1 (-w₀)) U (mobiusFn 0 1 1 (-w₀) '' U) := by
  have hden : ∀ z ∈ U, (1 : ℂ) * z + (-w₀) ≠ 0 := by
    intro z hz
    rw [show (1 : ℂ) * z + (-w₀) = z - w₀ by ring]
    exact sub_ne_zero.mpr (hU z hz)
  refine ⟨?_, ?_, rfl⟩
  · intro z hz
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (0 : ℂ) * w + 1) z := by fun_prop
    have h2 : DifferentiableAt ℂ (fun w : ℂ => (1 : ℂ) * w + (-w₀)) z := by fun_prop
    exact (h1.div h2 (hden z hz)).differentiableWithinAt
  · intro z₁ h₁ z₂ h₂ heq
    have e₁ := mobiusFn_inv_apply (uq_j_inv_det w₀) (hden z₁ h₁)
    have e₂ := mobiusFn_inv_apply (uq_j_inv_det w₀) (hden z₂ h₂)
    rw [← e₁, ← e₂, heq]

/-- The Möbius homeomorphism of `ℂ̄` is a homeomorphic extension of `z ↦ 1/(z - w₀)`. -/
theorem uq_j_isHomeoExtension_mobiusInv {w₀ : ℂ} {U : Set ℂ} (hU : ∀ z ∈ U, z ≠ w₀) :
    IsHomeoExtension (mobiusFn 0 1 1 (-w₀)) U (mobiusFn 0 1 1 (-w₀) '' U)
      (mobiusHomeomorph 0 1 1 (-w₀) (uq_j_inv_det w₀)) := by
  refine ⟨fun z hz => uq_j_mobiusInv_coe (hU z hz),
    (mobiusHomeomorph 0 1 1 (-w₀) (uq_j_inv_det w₀)).continuous.continuousOn,
    (mobiusHomeomorph 0 1 1 (-w₀) (uq_j_inv_det w₀)).injective.injOn, ?_⟩
  rw [(mobiusHomeomorph 0 1 1 (-w₀) (uq_j_inv_det w₀)).image_closure, uq_j_image_toExt hU]

/-- **Uniformization of an arbitrary Jordan domain**: every Jordan domain, bounded or not, has a
conformal map onto `upperHalf` with a homeomorphic extension. -/
theorem uq_exists_uniformizer {Ω : Set ℂ} (hΩ : IsJordanDomain Ω) :
    ∃ ψ : ℂ → ℂ, IsConformalOnto ψ Ω upperHalf ∧
      ∃ Ψ : ExtPlane → ExtPlane, IsHomeoExtension ψ Ω upperHalf Ψ := by
  obtain ⟨p, hp⟩ := uq_exists_notMem_closure hΩ
  rcases uq_j_eq_infty_or_coe p with rfl | ⟨w₀, rfl⟩
  · -- `Ω` is already bounded
    exact exists_conformalOnto_upperHalf_of_isJordanDomain hΩ
      (isBounded_of_extInf_notMem_closure_toExt hp)
  · -- send the omitted finite point `w₀` to `∞` and reduce to the bounded case
    have hne : ∀ z ∈ Ω, z ≠ w₀ := by
      intro z hz hzw
      exact hp (subset_closure (by rw [← hzw]; exact coe_mem_toExt_iff.mpr hz))
    have hconf : IsConformalOnto (mobiusFn 0 1 1 (-w₀)) Ω (mobiusFn 0 1 1 (-w₀) '' Ω) :=
      uq_j_isConformalOnto_mobiusInv hne
    have hext : IsHomeoExtension (mobiusFn 0 1 1 (-w₀)) Ω (mobiusFn 0 1 1 (-w₀) '' Ω)
        (mobiusHomeomorph 0 1 1 (-w₀) (uq_j_inv_det w₀)) :=
      uq_j_isHomeoExtension_mobiusInv hne
    have hJD : IsJordanDomain (mobiusFn 0 1 1 (-w₀) '' Ω) :=
      uq_isJordanDomain_image _ hΩ (uq_j_image_toExt hne)
    have hbdd : Bornology.IsBounded (mobiusFn 0 1 1 (-w₀) '' Ω) := by
      refine isBounded_of_extInf_notMem_closure_toExt ?_
      rw [← uq_j_image_toExt hne,
        ← (mobiusHomeomorph 0 1 1 (-w₀) (uq_j_inv_det w₀)).image_closure]
      rintro ⟨q, hq, hqe⟩
      rw [← uq_j_mobiusInv_apply_self w₀] at hqe
      exact hp ((mobiusHomeomorph 0 1 1 (-w₀) (uq_j_inv_det w₀)).injective hqe ▸ hq)
    obtain ⟨ψ', hψ'conf, Ψ', hΨ'ext⟩ :=
      exists_conformalOnto_upperHalf_of_isJordanDomain hJD hbdd
    exact ⟨ψ' ∘ mobiusFn 0 1 1 (-w₀), hψ'conf.comp hconf,
      Ψ' ∘ ⇑(mobiusHomeomorph 0 1 1 (-w₀) (uq_j_inv_det w₀)),
      IsHomeoExtension.comp hΨ'ext hext hconf.mapsTo⟩

/-! ### The key uniqueness lemma -/

/-- A point of the extended boundary of `ℍ` is either a real number or `∞`. -/
theorem uq_k_frontier_cases {p : ExtPlane} (hp : p ∈ frontier (toExt upperHalf)) :
    (∃ x : ℝ, p = (((x : ℝ) : ℂ) : ExtPlane)) ∨ p = extInf := by
  rw [scExt_frontier_toExt_upperHalf] at hp
  rcases hp with h | h
  · obtain ⟨z, hz, hzeq⟩ := h
    refine Or.inl ⟨z.re, ?_⟩
    rw [← hzeq]
    congr 1
    exact Complex.ext_iff.2 ⟨rfl, hz⟩
  · exact Or.inr h

/-- Three distinct points of `∂ℍ` (taken in `ℂ̄`) can be moved by a real Möbius transformation of
positive determinant onto `0`, `∞` and a nonzero real point. -/
theorem uq_k_normalize {r : Fin 3 → ExtPlane} (hr : Function.Injective r)
    (hrf : ∀ i, r i ∈ frontier (toExt upperHalf)) :
    ∃ a b c d t : ℝ, 0 < a * d - b * c ∧ t ≠ 0 ∧
      (∃ i, mobiusExt (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) (r i) = (((0 : ℂ)) : ExtPlane)) ∧
      (∃ i, mobiusExt (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) (r i) = extInf) ∧
      (∃ i, mobiusExt (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) (r i) = ((((t : ℝ) : ℂ)) : ExtPlane)) := by
  classical
  have hcls : ∀ i, (∃ x : ℝ, r i = (((x : ℝ) : ℂ) : ExtPlane)) ∨ r i = extInf := fun i =>
    uq_k_frontier_cases (hrf i)
  by_cases hinf : ∃ i, r i = extInf
  · obtain ⟨i₀, hi₀⟩ := hinf
    have hidx : ∀ i : Fin 3, i + 1 ≠ i ∧ i + 2 ≠ i ∧ i + 1 ≠ i + 2 := by decide
    obtain ⟨hA, hB, hC⟩ := hidx i₀
    have hrne : ∀ j, j ≠ i₀ → r j ≠ extInf := fun j hj hjinf => hj (hr (hjinf.trans hi₀.symm))
    obtain ⟨u, hu⟩ := (hcls (i₀ + 1)).resolve_right (hrne _ hA)
    obtain ⟨v, hv⟩ := (hcls (i₀ + 2)).resolve_right (hrne _ hB)
    have huv : u ≠ v := by
      intro hcon
      apply hC
      apply hr
      rw [hu, hv, hcon]
    have hden : (0 : ℝ) * u + 1 ≠ 0 := by norm_num
    have hden' : (0 : ℝ) * v + 1 ≠ 0 := by norm_num
    refine ⟨1, -u, 0, 1, (1 * v + -u) / (0 * v + 1), by norm_num, ?_, ⟨i₀ + 1, ?_⟩, ⟨i₀, ?_⟩,
      ⟨i₀ + 2, ?_⟩⟩
    · refine div_ne_zero ?_ hden'
      intro hcon
      exact huv (by linarith)
    · rw [hu, mobiusExt_ofReal_coe hden, show (1 : ℝ) * u + -u = 0 from by ring, zero_div]
      norm_num
    · rw [hi₀]
      exact mobiusExt_infty_of_eq (by norm_num)
    · rw [hv, mobiusExt_ofReal_coe hden']
  · have hinf2 : ∀ i, r i ≠ extInf := fun i hi => hinf ⟨i, hi⟩
    have hxex : ∀ i, ∃ s : ℝ, r i = (((s : ℝ) : ℂ) : ExtPlane) := fun i =>
      (hcls i).resolve_right (hinf2 i)
    choose x hxeq using hxex
    have hxne : ∀ i j : Fin 3, i ≠ j → x i ≠ x j := by
      intro i j hij hcon
      apply hij
      apply hr
      rw [hxeq i, hxeq j, hcon]
    have key : ∀ i j k : Fin 3, x j < x i → x k ≠ x i → x k ≠ x j →
        ∃ a b c d t : ℝ, 0 < a * d - b * c ∧ t ≠ 0 ∧
          (∃ l, mobiusExt (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) (r l) = (((0 : ℂ)) : ExtPlane)) ∧
          (∃ l, mobiusExt (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) (r l) = extInf) ∧
          (∃ l, mobiusExt (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) (r l)
            = ((((t : ℝ) : ℂ)) : ExtPlane)) := by
      intro i j k hij hki hkj
      have hdi : (1 : ℝ) * x i + -x j ≠ 0 := by
        intro hcon
        linarith
      have hdk : (1 : ℝ) * x k + -x j ≠ 0 := by
        intro hcon
        exact hkj (by linarith)
      refine ⟨1, -x i, 1, -x j, (1 * x k + -x i) / (1 * x k + -x j), by linarith, ?_,
        ⟨i, ?_⟩, ⟨j, ?_⟩, ⟨k, ?_⟩⟩
      · refine div_ne_zero ?_ hdk
        intro hcon
        exact hki (by linarith)
      · rw [hxeq i, mobiusExt_ofReal_coe hdi, show (1 : ℝ) * x i + -x i = 0 from by ring,
          zero_div]
        norm_num
      · rw [hxeq j, mobiusExt_ofReal_coe_of_eq_zero (show (1 : ℝ) * x j + -x j = 0 from by ring)]
      · rw [hxeq k, mobiusExt_ofReal_coe hdk]
    rcases lt_trichotomy (x 0) (x 1) with hlt | heq | hgt
    · exact key 1 0 2 hlt (hxne 2 1 (by decide)) (hxne 2 0 (by decide))
    · exact absurd heq (hxne 0 1 (by decide))
    · exact key 0 1 2 hgt (hxne 2 0 (by decide)) (hxne 2 1 (by decide))

/-- A real Möbius map of positive determinant is an automorphism of `ℍ`, with `mobiusExt` as its
homeomorphic extension. -/
theorem uq_k_mobius_auto {a b c d : ℝ} (h : 0 < a * d - b * c) :
    IsConformalOnto (mobiusFn (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ)) upperHalf upperHalf ∧
      IsHomeoExtension (mobiusFn (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ)) upperHalf upperHalf
        (mobiusExt (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ)) := by
  have hdetC : ((a : ℂ) * (d : ℂ) - (b : ℂ) * (c : ℂ)) ≠ 0 := by exact_mod_cast h.ne'
  refine ⟨isConformalOnto_mobius_upperHalf h, ?_⟩
  have hext := IsHomeoExtension.comp_homeomorph (scExt_isHomeoExtension_id upperHalf)
    (mapsTo_id upperHalf) (mobiusHomeomorph (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) hdetC)
    (g := mobiusFn (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ)) (W := upperHalf)
    (fun w hw => mobiusExt_coe (mobiusFn_den_ne_zero_real h.ne' hw))
    (mobiusExt_image_toExt_upperHalf h)
  exact hext

/-- On `ℍ`, the inverse real Möbius map undoes a real Möbius map of positive determinant. -/
theorem uq_k_mobiusFn_leftInv {a b c d : ℝ} (h : 0 < a * d - b * c) {z : ℂ}
    (hz : z ∈ upperHalf) :
    mobiusFn (d : ℂ) (-(b : ℂ)) (-(c : ℂ)) (a : ℂ)
      (mobiusFn (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) z) = z := by
  have hdetC : ((a : ℂ) * (d : ℂ) - (b : ℂ) * (c : ℂ)) ≠ 0 := by exact_mod_cast h.ne'
  have hden : (c : ℂ) * z + (d : ℂ) ≠ 0 := mobiusFn_den_ne_zero_real h.ne' hz
  have hw : mobiusFn (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) z ∈ upperHalf := mobiusFn_mem_upperHalf h hz
  have hdet' : (0 : ℝ) < d * a - -b * -c := by
    have hq : d * a - -b * -c = a * d - b * c := by ring
    rw [hq]; exact h
  have hden2 := mobiusFn_den_ne_zero_real (a := d) (b := -b) (c := -c) (d := a) hdet'.ne' hw
  simp only [Complex.ofReal_neg] at hden2
  have key := mobiusExt_inv_apply hdetC ((z : ℂ) : ExtPlane)
  rw [mobiusExt_coe hden, mobiusExt_coe hden2] at key
  exact OnePoint.coe_injective key

/-- An automorphism of `ℍ` whose homeomorphic extension fixes three distinct points of `∂ℍ` is the
identity. -/
theorem uq_k_finish {G : ℂ → ℂ} {H : ExtPlane → ExtPlane}
    (hG : IsConformalOnto G upperHalf upperHalf)
    (hGe : IsHomeoExtension G upperHalf upperHalf H) {r : Fin 3 → ExtPlane}
    (hr : Function.Injective r) (hrf : ∀ i, r i ∈ frontier (toExt upperHalf))
    (hfix : ∀ i, H (r i) = r i) : ∀ z ∈ upperHalf, G z = z := by
  obtain ⟨a, b, c, d, t, hdet, ht, ⟨i₀, hi₀⟩, ⟨i₁, hi₁⟩, ⟨i₂, hi₂⟩⟩ := uq_k_normalize hr hrf
  have hdetC : ((a : ℂ) * (d : ℂ) - (b : ℂ) * (c : ℂ)) ≠ 0 := by exact_mod_cast hdet.ne'
  have hdet' : (0 : ℝ) < d * a - -b * -c := by
    have hq : d * a - -b * -c = a * d - b * c := by ring
    rw [hq]; exact hdet
  obtain ⟨hmconf, hmext⟩ := uq_k_mobius_auto hdet
  obtain ⟨hm'conf, hm'ext⟩ := uq_k_mobius_auto hdet'
  simp only [Complex.ofReal_neg] at hm'conf hm'ext
  have hG'conf : IsConformalOnto (mobiusFn (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) ∘
      (G ∘ mobiusFn (d : ℂ) (-(b : ℂ)) (-(c : ℂ)) (a : ℂ))) upperHalf upperHalf :=
    hmconf.comp (hG.comp hm'conf)
  have hG'ext : IsHomeoExtension (mobiusFn (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) ∘
      (G ∘ mobiusFn (d : ℂ) (-(b : ℂ)) (-(c : ℂ)) (a : ℂ))) upperHalf upperHalf
      (mobiusExt (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) ∘
        (H ∘ mobiusExt (d : ℂ) (-(b : ℂ)) (-(c : ℂ)) (a : ℂ))) :=
    hmext.comp (hGe.comp hm'ext hm'conf.mapsTo) (hG.comp hm'conf).mapsTo
  have hfix' : ∀ i, mobiusExt (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ)
      (H (mobiusExt (d : ℂ) (-(b : ℂ)) (-(c : ℂ)) (a : ℂ)
        (mobiusExt (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) (r i))))
      = mobiusExt (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) (r i) := by
    intro i
    rw [mobiusExt_inv_apply hdetC, hfix i]
  have h0 : mobiusExt (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ)
      (H (mobiusExt (d : ℂ) (-(b : ℂ)) (-(c : ℂ)) (a : ℂ) (((0 : ℂ)) : ExtPlane)))
      = (((0 : ℂ)) : ExtPlane) := by
    rw [← hi₀]; exact hfix' i₀
  have hinfty : mobiusExt (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ)
      (H (mobiusExt (d : ℂ) (-(b : ℂ)) (-(c : ℂ)) (a : ℂ) extInf)) = extInf := by
    rw [← hi₁]; exact hfix' i₁
  have htf : mobiusExt (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ)
      (H (mobiusExt (d : ℂ) (-(b : ℂ)) (-(c : ℂ)) (a : ℂ) ((((t : ℝ) : ℂ)) : ExtPlane)))
      = ((((t : ℝ) : ℂ)) : ExtPlane) := by
    rw [← hi₂]; exact hfix' i₂
  have hid := uq_upperHalf_eq_id_of_fixed hG'conf hG'ext h0 hinfty ht htf
  intro z hz
  have hmz : mobiusFn (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) z ∈ upperHalf := hmconf.mapsTo hz
  have hkey : mobiusFn (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ)
      (G (mobiusFn (d : ℂ) (-(b : ℂ)) (-(c : ℂ)) (a : ℂ)
        (mobiusFn (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) z)))
      = mobiusFn (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) z := hid _ hmz
  rw [uq_k_mobiusFn_leftInv hdet hz] at hkey
  exact hmconf.2.1 (hG.mapsTo hz) hz hkey

/-- **Key uniqueness lemma.**  A conformal automorphism of a Jordan domain whose homeomorphic
extension fixes three distinct boundary points is the identity. -/
theorem uq_auto_eq_id {Ω : Set ℂ} (hΩ : IsJordanDomain Ω) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ Ω Ω) {Φ : ExtPlane → ExtPlane} (hΦ : IsHomeoExtension φ Ω Ω Φ)
    {q : Fin 3 → ExtPlane} (hq : Function.Injective q) (hqΩ : ∀ i, q i ∈ frontier (toExt Ω))
    (hfix : ∀ i, Φ (q i) = q i) : EqOn φ id Ω := by
  classical
  obtain ⟨ψ, hψ, Ψ, hΨ⟩ := uq_exists_uniformizer hΩ
  have hΩo : IsOpen Ω := hΩ.1
  have hψiconf : IsConformalOnto (Function.invFunOn ψ Ω) upperHalf Ω := hψ.symm hΩo
  have hΨiext : IsHomeoExtension (Function.invFunOn ψ Ω) upperHalf Ω
      (Function.invFunOn Ψ (closure (toExt Ω))) := isHomeoExtension_invFunOn hψ hΨ
  have hGconf : IsConformalOnto (ψ ∘ (φ ∘ Function.invFunOn ψ Ω)) upperHalf upperHalf :=
    hψ.comp (hφ.comp hψiconf)
  have hGext : IsHomeoExtension (ψ ∘ (φ ∘ Function.invFunOn ψ Ω)) upperHalf upperHalf
      (Ψ ∘ (Φ ∘ Function.invFunOn Ψ (closure (toExt Ω)))) :=
    hΨ.comp (hΦ.comp hΨiext hψiconf.mapsTo) (hφ.comp hψiconf).mapsTo
  have hqcl : ∀ i, q i ∈ closure (toExt Ω) := fun i => frontier_subset_closure (hqΩ i)
  have hrinj : Function.Injective fun i => Ψ (q i) := fun i j hij =>
    hq (hΨ.2.2.1 (hqcl i) (hqcl j) hij)
  have hrfr : ∀ i, Ψ (q i) ∈ frontier (toExt upperHalf) := by
    intro i
    rw [← IsHomeoExtension.image_frontier hΩo scExt_isOpen_upperHalf hψ.2.2 hΨ]
    exact mem_image_of_mem Ψ (hqΩ i)
  have hrfix : ∀ i, Ψ (Φ (Function.invFunOn Ψ (closure (toExt Ω)) (Ψ (q i)))) = Ψ (q i) := by
    intro i
    rw [hΨ.2.2.1.leftInvOn_invFunOn (hqcl i), hfix i]
  have hGid := uq_k_finish hGconf hGext hrinj hrfr hrfix
  intro z hz
  have hψz : ψ z ∈ upperHalf := hψ.mapsTo hz
  have hkey : ψ (φ (Function.invFunOn ψ Ω (ψ z))) = ψ z := hGid _ hψz
  rw [hψ.2.1.leftInvOn_invFunOn hz] at hkey
  exact hψ.2.1 (hφ.mapsTo hz) hz hkey

/-- The inverse of a homeomorphic extension of a homeomorphism is a homeomorphic extension of the
inverse. -/
theorem uq_isHomeoExtension_invFunOn {f : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hf : IsHomeomorphOnto f U V) {F : ExtPlane → ExtPlane} (hF : IsHomeoExtension f U V F) :
    IsHomeoExtension (Function.invFunOn f U) V U (Function.invFunOn F (closure (toExt U))) := by
  have _hUV : IsOpen U ∧ IsOpen V := ⟨hU, hV⟩
  obtain ⟨-, hfi, hfimg, -⟩ := hf
  obtain ⟨hF1, hF2, hF3, hF4⟩ := hF
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    have hwU : w ∈ f '' U := hfimg ▸ hw
    obtain ⟨z, hz, rfl⟩ := hwU
    have hzmem : ((z : ℂ) : ExtPlane) ∈ closure (toExt U) := subset_closure (mem_image_of_mem _ hz)
    have hFz : F ((z : ℂ) : ExtPlane) = ((f z : ℂ) : ExtPlane) := hF1 z hz
    rw [hfi.leftInvOn_invFunOn hz, ← hFz]
    exact hF3.leftInvOn_invFunOn hzmem
  · rw [← hF4]
    exact continuousOn_invFunOn_of_isClosed isClosed_closure hF2 hF3
  · rw [← hF4]
    intro a ha b hb hab
    calc a = F (Function.invFunOn F (closure (toExt U)) a) := (Function.invFunOn_eq ha).symm
      _ = F (Function.invFunOn F (closure (toExt U)) b) := by rw [hab]
      _ = b := Function.invFunOn_eq hb
  · rw [← hF4]
    exact hF3.leftInvOn_invFunOn.image_image

/-! ### The target -/

/-- Two quasiconformal maps of `D` onto the same image with the same complex dilatation differ by a
conformal automorphism of that image. -/
theorem uq_conformal_auto {f g : ℂ → ℂ} {D D' : Set ℂ} (hD : IsOpen D)
    (hf : IsQuasiconformal f D) (hg : IsQuasiconformal g D) (hfD : f '' D = D') (hgD : g '' D = D')
    (hμ : ∀ᵐ z ∂(volume.restrict D), complexDilatation f z = complexDilatation g z) :
    ∃ φ : ℂ → ℂ, IsConformalOnto φ D' D' ∧ ∀ z ∈ D, g z = φ (f z) := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨K', hK'⟩ := hg
  obtain ⟨hβf, hsolf⟩ := thm10_2_genHomeoSolution_of_isKQC hK
  obtain ⟨-, hsolg⟩ := thm10_2_genHomeoSolution_of_isKQC hK'
  have hK1 : (1 : ℝ) ≤ K := hK.2.1
  have hkpos : (0 : ℝ) < K + 1 := by linarith
  have hk : (K - 1) / (K + 1) < 1 := by
    rw [div_lt_one hkpos]
    linarith
  have hsolg' : IsGenHomeoSolution g (complexDilatation f) D 2 := by
    obtain ⟨hghom, gx, gy, hgp, hgae⟩ := hsolg
    refine ⟨hghom, gx, gy, hgp, ?_⟩
    filter_upwards [hgae, hμ] with z h1 h2
    rw [h2]
    exact h1
  obtain ⟨φ, hφ, hgφ⟩ := same_dilatation_conformal hD hk hβf hsolf hsolg'
  rw [hfD, hgD] at hφ
  exact ⟨φ, hφ, hgφ⟩

-- (the target follows)

/-- **Theorem 13.4** (唯一性定理): a quasiconformal map with given complex characteristic, of a
given Jordan domain onto another given Jordan domain, sending three given boundary points to
three given boundary points, is unique.

Proved (2026-09-23): `φ := g ∘ f⁻¹` is a CONFORMAL automorphism of `D'` by the similarity
principle (`same_dilatation_conformal`), and `G ∘ F⁻¹` extends it to a homeomorphism of the closed
domain fixing the three given boundary points; a conformal automorphism of a Jordan domain whose
extension fixes three boundary points is the identity (`uq_auto_eq_id`: uniformize to the upper
half-plane — `uq_exists_uniformizer`, valid for unbounded Jordan domains too — normalize two of
the fixed points to `0` and `∞` by a real Möbius map, and use that an automorphism of `ℍ` fixing
`0`, `∞` and one more real point is the identity). -/
theorem thm13_4_uniqueness {f g : ℂ → ℂ} {D D' : Set ℂ} (hD : IsJordanDomain D)
    (hD' : IsJordanDomain D') (hf : IsQuasiconformal f D) (hg : IsQuasiconformal g D)
    (hfD : f '' D = D') (hgD : g '' D = D')
    (hμ : ∀ᵐ z ∂(volume.restrict D), complexDilatation f z = complexDilatation g z)
    {F G : ExtPlane → ExtPlane} (hF : IsHomeoExtension f D D' F) (hG : IsHomeoExtension g D D' G)
    {p : Fin 3 → ExtPlane} (hp : Function.Injective p) (hpD : ∀ i, p i ∈ frontier (toExt D))
    (hFG : ∀ i, F (p i) = G (p i)) : EqOn f g D := by
  obtain ⟨φ, hφ, hgφ⟩ := uq_conformal_auto hD.1 hf hg hfD hgD hμ
  obtain ⟨K, hK⟩ := hf
  have hfh : IsHomeomorphOnto f D D' := by
    rw [← hfD]
    exact hK.2.2.1
  have hfi : InjOn f D := hfh.2.1
  have hFinvExt : IsHomeoExtension (Function.invFunOn f D) D' D
      (Function.invFunOn F (closure (toExt D))) :=
    uq_isHomeoExtension_invFunOn hD.1 hD'.1 hfh hF
  have hinvimg : Function.invFunOn f D '' D' = D := (isHomeomorphOnto_invFunOn hfh).2.2.1
  have hmaps : MapsTo (Function.invFunOn f D) D' D := by
    intro w hw
    have hmem : Function.invFunOn f D w ∈ Function.invFunOn f D '' D' := mem_image_of_mem _ hw
    rwa [hinvimg] at hmem
  have hcomp : IsHomeoExtension (g ∘ Function.invFunOn f D) D' D'
      (G ∘ Function.invFunOn F (closure (toExt D))) := hG.comp hFinvExt hmaps
  have hΦ : IsHomeoExtension φ D' D' (G ∘ Function.invFunOn F (closure (toExt D))) := by
    refine ⟨?_, hcomp.2.1, hcomp.2.2.1, hcomp.2.2.2⟩
    intro w hw
    have hwim : w ∈ f '' D := by
      rw [hfD]
      exact hw
    obtain ⟨z, hz, rfl⟩ := hwim
    rw [hcomp.1 (f z) hw]
    simp only [Function.comp_apply, hfi.leftInvOn_invFunOn hz]
    rw [hgφ z hz]
  have hpcl : ∀ i, p i ∈ closure (toExt D) := fun i => frontier_subset_closure (hpD i)
  have hqinj : Function.Injective (F ∘ p) := by
    intro i j hij
    simp only [Function.comp_apply] at hij
    exact hp (hF.2.2.1 (hpcl i) (hpcl j) hij)
  have hqfront : ∀ i, (F ∘ p) i ∈ frontier (toExt D') := by
    intro i
    have himf : F '' frontier (toExt D) = frontier (toExt D') :=
      hF.image_frontier hD.1 hD'.1 hfD
    rw [← himf]
    exact mem_image_of_mem F (hpD i)
  have hfix : ∀ i, (G ∘ Function.invFunOn F (closure (toExt D))) ((F ∘ p) i) = (F ∘ p) i := by
    intro i
    have h1 : Function.invFunOn F (closure (toExt D)) (F (p i)) = p i :=
      hF.2.2.1.leftInvOn_invFunOn (hpcl i)
    simp only [Function.comp_apply, h1]
    exact (hFG i).symm
  have hid : EqOn φ id D' := uq_auto_eq_id hD' hφ hΦ hqinj hqfront hfix
  intro z hz
  have hfz : f z ∈ D' := by
    rw [← hfD]
    exact mem_image_of_mem f hz
  rw [hgφ z hz, hid hfz]
  rfl

/-! ### Theorem 13.5 (plane uniqueness) — helpers -/

/-! ## Region 1: plane uniqueness (Theorem 13.5) -/

/-- A conformal bijection of the plane tends to `∞` at `∞`: the preimage of a compact set `K` lies
in the compact set `φ⁻¹(K)`, image of `K` under the continuous (holomorphic) inverse. -/
theorem nxU_tendsto_cocompact {φ : ℂ → ℂ} (hφ : IsConformalOnto φ univ univ) :
    Tendsto φ (cocompact ℂ) (cocompact ℂ) := by
  have hg := hφ.symm isOpen_univ
  have hgc : Continuous (Function.invFunOn φ univ) :=
    (differentiableOn_univ.mp hg.1).continuous
  have hleft : ∀ z, Function.invFunOn φ univ (φ z) = z := fun z =>
    hφ.2.1.leftInvOn_invFunOn (mem_univ z)
  rw [Filter.hasBasis_cocompact.tendsto_right_iff]
  intro K hK
  refine Filter.mem_cocompact.mpr ⟨Function.invFunOn φ univ '' K, hK.image hgc, fun z hz => ?_⟩
  intro hzK
  exact hz ⟨φ z, hzK, hleft z⟩

/-- An entire `φ` with `φ 0 = 0` and `φ z / z → L` at `∞` is `z ↦ L z`: `dslope φ 0` is entire and
tends to `L` at `∞`, so it is the constant `L` by Liouville (the same argument as
`entire_eq_add_const_of_tendsto_div` of `Lemmas/EntireLinearGrowth`, which S13 does not import). -/
theorem nxU_eq_mul_of_tendsto_div {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) (h0 : φ 0 = 0) {L : ℂ}
    (h : Tendsto (fun z => φ z / z) (cocompact ℂ) (𝓝 L)) : ∀ z, φ z = L * z := by
  have hd : Differentiable ℂ (dslope φ 0) := differentiableOn_univ.mp
    ((differentiableOn_dslope Filter.univ_mem).mpr hφ.differentiableOn)
  have heq : ∀ z, z ≠ 0 → dslope φ 0 z = φ z / z := by
    intro z hz
    rw [dslope_of_ne _ hz, slope_def_module, sub_zero, h0, sub_zero, smul_eq_mul, div_eq_inv_mul]
  have hne0 : {(0 : ℂ)}ᶜ ∈ cocompact ℂ :=
    Filter.mem_cocompact.mpr ⟨{0}, isCompact_singleton, subset_rfl⟩
  have hlim : Tendsto (dslope φ 0) (cocompact ℂ) (𝓝 L) := by
    refine h.congr' ?_
    filter_upwards [hne0] with z hz
    exact (heq z hz).symm
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · rw [h0, mul_zero]
  · have hz' := hd.apply_eq_of_tendsto_cocompact z hlim
    rw [heq z hz, div_eq_iff hz] at hz'
    exact hz'

/-- A conformal bijection of the plane fixing `0` is linear: `ψ(ζ) = 1/φ(1/ζ)` (with `0⁻¹ = 0`) is
an injective entire function (removable singularity at `0`, since `φ → ∞` at `∞`), so
`c = ψ'(0) ≠ 0`, `φ(z)/z → 1/c` at `∞`, and `φ z = z / c` by `nxU_eq_mul_of_tendsto_div`. -/
theorem nxU_entire_linear {φ : ℂ → ℂ} (hφ : IsConformalOnto φ univ univ) (h0 : φ 0 = 0) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ z, φ z = a * z := by
  have hφd : Differentiable ℂ φ := differentiableOn_univ.mp hφ.1
  have hinj : Function.Injective φ := injOn_univ.mp hφ.2.1
  have hne : ∀ z, z ≠ 0 → φ z ≠ 0 := fun z hz h => hz (hinj (h.trans h0.symm))
  set ψ : ℂ → ℂ := fun ζ => (φ ζ⁻¹)⁻¹ with hψ
  have hψ0 : ψ 0 = 0 := by simp [hψ, h0]
  have hψinj : Function.Injective ψ := by
    intro a b hab
    simp only [hψ, inv_inj] at hab
    exact inv_injective (hinj hab)
  have hψd : DifferentiableOn ℂ ψ (univ \ {0}) := by
    intro ζ hζ
    have hζ0 : ζ ≠ 0 := hζ.2
    have h1 : DifferentiableAt ℂ (fun ζ : ℂ => ζ⁻¹) ζ := differentiableAt_inv hζ0
    have h2 : DifferentiableAt ℂ φ ζ⁻¹ := hφd _
    have h3 : φ ζ⁻¹ ≠ 0 := hne _ (inv_ne_zero hζ0)
    exact ((h2.comp ζ h1).inv h3).differentiableWithinAt
  have hψc : ContinuousAt ψ 0 := by
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hψ0]
    have t1 : Tendsto (fun ζ : ℂ => ζ⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
      rw [← Metric.cobounded_eq_cocompact]
      exact Filter.tendsto_inv₀_nhdsNE_zero
    have t2 := (nxU_tendsto_cocompact hφ).comp t1
    have t3 : Tendsto (fun w : ℂ => w⁻¹) (cocompact ℂ) (𝓝 0) := by
      rw [← Metric.cobounded_eq_cocompact]
      exact Filter.tendsto_inv₀_cobounded
    exact t3.comp t2
  have hψD : Differentiable ℂ ψ := differentiableOn_univ.mp
    ((Complex.differentiableOn_compl_singleton_and_continuousAt_iff Filter.univ_mem).mp ⟨hψd, hψc⟩)
  set c := deriv ψ 0 with hc
  have hc0 : c ≠ 0 :=
    deriv_ne_zero_of_injOn isOpen_univ hψD.differentiableOn hψinj.injOn (mem_univ 0)
  have hslope : Tendsto (slope ψ 0) (𝓝[≠] 0) (𝓝 c) :=
    hasDerivAt_iff_tendsto_slope.mp (hψD 0).hasDerivAt
  have hlim : Tendsto (fun z => z / φ z) (cocompact ℂ) (𝓝 c) := by
    have t1 : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝[≠] 0) := by
      rw [← Metric.cobounded_eq_cocompact]
      exact Filter.tendsto_inv₀_cobounded'
    refine (hslope.comp t1).congr (fun z => ?_)
    simp only [Function.comp_apply, slope_def_module, hψ, inv_zero, h0, sub_zero, inv_inv,
      smul_eq_mul, div_eq_mul_inv]
  have hlim2 : Tendsto (fun z => φ z / z) (cocompact ℂ) (𝓝 c⁻¹) :=
    (hlim.inv₀ hc0).congr fun z => inv_div _ _
  exact ⟨c⁻¹, inv_ne_zero hc0, nxU_eq_mul_of_tendsto_div hφd h0 hlim2⟩

/-- A conformal bijection of the plane is affine. -/
theorem nx_entire_affine {φ : ℂ → ℂ} (hφ : IsConformalOnto φ univ univ) :
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ z, φ z = a * z + b := by
  have hφ₀ : IsConformalOnto (fun z => φ z - φ 0) univ univ := by
    refine ⟨hφ.1.sub (differentiableOn_const _), fun x _ y _ hxy => hφ.2.1 (mem_univ x)
      (mem_univ y) (sub_left_inj.mp hxy), ?_⟩
    refine eq_univ_of_forall fun w => ?_
    have hw : w + φ 0 ∈ φ '' univ := by
      rw [hφ.2.2]
      exact mem_univ _
    obtain ⟨z, -, hz⟩ := hw
    exact ⟨z, mem_univ z, by simp only [hz, add_sub_cancel_right]⟩
  obtain ⟨a, ha, hlin⟩ := nxU_entire_linear hφ₀ (sub_self _)
  refine ⟨a, φ 0, ha, fun z => ?_⟩
  rw [← hlin z, sub_add_cancel]

/-- **Theorem 13.5**: a quasiconformal map of the whole plane with given complex characteristic
satisfying `f(0) = 0`, `f(1) = 1` (and `f(∞) = ∞`) is unique.

Proved (2026-09-23): `g ∘ f⁻¹` is a conformal bijection of `ℂ` (`same_dilatation_conformal`), hence affine
(`nx_entire_affine`: removable singularity of `1/φ(1/ζ)` at `0`, then Liouville for the slope `dslope φ 0`), and
fixing `0` and `1` it is the identity. -/
theorem thm13_5_uniqueness_plane {f g : ℂ → ℂ} (hf : IsQuasiconformal f univ)
    (hg : IsQuasiconformal g univ) (hfs : f '' univ = univ) (hgs : g '' univ = univ)
    (hμ : ∀ᵐ z, complexDilatation f z = complexDilatation g z) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hg0 : g 0 = 0) (hg1 : g 1 = 1) : f = g := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨K', hK'⟩ := hg
  obtain ⟨hμb, hfsol⟩ := thm10_2_genHomeoSolution_of_isKQC hK
  obtain ⟨-, hgsol⟩ := thm10_2_genHomeoSolution_of_isKQC hK'
  have hK1 : (1 : ℝ) ≤ K := hK.2.1
  have hk : (K - 1) / (K + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hgsol' : IsGenHomeoSolution g (complexDilatation f) univ 2 := by
    obtain ⟨hh, gx, gy, hp, heq⟩ := hgsol
    refine ⟨hh, gx, gy, hp, ?_⟩
    rw [Measure.restrict_univ] at heq ⊢
    filter_upwards [heq, hμ] with z h1 h2
    rw [h1, h2]
  obtain ⟨φ, hφ, hgφ⟩ := same_dilatation_conformal isOpen_univ hk hμb hfsol hgsol'
  rw [hfs, hgs] at hφ
  obtain ⟨a, b, -, hab⟩ := nx_entire_affine hφ
  have hb : b = 0 := by
    have h := hgφ 0 (mem_univ 0)
    rw [hg0, hf0, hab, mul_zero, zero_add] at h
    exact h.symm
  have ha1 : a = 1 := by
    have h := hgφ 1 (mem_univ 1)
    rw [hg1, hf1, hab, hb, mul_one, add_zero] at h
    exact h.symm
  funext z
  rw [hgφ z (mem_univ z), hab, ha1, hb, one_mul, add_zero]

/-! ## §13.4 Hölder continuity -/

/-! ## §13.5 Quasiconformal extension -/

/-! ## §13.6–13.8 -/

section T1Helpers

open scoped Classical

/-- T1.1: a `K`-q.c. map of the whole plane onto itself is a homeomorphism `ℂ ≃ₜ ℂ`. -/
theorem t1_homeomorph {χ : ℂ → ℂ} {K : ℝ} (hχ : IsKQC χ univ K) (hs : χ '' univ = univ) :
    ∃ e : ℂ ≃ₜ ℂ, ⇑e = χ := by
  obtain ⟨-, -, hhom, -⟩ := hχ
  obtain ⟨hc, hi, -, hinv⟩ := hhom
  rw [hs] at hinv
  have hcont : Continuous χ := continuousOn_univ.1 hc
  have hbij : Function.Bijective χ := by
    refine ⟨fun a b hab => hi (mem_univ a) (mem_univ b) hab, fun y => ?_⟩
    have hy : y ∈ χ '' univ := by rw [hs]; exact mem_univ y
    obtain ⟨x, -, rfl⟩ := hy
    exact ⟨x, rfl⟩
  set ee : ℂ ≃ ℂ := Equiv.ofBijective χ hbij with hee
  have hsymm : ∀ y, ee.symm y = Function.invFunOn χ univ y := by
    intro y
    have h1 : χ (ee.symm y) = y := ee.apply_symm_apply y
    have hy : y ∈ χ '' univ := by rw [hs]; exact mem_univ y
    have h2 : χ (Function.invFunOn χ univ y) = y := Function.invFunOn_eq hy
    exact hi (mem_univ _) (mem_univ _) (h1.trans h2.symm)
  have hcontinv : Continuous ee.symm := (continuousOn_univ.1 hinv).congr (fun y => (hsymm y).symm)
  exact ⟨⟨ee, hcont, hcontinv⟩, rfl⟩

/-- T1.2a: the image of the unit disc under a homeomorphism of `ℂ` is open. -/
theorem t1_isOpen_image (e : ℂ ≃ₜ ℂ) : IsOpen (e '' unitDisc) :=
  e.isOpenMap unitDisc isOpen_ball

/-- T1.2b: the image of the unit disc under a homeomorphism of `ℂ` is connected. -/
theorem t1_isConnected_image (e : ℂ ≃ₜ ℂ) : IsConnected (e '' unitDisc) :=
  (isConnected_ball one_pos).image e e.continuous.continuousOn

/-- T1.2c: the image of the unit disc under a homeomorphism of `ℂ` is not the whole plane. -/
theorem t1_compl_nonempty (e : ℂ ≃ₜ ℂ) : (e '' unitDisc)ᶜ.Nonempty := by
  rw [nonempty_compl]
  intro hcon
  have himg : e '' unitDisc = e '' univ := by
    rw [hcon, Set.image_univ, e.surjective.range_eq]
  have heq : unitDisc = univ := (Set.image_eq_image e.injective).mp himg
  have h2 : (2 : ℂ) ∈ unitDisc := heq ▸ mem_univ (2 : ℂ)
  simp [unitDisc, mem_ball] at h2

theorem t1_contractible_unitDisc : ContractibleSpace ↥unitDisc :=
  (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, mem_ball_self one_pos⟩

attribute [local instance] t1_contractible_unitDisc

theorem t1_simplyConnected_unitDisc : SimplyConnectedSpace ↥unitDisc :=
  SimplyConnectedSpace.ofContractible _

attribute [local instance] t1_simplyConnected_unitDisc

/-- T1.2d: the image of the unit disc under a homeomorphism of `ℂ` is simply connected. -/
theorem t1_simplyConnected_image (e : ℂ ≃ₜ ℂ) : SimplyConnectedSpace ↥(e '' unitDisc) :=
  ContinuousMap.HomotopyEquiv.simplyConnectedSpace (e.image unitDisc).symm.toHomotopyEquiv

/-- T1.3: package the Riemann map given by `RMT.exists_riemannMap` into the form T1 needs:
conformal onto the unit disc, sending the base point to `0`, with everywhere-nonzero
derivative. -/
theorem t1_riemannMap {U : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U) (hUne : Uᶜ.Nonempty)
    [SimplyConnectedSpace ↥U] {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ f : ℂ → ℂ, IsConformalOnto f U unitDisc ∧ f z₀ = 0 ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  obtain ⟨f, hf, hfb⟩ := RMT.exists_riemannMap hUo hUc hUne hz₀
  refine ⟨f, ⟨hf.diff, hf.injOn, hfb.image_eq⟩, hf.center, fun z hz => ?_⟩
  exact deriv_ne_zero_of_injOn hUo hf.diff hf.injOn hz

/-- A conformal bijection sends null sets to null sets (given the image is known measurable). -/
theorem t1_null_image {f : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U) (hf : IsConformalOnto f U V)
    {s : Set ℂ} (hs : s ⊆ U) (hsm : MeasurableSet s) (hfsm : MeasurableSet (f '' s))
    (h0 : volume s = 0) : volume (f '' s) = 0 := by
  have hkey := lintegral_image_conformal hU hf ((f '' s).indicator (fun _ => (1 : ℝ≥0∞)))
  have hind : Set.EqOn
      (fun z => ‖deriv f z‖ₑ ^ 2 * (f '' s).indicator (fun _ => (1 : ℝ≥0∞)) (f z))
      (fun z => ‖deriv f z‖ₑ ^ 2 * s.indicator (fun _ => (1 : ℝ≥0∞)) z) U := by
    intro z hz
    by_cases hzs : z ∈ s
    · simp only [Set.indicator_of_mem hzs, Set.indicator_of_mem (mem_image_of_mem f hzs)]
    · have hnz : f z ∉ f '' s := by
        rintro ⟨z', hz's, hz'eq⟩
        exact hzs (hf.2.1 (hs hz's) hz hz'eq ▸ hz's)
      simp only [Set.indicator_of_notMem hzs, Set.indicator_of_notMem hnz]
  rw [setLIntegral_congr_fun hU.measurableSet hind] at hkey
  have hz0 : ∫⁻ z in U, ‖deriv f z‖ₑ ^ 2 * s.indicator (fun _ => (1 : ℝ≥0∞)) z = 0 := by
    have heqfun : (fun z => ‖deriv f z‖ₑ ^ 2 * s.indicator (fun _ => (1 : ℝ≥0∞)) z) =
        s.indicator (fun z => ‖deriv f z‖ₑ ^ 2) := by
      ext z
      by_cases hzs : z ∈ s <;> simp [Set.indicator, hzs]
    rw [setLIntegral_congr_fun hU.measurableSet (fun z _ => congrFun heqfun z),
      lintegral_indicator hsm, Measure.restrict_restrict hsm,
      Set.inter_eq_self_of_subset_left hs, Measure.restrict_eq_zero.2 h0, lintegral_zero_measure]
  rw [hz0] at hkey
  have hfsV : f '' s ⊆ V := hf.2.2 ▸ image_mono hs
  rwa [lintegral_indicator hfsm, setLIntegral_one,
    Measure.restrict_apply' (hf.isOpen hU).measurableSet,
    Set.inter_eq_self_of_subset_left hfsV] at hkey

/-- The (globally measurable, zero-off-`U`) piecewise extension of the inverse `g` of a conformal
map is quasi-measure-preserving from `U` to `V = g '' U`. -/
theorem t1_quasiMeasurePreserving {g : ℂ → ℂ} {U V : Set ℂ} (hUo : IsOpen U) (hVo : IsOpen V)
    (hg : IsConformalOnto g U V) :
    Measure.QuasiMeasurePreserving (U.piecewise g (fun _ => (0 : ℂ)) : ℂ → ℂ)
      (volume.restrict U) (volume.restrict V) := by
  set g₀ : ℂ → ℂ := U.piecewise g (fun _ => (0 : ℂ)) with hg₀def
  have hg₀m : Measurable g₀ :=
    ContinuousOn.measurable_piecewise hg.1.continuousOn continuousOn_const hUo.measurableSet
  set f : ℂ → ℂ := Function.invFunOn g U with hfdef
  have hf : IsConformalOnto f V U := hg.symm hUo
  refine ⟨hg₀m, fun s hs0 => ?_⟩
  obtain ⟨t, hst, htm, ht0⟩ := exists_measurable_superset (volume.restrict V) s
  have ht0' : (volume.restrict V) t = 0 := ht0.trans hs0
  have hle : (volume.restrict U).map g₀ s ≤ (volume.restrict U).map g₀ t :=
    measure_mono (preimage_mono hst)
  refine le_antisymm (hle.trans_eq ?_) bot_le
  rw [Measure.map_apply hg₀m htm, Measure.restrict_apply (htm.preimage hg₀m), Set.inter_comm]
  have htV : volume (t ∩ V) = 0 := by
    rwa [Measure.restrict_apply' hVo.measurableSet] at ht0'
  have hset : U ∩ g₀ ⁻¹' t = f '' (t ∩ V) := by
    ext w
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hwU, hwt⟩
      have hg₀w : g₀ w = g w := Set.piecewise_eq_of_mem _ _ _ hwU
      rw [hg₀w] at hwt
      exact ⟨g w, ⟨hwt, hg.2.2 ▸ mem_image_of_mem g hwU⟩, hg.2.1.leftInvOn_invFunOn hwU⟩
    · rintro ⟨v, ⟨hvt, hvV⟩, rfl⟩
      have hvgU : v ∈ g '' U := hg.2.2 ▸ hvV
      have hfvU : f v ∈ U := Function.invFunOn_mem hvgU
      have hgfv : g (f v) = v := Function.invFunOn_eq hvgU
      have hg₀fv : g₀ (f v) = g (f v) := Set.piecewise_eq_of_mem _ _ _ hfvU
      exact ⟨hfvU, by rw [hg₀fv, hgfv]; exact hvt⟩
  have hfsm : MeasurableSet (f '' (t ∩ V)) := hset ▸ (hUo.measurableSet.inter (htm.preimage hg₀m))
  rw [hset]
  exact t1_null_image hVo hf inter_subset_right (htm.inter hVo.measurableSet) hfsm htV

/-- Transport an a.e. property on the target of a conformal map back to an a.e. property on the
source, composed with (the inverse of) the map. -/
theorem t1_ae_transport {g : ℂ → ℂ} {U V : Set ℂ} (hUo : IsOpen U) (hVo : IsOpen V)
    (hg : IsConformalOnto g U V) {P : ℂ → Prop} (hP : ∀ᵐ z ∂(volume.restrict V), P z) :
    ∀ᵐ w ∂(volume.restrict U), P (g w) := by
  have hqmp := t1_quasiMeasurePreserving hUo hVo hg
  set g₀ : ℂ → ℂ := U.piecewise g (fun _ => (0 : ℂ)) with hg₀def
  have hg₀eq : Set.EqOn g₀ g U := fun w hw => Set.piecewise_eq_of_mem _ _ _ hw
  have hE0 : (volume.restrict V) {z | ¬ P z} = 0 := ae_iff.1 hP
  obtain ⟨T, hsub, hTm, hT0⟩ := exists_measurable_superset (volume.restrict V) {z | ¬ P z}
  have hT0' : (volume.restrict V) T = 0 := hT0.trans hE0
  have hmapT := hqmp.absolutelyContinuous hT0'
  rw [Measure.map_apply hqmp.measurable hTm,
    Measure.restrict_apply (hTm.preimage hqmp.measurable)] at hmapT
  rw [ae_iff, Measure.restrict_apply' hUo.measurableSet]
  refine measure_mono_null (fun w hw => ?_) hmapT
  simp only [mem_inter_iff, mem_preimage, mem_setOf_eq] at hw ⊢
  refine ⟨?_, hw.2⟩
  rw [hg₀eq hw.2]
  exact hsub hw.1

/-- Composing an a.e.-strongly-measurable function with (the inverse of) a conformal map stays
a.e.-strongly-measurable. -/
theorem t1_aestronglyMeasurable_comp {g : ℂ → ℂ} {U V : Set ℂ} (hUo : IsOpen U) (hVo : IsOpen V)
    (hg : IsConformalOnto g U V) {μ : ℂ → ℂ} (hμ : AEStronglyMeasurable μ (volume.restrict V)) :
    AEStronglyMeasurable (μ ∘ g) (volume.restrict U) := by
  have hqmp := t1_quasiMeasurePreserving hUo hVo hg
  have h1 : AEStronglyMeasurable (μ ∘ (U.piecewise g (fun _ => (0 : ℂ)))) (volume.restrict U) :=
    hμ.comp_quasiMeasurePreserving hqmp
  refine h1.congr ?_
  filter_upwards [self_mem_ae_restrict hUo.measurableSet] with w hw
  simp [Set.piecewise_eq_of_mem _ _ _ hw]

/-- T1.4: the pullback of a Beltrami coefficient under (the inverse of) a Riemann map is a
compactly supported Beltrami coefficient on the plane. -/
theorem t1_beltrami_pullback {D : Set ℂ} (hDo : IsOpen D) {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k)
    (hμ : IsBeltramiCoeff μ D k) {ψ : ℂ → ℂ} (hψ : IsConformalOnto ψ D unitDisc) :
    IsCompactBeltramiCoeff
      (unitDisc.indicator (fun w => μ (Function.invFunOn ψ D w) *
        conj (deriv (Function.invFunOn ψ D) w) / deriv (Function.invFunOn ψ D) w)) k := by
  set g : ℂ → ℂ := Function.invFunOn ψ D with hgdef
  have hg : IsConformalOnto g unitDisc D := hψ.symm hDo
  have hg' : ∀ w ∈ unitDisc, deriv g w ≠ 0 :=
    fun w hw => deriv_ne_zero_of_injOn isOpen_ball hg.1 hg.2.1 hw
  set F : ℂ → ℂ := fun w => μ (g w) * conj (deriv g w) / deriv g w with hFdef
  have hFmeas : AEStronglyMeasurable F (volume.restrict unitDisc) := by
    have h1 : AEStronglyMeasurable (μ ∘ g) (volume.restrict unitDisc) :=
      t1_aestronglyMeasurable_comp isOpen_ball hDo hg hμ.1
    have h2 : AEStronglyMeasurable (fun w => conj (deriv g w) / deriv g w)
        (volume.restrict unitDisc) := by
      apply ContinuousOn.aestronglyMeasurable ?_ isOpen_ball.measurableSet
      have hcd : ContinuousOn (deriv g) unitDisc :=
        (hg.1.analyticOnNhd isOpen_ball).deriv.continuousOn
      exact (continuous_conj.comp_continuousOn hcd).div hcd hg'
    have := h1.mul h2
    refine this.congr (Filter.Eventually.of_forall fun w => ?_)
    show μ (g w) * (conj (deriv g w) / deriv g w) = μ (g w) * conj (deriv g w) / deriv g w
    rw [mul_div_assoc]
  have hbound : ∀ᵐ w ∂(volume.restrict unitDisc), ‖F w‖ ≤ k := by
    have hbase : ∀ᵐ w ∂(volume.restrict unitDisc), ‖μ (g w)‖ ≤ k :=
      t1_ae_transport isOpen_ball hDo hg hμ.2
    filter_upwards [hbase, self_mem_ae_restrict isOpen_ball.measurableSet] with w hw1 hw2
    have hne : deriv g w ≠ 0 := hg' w hw2
    rw [hFdef]
    show ‖μ (g w) * conj (deriv g w) / deriv g w‖ ≤ k
    rw [norm_div, norm_mul, norm_conj, mul_div_assoc, div_self (norm_ne_zero_iff.2 hne), mul_one]
    exact hw1
  refine ⟨⟨?_, ?_⟩, 1, fun z hz => ?_⟩
  · rw [Measure.restrict_univ]
    exact (aestronglyMeasurable_indicator_iff isOpen_ball.measurableSet).mpr hFmeas
  · rw [Measure.restrict_univ, ae_iff]
    have hsub : {z : ℂ | ¬ ‖unitDisc.indicator F z‖ ≤ k} ⊆ {w | ¬ ‖F w‖ ≤ k} ∩ unitDisc := by
      intro z hz
      simp only [mem_setOf_eq] at hz
      by_cases hzd : z ∈ unitDisc
      · rw [Set.indicator_of_mem hzd] at hz
        exact ⟨hz, hzd⟩
      · exact absurd (by rw [Set.indicator_of_notMem hzd]; simpa using hk₀) hz
    refine measure_mono_null hsub ?_
    have hUDm : MeasurableSet unitDisc := isOpen_ball.measurableSet
    have hb0 := ae_iff.1 hbound
    rwa [Measure.restrict_apply' hUDm] at hb0
  · have : z ∉ unitDisc := by
      simp only [unitDisc, mem_ball, dist_zero_right, not_lt]
      linarith
    exact Set.indicator_of_notMem this _

/-- The derivative of the inverse of a conformal map is the reciprocal of the derivative. -/
theorem t1_deriv_invFunOn_mul {f : ℂ → ℂ} {U V : Set ℂ} (hUo : IsOpen U)
    (hf : IsConformalOnto f U V) {z : ℂ} (hz : z ∈ U) :
    deriv (Function.invFunOn f U) (f z) * deriv f z = 1 := by
  have heq : (Function.invFunOn f U ∘ f) =ᶠ[𝓝 z] id := by
    filter_upwards [hUo.mem_nhds hz] with z' hz'
    exact hf.2.1.leftInvOn_invFunOn hz'
  have hgd : DifferentiableAt ℂ (Function.invFunOn f U) (f z) :=
    hf.differentiableAt_invFunOn hUo hz
  have hfd : DifferentiableAt ℂ f z := hf.1.differentiableAt (hUo.mem_nhds hz)
  have h1 : HasDerivAt (Function.invFunOn f U ∘ f)
      (deriv (Function.invFunOn f U) (f z) * deriv f z) z :=
    hgd.hasDerivAt.comp z hfd.hasDerivAt
  have h2 : HasDerivAt (Function.invFunOn f U ∘ f) 1 z :=
    (hasDerivAt_id z).congr_of_eventuallyEq heq
  exact h1.unique h2

/-- If `χ` is not real-differentiable at `ψ z`, then `φ ∘ χ ∘ ψ` is not real-differentiable at
`z`, for conformal `ψ`, `φ` sandwiching `χ`. -/
theorem t1_not_differentiableAt_sandwich {ψ φ χ : ℂ → ℂ} {D W : Set ℂ} (hDo : IsOpen D)
    (hWo : IsOpen W) (hψ : IsConformalOnto ψ D (ψ '' D)) (hφ : IsConformalOnto φ W (φ '' W))
    (hχW : MapsTo χ (ψ '' D) W) {z : ℂ} (hz : z ∈ D)
    (hχnd : ¬ DifferentiableAt ℝ χ (ψ z)) :
    ¬ DifferentiableAt ℝ (φ ∘ χ ∘ ψ) z := by
  intro hfd
  apply hχnd
  set w : ℂ := ψ z with hwdef
  have hwψD : w ∈ ψ '' D := mem_image_of_mem ψ hz
  have hχwW : χ w ∈ W := hχW hwψD
  have hψDo : IsOpen (ψ '' D) := hψ.isOpen hDo
  have hinvψ : DifferentiableAt ℂ (Function.invFunOn ψ D) w := hψ.differentiableAt_invFunOn hDo hz
  have hinvφ : DifferentiableAt ℂ (Function.invFunOn φ W) (φ (χ w)) :=
    hφ.differentiableAt_invFunOn hWo hχwW
  have hinvψz : Function.invFunOn ψ D w = z := hψ.2.1.leftInvOn_invFunOn hz
  have hcomp : DifferentiableAt ℝ
      (Function.invFunOn φ W ∘ (φ ∘ χ ∘ ψ) ∘ Function.invFunOn ψ D) w := by
    have h1 : DifferentiableAt ℝ ((φ ∘ χ ∘ ψ) ∘ Function.invFunOn ψ D) w :=
      (hinvψz ▸ hfd : DifferentiableAt ℝ (φ ∘ χ ∘ ψ) (Function.invFunOn ψ D w)).comp w
        (hinvψ.restrictScalars ℝ)
    have hval : ((φ ∘ χ ∘ ψ) ∘ Function.invFunOn ψ D) w = φ (χ w) := by
      show φ (χ (ψ (Function.invFunOn ψ D w))) = φ (χ w)
      rw [Function.invFunOn_eq hwψD]
    rw [← hval] at hinvφ
    exact (hinvφ.restrictScalars ℝ).comp w h1
  have heq : (Function.invFunOn φ W ∘ (φ ∘ χ ∘ ψ) ∘ Function.invFunOn ψ D) =ᶠ[𝓝 w] χ := by
    filter_upwards [hψDo.mem_nhds hwψD] with w' hw'
    have hw'z : ψ (Function.invFunOn ψ D w') = w' := Function.invFunOn_eq hw'
    have hχw'W : χ w' ∈ W := hχW hw'
    show Function.invFunOn φ W (φ (χ (ψ (Function.invFunOn ψ D w')))) = χ w'
    rw [hw'z]
    exact hφ.2.1.leftInvOn_invFunOn hχw'W
  exact hcomp.congr_of_eventuallyEq heq.symm

/-- T1.5: the pointwise dilatation identity for `f = φ ∘ χ ∘ ψ`, at a point where the pulled-back
Beltrami equation for `χ` holds. -/
theorem t1_dilatation_identity {D : Set ℂ} (hDo : IsOpen D) {μ μ₁ ψ φ χ : ℂ → ℂ}
    (hψ : IsConformalOnto ψ D unitDisc) {W : Set ℂ} (hWo : IsOpen W)
    (hφ : IsConformalOnto φ W unitDisc) (hχW : MapsTo χ unitDisc W)
    (hμ₁def : ∀ w ∈ unitDisc, μ₁ w = μ (Function.invFunOn ψ D w) *
      conj (deriv (Function.invFunOn ψ D) w) / deriv (Function.invFunOn ψ D) w)
    {z : ℂ} (hz : z ∈ D) (hP : complexDilatation χ (ψ z) = μ₁ (ψ z)) :
    complexDilatation (φ ∘ χ ∘ ψ) z = μ z := by
  set w : ℂ := ψ z with hwdef
  set g : ℂ → ℂ := Function.invFunOn ψ D with hgdef
  have hwD : w ∈ unitDisc := hψ.2.2 ▸ mem_image_of_mem ψ hz
  have hψz : DifferentiableAt ℂ ψ z := hψ.1.differentiableAt (hDo.mem_nhds hz)
  have hψz' : deriv ψ z ≠ 0 := deriv_ne_zero_of_injOn hDo hψ.1 hψ.2.1 hz
  have hχwW : χ w ∈ W := hχW hwD
  have hφχw : DifferentiableAt ℂ φ (χ w) := hφ.1.differentiableAt (hWo.mem_nhds hχwW)
  have hφχw' : deriv φ (χ w) ≠ 0 := deriv_ne_zero_of_injOn hWo hφ.1 hφ.2.1 hχwW
  have hgw : g w = z := hψ.2.1.leftInvOn_invFunOn hz
  by_cases hd : DifferentiableAt ℝ χ w
  · -- differentiable case
    have hgw' : deriv g w * deriv ψ z = 1 := t1_deriv_invFunOn_mul hDo hψ hz
    have step1 : complexDilatation (χ ∘ ψ) z =
        complexDilatation χ w * (conj (deriv ψ z) / deriv ψ z) :=
      complexDilatation_comp_conformal_right hψz hψz' hd
    have hχψz : DifferentiableAt ℝ (χ ∘ ψ) z := hd.comp z (hψz.restrictScalars ℝ)
    have step2 : complexDilatation (φ ∘ (χ ∘ ψ)) z = complexDilatation (χ ∘ ψ) z :=
      complexDilatation_comp_conformal_left hχψz hφχw hφχw'
    have hcomb : complexDilatation (φ ∘ χ ∘ ψ) z =
        complexDilatation χ w * (conj (deriv ψ z) / deriv ψ z) := by
      rw [show (φ ∘ χ ∘ ψ) = φ ∘ (χ ∘ ψ) from rfl, step2, step1]
    rw [hcomb, hP, hμ₁def w hwD, hgw]
    have hg'ne : deriv g w ≠ 0 := by
      intro h; rw [h, zero_mul] at hgw'; exact zero_ne_one hgw'
    have hgeq : deriv g w = (deriv ψ z)⁻¹ := by
      field_simp at hgw' ⊢
      linear_combination hgw'
    have hcψz : (starRingEnd ℂ) (deriv ψ z) ≠ 0 := by simpa using hψz'
    rw [hgeq, map_inv₀]
    field_simp
  · -- non-differentiable case: both sides are the junk value `0`
    have hfnd : ¬ DifferentiableAt ℝ (φ ∘ χ ∘ ψ) z := by
      have hψD : IsConformalOnto ψ D (ψ '' D) := ⟨hψ.1, hψ.2.1, rfl⟩
      have hφW : IsConformalOnto φ W (φ '' W) := ⟨hφ.1, hφ.2.1, rfl⟩
      exact t1_not_differentiableAt_sandwich hDo hWo hψD hφW (hψ.2.2 ▸ hχW) hz hd
    have hcd0 : complexDilatation (φ ∘ χ ∘ ψ) z = 0 := by
      simp [complexDilatation, dz, dzbar, fderiv_zero_of_not_differentiableAt hfnd]
    have hχd0 : complexDilatation χ w = 0 := by
      simp [complexDilatation, dz, dzbar, fderiv_zero_of_not_differentiableAt hd]
    rw [hχd0] at hP
    have hμ1 : μ₁ w = 0 := hP.symm
    rw [hμ₁def w hwD, hgw] at hμ1
    have hgnz : deriv g w ≠ 0 := by
      have := t1_deriv_invFunOn_mul hDo hψ hz
      intro h; rw [h, zero_mul] at this; exact zero_ne_one this
    have hμz0 : μ z = 0 := by
      have hconjne : (starRingEnd ℂ) (deriv g w) ≠ 0 := by simpa using hgnz
      rw [div_eq_zero_iff] at hμ1
      rcases hμ1 with h | h
      · exact (mul_eq_zero.mp h).resolve_right hconjne
      · exact absurd h hgnz
    rw [hcd0, hμz0]

end T1Helpers

/-- **Theorem 13.6** (拟共形映射的 Riemann 映射定理).  Let `D` be a simply connected domain with more
than one boundary point in `ℂ̄` and `μ` measurable on `D` with `‖μ‖_∞ ≤ k < 1`.  Then there is a
quasiconformal map of `D` onto the unit disc with complex characteristic `μ`; moreover a given
point `z₀ ∈ D` can be sent to `0`.

*Proof.* Reduced to Theorem 12.2: `ψ : D → Δ` is a Riemann map (RMT), `μ₁` is `μ` pulled back to
`Δ` along `ψ⁻¹`, `χ` is the Theorem 12.2 solution for `μ₁`, and `φ : χ(Δ) → Δ` is a second Riemann
map; `f = φ ∘ χ ∘ ψ`.  At points where `χ` is not real-differentiable at `ψ z`, both
`complexDilatation f z` and the pulled-back identity give the junk value `0` on both sides, so no
a.e.-differentiability result is needed. -/
theorem thm13_6_riemann_mapping {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D)
    (hDs : IsSimplyConnected D) (hDne : D ≠ univ) {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμ : IsBeltramiCoeff μ D k) {z₀ : ℂ} (hz₀ : z₀ ∈ D) :
    ∃ f : ℂ → ℂ, IsKQC f D ((1 + k) / (1 - k)) ∧ f '' D = unitDisc ∧ f z₀ = 0 ∧
      ∀ᵐ z ∂(volume.restrict D), complexDilatation f z = μ z := by
  haveI : SimplyConnectedSpace ↥D := hDs
  obtain ⟨ψ, hψ, hψz₀, hψ'⟩ := t1_riemannMap hD hDc (Set.nonempty_compl.2 hDne) hz₀
  set g : ℂ → ℂ := Function.invFunOn ψ D with hgdef
  set μ₁ : ℂ → ℂ := unitDisc.indicator (fun w => μ (g w) * conj (deriv g w) / deriv g w)
    with hμ₁def
  have hμ₁c : IsCompactBeltramiCoeff μ₁ k := t1_beltrami_pullback hD hk₀ hμ hψ
  obtain ⟨χ, hχKQC, hχsurj, hχdilat, -⟩ := thm12_2 hk₀ hk hμ₁c
  obtain ⟨e, he⟩ := t1_homeomorph hχKQC hχsurj
  set W : Set ℂ := χ '' unitDisc with hWdef
  have hWeq : W = e '' unitDisc := by rw [hWdef, he]
  have hWo : IsOpen W := hWeq ▸ t1_isOpen_image e
  have hWc : IsConnected W := hWeq ▸ t1_isConnected_image e
  have hWne : Wᶜ.Nonempty := hWeq ▸ t1_compl_nonempty e
  haveI : SimplyConnectedSpace ↥W := hWeq ▸ t1_simplyConnected_image e
  have hχ0W : χ 0 ∈ W := mem_image_of_mem χ (by simp [unitDisc, mem_ball] : (0:ℂ) ∈ unitDisc)
  obtain ⟨φ, hφ, hφz, hφ'⟩ := t1_riemannMap hWo hWc hWne hχ0W
  set f : ℂ → ℂ := φ ∘ χ ∘ ψ with hfdef
  have hK : IsKQC f D ((1 + k) / (1 - k)) := by
    have h1 : IsKQC ψ D 1 := isKQC_one_of_conformal hD hψ
    have h2 : IsKQC (χ ∘ ψ) D (1 * ((1 + k) / (1 - k))) :=
      thm7_1_comp h1 hχKQC (hψ.2.2 ▸ subset_univ (ψ '' D))
    rw [one_mul] at h2
    have h3 : IsKQC φ W 1 := isKQC_one_of_conformal hWo hφ
    have hsub : (χ ∘ ψ) '' D ⊆ W := by
      rw [image_comp, hψ.2.2]
    have h4 : IsKQC (φ ∘ (χ ∘ ψ)) D (((1 + k) / (1 - k)) * 1) := thm7_1_comp h2 h3 hsub
    rwa [mul_one] at h4
  have himg : f '' D = unitDisc := by
    rw [hfdef, Set.image_comp φ (χ ∘ ψ), Set.image_comp χ ψ, hψ.2.2, ← hWdef, hφ.2.2]
  have hz₀0 : f z₀ = 0 := by
    show φ (χ (ψ z₀)) = 0
    rw [hψz₀, hφz]
  have hdilat : ∀ᵐ z ∂(volume.restrict D), complexDilatation f z = μ z := by
    have hP_local : ∀ᵐ w ∂(volume.restrict unitDisc), complexDilatation χ w = μ₁ w :=
      Filter.Eventually.filter_mono (ae_mono Measure.restrict_le_self) hχdilat
    have hae_ψz : ∀ᵐ z ∂(volume.restrict D), complexDilatation χ (ψ z) = μ₁ (ψ z) :=
      t1_ae_transport hD isOpen_ball hψ hP_local
    filter_upwards [hae_ψz, self_mem_ae_restrict hD.measurableSet] with z hz hzD
    exact t1_dilatation_identity hD hψ hWo hφ
      (fun w hw => mem_image_of_mem χ hw) (fun w hw => Set.indicator_of_mem hw _) hzD hz
  exact ⟨f, hK, himg, hz₀0, hdilat⟩

/-- `f` is the normalized solution (规范拟共形映射) for `μ` in the plane: a quasiconformal
homeomorphism of `ℂ` onto `ℂ` with complex characteristic `μ` fixing `0` and `1` (and `∞`). -/
def IsNormalizedSolution (f μ : ℂ → ℂ) : Prop :=
  IsQuasiconformal f univ ∧ f '' univ = univ ∧ f 0 = 0 ∧ f 1 = 1 ∧
    ∀ᵐ z, complexDilatation f z = μ z

/-! ### Theorem 13.7 (normalized plane solution) — helpers -/

/-! ## Region 2: existence (Theorem 13.7) -/

/-! ### Definitions -/

/-- `μ₂ = μ` off the unit disc, `0` on it. -/
def nxMu2 (μ : ℂ → ℂ) : ℂ → ℂ := unitDiscᶜ.indicator μ

/-- `μ̃₂(ζ) = μ₂(1/ζ) ζ²/ζ̄²`, the coefficient conjugated by `z ↦ 1/z`. -/
def nxMu2t (μ : ℂ → ℂ) (ζ : ℂ) : ℂ := nxMu2 μ ζ⁻¹ * (ζ ^ 2 / conj ζ ^ 2)

/-- `z ↦ 1/f(1/z)`; with Lean's `0⁻¹ = 0` this is a bijection of `ℂ` when `f` is one fixing `0`. -/
def nxInvConj (f : ℂ → ℂ) (z : ℂ) : ℂ := (f z⁻¹)⁻¹

/-- The push-forward of `μ|_Δ` by `ψ` to `ψ(Δ)`: `μ(g w) conj(g'(w))/g'(w)` with `g = ψ⁻¹`, and `0` off `ψ(Δ)`. -/
def nxPush (μ ψ : ℂ → ℂ) : ℂ → ℂ :=
  (ψ '' unitDisc).indicator (fun w => μ (Function.invFunOn ψ unitDisc w) *
    (conj (deriv (Function.invFunOn ψ unitDisc) w) / deriv (Function.invFunOn ψ unitDisc) w))

/-! ### Piece T: generic tools -/

theorem nx_isKQC_restrict {f : ℂ → ℂ} {D D' : Set ℂ} {K : ℝ} (hf : IsKQC f D K) (hD' : IsOpen D')
    (hsub : D' ⊆ D) : IsKQC f D' K := by
  obtain ⟨-, hK1, ⟨hc, hi, -, hinv⟩, hmod⟩ := hf
  have hinj' : InjOn f D' := hi.mono hsub
  have heq : EqOn (Function.invFunOn f D') (Function.invFunOn f D) (f '' D') := by
    rintro v ⟨z, hz, rfl⟩
    rw [hinj'.leftInvOn_invFunOn hz, hi.leftInvOn_invFunOn (hsub hz)]
  have hext : toExt D' ⊆ toExt D := image_mono hsub
  refine ⟨hD', hK1, ⟨hc.mono hsub, hinj', rfl, ?_⟩, fun Q hQ => hmod Q (hQ.trans hext)⟩
  exact (hinv.mono (image_mono hsub)).congr heq

/-- A set whose closure in `ℂ̄` avoids `∞` has its closure (in `ℂ̄`) inside the image of some disc
`B(0,R)`: the closure is compact in `ℂ̄`, hence its trace on `ℂ` is compact, hence bounded. -/
theorem nxT_exists_ball_of_closure_subset {s : Set ℂ} (hs : closure (toExt s) ⊆ toExt univ) :
    ∃ R : ℝ, 0 < R ∧ closure (toExt s) ⊆ toExt (ball 0 R) := by
  set C := closure (toExt s) with hC
  have hCc : IsCompact C := isClosed_closure.isCompact
  have hCr : C ⊆ range ((↑) : ℂ → ExtPlane) := by
    intro p hp
    obtain ⟨z, -, rfl⟩ := hs hp
    exact mem_range_self z
  have hpre : IsCompact (((↑) : ℂ → ExtPlane) ⁻¹' C) :=
    OnePoint.isOpenEmbedding_coe.isInducing.isCompact_preimage' hCc hCr
  obtain ⟨R, hR, hsub⟩ := hpre.isBounded.subset_ball_lt 0 0
  refine ⟨R, hR, fun p hp => ?_⟩
  obtain ⟨z, rfl⟩ := hCr hp
  exact ⟨z, hsub hp, rfl⟩

/-- A plane homeomorphism that is `K`-q.c. on every disc `B(0,R)` is `K`-q.c. on `ℂ`. -/
theorem nx_isKQC_univ_of_balls {f : ℂ → ℂ} {K : ℝ} (hf : IsHomeomorphOnto f univ (f '' univ))
    (hb : ∀ R : ℝ, 0 < R → IsKQC f (ball 0 R) K) : IsKQC f univ K := by
  refine ⟨isOpen_univ, (hb 1 one_pos).2.1, hf, fun Q hQ => ?_⟩
  obtain ⟨R, hR, hsub⟩ := nxT_exists_ball_of_closure_subset hQ
  exact (hb R hR).2.2.2 Q hsub

theorem nx_inv_isConformalOnto : IsConformalOnto (fun z : ℂ => z⁻¹) {0}ᶜ {0}ᶜ := by
  refine ⟨fun z hz => differentiableWithinAt_inv (mem_compl_singleton_iff.mp hz) _,
    fun a _ b _ hab => inv_injective hab, ?_⟩
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact mem_compl_singleton_iff.mpr (inv_ne_zero (mem_compl_singleton_iff.mp hw))
  · intro hz
    exact ⟨z⁻¹, mem_compl_singleton_iff.mpr (inv_ne_zero (mem_compl_singleton_iff.mp hz)), inv_inv z⟩

/-- `z ↦ 1/z` preserves null sets. -/
theorem nx_ae_inv {P : ℂ → Prop} (h : ∀ᵐ z, P z) : ∀ᵐ ζ, P ζ⁻¹ := by
  have hU : IsOpen ({0}ᶜ : Set ℂ) := isOpen_compl_singleton
  have h1 : ∀ᵐ z ∂(volume.restrict ({0}ᶜ : Set ℂ)), P z := ae_restrict_of_ae h
  have h2 : ∀ᵐ w ∂(volume.restrict ({0}ᶜ : Set ℂ)), P ((fun z : ℂ => z⁻¹) w) :=
    t1_ae_transport hU hU nx_inv_isConformalOnto h1
  rw [restrict_compl_singleton] at h2
  exact h2

/-- The complex dilatation of the identity vanishes everywhere. -/
theorem nxT_complexDilatation_id (z : ℂ) : complexDilatation (id : ℂ → ℂ) z = 0 := by
  simp [complexDilatation, dzbar, fderiv_id, Complex.I_mul_I]

/-- A q.c. map with vanishing complex dilatation is holomorphic. -/
theorem nx_differentiableOn_of_dilatation_zero {f : ℂ → ℂ} {U : Set ℂ} {K : ℝ} (hf : IsKQC f U K)
    (h0 : ∀ᵐ z ∂(volume.restrict U), complexDilatation f z = 0) : DifferentiableOn ℂ f U := by
  have hU : IsOpen U := hf.1
  -- `id` is a generalized homeomorphic solution of `∂_{z̄} w = 0 · ∂_z w`
  have hidc : IsConformalOnto (id : ℂ → ℂ) U (id '' U) := ⟨differentiableOn_id, injOn_id U, rfl⟩
  obtain ⟨-, hidsol⟩ := thm10_2_genHomeoSolution_of_isKQC (isKQC_one_of_conformal hU hidc)
  have hidsol' : IsGenHomeoSolution id (fun _ => (0 : ℂ)) U 2 := by
    obtain ⟨hh, g, h, hgp, heq⟩ := hidsol
    refine ⟨hh, g, h, hgp, ?_⟩
    filter_upwards [heq] with z hz
    rw [hz, nxT_complexDilatation_id z]
  -- so is `f`, since its dilatation vanishes a.e.
  obtain ⟨-, hfsol⟩ := thm10_2_genHomeoSolution_of_isKQC hf
  have hfsol' : IsGenHomeoSolution f (fun _ => (0 : ℂ)) U 2 := by
    obtain ⟨hh, g, h, hgp, heq⟩ := hfsol
    refine ⟨hh, g, h, hgp, ?_⟩
    filter_upwards [heq, h0] with z hz hz0
    rw [hz, hz0]
  have hμ : IsBeltramiCoeff (fun _ => (0 : ℂ)) U 0 :=
    ⟨aestronglyMeasurable_const, Filter.Eventually.of_forall fun _ => by simp⟩
  obtain ⟨φ, hφ, hfφ⟩ := same_dilatation_conformal hU (k := 0) zero_lt_one hμ hidsol' hfsol'
  rw [Set.image_id] at hφ
  exact hφ.1.congr hfφ

/-! ### Piece I: the inversion step -/

/-- `‖ζ²/ζ̄²‖ ≤ 1` (it is `1` for `ζ ≠ 0` and `0` at `ζ = 0`). -/
theorem nxI1_norm_sq_div_conj_sq_le (ζ : ℂ) : ‖ζ ^ 2 / conj ζ ^ 2‖ ≤ 1 := by
  rw [norm_div, norm_pow, norm_pow, Complex.norm_conj]
  exact div_self_le_one _

/-- `nxMu2t μ` is measurable as soon as `μ` is. -/
theorem nxI1_measurable_mu2t {μ : ℂ → ℂ} (hμ : Measurable μ) : Measurable (nxMu2t μ) := by
  have h1 : Measurable (fun ζ : ℂ => nxMu2 μ ζ⁻¹) :=
    (hμ.indicator measurableSet_ball.compl).comp measurable_inv
  have h2 : Measurable (fun ζ : ℂ => ζ ^ 2 / conj ζ ^ 2) :=
    (measurable_id.pow_const 2).div (Complex.continuous_conj.measurable.pow_const 2)
  exact h1.mul h2

theorem nx_mu2t_compact {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hμ : IsBeltramiCoeff μ univ k) :
    IsCompactBeltramiCoeff (nxMu2t μ) k := by
  obtain ⟨hm, hb⟩ := hμ
  rw [Measure.restrict_univ] at hm hb
  refine ⟨⟨?_, ?_⟩, 1, fun z hz => ?_⟩
  · rw [Measure.restrict_univ]
    have hae : ∀ᵐ ζ : ℂ, μ ζ⁻¹ = hm.mk μ ζ⁻¹ := nx_ae_inv hm.ae_eq_mk
    refine (nxI1_measurable_mu2t hm.stronglyMeasurable_mk.measurable).aestronglyMeasurable.congr ?_
    filter_upwards [hae] with ζ hζ
    simp only [nxMu2t, nxMu2, indicator, hζ]
  · rw [Measure.restrict_univ]
    have hb' : ∀ᵐ ζ : ℂ, ‖μ ζ⁻¹‖ ≤ k := nx_ae_inv hb
    filter_upwards [hb'] with ζ hζ
    rw [nxMu2t, norm_mul]
    calc ‖nxMu2 μ ζ⁻¹‖ * ‖ζ ^ 2 / conj ζ ^ 2‖ ≤ k * 1 :=
          mul_le_mul ((norm_indicator_le_norm_self _ _).trans hζ) (nxI1_norm_sq_div_conj_sq_le ζ)
            (norm_nonneg _) hk₀
      _ = k := mul_one k
  · have hin : z⁻¹ ∈ unitDisc := by
      rw [unitDisc, mem_ball, dist_zero_right, norm_inv]
      exact inv_lt_one_of_one_lt₀ hz
    rw [nxMu2t, nxMu2, indicator_of_notMem (notMem_compl_iff.mpr hin), zero_mul]

/-- For a homeomorphism `e` of `ℂ` fixing `0`, the conjugate `z ↦ 1/e(1/z)` is continuous
(at `0` because `e` maps a neighbourhood of `∞` to a neighbourhood of `∞`). -/
theorem nxI1_continuous_invConj (e : ℂ ≃ₜ ℂ) (h0 : e 0 = 0) : Continuous (nxInvConj e) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
    have hval : nxInvConj e 0 = 0 := by simp [nxInvConj, h0]
    rw [hval]
    have h1 : Tendsto (fun z : ℂ => z⁻¹) (𝓝[≠] 0) (cocompact ℂ) :=
      Metric.cobounded_eq_cocompact (α := ℂ) ▸ tendsto_inv₀_nhdsNE_zero
    have h2 : Tendsto e (cocompact ℂ) (cocompact ℂ) := e.map_cocompact.le
    have h3 : Tendsto (fun w : ℂ => w⁻¹) (cocompact ℂ) (𝓝 0) :=
      Metric.cobounded_eq_cocompact (α := ℂ) ▸ tendsto_inv₀_cobounded
    exact h3.comp (h2.comp h1)
  · have hez : e z⁻¹ ≠ 0 := by
      intro h
      rw [← h0] at h
      exact hz (inv_eq_zero.mp (e.injective h))
    exact (e.continuous.continuousAt.comp (continuousAt_inv₀ hz)).inv₀ hez

/-- The conjugate `z ↦ 1/e(1/z)` of a homeomorphism `e` of `ℂ` fixing `0` is a homeomorphism of `ℂ`
(with inverse `w ↦ 1/e⁻¹(1/w)`; recall Lean's `0⁻¹ = 0`). -/
theorem nxI1_exists_homeo (e : ℂ ≃ₜ ℂ) (h0 : e 0 = 0) : ∃ E : ℂ ≃ₜ ℂ, ⇑E = nxInvConj e := by
  have h0' : e.symm 0 = 0 := e.symm_apply_eq.mpr h0.symm
  exact ⟨{ toFun := nxInvConj e
           invFun := nxInvConj e.symm
           left_inv := fun z => by simp [nxInvConj]
           right_inv := fun z => by simp [nxInvConj]
           continuous_toFun := nxI1_continuous_invConj e h0
           continuous_invFun := nxI1_continuous_invConj e.symm h0' }, rfl⟩

/-- A homeomorphism of `ℂ` is a homeomorphism of `univ` onto `univ` in the project's sense. -/
theorem nxI1_isHomeomorphOnto_of_homeomorph (E : ℂ ≃ₜ ℂ) : IsHomeomorphOnto E univ univ := by
  have hinv : Function.invFunOn E univ = E.symm := by
    funext y
    have hy : y ∈ E '' univ := by rw [image_univ, E.surjective.range_eq]; exact mem_univ y
    have h1 : E (Function.invFunOn E univ y) = y := Function.invFunOn_eq hy
    rw [← h1, E.symm_apply_apply, h1]
  refine ⟨E.continuous.continuousOn, E.injective.injOn, ?_, ?_⟩
  · rw [image_univ, E.surjective.range_eq]
  · rw [hinv]
    exact E.symm.continuous.continuousOn

theorem nx_f2_homeo {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (hs : f '' univ = univ) (h0 : f 0 = 0)
    (hlim : Tendsto (fun z => f z / z) (cocompact ℂ) (𝓝 1)) :
    IsHomeomorphOnto (nxInvConj f) univ univ ∧ nxInvConj f 0 = 0 ∧ IsKQC (nxInvConj f) {0}ᶜ K := by
  obtain ⟨e, he⟩ := t1_homeomorph hf hs
  obtain ⟨E, hE⟩ := nxI1_exists_homeo e (by rw [he]; exact h0)
  refine ⟨?_, ?_, ?_⟩
  · rw [← he, ← hE]
    exact nxI1_isHomeomorphOnto_of_homeomorph E
  · simp [nxInvConj, h0]
  · have hinvq : IsKQC (fun z : ℂ => z⁻¹) {0}ᶜ 1 :=
      isKQC_one_of_conformal isOpen_compl_singleton nx_inv_isConformalOnto
    have hfinj : Function.Injective f := by rw [← he]; exact e.injective
    have h1 : IsKQC (f ∘ fun z : ℂ => z⁻¹) {0}ᶜ (1 * K) := thm7_1_comp hinvq hf (subset_univ _)
    have hsub : (f ∘ fun z : ℂ => z⁻¹) '' {0}ᶜ ⊆ {0}ᶜ := by
      rintro _ ⟨z, hz, rfl⟩ h
      rw [mem_singleton_iff, Function.comp_apply, ← h0] at h
      exact hz (inv_eq_zero.mp (hfinj h))
    have h2 := thm7_1_comp h1 hinvq hsub
    rw [mul_one, one_mul] at h2
    exact h2

/-- The pointwise computation behind `nx_f2_dilatation`: at `z ≠ 0` where `f` is real-differentiable
at `z⁻¹` and `f z⁻¹ ≠ 0`, `μ_{1/f(1/·)}(z) = μ_f(z⁻¹) · z²/z̄²` (the outer inversion is conformal at
`f z⁻¹`, the inner one at `z` with derivative `-z⁻²`). -/
theorem nxI2_dilatation_invConj_at {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0) (hfz : f z⁻¹ ≠ 0)
    (hd : DifferentiableAt ℝ f z⁻¹) :
    complexDilatation (nxInvConj f) z = complexDilatation f z⁻¹ * (z ^ 2 / conj z ^ 2) := by
  have hinvC : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) z := differentiableAt_inv hz
  have hderiv : deriv (fun w : ℂ => w⁻¹) z = -(z ^ 2)⁻¹ := deriv_inv
  have hd2 : deriv (fun w : ℂ => w⁻¹) z ≠ 0 := by
    rw [hderiv]
    exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hz))
  have hcomp : DifferentiableAt ℝ (f ∘ fun w : ℂ => w⁻¹) z :=
    hd.comp z (hinvC.restrictScalars ℝ)
  have hinvC' : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) ((f ∘ fun w : ℂ => w⁻¹) z) :=
    differentiableAt_inv hfz
  have hd3 : deriv (fun w : ℂ => w⁻¹) ((f ∘ fun w : ℂ => w⁻¹) z) ≠ 0 := by
    rw [deriv_inv]
    exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hfz))
  have hL := complexDilatation_comp_conformal_left hcomp hinvC' hd3
  have hR := complexDilatation_comp_conformal_right (g := f) hinvC hd2 hd
  have heq : nxInvConj f = (fun w : ℂ => w⁻¹) ∘ (f ∘ fun w : ℂ => w⁻¹) := rfl
  rw [heq, hL, hR, hderiv]
  have hc : conj z ≠ 0 := (map_ne_zero _).mpr hz
  simp only [map_neg, map_inv₀, map_pow]
  field_simp

theorem nx_f2_dilatation {μ f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (hs : f '' univ = univ)
    (h0 : f 0 = 0) (hdil : ∀ᵐ ζ, complexDilatation f ζ = nxMu2t μ ζ) :
    ∀ᵐ z, complexDilatation (nxInvConj f) z = nxMu2 μ z := by
  have hdiff : ∀ᵐ z, DifferentiableAt ℝ f z := by
    have h := thm9_3_differentiable_ae hf
    rwa [Measure.restrict_univ] at h
  have hne : ∀ᵐ z : ℂ, z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  have hinj : InjOn f univ := hf.2.2.1.2.1
  filter_upwards [nx_ae_inv hdiff, nx_ae_inv hdil, hne] with z hzd hzμ hz0
  have hz1 : z⁻¹ ≠ 0 := inv_ne_zero hz0
  have hfz : f z⁻¹ ≠ 0 := fun h => hz1 (hinj (mem_univ _) (mem_univ _) (h.trans h0.symm))
  rw [nxI2_dilatation_invConj_at hz0 hfz hzd, hzμ, nxMu2t, inv_inv]
  have hc : conj z ≠ 0 := (map_ne_zero _).mpr hz0
  simp only [map_inv₀]
  field_simp

theorem nx_f2_conformal {μ f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (hs : f '' univ = univ)
    (h0 : f 0 = 0) (hlim : Tendsto (fun z => f z / z) (cocompact ℂ) (𝓝 1))
    (hdil : ∀ᵐ ζ, complexDilatation f ζ = nxMu2t μ ζ) :
    IsConformalOnto (nxInvConj f) unitDisc (nxInvConj f '' unitDisc) := by
  obtain ⟨hH, -, hK⟩ := nx_f2_homeo hf hs h0 hlim
  have hopen : IsOpen (unitDisc \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hK' : IsKQC (nxInvConj f) (unitDisc \ {0}) K :=
    nx_isKQC_restrict hK hopen (fun z hz => hz.2)
  have hd := nx_f2_dilatation hf hs h0 hdil
  have hd0 : ∀ᵐ z ∂(volume.restrict (unitDisc \ {0})), complexDilatation (nxInvConj f) z = 0 := by
    rw [ae_restrict_iff' hopen.measurableSet]
    filter_upwards [hd] with z hz hzs
    rw [hz, nxMu2]
    exact indicator_of_notMem (fun h : z ∈ unitDiscᶜ => h hzs.1) μ
  have hdiff : DifferentiableOn ℂ (nxInvConj f) (unitDisc \ {0}) :=
    nx_differentiableOn_of_dilatation_zero hK' hd0
  have hcont : ContinuousAt (nxInvConj f) 0 :=
    hH.1.continuousAt (univ_mem)
  have hmem : unitDisc ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 one_pos
  refine ⟨(Complex.differentiableOn_compl_singleton_and_continuousAt_iff hmem).1 ⟨hdiff, hcont⟩,
    hH.2.1.mono (subset_univ _), rfl⟩

/-! ### Piece P: push-forward and composition -/

theorem nx_push_compact {μ ψ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hμ : IsBeltramiCoeff μ univ k)
    (hψ : IsConformalOnto ψ unitDisc (ψ '' unitDisc)) (hb : Bornology.IsBounded (ψ '' unitDisc)) :
    IsCompactBeltramiCoeff (nxPush μ ψ) k := by
  set D : Set ℂ := ψ '' unitDisc with hDdef
  set g : ℂ → ℂ := Function.invFunOn ψ unitDisc with hgdef
  have hDo : IsOpen D := hψ.isOpen isOpen_ball
  have hg : IsConformalOnto g D unitDisc := hψ.symm isOpen_ball
  have hg' : ∀ w ∈ D, deriv g w ≠ 0 :=
    fun w hw => deriv_ne_zero_of_injOn hDo hg.1 hg.2.1 hw
  set F : ℂ → ℂ := fun w => μ (g w) * (conj (deriv g w) / deriv g w) with hFdef
  have hpush : nxPush μ ψ = D.indicator F := rfl
  have hμv : AEStronglyMeasurable μ (volume.restrict unitDisc) := by
    have h := hμ.1
    rw [Measure.restrict_univ] at h
    exact h.restrict
  have hFmeas : AEStronglyMeasurable F (volume.restrict D) := by
    have h1 : AEStronglyMeasurable (μ ∘ g) (volume.restrict D) :=
      t1_aestronglyMeasurable_comp hDo isOpen_ball hg hμv
    have h2 : AEStronglyMeasurable (fun w => conj (deriv g w) / deriv g w)
        (volume.restrict D) := by
      apply ContinuousOn.aestronglyMeasurable ?_ hDo.measurableSet
      have hcd : ContinuousOn (deriv g) D :=
        (hg.1.analyticOnNhd hDo).deriv.continuousOn
      exact (continuous_conj.comp_continuousOn hcd).div hcd hg'
    exact h1.mul h2
  have hbound : ∀ᵐ w ∂(volume.restrict D), ‖F w‖ ≤ k := by
    have hμb : ∀ᵐ z ∂(volume.restrict unitDisc), ‖μ z‖ ≤ k := by
      have h := hμ.2
      rw [Measure.restrict_univ] at h
      exact ae_restrict_of_ae h
    have hbase : ∀ᵐ w ∂(volume.restrict D), ‖μ (g w)‖ ≤ k :=
      t1_ae_transport hDo isOpen_ball hg hμb
    filter_upwards [hbase, self_mem_ae_restrict hDo.measurableSet] with w hw1 hw2
    have hne : deriv g w ≠ 0 := hg' w hw2
    show ‖μ (g w) * (conj (deriv g w) / deriv g w)‖ ≤ k
    rw [norm_mul, norm_div, norm_conj, div_self (norm_ne_zero_iff.2 hne), mul_one]
    exact hw1
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  refine ⟨⟨?_, ?_⟩, R, fun z hz => ?_⟩
  · rw [Measure.restrict_univ, hpush]
    exact (aestronglyMeasurable_indicator_iff hDo.measurableSet).mpr hFmeas
  · rw [Measure.restrict_univ, ae_iff, hpush]
    have hsub : {z : ℂ | ¬ ‖D.indicator F z‖ ≤ k} ⊆ {w | ¬ ‖F w‖ ≤ k} ∩ D := by
      intro z hz
      simp only [mem_ofPred_eq] at hz
      by_cases hzd : z ∈ D
      · rw [Set.indicator_of_mem hzd] at hz
        exact ⟨hz, hzd⟩
      · exact absurd (by rw [Set.indicator_of_notMem hzd]; simpa using hk₀) hz
    refine measure_mono_null hsub ?_
    have hb0 := ae_iff.1 hbound
    rwa [Measure.restrict_apply' hDo.measurableSet] at hb0
  · have hzD : z ∉ D := by
      intro hzD
      have h := hR hzD
      rw [mem_closedBall, dist_zero_right] at h
      linarith
    rw [hpush]
    exact Set.indicator_of_notMem hzD _

theorem nx_comp_dilatation {μ f₁ f₂ : ℂ → ℂ} {K₁ K₂ : ℝ} (hf₁ : IsKQC f₁ univ K₁)
    (hs₁ : f₁ '' univ = univ) (hd₁ : ∀ᵐ w, complexDilatation f₁ w = nxPush μ f₂ w)
    (hf₂h : IsHomeomorphOnto f₂ univ univ) (hf₂ : IsKQC f₂ {0}ᶜ K₂)
    (hf₂c : IsConformalOnto f₂ unitDisc (f₂ '' unitDisc))
    (hd₂ : ∀ᵐ z, complexDilatation f₂ z = nxMu2 μ z) :
    ∀ᵐ z, complexDilatation (f₁ ∘ f₂) z = μ z := by
  set D : Set ℂ := f₂ '' unitDisc with hDdef
  set g : ℂ → ℂ := Function.invFunOn f₂ unitDisc with hgdef
  have hDo : IsOpen D := hf₂c.isOpen isOpen_ball
  -- inside the unit disc: transport the equation for `f₁` along the conformal map `f₂`
  have hdiff₁ : ∀ᵐ w, DifferentiableAt ℝ f₁ w := by
    have h := thm9_3_differentiable_ae hf₁
    rwa [Measure.restrict_univ] at h
  have hin : ∀ᵐ z ∂(volume.restrict unitDisc),
      complexDilatation f₁ (f₂ z) = nxPush μ f₂ (f₂ z) ∧ DifferentiableAt ℝ f₁ (f₂ z) := by
    have hP : ∀ᵐ w ∂(volume.restrict D),
        complexDilatation f₁ w = nxPush μ f₂ w ∧ DifferentiableAt ℝ f₁ w :=
      ae_restrict_of_ae (hd₁.and hdiff₁)
    exact t1_ae_transport isOpen_ball hDo hf₂c hP
  have hin' : ∀ᵐ z, z ∈ unitDisc →
      complexDilatation f₁ (f₂ z) = nxPush μ f₂ (f₂ z) ∧ DifferentiableAt ℝ f₁ (f₂ z) :=
    (ae_restrict_iff' isOpen_ball.measurableSet).1 hin
  -- outside the closed unit disc: `f₁` is conformal on `E = (f₂ '' closedBall 0 1)ᶜ`
  set E : Set ℂ := (f₂ '' closedBall 0 1)ᶜ with hEdef
  have hf₂cont : Continuous f₂ := continuousOn_univ.1 hf₂h.1
  have hEo : IsOpen E :=
    ((isCompact_closedBall (0 : ℂ) 1).image hf₂cont).isClosed.isOpen_compl
  have hDE : ∀ w ∈ E, w ∉ D := by
    intro w hwE hwD
    exact hwE (image_mono ball_subset_closedBall hwD)
  have hf₁E : IsKQC f₁ E K₁ := nx_isKQC_restrict hf₁ hEo (subset_univ E)
  have hE0 : ∀ᵐ w ∂(volume.restrict E), complexDilatation f₁ w = 0 := by
    filter_upwards [ae_restrict_of_ae hd₁, self_mem_ae_restrict hEo.measurableSet] with w hw hwE
    rw [hw]
    exact Set.indicator_of_notMem (hDE w hwE) _
  have hholE : DifferentiableOn ℂ f₁ E := nx_differentiableOn_of_dilatation_zero hf₁E hE0
  have hinj₁ : InjOn f₁ E := hf₁.2.2.1.2.1.mono (subset_univ E)
  have hderE : ∀ w ∈ E, deriv f₁ w ≠ 0 :=
    fun w hw => deriv_ne_zero_of_injOn hEo hholE hinj₁ hw
  have hmemE : ∀ z : ℂ, 1 < ‖z‖ → f₂ z ∈ E := by
    rintro z hz ⟨z', hz', hzz'⟩
    have he : z' = z := hf₂h.2.1 (mem_univ z') (mem_univ z) hzz'
    rw [he, mem_closedBall, dist_zero_right] at hz'
    linarith
  have hdiff₂ : ∀ᵐ z, z ∈ ({0}ᶜ : Set ℂ) → DifferentiableAt ℝ f₂ z :=
    (ae_restrict_iff' (measurableSet_singleton (0 : ℂ)).compl).1 (thm9_3_differentiable_ae hf₂)
  -- the unit circle is null
  have hsphere : ∀ᵐ z : ℂ, z ∉ sphere (0 : ℂ) 1 :=
    measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_sphere volume (0 : ℂ) 1)
  filter_upwards [hin', hd₂, hdiff₂, hsphere] with z hz1 hz2 hz3 hz4
  rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
  · -- `z ∈ Δ`: `μ_{f₁ ∘ f₂}(z) = μ_{f₁}(f₂ z) conj(f₂'(z))/f₂'(z)` and the unimodular factors cancel
    have hzD : z ∈ unitDisc := by
      rw [unitDisc, mem_ball, dist_zero_right]
      exact hlt
    obtain ⟨hc, hdf⟩ := hz1 hzD
    have hf₂z : DifferentiableAt ℂ f₂ z := hf₂c.1.differentiableAt (isOpen_ball.mem_nhds hzD)
    have hf₂z' : deriv f₂ z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hf₂c.1 hf₂c.2.1 hzD
    have hf₂zD : f₂ z ∈ D := mem_image_of_mem f₂ hzD
    have hgz : g (f₂ z) = z := hf₂c.2.1.leftInvOn_invFunOn hzD
    have hmul : deriv g (f₂ z) * deriv f₂ z = 1 := t1_deriv_invFunOn_mul isOpen_ball hf₂c hzD
    have hpv : nxPush μ f₂ (f₂ z) = μ z * (conj (deriv g (f₂ z)) / deriv g (f₂ z)) := by
      show D.indicator (fun w => μ (g w) * (conj (deriv g w) / deriv g w)) (f₂ z) = _
      rw [Set.indicator_of_mem hf₂zD, hgz]
    have hconj : conj (deriv g (f₂ z)) * conj (deriv f₂ z) = 1 := by
      rw [← map_mul, hmul, map_one]
    rw [complexDilatation_comp_conformal_right hf₂z hf₂z' hdf, hc, hpv, mul_assoc,
      div_mul_div_comm, hconj, hmul, div_one, mul_one]
  · -- the unit circle
    exact absurd (mem_sphere_zero_iff_norm.2 heq) hz4
  · -- `|z| > 1`: `f₁` is conformal near `f₂ z`, so `μ_{f₁ ∘ f₂}(z) = μ_{f₂}(z) = μ₂(z) = μ(z)`
    have hz0 : z ∈ ({0}ᶜ : Set ℂ) := by
      intro h
      rw [mem_singleton_iff] at h
      rw [h, norm_zero] at hgt
      linarith
    have hwE : f₂ z ∈ E := hmemE z hgt
    have hf₁d : DifferentiableAt ℂ f₁ (f₂ z) := hholE.differentiableAt (hEo.mem_nhds hwE)
    rw [complexDilatation_comp_conformal_left (hz3 hz0) hf₁d (hderE _ hwE), hz2]
    have hzD : z ∈ unitDiscᶜ := by
      rw [mem_compl_iff, unitDisc, mem_ball, dist_zero_right, not_lt]
      exact hgt.le
    exact Set.indicator_of_mem hzD μ

/-! ### Piece E: existence of a normalized solution, q.c. on `Δ` and on `ℂ ∖ {0}` -/

/-- The affine map `u ↦ (u - b) / a` (`a ≠ 0`) maps the plane conformally onto itself. -/
theorem nxE_affine_isConformalOnto {a b : ℂ} (ha : a ≠ 0) :
    IsConformalOnto (fun u => (u - b) / a) univ univ := by
  refine ⟨?_, ?_, ?_⟩
  · exact ((differentiable_id.sub_const b).div_const a).differentiableOn
  · intro u _ v _ huv
    have h := congrArg (fun t => t * a + b) huv
    simp only [div_mul_cancel₀ _ ha, sub_add_cancel] at h
    exact h
  · refine eq_univ_of_forall fun v => ⟨a * v + b, mem_univ _, ?_⟩
    simp only [add_sub_cancel_right]
    exact mul_div_cancel_left₀ v ha

/-- Post-composition with an affine map `u ↦ (u - b) / a` (`a ≠ 0`) does not change the complex
dilatation, at every point (both sides vanish where `f` is not real-differentiable). -/
theorem nxE_complexDilatation_affine {f : ℂ → ℂ} {a b : ℂ} (ha : a ≠ 0) (z : ℂ) :
    complexDilatation (fun ζ => (f ζ - b) / a) z = complexDilatation f z := by
  have hgd : ∀ u : ℂ, HasDerivAt (fun u : ℂ => (u - b) / a) (1 / a) u := fun u =>
    ((hasDerivAt_id u).sub_const b).div_const a
  by_cases hf : DifferentiableAt ℝ f z
  · have h := complexDilatation_comp_conformal_left (g := fun u : ℂ => (u - b) / a) hf
      (hgd (f z)).differentiableAt (by rw [(hgd (f z)).deriv]; exact one_div_ne_zero ha)
    exact h
  · have hf' : ¬ DifferentiableAt ℝ (fun ζ => (f ζ - b) / a) z := by
      intro h
      apply hf
      have heq : f = fun ζ => a * ((f ζ - b) / a) + b := by
        funext ζ
        rw [mul_div_cancel₀ _ ha, sub_add_cancel]
      rw [heq]
      exact (h.const_mul a).add_const b
    simp only [complexDilatation, dz, dzbar, fderiv_zero_of_not_differentiableAt hf,
      fderiv_zero_of_not_differentiableAt hf', zero_apply, mul_zero,
      add_zero, sub_zero, zero_div]

theorem nx_exists {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : IsBeltramiCoeff μ univ k) :
    ∃ F : ℂ → ℂ, IsHomeomorphOnto F univ univ ∧ F 0 = 0 ∧ F 1 = 1 ∧ (∃ K, IsKQC F unitDisc K) ∧
      (∃ K, IsKQC F {0}ᶜ K) ∧ ∀ᵐ z, complexDilatation F z = μ z := by
  -- Step 1: the Theorem 12.2 solution for `μ̃₂`, translated so that `0 ↦ 0`.
  obtain ⟨w, hw, hws, hwd, hwlim⟩ := thm12_2 hk₀ hk (nx_mu2t_compact hk₀ hμ)
  obtain ⟨f, hfdef⟩ : ∃ f : ℂ → ℂ, f = fun ζ => w ζ - w 0 := ⟨_, rfl⟩
  have hf : IsKQC f univ ((1 + k) / (1 - k)) := by
    have h := thm7_1_comp hw
      (isKQC_one_of_conformal isOpen_univ (nxE_affine_isConformalOnto (b := w 0) one_ne_zero))
      (subset_univ _)
    rw [mul_one] at h
    have heq : (fun u : ℂ => (u - w 0) / 1) ∘ w = f := by
      funext ζ
      rw [hfdef, Function.comp_apply, div_one]
    rwa [heq] at h
  have hfs : f '' univ = univ := by
    refine eq_univ_of_forall fun v => ?_
    have hv : v + w 0 ∈ w '' univ := by rw [hws]; exact mem_univ _
    obtain ⟨z, -, hz⟩ := hv
    exact ⟨z, mem_univ _, by simp only [hfdef]; rw [hz, add_sub_cancel_right]⟩
  have hf0 : f 0 = 0 := by simp only [hfdef, sub_self]
  have hflim : Tendsto (fun z => f z / z) (cocompact ℂ) (𝓝 1) := by
    have hinv : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
      rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_cobounded
    have h2 : Tendsto (fun z => w z / z - w 0 * z⁻¹) (cocompact ℂ) (𝓝 (1 - w 0 * 0)) :=
      hwlim.sub (hinv.const_mul (w 0))
    rw [mul_zero, sub_zero] at h2
    refine h2.congr fun z => ?_
    rw [hfdef, sub_div, div_eq_mul_inv (w 0)]
  have hfdil : ∀ᵐ ζ, complexDilatation f ζ = nxMu2t μ ζ := by
    filter_upwards [hwd] with ζ hζ
    rw [← hζ, hfdef]
    simp only [complexDilatation, dz, dzbar, fderiv_sub_const]
  -- Step 2: `f₂ = nxInvConj f`, a plane homeomorphism, `K`-q.c. off `0`, conformal on `Δ`.
  obtain ⟨hf2h, -, hf2K⟩ := nx_f2_homeo hf hfs hf0 hflim
  have hf2d := nx_f2_dilatation hf hfs hf0 hfdil
  have hf2c := nx_f2_conformal hf hfs hf0 hflim hfdil
  have hf2cont : Continuous (nxInvConj f) := continuousOn_univ.mp hf2h.1
  have hb : Bornology.IsBounded (nxInvConj f '' unitDisc) :=
    ((isCompact_closedBall (0 : ℂ) 1).image hf2cont).isBounded.subset
      (image_mono ball_subset_closedBall)
  -- Step 3: the Theorem 12.2 solution for the push-forward of `μ|_Δ` to `f₂(Δ)`.
  obtain ⟨w₁, hw₁, hw₁s, hw₁d, -⟩ := thm12_2 hk₀ hk (nx_push_compact hk₀ hμ hf2c hb)
  have hF₀d := nx_comp_dilatation hw₁ hw₁s hw₁d hf2h hf2K hf2c hf2d
  -- Step 4: normalize `F₀ = w₁ ∘ f₂` by an affine map fixing `0, 1`.
  have hw₁h : IsHomeomorphOnto w₁ univ univ := by
    have h := hw₁.2.2.1
    rwa [hw₁s] at h
  have hF₀h : IsHomeomorphOnto (w₁ ∘ nxInvConj f) univ univ := aqc_isHomeomorphOnto_comp hf2h hw₁h
  have ha : (w₁ ∘ nxInvConj f) 1 - (w₁ ∘ nxInvConj f) 0 ≠ 0 := sub_ne_zero.mpr fun h =>
    one_ne_zero (hF₀h.2.1 (mem_univ _) (mem_univ _) h)
  have hAc := nxE_affine_isConformalOnto (b := (w₁ ∘ nxInvConj f) 0) ha
  have hA1 := isKQC_one_of_conformal isOpen_univ hAc
  refine ⟨(fun u => (u - (w₁ ∘ nxInvConj f) 0) / ((w₁ ∘ nxInvConj f) 1 - (w₁ ∘ nxInvConj f) 0)) ∘
      (w₁ ∘ nxInvConj f),
    aqc_isHomeomorphOnto_comp hF₀h (aqc_isHomeomorphOnto_of_isConformalOnto isOpen_univ hAc),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.comp_apply, sub_self, zero_div]
  · rw [Function.comp_apply]
    exact div_self ha
  · exact ⟨_, thm7_1_comp (thm7_1_comp (isKQC_one_of_conformal isOpen_ball hf2c) hw₁
      (subset_univ _)) hA1 (subset_univ _)⟩
  · exact ⟨_, thm7_1_comp (thm7_1_comp hf2K hw₁ (subset_univ _)) hA1 (subset_univ _)⟩
  · filter_upwards [hF₀d] with z hz
    rw [← hz]
    exact nxE_complexDilatation_affine ha z

/-! ### Piece S: the sharp constant -/

/-- A generalized homeomorphic solution for `μ` is one for every `μ'` equal to `μ` a.e. on `D`
(the Beltrami equation is an a.e. statement). -/
theorem nxS_genHomeoSolution_congr {f μ μ' : ℂ → ℂ} {D : Set ℂ} {p : ℝ≥0∞}
    (hf : IsGenHomeoSolution f μ D p) (h : ∀ᵐ z ∂(volume.restrict D), μ z = μ' z) :
    IsGenHomeoSolution f μ' D p := by
  obtain ⟨hh, g, g', hg, hbe⟩ := hf
  refine ⟨hh, g, g', hg, ?_⟩
  filter_upwards [hbe, h] with z h1 h2
  rw [h1, h2]

/-- Two q.c. maps of an open `U` whose complex dilatations agree a.e. on `U` differ by a conformal
map: `F = φ ∘ χ` on `U` with `φ` conformal from `χ(U)` onto `F(U)` (Theorem 10.2 (⇒) for both maps,
then `same_dilatation_conformal` with the coefficient `μ_χ`, whose bound `(K₂-1)/(K₂+1) < 1`). -/
theorem nxS_factor {F χ : ℂ → ℂ} {U : Set ℂ} {K₁ K₂ : ℝ} (hU : IsOpen U) (hF : IsKQC F U K₁)
    (hχ : IsKQC χ U K₂)
    (hae : ∀ᵐ z ∂(volume.restrict U), complexDilatation F z = complexDilatation χ z) :
    ∃ φ : ℂ → ℂ, IsConformalOnto φ (χ '' U) (F '' U) ∧ ∀ z ∈ U, F z = φ (χ z) := by
  obtain ⟨-, hFsol⟩ := thm10_2_genHomeoSolution_of_isKQC hF
  obtain ⟨hχb, hχsol⟩ := thm10_2_genHomeoSolution_of_isKQC hχ
  have hK₂ : 1 ≤ K₂ := hχ.2.1
  have hk' : (K₂ - 1) / (K₂ + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  exact same_dilatation_conformal hU hk' hχb hχsol (nxS_genHomeoSolution_congr hFsol hae)

/-- Holomorphy is local: if `Φ ∘ e = F` for a homeomorphism `e` of `ℂ` and `F = φ ∘ e` on an open
`U` with `φ` holomorphic on `e(U)`, then `Φ` is complex differentiable at every point of `e(U)`. -/
theorem nxS_differentiableAt {F Φ φ : ℂ → ℂ} (e : ℂ ≃ₜ ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hΦ : ∀ z, Φ (e z) = F z) (hφ : DifferentiableOn ℂ φ (e '' U)) (hFφ : ∀ z ∈ U, F z = φ (e z))
    {w : ℂ} (hw : w ∈ e '' U) : DifferentiableAt ℂ Φ w := by
  have hopen : IsOpen (e '' U) := e.isOpenMap U hU
  have hev : Φ =ᶠ[𝓝 w] φ := by
    filter_upwards [hopen.mem_nhds hw] with v hv
    obtain ⟨z, hz, rfl⟩ := hv
    rw [hΦ, hFφ z hz]
  exact (hφ.differentiableAt (hopen.mem_nhds hw)).congr_of_eventuallyEq hev

theorem nx_sharp {μ F : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : IsBeltramiCoeff μ univ k)
    (hF : IsHomeomorphOnto F univ univ) (hF₁ : ∃ K, IsKQC F unitDisc K) (hF₂ : ∃ K, IsKQC F {0}ᶜ K)
    (hd : ∀ᵐ z, complexDilatation F z = μ z) : IsKQC F univ ((1 + k) / (1 - k)) := by
  have hFs : F '' univ = univ := hF.2.2.1
  have hFh : IsHomeomorphOnto F univ (F '' univ) := by
    rw [hFs]
    exact hF
  refine nx_isKQC_univ_of_balls hFh (fun R _ => ?_)
  obtain ⟨K₁, hFK₁⟩ := hF₁
  obtain ⟨K₂, hFK₂⟩ := hF₂
  -- the comparison map `χ`: Theorem 12.2 for `μ · 1_{B_R}`
  have hν : IsCompactBeltramiCoeff ((ball (0 : ℂ) R).indicator μ) k :=
    gs_indicator_isCompactBeltramiCoeff hk₀ hμ (subset_univ _)
  obtain ⟨χ, hχK, hχs, hχd, -⟩ := thm12_2 hk₀ hk hν
  obtain ⟨e, he⟩ := t1_homeomorph hχK hχs
  subst he
  -- the dilatations of `F` and `χ` agree a.e. on the ball
  have hae : ∀ U : Set ℂ, IsOpen U → U ⊆ ball 0 R →
      ∀ᵐ z ∂(volume.restrict U), complexDilatation F z = complexDilatation (⇑e) z := by
    intro U hU hUB
    filter_upwards [ae_restrict_of_ae hd, ae_restrict_of_ae hχd,
      ae_restrict_mem hU.measurableSet] with z h1 h2 hz
    rw [h1, h2, Set.indicator_of_mem (hUB hz)]
  -- the two pieces `B_R ∩ Δ` and `B_R ∖ {0}`
  have hU₁o : IsOpen (ball (0 : ℂ) R ∩ unitDisc) := isOpen_ball.inter isOpen_ball
  have hU₂o : IsOpen (ball (0 : ℂ) R ∩ {0}ᶜ) := isOpen_ball.inter isOpen_compl_singleton
  obtain ⟨φ₁, hφ₁, hFφ₁⟩ := nxS_factor hU₁o (nx_isKQC_restrict hFK₁ hU₁o inter_subset_right)
    (nx_isKQC_restrict hχK hU₁o (subset_univ _)) (hae _ hU₁o inter_subset_left)
  obtain ⟨φ₂, hφ₂, hFφ₂⟩ := nxS_factor hU₂o (nx_isKQC_restrict hFK₂ hU₂o inter_subset_right)
    (nx_isKQC_restrict hχK hU₂o (subset_univ _)) (hae _ hU₂o inter_subset_left)
  have hunion : ball (0 : ℂ) R ∩ unitDisc ∪ ball (0 : ℂ) R ∩ {0}ᶜ = ball 0 R := by
    rw [← inter_union_distrib_left]
    refine inter_eq_left.mpr (fun z _ => ?_)
    by_cases hz : z = 0
    · left
      rw [hz]
      exact mem_ball_self one_pos
    · right
      exact hz
  -- `Φ = F ∘ χ⁻¹` is conformal on `χ(B_R)`
  set Φ : ℂ → ℂ := F ∘ e.symm with hΦdef
  have hΦe : ∀ z, Φ (e z) = F z := fun z => by
    rw [hΦdef, Function.comp_apply, Homeomorph.symm_apply_apply]
  have hBo : IsOpen (e '' ball (0 : ℂ) R) := e.isOpenMap _ isOpen_ball
  have hΦc : IsConformalOnto Φ (e '' ball (0 : ℂ) R) (F '' ball (0 : ℂ) R) := by
    refine ⟨fun w hw => ?_, ?_, ?_⟩
    · rw [← hunion, image_union] at hw
      rcases hw with hw | hw
      · exact (nxS_differentiableAt e hU₁o hΦe hφ₁.1 hFφ₁ hw).differentiableWithinAt
      · exact (nxS_differentiableAt e hU₂o hΦe hφ₂.1 hFφ₂ hw).differentiableWithinAt
    · rintro _ ⟨z₁, -, rfl⟩ _ ⟨z₂, -, rfl⟩ h
      rw [hΦe, hΦe] at h
      rw [hF.2.1 (mem_univ z₁) (mem_univ z₂) h]
    · rw [image_image]
      exact image_congr (fun z _ => hΦe z)
  have hχB : IsKQC (⇑e) (ball (0 : ℂ) R) ((1 + k) / (1 - k)) :=
    nx_isKQC_restrict hχK isOpen_ball (subset_univ _)
  have hcomp := thm7_1_comp hχB (isKQC_one_of_conformal hBo hΦc) subset_rfl
  rw [mul_one] at hcomp
  have hΦF : Φ ∘ ⇑e = F := funext hΦe
  rwa [hΦF] at hcomp

/-! ### The target -/

/-- **Theorem 13.7**: for every measurable `μ` on `ℂ` with `‖μ‖_∞ ≤ k < 1` there is a unique
quasiconformal map of the plane with complex characteristic `μ` fixing `0, 1, ∞`.

Proved (2026-09-23) along the book's decomposition `μ = μ₁ + μ₂`: the outer part is solved by Theorem 12.2
after conjugation by `z ↦ 1/z` (`nxInvConj`, conformal on `Δ` by a removable singularity), the pushed-forward inner
part by Theorem 12.2 again, and the composition is normalized at `0, 1`.  The sharp constant comes WITHOUT
Theorem 10.2 (⇐): on each disc the solution is a conformal map of a Theorem 12.2 solution (`same_dilatation_conformal`
on two covering pieces; holomorphy is local), and discs exhaust `ℂ` (`nx_sharp`).  Uniqueness is Theorem 13.5. -/
theorem thm13_7_normalized_existence {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμ : IsBeltramiCoeff μ univ k) :
    ∃ f : ℂ → ℂ, IsNormalizedSolution f μ ∧ IsKQC f univ ((1 + k) / (1 - k)) ∧
      ∀ g : ℂ → ℂ, IsNormalizedSolution g μ → g = f := by
  obtain ⟨F, hFh, hF0, hF1, hFΔ, hFc, hFd⟩ := nx_exists hk₀ hk hμ
  have hK := nx_sharp hk₀ hk hμ hFh hFΔ hFc hFd
  have hFs : F '' univ = univ := hFh.2.2.1
  have hFn : IsNormalizedSolution F μ := ⟨⟨_, hK⟩, hFs, hF0, hF1, hFd⟩
  refine ⟨F, hFn, hK, fun g hg => ?_⟩
  obtain ⟨hgq, hgs, hg0, hg1, hgd⟩ := hg
  refine thm13_5_uniqueness_plane hgq ⟨_, hK⟩ hgs hFs ?_ hg0 hg1 hF0 hF1
  filter_upwards [hgd, hFd] with z h1 h2
  rw [h1, h2]

/-- `f` is the quasiconformal self-map of the unit disc with complex characteristic `μ`
fixing the boundary points `1, i, -1`. -/
def IsDiscNormalizedSolution (f μ : ℂ → ℂ) : Prop :=
  IsQuasiconformal f unitDisc ∧ f '' unitDisc = unitDisc ∧
    (∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation f z = μ z) ∧
    ∃ F : ExtPlane → ExtPlane, IsHomeoExtension f unitDisc unitDisc F ∧
      F ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧ F (I : ExtPlane) = (I : ExtPlane) ∧
      F ((-1 : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane)

/-! ## §10 (moved here): Theorems 10.1 and 10.2 (⇐)

These three statements belong to §10 (`Ch01/S10_AnalyticDefinition.lean`) and are unchanged; they live here
because the proof uses Theorem 12.2 and the similarity principle.  The book's proof of Theorem 10.1 does
not show that `f` preserves the orientation of quadrilaterals, which `IsKQC` requires; writing
`f = φ ∘ χ` locally with `χ` from Theorem 12.2 and `φ` conformal supplies it.  (Leader -a7, 2026-09-24.) -/

/-! ### Piece C — generic tools -/

/-- `IsKQC` only depends on the values on `U`. -/
theorem ad_isKQC_congr {f g : ℂ → ℂ} {U : Set ℂ} {K : ℝ} (hg : IsKQC g U K) (h : EqOn f g U) :
    IsKQC f U K := by
  obtain ⟨hU, hK, ⟨hc, hi, -, hinv⟩, hmod⟩ := hg
  have himg : ∀ s ⊆ U, f '' s = g '' s := fun s hs => image_congr fun z hz => h (hs hz)
  have hfi : InjOn f U := hi.congr h.symm
  refine ⟨hU, hK, ⟨hc.congr h, hfi, rfl, ?_⟩, fun Q hQ => ?_⟩
  · rw [himg U subset_rfl]
    refine hinv.congr ?_
    rintro w ⟨z, hz, rfl⟩
    rw [hi.leftInvOn_invFunOn hz, ← h hz, hfi.leftInvOn_invFunOn hz]
  · obtain ⟨Q', ⟨hdom, hvert⟩, hle⟩ := hmod Q hQ
    have hQU : Q.dom ⊆ U := fun z hz => by
      obtain ⟨w, hw, hwz⟩ := hQ (subset_closure ⟨z, hz, rfl⟩)
      rwa [OnePoint.coe_injective hwz] at hw
    refine ⟨Q', ⟨?_, fun i => ?_⟩, hle⟩
    · rw [hdom, himg Q.dom hQU]
    · obtain ⟨z, hz, hzv⟩ := hQ (frontier_subset_closure (Q.isTopQuad.2.1 i))
      rw [hvert i, ← hzv, OnePoint.map_some, OnePoint.map_some, h hz]

/-- Local-to-global over the exhaustion `D ∩ B(0,R)`: every quadrilateral with `Q̄ ⊆ D` lies in one of them. -/
theorem ad_isKQC_of_balls {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hD : IsOpen D)
    (hf : IsHomeomorphOnto f D (f '' D)) (hK : 1 ≤ K)
    (hb : ∀ R : ℝ, 0 < R → IsKQC f (D ∩ ball 0 R) K) : IsKQC f D K := by
  refine ⟨hD, hK, hf, fun Q hQ => ?_⟩
  obtain ⟨R, hR, hsub⟩ :=
    nxT_exists_ball_of_closure_subset (hQ.trans (image_mono (subset_univ D)))
  refine (hb R hR).2.2.2 Q fun p hp => ?_
  obtain ⟨z, hzD, rfl⟩ := hQ hp
  obtain ⟨w, hwB, hw⟩ := hsub hp
  rw [OnePoint.coe_injective hw] at hwB
  exact ⟨z, ⟨hzD, hwB⟩, rfl⟩

/-- The extension by `0` of a Beltrami coefficient on a bounded open set is a compactly supported one. -/
theorem ad_isCompactBeltramiCoeff_indicator {μ : ℂ → ℂ} {U : Set ℂ} {k : ℝ} (hk₀ : 0 ≤ k)
    (hμ : IsBeltramiCoeff μ U k) (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    IsCompactBeltramiCoeff (U.indicator μ) k := by
  obtain ⟨R, hR⟩ := hUb.subset_closedBall 0
  refine ⟨⟨?_, ?_⟩, ⟨R, fun z hz => ?_⟩⟩
  · rw [Measure.restrict_univ, aestronglyMeasurable_indicator_iff hU.measurableSet]
    exact hμ.1
  · rw [Measure.restrict_univ]
    filter_upwards [(ae_restrict_iff' hU.measurableSet).1 hμ.2] with z hz
    by_cases hzU : z ∈ U
    · rw [Set.indicator_of_mem hzU]
      exact hz hzU
    · rw [Set.indicator_of_notMem hzU, norm_zero]
      exact hk₀
  · refine Set.indicator_of_notMem (fun hzU => ?_) _
    have h1 := hR hzU
    rw [mem_closedBall, dist_zero_right] at h1
    linarith

/-- A generalized homeomorphic solution restricts to open subsets. -/
theorem ad_genHomeoSolution_mono {f μ : ℂ → ℂ} {D U : Set ℂ} (hU : IsOpen U) (hUD : U ⊆ D)
    {p : ℝ≥0∞} (hf : IsGenHomeoSolution f μ D p) : IsGenHomeoSolution f μ U p := by
  obtain ⟨⟨hc, hi, -, hinv⟩, g, h, ⟨hloc, fn, hfnC1, hfnU, hfnConv⟩, hbe⟩ := hf
  have hinj' : InjOn f U := hi.mono hUD
  have heq : EqOn (Function.invFunOn f U) (Function.invFunOn f D) (f '' U) := by
    rintro v ⟨z, hz, rfl⟩
    rw [hinj'.leftInvOn_invFunOn hz, hi.leftInvOn_invFunOn (hUD hz)]
  refine ⟨⟨hc.mono hUD, hinj', rfl, (hinv.mono (image_mono hUD)).congr heq⟩, g, h,
    ⟨fun C hCU hCc => hloc C (hCU.trans hUD) hCc, fn, fun n => (hfnC1 n).mono hUD, hfnU.mono hUD,
      fun C hCU hCc => hfnConv C (hCU.trans hUD) hCc⟩, ?_⟩
  exact hbe.filter_mono (ae_mono (Measure.restrict_mono hUD le_rfl))

/-! ### Piece S — Theorem 10.2 (⇐) on a bounded open set -/

/-- Theorem 10.2 (⇐) on a bounded open set, via the Theorem 12.2 solution of `μ·1_U` and the similarity
principle. -/
theorem ad_isKQC_of_genHomeoSolution_bounded {f μ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {k : ℝ} (hk₀ : 0 ≤ k) (hk₁ : k < 1) (hμ : IsBeltramiCoeff μ U k)
    (hf : IsGenHomeoSolution f μ U 2) : IsKQC f U ((1 + k) / (1 - k)) := by
  obtain ⟨χ, hχK, -, hχd, -⟩ :=
    thm12_2 hk₀ hk₁ (ad_isCompactBeltramiCoeff_indicator hk₀ hμ hU hUb)
  have hχU : IsKQC χ U ((1 + k) / (1 - k)) := nx_isKQC_restrict hχK hU (subset_univ _)
  obtain ⟨-, hχsol⟩ := thm10_2_genHomeoSolution_of_isKQC hχU
  have hχsol' : IsGenHomeoSolution χ μ U 2 := by
    refine nxS_genHomeoSolution_congr hχsol ?_
    filter_upwards [ae_restrict_of_ae hχd, ae_restrict_mem hU.measurableSet] with z h1 hz
    rw [h1, Set.indicator_of_mem hz]
  obtain ⟨φ, hφ, hfφ⟩ := same_dilatation_conformal hU hk₁ hμ hχsol' hf
  have hχo : IsOpen (χ '' U) :=
    isOpen_image_of_continuousOn_injOn hU hχU.2.2.1.1 hχU.2.2.1.2.1
  have hcomp := thm7_1_comp hχU (isKQC_one_of_conformal hχo hφ) subset_rfl
  rw [mul_one] at hcomp
  exact ad_isKQC_congr hcomp hfφ

/-! ### Piece L — A.C.L. + (10.1) ⇒ `L₂` generalized homeomorphic solution -/

/-- `∫_σ J_f ≤ m(f(σ))` for an injective map differentiable a.e. (the proof of
`lintegral_jacobian_le_volume_image` without quasiconformality). -/
theorem ad_lintegral_jacobian_le_volume_image {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hinj : InjOn f D) (hdiff : ∀ᵐ z ∂(volume.restrict D), DifferentiableAt ℝ f z) {σ : Set ℂ}
    (hσ : MeasurableSet σ) (hσD : σ ⊆ D) :
    ∫⁻ z in σ, ENNReal.ofReal (jacobian f z) ≤ volume (f '' σ) := by
  have hSm : MeasurableSet (σ ∩ {z | DifferentiableAt ℝ f z}) :=
    hσ.inter (measurableSet_of_differentiableAt ℝ f)
  have hnull : volume (σ \ (σ ∩ {z | DifferentiableAt ℝ f z})) = 0 := by
    have h := hdiff
    rw [ae_restrict_iff' hD.measurableSet, ae_iff] at h
    exact measure_mono_null (fun z hz => fun h' => hz.2 ⟨hz.1, h' (hσD hz.1)⟩) h
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSm
    (fun z hz => hz.2.hasFDerivAt.hasFDerivWithinAt)
    (hinj.mono fun z hz => hσD hz.1) (fun _ => 1)
  simp only [mul_one, setLIntegral_const, one_mul] at hcv
  calc ∫⁻ z in σ, ENNReal.ofReal (jacobian f z)
      = ∫⁻ z in σ ∩ {z | DifferentiableAt ℝ f z}, ENNReal.ofReal (jacobian f z) :=
        setLIntegral_congr (ae_eq_set.2 ⟨hnull, by
          rw [Set.sdiff_eq_empty.2 inter_subset_left, measure_empty]⟩)
    _ ≤ ∫⁻ z in σ ∩ {z | DifferentiableAt ℝ f z}, ENNReal.ofReal |(fderiv ℝ f z).det| := by
        refine setLIntegral_mono' hSm fun z hz => ENNReal.ofReal_le_ofReal ?_
        have e : (fderiv ℝ f z).det = jacobian f z := det_fderiv_eq_jacobian hz.2
        rw [e]
        exact le_abs_self _
    _ = volume (f '' (σ ∩ {z | DifferentiableAt ℝ f z})) := hcv.symm
    _ ≤ volume (f '' σ) := measure_mono (image_mono inter_subset_left)

/-- An A.C.L. homeomorphism satisfying (10.1) a.e. is an `L₂` generalized homeomorphic solution of the
Beltrami equation with its own complex characteristic, `|μ_f| ≤ (K-1)/(K+1)`. -/
theorem ad_genHomeoSolution_of_isACL {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) {K : ℝ} (hK : 1 ≤ K)
    (hf : IsHomeomorphOnto f D (f '' D)) (hacl : IsACL f D)
    (hineq : ∀ᵐ z ∂(volume.restrict D), ‖dz f z‖ + ‖dzbar f z‖ ≤ K * (‖dz f z‖ - ‖dzbar f z‖)) :
    IsBeltramiCoeff (complexDilatation f) D ((K - 1) / (K + 1)) ∧
      IsGenHomeoSolution f (complexDilatation f) D 2 := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  -- Menchoff: `f` is differentiable a.e.
  have hdiff : ∀ᵐ z ∂(volume.restrict D), DifferentiableAt ℝ f z :=
    lemma9_1_menchoff hD hf (cr_p_partials_ae_of_isACL hD hacl)
  -- `(|∂_z f| + |∂_{z̄} f|)² ≤ K J_f` almost everywhere, from (10.1)
  have hsq : ∀ᵐ z ∂(volume.restrict D), (‖dz f z‖ + ‖dzbar f z‖) ^ 2 ≤ K * jacobian f z := by
    filter_upwards [hineq] with z hz
    have h0 : 0 ≤ ‖dz f z‖ + ‖dzbar f z‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    unfold jacobian
    nlinarith
  have hkey : ∀ σ : Set ℂ, MeasurableSet σ → σ ⊆ D →
      ∫⁻ z in σ, ENNReal.ofReal ((‖dz f z‖ + ‖dzbar f z‖) ^ 2) ≤
        ENNReal.ofReal K * volume (f '' σ) := by
    intro σ hσ hσD
    calc ∫⁻ z in σ, ENNReal.ofReal ((‖dz f z‖ + ‖dzbar f z‖) ^ 2)
        ≤ ∫⁻ z in σ, ENNReal.ofReal K * ENNReal.ofReal (jacobian f z) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_of_ae_restrict_of_subset hσD hsq] with z hz
          rw [← ENNReal.ofReal_mul hK0]
          exact ENNReal.ofReal_le_ofReal hz
      _ = ENNReal.ofReal K * ∫⁻ z in σ, ENNReal.ofReal (jacobian f z) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal K * volume (f '' σ) := by
          gcongr
          exact ad_lintegral_jacobian_le_volume_image hD hf.2.1 hdiff hσ hσD
  -- the classical partial derivatives are locally square integrable, so Lemma 9.2 (⇒) applies
  have hgp : HasGenPartials f (partialX f) (partialY f) D 2 := by
    refine lemma9_2_genPartials_of_isACL hD one_le_two (by simp) hacl fun C hCD hC => ?_
    have hdiffC : ∀ᵐ z ∂(volume.restrict C), DifferentiableAt ℝ f z :=
      ae_restrict_of_ae_restrict_of_subset hCD hdiff
    have hgm : Measurable fun z => ‖dz f z‖ + ‖dzbar f z‖ :=
      (measurable_dz f).norm.add (measurable_dzbar f).norm
    have hfin : volume (f '' C) < ⊤ :=
      (hC.image_of_continuousOn (hf.1.mono hCD)).measure_lt_top
    have hg : MemLp (fun z => ‖dz f z‖ + ‖dzbar f z‖) 2 (volume.restrict C) := by
      rw [memLp_two_iff_integrable_sq hgm.aestronglyMeasurable]
      refine ⟨(hgm.pow_const 2).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => sq_nonneg _)]
      exact (hkey C hC.isClosed.measurableSet hCD).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
    have hbound : ∀ w z, DifferentiableAt ℝ f z → ‖w‖ = 1 →
        ‖fderiv ℝ f z w‖ ≤ ‖‖dz f z‖ + ‖dzbar f z‖‖ := fun w z hz hw => by
      rw [fderiv_eq_dz_dzbar hz, Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      calc ‖dz f z * w + dzbar f z * conj w‖
          ≤ ‖dz f z * w‖ + ‖dzbar f z * conj w‖ := norm_add_le _ _
        _ = ‖dz f z‖ + ‖dzbar f z‖ := by rw [norm_mul, norm_mul, norm_conj, hw, mul_one, mul_one]
    refine ⟨hg.of_le ?_ ?_, hg.of_le ?_ ?_⟩
    · exact (measurable_fderiv_apply_const ℝ f (1 : ℂ)).aestronglyMeasurable.congr
        (hdiffC.mono fun z hz => (partialX_eq_of_differentiableAt hz).symm)
    · filter_upwards [hdiffC] with z hz
      rw [partialX_eq_of_differentiableAt hz]
      exact hbound 1 z hz (by simp)
    · exact (measurable_fderiv_apply_const ℝ f I).aestronglyMeasurable.congr
        (hdiffC.mono fun z hz => (partialY_eq_of_differentiableAt hz).symm)
    · filter_upwards [hdiffC] with z hz
      rw [partialY_eq_of_differentiableAt hz]
      exact hbound I z hz (by simp)
  refine ⟨⟨((measurable_dzbar f).div (measurable_dz f)).aestronglyMeasurable, ?_⟩,
    hf, partialX f, partialY f, hgp, ?_⟩
  · -- `|μ_f| ≤ (K-1)/(K+1)`: from (10.1), `(K+1)|∂_{z̄} f| ≤ (K-1)|∂_z f|`
    filter_upwards [hineq] with z hz
    rcases eq_or_ne (dz f z) 0 with h0 | h0
    · rw [complexDilatation, h0, div_zero, norm_zero]
      exact div_nonneg (by linarith) hK1.le
    · have hp : 0 < ‖dz f z‖ := norm_pos_iff.2 h0
      rw [complexDilatation, norm_div, div_le_div_iff₀ hp hK1]
      linarith
  · -- the Beltrami equation: at points of differentiability the generalized derivatives are the
    -- classical ones, and `∂_z f = 0` forces `∂_{z̄} f = 0` by (10.1)
    filter_upwards [hdiff, hineq] with z hz hz'
    have hx : partialX f z = dz f z + dzbar f z := by
      rw [partialX_eq_of_differentiableAt hz, fderiv_eq_dz_dzbar hz]
      simp
    have hy : partialY f z = I * (dz f z - dzbar f z) := by
      rw [partialY_eq_of_differentiableAt hz, fderiv_eq_dz_dzbar hz, Complex.conj_I]
      ring
    have hgz : genDz (partialX f) (partialY f) z = dz f z := by
      rw [genDz, hx, hy]
      linear_combination (-(dz f z - dzbar f z) / 2) * I_sq
    have hgzb : genDzbar (partialX f) (partialY f) z = dzbar f z := by
      rw [genDzbar, hx, hy]
      linear_combination ((dz f z - dzbar f z) / 2) * I_sq
    rw [hgz, hgzb, complexDilatation]
    rcases eq_or_ne (dz f z) 0 with h0 | h0
    · rw [h0, norm_zero] at hz'
      rw [h0, mul_zero]
      have hb : ‖dzbar f z‖ ≤ 0 := by nlinarith [norm_nonneg (dzbar f z)]
      exact norm_le_zero_iff.1 hb
    · rw [div_mul_cancel₀ _ h0]

/-! ### Targets (moved from S10; statements byte-identical up to the prime) -/

/-- **Theorem 10.2** (⇐).  An `L₂` generalized homeomorphic solution of `∂_{z̄} w = μ ∂_z w`
with `|μ| ≤ k < 1` is `(1+k)/(1-k)`-quasiconformal.

Proved (2026-09-24; moved here from S10): on each `D ∩ B(0,R)` compare with the Theorem 12.2 solution
`χ` of `μ·1_{D ∩ B(0,R)}`; the similarity principle (`same_dilatation_conformal`) gives `f = φ ∘ χ` with
`φ` conformal, so `f` is `(1+k)/(1-k)`-q.c. there, sense preservation included
(`ad_isKQC_of_genHomeoSolution_bounded`); exhaust `D` (`ad_isKQC_of_balls`). -/
theorem thm10_2_isKQC_of_genHomeoSolution {f μ : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) {k : ℝ}
    (hk₀ : 0 ≤ k) (hk₁ : k < 1) (hμ : IsBeltramiCoeff μ D k) (hf : IsGenHomeoSolution f μ D 2) :
    IsKQC f D ((1 + k) / (1 - k)) := by
  have hK : (1 : ℝ) ≤ (1 + k) / (1 - k) := (one_le_div (by linarith)).2 (by linarith)
  refine ad_isKQC_of_balls hD hf.1 hK fun R _ => ?_
  have hU : IsOpen (D ∩ ball (0 : ℂ) R) := hD.inter isOpen_ball
  exact ad_isKQC_of_genHomeoSolution_bounded hU (isBounded_ball.subset inter_subset_right) hk₀ hk₁
    (gs_isBeltramiCoeff_mono hμ inter_subset_left) (ad_genHomeoSolution_mono hU inter_subset_left hf)

/-- **Theorem 10.1**: a homeomorphism `f` of a domain `D` onto `D'` is `K`-quasiconformal iff
(i) `f` is A.C.L. in `D` and (ii) `|∂_z f| + |∂_{z̄} f| ≤ K(|∂_z f| - |∂_{z̄} f|)` a.e. in `D`.

Proved (2026-09-24; moved here from S10): necessity is Theorems 9.1 and 9.4; for sufficiency (i) and (ii)
make `f` an `L₂` generalized homeomorphic solution with `|μ_f| ≤ (K-1)/(K+1)`
(`ad_genHomeoSolution_of_isACL`: Menchoff, `(|f_z|+|f_z̄|)² ≤ K J_f`, `∫ J_f ≤ m(f(σ))`, Lemma 9.2), and
Theorem 10.2 (⇐) gives `K`-quasiconformality. -/
theorem thm10_1_isKQC_iff {f : ℂ → ℂ} {D D' : Set ℂ} (hD : IsOpen D) {K : ℝ} (hK : 1 ≤ K)
    (hf : IsHomeomorphOnto f D D') :
    IsKQC f D K ↔ IsACL f D ∧
      ∀ᵐ z ∂(volume.restrict D), ‖dz f z‖ + ‖dzbar f z‖ ≤ K * (‖dz f z‖ - ‖dzbar f z‖) := by
  refine ⟨fun h => ⟨thm9_1_isACL h, thm9_4_dilatation_ae h⟩, fun ⟨hacl, hineq⟩ => ?_⟩
  have hf' : IsHomeomorphOnto f D (f '' D) := by
    rw [hf.2.2.1]
    exact hf
  obtain ⟨hb, hs⟩ := ad_genHomeoSolution_of_isACL hD hK hf' hacl hineq
  have hk₀ : 0 ≤ (K - 1) / (K + 1) := div_nonneg (by linarith) (by linarith)
  have hk₁ : (K - 1) / (K + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have e : (1 + (K - 1) / (K + 1)) / (1 - (K - 1) / (K + 1)) = K := by
    field_simp
    ring
  simpa only [e] using thm10_2_isKQC_of_genHomeoSolution hD hk₀ hk₁ hb hs

/-- **Theorem 10.2**: `f` is quasiconformal in `D` iff it is an `L₂` generalized homeomorphic
solution of some Beltrami equation `∂_{z̄} w = μ ∂_z w` with `‖μ‖_∞ < 1`.

Proved (2026-09-24; moved here from S10 together with Theorem 10.2 (⇐)). -/
theorem thm10_2_isQuasiconformal_iff {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) :
    IsQuasiconformal f D ↔
      ∃ (μ : ℂ → ℂ) (k : ℝ), 0 ≤ k ∧ k < 1 ∧ IsBeltramiCoeff μ D k ∧ IsGenHomeoSolution f μ D 2 := by
  constructor
  · rintro ⟨K, hK⟩
    have h1 : (1 : ℝ) ≤ K := hK.2.1
    obtain ⟨hb, hs⟩ := thm10_2_genHomeoSolution_of_isKQC hK
    exact ⟨complexDilatation f, (K - 1) / (K + 1), div_nonneg (by linarith) (by linarith),
      (div_lt_one (by linarith)).2 (by linarith), hb, hs⟩
  · rintro ⟨μ, k, hk0, hk1, hμ, hsol⟩
    exact ⟨(1 + k) / (1 - k), thm10_2_isKQC_of_genHomeoSolution hD hk0 hk1 hμ hsol⟩

/-! ## §13.8 (moved here): Theorem 13.8, continuous dependence on parameters

Development for `thm13_8_ahlfors_bers_continuous` (leader -a7 / session "worker", 2026-09-24).  It uses
Theorems 10.1 and 10.2 (⇐) above (reflection across the unit circle, uniform constants) and Grötzsch's
Theorem 5.1 (S05).  Helpers are prefixed `ab`. -/

/-- The disc automorphism `w ↦ λ (w - a)/(1 - ā w)`, `λ = (1 - ā)/(1 - a)`: it sends `a ↦ 0` and fixes `1`. -/
def abMob (a w : ℂ) : ℂ := (1 - conj a) / (1 - a) * ((w - a) / (1 - conj a * w))

/-! ### Piece C — dilatation of `f ∘ g⁻¹` -/

/-- A.e. on `D`, the inverse `invFunOn g D` of a q.c. map `g` is real-differentiable at `g z`:
Theorem 9.3 for the q.c. inverse (`thm7_2_inv`), pulled back to `D` by Lusin's property (N) of the
inverse (step 2 of the proof of `eq13_5_7_inverse`). -/
theorem abC_differentiableAt_invFunOn_ae {g : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hg : IsKQC g D K) :
    ∀ᵐ z ∂(volume.restrict D), DifferentiableAt ℝ (Function.invFunOn g D) (g z) := by
  set φ : ℂ → ℂ := Function.invFunOn g D with hφdef
  have hD : IsOpen D := hg.1
  have hφ : IsKQC φ (g '' D) K := thm7_2_inv hg
  have hD' : IsOpen (g '' D) := hφ.1
  have hleft : LeftInvOn φ g D := hg.2.2.1.2.1.leftInvOn_invFunOn
  have hφae : ∀ᵐ w ∂(volume.restrict (g '' D)), DifferentiableAt ℝ φ w :=
    thm9_3_differentiable_ae hφ
  rw [ae_restrict_iff' hD'.measurableSet, ae_iff] at hφae
  set N : Set ℂ := {w | ¬ (w ∈ g '' D → DifferentiableAt ℝ φ w)} with hNdef
  have hNsub : N ⊆ g '' D := fun w hw => by
    by_contra h
    exact hw (fun h' => absurd h' h)
  have hφN : volume (φ '' N) = 0 := ac_n_volume_image_null_of_isKQC hφ hNsub hφae
  rw [ae_restrict_iff' hD.measurableSet, ae_iff]
  refine measure_mono_null ?_ hφN
  intro z hz
  simp only [Set.mem_ofPred_eq, Classical.not_imp] at hz
  obtain ⟨hzD, hnd⟩ := hz
  refine ⟨g z, ?_, hleft hzD⟩
  simp only [hNdef, Set.mem_ofPred_eq, Classical.not_imp]
  exact ⟨⟨z, hzD, rfl⟩, hnd⟩

/-- The algebra of piece C.  With `A ζ = a ζ + b ζ̄` (inverse `ζ ↦ (ā ζ - b ζ̄)/J`, `J = |a|² - |b|²`) and
`B ζ = c ζ + d ζ̄`, the Wirtinger coefficients of `B ∘ A⁻¹` are `(c ā - d b̄)/J` and `(d a - c b)/J`; since
`c ā - d b̄ = c ā (1 - conj(b/a)(d/c))` and `d a - c b = c a (d/c - b/a)`, the modulus of their quotient
times `|1 - conj(b/a)(d/c)|` is `|d/c - b/a|` (the denominator is `≠ 0` because `|b| < |a|`, `|d| < |c|`). -/
theorem abC_norm_identity {a b c d : ℂ} {J : ℝ} (hJ : J ≠ 0) (hba : ‖b‖ < ‖a‖) (hdc : ‖d‖ < ‖c‖) :
    ‖(c * (-b / J) + d * conj (conj a / J)) / (c * (conj a / J) + d * conj (-b / J))‖ *
        ‖1 - conj (b / a) * (d / c)‖ = ‖d / c - b / a‖ := by
  have ha : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at hba
    exact (norm_nonneg b).not_gt hba
  have hc : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdc
    exact (norm_nonneg d).not_gt hdc
  have hJc : (J : ℂ) ≠ 0 := by exact_mod_cast hJ
  have hca : conj a ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr ha
  have hP : c * conj a - d * conj b ≠ 0 := by
    intro h
    have h' : c * conj a = d * conj b := by linear_combination h
    have hn := congrArg norm h'
    rw [norm_mul, norm_mul, norm_conj, norm_conj] at hn
    have hlt : ‖d‖ * ‖b‖ < ‖c‖ * ‖a‖ := mul_lt_mul'' hdc hba (norm_nonneg _) (norm_nonneg _)
    linarith
  have e1 : c * (conj a / J) + d * conj (-b / J) = (c * conj a - d * conj b) / J := by
    simp only [map_div₀, map_neg, Complex.conj_ofReal]
    ring
  have e2 : c * (-b / J) + d * conj (conj a / J) = (d * a - c * b) / J := by
    simp only [map_div₀, Complex.conj_ofReal, Complex.conj_conj]
    ring
  have e3 : 1 - conj (b / a) * (d / c) = (c * conj a - d * conj b) / (c * conj a) := by
    rw [map_div₀]
    field_simp
  have e4 : d / c - b / a = (d * a - c * b) / (c * a) := by
    field_simp
  rw [e1, e2, e3, e4, div_div_div_cancel_right₀ hJc, norm_div, norm_div, norm_div, norm_mul,
    norm_mul, norm_conj]
  have hPn : ‖c * conj a - d * conj b‖ ≠ 0 := norm_ne_zero_iff.2 hP
  have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc
  have han : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha
  field_simp

/-- `|μ_{f∘g⁻¹}(g z)| · |1 - conj(μ_g) μ_f| = |μ_f - μ_g|` a.e. -/
theorem ab_comp_inv_dilatation {f g : ℂ → ℂ} {D : Set ℂ} {K₁ K₂ : ℝ} (hf : IsKQC f D K₁)
    (hg : IsKQC g D K₂) :
    ∀ᵐ z ∂(volume.restrict D),
      ‖complexDilatation (f ∘ Function.invFunOn g D) (g z)‖ *
          ‖1 - conj (complexDilatation g z) * complexDilatation f z‖ =
        ‖complexDilatation f z - complexDilatation g z‖ := by
  have hD : IsOpen D := hg.1
  have hleft : LeftInvOn (Function.invFunOn g D) g D := hg.2.2.1.2.1.leftInvOn_invFunOn
  filter_upwards [thm9_3_differentiable_ae hf, thm9_3_differentiable_ae hg,
    abC_differentiableAt_invFunOn_ae hg, thm9_6_cor2_jacobian_pos hf,
    thm9_6_cor2_jacobian_pos hg, ae_restrict_mem hD.measurableSet] with z hfz hgz hφz hJf hJg hzD
  set φ : ℂ → ℂ := Function.invFunOn g D with hφdef
  have hφgz : φ (g z) = z := hleft hzD
  -- `φ'(g z) = g'(z)⁻¹` in Wirtinger form (13.5)–(13.6)
  have hid : φ ∘ g =ᶠ[𝓝 z] id :=
    Filter.eventually_of_mem (hD.mem_nhds hzD) fun w hw => hleft hw
  have hBA : (fderiv ℝ φ (g z)).comp (fderiv ℝ g z) = ContinuousLinearMap.id ℝ ℂ :=
    (hφz.hasFDerivAt.comp z hgz.hasFDerivAt).unique ((hasFDerivAt_id z).congr_of_eventuallyEq hid)
  obtain ⟨hp, hq, -⟩ := ie_wirtinger_of_comp_eq_id hgz hφz hBA
  -- the chain rule (6.2) for `f ∘ φ` at `g z`
  have hfφ : DifferentiableAt ℝ f (φ (g z)) := by
    rw [hφgz]
    exact hfz
  have h1 := eq6_2_dz_comp hφz hfφ
  have h2 := eq6_2_dzbar_comp hφz hfφ
  obtain ⟨c1, c2⟩ := eq6_3 hφz
  rw [← c2, hφgz, hp, hq] at h1
  rw [← c1, hφgz, hp, hq] at h2
  -- positive Jacobians: `|∂_{z̄}| < |∂_z|` for `f` and `g`
  have hba : ‖dzbar g z‖ < ‖dz g z‖ := by
    unfold jacobian at hJg
    nlinarith [norm_nonneg (dz g z), norm_nonneg (dzbar g z)]
  have hdc : ‖dzbar f z‖ < ‖dz f z‖ := by
    unfold jacobian at hJf
    nlinarith [norm_nonneg (dz f z), norm_nonneg (dzbar f z)]
  unfold complexDilatation
  rw [h1, h2]
  exact abC_norm_identity hJg.ne' hba hdc

/-! ### Piece Q — the quotient `f₁ ∘ f₀⁻¹` of two normalized disc solutions -/

/-- A normalized disc solution for a coefficient bounded by `k < 1` is `(1+k)/(1-k)`-q.c. on `Δ`:
Theorem 10.2 (⇒) for its own dilatation, the coefficient switched to `μ` (equal a.e.), then
Theorem 10.2 (⇐). -/
theorem abQ_isKQC {f μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμ : IsBeltramiCoeff μ unitDisc k) (hf : IsDiscNormalizedSolution f μ) :
    IsKQC f unitDisc ((1 + k) / (1 - k)) := by
  obtain ⟨K, hK⟩ := hf.1
  have hsol : IsGenHomeoSolution f μ unitDisc 2 :=
    nxS_genHomeoSolution_congr (thm10_2_genHomeoSolution_of_isKQC hK).2 hf.2.2.1
  exact thm10_2_isKQC_of_genHomeoSolution isOpen_ball hk₀ hk hμ hsol

/-- A point of the closed unit disc lies in the closure of `Δ` in `ℂ̄`. -/
theorem abQ_coe_mem_closure {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ((z : ℂ) : ExtPlane) ∈ closure (toExt unitDisc) := by
  have h1 : z ∈ closure unitDisc := by
    rw [unitDisc, closure_ball (0 : ℂ) one_ne_zero]
    exact mem_closedBall_zero_iff.2 hz
  exact image_closure_subset_closure_image OnePoint.continuous_coe ⟨z, h1, rfl⟩

/-- A fixed point of a map injective on `C` is fixed by its inverse `invFunOn F C`. -/
theorem abQ_invFunOn_fixed {F : ExtPlane → ExtPlane} {C : Set ExtPlane} (hF : InjOn F C)
    {p : ExtPlane} (hp : p ∈ C) (hFp : F p = p) : Function.invFunOn F C p = p := by
  have h := hF.leftInvOn_invFunOn hp
  rwa [hFp] at h

/-- The quotient of two normalized disc solutions is a `K₀²`-q.c. self-map of `Δ` whose boundary extension
fixes `1, i, -1`, with dilatation controlled by `|μ₁ - μ₀|`. -/
theorem ab_quotient {f₁ f₀ μ₁ μ₀ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμ₁ : IsBeltramiCoeff μ₁ unitDisc k) (hμ₀ : IsBeltramiCoeff μ₀ unitDisc k)
    (hf₁ : IsDiscNormalizedSolution f₁ μ₁) (hf₀ : IsDiscNormalizedSolution f₀ μ₀) :
    IsKQC (f₁ ∘ Function.invFunOn f₀ unitDisc) unitDisc (((1 + k) / (1 - k)) ^ 2) ∧
      (f₁ ∘ Function.invFunOn f₀ unitDisc) '' unitDisc = unitDisc ∧
      (∃ H : ExtPlane → ExtPlane,
        IsHomeoExtension (f₁ ∘ Function.invFunOn f₀ unitDisc) unitDisc unitDisc H ∧
          H ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧ H (I : ExtPlane) = (I : ExtPlane) ∧
          H ((-1 : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane)) ∧
      ∀ᵐ z ∂(volume.restrict unitDisc),
        ‖complexDilatation (f₁ ∘ Function.invFunOn f₀ unitDisc) (f₀ z)‖ * (1 - k) ≤ ‖μ₁ z - μ₀ z‖ := by
  have hΔ : IsOpen unitDisc := isOpen_ball
  have hK1 : IsKQC f₁ unitDisc ((1 + k) / (1 - k)) := abQ_isKQC hk₀ hk hμ₁ hf₁
  have hK0 : IsKQC f₀ unitDisc ((1 + k) / (1 - k)) := abQ_isKQC hk₀ hk hμ₀ hf₀
  obtain ⟨-, himg₁, hd₁, F₁, hF₁, hF₁1, hF₁I, hF₁m⟩ := hf₁
  obtain ⟨-, himg₀, hd₀, F₀, hF₀, hF₀1, hF₀I, hF₀m⟩ := hf₀
  have hC := ab_comp_inv_dilatation hK1 hK0
  set φ : ℂ → ℂ := Function.invFunOn f₀ unitDisc with hφdef
  have hleft : LeftInvOn φ f₀ unitDisc := hK0.2.2.1.2.1.leftInvOn_invFunOn
  have hφimg : φ '' unitDisc = unitDisc := by
    have h := hleft.image_image
    rwa [himg₀] at h
  have hφK : IsKQC φ unitDisc ((1 + k) / (1 - k)) := by
    have h := thm7_2_inv hK0
    rwa [himg₀] at h
  have hmaps : MapsTo φ unitDisc unitDisc := fun w hw => by
    have h := mem_image_of_mem φ hw
    rwa [hφimg] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Theorem 7.2 (inverse) and Theorem 7.1 (composition)
    have h := thm7_1_comp hφK hK1 hφimg.subset
    rw [sq]
    exact h
  · rw [image_comp, hφimg, himg₁]
  · -- `H = F₁ ∘ F₀⁻¹` on the closed disc
    have hhom : IsHomeomorphOnto f₀ unitDisc unitDisc := by
      have h := hK0.2.2.1
      rwa [himg₀] at h
    have hinv := uq_isHomeoExtension_invFunOn hΔ hΔ hhom hF₀
    refine ⟨F₁ ∘ Function.invFunOn F₀ (closure (toExt unitDisc)), hF₁.comp hinv hmaps, ?_, ?_, ?_⟩
    · show F₁ (Function.invFunOn F₀ (closure (toExt unitDisc)) ((1 : ℂ) : ExtPlane)) = _
      rw [abQ_invFunOn_fixed hF₀.2.2.1 (abQ_coe_mem_closure (by simp)) hF₀1, hF₁1]
    · show F₁ (Function.invFunOn F₀ (closure (toExt unitDisc)) (I : ExtPlane)) = _
      rw [abQ_invFunOn_fixed hF₀.2.2.1 (abQ_coe_mem_closure (by simp)) hF₀I, hF₁I]
    · show F₁ (Function.invFunOn F₀ (closure (toExt unitDisc)) ((-1 : ℂ) : ExtPlane)) = _
      rw [abQ_invFunOn_fixed hF₀.2.2.1 (abQ_coe_mem_closure (by simp)) hF₀m, hF₁m]
  · -- piece C with `μ_{f₁} = μ₁`, `μ_{f₀} = μ₀` and `|1 - conj(μ₀) μ₁| ≥ 1 - k² ≥ 1 - k`
    filter_upwards [hC, hd₁, hd₀, hμ₁.2, hμ₀.2] with z hz h1 h0 hb1 hb0
    rw [h1, h0] at hz
    have hge : 1 - k ≤ ‖1 - conj (μ₀ z) * μ₁ z‖ := by
      have h2 : ‖conj (μ₀ z) * μ₁ z‖ ≤ k * k := by
        rw [norm_mul, norm_conj]
        exact mul_le_mul hb0 hb1 (norm_nonneg _) hk₀
      have h3 : ‖(1 : ℂ)‖ - ‖conj (μ₀ z) * μ₁ z‖ ≤ ‖1 - conj (μ₀ z) * μ₁ z‖ :=
        norm_sub_norm_le _ _
      rw [norm_one] at h3
      nlinarith
    calc ‖complexDilatation (f₁ ∘ φ) (f₀ z)‖ * (1 - k)
        ≤ ‖complexDilatation (f₁ ∘ φ) (f₀ z)‖ * ‖1 - conj (μ₀ z) * μ₁ z‖ :=
          mul_le_mul_of_nonneg_left hge (norm_nonneg _)
      _ = ‖μ₁ z - μ₀ z‖ := hz

/-! ### Piece N — normalization at `0` inside the disc -/

/-- `1 - a ≠ 0` for `a` in the open unit disc. -/
theorem abN_one_sub_ne_zero {a : ℂ} (ha : ‖a‖ < 1) : (1 : ℂ) - a ≠ 0 := by
  intro h
  have h' : a = 1 := by linear_combination -h
  rw [h', norm_one] at ha
  exact lt_irrefl _ ha

/-- The denominator `1 - ā w` of `abMob a` does not vanish for `‖a‖ < 1`, `‖w‖ ≤ 1`. -/
theorem abN_den_ne_zero {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1) : (1 : ℂ) - conj a * w ≠ 0 := by
  intro h
  have h1 : conj a * w = 1 := by linear_combination -h
  have h2 : ‖conj a * w‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖a‖ * ‖w‖ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hw (norm_nonneg a)
      _ = ‖a‖ := mul_one _
      _ < 1 := ha
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

/-- The rotation factor `λ = (1 - ā)/(1 - a)` of `abMob a` is unimodular. -/
theorem abN_norm_lam {a : ℂ} (ha : ‖a‖ < 1) : ‖(1 - conj a) / (1 - a)‖ = 1 := by
  have h1 : (1 : ℂ) - conj a = conj (1 - a) := by simp
  rw [norm_div, h1, Complex.norm_conj, div_self (norm_ne_zero_iff.2 (abN_one_sub_ne_zero ha))]

/-- `abMob a` is a conformal map of `Δ` onto itself (a rotation of the Blaschke factor). -/
theorem abN_isConformalOnto {a : ℂ} (ha : ‖a‖ < 1) :
    IsConformalOnto (abMob a) unitDisc unitDisc := by
  have hc1 : ‖(1 - conj a) / (1 - a)‖ = 1 := abN_norm_lam ha
  have hc0 : (1 - conj a) / (1 - a) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc1
    exact zero_ne_one hc1
  have hfun : abMob a = fun w => (1 - conj a) / (1 - a) * blaschke a w := rfl
  obtain ⟨hd, hi, hs⟩ := isConformalOnto_blaschke ha
  rw [hfun]
  refine ⟨hd.const_mul _, fun x hx y hy hxy => hi hx hy (mul_left_cancel₀ hc0 hxy), ?_⟩
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hbz : blaschke a z ∈ unitDisc := by rw [← hs]; exact mem_image_of_mem _ hz
    refine mem_ball_zero_iff.2 ?_
    rw [norm_mul, hc1, one_mul]
    exact mem_ball_zero_iff.1 hbz
  · intro hw
    have hw' : ((1 - conj a) / (1 - a))⁻¹ * w ∈ unitDisc := by
      refine mem_ball_zero_iff.2 ?_
      rw [norm_mul, norm_inv, hc1, inv_one, one_mul]
      exact mem_ball_zero_iff.1 hw
    rw [← hs] at hw'
    obtain ⟨z, hz, hzw⟩ := hw'
    refine ⟨z, hz, ?_⟩
    simp only
    rw [hzw, mul_inv_cancel_left₀ hc0]

/-- The derivative of `abMob a` on the disc. -/
theorem abN_hasDerivAt {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    HasDerivAt (abMob a)
      ((1 - conj a) / (1 - a) * ((1 - a * conj a) / (1 - conj a * w) ^ 2)) w :=
  (hasDerivAt_blaschke ha hw).const_mul ((1 - conj a) / (1 - a))

/-- The derivative of `abMob a` does not vanish on the disc. -/
theorem abN_deriv_ne_zero {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) : deriv (abMob a) w ≠ 0 := by
  rw [(abN_hasDerivAt ha hw).deriv]
  refine mul_ne_zero (div_ne_zero ?_ (abN_one_sub_ne_zero ha))
    (div_ne_zero (one_sub_mul_conj_ne_zero ha) (pow_ne_zero 2 (blaschke_den_ne_zero ha hw)))
  exact abN_one_sub_ne_zero (by rwa [Complex.norm_conj])

/-- `abMob a` is the fractional linear map with coefficients `(λ, -λa, -ā, 1)`. -/
theorem abN_mobiusFn_eq (a : ℂ) :
    mobiusFn ((1 - conj a) / (1 - a)) (-((1 - conj a) / (1 - a) * a)) (-conj a) 1 = abMob a := by
  funext w
  simp only [mobiusFn, abMob]
  rw [mul_div_assoc']
  congr 1 <;> ring

/-- The determinant of the coefficients of `abMob a` does not vanish for `‖a‖ < 1`. -/
theorem abN_det_ne_zero {a : ℂ} (ha : ‖a‖ < 1) :
    (1 - conj a) / (1 - a) * 1 - -((1 - conj a) / (1 - a) * a) * -conj a ≠ 0 := by
  have e : (1 - conj a) / (1 - a) * 1 - -((1 - conj a) / (1 - a) * a) * -conj a =
      (1 - conj a) / (1 - a) * (1 - a * conj a) := by ring
  rw [e]
  refine mul_ne_zero (div_ne_zero ?_ (abN_one_sub_ne_zero ha)) (one_sub_mul_conj_ne_zero ha)
  exact abN_one_sub_ne_zero (by rwa [Complex.norm_conj])

/-- On the closed disc, the Möbius extension of `abMob a` to `ℂ̄` is `abMob a`. -/
theorem abN_mobiusExt_coe {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1) :
    mobiusExt ((1 - conj a) / (1 - a)) (-((1 - conj a) / (1 - a) * a)) (-conj a) 1 (w : ExtPlane) =
      ((abMob a w : ℂ) : ExtPlane) := by
  have hden : -conj a * w + 1 ≠ 0 := by
    have h := abN_den_ne_zero ha hw
    intro h'
    exact h (by linear_combination h')
  rw [mobiusExt_coe hden, abN_mobiusFn_eq]

/-- The closure of `Δ` in `ℂ̄` is the closed unit disc. -/
theorem abN_closure_toExt_unitDisc : closure (toExt unitDisc) = toExt (closedBall 0 1) := by
  rw [closure_toExt_of_isBounded (A := unitDisc) isBounded_ball]
  congr 1
  exact closure_ball (0 : ℂ) one_ne_zero

/-- Post-composing with `abMob (h 0)` normalizes a q.c. self-map of `Δ` at `0`, keeps the constant, the
dilatation and a boundary extension (transported by `abMob (h 0)`). -/
theorem ab_normalize {h : ℂ → ℂ} {K : ℝ} (hh : IsKQC h unitDisc K) (himg : h '' unitDisc = unitDisc)
    {H : ExtPlane → ExtPlane} (hH : IsHomeoExtension h unitDisc unitDisc H) :
    IsKQC (fun z => abMob (h 0) (h z)) unitDisc K ∧
      (fun z => abMob (h 0) (h z)) '' unitDisc = unitDisc ∧ abMob (h 0) (h 0) = 0 ∧
      (∃ G : ExtPlane → ExtPlane,
        IsHomeoExtension (fun z => abMob (h 0) (h z)) unitDisc unitDisc G ∧
          ∀ z : ℂ, ‖z‖ = 1 → G (z : ExtPlane) = OnePoint.map (abMob (h 0)) (H (z : ExtPlane))) ∧
      ∀ᵐ z ∂(volume.restrict unitDisc),
        complexDilatation (fun z => abMob (h 0) (h z)) z = complexDilatation h z := by
  have h0mem : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hmaps : MapsTo h unitDisc unitDisc := fun z hz => by
    rw [← himg]
    exact mem_image_of_mem h hz
  have ha : ‖h 0‖ < 1 := mem_ball_zero_iff.1 (hmaps h0mem)
  have hconf := abN_isConformalOnto ha
  have hcomp : (fun z => abMob (h 0) (h z)) = abMob (h 0) ∘ h := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hK := thm7_1_comp hh (isKQC_one_of_conformal isOpen_ball hconf) himg.subset
    rw [mul_one] at hK
    exact hK
  · rw [hcomp, image_comp, himg, hconf.2.2]
  · simp only [abMob, sub_self, zero_div, mul_zero]
  · set e : ExtPlane ≃ₜ ExtPlane := mobiusHomeomorph _ _ _ _ (abN_det_ne_zero ha) with he_def
    have he : ∀ w : ℂ, ‖w‖ ≤ 1 → e (w : ExtPlane) = ((abMob (h 0) w : ℂ) : ExtPlane) := by
      intro w hw
      rw [he_def, mobiusHomeomorph_apply]
      exact abN_mobiusExt_coe ha hw
    have heimg : e '' toExt unitDisc = toExt unitDisc := by
      ext p
      constructor
      · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
        rw [he w (mem_ball_zero_iff.1 hw).le]
        exact ⟨_, hconf.mapsTo hw, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        rw [← hconf.2.2] at hw
        obtain ⟨v, hv, rfl⟩ := hw
        exact ⟨(v : ExtPlane), ⟨v, hv, rfl⟩, he v (mem_ball_zero_iff.1 hv).le⟩
    refine ⟨e ∘ H, IsHomeoExtension.comp_homeomorph hH hmaps e
      (fun w hw => he w (mem_ball_zero_iff.1 hw).le) heimg, fun z hz => ?_⟩
    have hzc : ((z : ℂ) : ExtPlane) ∈ closure (toExt unitDisc) := by
      rw [abN_closure_toExt_unitDisc]
      exact ⟨z, mem_closedBall_zero_iff.2 hz.le, rfl⟩
    have hHz : H (z : ExtPlane) ∈ closure (toExt unitDisc) := by
      rw [← hH.2.2.2]
      exact mem_image_of_mem H hzc
    rw [abN_closure_toExt_unitDisc] at hHz
    obtain ⟨w, hw, hwz⟩ := hHz
    rw [Function.comp_apply, ← hwz, he w (mem_closedBall_zero_iff.1 hw)]
    rfl
  · rw [hcomp]
    filter_upwards [thm9_3_differentiable_ae hh, ae_restrict_mem measurableSet_ball]
      with z hz hzmem
    have hhz : ‖h z‖ < 1 := mem_ball_zero_iff.1 (hmaps hzmem)
    exact complexDilatation_comp_conformal_left (f := h) (g := abMob (h 0)) hz
      (abN_hasDerivAt ha hhz).differentiableAt (abN_deriv_ne_zero ha hhz)

/-! ### Piece R — reflection in the unit circle -/

/-- `AbsolutelyContinuousOnInterval` transfers under the reflection `t ↦ -t`. -/
theorem abR_x_ac_neg {φ : ℝ → ℂ} {a b : ℝ} (hφ : AbsolutelyContinuousOnInterval φ a b) :
    AbsolutelyContinuousOnInterval (fun t => φ (-t)) (-a) (-b) := by
  rw [absolutelyContinuousOnInterval_iff] at hφ ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hφ ε hε
  refine ⟨δ, hδ, ?_⟩
  rintro ⟨n, I⟩ hE hlt
  set I' : ℕ → ℝ × ℝ := fun i => (-(I i).1, -(I i).2) with hI'def
  have hmem : ∀ x, x ∈ uIcc (-a) (-b) → -x ∈ uIcc a b := by
    intro x hx
    rw [mem_uIcc] at hx ⊢
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; exact ⟨by linarith, by linarith⟩
    · left; exact ⟨by linarith, by linarith⟩
  have hE' : ((n, I') : ℕ × (ℕ → ℝ × ℝ)) ∈ AbsolutelyContinuousOnInterval.disjWithin a b := by
    refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_⟩
    · obtain ⟨h1, h2⟩ := hE.1 i hi
      exact ⟨hmem _ h1, hmem _ h2⟩
    · have hdd : Disjoint (uIoc (I i).1 (I i).2) (uIoc (I j).1 (I j).2) := hE.2 hi hj hij
      show Disjoint (uIoc (-(I i).1) (-(I i).2)) (uIoc (-(I j).1) (-(I j).2))
      simp only [uIoc] at hdd ⊢
      rw [Set.Ioc_disjoint_Ioc] at hdd ⊢
      simp only [min_neg_neg, max_neg_neg]
      exact neg_le_neg hdd
  have hlen : ∑ i ∈ Finset.range n, dist (I' i).1 (I' i).2 =
      ∑ i ∈ Finset.range n, dist (I i).1 (I i).2 :=
    Finset.sum_congr rfl fun i _ => by simp only [hI'def, dist_neg_neg]
  exact hbound (n, I') hE' (hlen ▸ hlt)

/-- Almost-everywhere statements on `(-d, -c)` transfer to `(c, d)` under `y ↦ -y`. -/
theorem abR_x_ae_neg_Ioo {P : ℝ → Prop} {c d : ℝ}
    (h : ∀ᵐ y ∂(volume.restrict (Ioo (-d) (-c))), P y) :
    ∀ᵐ y ∂(volume.restrict (Ioo c d)), P (-y) := by
  have hpre : (fun x : ℝ => -x) ⁻¹' Ioo (-d) (-c) = Ioo c d := by
    ext x
    simp only [mem_preimage, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  have hneg : MeasurePreserving (fun x : ℝ => -x) (volume.restrict (Ioo c d))
      (volume.restrict (Ioo (-d) (-c))) := by
    have := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
      (measurableSet_Ioo (a := -d) (b := -c))
    rwa [show (Neg.neg : ℝ → ℝ) ⁻¹' Ioo (-d) (-c) = Ioo c d from hpre] at this
  exact hneg.quasiMeasurePreserving.ae h

/-- A.C.L. is preserved by the conjugation `h ↦ conj ∘ h ∘ conj` (with the domain reflected). -/
theorem abR_x_isACL_conj {h : ℂ → ℂ} {D : Set ℂ} (hh : IsACL h D) :
    IsACL (fun z => conj (h (conj z))) (conj ⁻¹' D) := by
  obtain ⟨hc, hrect⟩ := hh
  refine ⟨Complex.continuous_conj.comp_continuousOn
    (hc.comp Complex.continuous_conj.continuousOn fun z hz => hz), fun a b c d hab hcd hR => ?_⟩
  have hR' : closedRect a b (-d) (-c) ⊆ D := by
    intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    have hz' : conj z ∈ closedRect a b c d := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [Complex.conj_re]; exact h1
      · rw [Complex.conj_re]; exact h2
      · rw [Complex.conj_im]; linarith
      · rw [Complex.conj_im]; linarith
    have := hR hz'
    rwa [mem_preimage, Complex.conj_conj] at this
  obtain ⟨hV, hH⟩ := hrect a b (-d) (-c) hab (neg_lt_neg hcd) hR'
  have hconjx : ∀ x y : ℝ, conj ((x : ℂ) + (y : ℂ) * I) = (x : ℂ) + ((-y : ℝ) : ℂ) * I := by
    intro x y
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · filter_upwards [hV] with x hx
    have h1 := abR_x_ac_neg hx
    rw [neg_neg, neg_neg] at h1
    have h2 := (Complex.conjLIE.lipschitzWith.comp_absolutelyContinuousOnInterval h1).symm
    have e : (fun y : ℝ => conj (h (conj ((x : ℂ) + (y : ℂ) * I)))) =
        (⇑Complex.conjLIE) ∘ (fun t : ℝ => h ((x : ℂ) + ((-t : ℝ) : ℂ) * I)) := by
      funext y
      rw [hconjx]
      rfl
    rw [e]
    exact h2
  · filter_upwards [abR_x_ae_neg_Ioo hH] with y hy
    have h2 := Complex.conjLIE.lipschitzWith.comp_absolutelyContinuousOnInterval hy
    have e : (fun x : ℝ => conj (h (conj ((x : ℂ) + (y : ℂ) * I)))) =
        (⇑Complex.conjLIE) ∘ (fun x : ℝ => h ((x : ℂ) + ((-y : ℝ) : ℂ) * I)) := by
      funext x
      rw [hconjx]
      rfl
    rw [e]
    exact h2

/-- Derivatives of `conj ∘ h ∘ conj`: `∂_z` and `∂_{z̄}` are conjugated (and evaluated at `z̄`). -/
theorem abR_x_dz_dzbar_conj {h : ℂ → ℂ} {z : ℂ} (hd : DifferentiableAt ℝ h (conj z)) :
    DifferentiableAt ℝ (fun w => conj (h (conj w))) z ∧
      dz (fun w => conj (h (conj w))) z = conj (dz h (conj z)) ∧
        dzbar (fun w => conj (h (conj w))) z = conj (dzbar h (conj z)) := by
  have hσ : ∀ w, HasFDerivAt (fun w : ℂ => conj w) (conjCLE : ℂ →L[ℝ] ℂ) w := fun w =>
    (conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt
  have hd' : HasFDerivAt (fun w => conj (h (conj w)))
      ((conjCLE : ℂ →L[ℝ] ℂ).comp ((fderiv ℝ h (conj z)).comp (conjCLE : ℂ →L[ℝ] ℂ))) z :=
    (hσ _).comp z (hd.hasFDerivAt.comp z (hσ z))
  refine ⟨hd'.differentiableAt, ?_, ?_⟩ <;>
  simp only [dz, dzbar, hd'.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, map_one, Complex.conj_I, map_neg, map_sub, map_add, map_mul, map_div₀,
    map_ofNat] <;> ring

/-- The conjugate `conj ∘ h ∘ conj` of a homeomorphism is a homeomorphism of the reflected domain. -/
theorem abR_x_isHomeomorphOnto_conj {h : ℂ → ℂ} {D : Set ℂ} (hh : IsHomeomorphOnto h D (h '' D)) :
    IsHomeomorphOnto (fun z => conj (h (conj z))) (conj ⁻¹' D)
      ((fun z => conj (h (conj z))) '' (conj ⁻¹' D)) := by
  obtain ⟨hc, hi, -, hinv⟩ := hh
  have hmaps : MapsTo (fun z : ℂ => conj z) (conj ⁻¹' D) D := fun z hz => hz
  have hinj' : InjOn (fun z => conj (h (conj z))) (conj ⁻¹' D) := by
    intro z hz w hw hzw
    exact star_injective (hi hz hw (star_injective hzw))
  refine ⟨Complex.continuous_conj.comp_continuousOn (hc.comp Complex.continuous_conj.continuousOn
    hmaps), hinj', rfl, ?_⟩
  have heq : EqOn (Function.invFunOn (fun z => conj (h (conj z))) (conj ⁻¹' D))
      (fun w => conj (Function.invFunOn h D (conj w)))
      ((fun z => conj (h (conj z))) '' (conj ⁻¹' D)) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hinj'.leftInvOn_invFunOn hz]
    show z = conj (Function.invFunOn h D (conj (conj (h (conj z)))))
    rw [Complex.conj_conj, hi.leftInvOn_invFunOn hz, Complex.conj_conj]
  refine ContinuousOn.congr ?_ heq
  refine Complex.continuous_conj.comp_continuousOn (hinv.comp Complex.continuous_conj.continuousOn ?_)
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨conj z, hz, (Complex.conj_conj _).symm⟩

/-- Conjugation by `z ↦ z̄` preserves `K`-quasiconformality (Theorem 10.1 in both directions). -/
theorem abR_x_isKQC_conj {h : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hh : IsKQC h D K) :
    IsKQC (fun z => conj (h (conj z))) (conj ⁻¹' D) K := by
  have hD' : IsOpen (conj ⁻¹' D) := hh.1.preimage Complex.continuous_conj
  have hhom := abR_x_isHomeomorphOnto_conj hh.2.2.1
  refine (thm10_1_isKQC_iff hD' hh.2.1 hhom).2 ⟨abR_x_isACL_conj (thm9_1_isACL hh), ?_⟩
  have hmp : MeasurePreserving (fun z : ℂ => conj z) (volume.restrict (conj ⁻¹' D))
      (volume.restrict D) :=
    gzE_conj_measurePreserving.restrict_preimage hh.1.measurableSet
  filter_upwards [hmp.quasiMeasurePreserving.ae (thm9_3_differentiable_ae hh),
    hmp.quasiMeasurePreserving.ae (thm9_4_dilatation_ae hh)] with z hzd hzi
  obtain ⟨-, h1, h2⟩ := abR_x_dz_dzbar_conj hzd
  rw [h1, h2, Complex.norm_conj, Complex.norm_conj]
  exact hzi

/-- Piece R interface (exterior half of the reflection): `z ↦ 1/conj(h(1/z̄))` is `K`-q.c. on `|z| > 1`,
and its dilatation has modulus `|μ_h(1/z̄)|` a.e. there. -/
theorem abR_exterior {h : ℂ → ℂ} {K : ℝ} (hh : IsKQC h unitDisc K) (himg : h '' unitDisc = unitDisc)
    (h0 : h 0 = 0) :
    IsKQC (fun z => (conj (h (conj z)⁻¹))⁻¹) {z : ℂ | 1 < ‖z‖} K ∧
      ∀ᵐ z, 1 < ‖z‖ →
        ‖complexDilatation (fun z => (conj (h (conj z)⁻¹))⁻¹) z‖ = ‖complexDilatation h (conj z)⁻¹‖ := by
  -- the image condition `himg` is not needed for the exterior half
  have _himg : h '' unitDisc = unitDisc := himg
  set g : ℂ → ℂ := fun z => conj (h (conj z)) with hgdef
  have hpre : conj ⁻¹' unitDisc = unitDisc := by
    ext z
    simp only [mem_preimage, unitDisc, mem_ball, dist_zero_right, Complex.norm_conj]
  have hgK : IsKQC g unitDisc K := by
    have := abR_x_isKQC_conj hh
    rwa [hpre] at this
  have hinj : InjOn h unitDisc := hh.2.2.1.2.1
  have h0mem : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  -- `h w ≠ 0` for `w ∈ Δ ∖ {0}`
  have hne : ∀ w ∈ unitDisc, w ≠ 0 → h w ≠ 0 := fun w hw hw0 hhw =>
    hw0 (hinj hw h0mem (hhw.trans h0.symm))
  -- the exterior map is `inv ∘ g ∘ inv`
  have hF : (fun z => (conj (h (conj z)⁻¹))⁻¹) = nxInvConj g := by
    funext z
    simp only [nxInvConj, hgdef, map_inv₀]
  have hF' : nxInvConj g = (fun w : ℂ => w⁻¹) ∘ (g ∘ fun w : ℂ => w⁻¹) := rfl
  set E : Set ℂ := {z : ℂ | 1 < ‖z‖} with hEdef
  have hEo : IsOpen E := isOpen_lt continuous_const continuous_norm
  have hE0 : E ⊆ {0}ᶜ := fun z hz h0z => by
    rw [mem_singleton_iff] at h0z
    rw [hEdef, mem_ofPred_eq, h0z, norm_zero] at hz
    linarith
  set P : Set ℂ := unitDisc \ {0} with hPdef
  have hPo : IsOpen P := isOpen_ball.sdiff isClosed_singleton
  have hinvE : IsKQC (fun w : ℂ => w⁻¹) E 1 :=
    isKQC_one_of_conformal hEo (D' := (fun w : ℂ => w⁻¹) '' E)
      ⟨nx_inv_isConformalOnto.1.mono hE0, nx_inv_isConformalOnto.2.1.mono hE0, rfl⟩
  have hinv0 : IsKQC (fun w : ℂ => w⁻¹) {0}ᶜ 1 :=
    isKQC_one_of_conformal isOpen_compl_singleton nx_inv_isConformalOnto
  have hgP : IsKQC g P K := nx_isKQC_restrict hgK hPo sdiff_subset
  have hsub1 : (fun w : ℂ => w⁻¹) '' E ⊆ P := by
    rintro _ ⟨z, hz, rfl⟩
    have hz0 : z ≠ 0 := hE0 hz
    refine ⟨?_, ?_⟩
    · show z⁻¹ ∈ ball (0 : ℂ) 1
      rw [mem_ball, dist_zero_right, norm_inv]
      exact inv_lt_one_of_one_lt₀ hz
    · exact inv_ne_zero hz0
  have h1 := thm7_1_comp hinvE hgP hsub1
  have hsub2 : (g ∘ fun w : ℂ => w⁻¹) '' E ⊆ {0}ᶜ := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hzP, hz0⟩ := hsub1 ⟨z, hz, rfl⟩
    have hc : conj z⁻¹ ∈ unitDisc := by
      rw [← hpre] at hzP
      exact hzP
    have hc0 : conj z⁻¹ ≠ 0 := (map_ne_zero _).2 hz0
    show conj (h (conj z⁻¹)) ∈ ({0}ᶜ : Set ℂ)
    exact (map_ne_zero _).2 (hne _ hc hc0)
  have h2 := thm7_1_comp h1 hinv0 hsub2
  rw [one_mul, mul_one] at h2
  refine ⟨?_, ?_⟩
  · rw [hF, hF']
    exact h2
  · have hdiff : ∀ᵐ w, w ∈ unitDisc → DifferentiableAt ℝ h w :=
      (ae_restrict_iff' hh.1.measurableSet).1 (thm9_3_differentiable_ae hh)
    have hdc : ∀ᵐ w, conj w ∈ unitDisc → DifferentiableAt ℝ h (conj w) :=
      gzE_conj_measurePreserving.quasiMeasurePreserving.ae hdiff
    filter_upwards [nx_ae_inv hdc] with z hz hz1
    have hz0 : z ≠ 0 := hE0 hz1
    have hzP := hsub1 ⟨z, hz1, rfl⟩
    have hcz : conj z⁻¹ ∈ unitDisc := by
      have := hzP.1
      rw [← hpre] at this
      exact this
    have hc0 : conj z⁻¹ ≠ 0 := (map_ne_zero _).2 (inv_ne_zero hz0)
    obtain ⟨hgd, hdz, hdzbar⟩ := abR_x_dz_dzbar_conj (hz hcz)
    have hgz : g z⁻¹ ≠ 0 := (map_ne_zero _).2 (hne _ hcz hc0)
    rw [hF, nxI2_dilatation_invConj_at hz0 hgz hgd, norm_mul]
    have hn1 : ‖z ^ 2 / conj z ^ 2‖ = 1 := by
      rw [norm_div, norm_pow, norm_pow, Complex.norm_conj]
      exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.2 hz0))
    rw [hn1, mul_one, complexDilatation, complexDilatation, hdz, hdzbar, norm_div, norm_div,
      Complex.norm_conj, Complex.norm_conj, map_inv₀]

/-- One-dimensional gluing: a function continuous on `[c, d]`, absolutely continuous near every point of
`(c, d)` off a countable set `S`, with an integrable derivative on `[c, d]`, is absolutely continuous on
`[c, d]` (`φ - ∫_c φ'` is continuous and locally constant off `S`, hence constant). -/
theorem abR_c_ac_of_local {φ : ℝ → ℂ} {c d : ℝ} (hcd : c ≤ d) {S : Set ℝ} (hS : S.Countable)
    (hcont : ContinuousOn φ (Icc c d)) (hint : IntervalIntegrable (deriv φ) volume c d)
    (hloc : ∀ y ∈ Ioo c d \ S, ∃ ε > 0, ∀ u v, u ∈ Ioo (y - ε) (y + ε) →
      v ∈ Ioo (y - ε) (y + ε) → AbsolutelyContinuousOnInterval φ u v) :
    AbsolutelyContinuousOnInterval φ c d := by
  have hcI : c ∈ uIcc c d := by rw [uIcc_of_le hcd]; exact ⟨le_rfl, hcd⟩
  have hmem : ∀ {t : ℝ}, t ∈ Icc c d → t ∈ uIcc c d := fun ht => by rw [uIcc_of_le hcd]; exact ht
  have hsub : ∀ {t : ℝ}, t ∈ Icc c d → IntervalIntegrable (deriv φ) volume c t :=
    fun ht => hint.mono_set (uIcc_subset_uIcc hcI (hmem ht))
  have hprim : ContinuousOn (fun y => ∫ t in c..y, deriv φ t) (Icc c d) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hint hcI
    rwa [uIcc_of_le hcd] at h
  have hFc : ContinuousOn (fun y => φ y - ∫ t in c..y, deriv φ t) (Icc c d) := hcont.sub hprim
  have hFd : ∀ y ∈ Ioo c d \ S, HasDerivAt (fun y => φ y - ∫ t in c..y, deriv φ t) 0 y := by
    intro y hy
    obtain ⟨ε, hε, hac⟩ := hloc y hy
    have hyI : y ∈ Ioo c d := hy.1
    refine (hasDerivAt_const y (φ y - ∫ t in c..y, deriv φ t)).congr_of_eventuallyEq ?_
    have hn : Ioo (max c (y - ε)) (min d (y + ε)) ∈ 𝓝 y :=
      Ioo_mem_nhds (max_lt hyI.1 (by linarith)) (lt_min hyI.2 (by linarith))
    filter_upwards [hn] with t ht
    have ht1 : max c (y - ε) < t := ht.1
    have ht2 : t < min d (y + ε) := ht.2
    have hAC : AbsolutelyContinuousOnInterval φ y t :=
      hac y t ⟨by linarith, by linarith⟩
        ⟨(le_max_right _ _).trans_lt ht1, ht2.trans_le (min_le_right _ _)⟩
    have hFTC := integral_deriv_eq_sub_of_absolutelyContinuous hAC
    have htI : t ∈ Icc c d := ⟨(le_max_left _ _).trans ht1.le, ht2.le.trans (min_le_left _ _)⟩
    have hdiff := intervalIntegral.integral_interval_sub_left (hsub htI)
      (hsub (Ioo_subset_Icc_self hyI))
    show φ t - ∫ s in c..t, deriv φ s = φ y - ∫ s in c..y, deriv φ s
    linear_combination -hdiff - hFTC
  have hconst : ∀ y ∈ Icc c d,
      φ y - ∫ t in c..y, deriv φ t = φ c - ∫ t in c..c, deriv φ t := by
    intro y hy
    have h := integral_eq_of_hasDerivAt_off_countable_of_le
      (fun y => φ y - ∫ t in c..y, deriv φ t) (fun _ => (0 : ℂ)) hy.1 hS
      (hFc.mono (Icc_subset_Icc_right hy.2))
      (fun t ht => hFd t ⟨⟨ht.1.1, ht.1.2.trans_le hy.2⟩, ht.2⟩)
      (continuous_const.intervalIntegrable _ _)
    rw [intervalIntegral.integral_zero] at h
    exact (sub_eq_zero.1 h.symm)
  refine absolutelyContinuousOnInterval_congr (fun y hy => ?_)
    ((absolutelyContinuousOnInterval_const (φ c) c d).add
      (absolutelyContinuousOnInterval_intervalIntegral_complex hint hcI))
  rw [uIcc_of_le hcd] at hy
  have h := hconst y hy
  rw [intervalIntegral.integral_same, sub_zero] at h
  show φ c + ∫ v in c..y, deriv φ v = φ y
  linear_combination -h

/-- The unit circle is Lebesgue-null: a property holding a.e. inside and a.e. outside it holds a.e. on
`ℂ`. -/
theorem abR_c_ae_of_in_out {P : ℂ → Prop} (hin : ∀ᵐ z ∂(volume.restrict unitDisc), P z)
    (hout : ∀ᵐ z ∂(volume.restrict {z : ℂ | 1 < ‖z‖}), P z) : ∀ᵐ z, P z := by
  have hs : ∀ᵐ z : ℂ, z ∉ sphere (0 : ℂ) 1 := by
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq] using Measure.addHaar_sphere volume (0 : ℂ) 1
  have h1 := (ae_restrict_iff' (isOpen_ball.measurableSet : MeasurableSet (ball (0 : ℂ) 1))).1 hin
  have h2 := (ae_restrict_iff'
    (isOpen_lt continuous_const continuous_norm).measurableSet).1 hout
  filter_upwards [hs, h1, h2] with z hz hz1 hz2
  rcases lt_trichotomy ‖z‖ 1 with h | h | h
  · exact hz1 (mem_ball_zero_iff.2 h)
  · exact absurd (mem_sphere_zero_iff_norm.2 h) hz
  · exact hz2 h

/-- `∫_R |g'(z) v| < ∞` on every open rectangle `R` for `|v| = 1`, from `|g'(z) v| ≤ |∂g| + |∂̄g|`,
`(|∂g| + |∂̄g|)² ≤ K J_g` and `∫_R J_g ≤ m(g(R̄)) < ∞`. -/
theorem abR_c_lintegral_fderiv_lt_top {g : ℂ → ℂ} {K : ℝ} (hg : IsHomeomorphOnto g univ univ)
    (hK : 0 ≤ K) (hdiff : ∀ᵐ z, DifferentiableAt ℝ g z)
    (hineq : ∀ᵐ z, ‖dz g z‖ + ‖dzbar g z‖ ≤ K * (‖dz g z‖ - ‖dzbar g z‖))
    {v : ℂ} (hv : ‖v‖ = 1) (a b c d : ℝ) :
    ∫⁻ z in openRect a b c d, ‖fderiv ℝ g z v‖ₑ < ∞ := by
  have hpt : ∀ᵐ z, ‖fderiv ℝ g z v‖ₑ ≤
      ENNReal.ofReal K * ENNReal.ofReal (jacobian g z) + 1 := by
    filter_upwards [hdiff, hineq] with z hz hz'
    have hA0 : 0 ≤ ‖dz g z‖ + ‖dzbar g z‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hbound : ‖fderiv ℝ g z v‖ ≤ ‖dz g z‖ + ‖dzbar g z‖ := by
      rw [fderiv_eq_dz_dzbar hz]
      calc ‖dz g z * v + dzbar g z * conj v‖
          ≤ ‖dz g z * v‖ + ‖dzbar g z * conj v‖ := norm_add_le _ _
        _ = ‖dz g z‖ + ‖dzbar g z‖ := by
            rw [norm_mul, norm_mul, Complex.norm_conj, hv, mul_one, mul_one]
    have hsq : (‖dz g z‖ + ‖dzbar g z‖) ^ 2 ≤ K * jacobian g z := by
      unfold jacobian
      nlinarith [norm_nonneg (dz g z), norm_nonneg (dzbar g z)]
    have h1 : ‖fderiv ℝ g z v‖ ≤ K * jacobian g z + 1 := by
      nlinarith [norm_nonneg (fderiv ℝ g z v)]
    calc ‖fderiv ℝ g z v‖ₑ = ENNReal.ofReal ‖fderiv ℝ g z v‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (K * jacobian g z + 1) := ENNReal.ofReal_le_ofReal h1
      _ ≤ ENNReal.ofReal (K * jacobian g z) + ENNReal.ofReal 1 := ENNReal.ofReal_add_le
      _ = ENNReal.ofReal K * ENNReal.ofReal (jacobian g z) + 1 := by
          rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_one]
  have hJ : ∫⁻ z in openRect a b c d, ENNReal.ofReal (jacobian g z) ≤
      volume (g '' openRect a b c d) :=
    ad_lintegral_jacobian_le_volume_image isOpen_univ hg.2.1
      (by rw [Measure.restrict_univ]; exact hdiff) (measurableSet_openRect a b c d) (subset_univ _)
  have hfin : volume (g '' openRect a b c d) < ∞ :=
    (measure_mono (image_mono (openRect_subset_closedRect a b c d))).trans_lt
      ((isCompact_closedRect a b c d).image_of_continuousOn
        (hg.1.mono (subset_univ _))).measure_lt_top
  have hR : volume (openRect a b c d) < ∞ :=
    (measure_mono (openRect_subset_closedRect a b c d)).trans_lt
      (isCompact_closedRect a b c d).measure_lt_top
  calc ∫⁻ z in openRect a b c d, ‖fderiv ℝ g z v‖ₑ
      ≤ ∫⁻ z in openRect a b c d, (ENNReal.ofReal K * ENNReal.ofReal (jacobian g z) + 1) :=
        lintegral_mono_ae (ae_restrict_of_ae hpt)
    _ = ENNReal.ofReal K * (∫⁻ z in openRect a b c d, ENNReal.ofReal (jacobian g z)) +
          volume (openRect a b c d) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          setLIntegral_const, one_mul]
    _ < ∞ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hJ.trans_lt hfin), hR⟩

/-- An a.e. property on `ℂ` holds, for almost every `x ∈ (a, b)`, at `x + iy` for almost every
`y ∈ (c, d)` (Fubini for null sets). -/
theorem abR_c_ae_ae_of_ae {P : ℂ → Prop} (hP : MeasurableSet {z | P z}) (h : ∀ᵐ z, P z)
    (a b c d : ℝ) :
    ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioo a b)), ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo c d)),
      P ((x : ℂ) + (y : ℂ) * I) := by
  have he := Complex.measurableEquivRealProd.symm.measurableEmbedding
  have h' : ∀ᵐ z ∂(volume.restrict (openRect a b c d)), P z := ae_restrict_of_ae h
  rw [volume_restrict_openRect_eq_map, ae_map_iff he.measurable.aemeasurable hP,
    Measure.ae_prod_iff_ae_ae (p := fun q => P (Complex.measurableEquivRealProd.symm q))
      (show MeasurableSet {q | P (Complex.measurableEquivRealProd.symm q)} from
        he.measurable hP)] at h'
  simpa only [measurableEquivRealProd_symm_apply'] using h'

/-- An a.e. property on `ℂ` holds, for almost every `y ∈ (c, d)`, at `x + iy` for almost every
`x ∈ (a, b)` (Fubini for null sets, other order). -/
theorem abR_c_ae_ae_of_ae_symm {P : ℂ → Prop} (hP : MeasurableSet {z | P z}) (h : ∀ᵐ z, P z)
    (a b c d : ℝ) :
    ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo c d)), ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioo a b)),
      P ((x : ℂ) + (y : ℂ) * I) :=
  (Measure.ae_ae_comm (p := fun (x y : ℝ) => P ((x : ℂ) + (y : ℂ) * I))
    (continuous_rectCoords.measurable hP)).1 (abR_c_ae_ae_of_ae hP h a b c d)

/-- A line meets the unit circle in at most two points: `{s | s² + t² = 1}` is countable. -/
theorem abR_c_countable_circle (t : ℝ) : {s : ℝ | s ^ 2 + t ^ 2 = 1}.Countable := by
  refine ((countable_singleton (√(1 - t ^ 2))).insert (-√(1 - t ^ 2))).mono ?_
  intro s hs
  have hs2 : s ^ 2 + t ^ 2 = 1 := hs
  have hs' : s ^ 2 = 1 - t ^ 2 := by linarith
  have h0 : 0 ≤ 1 - t ^ 2 := by rw [← hs']; exact sq_nonneg s
  have h2 : s ^ 2 = (√(1 - t ^ 2)) ^ 2 := by rw [Real.sq_sqrt h0, hs']
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
  · exact Or.inr (mem_singleton_iff.2 h)
  · exact Or.inl h

/-- `|x + iy| = 1` means `x² + y² = 1`. -/
theorem abR_c_norm_eq_one {x y : ℝ} (h : ‖(x : ℂ) + (y : ℂ) * I‖ = 1) : x ^ 2 + y ^ 2 = 1 := by
  have h2 := Complex.sq_norm ((x : ℂ) + (y : ℂ) * I)
  rw [h, one_pow, Complex.normSq_add_mul_I] at h2
  linarith

/-- A point off the unit circle lies, with a margin `ε`, inside a rational closed rectangle contained in
`Δ` or in `{|z| > 1}`. -/
theorem abR_c_rat_rect {z : ℂ} (hz : ‖z‖ ≠ 1) :
    ∃ q : ℚ × ℚ × ℚ × ℚ, ∃ ε > (0 : ℝ),
      (closedRect q.1 q.2.1 q.2.2.1 q.2.2.2 ⊆ unitDisc ∨
        closedRect q.1 q.2.1 q.2.2.1 q.2.2.2 ⊆ {w : ℂ | 1 < ‖w‖}) ∧
      (q.1 : ℝ) < z.re - ε ∧ z.re + ε < q.2.1 ∧ (q.2.2.1 : ℝ) < z.im - ε ∧
        z.im + ε < q.2.2.2 := by
  obtain ⟨U, hU, hzU, hUsub⟩ : ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      (U ⊆ unitDisc ∨ U ⊆ {w : ℂ | 1 < ‖w‖}) := by
    rcases hz.lt_or_gt with h | h
    · exact ⟨ball 0 1, isOpen_ball, mem_ball_zero_iff.2 h, Or.inl subset_rfl⟩
    · exact ⟨{w | 1 < ‖w‖}, isOpen_lt continuous_const continuous_norm, h, Or.inr subset_rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z hzU
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show z.re - r / 2 < z.re - r / 4 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show z.re + r / 4 < z.re + r / 2 by linarith)
  obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn (show z.im - r / 2 < z.im - r / 4 by linarith)
  obtain ⟨d, hd1, hd2⟩ := exists_rat_btwn (show z.im + r / 4 < z.im + r / 2 by linarith)
  have hR : closedRect a b c d ⊆ U := by
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hw
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖w - z‖ ≤ |(w - z).re| + |(w - z).im| := Complex.norm_le_abs_re_add_abs_im _
      _ < r / 2 + r / 2 := by
          rw [sub_re, sub_im]
          exact add_lt_add (abs_lt.2 ⟨by linarith, by linarith⟩)
            (abs_lt.2 ⟨by linarith, by linarith⟩)
      _ = r := by ring
  exact ⟨(a, b, c, d), r / 4, by positivity, hUsub.imp hR.trans hR.trans, ha2, hb1, hc2, hd1⟩

/-- For almost every `x`, `y ↦ g(x + iy)` is absolutely continuous on `[q₃, q₄]` for every rational
closed rectangle `[q₁, q₂] × [q₃, q₄]` inside or outside the unit circle with `x ∈ (q₁, q₂)`
(Theorem 9.1 on both sides; countably many rectangles). -/
theorem abR_c_vertical_rat {g : ℂ → ℂ} {K : ℝ} (hin : IsKQC g unitDisc K)
    (hout : IsKQC g {z : ℂ | 1 < ‖z‖} K) :
    ∀ᵐ x : ℝ, ∀ q : ℚ × ℚ × ℚ × ℚ, (q.1 : ℝ) < q.2.1 → (q.2.2.1 : ℝ) < q.2.2.2 →
      (closedRect q.1 q.2.1 q.2.2.1 q.2.2.2 ⊆ unitDisc ∨
        closedRect q.1 q.2.1 q.2.2.1 q.2.2.2 ⊆ {w : ℂ | 1 < ‖w‖}) →
      x ∈ Ioo (q.1 : ℝ) q.2.1 →
      AbsolutelyContinuousOnInterval (fun y : ℝ => g ((x : ℂ) + (y : ℂ) * I)) q.2.2.1 q.2.2.2 := by
  rw [ae_all_iff]
  intro q
  by_cases h : (q.1 : ℝ) < q.2.1 ∧ (q.2.2.1 : ℝ) < q.2.2.2 ∧
      (closedRect q.1 q.2.1 q.2.2.1 q.2.2.2 ⊆ unitDisc ∨
        closedRect q.1 q.2.1 q.2.2.1 q.2.2.2 ⊆ {w : ℂ | 1 < ‖w‖})
  · obtain ⟨h1, h2, h3⟩ := h
    have hv : ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioo (q.1 : ℝ) q.2.1)),
        AbsolutelyContinuousOnInterval (fun y : ℝ => g ((x : ℂ) + (y : ℂ) * I)) q.2.2.1 q.2.2.2 := by
      rcases h3 with h3 | h3
      · exact ((thm9_1_isACL hin).2 _ _ _ _ h1 h2 h3).1
      · exact ((thm9_1_isACL hout).2 _ _ _ _ h1 h2 h3).1
    rw [ae_restrict_iff' measurableSet_Ioo] at hv
    filter_upwards [hv] with x hx _ _ _ hxI
    exact hx hxI
  · exact Eventually.of_forall fun x h1 h2 h3 _ => absurd ⟨h1, h2, h3⟩ h

/-- For almost every `y`, `x ↦ g(x + iy)` is absolutely continuous on `[q₁, q₂]` for every rational
closed rectangle `[q₁, q₂] × [q₃, q₄]` inside or outside the unit circle with `y ∈ (q₃, q₄)`. -/
theorem abR_c_horizontal_rat {g : ℂ → ℂ} {K : ℝ} (hin : IsKQC g unitDisc K)
    (hout : IsKQC g {z : ℂ | 1 < ‖z‖} K) :
    ∀ᵐ y : ℝ, ∀ q : ℚ × ℚ × ℚ × ℚ, (q.1 : ℝ) < q.2.1 → (q.2.2.1 : ℝ) < q.2.2.2 →
      (closedRect q.1 q.2.1 q.2.2.1 q.2.2.2 ⊆ unitDisc ∨
        closedRect q.1 q.2.1 q.2.2.1 q.2.2.2 ⊆ {w : ℂ | 1 < ‖w‖}) →
      y ∈ Ioo (q.2.2.1 : ℝ) q.2.2.2 →
      AbsolutelyContinuousOnInterval (fun x : ℝ => g ((x : ℂ) + (y : ℂ) * I)) q.1 q.2.1 := by
  rw [ae_all_iff]
  intro q
  by_cases h : (q.1 : ℝ) < q.2.1 ∧ (q.2.2.1 : ℝ) < q.2.2.2 ∧
      (closedRect q.1 q.2.1 q.2.2.1 q.2.2.2 ⊆ unitDisc ∨
        closedRect q.1 q.2.1 q.2.2.1 q.2.2.2 ⊆ {w : ℂ | 1 < ‖w‖})
  · obtain ⟨h1, h2, h3⟩ := h
    have hv : ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo (q.2.2.1 : ℝ) q.2.2.2)),
        AbsolutelyContinuousOnInterval (fun x : ℝ => g ((x : ℂ) + (y : ℂ) * I)) q.1 q.2.1 := by
      rcases h3 with h3 | h3
      · exact ((thm9_1_isACL hin).2 _ _ _ _ h1 h2 h3).2
      · exact ((thm9_1_isACL hout).2 _ _ _ _ h1 h2 h3).2
    rw [ae_restrict_iff' measurableSet_Ioo] at hv
    filter_upwards [hv] with y hy _ _ _ hyI
    exact hy hyI
  · exact Eventually.of_forall fun y h1 h2 h3 _ => absurd ⟨h1, h2, h3⟩ h

/-- On almost every vertical segment of a rectangle, `y ↦ g(x + iy)` has an integrable derivative: it
is `g'(x + iy) i` a.e. on the segment, and Tonelli applies to `∫_R |g' i| < ∞`. -/
theorem abR_c_vertical_integrable {g : ℂ → ℂ} (hdiff : ∀ᵐ z, DifferentiableAt ℝ g z)
    {a b c d : ℝ} (hcd : c ≤ d) (hfin : ∫⁻ z in openRect a b c d, ‖fderiv ℝ g z I‖ₑ < ∞) :
    ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioo a b)),
      IntervalIntegrable (deriv fun y : ℝ => g ((x : ℂ) + (y : ℂ) * I)) volume c d := by
  have hFm : Measurable fun z => ‖fderiv ℝ g z I‖ₑ :=
    (measurable_fderiv_apply_const ℝ g I).enorm
  rw [lintegral_openRect hFm] at hfin
  have hm : Measurable fun x : ℝ => ∫⁻ y in Ioo c d, ‖fderiv ℝ g ((x : ℂ) + (y : ℂ) * I) I‖ₑ :=
    (hFm.comp continuous_rectCoords.measurable).lintegral_prod_right'
  filter_upwards [ae_lt_top hm hfin.ne,
    abR_c_ae_ae_of_ae (measurableSet_of_differentiableAt ℝ g) hdiff a b c d] with x hx1 hx2
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hcd]
  refine ⟨(measurable_deriv _).aestronglyMeasurable, ?_⟩
  show ∫⁻ y in Ioo c d, ‖deriv (fun y : ℝ => g ((x : ℂ) + (y : ℂ) * I)) y‖ₑ < ∞
  calc ∫⁻ y in Ioo c d, ‖deriv (fun y : ℝ => g ((x : ℂ) + (y : ℂ) * I)) y‖ₑ
      = ∫⁻ y in Ioo c d, ‖fderiv ℝ g ((x : ℂ) + (y : ℂ) * I) I‖ₑ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hx2] with y hy
        rw [← partialY_ofReal_add, partialY_eq_of_differentiableAt hy]
    _ < ∞ := hx1

/-- On almost every horizontal segment of a rectangle, `x ↦ g(x + iy)` has an integrable derivative:
it is `g'(x + iy) 1` a.e. on the segment, and Tonelli applies to `∫_R |g' 1| < ∞`. -/
theorem abR_c_horizontal_integrable {g : ℂ → ℂ} (hdiff : ∀ᵐ z, DifferentiableAt ℝ g z)
    {a b c d : ℝ} (hab : a ≤ b) (hfin : ∫⁻ z in openRect a b c d, ‖fderiv ℝ g z 1‖ₑ < ∞) :
    ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo c d)),
      IntervalIntegrable (deriv fun x : ℝ => g ((x : ℂ) + (y : ℂ) * I)) volume a b := by
  have hFm : Measurable fun z => ‖fderiv ℝ g z 1‖ₑ :=
    (measurable_fderiv_apply_const ℝ g 1).enorm
  rw [lintegral_openRect_symm hFm] at hfin
  have hc : Continuous fun q : ℝ × ℝ => (q.2 : ℂ) + (q.1 : ℂ) * I := by fun_prop
  have hm : Measurable fun y : ℝ => ∫⁻ x in Ioo a b, ‖fderiv ℝ g ((x : ℂ) + (y : ℂ) * I) 1‖ₑ :=
    (hFm.comp hc.measurable).lintegral_prod_right'
  filter_upwards [ae_lt_top hm hfin.ne,
    abR_c_ae_ae_of_ae_symm (measurableSet_of_differentiableAt ℝ g) hdiff a b c d] with y hy1 hy2
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  refine ⟨(measurable_deriv _).aestronglyMeasurable, ?_⟩
  show ∫⁻ x in Ioo a b, ‖deriv (fun x : ℝ => g ((x : ℂ) + (y : ℂ) * I)) x‖ₑ < ∞
  calc ∫⁻ x in Ioo a b, ‖deriv (fun x : ℝ => g ((x : ℂ) + (y : ℂ) * I)) x‖ₑ
      = ∫⁻ x in Ioo a b, ‖fderiv ℝ g ((x : ℂ) + (y : ℂ) * I) 1‖ₑ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hy2] with x hx
        rw [← partialX_ofReal_add, partialX_eq_of_differentiableAt hx]
    _ < ∞ := hy1

/-- A.C.L. across the unit circle on vertical segments: for almost every `x ∈ (a, b)`, `y ↦ g(x + iy)` is
absolutely continuous on `[c, d]` (local A.C. off the at most two circle points, glued by
`abR_c_ac_of_local`). -/
theorem abR_c_vertical {g : ℂ → ℂ} {K : ℝ} (hg : IsHomeomorphOnto g univ univ)
    (hin : IsKQC g unitDisc K) (hout : IsKQC g {z : ℂ | 1 < ‖z‖} K)
    (hdiff : ∀ᵐ z, DifferentiableAt ℝ g z)
    (hineq : ∀ᵐ z, ‖dz g z‖ + ‖dzbar g z‖ ≤ K * (‖dz g z‖ - ‖dzbar g z‖))
    {a b c d : ℝ} (hcd : c < d) :
    ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioo a b)),
      AbsolutelyContinuousOnInterval (fun y : ℝ => g ((x : ℂ) + (y : ℂ) * I)) c d := by
  have hK : 0 ≤ K := zero_le_one.trans hin.2.1
  have hgc : Continuous g := continuousOn_univ.1 hg.1
  have hfin := abR_c_lintegral_fderiv_lt_top hg hK hdiff hineq (v := I) (by simp) a b c d
  filter_upwards [abR_c_vertical_integrable hdiff hcd.le hfin,
    ae_restrict_of_ae (abR_c_vertical_rat hin hout)] with x hint hrat
  refine abR_c_ac_of_local (S := {y : ℝ | ‖(x : ℂ) + (y : ℂ) * I‖ = 1}) hcd.le
    ((abR_c_countable_circle x).mono fun y hy => ?_) (by fun_prop) hint fun y hy => ?_
  · have h := abR_c_norm_eq_one hy
    show y ^ 2 + x ^ 2 = 1
    linarith
  · obtain ⟨q, ε, hε, hsub, h1, h2, h3, h4⟩ := abR_c_rat_rect (z := (x : ℂ) + (y : ℂ) * I) hy.2
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
      add_zero, add_im, mul_im, zero_add] at h1 h2 h3 h4
    refine ⟨ε, hε, fun u v hu hv => ?_⟩
    have hq := hrat q (by linarith) (by linarith) hsub ⟨by linarith, by linarith⟩
    refine hq.mono (uIcc_subset_uIcc ?_ ?_)
    · rw [uIcc_of_le (by linarith)]
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    · rw [uIcc_of_le (by linarith)]
      exact ⟨by linarith [hv.1], by linarith [hv.2]⟩

/-- A.C.L. across the unit circle on horizontal segments: for almost every `y ∈ (c, d)`,
`x ↦ g(x + iy)` is absolutely continuous on `[a, b]`. -/
theorem abR_c_horizontal {g : ℂ → ℂ} {K : ℝ} (hg : IsHomeomorphOnto g univ univ)
    (hin : IsKQC g unitDisc K) (hout : IsKQC g {z : ℂ | 1 < ‖z‖} K)
    (hdiff : ∀ᵐ z, DifferentiableAt ℝ g z)
    (hineq : ∀ᵐ z, ‖dz g z‖ + ‖dzbar g z‖ ≤ K * (‖dz g z‖ - ‖dzbar g z‖))
    {a b c d : ℝ} (hab : a < b) :
    ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo c d)),
      AbsolutelyContinuousOnInterval (fun x : ℝ => g ((x : ℂ) + (y : ℂ) * I)) a b := by
  have hK : 0 ≤ K := zero_le_one.trans hin.2.1
  have hgc : Continuous g := continuousOn_univ.1 hg.1
  have hfin := abR_c_lintegral_fderiv_lt_top hg hK hdiff hineq (v := 1) (by simp) a b c d
  filter_upwards [abR_c_horizontal_integrable hdiff hab.le hfin,
    ae_restrict_of_ae (abR_c_horizontal_rat hin hout)] with y hint hrat
  refine abR_c_ac_of_local (S := {x : ℝ | ‖(x : ℂ) + (y : ℂ) * I‖ = 1}) hab.le
    ((abR_c_countable_circle y).mono fun x hx => abR_c_norm_eq_one hx) (by fun_prop) hint
    fun x hx => ?_
  obtain ⟨q, ε, hε, hsub, h1, h2, h3, h4⟩ := abR_c_rat_rect (z := (x : ℂ) + (y : ℂ) * I) hx.2
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
    add_zero, add_im, mul_im, zero_add] at h1 h2 h3 h4
  refine ⟨ε, hε, fun u v hu hv => ?_⟩
  have hq := hrat q (by linarith) (by linarith) hsub ⟨by linarith, by linarith⟩
  refine hq.mono (uIcc_subset_uIcc ?_ ?_)
  · rw [uIcc_of_le (by linarith)]
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  · rw [uIcc_of_le (by linarith)]
    exact ⟨by linarith [hv.1], by linarith [hv.2]⟩

/-- Piece R interface (removability of the unit circle): a homeomorphism of `ℂ` that is `K`-q.c. inside and
outside the unit circle is `K`-q.c. on `ℂ` (Theorem 10.1 (⇐): A.C.L. across the circle, the circle being
null). -/
theorem abR_removable {g : ℂ → ℂ} {K : ℝ} (hg : IsHomeomorphOnto g univ univ)
    (hin : IsKQC g unitDisc K) (hout : IsKQC g {z : ℂ | 1 < ‖z‖} K) : IsKQC g univ K := by
  have hdiff : ∀ᵐ z, DifferentiableAt ℝ g z :=
    abR_c_ae_of_in_out (thm9_3_differentiable_ae hin) (thm9_3_differentiable_ae hout)
  have hineq : ∀ᵐ z, ‖dz g z‖ + ‖dzbar g z‖ ≤ K * (‖dz g z‖ - ‖dzbar g z‖) :=
    abR_c_ae_of_in_out (thm9_4_dilatation_ae hin) (thm9_4_dilatation_ae hout)
  refine (thm10_1_isKQC_iff isOpen_univ hin.2.1 hg).2 ⟨⟨hg.1, fun a b c d hab hcd _ =>
    ⟨abR_c_vertical hg hin hout hdiff hineq hcd, abR_c_horizontal hg hin hout hdiff hineq hab⟩⟩,
    ?_⟩
  rw [Measure.restrict_univ]
  exact hineq

/-- The closure of `Δ` in `ℂ̄` is the closed unit disc. -/
theorem abR_t_closure : closure (toExt unitDisc) = toExt (closedBall 0 1) := by
  rw [closure_toExt_of_isBounded (A := unitDisc) Metric.isBounded_ball, unitDisc,
    closure_ball (0 : ℂ) one_ne_zero]

/-- The finite part of `H z` (`0` if `H z = ∞`). -/
def abR_t_fin (H : ExtPlane → ExtPlane) (z : ℂ) : ℂ := OnePoint.elim (H (z : ExtPlane)) 0 id

/-- If `H z` is the finite point `w`, then `abR_t_fin H z = w`. -/
theorem abR_t_fin_of_eq {H : ExtPlane → ExtPlane} {z w : ℂ} (hw : H (z : ExtPlane) = (w : ExtPlane)) :
    abR_t_fin H z = w := by
  rw [abR_t_fin, hw]
  rfl

/-- On the closed disc, `H` takes the finite value `abR_t_fin H z`, of modulus `≤ 1`. -/
theorem abR_t_fin_spec {h : ℂ → ℂ} {H : ExtPlane → ExtPlane}
    (hH : IsHomeoExtension h unitDisc unitDisc H) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    H (z : ExtPlane) = ((abR_t_fin H z : ℂ) : ExtPlane) ∧ ‖abR_t_fin H z‖ ≤ 1 := by
  have hmem : H (z : ExtPlane) ∈ toExt (closedBall (0 : ℂ) 1) := by
    rw [← abR_t_closure, ← hH.2.2.2]
    refine mem_image_of_mem H ?_
    rw [abR_t_closure]
    exact ⟨z, mem_closedBall_zero_iff.2 hz, rfl⟩
  obtain ⟨w, hw, hwz⟩ := hmem
  rw [abR_t_fin_of_eq hwz.symm]
  exact ⟨hwz.symm, mem_closedBall_zero_iff.1 hw⟩

/-- On `Δ`, the finite value of `H` is `h`. -/
theorem abR_t_fin_eq {h : ℂ → ℂ} {H : ExtPlane → ExtPlane}
    (hH : IsHomeoExtension h unitDisc unitDisc H) {z : ℂ} (hz : z ∈ unitDisc) :
    abR_t_fin H z = h z :=
  abR_t_fin_of_eq (hH.1 z hz)

/-- The finite value of `H` is injective on the closed disc. -/
theorem abR_t_fin_injOn {h : ℂ → ℂ} {H : ExtPlane → ExtPlane}
    (hH : IsHomeoExtension h unitDisc unitDisc H) : InjOn (abR_t_fin H) (closedBall 0 1) := by
  intro z₁ hz₁ z₂ hz₂ heq
  have hm : ∀ z ∈ closedBall (0 : ℂ) 1, (z : ExtPlane) ∈ closure (toExt unitDisc) := fun z hz => by
    rw [abR_t_closure]; exact ⟨z, hz, rfl⟩
  refine OnePoint.coe_injective (hH.2.2.1 (hm z₁ hz₁) (hm z₂ hz₂) ?_)
  rw [(abR_t_fin_spec hH (mem_closedBall_zero_iff.1 hz₁)).1,
    (abR_t_fin_spec hH (mem_closedBall_zero_iff.1 hz₂)).1, heq]

/-- The finite value of `H` maps `Δ` into `Δ`. -/
theorem abR_t_fin_lt_one {h : ℂ → ℂ} {H : ExtPlane → ExtPlane}
    (hH : IsHomeoExtension h unitDisc unitDisc H) (himg : h '' unitDisc = unitDisc) {z : ℂ}
    (hz : ‖z‖ < 1) : ‖abR_t_fin H z‖ < 1 := by
  have hzD : z ∈ unitDisc := mem_ball_zero_iff.2 hz
  have hhz : h z ∈ unitDisc := himg ▸ mem_image_of_mem h hzD
  rw [abR_t_fin_eq hH hzD]
  exact mem_ball_zero_iff.1 hhz

/-- The finite value of `H` maps the unit circle into the unit circle. -/
theorem abR_t_fin_norm_one {h : ℂ → ℂ} {H : ExtPlane → ExtPlane}
    (hH : IsHomeoExtension h unitDisc unitDisc H) (himg : h '' unitDisc = unitDisc) {z : ℂ}
    (hz : ‖z‖ = 1) : ‖abR_t_fin H z‖ = 1 := by
  refine le_antisymm (abR_t_fin_spec hH hz.le).2 (not_lt.1 fun hlt => ?_)
  have hmem : abR_t_fin H z ∈ h '' unitDisc := by rw [himg]; exact mem_ball_zero_iff.2 hlt
  obtain ⟨z', hz', hz'eq⟩ := hmem
  have hz'1 : ‖z'‖ < 1 := mem_ball_zero_iff.1 hz'
  have heq : z' = z := abR_t_fin_injOn hH (mem_closedBall_zero_iff.2 hz'1.le)
    (mem_closedBall_zero_iff.2 hz.le) (by rw [abR_t_fin_eq hH hz', hz'eq])
  rw [heq, hz] at hz'1
  exact lt_irrefl _ hz'1

/-- The finite value of `H` maps the closed disc onto the closed disc. -/
theorem abR_t_fin_surj {h : ℂ → ℂ} {H : ExtPlane → ExtPlane}
    (hH : IsHomeoExtension h unitDisc unitDisc H) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ∃ z : ℂ, ‖z‖ ≤ 1 ∧ abR_t_fin H z = w := by
  have hmem : (w : ExtPlane) ∈ H '' closure (toExt unitDisc) := by
    rw [hH.2.2.2, abR_t_closure]; exact ⟨w, mem_closedBall_zero_iff.2 hw, rfl⟩
  obtain ⟨p, hp, hpw⟩ := hmem
  rw [abR_t_closure] at hp
  obtain ⟨z, hz, rfl⟩ := hp
  exact ⟨z, mem_closedBall_zero_iff.1 hz, abR_t_fin_of_eq hpw⟩

/-- The finite value of `H` is continuous on the closed disc. -/
theorem abR_t_fin_continuousOn {h : ℂ → ℂ} {H : ExtPlane → ExtPlane}
    (hH : IsHomeoExtension h unitDisc unitDisc H) :
    ContinuousOn (abR_t_fin H) (closedBall 0 1) := by
  rw [OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_iff]
  have hc : ContinuousOn (H ∘ ((↑) : ℂ → ExtPlane)) (closedBall 0 1) := by
    refine hH.2.1.comp OnePoint.continuous_coe.continuousOn fun z hz => ?_
    rw [abR_t_closure]; exact ⟨z, hz, rfl⟩
  refine hc.congr fun z hz => ?_
  exact (abR_t_fin_spec hH (mem_closedBall_zero_iff.1 hz)).1.symm

/-- The finite value of `H` vanishes on the closed disc only at `0`. -/
theorem abR_t_fin_ne_zero {h : ℂ → ℂ} {H : ExtPlane → ExtPlane}
    (hH : IsHomeoExtension h unitDisc unitDisc H) (h0 : h 0 = 0) {w : ℂ} (hw : ‖w‖ ≤ 1)
    (hw0 : w ≠ 0) : abR_t_fin H w ≠ 0 := by
  intro heq
  have h00 : abR_t_fin H 0 = 0 := by
    rw [abR_t_fin_eq hH (mem_ball_zero_iff.2 (by simp)), h0]
  exact hw0 (abR_t_fin_injOn hH (mem_closedBall_zero_iff.2 hw)
    (mem_closedBall_zero_iff.2 (by simp)) (heq.trans h00.symm))

/-- `1/conj(1/z̄) = z`. -/
theorem abR_t_conj_inv_inv (z : ℂ) : (conj (conj z)⁻¹)⁻¹ = z := by
  rw [map_inv₀, Complex.conj_conj, inv_inv]

/-- `1/z̄ = z` on the unit circle. -/
theorem abR_t_inv_conj_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : (conj z)⁻¹ = z := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [Complex.conj_mul', hz]
  norm_num

/-- `‖1/z̄‖ = 1/‖z‖`. -/
theorem abR_t_norm_inv_conj (z : ℂ) : ‖(conj z)⁻¹‖ = ‖z‖⁻¹ := by
  rw [norm_inv, Complex.norm_conj]

/-- The reflected extension of `H`: the finite value of `H` on the closed disc, and
`1/conj(H(1/z̄))` outside it. -/
def abR_t_ext (H : ExtPlane → ExtPlane) (z : ℂ) : ℂ :=
  if ‖z‖ ≤ 1 then abR_t_fin H z else (conj (abR_t_fin H (conj z)⁻¹))⁻¹

/-- The reflected extension on the closed disc. -/
theorem abR_t_ext_of_le {H : ExtPlane → ExtPlane} {z : ℂ} (hz : ‖z‖ ≤ 1) :
    abR_t_ext H z = abR_t_fin H z :=
  ite_eq_left hz

/-- The reflected extension outside the closed disc. -/
theorem abR_t_ext_of_gt {H : ExtPlane → ExtPlane} {z : ℂ} (hz : 1 < ‖z‖) :
    abR_t_ext H z = (conj (abR_t_fin H (conj z)⁻¹))⁻¹ :=
  ite_eq_right (not_le.2 hz)

/-- The reflected extension maps the exterior of the closed disc into itself. -/
theorem abR_t_ext_norm_gt {h : ℂ → ℂ} {H : ExtPlane → ExtPlane}
    (hH : IsHomeoExtension h unitDisc unitDisc H) (himg : h '' unitDisc = unitDisc) (h0 : h 0 = 0)
    {z : ℂ} (hz : 1 < ‖z‖) : 1 < ‖abR_t_ext H z‖ := by
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
  have hw : ‖(conj z)⁻¹‖ < 1 := by rw [abR_t_norm_inv_conj]; exact inv_lt_one_of_one_lt₀ hz
  have hw0 : (conj z)⁻¹ ≠ 0 := by simpa using hz0
  have hne := abR_t_fin_ne_zero hH h0 hw.le hw0
  rw [abR_t_ext_of_gt hz, abR_t_norm_inv_conj]
  exact (one_lt_inv₀ (norm_pos_iff.2 hne)).2 (abR_t_fin_lt_one hH himg hw)

/-- The reflected extension is continuous. -/
theorem abR_t_ext_continuous {h : ℂ → ℂ} {H : ExtPlane → ExtPlane}
    (hH : IsHomeoExtension h unitDisc unitDisc H) (himg : h '' unitDisc = unitDisc) (h0 : h 0 = 0) :
    Continuous (abR_t_ext H) := by
  have hfc := abR_t_fin_continuousOn hH
  have hmaps : MapsTo (fun z : ℂ => (conj z)⁻¹) {z : ℂ | 1 ≤ ‖z‖} (closedBall 0 1) := fun z hz => by
    rw [mem_closedBall_zero_iff, abR_t_norm_inv_conj]
    exact inv_le_one_of_one_le₀ hz
  have hne : ∀ z ∈ {z : ℂ | 1 ≤ ‖z‖}, z ≠ 0 := fun z hz h => by
    subst h
    change (1 : ℝ) ≤ ‖(0 : ℂ)‖ at hz
    norm_num at hz
  have hinvc : ContinuousOn (fun z : ℂ => (conj z)⁻¹) {z : ℂ | 1 ≤ ‖z‖} :=
    Complex.continuous_conj.continuousOn.inv₀ fun z hz => (map_ne_zero _).2 (hne z hz)
  have hout : ContinuousOn (fun z : ℂ => (conj (abR_t_fin H (conj z)⁻¹))⁻¹)
      {z : ℂ | 1 ≤ ‖z‖} := by
    refine (Complex.continuous_conj.comp_continuousOn (hfc.comp hinvc hmaps)).inv₀ fun z hz => ?_
    refine (map_ne_zero _).2 (abR_t_fin_ne_zero hH h0 (mem_closedBall_zero_iff.1 (hmaps hz)) ?_)
    exact inv_ne_zero ((map_ne_zero _).2 (hne z hz))
  unfold abR_t_ext
  refine continuous_if_le continuous_norm continuous_const
    (hfc.mono fun z hz => mem_closedBall_zero_iff.2 hz) hout fun z hz => ?_
  change ‖z‖ = 1 at hz
  rw [abR_t_inv_conj_of_norm_one hz, abR_t_inv_conj_of_norm_one (abR_t_fin_norm_one hH himg hz)]

/-- The reflected extension is injective. -/
theorem abR_t_ext_injective {h : ℂ → ℂ} {H : ExtPlane → ExtPlane}
    (hH : IsHomeoExtension h unitDisc unitDisc H) (himg : h '' unitDisc = unitDisc) (h0 : h 0 = 0) :
    Function.Injective (abR_t_ext H) := by
  intro z₁ z₂ heq
  rcases le_or_gt ‖z₁‖ 1 with h₁ | h₁ <;> rcases le_or_gt ‖z₂‖ 1 with h₂ | h₂
  · rw [abR_t_ext_of_le h₁, abR_t_ext_of_le h₂] at heq
    exact abR_t_fin_injOn hH (mem_closedBall_zero_iff.2 h₁) (mem_closedBall_zero_iff.2 h₂) heq
  · have hle : ‖abR_t_ext H z₁‖ ≤ 1 := by
      rw [abR_t_ext_of_le h₁]; exact (abR_t_fin_spec hH h₁).2
    have hgt := abR_t_ext_norm_gt hH himg h0 h₂
    rw [heq] at hle
    exact absurd hle (not_le.2 hgt)
  · have hle : ‖abR_t_ext H z₂‖ ≤ 1 := by
      rw [abR_t_ext_of_le h₂]; exact (abR_t_fin_spec hH h₂).2
    have hgt := abR_t_ext_norm_gt hH himg h0 h₁
    rw [heq] at hgt
    exact absurd hle (not_le.2 hgt)
  · rw [abR_t_ext_of_gt h₁, abR_t_ext_of_gt h₂] at heq
    have h1' : ‖(conj z₁)⁻¹‖ ≤ 1 := by
      rw [abR_t_norm_inv_conj]; exact inv_le_one_of_one_le₀ h₁.le
    have h2' : ‖(conj z₂)⁻¹‖ ≤ 1 := by
      rw [abR_t_norm_inv_conj]; exact inv_le_one_of_one_le₀ h₂.le
    have hfeq : abR_t_fin H (conj z₁)⁻¹ = abR_t_fin H (conj z₂)⁻¹ := by
      have := congrArg (fun x => (conj x)⁻¹) heq
      simpa only [abR_t_conj_inv_inv] using this
    have hw := abR_t_fin_injOn hH (mem_closedBall_zero_iff.2 h1') (mem_closedBall_zero_iff.2 h2')
      hfeq
    have := congrArg (fun x => (conj x)⁻¹) hw
    simpa only [abR_t_conj_inv_inv] using this

/-- The reflected extension is surjective. -/
theorem abR_t_ext_surjective {h : ℂ → ℂ} {H : ExtPlane → ExtPlane}
    (hH : IsHomeoExtension h unitDisc unitDisc H) (himg : h '' unitDisc = unitDisc) (h0 : h 0 = 0) :
    Function.Surjective (abR_t_ext H) := by
  intro w
  rcases le_or_gt ‖w‖ 1 with hw | hw
  · obtain ⟨z, hz, rfl⟩ := abR_t_fin_surj hH hw
    exact ⟨z, abR_t_ext_of_le hz⟩
  · have hw0 : w ≠ 0 := by rintro rfl; norm_num at hw
    have hw' : ‖(conj w)⁻¹‖ ≤ 1 := by
      rw [abR_t_norm_inv_conj]; exact inv_le_one_of_one_le₀ hw.le
    obtain ⟨z', hz', hz'eq⟩ := abR_t_fin_surj hH hw'
    have hz'lt : ‖z'‖ < 1 := by
      refine lt_of_le_of_ne hz' fun h1 => ?_
      have h2 := abR_t_fin_norm_one hH himg h1
      rw [hz'eq, abR_t_norm_inv_conj, inv_eq_one] at h2
      rw [h2] at hw
      exact lt_irrefl _ hw
    have hz'0 : z' ≠ 0 := by
      rintro rfl
      have h00 : abR_t_fin H 0 = 0 := by
        rw [abR_t_fin_eq hH (mem_ball_zero_iff.2 (by simp)), h0]
      rw [h00] at hz'eq
      exact inv_ne_zero ((map_ne_zero _).2 hw0) hz'eq.symm
    refine ⟨(conj z')⁻¹, ?_⟩
    have hgt : 1 < ‖(conj z')⁻¹‖ := by
      rw [abR_t_norm_inv_conj]; exact (one_lt_inv₀ (norm_pos_iff.2 hz'0)).2 hz'lt
    rw [abR_t_ext_of_gt hgt, abR_t_conj_inv_inv z', hz'eq, abR_t_conj_inv_inv w]

/-- The reflected extension is symmetric under `z ↦ 1/z̄`. -/
theorem abR_t_ext_symm {h : ℂ → ℂ} {H : ExtPlane → ExtPlane}
    (hH : IsHomeoExtension h unitDisc unitDisc H) (himg : h '' unitDisc = unitDisc) {z : ℂ}
    (hz : z ≠ 0) : abR_t_ext H (conj z)⁻¹ = (conj (abR_t_ext H z))⁻¹ := by
  rcases lt_trichotomy ‖z‖ 1 with h1 | h1 | h1
  · have hgt : 1 < ‖(conj z)⁻¹‖ := by
      rw [abR_t_norm_inv_conj]; exact (one_lt_inv₀ (norm_pos_iff.2 hz)).2 h1
    rw [abR_t_ext_of_gt hgt, abR_t_conj_inv_inv z, abR_t_ext_of_le h1.le]
  · rw [abR_t_inv_conj_of_norm_one h1, abR_t_ext_of_le h1.le,
      abR_t_inv_conj_of_norm_one (abR_t_fin_norm_one hH himg h1)]
  · have hle : ‖(conj z)⁻¹‖ ≤ 1 := by
      rw [abR_t_norm_inv_conj]; exact inv_le_one_of_one_le₀ h1.le
    rw [abR_t_ext_of_le hle, abR_t_ext_of_gt h1, abR_t_conj_inv_inv (abR_t_fin H (conj z)⁻¹)]

/-- The reflected extension has boundary values `H` on the unit circle. -/
theorem abR_t_ext_bdry {h : ℂ → ℂ} {H : ExtPlane → ExtPlane}
    (hH : IsHomeoExtension h unitDisc unitDisc H) {z : ℂ} (hz : ‖z‖ = 1) :
    ((abR_t_ext H z : ℂ) : ExtPlane) = H (z : ExtPlane) := by
  rw [abR_t_ext_of_le hz.le]
  exact (abR_t_fin_spec hH hz.le).1.symm

/-- The reflected extension is `h` on `Δ`. -/
theorem abR_t_ext_eqOn_disc {h : ℂ → ℂ} {H : ExtPlane → ExtPlane}
    (hH : IsHomeoExtension h unitDisc unitDisc H) : EqOn (abR_t_ext H) h unitDisc := fun z hz => by
  rw [abR_t_ext_of_le (mem_ball_zero_iff.1 hz).le, abR_t_fin_eq hH hz]

/-- The reflected extension is `1/conj(h(1/z̄))` outside the closed disc. -/
theorem abR_t_ext_eqOn_ext {h : ℂ → ℂ} {H : ExtPlane → ExtPlane}
    (hH : IsHomeoExtension h unitDisc unitDisc H) :
    EqOn (abR_t_ext H) (fun z => (conj (h (conj z)⁻¹))⁻¹) {z : ℂ | 1 < ‖z‖} := fun z hz => by
  have hw : (conj z)⁻¹ ∈ unitDisc := by
    rw [unitDisc, mem_ball_zero_iff, abR_t_norm_inv_conj]; exact inv_lt_one_of_one_lt₀ hz
  rw [abR_t_ext_of_gt hz, abR_t_fin_eq hH hw]

/-- Two maps that agree on an open set have the same complex dilatation there. -/
theorem abR_t_complexDilatation_congr {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hfg : EqOn f g U) {z : ℂ} (hz : z ∈ U) : complexDilatation f z = complexDilatation g z := by
  have hev : f =ᶠ[𝓝 z] g := Filter.eventuallyEq_of_mem (hU.mem_nhds hz) hfg
  simp only [complexDilatation, dz, dzbar, hev.fderiv_eq (𝕜 := ℝ)]

/-- A `K`-q.c. self-map of `Δ` fixing `0`, with a boundary extension, extends by reflection
`z ↦ 1/z̄` to a symmetric `K`-q.c. homeomorphism of `ℂ` (Theorem 10.1 across the circle). -/
theorem ab_reflect {h : ℂ → ℂ} {K : ℝ} (hh : IsKQC h unitDisc K) (himg : h '' unitDisc = unitDisc)
    (h0 : h 0 = 0) {H : ExtPlane → ExtPlane} (hH : IsHomeoExtension h unitDisc unitDisc H) :
    ∃ g : ℂ → ℂ, IsKQC g univ K ∧ g '' univ = univ ∧ EqOn g h unitDisc ∧
      (∀ z : ℂ, ‖z‖ = 1 → ((g z : ℂ) : ExtPlane) = H (z : ExtPlane)) ∧
      (∀ z : ℂ, z ≠ 0 → g (conj z)⁻¹ = (conj (g z))⁻¹) ∧
      ∀ᵐ z, 1 < ‖z‖ → ‖complexDilatation g z‖ = ‖complexDilatation h (conj z)⁻¹‖ := by
  have hinj := abR_t_ext_injective hH himg h0
  have himg_univ : abR_t_ext H '' univ = univ := by
    rw [image_univ]; exact (abR_t_ext_surjective hH himg h0).range_eq
  have hhomeo : IsHomeomorphOnto (abR_t_ext H) univ univ := by
    have := qcl_f_isHomeomorphOnto_of_injOn isOpen_univ
      (abR_t_ext_continuous hH himg h0).continuousOn hinj.injOn
    rwa [himg_univ] at this
  have hin := abR_t_ext_eqOn_disc hH
  have hout := abR_t_ext_eqOn_ext hH
  obtain ⟨hext, hdil⟩ := abR_exterior hh himg h0
  refine ⟨abR_t_ext H, abR_removable hhomeo (ad_isKQC_congr hh hin) (ad_isKQC_congr hext hout),
    himg_univ, hin, fun z hz => abR_t_ext_bdry hH hz, fun z hz => abR_t_ext_symm hH himg hz, ?_⟩
  filter_upwards [hdil] with z hz hz1
  rw [abR_t_complexDilatation_congr (isOpen_lt continuous_const continuous_norm) hout hz1]
  exact hz hz1

/-! ### Piece D — Grötzsch lower bound -/

/-- If `F` is a continuous injective map of `ℂ` with `F(Δ) = Δ` and `ρ < 1`, then `F({ρ < |w| < 1})`
separates the unit circle from `{F a, F b}` for `|a|, |b| ≤ ρ`: `ℂ̄ ∖ F(A)` is the union of the disjoint
closed sets `F(|w| ≤ ρ)` (connected, containing `F a, F b`) and `ℂ̄ ∖ Δ` (containing the circle). -/
theorem abD_separates {F : ℂ → ℂ} (hFc : Continuous F) (hFi : Function.Injective F)
    (hFΔ : F '' unitDisc = unitDisc) {ρ : ℝ} (hρ1 : ρ < 1) {a b : ℂ} (ha : ‖a‖ ≤ ρ)
    (hb : ‖b‖ ≤ ρ) :
    SeparatesSets (F '' annulus ρ 1) (toExt (sphere 0 1))
      {((F a : ℂ) : ExtPlane), ((F b : ℂ) : ExtPlane)} := by
  set S : Set ExtPlane := (toExt (F '' annulus ρ 1))ᶜ with hS
  set P : Set ExtPlane := toExt (F '' closedBall 0 ρ) with hP
  set Q : Set ExtPlane := (toExt unitDisc)ᶜ with hQ
  have hPc : IsClosed P :=
    (((isCompact_closedBall (0 : ℂ) ρ).image hFc).image OnePoint.continuous_coe).isClosed
  have hQc : IsClosed Q := isClosed_compl_toExt isOpen_ball
  have hball : closedBall (0 : ℂ) ρ ⊆ unitDisc := closedBall_subset_ball hρ1
  have hPΔ : P ⊆ toExt unitDisc := by
    rw [hP, ← hFΔ]
    exact image_mono (image_mono hball)
  have hPS : P ⊆ S := by
    rintro _ ⟨w, ⟨u, hu, rfl⟩, rfl⟩ ⟨v, ⟨u', hu', rfl⟩, hv⟩
    have huu : u' = u := hFi (OnePoint.coe_injective hv)
    subst huu
    exact absurd (mem_closedBall_zero_iff.1 hu) (not_le.2 hu'.1)
  have hSPQ : S ⊆ P ∪ Q := by
    intro x hx
    induction x using OnePoint.rec with
    | infty => exact Or.inr (extInf_notMem_toExt _)
    | coe w =>
      by_cases hw : w ∈ unitDisc
      · left
        rw [← hFΔ] at hw
        obtain ⟨u, hu, rfl⟩ := hw
        refine ⟨F u, ⟨u, ?_, rfl⟩, rfl⟩
        rw [mem_closedBall_zero_iff]
        by_contra hlt
        push Not at hlt
        exact hx ⟨F u, ⟨u, ⟨hlt, mem_ball_zero_iff.1 hu⟩, rfl⟩, rfl⟩
      · right
        exact fun h => hw (coe_mem_toExt_iff.1 h)
  have hPQ : P ∩ Q = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hxP hxQ
    exact hxQ (hPΔ hxP)
  have hsph : IsPreconnected (toExt (sphere (0 : ℂ) 1)) :=
    (isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) 0 1).image _
      OnePoint.continuous_coe.continuousOn
  have h1sph : ((1 : ℂ) : ExtPlane) ∈ toExt (sphere (0 : ℂ) 1) := ⟨1, by simp, rfl⟩
  have hsphS : toExt (sphere (0 : ℂ) 1) ⊆ S := by
    rintro _ ⟨w, hw, rfl⟩ ⟨v, ⟨u, hu, rfl⟩, hv⟩
    have hFu : F u ∈ unitDisc := hFΔ ▸ mem_image_of_mem F (mem_ball_zero_iff.2 hu.2)
    rw [OnePoint.coe_injective hv] at hFu
    exact absurd (mem_sphere_zero_iff_norm.1 hw) (ne_of_lt (mem_ball_zero_iff.1 hFu))
  have hPconn : IsPreconnected P :=
    (isPreconnected_closedBall.image F hFc.continuousOn).image _ OnePoint.continuous_coe.continuousOn
  have haP : ((F a : ℂ) : ExtPlane) ∈ P := ⟨F a, ⟨a, mem_closedBall_zero_iff.2 ha, rfl⟩, rfl⟩
  have hbP : ((F b : ℂ) : ExtPlane) ∈ P := ⟨F b, ⟨b, mem_closedBall_zero_iff.2 hb, rfl⟩, rfl⟩
  have hPcomp : P ⊆ connectedComponentIn S ((F a : ℂ) : ExtPlane) :=
    hPconn.subset_connectedComponentIn haP hPS
  refine ⟨((1 : ℂ) : ExtPlane), hsphS h1sph, ((F a : ℂ) : ExtPlane), hPS haP,
    hsph.subset_connectedComponentIn h1sph hsphS,
    insert_subset_iff.2 ⟨hPcomp haP, singleton_subset_iff.2 (hPcomp hbP)⟩, ?_⟩
  intro heq
  have hC := isPreconnected_iff_subset_of_disjoint_closed.1
    (isPreconnected_connectedComponentIn (x := ((F a : ℂ) : ExtPlane)) (F := S)) P Q hPc hQc
    ((connectedComponentIn_subset _ _).trans hSPQ) (by rw [hPQ, inter_empty])
  have hmem1 : ((1 : ℂ) : ExtPlane) ∈ connectedComponentIn S ((F a : ℂ) : ExtPlane) :=
    heq ▸ mem_connectedComponentIn (hsphS h1sph)
  have hmema : ((F a : ℂ) : ExtPlane) ∈ connectedComponentIn S ((F a : ℂ) : ExtPlane) :=
    mem_connectedComponentIn (hPS haP)
  rcases hC with hC | hC
  · have h1 := hPΔ (hC hmem1)
    rw [coe_mem_toExt_iff] at h1
    exact absurd (mem_ball_zero_iff.1 h1) (by simp)
  · exact hC hmema (hPΔ haP)

/-- A `K`-q.c. homeomorphism of `ℂ` preserving `Δ` and fixing `0` satisfies `|G z| ≥ exp(-K μ(|z|))` on `Δ`
(Theorem 7.4 for `G⁻¹` on the annulus `|G z| < |w| < 1`, then Grötzsch, Theorem 5.1, after a rotation). -/
theorem ab_lower_bound {G : ℂ → ℂ} {K : ℝ} (hG : IsKQC G univ K) (hGs : G '' univ = univ)
    (hΔ : G '' unitDisc = unitDisc) (h0 : G 0 = 0) {z : ℂ} (hz : z ∈ unitDisc) (hz0 : z ≠ 0) :
    Real.exp (-(K * grotzschMu ‖z‖)) ≤ ‖G z‖ := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hGinj : InjOn G univ := hG.2.2.1.2.1
  have hGiG : ∀ w, Function.invFunOn G univ (G w) = w := fun w =>
    hGinj.leftInvOn_invFunOn (mem_univ w)
  have hGz : G z ∈ unitDisc := hΔ ▸ mem_image_of_mem G hz
  have hGz0 : G z ≠ 0 := fun h => hz0 (hGinj (mem_univ z) (mem_univ 0) (h.trans h0.symm))
  set ρ := ‖G z‖ with hρ
  have hρ0 : 0 < ρ := norm_pos_iff.2 hGz0
  have hρ1 : ρ < 1 := mem_ball_zero_iff.1 hGz
  -- the inverse map and the rotation `w ↦ (|z|/z) w`
  have hGi : IsKQC (Function.invFunOn G univ) univ K := by
    have h := thm7_2_inv hG
    rwa [hGs] at h
  set c : ℂ := (‖z‖ : ℂ) / z with hc
  have hc0 : c ≠ 0 := div_ne_zero (ofReal_ne_zero.2 hzn.ne') hz0
  have hc1 : ‖c‖ = 1 := by
    rw [hc, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hzn, div_self hzn.ne']
  have hrot : IsKQC (fun w => c * w) univ 1 :=
    isKQC_one_of_conformal isOpen_univ ⟨(differentiable_id.const_mul c).differentiableOn,
      fun a _ b _ h => mul_left_cancel₀ hc0 h, rfl⟩
  set F : ℂ → ℂ := (fun w => c * w) ∘ Function.invFunOn G univ with hFdef
  have hF : IsKQC F univ K := by
    have h := thm7_1_comp hGi hrot (subset_univ _)
    rwa [mul_one] at h
  have hFc : Continuous F := continuousOn_univ.1 hF.2.2.1.1
  have hFi : Function.Injective F := injOn_univ.1 hF.2.2.1.2.1
  have hGiΔ : Function.invFunOn G univ '' unitDisc = unitDisc := by
    conv_lhs => rw [← hΔ]
    exact (hGinj.leftInvOn_invFunOn.mono (subset_univ _)).image_image
  have hrotΔ : (fun w => c * w) '' unitDisc = unitDisc := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine mem_ball_zero_iff.2 ?_
      show ‖c * u‖ < 1
      rw [norm_mul, hc1, one_mul]
      exact mem_ball_zero_iff.1 hu
    · intro hw
      refine ⟨c⁻¹ * w, mem_ball_zero_iff.2 ?_, ?_⟩
      · rw [norm_mul, norm_inv, hc1, inv_one, one_mul]
        exact mem_ball_zero_iff.1 hw
      · show c * (c⁻¹ * w) = w
        rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  have hFΔ : F '' unitDisc = unitDisc := by
    rw [hFdef, image_comp, hGiΔ, hrotΔ]
  have hF0 : F 0 = 0 := by
    show c * Function.invFunOn G univ 0 = 0
    rw [← h0, hGiG, h0, mul_zero]
  have hFz : F (G z) = ((‖z‖ : ℝ) : ℂ) := by
    show c * Function.invFunOn G univ (G z) = _
    rw [hGiG, hc, div_mul_cancel₀ _ hz0]
  -- the annulus `A = {ρ < |w| < 1}` and its image `B = F(A)`
  have hA : IsDoublyConnected (annulus ρ 1) := by
    have h := nf_g_isDoublyConnected_annulusAt 0 hρ0 hρ1
    rwa [gsep_z_annulusAt_zero] at h
  have hAD : closure (toExt (annulus ρ 1)) ⊆ toExt univ :=
    (nf_e_closure_toExt_subset (isCompact_closedBall (0 : ℂ) 1)
      fun w hw => mem_closedBall_zero_iff.2 hw.2.le).trans (image_mono (subset_univ _))
  obtain ⟨hB, hAB, -⟩ := thm7_4_dcModulus_quasi_invariance hF hA hAD
  have hBsub : F '' annulus ρ 1 ⊆ unitDisc := by
    rw [← hFΔ]
    exact image_mono fun w hw => mem_ball_zero_iff.2 hw.2
  have hsep : SeparatesSets (F '' annulus ρ 1) (toExt (sphere 0 1))
      {((0 : ℂ) : ExtPlane), (((‖z‖ : ℝ) : ℂ) : ExtPlane)} := by
    have h := abD_separates hFc hFi hFΔ hρ1 (a := 0) (b := G z)
      (by rw [norm_zero]; exact hρ0.le) le_rfl
    rwa [hF0, hFz] at h
  have hgr := thm5_1_grotzsch hzn hz1 hB hBsub hsep
  rw [gz_dcModulus_grotzschDomain hzn hz1, ← gm_grotzschMu_eq hzn hz1] at hgr
  rw [dcModulus_annulus hρ0 hρ1] at hAB
  have hK0 : 0 ≤ K := zero_le_one.trans hG.2.1
  have hmu0 : 0 ≤ grotzschMu ‖z‖ := ENNReal.toReal_nonneg
  have key : ENNReal.ofReal (Real.log (1 / ρ)) ≤ ENNReal.ofReal (K * grotzschMu ‖z‖) := by
    rw [ENNReal.ofReal_mul hK0]
    calc ENNReal.ofReal (Real.log (1 / ρ)) ≤ ENNReal.ofReal K * dcModulus (F '' annulus ρ 1) :=
          hAB
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal (grotzschMu ‖z‖) := by gcongr
  rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK0 hmu0), one_div, Real.log_inv] at key
  calc Real.exp (-(K * grotzschMu ‖z‖)) ≤ Real.exp (Real.log ρ) := Real.exp_le_exp.2 (by linarith)
    _ = ρ := Real.exp_log hρ0

/-! ### Piece W — limits with vanishing dilatation are holomorphic -/

/-- For a `K`-q.c. map, almost everywhere `∂_{z̄} f = μ_f ∂_z f`, `‖μ_f‖ ≤ 1` and
`‖∂_z f‖² ≤ K J_f` (all from (9.12)). -/
theorem abW_ae_dilatation {f : ℂ → ℂ} {U : Set ℂ} {K : ℝ} (hf : IsKQC f U K) :
    ∀ᵐ z ∂(volume.restrict U), dzbar f z = complexDilatation f z * dz f z ∧
      ‖complexDilatation f z‖ ≤ 1 ∧ ‖dz f z‖ ^ 2 ≤ K * jacobian f z := by
  have hK1 : 1 ≤ K := hf.2.1
  filter_upwards [thm9_4_dilatation_ae hf] with z hz
  have hb0 : 0 ≤ ‖dzbar f z‖ := norm_nonneg _
  have ha0 : 0 ≤ ‖dz f z‖ := norm_nonneg _
  have hba : ‖dzbar f z‖ ≤ ‖dz f z‖ := by
    by_contra hlt
    push Not at hlt
    nlinarith [mul_nonneg (sub_nonneg.2 hK1) (sub_nonneg.2 hlt.le)]
  refine ⟨?_, ?_, ?_⟩
  · by_cases h0 : dz f z = 0
    · have h1 : ‖dzbar f z‖ = 0 := by
        rw [h0, norm_zero] at hba
        exact le_antisymm hba hb0
      rw [norm_eq_zero] at h1
      rw [h1, h0, mul_zero]
    · unfold complexDilatation
      field_simp
  · unfold complexDilatation
    rw [norm_div]
    by_cases h0 : ‖dz f z‖ = 0
    · rw [h0, div_zero]
      exact zero_le_one
    · exact div_le_one_of_le₀ hba ha0
  · unfold jacobian
    nlinarith [mul_le_mul_of_nonneg_right hz (add_nonneg ha0 hb0), mul_nonneg ha0 hb0]

/-- The `L²` energy of `∂_z f` over a measurable `σ ⊆ U` is at most `K m(f(σ))` (Theorem 9.5). -/
theorem abW_energy {f : ℂ → ℂ} {U : Set ℂ} {K : ℝ} (hf : IsKQC f U K) {σ : Set ℂ}
    (hσ : MeasurableSet σ) (hσU : σ ⊆ U) :
    ∫⁻ z in σ, ‖dz f z‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal K * volume (f '' σ) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hf.2.1
  calc ∫⁻ z in σ, ‖dz f z‖ₑ ^ (2 : ℝ)
      ≤ ∫⁻ z in σ, ENNReal.ofReal K * ENNReal.ofReal (jacobian f z) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hσU (abW_ae_dilatation hf)] with z hz
        rw [← ENNReal.ofReal_mul hK0, ← ofReal_norm,
          ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.rpow_two]
        exact hz.2.2
    _ = ENNReal.ofReal K * ∫⁻ z in σ, ENNReal.ofReal (jacobian f z) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * volume (f '' σ) := by
        gcongr
        exact lintegral_jacobian_le_volume_image hf hσ hσU

/-- Cauchy–Schwarz: if `aₙ ≤ 1` and `aₙ → 0` a.e. on a finite measure space and `∫ bₙ² ≤ B < ∞`,
then `∫ aₙ bₙ → 0`. -/
theorem abW_lintegral_mul_tendsto_zero {μ : Measure ℂ} [IsFiniteMeasure μ] {a b : ℕ → ℂ → ℝ≥0∞}
    (ha : ∀ n, AEMeasurable (a n) μ) (hb : ∀ n, AEMeasurable (b n) μ)
    (ha1 : ∀ n, ∀ᵐ z ∂μ, a n z ≤ 1) (ha0 : ∀ᵐ z ∂μ, Tendsto (fun n => a n z) atTop (𝓝 0))
    {B : ℝ≥0∞} (hB : B ≠ ⊤) (hbB : ∀ n, ∫⁻ z, b n z ^ (2 : ℝ) ∂μ ≤ B) :
    Tendsto (fun n => ∫⁻ z, a n z * b n z ∂μ) atTop (𝓝 0) := by
  have hX : Tendsto (fun n => ∫⁻ z, a n z ^ (2 : ℝ) ∂μ) atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence' (μ := μ)
      (F := fun n z => a n z ^ (2 : ℝ)) (f := fun _ => 0) (fun _ => 1)
      (fun n => (ha n).pow_const _)
      (fun n => (ha1 n).mono fun z hz => ENNReal.rpow_le_one hz (by norm_num))
      (by simp [measure_ne_top])
      (ha0.mono fun z hz => by
        have h2 := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp hz
        simpa [Function.comp_def, ENNReal.zero_rpow_of_pos] using h2)
    simpa using h
  have h1 : Tendsto (fun n => (∫⁻ z, a n z ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) atTop (𝓝 0) := by
    have h2 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hX
    simpa [Function.comp_def, ENNReal.zero_rpow_of_pos] using h2
  have hX' : Tendsto (fun n => (∫⁻ z, a n z ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * B ^ (1 / (2 : ℝ)))
      atTop (𝓝 0) := by
    have h3 := ENNReal.Tendsto.mul_const h1 (b := B ^ (1 / (2 : ℝ)))
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hB))
    simpa using h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hX' (fun _ => zero_le)
    fun n => ?_
  calc ∫⁻ z, a n z * b n z ∂μ
      ≤ (∫⁻ z, a n z ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (∫⁻ z, b n z ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two (ha n) (hb n)
    _ ≤ (∫⁻ z, a n z ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * B ^ (1 / (2 : ℝ)) := by
        gcongr
        exact hbB n

/-- Integration by parts for a `K`-q.c. map against a `C¹` test function compactly supported in `U`:
`∫_U f ∂_{z̄}ψ = -∫_U ψ ∂_{z̄} f` (generalized derivatives of Theorem 9.5, `sp_ibp`). -/
theorem abW_ibp {f : ℂ → ℂ} {U : Set ℂ} {K : ℝ} (hf : IsKQC f U K) {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ U) :
    ∫ z in U, f z * dzbar ψ z = -∫ z in U, ψ z * dzbar f z := by
  have hU : IsOpen U := hf.1
  have hv := (thm9_5_L2_derivatives hf).1
  obtain ⟨h1, hI⟩ := sp_ibp hU hv hψ hcψ hsψ
  have hKc : IsCompact (tsupport ψ) := hcψ.isCompact
  have hKm : MeasurableSet (tsupport ψ) := hKc.isClosed.measurableSet
  have hψ0 : ∀ z ∉ tsupport ψ, ψ z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hfc : ContinuousOn f U := hf.2.2.1.1
  have hint1 : ∀ e : ℂ, IntegrableOn (fun z => fderiv ℝ ψ z e * f z) U := by
    intro e
    have hdψc : Continuous (fun z => fderiv ℝ ψ z e) :=
      (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    refine (sp_ibp_integrable_of_support hKm ?_ fun z hz => by
      rw [sp_fderiv_eq_zero_of_notMem_tsupport hz e, zero_mul]).integrableOn
    exact (hdψc.continuousOn.mul (hfc.mono hsψ)).integrableOn_compact hKc
  have hψL : MemLp ψ 2 (volume.restrict (tsupport ψ)) :=
    (hψ.continuous.memLp_of_hasCompactSupport (μ := volume) hcψ).restrict _
  have hint2 : ∀ g : ℂ → ℂ, MemLp g 2 (volume.restrict (tsupport ψ)) →
      IntegrableOn (fun z => ψ z * g z) U := fun g hg =>
    (sp_ibp_integrable_of_support hKm (hψL.integrable_mul hg) fun z hz => by
      rw [Pi.mul_apply, hψ0 z hz, zero_mul]).integrableOn
  have hgx := hint2 _ (hv.1 _ hsψ hKc).1
  have hgy := hint2 _ (hv.1 _ hsψ hKc).2
  have hae : ∀ᵐ z ∂(volume.restrict U), ψ z * dzbar f z =
      (ψ z * partialX f z + I * (ψ z * partialY f z)) / 2 := by
    filter_upwards [thm9_3_differentiable_ae hf] with z hz
    rw [partialX_eq_of_differentiableAt hz, partialY_eq_of_differentiableAt hz]
    unfold dzbar
    ring
  have hL : ∫ z in U, f z * dzbar ψ z =
      ((∫ z in U, fderiv ℝ ψ z 1 * f z) + I * ∫ z in U, fderiv ℝ ψ z I * f z) / 2 := by
    rw [← integral_const_mul, ← integral_add (hint1 1) ((hint1 I).const_mul I), ← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [dzbar]
    ring
  have hR : ∫ z in U, ψ z * dzbar f z =
      ((∫ z in U, ψ z * partialX f z) + I * ∫ z in U, ψ z * partialY f z) / 2 := by
    rw [integral_congr_ae hae, ← integral_const_mul, ← integral_add hgx (hgy.const_mul I),
      ← integral_div]
  rw [hL, hR, h1, hI]
  ring

/-- For uniformly bounded `K`-q.c. maps whose dilatations tend to `0` a.e., `∫_C |∂_{z̄} Gₙ| → 0` on
every compact `C ⊆ U` (Cauchy–Schwarz against the energy bound). -/
theorem abW_tendsto_lintegral_dzbar {U : Set ℂ} {K : ℝ} {Gn : ℕ → ℂ → ℂ}
    (hG : ∀ n, IsKQC (Gn n) U K) {M : ℝ} (hM : ∀ n, ∀ z ∈ U, ‖Gn n z‖ ≤ M)
    (hμ : ∀ᵐ z ∂(volume.restrict U), Tendsto (fun n => complexDilatation (Gn n) z) atTop (𝓝 0))
    {C : Set ℂ} (hC : IsCompact C) (hCU : C ⊆ U) :
    Tendsto (fun n => ∫⁻ z in C, ‖dzbar (Gn n) z‖ₑ) atTop (𝓝 0) := by
  have : IsFiniteMeasure (volume.restrict C) := isFiniteMeasure_restrict.2 hC.measure_lt_top.ne
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have heq : ∀ n, ∫⁻ z in C, ‖dzbar (Gn n) z‖ₑ =
      ∫⁻ z in C, ‖complexDilatation (Gn n) z‖ₑ * ‖dz (Gn n) z‖ₑ := fun n => by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hCU (abW_ae_dilatation (hG n))] with z hz
    rw [hz.1, enorm_mul]
  simp_rw [heq]
  refine abW_lintegral_mul_tendsto_zero
    (b := fun n z => ‖dz (Gn n) z‖ₑ) (B := ENNReal.ofReal K * volume (closedBall (0 : ℂ) M))
    (fun n => ((measurable_dzbar _).div (measurable_dz _)).enorm.aemeasurable)
    (fun n => (measurable_dz _).enorm.aemeasurable) (fun n => ?_) ?_
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_closedBall_lt_top (μ := (volume : Measure ℂ)) (x := (0 : ℂ)) (r := M)).ne)
    (fun n => ?_)
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset hCU (abW_ae_dilatation (hG n))] with z hz
    rw [← ofReal_norm, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hz.2.1
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset hCU hμ] with z hz
    simpa using hz.enorm
  · refine (abW_energy (hG n) hCm hCU).trans ?_
    gcongr
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    exact hM n z (hCU hz)

/-- A locally uniform limit of uniformly bounded `K`-q.c. maps whose dilatations tend to `0` a.e. is
holomorphic (`∫ Gₙ ∂̄φ = -∫ μₙ ∂Gₙ φ → 0` by Cauchy–Schwarz and Theorem 9.5, then `sp_w_weyl`). -/
theorem ab_limit_holomorphic {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) {K : ℝ}
    {Gn : ℕ → ℂ → ℂ} {G : ℂ → ℂ} (hG : ∀ n, IsKQC (Gn n) U K)
    (hbd : ∃ M : ℝ, ∀ n, ∀ z ∈ U, ‖Gn n z‖ ≤ M) (hlim : TendstoLocallyUniformlyOn Gn G atTop U)
    (hμ : ∀ᵐ z ∂(volume.restrict U), Tendsto (fun n => complexDilatation (Gn n) z) atTop (𝓝 0)) :
    DifferentiableOn ℂ G U := by
  -- boundedness of `U` is not needed: the energy bound uses `Gₙ(C) ⊆ B̄(0, M)` for compact `C ⊆ U`
  have _ : Bornology.IsBounded U := hUb
  obtain ⟨M, hM⟩ := hbd
  have hGc : ContinuousOn G U :=
    hlim.continuousOn (Frequently.of_forall fun n => (hG n).2.2.1.1)
  refine sp_w_weyl hU hGc fun ψ hψ hcψ hsψ => ?_
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hKc : IsCompact (tsupport ψ) := hcψ.isCompact
  have hKm : MeasurableSet (tsupport ψ) := hKc.isClosed.measurableSet
  have hdψ0 : ∀ z ∉ tsupport ψ, dzbar ψ z = 0 := fun z hz => by
    unfold dzbar
    rw [sp_fderiv_eq_zero_of_notMem_tsupport hz 1, sp_fderiv_eq_zero_of_notMem_tsupport hz I]
    ring
  have hdψc : Continuous (dzbar ψ) := by
    have hc : ∀ v : ℂ, Continuous fun z => fderiv ℝ ψ z v := fun v =>
      (hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact ((hc 1).add (continuous_const.mul (hc I))).div_const 2
  -- both integrals live on the compact set `tsupport ψ`
  have hU2C : ∀ F : ℂ → ℂ, ∫ z in U, F z * dzbar ψ z = ∫ z in tsupport ψ, F z * dzbar ψ z :=
    fun F => by
      have h0 : ∀ z ∉ tsupport ψ, F z * dzbar ψ z = 0 := fun z hz => by rw [hdψ0 z hz, mul_zero]
      rw [sp_setIntegral_eq_integral hU.measurableSet hsψ h0,
        ← sp_setIntegral_eq_integral hKm subset_rfl h0]
  -- (1) `∫_U Gₙ ∂̄ψ → ∫_U G ∂̄ψ` (uniform convergence on `tsupport ψ`)
  have hconv : Tendsto (fun n => ∫ z in U, Gn n z * dzbar ψ z) atTop
      (𝓝 (∫ z in U, G z * dzbar ψ z)) := by
    simp_rw [hU2C]
    exact sp_tendsto_integral_mul_of_uniform (hdψc.continuousOn.integrableOn_compact hKc)
      (fun n => ((((hG n).2.2.1.1).mono hsψ).mul hdψc.continuousOn).integrableOn_compact hKc)
      (((hGc.mono hsψ).mul hdψc.continuousOn).integrableOn_compact hKc)
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hlim _ hsψ hKc)
  -- (2) `∫_U Gₙ ∂̄ψ = -∫_U ψ ∂̄Gₙ → 0`
  have hzero : Tendsto (fun n => ∫ z in U, Gn n z * dzbar ψ z) atTop (𝓝 0) := by
    obtain ⟨Cψ, hCψ⟩ := hψ1.continuous.bounded_above_of_compact_support hcψ
    have hT := abW_tendsto_lintegral_dzbar hG hM hμ hKc hsψ
    have hT' : Tendsto (fun n => ENNReal.ofReal Cψ * ∫⁻ z in tsupport ψ, ‖dzbar (Gn n) z‖ₑ)
        atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hT (Or.inr ENNReal.ofReal_ne_top)
    refine tendsto_zero_iff_enorm_tendsto_zero.2
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT' (fun _ => zero_le)
        fun n => ?_)
    have hsupp : Function.support (fun z => ‖ψ z * dzbar (Gn n) z‖ₑ) ⊆ tsupport ψ := by
      intro z hz
      by_contra hzK
      exact hz (show ‖ψ z * dzbar (Gn n) z‖ₑ = 0 by
        rw [image_eq_zero_of_notMem_tsupport hzK, zero_mul, enorm_zero])
    calc ‖∫ z in U, Gn n z * dzbar ψ z‖ₑ
        = ‖∫ z in U, ψ z * dzbar (Gn n) z‖ₑ := by
          rw [abW_ibp (hG n) hψ1 hcψ hsψ, enorm_neg]
      _ ≤ ∫⁻ z in U, ‖ψ z * dzbar (Gn n) z‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ z, ‖ψ z * dzbar (Gn n) z‖ₑ := setLIntegral_le_lintegral _ _
      _ = ∫⁻ z in tsupport ψ, ‖ψ z * dzbar (Gn n) z‖ₑ :=
          (setLIntegral_eq_of_support_subset hsupp).symm
      _ ≤ ∫⁻ z in tsupport ψ, ENNReal.ofReal Cψ * ‖dzbar (Gn n) z‖ₑ := by
          refine lintegral_mono fun z => ?_
          rw [enorm_mul, ← ofReal_norm]
          gcongr
          exact hCψ z
      _ = ENNReal.ofReal Cψ * ∫⁻ z in tsupport ψ, ‖dzbar (Gn n) z‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  exact tendsto_nhds_unique hconv hzero

/-! ### Piece L — symmetric normalized maps with vanishing dilatation tend to the identity -/

/-- The uniform bound on `B(0,2)`: `|G z| ≤ exp(K μ(1/2))`, on `Δ` because `G(Δ) = Δ`, on the unit circle by
symmetry, and on `1 < |z| < 2` by symmetry and the Grötzsch lower bound `ab_lower_bound` at `1/z̄`. -/
theorem abL_bound {G : ℂ → ℂ} {K : ℝ} (hG : IsKQC G univ K) (hGs : G '' univ = univ)
    (hΔ : G '' unitDisc = unitDisc) (h0 : G 0 = 0)
    (hsym : ∀ z : ℂ, z ≠ 0 → G (conj z)⁻¹ = (conj (G z))⁻¹) :
    ∀ z : ℂ, ‖z‖ < 2 → ‖G z‖ ≤ Real.exp (K * grotzschMu (1 / 2)) := by
  have hK : 0 ≤ K := zero_le_one.trans hG.2.1
  have hμ0 : 0 ≤ grotzschMu (1 / 2) := ENNReal.toReal_nonneg
  have hM1 : 1 ≤ Real.exp (K * grotzschMu (1 / 2)) := Real.one_le_exp (mul_nonneg hK hμ0)
  intro z hz2
  rcases lt_trichotomy ‖z‖ 1 with hz1 | hz1 | hz1
  · have hmem : G z ∈ unitDisc := by
      rw [← hΔ]
      exact mem_image_of_mem G (mem_ball_zero_iff.2 hz1)
    exact (mem_ball_zero_iff.1 hmem).le.trans hM1
  · have hz0 : z ≠ 0 := by
      rintro rfl
      simp at hz1
    have hcz : (conj z)⁻¹ = z := by
      rw [← Complex.inv_eq_conj hz1, inv_inv]
    have hs := hsym z hz0
    rw [hcz] at hs
    have hn : ‖G z‖ = ‖G z‖⁻¹ := by
      conv_lhs => rw [hs]
      rw [norm_inv, Complex.norm_conj]
    have hle : ‖G z‖ ≤ 1 := by
      by_contra hlt
      push Not at hlt
      have hinv := inv_lt_one_of_one_lt₀ hlt
      rw [← hn] at hinv
      exact absurd hlt (not_lt.2 hinv.le)
    exact hle.trans hM1
  · have hzpos : 0 < ‖z‖ := zero_lt_one.trans hz1
    have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
    set w : ℂ := (conj z)⁻¹ with hwdef
    have hwn : ‖w‖ = ‖z‖⁻¹ := by
      rw [hwdef, norm_inv, Complex.norm_conj]
    have hw1 : ‖w‖ < 1 := by
      rw [hwn]
      exact inv_lt_one_of_one_lt₀ hz1
    have hw2 : 1 / 2 < ‖w‖ := by
      rw [hwn, one_div]
      exact inv_strictAnti₀ hzpos hz2
    have hw0 : w ≠ 0 := by
      rw [hwdef]
      exact inv_ne_zero ((map_ne_zero _).2 hz0)
    have hwz : (conj w)⁻¹ = z := by
      rw [hwdef, map_inv₀, Complex.conj_conj, inv_inv]
    have hs := hsym w hw0
    rw [hwz] at hs
    have hlb := ab_lower_bound hG hGs hΔ h0 (mem_ball_zero_iff.2 hw1) hw0
    have hμle : grotzschMu ‖w‖ ≤ grotzschMu (1 / 2) :=
      (grotzschMu_strictAntiOn ⟨by norm_num, by norm_num⟩
        ⟨(by norm_num : (0 : ℝ) < 1 / 2).trans hw2, hw1⟩ hw2).le
    rw [hs, norm_inv, Complex.norm_conj]
    calc ‖G w‖⁻¹ ≤ (Real.exp (-(K * grotzschMu ‖w‖)))⁻¹ := inv_anti₀ (Real.exp_pos _) hlb
      _ = Real.exp (K * grotzschMu ‖w‖) := by rw [Real.exp_neg, inv_inv]
      _ ≤ Real.exp (K * grotzschMu (1 / 2)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hμle hK)

/-- Identification of the limit (Schwarz lemma, symmetry and the maximum modulus principle): an injective
holomorphic map of `B(0,2)` fixing `0` and `1`, sending `Δ` into `Δ̄` and symmetric in the unit circle, is
the identity on `B(0,2)`.  (`|f z| ≤ |z|` on `Δ` gives `|f w| ≥ |w|` on `1 < |w| < 2`, so `z/f(z)` is
bounded by `1` on every circle `|z| = r ∈ (1,2)` and takes the value `1` at `z = 1`.) -/
theorem abL_eq_id_of_symm {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball 0 2))
    (hinj : InjOn f (ball 0 2)) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hmaps : MapsTo f (ball 0 1) (closedBall 0 1))
    (hsym : ∀ z : ℂ, 1 / 2 < ‖z‖ → ‖z‖ < 1 → f (conj z)⁻¹ = (conj (f z))⁻¹) :
    ∀ z : ℂ, ‖z‖ < 2 → f z = z := by
  have h02 : (0 : ℂ) ∈ ball (0 : ℂ) 2 := mem_ball_self (by norm_num)
  -- `f` vanishes only at `0`
  have hfne : ∀ z : ℂ, ‖z‖ < 2 → z ≠ 0 → f z ≠ 0 := by
    intro z hz hz0 hfz
    exact hz0 (hinj (mem_ball_zero_iff.2 hz) h02 (hfz.trans hf0.symm))
  -- Schwarz lemma on `Δ`
  have hsch : ∀ z : ℂ, ‖z‖ < 1 → ‖f z‖ ≤ ‖z‖ := fun z hz =>
    Complex.norm_le_norm_of_mapsTo_ball (hd.mono (ball_subset_ball (by norm_num))) hmaps hf0 hz
  -- the reversed inequality on the annulus `1 < |w| < 2`, by symmetry
  have hann : ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ < 2 → ‖w‖ ≤ ‖f w‖ := by
    intro w hw1 hw2
    have hwpos : 0 < ‖w‖ := zero_lt_one.trans hw1
    have hw0 : w ≠ 0 := norm_pos_iff.1 hwpos
    have hzn : ‖(conj w)⁻¹‖ = ‖w‖⁻¹ := by
      rw [norm_inv, Complex.norm_conj]
    have hz1 : ‖(conj w)⁻¹‖ < 1 := by
      rw [hzn]
      exact inv_lt_one_of_one_lt₀ hw1
    have hz2 : 1 / 2 < ‖(conj w)⁻¹‖ := by
      rw [hzn, one_div]
      exact inv_strictAnti₀ hwpos hw2
    have hzw : (conj (conj w)⁻¹)⁻¹ = w := by
      rw [map_inv₀, Complex.conj_conj, inv_inv]
    have hfw : f w = (conj (f (conj w)⁻¹))⁻¹ := by
      have e := hsym _ hz2 hz1
      rw [hzw] at e
      exact e
    have hfz0 : f (conj w)⁻¹ ≠ 0 :=
      hfne _ (hz1.trans (by norm_num)) (inv_ne_zero ((map_ne_zero _).2 hw0))
    have hle := hsch _ hz1
    rw [hzn] at hle
    rw [hfw, norm_inv, Complex.norm_conj]
    have hpos : 0 < ‖f (conj w)⁻¹‖ := norm_pos_iff.2 hfz0
    calc ‖w‖ = (‖w‖⁻¹)⁻¹ := (inv_inv _).symm
      _ ≤ ‖f (conj w)⁻¹‖⁻¹ := inv_anti₀ hpos hle
  -- the divided difference `g = f(z)/z`
  set g : ℂ → ℂ := dslope f 0 with hgdef
  have hgd : DifferentiableOn ℂ g (ball 0 2) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds h02)).2 hd
  have hg_of_ne : ∀ z : ℂ, z ≠ 0 → g z = f z / z := by
    intro z hz
    rw [hgdef, dslope_of_ne _ hz, slope_def_field, hf0, sub_zero, sub_zero]
  have hg0 : g 0 ≠ 0 := by
    rw [hgdef, dslope_same]
    exact deriv_ne_zero_of_injOn isOpen_ball hd hinj h02
  have hgne : ∀ z : ℂ, ‖z‖ < 2 → g z ≠ 0 := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · exact hg0
    · rw [hg_of_ne z hz0]
      exact div_ne_zero (hfne z hz hz0) hz0
  have hg1 : g 1 = 1 := by
    rw [hg_of_ne 1 one_ne_zero, hf1, div_one]
  -- `h = 1/g` is holomorphic on `B(0,2)`, bounded by `1` on the annulus, and `h 1 = 1`
  set h : ℂ → ℂ := fun z => (g z)⁻¹ with hhdef
  have hhd : DifferentiableOn ℂ h (ball 0 2) :=
    hgd.inv fun z hz => hgne z (mem_ball_zero_iff.1 hz)
  have hh1 : h 1 = 1 := by
    rw [hhdef]
    simp only [hg1, inv_one]
  have hhann : ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ < 2 → ‖h w‖ ≤ 1 := by
    intro w hw1 hw2
    have hwpos : 0 < ‖w‖ := zero_lt_one.trans hw1
    have hw0 : w ≠ 0 := norm_pos_iff.1 hwpos
    have hgw : 1 ≤ ‖g w‖ := by
      rw [hg_of_ne w hw0, norm_div, le_div_iff₀ hwpos, one_mul]
      exact hann w hw1 hw2
    have e : ‖h w‖ = ‖g w‖⁻¹ := by
      rw [hhdef]
      exact norm_inv _
    rw [e]
    exact inv_le_one_of_one_le₀ hgw
  intro z hz
  rcases eq_or_ne z 0 with rfl | hz0
  · exact hf0
  -- maximum modulus on `B(0,r)`, `max 1 |z| < r < 2`
  set r : ℝ := (max 1 ‖z‖ + 2) / 2 with hrdef
  have hr1 : 1 < r := by
    have := le_max_left 1 ‖z‖
    rw [hrdef]
    linarith
  have hr2 : r < 2 := by
    have : max 1 ‖z‖ < 2 := max_lt (by norm_num) hz
    rw [hrdef]
    linarith
  have hzr : ‖z‖ < r := by
    have := le_max_right 1 ‖z‖
    rw [hrdef]
    linarith
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 2 := closedBall_subset_ball hr2
  have hbd : ∀ y ∈ closure (ball (0 : ℂ) r), ‖h y‖ ≤ 1 := by
    intro y hy
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (hhd.diffContOnCl_ball hsub) (fun w hw => ?_) hy
    have hw' : ‖w‖ = r := mem_sphere_zero_iff_norm.1 (frontier_ball_subset_sphere hw)
    refine hhann w ?_ ?_
    · rw [hw']
      exact hr1
    · rw [hw']
      exact hr2
  have h1r : (1 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_zero_iff.2 (by simpa using hr1)
  have hmax : IsMaxOn (norm ∘ h) (ball 0 r) 1 := by
    refine isMaxOn_iff.2 fun y hy => ?_
    simp only [Function.comp_apply, hh1, norm_one]
    exact hbd y (subset_closure hy)
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    (convex_ball (0 : ℂ) r).isPreconnected isOpen_ball
    (hhd.mono (ball_subset_closedBall.trans hsub)) h1r hmax (mem_ball_zero_iff.2 hzr)
  have hhz : h z = 1 := by
    rw [heq, Function.const_apply, hh1]
  have hgz : g z = 1 := by
    have e : (g z)⁻¹ = 1 := hhz
    exact inv_eq_one.1 e
  rw [hg_of_ne z hz0] at hgz
  exact (div_eq_one_iff_eq hz0).1 hgz

/-- Every sequence as in `ab_tendsto_id` has a subsequence converging to the identity pointwise on `B(0,2)`:
Theorem 8.1 on `B(0,2)` (bound `abL_bound`), Theorem 8.2 (the limit is not constant, so it is injective),
`ab_limit_holomorphic`, and `abL_eq_id_of_symm` for the limit. -/
theorem abL_exists_subseq {Gn : ℕ → ℂ → ℂ} {K : ℝ} (hG : ∀ n, IsKQC (Gn n) univ K)
    (hs : ∀ n, Gn n '' univ = univ) (hΔ : ∀ n, Gn n '' unitDisc = unitDisc) (h0 : ∀ n, Gn n 0 = 0)
    (h1 : ∀ n, Gn n 1 = 1) (hsym : ∀ n, ∀ z : ℂ, z ≠ 0 → Gn n (conj z)⁻¹ = (conj (Gn n z))⁻¹)
    (hμ : ∀ᵐ z, Tendsto (fun n => complexDilatation (Gn n) z) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ z : ℂ, ‖z‖ < 2 → Tendsto (fun n => Gn (φ n) z) atTop (𝓝 z) := by
  have hDb : Bornology.IsBounded (ball (0 : ℂ) 2) := isBounded_ball
  have hDc : IsConnected (ball (0 : ℂ) 2) := isConnected_ball (by norm_num)
  have hqc : ∀ n, IsKQC (Gn n) (ball 0 2) K := fun n =>
    nx_isKQC_restrict (hG n) isOpen_ball (subset_univ _)
  have hM : ∀ n, ∀ z ∈ ball (0 : ℂ) 2, ‖Gn n z‖ ≤ Real.exp (K * grotzschMu (1 / 2)) :=
    fun n z hz => abL_bound (hG n) (hs n) (hΔ n) (h0 n) (hsym n) z (mem_ball_zero_iff.1 hz)
  obtain ⟨φ, hφ, f, hlim⟩ := thm8_1_normal_family hDb hDc hqc hM
  have hqcφ : ∀ n, IsKQC (Gn (φ n)) (ball 0 2) K := fun n => hqc (φ n)
  have hpt : ∀ z : ℂ, ‖z‖ < 2 → Tendsto (fun n => Gn (φ n) z) atTop (𝓝 (f z)) :=
    fun z hz => hlim.tendsto_at (mem_ball_zero_iff.2 hz)
  have hf0 : f 0 = 0 := by
    refine tendsto_nhds_unique (hpt 0 (by norm_num)) ?_
    simp only [h0]
    exact tendsto_const_nhds
  have hf1 : f 1 = 1 := by
    refine tendsto_nhds_unique (hpt 1 (by norm_num)) ?_
    simp only [h1]
    exact tendsto_const_nhds
  have hKQC : IsKQC f (ball 0 2) K := by
    rcases thm8_2_limit hDb hDc hqcφ hlim with ⟨c, hc⟩ | hq
    · exfalso
      have e0 := hc 0 (mem_ball_self (by norm_num))
      have e1 := hc 1 (mem_ball_zero_iff.2 (by norm_num))
      rw [hf0] at e0
      rw [hf1] at e1
      exact one_ne_zero (e1.trans e0.symm)
    · exact hq
  have hinj : InjOn f (ball 0 2) := hKQC.2.2.1.2.1
  have hμ' : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 2)),
      Tendsto (fun n => complexDilatation (Gn (φ n)) z) atTop (𝓝 0) :=
    ae_restrict_of_ae (hμ.mono fun z hz => hz.comp hφ.tendsto_atTop)
  have hdiff : DifferentiableOn ℂ f (ball 0 2) :=
    ab_limit_holomorphic isOpen_ball hDb hqcφ ⟨_, fun n => hM (φ n)⟩ hlim hμ'
  have hmaps : MapsTo f (ball 0 1) (closedBall 0 1) := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    refine isClosed_closedBall.mem_of_tendsto (hpt z (hz1.trans (by norm_num)))
      (Eventually.of_forall fun n => ?_)
    have hmem : Gn (φ n) z ∈ unitDisc := by
      rw [← hΔ (φ n)]
      exact mem_image_of_mem _ hz
    exact ball_subset_closedBall hmem
  have hsymf : ∀ z : ℂ, 1 / 2 < ‖z‖ → ‖z‖ < 1 → f (conj z)⁻¹ = (conj (f z))⁻¹ := by
    intro z hz1 hz2
    have hzpos : 0 < ‖z‖ := (by norm_num : (0 : ℝ) < 1 / 2).trans hz1
    have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
    have hzD : ‖z‖ < 2 := hz2.trans (by norm_num)
    have hwD : ‖(conj z)⁻¹‖ < 2 := by
      rw [norm_inv, Complex.norm_conj]
      calc ‖z‖⁻¹ < (1 / 2)⁻¹ := inv_strictAnti₀ (by norm_num) hz1
        _ = 2 := by norm_num
    have hfz0 : f z ≠ 0 := fun hfz =>
      hz0 (hinj (mem_ball_zero_iff.2 hzD) (mem_ball_self (by norm_num)) (hfz.trans hf0.symm))
    have hA := hpt _ hwD
    have hB : Tendsto (fun n => (conj (Gn (φ n) z))⁻¹) atTop (𝓝 (conj (f z))⁻¹) :=
      ((Complex.continuous_conj.tendsto _).comp (hpt z hzD)).inv₀ ((map_ne_zero _).2 hfz0)
    refine tendsto_nhds_unique hA (hB.congr fun n => ?_)
    exact (hsym (φ n) z hz0).symm
  refine ⟨φ, hφ, fun z hz => ?_⟩
  have hz' := hpt z hz
  rwa [abL_eq_id_of_symm hdiff hinj hf0 hf1 hmaps hsymf z hz] at hz'

/-- Symmetric `K`-q.c. homeomorphisms of `ℂ` preserving `Δ`, fixing `0` and `1`, whose dilatations tend to `0`
a.e., converge to the identity on `B(0,2)`. -/
theorem ab_tendsto_id {Gn : ℕ → ℂ → ℂ} {K : ℝ} (hG : ∀ n, IsKQC (Gn n) univ K)
    (hs : ∀ n, Gn n '' univ = univ) (hΔ : ∀ n, Gn n '' unitDisc = unitDisc) (h0 : ∀ n, Gn n 0 = 0)
    (h1 : ∀ n, Gn n 1 = 1) (hsym : ∀ n, ∀ z : ℂ, z ≠ 0 → Gn n (conj z)⁻¹ = (conj (Gn n z))⁻¹)
    (hμ : ∀ᵐ z, Tendsto (fun n => complexDilatation (Gn n) z) atTop (𝓝 0)) :
    ∀ z : ℂ, ‖z‖ < 2 → Tendsto (fun n => Gn n z) atTop (𝓝 z) := by
  intro z hz
  refine Filter.tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨φ, -, hφ⟩ := abL_exists_subseq (Gn := fun n => Gn (ns n)) (fun n => hG (ns n))
    (fun n => hs (ns n)) (fun n => hΔ (ns n)) (fun n => h0 (ns n)) (fun n => h1 (ns n))
    (fun n => hsym (ns n)) (hμ.mono fun w hw => hw.comp hns)
  exact ⟨φ, hφ z hz⟩

/-! ### Piece M — the Möbius normalizations tend to the identity -/

/-- The Cramer-rule identity recovering `ā` from the values of `abMob a` at `i` and `-1`. -/
theorem abM_key {a : ℂ} (ha : ‖a‖ < 1) :
    conj a * (abMob a (-1) * (1 - I) + 2 * I * abMob a I - I - 1) =
      2 * abMob a I + abMob a (-1) * (I - 1) - I - 1 := by
  have h1 : (1 : ℂ) - a ≠ 0 := abN_one_sub_ne_zero ha
  have hI : (1 : ℂ) - conj a * I ≠ 0 := abN_den_ne_zero ha (by simp)
  have hm : (1 : ℂ) - conj a * (-1) ≠ 0 := abN_den_ne_zero ha (by simp)
  have e1 : (1 - conj a) / (1 - a) * (1 - a) = 1 - conj a := div_mul_cancel₀ _ h1
  have e2 : abMob a I * (1 - conj a * I) = (1 - conj a) / (1 - a) * (I - a) := by
    rw [abMob, mul_assoc, div_mul_cancel₀ _ hI]
  have e3 : abMob a (-1) * (1 - conj a * (-1)) = (1 - conj a) / (1 - a) * (-1 - a) := by
    rw [abMob, mul_assoc, div_mul_cancel₀ _ hm]
  linear_combination (-I - 1) * e1 - 2 * e2 - (I - 1) * e3

/-- If `abMob aₙ` nearly fixes `i` and `-1` (it always fixes `1`), then `aₙ → 0`. -/
theorem ab_mob_tendsto {a : ℕ → ℂ} (ha : ∀ n, a n ∈ unitDisc)
    (hi : Tendsto (fun n => abMob (a n) I) atTop (𝓝 I))
    (hm : Tendsto (fun n => abMob (a n) (-1)) atTop (𝓝 (-1))) : Tendsto a atTop (𝓝 0) := by
  have hD : Tendsto (fun n => abMob (a n) (-1) * (1 - I) + 2 * I * abMob (a n) I - I - 1) atTop
      (𝓝 ((-1) * (1 - I) + 2 * I * I - I - 1)) :=
    (((hm.mul_const (1 - I)).add (hi.const_mul (2 * I))).sub_const I).sub_const 1
  have hN : Tendsto (fun n => 2 * abMob (a n) I + abMob (a n) (-1) * (I - 1) - I - 1) atTop
      (𝓝 (2 * I + (-1) * (I - 1) - I - 1)) :=
    (((hi.const_mul 2).add (hm.mul_const (I - 1))).sub_const I).sub_const 1
  have hD0 : ((-1) * (1 - I) + 2 * I * I - I - 1 : ℂ) = -4 := by
    have hII : I * I = -1 := I_mul_I
    linear_combination 2 * hII
  have hN0 : (2 * I + (-1) * (I - 1) - I - 1 : ℂ) = 0 := by ring
  have hne : ((-1) * (1 - I) + 2 * I * I - I - 1 : ℂ) ≠ 0 := by
    rw [hD0]
    norm_num
  have hq := hN.div hD hne
  rw [hN0, zero_div] at hq
  have hc : Tendsto (fun n => conj (a n)) atTop (𝓝 0) := by
    refine hq.congr' ?_
    filter_upwards [hD.eventually_ne hne] with n hn
    have hk := abM_key (mem_ball_zero_iff.1 (ha n))
    rw [Pi.div_apply, ← hk, mul_div_cancel_right₀ _ hn]
  have hcc : Tendsto (fun n => conj (conj (a n))) atTop (𝓝 (conj 0)) :=
    (Complex.continuous_conj.tendsto 0).comp hc
  simpa using hcc

/-- The explicit estimate `‖abMob a v - v‖ ≤ 32 ‖a‖` for `‖a‖ ≤ 1/2`, `‖v‖ ≤ 1`. -/
theorem abM_norm_sub_le {a v : ℂ} (ha : ‖a‖ ≤ 1 / 2) (hv : ‖v‖ ≤ 1) :
    ‖abMob a v - v‖ ≤ 32 * ‖a‖ := by
  have ha1 : ‖a‖ < 1 := by linarith
  have h1 : (1 : ℂ) - a ≠ 0 := abN_one_sub_ne_zero ha1
  have h2 : (1 : ℂ) - conj a * v ≠ 0 := abN_den_ne_zero ha1 hv
  have key : abMob a v - v = (v - 1) * (a + conj a * v - a * conj a * (v + 1)) /
      ((1 - a) * (1 - conj a * v)) := by
    rw [abMob, eq_div_iff (mul_ne_zero h1 h2)]
    field_simp
    ring
  have hb1 : 1 / 2 ≤ ‖1 - a‖ := by
    have h := norm_sub_norm_le (1 : ℂ) a
    rw [norm_one] at h
    linarith
  have hb2 : 1 / 2 ≤ ‖1 - conj a * v‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (conj a * v)
    rw [norm_one, norm_mul, Complex.norm_conj] at h
    nlinarith [norm_nonneg a, norm_nonneg v]
  have hn1 : ‖v - 1‖ ≤ 2 := by
    calc ‖v - 1‖ ≤ ‖v‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  have hv1 : ‖v + 1‖ ≤ 2 := by
    calc ‖v + 1‖ ≤ ‖v‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  have hn2 : ‖a + conj a * v - a * conj a * (v + 1)‖ ≤ 4 * ‖a‖ := by
    calc ‖a + conj a * v - a * conj a * (v + 1)‖
        ≤ ‖a + conj a * v‖ + ‖a * conj a * (v + 1)‖ := norm_sub_le _ _
      _ ≤ (‖a‖ + ‖conj a * v‖) + ‖a * conj a * (v + 1)‖ := by
          gcongr
          exact norm_add_le _ _
      _ = ‖a‖ + ‖a‖ * ‖v‖ + ‖a‖ * ‖a‖ * ‖v + 1‖ := by
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj]
      _ ≤ 4 * ‖a‖ := by
          nlinarith [norm_nonneg a, norm_nonneg v, norm_nonneg (v + 1),
            mul_le_mul_of_nonneg_left hv (norm_nonneg a),
            mul_le_mul_of_nonneg_left hv1 (mul_nonneg (norm_nonneg a) (norm_nonneg a))]
  have hpos : 0 < ‖1 - a‖ * ‖1 - conj a * v‖ := mul_pos (by linarith) (by linarith)
  rw [key, norm_div, norm_mul, norm_mul, div_le_iff₀ hpos]
  have hprod : 1 / 4 ≤ ‖1 - a‖ * ‖1 - conj a * v‖ := by nlinarith
  calc ‖v - 1‖ * ‖a + conj a * v - a * conj a * (v + 1)‖ ≤ 2 * (4 * ‖a‖) :=
        mul_le_mul hn1 hn2 (norm_nonneg _) (by norm_num)
    _ ≤ 32 * ‖a‖ * (‖1 - a‖ * ‖1 - conj a * v‖) := by nlinarith [norm_nonneg a]

/-- `abMob aₙ → id` uniformly on the closed disc when `aₙ → 0`. -/
theorem ab_mob_near_id {a : ℕ → ℂ} (ha : Tendsto a atTop (𝓝 0)) {v : ℕ → ℂ} (hv : ∀ n, ‖v n‖ ≤ 1) :
    Tendsto (fun n => abMob (a n) (v n) - v n) atTop (𝓝 0) := by
  have hna : Tendsto (fun n => ‖a n‖) atTop (𝓝 0) := by simpa using ha.norm
  have h32 : Tendsto (fun n => 32 * ‖a n‖) atTop (𝓝 0) := by simpa using hna.const_mul 32
  refine squeeze_zero_norm' ?_ h32
  filter_upwards [hna.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn
  exact abM_norm_sub_le hn (hv n)

/-! ### Target (moved to the end of S13; statement byte-identical up to the prime) -/

/-- `abMob a` fixes `1` for `a` in the disc. -/
theorem abT_abMob_one {a : ℂ} (ha : a ∈ unitDisc) : abMob a 1 = 1 := by
  have h1 : ‖a‖ < 1 := mem_ball_zero_iff.1 ha
  have ha1 : 1 - a ≠ 0 := fun h => by
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at h1
    exact lt_irrefl _ h1
  have hc1 : 1 - conj a ≠ 0 := fun h => by
    rw [sub_eq_zero] at h
    rw [← Complex.norm_conj, ← h, norm_one] at h1
    exact lt_irrefl _ h1
  rw [abMob, mul_one]
  field_simp

/-- A null set stays null under `z ↦ 1/z̄`. -/
theorem abT_ae_conj_inv {p : ℂ → Prop} (h : ∀ᵐ z, p z) : ∀ᵐ w, p (conj w)⁻¹ :=
  Complex.conjLIE.measurePreserving.quasiMeasurePreserving.ae (p := fun ζ => p ζ⁻¹) (nx_ae_inv h)

/-- Two maps agreeing on an open set have the same complex dilatation there. -/
theorem abT_dilatation_congr {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (h : EqOn f g U) {z : ℂ}
    (hz : z ∈ U) : complexDilatation f z = complexDilatation g z := by
  have hev : f =ᶠ[𝓝 z] g := Filter.eventuallyEq_of_mem (hU.mem_nhds hz) h
  rw [complexDilatation, complexDilatation, dz, dzbar, dz, dzbar, hev.fderiv_eq]

/-- Pushing an a.e. statement forward through a quasiconformal map (Lusin's property (N)). -/
theorem abT_ae_image {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) {p : ℂ → Prop}
    (h : ∀ᵐ z ∂(volume.restrict D), p (f z)) : ∀ᵐ w ∂(volume.restrict (f '' D)), p w := by
  have hDm : MeasurableSet D := hf.1.measurableSet
  have hS : volume {z | z ∈ D ∧ ¬ p (f z)} = 0 := by
    have h1 := (ae_restrict_iff' hDm).1 h
    rw [ae_iff] at h1
    refine measure_mono_null (fun z hz => ?_) h1
    exact fun h' => hz.2 (h' hz.1)
  have hS' : volume (f '' {z | z ∈ D ∧ ¬ p (f z)}) = 0 :=
    thm9_6_cor1_null hf (fun z hz => hz.1) hS
  have h2 : ∀ᵐ w, w ∉ f '' {z | z ∈ D ∧ ¬ p (f z)} := measure_eq_zero_iff_ae_notMem.1 hS'
  filter_upwards [ae_restrict_of_ae h2,
    ae_restrict_mem (isOpen_image_of_continuousOn_injOn hf.1 hf.2.2.1.1 hf.2.2.1.2.1).measurableSet]
    with w hw hwD
  obtain ⟨z, hz, rfl⟩ := hwD
  by_contra hp
  exact hw ⟨z, ⟨hz, hp⟩, rfl⟩

/-- The sequential form of Theorem 13.8: along `tₙ → t₀` in `P`, `f(tₙ, z) → f(t₀, z)`. -/
theorem abT_seq {P : Set ℂ} {μ : ℂ → ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμ : ∀ t ∈ P, IsBeltramiCoeff (μ t) unitDisc k)
    (hcont : ∀ z ∈ unitDisc, ContinuousOn (fun t => μ t z) P) {f : ℂ → ℂ → ℂ}
    (hf : ∀ t ∈ P, IsDiscNormalizedSolution (f t) (μ t)) {t₀ : ℂ} (ht₀ : t₀ ∈ P) {u : ℕ → ℂ}
    (huP : ∀ n, u n ∈ P) (hu : Tendsto u atTop (𝓝 t₀)) {z : ℂ} (hz : z ∈ unitDisc) :
    Tendsto (fun n => f (u n) z) atTop (𝓝 (f t₀ z)) := by
  have hΔo : IsOpen unitDisc := isOpen_ball
  have h0Δ : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have h1k : 0 < 1 - k := by linarith
  set K₀ : ℝ := (1 + k) / (1 - k) with hK₀
  set f₀ : ℂ → ℂ := f t₀ with hf₀def
  obtain ⟨K₁, hf₀K⟩ := (hf t₀ ht₀).1
  have hf₀img : f₀ '' unitDisc = unitDisc := (hf t₀ ht₀).2.1
  -- the quotients `hₙ = fₙ ∘ f₀⁻¹` (piece Q)
  set h : ℕ → ℂ → ℂ := fun n => f (u n) ∘ Function.invFunOn f₀ unitDisc with hdef
  have hQ : ∀ n, ∃ H : ExtPlane → ExtPlane, IsKQC (h n) unitDisc (K₀ ^ 2) ∧
      h n '' unitDisc = unitDisc ∧ IsHomeoExtension (h n) unitDisc unitDisc H ∧
      H ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧ H (I : ExtPlane) = (I : ExtPlane) ∧
      H ((-1 : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane) ∧
      ∀ᵐ z ∂(volume.restrict unitDisc),
        ‖complexDilatation (h n) (f₀ z)‖ * (1 - k) ≤ ‖μ (u n) z - μ t₀ z‖ := by
    intro n
    obtain ⟨h1, h2, ⟨H, hH, hH1, hHI, hHm⟩, h4⟩ :=
      ab_quotient hk₀ hk (hμ (u n) (huP n)) (hμ t₀ ht₀) (hf (u n) (huP n)) (hf t₀ ht₀)
    exact ⟨H, h1, h2, hH, hH1, hHI, hHm, h4⟩
  choose H hhK hhimg hH hH1 hHI hHm hbd using hQ
  -- the centres `aₙ = hₙ 0` and the normalized maps (piece N)
  set a : ℕ → ℂ := fun n => h n 0 with hadef
  have haΔ : ∀ n, a n ∈ unitDisc := fun n => by
    rw [← hhimg n]
    exact mem_image_of_mem _ h0Δ
  set Gd : ℕ → ℂ → ℂ := fun n z => abMob (h n 0) (h n z) with hGddef
  have hN : ∀ n, ∃ G : ExtPlane → ExtPlane, IsKQC (Gd n) unitDisc (K₀ ^ 2) ∧
      Gd n '' unitDisc = unitDisc ∧ Gd n 0 = 0 ∧ IsHomeoExtension (Gd n) unitDisc unitDisc G ∧
      (∀ z : ℂ, ‖z‖ = 1 → G (z : ExtPlane) = OnePoint.map (abMob (a n)) (H n (z : ExtPlane))) ∧
      ∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation (Gd n) z = complexDilatation (h n) z := by
    intro n
    obtain ⟨h1, h2, h3, ⟨G, hG, hGb⟩, h5⟩ := ab_normalize (hhK n) (hhimg n) (hH n)
    exact ⟨G, h1, h2, h3, hG, hGb, h5⟩
  choose G hGdK hGdimg hGd0 hG hGb hGdμ using hN
  -- the reflected maps (piece R)
  have hR := fun n => ab_reflect (hGdK n) (hGdimg n) (hGd0 n) (hG n)
  choose g hgK hgs hgeq hgb hgsym hgμ using hR
  -- boundary values of `gₙ`
  have hgbd : ∀ n (w : ℂ), ‖w‖ = 1 → H n (w : ExtPlane) = (w : ExtPlane) →
      g n w = abMob (a n) w := by
    intro n w hw hHw
    apply OnePoint.coe_injective
    rw [hgb n w hw, hGb n w hw, hHw]
    rfl
  have hg1 : ∀ n, g n 1 = 1 := fun n => by
    rw [hgbd n 1 (by simp) (hH1 n), abT_abMob_one (haΔ n)]
  have hg0 : ∀ n, g n 0 = 0 := fun n => (hgeq n h0Δ).trans (hGd0 n)
  have hgΔ : ∀ n, g n '' unitDisc = unitDisc := fun n => (image_congr (hgeq n)).trans (hGdimg n)
  -- the dilatations of `hₙ` tend to `0` a.e. in `Δ` (piece Q's bound, continuity in `t`, property (N))
  have hgood : ∀ᵐ z ∂(volume.restrict unitDisc),
      Tendsto (fun n => complexDilatation (h n) (f₀ z)) atTop (𝓝 0) := by
    filter_upwards [ae_all_iff.2 hbd, ae_restrict_mem hΔo.measurableSet] with z hzb hzΔ
    have hc : Tendsto (fun n => μ (u n) z) atTop (𝓝 (μ t₀ z)) :=
      ((hcont z hzΔ) t₀ ht₀).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hu, Eventually.of_forall huP⟩)
    have hc' : Tendsto (fun n => ‖μ (u n) z - μ t₀ z‖ / (1 - k)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => μ (u n) z - μ t₀ z) atTop (𝓝 0) := by
        simpa using hc.sub_const (μ t₀ z)
      simpa using h1.norm.div_const (1 - k)
    refine squeeze_zero_norm (fun n => ?_) hc'
    rw [le_div_iff₀ h1k]
    exact hzb n
  have hin : ∀ᵐ w ∂(volume.restrict unitDisc),
      Tendsto (fun n => complexDilatation (h n) w) atTop (𝓝 0) := by
    have h1 := abT_ae_image (p := fun w => Tendsto (fun n => complexDilatation (h n) w) atTop (𝓝 0))
      hf₀K hgood
    rwa [hf₀img] at h1
  have hGdin : ∀ᵐ w, w ∈ unitDisc → Tendsto (fun n => complexDilatation (Gd n) w) atTop (𝓝 0) := by
    have h1 := (ae_restrict_iff' hΔo.measurableSet).1 (hin.and (ae_all_iff.2 hGdμ))
    filter_upwards [h1] with w hw hwΔ
    obtain ⟨ht, heq⟩ := hw hwΔ
    exact ht.congr fun n => (heq n).symm
  have hout := abT_ae_conj_inv hGdin
  have hsph : ∀ᵐ w : ℂ, ‖w‖ ≠ 1 := by
    have h1 : volume (sphere (0 : ℂ) 1) = 0 := Measure.addHaar_sphere volume 0 1
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1] with w hw
    simpa [mem_sphere_zero_iff_norm] using hw
  have hμL : ∀ᵐ w, Tendsto (fun n => complexDilatation (g n) w) atTop (𝓝 0) := by
    filter_upwards [hGdin, hout, hsph, ae_all_iff.2 hgμ] with w hw1 hw2 hw3 hw4
    rcases lt_trichotomy ‖w‖ 1 with hlt | heq | hgt
    · have hwΔ : w ∈ unitDisc := mem_ball_zero_iff.2 hlt
      exact (hw1 hwΔ).congr fun n => (abT_dilatation_congr hΔo (hgeq n) hwΔ).symm
    · exact absurd heq hw3
    · have hwi : (conj w)⁻¹ ∈ unitDisc := by
        refine mem_ball_zero_iff.2 ?_
        rw [norm_inv, Complex.norm_conj]
        exact inv_lt_one_of_one_lt₀ hgt
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h2 := (hw2 hwi).norm
      rw [norm_zero] at h2
      exact h2.congr fun n => (hw4 n hgt).symm
  -- the symmetric normalized maps tend to the identity (piece L)
  have hL := ab_tendsto_id hgK hgs hgΔ hg0 hg1 hgsym hμL
  -- so the Möbius normalizations tend to the identity (piece M)
  have hgI : ∀ n, g n I = abMob (a n) I := fun n => hgbd n I (by simp) (hHI n)
  have hgm : ∀ n, g n (-1) = abMob (a n) (-1) := fun n => hgbd n (-1) (by simp) (hHm n)
  have ha0 : Tendsto a atTop (𝓝 0) := by
    refine ab_mob_tendsto haΔ ?_ ?_
    · exact (hL I (by simp)).congr fun n => hgI n
    · exact (hL (-1) (by norm_num)).congr fun n => hgm n
  -- conclusion: `fₙ z = hₙ (f₀ z) → f₀ z`
  have hw₀ : f₀ z ∈ unitDisc := by
    rw [← hf₀img]
    exact mem_image_of_mem _ hz
  have hleft : Function.invFunOn f₀ unitDisc (f₀ z) = z := hf₀K.2.2.1.2.1.leftInvOn_invFunOn hz
  have hfz : ∀ n, f (u n) z = h n (f₀ z) := fun n => by
    simp only [hdef, Function.comp_apply, hleft]
  have hhw : ∀ n, ‖h n (f₀ z)‖ ≤ 1 := fun n => by
    have : h n (f₀ z) ∈ unitDisc := by
      rw [← hhimg n]
      exact mem_image_of_mem _ hw₀
    exact (mem_ball_zero_iff.1 this).le
  have hconv : Tendsto (fun n => abMob (a n) (h n (f₀ z))) atTop (𝓝 (f₀ z)) :=
    (hL (f₀ z) (by linarith [mem_ball_zero_iff.1 hw₀])).congr fun n => hgeq n hw₀
  have hnear := ab_mob_near_id ha0 hhw
  have hlim : Tendsto (fun n => h n (f₀ z)) atTop (𝓝 (f₀ z)) := by
    have h1 := hconv.sub hnear
    rw [sub_zero] at h1
    exact h1.congr fun n => by ring
  exact hlim.congr fun n => (hfz n).symm

/-- **Theorem 13.8** (Ahlfors–Bers, continuous dependence).  Let `μ(z, t)` be, for every `t` in a
domain `P`, measurable in `z ∈ Δ` with `‖μ(·, t)‖_∞ ≤ k < 1`, and continuous in `t` for every
fixed `z`.  Then the quasiconformal self-maps `f(·, t)` of `Δ` with complex characteristic
`μ(·, t)` fixing `1, i, -1` depend continuously on `t`.

Proved (2026-09-24; moved here from §13.8 because it uses Theorems 10.1/10.2): for `tₙ → t₀` the quotients
`hₙ = f(·,tₙ) ∘ f(·,t₀)⁻¹` have dilatations `→ 0` a.e. (`ab_quotient`); normalized at `0` by a disc automorphism
(`ab_normalize`) and reflected in the unit circle (`ab_reflect`) they become symmetric q.c. maps of `ℂ`, which
Grötzsch's theorem keeps uniformly bounded on `B(0,2)` (`ab_lower_bound`); every limit is holomorphic
(`ab_limit_holomorphic`) and hence the identity (`ab_tendsto_id`); the automorphisms tend to the identity
(`ab_mob_tendsto`, `ab_mob_near_id`).  (The book's "z + Tω" argument does not cover the disc normalization.) -/
theorem thm13_8_ahlfors_bers_continuous {P : Set ℂ} (hP : IsOpen P) {μ : ℂ → ℂ → ℂ} {k : ℝ}
    (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : ∀ t ∈ P, IsBeltramiCoeff (μ t) unitDisc k)
    (hcont : ∀ z ∈ unitDisc, ContinuousOn (fun t => μ t z) P) {f : ℂ → ℂ → ℂ}
    (hf : ∀ t ∈ P, IsDiscNormalizedSolution (f t) (μ t)) :
    ∀ z ∈ unitDisc, ContinuousOn (fun t => f t z) P := by
  intro z hz t₀ ht₀
  rw [ContinuousWithinAt, Filter.tendsto_iff_seq_tendsto]
  intro x hx
  obtain ⟨hx1, hx2⟩ := tendsto_nhdsWithin_iff.1 hx
  classical
  set x' : ℕ → ℂ := fun n => if x n ∈ P then x n else t₀ with hx'def
  have hx'P : ∀ n, x' n ∈ P := fun n => by
    by_cases h : x n ∈ P
    · simp only [hx'def, h, ↓reduceIte]
    · simp only [hx'def, h, ↓reduceIte]
      exact ht₀
  have hxx' : ∀ᶠ n in atTop, x' n = x n := hx2.mono fun n hn => by simp only [hx'def, hn, ↓reduceIte]
  have hx'1 : Tendsto x' atTop (𝓝 t₀) := hx1.congr' (hxx'.mono fun n hn => hn.symm)
  have h1 := abT_seq hk₀ hk hμ hcont hf ht₀ hx'P hx'1 hz
  exact h1.congr' (hxx'.mono fun n hn => by simp only [Function.comp_apply, hn])

/-! ## §13.8 (moved here): Theorem 13.8, holomorphic dependence on parameters

Development for `thm13_8_ahlfors_bers_holomorphic` (leader -a7 / session "worker", 2026-09-24): the first
variation of normalized plane solutions and Ahlfors' variational proof.  Helpers are prefixed `ah`. -/

/-- The kernel of the first variation of normalized solutions, `w(w-1)/(ζ(ζ-1)(ζ-w))`. -/
def ahKer (w ζ : ℂ) : ℂ := w * (w - 1) / (ζ * (ζ - 1) * (ζ - w))

/-- The first variation `V[ν](w) = -(1/π) ∫ ν(ζ) w(w-1)/(ζ(ζ-1)(ζ-w)) dζ`. -/
def ahVar (ν : ℂ → ℂ) (w : ℂ) : ℂ := -(1 / π : ℂ) * ∫ ζ, ν ζ * ahKer w ζ

/-- The complex dilatation of `f₁ ∘ f₀⁻¹` at `w = f₀ z`:
`(μ₁ - μ₀)/(1 - conj μ₀ · μ₁) · ∂_z f₀ / conj (∂_z f₀)` evaluated at `z = f₀⁻¹ w`. -/
def ahQuot (μ₁ μ₀ f₀ : ℂ → ℂ) (w : ℂ) : ℂ :=
  (μ₁ (Function.invFunOn f₀ univ w) - μ₀ (Function.invFunOn f₀ univ w)) /
      (1 - conj (μ₀ (Function.invFunOn f₀ univ w)) * μ₁ (Function.invFunOn f₀ univ w)) *
    (dz f₀ (Function.invFunOn f₀ univ w) / conj (dz f₀ (Function.invFunOn f₀ univ w)))

/-! ### Piece K — the kernel and the functional `V` -/

/-- The kernel `ζ ↦ K_w(ζ)` is measurable. -/
theorem ahK_measurable (w : ℂ) : Measurable (ahKer w) := by
  unfold ahKer
  fun_prop

/-- `K_0 = 0`. -/
theorem ahK_ker_zero (ζ : ℂ) : ahKer 0 ζ = 0 := by
  simp [ahKer]

/-- Off the four points `0, 1, a, w` the difference of two kernels factors as
`K_a - K_w = (a - w) (1/((ζ - a)(ζ - w)) - 1/(ζ (ζ - 1)))`. -/
theorem ahK_sub_eq {a w ζ : ℂ} (h0 : ζ ≠ 0) (h1 : ζ ≠ 1) (ha : ζ ≠ a) (hw : ζ ≠ w) :
    ahKer a ζ - ahKer w ζ =
      (a - w) * (1 / ((ζ - a) * (ζ - w)) - 1 / ((ζ - 0) * (ζ - 1))) := by
  have h1' : ζ - 1 ≠ 0 := sub_ne_zero.2 h1
  have ha' : ζ - a ≠ 0 := sub_ne_zero.2 ha
  have hw' : ζ - w ≠ 0 := sub_ne_zero.2 hw
  rw [sub_zero]
  unfold ahKer
  field_simp
  ring

/-- Pointwise `enorm` bound for the difference of two kernels off the four points `0, 1, a, w`:
`|K_a - K_w| ≤ |a - w| (1/(|ζ - a| |ζ - w|) + 1/(|ζ| |ζ - 1|))`. -/
theorem ahK_enorm_sub_le {a w ζ : ℂ} (h0 : ζ ≠ 0) (h1 : ζ ≠ 1) (ha : ζ ≠ a) (hw : ζ ≠ w) :
    ‖ahKer a ζ - ahKer w ζ‖ₑ ≤
      ‖a - w‖ₑ * (‖ζ - a‖ₑ⁻¹ * ‖ζ - w‖ₑ⁻¹ + ‖ζ - 0‖ₑ⁻¹ * ‖ζ - 1‖ₑ⁻¹) := by
  have h0' : ζ - 0 ≠ 0 := by rwa [sub_zero]
  have h1' : ζ - 1 ≠ 0 := sub_ne_zero.2 h1
  have ha' : ζ - a ≠ 0 := sub_ne_zero.2 ha
  have hw' : ζ - w ≠ 0 := sub_ne_zero.2 hw
  rw [ahK_sub_eq h0 h1 ha hw, enorm_mul]
  gcongr
  refine enorm_sub_le.trans (le_of_eq ?_)
  rw [one_div, one_div, mul_inv, mul_inv, enorm_mul, enorm_mul, enorm_inv ha', enorm_inv hw',
    enorm_inv h0', enorm_inv h1']

/-- Far from the four points: `|K_a(ζ) - K_w(ζ)| ≤ 32 R |a - w|/|ζ|³` when `|a|, |w| ≤ R`,
`1 ≤ R` and `2R < |ζ|`. -/
theorem ahK_norm_sub_le_far {R : ℝ} (hR : 1 ≤ R) {a w ζ : ℂ} (ha : ‖a‖ ≤ R) (hw : ‖w‖ ≤ R)
    (hζ : 2 * R < ‖ζ‖) :
    ‖ahKer a ζ - ahKer w ζ‖ ≤ 32 * R * ‖a - w‖ / ‖ζ‖ ^ 3 := by
  have hR0 : 0 ≤ R := by linarith
  have hn : 0 < ‖ζ‖ := by linarith
  have hn' : ‖ζ‖ ≠ 0 := hn.ne'
  have hd1 : ‖ζ‖ / 2 ≤ ‖ζ - 1‖ := by
    have := norm_sub_norm_le ζ 1
    rw [norm_one] at this
    linarith
  have hda : ‖ζ‖ / 2 ≤ ‖ζ - a‖ := by
    have := norm_sub_norm_le ζ a
    linarith
  have hdw : ‖ζ‖ / 2 ≤ ‖ζ - w‖ := by
    have := norm_sub_norm_le ζ w
    linarith
  have hζ0 : ζ ≠ 0 := norm_pos_iff.1 hn
  have hζ1 : ζ - 1 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hd1
    linarith
  have hζa : ζ - a ≠ 0 := by
    intro h
    rw [h, norm_zero] at hda
    linarith
  have hζw : ζ - w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdw
    linarith
  have key : ahKer a ζ - ahKer w ζ =
      (a - w) * ((a + w - 1) * ζ - a * w) / (ζ * (ζ - 1) * (ζ - a) * (ζ - w)) := by
    unfold ahKer
    field_simp
    ring
  have h3 : ‖a + w - 1‖ ≤ 3 * R := by
    have e1 := norm_sub_le (a + w) 1
    have e2 := norm_add_le a w
    rw [norm_one] at e1
    linarith
  have hnum : ‖(a + w - 1) * ζ - a * w‖ ≤ 4 * R * ‖ζ‖ := by
    have e1 := norm_sub_le ((a + w - 1) * ζ) (a * w)
    rw [norm_mul, norm_mul] at e1
    have e2 : ‖a + w - 1‖ * ‖ζ‖ ≤ 3 * R * ‖ζ‖ := mul_le_mul_of_nonneg_right h3 hn.le
    have e3 : ‖a‖ * ‖w‖ ≤ R * R := mul_le_mul ha hw (norm_nonneg w) hR0
    have e4 : R * R ≤ R * ‖ζ‖ := mul_le_mul_of_nonneg_left (by linarith) hR0
    linarith
  have hden : ‖ζ‖ ^ 4 / 8 ≤ ‖ζ‖ * ‖ζ - 1‖ * ‖ζ - a‖ * ‖ζ - w‖ := by
    calc ‖ζ‖ ^ 4 / 8 = ‖ζ‖ * (‖ζ‖ / 2) * (‖ζ‖ / 2) * (‖ζ‖ / 2) := by ring
      _ ≤ ‖ζ‖ * ‖ζ - 1‖ * ‖ζ - a‖ * ‖ζ - w‖ := by gcongr
  rw [key, norm_div, norm_mul, norm_mul, norm_mul, norm_mul]
  calc ‖a - w‖ * ‖(a + w - 1) * ζ - a * w‖ / (‖ζ‖ * ‖ζ - 1‖ * ‖ζ - a‖ * ‖ζ - w‖)
      ≤ ‖a - w‖ * (4 * R * ‖ζ‖) / (‖ζ‖ ^ 4 / 8) :=
        div_le_div₀ (mul_nonneg (norm_nonneg _) (mul_nonneg (by linarith) hn.le))
          (mul_le_mul_of_nonneg_left hnum (norm_nonneg _)) (by positivity) hden
    _ = 32 * R * ‖a - w‖ / ‖ζ‖ ^ 3 := by
        field_simp
        ring

/-- For `0 < ‖x‖ ≤ r`: `‖x‖⁻¹ ≤ r^{1/4} ‖x‖^{-5/4}` in `ℝ≥0∞`. -/
theorem ahK_enorm_inv_le {x : ℂ} {r : ℝ} (hx : x ≠ 0) (hxr : ‖x‖ ≤ r) :
    ‖x‖ₑ⁻¹ ≤ ENNReal.ofReal (r ^ (1 / 4 : ℝ)) * ‖x‖ₑ ^ (-(5 / 4 : ℝ)) := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [← ofReal_norm, ← ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_rpow_of_pos hpos,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (hpos.le.trans hxr) _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsplit : ‖x‖⁻¹ = ‖x‖ ^ (1 / 4 : ℝ) * ‖x‖ ^ (-(5 / 4 : ℝ)) := by
    rw [← Real.rpow_add hpos]
    norm_num [Real.rpow_neg_one]
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hpos.le hxr (by norm_num))
    (Real.rpow_nonneg hpos.le _)

/-- The two-singularity estimate of §11.1 at the exponent `q = 5/4`:
`∬ dA/(|ζ - z₁|^{5/4} |ζ - z₂|^{5/4}) ≤ C |z₁ - z₂|^{-1/2}`. -/
theorem ahK_two_singularities :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z₁ z₂ : ℂ, z₁ ≠ z₂ →
      ∫⁻ ζ, ‖ζ - z₁‖ₑ ^ (-(5 / 4 : ℝ)) * ‖ζ - z₂‖ₑ ^ (-(5 / 4 : ℝ)) ≤
        ENNReal.ofReal (C * (√‖z₁ - z₂‖)⁻¹) := by
  refine ⟨2 * (2 * π / (2 - 5 / 4) * 2 ^ (2 * (5 / 4 : ℝ) - 2))
      + 2 * π / (2 * (5 / 4 : ℝ) - 2) * 4 ^ (3 * (5 / 4 : ℝ) - 2), ?_, fun z₁ z₂ hne => ?_⟩
  · norm_num
    positivity
  refine (lintegral_two_singularities_le (q := 5 / 4) (by norm_num) (by norm_num) hne).trans
    (le_of_eq ?_)
  have hd : 0 ≤ ‖z₁ - z₂‖ := norm_nonneg _
  have hexp : ‖z₁ - z₂‖ ^ (2 - 2 * (5 / 4 : ℝ)) = (√‖z₁ - z₂‖)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hd]
    norm_num
  rw [hexp]

/-- Two singularities of order one in a disc: for `‖z₁‖, ‖z₂‖ ≤ ρ`, `z₁ ≠ z₂`,
`∬_{|ζ| ≤ ρ} dA/(|ζ - z₁| |ζ - z₂|) ≤ C |z₁ - z₂|^{-1/2}`. -/
theorem ahK_lintegral_closedBall_two_le {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z₁ z₂ : ℂ, ‖z₁‖ ≤ ρ → ‖z₂‖ ≤ ρ → z₁ ≠ z₂ →
      ∫⁻ ζ in closedBall (0 : ℂ) ρ, ‖ζ - z₁‖ₑ⁻¹ * ‖ζ - z₂‖ₑ⁻¹ ≤
        ENNReal.ofReal (C * (√‖z₁ - z₂‖)⁻¹) := by
  obtain ⟨Cq, hCq0, hCq⟩ := ahK_two_singularities
  have hm0 : 0 ≤ (2 * ρ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by linarith) _
  refine ⟨(2 * ρ) ^ (1 / 4 : ℝ) * (2 * ρ) ^ (1 / 4 : ℝ) * Cq, by positivity,
    fun z₁ z₂ h₁ h₂ hne => ?_⟩
  have hpt : ∀ᵐ ζ ∂(volume.restrict (closedBall (0 : ℂ) ρ)),
      ‖ζ - z₁‖ₑ⁻¹ * ‖ζ - z₂‖ₑ⁻¹ ≤
        ENNReal.ofReal ((2 * ρ) ^ (1 / 4 : ℝ) * (2 * ρ) ^ (1 / 4 : ℝ)) *
          (‖ζ - z₁‖ₑ ^ (-(5 / 4 : ℝ)) * ‖ζ - z₂‖ₑ ^ (-(5 / 4 : ℝ))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_closedBall,
      ae_restrict_of_ae (ae_ne z₁), ae_restrict_of_ae (ae_ne z₂)] with ζ hζ hζ₁ hζ₂
    have hζn : ‖ζ‖ ≤ ρ := by simpa [mem_closedBall, dist_zero_right] using hζ
    have hb₁ : ‖ζ - z₁‖ ≤ 2 * ρ := (norm_sub_le _ _).trans (by linarith)
    have hb₂ : ‖ζ - z₂‖ ≤ 2 * ρ := (norm_sub_le _ _).trans (by linarith)
    rw [ENNReal.ofReal_mul hm0]
    calc ‖ζ - z₁‖ₑ⁻¹ * ‖ζ - z₂‖ₑ⁻¹
        ≤ (ENNReal.ofReal ((2 * ρ) ^ (1 / 4 : ℝ)) * ‖ζ - z₁‖ₑ ^ (-(5 / 4 : ℝ))) *
            (ENNReal.ofReal ((2 * ρ) ^ (1 / 4 : ℝ)) * ‖ζ - z₂‖ₑ ^ (-(5 / 4 : ℝ))) :=
          mul_le_mul' (ahK_enorm_inv_le (sub_ne_zero.2 hζ₁) hb₁)
            (ahK_enorm_inv_le (sub_ne_zero.2 hζ₂) hb₂)
      _ = _ := by ring
  calc ∫⁻ ζ in closedBall (0 : ℂ) ρ, ‖ζ - z₁‖ₑ⁻¹ * ‖ζ - z₂‖ₑ⁻¹
      ≤ ∫⁻ ζ in closedBall (0 : ℂ) ρ,
          ENNReal.ofReal ((2 * ρ) ^ (1 / 4 : ℝ) * (2 * ρ) ^ (1 / 4 : ℝ)) *
            (‖ζ - z₁‖ₑ ^ (-(5 / 4 : ℝ)) * ‖ζ - z₂‖ₑ ^ (-(5 / 4 : ℝ))) := lintegral_mono_ae hpt
    _ ≤ ∫⁻ ζ, ENNReal.ofReal ((2 * ρ) ^ (1 / 4 : ℝ) * (2 * ρ) ^ (1 / 4 : ℝ)) *
            (‖ζ - z₁‖ₑ ^ (-(5 / 4 : ℝ)) * ‖ζ - z₂‖ₑ ^ (-(5 / 4 : ℝ))) :=
          setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal ((2 * ρ) ^ (1 / 4 : ℝ) * (2 * ρ) ^ (1 / 4 : ℝ)) *
          ∫⁻ ζ, ‖ζ - z₁‖ₑ ^ (-(5 / 4 : ℝ)) * ‖ζ - z₂‖ₑ ^ (-(5 / 4 : ℝ)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((2 * ρ) ^ (1 / 4 : ℝ) * (2 * ρ) ^ (1 / 4 : ℝ)) *
          ENNReal.ofReal (Cq * (√‖z₁ - z₂‖)⁻¹) := by
          gcongr
          exact hCq z₁ z₂ hne
    _ = ENNReal.ofReal ((2 * ρ) ^ (1 / 4 : ℝ) * (2 * ρ) ^ (1 / 4 : ℝ) * Cq *
          (√‖z₁ - z₂‖)⁻¹) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring

/-- A function bounded by `C/|ζ|³` outside `B̄(0, ρ)` has `∬_{|ζ| > ρ} |f| ≤ 2π C/ρ`. -/
theorem ahK_lintegral_compl_le {f : ℂ → ℂ} {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hf : ∀ ζ : ℂ, ρ < ‖ζ‖ → ‖f ζ‖ ≤ C / ‖ζ‖ ^ 3) :
    ∫⁻ ζ in (closedBall (0 : ℂ) ρ)ᶜ, ‖f ζ‖ₑ ≤ ENNReal.ofReal (2 * π * C / ρ) := by
  have hset : (closedBall (0 : ℂ) ρ)ᶜ = {ζ : ℂ | ρ < ‖ζ‖} := by
    ext ζ
    simp [mem_closedBall, dist_zero_right, not_le]
  have hmeas : MeasurableSet {ζ : ℂ | ρ < ‖ζ‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  rw [hset]
  calc ∫⁻ ζ in {ζ : ℂ | ρ < ‖ζ‖}, ‖f ζ‖ₑ
      ≤ ∫⁻ ζ in {ζ : ℂ | ρ < ‖ζ‖}, ENNReal.ofReal C * ‖ζ‖ₑ ^ (-(3 : ℝ)) := by
        refine setLIntegral_mono' hmeas (fun ζ hζ => ?_)
        have hζ' : ρ < ‖ζ‖ := hζ
        have hn : 0 < ‖ζ‖ := hρ.trans hζ'
        rw [← ofReal_norm (f ζ), ← ofReal_norm ζ, ENNReal.ofReal_rpow_of_pos hn,
          ← ENNReal.ofReal_mul hC]
        refine ENNReal.ofReal_le_ofReal ((hf ζ hζ').trans (le_of_eq ?_))
        rw [Real.rpow_neg hn.le, div_eq_mul_inv]
        norm_cast
    _ = ENNReal.ofReal C * ∫⁻ ζ in {ζ : ℂ | ρ < ‖ζ‖}, ‖ζ‖ₑ ^ (-(3 : ℝ)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal C *
          (ENNReal.ofReal (2 * π) * ENNReal.ofReal (-ρ ^ (2 - 3 : ℝ) / (2 - 3))) := by
        rw [lintegral_compl_ball_enorm_rpow_neg (a := 3) (by norm_num) hρ]
    _ = ENNReal.ofReal (2 * π * C / ρ) := by
        have h3 : -ρ ^ (2 - 3 : ℝ) / (2 - 3) = ρ⁻¹ := by
          norm_num [Real.rpow_neg_one]
        rw [h3, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC]
        congr 1
        rw [div_eq_mul_inv]
        ring

/-- **The `L¹` estimate for the difference of two kernels.**  For `‖a‖, ‖w‖ ≤ R`, `1 ≤ R`,
`a ≠ w`: `∬ |K_a - K_w| ≤ C √|a - w| + (C + 32π) |a - w|`. -/
theorem ahK_lintegral_sub_le {R : ℝ} (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a w : ℂ, ‖a‖ ≤ R → ‖w‖ ≤ R → a ≠ w →
      ∫⁻ ζ, ‖ahKer a ζ - ahKer w ζ‖ₑ ≤
        ENNReal.ofReal (C * √‖a - w‖ + (C + 32 * π) * ‖a - w‖) := by
  have hR0 : 0 < R := by linarith
  obtain ⟨C, hC0, hC⟩ := ahK_lintegral_closedBall_two_le (ρ := 2 * R) (by linarith)
  refine ⟨C, hC0, fun a w ha hw hne => ?_⟩
  have hd0 : 0 ≤ ‖a - w‖ := norm_nonneg _
  -- inside the disc `|ζ| ≤ 2R`
  have hin : ∫⁻ ζ in closedBall (0 : ℂ) (2 * R), ‖ahKer a ζ - ahKer w ζ‖ₑ ≤
      ENNReal.ofReal (C * √‖a - w‖ + C * ‖a - w‖) := by
    have hpt : ∀ᵐ ζ ∂(volume.restrict (closedBall (0 : ℂ) (2 * R))),
        ‖ahKer a ζ - ahKer w ζ‖ₑ ≤
          ‖a - w‖ₑ * (‖ζ - a‖ₑ⁻¹ * ‖ζ - w‖ₑ⁻¹ + ‖ζ - 0‖ₑ⁻¹ * ‖ζ - 1‖ₑ⁻¹) := by
      filter_upwards [ae_restrict_of_ae (ae_ne (0 : ℂ)), ae_restrict_of_ae (ae_ne (1 : ℂ)),
        ae_restrict_of_ae (ae_ne a), ae_restrict_of_ae (ae_ne w)] with ζ h0 h1 ha' hw'
      exact ahK_enorm_sub_le h0 h1 ha' hw'
    have hm₁ : Measurable fun ζ : ℂ => ‖ζ - a‖ₑ⁻¹ * ‖ζ - w‖ₑ⁻¹ :=
      ((measurable_id.sub_const a).enorm.inv).mul ((measurable_id.sub_const w).enorm.inv)
    have i₁ := hC a w (by linarith) (by linarith) hne
    have i₂ := hC 0 1 (by simp; linarith) (by simp; linarith) zero_ne_one
    have h01 : ‖(0 : ℂ) - 1‖ = 1 := by simp
    rw [h01, Real.sqrt_one, inv_one, mul_one] at i₂
    have hs : ‖a - w‖ * (√‖a - w‖)⁻¹ = √‖a - w‖ := by
      rw [← div_eq_mul_inv, Real.div_sqrt]
    calc ∫⁻ ζ in closedBall (0 : ℂ) (2 * R), ‖ahKer a ζ - ahKer w ζ‖ₑ
        ≤ ∫⁻ ζ in closedBall (0 : ℂ) (2 * R),
            ‖a - w‖ₑ * (‖ζ - a‖ₑ⁻¹ * ‖ζ - w‖ₑ⁻¹ + ‖ζ - 0‖ₑ⁻¹ * ‖ζ - 1‖ₑ⁻¹) :=
          lintegral_mono_ae hpt
      _ = ‖a - w‖ₑ * ((∫⁻ ζ in closedBall (0 : ℂ) (2 * R), ‖ζ - a‖ₑ⁻¹ * ‖ζ - w‖ₑ⁻¹) +
            ∫⁻ ζ in closedBall (0 : ℂ) (2 * R), ‖ζ - 0‖ₑ⁻¹ * ‖ζ - 1‖ₑ⁻¹) := by
          rw [lintegral_const_mul' _ _ enorm_ne_top, lintegral_add_left hm₁]
      _ ≤ ‖a - w‖ₑ * (ENNReal.ofReal (C * (√‖a - w‖)⁻¹) + ENNReal.ofReal C) := by
          gcongr
      _ = ENNReal.ofReal (C * √‖a - w‖ + C * ‖a - w‖) := by
          rw [← ofReal_norm, ← ENNReal.ofReal_add (by positivity) hC0,
            ← ENNReal.ofReal_mul hd0]
          congr 1
          linear_combination C * hs
  -- outside the disc
  have hout : ∫⁻ ζ in (closedBall (0 : ℂ) (2 * R))ᶜ, ‖ahKer a ζ - ahKer w ζ‖ₑ ≤
      ENNReal.ofReal (32 * π * ‖a - w‖) := by
    refine (ahK_lintegral_compl_le (f := fun ζ => ahKer a ζ - ahKer w ζ)
      (C := 32 * R * ‖a - w‖) (mul_nonneg (by linarith) hd0) (by linarith)
      (fun ζ hζ => ahK_norm_sub_le_far hR ha hw hζ)).trans (le_of_eq ?_)
    congr 1
    field_simp
  rw [← lintegral_add_compl _
    (measurableSet_closedBall : MeasurableSet (closedBall (0 : ℂ) (2 * R)))]
  calc _ ≤ ENNReal.ofReal (C * √‖a - w‖ + C * ‖a - w‖) + ENNReal.ofReal (32 * π * ‖a - w‖) :=
        add_le_add hin hout
    _ = ENNReal.ofReal (C * √‖a - w‖ + (C + 32 * π) * ‖a - w‖) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- The kernel is integrable (singularities of order `1` at `0, 1, w`, decay `|ζ|⁻³`). -/
theorem ah_ker_integrable (w : ℂ) : Integrable (ahKer w) := by
  rcases eq_or_ne w 0 with rfl | hw0
  · have h0 : ahKer 0 = fun _ => 0 := funext ahK_ker_zero
    rw [h0]
    exact integrable_zero _ _ _
  obtain ⟨C, -, hC⟩ := ahK_lintegral_sub_le (R := ‖w‖ + 1) (by linarith [norm_nonneg w])
  have h := hC w 0 (by linarith) (by simp; linarith [norm_nonneg w]) hw0
  simp only [ahK_ker_zero, sub_zero] at h
  exact ⟨(ahK_measurable w).aestronglyMeasurable, lt_of_le_of_lt h ENNReal.ofReal_lt_top⟩

/-- The kernel depends continuously on `w` in `L¹`. -/
theorem ah_ker_continuous (w : ℂ) :
    ∀ η > 0, ∃ δ > 0, ∀ a : ℂ, ‖a - w‖ < δ → ∫ ζ, ‖ahKer a ζ - ahKer w ζ‖ < η := by
  intro η hη
  obtain ⟨C, hC0, hC⟩ := ahK_lintegral_sub_le (R := ‖w‖ + 1) (by linarith [norm_nonneg w])
  have hcont : Continuous fun d : ℝ => C * √d + (C + 32 * π) * d :=
    (continuous_const.mul Real.continuous_sqrt).add (continuous_const.mul continuous_id)
  obtain ⟨δ, hδ, hδη⟩ := Metric.continuous_iff.1 hcont 0 η hη
  refine ⟨min δ 1, lt_min hδ one_pos, fun a ha => ?_⟩
  rcases eq_or_ne a w with rfl | hne
  · simpa using hη
  have ha1 : ‖a - w‖ < 1 := lt_of_lt_of_le ha (min_le_right _ _)
  have haR : ‖a‖ ≤ ‖w‖ + 1 := by
    have := norm_sub_norm_le a w
    linarith
  have hb := hC a w haR (by linarith) hne
  have hmeas : AEStronglyMeasurable (fun ζ => ahKer a ζ - ahKer w ζ) volume :=
    ((ahK_measurable a).sub (ahK_measurable w)).aestronglyMeasurable
  rw [integral_norm_eq_lintegral_enorm hmeas]
  have hδ' := hδη ‖a - w‖ (by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    exact lt_of_lt_of_le ha (min_le_left _ _))
  simp only [Real.sqrt_zero, mul_zero, add_zero, Real.dist_eq, sub_zero] at hδ'
  have hnn : 0 ≤ C * √‖a - w‖ + (C + 32 * π) * ‖a - w‖ := by positivity
  calc (∫⁻ ζ, ‖ahKer a ζ - ahKer w ζ‖ₑ).toReal
      ≤ C * √‖a - w‖ + (C + 32 * π) * ‖a - w‖ := ENNReal.toReal_le_of_le_ofReal hnn hb
    _ < η := lt_of_abs_lt hδ'

/-- `|V[ν](w)| ≤ (1/π) ‖K_w‖₁ ε` when `|ν| ≤ ε` a.e. -/
theorem ah_var_bound (w : ℂ) {ν : ℂ → ℂ} {ε : ℝ} (hν : IsBeltramiCoeff ν univ ε) :
    ‖ahVar ν w‖ ≤ (1 / π) * (∫ ζ, ‖ahKer w ζ‖) * ε := by
  have hb : ∀ᵐ ζ ∂volume, ‖ν ζ‖ ≤ ε := by
    have h := hν.2
    rwa [Measure.restrict_univ] at h
  have hint : Integrable (fun ζ => ε * ‖ahKer w ζ‖) := (ah_ker_integrable w).norm.const_mul ε
  have h1 : ‖∫ ζ, ν ζ * ahKer w ζ‖ ≤ ∫ ζ, ε * ‖ahKer w ζ‖ := by
    refine norm_integral_le_of_norm_le hint ?_
    filter_upwards [hb] with ζ hζ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hζ (norm_nonneg _)
  rw [integral_const_mul] at h1
  have hπ : ‖-(1 / π : ℂ)‖ = 1 / π := by
    rw [norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  unfold ahVar
  rw [norm_mul, hπ]
  calc 1 / π * ‖∫ ζ, ν ζ * ahKer w ζ‖ ≤ 1 / π * (ε * ∫ ζ, ‖ahKer w ζ‖) := by
        gcongr
    _ = 1 / π * (∫ ζ, ‖ahKer w ζ‖) * ε := by ring

/-- `V` is linear on bounded measurable coefficients. -/
theorem ah_var_linear {ν₁ ν₂ : ℂ → ℂ} {ε₁ ε₂ : ℝ} (h₁ : IsBeltramiCoeff ν₁ univ ε₁)
    (h₂ : IsBeltramiCoeff ν₂ univ ε₂) (a w : ℂ) :
    ahVar (fun ζ => a * ν₁ ζ + ν₂ ζ) w = a * ahVar ν₁ w + ahVar ν₂ w := by
  have hK := ah_ker_integrable w
  have i₁ : Integrable (fun ζ => ν₁ ζ * ahKer w ζ) := by
    have hm := h₁.1
    have hb := h₁.2
    rw [Measure.restrict_univ] at hm hb
    exact hK.bdd_mul hm hb
  have i₂ : Integrable (fun ζ => ν₂ ζ * ahKer w ζ) := by
    have hm := h₂.1
    have hb := h₂.2
    rw [Measure.restrict_univ] at hm hb
    exact hK.bdd_mul hm hb
  have e : ∫ ζ, (a * ν₁ ζ + ν₂ ζ) * ahKer w ζ =
      a * (∫ ζ, ν₁ ζ * ahKer w ζ) + ∫ ζ, ν₂ ζ * ahKer w ζ := by
    rw [← integral_const_mul, ← integral_add (i₁.const_mul a) i₂]
    congr 1
    funext ζ
    ring
  simp only [ahVar]
  rw [e]
  ring

/-! ### Piece CFV — first variation for compactly supported coefficients -/

/-- The plane solution `z + T ω` of (12.4) at a fixed exponent `p > 2` is an `L_p` generalized
homeomorphic solution of the Beltrami equation for `ν` (the construction in the proof of
Theorem 12.1, for a given `p` and `ω`). -/
theorem ahC_genHomeoSolution {ν ω : ℂ → ℂ} {p R : ℝ} (hp : 2 < p)
    (hνR : ∀ z : ℂ, R < ‖z‖ → ν z = 0) (hω : MemLp ω (ENNReal.ofReal p))
    (hsol : ω =ᵐ[volume] fun z => ν z * hilbertH ω z + ν z)
    (hhom : IsHomeomorphOnto (fun z => z + cauchyT ω z) univ
      ((fun z => z + cauchyT ω z) '' univ)) :
    IsGenHomeoSolution (fun z => z + cauchyT ω z) ν univ (ENNReal.ofReal p) := by
  refine ⟨hhom, ?_⟩
  set omR : ℂ → ℂ := (closedBall (0 : ℂ) R).indicator ω with homRdef
  have homs : ω =ᵐ[volume] omR := t2_omega_ae_eq_indicator hνR hsol
  have hcT : cauchyT ω = cauchyT omR := cauchyT_congr_ae homs
  have hHT : hilbertH ω = hilbertH omR := hilbertH_congr_ae homs
  have homRmem : MemLp omR (ENNReal.ofReal p) := hω.indicator measurableSet_closedBall
  have homRbdd : Bornology.IsBounded (Function.support omR) := t3_isBounded_support_indicator
  obtain ⟨hgp, heqbar, heqz⟩ := thm11_1 hp homRmem homRbdd
  have hgp' := t3_hasGenPartials_add_id hgp
  have hpteq : ∀ z : ℂ, genDzbar (fun z => 1 + (hilbertH omR z + omR z))
      (fun z => I + I * (hilbertH omR z - omR z)) z = omR z := by
    intro z
    have h1 := heqbar z
    rw [genDzbar] at h1 ⊢
    linear_combination h1 + (1 / 2 : ℂ) * I_sq
  have hpteq2 : ∀ z : ℂ, genDz (fun z => 1 + (hilbertH omR z + omR z))
      (fun z => I + I * (hilbertH omR z - omR z)) z = 1 + hilbertH omR z := by
    intro z
    have h2 := heqz z
    rw [genDz] at h2 ⊢
    linear_combination h2 - (1 / 2 : ℂ) * I_sq
  refine ⟨fun z => 1 + (hilbertH omR z + omR z), fun z => I + I * (hilbertH omR z - omR z),
    ?_, ?_⟩
  · rw [show (fun z => z + cauchyT ω z) = (fun z => z + cauchyT omR z) from
      by funext z; rw [hcT]]
    exact hgp'
  · rw [Measure.restrict_univ]
    filter_upwards [hsol, homs] with z hsolz hz
    rw [hpteq z, hpteq2 z, ← hz, hsolz, congrFun hHT z]
    ring

/-- The normalized solution is the affine normalization of `z + T ω`:
`F w = (w + Tω(w) - Tω(0)) / (1 + Tω(1) - Tω(0))` (Theorem 12.1 at the fixed exponent, the
identification of the dilatation as in Theorem 12.2, and the uniqueness Theorem 13.5). -/
theorem ahC_normalized_eq {ν ω F : ℂ → ℂ} {k p R : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hν : IsBeltramiCoeff ν univ k) (hνR : ∀ z : ℂ, R < ‖z‖ → ν z = 0) (hp : 2 < p)
    (hkp : k * hilbertNorm p < 1) (hω : MemLp ω (ENNReal.ofReal p))
    (hsol : ω =ᵐ[volume] fun z => ν z * hilbertH ω z + ν z) (hF : IsNormalizedSolution F ν) :
    1 + cauchyT ω 1 - cauchyT ω 0 ≠ 0 ∧
      ∀ w, F w = (w + cauchyT ω w - cauchyT ω 0) / (1 + cauchyT ω 1 - cauchyT ω 0) := by
  have hνc : IsCompactBeltramiCoeff ν k := ⟨hν, R, hνR⟩
  obtain ⟨hkqc, e, he⟩ := thm12_1_isKQC hk₀ hk hνc hp hkp hω hsol
  have hgen := ahC_genHomeoSolution hp hνR hω hsol hkqc.2.2.1
  have hdil := t2_complexDilatation_ae hkqc hp hgen
  set W : ℂ → ℂ := fun z => z + cauchyT ω z with hWdef
  have hW10 : W 1 - W 0 = 1 + cauchyT ω 1 - cauchyT ω 0 := by simp only [hWdef]; ring
  have ha : W 1 - W 0 ≠ 0 := by
    intro h
    have h' : e 1 = e 0 := by rw [he]; exact sub_eq_zero.mp h
    exact one_ne_zero (e.injective h')
  refine ⟨hW10 ▸ ha, ?_⟩
  set G : ℂ → ℂ := (fun u => (u - W 0) / (W 1 - W 0)) ∘ W with hGdef
  have hAc := nxE_affine_isConformalOnto (b := W 0) ha
  have hA1 := isKQC_one_of_conformal isOpen_univ hAc
  have hGq : IsQuasiconformal G univ := ⟨_, thm7_1_comp hkqc hA1 (subset_univ _)⟩
  have hWs : W '' univ = univ := by
    rw [image_univ, ← he]
    exact e.surjective.range_eq
  have hGs : G '' univ = univ := by
    rw [hGdef, image_comp, hWs]
    exact hAc.2.2
  have hG0 : G 0 = 0 := by simp only [hGdef, Function.comp_apply, sub_self, zero_div]
  have hG1 : G 1 = 1 := by
    simp only [hGdef, Function.comp_apply]
    exact div_self ha
  have hGdil : ∀ z, complexDilatation G z = complexDilatation W z := fun z =>
    nxE_complexDilatation_affine ha z
  have hFG : F = G := thm13_5_uniqueness_plane hF.1 hGq hF.2.1 hGs
    (by filter_upwards [hF.2.2.2.2, hdil] with z h1 h2; rw [h1, hGdil, h2]) hF.2.2.1 hF.2.2.2.1
    hG0 hG1
  intro w
  rw [hFG, hGdef, Function.comp_apply, hW10]
  simp only [hWdef]
  ring

/-- A coefficient with `|ν| ≤ ε` a.e. vanishing outside `B̄(0,R)` has `‖ν‖_p ≤ m ε` for a constant
`m = m(R, p)` (`m = |B̄(0,R)|^{1/p}`). -/
theorem ahC_eLpNorm_le (R p : ℝ) :
    ∃ m : ℝ, 0 ≤ m ∧ ∀ (ν : ℂ → ℂ) (ε : ℝ), 0 ≤ ε → IsBeltramiCoeff ν univ ε →
      (∀ z : ℂ, R < ‖z‖ → ν z = 0) → (eLpNorm ν (ENNReal.ofReal p)).toReal ≤ m * ε := by
  set X : ℝ≥0∞ := volume (closedBall (0 : ℂ) R) ^ (ENNReal.ofReal p).toReal⁻¹ with hXdef
  have hX : X ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) measure_closedBall_lt_top.ne
  refine ⟨X.toReal, ENNReal.toReal_nonneg, fun ν ε hε hν hνR => ?_⟩
  have hind : ν = (closedBall (0 : ℂ) R).indicator ν := by
    funext z
    by_cases hz : z ∈ closedBall (0 : ℂ) R
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz]
      exact hνR z (by rwa [mem_closedBall_zero_iff, not_le] at hz)
  have hνm : AEStronglyMeasurable ν volume := by simpa using hν.1
  have hνb : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν z‖ ≤ ε := by simpa using hν.2
  have hle : eLpNorm ν (ENNReal.ofReal p) volume ≤ X * ENNReal.ofReal ε := by
    rw [hind, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall]
    have h := eLpNorm_le_of_ae_bound (p := ENNReal.ofReal p)
      (μ := volume.restrict (closedBall (0 : ℂ) R)) hνm.restrict (ae_restrict_of_ae hνb)
    rwa [Measure.restrict_apply_univ] at h
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top hX ENNReal.ofReal_ne_top) hle
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε] at h2

/-- For the solution of `ω = ν H(ω) + ν` with `|ν| ≤ ε`: `‖ω - ν‖_p ≤ ε Λ_p ‖ω‖_p` and
`‖ω‖_p ≤ ‖ω - ν‖_p + ‖ν‖_p`. -/
theorem ahC_omega_bounds {ν ω : ℂ → ℂ} {ε p : ℝ} (hε : 0 ≤ ε) (hν : IsBeltramiCoeff ν univ ε)
    (hp : 1 < p) (hνm : MemLp ν (ENNReal.ofReal p)) (hω : MemLp ω (ENNReal.ofReal p))
    (hsol : ω =ᵐ[volume] fun z => ν z * hilbertH ω z + ν z) :
    (eLpNorm (fun z => ω z - ν z) (ENNReal.ofReal p)).toReal ≤
        ε * hilbertNorm p * (eLpNorm ω (ENNReal.ofReal p)).toReal ∧
      (eLpNorm ω (ENNReal.ofReal p)).toReal ≤
        (eLpNorm (fun z => ω z - ν z) (ENNReal.ofReal p)).toReal +
          (eLpNorm ν (ENNReal.ofReal p)).toReal := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  have hνbd : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν z‖ ≤ ε := by simpa using hν.2
  have hνmeas : AEStronglyMeasurable ν volume := by simpa using hν.1
  have hH : MemLp (hilbertH ω) (ENNReal.ofReal p) := hilbertH_memLp hp hω
  have hcong : (fun z => ω z - ν z) =ᵐ[volume] fun z => ν z * hilbertH ω z := by
    filter_upwards [hsol] with z hz
    rw [hz]; ring
  have hmeas : AEStronglyMeasurable (fun z => ν z * hilbertH ω z) volume :=
    hνmeas.mul hH.aestronglyMeasurable
  have h1 : eLpNorm (fun z => ω z - ν z) (ENNReal.ofReal p) ≤
      ENNReal.ofReal ε * (ENNReal.ofReal (hilbertNorm p) * eLpNorm ω (ENNReal.ofReal p)) := by
    rw [eLpNorm_congr_ae hcong]
    calc eLpNorm (fun z => ν z * hilbertH ω z) (ENNReal.ofReal p) volume
        ≤ ENNReal.ofReal ε * eLpNorm (hilbertH ω) (ENNReal.ofReal p) volume := by
          refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas ?_ _
          filter_upwards [hνbd] with z hz
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      _ ≤ _ := by gcongr; exact eq11_16_eLpNorm hp hω
  have hων : MemLp (fun z => ω z - ν z) (ENNReal.ofReal p) := hω.sub hνm
  refine ⟨?_, ?_⟩
  · have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω.eLpNorm_ne_top)) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hε,
      ENNReal.toReal_ofReal (hilbertNorm_nonneg p), ← mul_assoc] at h3
  · have h2 : eLpNorm ω (ENNReal.ofReal p) ≤
        eLpNorm (fun z => ω z - ν z) (ENNReal.ofReal p) + eLpNorm ν (ENNReal.ofReal p) := by
      have h4 := eLpNorm_add_le (μ := volume) (f := fun z => ω z - ν z) (g := ν) hp1
      have heq : ((fun z => ω z - ν z) + ν) = ω := by
        funext z; simp
      rwa [heq] at h4
    have h5 := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨hων.eLpNorm_ne_top, hνm.eLpNorm_ne_top⟩) h2
    rwa [ENNReal.toReal_add hων.eLpNorm_ne_top hνm.eLpNorm_ne_top] at h5

/-- `T` is additive on functions whose Cauchy kernels at `z` are integrable. -/
theorem ahC_cauchyT_sub {ω ν : ℂ → ℂ} {z : ℂ} (hω : Integrable (fun ζ => ω ζ / (ζ - z)))
    (hν : Integrable (fun ζ => ν ζ / (ζ - z))) :
    cauchyT ω z - cauchyT ν z = cauchyT (fun ζ => ω ζ - ν ζ) z := by
  unfold cauchyT
  rw [← mul_sub, ← integral_sub hω hν]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
  simp only [sub_div]

/-- The kernel identity `V[ν](w) = Tν(w) - Tν(0) - w (Tν(1) - Tν(0))`, from
`1/(ζ-w) - 1/ζ - w (1/(ζ-1) - 1/ζ) = w(w-1)/(ζ(ζ-1)(ζ-w))` off `{0, 1, w}`. -/
theorem ahC_ahVar_eq {ν : ℂ → ℂ} {p R : ℝ} (hp : 2 < p) (hR : 0 < R)
    (hν : MemLp ν (ENNReal.ofReal p)) (hνR : ∀ z : ℂ, R < ‖z‖ → ν z = 0) (w : ℂ) :
    ahVar ν w = cauchyT ν w - cauchyT ν 0 - w * (cauchyT ν 1 - cauchyT ν 0) := by
  have hi : ∀ z, Integrable (fun ζ => ν ζ / (ζ - z)) := integrable_cauchyT_kernel hp hR hν hνR
  have hae : (fun ζ => ν ζ * ahKer w ζ) =ᵐ[volume]
      fun ζ => (ν ζ / (ζ - w) - ν ζ / (ζ - 0)) - w * (ν ζ / (ζ - 1) - ν ζ / (ζ - 0)) := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ), Measure.ae_ne volume (1 : ℂ),
      Measure.ae_ne volume w] with ζ h0 h1 hw
    have h1' : ζ - 1 ≠ 0 := sub_ne_zero.2 h1
    have hw' : ζ - w ≠ 0 := sub_ne_zero.2 hw
    simp only [ahKer, sub_zero]
    field_simp
    ring
  have hint : ∫ ζ, ν ζ * ahKer w ζ = ((∫ ζ, ν ζ / (ζ - w)) - ∫ ζ, ν ζ / (ζ - 0)) -
      w * ((∫ ζ, ν ζ / (ζ - 1)) - ∫ ζ, ν ζ / (ζ - 0)) := by
    have hA : Integrable (fun ζ => ν ζ / (ζ - w) - ν ζ / (ζ - 0)) := (hi w).sub (hi 0)
    have hB : Integrable (fun ζ => w * (ν ζ / (ζ - 1) - ν ζ / (ζ - 0))) :=
      ((hi 1).sub (hi 0)).const_mul w
    rw [integral_congr_ae hae, integral_sub hA hB, integral_sub (hi w) (hi 0), integral_const_mul,
      integral_sub (hi 1) (hi 0)]
  unfold ahVar cauchyT
  rw [hint]
  ring

/-- The elementary estimates: with `d = t₁ - t₀`, `|d| ≤ 1/2`,
`(w + t_w - t₀)/(1 + d) - w = (t_w - t₀ - w d)/(1 + d)` and, with `V = s_w - s₀ - w(s₁ - s₀)`
and `u = t - s`, `(w + t_w - t₀)/(1 + d) - w - V = [u_w - u₀ - w(u₁ - u₀) - d V]/(1 + d)`. -/
theorem ahC_algebra {w tw t0 t1 sw s0 s1 : ℂ} {M a b c : ℝ} (hM : 0 ≤ M) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (htw : ‖tw‖ ≤ M * b) (ht0 : ‖t0‖ ≤ M * b) (ht1 : ‖t1‖ ≤ M * b)
    (hsw : ‖sw‖ ≤ M * a) (hs0 : ‖s0‖ ≤ M * a) (hs1 : ‖s1‖ ≤ M * a)
    (hdw : ‖tw - sw‖ ≤ M * c) (hd0 : ‖t0 - s0‖ ≤ M * c) (hd1 : ‖t1 - s1‖ ≤ M * c)
    (hsmall : 2 * (M * b) ≤ 1 / 2) :
    ‖(w + tw - t0) / (1 + t1 - t0) - w‖ ≤ 4 * M * b * (1 + ‖w‖) ∧
      ‖(w + tw - t0) / (1 + t1 - t0) - w - (sw - s0 - w * (s1 - s0))‖ ≤
        (4 * M * c + 8 * M ^ 2 * a * b) * (1 + ‖w‖) := by
  have hwn := norm_nonneg w
  have hd : ‖t1 - t0‖ ≤ 2 * (M * b) := by
    calc ‖t1 - t0‖ ≤ ‖t1‖ + ‖t0‖ := norm_sub_le _ _
      _ ≤ 2 * (M * b) := by linarith
  have hden : 1 / 2 ≤ ‖1 + t1 - t0‖ := by
    have h1 : (1 : ℝ) ≤ ‖1 + t1 - t0‖ + ‖t1 - t0‖ := by
      calc (1 : ℝ) = ‖(1 + t1 - t0) - (t1 - t0)‖ := by
            rw [show (1 + t1 - t0) - (t1 - t0) = (1 : ℂ) by ring, norm_one]
        _ ≤ _ := norm_sub_le _ _
    linarith
  have hpos : 0 < ‖1 + t1 - t0‖ := by linarith
  have hne : (1 + t1 - t0) ≠ 0 := norm_pos_iff.1 hpos
  have hV : ‖sw - s0 - w * (s1 - s0)‖ ≤ 2 * (M * a) * (1 + ‖w‖) := by
    calc ‖sw - s0 - w * (s1 - s0)‖ ≤ ‖sw - s0‖ + ‖w * (s1 - s0)‖ := norm_sub_le _ _
      _ ≤ (‖sw‖ + ‖s0‖) + ‖w‖ * (‖s1‖ + ‖s0‖) := by
          rw [norm_mul]
          gcongr
          · exact norm_sub_le _ _
          · exact norm_sub_le _ _
      _ ≤ (M * a + M * a) + ‖w‖ * (M * a + M * a) := by gcongr
      _ = 2 * (M * a) * (1 + ‖w‖) := by ring
  constructor
  · have heq : (w + tw - t0) / (1 + t1 - t0) - w =
        (tw - t0 - w * (t1 - t0)) / (1 + t1 - t0) := by
      field_simp
      ring
    rw [heq, norm_div, div_le_iff₀ hpos]
    have hnum : ‖tw - t0 - w * (t1 - t0)‖ ≤ 2 * (M * b) * (1 + ‖w‖) := by
      calc ‖tw - t0 - w * (t1 - t0)‖ ≤ ‖tw - t0‖ + ‖w * (t1 - t0)‖ := norm_sub_le _ _
        _ ≤ (‖tw‖ + ‖t0‖) + ‖w‖ * ‖t1 - t0‖ := by
            rw [norm_mul]
            gcongr
            exact norm_sub_le _ _
        _ ≤ (M * b + M * b) + ‖w‖ * (2 * (M * b)) := by gcongr
        _ = 2 * (M * b) * (1 + ‖w‖) := by ring
    have hnn : 0 ≤ 4 * M * b * (1 + ‖w‖) := by positivity
    calc ‖tw - t0 - w * (t1 - t0)‖ ≤ 2 * (M * b) * (1 + ‖w‖) := hnum
      _ = 4 * M * b * (1 + ‖w‖) * (1 / 2) := by ring
      _ ≤ 4 * M * b * (1 + ‖w‖) * ‖1 + t1 - t0‖ := mul_le_mul_of_nonneg_left hden hnn
  · have heq : (w + tw - t0) / (1 + t1 - t0) - w - (sw - s0 - w * (s1 - s0)) =
        ((tw - sw) - (t0 - s0) - w * ((t1 - s1) - (t0 - s0)) -
          (t1 - t0) * (sw - s0 - w * (s1 - s0))) / (1 + t1 - t0) := by
      field_simp
      ring
    rw [heq, norm_div, div_le_iff₀ hpos]
    have hc : 0 ≤ M * c := (norm_nonneg _).trans hdw
    have hnum : ‖(tw - sw) - (t0 - s0) - w * ((t1 - s1) - (t0 - s0)) -
        (t1 - t0) * (sw - s0 - w * (s1 - s0))‖ ≤
          (2 * M * c + 4 * M ^ 2 * a * b) * (1 + ‖w‖) := by
      calc _ ≤ ‖(tw - sw) - (t0 - s0) - w * ((t1 - s1) - (t0 - s0))‖ +
            ‖(t1 - t0) * (sw - s0 - w * (s1 - s0))‖ := norm_sub_le _ _
        _ ≤ ((‖tw - sw‖ + ‖t0 - s0‖) + ‖w‖ * (‖t1 - s1‖ + ‖t0 - s0‖)) +
            ‖t1 - t0‖ * ‖sw - s0 - w * (s1 - s0)‖ := by
            rw [norm_mul (t1 - t0)]
            gcongr
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul]
            gcongr
            · exact norm_sub_le _ _
            · exact norm_sub_le _ _
        _ ≤ ((M * c + M * c) + ‖w‖ * (M * c + M * c)) +
            (2 * (M * b)) * (2 * (M * a) * (1 + ‖w‖)) := by gcongr
        _ = (2 * M * c + 4 * M ^ 2 * a * b) * (1 + ‖w‖) := by ring
    have hnn : 0 ≤ (4 * M * c + 8 * M ^ 2 * a * b) * (1 + ‖w‖) := by
      have : 0 ≤ 4 * M * c := by linarith
      positivity
    calc _ ≤ (2 * M * c + 4 * M ^ 2 * a * b) * (1 + ‖w‖) := hnum
      _ = (4 * M * c + 8 * M ^ 2 * a * b) * (1 + ‖w‖) * (1 / 2) := by ring
      _ ≤ (4 * M * c + 8 * M ^ 2 * a * b) * (1 + ‖w‖) * ‖1 + t1 - t0‖ :=
          mul_le_mul_of_nonneg_left hden hnn

/-- For coefficients supported in `B̄(0,R)` with `|ν| ≤ ε ≤ δ`: `|F^ν(w) - w| ≤ C ε (1 + |w|)` everywhere and
`|F^ν(w) - w - V[ν](w)| ≤ C ε²` for `|w| ≤ R`. -/
theorem ah_first_variation_compact (R : ℝ) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ (ν F : ℂ → ℂ) (ε : ℝ), ε ≤ δ → IsBeltramiCoeff ν univ ε →
      (∀ ζ : ℂ, R < ‖ζ‖ → ν ζ = 0) → IsNormalizedSolution F ν →
      (∀ w : ℂ, ‖F w - w‖ ≤ C * ε * (1 + ‖w‖)) ∧
        ∀ w : ℂ, ‖w‖ ≤ R → ‖F w - w - ahVar ν w‖ ≤ C * ε ^ 2 := by
  obtain ⟨R', hR'0, hRR'⟩ : ∃ R' : ℝ, 0 < R' ∧ R ≤ R' :=
    ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _), le_max_left _ _⟩
  -- the fixed exponent: `p > 2` with `Λ_p / 2 < 1`
  obtain ⟨p, hp, -, hkp⟩ := eq12_1_exists_exponent (k := 1 / 2) (by norm_num)
    (show (2 : ℝ) < 3 by norm_num)
  have hp1 : 1 < p := by linarith
  set Λ : ℝ := hilbertNorm p with hΛdef
  have hΛ : 0 ≤ Λ := hilbertNorm_nonneg p
  set c₀ : ℝ := 1 - Λ / 2 with hc₀def
  have hc₀ : 0 < c₀ := by rw [hc₀def]; linarith
  -- Lemma 11.1 on `B̄(0,R')`
  obtain ⟨M₁, hM₁⟩ := lemma11_1 hp hR'0
  set M : ℝ := max M₁ 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  have hMb : ∀ ω : ℂ → ℂ, MemLp ω (ENNReal.ofReal p) → (∀ z, R' < ‖z‖ → ω z = 0) →
      ∀ z, ‖cauchyT ω z‖ ≤ M * (eLpNorm ω (ENNReal.ofReal p)).toReal := fun ω hω hs z =>
    (hM₁ ω hω hs z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg)
  obtain ⟨m, hm0, hm⟩ := ahC_eLpNorm_le R' p
  set δ : ℝ := min (1 / 2) (c₀ / (4 * M * m + 1)) with hδdef
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hc₀ (by positivity))
  set C : ℝ := 4 * M * m / c₀ + (1 + R') * (4 * M * Λ * m / c₀ + 8 * M ^ 2 * m ^ 2 / c₀)
    with hCdef
  refine ⟨C, δ, hδ, fun ν F ε hεδ hν hνR hF => ?_⟩
  -- `ε ≥ 0` (a negative a.e. bound is impossible)
  have hε : 0 ≤ ε := by
    by_contra hneg
    push Not at hneg
    have h := hν.2
    rw [Measure.restrict_univ] at h
    obtain ⟨z, hz⟩ := h.exists
    linarith [norm_nonneg (ν z)]
  have hνR' : ∀ z : ℂ, R' < ‖z‖ → ν z = 0 := fun z hz => hνR z (lt_of_le_of_lt hRR' hz)
  have hε1 : ε ≤ 1 / 2 := hεδ.trans (min_le_left _ _)
  have hεs : ε ≤ c₀ / (4 * M * m + 1) := hεδ.trans (min_le_right _ _)
  have hk : ε < 1 := by linarith
  have hεΛ : ε * Λ ≤ Λ / 2 := by nlinarith
  have hkp' : ε * Λ < 1 := by linarith
  -- Theorem 12.1 at the fixed exponent
  have hνc : IsCompactBeltramiCoeff ν ε := ⟨hν, R', hνR'⟩
  have hνm : MemLp ν (ENNReal.ofReal p) := t3_memLp_of_compactBeltrami hνc
  obtain ⟨ω, hω, hsol, -⟩ := eq12_1_solution hε hν hp hkp' hνm
  obtain ⟨-, hFeq⟩ := ahC_normalized_eq hε hk hν hνR' hp hkp' hω hsol hF
  -- the representative of `ω` supported in `B̄(0,R')`
  set omR : ℂ → ℂ := (closedBall (0 : ℂ) R').indicator ω with homRdef
  have homs : ω =ᵐ[volume] omR := t2_omega_ae_eq_indicator hνR' hsol
  have hcT : cauchyT ω = cauchyT omR := cauchyT_congr_ae homs
  have homRmem : MemLp omR (ENNReal.ofReal p) := hω.indicator measurableSet_closedBall
  have homRsupp : ∀ z : ℂ, R' < ‖z‖ → omR z = 0 := fun z hz =>
    indicator_of_notMem (by rwa [mem_closedBall_zero_iff, not_le]) _
  have hdmem : MemLp (fun ζ => omR ζ - ν ζ) (ENNReal.ofReal p) := homRmem.sub hνm
  have hdsupp : ∀ z : ℂ, R' < ‖z‖ → (fun ζ => omR ζ - ν ζ) z = 0 := fun z hz => by
    simp only [homRsupp z hz, hνR' z hz, sub_zero]
  -- `L_p` bounds
  obtain ⟨hc, hb⟩ := ahC_omega_bounds hε hν hp1 hνm hω hsol
  set a : ℝ := (eLpNorm ν (ENNReal.ofReal p)).toReal with hadef
  set b : ℝ := (eLpNorm ω (ENNReal.ofReal p)).toReal with hbdef
  set c : ℝ := (eLpNorm (fun z => ω z - ν z) (ENNReal.ofReal p)).toReal with hcdef
  have ha : a ≤ m * ε := hm ν ε hε hν hνR'
  have hbR : (eLpNorm omR (ENNReal.ofReal p)).toReal = b := by
    rw [hbdef, eLpNorm_congr_ae homs.symm]
  have hcR : (eLpNorm (fun ζ => omR ζ - ν ζ) (ENNReal.ofReal p)).toReal = c := by
    rw [hcdef]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [homs] with z hz
    rw [hz]
  -- uniform bounds for `T` (Lemma 11.1)
  have htb : ∀ z, ‖cauchyT omR z‖ ≤ M * b := fun z => hbR ▸ hMb omR homRmem homRsupp z
  have hsb : ∀ z, ‖cauchyT ν z‖ ≤ M * a := fun z => hMb ν hνm hνR' z
  have hdb : ∀ z, ‖cauchyT omR z - cauchyT ν z‖ ≤ M * c := fun z => by
    rw [ahC_cauchyT_sub (integrable_cauchyT_kernel hp hR'0 homRmem homRsupp z)
      (integrable_cauchyT_kernel hp hR'0 hνm hνR' z), ← hcR]
    exact hMb _ hdmem hdsupp z
  -- real estimates: `‖ω‖_p = O(ε)`, `‖ω - ν‖_p = O(ε²)`
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hbε : c₀ * b ≤ m * ε := by
    have h1 : ε * Λ * b ≤ Λ / 2 * b := mul_le_mul_of_nonneg_right hεΛ hb0
    have h2 : c₀ * b = b - Λ / 2 * b := by rw [hc₀def]; ring
    linarith
  have hb' : b ≤ m * ε / c₀ := by rw [le_div_iff₀ hc₀]; linarith
  have hc' : c ≤ Λ * m * ε ^ 2 / c₀ := by
    calc c ≤ ε * Λ * b := hc
      _ ≤ ε * Λ * (m * ε / c₀) := mul_le_mul_of_nonneg_left hb' (mul_nonneg hε hΛ)
      _ = Λ * m * ε ^ 2 / c₀ := by ring
  have hsmall : 2 * (M * b) ≤ 1 / 2 := by
    have h1 : ε * (4 * M * m + 1) ≤ c₀ := by
      rwa [le_div_iff₀ (by positivity)] at hεs
    have h2 : M * (c₀ * b) ≤ M * (m * ε) := mul_le_mul_of_nonneg_left hbε hM
    have h3 : 4 * (M * b) * c₀ ≤ 1 * c₀ := by nlinarith
    have h4 := le_of_mul_le_mul_right h3 hc₀
    linarith
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · rw [hFeq w, hcT]
    have hA := (ahC_algebra (w := w) hM ha0 hb0 (htb w) (htb 0) (htb 1) (hsb w) (hsb 0) (hsb 1)
      (hdb w) (hdb 0) (hdb 1) hsmall).1
    have hw0 : 0 ≤ 1 + ‖w‖ := by positivity
    have hrest : 0 ≤ (1 + R') * (4 * M * Λ * m / c₀ + 8 * M ^ 2 * m ^ 2 / c₀) * ε := by
      positivity
    have hCε : C * ε = 4 * M * m / c₀ * ε +
        (1 + R') * (4 * M * Λ * m / c₀ + 8 * M ^ 2 * m ^ 2 / c₀) * ε := by
      rw [hCdef]; ring
    calc _ ≤ 4 * M * b * (1 + ‖w‖) := hA
      _ ≤ 4 * M * (m * ε / c₀) * (1 + ‖w‖) := by gcongr
      _ = (4 * M * m / c₀ * ε) * (1 + ‖w‖) := by ring
      _ ≤ C * ε * (1 + ‖w‖) := by
          refine mul_le_mul_of_nonneg_right ?_ hw0
          linarith
  · rw [hFeq w, hcT, ahC_ahVar_eq hp hR'0 hνm hνR' w]
    have hB := (ahC_algebra (w := w) hM ha0 hb0 (htb w) (htb 0) (htb 1) (hsb w) (hsb 0) (hsb 1)
      (hdb w) (hdb 0) (hdb 1) hsmall).2
    have hwR : ‖w‖ ≤ R' := hw.trans hRR'
    have hab : a * b ≤ m ^ 2 * ε ^ 2 / c₀ := by
      calc a * b ≤ (m * ε) * (m * ε / c₀) := mul_le_mul ha hb' hb0 (by positivity)
        _ = m ^ 2 * ε ^ 2 / c₀ := by ring
    have hK : 4 * M * c + 8 * M ^ 2 * a * b ≤
        (4 * M * Λ * m / c₀ + 8 * M ^ 2 * m ^ 2 / c₀) * ε ^ 2 := by
      have h1 : 4 * M * c ≤ 4 * M * (Λ * m * ε ^ 2 / c₀) :=
        mul_le_mul_of_nonneg_left hc' (by positivity)
      have h2 : 8 * M ^ 2 * (a * b) ≤ 8 * M ^ 2 * (m ^ 2 * ε ^ 2 / c₀) :=
        mul_le_mul_of_nonneg_left hab (by positivity)
      have h3 : (4 * M * Λ * m / c₀ + 8 * M ^ 2 * m ^ 2 / c₀) * ε ^ 2 =
          4 * M * (Λ * m * ε ^ 2 / c₀) + 8 * M ^ 2 * (m ^ 2 * ε ^ 2 / c₀) := by ring
      have h4 : 8 * M ^ 2 * a * b = 8 * M ^ 2 * (a * b) := by ring
      rw [h3, h4]
      linarith
    have hCε : C * ε ^ 2 = 4 * M * m / c₀ * ε ^ 2 +
        ((4 * M * Λ * m / c₀ + 8 * M ^ 2 * m ^ 2 / c₀) * ε ^ 2) * (1 + R') := by
      rw [hCdef]; ring
    have hfirst : 0 ≤ 4 * M * m / c₀ * ε ^ 2 := by positivity
    calc _ ≤ (4 * M * c + 8 * M ^ 2 * a * b) * (1 + ‖w‖) := hB
      _ ≤ ((4 * M * Λ * m / c₀ + 8 * M ^ 2 * m ^ 2 / c₀) * ε ^ 2) * (1 + R') :=
          mul_le_mul hK (by linarith) (by positivity) (by positivity)
      _ ≤ C * ε ^ 2 := by linarith

/-! ### Piece INV — coefficients vanishing in the unit disc (conjugation by `z ↦ 1/z`) -/

/-- A bound `‖ν‖ ≤ ε` a.e. on `ℂ` forces `0 ≤ ε`. -/
theorem ahI_nonneg_of_isBeltramiCoeff {ν : ℂ → ℂ} {ε : ℝ} (hν : IsBeltramiCoeff ν univ ε) : 0 ≤ ε := by
  obtain ⟨-, hb⟩ := hν
  rw [Measure.restrict_univ] at hb
  obtain ⟨z, hz⟩ := hb.exists
  exact (norm_nonneg _).trans hz

/-- The conjugation `f ↦ (z ↦ 1/f(1/z))` is an involution. -/
theorem ahI_invConj_invConj (f : ℂ → ℂ) : nxInvConj (nxInvConj f) = f := by
  funext z
  simp only [nxInvConj, inv_inv]

/-- A coefficient vanishing in the unit disc is its own outer part `nxMu2 ν`. -/
theorem ahI_nxMu2_eq {ν : ℂ → ℂ} (hν0 : ∀ ζ : ℂ, ‖ζ‖ < 1 → ν ζ = 0) : nxMu2 ν = ν := by
  funext ζ
  by_cases h : ζ ∈ unitDisc
  · rw [nxMu2, indicator_of_notMem (notMem_compl_iff.mpr h), hν0 ζ (mem_ball_zero_iff.1 h)]
  · rw [nxMu2, indicator_of_mem (mem_compl h)]

/-- The conjugated coefficient `nxMu2t ν` vanishes outside the closed unit disc. -/
theorem ahI_mu2t_eq_zero (ν : ℂ → ℂ) {ζ : ℂ} (hζ : 1 < ‖ζ‖) : nxMu2t ν ζ = 0 := by
  have hin : ζ⁻¹ ∈ unitDisc := by
    rw [unitDisc, mem_ball, dist_zero_right, norm_inv]
    exact inv_lt_one_of_one_lt₀ hζ
  rw [nxMu2t, nxMu2, indicator_of_notMem (notMem_compl_iff.mpr hin), zero_mul]

/-- `nx_f2_homeo` without its normalization at `∞` (unused in its proof): for a `K`-q.c. self-map `f` of `ℂ`
fixing `0`, `z ↦ 1/f(1/z)` is a homeomorphism of `ℂ` fixing `0` which is `K`-q.c. off `0`. -/
theorem ahI_f2_homeo {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (hs : f '' univ = univ) (h0 : f 0 = 0) :
    IsHomeomorphOnto (nxInvConj f) univ univ ∧ nxInvConj f 0 = 0 ∧ IsKQC (nxInvConj f) {0}ᶜ K := by
  obtain ⟨e, he⟩ := t1_homeomorph hf hs
  obtain ⟨E, hE⟩ := nxI1_exists_homeo e (by rw [he]; exact h0)
  refine ⟨?_, ?_, ?_⟩
  · rw [← he, ← hE]
    exact nxI1_isHomeomorphOnto_of_homeomorph E
  · simp [nxInvConj, h0]
  · have hinvq : IsKQC (fun z : ℂ => z⁻¹) {0}ᶜ 1 :=
      isKQC_one_of_conformal isOpen_compl_singleton nx_inv_isConformalOnto
    have hfinj : Function.Injective f := by rw [← he]; exact e.injective
    have h1 : IsKQC (f ∘ fun z : ℂ => z⁻¹) {0}ᶜ (1 * K) := thm7_1_comp hinvq hf (subset_univ _)
    have hsub : (f ∘ fun z : ℂ => z⁻¹) '' {0}ᶜ ⊆ {0}ᶜ := by
      rintro _ ⟨z, hz, rfl⟩ h
      rw [mem_singleton_iff, Function.comp_apply, ← h0] at h
      exact hz (inv_eq_zero.mp (hfinj h))
    have h2 := thm7_1_comp h1 hinvq hsub
    rw [mul_one, one_mul] at h2
    exact h2

/-- `nx_f2_conformal` without its normalization at `∞`: if `μ_f = nxMu2t μ` a.e., then `z ↦ 1/f(1/z)` is
conformal on the unit disc (conformal on `Δ ∖ {0}`, continuous at `0`: removable singularity). -/
theorem ahI_f2_conformal {μ f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (hs : f '' univ = univ)
    (h0 : f 0 = 0) (hdil : ∀ᵐ ζ, complexDilatation f ζ = nxMu2t μ ζ) :
    IsConformalOnto (nxInvConj f) unitDisc (nxInvConj f '' unitDisc) := by
  obtain ⟨hH, -, hK⟩ := ahI_f2_homeo hf hs h0
  have hopen : IsOpen (unitDisc \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hK' : IsKQC (nxInvConj f) (unitDisc \ {0}) K :=
    nx_isKQC_restrict hK hopen (fun z hz => hz.2)
  have hd := nx_f2_dilatation hf hs h0 hdil
  have hd0 : ∀ᵐ z ∂(volume.restrict (unitDisc \ {0})), complexDilatation (nxInvConj f) z = 0 := by
    rw [ae_restrict_iff' hopen.measurableSet]
    filter_upwards [hd] with z hz hzs
    rw [hz, nxMu2]
    exact indicator_of_notMem (fun h : z ∈ unitDiscᶜ => h hzs.1) μ
  have hdiff : DifferentiableOn ℂ (nxInvConj f) (unitDisc \ {0}) :=
    nx_differentiableOn_of_dilatation_zero hK' hd0
  have hcont : ContinuousAt (nxInvConj f) 0 :=
    hH.1.continuousAt (univ_mem)
  have hmem : unitDisc ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 one_pos
  exact ⟨(Complex.differentiableOn_compl_singleton_and_continuousAt_iff hmem).1 ⟨hdiff, hcont⟩,
    hH.2.1.mono (subset_univ _), rfl⟩

/-- **Inversion step.**  If `ν` vanishes in the unit disc and `F` is the normalized solution of `ν`, then
`z ↦ 1/F(1/z)` is the normalized solution of the conjugated coefficient `nxMu2t ν`.  (Take the normalized
solution `G` of `nxMu2t ν` (Theorem 13.7); `z ↦ 1/G(1/z)` is a homeomorphism fixing `0, 1`, q.c. off `0`,
conformal on `Δ`, with dilatation `ν`, hence q.c. on `ℂ` (`nx_sharp`), so it is `F` (Theorem 13.5).) -/
theorem ahI_invConj_isNormalizedSolution {ν F : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hν : IsBeltramiCoeff ν univ k) (hν0 : ∀ ζ : ℂ, ‖ζ‖ < 1 → ν ζ = 0)
    (hF : IsNormalizedSolution F ν) : IsNormalizedSolution (nxInvConj F) (nxMu2t ν) := by
  have hνt : IsBeltramiCoeff (nxMu2t ν) univ k := (nx_mu2t_compact hk₀ hν).1
  obtain ⟨G, ⟨-, hGs, hG0, hG1, hGd⟩, hGK, -⟩ := thm13_7_normalized_existence hk₀ hk hνt
  obtain ⟨hHh, hH0, hHK⟩ := ahI_f2_homeo hGK hGs hG0
  have hHc := ahI_f2_conformal hGK hGs hG0 hGd
  have hHd : ∀ᵐ z, complexDilatation (nxInvConj G) z = ν z := by
    have h := nx_f2_dilatation hGK hGs hG0 hGd
    rwa [ahI_nxMu2_eq hν0] at h
  have hH1 : nxInvConj G 1 = 1 := by simp [nxInvConj, hG1]
  have hHq : IsKQC (nxInvConj G) univ ((1 + k) / (1 - k)) :=
    nx_sharp hk₀ hk hν hHh ⟨1, isKQC_one_of_conformal isOpen_ball hHc⟩ ⟨_, hHK⟩ hHd
  have hFH : F = nxInvConj G := by
    obtain ⟨hFq, hFs, hF0, hF1, hFd⟩ := hF
    refine thm13_5_uniqueness_plane hFq ⟨_, hHq⟩ hFs hHh.2.2.1 ?_ hF0 hF1 hH0 hH1
    filter_upwards [hFd, hHd] with z h1 h2
    rw [h1, h2]
  rw [hFH, ahI_invConj_invConj]
  exact ⟨⟨_, hGK⟩, hGs, hG0, hG1, hGd⟩

/-- Uniform closeness to the identity on the closed unit disc. -/
theorem ah_outside_uniform :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ (ν F : ℂ → ℂ) (ε : ℝ), ε ≤ δ → IsBeltramiCoeff ν univ ε →
      (∀ ζ : ℂ, ‖ζ‖ < 1 → ν ζ = 0) → IsNormalizedSolution F ν →
      ∀ z : ℂ, ‖z‖ ≤ 1 → ‖F z - z‖ ≤ C * ε := by
  obtain ⟨C₀, δ₀, hδ₀, hCFV⟩ := ah_first_variation_compact 1
  set C₁ : ℝ := max C₀ 1 with hC₁
  have hC₁1 : 1 ≤ C₁ := le_max_right _ _
  have hC₁0 : 0 < C₁ := lt_of_lt_of_le one_pos hC₁1
  refine ⟨4 * C₁, min δ₀ (min (1 / 2) (1 / (4 * C₁))),
    lt_min hδ₀ (lt_min (by norm_num) (by positivity)), ?_⟩
  intro ν F ε hε hν hν0 hF z hz
  have hε0 : 0 ≤ ε := ahI_nonneg_of_isBeltramiCoeff hν
  have hεδ₀ : ε ≤ δ₀ := hε.trans (min_le_left _ _)
  have hε2 : ε ≤ 1 / 2 := hε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε4 : ε ≤ 1 / (4 * C₁) := hε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hC₁ε : 4 * C₁ * ε ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hε4
    linarith
  have hG := ahI_invConj_isNormalizedSolution hε0 (by linarith) hν hν0 hF
  have hνt : IsBeltramiCoeff (nxMu2t ν) univ ε := (nx_mu2t_compact hε0 hν).1
  obtain ⟨hunif, -⟩ :=
    hCFV (nxMu2t ν) (nxInvConj F) ε hεδ₀ hνt (fun ζ hζ => ahI_mu2t_eq_zero ν hζ) hG
  by_cases hz0 : z = 0
  · rw [hz0, hF.2.2.1, sub_zero, norm_zero]
    positivity
  -- `u = 1/z`, `‖u‖ ≥ 1`, `a = F̃ u`, `F z = 1/a`
  set u : ℂ := z⁻¹ with hu
  set a : ℂ := nxInvConj F u with ha
  have hu0 : u ≠ 0 := inv_ne_zero hz0
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hu1 : 1 ≤ ‖u‖ := by
    rw [hu, norm_inv]
    exact (one_le_inv₀ hzn).2 hz
  have hFz : F z = a⁻¹ := by rw [ha, hu, nxInvConj, inv_inv, inv_inv]
  have hzu : z = u⁻¹ := by rw [hu, inv_inv]
  have hau : ‖a - u‖ ≤ 2 * C₁ * ε * ‖u‖ := by
    calc ‖a - u‖ ≤ C₀ * ε * (1 + ‖u‖) := hunif u
      _ ≤ C₁ * ε * (1 + ‖u‖) := by gcongr; exact le_max_left _ _
      _ ≤ C₁ * ε * (2 * ‖u‖) := by gcongr; linarith
      _ = 2 * C₁ * ε * ‖u‖ := by ring
  have han : ‖u‖ / 2 ≤ ‖a‖ := by
    have h1 : ‖u‖ - ‖a‖ ≤ ‖a - u‖ := by
      rw [norm_sub_rev]
      exact norm_sub_norm_le u a
    have h2 : 2 * C₁ * ε * ‖u‖ ≤ ‖u‖ / 2 := by nlinarith
    linarith
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at han
    linarith
  rw [hFz, hzu, inv_sub_inv ha0 hu0, norm_div, norm_mul, div_le_iff₀ (by positivity), norm_sub_rev]
  calc ‖a - u‖ ≤ 2 * C₁ * ε * ‖u‖ := hau
    _ ≤ 2 * C₁ * ε * (‖u‖ * ‖u‖) := by gcongr; nlinarith
    _ = 4 * C₁ * ε * (‖u‖ / 2 * ‖u‖) := by ring
    _ ≤ 4 * C₁ * ε * (‖a‖ * ‖u‖) := by gcongr

/-- Change of variables `ζ = 1/ξ` in a plane integral: `∫ g(ζ) dζ = ∫ |ξ|⁻⁴ g(1/ξ) dξ`. -/
theorem ahI_integral_comp_inv (g : ℂ → ℂ) :
    ∫ ζ, g ζ = ∫ ξ, ((‖ξ‖ ^ 4)⁻¹ : ℝ) • g ξ⁻¹ := by
  have hs : MeasurableSet ({0}ᶜ : Set ℂ) := (measurableSet_singleton 0).compl
  have hd : ∀ x ∈ ({0}ᶜ : Set ℂ), HasFDerivWithinAt (fun z : ℂ => z⁻¹)
      (fderiv ℝ (fun z : ℂ => z⁻¹) x) ({0}ᶜ : Set ℂ) x := by
    intro x hx
    have hC : DifferentiableAt ℂ (fun z : ℂ => z⁻¹) x :=
      differentiableAt_inv (mem_compl_singleton_iff.mp hx)
    exact (hC.restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  have hinj : InjOn (fun z : ℂ => z⁻¹) ({0}ᶜ : Set ℂ) := fun a _ b _ hab => inv_injective hab
  have himg : (fun z : ℂ => z⁻¹) '' ({0}ᶜ : Set ℂ) = {0}ᶜ := nx_inv_isConformalOnto.2.2
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume hs hd hinj g
  rw [himg] at h
  simp only [restrict_compl_singleton] at h
  rw [h]
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with x hx
  have hx0 : x ≠ 0 := hx
  have hC : DifferentiableAt ℂ (fun z : ℂ => z⁻¹) x := differentiableAt_inv hx0
  have hdet : (fderiv ℝ (fun z : ℂ => z⁻¹) x).det = (‖x‖ ^ 4)⁻¹ := by
    have h1 := det_fderiv_eq_jacobian (hC.restrictScalars ℝ)
    rw [jacobian, (cauchyRiemann_iff.1 hC).2, dz_eq_deriv hC, deriv_inv, norm_zero, norm_neg,
      norm_inv, norm_pow] at h1
    rw [ContinuousLinearMap.det, h1]
    ring
  rw [hdet, abs_of_nonneg (by positivity)]

/-- The kernel identity of the inversion step: `V[nxMu2t ν](1/w) = -V[ν](w)/w²` for a coefficient `ν` vanishing
in the unit disc (substitute `ζ = 1/ξ`; pointwise `ν̃(1/ξ) K(1/w, 1/ξ) |ξ|⁻⁴ = -ν(ξ) K(w, ξ)/w²`). -/
theorem ahI_var_invConj {ν : ℂ → ℂ} (hν0 : ∀ ζ : ℂ, ‖ζ‖ < 1 → ν ζ = 0) {w : ℂ} (hw : w ≠ 0) :
    ahVar (nxMu2t ν) w⁻¹ = -ahVar ν w / w ^ 2 := by
  have hpt : ∀ ξ : ℂ, ξ ≠ 0 → ξ ≠ 1 → ξ ≠ w →
      ((‖ξ‖ ^ 4)⁻¹ : ℝ) • (nxMu2t ν ξ⁻¹ * ahKer w⁻¹ ξ⁻¹) = -(w ^ 2)⁻¹ * (ν ξ * ahKer w ξ) := by
    intro ξ h0 h1 hξw
    have hn : (((‖ξ‖ ^ 4)⁻¹ : ℝ) : ℂ) = ((ξ * conj ξ) ^ 2)⁻¹ := by
      rw [Complex.mul_conj, ← Complex.sq_norm]
      push_cast
      ring
    have hc : conj ξ ≠ 0 := (map_ne_zero _).mpr h0
    have hξ1 : ξ - 1 ≠ 0 := sub_ne_zero.mpr h1
    have hξw' : ξ - w ≠ 0 := sub_ne_zero.mpr hξw
    have h1ξ : 1 - ξ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    have hwξ : w - ξ ≠ 0 := sub_ne_zero.mpr (Ne.symm hξw)
    have e1 : ξ⁻¹ - 1 = (1 - ξ) / ξ := by field_simp
    have e2 : ξ⁻¹ - w⁻¹ = (w - ξ) / (ξ * w) := by field_simp
    rw [Complex.real_smul, hn, nxMu2t, inv_inv, ahI_nxMu2_eq hν0, ahKer, ahKer, map_inv₀, e1, e2]
    field_simp
    ring
  have hae : ∀ᵐ ξ : ℂ, ξ ≠ 0 ∧ ξ ≠ 1 ∧ ξ ≠ w := by
    have h3 : ∀ b : ℂ, ∀ᵐ ξ : ℂ, ξ ≠ b := fun b => compl_mem_ae_iff.2 (measure_singleton b)
    filter_upwards [h3 0, h3 1, h3 w] with ξ ha hb hc
    exact ⟨ha, hb, hc⟩
  have hint : ∫ ζ, nxMu2t ν ζ * ahKer w⁻¹ ζ = -(w ^ 2)⁻¹ * ∫ ξ, ν ξ * ahKer w ξ := by
    rw [ahI_integral_comp_inv (fun ζ => nxMu2t ν ζ * ahKer w⁻¹ ζ), ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ξ hξ
    exact hpt ξ hξ.1 hξ.2.1 hξ.2.2
  rw [ahVar, ahVar, hint]
  ring

/-- First variation for coefficients vanishing in the unit disc. -/
theorem ah_first_variation_outside (w : ℂ) :
    ∀ η > 0, ∃ δ > 0, ∀ (ν F : ℂ → ℂ) (ε : ℝ), 0 < ε → ε ≤ δ → IsBeltramiCoeff ν univ ε →
      (∀ ζ : ℂ, ‖ζ‖ < 1 → ν ζ = 0) → IsNormalizedSolution F ν →
      ‖F w - w - ahVar ν w‖ ≤ η * ε := by
  intro η hη
  by_cases hw : w = 0
  · refine ⟨1, one_pos, fun ν F ε hε _ _ _ hF => ?_⟩
    have hV : ahVar ν 0 = 0 := by simp [ahVar, ahKer]
    rw [hw, hF.2.2.1, hV, sub_zero, sub_zero, norm_zero]
    positivity
  set u : ℂ := w⁻¹ with hu
  have hu0 : u ≠ 0 := inv_ne_zero hw
  have hun : 0 < ‖u‖ := norm_pos_iff.2 hu0
  obtain ⟨C₀, δ₀, hδ₀, hCFV⟩ := ah_first_variation_compact (max 1 ‖u‖)
  set C₁ : ℝ := max C₀ 1 with hC₁
  have hC₁1 : 1 ≤ C₁ := le_max_right _ _
  have hC₁0 : 0 < C₁ := lt_of_lt_of_le one_pos hC₁1
  set A : ℝ := C₁ * (1 + ‖u‖) with hA
  have hA0 : 0 < A := by positivity
  have hCA : C₁ ≤ A := by
    rw [hA]
    nlinarith [norm_nonneg u]
  set S : ℝ := 2 * A ^ 2 / ‖u‖ + A with hS
  have hS0 : 0 < S := by positivity
  set M : ℝ := 2 * S / ‖u‖ ^ 2 with hM
  have hM0 : 0 < M := by positivity
  refine ⟨min δ₀ (min (1 / 2) (min (‖u‖ / (2 * A)) (η / M))),
    lt_min hδ₀ (lt_min (by norm_num) (lt_min (by positivity) (by positivity))), ?_⟩
  intro ν F ε hε hεδ hν hν0 hF
  have hεδ₀ : ε ≤ δ₀ := hεδ.trans (min_le_left _ _)
  have hε2 : ε ≤ 1 / 2 := hεδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεA : ε ≤ ‖u‖ / (2 * A) :=
    hεδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεM : ε ≤ η / M :=
    hεδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hG := ahI_invConj_isNormalizedSolution hε.le (by linarith) hν hν0 hF
  have hνt : IsBeltramiCoeff (nxMu2t ν) univ ε := (nx_mu2t_compact hε.le hν).1
  obtain ⟨hunif, hvar⟩ := hCFV (nxMu2t ν) (nxInvConj F) ε hεδ₀ hνt
    (fun ζ hζ => ahI_mu2t_eq_zero ν (lt_of_le_of_lt (le_max_left _ _) hζ)) hG
  -- `a = F̃ u`, `V = V[ν̃](u)`, `E = a - u - V`
  set a : ℂ := nxInvConj F u with ha
  set V : ℂ := ahVar (nxMu2t ν) u with hV
  have h1 : ‖a - u‖ ≤ A * ε := by
    calc ‖a - u‖ ≤ C₀ * ε * (1 + ‖u‖) := hunif u
      _ ≤ C₁ * ε * (1 + ‖u‖) := by gcongr; exact le_max_left _ _
      _ = A * ε := by rw [hA]; ring
  have h2 : ‖a - u - V‖ ≤ A * ε ^ 2 := by
    calc ‖a - u - V‖ ≤ C₀ * ε ^ 2 := hvar u (le_max_right _ _)
      _ ≤ C₁ * ε ^ 2 := by gcongr; exact le_max_left _ _
      _ ≤ A * ε ^ 2 := by gcongr
  have hVb : ‖V‖ ≤ 2 * A * ε := by
    have heq : V = (a - u) - (a - u - V) := by ring
    calc ‖V‖ = ‖(a - u) - (a - u - V)‖ := by rw [← heq]
      _ ≤ ‖a - u‖ + ‖a - u - V‖ := norm_sub_le _ _
      _ ≤ A * ε + A * ε ^ 2 := add_le_add h1 h2
      _ ≤ 2 * A * ε := by
        nlinarith [mul_le_mul_of_nonneg_left (show ε ≤ 1 by linarith) (mul_pos hA0 hε).le]
  have hAε : A * ε ≤ ‖u‖ / 2 := by
    rw [le_div_iff₀ (by positivity)] at hεA
    linarith
  have han : ‖u‖ / 2 ≤ ‖a‖ := by
    have h3 : ‖u‖ - ‖a‖ ≤ ‖a - u‖ := by
      rw [norm_sub_rev]
      exact norm_sub_norm_le u a
    linarith
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at han
    linarith
  have hFw : F w = a⁻¹ := by rw [ha, hu, nxInvConj, inv_inv, inv_inv]
  have hwu : w = u⁻¹ := by rw [hu, inv_inv]
  have hker : ahVar ν w = -(w ^ 2) * V := by
    have h4 := ahI_var_invConj hν0 hw
    rw [← hu, ← hV] at h4
    rw [h4]
    field_simp
  -- `(F w - w - V[ν](w)) · a u = V (a - u)/u - E`
  have hid : (F w - w - ahVar ν w) * (a * u) = V * (a - u) / u - (a - u - V) := by
    rw [hker, hFw, hwu]
    field_simp
    ring
  have hX : ‖F w - w - ahVar ν w‖ * (‖a‖ * ‖u‖) ≤ ε ^ 2 * S := by
    rw [← norm_mul, ← norm_mul, hid]
    calc ‖V * (a - u) / u - (a - u - V)‖ ≤ ‖V * (a - u) / u‖ + ‖a - u - V‖ := norm_sub_le _ _
      _ = ‖V‖ * ‖a - u‖ / ‖u‖ + ‖a - u - V‖ := by rw [norm_div, norm_mul]
      _ ≤ (2 * A * ε) * (A * ε) / ‖u‖ + A * ε ^ 2 := by gcongr
      _ = ε ^ 2 * S := by rw [hS]; ring
  have hX2 : ‖F w - w - ahVar ν w‖ ≤ ε ^ 2 * M := by
    have h5 : ‖F w - w - ahVar ν w‖ * (‖u‖ ^ 2 / 2) ≤ ε ^ 2 * S := by
      calc ‖F w - w - ahVar ν w‖ * (‖u‖ ^ 2 / 2) = ‖F w - w - ahVar ν w‖ * (‖u‖ / 2 * ‖u‖) := by ring
        _ ≤ ‖F w - w - ahVar ν w‖ * (‖a‖ * ‖u‖) := by gcongr
        _ ≤ ε ^ 2 * S := hX
    rw [← le_div_iff₀ (by positivity)] at h5
    calc ‖F w - w - ahVar ν w‖ ≤ ε ^ 2 * S / (‖u‖ ^ 2 / 2) := h5
      _ = ε ^ 2 * M := by rw [hM]; field_simp
  have hMε : M * ε ≤ η := by
    rw [le_div_iff₀ hM0] at hεM
    linarith
  calc ‖F w - w - ahVar ν w‖ ≤ ε ^ 2 * M := hX2
    _ = ε * (M * ε) := by ring
    _ ≤ ε * η := by gcongr
    _ = η * ε := by ring

/-! ### Piece PUSH — the pushed-forward inner coefficient has the same first variation -/

/-- The kernel `ζ ↦ w(w-1)/(ζ(ζ-1)(ζ-w))` is measurable. -/
theorem ahP_ker_measurable (w : ℂ) : Measurable (ahKer w) := by
  unfold ahKer
  fun_prop

/-- The kernel is continuous off its three poles `0, 1, w`, hence at almost every point. -/
theorem ahP_ker_continuousAt_ae (w : ℂ) : ∀ᵐ z : ℂ, ContinuousAt (ahKer w) z := by
  have h0 : ∀ᵐ z : ℂ, z ∉ ({0, 1, w} : Set ℂ) :=
    measure_eq_zero_iff_ae_notMem.1 ((Set.toFinite _).measure_zero _)
  filter_upwards [h0] with z hz
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz
  obtain ⟨h0, h1, hw⟩ := hz
  have hne : z * (z - 1) * (z - w) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.2 h1)) (sub_ne_zero.2 hw)
  show ContinuousAt (fun ζ => w * (w - 1) / (ζ * (ζ - 1) * (ζ - w))) z
  exact continuousAt_const.div (by fun_prop) hne

/-- The outer part `nxMu2 ν` of a Beltrami coefficient is a Beltrami coefficient with the same bound. -/
theorem ahP_mu2_beltrami {ν : ℂ → ℂ} {ε : ℝ} (hν : IsBeltramiCoeff ν univ ε) :
    IsBeltramiCoeff (nxMu2 ν) univ ε := by
  refine ⟨hν.1.indicator isOpen_ball.measurableSet.compl, ?_⟩
  filter_upwards [hν.2] with z hz
  exact (norm_indicator_le_norm_self _ _).trans hz

/-- The normalized solution of a coefficient vanishing on `Δ` is holomorphic and injective on `Δ`. -/
theorem ahP_conformal {ν G : ℂ → ℂ} (hG : IsNormalizedSolution G (nxMu2 ν)) :
    DifferentiableOn ℂ G unitDisc ∧ InjOn G unitDisc := by
  obtain ⟨⟨K, hK⟩, -, -, -, hd⟩ := hG
  have hKD : IsKQC G unitDisc K := nx_isKQC_restrict hK isOpen_ball (subset_univ _)
  have h0 : ∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation G z = 0 := by
    filter_upwards [ae_restrict_of_ae hd, self_mem_ae_restrict isOpen_ball.measurableSet]
      with z hz hzD
    rw [hz, nxMu2]
    exact indicator_of_notMem (fun h : z ∈ unitDiscᶜ => h hzD) ν
  exact ⟨nx_differentiableOn_of_dilatation_zero hKD h0, hK.2.2.1.2.1.mono (subset_univ _)⟩

/-- Change of variables through a holomorphic injective map, Bochner form:
`∫_{f(U)} g = ∫_U |f'|² • (g ∘ f)`. -/
theorem ahP_integral_image {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hd : DifferentiableOn ℂ f U) (hi : InjOn f U) (g : ℂ → E) :
    ∫ w in f '' U, g w = ∫ z in U, (‖deriv f z‖ ^ 2) • g (f z) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet
    (fun z hz => ((hd.differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt) hi g]
  refine setIntegral_congr_fun hU.measurableSet fun z _ => ?_
  simp only [det_restrictScalars_toSpanSingleton]
  rw [abs_of_nonneg (sq_nonneg _)]

/-- Change of variables through a holomorphic injective map, integrability form. -/
theorem ahP_integrableOn_image {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hd : DifferentiableOn ℂ f U) (hi : InjOn f U) (g : ℂ → E) :
    IntegrableOn g (f '' U) ↔ IntegrableOn (fun z => (‖deriv f z‖ ^ 2) • g (f z)) U := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hU.measurableSet
    (fun z hz => ((hd.differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt) hi g]
  refine integrableOn_congr_fun (fun z _ => ?_) hU.measurableSet
  simp only [det_restrictScalars_toSpanSingleton]
  rw [abs_of_nonneg (sq_nonneg _)]

/-- Cauchy's estimate: a holomorphic map of `Δ` that is `r`-close to the identity on `Δ` has
`|F'(z) - 1| ≤ r / ((1 - |z|)/2)`. -/
theorem ahP_norm_deriv_sub_one_le {F : ℂ → ℂ} {r : ℝ} (hF : DifferentiableOn ℂ F unitDisc)
    (hb : ∀ z : ℂ, ‖z‖ < 1 → ‖F z - z‖ ≤ r) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖deriv F z - 1‖ ≤ r / ((1 - ‖z‖) / 2) := by
  have hR : 0 < (1 - ‖z‖) / 2 := by linarith
  have hsub : closedBall z ((1 - ‖z‖) / 2) ⊆ unitDisc := by
    intro ζ hζ
    rw [mem_closedBall, dist_eq_norm] at hζ
    rw [unitDisc, mem_ball_zero_iff]
    calc ‖ζ‖ = ‖(ζ - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖ζ - z‖ + ‖z‖ := norm_add_le _ _
      _ < 1 := by linarith
  have hzD : z ∈ unitDisc := mem_ball_zero_iff.2 hz
  have hFz : DifferentiableAt ℂ F z := hF.differentiableAt (isOpen_ball.mem_nhds hzD)
  have hd : DiffContOnCl ℂ (fun ζ => F ζ - ζ) (ball z ((1 - ‖z‖) / 2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z hR.ne']
    exact (hF.mono hsub).sub differentiableOn_id
  have hC : ∀ ζ ∈ sphere z ((1 - ‖z‖) / 2), ‖F ζ - ζ‖ ≤ r := fun ζ hζ =>
    hb ζ (mem_ball_zero_iff.1 (hsub (sphere_subset_closedBall hζ)))
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hd hC
  have hder : deriv (fun ζ => F ζ - ζ) z = deriv F z - 1 :=
    (hFz.hasDerivAt.sub (hasDerivAt_id' z)).deriv
  rwa [hder] at h

/-- For `G` holomorphic and injective on `Δ` and `K` integrable, `z ↦ K(G z) G'(z)²` is integrable
on `Δ`, and `∫_Δ |K(G z) G'(z)²| = ∫_{G(Δ)} |K|`. -/
theorem ahP_pull {K G : ℂ → ℂ} (hKm : Measurable K) (hKi : Integrable K)
    (hd : DifferentiableOn ℂ G unitDisc) (hi : InjOn G unitDisc) :
    IntegrableOn (fun z => K (G z) * deriv G z ^ 2) unitDisc ∧
      ∫ z in unitDisc, ‖K (G z) * deriv G z ^ 2‖ = ∫ ζ in G '' unitDisc, ‖K ζ‖ := by
  have hGm : AEMeasurable G (volume.restrict unitDisc) :=
    hd.continuousOn.aemeasurable isOpen_ball.measurableSet
  have hmeas : AEStronglyMeasurable (fun z => K (G z) * deriv G z ^ 2)
      (volume.restrict unitDisc) :=
    ((hKm.comp_aemeasurable hGm).mul
      ((measurable_deriv G).pow_const 2).aemeasurable).aestronglyMeasurable
  constructor
  · have h := (ahP_integrableOn_image isOpen_ball hd hi K).1 hKi.integrableOn
    refine h.congr' hmeas (Eventually.of_forall fun z => ?_)
    rw [norm_smul, Real.norm_of_nonneg (sq_nonneg _), norm_mul, norm_pow, mul_comm]
  · rw [ahP_integral_image (U := unitDisc) isOpen_ball hd hi (fun ζ => ‖K ζ‖)]
    refine setIntegral_congr_fun isOpen_ball.measurableSet fun z _ => ?_
    simp only [smul_eq_mul, norm_mul, norm_pow]
    ring

/-- Change of variables for the pushed-forward coefficient:
`∫ nxPush ν G · K = ∫_Δ ν(z) K(G z) G'(z)² dz` (the unimodular factor and the Jacobian `|G'|²`
combine into `G'²`). -/
theorem ahP_push_integral {ν G K : ℂ → ℂ} (hd : DifferentiableOn ℂ G unitDisc)
    (hi : InjOn G unitDisc) :
    ∫ ζ, nxPush ν G ζ * K ζ = ∫ z in unitDisc, ν z * (K (G z) * deriv G z ^ 2) := by
  have hc : IsConformalOnto G unitDisc (G '' unitDisc) := ⟨hd, hi, rfl⟩
  have hDo : IsOpen (G '' unitDisc) := hc.isOpen isOpen_ball
  have hpush : ∀ ζ, nxPush ν G ζ * K ζ = (G '' unitDisc).indicator
      (fun ζ => ν (Function.invFunOn G unitDisc ζ) *
        (conj (deriv (Function.invFunOn G unitDisc) ζ) /
          deriv (Function.invFunOn G unitDisc) ζ) * K ζ) ζ := by
    intro ζ
    by_cases hζ : ζ ∈ G '' unitDisc
    · simp only [nxPush, Set.indicator_of_mem hζ]
    · simp only [nxPush, Set.indicator_of_notMem hζ, zero_mul]
  simp_rw [hpush]
  rw [integral_indicator hDo.measurableSet, ahP_integral_image (U := unitDisc) isOpen_ball hd hi]
  refine setIntegral_congr_fun isOpen_ball.measurableSet fun z hz => ?_
  have hgz : Function.invFunOn G unitDisc (G z) = z := hi.leftInvOn_invFunOn hz
  have hmul : deriv (Function.invFunOn G unitDisc) (G z) * deriv G z = 1 :=
    t1_deriv_invFunOn_mul isOpen_ball hc hz
  have hne : deriv G z ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hd hi hz
  have hg' : deriv (Function.invFunOn G unitDisc) (G z) = (deriv G z)⁻¹ :=
    eq_inv_of_mul_eq_one_left hmul
  simp only [hgz, hg']
  rw [Complex.real_smul]
  have hc' : conj (deriv G z) ≠ 0 := (map_ne_zero _).2 hne
  have hn : ((‖deriv G z‖ ^ 2 : ℝ) : ℂ) = deriv G z * conj (deriv G z) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hn, map_inv₀]
  field_simp

/-- The basic estimate:
`|V[nxPush ν G](w) - V[ν 1_Δ](w)| ≤ (1/π) ε ∫_Δ |K_w(G z) G'(z)² - K_w(z)| dz`. -/
theorem ahP_var_sub_le {w : ℂ} {ν G : ℂ → ℂ} {ε : ℝ} (hν : IsBeltramiCoeff ν univ ε)
    (hKi : Integrable (ahKer w)) (hd : DifferentiableOn ℂ G unitDisc) (hi : InjOn G unitDisc) :
    ‖ahVar (nxPush ν G) w - ahVar (unitDisc.indicator ν) w‖ ≤
      1 / π * (ε * ∫ z in unitDisc, ‖ahKer w (G z) * deriv G z ^ 2 - ahKer w z‖) := by
  have hνm : AEStronglyMeasurable ν (volume.restrict unitDisc) := by
    have h := hν.1
    rw [Measure.restrict_univ] at h
    exact h.restrict
  have hνb : ∀ᵐ z ∂(volume.restrict unitDisc), ‖ν z‖ ≤ ε := by
    have h := hν.2
    rw [Measure.restrict_univ] at h
    exact ae_restrict_of_ae h
  obtain ⟨hYi, -⟩ := ahP_pull (ahP_ker_measurable w) hKi hd hi
  have hKiD : IntegrableOn (ahKer w) unitDisc := hKi.integrableOn
  have h1 : ahVar (nxPush ν G) w =
      -(1 / π : ℂ) * ∫ z in unitDisc, ν z * (ahKer w (G z) * deriv G z ^ 2) := by
    rw [ahVar, ahP_push_integral hd hi]
  have h2 : ahVar (unitDisc.indicator ν) w =
      -(1 / π : ℂ) * ∫ z in unitDisc, ν z * ahKer w z := by
    have hind : ∀ ζ, unitDisc.indicator ν ζ * ahKer w ζ =
        unitDisc.indicator (fun z => ν z * ahKer w z) ζ := by
      intro ζ
      by_cases hζ : ζ ∈ unitDisc
      · simp only [Set.indicator_of_mem hζ]
      · simp only [Set.indicator_of_notMem hζ, zero_mul]
    rw [ahVar]
    simp_rw [hind]
    rw [integral_indicator (s := unitDisc) measurableSet_ball]
  have hI1 : IntegrableOn (fun z => ν z * (ahKer w (G z) * deriv G z ^ 2)) unitDisc :=
    hYi.bdd_mul hνm hνb
  have hI2 : IntegrableOn (fun z => ν z * ahKer w z) unitDisc := hKiD.bdd_mul hνm hνb
  rw [h1, h2, ← mul_sub, ← integral_sub hI1 hI2, norm_mul, norm_neg]
  have hpi : ‖(1 / π : ℂ)‖ = 1 / π := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hpi]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le ((hYi.sub hKiD).norm.const_mul ε) ?_
  filter_upwards [hνb] with z hz
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)

/-- **Scheffé-type `L¹` convergence.**  Let `G_t` be holomorphic and injective on `Δ` with
`|G_t z - z| ≤ r_t` on `Δ`, `r_t → 0` along a countably generated filter.  Then
`∫_Δ |K(G_t z) G_t'(z)² - K(z)| dz → 0` for every measurable integrable `K` that is continuous a.e.:
pointwise convergence comes from Cauchy's estimate, and the `L¹` norms
`∫_Δ |K(G_t z)| |G_t'(z)|² = ∫_{G_t(Δ)} |K| ≤ ∫_{B(0, 1 + r_t)} |K|` tend to at most `∫_Δ |K|`, so
dominated convergence for `|f_t - K| - |f_t|` (bounded by `|K|`) squeezes the limit to `0`. -/
theorem ahP_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {K : ℂ → ℂ}
    (hKm : Measurable K) (hKi : Integrable K) (hKc : ∀ᵐ z, ContinuousAt K z)
    {G : ι → ℂ → ℂ} {r : ι → ℝ} (hr : Tendsto r l (𝓝 0))
    (hG : ∀ᶠ t in l, DifferentiableOn ℂ (G t) unitDisc ∧ InjOn (G t) unitDisc ∧
      ∀ z : ℂ, ‖z‖ < 1 → ‖G t z - z‖ ≤ r t) :
    Tendsto (fun t => ∫ z in unitDisc, ‖K (G t z) * deriv (G t) z ^ 2 - K z‖) l (𝓝 0) := by
  -- pointwise convergence of the pulled-back kernels
  have hlim : ∀ᵐ z ∂(volume.restrict unitDisc),
      Tendsto (fun t => K (G t z) * deriv (G t) z ^ 2) l (𝓝 (K z)) := by
    filter_upwards [ae_restrict_of_ae hKc, self_mem_ae_restrict isOpen_ball.measurableSet]
      with z hzc hzD
    have hz : ‖z‖ < 1 := mem_ball_zero_iff.1 hzD
    have hGz : Tendsto (fun t => G t z) l (𝓝 z) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hr
      filter_upwards [hG] with t ht
      exact ht.2.2 z hz
    have hdG : Tendsto (fun t => deriv (G t) z) l (𝓝 1) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hr' : Tendsto (fun t => r t / ((1 - ‖z‖) / 2)) l (𝓝 0) := by
        simpa using hr.div_const ((1 - ‖z‖) / 2)
      refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hr'
      filter_upwards [hG] with t ht
      exact ahP_norm_deriv_sub_one_le ht.1 ht.2.2 hz
    have h := (hzc.tendsto.comp hGz).mul (hdG.pow 2)
    simpa using h
  -- `r_t ≥ 0` eventually
  have hr0 : ∀ᶠ t in l, 0 ≤ r t := by
    filter_upwards [hG] with t ht
    exact (norm_nonneg _).trans (ht.2.2 0 (by simp))
  -- integrability and the `L¹` norms of the pulled-back kernels
  have hpull : ∀ᶠ t in l, IntegrableOn (fun z => K (G t z) * deriv (G t) z ^ 2) unitDisc ∧
      ∫ z in unitDisc, ‖K (G t z) * deriv (G t) z ^ 2‖ = ∫ ζ in G t '' unitDisc, ‖K ζ‖ := by
    filter_upwards [hG] with t ht
    exact ahP_pull hKm hKi ht.1 ht.2.1
  -- the reverse triangle inequality `||f - K| - |f|| ≤ |K|`
  have htri : ∀ a b : ℂ, ‖‖a - b‖ - ‖a‖‖ ≤ ‖b‖ := by
    intro a b
    rw [Real.norm_eq_abs]
    have h := abs_norm_sub_norm_le (a - b) a
    rwa [sub_sub_cancel_left, norm_neg] at h
  -- dominated convergence for `φ_t = |f_t - K| - |f_t|`
  have hA : Tendsto (fun t => ∫ z in unitDisc,
      (‖K (G t z) * deriv (G t) z ^ 2 - K z‖ - ‖K (G t z) * deriv (G t) z ^ 2‖)) l
      (𝓝 (∫ z in unitDisc, -‖K z‖)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z => ‖K z‖) ?_ ?_
      hKi.norm.integrableOn ?_
    · filter_upwards [hpull] with t ht
      exact (ht.1.aestronglyMeasurable.sub hKi.aestronglyMeasurable.restrict).norm.sub
        ht.1.aestronglyMeasurable.norm
    · exact Eventually.of_forall fun t => Eventually.of_forall fun z => htri _ _
    · filter_upwards [hlim] with z hz
      have h := ((hz.sub (tendsto_const_nhds : Tendsto (fun _ : ι => K z) l (𝓝 (K z)))).norm).sub
        hz.norm
      simpa using h
  -- dominated convergence for `|K| 1_{B(0, 1 + r_t)}`
  have hsph : ∀ᵐ ζ : ℂ, ζ ∉ sphere (0 : ℂ) 1 :=
    measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_sphere volume (0 : ℂ) 1)
  have hB : Tendsto (fun t => ∫ ζ, (ball (0 : ℂ) (1 + r t)).indicator (fun ζ => ‖K ζ‖) ζ) l
      (𝓝 (∫ ζ, unitDisc.indicator (fun ζ => ‖K ζ‖) ζ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z => ‖K z‖) ?_ ?_ hKi.norm ?_
    · exact Eventually.of_forall fun t =>
        hKi.norm.aestronglyMeasurable.indicator measurableSet_ball
    · refine Eventually.of_forall fun t => Eventually.of_forall fun ζ => ?_
      exact (norm_indicator_le_norm_self _ _).trans (norm_norm _).le
    · filter_upwards [hsph] with ζ hζ
      have hζ1 : ‖ζ‖ ≠ 1 := fun h => hζ (mem_sphere_zero_iff_norm.2 h)
      rcases lt_or_gt_of_ne hζ1 with h1 | h1
      · have hζD : ζ ∈ unitDisc := mem_ball_zero_iff.2 h1
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hr0] with t ht
        rw [Set.indicator_of_mem hζD, Set.indicator_of_mem (mem_ball_zero_iff.2 (by linarith))]
      · have hζD : ζ ∉ unitDisc := fun h => by
          have := mem_ball_zero_iff.1 h
          linarith
        have hev : ∀ᶠ t in l, r t < ‖ζ‖ - 1 := hr (Iio_mem_nhds (by linarith))
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with t ht
        rw [Set.indicator_of_notMem hζD, Set.indicator_of_notMem]
        intro h
        have := mem_ball_zero_iff.1 h
        linarith
  -- the squeeze
  have hsum := hA.add hB
  rw [integral_indicator (s := unitDisc) measurableSet_ball, integral_neg, neg_add_cancel] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun t => integral_nonneg fun z => norm_nonneg _) ?_
  filter_upwards [hG, hpull] with t ht hp
  have hφi : IntegrableOn (fun z => ‖K (G t z) * deriv (G t) z ^ 2 - K z‖ -
      ‖K (G t z) * deriv (G t) z ^ 2‖) unitDisc := by
    refine hKi.norm.integrableOn.mono' ?_ (Eventually.of_forall fun z => htri _ _)
    exact (hp.1.aestronglyMeasurable.sub hKi.aestronglyMeasurable.restrict).norm.sub
      hp.1.aestronglyMeasurable.norm
  have hsplit : ∫ z in unitDisc, ‖K (G t z) * deriv (G t) z ^ 2 - K z‖ =
      (∫ z in unitDisc, (‖K (G t z) * deriv (G t) z ^ 2 - K z‖ - ‖K (G t z) * deriv (G t) z ^ 2‖)) +
        ∫ z in unitDisc, ‖K (G t z) * deriv (G t) z ^ 2‖ := by
    rw [← integral_add hφi hp.1.norm]
    congr 1
    funext z
    ring
  rw [hsplit, hp.2]
  refine add_le_add le_rfl ?_
  rw [integral_indicator measurableSet_ball]
  refine setIntegral_mono_set hKi.norm.integrableOn
    (Eventually.of_forall fun ζ => norm_nonneg _) (LE.le.eventuallySubset ?_)
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_ball_zero_iff]
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have h := ht.2.2 z hz1
  calc ‖G t z‖ = ‖z + (G t z - z)‖ := by rw [add_sub_cancel]
    _ ≤ ‖z‖ + ‖G t z - z‖ := norm_add_le _ _
    _ < 1 + r t := by linarith

/-- `V[nxPush ν G](w) = V[ν·1_Δ](w) + o(ε)` for the normalized solution `G` of the outer part. -/
theorem ah_push_variation (w : ℂ) :
    ∀ η > 0, ∃ δ > 0, ∀ (ν G : ℂ → ℂ) (ε : ℝ), 0 < ε → ε ≤ δ → IsBeltramiCoeff ν univ ε →
      IsNormalizedSolution G (nxMu2 ν) →
      ‖ahVar (nxPush ν G) w - ahVar (unitDisc.indicator ν) w‖ ≤ η * ε := by
  intro η hη
  by_contra hcon
  push Not at hcon
  obtain ⟨C, δ₀, hδ₀, hC⟩ := ah_outside_uniform
  have hKi : Integrable (ahKer w) := ah_ker_integrable w
  choose ν G ε hε hεδ hν hGs hbad using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  have hεt : Tendsto ε atTop (𝓝 0) :=
    squeeze_zero (fun n => (hε n).le) hεδ tendsto_one_div_add_atTop_nhds_zero_nat
  have hr : Tendsto (fun n => C * ε n) atTop (𝓝 0) := by
    simpa using hεt.const_mul C
  have hG : ∀ᶠ n in atTop, DifferentiableOn ℂ (G n) unitDisc ∧ InjOn (G n) unitDisc ∧
      ∀ z : ℂ, ‖z‖ < 1 → ‖G n z - z‖ ≤ C * ε n := by
    filter_upwards [hεt.eventually (eventually_le_nhds hδ₀)] with n hn
    obtain ⟨hd, hi⟩ := ahP_conformal (hGs n)
    refine ⟨hd, hi, fun z hz => hC _ _ _ hn (ahP_mu2_beltrami (hν n)) ?_ (hGs n) z hz.le⟩
    intro ζ hζ
    rw [nxMu2]
    exact indicator_of_notMem (fun h : ζ ∈ unitDiscᶜ => h (mem_ball_zero_iff.2 hζ)) _
  have key := ahP_tendsto (ahP_ker_measurable w) hKi (ahP_ker_continuousAt_ae w) hr hG
  have hev : ∀ᶠ n in atTop,
      ∫ z in unitDisc, ‖ahKer w (G n z) * deriv (G n) z ^ 2 - ahKer w z‖ < π * η :=
    key.eventually (eventually_lt_nhds (mul_pos Real.pi_pos hη))
  obtain ⟨n, hn⟩ := hev.exists
  obtain ⟨hd, hi⟩ := ahP_conformal (hGs n)
  have h1 := ahP_var_sub_le (hν n) hKi hd hi
  have h2 : 1 / π * (ε n * ∫ z in unitDisc, ‖ahKer w (G n z) * deriv (G n) z ^ 2 - ahKer w z‖) ≤
      η * ε n := by
    calc 1 / π * (ε n * ∫ z in unitDisc, ‖ahKer w (G n z) * deriv (G n) z ^ 2 - ahKer w z‖)
        ≤ 1 / π * (ε n * (π * η)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn.le (hε n).le) (by positivity)
      _ = η * ε n := by
          field_simp
  linarith [hbad n]

/-! ### Piece FV — the first variation in general -/

/-- Cutting a Beltrami coefficient down to a measurable set keeps it a Beltrami coefficient with the same
bound. -/
theorem ahF_indicator_beltrami {ν : ℂ → ℂ} {ε : ℝ} {s : Set ℂ} (hs : MeasurableSet s)
    (hν : IsBeltramiCoeff ν univ ε) : IsBeltramiCoeff (s.indicator ν) univ ε := by
  obtain ⟨hm, hb⟩ := hν
  refine ⟨hm.indicator hs, ?_⟩
  filter_upwards [hb] with z hz
  exact (norm_indicator_le_norm_self ν z).trans hz

/-- The outer part `nxMu2 ν` of a Beltrami coefficient is one, with the same bound. -/
theorem ahF_nxMu2_beltrami {ν : ℂ → ℂ} {ε : ℝ} (hν : IsBeltramiCoeff ν univ ε) :
    IsBeltramiCoeff (nxMu2 ν) univ ε :=
  ahF_indicator_beltrami (s := unitDiscᶜ) measurableSet_ball.compl hν

/-- The outer part `nxMu2 ν` vanishes in the unit disc. -/
theorem ahF_nxMu2_vanish (ν : ℂ → ℂ) : ∀ ζ : ℂ, ‖ζ‖ < 1 → nxMu2 ν ζ = 0 := by
  intro ζ hζ
  rw [nxMu2]
  exact indicator_of_notMem (fun h : ζ ∈ unitDiscᶜ => h (mem_ball_zero_iff.2 hζ)) ν

/-- The inner and the outer part add up to the coefficient: `1 · (ν·1_Δ) + nxMu2 ν = ν`. -/
theorem ahF_split (ν : ℂ → ℂ) : (fun ζ => 1 * unitDisc.indicator ν ζ + nxMu2 ν ζ) = ν := by
  funext ζ
  rw [one_mul, nxMu2, Set.indicator_self_add_compl_apply]

/-- The first variation splits along `ν = ν·1_Δ + nxMu2 ν` (linearity of `V`). -/
theorem ahF_var_split (w : ℂ) {ν : ℂ → ℂ} {ε : ℝ} (hν : IsBeltramiCoeff ν univ ε) :
    ahVar (unitDisc.indicator ν) w + ahVar (nxMu2 ν) w = ahVar ν w := by
  have h : ahVar (fun ζ => 1 * unitDisc.indicator ν ζ + nxMu2 ν ζ) w =
      1 * ahVar (unitDisc.indicator ν) w + ahVar (nxMu2 ν) w :=
    ah_var_linear (ahF_indicator_beltrami (s := unitDisc) measurableSet_ball hν)
      (ahF_nxMu2_beltrami hν) 1 w
  rw [ahF_split, one_mul] at h
  exact h.symm

/-- The normalized solution `G` of the outer part `nxMu2 ν` is conformal on `Δ` (its dilatation vanishes
there), a homeomorphism of `ℂ`, quasiconformal on `ℂ ∖ {0}`, and `G(Δ)` is bounded. -/
theorem ahF_outer {ν G : ℂ → ℂ} (hG : IsNormalizedSolution G (nxMu2 ν)) :
    IsConformalOnto G unitDisc (G '' unitDisc) ∧ IsHomeomorphOnto G univ univ ∧
      (∃ K, IsKQC G {0}ᶜ K) ∧ Bornology.IsBounded (G '' unitDisc) := by
  obtain ⟨⟨K, hK⟩, hs, -, -, hd⟩ := hG
  have hh : IsHomeomorphOnto G univ univ := by
    have h := hK.2.2.1
    rwa [hs] at h
  have hΔo : IsOpen unitDisc := isOpen_ball
  have hKΔ : IsKQC G unitDisc K := nx_isKQC_restrict hK hΔo (subset_univ _)
  have h0 : ∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation G z = 0 := by
    rw [ae_restrict_iff' hΔo.measurableSet]
    filter_upwards [hd] with z hz hzΔ
    rw [hz]
    exact ahF_nxMu2_vanish ν z (mem_ball_zero_iff.1 hzΔ)
  have hcont : Continuous G := continuousOn_univ.1 hh.1
  refine ⟨⟨nx_differentiableOn_of_dilatation_zero hKΔ h0, hK.2.2.1.2.1.mono (subset_univ _), rfl⟩, hh,
    ⟨K, nx_isKQC_restrict hK isOpen_compl_singleton (subset_univ _)⟩, ?_⟩
  exact ((isCompact_closedBall (0 : ℂ) 1).image hcont).isBounded.subset
    (image_mono ball_subset_closedBall)

/-- The pushed-forward inner coefficient `nxPush ν G` is a Beltrami coefficient with the bound of `ν`. -/
theorem ahF_push_beltrami {ν G : ℂ → ℂ} {ε : ℝ} (hε : 0 ≤ ε) (hν : IsBeltramiCoeff ν univ ε)
    (hG : IsNormalizedSolution G (nxMu2 ν)) : IsBeltramiCoeff (nxPush ν G) univ ε := by
  obtain ⟨hc, -, -, hb⟩ := ahF_outer hG
  exact (nx_push_compact hε hν hc hb).1

/-- If `|G| ≤ R` on `Δ`, the pushed-forward coefficient `nxPush ν G` vanishes for `|ζ| > R`. -/
theorem ahF_push_support {ν G : ℂ → ℂ} {R : ℝ} (hR : ∀ z ∈ unitDisc, ‖G z‖ ≤ R) :
    ∀ ζ : ℂ, R < ‖ζ‖ → nxPush ν G ζ = 0 := by
  intro ζ hζ
  rw [nxPush]
  refine indicator_of_notMem ?_ _
  rintro ⟨z, hz, rfl⟩
  exact absurd (hR z hz) (not_le.2 hζ)

/-- `F^ν = F^λ ∘ G` for `G = F^{nxMu2 ν}` and `λ = nxPush ν G` (`nx_comp_dilatation` and Theorem 13.5). -/
theorem ahF_comp {ν F G H : ℂ → ℂ} (hF : IsNormalizedSolution F ν)
    (hG : IsNormalizedSolution G (nxMu2 ν)) (hH : IsNormalizedSolution H (nxPush ν G)) :
    F = H ∘ G := by
  obtain ⟨hc, hh, ⟨K₂, hK₂⟩, -⟩ := ahF_outer hG
  obtain ⟨⟨KG, hKG⟩, hGs, hG0, hG1, hGd⟩ := hG
  obtain ⟨⟨KH, hKH⟩, hHs, hH0, hH1, hHd⟩ := hH
  obtain ⟨hFq, hFs, hF0, hF1, hFd⟩ := hF
  have hd : ∀ᵐ z, complexDilatation (H ∘ G) z = ν z :=
    nx_comp_dilatation hKH hHs hHd hh hK₂ hc hGd
  refine thm13_5_uniqueness_plane hFq ⟨_, thm7_1_comp hKG hKH (subset_univ _)⟩ hFs ?_ ?_ hF0 hF1
    ?_ ?_
  · rw [image_comp, hGs, hHs]
  · filter_upwards [hFd, hd] with z h1 h2
    rw [h1, h2]
  · rw [Function.comp_apply, hG0, hH0]
  · rw [Function.comp_apply, hG1, hH1]

/-- `|V[ρ](a) - V[ρ](w)| ≤ (1/π) ‖K_a - K_w‖₁ ε` when `|ρ| ≤ ε` a.e. -/
theorem ahF_var_sub_bound (a w : ℂ) {ρ : ℂ → ℂ} {ε : ℝ} (hρ : IsBeltramiCoeff ρ univ ε) :
    ‖ahVar ρ a - ahVar ρ w‖ ≤ (1 / π) * (∫ ζ, ‖ahKer a ζ - ahKer w ζ‖) * ε := by
  obtain ⟨hm, hb⟩ := hρ
  rw [Measure.restrict_univ] at hm hb
  have hia : Integrable (fun ζ => ρ ζ * ahKer a ζ) := (ah_ker_integrable a).bdd_mul hm hb
  have hiw : Integrable (fun ζ => ρ ζ * ahKer w ζ) := (ah_ker_integrable w).bdd_mul hm hb
  have hd : Integrable (fun ζ => ahKer a ζ - ahKer w ζ) :=
    (ah_ker_integrable a).sub (ah_ker_integrable w)
  have heq : ahVar ρ a - ahVar ρ w = -(1 / π : ℂ) * ∫ ζ, ρ ζ * (ahKer a ζ - ahKer w ζ) := by
    simp only [ahVar]
    rw [← mul_sub, ← integral_sub hia hiw]
    simp only [mul_sub]
  have hbound : ‖∫ ζ, ρ ζ * (ahKer a ζ - ahKer w ζ)‖ ≤ ε * ∫ ζ, ‖ahKer a ζ - ahKer w ζ‖ := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hd.norm.const_mul ε) ?_
    filter_upwards [hb] with ζ hζ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hζ (norm_nonneg _)
  have hπ : ‖-(1 / π : ℂ)‖ = 1 / π := by
    rw [norm_neg, norm_div, norm_one, Complex.norm_of_nonneg Real.pi_pos.le]
  rw [heq, norm_mul, hπ]
  calc 1 / π * ‖∫ ζ, ρ ζ * (ahKer a ζ - ahKer w ζ)‖
      ≤ 1 / π * (ε * ∫ ζ, ‖ahKer a ζ - ahKer w ζ‖) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 1 / π * (∫ ζ, ‖ahKer a ζ - ahKer w ζ‖) * ε := by ring

/-- **First variation** of normalized plane solutions: `F^ν(w) = w + V[ν](w) + o(‖ν‖∞)`. -/
theorem ah_first_variation (w : ℂ) :
    ∀ η > 0, ∃ δ > 0, ∀ (ν F : ℂ → ℂ) (ε : ℝ), 0 < ε → ε ≤ δ → IsBeltramiCoeff ν univ ε →
      IsNormalizedSolution F ν → ‖F w - w - ahVar ν w‖ ≤ η * ε := by
  intro η hη
  have hη4 : 0 < η / 4 := by positivity
  obtain ⟨C₀, δ₀, hδ₀, hout⟩ := ah_outside_uniform
  obtain ⟨C₁, δ₁, hδ₁, hcfv⟩ := ah_first_variation_compact (‖w‖ + 2)
  obtain ⟨δ₂, hδ₂, hfvo⟩ := ah_first_variation_outside w (η / 4) hη4
  obtain ⟨δ₃, hδ₃, hpush⟩ := ah_push_variation w (η / 4) hη4
  obtain ⟨δ₄, hδ₄, hkc⟩ := ah_ker_continuous w (η / 4) hη4
  have hI : 0 ≤ ∫ ζ, ‖ahKer w ζ‖ := integral_nonneg fun _ => norm_nonneg _
  have hπ1 : 1 / π ≤ 1 := by
    rw [div_le_one Real.pi_pos]
    linarith [Real.pi_gt_three]
  have hπ0 : 0 ≤ 1 / π := by positivity
  set A : ℝ := η / 4 + 1 / π * (∫ ζ, ‖ahKer w ζ‖) + 1 with hAdef
  have hA : 0 < A := by
    have : 0 ≤ 1 / π * (∫ ζ, ‖ahKer w ζ‖) := mul_nonneg hπ0 hI
    linarith
  have hC₀ : 0 < |C₀| + 1 := by positivity
  have hC₁ : 0 < |C₁| + 1 := by positivity
  refine ⟨min (1 / 2) (min δ₀ (min (1 / (|C₀| + 1)) (min δ₁ (min (η / 4 / (|C₁| + 1))
    (min δ₂ (min δ₃ (min (δ₄ / (2 * A)) (2 / A)))))))), ?_, ?_⟩
  · exact lt_min (by norm_num) (lt_min hδ₀ (lt_min (by positivity) (lt_min hδ₁
      (lt_min (by positivity) (lt_min hδ₂ (lt_min hδ₃ (lt_min (by positivity) (by positivity))))))))
  intro ν F ε hε hεδ hν hF
  simp only [le_min_iff] at hεδ
  obtain ⟨hε1, hε0, hεC₀, hεR, hεC₁, hε2, hε3, hε4, hε5⟩ := hεδ
  -- the outer solution `G = F^{nxMu2 ν}`, the pushed coefficient `ρ = nxPush ν G`, and `H = F^ρ`
  have hν₂ : IsBeltramiCoeff (nxMu2 ν) univ ε := ahF_nxMu2_beltrami hν
  obtain ⟨G, hG, -, -⟩ := thm13_7_normalized_existence hε.le (by linarith) hν₂
  have hρ : IsBeltramiCoeff (nxPush ν G) univ ε := ahF_push_beltrami hε.le hν hG
  obtain ⟨H, hH, -, -⟩ := thm13_7_normalized_existence hε.le (by linarith) hρ
  have hFHG : F = H ∘ G := ahF_comp hF hG hH
  -- `|G - id| ≤ C₀ ε ≤ 1` on `Δ`, so `ρ` vanishes off `B̄(0, |w| + 2)`
  have hGdisc : ∀ z ∈ unitDisc, ‖G z‖ ≤ ‖w‖ + 2 := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    have h := hout (nxMu2 ν) G ε hε0 hν₂ (ahF_nxMu2_vanish ν) hG z hz1.le
    have hC : C₀ * ε ≤ |C₀| * ε := mul_le_mul_of_nonneg_right (le_abs_self C₀) hε.le
    have hC' : ε * (|C₀| + 1) ≤ 1 := (le_div_iff₀ hC₀).1 hεC₀
    have htri : ‖G z‖ ≤ ‖G z - z‖ + ‖z‖ := by
      simpa using norm_add_le (G z - z) z
    nlinarith [norm_nonneg w]
  have hρsupp : ∀ ζ : ℂ, ‖w‖ + 2 < ‖ζ‖ → nxPush ν G ζ = 0 := ahF_push_support hGdisc
  -- term (4): `G w - w - V[nxMu2 ν](w)`, and the resulting bound `|G w - w| ≤ (A - 1) ε`
  have h4 : ‖G w - w - ahVar (nxMu2 ν) w‖ ≤ η / 4 * ε :=
    hfvo (nxMu2 ν) G ε hε hε2 hν₂ (ahF_nxMu2_vanish ν) hG
  have hV₂ : ‖ahVar (nxMu2 ν) w‖ ≤ 1 / π * (∫ ζ, ‖ahKer w ζ‖) * ε := ah_var_bound w hν₂
  have hGw : ‖G w - w‖ ≤ (A - 1) * ε := by
    have htri : ‖G w - w‖ ≤ ‖G w - w - ahVar (nxMu2 ν) w‖ + ‖ahVar (nxMu2 ν) w‖ := by
      simpa using norm_add_le (G w - w - ahVar (nxMu2 ν) w) (ahVar (nxMu2 ν) w)
    rw [hAdef]
    linarith
  have hAε4 : ε * (2 * A) ≤ δ₄ := (le_div_iff₀ (by positivity)).1 hε4
  have hAε5 : ε * A ≤ 2 := (le_div_iff₀ hA).1 hε5
  have hGwδ : ‖G w - w‖ < δ₄ := by nlinarith
  have hGwR : ‖G w‖ ≤ ‖w‖ + 2 := by
    have htri : ‖G w‖ ≤ ‖G w - w‖ + ‖w‖ := by
      simpa using norm_add_le (G w - w) w
    nlinarith
  -- term (1): the compactly supported first variation of `H` at `G w`
  have h1 : ‖H (G w) - G w - ahVar (nxPush ν G) (G w)‖ ≤ C₁ * ε ^ 2 :=
    (hcfv (nxPush ν G) H ε hεR hρ hρsupp hH).2 (G w) hGwR
  have h1' : C₁ * ε ^ 2 ≤ η / 4 * ε := by
    have hC : ε * (|C₁| + 1) ≤ η / 4 := (le_div_iff₀ hC₁).1 hεC₁
    have hC' : C₁ * ε ≤ |C₁| * ε := mul_le_mul_of_nonneg_right (le_abs_self C₁) hε.le
    have : C₁ * ε ≤ η / 4 := by nlinarith
    calc C₁ * ε ^ 2 = (C₁ * ε) * ε := by ring
      _ ≤ η / 4 * ε := mul_le_mul_of_nonneg_right this hε.le
  -- term (2): moving the point from `G w` to `w`
  have h2 : ‖ahVar (nxPush ν G) (G w) - ahVar (nxPush ν G) w‖ ≤ η / 4 * ε := by
    have hK := hkc (G w) hGwδ
    have hb := ahF_var_sub_bound (G w) w hρ
    have hK0 : 0 ≤ ∫ ζ, ‖ahKer (G w) ζ - ahKer w ζ‖ := integral_nonneg fun _ => norm_nonneg _
    calc ‖ahVar (nxPush ν G) (G w) - ahVar (nxPush ν G) w‖
        ≤ 1 / π * (∫ ζ, ‖ahKer (G w) ζ - ahKer w ζ‖) * ε := hb
      _ ≤ 1 * (η / 4) * ε := by
        refine mul_le_mul_of_nonneg_right ?_ hε.le
        exact mul_le_mul hπ1 hK.le hK0 zero_le_one
      _ = η / 4 * ε := by ring
  -- term (3): the pushed-forward inner coefficient has the first variation of `ν·1_Δ`
  have h3 : ‖ahVar (nxPush ν G) w - ahVar (unitDisc.indicator ν) w‖ ≤ η / 4 * ε :=
    hpush ν G ε hε hε3 hν hG
  -- term (5): `V[ν·1_Δ] + V[nxMu2 ν] = V[ν]`
  have h5 : ahVar (unitDisc.indicator ν) w + ahVar (nxMu2 ν) w = ahVar ν w := ahF_var_split w hν
  rw [hFHG, Function.comp_apply, ← h5]
  have halg : H (G w) - w - (ahVar (unitDisc.indicator ν) w + ahVar (nxMu2 ν) w) =
      (H (G w) - G w - ahVar (nxPush ν G) (G w)) +
        (ahVar (nxPush ν G) (G w) - ahVar (nxPush ν G) w) +
        (ahVar (nxPush ν G) w - ahVar (unitDisc.indicator ν) w) +
        (G w - w - ahVar (nxMu2 ν) w) := by ring
  rw [halg]
  calc _ ≤ ‖H (G w) - G w - ahVar (nxPush ν G) (G w)‖ +
        ‖ahVar (nxPush ν G) (G w) - ahVar (nxPush ν G) w‖ +
        ‖ahVar (nxPush ν G) w - ahVar (unitDisc.indicator ν) w‖ +
        ‖G w - w - ahVar (nxMu2 ν) w‖ := norm_add₄_le
    _ ≤ η / 4 * ε + η / 4 * ε + η / 4 * ε + η / 4 * ε := by
        gcongr
        exact h1.trans h1'
    _ = η * ε := by ring

/-! ### Piece Q — the quotient of two normalized solutions -/

/-- The pseudo-hyperbolic bound `|(a - b)/(1 - b̄ a)| ≤ 2k/(1 + k²)` for `|a|, |b| ≤ k < 1`: from the
identity `|1 - b̄ a|² - |a - b|² = (1 - |a|²)(1 - |b|²) ≥ (1 - k²)²` and `|a - b| ≤ 2k`. -/
theorem ahQ_pseudo_bound {a b : ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (ha : ‖a‖ ≤ k)
    (hb : ‖b‖ ≤ k) : ‖(a - b) / (1 - conj b * a)‖ ≤ 2 * k / (1 + k ^ 2) := by
  have hid : ‖1 - conj b * a‖ ^ 2 - ‖a - b‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re,
      Complex.one_im]
    ring
  have hx2 : ‖a‖ ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
  have hy2 : ‖b‖ ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hprod : (1 - k ^ 2) * (1 - k ^ 2) ≤ (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hN : ‖a - b‖ ≤ 2 * k := (norm_sub_le a b).trans (by linarith)
  have hN0 : 0 ≤ ‖a - b‖ := norm_nonneg _
  have hD0 : 0 ≤ ‖1 - conj b * a‖ := norm_nonneg _
  have hDsq : 0 < ‖1 - conj b * a‖ ^ 2 := by nlinarith
  have hD : 0 < ‖1 - conj b * a‖ := by
    rcases hD0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hDsq
      norm_num at hDsq
  have hsq : (‖a - b‖ * (1 + k ^ 2)) ^ 2 ≤ (2 * k * ‖1 - conj b * a‖) ^ 2 := by
    have e : (2 * k * ‖1 - conj b * a‖) ^ 2 - (‖a - b‖ * (1 + k ^ 2)) ^ 2 =
        4 * k ^ 2 * (‖1 - conj b * a‖ ^ 2 - ‖a - b‖ ^ 2) - ‖a - b‖ ^ 2 * (1 - k ^ 2) ^ 2 := by
      ring
    have h2 : 4 * k ^ 2 * ((1 - k ^ 2) * (1 - k ^ 2)) ≤
        4 * k ^ 2 * (‖1 - conj b * a‖ ^ 2 - ‖a - b‖ ^ 2) := by
      rw [hid]
      exact mul_le_mul_of_nonneg_left hprod (by positivity)
    have h3 : ‖a - b‖ ^ 2 * (1 - k ^ 2) ^ 2 ≤ (2 * k) ^ 2 * (1 - k ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hN0 hN 2) (sq_nonneg _)
    nlinarith
  have hle : ‖a - b‖ * (1 + k ^ 2) ≤ 2 * k * ‖1 - conj b * a‖ :=
    le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq
  rw [norm_div, div_le_div_iff₀ hD (by positivity)]
  linarith

/-- The algebra of the value form of piece C: with `A ζ = a ζ + b ζ̄` (inverse `ζ ↦ (ā ζ - b ζ̄)/J`,
`J = |a|² - |b|²`) and `B ζ = c ζ + d ζ̄`, the quotient of the Wirtinger coefficients of `B ∘ A⁻¹` is
`(d a - c b)/(c ā - d b̄) = (d/c - b/a)/(1 - conj(b/a)(d/c)) · a/ā` (for `|b| < |a|`, `|d| < |c|`). -/
theorem ahQ_value_identity {a b c d : ℂ} {J : ℝ} (hJ : J ≠ 0) (hba : ‖b‖ < ‖a‖)
    (hdc : ‖d‖ < ‖c‖) :
    (c * (-b / J) + d * conj (conj a / J)) / (c * (conj a / J) + d * conj (-b / J)) =
      (d / c - b / a) / (1 - conj (b / a) * (d / c)) * (a / conj a) := by
  have ha : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at hba
    exact (norm_nonneg b).not_gt hba
  have hc : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdc
    exact (norm_nonneg d).not_gt hdc
  have hJc : (J : ℂ) ≠ 0 := by exact_mod_cast hJ
  have hca : conj a ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr ha
  have hP : c * conj a - d * conj b ≠ 0 := by
    intro h
    have h' : c * conj a = d * conj b := by linear_combination h
    have hn := congrArg norm h'
    rw [norm_mul, norm_mul, norm_conj, norm_conj] at hn
    have hlt : ‖d‖ * ‖b‖ < ‖c‖ * ‖a‖ := mul_lt_mul'' hdc hba (norm_nonneg _) (norm_nonneg _)
    linarith
  have e1 : c * (conj a / J) + d * conj (-b / J) = (c * conj a - d * conj b) / J := by
    simp only [map_div₀, map_neg, Complex.conj_ofReal]
    ring
  have e2 : c * (-b / J) + d * conj (conj a / J) = (d * a - c * b) / J := by
    simp only [map_div₀, Complex.conj_ofReal, Complex.conj_conj]
    ring
  have e3 : 1 - conj (b / a) * (d / c) = (c * conj a - d * conj b) / (c * conj a) := by
    rw [map_div₀]
    field_simp
  have e4 : d / c - b / a = (d * a - c * b) / (c * a) := by
    field_simp
  rw [e1, e2, e3, e4, div_div_div_cancel_right₀ hJc]
  field_simp

/-- The value form of piece C: a.e. on `D`,
`μ_{f∘g⁻¹}(g z) = (μ_f - μ_g)/(1 - conj(μ_g) μ_f) · ∂_z g / conj(∂_z g)` — the chain rule (6.2) for
`f ∘ g⁻¹` at `g z` with the Wirtinger coefficients (13.5)–(13.6) of `g⁻¹` (`ie_wirtinger_of_comp_eq_id`). -/
theorem ahQ_comp_inv_dilatation {f g : ℂ → ℂ} {D : Set ℂ} {K₁ K₂ : ℝ} (hf : IsKQC f D K₁)
    (hg : IsKQC g D K₂) :
    ∀ᵐ z ∂(volume.restrict D),
      complexDilatation (f ∘ Function.invFunOn g D) (g z) =
        (complexDilatation f z - complexDilatation g z) /
            (1 - conj (complexDilatation g z) * complexDilatation f z) *
          (dz g z / conj (dz g z)) := by
  have hD : IsOpen D := hg.1
  have hleft : LeftInvOn (Function.invFunOn g D) g D := hg.2.2.1.2.1.leftInvOn_invFunOn
  filter_upwards [thm9_3_differentiable_ae hf, thm9_3_differentiable_ae hg,
    abC_differentiableAt_invFunOn_ae hg, thm9_6_cor2_jacobian_pos hf,
    thm9_6_cor2_jacobian_pos hg, ae_restrict_mem hD.measurableSet] with z hfz hgz hφz hJf hJg hzD
  set φ : ℂ → ℂ := Function.invFunOn g D with hφdef
  have hφgz : φ (g z) = z := hleft hzD
  -- `φ'(g z) = g'(z)⁻¹` in Wirtinger form (13.5)–(13.6)
  have hid : φ ∘ g =ᶠ[𝓝 z] id :=
    Filter.eventually_of_mem (hD.mem_nhds hzD) fun w hw => hleft hw
  have hBA : (fderiv ℝ φ (g z)).comp (fderiv ℝ g z) = ContinuousLinearMap.id ℝ ℂ :=
    (hφz.hasFDerivAt.comp z hgz.hasFDerivAt).unique ((hasFDerivAt_id z).congr_of_eventuallyEq hid)
  obtain ⟨hp, hq, -⟩ := ie_wirtinger_of_comp_eq_id hgz hφz hBA
  -- the chain rule (6.2) for `f ∘ φ` at `g z`
  have hfφ : DifferentiableAt ℝ f (φ (g z)) := by
    rw [hφgz]
    exact hfz
  have h1 := eq6_2_dz_comp hφz hfφ
  have h2 := eq6_2_dzbar_comp hφz hfφ
  obtain ⟨c1, c2⟩ := eq6_3 hφz
  rw [← c2, hφgz, hp, hq] at h1
  rw [← c1, hφgz, hp, hq] at h2
  -- positive Jacobians: `|∂_{z̄}| < |∂_z|` for `f` and `g`
  have hba : ‖dzbar g z‖ < ‖dz g z‖ := by
    unfold jacobian at hJg
    nlinarith [norm_nonneg (dz g z), norm_nonneg (dzbar g z)]
  have hdc : ‖dzbar f z‖ < ‖dz f z‖ := by
    unfold jacobian at hJf
    nlinarith [norm_nonneg (dz f z), norm_nonneg (dzbar f z)]
  unfold complexDilatation
  rw [h1, h2]
  exact ahQ_value_identity hJg.ne' hba hdc

/-- For a q.c. self-map `f` of `ℂ`, `μ ∘ f⁻¹` is a.e.-strongly measurable whenever `μ` is: the inverse
`invFunOn f univ` is continuous and pulls null sets `N` back into the null sets `f '' N` (Lusin's
property (N), `thm9_6_cor1_null`), so it is quasi-measure-preserving. -/
theorem ahQ_aestronglyMeasurable_comp_invFunOn {f μ : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K)
    (hs : f '' univ = univ) (hμ : AEStronglyMeasurable μ volume) :
    AEStronglyMeasurable (fun w => μ (Function.invFunOn f univ w)) volume := by
  have hφK : IsKQC (Function.invFunOn f univ) univ K := by
    have h := thm7_2_inv hf
    rwa [hs] at h
  have hφm : Measurable (Function.invFunOn f univ) :=
    (continuousOn_univ.1 hφK.2.2.1.1).measurable
  have hright : ∀ w, f (Function.invFunOn f univ w) = w := fun w => by
    apply Function.invFunOn_eq
    have hw : w ∈ f '' univ := by
      rw [hs]
      exact mem_univ w
    obtain ⟨z, hz, hzw⟩ := hw
    exact ⟨z, hz, hzw⟩
  have hqmp : Measure.QuasiMeasurePreserving (Function.invFunOn f univ) volume volume := by
    refine ⟨hφm, Measure.AbsolutelyContinuous.mk fun s hsm hs0 => ?_⟩
    rw [Measure.map_apply hφm hsm]
    have hsub : Function.invFunOn f univ ⁻¹' s ⊆ f '' s := fun w hw =>
      ⟨Function.invFunOn f univ w, hw, hright w⟩
    exact measure_mono_null hsub (thm9_6_cor1_null hf (subset_univ s) hs0)
  exact hμ.comp_quasiMeasurePreserving hqmp

/-- `f₁ ∘ f₀⁻¹` is the normalized solution of `ahQuot μ₁ μ₀ f₀`, a coefficient bounded by `2k/(1+k²)`. -/
theorem ah_quotient {f₁ f₀ μ₁ μ₀ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμ₁ : IsBeltramiCoeff μ₁ univ k) (hμ₀ : IsBeltramiCoeff μ₀ univ k)
    (hf₁ : IsNormalizedSolution f₁ μ₁) (hf₀ : IsNormalizedSolution f₀ μ₀) :
    IsNormalizedSolution (f₁ ∘ Function.invFunOn f₀ univ) (ahQuot μ₁ μ₀ f₀) ∧
      IsBeltramiCoeff (ahQuot μ₁ μ₀ f₀) univ (2 * k / (1 + k ^ 2)) := by
  obtain ⟨⟨K₁, hK₁⟩, himg₁, h0₁, h1₁, hd₁⟩ := hf₁
  obtain ⟨⟨K₀, hK₀⟩, himg₀, h0₀, h1₀, hd₀⟩ := hf₀
  have hleft : LeftInvOn (Function.invFunOn f₀ univ) f₀ univ := hK₀.2.2.1.2.1.leftInvOn_invFunOn
  have hφK : IsKQC (Function.invFunOn f₀ univ) univ K₀ := by
    have h := thm7_2_inv hK₀
    rwa [himg₀] at h
  have hφimg : Function.invFunOn f₀ univ '' univ = univ := by
    have h := hleft.image_image
    rwa [himg₀] at h
  have hφ0 : Function.invFunOn f₀ univ 0 = 0 := by
    have h := hleft (mem_univ 0)
    rwa [h0₀] at h
  have hφ1 : Function.invFunOn f₀ univ 1 = 1 := by
    have h := hleft (mem_univ 1)
    rwa [h1₀] at h
  -- a.e. in `z`: the value of the dilatation at `f₀ z` and the bound
  have hC := ahQ_comp_inv_dilatation hK₁ hK₀
  have hb₁ := hμ₁.2
  have hb₀ := hμ₀.2
  rw [Measure.restrict_univ] at hC hb₁ hb₀
  have hz : ∀ᵐ z ∂(volume.restrict univ),
      complexDilatation (f₁ ∘ Function.invFunOn f₀ univ) (f₀ z) = ahQuot μ₁ μ₀ f₀ (f₀ z) ∧
        ‖ahQuot μ₁ μ₀ f₀ (f₀ z)‖ ≤ 2 * k / (1 + k ^ 2) := by
    rw [Measure.restrict_univ]
    filter_upwards [hC, hd₁, hd₀, hb₁, hb₀] with z hCz h1z h0z hb1 hb0
    have hq : ahQuot μ₁ μ₀ f₀ (f₀ z) =
        (μ₁ z - μ₀ z) / (1 - conj (μ₀ z) * μ₁ z) * (dz f₀ z / conj (dz f₀ z)) := by
      rw [ahQuot, hleft (mem_univ z)]
    refine ⟨?_, ?_⟩
    · rw [hCz, h1z, h0z, hq]
    · rw [hq, norm_mul]
      have h1 := ahQ_pseudo_bound hk₀ hk hb1 hb0
      have h2 : ‖dz f₀ z / conj (dz f₀ z)‖ ≤ 1 := by
        rw [norm_div, Complex.norm_conj]
        exact div_self_le_one _
      calc ‖(μ₁ z - μ₀ z) / (1 - conj (μ₀ z) * μ₁ z)‖ * ‖dz f₀ z / conj (dz f₀ z)‖
          ≤ 2 * k / (1 + k ^ 2) * 1 :=
            mul_le_mul h1 h2 (norm_nonneg _) (div_nonneg (by linarith) (by positivity))
        _ = 2 * k / (1 + k ^ 2) := mul_one _
  -- transfer to `w = f₀ z` (Lusin's property (N) of `f₀`)
  have hw := abT_ae_image (p := fun w =>
      complexDilatation (f₁ ∘ Function.invFunOn f₀ univ) w = ahQuot μ₁ μ₀ f₀ w ∧
        ‖ahQuot μ₁ μ₀ f₀ w‖ ≤ 2 * k / (1 + k ^ 2)) hK₀ hz
  rw [himg₀, Measure.restrict_univ] at hw
  -- measurability of `ahQuot μ₁ μ₀ f₀`
  have hm₁ : AEStronglyMeasurable μ₁ volume := by
    have h := hμ₁.1
    rwa [Measure.restrict_univ] at h
  have hm₀ : AEStronglyMeasurable μ₀ volume := by
    have h := hμ₀.1
    rwa [Measure.restrict_univ] at h
  have hc₁ := (ahQ_aestronglyMeasurable_comp_invFunOn hK₀ himg₀ hm₁).aemeasurable
  have hc₀ := (ahQ_aestronglyMeasurable_comp_invFunOn hK₀ himg₀ hm₀).aemeasurable
  have hφm : Measurable (Function.invFunOn f₀ univ) :=
    (continuousOn_univ.1 hφK.2.2.1.1).measurable
  have hcd : AEMeasurable (fun w => dz f₀ (Function.invFunOn f₀ univ w)) volume :=
    ((measurable_dz f₀).comp hφm).aemeasurable
  have hcj := Complex.continuous_conj.measurable
  have hmeas : AEStronglyMeasurable (ahQuot μ₁ μ₀ f₀) volume :=
    (((hc₁.sub hc₀).div (aemeasurable_const.sub ((hcj.comp_aemeasurable hc₀).mul hc₁))).mul
      (hcd.div (hcj.comp_aemeasurable hcd))).aestronglyMeasurable
  refine ⟨⟨⟨K₀ * K₁, thm7_1_comp hφK hK₁ (subset_univ _)⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [image_comp, hφimg, himg₁]
  · rw [Function.comp_apply, hφ0, h0₁]
  · rw [Function.comp_apply, hφ1, h1₁]
  · filter_upwards [hw] with w hw1
    exact hw1.1
  · rw [Measure.restrict_univ]
    exact hmeas
  · rw [Measure.restrict_univ]
    filter_upwards [hw] with w hw1
    exact hw1.2

/-! ### Piece CE — Cauchy estimates for the coefficient family -/

/-- The a.e. bound `‖μ t z‖ ≤ k` holds for a.e. `z` simultaneously for ALL `t ∈ P`: it holds on a
countable dense subset of `P` (countable intersection of full-measure sets), and `t ↦ μ t z` is
continuous on the open set `P`. -/
theorem ahE_ae_forall_norm_le {P : Set ℂ} (hP : IsOpen P) {μ : ℂ → ℂ → ℂ} {k : ℝ}
    (hμ : ∀ t ∈ P, IsBeltramiCoeff (μ t) univ k)
    (hhol : ∀ z, DifferentiableOn ℂ (fun t => μ t z) P) :
    ∀ᵐ z, ∀ t ∈ P, ‖μ t z‖ ≤ k := by
  obtain ⟨S, hSP, hSc, hSd⟩ : ∃ S, S ⊆ P ∧ S.Countable ∧ P ⊆ closure S :=
    (TopologicalSpace.IsSeparable.of_separableSpace P).exists_countable_dense_subset
  have h1 : ∀ᵐ z, ∀ s ∈ S, ‖μ s z‖ ≤ k := by
    refine (ae_ball_iff hSc).mpr fun s hs => ?_
    simpa [Measure.restrict_univ] using (hμ s (hSP hs)).2
  filter_upwards [h1] with z hz t ht
  have hcont : ContinuousAt (fun s => ‖μ s z‖) t :=
    ((hhol z).differentiableAt (hP.mem_nhds ht)).continuousAt.norm
  have hsub : closure ((fun s => ‖μ s z‖) '' S) ⊆ Iic k :=
    closure_minimal (by rintro _ ⟨s, hs, rfl⟩; exact hz s hs) isClosed_Iic
  exact hsub (mem_closure_image hcont (hSd ht))

/-- The `t`-derivative `z ↦ ∂_t μ(t, z)|_{t₀}` is a.e. strongly measurable: it is the pointwise limit
of the difference quotients `dslope (μ · z) t₀ (t₀ + εₙ)`, `εₙ = (R/2)/(n+1)`, each a.e. strongly
measurable since `t₀ + εₙ ∈ P`. -/
theorem ahE_aestronglyMeasurable_deriv {P : Set ℂ} (hP : IsOpen P) {μ : ℂ → ℂ → ℂ} {k : ℝ}
    (hμ : ∀ t ∈ P, IsBeltramiCoeff (μ t) univ k)
    (hhol : ∀ z, DifferentiableOn ℂ (fun t => μ t z) P) {t₀ : ℂ} (ht₀ : t₀ ∈ P) :
    AEStronglyMeasurable (fun z => deriv (fun s => μ s z) t₀) volume := by
  obtain ⟨R, hR, hRP⟩ := Metric.isOpen_iff.mp hP t₀ ht₀
  set ε : ℕ → ℝ := fun n => R / 2 * (1 / ((n : ℝ) + 1)) with hεdef
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  have hεlt : ∀ n, ε n < R := fun n => by
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [n.cast_nonneg (α := ℝ)]
    have h2 : ε n ≤ R / 2 := by
      simp only [hεdef]
      calc R / 2 * (1 / ((n : ℝ) + 1)) ≤ R / 2 * 1 :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = R / 2 := mul_one _
    linarith
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (R / 2)
    rw [mul_zero] at this
    exact this
  set v : ℕ → ℂ := fun n => t₀ + (ε n : ℂ) with hvdef
  have hvlim : Tendsto v atTop (𝓝 t₀) := by
    have := tendsto_const_nhds (x := t₀) |>.add ((continuous_ofReal.tendsto 0).comp hεlim)
    simpa using this
  have hvP : ∀ n, v n ∈ P := fun n => hRP (by
    rw [mem_ball, dist_eq_norm]
    simp only [hvdef, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hεpos n)]
    exact hεlt n)
  have hvne : ∀ n, v n ≠ t₀ := fun n => by
    simp only [hvdef, ne_eq, add_eq_left, ofReal_eq_zero]
    exact (hεpos n).ne'
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun n z => dslope (fun s => μ s z) t₀ (v n)) (fun n => ?_) (ae_of_all _ fun z => ?_)
  · have h1 : AEStronglyMeasurable (μ (v n)) volume := by
      simpa [Measure.restrict_univ] using (hμ _ (hvP n)).1
    have h2 : AEStronglyMeasurable (μ t₀) volume := by
      simpa [Measure.restrict_univ] using (hμ _ ht₀).1
    have heq : (fun z => dslope (fun s => μ s z) t₀ (v n)) =
        fun z => (v n - t₀)⁻¹ • (μ (v n) z - μ t₀ z) := by
      funext z
      rw [dslope_of_ne _ (hvne n), slope_def_module]
    rw [heq]
    exact (h1.sub h2).const_smul (v n - t₀)⁻¹
  · have hd : DifferentiableAt ℂ (fun s => μ s z) t₀ :=
      (hhol z).differentiableAt (hP.mem_nhds ht₀)
    have := (continuousAt_dslope_same.mpr hd).tendsto.comp hvlim
    rw [dslope_same] at this
    exact this

/-- Cauchy estimates for one function: if `φ` is holomorphic on `ball t₀ R` with `‖φ‖ ≤ k` there,
then on that ball `‖φ t - φ t₀‖ ≤ (2k/R)‖t - t₀‖` and
`‖φ t - φ t₀ - (t - t₀) φ'(t₀)‖ ≤ (2(2k/R)/R)‖t - t₀‖²` (Schwarz lemma applied to `φ` and to
`dslope φ t₀`). -/
theorem ahE_pointwise {φ : ℂ → ℂ} {t₀ : ℂ} {R k : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ φ (ball t₀ R)) (hb : ∀ s ∈ ball t₀ R, ‖φ s‖ ≤ k) {t : ℂ}
    (ht : t ∈ ball t₀ R) :
    ‖φ t - φ t₀‖ ≤ 2 * k / R * ‖t - t₀‖ ∧
      ‖φ t - φ t₀ - (t - t₀) * deriv φ t₀‖ ≤ 2 * (2 * k / R) / R * ‖t - t₀‖ ^ 2 := by
  have ht₀ : t₀ ∈ ball t₀ R := mem_ball_self hR
  have hmaps : MapsTo φ (ball t₀ R) (closedBall (φ t₀) (2 * k)) := by
    intro s hs
    rw [mem_closedBall, dist_eq_norm]
    calc ‖φ s - φ t₀‖ ≤ ‖φ s‖ + ‖φ t₀‖ := norm_sub_le _ _
      _ ≤ k + k := add_le_add (hb s hs) (hb t₀ ht₀)
      _ = 2 * k := by ring
  have hg : ∀ s ∈ ball t₀ R, ‖dslope φ t₀ s‖ ≤ 2 * k / R := fun s hs =>
    Complex.norm_dslope_le_div_of_mapsTo_ball hd hmaps hs
  have hgd : DifferentiableOn ℂ (dslope φ t₀) (ball t₀ R) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds t₀ hR)).mpr hd
  have hmaps2 : MapsTo (dslope φ t₀) (ball t₀ R)
      (closedBall (dslope φ t₀ t₀) (2 * (2 * k / R))) := by
    intro s hs
    rw [mem_closedBall, dist_eq_norm]
    calc ‖dslope φ t₀ s - dslope φ t₀ t₀‖ ≤ ‖dslope φ t₀ s‖ + ‖dslope φ t₀ t₀‖ :=
          norm_sub_le _ _
      _ ≤ 2 * k / R + 2 * k / R := add_le_add (hg s hs) (hg t₀ ht₀)
      _ = 2 * (2 * k / R) := by ring
  have hh : ‖dslope (dslope φ t₀) t₀ t‖ ≤ 2 * (2 * k / R) / R :=
    Complex.norm_dslope_le_div_of_mapsTo_ball hgd hmaps2 ht
  have e1 : φ t - φ t₀ = (t - t₀) * dslope φ t₀ t := by
    rw [← smul_eq_mul, sub_smul_dslope]
  have e2 : dslope φ t₀ t - dslope φ t₀ t₀ = (t - t₀) * dslope (dslope φ t₀) t₀ t := by
    rw [← smul_eq_mul, sub_smul_dslope]
  have e3 : dslope φ t₀ t₀ = deriv φ t₀ := dslope_same φ t₀
  constructor
  · rw [e1, norm_mul]
    calc ‖t - t₀‖ * ‖dslope φ t₀ t‖ ≤ ‖t - t₀‖ * (2 * k / R) :=
          mul_le_mul_of_nonneg_left (hg t ht) (norm_nonneg _)
      _ = 2 * k / R * ‖t - t₀‖ := mul_comm _ _
  · have e4 : φ t - φ t₀ - (t - t₀) * deriv φ t₀ =
        (t - t₀) ^ 2 * dslope (dslope φ t₀) t₀ t := by
      rw [e1, ← e3, pow_two, mul_assoc, ← e2]
      ring
    rw [e4, norm_mul, norm_pow]
    calc ‖t - t₀‖ ^ 2 * ‖dslope (dslope φ t₀) t₀ t‖ ≤ ‖t - t₀‖ ^ 2 * (2 * (2 * k / R) / R) :=
          mul_le_mul_of_nonneg_left hh (by positivity)
      _ = 2 * (2 * k / R) / R * ‖t - t₀‖ ^ 2 := mul_comm _ _

/-- Near `t₀`, `μ t = μ t₀ + (t - t₀) μ̇ + O(|t - t₀|²)` uniformly a.e., with `μ̇` measurable. -/
theorem ah_cauchy_estimate {P : Set ℂ} (hP : IsOpen P) {μ : ℂ → ℂ → ℂ} {k : ℝ}
    (hμ : ∀ t ∈ P, IsBeltramiCoeff (μ t) univ k) (hhol : ∀ z, DifferentiableOn ℂ (fun t => μ t z) P)
    {t₀ : ℂ} (ht₀ : t₀ ∈ P) :
    ∃ r C : ℝ, 0 < r ∧ ball t₀ r ⊆ P ∧
      AEStronglyMeasurable (fun z => deriv (fun s => μ s z) t₀) volume ∧
      ∀ t ∈ ball t₀ r, ∀ᵐ z, ‖μ t z - μ t₀ z‖ ≤ C * ‖t - t₀‖ ∧
        ‖μ t z - μ t₀ z - (t - t₀) * deriv (fun s => μ s z) t₀‖ ≤ C * ‖t - t₀‖ ^ 2 := by
  obtain ⟨R, hR, hRP⟩ := Metric.isOpen_iff.mp hP t₀ ht₀
  refine ⟨R, max (2 * k / R) (2 * (2 * k / R) / R), hR, hRP,
    ahE_aestronglyMeasurable_deriv hP hμ hhol ht₀, fun t ht => ?_⟩
  filter_upwards [ahE_ae_forall_norm_le hP hμ hhol] with z hz
  obtain ⟨h1, h2⟩ := ahE_pointwise (φ := fun s => μ s z) hR ((hhol z).mono hRP)
    (fun s hs => hz s (hRP hs)) ht
  exact ⟨h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)),
    h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))⟩

/-! ### Target (moved to the end of S13; statement byte-identical up to the prime) -/

/-- The candidate `t`-derivative at `t₀` of the quotient coefficients `ahQuot (μ t) μ₀ f₀`:
`μ̇/(1 - |μ₀|²) · ∂_z f₀ / conj (∂_z f₀)` evaluated at `f₀⁻¹ w` (it mirrors `ahQuot`). -/
def ahT_dot (μd μ₀ f₀ : ℂ → ℂ) (w : ℂ) : ℂ :=
  μd (Function.invFunOn f₀ univ w) /
      (1 - conj (μ₀ (Function.invFunOn f₀ univ w)) * μ₀ (Function.invFunOn f₀ univ w)) *
    (dz f₀ (Function.invFunOn f₀ univ w) / conj (dz f₀ (Function.invFunOn f₀ univ w)))

/-- The inverse `f₀⁻¹ = invFunOn f₀ univ` of a quasiconformal map of `ℂ` onto `ℂ` is continuous and
quasi-measure-preserving: the preimage under `f₀⁻¹` of a null set lies in its `f₀`-image, which is null by
Lusin's property (N) (`thm9_6_cor1_null`). -/
theorem ahT_qmp_inv {f₀ : ℂ → ℂ} (hq : IsQuasiconformal f₀ univ) (himg : f₀ '' univ = univ) :
    Measure.QuasiMeasurePreserving (Function.invFunOn f₀ univ) volume volume := by
  obtain ⟨K, hK⟩ := hq
  have hcont : Continuous (Function.invFunOn f₀ univ) := by
    have h := hK.2.2.1.2.2.2
    rw [himg] at h
    exact continuousOn_univ.1 h
  refine ⟨hcont.measurable, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply hcont.measurable hs]
  have hsub : Function.invFunOn f₀ univ ⁻¹' s ⊆ f₀ '' s := by
    intro w hw
    have hw' : w ∈ f₀ '' univ := by
      rw [himg]
      exact mem_univ w
    exact ⟨_, hw, Function.invFunOn_eq hw'⟩
  exact measure_mono_null hsub (thm9_6_cor1_null hK (subset_univ s) hs0)

/-- `‖d / conj d‖ ≤ 1` (it is `1` for `d ≠ 0` and `0` for `d = 0`). -/
theorem ahT_norm_div_conj_le (d : ℂ) : ‖d / conj d‖ ≤ 1 := by
  rw [norm_div, Complex.norm_conj]
  exact div_self_le_one _

/-- `1 - k² ≤ |1 - b̄ a|` for `|a|, |b| ≤ k`. -/
theorem ahT_denom_ge {a b : ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (ha : ‖a‖ ≤ k) (hb : ‖b‖ ≤ k) :
    1 - k ^ 2 ≤ ‖1 - conj b * a‖ := by
  have h1 : ‖conj b * a‖ ≤ k ^ 2 := by
    rw [norm_mul, Complex.norm_conj, sq]
    exact mul_le_mul hb ha (norm_nonneg _) hk₀
  have h2 := norm_sub_norm_le (1 : ℂ) (conj b * a)
  rw [norm_one] at h2
  linarith

/-- `|x/(1 - b̄a) · ρ| ≤ M/(1 - k²)` for `|x| ≤ M`, `|a|, |b| ≤ k < 1` and `|ρ| ≤ 1`. -/
theorem ahT_frac_le {x a b ρ : ℂ} {k M : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (ha : ‖a‖ ≤ k)
    (hb : ‖b‖ ≤ k) (hρ : ‖ρ‖ ≤ 1) (hx : ‖x‖ ≤ M) :
    ‖x / (1 - conj b * a) * ρ‖ ≤ M / (1 - k ^ 2) := by
  have hk2 : 0 < 1 - k ^ 2 := by nlinarith
  have hD := ahT_denom_ge hk₀ ha hb
  rw [norm_mul, norm_div]
  calc ‖x‖ / ‖1 - conj b * a‖ * ‖ρ‖ ≤ ‖x‖ / ‖1 - conj b * a‖ * 1 :=
        mul_le_mul_of_nonneg_left hρ (div_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ‖x‖ / ‖1 - conj b * a‖ := mul_one _
    _ ≤ ‖x‖ / (1 - k ^ 2) := div_le_div_of_nonneg_left (norm_nonneg _) hk2 hD
    _ ≤ M / (1 - k ^ 2) := div_le_div_of_nonneg_right hx hk2.le

/-- The second-order algebra behind `ν_t - (t - t₀) ν̇ = O(|t - t₀|²)`: with `|a|, |b| ≤ k < 1`, `|ρ| ≤ 1`,
`|a - b| ≤ C|s|` and `|a - b - s m| ≤ C|s|²`, the difference `(a-b)/(1 - b̄a) ρ - s · m/(1 - |b|²) ρ`
equals `(b̄(a-b)²/((1 - b̄a)(1 - |b|²)) + (a - b - s m)/(1 - |b|²)) ρ`, hence is `O(|s|²)`. -/
theorem ahT_quot_second {a b m s ρ : ℂ} {k C : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (ha : ‖a‖ ≤ k)
    (hb : ‖b‖ ≤ k) (hρ : ‖ρ‖ ≤ 1) (h1 : ‖a - b‖ ≤ C * ‖s‖) (h2 : ‖a - b - s * m‖ ≤ C * ‖s‖ ^ 2) :
    ‖(a - b) / (1 - conj b * a) * ρ - s * (m / (1 - conj b * b) * ρ)‖ ≤
      (k * C ^ 2 / (1 - k ^ 2) ^ 2 + C / (1 - k ^ 2)) * ‖s‖ ^ 2 := by
  have hk2 : 0 < 1 - k ^ 2 := by nlinarith
  have hD1 := ahT_denom_ge hk₀ ha hb
  have hD2 := ahT_denom_ge hk₀ hb hb
  have hD1p : 0 < ‖1 - conj b * a‖ := hk2.trans_le hD1
  have hD2p : 0 < ‖1 - conj b * b‖ := hk2.trans_le hD2
  have hD1ne : 1 - conj b * a ≠ 0 := norm_pos_iff.1 hD1p
  have hD2ne : 1 - conj b * b ≠ 0 := norm_pos_iff.1 hD2p
  have hid : (a - b) / (1 - conj b * a) * ρ - s * (m / (1 - conj b * b) * ρ) =
      (conj b * (a - b) ^ 2 / ((1 - conj b * a) * (1 - conj b * b)) +
        (a - b - s * m) / (1 - conj b * b)) * ρ := by
    rw [← div_div]
    have hu : (1 - conj b * a) * (1 - conj b * a)⁻¹ = 1 := mul_inv_cancel₀ hD1ne
    have hv : (1 - conj b * b) * (1 - conj b * b)⁻¹ = 1 := mul_inv_cancel₀ hD2ne
    linear_combination (ρ * (a - b) * (1 - conj b * b)⁻¹) * hu - (ρ * (a - b) * (1 - conj b * a)⁻¹) * hv
  have hab2 : ‖a - b‖ ^ 2 ≤ C ^ 2 * ‖s‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hT1 : ‖conj b * (a - b) ^ 2 / ((1 - conj b * a) * (1 - conj b * b))‖ ≤
      k * C ^ 2 / (1 - k ^ 2) ^ 2 * ‖s‖ ^ 2 := by
    rw [norm_div, norm_mul, norm_mul, Complex.norm_conj, norm_pow]
    calc ‖b‖ * ‖a - b‖ ^ 2 / (‖1 - conj b * a‖ * ‖1 - conj b * b‖) ≤
          k * (C ^ 2 * ‖s‖ ^ 2) / ((1 - k ^ 2) * (1 - k ^ 2)) :=
        div_le_div₀ (mul_nonneg hk₀ (by positivity)) (mul_le_mul hb hab2 (by positivity) hk₀)
          (mul_pos hk2 hk2) (mul_le_mul hD1 hD2 hk2.le (norm_nonneg _))
      _ = k * C ^ 2 / (1 - k ^ 2) ^ 2 * ‖s‖ ^ 2 := by ring
  have hT2 : ‖(a - b - s * m) / (1 - conj b * b)‖ ≤ C / (1 - k ^ 2) * ‖s‖ ^ 2 := by
    rw [norm_div]
    calc ‖a - b - s * m‖ / ‖1 - conj b * b‖ ≤ C * ‖s‖ ^ 2 / (1 - k ^ 2) :=
          div_le_div₀ ((norm_nonneg _).trans h2) h2 hk2 hD2
      _ = C / (1 - k ^ 2) * ‖s‖ ^ 2 := by ring
  rw [hid, norm_mul]
  calc ‖conj b * (a - b) ^ 2 / ((1 - conj b * a) * (1 - conj b * b)) +
        (a - b - s * m) / (1 - conj b * b)‖ * ‖ρ‖ ≤
        ‖conj b * (a - b) ^ 2 / ((1 - conj b * a) * (1 - conj b * b)) +
          (a - b - s * m) / (1 - conj b * b)‖ * 1 :=
        mul_le_mul_of_nonneg_left hρ (norm_nonneg _)
    _ ≤ ‖conj b * (a - b) ^ 2 / ((1 - conj b * a) * (1 - conj b * b))‖ +
          ‖(a - b - s * m) / (1 - conj b * b)‖ := by
        rw [mul_one]
        exact norm_add_le _ _
    _ ≤ k * C ^ 2 / (1 - k ^ 2) ^ 2 * ‖s‖ ^ 2 + C / (1 - k ^ 2) * ‖s‖ ^ 2 := add_le_add hT1 hT2
    _ = (k * C ^ 2 / (1 - k ^ 2) ^ 2 + C / (1 - k ^ 2)) * ‖s‖ ^ 2 := by ring

/-- The coefficient estimates at `t₀`, pulled back from `z` to `w = f₀ z` through `f₀⁻¹` (quasi-measure-
preserving, `ahT_qmp_inv`): `ν̇ = ahT_dot μd (μ t₀) f₀` is a bounded measurable coefficient, and for
`t ∈ B(t₀, r)` the quotient coefficient `ν_t = ahQuot (μ t) (μ t₀) f₀` is `O(|t - t₀|)` (with a positive
constant) and `ν_t - (t - t₀) ν̇ = O(|t - t₀|²)`. -/
theorem ahT_coeff_estimates {μ : ℂ → ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) {f₀ : ℂ → ℂ}
    (hq : IsQuasiconformal f₀ univ) (himg : f₀ '' univ = univ) {t₀ : ℂ} {r C : ℝ} (hr : 0 < r)
    (hμ : ∀ t ∈ ball t₀ r, IsBeltramiCoeff (μ t) univ k) {μd : ℂ → ℂ}
    (hmeas : AEStronglyMeasurable μd volume)
    (hest : ∀ t ∈ ball t₀ r, ∀ᵐ z, ‖μ t z - μ t₀ z‖ ≤ C * ‖t - t₀‖ ∧
      ‖μ t z - μ t₀ z - (t - t₀) * μd z‖ ≤ C * ‖t - t₀‖ ^ 2) :
    ∃ C₁ C₂ C₃ : ℝ, 0 < C₃ ∧ IsBeltramiCoeff (ahT_dot μd (μ t₀) f₀) univ C₁ ∧
      ∀ t ∈ ball t₀ r, IsBeltramiCoeff (ahQuot (μ t) (μ t₀) f₀) univ (C₃ * ‖t - t₀‖) ∧
        IsBeltramiCoeff (fun w => ahQuot (μ t) (μ t₀) f₀ w - (t - t₀) * ahT_dot μd (μ t₀) f₀ w) univ
          (C₂ * ‖t - t₀‖ ^ 2) := by
  have hqmp := ahT_qmp_inv hq himg
  have hk2 : 0 < 1 - k ^ 2 := by nlinarith
  have ht₀r : t₀ ∈ ball t₀ r := mem_ball_self hr
  obtain ⟨hμ₀m, hμ₀b⟩ := hμ t₀ ht₀r
  rw [Measure.restrict_univ] at hμ₀m hμ₀b
  have hdzm : AEStronglyMeasurable (dz f₀) volume := (measurable_dz f₀).aestronglyMeasurable
  have hρm : AEStronglyMeasurable (fun z => dz f₀ z / conj (dz f₀ z)) volume :=
    hdzm.div₀ (Complex.continuous_conj.comp_aestronglyMeasurable hdzm)
  have hDm : AEStronglyMeasurable (ahT_dot μd (μ t₀) f₀) volume := by
    have hin : AEStronglyMeasurable (fun z => μd z / (1 - conj (μ t₀ z) * μ t₀ z) *
        (dz f₀ z / conj (dz f₀ z))) volume :=
      (hmeas.div₀ (aestronglyMeasurable_const.sub
        ((Complex.continuous_conj.comp_aestronglyMeasurable hμ₀m).mul hμ₀m))).mul hρm
    exact hin.comp_quasiMeasurePreserving hqmp
  -- the a.e. bound `|μd| ≤ C (1 + r/2)`, from the estimates at `t₁ = t₀ + r/2`
  have hr2 : 0 < r / 2 := by positivity
  set t₁ : ℂ := t₀ + ((r / 2 : ℝ) : ℂ) with ht₁def
  have ht₁ : ‖t₁ - t₀‖ = r / 2 := by
    rw [ht₁def, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr2]
  have ht₁r : t₁ ∈ ball t₀ r := by
    rw [mem_ball, dist_eq_norm, ht₁]
    linarith
  have hμd : ∀ᵐ z, ‖μd z‖ ≤ C + C * (r / 2) := by
    filter_upwards [hest t₁ ht₁r] with z hz
    obtain ⟨h1, h2⟩ := hz
    have h3 : ‖(t₁ - t₀) * μd z‖ ≤ ‖μ t₁ z - μ t₀ z‖ + ‖μ t₁ z - μ t₀ z - (t₁ - t₀) * μd z‖ := by
      have h := norm_sub_le (μ t₁ z - μ t₀ z) (μ t₁ z - μ t₀ z - (t₁ - t₀) * μd z)
      rwa [sub_sub_cancel] at h
    rw [norm_mul, ht₁] at h3
    rw [ht₁] at h1 h2
    have h4 : r / 2 * ‖μd z‖ ≤ r / 2 * (C + C * (r / 2)) := by nlinarith
    exact le_of_mul_le_mul_left h4 hr2
  refine ⟨(C + C * (r / 2)) / (1 - k ^ 2),
    k * (|C| + 1) ^ 2 / (1 - k ^ 2) ^ 2 + (|C| + 1) / (1 - k ^ 2), (|C| + 1) / (1 - k ^ 2),
    div_pos (by positivity) hk2, ⟨?_, ?_⟩, fun t ht => ?_⟩
  · rw [Measure.restrict_univ]
    exact hDm
  · rw [Measure.restrict_univ]
    filter_upwards [hqmp.ae (hμd.and hμ₀b)] with w hw
    exact ahT_frac_le hk₀ hk hw.2 hw.2 (ahT_norm_div_conj_le _) hw.1
  · obtain ⟨hμtm, hμtb⟩ := hμ t ht
    rw [Measure.restrict_univ] at hμtm hμtb
    have hC : C * ‖t - t₀‖ ≤ (|C| + 1) * ‖t - t₀‖ :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (norm_nonneg _)
    have hC2 : C * ‖t - t₀‖ ^ 2 ≤ (|C| + 1) * ‖t - t₀‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (by positivity)
    have hQm : AEStronglyMeasurable (ahQuot (μ t) (μ t₀) f₀) volume := by
      have hin : AEStronglyMeasurable (fun z => (μ t z - μ t₀ z) / (1 - conj (μ t₀ z) * μ t z) *
          (dz f₀ z / conj (dz f₀ z))) volume :=
        ((hμtm.sub hμ₀m).div₀ (aestronglyMeasurable_const.sub
          ((Complex.continuous_conj.comp_aestronglyMeasurable hμ₀m).mul hμtm))).mul hρm
      exact hin.comp_quasiMeasurePreserving hqmp
    have hae := hqmp.ae (((hest t ht).and hμtb).and hμ₀b)
    refine ⟨⟨by rw [Measure.restrict_univ]; exact hQm, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [Measure.restrict_univ]
      filter_upwards [hae] with w hw
      exact (ahT_frac_le hk₀ hk hw.1.2 hw.2 (ahT_norm_div_conj_le _) (hw.1.1.1.trans hC)).trans_eq
        (by ring)
    · rw [Measure.restrict_univ]
      exact hQm.sub (aestronglyMeasurable_const.mul hDm)
    · rw [Measure.restrict_univ]
      filter_upwards [hae] with w hw
      exact ahT_quot_second hk₀ hk hw.1.2 hw.2 (ahT_norm_div_conj_le _) (hw.1.1.1.trans hC)
        (hw.1.1.2.trans hC2)

/-- **The `t`-derivative.**  At `t₀ ∈ P`, `∂_t f(t, z) = V[ν̇](f(t₀, z))` with `ν̇ = ahT_dot μ̇ (μ t₀) (f t₀)`:
`f t z = G_t (f t₀ z)` for the normalized solution `G_t = f t ∘ (f t₀)⁻¹` of `ν_t = ahQuot (μ t) (μ t₀) (f t₀)`
(`ah_quotient`); `|ν_t| = O(|t - t₀|)` and `ν_t - (t - t₀) ν̇ = O(|t - t₀|²)` (`ah_cauchy_estimate`,
`ahT_coeff_estimates`); the first variation (`ah_first_variation`) and the linearity and boundedness of `V`
(`ah_var_linear`, `ah_var_bound`) give `f t z - f t₀ z - (t - t₀) V[ν̇](f t₀ z) = o(|t - t₀|)`. -/
theorem ahT_hasDerivAt {P : Set ℂ} (hP : IsOpen P) {μ : ℂ → ℂ → ℂ} {k : ℝ}
    (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : ∀ t ∈ P, IsBeltramiCoeff (μ t) univ k)
    (hhol : ∀ z, DifferentiableOn ℂ (fun t => μ t z) P) {f : ℂ → ℂ → ℂ}
    (hf : ∀ t ∈ P, IsNormalizedSolution (f t) (μ t)) {t₀ : ℂ} (ht₀ : t₀ ∈ P) (z : ℂ) :
    HasDerivAt (fun t => f t z)
      (ahVar (ahT_dot (fun ζ => deriv (fun s => μ s ζ) t₀) (μ t₀) (f t₀)) (f t₀ z)) t₀ := by
  obtain ⟨r, C, hr, hrP, hmeas, hest⟩ := ah_cauchy_estimate hP hμ hhol ht₀
  obtain ⟨hq₀, himg₀, -, -, -⟩ := hf t₀ ht₀
  obtain ⟨C₁, C₂, C₃, hC₃, hνd, hν⟩ := ahT_coeff_estimates (μd := fun ζ => deriv (fun s => μ s ζ) t₀)
    hk₀ hk hq₀ himg₀ hr (fun t ht => hμ t (hrP ht)) hmeas hest
  set νd : ℂ → ℂ := ahT_dot (fun ζ => deriv (fun s => μ s ζ) t₀) (μ t₀) (f t₀)
  set w : ℂ := f t₀ z with hwdef
  have hinj : InjOn (f t₀) univ := by
    obtain ⟨K, hK⟩ := hq₀
    exact hK.2.2.1.2.1
  have hleft : Function.invFunOn (f t₀) univ w = z := hinj.leftInvOn_invFunOn (mem_univ z)
  set Kw : ℝ := 1 / π * ∫ ζ, ‖ahKer w ζ‖
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hA : 0 < |Kw * C₂| + 1 := by positivity
  obtain ⟨δ, hδ, hFV⟩ := ah_first_variation w (c / (2 * C₃)) (div_pos hc (by linarith))
  have hρ : 0 < min r (min (δ / C₃) (c / (2 * (|Kw * C₂| + 1)))) :=
    lt_min hr (lt_min (div_pos hδ hC₃) (div_pos hc (by linarith)))
  filter_upwards [ball_mem_nhds t₀ hρ] with t ht
  rw [mem_ball, dist_eq_norm] at ht
  have htr : ‖t - t₀‖ < r := lt_of_lt_of_le ht (min_le_left _ _)
  have htδ : ‖t - t₀‖ < δ / C₃ := lt_of_lt_of_le ht ((min_le_right _ _).trans (min_le_left _ _))
  have htc : ‖t - t₀‖ < c / (2 * (|Kw * C₂| + 1)) :=
    lt_of_lt_of_le ht ((min_le_right _ _).trans (min_le_right _ _))
  show ‖f t z - w - (t - t₀) • ahVar νd w‖ ≤ c * ‖t - t₀‖
  rw [smul_eq_mul]
  by_cases hteq : t = t₀
  · rw [hteq, hwdef]
    simp
  have hs : 0 < ‖t - t₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hteq)
  have htball : t ∈ ball t₀ r := by
    rw [mem_ball, dist_eq_norm]
    exact htr
  obtain ⟨hνt, hν2⟩ := hν t htball
  have hG := (ah_quotient hk₀ hk (hμ t (hrP htball)) (hμ t₀ ht₀) (hf t (hrP htball)) (hf t₀ ht₀)).1
  have hε : C₃ * ‖t - t₀‖ ≤ δ := by
    have := (lt_div_iff₀ hC₃).1 htδ
    linarith
  have h1 := hFV _ _ (C₃ * ‖t - t₀‖) (mul_pos hC₃ hs) hε hνt hG
  have hcomp : (f t ∘ Function.invFunOn (f t₀) univ) w = f t z := by
    rw [Function.comp_apply, hleft]
  rw [hcomp] at h1
  set ν₂ : ℂ → ℂ := fun w' => ahQuot (μ t) (μ t₀) (f t₀) w' - (t - t₀) * νd w' with hν₂def
  have hlin : ahVar (ahQuot (μ t) (μ t₀) (f t₀)) w = (t - t₀) * ahVar νd w + ahVar ν₂ w := by
    have e : ahQuot (μ t) (μ t₀) (f t₀) = fun ζ => (t - t₀) * νd ζ + ν₂ ζ := by
      funext ζ
      rw [hν₂def]
      ring
    rw [e]
    exact ah_var_linear hνd hν2 (t - t₀) w
  rw [hlin] at h1
  have h2 := ah_var_bound w hν2
  have hkey : Kw * (C₂ * ‖t - t₀‖ ^ 2) ≤ c / 2 * ‖t - t₀‖ := by
    have e1 : Kw * (C₂ * ‖t - t₀‖ ^ 2) ≤ |Kw * C₂| * (‖t - t₀‖ * ‖t - t₀‖) := by
      have e : Kw * (C₂ * ‖t - t₀‖ ^ 2) = Kw * C₂ * (‖t - t₀‖ * ‖t - t₀‖) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have e2 : (|Kw * C₂| + 1) * ‖t - t₀‖ < c / 2 := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (|Kw * C₂| + 1))).1 htc
      linarith
    calc Kw * (C₂ * ‖t - t₀‖ ^ 2) ≤ |Kw * C₂| * (‖t - t₀‖ * ‖t - t₀‖) := e1
      _ ≤ (|Kw * C₂| + 1) * ‖t - t₀‖ * ‖t - t₀‖ := by nlinarith [mul_self_nonneg ‖t - t₀‖]
      _ ≤ c / 2 * ‖t - t₀‖ := mul_le_mul_of_nonneg_right e2.le (norm_nonneg _)
  have htri : ‖f t z - w - (t - t₀) * ahVar νd w‖ ≤
      ‖f t z - w - ((t - t₀) * ahVar νd w + ahVar ν₂ w)‖ + ‖ahVar ν₂ w‖ := by
    have e : f t z - w - (t - t₀) * ahVar νd w =
        (f t z - w - ((t - t₀) * ahVar νd w + ahVar ν₂ w)) + ahVar ν₂ w := by ring
    rw [e]
    exact norm_add_le _ _
  have h1' : c / (2 * C₃) * (C₃ * ‖t - t₀‖) = c / 2 * ‖t - t₀‖ := by
    field_simp
  linarith

/-- **Theorem 13.8** (Ahlfors–Bers, holomorphic dependence).  If `μ(z, t)` depends holomorphically
on `t` then so does the normalized solution.

*Correction.* The book states this for the self-maps of the disc fixing `1, i, -1`; that
version fails in general (the disc solution also involves the reflected coefficient
`conj μ`, which is anti-holomorphic in `t`).  The correct statement, formalized here, is for the
normalized solutions of the whole plane fixing `0, 1, ∞` (Theorem 13.7).

Proved (2026-09-24; moved here from §13.8): Ahlfors' variational argument.  The first variation
`F^ν(w) = w + V[ν](w) + o(‖ν‖∞)` (`ah_first_variation`) is proved for compactly supported `ν` from `z + Tω`
(`ah_first_variation_compact`), for `ν` vanishing in `Δ` by inversion (`ah_first_variation_outside`), and in
general via `F^ν = F^λ ∘ F^{ν₂}` with the pushed-forward inner part (`ah_push_variation`).  At `t₀`,
`f_t = G_t ∘ f_{t₀}` with `G_t` the normalized solution of `ahQuot (μ t) (μ t₀) (f t₀) = (t - t₀) ν̇ + O(|t - t₀|²)`
(`ah_quotient`, `ah_cauchy_estimate`), so `∂_t f(z, t)|_{t₀} = V[ν̇](f(z, t₀))`. -/
theorem thm13_8_ahlfors_bers_holomorphic {P : Set ℂ} (hP : IsOpen P) {μ : ℂ → ℂ → ℂ} {k : ℝ}
    (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : ∀ t ∈ P, IsBeltramiCoeff (μ t) univ k)
    (hhol : ∀ z, DifferentiableOn ℂ (fun t => μ t z) P) {f : ℂ → ℂ → ℂ}
    (hf : ∀ t ∈ P, IsNormalizedSolution (f t) (μ t)) :
    ∀ z, DifferentiableOn ℂ (fun t => f t z) P := by
  intro z t₀ ht₀
  exact (ahT_hasDerivAt hP hk₀ hk hμ hhol hf ht₀ z).differentiableAt.differentiableWithinAt

/-! ## Remark after Theorem 12.2 (moved here from S12) -/

/-- If `w(z)/z → 1` as `z → ∞`, then `w(z) → ∞` as `z → ∞`: eventually `|w(z)/z| > 1/2`, so
`|w(z)| > |z|/2`. -/
theorem s13x_un_tendsto_cocompact {w : ℂ → ℂ}
    (hlim : Tendsto (fun z => w z / z) (cocompact ℂ) (𝓝 1)) :
    Tendsto w (cocompact ℂ) (cocompact ℂ) := by
  rw [← Metric.cobounded_eq_cocompact,
    (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).tendsto_right_iff]
  intro r _
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) (Bornology.cobounded ℂ) atTop := by
    rw [Metric.cobounded_eq_cocompact]; exact tendsto_norm_cocompact_atTop
  have hl : ∀ᶠ z in Bornology.cobounded ℂ, dist (w z / z) 1 < 1 / 2 := by
    rw [Metric.cobounded_eq_cocompact]
    exact Metric.tendsto_nhds.1 hlim _ (by norm_num)
  filter_upwards [hnorm.eventually_gt_atTop (2 * |r| + 1), hl] with z hz hwz
  simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
  rw [dist_eq_norm] at hwz
  have hzpos : 0 < ‖z‖ := by linarith [abs_nonneg r]
  have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
  have h1 : 1 / 2 < ‖w z / z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (w z / z)
    rw [norm_one, norm_sub_rev] at h
    linarith
  have h2 : ‖w z‖ = ‖w z / z‖ * ‖z‖ := by
    rw [← norm_mul, div_mul_cancel₀ (w z) hz0]
  rw [h2]
  have h3 := mul_lt_mul_of_pos_right h1 hzpos
  linarith [le_abs_self r]

/-- A `K`-q.c. map `w` of the plane with `w(z)/z → 1` as `z → ∞` maps `ℂ` onto `ℂ`: `w` is continuous and
proper (`s13x_un_tendsto_cocompact`), hence closed, and `w(ℂ)` is open (`isOpen_image_of_isKQC`), so the nonempty
clopen set `w(ℂ)` is all of `ℂ`. -/
theorem s13x_un_image_univ {w : ℂ → ℂ} {K : ℝ} (hK : IsKQC w univ K)
    (hlim : Tendsto (fun z => w z / z) (cocompact ℂ) (𝓝 1)) : w '' univ = univ := by
  have hcont : Continuous w := continuousOn_univ.mp hK.2.2.1.1
  have hproper : IsProperMap w :=
    isProperMap_iff_tendsto_cocompact.2 ⟨hcont, s13x_un_tendsto_cocompact hlim⟩
  have hclopen : IsClopen (w '' univ) :=
    ⟨hproper.isClosedMap univ isClosed_univ, isOpen_image_of_isKQC hK⟩
  exact hclopen.eq_univ ⟨w 0, mem_image_of_mem w (mem_univ 0)⟩

/-- Remark after Theorem 12.2: the quasiconformal map of Theorem 12.2 is unique if in addition
to (12.12) one requires `w(0) = 0`.

(Moved here from S12 on 2026-09-24, statement unchanged, user-approved: the proof uses §13's
similarity principle and Theorem 13.5's affine-rigidity argument.) -/
theorem thm12_2_unique {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμ : IsCompactBeltramiCoeff μ k) {w₁ w₂ : ℂ → ℂ} (h₁ : IsQuasiconformal w₁ univ)
    (h₂ : IsQuasiconformal w₂ univ) (hμ₁ : ∀ᵐ z, complexDilatation w₁ z = μ z)
    (hμ₂ : ∀ᵐ z, complexDilatation w₂ z = μ z)
    (hlim₁ : Tendsto (fun z => w₁ z / z) (cocompact ℂ) (𝓝 1))
    (hlim₂ : Tendsto (fun z => w₂ z / z) (cocompact ℂ) (𝓝 1)) (h0₁ : w₁ 0 = 0) (h0₂ : w₂ 0 = 0) :
    w₁ = w₂ := by
  have _ := hk₀
  have _ := hk
  have _ := hμ
  obtain ⟨K₁, hK₁⟩ := h₁
  obtain ⟨K₂, hK₂⟩ := h₂
  have hs₁ : w₁ '' univ = univ := s13x_un_image_univ hK₁ hlim₁
  have hs₂ : w₂ '' univ = univ := s13x_un_image_univ hK₂ hlim₂
  obtain ⟨hμb, hsol₁⟩ := thm10_2_genHomeoSolution_of_isKQC hK₁
  obtain ⟨-, hsol₂⟩ := thm10_2_genHomeoSolution_of_isKQC hK₂
  have hK1 : (1 : ℝ) ≤ K₁ := hK₁.2.1
  have hkK : (K₁ - 1) / (K₁ + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hsol₂' : IsGenHomeoSolution w₂ (complexDilatation w₁) univ 2 := by
    obtain ⟨hh, gx, gy, hp, heq⟩ := hsol₂
    refine ⟨hh, gx, gy, hp, ?_⟩
    rw [Measure.restrict_univ] at heq ⊢
    filter_upwards [heq, hμ₁, hμ₂] with z h1 h2 h3
    rw [h1, h2, h3]
  obtain ⟨φ, hφ, hwφ⟩ := same_dilatation_conformal isOpen_univ hkK hμb hsol₁ hsol₂'
  rw [hs₁, hs₂] at hφ
  obtain ⟨a, b, -, hab⟩ := nx_entire_affine hφ
  have hb : b = 0 := by
    have h := hwφ 0 (mem_univ 0)
    rw [h0₂, h0₁, hab, mul_zero, zero_add] at h
    exact h.symm
  have hw : ∀ z, w₂ z = a * w₁ z := fun z => by
    rw [hwφ z (mem_univ z), hab, hb, add_zero]
  have ha : a = 1 := by
    have t : Tendsto (fun z => w₂ z / z) (cocompact ℂ) (𝓝 (a * 1)) :=
      (hlim₁.const_mul a).congr fun z => by rw [hw z, mul_div_assoc]
    have h := tendsto_nhds_unique t hlim₂
    rwa [mul_one] at h
  funext z
  rw [hw z, ha, one_mul]


/-! ### S13 track interface (coordinator 553e2d) -/

/-- **Representation of a q.c. self-map of the disc** (Theorems 12.2 and 13.2): `h = φ ∘ χ` on `Δ`, where `χ` is a
homeomorphism of `ℂ` onto `ℂ` (the Theorem 12.2 solution for `μ_h · 1_Δ`) and `φ` maps `χ(Δ)` conformally onto
`Δ` (`same_dilatation_conformal`). -/
theorem s13x_disc_repr {h : ℂ → ℂ} (hh : IsQuasiconformal h unitDisc)
    (himg : h '' unitDisc = unitDisc) :
    ∃ χ φ : ℂ → ℂ, IsHomeomorphOnto χ univ univ ∧ IsConformalOnto φ (χ '' unitDisc) unitDisc ∧
      ∀ z ∈ unitDisc, h z = φ (χ z) := by
  obtain ⟨K, hK⟩ := hh
  have hΔ : IsOpen unitDisc := isOpen_ball
  have hK1 : (1 : ℝ) ≤ K := hK.2.1
  have hk₀ : (0 : ℝ) ≤ (K - 1) / (K + 1) := div_nonneg (by linarith) (by linarith)
  have hk₁ : (K - 1) / (K + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  obtain ⟨hμ, -⟩ := thm10_2_genHomeoSolution_of_isKQC hK
  obtain ⟨χ, hχK, hχimg, hχd, -⟩ :=
    thm12_2 hk₀ hk₁ (ad_isCompactBeltramiCoeff_indicator hk₀ hμ hΔ isBounded_ball)
  have hχU := nx_isKQC_restrict hχK hΔ (subset_univ _)
  have hae : ∀ᵐ z ∂(volume.restrict unitDisc), complexDilatation h z = complexDilatation χ z := by
    filter_upwards [ae_restrict_of_ae hχd, ae_restrict_mem hΔ.measurableSet] with z h1 hz
    rw [h1, Set.indicator_of_mem hz]
  obtain ⟨φ, hφ, hhφ⟩ := nxS_factor hΔ hK hχU hae
  rw [himg] at hφ
  have hχh : IsHomeomorphOnto χ univ univ := by
    have h2 := hχK.2.2.1
    rw [hχimg] at h2
    exact h2
  exact ⟨χ, φ, hχh, hφ, hhφ⟩

/-- A homeomorphism of `ℂ` onto `ℂ` in the sense of `IsHomeomorphOnto` is (the underlying map of) a
`Homeomorph ℂ ℂ`. -/
theorem s13x_de_exists_homeomorph {χ : ℂ → ℂ} (hχ : IsHomeomorphOnto χ univ univ) :
    ∃ e : ℂ ≃ₜ ℂ, ⇑e = χ := by
  obtain ⟨hc, hi, himg, hic⟩ := hχ
  have hleft : ∀ z, Function.invFunOn χ univ (χ z) = z := fun z =>
    hi.leftInvOn_invFunOn (mem_univ z)
  have hright : ∀ w, χ (Function.invFunOn χ univ w) = w := by
    intro w
    have hw : w ∈ χ '' univ := by
      rw [himg]
      exact mem_univ w
    exact Function.invFunOn_eq hw
  exact ⟨⟨⟨χ, Function.invFunOn χ univ, hleft, hright⟩, continuousOn_univ.1 hc,
    continuousOn_univ.1 hic⟩, rfl⟩

/-- The one-point extension `e.onePointCongr` of a homeomorphism `e` of `ℂ` maps `toExt U` onto
`toExt (e '' U)`. -/
theorem s13x_de_image_toExt (e : ℂ ≃ₜ ℂ) (U : Set ℂ) :
    e.onePointCongr '' toExt U = toExt (e '' U) := by
  unfold toExt
  rw [image_image, image_image]
  rfl

/-- A homeomorphism `e` of `ℂ` extends (by `∞ ↦ ∞`) to a homeomorphism of `ℂ̄`, which is a homeomorphic
extension of `e : U → e(U)` for every `U`. -/
theorem s13x_de_isHomeoExtension_homeomorph (e : ℂ ≃ₜ ℂ) (U : Set ℂ) :
    IsHomeoExtension e U (e '' U) e.onePointCongr := by
  refine ⟨fun z _ => rfl, e.onePointCongr.continuous.continuousOn,
    e.onePointCongr.injective.injOn, ?_⟩
  rw [e.onePointCongr.image_closure, s13x_de_image_toExt]

/-- The frontier in `ℂ̄` of the image of `Δ` under a homeomorphism `e` of `ℂ` is a Jordan curve: it is
the image `e(∂Δ)` of the unit circle. -/
theorem s13x_de_isJordanCurve_frontier (e : ℂ ≃ₜ ℂ) :
    IsJordanCurve (frontier (toExt (e '' unitDisc))) := by
  have hfr : frontier (toExt unitDisc) = toExt (sphere (0 : ℂ) 1) := by
    rw [frontier_toExt_of_isBounded' (A := unitDisc) isBounded_ball isOpen_ball, unitDisc,
      frontier_ball (0 : ℂ) one_ne_zero]
  have hEq : frontier (toExt (e '' unitDisc)) = toExt (e '' sphere (0 : ℂ) 1) := by
    rw [← s13x_de_image_toExt, ← e.onePointCongr.image_frontier, hfr, s13x_de_image_toExt]
  rw [hEq]
  refine ⟨fun θ => ((e (θ : ℂ) : ℂ) : ExtPlane), ?_, ?_, ?_⟩
  · exact OnePoint.continuous_coe.comp (e.continuous.comp continuous_subtype_val)
  · intro a b hab
    exact Circle.coe_injective (e.injective (OnePoint.coe_injective hab))
  · unfold toExt
    ext w
    simp only [mem_range, mem_image]
    constructor
    · rintro ⟨θ, rfl⟩
      exact ⟨e θ, ⟨θ, mem_sphere_zero_iff_norm.2 (Circle.norm_coe θ), rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩

/-- `IsHomeoExtension f U V F` only depends on the values of `f` on `U`. -/
theorem s13x_de_isHomeoExtension_congr {f g : ℂ → ℂ} {U V : Set ℂ} {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f U V F) (hfg : EqOn f g U) : IsHomeoExtension g U V F := by
  obtain ⟨h1, h2, h3, h4⟩ := hF
  exact ⟨fun z hz => (h1 z hz).trans (by rw [hfg hz]), h2, h3, h4⟩

/-- **Boundary correspondence on the disc**: a quasiconformal map of `Δ` onto `Δ` extends to a homeomorphism of
`Δ̄` (`χ` is a plane homeomorphism, and `φ⁻¹ : Δ → χ(Δ)` extends by Carathéodory's theorem). -/
theorem s13x_disc_extension {h : ℂ → ℂ} (hh : IsQuasiconformal h unitDisc)
    (himg : h '' unitDisc = unitDisc) :
    ∃ H : ExtPlane → ExtPlane, IsHomeoExtension h unitDisc unitDisc H := by
  obtain ⟨χ, φ, hχ, hφ, hrepr⟩ := s13x_disc_repr hh himg
  obtain ⟨e, rfl⟩ := s13x_de_exists_homeomorph hχ
  have hΔo : IsOpen unitDisc := isOpen_ball
  have hΩo : IsOpen (e '' unitDisc) := e.isOpenMap _ hΔo
  have hΩb : Bornology.IsBounded (e '' unitDisc) :=
    ((isCompact_closedBall (0 : ℂ) 1).image e.continuous).isBounded.subset
      (image_mono ball_subset_closedBall)
  have hψ : IsConformalOnto (Function.invFunOn φ (e '' unitDisc)) unitDisc (e '' unitDisc) :=
    IsConformalOnto.symm hΩo hφ
  obtain ⟨F, hF⟩ := caratheodory_jordan_clean hΩb hψ (s13x_de_isJordanCurve_frontier e)
  have hΦ : IsHomeoExtension φ (e '' unitDisc) unitDisc
      (Function.invFunOn F (closure (toExt unitDisc))) := by
    refine s13x_de_isHomeoExtension_congr (isHomeoExtension_invFunOn hψ hF) ?_
    intro z hz
    have h1 : Function.invFunOn φ (e '' unitDisc) (φ z) = z := hφ.2.1.leftInvOn_invFunOn hz
    have h2 : Function.invFunOn (Function.invFunOn φ (e '' unitDisc)) unitDisc
        (Function.invFunOn φ (e '' unitDisc) (φ z)) = φ z :=
      hψ.2.1.leftInvOn_invFunOn (hφ.mapsTo hz)
    rw [h1] at h2
    exact h2
  have hcomp := hΦ.comp (s13x_de_isHomeoExtension_homeomorph e unitDisc)
    (fun z hz => mem_image_of_mem e hz)
  exact ⟨_, s13x_de_isHomeoExtension_congr hcomp fun z hz => (hrepr z hz).symm⟩

/-- Local-to-global a.e.: if `P` holds a.e. near every point of `Ω ∖ L` and `L` is null, then `P` holds a.e.
on `Ω` (Lindelöf). -/
theorem s13x_ae_of_local {P : ℂ → Prop} {Ω L : Set ℂ} (hLnull : volume L = 0)
    (hloc : ∀ z ∈ Ω \ L, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ ∀ᵐ w ∂(volume.restrict U), P w) :
    ∀ᵐ w ∂(volume.restrict Ω), P w := by
  choose! U hUo hzU hUP using hloc
  obtain ⟨T, hTsub, hTc, hTeq⟩ :=
    TopologicalSpace.isOpen_biUnion_countable (Ω \ L) U fun z hz => hUo z hz
  have hcov : Ω ⊆ (⋃ z ∈ T, U z) ∪ L := by
    intro w hw
    by_cases hwL : w ∈ L
    · exact Or.inr hwL
    · refine Or.inl ?_
      rw [hTeq]
      exact mem_biUnion (show w ∈ Ω \ L from ⟨hw, hwL⟩) (hzU w ⟨hw, hwL⟩)
  refine ae_restrict_of_ae_restrict_of_subset hcov ((ae_restrict_union_iff _ _ _).2 ⟨?_, ?_⟩)
  · exact (ae_restrict_biUnion_iff U hTc P).2 fun z hz => hUP z (hTsub hz)
  · rw [Measure.restrict_eq_zero.2 hLnull]
    simp

/-- Energy bound on rectangles: for a homeomorphism `g` of `Ω` with `|∂g| + |∂̄g| ≤ K(|∂g| - |∂̄g|)` a.e. on `Ω`,
`∫_R |g'(z) v| < ∞` on every open rectangle `R` with `R̄ ⊆ Ω`, `|v| = 1` (`∫_R J_g ≤ m(g(R̄)) < ∞`). -/
theorem s13x_lintegral_fderiv_lt_top {g : ℂ → ℂ} {Ω : Set ℂ} {K : ℝ} (hΩ : IsOpen Ω)
    (hg : IsHomeomorphOnto g Ω (g '' Ω)) (hK : 0 ≤ K)
    (hdiff : ∀ᵐ z ∂(volume.restrict Ω), DifferentiableAt ℝ g z)
    (hineq : ∀ᵐ z ∂(volume.restrict Ω), ‖dz g z‖ + ‖dzbar g z‖ ≤ K * (‖dz g z‖ - ‖dzbar g z‖))
    {v : ℂ} (hv : ‖v‖ = 1) {a b c d : ℝ} (hR : closedRect a b c d ⊆ Ω) :
    ∫⁻ z in openRect a b c d, ‖fderiv ℝ g z v‖ₑ < ∞ := by
  have hRΩ : openRect a b c d ⊆ Ω := (openRect_subset_closedRect a b c d).trans hR
  have hpt : ∀ᵐ z ∂(volume.restrict Ω), ‖fderiv ℝ g z v‖ₑ ≤
      ENNReal.ofReal K * ENNReal.ofReal (jacobian g z) + 1 := by
    filter_upwards [hdiff, hineq] with z hz hz'
    have hA0 : 0 ≤ ‖dz g z‖ + ‖dzbar g z‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hbound : ‖fderiv ℝ g z v‖ ≤ ‖dz g z‖ + ‖dzbar g z‖ := by
      rw [fderiv_eq_dz_dzbar hz]
      calc ‖dz g z * v + dzbar g z * conj v‖
          ≤ ‖dz g z * v‖ + ‖dzbar g z * conj v‖ := norm_add_le _ _
        _ = ‖dz g z‖ + ‖dzbar g z‖ := by
            rw [norm_mul, norm_mul, Complex.norm_conj, hv, mul_one, mul_one]
    have hsq : (‖dz g z‖ + ‖dzbar g z‖) ^ 2 ≤ K * jacobian g z := by
      unfold jacobian
      nlinarith [norm_nonneg (dz g z), norm_nonneg (dzbar g z)]
    have h1 : ‖fderiv ℝ g z v‖ ≤ K * jacobian g z + 1 := by
      nlinarith [norm_nonneg (fderiv ℝ g z v)]
    calc ‖fderiv ℝ g z v‖ₑ = ENNReal.ofReal ‖fderiv ℝ g z v‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (K * jacobian g z + 1) := ENNReal.ofReal_le_ofReal h1
      _ ≤ ENNReal.ofReal (K * jacobian g z) + ENNReal.ofReal 1 := ENNReal.ofReal_add_le
      _ = ENNReal.ofReal K * ENNReal.ofReal (jacobian g z) + 1 := by
          rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_one]
  have hJ : ∫⁻ z in openRect a b c d, ENNReal.ofReal (jacobian g z) ≤
      volume (g '' openRect a b c d) :=
    ad_lintegral_jacobian_le_volume_image hΩ hg.2.1 hdiff (measurableSet_openRect a b c d) hRΩ
  have hfin : volume (g '' openRect a b c d) < ∞ :=
    (measure_mono (image_mono (openRect_subset_closedRect a b c d))).trans_lt
      ((isCompact_closedRect a b c d).image_of_continuousOn (hg.1.mono hR)).measure_lt_top
  have hRfin : volume (openRect a b c d) < ∞ :=
    (measure_mono (openRect_subset_closedRect a b c d)).trans_lt
      (isCompact_closedRect a b c d).measure_lt_top
  calc ∫⁻ z in openRect a b c d, ‖fderiv ℝ g z v‖ₑ
      ≤ ∫⁻ z in openRect a b c d, (ENNReal.ofReal K * ENNReal.ofReal (jacobian g z) + 1) :=
        lintegral_mono_ae (ae_restrict_of_ae_restrict_of_subset hRΩ hpt)
    _ = ENNReal.ofReal K * (∫⁻ z in openRect a b c d, ENNReal.ofReal (jacobian g z)) +
          volume (openRect a b c d) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          setLIntegral_const, one_mul]
    _ < ∞ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hJ.trans_lt hfin),
          hRfin⟩

/-- A point of an open set `U` lies, with a margin `ε`, inside a rational closed rectangle contained in
`U`. -/
theorem s13x_rm2_rat_rect {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hzU : z ∈ U) :
    ∃ q : ℚ × ℚ × ℚ × ℚ, ∃ ε > (0 : ℝ), closedRect q.1 q.2.1 q.2.2.1 q.2.2.2 ⊆ U ∧
      (q.1 : ℝ) < z.re - ε ∧ z.re + ε < q.2.1 ∧ (q.2.2.1 : ℝ) < z.im - ε ∧
        z.im + ε < q.2.2.2 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z hzU
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show z.re - r / 2 < z.re - r / 4 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show z.re + r / 4 < z.re + r / 2 by linarith)
  obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn (show z.im - r / 2 < z.im - r / 4 by linarith)
  obtain ⟨d, hd1, hd2⟩ := exists_rat_btwn (show z.im + r / 4 < z.im + r / 2 by linarith)
  have hR : closedRect a b c d ⊆ U := by
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hw
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖w - z‖ ≤ |(w - z).re| + |(w - z).im| := Complex.norm_le_abs_re_add_abs_im _
      _ < r / 2 + r / 2 := by
          rw [sub_re, sub_im]
          exact add_lt_add (abs_lt.2 ⟨by linarith, by linarith⟩)
            (abs_lt.2 ⟨by linarith, by linarith⟩)
      _ = r := by ring
  exact ⟨(a, b, c, d), r / 4, by positivity, hR, ha2, hb1, hc2, hd1⟩

/-- For almost every `x`, `y ↦ g(x + iy)` is absolutely continuous on `[q₃, q₄]` for every rational
closed rectangle `[q₁, q₂] × [q₃, q₄]` contained in an open set on which `g` is A.C.L., with
`x ∈ (q₁, q₂)` (countably many rectangles). -/
theorem s13x_rm2_vertical_rat {g : ℂ → ℂ} :
    ∀ᵐ x : ℝ, ∀ q : ℚ × ℚ × ℚ × ℚ, (q.1 : ℝ) < q.2.1 → (q.2.2.1 : ℝ) < q.2.2.2 →
      (∃ U : Set ℂ, IsACL g U ∧ closedRect q.1 q.2.1 q.2.2.1 q.2.2.2 ⊆ U) →
      x ∈ Ioo (q.1 : ℝ) q.2.1 →
      AbsolutelyContinuousOnInterval (fun y : ℝ => g ((x : ℂ) + (y : ℂ) * I)) q.2.2.1 q.2.2.2 := by
  rw [ae_all_iff]
  intro q
  by_cases h : (q.1 : ℝ) < q.2.1 ∧ (q.2.2.1 : ℝ) < q.2.2.2 ∧
      (∃ U : Set ℂ, IsACL g U ∧ closedRect q.1 q.2.1 q.2.2.1 q.2.2.2 ⊆ U)
  · obtain ⟨h1, h2, U, hU, h3⟩ := h
    have hv := (hU.2 _ _ _ _ h1 h2 h3).1
    rw [ae_restrict_iff' measurableSet_Ioo] at hv
    filter_upwards [hv] with x hx _ _ _ hxI
    exact hx hxI
  · exact Eventually.of_forall fun x h1 h2 h3 _ => absurd ⟨h1, h2, h3⟩ h

/-- A property holding a.e. on an open rectangle holds, for almost every `x ∈ (a, b)`, at `x + iy` for
almost every `y ∈ (c, d)` (Fubini for null sets). -/
theorem s13x_rm2_ae_ae_of_ae_rect {P : ℂ → Prop} (hP : MeasurableSet {z | P z}) {a b c d : ℝ}
    (h : ∀ᵐ z ∂(volume.restrict (openRect a b c d)), P z) :
    ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioo a b)), ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo c d)),
      P ((x : ℂ) + (y : ℂ) * I) := by
  have he := Complex.measurableEquivRealProd.symm.measurableEmbedding
  rw [volume_restrict_openRect_eq_map, ae_map_iff he.measurable.aemeasurable hP,
    Measure.ae_prod_iff_ae_ae (p := fun q => P (Complex.measurableEquivRealProd.symm q))
      (show MeasurableSet {q | P (Complex.measurableEquivRealProd.symm q)} from
        he.measurable hP)] at h
  simpa only [measurableEquivRealProd_symm_apply'] using h

/-- On almost every vertical segment of a rectangle on which `g` is a.e. differentiable,
`y ↦ g(x + iy)` has an integrable derivative: it is `g'(x + iy) i` a.e. on the segment, and Tonelli
applies to `∫_R |g' i| < ∞`. -/
theorem s13x_rm2_vertical_integrable {g : ℂ → ℂ} {a b c d : ℝ}
    (hdiff : ∀ᵐ z ∂(volume.restrict (openRect a b c d)), DifferentiableAt ℝ g z) (hcd : c ≤ d)
    (hfin : ∫⁻ z in openRect a b c d, ‖fderiv ℝ g z I‖ₑ < ∞) :
    ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioo a b)),
      IntervalIntegrable (deriv fun y : ℝ => g ((x : ℂ) + (y : ℂ) * I)) volume c d := by
  have hFm : Measurable fun z => ‖fderiv ℝ g z I‖ₑ :=
    (measurable_fderiv_apply_const ℝ g I).enorm
  rw [lintegral_openRect hFm] at hfin
  have hm : Measurable fun x : ℝ => ∫⁻ y in Ioo c d, ‖fderiv ℝ g ((x : ℂ) + (y : ℂ) * I) I‖ₑ :=
    (hFm.comp continuous_rectCoords.measurable).lintegral_prod_right'
  filter_upwards [ae_lt_top hm hfin.ne,
    s13x_rm2_ae_ae_of_ae_rect (measurableSet_of_differentiableAt ℝ g) hdiff] with x hx1 hx2
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hcd]
  refine ⟨(measurable_deriv _).aestronglyMeasurable, ?_⟩
  show ∫⁻ y in Ioo c d, ‖deriv (fun y : ℝ => g ((x : ℂ) + (y : ℂ) * I)) y‖ₑ < ∞
  calc ∫⁻ y in Ioo c d, ‖deriv (fun y : ℝ => g ((x : ℂ) + (y : ℂ) * I)) y‖ₑ
      = ∫⁻ y in Ioo c d, ‖fderiv ℝ g ((x : ℂ) + (y : ℂ) * I) I‖ₑ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hx2] with y hy
        rw [← partialY_ofReal_add, partialY_eq_of_differentiableAt hy]
    _ < ∞ := hx1

/-- From the local hypothesis: `g` is differentiable and satisfies the dilatation inequality a.e. on `Ω`
(Theorems 9.3 and 9.4 near every point of `Ω ∖ L`, `L` null). -/
theorem s13x_rm2_diff_ineq_ae {g : ℂ → ℂ} {Ω L : Set ℂ} {K : ℝ} (hLnull : volume L = 0)
    (hloc : ∀ z ∈ Ω \ L, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U ⊆ Ω ∧ IsKQC g U K) :
    (∀ᵐ z ∂(volume.restrict Ω), DifferentiableAt ℝ g z) ∧
      ∀ᵐ z ∂(volume.restrict Ω), ‖dz g z‖ + ‖dzbar g z‖ ≤ K * (‖dz g z‖ - ‖dzbar g z‖) := by
  refine ⟨s13x_ae_of_local hLnull fun z hz => ?_, s13x_ae_of_local hLnull fun z hz => ?_⟩
  · obtain ⟨U, hU, hzU, -, hgU⟩ := hloc z hz
    exact ⟨U, hU, hzU, thm9_3_differentiable_ae hgU⟩
  · obtain ⟨U, hU, hzU, -, hgU⟩ := hloc z hz
    exact ⟨U, hU, hzU, thm9_4_dilatation_ae hgU⟩

/-- A.C.L. across `L`, vertical lines: for a homeomorphism `g` of `Ω`, `K`-q.c. near every point of `Ω ∖ L`
(`L` null, met by almost every vertical line in a countable set), almost every vertical segment of a closed
rectangle in `Ω` carries an absolutely continuous restriction of `g`. -/
theorem s13x_line_ac_vertical {g : ℂ → ℂ} {Ω L : Set ℂ} {K : ℝ} (hΩ : IsOpen Ω) (hK : 1 ≤ K)
    (hg : IsHomeomorphOnto g Ω (g '' Ω)) (hLnull : volume L = 0)
    (hLv : ∀ᵐ x : ℝ, {y : ℝ | (x : ℂ) + (y : ℂ) * I ∈ L}.Countable)
    (hloc : ∀ z ∈ Ω \ L, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U ⊆ Ω ∧ IsKQC g U K)
    {a b c d : ℝ} (hcd : c < d) (hR : closedRect a b c d ⊆ Ω) :
    ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioo a b)),
      AbsolutelyContinuousOnInterval (fun y : ℝ => g ((x : ℂ) + (y : ℂ) * I)) c d := by
  obtain ⟨hdiff, hineq⟩ := s13x_rm2_diff_ineq_ae hLnull hloc
  have hfin := s13x_lintegral_fderiv_lt_top hΩ hg (zero_le_one.trans hK) hdiff hineq (v := I)
    (by simp) hR
  have hdiffR : ∀ᵐ z ∂(volume.restrict (openRect a b c d)), DifferentiableAt ℝ g z :=
    ae_restrict_of_ae_restrict_of_subset ((openRect_subset_closedRect a b c d).trans hR) hdiff
  filter_upwards [s13x_rm2_vertical_integrable hdiffR hcd.le hfin,
    ae_restrict_of_ae (s13x_rm2_vertical_rat (g := g)), ae_restrict_of_ae hLv,
    ae_restrict_mem measurableSet_Ioo] with x hint hrat hLx hx
  have hmem : ∀ y ∈ Icc c d, (x : ℂ) + (y : ℂ) * I ∈ Ω := fun y hy => hR (by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
        add_zero, add_im, mul_im, zero_add]
    exacts [hx.1.le, hx.2.le, hy.1, hy.2])
  refine abR_c_ac_of_local (S := {y : ℝ | (x : ℂ) + (y : ℂ) * I ∈ L}) hcd.le hLx
    (hg.1.comp (by fun_prop : Continuous fun y : ℝ => (x : ℂ) + (y : ℂ) * I).continuousOn hmem)
    hint fun y hy => ?_
  obtain ⟨U, hU, hzU, -, hgU⟩ := hloc _ ⟨hmem y (Ioo_subset_Icc_self hy.1), hy.2⟩
  obtain ⟨q, ε, hε, hsub, h1, h2, h3, h4⟩ := s13x_rm2_rat_rect hU hzU
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
    add_zero, add_im, mul_im, zero_add] at h1 h2 h3 h4
  refine ⟨ε, hε, fun u v hu hv => ?_⟩
  have hq := hrat q (by linarith) (by linarith) ⟨U, thm9_1_isACL hgU, hsub⟩ ⟨by linarith, by linarith⟩
  refine hq.mono (uIcc_subset_uIcc ?_ ?_)
  · rw [uIcc_of_le (by linarith)]
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  · rw [uIcc_of_le (by linarith)]
    exact ⟨by linarith [hv.1], by linarith [hv.2]⟩

/-- For almost every `y`, `x ↦ g(x + iy)` is absolutely continuous on `[q₁, q₂]` for every rational
closed rectangle `[q₁, q₂] × [q₃, q₄]` contained in an open set on which `g` is A.C.L., with
`y ∈ (q₃, q₄)` (countably many rectangles). -/
theorem s13x_rm2_horizontal_rat {g : ℂ → ℂ} :
    ∀ᵐ y : ℝ, ∀ q : ℚ × ℚ × ℚ × ℚ, (q.1 : ℝ) < q.2.1 → (q.2.2.1 : ℝ) < q.2.2.2 →
      (∃ U : Set ℂ, IsACL g U ∧ closedRect q.1 q.2.1 q.2.2.1 q.2.2.2 ⊆ U) →
      y ∈ Ioo (q.2.2.1 : ℝ) q.2.2.2 →
      AbsolutelyContinuousOnInterval (fun x : ℝ => g ((x : ℂ) + (y : ℂ) * I)) q.1 q.2.1 := by
  rw [ae_all_iff]
  intro q
  by_cases h : (q.1 : ℝ) < q.2.1 ∧ (q.2.2.1 : ℝ) < q.2.2.2 ∧
      (∃ U : Set ℂ, IsACL g U ∧ closedRect q.1 q.2.1 q.2.2.1 q.2.2.2 ⊆ U)
  · obtain ⟨h1, h2, U, hU, h3⟩ := h
    have hv := (hU.2 _ _ _ _ h1 h2 h3).2
    rw [ae_restrict_iff' measurableSet_Ioo] at hv
    filter_upwards [hv] with y hy _ _ _ hyI
    exact hy hyI
  · exact Eventually.of_forall fun y h1 h2 h3 _ => absurd ⟨h1, h2, h3⟩ h

/-- A property holding a.e. on an open rectangle holds, for almost every `y ∈ (c, d)`, at `x + iy` for
almost every `x ∈ (a, b)` (Fubini for null sets, other order). -/
theorem s13x_rm2_ae_ae_of_ae_rect_symm {P : ℂ → Prop} (hP : MeasurableSet {z | P z}) {a b c d : ℝ}
    (h : ∀ᵐ z ∂(volume.restrict (openRect a b c d)), P z) :
    ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo c d)), ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioo a b)),
      P ((x : ℂ) + (y : ℂ) * I) :=
  (Measure.ae_ae_comm (p := fun (x y : ℝ) => P ((x : ℂ) + (y : ℂ) * I))
    (continuous_rectCoords.measurable hP)).1 (s13x_rm2_ae_ae_of_ae_rect hP h)

/-- On almost every horizontal segment of a rectangle on which `g` is a.e. differentiable,
`x ↦ g(x + iy)` has an integrable derivative: it is `g'(x + iy) 1` a.e. on the segment, and Tonelli
applies to `∫_R |g' 1| < ∞`. -/
theorem s13x_rm2_horizontal_integrable {g : ℂ → ℂ} {a b c d : ℝ}
    (hdiff : ∀ᵐ z ∂(volume.restrict (openRect a b c d)), DifferentiableAt ℝ g z) (hab : a ≤ b)
    (hfin : ∫⁻ z in openRect a b c d, ‖fderiv ℝ g z 1‖ₑ < ∞) :
    ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo c d)),
      IntervalIntegrable (deriv fun x : ℝ => g ((x : ℂ) + (y : ℂ) * I)) volume a b := by
  have hFm : Measurable fun z => ‖fderiv ℝ g z 1‖ₑ :=
    (measurable_fderiv_apply_const ℝ g 1).enorm
  rw [lintegral_openRect_symm hFm] at hfin
  have hc : Continuous fun q : ℝ × ℝ => (q.2 : ℂ) + (q.1 : ℂ) * I := by fun_prop
  have hm : Measurable fun y : ℝ => ∫⁻ x in Ioo a b, ‖fderiv ℝ g ((x : ℂ) + (y : ℂ) * I) 1‖ₑ :=
    (hFm.comp hc.measurable).lintegral_prod_right'
  filter_upwards [ae_lt_top hm hfin.ne,
    s13x_rm2_ae_ae_of_ae_rect_symm (measurableSet_of_differentiableAt ℝ g) hdiff] with y hy1 hy2
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  refine ⟨(measurable_deriv _).aestronglyMeasurable, ?_⟩
  show ∫⁻ x in Ioo a b, ‖deriv (fun x : ℝ => g ((x : ℂ) + (y : ℂ) * I)) x‖ₑ < ∞
  calc ∫⁻ x in Ioo a b, ‖deriv (fun x : ℝ => g ((x : ℂ) + (y : ℂ) * I)) x‖ₑ
      = ∫⁻ x in Ioo a b, ‖fderiv ℝ g ((x : ℂ) + (y : ℂ) * I) 1‖ₑ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hy2] with x hx
        rw [← partialX_ofReal_add, partialX_eq_of_differentiableAt hx]
    _ < ∞ := hy1

/-- A.C.L. across `L`, horizontal lines (the horizontal analogue of `s13x_line_ac_vertical`). -/
theorem s13x_line_ac_horizontal {g : ℂ → ℂ} {Ω L : Set ℂ} {K : ℝ} (hΩ : IsOpen Ω) (hK : 1 ≤ K)
    (hg : IsHomeomorphOnto g Ω (g '' Ω)) (hLnull : volume L = 0)
    (hLh : ∀ᵐ y : ℝ, {x : ℝ | (x : ℂ) + (y : ℂ) * I ∈ L}.Countable)
    (hloc : ∀ z ∈ Ω \ L, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U ⊆ Ω ∧ IsKQC g U K)
    {a b c d : ℝ} (hab : a < b) (hR : closedRect a b c d ⊆ Ω) :
    ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo c d)),
      AbsolutelyContinuousOnInterval (fun x : ℝ => g ((x : ℂ) + (y : ℂ) * I)) a b := by
  obtain ⟨hdiff, hineq⟩ := s13x_rm2_diff_ineq_ae hLnull hloc
  have hfin := s13x_lintegral_fderiv_lt_top hΩ hg (zero_le_one.trans hK) hdiff hineq (v := 1)
    (by simp) hR
  have hdiffR : ∀ᵐ z ∂(volume.restrict (openRect a b c d)), DifferentiableAt ℝ g z :=
    ae_restrict_of_ae_restrict_of_subset ((openRect_subset_closedRect a b c d).trans hR) hdiff
  filter_upwards [s13x_rm2_horizontal_integrable hdiffR hab.le hfin,
    ae_restrict_of_ae (s13x_rm2_horizontal_rat (g := g)), ae_restrict_of_ae hLh,
    ae_restrict_mem measurableSet_Ioo] with y hint hrat hLy hy
  have hmem : ∀ x ∈ Icc a b, (x : ℂ) + (y : ℂ) * I ∈ Ω := fun x hx => hR (by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
        add_zero, add_im, mul_im, zero_add]
    exacts [hx.1, hx.2, hy.1.le, hy.2.le])
  refine abR_c_ac_of_local (S := {x : ℝ | (x : ℂ) + (y : ℂ) * I ∈ L}) hab.le hLy
    (hg.1.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + (y : ℂ) * I).continuousOn hmem)
    hint fun x hx => ?_
  obtain ⟨U, hU, hzU, -, hgU⟩ := hloc _ ⟨hmem x (Ioo_subset_Icc_self hx.1), hx.2⟩
  obtain ⟨q, ε, hε, hsub, h1, h2, h3, h4⟩ := s13x_rm2_rat_rect hU hzU
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
    add_zero, add_im, mul_im, zero_add] at h1 h2 h3 h4
  refine ⟨ε, hε, fun u v hu hv => ?_⟩
  have hq := hrat q (by linarith) (by linarith) ⟨U, thm9_1_isACL hgU, hsub⟩ ⟨by linarith, by linarith⟩
  refine hq.mono (uIcc_subset_uIcc ?_ ?_)
  · rw [uIcc_of_le (by linarith)]
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  · rw [uIcc_of_le (by linarith)]
    exact ⟨by linarith [hv.1], by linarith [hv.2]⟩

/-- **Removability** (Theorem 10.1 (⇐)): a homeomorphism `g` of an open set `Ω` which is `K`-q.c. near every point
of `Ω ∖ L`, where `L` is null and met by almost every horizontal and vertical line in a countable set (e.g. a line
or a segment), is `K`-q.c. on `Ω`. -/
theorem s13x_removable {g : ℂ → ℂ} {Ω L : Set ℂ} {K : ℝ} (hΩ : IsOpen Ω) (hK : 1 ≤ K)
    (hg : IsHomeomorphOnto g Ω (g '' Ω)) (hLnull : volume L = 0)
    (hLv : ∀ᵐ x : ℝ, {y : ℝ | (x : ℂ) + (y : ℂ) * I ∈ L}.Countable)
    (hLh : ∀ᵐ y : ℝ, {x : ℝ | (x : ℂ) + (y : ℂ) * I ∈ L}.Countable)
    (hloc : ∀ z ∈ Ω \ L, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U ⊆ Ω ∧ IsKQC g U K) :
    IsKQC g Ω K := by
  refine (thm10_1_isKQC_iff hΩ hK hg).2 ⟨⟨hg.1, fun a b c d hab hcd hR =>
    ⟨s13x_line_ac_vertical hΩ hK hg hLnull hLv hloc hcd hR,
      s13x_line_ac_horizontal hΩ hK hg hLnull hLh hloc hab hR⟩⟩, ?_⟩
  exact s13x_ae_of_local hLnull fun z hz => by
    obtain ⟨U, hU, hzU, -, hgU⟩ := hloc z hz
    exact ⟨U, hU, hzU, thm9_4_dilatation_ae hgU⟩

/-- The Möbius homeomorphism `z ↦ (z - i)/(z + i)` of `ℂ̄` agrees with the Cayley transform `cayley` on the
upper half-plane. -/
theorem s13x_th_cayleyExt_coe {z : ℂ} (hz : z ∈ upperHalf) :
    mobiusHomeomorph 1 (-I) 1 I cayley_inv_det ((z : ℂ) : ExtPlane) = ((cayley z : ℂ) : ExtPlane) := by
  have hden : (1 : ℂ) * z + I ≠ 0 := by
    rw [one_mul]
    exact cayley_den_ne_zero hz
  rw [mobiusHomeomorph_apply, mobiusExt_coe hden]
  congr 1
  simp only [mobiusFn, cayley, one_mul, sub_eq_add_neg]

/-- The Möbius homeomorphism `z ↦ (z - i)/(z + i)` of `ℂ̄` carries `toExt upperHalf` onto `toExt unitDisc`. -/
theorem s13x_th_cayleyExt_image :
    mobiusHomeomorph 1 (-I) 1 I cayley_inv_det '' toExt upperHalf = toExt unitDisc := by
  rw [← isConformalOnto_cayley.2.2]
  ext p
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [s13x_th_cayleyExt_coe hz]
    exact ⟨cayley z, ⟨z, hz, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨((z : ℂ) : ExtPlane), ⟨z, hz, rfl⟩, s13x_th_cayleyExt_coe hz⟩

/-- **Disc uniformizer of a Jordan domain**: every Jordan domain, bounded or not, has a conformal map onto the unit
disc with a homeomorphic extension (`uq_exists_uniformizer` followed by the Cayley transform). -/
theorem s13x_th_exists_disc_uniformizer {Ω : Set ℂ} (hΩ : IsJordanDomain Ω) :
    ∃ φ : ℂ → ℂ, IsConformalOnto φ Ω unitDisc ∧
      ∃ Φ : ExtPlane → ExtPlane, IsHomeoExtension φ Ω unitDisc Φ := by
  obtain ⟨ψ, hψ, Ψ, hΨ⟩ := uq_exists_uniformizer hΩ
  exact ⟨cayley ∘ ψ, isConformalOnto_cayley.comp hψ,
    ⇑(mobiusHomeomorph 1 (-I) 1 I cayley_inv_det) ∘ Ψ,
    hΨ.comp_homeomorph hψ.mapsTo _ (fun _ hv => s13x_th_cayleyExt_coe hv) s13x_th_cayleyExt_image⟩

/-- A homeomorphic extension of `f` is a homeomorphic extension of every map agreeing with `f` on the domain. -/
theorem s13x_th_isHomeoExtension_congr {f g : ℂ → ℂ} {U V : Set ℂ} {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f U V F) (hfg : EqOn f g U) : IsHomeoExtension g U V F :=
  ⟨fun z hz => by rw [hF.1 z hz, hfg hz], hF.2⟩

/-- **Theorem 13.3** (边界对应定理): a quasiconformal map of a Jordan domain `D` onto a Jordan
domain `D'` extends to a homeomorphism of `D̄` onto `D̄'`. -/
theorem thm13_3_boundary_correspondence {w : ℂ → ℂ} {D D' : Set ℂ} (hD : IsJordanDomain D)
    (hD' : IsJordanDomain D') (hw : IsQuasiconformal w D) (himg : w '' D = D') :
    ∃ F : ExtPlane → ExtPlane, IsHomeoExtension w D D' F := by
  -- uniformize both Jordan domains onto the disc, with homeomorphic extensions
  obtain ⟨φ, hφ, Φ, hΦ⟩ := s13x_th_exists_disc_uniformizer hD
  obtain ⟨φ', hφ', Φ', hΦ'⟩ := s13x_th_exists_disc_uniformizer hD'
  obtain ⟨K, hK⟩ := hw
  have hφi : IsConformalOnto (Function.invFunOn φ D) unitDisc D := hφ.symm hD.1
  have hΦ'i : IsHomeoExtension (Function.invFunOn φ' D') unitDisc D'
      (Function.invFunOn Φ' (closure (toExt D'))) := isHomeoExtension_invFunOn hφ' hΦ'
  -- the transported map `φ' ∘ w ∘ φ⁻¹` is a quasiconformal self-map of the disc
  have hdisc : IsOpen unitDisc := Metric.isOpen_ball
  have himg1 : (w ∘ Function.invFunOn φ D) '' unitDisc = D' := by
    rw [image_comp, hφi.2.2, himg]
  have hK1 : IsKQC (w ∘ Function.invFunOn φ D) unitDisc (1 * K) :=
    thm7_1_comp (isKQC_one_of_conformal hdisc hφi) hK hφi.2.2.subset
  have hK2 : IsKQC (φ' ∘ (w ∘ Function.invFunOn φ D)) unitDisc (1 * K * 1) :=
    thm7_1_comp hK1 (isKQC_one_of_conformal hD'.1 hφ') himg1.subset
  have himg2 : (φ' ∘ (w ∘ Function.invFunOn φ D)) '' unitDisc = unitDisc := by
    rw [image_comp, himg1, hφ'.2.2]
  obtain ⟨H, hH⟩ := s13x_disc_extension ⟨_, hK2⟩ himg2
  -- transport the disc extension back: `w = φ'⁻¹ ∘ (φ' ∘ w ∘ φ⁻¹) ∘ φ` on `D`
  have hmaps : MapsTo ((φ' ∘ (w ∘ Function.invFunOn φ D)) ∘ φ) D unitDisc := by
    intro z hz
    have hmem : (φ' ∘ (w ∘ Function.invFunOn φ D)) (φ z) ∈
        (φ' ∘ (w ∘ Function.invFunOn φ D)) '' unitDisc := mem_image_of_mem _ (hφ.mapsTo hz)
    rwa [himg2] at hmem
  have hF := hΦ'i.comp (hH.comp hΦ hφ.mapsTo) hmaps
  refine ⟨_, s13x_th_isHomeoExtension_congr hF fun z hz => ?_⟩
  have hwz : w z ∈ D' := by
    rw [← himg]
    exact mem_image_of_mem w hz
  show Function.invFunOn φ' D' (φ' (w (Function.invFunOn φ D (φ z)))) = w z
  rw [hφ.2.1.leftInvOn_invFunOn hz, hφ'.2.1.leftInvOn_invFunOn hwz]

/-- A Hölder bound stated with `dist` gives `HolderOnWith`. -/
theorem s13x_ho_holderOnWith_of_dist {f : ℂ → ℂ} {s : Set ℂ} {C r : ℝ≥0}
    (h : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ C * dist x y ^ (r : ℝ)) :
    HolderOnWith C r f s := by
  intro x hx y hy
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg r.coe_nonneg,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (h x hx y hy)

/-- Separation for an off-centre annulus: if `G` is continuous and injective on `D ⊇ B(z₀, δ)`,
`G(B(z₀, δ))` is open and contained in `Δ`, and `ρ < δ`, then `G({ρ < |z - z₀| < δ})` separates the unit
circle from `{G a, G b}` for `|a - z₀|, |b - z₀| ≤ ρ`: `ℂ̄ ∖ G(A)` is the union of the disjoint closed sets
`G(|z - z₀| ≤ ρ)` (connected, containing `G a, G b`) and `ℂ̄ ∖ G(B(z₀, δ))` (containing the circle). -/
theorem s13x_ho_separates {G : ℂ → ℂ} {D : Set ℂ} (hGc : ContinuousOn G D) (hGi : InjOn G D)
    {z₀ : ℂ} {ρ δ : ℝ} (hρδ : ρ < δ) (hball : ball z₀ δ ⊆ D) (hopen : IsOpen (G '' ball z₀ δ))
    (hsub : G '' ball z₀ δ ⊆ unitDisc) {a b : ℂ} (ha : ‖a - z₀‖ ≤ ρ) (hb : ‖b - z₀‖ ≤ ρ) :
    SeparatesSets (G '' annulusAt z₀ ρ δ) (toExt (sphere 0 1))
      {((G a : ℂ) : ExtPlane), ((G b : ℂ) : ExtPlane)} := by
  set S : Set ExtPlane := (toExt (G '' annulusAt z₀ ρ δ))ᶜ with hS
  set P : Set ExtPlane := toExt (G '' closedBall z₀ ρ) with hP
  set Q : Set ExtPlane := (toExt (G '' ball z₀ δ))ᶜ with hQ
  have hcb : closedBall z₀ ρ ⊆ ball z₀ δ := closedBall_subset_ball hρδ
  have hcbD : closedBall z₀ ρ ⊆ D := hcb.trans hball
  have hAD : annulusAt z₀ ρ δ ⊆ D := fun w hw => hball (mem_ball_iff_norm.2 hw.2)
  have hPc : IsClosed P :=
    (((isCompact_closedBall z₀ ρ).image_of_continuousOn (hGc.mono hcbD)).image
      OnePoint.continuous_coe).isClosed
  have hQc : IsClosed Q := isClosed_compl_toExt hopen
  have hPB : P ⊆ toExt (G '' ball z₀ δ) := image_mono (image_mono hcb)
  have hPS : P ⊆ S := by
    rintro _ ⟨w, ⟨u, hu, rfl⟩, rfl⟩ ⟨v, ⟨u', hu', rfl⟩, hv⟩
    have huu : u' = u := hGi (hAD hu') (hcbD hu) (OnePoint.coe_injective hv)
    subst huu
    exact absurd (mem_closedBall_iff_norm.1 hu) (not_le.2 hu'.1)
  have hSPQ : S ⊆ P ∪ Q := by
    intro x hx
    induction x using OnePoint.rec with
    | infty => exact Or.inr (extInf_notMem_toExt _)
    | coe w =>
      by_cases hw : w ∈ G '' ball z₀ δ
      · left
        obtain ⟨u, hu, rfl⟩ := hw
        refine ⟨G u, ⟨u, ?_, rfl⟩, rfl⟩
        rw [mem_closedBall_iff_norm]
        by_contra hlt
        push Not at hlt
        exact hx ⟨G u, ⟨u, ⟨hlt, mem_ball_iff_norm.1 hu⟩, rfl⟩, rfl⟩
      · right
        exact fun h => hw (coe_mem_toExt_iff.1 h)
  have hPQ : P ∩ Q = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hxP hxQ
    exact hxQ (hPB hxP)
  have hsph : IsPreconnected (toExt (sphere (0 : ℂ) 1)) :=
    (isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) 0 1).image _
      OnePoint.continuous_coe.continuousOn
  have h1sph : ((1 : ℂ) : ExtPlane) ∈ toExt (sphere (0 : ℂ) 1) := ⟨1, by simp, rfl⟩
  have hsphB : ∀ w ∈ sphere (0 : ℂ) 1, w ∉ G '' ball z₀ δ := fun w hw hwB =>
    absurd (mem_sphere_zero_iff_norm.1 hw) (ne_of_lt (mem_ball_zero_iff.1 (hsub hwB)))
  have hsphS : toExt (sphere (0 : ℂ) 1) ⊆ S := by
    rintro _ ⟨w, hw, rfl⟩ ⟨v, ⟨u, hu, rfl⟩, hv⟩
    exact hsphB w hw ⟨u, mem_ball_iff_norm.2 hu.2, OnePoint.coe_injective hv⟩
  have hPconn : IsPreconnected P :=
    (isPreconnected_closedBall.image G (hGc.mono hcbD)).image _
      OnePoint.continuous_coe.continuousOn
  have haP : ((G a : ℂ) : ExtPlane) ∈ P := ⟨G a, ⟨a, mem_closedBall_iff_norm.2 ha, rfl⟩, rfl⟩
  have hbP : ((G b : ℂ) : ExtPlane) ∈ P := ⟨G b, ⟨b, mem_closedBall_iff_norm.2 hb, rfl⟩, rfl⟩
  have hPcomp : P ⊆ connectedComponentIn S ((G a : ℂ) : ExtPlane) :=
    hPconn.subset_connectedComponentIn haP hPS
  refine ⟨((1 : ℂ) : ExtPlane), hsphS h1sph, ((G a : ℂ) : ExtPlane), hPS haP,
    hsph.subset_connectedComponentIn h1sph hsphS,
    insert_subset_iff.2 ⟨hPcomp haP, singleton_subset_iff.2 (hPcomp hbP)⟩, ?_⟩
  intro heq
  have hC := isPreconnected_iff_subset_of_disjoint_closed.1
    (isPreconnected_connectedComponentIn (x := ((G a : ℂ) : ExtPlane)) (F := S)) P Q hPc hQc
    ((connectedComponentIn_subset _ _).trans hSPQ) (by rw [hPQ, inter_empty])
  have hmem1 : ((1 : ℂ) : ExtPlane) ∈ connectedComponentIn S ((G a : ℂ) : ExtPlane) :=
    heq ▸ mem_connectedComponentIn (hsphS h1sph)
  have hmema : ((G a : ℂ) : ExtPlane) ∈ connectedComponentIn S ((G a : ℂ) : ExtPlane) :=
    mem_connectedComponentIn (hPS haP)
  rcases hC with hC | hC
  · have h1 := hPB (hC hmem1)
    rw [coe_mem_toExt_iff] at h1
    exact hsphB 1 (by simp) h1
  · exact hC hmema (hPB haP)

/-- Core modulus estimate: if `G` is `K`-q.c. on `D ⊇ B̄(z₀, δ)`, `G(B(z₀, δ)) ⊆ Δ`, `G z₀ = 0` and
`G z₂ = r > 0` with `|z₂ - z₀| ≤ ρ < δ`, then `log(δ/ρ) ≤ K log(4/r)` (Theorem 7.4 on the annulus
`ρ < |z - z₀| < δ`, Grötzsch's Theorem 5.1 and the upper half of (14.27)). -/
theorem s13x_ho_log_le {G : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hG : IsKQC G D K) {z₀ z₂ : ℂ}
    {ρ δ r : ℝ} (hρ : 0 < ρ) (hρδ : ρ < δ) (hD : closedBall z₀ δ ⊆ D)
    (hsub : G '' ball z₀ δ ⊆ unitDisc) (h0 : G z₀ = 0) (hz₂ : ‖z₂ - z₀‖ ≤ ρ) (hr : 0 < r)
    (h2 : G z₂ = (r : ℂ)) : Real.log (δ / ρ) ≤ K * Real.log (4 / r) := by
  have hGc : ContinuousOn G D := hG.2.2.1.1
  have hGi : InjOn G D := hG.2.2.1.2.1
  have hballD : ball z₀ δ ⊆ D := ball_subset_closedBall.trans hD
  have hopen : IsOpen (G '' ball z₀ δ) :=
    aqc_isOpen_image_of_isHomeomorphOnto hG.2.2.1 (isOpen_image_of_isKQC hG) hballD isOpen_ball
  have hz₂B : z₂ ∈ ball z₀ δ := mem_ball_iff_norm.2 (hz₂.trans_lt hρδ)
  have hr1 : r < 1 := by
    have h := hsub ⟨z₂, hz₂B, rfl⟩
    rw [h2, unitDisc, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h
    exact h
  have hA : IsDoublyConnected (annulusAt z₀ ρ δ) := nf_g_isDoublyConnected_annulusAt z₀ hρ hρδ
  have hAD : closure (toExt (annulusAt z₀ ρ δ)) ⊆ toExt D :=
    (nf_e_closure_toExt_subset (isCompact_closedBall z₀ δ)
      fun w hw => mem_closedBall_iff_norm.2 hw.2.le).trans (image_mono hD)
  obtain ⟨hB, hAB, -⟩ := thm7_4_dcModulus_quasi_invariance hG hA hAD
  have hBsub : G '' annulusAt z₀ ρ δ ⊆ unitDisc :=
    (image_mono fun w hw => mem_ball_iff_norm.2 hw.2).trans hsub
  have hsep : SeparatesSets (G '' annulusAt z₀ ρ δ) (toExt (sphere 0 1))
      {((0 : ℂ) : ExtPlane), ((r : ℂ) : ExtPlane)} := by
    have h := s13x_ho_separates hGc hGi hρδ hballD hopen hsub (a := z₀) (b := z₂)
      (by rw [sub_self, norm_zero]; exact hρ.le) hz₂
    rwa [h0, h2] at h
  have hgr := thm5_1_grotzsch hr hr1 hB hBsub hsep
  rw [gz_dcModulus_grotzschDomain hr hr1, ← gm_grotzschMu_eq hr hr1] at hgr
  rw [nf_e_dcModulus_annulusAt z₀ hρ hρδ] at hAB
  have hK0 : 0 ≤ K := zero_le_one.trans hG.2.1
  have hmu0 : 0 ≤ grotzschMu r := ENNReal.toReal_nonneg
  have key : ENNReal.ofReal (Real.log (δ / ρ)) ≤ ENNReal.ofReal (K * grotzschMu r) := by
    rw [ENNReal.ofReal_mul hK0]
    calc ENNReal.ofReal (Real.log (δ / ρ))
        ≤ ENNReal.ofReal K * dcModulus (G '' annulusAt z₀ ρ δ) := hAB
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal (grotzschMu r) := by gcongr
  rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK0 hmu0)] at key
  exact key.trans (mul_le_mul_of_nonneg_left (em_upper hr hr1) hK0)

/-- Distortion at a point: if `f` is `K`-q.c. on `D ⊇ B̄(z₁, δ)`, `|f ζ - f z₁| < R` on `B(z₁, δ)` and
`0 < |z₂ - z₁| < δ`, then `|f z₂ - f z₁| ≤ 4R (|z₂ - z₁|/δ)^{1/K}` (normalize by the similarity
`w ↦ c (w - f z₁)` taking `f z₁ ↦ 0` and `f z₂ ↦ |f z₂ - f z₁|/R`, then `s13x_ho_log_le`). -/
theorem s13x_ho_dist_le {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) {z₁ z₂ : ℂ} {δ R : ℝ}
    (hD : closedBall z₁ δ ⊆ D) (hR : ∀ ζ ∈ ball z₁ δ, ‖f ζ - f z₁‖ < R)
    (hpos : 0 < ‖z₂ - z₁‖) (hlt : ‖z₂ - z₁‖ < δ) :
    ‖f z₂ - f z₁‖ ≤ 4 * R * (‖z₂ - z₁‖ / δ) ^ (1 / K) := by
  have hδ : 0 < δ := hpos.trans hlt
  have hz₁B : z₁ ∈ ball z₁ δ := mem_ball_self hδ
  have hRpos : 0 < R := (norm_nonneg _).trans_lt (hR z₁ hz₁B)
  have hz₂D : z₂ ∈ D := hD (mem_closedBall_iff_norm.2 hlt.le)
  have hz₁D : z₁ ∈ D := hD (mem_closedBall_self hδ.le)
  have hne : z₂ ≠ z₁ := fun h => by rw [h, sub_self, norm_zero] at hpos; exact lt_irrefl _ hpos
  set d : ℂ := f z₂ - f z₁ with hd
  have hd0 : d ≠ 0 := fun h => hne (hf.2.2.1.2.1 hz₂D hz₁D (sub_eq_zero.1 h))
  set t : ℝ := ‖d‖ with ht
  have htpos : 0 < t := norm_pos_iff.2 hd0
  have htR : 0 < t * R := mul_pos htpos hRpos
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 htpos.ne'
  have hRc : (R : ℂ) ≠ 0 := ofReal_ne_zero.2 hRpos.ne'
  set c : ℂ := conj d / ((t * R : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := div_ne_zero ((map_ne_zero _).2 hd0) (ofReal_ne_zero.2 htR.ne')
  have hcn : ‖c‖ = 1 / R := by
    rw [hc, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htR, ← ht]
    field_simp
  set T : ℂ → ℂ := fun w => c * (w - f z₁) with hT
  have hTq : IsKQC T univ 1 := isKQC_one_of_conformal isOpen_univ
    ⟨((differentiable_id.sub_const _).const_mul c).differentiableOn,
      fun a _ b _ h => sub_left_injective (mul_left_cancel₀ hc0 h), rfl⟩
  have hG : IsKQC (T ∘ f) D K := by
    have h := thm7_1_comp hf hTq (subset_univ _)
    rwa [mul_one] at h
  have hsub : (T ∘ f) '' ball z₁ δ ⊆ unitDisc := by
    rintro _ ⟨ζ, hζ, rfl⟩
    rw [unitDisc, mem_ball_zero_iff]
    show ‖c * (f ζ - f z₁)‖ < 1
    rw [norm_mul, hcn, one_div, inv_mul_lt_iff₀ hRpos, mul_one]
    exact hR ζ hζ
  have h0 : (T ∘ f) z₁ = 0 := by
    show c * (f z₁ - f z₁) = 0
    rw [sub_self, mul_zero]
  have h2 : (T ∘ f) z₂ = ((t / R : ℝ) : ℂ) := by
    show c * d = _
    rw [hc, div_mul_eq_mul_div, Complex.conj_mul', ← ht]
    push_cast
    field_simp
  have hlog := s13x_ho_log_le hG hpos hlt hD hsub h0 le_rfl (div_pos htpos hRpos) h2
  -- conversion to `t ≤ 4R (ρ/δ)^{1/K}`
  have hK : 0 < K := zero_lt_one.trans_le hf.2.1
  set ρ := ‖z₂ - z₁‖ with hρ
  have hρδ : 0 < ρ / δ := div_pos hpos hδ
  have hx : 0 < (ρ / δ) ^ (1 / K) := Real.rpow_pos_of_pos hρδ _
  have hlogx : Real.log ((ρ / δ) ^ (1 / K)) = -(Real.log (δ / ρ) / K) := by
    rw [Real.log_rpow hρδ, ← inv_div δ ρ, Real.log_inv]
    ring
  have h4 : Real.log (4 / (t / R)) = -Real.log (t / (4 * R)) := by
    rw [← Real.log_inv, inv_div]
    congr 1
    field_simp
  have key : Real.log (t / (4 * R)) ≤ Real.log ((ρ / δ) ^ (1 / K)) := by
    rw [hlogx, le_neg, ← h4, div_le_iff₀ hK]
    linarith [hlog]
  have hle := (Real.log_le_log_iff (by positivity) hx).1 key
  rw [div_le_iff₀ (by positivity)] at hle
  linarith

/-- On a compact `F ⊆ D`, a `K`-q.c. map `f` satisfies `|f x - f y| ≤ C |x - y|^{1/K}`: take `δ > 0` with
`F_δ ⊆ D` (closed `δ`-neighbourhood), a bound `M` for `|f|` on the compact `F_δ` and `R = 2M + 1`; for
`|x - y| < δ` use `s13x_ho_dist_le`, for `|x - y| ≥ δ` the bound `|f x - f y| ≤ 2M`. -/
theorem s13x_ho_exists_bound {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hf : IsKQC f D K) {F : Set ℂ}
    (hFD : F ⊆ D) (hF : IsCompact F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ F, ∀ y ∈ F, dist (f x) (f y) ≤ C * dist x y ^ (1 / K) := by
  have hK0 : 0 < K := zero_lt_one.trans_le hf.2.1
  obtain ⟨δ, hδ, hδD⟩ := hF.exists_cthickening_subset_open hf.1 hFD
  have hfc : ContinuousOn f (cthickening δ F) := hf.2.2.1.1.mono hδD
  obtain ⟨M₀, hM₀⟩ := (hF.cthickening.image_of_continuousOn hfc).isBounded.exists_norm_le
  set M := max M₀ 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMb : ∀ ζ ∈ cthickening δ F, ‖f ζ‖ ≤ M := fun ζ hζ =>
    (hM₀ _ ⟨ζ, hζ, rfl⟩).trans (le_max_left _ _)
  set R := 2 * M + 1 with hR
  have hRpos : 0 < R := by positivity
  refine ⟨4 * R / δ ^ (1 / K), by positivity, fun x hx y hy => ?_⟩
  have hxF : ∀ ζ ∈ closedBall x δ, ‖f ζ‖ ≤ M := fun ζ hζ =>
    hMb ζ (closedBall_subset_cthickening hx δ hζ)
  have hbound : dist (f x) (f y) ≤ 4 * R * (dist x y / δ) ^ (1 / K) := by
    rcases eq_or_lt_of_le (dist_nonneg : 0 ≤ dist x y) with h0 | hpos
    · rw [← h0, zero_div, Real.zero_rpow (one_div_pos.2 hK0).ne', mul_zero]
      rw [eq_comm, dist_eq_zero] at h0
      rw [h0, dist_self]
    rcases lt_or_ge (dist x y) δ with hlt | hge
    · -- near points: the Grötzsch estimate
      have hyx : ‖y - x‖ = dist x y := by rw [dist_eq_norm, norm_sub_rev]
      have hRball : ∀ ζ ∈ ball x δ, ‖f ζ - f x‖ < R := fun ζ hζ => by
        calc ‖f ζ - f x‖ ≤ ‖f ζ‖ + ‖f x‖ := norm_sub_le _ _
          _ ≤ M + M := add_le_add (hxF ζ (ball_subset_closedBall hζ))
              (hxF x (mem_closedBall_self hδ.le))
          _ < R := by linarith
      have h := s13x_ho_dist_le hf ((closedBall_subset_cthickening hx δ).trans hδD) hRball
        (by rw [hyx]; exact hpos) (by rw [hyx]; exact hlt)
      rw [dist_eq_norm, norm_sub_rev, ← hyx]
      exact h
    · -- far points: the trivial bound
      have h1 : 1 ≤ (dist x y / δ) ^ (1 / K) :=
        Real.one_le_rpow ((one_le_div hδ).2 hge) (one_div_pos.2 hK0).le
      calc dist (f x) (f y) ≤ ‖f x‖ + ‖f y‖ := by rw [dist_eq_norm]; exact norm_sub_le _ _
        _ ≤ M + M := add_le_add (hMb x (self_subset_cthickening _ hx))
            (hMb y (self_subset_cthickening _ hy))
        _ ≤ 4 * R * 1 := by linarith
        _ ≤ 4 * R * (dist x y / δ) ^ (1 / K) := by gcongr
  rw [Real.div_rpow dist_nonneg hδ.le] at hbound
  calc dist (f x) (f y) ≤ 4 * R * (dist x y ^ (1 / K) / δ ^ (1 / K)) := hbound
    _ = 4 * R / δ ^ (1 / K) * dist x y ^ (1 / K) := by ring

/-- §13.4: every `K`-q.c. map is locally Hölder continuous, with a Hölder exponent depending
only on `K`. -/
theorem qc_holder {K : ℝ} (hK : 1 ≤ K) :
    ∃ α : ℝ≥0, 0 < α ∧ ∀ (D : Set ℂ) (f : ℂ → ℂ), Bornology.IsBounded D → IsKQC f D K →
      ∀ F ⊆ D, IsCompact F → ∃ C : ℝ≥0, HolderOnWith C α f F := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hα : 0 ≤ 1 / K := (one_div_pos.2 hK0).le
  refine ⟨Real.toNNReal (1 / K), Real.toNNReal_pos.2 (one_div_pos.2 hK0),
    fun D f _ hf F hFD hF => ?_⟩
  obtain ⟨C, hC0, hC⟩ := s13x_ho_exists_bound hf hFD hF
  refine ⟨Real.toNNReal C, s13x_ho_holderOnWith_of_dist fun x hx y hy => ?_⟩
  rw [Real.coe_toNNReal _ hC0, Real.coe_toNNReal _ hα]
  exact hC x hx y hy

/-- A nondegenerate open segment `(a, b)` of `ℂ` is Lebesgue-null: it lies in the proper affine line
`a + ℝ (b - a)`. -/
theorem s13x_ar_volume_openSegment {a b : ℂ} (hab : a ≠ b) : volume (openSegment ℝ a b) = 0 := by
  have hsub : openSegment ℝ a b ⊆ (AffineSubspace.mk' a (ℝ ∙ (b - a)) : Set ℂ) := by
    rw [openSegment_eq_image']
    rintro _ ⟨t, -, rfl⟩
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub, add_sub_cancel_left]
    exact Submodule.smul_mem _ t (Submodule.mem_span_singleton_self _)
  have hne : AffineSubspace.mk' a (ℝ ∙ (b - a)) ≠ ⊤ := by
    intro h
    have hmem : a + I * (b - a) ∈ AffineSubspace.mk' a (ℝ ∙ (b - a)) := by
      rw [h]; exact AffineSubspace.mem_top ℝ ℂ _
    rw [AffineSubspace.mem_mk', vsub_eq_sub, add_sub_cancel_left,
      Submodule.mem_span_singleton] at hmem
    obtain ⟨r, hr⟩ := hmem
    rw [Complex.real_smul] at hr
    have hrI : (r : ℂ) = I := mul_right_cancel₀ (sub_ne_zero.2 hab.symm) hr
    simpa using congrArg Complex.im hrI
  exact measure_mono_null hsub (Measure.addHaar_affineSubspace volume _ hne)

/-- Coordinates of a point of the open segment `(a, b)`: `z = a + t (b - a)` for a real `t`. -/
theorem s13x_ar_openSegment_coords {a b z : ℂ} (hz : z ∈ openSegment ℝ a b) :
    ∃ t : ℝ, z.re = a.re + t * (b.re - a.re) ∧ z.im = a.im + t * (b.im - a.im) := by
  rw [openSegment_eq_image'] at hz
  obtain ⟨t, -, rfl⟩ := hz
  exact ⟨t, by simp, by simp⟩

/-- Almost every vertical line meets the open segment `(a, b)` in a countable set: every vertical line other than
`Re z = Re a` meets it in at most one point. -/
theorem s13x_ar_vertical_countable (a b : ℂ) :
    ∀ᵐ x : ℝ, {y : ℝ | (x : ℂ) + (y : ℂ) * I ∈ openSegment ℝ a b}.Countable := by
  filter_upwards [(Set.countable_singleton a.re).ae_notMem volume] with x hx
  have hx' : x ≠ a.re := hx
  refine Set.Subsingleton.countable fun y₁ hy₁ y₂ hy₂ => ?_
  obtain ⟨t₁, h1r, h1i⟩ :=
    s13x_ar_openSegment_coords (a := a) (b := b) (z := (x : ℂ) + (y₁ : ℂ) * I) hy₁
  obtain ⟨t₂, h2r, h2i⟩ :=
    s13x_ar_openSegment_coords (a := a) (b := b) (z := (x : ℂ) + (y₂ : ℂ) * I) hy₂
  simp at h1r h1i h2r h2i
  have hd : b.re - a.re ≠ 0 := by
    intro hd
    exact hx' (by rw [h1r, hd, mul_zero, add_zero])
  have ht : t₁ = t₂ := mul_right_cancel₀ hd (by linarith)
  rw [h1i, h2i, ht]

/-- Almost every horizontal line meets the open segment `(a, b)` in a countable set: every horizontal line other
than `Im z = Im a` meets it in at most one point. -/
theorem s13x_ar_horizontal_countable (a b : ℂ) :
    ∀ᵐ y : ℝ, {x : ℝ | (x : ℂ) + (y : ℂ) * I ∈ openSegment ℝ a b}.Countable := by
  filter_upwards [(Set.countable_singleton a.im).ae_notMem volume] with y hy
  have hy' : y ≠ a.im := hy
  refine Set.Subsingleton.countable fun x₁ hx₁ x₂ hx₂ => ?_
  obtain ⟨t₁, h1r, h1i⟩ :=
    s13x_ar_openSegment_coords (a := a) (b := b) (z := (x₁ : ℂ) + (y : ℂ) * I) hx₁
  obtain ⟨t₂, h2r, h2i⟩ :=
    s13x_ar_openSegment_coords (a := a) (b := b) (z := (x₂ : ℂ) + (y : ℂ) * I) hx₂
  simp at h1r h1i h2r h2i
  have hd : b.im - a.im ≠ 0 := by
    intro hd
    exact hy' (by rw [h1i, hd, mul_zero, add_zero])
  have ht : t₁ = t₂ := mul_right_cancel₀ hd (by linarith)
  rw [h1r, h2r, ht]

/-- §13.5 (拟共形延拓): let `fⱼ` be quasiconformal maps of the disjoint Jordan domains `Dⱼ`
onto disjoint domains, extending continuously to a common boundary arc `γ` on which they
agree.  Then the map equal to `f₁` on `D₁ ∪ γ` and to `f₂` on `D₂` is quasiconformal on
`D₁ ∪ D₂ ∪ γ`.

*Correction (2026-09-24, user-approved).*  The book allows an arbitrary Jordan arc `γ`; that is false in general
(there are non-removable Jordan curves: a homeomorphism can be conformal on both sides of such a curve without being
quasiconformal across it — Kaufman 1984, Bishop 1994), and the book's proof silently assumes `γ` removable.  Here
`γ` is an open line segment (the case used in the book: reflection across lines).  The book's hypothesis that `fⱼ`
extends HOMEOMORPHICALLY to `γ` is also made explicit (`InjOn fⱼ (Dⱼ ∪ γ)`). -/
theorem qc_extension_across_arc {f f₁ f₂ : ℂ → ℂ} {D₁ D₂ γ : Set ℂ} (hD₁ : IsJordanDomain D₁)
    (hD₂ : IsJordanDomain D₂) (hdisj : Disjoint D₁ D₂) (hdisj' : Disjoint (f₁ '' D₁) (f₂ '' D₂))
    (hq₁ : IsQuasiconformal f₁ D₁) (hq₂ : IsQuasiconformal f₂ D₂)
    (hγ : ∃ a b : ℂ, a ≠ b ∧ γ = openSegment ℝ a b)
    (hγsub : γ ⊆ frontier D₁ ∩ frontier D₂) (hopen : IsOpen (D₁ ∪ D₂ ∪ γ))
    (hc₁ : ContinuousOn f₁ (D₁ ∪ γ)) (hc₂ : ContinuousOn f₂ (D₂ ∪ γ))
    (hi₁ : InjOn f₁ (D₁ ∪ γ)) (hi₂ : InjOn f₂ (D₂ ∪ γ)) (hagree : EqOn f₁ f₂ γ)
    (hf₁ : EqOn f f₁ (D₁ ∪ γ)) (hf₂ : EqOn f f₂ D₂) :
    IsQuasiconformal f (D₁ ∪ D₂ ∪ γ) := by
  have _ := hdisj
  have _ := hγsub
  obtain ⟨a, b, hab, rfl⟩ := hγ
  obtain ⟨K₁, hK₁⟩ := hq₁
  obtain ⟨K₂, hK₂⟩ := hq₂
  have hD₁o : IsOpen D₁ := hD₁.1
  have hD₂o : IsOpen D₂ := hD₂.1
  have hf₂' : EqOn f f₂ (D₂ ∪ openSegment ℝ a b) := by
    rintro z (hz | hz)
    · exact hf₂ hz
    · exact (hf₁ (Or.inr hz)).trans (hagree hz)
  have hcont : ContinuousOn f (D₁ ∪ D₂ ∪ openSegment ℝ a b) := by
    have h1 : ContinuousOn f (D₁ ∪ openSegment ℝ a b) := hc₁.congr hf₁
    have h2 : ContinuousOn f (D₂ ∪ openSegment ℝ a b) := hc₂.congr hf₂'
    rintro z ((hz | hz) | hz)
    · exact (h1.continuousAt
        (mem_of_superset (hD₁o.mem_nhds hz) subset_union_left)).continuousWithinAt
    · exact (h2.continuousAt
        (mem_of_superset (hD₂o.mem_nhds hz) subset_union_left)).continuousWithinAt
    · have h := (h1 z (Or.inr hz)).union (h2 z (Or.inr hz))
      have hset : D₁ ∪ openSegment ℝ a b ∪ (D₂ ∪ openSegment ℝ a b) =
          D₁ ∪ D₂ ∪ openSegment ℝ a b := by
        ext w; simp only [mem_union]; tauto
      rwa [hset] at h
  have hinj : InjOn f (D₁ ∪ D₂ ∪ openSegment ℝ a b) := by
    have hi₁' : InjOn f (D₁ ∪ openSegment ℝ a b) := hi₁.congr hf₁.symm
    have hi₂' : InjOn f (D₂ ∪ openSegment ℝ a b) := hi₂.congr hf₂'.symm
    have hcross : ∀ z ∈ D₁, ∀ w ∈ D₂, f z ≠ f w := by
      intro z hz w hw hzw
      rw [hf₁ (Or.inl hz), hf₂ hw] at hzw
      exact disjoint_left.1 hdisj' (mem_image_of_mem f₁ hz)
        (by rw [hzw]; exact mem_image_of_mem f₂ hw)
    rintro z hz w hw hzw
    rcases hz with (hz | hz) | hz <;> rcases hw with (hw | hw) | hw
    · exact hi₁' (Or.inl hz) (Or.inl hw) hzw
    · exact absurd hzw (hcross z hz w hw)
    · exact hi₁' (Or.inl hz) (Or.inr hw) hzw
    · exact absurd hzw.symm (hcross w hw z hz)
    · exact hi₂' (Or.inl hz) (Or.inl hw) hzw
    · exact hi₂' (Or.inl hz) (Or.inr hw) hzw
    · exact hi₁' (Or.inr hz) (Or.inl hw) hzw
    · exact hi₂' (Or.inr hz) (Or.inl hw) hzw
    · exact hi₁' (Or.inr hz) (Or.inr hw) hzw
  have hhom : IsHomeomorphOnto f (D₁ ∪ D₂ ∪ openSegment ℝ a b)
      (f '' (D₁ ∪ D₂ ∪ openSegment ℝ a b)) :=
    qcl_f_isHomeomorphOnto_of_injOn hopen hcont hinj
  have hK : 1 ≤ max K₁ K₂ := hK₁.2.1.trans (le_max_left _ _)
  refine ⟨max K₁ K₂, s13x_removable hopen hK hhom (L := openSegment ℝ a b)
    (s13x_ar_volume_openSegment hab) (s13x_ar_vertical_countable a b)
    (s13x_ar_horizontal_countable a b) ?_⟩
  rintro z ⟨(hz | hz) | hz, hzγ⟩
  · refine ⟨D₁, hD₁o, hz, fun w hw => Or.inl (Or.inl hw), ?_⟩
    exact ad_isKQC_congr (hK₁.mono (le_max_left _ _)) (hf₁.mono subset_union_left)
  · refine ⟨D₂, hD₂o, hz, fun w hw => Or.inl (Or.inr hw), ?_⟩
    exact ad_isKQC_congr (hK₂.mono (le_max_right _ _)) hf₂
  · exact absurd hz hzγ

/-- A point of the closed upper half-plane lies in the closure of `ℍ` in `ℂ̄`. -/
theorem s13x_rf_coe_mem_closure {z : ℂ} (hz : 0 ≤ z.im) :
    (z : ExtPlane) ∈ closure (toExt upperHalf) := by
  rw [scExt_closure_toExt_upperHalf]
  exact Or.inl ⟨z, hz, rfl⟩

/-- `∞` lies in the closure of `ℍ` in `ℂ̄`. -/
theorem s13x_rf_infty_mem_closure : extInf ∈ closure (toExt upperHalf) := by
  rw [scExt_closure_toExt_upperHalf]
  exact Or.inr rfl

/-- A boundary extension `F` of a self-map `f` of `ℍ` with `f(z) → ∞` as `z → ∞` in `ℍ` fixes `∞`. -/
theorem s13x_rf_infty {f : ℂ → ℂ} {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f upperHalf upperHalf F)
    (hinf : Tendsto f (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ)) : F extInf = extInf := by
  set γ : ℕ → ℂ := fun n => (((n : ℝ) + 1 : ℝ) : ℂ) * I with hγdef
  have hγU : ∀ n, γ n ∈ upperHalf := fun n => by
    show 0 < (γ n).im
    simp only [hγdef, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_one, zero_mul, add_zero]
    positivity
  have hγ : Tendsto γ atTop (cocompact ℂ) := by
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    have hn : ∀ n : ℕ, (n : ℝ) + 1 = ‖γ n‖ := fun n => by
      simp only [hγdef, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact (abs_of_pos (by positivity)).symm
    exact (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).congr hn
  have hc : Tendsto ((↑) : ℂ → ExtPlane) (cocompact ℂ) (𝓝 extInf) := by
    rw [← coclosedCompact_eq_cocompact]
    exact OnePoint.tendsto_coe_infty
  have h1 : Tendsto (fun n => (γ n : ExtPlane)) atTop (𝓝 extInf) := hc.comp hγ
  have h2 := hF.tendsto_comp s13x_rf_infty_mem_closure (Eventually.of_forall hγU) h1
  have h3 : Tendsto (fun n => (f (γ n) : ExtPlane)) atTop (𝓝 extInf) :=
    hc.comp (hinf.comp (tendsto_inf.2 ⟨hγ, tendsto_principal.2 (Eventually.of_forall hγU)⟩))
  exact tendsto_nhds_unique h2 h3

/-- On the closed upper half-plane, a boundary extension `F` fixing `∞` takes the finite value
`abR_t_fin F z`, which again lies in the closed upper half-plane. -/
theorem s13x_rf_fin_spec {f : ℂ → ℂ} {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f upperHalf upperHalf F) (hFinf : F extInf = extInf) {z : ℂ}
    (hz : 0 ≤ z.im) :
    F (z : ExtPlane) = ((abR_t_fin F z : ℂ) : ExtPlane) ∧ 0 ≤ (abR_t_fin F z).im := by
  have hmem : F (z : ExtPlane) ∈ closure (toExt upperHalf) := by
    rw [← hF.2.2.2]
    exact mem_image_of_mem F (s13x_rf_coe_mem_closure hz)
  rw [scExt_closure_toExt_upperHalf] at hmem
  rcases hmem with ⟨w, hw, hwz⟩ | hinf
  · rw [abR_t_fin_of_eq hwz.symm]
    exact ⟨hwz.symm, hw⟩
  · exfalso
    rw [mem_singleton_iff, ← hFinf] at hinf
    exact OnePoint.coe_ne_infty z
      (hF.2.2.1 (s13x_rf_coe_mem_closure hz) s13x_rf_infty_mem_closure hinf)

/-- On `ℍ`, the finite value of the boundary extension `F` is `f`. -/
theorem s13x_rf_fin_eq {f : ℂ → ℂ} {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f upperHalf upperHalf F) {z : ℂ} (hz : z ∈ upperHalf) :
    abR_t_fin F z = f z :=
  abR_t_fin_of_eq (hF.1 z hz)

/-- The finite value of `F` is injective on the closed upper half-plane. -/
theorem s13x_rf_fin_injOn {f : ℂ → ℂ} {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f upperHalf upperHalf F) (hFinf : F extInf = extInf) :
    InjOn (abR_t_fin F) {z : ℂ | 0 ≤ z.im} := by
  intro z₁ hz₁ z₂ hz₂ heq
  refine OnePoint.coe_injective
    (hF.2.2.1 (s13x_rf_coe_mem_closure hz₁) (s13x_rf_coe_mem_closure hz₂) ?_)
  rw [(s13x_rf_fin_spec hF hFinf hz₁).1, (s13x_rf_fin_spec hF hFinf hz₂).1, heq]

/-- The finite value of `F` maps `ℍ` into `ℍ`. -/
theorem s13x_rf_fin_pos {f : ℂ → ℂ} {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f upperHalf upperHalf F) (himg : f '' upperHalf = upperHalf) {z : ℂ}
    (hz : 0 < z.im) : 0 < (abR_t_fin F z).im := by
  have hzU : z ∈ upperHalf := hz
  have hmem : f z ∈ upperHalf := by
    rw [← himg]
    exact mem_image_of_mem f hzU
  rw [s13x_rf_fin_eq hF hzU]
  exact hmem

/-- The finite value of `F` maps the real axis into the real axis. -/
theorem s13x_rf_fin_im_eq_zero {f : ℂ → ℂ} {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f upperHalf upperHalf F) (himg : f '' upperHalf = upperHalf)
    (hFinf : F extInf = extInf) {x : ℂ} (hx : x.im = 0) : (abR_t_fin F x).im = 0 := by
  have hfr := IsHomeoExtension.image_frontier scExt_isOpen_upperHalf scExt_isOpen_upperHalf himg hF
  have hmem : F (x : ExtPlane) ∈ frontier (toExt upperHalf) := by
    rw [← hfr]
    exact mem_image_of_mem F (scExt_coe_mem_frontier_toExt_upperHalf_iff.2 hx)
  rw [(s13x_rf_fin_spec hF hFinf hx.ge).1] at hmem
  exact scExt_coe_mem_frontier_toExt_upperHalf_iff.1 hmem

/-- The finite value of `F` maps the closed upper half-plane onto itself. -/
theorem s13x_rf_fin_surj {f : ℂ → ℂ} {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f upperHalf upperHalf F) (hFinf : F extInf = extInf) {w : ℂ}
    (hw : 0 ≤ w.im) : ∃ z : ℂ, 0 ≤ z.im ∧ abR_t_fin F z = w := by
  have hmem : (w : ExtPlane) ∈ F '' closure (toExt upperHalf) := by
    rw [hF.2.2.2]
    exact s13x_rf_coe_mem_closure hw
  obtain ⟨p, hp, hpw⟩ := hmem
  rw [scExt_closure_toExt_upperHalf] at hp
  rcases hp with ⟨z, hz, rfl⟩ | hpinf
  · exact ⟨z, hz, abR_t_fin_of_eq hpw⟩
  · rw [mem_singleton_iff] at hpinf
    rw [hpinf, hFinf] at hpw
    exact absurd hpw.symm (OnePoint.coe_ne_infty w)

/-- The finite value of `F` is continuous on the closed upper half-plane. -/
theorem s13x_rf_fin_continuousOn {f : ℂ → ℂ} {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f upperHalf upperHalf F) (hFinf : F extInf = extInf) :
    ContinuousOn (abR_t_fin F) {z : ℂ | 0 ≤ z.im} := by
  rw [OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_iff]
  have hc : ContinuousOn (F ∘ ((↑) : ℂ → ExtPlane)) {z : ℂ | 0 ≤ z.im} :=
    hF.2.1.comp OnePoint.continuous_coe.continuousOn fun z hz => s13x_rf_coe_mem_closure hz
  exact hc.congr fun z hz => (s13x_rf_fin_spec hF hFinf hz).1.symm

/-- The reflection of `F` across the real axis: the finite value of `F` on the closed upper half-plane,
and `conj (F (conj z))` on the lower half-plane. -/
def s13x_rf_ext (F : ExtPlane → ExtPlane) (z : ℂ) : ℂ :=
  if 0 ≤ z.im then abR_t_fin F z else conj (abR_t_fin F (conj z))

/-- The reflected extension on the closed upper half-plane. -/
theorem s13x_rf_ext_of_nonneg {F : ExtPlane → ExtPlane} {z : ℂ} (hz : 0 ≤ z.im) :
    s13x_rf_ext F z = abR_t_fin F z :=
  ite_eq_left hz

/-- The reflected extension on the lower half-plane. -/
theorem s13x_rf_ext_of_neg {F : ExtPlane → ExtPlane} {z : ℂ} (hz : z.im < 0) :
    s13x_rf_ext F z = conj (abR_t_fin F (conj z)) :=
  ite_eq_right (not_le.2 hz)

/-- The reflected extension is continuous. -/
theorem s13x_rf_ext_continuous {f : ℂ → ℂ} {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f upperHalf upperHalf F) (himg : f '' upperHalf = upperHalf)
    (hFinf : F extInf = extInf) : Continuous (s13x_rf_ext F) := by
  have hfc := s13x_rf_fin_continuousOn hF hFinf
  have hmaps : MapsTo (fun z : ℂ => conj z) {z : ℂ | z.im ≤ 0} {z : ℂ | 0 ≤ z.im} :=
    fun z hz => by
      show 0 ≤ (conj z).im
      rw [Complex.conj_im]
      exact neg_nonneg.2 hz
  have hlow : ContinuousOn (fun z : ℂ => conj (abR_t_fin F (conj z))) {z : ℂ | z.im ≤ 0} :=
    Complex.continuous_conj.comp_continuousOn (hfc.comp Complex.continuous_conj.continuousOn hmaps)
  unfold s13x_rf_ext
  refine continuous_if_le continuous_const Complex.continuous_im hfc hlow fun z hz => ?_
  have hz' : z.im = 0 := hz.symm
  rw [Complex.conj_eq_iff_im.2 hz']
  exact (Complex.conj_eq_iff_im.2 (s13x_rf_fin_im_eq_zero hF himg hFinf hz')).symm

/-- The reflected extension is injective. -/
theorem s13x_rf_ext_injective {f : ℂ → ℂ} {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f upperHalf upperHalf F) (himg : f '' upperHalf = upperHalf)
    (hFinf : F extInf = extInf) : Function.Injective (s13x_rf_ext F) := by
  have hinj := s13x_rf_fin_injOn hF hFinf
  have hsign : ∀ z : ℂ, 0 ≤ z.im → 0 ≤ (s13x_rf_ext F z).im := fun z hz => by
    rw [s13x_rf_ext_of_nonneg hz]
    exact (s13x_rf_fin_spec hF hFinf hz).2
  have hneg : ∀ z : ℂ, z.im < 0 → (s13x_rf_ext F z).im < 0 := fun z hz => by
    rw [s13x_rf_ext_of_neg hz, Complex.conj_im, neg_lt_zero]
    exact s13x_rf_fin_pos hF himg (by rw [Complex.conj_im]; linarith)
  intro z₁ z₂ heq
  rcases le_or_gt 0 z₁.im with h₁ | h₁ <;> rcases le_or_gt 0 z₂.im with h₂ | h₂
  · rw [s13x_rf_ext_of_nonneg h₁, s13x_rf_ext_of_nonneg h₂] at heq
    exact hinj h₁ h₂ heq
  · have h := hsign z₁ h₁
    rw [heq] at h
    linarith [hneg z₂ h₂]
  · have h := hsign z₂ h₂
    rw [← heq] at h
    linarith [hneg z₁ h₁]
  · rw [s13x_rf_ext_of_neg h₁, s13x_rf_ext_of_neg h₂] at heq
    have h1' : 0 ≤ (conj z₁).im := by rw [Complex.conj_im]; linarith
    have h2' : 0 ≤ (conj z₂).im := by rw [Complex.conj_im]; linarith
    exact star_injective (hinj h1' h2' (star_injective heq))

/-- The reflected extension is surjective. -/
theorem s13x_rf_ext_surjective {f : ℂ → ℂ} {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f upperHalf upperHalf F) (himg : f '' upperHalf = upperHalf)
    (hFinf : F extInf = extInf) : Function.Surjective (s13x_rf_ext F) := by
  intro w
  rcases le_or_gt 0 w.im with hw | hw
  · obtain ⟨z, hz, hzw⟩ := s13x_rf_fin_surj hF hFinf hw
    exact ⟨z, (s13x_rf_ext_of_nonneg hz).trans hzw⟩
  · have hw' : 0 ≤ (conj w).im := by rw [Complex.conj_im]; linarith
    obtain ⟨z, hz, hzw⟩ := s13x_rf_fin_surj hF hFinf hw'
    have hzpos : 0 < z.im := by
      refine lt_of_le_of_ne hz fun h0 => ?_
      have h := s13x_rf_fin_im_eq_zero hF himg hFinf h0.symm
      rw [hzw, Complex.conj_im] at h
      linarith
    have hneg : (conj z).im < 0 := by rw [Complex.conj_im]; linarith
    refine ⟨conj z, ?_⟩
    rw [s13x_rf_ext_of_neg hneg, Complex.conj_conj, hzw, Complex.conj_conj]

/-- The reflected extension is `f` on `ℍ`. -/
theorem s13x_rf_ext_eqOn_upper {f : ℂ → ℂ} {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f upperHalf upperHalf F) : EqOn (s13x_rf_ext F) f upperHalf :=
  fun z hz => by
    rw [s13x_rf_ext_of_nonneg (le_of_lt hz), s13x_rf_fin_eq hF hz]

/-- The reflected extension is `conj ∘ f ∘ conj` on the lower half-plane. -/
theorem s13x_rf_ext_eqOn_lower {f : ℂ → ℂ} {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f upperHalf upperHalf F) :
    EqOn (s13x_rf_ext F) (fun z => conj (f (conj z))) (conj ⁻¹' upperHalf) := fun z hz => by
  have hz' : z.im < 0 := by
    have h : 0 < (conj z).im := hz
    rw [Complex.conj_im] at h
    linarith
  rw [s13x_rf_ext_of_neg hz', s13x_rf_fin_eq hF (z := conj z) hz]

/-- The reflected extension commutes with `z ↦ z̄`. -/
theorem s13x_rf_ext_conj {f : ℂ → ℂ} {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f upperHalf upperHalf F) (himg : f '' upperHalf = upperHalf)
    (hFinf : F extInf = extInf) (z : ℂ) : s13x_rf_ext F (conj z) = conj (s13x_rf_ext F z) := by
  rcases lt_trichotomy z.im 0 with h | h | h
  · have h' : 0 ≤ (conj z).im := by rw [Complex.conj_im]; linarith
    rw [s13x_rf_ext_of_nonneg h', s13x_rf_ext_of_neg h, Complex.conj_conj]
  · rw [Complex.conj_eq_iff_im.2 h, s13x_rf_ext_of_nonneg h.ge]
    exact (Complex.conj_eq_iff_im.2 (s13x_rf_fin_im_eq_zero hF himg hFinf h)).symm
  · have h' : (conj z).im < 0 := by rw [Complex.conj_im]; linarith
    rw [s13x_rf_ext_of_neg h', Complex.conj_conj, s13x_rf_ext_of_nonneg h.le]

/-- §13.5: a quasiconformal self-map of the upper half-plane extends by reflection
`f(z) = conj(f(z̄))` to a quasiconformal map of the plane (with the same constant).

*Correction (2026-09-24, user-approved).*  The book works on `ℂ̂`; as a map `ℂ → ℂ` the statement needs `f` to keep
`∞` fixed (a q.c. self-map of `ℍ` may move `∞`, e.g. `z ↦ -1/z`, and then no plane map extends it), hence the
hypothesis `hinf : f z → ∞` as `z → ∞` in `ℍ`. -/
theorem qc_reflection_extension {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f upperHalf K)
    (himg : f '' upperHalf = upperHalf)
    (hinf : Tendsto f (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ)) :
    ∃ g : ℂ → ℂ, IsKQC g univ K ∧ g '' univ = univ ∧ EqOn g f upperHalf ∧
      ∀ z, g (conj z) = conj (g z) := by
  obtain ⟨F, hF⟩ := thm13_3_boundary_correspondence isJordanDomain_upperHalf
    isJordanDomain_upperHalf ⟨K, hf⟩ himg
  have hFinf : F extInf = extInf := s13x_rf_infty hF hinf
  have hcont := s13x_rf_ext_continuous hF himg hFinf
  have hinj := s13x_rf_ext_injective hF himg hFinf
  have himg' : s13x_rf_ext F '' univ = univ :=
    image_univ_of_surjective (s13x_rf_ext_surjective hF himg hFinf)
  have hhom : IsHomeomorphOnto (s13x_rf_ext F) univ (s13x_rf_ext F '' univ) :=
    qcl_f_isHomeomorphOnto_of_injOn isOpen_univ hcont.continuousOn (injOn_of_injective hinj)
  refine ⟨s13x_rf_ext F, ?_, himg', s13x_rf_ext_eqOn_upper hF, s13x_rf_ext_conj hF himg hFinf⟩
  refine s13x_removable (L := {z : ℂ | z.im = 0}) isOpen_univ hf.2.1 hhom gzE_volume_im_eq_zero
    ?_ ?_ ?_
  · -- a vertical line meets the real axis in one point
    refine Eventually.of_forall fun x => (countable_singleton (0 : ℝ)).mono fun y hy => ?_
    simpa using hy
  · -- a horizontal line off the real axis misses it
    have h0 : ∀ᵐ y : ℝ, y ∉ ({0} : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.1 (measure_singleton 0)
    filter_upwards [h0] with y hy
    refine countable_empty.mono fun x hx => ?_
    exact absurd (by simpa using hx) hy
  · rintro z ⟨-, hz⟩
    have hz' : z.im ≠ 0 := hz
    rcases lt_or_gt_of_ne hz' with hlt | hgt
    · refine ⟨conj ⁻¹' upperHalf, hf.1.preimage Complex.continuous_conj, ?_, subset_univ _,
        ad_isKQC_congr (abR_x_isKQC_conj hf) (s13x_rf_ext_eqOn_lower hF)⟩
      show 0 < (conj z).im
      rw [Complex.conj_im]
      linarith
    · exact ⟨upperHalf, hf.1, hgt, subset_univ _, ad_isKQC_congr hf (s13x_rf_ext_eqOn_upper hF)⟩

end LiZhongQC
