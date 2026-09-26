import LiZhongQC.Ch02.S11_IntegralOperators
import LiZhongQC.Lemmas.LpDuality
import Mathlib.Analysis.Complex.Hadamard

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-! ## New work: the interpolation lemma.

`hilbertHSmooth`, `hilbertH`, and all the canonical interface theorems (`hilbertH_memLp`,
`hilbertH_memLp_two`, `hilbertH_add_ae`, `hilbertH_smul_ae`, `hilbertH_eq_ae_smooth`, etc.)
now come from the real, installed `S11_IntegralOperators.lean` (-5d's refactor, build green
8616 jobs) via the `import` above — no pasted stubs needed anymore. -/

section Family

variable {p p₁ : ℝ} (hp₁ : 2 < p₁) (hp2 : 2 < p) (hpp₁ : p ≤ p₁)

/-- The interpolation parameter `θ(p) = (1/2 - 1/p) / (1/2 - 1/p₁) ∈ (0, 1]`, cast to `ℂ` for use
as the point at which the analytic family is evaluated. -/
def interpTheta (p p₁ : ℝ) : ℝ := (1/2 - 1/p) / (1/2 - 1/p₁)

theorem interpTheta_mem_Ioc (hp₁ : 2 < p₁) (hp2 : 2 < p) (hpp₁ : p ≤ p₁) :
    interpTheta p p₁ ∈ Ioc (0:ℝ) 1 := by
  unfold interpTheta
  have hden : (0:ℝ) < 1/2 - 1/p₁ := by
    have : (1:ℝ)/p₁ < 1/2 := by
      apply div_lt_div_of_pos_left one_pos (by linarith) hp₁
    linarith
  constructor
  · apply div_pos _ hden
    have : (1:ℝ)/p < 1/2 := by
      apply div_lt_div_of_pos_left one_pos (by linarith) hp2
    linarith
  · rw [div_le_one hden]
    have : (1:ℝ)/p₁ ≤ 1/p := by
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith) hpp₁
    linarith

/-- The key exponent identity: `(1-θ)/2 + θ/p₁ = 1/p`, i.e. `γ(θ) = p·(1/p) = 1` for
`γ(z) := p·((1-z)/2 + z/p₁)`. This is what makes the analytic family's value at `z = θ`
equal the original function. -/
theorem interpTheta_spec (hp₁ : 2 < p₁) (hp2 : 2 < p) (hpp₁ : p ≤ p₁) :
    (1 - interpTheta p p₁) / 2 + interpTheta p p₁ / p₁ = 1 / p := by
  unfold interpTheta
  have hden : (1:ℝ)/2 - 1/p₁ ≠ 0 := by
    have : (1:ℝ)/p₁ < 1/2 := by
      apply div_lt_div_of_pos_left one_pos (by linarith) hp₁
    intro h; linarith
  have hp0 : p ≠ 0 := by linarith
  have hp₁0 : p₁ ≠ 0 := by linarith
  have hp₁2 : p₁ - 2 ≠ 0 := by linarith
  have hp₁2' : (-2 + p₁) ≠ 0 := by linarith
  field_simp
  ring

end Family

/-- Missing from Mathlib (checked): a simple function as an explicit finite sum of level-set
indicators. Needed so `hilbertH`'s BINARY `add_ae`/`smul_ae` apply to the analytic family term
by term. -/
theorem simpleFunc_eq_sum_indicator_preimage {α : Type*} [MeasurableSpace α]
    (s : MeasureTheory.SimpleFunc α ℂ) (a : α) :
    s a = ∑ c ∈ s.range, (s ⁻¹' {c}).indicator (fun _ => c) a := by
  rw [Finset.sum_eq_single (s a)]
  · simp
  · intro c _ hc
    apply Set.indicator_of_notMem
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact fun h => hc h.symm
  · intro h
    exact absurd (MeasureTheory.SimpleFunc.mem_range_self s a) h

/-! ## The analytic family -/

/-- The exponent function `γ(z) = p·((1-z)/2 + z/p₁)`, entire and affine in `z`; `Re γ(θ) `-type
facts come from `interpTheta_spec` cast to `ℂ`. -/
def famExp (p p₁ : ℝ) (z : ℂ) : ℂ := (p : ℂ) * ((1 - z) / 2 + z / p₁)

/-- The per-value reweighting `c ↦ sign(c) · ‖c‖^{γ(z)}`, junk `0` at `c = 0` (matching the
level set `s⁻¹{0}` contributing nothing, consistently with `s` itself vanishing there). -/
def famCoeff (p p₁ : ℝ) (c : ℂ) (z : ℂ) : ℂ :=
  if c = 0 then 0 else (c / (‖c‖ : ℂ)) * (‖c‖ : ℂ) ^ famExp p p₁ z

/-- The analytic family built from a simple function `s`, as an explicit finite sum of
reweighted level-set indicators (via `simpleFunc_eq_sum_indicator_preimage`'s decomposition). -/
def fam (s : MeasureTheory.SimpleFunc ℂ ℂ) (p p₁ : ℝ) (z : ℂ) : ℂ → ℂ :=
  fun a => ∑ c ∈ s.range, (s ⁻¹' {c}).indicator (fun _ => famCoeff p p₁ c z) a

theorem famExp_interpTheta {p p₁ : ℝ} (hp₁ : 2 < p₁) (hp2 : 2 < p) (hpp₁ : p ≤ p₁) :
    famExp p p₁ (interpTheta p p₁ : ℂ) = 1 := by
  have hspec := interpTheta_spec hp₁ hp2 hpp₁
  have hp0 : p ≠ 0 := by linarith
  unfold famExp
  have : ((1 - (interpTheta p p₁ : ℂ)) / 2 + (interpTheta p p₁ : ℂ) / p₁) =
      (((1 - interpTheta p p₁) / 2 + interpTheta p p₁ / p₁ : ℝ) : ℂ) := by push_cast; ring
  rw [this, hspec]
  push_cast
  rw [mul_one_div, div_self (by exact_mod_cast hp0 : (p:ℂ) ≠ 0)]

theorem famCoeff_interpTheta {p p₁ : ℝ} (hp₁ : 2 < p₁) (hp2 : 2 < p) (hpp₁ : p ≤ p₁) (c : ℂ) :
    famCoeff p p₁ c (interpTheta p p₁ : ℂ) = c := by
  unfold famCoeff
  rw [famExp_interpTheta hp₁ hp2 hpp₁]
  by_cases hc : c = 0
  · simp [hc]
  · rw [if_neg hc, Complex.cpow_one]
    have hcnorm : (‖c‖ : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero, norm_eq_zero]; exact hc
    field_simp

/-- The family evaluated at `z = θ(p)` recovers `s` exactly. -/
theorem fam_interpTheta {s : MeasureTheory.SimpleFunc ℂ ℂ} {p p₁ : ℝ}
    (hp₁ : 2 < p₁) (hp2 : 2 < p) (hpp₁ : p ≤ p₁) :
    fam s p p₁ (interpTheta p p₁ : ℂ) = (s : ℂ → ℂ) := by
  funext a
  unfold fam
  simp_rw [famCoeff_interpTheta hp₁ hp2 hpp₁]
  exact (simpleFunc_eq_sum_indicator_preimage s a).symm

/-- Generalized versions of the four `interpTheta`-recovery facts above, for use on the DUAL
(conjugate-exponent) side where `q = p.conjExponent` and `p₁' = p₁.conjExponent` are both `< 2`
(since `p, p₁ > 2`), so the `2 < _` hypotheses of the originals don't apply. The underlying algebra
never actually needed `2 < p₁`/`2 < p`/`p ≤ p₁` — only `p₁ ≠ 2` and `p ≠ 0` (checked: `hpp₁` is
unused in the original `interpTheta_spec` proof). -/
theorem interpTheta_spec' {p p₁ : ℝ} (hp₁2 : p₁ ≠ 2) (hp₁0 : p₁ ≠ 0) (hp0 : p ≠ 0) :
    (1 - interpTheta p p₁) / 2 + interpTheta p p₁ / p₁ = 1 / p := by
  unfold interpTheta
  have hden : (1:ℝ)/2 - 1/p₁ ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    apply hp₁2
    field_simp at h
    linarith
  field_simp
  ring

theorem famExp_interpTheta' {p p₁ : ℝ} (hp₁2 : p₁ ≠ 2) (hp₁0 : p₁ ≠ 0) (hp0 : p ≠ 0) :
    famExp p p₁ (interpTheta p p₁ : ℂ) = 1 := by
  have hspec := interpTheta_spec' hp₁2 hp₁0 hp0
  unfold famExp
  have : ((1 - (interpTheta p p₁ : ℂ)) / 2 + (interpTheta p p₁ : ℂ) / p₁) =
      (((1 - interpTheta p p₁) / 2 + interpTheta p p₁ / p₁ : ℝ) : ℂ) := by push_cast; ring
  rw [this, hspec]
  push_cast
  rw [mul_one_div, div_self (by exact_mod_cast hp0 : (p:ℂ) ≠ 0)]

theorem famCoeff_interpTheta' {p p₁ : ℝ} (hp₁2 : p₁ ≠ 2) (hp₁0 : p₁ ≠ 0) (hp0 : p ≠ 0) (c : ℂ) :
    famCoeff p p₁ c (interpTheta p p₁ : ℂ) = c := by
  unfold famCoeff
  rw [famExp_interpTheta' hp₁2 hp₁0 hp0]
  by_cases hc : c = 0
  · simp [hc]
  · rw [if_neg hc, Complex.cpow_one]
    have hcnorm : (‖c‖ : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero, norm_eq_zero]; exact hc
    field_simp

theorem fam_interpTheta' {s : MeasureTheory.SimpleFunc ℂ ℂ} {p p₁ : ℝ}
    (hp₁2 : p₁ ≠ 2) (hp₁0 : p₁ ≠ 0) (hp0 : p ≠ 0) :
    fam s p p₁ (interpTheta p p₁ : ℂ) = (s : ℂ → ℂ) := by
  funext a
  unfold fam
  simp_rw [famCoeff_interpTheta' hp₁2 hp₁0 hp0]
  exact (simpleFunc_eq_sum_indicator_preimage s a).symm

/-- `fam` evaluated pointwise reduces to `famCoeff` at `s a`, same proof shape as the
decomposition lemma. -/
theorem fam_apply (s : MeasureTheory.SimpleFunc ℂ ℂ) (p p₁ : ℝ) (z : ℂ) (a : ℂ) :
    fam s p p₁ z a = famCoeff p p₁ (s a) z := by
  unfold fam
  rw [Finset.sum_eq_single (s a)]
  · simp
  · intro c _ hc
    apply Set.indicator_of_notMem
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact fun h => hc h.symm
  · intro h
    exact absurd (MeasureTheory.SimpleFunc.mem_range_self s a) h

/-- The real part of `famExp` depends only on `Re z`, affinely. -/
theorem famExp_re (p p₁ : ℝ) (z : ℂ) :
    (famExp p p₁ z).re = p * ((1 - z.re) / 2 + z.re / p₁) := by
  have key : famExp p p₁ z = ((p / 2 : ℝ) : ℂ) + ((p * (1 / p₁ - 1 / 2) : ℝ) : ℂ) * z := by
    unfold famExp; push_cast; ring
  rw [key, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- `‖famCoeff p p₁ c z‖ = ‖c‖ ^ (famExp p p₁ z).re` for `c ≠ 0` (junk `0` at `c = 0`). -/
theorem norm_famCoeff (p p₁ : ℝ) (c : ℂ) (z : ℂ) :
    ‖famCoeff p p₁ c z‖ = if c = 0 then 0 else ‖c‖ ^ (famExp p p₁ z).re := by
  unfold famCoeff
  split_ifs with hc
  · simp
  · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr hc)]
    have : ‖c / (‖c‖:ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg c),
        div_self (norm_ne_zero_iff.mpr hc)]
    rw [this, one_mul]

/-- The `Lq`-norm of the family at a point `z` with `Re γ(z)·q = p` collapses to a single power
of `‖s‖_p` — this is the boundary-line norm computation, generic enough to cover both `Re z = 0`
(`q = 2`) and `Re z = 1` (`q = p₁`). -/
theorem eLpNorm_fam_eq_rpow {s : MeasureTheory.SimpleFunc ℂ ℂ} {p p₁ : ℝ} (hp1' : 1 < p)
    {z : ℂ} {q : ℝ} (hq1 : 1 < q) (hre : (famExp p p₁ z).re * q = p) :
    eLpNorm (fam s p p₁ z) (ENNReal.ofReal q) volume =
      (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume) ^ (p / q) := by
  have hq0 : q ≠ 0 := by linarith
  have hfm : AEStronglyMeasurable (fam s p p₁ z) volume := by
    have : fam s p p₁ z = (s.map (fun c => famCoeff p p₁ c z) : ℂ → ℂ) :=
      funext fun a => by rw [fam_apply]; rfl
    rw [this]; exact SimpleFunc.aestronglyMeasurable _
  have hstep : (eLpNorm (fam s p p₁ z) (ENNReal.ofReal q) volume) ^ q =
      ∫⁻ a, ‖fam s p p₁ z a‖ₑ ^ q ∂volume := enn_pow_eLpNorm_eq_lintegral hq1 _ hfm
  have hpteq : ∀ a, ‖fam s p p₁ z a‖ₑ ^ q = ‖s a‖ₑ ^ p := by
    intro a
    rw [fam_apply, ← ofReal_norm, norm_famCoeff]
    by_cases hsa : s a = 0
    · simp only [hsa, if_pos, ENNReal.ofReal_zero, enorm_zero]
      rw [ENNReal.zero_rpow_of_pos (by linarith : (0:ℝ) < q),
        ENNReal.zero_rpow_of_pos (by linarith : (0:ℝ) < p)]
    · rw [if_neg hsa,
        ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (by linarith : (0:ℝ) ≤ q),
        ← Real.rpow_mul (norm_nonneg _), hre, ← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith : (0:ℝ) ≤ p)]
  have hkey : (eLpNorm (fam s p p₁ z) (ENNReal.ofReal q) volume) ^ q =
      (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume) ^ p := by
    rw [hstep]
    simp_rw [hpteq]
    exact (enn_pow_eLpNorm_eq_lintegral hp1' (s : ℂ → ℂ) s.aestronglyMeasurable).symm
  calc eLpNorm (fam s p p₁ z) (ENNReal.ofReal q) volume
      = ((eLpNorm (fam s p p₁ z) (ENNReal.ofReal q) volume) ^ q) ^ (1 / q) := by
        rw [← ENNReal.rpow_mul, mul_one_div, div_self hq0, ENNReal.rpow_one]
    _ = ((eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume) ^ p) ^ (1 / q) := by rw [hkey]
    _ = (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume) ^ (p / q) := by
        rw [← ENNReal.rpow_mul]; congr 1; ring

/-! ## Pushing `hilbertH`'s (binary) linearity through a finite sum -/

theorem hilbertH_zero_ae : hilbertH (0 : ℂ → ℂ) =ᵐ[volume] (0 : ℂ → ℂ) := by
  have h := hilbertH_add_ae (ω₁ := (0:ℂ→ℂ)) (ω₂ := (0:ℂ→ℂ)) (MemLp.zero) (MemLp.zero)
  simp only [add_zero] at h
  filter_upwards [h] with a ha
  have ha' : hilbertH 0 a = hilbertH 0 a + hilbertH 0 a := by simpa using ha
  show hilbertH 0 a = (0:ℂ→ℂ) a
  simp only [Pi.zero_apply]
  linear_combination -ha'

theorem hilbertH_finset_sum_ae {ι : Type*} (t : Finset ι) (c : ι → ℂ) (E : ι → ℂ → ℂ)
    (hE : ∀ i ∈ t, MemLp (E i) 2 volume) :
    hilbertH (∑ i ∈ t, c i • E i) =ᵐ[volume] ∑ i ∈ t, c i • hilbertH (E i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hilbertH_zero_ae
  | insert a s ha ih =>
    have hEa : MemLp (E a) 2 volume := hE a (Finset.mem_insert_self a s)
    have hEs : ∀ i ∈ s, MemLp (E i) 2 volume := fun i hi => hE i (Finset.mem_insert_of_mem hi)
    have hsum_mem : MemLp (∑ i ∈ s, c i • E i) 2 volume :=
      memLp_finsetSum' s (fun i hi => (hEs i hi).const_smul (c i))
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := hilbertH_add_ae ((hEa).const_smul (c a)) hsum_mem
    have h2 := hilbertH_smul_ae (c a) hEa
    have h3 := ih hEs
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    rw [hx1, Pi.add_apply, hx2, hx3, Pi.add_apply]

/-- `hilbertH` distributes over the family's defining finite sum. -/
theorem hilbertH_fam_ae {s : MeasureTheory.SimpleFunc ℂ ℂ} {p p₁ : ℝ} (z : ℂ)
    (hp1' : 1 < p) (hs : MemLp (s : ℂ → ℂ) (ENNReal.ofReal p) volume) :
    hilbertH (fam s p p₁ z) =ᵐ[volume]
      ∑ c ∈ s.range, (1:ℂ) •
        hilbertH ((s ⁻¹' {c}).indicator (fun _ => famCoeff p p₁ c z)) := by
  have hpne0 : ENNReal.ofReal p ≠ 0 := by
    simp only [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
  have heq : fam s p p₁ z =
      ∑ c ∈ s.range, (1:ℂ) • (s ⁻¹' {c}).indicator (fun _ => famCoeff p p₁ c z) := by
    unfold fam; funext a; simp
  rw [heq]
  apply hilbertH_finset_sum_ae
  intro c _
  by_cases hc0 : c = 0
  · simp [hc0, famCoeff]
  · have hfin := MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_memLp
      hpne0 ENNReal.ofReal_ne_top s hs c hc0
    exact memLp_indicator_const 2 (s.measurableSet_fiber c) _ (Or.inr hfin.ne)

/-! ## Entireness of the family's coefficients -/

theorem differentiable_famExp (p p₁ : ℝ) : Differentiable ℂ (famExp p p₁) := by
  unfold famExp
  fun_prop

theorem differentiable_famCoeff (p p₁ : ℝ) {c : ℂ} (hc : c ≠ 0) :
    Differentiable ℂ (fun z => famCoeff p p₁ c z) := by
  have hbase : (‖c‖ : ℂ) ≠ 0 := by simp [hc]
  have hcpow : Differentiable ℂ (fun z => (‖c‖ : ℂ) ^ famExp p p₁ z) :=
    (differentiable_famExp p p₁).const_cpow (Or.inl hbase)
  have heq : (fun z => famCoeff p p₁ c z) =
      fun z => (c / (‖c‖ : ℂ)) * (‖c‖ : ℂ) ^ famExp p p₁ z := by
    funext z; unfold famCoeff; rw [if_neg hc]
  rw [heq]
  exact hcpow.const_mul _

/-! ## The pairing sum -/

/-- `fam` re-expressed with the coefficient pulled out of the indicator (pointwise), summed over
`s.range.erase 0` (the `c = 0` term is exactly the zero function, dropped for free). -/
theorem fam_eq_sum_smul_indicator (s : MeasureTheory.SimpleFunc ℂ ℂ) (p p₁ : ℝ) (z : ℂ) :
    fam s p p₁ z =
      ∑ c ∈ s.range.erase 0, famCoeff p p₁ c z • (s ⁻¹' {c}).indicator (1 : ℂ → ℂ) := by
  funext a
  rw [fam_apply, Finset.sum_apply]
  by_cases hsa : s a = 0
  · rw [hsa, show famCoeff p p₁ 0 z = 0 from by simp [famCoeff]]
    symm
    apply Finset.sum_eq_zero
    intro c hc
    have hcne : c ≠ 0 := (Finset.mem_erase.mp hc).1
    have : a ∉ s ⁻¹' {c} := by
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact fun h => hcne (hsa.symm.trans h).symm
    simp [Pi.smul_apply, Set.indicator_of_notMem this]
  · rw [Finset.sum_eq_single (s a)]
    · simp only [Pi.smul_apply, smul_eq_mul, Set.indicator_of_mem
        (show a ∈ s ⁻¹' {s a} from rfl), Pi.one_apply, mul_one]
    · intro c hc hcne'
      have : a ∉ s ⁻¹' {c} := by
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact fun h => hcne' h.symm
      simp [Pi.smul_apply, Set.indicator_of_notMem this]
    · intro h
      exact absurd (Finset.mem_erase.mpr ⟨hsa, MeasureTheory.SimpleFunc.mem_range_self s a⟩) h

/-- `hilbertH` applied to the family, coefficient pulled out, over `s.range.erase 0` (so every
summand's raw indicator has finite-measure support and is genuinely `MemLp 2`). -/
theorem hilbertH_fam_ae' {s : MeasureTheory.SimpleFunc ℂ ℂ} {p p₁ : ℝ} (z : ℂ)
    (hp1' : 1 < p) (hs : MemLp (s : ℂ → ℂ) (ENNReal.ofReal p) volume) :
    hilbertH (fam s p p₁ z) =ᵐ[volume]
      ∑ c ∈ s.range.erase 0,
        famCoeff p p₁ c z • hilbertH ((s ⁻¹' {c}).indicator (1 : ℂ → ℂ)) := by
  rw [fam_eq_sum_smul_indicator]
  have hpne0 : ENNReal.ofReal p ≠ 0 := by
    simp only [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
  apply hilbertH_finset_sum_ae
  intro c hc
  have hcne : c ≠ 0 := (Finset.mem_erase.mp hc).1
  have hfin := MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_memLp
    hpne0 ENNReal.ofReal_ne_top s hs c hcne
  exact memLp_indicator_const 2 (s.measurableSet_fiber c) _ (Or.inr hfin.ne)

/-- The fixed (z-independent) pairing constant between an `s`-level-set image under `hilbertH`
and a `g`-level-set. -/
def pairConst (s g : MeasureTheory.SimpleFunc ℂ ℂ) (c d : ℂ) : ℂ :=
  ∫ x, hilbertH ((s ⁻¹' {c}).indicator (1 : ℂ → ℂ)) x * (g ⁻¹' {d}).indicator (1 : ℂ → ℂ) x
    ∂volume

theorem integrable_pairConst_term {s g : MeasureTheory.SimpleFunc ℂ ℂ} {p q : ℝ} (c d : ℂ)
    (hp1' : 1 < p) (hs : MemLp (s : ℂ → ℂ) (ENNReal.ofReal p) volume) (hq1' : 1 < q)
    (hg : MemLp (g : ℂ → ℂ) (ENNReal.ofReal q) volume) (hc : c ≠ 0) (hd : d ≠ 0) :
    Integrable (fun x => hilbertH ((s ⁻¹' {c}).indicator (1 : ℂ → ℂ)) x *
      (g ⁻¹' {d}).indicator (1 : ℂ → ℂ) x) volume := by
  have hpne0 : ENNReal.ofReal p ≠ 0 := by
    simp only [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hqne0 : ENNReal.ofReal q ≠ 0 := by
    simp only [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hfinc := MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_memLp
    hpne0 ENNReal.ofReal_ne_top s hs c hc
  have hfind := MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_memLp
    hqne0 ENNReal.ofReal_ne_top g hg d hd
  have hmemc : MemLp ((s ⁻¹' {c}).indicator (1 : ℂ → ℂ)) 2 volume :=
    memLp_indicator_const 2 (s.measurableSet_fiber c) _ (Or.inr hfinc.ne)
  have hmemd : MemLp ((g ⁻¹' {d}).indicator (1 : ℂ → ℂ)) 2 volume :=
    memLp_indicator_const 2 (g.measurableSet_fiber d) _ (Or.inr hfind.ne)
  exact (hilbertH_memLp_two hmemc).1.integrable_mul hmemd

theorem integral_hilbertH_fam_mul_fam {s g : MeasureTheory.SimpleFunc ℂ ℂ} {p p₁ q p₁' : ℝ}
    (z : ℂ) (hp1' : 1 < p) (hs : MemLp (s : ℂ → ℂ) (ENNReal.ofReal p) volume)
    (hq1' : 1 < q) (hg : MemLp (g : ℂ → ℂ) (ENNReal.ofReal q) volume) :
    ∫ x, hilbertH (fam s p p₁ z) x * fam g q p₁' z x ∂volume =
      ∑ c ∈ s.range.erase 0, ∑ d ∈ g.range.erase 0,
        famCoeff p p₁ c z * famCoeff q p₁' d z * pairConst s g c d := by
  have hae : (fun x => hilbertH (fam s p p₁ z) x * fam g q p₁' z x) =ᵐ[volume]
      (fun x => (∑ c ∈ s.range.erase 0, famCoeff p p₁ c z •
        hilbertH ((s ⁻¹' {c}).indicator (1 : ℂ → ℂ))) x * fam g q p₁' z x) := by
    filter_upwards [hilbertH_fam_ae' z hp1' hs] with x hx
    rw [hx]
  rw [integral_congr_ae hae, fam_eq_sum_smul_indicator g q p₁' z]
  have hint : ∀ x, (∑ c ∈ s.range.erase 0, famCoeff p p₁ c z •
        hilbertH ((s ⁻¹' {c}).indicator (1 : ℂ → ℂ))) x *
      (∑ d ∈ g.range.erase 0, famCoeff q p₁' d z • (g ⁻¹' {d}).indicator (1 : ℂ → ℂ)) x =
      ∑ c ∈ s.range.erase 0, ∑ d ∈ g.range.erase 0,
        (famCoeff p p₁ c z * famCoeff q p₁' d z) *
          (hilbertH ((s ⁻¹' {c}).indicator (1 : ℂ → ℂ)) x *
            (g ⁻¹' {d}).indicator (1 : ℂ → ℂ) x) := by
    intro x
    simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro d _
    ring
  simp_rw [hint]
  have hintegrable : ∀ c ∈ s.range.erase 0, ∀ d ∈ g.range.erase 0,
      Integrable (fun x => (famCoeff p p₁ c z * famCoeff q p₁' d z) *
        (hilbertH ((s ⁻¹' {c}).indicator (1 : ℂ → ℂ)) x *
          (g ⁻¹' {d}).indicator (1 : ℂ → ℂ) x)) volume := by
    intro c hc d hd
    exact (integrable_pairConst_term c d hp1' hs hq1' hg
      (Finset.mem_erase.mp hc).1 (Finset.mem_erase.mp hd).1).const_mul _
  rw [integral_finsetSum _ (fun c hc => integrable_finsetSum _ (fun d hd => hintegrable c hc d hd))]
  apply Finset.sum_congr rfl; intro c hc
  rw [integral_finsetSum _ (fun d hd => hintegrable c hc d hd)]
  apply Finset.sum_congr rfl; intro d hd
  rw [integral_const_mul]
  rfl

/-! ## Entireness and boundedness of the pairing sum -/

theorem differentiable_pairSum (s g : MeasureTheory.SimpleFunc ℂ ℂ) (p p₁ q p₁' : ℝ) :
    Differentiable ℂ (fun z => ∑ c ∈ s.range.erase 0, ∑ d ∈ g.range.erase 0,
      famCoeff p p₁ c z * famCoeff q p₁' d z * pairConst s g c d) := by
  have heq : (fun z => ∑ c ∈ s.range.erase 0, ∑ d ∈ g.range.erase 0,
      famCoeff p p₁ c z * famCoeff q p₁' d z * pairConst s g c d) =
      ∑ c ∈ s.range.erase 0, (fun z => ∑ d ∈ g.range.erase 0,
        famCoeff p p₁ c z * famCoeff q p₁' d z * pairConst s g c d) := by
    funext z; rw [Finset.sum_apply]
  rw [heq]
  apply Differentiable.sum
  intro c hc
  have heq2 : (fun z => ∑ d ∈ g.range.erase 0,
      famCoeff p p₁ c z * famCoeff q p₁' d z * pairConst s g c d) =
      ∑ d ∈ g.range.erase 0, (fun z => famCoeff p p₁ c z * famCoeff q p₁' d z * pairConst s g c d) := by
    funext z; rw [Finset.sum_apply]
  rw [heq2]
  apply Differentiable.sum
  intro d hd
  have hcne : c ≠ 0 := (Finset.mem_erase.mp hc).1
  have hdne : d ≠ 0 := (Finset.mem_erase.mp hd).1
  exact ((differentiable_famCoeff p p₁ hcne).mul (differentiable_famCoeff q p₁' hdne)).mul_const _

theorem memLp_fam {s : MeasureTheory.SimpleFunc ℂ ℂ} {p p₁ : ℝ} (hp1' : 1 < p)
    (hs : MemLp (s : ℂ → ℂ) (ENNReal.ofReal p) volume) (z : ℂ) {r : ℝ} :
    MemLp (fam s p p₁ z) (ENNReal.ofReal r) volume := by
  rw [fam_eq_sum_smul_indicator]
  apply memLp_finsetSum'
  intro c hc
  have hcne : c ≠ 0 := (Finset.mem_erase.mp hc).1
  have hpne0 : ENNReal.ofReal p ≠ 0 := by
    simp only [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hfin := MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_memLp
    hpne0 ENNReal.ofReal_ne_top s hs c hcne
  exact (memLp_indicator_const (ENNReal.ofReal r) (s.measurableSet_fiber c) _
    (Or.inr hfin.ne)).const_smul _

/-- ENNReal `X^r` cast to a real number equals the real `.toReal`-power, when `X ≠ ⊤`. -/
theorem toReal_rpow_of_ne_top {X : ℝ≥0∞} (hX : X ≠ ⊤) (r : ℝ) :
    (X ^ r).toReal = X.toReal ^ r := (ENNReal.toReal_rpow X r).symm

/-- The `Re z = 0` boundary bound: Cauchy–Schwarz (`HolderConjugate 2 2`) plus the isometry
(`hilbertH_memLp_two`) and the boundary-line norm formula, constant in `t`. -/
theorem boundary_bound_zero {s g : MeasureTheory.SimpleFunc ℂ ℂ} {p p₁ q p₁' : ℝ} (t : ℝ)
    (hp1' : 1 < p) (hs : MemLp (s : ℂ → ℂ) (ENNReal.ofReal p) volume)
    (hq1' : 1 < q) (hg : MemLp (g : ℂ → ℂ) (ENNReal.ofReal q) volume) :
    ‖∫ x, hilbertH (fam s p p₁ ((t : ℂ) * I)) x * fam g q p₁' ((t : ℂ) * I) x ∂volume‖ ≤
      (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal ^ (p / 2) *
        (eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume).toReal ^ (q / 2) := by
  set z : ℂ := (t : ℂ) * I
  have h2eq : ENNReal.ofReal (2:ℝ) = (2:ℝ≥0∞) := by norm_num
  have hmem_fs2' : MemLp (fam s p p₁ z) (ENNReal.ofReal 2) volume := memLp_fam hp1' hs z
  have hmem_g2' : MemLp (fam g q p₁' z) (ENNReal.ofReal 2) volume := memLp_fam hq1' hg z
  have hmem_fs2 : MemLp (fam s p p₁ z) 2 volume := h2eq ▸ hmem_fs2'
  have hmem_g2 : MemLp (fam g q p₁' z) 2 volume := h2eq ▸ hmem_g2'
  have hmemHs2' : MemLp (hilbertH (fam s p p₁ z)) (ENNReal.ofReal 2) volume :=
    h2eq ▸ (hilbertH_memLp_two hmem_fs2).1
  have hisom : eLpNorm (hilbertH (fam s p p₁ z)) (ENNReal.ofReal 2) volume =
      eLpNorm (fam s p p₁ z) (ENNReal.ofReal 2) volume := by
    rw [h2eq]; exact (hilbertH_memLp_two hmem_fs2).2
  have hre0 : ((t : ℂ) * I).re = 0 := by simp
  have hexps : (famExp p p₁ z).re * 2 = p := by rw [famExp_re, hre0]; ring
  have hexpg : (famExp q p₁' z).re * 2 = q := by rw [famExp_re, hre0]; ring
  have hnorm_s : eLpNorm (fam s p p₁ z) (ENNReal.ofReal 2) volume =
      (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume) ^ (p / 2) :=
    eLpNorm_fam_eq_rpow (s := s) (p := p) (p₁ := p₁) hp1' (z := z) (q := 2) (by norm_num) hexps
  have hnorm_g : eLpNorm (fam g q p₁' z) (ENNReal.ofReal 2) volume =
      (eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume) ^ (q / 2) :=
    eLpNorm_fam_eq_rpow (s := g) (p := q) (p₁ := p₁') hq1' (z := z) (q := 2) (by norm_num) hexpg
  have hcombine : ∀ (X : ℝ≥0∞) (a : ℝ), ((X ^ a) ^ (2:ℕ)).toReal ^ (1/2:ℝ) = X.toReal ^ a := by
    intro X a
    rw [← ENNReal.rpow_natCast (X ^ a) 2, ← ENNReal.rpow_mul, ← ENNReal.toReal_rpow,
      ← Real.rpow_mul ENNReal.toReal_nonneg]
    congr 1
    push_cast
    ring
  calc ‖∫ x, hilbertH (fam s p p₁ z) x * fam g q p₁' z x ∂volume‖
      ≤ ∫ x, ‖hilbertH (fam s p p₁ z) x * fam g q p₁' z x‖ ∂volume :=
        norm_integral_le_integral_norm _
    _ = ∫ x, ‖hilbertH (fam s p p₁ z) x‖ * ‖fam g q p₁' z x‖ ∂volume := by
        simp_rw [norm_mul]
    _ ≤ (∫ x, ‖hilbertH (fam s p p₁ z) x‖ ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) *
          (∫ x, ‖fam g q p₁' z x‖ ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) :=
        integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hmemHs2' hmem_g2'
    _ = ((eLpNorm (hilbertH (fam s p p₁ z)) (ENNReal.ofReal 2) volume) ^ 2).toReal ^ (1 / 2 : ℝ) *
          ((eLpNorm (fam g q p₁' z) (ENNReal.ofReal 2) volume) ^ 2).toReal ^ (1 / 2 : ℝ) := by
        have e1 := integral_norm_rpow_eq_toReal_pow (f := hilbertH (fam s p p₁ z))
          (by norm_num : (1:ℝ) < 2) hmemHs2'.aestronglyMeasurable
        have e2 := integral_norm_rpow_eq_toReal_pow (f := fam g q p₁' z)
          (by norm_num : (1:ℝ) < 2) hmem_g2'.aestronglyMeasurable
        rw [ENNReal.rpow_two] at e1 e2
        rw [e1, e2]
    _ = (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal ^ (p / 2) *
          (eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume).toReal ^ (q / 2) := by
        rw [hisom, hnorm_s, hnorm_g]
        congr 1
        · exact hcombine (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume) (p/2)
        · exact hcombine (eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume) (q/2)

/-- The `Re z = 1` boundary bound: Hölder (`p₁.HolderConjugate p₁'`) plus the `hgen` hypothesis
and the boundary-line norm formula, constant in `t`. -/
theorem boundary_bound_one {s g : MeasureTheory.SimpleFunc ℂ ℂ} {p p₁ q p₁' M : ℝ} (t : ℝ)
    (hp1' : 1 < p) (hs : MemLp (s : ℂ → ℂ) (ENNReal.ofReal p) volume)
    (hq1' : 1 < q) (hg : MemLp (g : ℂ → ℂ) (ENNReal.ofReal q) volume)
    (hp₁ : 2 < p₁) (hp1q : p₁.HolderConjugate p₁') (hM0 : 0 ≤ M)
    (hgen : ∀ ω : ℂ → ℂ, MemLp ω (ENNReal.ofReal p₁) volume →
      MemLp (hilbertH ω) (ENNReal.ofReal p₁) volume ∧
        eLpNorm (hilbertH ω) (ENNReal.ofReal p₁) volume ≤
          ENNReal.ofReal M * eLpNorm ω (ENNReal.ofReal p₁) volume) :
    ‖∫ x, hilbertH (fam s p p₁ (1 + (t : ℂ) * I)) x * fam g q p₁' (1 + (t : ℂ) * I) x
      ∂volume‖ ≤
      M * (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal ^ (p / p₁) *
        (eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume).toReal ^ (q / p₁') := by
  set z : ℂ := 1 + (t : ℂ) * I
  have hp₁0 : p₁ ≠ 0 := by linarith
  have hp₁'pos : 1 < p₁' := hp1q.symm.lt
  have hp₁'0 : p₁' ≠ 0 := by linarith
  have hmem_fsp1 : MemLp (fam s p p₁ z) (ENNReal.ofReal p₁) volume := memLp_fam hp1' hs z
  have hmem_gp1' : MemLp (fam g q p₁' z) (ENNReal.ofReal p₁') volume := memLp_fam hq1' hg z
  obtain ⟨hmemH, hboundH⟩ := hgen (fam s p p₁ z) hmem_fsp1
  have hre1 : (1 + (t : ℂ) * I).re = 1 := by simp
  have hexps : (famExp p p₁ z).re * p₁ = p := by
    rw [famExp_re, hre1]; field_simp [hp₁0]; ring
  have hexpg : (famExp q p₁' z).re * p₁' = q := by
    rw [famExp_re, hre1]; field_simp [hp₁'0]; ring
  have hnorm_s : eLpNorm (fam s p p₁ z) (ENNReal.ofReal p₁) volume =
      (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume) ^ (p / p₁) :=
    eLpNorm_fam_eq_rpow (s := s) (p := p) (p₁ := p₁) hp1' (z := z) (q := p₁)
      (by linarith : (1:ℝ) < p₁) hexps
  have hnorm_g : eLpNorm (fam g q p₁' z) (ENNReal.ofReal p₁') volume =
      (eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume) ^ (q / p₁') :=
    eLpNorm_fam_eq_rpow (s := g) (p := q) (p₁ := p₁') hq1' (z := z) (q := p₁') hp₁'pos hexpg
  calc ‖∫ x, hilbertH (fam s p p₁ z) x * fam g q p₁' z x ∂volume‖
      ≤ ∫ x, ‖hilbertH (fam s p p₁ z) x * fam g q p₁' z x‖ ∂volume :=
        norm_integral_le_integral_norm _
    _ = ∫ x, ‖hilbertH (fam s p p₁ z) x‖ * ‖fam g q p₁' z x‖ ∂volume := by simp_rw [norm_mul]
    _ ≤ (∫ x, ‖hilbertH (fam s p p₁ z) x‖ ^ p₁ ∂volume) ^ (1 / p₁) *
          (∫ x, ‖fam g q p₁' z x‖ ^ p₁' ∂volume) ^ (1 / p₁') :=
        integral_mul_norm_le_Lp_mul_Lq hp1q hmemH hmem_gp1'
    _ = ((eLpNorm (hilbertH (fam s p p₁ z)) (ENNReal.ofReal p₁) volume) ^ p₁).toReal ^ (1 / p₁) *
          ((eLpNorm (fam g q p₁' z) (ENNReal.ofReal p₁') volume) ^ p₁').toReal ^ (1 / p₁') := by
        rw [integral_norm_rpow_eq_toReal_pow (by linarith : (1:ℝ) < p₁) hmemH.aestronglyMeasurable,
          integral_norm_rpow_eq_toReal_pow hp₁'pos hmem_gp1'.aestronglyMeasurable]
    _ ≤ ((ENNReal.ofReal M * eLpNorm (fam s p p₁ z) (ENNReal.ofReal p₁) volume) ^ p₁).toReal
          ^ (1 / p₁) *
          ((eLpNorm (fam g q p₁' z) (ENNReal.ofReal p₁') volume) ^ p₁').toReal ^ (1 / p₁') := by
        have hstep : ((eLpNorm (hilbertH (fam s p p₁ z)) (ENNReal.ofReal p₁) volume) ^ p₁).toReal
            ≤ ((ENNReal.ofReal M * eLpNorm (fam s p p₁ z) (ENNReal.ofReal p₁) volume) ^ p₁).toReal :=
          ENNReal.toReal_mono (by finiteness)
            (ENNReal.rpow_le_rpow hboundH (by linarith : (0:ℝ) ≤ p₁))
        have hp1p : (0:ℝ) ≤ 1 / p₁ := by positivity
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ENNReal.toReal_nonneg hstep hp1p) (by positivity)
    _ = (M ^ p₁ * (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal ^ p) ^ (1 / p₁) *
          ((eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume).toReal ^ q) ^ (1 / p₁') := by
        have hpow2 : ∀ (X : ℝ≥0∞) (a b : ℝ), ((X ^ a) ^ b).toReal = X.toReal ^ (a * b) :=
          fun X a b => by rw [← ENNReal.rpow_mul]; exact (ENNReal.toReal_rpow X (a * b)).symm
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : (0:ℝ) ≤ p₁), ENNReal.toReal_mul,
          hnorm_s, hnorm_g, hpow2, hpow2,
          div_mul_cancel₀ _ hp₁0, div_mul_cancel₀ _ hp₁'0,
          show ((ENNReal.ofReal M) ^ p₁).toReal = M ^ p₁ from by
            rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hM0]]
    _ = M * (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal ^ (p / p₁) *
          (eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume).toReal ^ (q / p₁') := by
        rw [Real.mul_rpow (Real.rpow_nonneg hM0 p₁) (by positivity), ← Real.rpow_mul hM0,
          ← Real.rpow_mul ENNReal.toReal_nonneg, ← Real.rpow_mul ENNReal.toReal_nonneg]
        rw [mul_one_div p₁ p₁, div_self hp₁0, Real.rpow_one, mul_one_div p p₁, mul_one_div q p₁',
          mul_assoc]

/-- For `Re z ∈ [0,1]`, `‖famCoeff p p₁ c z‖` is bounded by the max of its two boundary values
(the exponent `Re γ(z)` decreases monotonically from `p/2` to `p/p₁` as `Re z : 0 → 1`, and
`‖c‖^t` is monotone in `t`, in one direction if `‖c‖ ≥ 1` and the other if `‖c‖ < 1`). -/
theorem norm_famCoeff_le_max {p p₁ : ℝ} (hp₁pos : 0 < p₁) (hp1' : 1 < p) {c z : ℂ}
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) :
    ‖famCoeff p p₁ c z‖ ≤ max (‖c‖ ^ (p / 2)) (‖c‖ ^ (p / p₁)) := by
  rw [norm_famCoeff]
  split_ifs with hc
  · positivity
  · rw [famExp_re]
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hp0 : 0 < p := by linarith
    rcases le_total (p/2) (p/p₁) with hcmp | hcmp
    · have hcmp' : p * p₁ ≤ p * 2 := by
        have h := mul_le_mul_of_nonneg_right hcmp (mul_pos (by norm_num : (0:ℝ) < 2) hp₁pos).le
        calc p * p₁ = p / 2 * (2 * p₁) := by field_simp
          _ ≤ p / p₁ * (2 * p₁) := h
          _ = p * 2 := by field_simp
      have hp1le2 : p₁ ≤ 2 := le_of_mul_le_mul_left (by linarith) hp0
      have hsign : (0:ℝ) ≤ 1/p₁ - 1/2 := by
        rw [div_sub_div _ _ (ne_of_gt hp₁pos) (by norm_num : (2:ℝ) ≠ 0)]
        apply div_nonneg _ (by positivity)
        linarith
      have hlow : p / 2 ≤ p * ((1 - z.re) / 2 + z.re / p₁) := by
        have key : p * ((1 - z.re) / 2 + z.re / p₁) - p / 2 = p * z.re * (1/p₁ - 1/2) := by
          field_simp; ring
        nlinarith [mul_nonneg (mul_nonneg hp0.le hz0) hsign]
      have hhigh : p * ((1 - z.re) / 2 + z.re / p₁) ≤ p / p₁ := by
        have key : p / p₁ - p * ((1 - z.re) / 2 + z.re / p₁) = p * (1 - z.re) * (1/p₁ - 1/2) := by
          field_simp; ring
        nlinarith [mul_nonneg (mul_nonneg hp0.le (by linarith : (0:ℝ) ≤ 1 - z.re)) hsign]
      by_cases h1 : ‖c‖ < 1
      · exact le_trans (Real.rpow_le_rpow_of_exponent_ge hcpos h1.le hlow) (le_max_left _ _)
      · push_neg at h1
        exact le_trans (Real.rpow_le_rpow_of_exponent_le h1 hhigh) (le_max_right _ _)
    · have hcmp' : p * 2 ≤ p * p₁ := by
        have h := mul_le_mul_of_nonneg_right hcmp (mul_pos (by norm_num : (0:ℝ) < 2) hp₁pos).le
        calc p * 2 = p / p₁ * (2 * p₁) := by field_simp
          _ ≤ p / 2 * (2 * p₁) := h
          _ = p * p₁ := by field_simp
      have hp1ge2 : 2 ≤ p₁ := le_of_mul_le_mul_left (by linarith) hp0
      have hsign : (0:ℝ) ≤ 1/2 - 1/p₁ := by
        rw [div_sub_div _ _ (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hp₁pos)]
        apply div_nonneg _ (by positivity)
        linarith
      have hlow : p / p₁ ≤ p * ((1 - z.re) / 2 + z.re / p₁) := by
        have key : p * ((1 - z.re) / 2 + z.re / p₁) - p / p₁ = p * (1 - z.re) * (1/2 - 1/p₁) := by
          field_simp; ring
        nlinarith [mul_nonneg (mul_nonneg hp0.le (by linarith : (0:ℝ) ≤ 1 - z.re)) hsign]
      have hhigh : p * ((1 - z.re) / 2 + z.re / p₁) ≤ p / 2 := by
        have key : p / 2 - p * ((1 - z.re) / 2 + z.re / p₁) = p * z.re * (1/2 - 1/p₁) := by
          field_simp; ring
        nlinarith [mul_nonneg (mul_nonneg hp0.le hz0) hsign]
      by_cases h1 : ‖c‖ < 1
      · exact le_trans (Real.rpow_le_rpow_of_exponent_ge hcpos h1.le hlow) (le_max_right _ _)
      · push_neg at h1
        exact le_trans (Real.rpow_le_rpow_of_exponent_le h1 hhigh) (le_max_left _ _)

open Complex.HadamardThreeLines in
/-- The pairing sum is bounded on the closed strip `0 ≤ Re z ≤ 1` (finite sum of terms, each
bounded via `norm_famCoeff_le_max`). -/
theorem bddAbove_pairSum (s g : MeasureTheory.SimpleFunc ℂ ℂ) {p p₁ q p₁' : ℝ}
    (hp1' : 1 < p) (hq1' : 1 < q) (hp₁pos : 0 < p₁) (hp₁'pos : 0 < p₁') :
    BddAbove ((norm ∘ (fun z => ∑ c ∈ s.range.erase 0, ∑ d ∈ g.range.erase 0,
      famCoeff p p₁ c z * famCoeff q p₁' d z * pairConst s g c d)) ''
      verticalClosedStrip 0 1) := by
  use ∑ c ∈ s.range.erase 0, ∑ d ∈ g.range.erase 0,
    (max (‖c‖ ^ (p/2)) (‖c‖ ^ (p/p₁))) * (max (‖d‖ ^ (q/2)) (‖d‖ ^ (q/p₁'))) * ‖pairConst s g c d‖
  rintro _ ⟨z, hz, rfl⟩
  simp only [Function.comp_apply]
  have hz0 : 0 ≤ z.re := hz.1
  have hz1 : z.re ≤ 1 := hz.2
  calc ‖∑ c ∈ s.range.erase 0, ∑ d ∈ g.range.erase 0,
        famCoeff p p₁ c z * famCoeff q p₁' d z * pairConst s g c d‖
      ≤ ∑ c ∈ s.range.erase 0, ‖∑ d ∈ g.range.erase 0,
          famCoeff p p₁ c z * famCoeff q p₁' d z * pairConst s g c d‖ := norm_sum_le _ _
    _ ≤ ∑ c ∈ s.range.erase 0, ∑ d ∈ g.range.erase 0,
          ‖famCoeff p p₁ c z * famCoeff q p₁' d z * pairConst s g c d‖ := by
        apply Finset.sum_le_sum; intro c _; exact norm_sum_le _ _
    _ ≤ ∑ c ∈ s.range.erase 0, ∑ d ∈ g.range.erase 0,
          (max (‖c‖ ^ (p/2)) (‖c‖ ^ (p/p₁))) * (max (‖d‖ ^ (q/2)) (‖d‖ ^ (q/p₁'))) *
            ‖pairConst s g c d‖ := by
        apply Finset.sum_le_sum; intro c _
        apply Finset.sum_le_sum; intro d _
        rw [norm_mul, norm_mul]
        exact mul_le_mul
          (mul_le_mul (norm_famCoeff_le_max hp₁pos hp1' hz0 hz1)
            (norm_famCoeff_le_max hp₁'pos hq1' hz0 hz1) (norm_nonneg _) (by positivity))
          le_rfl (norm_nonneg _) (by positivity)

theorem interpTheta_conjExponent {p q p₁ p₁' : ℝ} (hpq : p.HolderConjugate q)
    (hp1q : p₁.HolderConjugate p₁') :
    interpTheta q p₁' = interpTheta p p₁ := by
  have h1 := hpq.inv_add_inv_eq_one
  have h2 := hp1q.inv_add_inv_eq_one
  rw [inv_eq_one_div, inv_eq_one_div] at h1 h2
  unfold interpTheta
  have e1 : (1:ℝ)/2 - 1/q = -(1/2 - 1/p) := by linarith
  have e2 : (1:ℝ)/2 - 1/p₁' = -(1/2 - 1/p₁) := by linarith
  rw [e1, e2, neg_div_neg_eq]

/-- Elementary (CZ-wall-free) pointwise domination: for `2 ≤ p ≤ p₁` and `a ≥ 0`,
`a^p ≤ a^2 + a^{p₁}`. Split on `a ≤ 1` (bigger exponent shrinks the value) vs `a > 1` (bigger
exponent grows it). -/
theorem rpow_le_rpow_two_add_rpow {p p₁ : ℝ} (hp2 : (2:ℝ) ≤ p) (hpp₁ : p ≤ p₁)
    {a : ℝ} (ha : 0 ≤ a) : a ^ p ≤ a ^ (2:ℝ) + a ^ p₁ := by
  rcases eq_or_lt_of_le ha with rfl | hapos
  · simp only [Real.zero_rpow (show p ≠ 0 by linarith), Real.zero_rpow (show (2:ℝ) ≠ 0 by norm_num)]
    positivity
  by_cases h1 : a ≤ 1
  · have : a ^ p ≤ a ^ (2:ℝ) := Real.rpow_le_rpow_of_exponent_ge hapos h1 hp2
    linarith [Real.rpow_nonneg ha p₁]
  · push_neg at h1
    have : a ^ p ≤ a ^ p₁ := Real.rpow_le_rpow_of_exponent_le h1.le hpp₁
    linarith [Real.rpow_nonneg ha (2:ℝ)]

/-- CZ-wall-free membership interpolation: if `Ω ∈ L² ∩ L^{p₁}` then `Ω ∈ L^p` for
`2 ≤ p ≤ p₁`, via the elementary pointwise bound above (no operator norm / three-lines argument
needed — this is about the FUNCTION `Ω` belonging to the space, not about a bound on its norm). -/
theorem memLp_of_memLp_two_of_memLp {p p₁ : ℝ} (hp2 : (2:ℝ) ≤ p) (hpp₁ : p ≤ p₁)
    {Ω : ℂ → ℂ} (hΩ2 : MemLp Ω 2 volume) (hΩp₁ : MemLp Ω (ENNReal.ofReal p₁) volume) :
    MemLp Ω (ENNReal.ofReal p) volume := by
  have hmeas := hΩ2.aestronglyMeasurable
  have hp0 : (0:ℝ) < p := by linarith
  have hp₁0 : (0:ℝ) < p₁ := by linarith
  rw [← integrable_norm_rpow_iff hmeas (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]
  have hI2 : Integrable (fun x => ‖Ω x‖ ^ (2:ℝ)) volume := by
    have := hΩ2.integrable_norm_rpow (two_ne_zero) (by norm_num)
    simpa using this
  have hIp₁ : Integrable (fun x => ‖Ω x‖ ^ p₁) volume := by
    have := hΩp₁.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp₁0).ne' ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal hp₁0.le] at this
  apply Integrable.mono' (hI2.add hIp₁)
    ((Real.continuous_rpow_const hp0.le).comp_aestronglyMeasurable hmeas.norm)
  filter_upwards with x
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) p)]
  exact rpow_le_rpow_two_add_rpow hp2 hpp₁ (norm_nonneg _)

open Complex.HadamardThreeLines in
/-- **The simple-function core.** Riesz–Thorin, one-sided fixed-pair, for `hilbertH` on simple
functions: given the general `L^{p₁}` bound `hgen` (delivered by `hilbertH_memLp_of_smooth_bound`
from the C₀^∞ hypothesis) and the unconditional `L²` isometry, interpolate to get the bound at
every `p ∈ (2, p₁]`. -/
theorem simpleFunc_hilbertH_bound {p₁ M : ℝ} (hp₁ : 2 < p₁) (hM0 : 0 ≤ M)
    (hgen : ∀ ω : ℂ → ℂ, MemLp ω (ENNReal.ofReal p₁) volume →
      MemLp (hilbertH ω) (ENNReal.ofReal p₁) volume ∧
        eLpNorm (hilbertH ω) (ENNReal.ofReal p₁) volume ≤
          ENNReal.ofReal M * eLpNorm ω (ENNReal.ofReal p₁) volume)
    {p : ℝ} (hp2 : 2 < p) (hpp₁ : p ≤ p₁)
    (s : MeasureTheory.SimpleFunc ℂ ℂ) (hs : MemLp (s : ℂ → ℂ) (ENNReal.ofReal p) volume) :
    eLpNorm (hilbertH s) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (M ^ interpTheta p p₁) * eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume := by
  have hp1' : (1:ℝ) < p := by linarith
  have hp1'' : (1:ℝ) < p₁ := by linarith
  set θ := interpTheta p p₁ with hθ_def
  obtain ⟨hθ0, hθ1⟩ := interpTheta_mem_Ioc hp₁ hp2 hpp₁
  have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp1'
  have hp1q : p₁.HolderConjugate (Real.conjExponent p₁) :=
    Real.HolderConjugate.conjExponent hp1''
  -- `MemLp (hilbertH s) (ofReal p)`, built WITHOUT the still-open general CZ wall
  -- (`hilbertH_memLp`/`zygmund_calderon`): `s` simple ⟹ its finite-measure-preimage condition
  -- is exponent-independent, so `s ∈ L² ∩ L^{p₁}` too; then `hgen` (at `p₁`) and
  -- `hilbertH_memLp_two` (unconditional at `2`) give `hilbertH s ∈ L² ∩ L^{p₁}`, and the
  -- elementary membership-interpolation lemma above finishes it.
  have hfin : ∀ y : ℂ, y ≠ 0 → volume (s ⁻¹' {y}) < ⊤ := fun y hy =>
    MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_memLp
      (show (ENNReal.ofReal p) ≠ 0 by positivity) ENNReal.ofReal_ne_top s hs y hy
  have hs2 : MemLp (s : ℂ → ℂ) 2 volume :=
    MeasureTheory.SimpleFunc.memLp_of_finite_measure_preimage 2 hfin
  have hsp₁ : MemLp (s : ℂ → ℂ) (ENNReal.ofReal p₁) volume :=
    MeasureTheory.SimpleFunc.memLp_of_finite_measure_preimage (ENNReal.ofReal p₁) hfin
  have hHmemLp : MemLp (hilbertH (s : ℂ → ℂ)) (ENNReal.ofReal p) volume :=
    memLp_of_memLp_two_of_memLp hp2.le hpp₁ (hilbertH_memLp_two hs2).1 (hgen s hsp₁).1
  have hraw : eLpNorm (hilbertH (s : ℂ → ℂ)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (M ^ θ * (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal) := by
    apply eLpNorm_le_of_forall_dual_simpleFunc_le hpq hHmemLp
      (mul_nonneg (Real.rpow_nonneg hM0 θ) ENNReal.toReal_nonneg)
    intro g hgle1
    set q := Real.conjExponent p with hq_def
    set p₁' := Real.conjExponent p₁ with hp₁'_def
    have hq1' : (1:ℝ) < q := hpq.symm.lt
    have hp₁'pos : 0 < p₁' := hp1q.symm.pos
    have hg : MemLp (g : ℂ → ℂ) (ENNReal.ofReal q) volume :=
      lt_of_le_of_lt hgle1 (by norm_num : (1:ℝ≥0∞) < ⊤)
    have hθ' : interpTheta q p₁' = θ := interpTheta_conjExponent hpq hp1q
    have hp₁'lt2 : p₁' < 2 := by
      have hsum := hp1q.inv_add_inv_eq_one
      rw [inv_eq_one_div, inv_eq_one_div] at hsum
      have h1 : (1:ℝ)/p₁ < 1/2 := by
        apply div_lt_div_of_pos_left one_pos (by linarith) hp₁
      have h2 : (1:ℝ)/2 < 1/p₁' := by linarith
      have hinv : (1/p₁') * p₁' = 1 := one_div_mul_cancel hp₁'pos.ne'
      nlinarith [mul_lt_mul_of_pos_right h2 hp₁'pos]
    set F : ℂ → ℂ := fun z => ∑ c ∈ s.range.erase 0, ∑ d ∈ g.range.erase 0,
      famCoeff p p₁ c z * famCoeff q p₁' d z * pairConst s g c d with hF_def
    have hFeq : ∀ z, F z = ∫ x, hilbertH (fam s p p₁ z) x * fam g q p₁' z x ∂volume := fun z =>
      (integral_hilbertH_fam_mul_fam z hp1' hs hq1' hg).symm
    have hFθ : F (θ:ℂ) = ∫ x, hilbertH (s:ℂ→ℂ) x * g x ∂volume := by
      rw [hFeq, fam_interpTheta hp₁ hp2 hpp₁]
      congr 2
      rw [← hθ', fam_interpTheta' hp₁'lt2.ne hp₁'pos.ne' (lt_trans one_pos hq1').ne']
    have ha : ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ), ‖F z‖ ≤
        (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal ^ (p / 2) *
          (eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume).toReal ^ (q / 2) := by
      intro z hz
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
      have hzeq : z = (z.im : ℂ) * I := by
        apply Complex.ext <;> simp [hz]
      rw [hFeq, hzeq]
      exact boundary_bound_zero z.im hp1' hs hq1' hg
    have hb : ∀ z ∈ Complex.re ⁻¹' ({1} : Set ℝ), ‖F z‖ ≤
        M * (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal ^ (p / p₁) *
          (eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume).toReal ^ (q / p₁') := by
      intro z hz
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
      have hzeq : z = 1 + (z.im : ℂ) * I := by
        apply Complex.ext <;> simp [hz]
      rw [hFeq, hzeq]
      exact boundary_bound_one z.im hp1' hs hq1' hg hp₁ hp1q (by linarith) hgen
    have hd : DiffContOnCl ℂ F (verticalStrip 0 1) :=
      (differentiable_pairSum s g p p₁ q p₁').diffContOnCl
    have hB : BddAbove ((norm ∘ F) '' verticalClosedStrip 0 1) :=
      bddAbove_pairSum s g hp1' hq1' (by linarith) hp₁'pos
    have hzmem : (θ:ℂ) ∈ verticalClosedStrip 0 1 := by
      rw [hθ_def]
      refine ⟨?_, ?_⟩ <;> simp only [Complex.ofReal_re]
      · exact hθ0.le
      · exact hθ1
    have hHad := norm_le_interp_of_mem_verticalClosedStrip₀₁' F hzmem hd hB ha hb
    rw [hFθ, Complex.ofReal_re] at hHad
    set A := (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal with hA_def
    set B := (eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume).toReal with hB_def
    have hBmem : 0 ≤ B ∧ B ≤ 1 := ⟨ENNReal.toReal_nonneg, by
      have : (eLpNorm (g:ℂ→ℂ) (ENNReal.ofReal q) volume).toReal ≤ (1:ℝ≥0∞).toReal :=
        ENNReal.toReal_mono (by norm_num) hgle1
      simpa using this⟩
    have step1 : (A ^ (p/2) * B ^ (q/2)) ^ (1 - θ) ≤ A ^ ((p/2) * (1-θ)) := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul (by positivity)]
      calc A ^ (p/2 * (1 - θ)) * B ^ (q/2*(1-θ))
          ≤ A ^ (p/2 * (1 - θ)) * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.rpow_le_one hBmem.1 hBmem.2 (by positivity)
        _ = A ^ (p/2 * (1-θ)) := mul_one _
    have step2 : (M * A ^ (p/p₁) * B ^ (q/p₁')) ^ θ ≤ M ^ θ * A ^ ((p/p₁) * θ) := by
      rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hM0 (by positivity),
        ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity), mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hM0 θ)
      calc A ^ (p/p₁*θ) * B ^ (q/p₁'*θ)
          ≤ A ^ (p/p₁*θ) * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.rpow_le_one hBmem.1 hBmem.2 (by positivity)
        _ = A ^ (p/p₁*θ) := mul_one _
    have hexp1 : p/2*(1-θ) + p/p₁*θ = 1 := by
      have hspec := interpTheta_spec hp₁ hp2 hpp₁
      rw [← hθ_def] at hspec
      field_simp at hspec ⊢
      nlinarith [hspec]
    have hA_nonneg : (0:ℝ) ≤ A := by rw [hA_def]; exact ENNReal.toReal_nonneg
    rcases hA_nonneg.eq_or_lt with hA0 | hApos
    · have hfactor0 : (M * A ^ (p/p₁) * B ^ (q/p₁')) ^ θ = 0 := by
        rw [← hA0, Real.zero_rpow (show (p/p₁:ℝ) ≠ 0 by positivity), mul_zero, zero_mul,
          Real.zero_rpow (ne_of_gt hθ0)]
      calc ‖∫ x, hilbertH (s:ℂ→ℂ) x * g x ∂volume‖
          ≤ (A ^ (p/2) * B ^ (q/2)) ^ (1-θ) * (M * A ^ (p/p₁) * B ^ (q/p₁')) ^ θ := hHad
        _ = 0 := by rw [hfactor0, mul_zero]
        _ ≤ M ^ θ * A := by rw [← hA0]; simp
    · calc ‖∫ x, hilbertH (s:ℂ→ℂ) x * g x ∂volume‖
          ≤ (A ^ (p/2) * B ^ (q/2)) ^ (1-θ) * (M * A ^ (p/p₁) * B ^ (q/p₁')) ^ θ := hHad
        _ ≤ A ^ (p/2*(1-θ)) * (M ^ θ * A ^ (p/p₁*θ)) :=
            mul_le_mul step1 step2 (by positivity) (by positivity)
        _ = M ^ θ * A ^ (p/2*(1-θ) + p/p₁*θ) := by
            rw [Real.rpow_add hApos]; ring
        _ = M ^ θ * A := by rw [hexp1, Real.rpow_one]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hM0 θ), ENNReal.ofReal_toReal hs.eLpNorm_ne_top] at hraw
  exact hraw

/-- **Fatou/subsequence descent.** Bridges the simple-function core up to `hilbertHSmooth` on
`C₀^∞`: approximate `φ` by the canonical `approxOn`-simple-function sequence (the SAME sequence
works simultaneously at every finite exponent, since `φ` is bounded with compact support), get the
bound on each approximant from `simpleFunc_hilbertH_bound`, transport the `L²` convergence
through `hilbertH`'s linearity + isometry to an a.e.-convergent subsequence, and close with
Fatou (`Lp.eLpNorm_lim_le_liminf_eLpNorm`) plus the `hilbertH_eq_ae_smooth` linchpin. -/
theorem hilbertH_boundedLp_interp {p₁ M : ℝ} (hp₁ : 2 < p₁) (hM0 : 0 ≤ M)
    (hsmooth : ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p₁) ≤
        ENNReal.ofReal M * eLpNorm φ (ENNReal.ofReal p₁))
    {p : ℝ} (hp2 : 2 < p) (hpp₁ : p ≤ p₁) :
    ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p) ≤
        ENNReal.ofReal (M ^ ((1/2 - 1/p) / (1/2 - 1/p₁))) * eLpNorm φ (ENNReal.ofReal p) := by
  intro φ hφ hc
  have hp1' : (1:ℝ) < p := by linarith
  have hp1'' : (1:ℝ) < p₁ := by linarith
  have hgen := hilbertH_memLp_of_smooth_bound hp1'' hsmooth
  have hφcont : Continuous φ := hφ.continuous
  have hφmeas : Measurable φ := hφcont.measurable
  have hφ2 : MemLp φ 2 volume := hφcont.memLp_of_hasCompactSupport hc
  have hφp : MemLp φ (ENNReal.ofReal p) volume := hφcont.memLp_of_hasCompactSupport hc
  set s : ℕ → MeasureTheory.SimpleFunc ℂ ℂ :=
    fun n => MeasureTheory.SimpleFunc.approxOn φ hφmeas (Set.range φ ∪ {0}) 0 (by simp) n
    with hs_def
  have hs2 : ∀ n, MemLp (s n : ℂ → ℂ) 2 volume :=
    fun n => MeasureTheory.SimpleFunc.memLp_approxOn_range hφmeas hφ2 n
  have hsp : ∀ n, MemLp (s n : ℂ → ℂ) (ENNReal.ofReal p) volume :=
    fun n => MeasureTheory.SimpleFunc.memLp_approxOn_range hφmeas hφp n
  have htendsto2 : Tendsto (fun n => eLpNorm ((s n : ℂ → ℂ) - φ) 2 volume) atTop (𝓝 0) :=
    MeasureTheory.SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm (by norm_num) hφmeas hφ2.eLpNorm_lt_top
  have htendstop : Tendsto (fun n => eLpNorm ((s n : ℂ → ℂ) - φ) (ENNReal.ofReal p) volume)
      atTop (𝓝 0) :=
    MeasureTheory.SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm ENNReal.ofReal_ne_top hφmeas hφp.eLpNorm_lt_top
  -- linearity transport at p = 2: `hilbertH (sₙ - φ) =ᵐ hilbertH sₙ - hilbertH φ`
  have h2neg : hilbertH (-φ) =ᵐ[volume] -hilbertH φ := by
    have := hilbertH_smul_ae (-1) hφ2
    rwa [neg_one_smul, neg_one_smul] at this
  have hlin : ∀ n, hilbertH ((s n : ℂ → ℂ) - φ) =ᵐ[volume] hilbertH (s n) - hilbertH φ := by
    intro n
    have h1 : hilbertH ((s n : ℂ → ℂ) + (-φ)) =ᵐ[volume] hilbertH (s n) + hilbertH (-φ) :=
      hilbertH_add_ae (hs2 n) hφ2.neg
    have h3 : hilbertH (s n) + hilbertH (-φ) =ᵐ[volume] hilbertH (s n) - hilbertH φ := by
      filter_upwards [h2neg] with x hx
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply] at hx ⊢
      rw [hx]; ring
    rw [sub_eq_add_neg]
    exact h1.trans h3
  have heLp_eq : ∀ n, eLpNorm (hilbertH (s n) - hilbertH φ) 2 volume =
      eLpNorm ((s n : ℂ → ℂ) - φ) 2 volume := fun n =>
    (eLpNorm_congr_ae (hlin n)).symm.trans (hilbertH_memLp_two ((hs2 n).sub hφ2)).2
  have hfg : Tendsto (fun n => eLpNorm (hilbertH (s n) - hilbertH φ) 2 volume) atTop (𝓝 0) := by
    simp_rw [heLp_eq]
    exact htendsto2
  have hHmeas : ∀ n, AEStronglyMeasurable (hilbertH (s n)) volume :=
    fun n => (hilbertH_memLp_two (hs2 n)).1.aestronglyMeasurable
  have hgmeas : AEStronglyMeasurable (hilbertH φ) volume :=
    (hilbertH_memLp_two hφ2).1.aestronglyMeasurable
  have htim : TendstoInMeasure volume (fun n => hilbertH (s n)) atTop (hilbertH φ) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hfg
  obtain ⟨ns, hns_mono, hns_ae⟩ := htim.exists_seq_tendsto_ae
  have hfatou : eLpNorm (hilbertH φ) (ENNReal.ofReal p) volume ≤
      atTop.liminf (fun i => eLpNorm (hilbertH (s (ns i))) (ENNReal.ofReal p) volume) :=
    MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm (fun i => hHmeas (ns i)) (hilbertH φ) hgmeas hns_ae
  set θ : ℝ := (1/2 - 1/p) / (1/2 - 1/p₁) with hθ_def
  have hbound : ∀ n, eLpNorm (hilbertH (s n)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (M ^ θ) * eLpNorm (s n : ℂ → ℂ) (ENNReal.ofReal p) volume := by
    intro n
    have hraw := simpleFunc_hilbertH_bound hp₁ hM0 hgen hp2 hpp₁ (s n) (hsp n)
    rwa [show interpTheta p p₁ = θ from rfl] at hraw
  have h1p : (1:ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hmink : ∀ n, eLpNorm (s n : ℂ → ℂ) (ENNReal.ofReal p) volume ≤
      eLpNorm φ (ENNReal.ofReal p) volume + eLpNorm ((s n : ℂ → ℂ) - φ) (ENNReal.ofReal p) volume := by
    intro n
    have heq : (s n : ℂ → ℂ) = φ + ((s n : ℂ → ℂ) - φ) := by ring
    calc eLpNorm (s n : ℂ → ℂ) (ENNReal.ofReal p) volume
        = eLpNorm (φ + ((s n : ℂ → ℂ) - φ)) (ENNReal.ofReal p) volume := by rw [← heq]
      _ ≤ eLpNorm φ (ENNReal.ofReal p) volume +
            eLpNorm ((s n : ℂ → ℂ) - φ) (ENNReal.ofReal p) volume :=
          eLpNorm_add_le h1p
  have hns_tendsto : Tendsto ns atTop atTop := hns_mono.tendsto_atTop
  have hsub2 : Tendsto (fun i => eLpNorm ((s (ns i) : ℂ → ℂ) - φ) (ENNReal.ofReal p) volume)
      atTop (𝓝 0) := htendstop.comp hns_tendsto
  have hrhs_tendsto : Tendsto (fun i => ENNReal.ofReal (M ^ θ) * eLpNorm φ (ENNReal.ofReal p) volume +
      ENNReal.ofReal (M ^ θ) * eLpNorm ((s (ns i) : ℂ → ℂ) - φ) (ENNReal.ofReal p) volume)
      atTop (𝓝 (ENNReal.ofReal (M ^ θ) * eLpNorm φ (ENNReal.ofReal p) volume)) := by
    have hmulconv := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (M ^ θ)) hsub2
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using Tendsto.add tendsto_const_nhds hmulconv
  have hliminf_le : atTop.liminf
      (fun i => eLpNorm (hilbertH (s (ns i))) (ENNReal.ofReal p) volume) ≤
      ENNReal.ofReal (M ^ θ) * eLpNorm φ (ENNReal.ofReal p) volume := by
    calc atTop.liminf (fun i => eLpNorm (hilbertH (s (ns i))) (ENNReal.ofReal p) volume)
        ≤ atTop.liminf (fun i =>
            ENNReal.ofReal (M ^ θ) * eLpNorm (s (ns i) : ℂ → ℂ) (ENNReal.ofReal p) volume) :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall fun i => hbound (ns i))
      _ ≤ atTop.liminf (fun i => ENNReal.ofReal (M ^ θ) * eLpNorm φ (ENNReal.ofReal p) volume +
            ENNReal.ofReal (M ^ θ) * eLpNorm ((s (ns i) : ℂ → ℂ) - φ) (ENNReal.ofReal p) volume) :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall fun i =>
            (mul_le_mul_right (hmink (ns i)) (ENNReal.ofReal (M ^ θ))).trans_eq
              (mul_add (ENNReal.ofReal (M ^ θ)) _ _))
      _ = ENNReal.ofReal (M ^ θ) * eLpNorm φ (ENNReal.ofReal p) volume := hrhs_tendsto.liminf_eq
  have hfinal : eLpNorm (hilbertH φ) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (M ^ θ) * eLpNorm φ (ENNReal.ofReal p) volume := hfatou.trans hliminf_le
  rwa [eLpNorm_congr_ae (hilbertH_eq_ae_smooth hφ hc)] at hfinal

end LiZhongQC
