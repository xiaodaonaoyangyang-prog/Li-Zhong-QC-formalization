import LiZhongQC.Ch02.S11_IntegralOperators
import LiZhongQC.Lemmas.LpDuality
import LiZhongQC.Lemmas.HilbertInterp
import Mathlib.Analysis.Complex.Hadamard

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-! ## RT1: the general fixed-pair (`p₀`, `p₁`) Riesz–Thorin interpolation theorem.

Generalizes `HilbertInterp.lean`'s `p₀ = 2` special case (which used the exact `L²` isometry on
the left boundary) to an arbitrary pair `p₀, p₁ > 1`, with `θ` and `p` linked by
`1/p = (1-θ)/p₀ + θ/p₁` exactly as given (not solved-for) — both boundaries now use the SAME
Hölder + general-bound (`h₀`/`h₁`) technique. Reuses `pairConst`, `integrable_pairConst_term`,
`hilbertH_zero_ae`, `hilbertH_finset_sum_ae`, `simpleFunc_eq_sum_indicator_preimage`,
`enn_pow_eLpNorm_eq_lintegral`, `integral_norm_rpow_eq_toReal_pow` verbatim from the installed
`HilbertInterp`/`LpDuality` leaves (none of those depend on the specific `famExp` formula). -/

/-! ### The analytic family, generalized to a `(p₀, p₁)` pair -/

/-- The exponent function `γ(z) = p·((1-z)/p₀ + z/p₁)`, entire and affine in `z`. Generalizes
`famExp` (which hardcoded `p₀ = 2`). -/
def famExpPair (p₀ p₁ p : ℝ) (z : ℂ) : ℂ := (p : ℂ) * ((1 - z) / p₀ + z / p₁)

/-- Generalizes `famCoeff`. -/
def famCoeffPair (p₀ p₁ p : ℝ) (c : ℂ) (z : ℂ) : ℂ :=
  if c = 0 then 0 else (c / (‖c‖ : ℂ)) * (‖c‖ : ℂ) ^ famExpPair p₀ p₁ p z

/-- Generalizes `fam`. -/
def famPair (s : MeasureTheory.SimpleFunc ℂ ℂ) (p₀ p₁ p : ℝ) (z : ℂ) : ℂ → ℂ :=
  fun a => ∑ c ∈ s.range, (s ⁻¹' {c}).indicator (fun _ => famCoeffPair p₀ p₁ p c z) a

/-- `θ` is given directly (not solved-for), so the recovery fact is a one-line substitution using
`hp : 1/p = (1-θ)/p₀ + θ/p₁` instead of the `interpTheta_spec`-style clearing-denominators
algebra. -/
theorem famExpPair_atTheta {p₀ p₁ p θ : ℝ} (hp0 : p ≠ 0)
    (hp : 1 / p = (1 - θ) / p₀ + θ / p₁) : famExpPair p₀ p₁ p (θ : ℂ) = 1 := by
  unfold famExpPair
  have hcast : ((1 - (θ:ℂ)) / p₀ + (θ:ℂ) / p₁) = (((1 - θ) / p₀ + θ / p₁ : ℝ) : ℂ) := by
    push_cast; ring
  rw [hcast, ← hp]
  push_cast
  rw [mul_one_div, div_self (by exact_mod_cast hp0 : (p:ℂ) ≠ 0)]

theorem famCoeffPair_atTheta {p₀ p₁ p θ : ℝ} (hp0 : p ≠ 0)
    (hp : 1 / p = (1 - θ) / p₀ + θ / p₁) (c : ℂ) :
    famCoeffPair p₀ p₁ p c (θ : ℂ) = c := by
  unfold famCoeffPair
  rw [famExpPair_atTheta hp0 hp]
  by_cases hc : c = 0
  · simp [hc]
  · rw [if_neg hc, Complex.cpow_one]
    have hcnorm : (‖c‖ : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero, norm_eq_zero]; exact hc
    field_simp

theorem famPair_atTheta {s : MeasureTheory.SimpleFunc ℂ ℂ} {p₀ p₁ p θ : ℝ} (hp0 : p ≠ 0)
    (hp : 1 / p = (1 - θ) / p₀ + θ / p₁) :
    famPair s p₀ p₁ p (θ : ℂ) = (s : ℂ → ℂ) := by
  funext a
  unfold famPair
  simp_rw [famCoeffPair_atTheta hp0 hp]
  exact (simpleFunc_eq_sum_indicator_preimage s a).symm

theorem famPair_apply (s : MeasureTheory.SimpleFunc ℂ ℂ) (p₀ p₁ p : ℝ) (z : ℂ) (a : ℂ) :
    famPair s p₀ p₁ p z a = famCoeffPair p₀ p₁ p (s a) z := by
  unfold famPair
  rw [Finset.sum_eq_single (s a)]
  · simp
  · intro c _ hc
    apply Set.indicator_of_notMem
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact fun h => hc h.symm
  · intro h
    exact absurd (MeasureTheory.SimpleFunc.mem_range_self s a) h

theorem famExpPair_re (p₀ p₁ p : ℝ) (z : ℂ) :
    (famExpPair p₀ p₁ p z).re = p * ((1 - z.re) / p₀ + z.re / p₁) := by
  have key : famExpPair p₀ p₁ p z =
      ((p / p₀ : ℝ) : ℂ) + ((p * (1 / p₁ - 1 / p₀) : ℝ) : ℂ) * z := by
    unfold famExpPair; push_cast; ring
  rw [key, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem norm_famCoeffPair (p₀ p₁ p : ℝ) (c : ℂ) (z : ℂ) :
    ‖famCoeffPair p₀ p₁ p c z‖ = if c = 0 then 0 else ‖c‖ ^ (famExpPair p₀ p₁ p z).re := by
  unfold famCoeffPair
  split_ifs with hc
  · simp
  · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr hc)]
    have : ‖c / (‖c‖:ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg c),
        div_self (norm_ne_zero_iff.mpr hc)]
    rw [this, one_mul]

/-- Generalizes `eLpNorm_fam_eq_rpow`; the proof never used the specific value of `p₀`, only the
identity `Re γ(z) · q = p`. -/
theorem eLpNorm_famPair_eq_rpow {s : MeasureTheory.SimpleFunc ℂ ℂ} {p₀ p₁ p : ℝ} (hp1' : 1 < p)
    {z : ℂ} {q : ℝ} (hq1 : 1 < q) (hre : (famExpPair p₀ p₁ p z).re * q = p) :
    eLpNorm (famPair s p₀ p₁ p z) (ENNReal.ofReal q) volume =
      (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume) ^ (p / q) := by
  have hq0 : q ≠ 0 := by linarith
  have hfm : AEStronglyMeasurable (famPair s p₀ p₁ p z) volume := by
    have : famPair s p₀ p₁ p z = (s.map (fun c => famCoeffPair p₀ p₁ p c z) : ℂ → ℂ) :=
      funext fun a => by rw [famPair_apply]; rfl
    rw [this]; exact SimpleFunc.aestronglyMeasurable _
  have hstep : (eLpNorm (famPair s p₀ p₁ p z) (ENNReal.ofReal q) volume) ^ q =
      ∫⁻ a, ‖famPair s p₀ p₁ p z a‖ₑ ^ q ∂volume := enn_pow_eLpNorm_eq_lintegral hq1 _ hfm
  have hpteq : ∀ a, ‖famPair s p₀ p₁ p z a‖ₑ ^ q = ‖s a‖ₑ ^ p := by
    intro a
    rw [famPair_apply, ← ofReal_norm, norm_famCoeffPair]
    by_cases hsa : s a = 0
    · simp only [hsa, if_pos, ENNReal.ofReal_zero, enorm_zero]
      rw [ENNReal.zero_rpow_of_pos (by linarith : (0:ℝ) < q),
        ENNReal.zero_rpow_of_pos (by linarith : (0:ℝ) < p)]
    · rw [if_neg hsa,
        ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (by linarith : (0:ℝ) ≤ q),
        ← Real.rpow_mul (norm_nonneg _), hre, ← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith : (0:ℝ) ≤ p)]
  have hkey : (eLpNorm (famPair s p₀ p₁ p z) (ENNReal.ofReal q) volume) ^ q =
      (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume) ^ p := by
    rw [hstep]
    simp_rw [hpteq]
    exact (enn_pow_eLpNorm_eq_lintegral hp1' (s : ℂ → ℂ) s.aestronglyMeasurable).symm
  calc eLpNorm (famPair s p₀ p₁ p z) (ENNReal.ofReal q) volume
      = ((eLpNorm (famPair s p₀ p₁ p z) (ENNReal.ofReal q) volume) ^ q) ^ (1 / q) := by
        rw [← ENNReal.rpow_mul, mul_one_div, div_self hq0, ENNReal.rpow_one]
    _ = ((eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume) ^ p) ^ (1 / q) := by rw [hkey]
    _ = (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume) ^ (p / q) := by
        rw [← ENNReal.rpow_mul]; congr 1; ring

theorem famPair_eq_sum_smul_indicator (s : MeasureTheory.SimpleFunc ℂ ℂ) (p₀ p₁ p : ℝ) (z : ℂ) :
    famPair s p₀ p₁ p z =
      ∑ c ∈ s.range.erase 0, famCoeffPair p₀ p₁ p c z • (s ⁻¹' {c}).indicator (1 : ℂ → ℂ) := by
  funext a
  rw [famPair_apply, Finset.sum_apply]
  by_cases hsa : s a = 0
  · rw [hsa, show famCoeffPair p₀ p₁ p 0 z = 0 from by simp [famCoeffPair]]
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

theorem hilbertH_famPair_ae' {s : MeasureTheory.SimpleFunc ℂ ℂ} {p₀ p₁ p : ℝ} (z : ℂ)
    (hp1' : 1 < p) (hs : MemLp (s : ℂ → ℂ) (ENNReal.ofReal p) volume) :
    hilbertH (famPair s p₀ p₁ p z) =ᵐ[volume]
      ∑ c ∈ s.range.erase 0,
        famCoeffPair p₀ p₁ p c z • hilbertH ((s ⁻¹' {c}).indicator (1 : ℂ → ℂ)) := by
  rw [famPair_eq_sum_smul_indicator]
  have hpne0 : ENNReal.ofReal p ≠ 0 := by
    simp only [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
  apply hilbertH_finset_sum_ae
  intro c hc
  have hcne : c ≠ 0 := (Finset.mem_erase.mp hc).1
  have hfin := MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_memLp
    hpne0 ENNReal.ofReal_ne_top s hs c hcne
  exact memLp_indicator_const 2 (s.measurableSet_fiber c) _ (Or.inr hfin.ne)

theorem memLp_famPair {s : MeasureTheory.SimpleFunc ℂ ℂ} {p₀ p₁ p : ℝ} (hp1' : 1 < p)
    (hs : MemLp (s : ℂ → ℂ) (ENNReal.ofReal p) volume) (z : ℂ) {r : ℝ} :
    MemLp (famPair s p₀ p₁ p z) (ENNReal.ofReal r) volume := by
  rw [famPair_eq_sum_smul_indicator]
  apply memLp_finsetSum'
  intro c hc
  have hcne : c ≠ 0 := (Finset.mem_erase.mp hc).1
  have hpne0 : ENNReal.ofReal p ≠ 0 := by
    simp only [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hfin := MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_memLp
    hpne0 ENNReal.ofReal_ne_top s hs c hcne
  exact (memLp_indicator_const (ENNReal.ofReal r) (s.measurableSet_fiber c) _
    (Or.inr hfin.ne)).const_smul _

theorem integral_hilbertH_famPair_mul_famPair {s g : MeasureTheory.SimpleFunc ℂ ℂ}
    {p₀ p₁ p q₀ q₁ q : ℝ} (z : ℂ) (hp1' : 1 < p) (hs : MemLp (s : ℂ → ℂ) (ENNReal.ofReal p) volume)
    (hq1' : 1 < q) (hg : MemLp (g : ℂ → ℂ) (ENNReal.ofReal q) volume) :
    ∫ x, hilbertH (famPair s p₀ p₁ p z) x * famPair g q₀ q₁ q z x ∂volume =
      ∑ c ∈ s.range.erase 0, ∑ d ∈ g.range.erase 0,
        famCoeffPair p₀ p₁ p c z * famCoeffPair q₀ q₁ q d z * pairConst s g c d := by
  have hae : (fun x => hilbertH (famPair s p₀ p₁ p z) x * famPair g q₀ q₁ q z x) =ᵐ[volume]
      (fun x => (∑ c ∈ s.range.erase 0, famCoeffPair p₀ p₁ p c z •
        hilbertH ((s ⁻¹' {c}).indicator (1 : ℂ → ℂ))) x * famPair g q₀ q₁ q z x) := by
    filter_upwards [hilbertH_famPair_ae' z hp1' hs] with x hx
    rw [hx]
  rw [integral_congr_ae hae, famPair_eq_sum_smul_indicator g q₀ q₁ q z]
  have hint : ∀ x, (∑ c ∈ s.range.erase 0, famCoeffPair p₀ p₁ p c z •
        hilbertH ((s ⁻¹' {c}).indicator (1 : ℂ → ℂ))) x *
      (∑ d ∈ g.range.erase 0, famCoeffPair q₀ q₁ q d z • (g ⁻¹' {d}).indicator (1 : ℂ → ℂ)) x =
      ∑ c ∈ s.range.erase 0, ∑ d ∈ g.range.erase 0,
        (famCoeffPair p₀ p₁ p c z * famCoeffPair q₀ q₁ q d z) *
          (hilbertH ((s ⁻¹' {c}).indicator (1 : ℂ → ℂ)) x *
            (g ⁻¹' {d}).indicator (1 : ℂ → ℂ) x) := by
    intro x
    simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro d _
    ring
  simp_rw [hint]
  have hintegrable : ∀ c ∈ s.range.erase 0, ∀ d ∈ g.range.erase 0,
      Integrable (fun x => (famCoeffPair p₀ p₁ p c z * famCoeffPair q₀ q₁ q d z) *
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

theorem differentiable_famExpPair (p₀ p₁ p : ℝ) : Differentiable ℂ (famExpPair p₀ p₁ p) := by
  unfold famExpPair
  fun_prop

theorem differentiable_famCoeffPair (p₀ p₁ p : ℝ) {c : ℂ} (hc : c ≠ 0) :
    Differentiable ℂ (fun z => famCoeffPair p₀ p₁ p c z) := by
  have hbase : (‖c‖ : ℂ) ≠ 0 := by simp [hc]
  have hcpow : Differentiable ℂ (fun z => (‖c‖ : ℂ) ^ famExpPair p₀ p₁ p z) :=
    (differentiable_famExpPair p₀ p₁ p).const_cpow (Or.inl hbase)
  have heq : (fun z => famCoeffPair p₀ p₁ p c z) =
      fun z => (c / (‖c‖ : ℂ)) * (‖c‖ : ℂ) ^ famExpPair p₀ p₁ p z := by
    funext z; unfold famCoeffPair; rw [if_neg hc]
  rw [heq]
  exact hcpow.const_mul _

theorem differentiable_pairSumPair (s g : MeasureTheory.SimpleFunc ℂ ℂ)
    (p₀ p₁ p q₀ q₁ q : ℝ) :
    Differentiable ℂ (fun z => ∑ c ∈ s.range.erase 0, ∑ d ∈ g.range.erase 0,
      famCoeffPair p₀ p₁ p c z * famCoeffPair q₀ q₁ q d z * pairConst s g c d) := by
  have heq : (fun z => ∑ c ∈ s.range.erase 0, ∑ d ∈ g.range.erase 0,
      famCoeffPair p₀ p₁ p c z * famCoeffPair q₀ q₁ q d z * pairConst s g c d) =
      ∑ c ∈ s.range.erase 0, (fun z => ∑ d ∈ g.range.erase 0,
        famCoeffPair p₀ p₁ p c z * famCoeffPair q₀ q₁ q d z * pairConst s g c d) := by
    funext z; rw [Finset.sum_apply]
  rw [heq]
  apply Differentiable.sum
  intro c hc
  have heq2 : (fun z => ∑ d ∈ g.range.erase 0,
      famCoeffPair p₀ p₁ p c z * famCoeffPair q₀ q₁ q d z * pairConst s g c d) =
      ∑ d ∈ g.range.erase 0,
        (fun z => famCoeffPair p₀ p₁ p c z * famCoeffPair q₀ q₁ q d z * pairConst s g c d) := by
    funext z; rw [Finset.sum_apply]
  rw [heq2]
  apply Differentiable.sum
  intro d hd
  have hcne : c ≠ 0 := (Finset.mem_erase.mp hc).1
  have hdne : d ≠ 0 := (Finset.mem_erase.mp hd).1
  exact ((differentiable_famCoeffPair p₀ p₁ p hcne).mul
    (differentiable_famCoeffPair q₀ q₁ q hdne)).mul_const _

/-- One boundary bound covers BOTH `Re z = 0` (`r := p₀`) and `Re z = 1` (`r := p₁`): unlike
`HilbertInterp`'s `boundary_bound_zero` (which used Cauchy–Schwarz + the exact `L²` isometry,
specific to `p₀ = 2`), here we ALWAYS use Hölder + a general `hgen`-shaped bound, since neither
`p₀` nor `p₁` is assumed to be `2`. -/
theorem boundary_bound_pair_generic {s g : MeasureTheory.SimpleFunc ℂ ℂ} {p₀ p₁ p q₀ q₁ q r r' M : ℝ}
    {z : ℂ} (hp1' : 1 < p) (hs : MemLp (s : ℂ → ℂ) (ENNReal.ofReal p) volume)
    (hq1' : 1 < q) (hg : MemLp (g : ℂ → ℂ) (ENNReal.ofReal q) volume)
    (hrr' : r.HolderConjugate r') (hM0 : 0 ≤ M)
    (hgen : ∀ ω : ℂ → ℂ, MemLp ω (ENNReal.ofReal r) volume →
      MemLp (hilbertH ω) (ENNReal.ofReal r) volume ∧
        eLpNorm (hilbertH ω) (ENNReal.ofReal r) volume ≤
          ENNReal.ofReal M * eLpNorm ω (ENNReal.ofReal r) volume)
    (hexps : (famExpPair p₀ p₁ p z).re * r = p) (hexpg : (famExpPair q₀ q₁ q z).re * r' = q) :
    ‖∫ x, hilbertH (famPair s p₀ p₁ p z) x * famPair g q₀ q₁ q z x ∂volume‖ ≤
      M * (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal ^ (p / r) *
        (eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume).toReal ^ (q / r') := by
  have hr1 : (1:ℝ) < r := hrr'.lt
  have hr0 : r ≠ 0 := by linarith
  have hr'pos : 1 < r' := hrr'.symm.lt
  have hr'0 : r' ≠ 0 := by linarith
  have hmem_fsp1 : MemLp (famPair s p₀ p₁ p z) (ENNReal.ofReal r) volume := memLp_famPair hp1' hs z
  have hmem_gp1' : MemLp (famPair g q₀ q₁ q z) (ENNReal.ofReal r') volume := memLp_famPair hq1' hg z
  obtain ⟨hmemH, hboundH⟩ := hgen (famPair s p₀ p₁ p z) hmem_fsp1
  have hnorm_s : eLpNorm (famPair s p₀ p₁ p z) (ENNReal.ofReal r) volume =
      (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume) ^ (p / r) :=
    eLpNorm_famPair_eq_rpow (s := s) (p₀ := p₀) (p₁ := p₁) (p := p) hp1' (z := z) (q := r)
      (by linarith : (1:ℝ) < r) hexps
  have hnorm_g : eLpNorm (famPair g q₀ q₁ q z) (ENNReal.ofReal r') volume =
      (eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume) ^ (q / r') :=
    eLpNorm_famPair_eq_rpow (s := g) (p₀ := q₀) (p₁ := q₁) (p := q) hq1' (z := z) (q := r')
      hr'pos hexpg
  calc ‖∫ x, hilbertH (famPair s p₀ p₁ p z) x * famPair g q₀ q₁ q z x ∂volume‖
      ≤ ∫ x, ‖hilbertH (famPair s p₀ p₁ p z) x * famPair g q₀ q₁ q z x‖ ∂volume :=
        norm_integral_le_integral_norm _
    _ = ∫ x, ‖hilbertH (famPair s p₀ p₁ p z) x‖ * ‖famPair g q₀ q₁ q z x‖ ∂volume := by
        simp_rw [norm_mul]
    _ ≤ (∫ x, ‖hilbertH (famPair s p₀ p₁ p z) x‖ ^ r ∂volume) ^ (1 / r) *
          (∫ x, ‖famPair g q₀ q₁ q z x‖ ^ r' ∂volume) ^ (1 / r') :=
        integral_mul_norm_le_Lp_mul_Lq hrr' hmemH hmem_gp1'
    _ = ((eLpNorm (hilbertH (famPair s p₀ p₁ p z)) (ENNReal.ofReal r) volume) ^ r).toReal
          ^ (1 / r) *
          ((eLpNorm (famPair g q₀ q₁ q z) (ENNReal.ofReal r') volume) ^ r').toReal ^ (1 / r') := by
        rw [integral_norm_rpow_eq_toReal_pow (by linarith : (1:ℝ) < r) hmemH.aestronglyMeasurable,
          integral_norm_rpow_eq_toReal_pow hr'pos hmem_gp1'.aestronglyMeasurable]
    _ ≤ ((ENNReal.ofReal M * eLpNorm (famPair s p₀ p₁ p z) (ENNReal.ofReal r) volume) ^ r).toReal
          ^ (1 / r) *
          ((eLpNorm (famPair g q₀ q₁ q z) (ENNReal.ofReal r') volume) ^ r').toReal ^ (1 / r') := by
        have hstep : ((eLpNorm (hilbertH (famPair s p₀ p₁ p z)) (ENNReal.ofReal r) volume) ^ r).toReal
            ≤ ((ENNReal.ofReal M * eLpNorm (famPair s p₀ p₁ p z) (ENNReal.ofReal r) volume) ^ r).toReal :=
          ENNReal.toReal_mono (by finiteness)
            (ENNReal.rpow_le_rpow hboundH (by linarith : (0:ℝ) ≤ r))
        have hr1r : (0:ℝ) ≤ 1 / r := by positivity
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ENNReal.toReal_nonneg hstep hr1r)
          (by positivity)
    _ = (M ^ r * (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal ^ p) ^ (1 / r) *
          ((eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume).toReal ^ q) ^ (1 / r') := by
        have hpow2 : ∀ (X : ℝ≥0∞) (a b : ℝ), ((X ^ a) ^ b).toReal = X.toReal ^ (a * b) :=
          fun X a b => by rw [← ENNReal.rpow_mul]; exact (ENNReal.toReal_rpow X (a * b)).symm
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : (0:ℝ) ≤ r), ENNReal.toReal_mul,
          hnorm_s, hnorm_g, hpow2, hpow2,
          div_mul_cancel₀ _ hr0, div_mul_cancel₀ _ hr'0,
          show ((ENNReal.ofReal M) ^ r).toReal = M ^ r from by
            rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hM0]]
    _ = M * (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal ^ (p / r) *
          (eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume).toReal ^ (q / r') := by
        rw [Real.mul_rpow (Real.rpow_nonneg hM0 r) (by positivity), ← Real.rpow_mul hM0,
          ← Real.rpow_mul ENNReal.toReal_nonneg, ← Real.rpow_mul ENNReal.toReal_nonneg]
        rw [mul_one_div r r, div_self hr0, Real.rpow_one, mul_one_div p r, mul_one_div q r',
          mul_assoc]

theorem norm_famCoeffPair_le_max {p₀ p₁ p : ℝ} (hp₀pos : 0 < p₀) (hp₁pos : 0 < p₁) (hp1' : 1 < p)
    {c z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) :
    ‖famCoeffPair p₀ p₁ p c z‖ ≤ max (‖c‖ ^ (p / p₀)) (‖c‖ ^ (p / p₁)) := by
  rw [norm_famCoeffPair]
  split_ifs with hc
  · positivity
  · rw [famExpPair_re]
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hp0 : 0 < p := by linarith
    rcases le_total (p/p₀) (p/p₁) with hcmp | hcmp
    · have hcmp' : p * p₁ ≤ p * p₀ := by
        have h := mul_le_mul_of_nonneg_right hcmp (mul_pos hp₀pos hp₁pos).le
        calc p * p₁ = p / p₀ * (p₀ * p₁) := by field_simp
          _ ≤ p / p₁ * (p₀ * p₁) := h
          _ = p * p₀ := by field_simp
      have hp1le0 : p₁ ≤ p₀ := le_of_mul_le_mul_left (by linarith) hp0
      have hsign : (0:ℝ) ≤ 1/p₁ - 1/p₀ := by
        rw [div_sub_div _ _ (ne_of_gt hp₁pos) (ne_of_gt hp₀pos)]
        apply div_nonneg _ (by positivity)
        linarith
      have hlow : p / p₀ ≤ p * ((1 - z.re) / p₀ + z.re / p₁) := by
        have key : p * ((1 - z.re) / p₀ + z.re / p₁) - p / p₀ = p * z.re * (1/p₁ - 1/p₀) := by
          field_simp; ring
        nlinarith [mul_nonneg (mul_nonneg hp0.le hz0) hsign]
      have hhigh : p * ((1 - z.re) / p₀ + z.re / p₁) ≤ p / p₁ := by
        have key : p / p₁ - p * ((1 - z.re) / p₀ + z.re / p₁) = p * (1 - z.re) * (1/p₁ - 1/p₀) := by
          field_simp; ring
        nlinarith [mul_nonneg (mul_nonneg hp0.le (by linarith : (0:ℝ) ≤ 1 - z.re)) hsign]
      by_cases h1 : ‖c‖ < 1
      · exact le_trans (Real.rpow_le_rpow_of_exponent_ge hcpos h1.le hlow) (le_max_left _ _)
      · push_neg at h1
        exact le_trans (Real.rpow_le_rpow_of_exponent_le h1 hhigh) (le_max_right _ _)
    · have hcmp' : p * p₀ ≤ p * p₁ := by
        have h := mul_le_mul_of_nonneg_right hcmp (mul_pos hp₀pos hp₁pos).le
        calc p * p₀ = p / p₁ * (p₀ * p₁) := by field_simp
          _ ≤ p / p₀ * (p₀ * p₁) := h
          _ = p * p₁ := by field_simp
      have hp1ge0 : p₀ ≤ p₁ := le_of_mul_le_mul_left (by linarith) hp0
      have hsign : (0:ℝ) ≤ 1/p₀ - 1/p₁ := by
        rw [div_sub_div _ _ (ne_of_gt hp₀pos) (ne_of_gt hp₁pos)]
        apply div_nonneg _ (by positivity)
        linarith
      have hlow : p / p₁ ≤ p * ((1 - z.re) / p₀ + z.re / p₁) := by
        have key : p * ((1 - z.re) / p₀ + z.re / p₁) - p / p₁ = p * (1 - z.re) * (1/p₀ - 1/p₁) := by
          field_simp; ring
        nlinarith [mul_nonneg (mul_nonneg hp0.le (by linarith : (0:ℝ) ≤ 1 - z.re)) hsign]
      have hhigh : p * ((1 - z.re) / p₀ + z.re / p₁) ≤ p / p₀ := by
        have key : p / p₀ - p * ((1 - z.re) / p₀ + z.re / p₁) = p * z.re * (1/p₀ - 1/p₁) := by
          field_simp; ring
        nlinarith [mul_nonneg (mul_nonneg hp0.le hz0) hsign]
      by_cases h1 : ‖c‖ < 1
      · exact le_trans (Real.rpow_le_rpow_of_exponent_ge hcpos h1.le hlow) (le_max_right _ _)
      · push_neg at h1
        exact le_trans (Real.rpow_le_rpow_of_exponent_le h1 hhigh) (le_max_left _ _)

open Complex.HadamardThreeLines in
theorem bddAbove_pairSumPair (s g : MeasureTheory.SimpleFunc ℂ ℂ) {p₀ p₁ p q₀ q₁ q : ℝ}
    (hp1' : 1 < p) (hq1' : 1 < q) (hp₀pos : 0 < p₀) (hp₁pos : 0 < p₁) (hq₀pos : 0 < q₀)
    (hq₁pos : 0 < q₁) :
    BddAbove ((norm ∘ (fun z => ∑ c ∈ s.range.erase 0, ∑ d ∈ g.range.erase 0,
      famCoeffPair p₀ p₁ p c z * famCoeffPair q₀ q₁ q d z * pairConst s g c d)) ''
      verticalClosedStrip 0 1) := by
  use ∑ c ∈ s.range.erase 0, ∑ d ∈ g.range.erase 0,
    (max (‖c‖ ^ (p/p₀)) (‖c‖ ^ (p/p₁))) * (max (‖d‖ ^ (q/q₀)) (‖d‖ ^ (q/q₁))) * ‖pairConst s g c d‖
  rintro _ ⟨z, hz, rfl⟩
  simp only [Function.comp_apply]
  have hz0 : 0 ≤ z.re := hz.1
  have hz1 : z.re ≤ 1 := hz.2
  calc ‖∑ c ∈ s.range.erase 0, ∑ d ∈ g.range.erase 0,
        famCoeffPair p₀ p₁ p c z * famCoeffPair q₀ q₁ q d z * pairConst s g c d‖
      ≤ ∑ c ∈ s.range.erase 0, ‖∑ d ∈ g.range.erase 0,
          famCoeffPair p₀ p₁ p c z * famCoeffPair q₀ q₁ q d z * pairConst s g c d‖ := norm_sum_le _ _
    _ ≤ ∑ c ∈ s.range.erase 0, ∑ d ∈ g.range.erase 0,
          ‖famCoeffPair p₀ p₁ p c z * famCoeffPair q₀ q₁ q d z * pairConst s g c d‖ := by
        apply Finset.sum_le_sum; intro c _; exact norm_sum_le _ _
    _ ≤ ∑ c ∈ s.range.erase 0, ∑ d ∈ g.range.erase 0,
          (max (‖c‖ ^ (p/p₀)) (‖c‖ ^ (p/p₁))) * (max (‖d‖ ^ (q/q₀)) (‖d‖ ^ (q/q₁))) *
            ‖pairConst s g c d‖ := by
        apply Finset.sum_le_sum; intro c _
        apply Finset.sum_le_sum; intro d _
        rw [norm_mul, norm_mul]
        exact mul_le_mul
          (mul_le_mul (norm_famCoeffPair_le_max hp₀pos hp₁pos hp1' hz0 hz1)
            (norm_famCoeffPair_le_max hq₀pos hq₁pos hq1' hz0 hz1) (norm_nonneg _) (by positivity))
          le_rfl (norm_nonneg _) (by positivity)

/-! ### CZ-wall-free `MemLp` interpolation, generalized to an arbitrary ordered pair -/

/-- Generalizes `rpow_le_rpow_two_add_rpow` (`HilbertInterp`) to an arbitrary ordered pair. -/
theorem rpow_le_rpow_pair {p₀ p₁ p : ℝ} (hp₀pos : 0 < p₀) (hp₀p : p₀ ≤ p) (hpp₁ : p ≤ p₁)
    {a : ℝ} (ha : 0 ≤ a) : a ^ p ≤ a ^ p₀ + a ^ p₁ := by
  have hppos : 0 < p := lt_of_lt_of_le hp₀pos hp₀p
  rcases eq_or_lt_of_le ha with rfl | hapos
  · simp only [Real.zero_rpow hppos.ne', Real.zero_rpow hp₀pos.ne']
    positivity
  by_cases h1 : a ≤ 1
  · have : a ^ p ≤ a ^ p₀ := Real.rpow_le_rpow_of_exponent_ge hapos h1 hp₀p
    linarith [Real.rpow_nonneg ha p₁]
  · push_neg at h1
    have : a ^ p ≤ a ^ p₁ := Real.rpow_le_rpow_of_exponent_le h1.le hpp₁
    linarith [Real.rpow_nonneg ha p₀]

/-- Generalizes `memLp_of_memLp_two_of_memLp` to an arbitrary ordered pair (`p₀ = 2` was never
essential to that proof, only `0 < p₀`). -/
theorem memLp_of_memLp_pair_ordered {p₀ p₁ p : ℝ} (hp₀pos : 0 < p₀) (hp₀p : p₀ ≤ p)
    (hpp₁ : p ≤ p₁) {Ω : ℂ → ℂ} (hΩ0 : MemLp Ω (ENNReal.ofReal p₀) volume)
    (hΩ1 : MemLp Ω (ENNReal.ofReal p₁) volume) :
    MemLp Ω (ENNReal.ofReal p) volume := by
  have hmeas := hΩ0.aestronglyMeasurable
  have hp0 : (0:ℝ) < p := lt_of_lt_of_le hp₀pos hp₀p
  have hp₁0 : (0:ℝ) < p₁ := lt_of_lt_of_le hp0 hpp₁
  rw [← integrable_norm_rpow_iff hmeas (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]
  have hI0 : Integrable (fun x => ‖Ω x‖ ^ p₀) volume := by
    have := hΩ0.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp₀pos).ne' ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal hp₀pos.le] at this
  have hI1 : Integrable (fun x => ‖Ω x‖ ^ p₁) volume := by
    have := hΩ1.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp₁0).ne' ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal hp₁0.le] at this
  apply Integrable.mono' (hI0.add hI1)
    ((Real.continuous_rpow_const hp0.le).comp_aestronglyMeasurable hmeas.norm)
  filter_upwards with x
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) p)]
  exact rpow_le_rpow_pair hp₀pos hp₀p hpp₁ (norm_nonneg _)

/-- Symmetric version, no assumption on which of `p₀, p₁` is larger. -/
theorem memLp_of_memLp_pair {p₀ p₁ p : ℝ} (hp₀pos : 0 < p₀) (hp₁pos : 0 < p₁)
    {Ω : ℂ → ℂ} (hΩ0 : MemLp Ω (ENNReal.ofReal p₀) volume) (hΩ1 : MemLp Ω (ENNReal.ofReal p₁) volume)
    (hp_lo : min p₀ p₁ ≤ p) (hp_hi : p ≤ max p₀ p₁) :
    MemLp Ω (ENNReal.ofReal p) volume := by
  rcases le_total p₀ p₁ with h | h
  · rw [min_eq_left h] at hp_lo
    rw [max_eq_right h] at hp_hi
    exact memLp_of_memLp_pair_ordered hp₀pos hp_lo hp_hi hΩ0 hΩ1
  · rw [min_eq_right h] at hp_lo
    rw [max_eq_left h] at hp_hi
    exact memLp_of_memLp_pair_ordered hp₁pos hp_lo hp_hi hΩ1 hΩ0

/-! ### The general fixed-pair assembly on simple functions -/

/-- `p` (linked to `θ, p₀, p₁` by `hp`) always lies between `p₀` and `p₁`, whichever is smaller. -/
theorem interpTheta_pair_between {p₀ p₁ p θ : ℝ} (hp₀pos : 0 < p₀) (hp₁pos : 0 < p₁)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hp : 1 / p = (1 - θ) / p₀ + θ / p₁) (hppos : 0 < p) :
    min p₀ p₁ ≤ p ∧ p ≤ max p₀ p₁ := by
  have key0 : (1:ℝ) / p₀ - 1 / p = θ * (1 / p₀ - 1 / p₁) := by rw [hp]; ring
  have key1 : (1:ℝ) / p - 1 / p₁ = (1 - θ) * (1 / p₀ - 1 / p₁) := by rw [hp]; ring
  rcases le_total p₀ p₁ with h | h
  · have hdiff : (0:ℝ) ≤ 1 / p₀ - 1 / p₁ := by
      have := one_div_le_one_div_of_le hp₀pos h; linarith
    have h1 : (0:ℝ) ≤ 1 / p₀ - 1 / p := by rw [key0]; exact mul_nonneg hθ0 hdiff
    have h2 : (0:ℝ) ≤ 1 / p - 1 / p₁ := by rw [key1]; exact mul_nonneg (by linarith) hdiff
    rw [min_eq_left h, max_eq_right h]
    exact ⟨le_of_one_div_le_one_div hppos (by linarith), le_of_one_div_le_one_div hp₁pos (by linarith)⟩
  · have hdiff : (1:ℝ) / p₀ - 1 / p₁ ≤ 0 := by
      have := one_div_le_one_div_of_le hp₁pos h; linarith
    have h1 : (1:ℝ) / p₀ - 1 / p ≤ 0 := by
      rw [key0]; exact mul_nonpos_of_nonneg_of_nonpos hθ0 hdiff
    have h2 : (1:ℝ) / p - 1 / p₁ ≤ 0 := by
      rw [key1]; exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hdiff
    rw [min_eq_right h, max_eq_left h]
    exact ⟨le_of_one_div_le_one_div hppos (by linarith), le_of_one_div_le_one_div hp₀pos (by linarith)⟩

open Complex.HadamardThreeLines in
/-- **RT1 core.** The general fixed-pair Riesz–Thorin bound on simple functions: given general
`L^{p₀}` and `L^{p₁}` bounds `h₀`, `h₁` and `θ, p` linked by `1/p = (1-θ)/p₀ + θ/p₁`, get the
weighted geometric-mean bound at `p`. `θ = 0, 1` are read off `h₀`/`h₁` directly; `0 < θ < 1` runs
the three-lines argument with BOTH boundaries using the Hölder + general-bound technique
(`boundary_bound_pair_generic`, instantiated at `(p₀, h₀)` and `(p₁, h₁)`). -/
theorem simpleFunc_hilbertH_bound_pair {p₀ p₁ M₀ M₁ : ℝ} (hp₀ : 1 < p₀) (hp₁ : 1 < p₁)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₀ : ∀ ω : ℂ → ℂ, MemLp ω (ENNReal.ofReal p₀) volume →
      MemLp (hilbertH ω) (ENNReal.ofReal p₀) volume ∧
        eLpNorm (hilbertH ω) (ENNReal.ofReal p₀) volume ≤
          ENNReal.ofReal M₀ * eLpNorm ω (ENNReal.ofReal p₀) volume)
    (h₁ : ∀ ω : ℂ → ℂ, MemLp ω (ENNReal.ofReal p₁) volume →
      MemLp (hilbertH ω) (ENNReal.ofReal p₁) volume ∧
        eLpNorm (hilbertH ω) (ENNReal.ofReal p₁) volume ≤
          ENNReal.ofReal M₁ * eLpNorm ω (ENNReal.ofReal p₁) volume)
    {θ p : ℝ} (hθ : θ ∈ Icc (0:ℝ) 1) (hp : 1 / p = (1 - θ) / p₀ + θ / p₁)
    (s : MeasureTheory.SimpleFunc ℂ ℂ) (hs : MemLp (s : ℂ → ℂ) (ENNReal.ofReal p) volume) :
    eLpNorm (hilbertH s) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume := by
  have hp₀0 : (0:ℝ) < p₀ := by linarith
  have hp₁0 : (0:ℝ) < p₁ := by linarith
  have hppos : 0 < p := by
    have hp1_nonneg : (0:ℝ) ≤ 1 / p := by
      rw [hp]
      exact add_nonneg (div_nonneg (by linarith [hθ.2]) hp₀0.le) (div_nonneg hθ.1 hp₁0.le)
    have hp1_ne : (1:ℝ) / p ≠ 0 := by
      rw [hp]
      intro he
      have h1 : (0:ℝ) ≤ (1 - θ) / p₀ := div_nonneg (by linarith [hθ.2]) hp₀0.le
      have h2 : (0:ℝ) ≤ θ / p₁ := div_nonneg hθ.1 hp₁0.le
      have e1 : (1 - θ) / p₀ = 0 := by linarith
      have e2 : θ / p₁ = 0 := by linarith
      rw [div_eq_zero_iff] at e1 e2
      rcases e1 with e1 | e1
      · rcases e2 with e2 | e2
        · linarith
        · exact hp₁0.ne' e2
      · exact hp₀0.ne' e1
    exact one_div_pos.mp (hp1_nonneg.lt_of_ne' hp1_ne)
  rcases hθ.1.eq_or_lt with hθ0 | hθ0pos
  · -- θ = 0: p = p₀, direct from h₀
    have hpeq : p = p₀ := by
      have h := hp
      rw [← hθ0] at h
      simp only [sub_zero, zero_div, add_zero] at h
      field_simp at h
      linarith
    rw [hpeq] at hs ⊢
    rw [← hθ0]
    simp only [sub_zero, Real.rpow_one, Real.rpow_zero, mul_one]
    exact (h₀ s hs).2
  · rcases hθ.2.eq_or_lt with hθ1 | hθ1pos
    · -- θ = 1: p = p₁, direct from h₁
      have hpeq : p = p₁ := by
        have h := hp
        rw [hθ1] at h
        simp only [sub_self, zero_div, zero_add, div_self (one_ne_zero)] at h
        field_simp at h
        linarith
      rw [hpeq] at hs ⊢
      rw [hθ1]
      simp only [sub_self, Real.rpow_zero, Real.rpow_one, one_mul]
      exact (h₁ s hs).2
    · -- 0 < θ < 1: the three-lines core
      have hp1' : (1:ℝ) < p := by
        obtain ⟨hlo, _⟩ := interpTheta_pair_between hp₀0 hp₁0 hθ.1 hθ.2 hp hppos
        rcases le_total p₀ p₁ with hle | hle
        · rw [min_eq_left hle] at hlo; linarith
        · rw [min_eq_right hle] at hlo; linarith
      have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp1'
      have hp0q0 : p₀.HolderConjugate (Real.conjExponent p₀) :=
        Real.HolderConjugate.conjExponent hp₀
      have hp1q1 : p₁.HolderConjugate (Real.conjExponent p₁) :=
        Real.HolderConjugate.conjExponent hp₁
      set q := Real.conjExponent p with hq_def
      set q₀ := Real.conjExponent p₀ with hq₀_def
      set q₁ := Real.conjExponent p₁ with hq₁_def
      have hq1' : (1:ℝ) < q := hpq.symm.lt
      have hq_rel : 1 / q = (1 - θ) / q₀ + θ / q₁ := by
        rw [hq_def, hq₀_def, hq₁_def]
        unfold Real.conjExponent
        have hp0ne1 : p₀ - 1 ≠ 0 := by intro h; apply hp₀0.ne'; linarith
        have hp1ne1 : p₁ - 1 ≠ 0 := by intro h; apply hp₁0.ne'; linarith
        have hpne1 : p - 1 ≠ 0 := by intro h; apply hppos.ne'; linarith
        have hp0ne : p₀ ≠ 0 := hp₀0.ne'
        have hp1ne : p₁ ≠ 0 := hp₁0.ne'
        have hpne : p ≠ 0 := hppos.ne'
        field_simp at hp ⊢
        nlinarith [hp]
      have hq₀pos : (0:ℝ) < q₀ := by linarith [hp0q0.symm.lt]
      have hq₁pos : (0:ℝ) < q₁ := by linarith [hp1q1.symm.lt]
      have hfin : ∀ y : ℂ, y ≠ 0 → volume (s ⁻¹' {y}) < ⊤ := fun y hy =>
        MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_memLp
          (ENNReal.ofReal_pos.mpr hppos).ne' ENNReal.ofReal_ne_top s hs y hy
      have hsp0 : MemLp (s : ℂ → ℂ) (ENNReal.ofReal p₀) volume :=
        MeasureTheory.SimpleFunc.memLp_of_finite_measure_preimage _ hfin
      have hsp1 : MemLp (s : ℂ → ℂ) (ENNReal.ofReal p₁) volume :=
        MeasureTheory.SimpleFunc.memLp_of_finite_measure_preimage _ hfin
      obtain ⟨hlo, hhi⟩ := interpTheta_pair_between hp₀0 hp₁0 hθ.1 hθ.2 hp hppos
      have hHmemLp : MemLp (hilbertH (s : ℂ → ℂ)) (ENNReal.ofReal p) volume :=
        memLp_of_memLp_pair hp₀0 hp₁0 (h₀ s hsp0).1 (h₁ s hsp1).1 hlo hhi
      have hraw : eLpNorm (hilbertH (s : ℂ → ℂ)) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (M₀ ^ (1-θ) * M₁ ^ θ *
            (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal) := by
        apply eLpNorm_le_of_forall_dual_simpleFunc_le hpq hHmemLp
          (mul_nonneg (by positivity) ENNReal.toReal_nonneg)
        intro g hgle1
        have hg : MemLp (g : ℂ → ℂ) (ENNReal.ofReal q) volume :=
          lt_of_le_of_lt hgle1 (by norm_num : (1:ℝ≥0∞) < ⊤)
        set F : ℂ → ℂ := fun z => ∑ c ∈ s.range.erase 0, ∑ d ∈ g.range.erase 0,
          famCoeffPair p₀ p₁ p c z * famCoeffPair q₀ q₁ q d z * pairConst s g c d with hF_def
        have hFeq : ∀ z, F z =
            ∫ x, hilbertH (famPair s p₀ p₁ p z) x * famPair g q₀ q₁ q z x ∂volume := fun z =>
          (integral_hilbertH_famPair_mul_famPair z hp1' hs hq1' hg).symm
        have hFθ : F (θ:ℂ) = ∫ x, hilbertH (s:ℂ→ℂ) x * g x ∂volume := by
          rw [hFeq, famPair_atTheta hppos.ne' hp,
            famPair_atTheta (show q ≠ 0 by linarith) hq_rel]
        have ha : ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ), ‖F z‖ ≤
            M₀ * (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal ^ (p / p₀) *
              (eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume).toReal ^ (q / q₀) := by
          intro z hz
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
          have hq₀pos : (0:ℝ) < q₀ := by linarith [hp0q0.symm.lt]
          have hq₁pos : (0:ℝ) < q₁ := by linarith [hp1q1.symm.lt]
          have hexps : (famExpPair p₀ p₁ p z).re * p₀ = p := by
            rw [famExpPair_re, hz]; field_simp [hp₀0.ne', hp₁0.ne']; ring
          have hexpg : (famExpPair q₀ q₁ q z).re * q₀ = q := by
            rw [famExpPair_re, hz]
            field_simp [hq₀pos.ne', hq₁pos.ne']; ring
          rw [hFeq]
          exact boundary_bound_pair_generic hp1' hs hq1' hg hp0q0 hM₀ h₀ hexps hexpg
        have hb : ∀ z ∈ Complex.re ⁻¹' ({1} : Set ℝ), ‖F z‖ ≤
            M₁ * (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal ^ (p / p₁) *
              (eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume).toReal ^ (q / q₁) := by
          intro z hz
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
          have hq₀pos : (0:ℝ) < q₀ := by linarith [hp0q0.symm.lt]
          have hq₁pos : (0:ℝ) < q₁ := by linarith [hp1q1.symm.lt]
          have hexps : (famExpPair p₀ p₁ p z).re * p₁ = p := by
            rw [famExpPair_re, hz]; field_simp [hp₀0.ne', hp₁0.ne']; ring
          have hexpg : (famExpPair q₀ q₁ q z).re * q₁ = q := by
            rw [famExpPair_re, hz]
            field_simp [hq₀pos.ne', hq₁pos.ne']; ring
          rw [hFeq]
          exact boundary_bound_pair_generic hp1' hs hq1' hg hp1q1 hM₁ h₁ hexps hexpg
        have hd : DiffContOnCl ℂ F (verticalStrip 0 1) :=
          (differentiable_pairSumPair s g p₀ p₁ p q₀ q₁ q).diffContOnCl
        have hB : BddAbove ((norm ∘ F) '' verticalClosedStrip 0 1) :=
          bddAbove_pairSumPair s g hp1' hq1' hp₀0 hp₁0
            (by linarith [hp0q0.symm.lt] : (0:ℝ) < q₀) (by linarith [hp1q1.symm.lt] : (0:ℝ) < q₁)
        have hzmem : (θ:ℂ) ∈ verticalClosedStrip 0 1 := by
          refine ⟨?_, ?_⟩ <;> simp only [Complex.ofReal_re]
          · exact hθ.1
          · exact hθ.2
        have hHad := norm_le_interp_of_mem_verticalClosedStrip₀₁' F hzmem hd hB ha hb
        rw [hFθ, Complex.ofReal_re] at hHad
        set A := (eLpNorm (s : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal with hA_def
        set B := (eLpNorm (g : ℂ → ℂ) (ENNReal.ofReal q) volume).toReal with hB_def
        have hBmem : 0 ≤ B ∧ B ≤ 1 := ⟨ENNReal.toReal_nonneg, by
          have : (eLpNorm (g:ℂ→ℂ) (ENNReal.ofReal q) volume).toReal ≤ (1:ℝ≥0∞).toReal :=
            ENNReal.toReal_mono (by norm_num) hgle1
          simpa using this⟩
        have hexp1 : p/p₀*(1-θ) + p/p₁*θ = 1 := by
          have hp0ne : p₀ ≠ 0 := hp₀0.ne'
          have hp1ne : p₁ ≠ 0 := hp₁0.ne'
          have hpne : p ≠ 0 := hppos.ne'
          field_simp at hp ⊢
          nlinarith [hp]
        have step1 : (M₀ * A ^ (p/p₀) * B ^ (q/q₀)) ^ (1-θ) ≤ M₀ ^ (1-θ) * A ^ (p/p₀*(1-θ)) := by
          rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hM₀ (by positivity),
            ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity), mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hM₀ (1-θ))
          calc A ^ (p/p₀*(1-θ)) * B ^ (q/q₀*(1-θ))
              ≤ A ^ (p/p₀*(1-θ)) * 1 := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact Real.rpow_le_one hBmem.1 hBmem.2 (by positivity)
            _ = A ^ (p/p₀*(1-θ)) := mul_one _
        have step2 : (M₁ * A ^ (p/p₁) * B ^ (q/q₁)) ^ θ ≤ M₁ ^ θ * A ^ (p/p₁*θ) := by
          rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hM₁ (by positivity),
            ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity), mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hM₁ θ)
          calc A ^ (p/p₁*θ) * B ^ (q/q₁*θ)
              ≤ A ^ (p/p₁*θ) * 1 := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact Real.rpow_le_one hBmem.1 hBmem.2 (by positivity)
            _ = A ^ (p/p₁*θ) := mul_one _
        have hA_nonneg : (0:ℝ) ≤ A := by rw [hA_def]; exact ENNReal.toReal_nonneg
        rcases hA_nonneg.eq_or_lt with hA0 | hApos
        · have hfactor0 : (M₁ * A ^ (p/p₁) * B ^ (q/q₁)) ^ θ = 0 := by
            rw [← hA0, Real.zero_rpow (show (p/p₁:ℝ) ≠ 0 by positivity), mul_zero, zero_mul,
              Real.zero_rpow (ne_of_gt hθ0pos)]
          calc ‖∫ x, hilbertH (s:ℂ→ℂ) x * g x ∂volume‖
              ≤ (M₀ * A ^ (p/p₀) * B ^ (q/q₀)) ^ (1-θ) * (M₁ * A ^ (p/p₁) * B ^ (q/q₁)) ^ θ := hHad
            _ = 0 := by rw [hfactor0, mul_zero]
            _ ≤ M₀ ^ (1-θ) * M₁ ^ θ * A := by rw [← hA0]; simp
        · calc ‖∫ x, hilbertH (s:ℂ→ℂ) x * g x ∂volume‖
              ≤ (M₀ * A ^ (p/p₀) * B ^ (q/q₀)) ^ (1-θ) * (M₁ * A ^ (p/p₁) * B ^ (q/q₁)) ^ θ := hHad
            _ ≤ M₀ ^ (1-θ) * A ^ (p/p₀*(1-θ)) * (M₁ ^ θ * A ^ (p/p₁*θ)) :=
                mul_le_mul step1 step2 (by positivity) (by positivity)
            _ = M₀ ^ (1-θ) * M₁ ^ θ * A ^ (p/p₀*(1-θ) + p/p₁*θ) := by
                rw [Real.rpow_add hApos]; ring
            _ = M₀ ^ (1-θ) * M₁ ^ θ * A := by rw [hexp1, Real.rpow_one]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hs.eLpNorm_ne_top] at hraw
      exact hraw

/-! ### Fatou/subsequence descent to `hilbertHSmooth` on `C₀^∞` -/

/-- **RT1, the frozen final statement.** Same Fatou/subsequence descent as
`hilbertH_boundedLp_interp` (canonical `approxOn` sequence, `L²` linearity/isometry transport to
an a.e.-convergent subsequence, Fatou plus a one-directional Minkowski bound, then
`hilbertH_eq_ae_smooth`), generalized to the `(p₀, h₀)`/`(p₁, h₁)` pair. -/
theorem hilbertH_boundedLp_interp_pair {p₀ p₁ M₀ M₁ : ℝ} (hp₀ : 1 < p₀) (hp₁ : 1 < p₁)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₀ : ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p₀) ≤
        ENNReal.ofReal M₀ * eLpNorm φ (ENNReal.ofReal p₀))
    (h₁ : ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p₁) ≤
        ENNReal.ofReal M₁ * eLpNorm φ (ENNReal.ofReal p₁))
    {θ : ℝ} (hθ : θ ∈ Icc (0:ℝ) 1) {p : ℝ} (hp : 1 / p = (1 - θ) / p₀ + θ / p₁) :
    ∀ φ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      eLpNorm (hilbertHSmooth φ) (ENNReal.ofReal p) ≤
        ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm φ (ENNReal.ofReal p) := by
  intro φ hφ hc
  have hp₀0 : (0:ℝ) < p₀ := by linarith
  have hp₁0 : (0:ℝ) < p₁ := by linarith
  have hppos : 0 < p := by
    have hp1_nonneg : (0:ℝ) ≤ 1 / p := by
      rw [hp]
      exact add_nonneg (div_nonneg (by linarith [hθ.2]) hp₀0.le) (div_nonneg hθ.1 hp₁0.le)
    have hp1_ne : (1:ℝ) / p ≠ 0 := by
      rw [hp]
      intro he
      have h1 : (0:ℝ) ≤ (1 - θ) / p₀ := div_nonneg (by linarith [hθ.2]) hp₀0.le
      have h2 : (0:ℝ) ≤ θ / p₁ := div_nonneg hθ.1 hp₁0.le
      have e1 : (1 - θ) / p₀ = 0 := by linarith
      have e2 : θ / p₁ = 0 := by linarith
      rw [div_eq_zero_iff] at e1 e2
      rcases e1 with e1 | e1
      · rcases e2 with e2 | e2
        · linarith
        · exact hp₁0.ne' e2
      · exact hp₀0.ne' e1
    exact one_div_pos.mp (hp1_nonneg.lt_of_ne' hp1_ne)
  have hp1' : (1:ℝ) < p := by
    obtain ⟨hlo, _⟩ := interpTheta_pair_between hp₀0 hp₁0 hθ.1 hθ.2 hp hppos
    rcases le_total p₀ p₁ with hle | hle
    · rw [min_eq_left hle] at hlo; linarith
    · rw [min_eq_right hle] at hlo; linarith
  have hgen₀ := hilbertH_memLp_of_smooth_bound hp₀ h₀
  have hgen₁ := hilbertH_memLp_of_smooth_bound hp₁ h₁
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
  have hbound : ∀ n, eLpNorm (hilbertH (s n)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (M₀ ^ (1-θ) * M₁ ^ θ) * eLpNorm (s n : ℂ → ℂ) (ENNReal.ofReal p) volume :=
    fun n => simpleFunc_hilbertH_bound_pair hp₀ hp₁ hM₀ hM₁ hgen₀ hgen₁ hθ hp (s n) (hsp n)
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
  have hrhs_tendsto : Tendsto (fun i =>
      ENNReal.ofReal (M₀ ^ (1-θ) * M₁ ^ θ) * eLpNorm φ (ENNReal.ofReal p) volume +
      ENNReal.ofReal (M₀ ^ (1-θ) * M₁ ^ θ) * eLpNorm ((s (ns i) : ℂ → ℂ) - φ) (ENNReal.ofReal p) volume)
      atTop (𝓝 (ENNReal.ofReal (M₀ ^ (1-θ) * M₁ ^ θ) * eLpNorm φ (ENNReal.ofReal p) volume)) := by
    have hmulconv := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (M₀ ^ (1-θ) * M₁ ^ θ)) hsub2
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using Tendsto.add tendsto_const_nhds hmulconv
  have hliminf_le : atTop.liminf
      (fun i => eLpNorm (hilbertH (s (ns i))) (ENNReal.ofReal p) volume) ≤
      ENNReal.ofReal (M₀ ^ (1-θ) * M₁ ^ θ) * eLpNorm φ (ENNReal.ofReal p) volume := by
    calc atTop.liminf (fun i => eLpNorm (hilbertH (s (ns i))) (ENNReal.ofReal p) volume)
        ≤ atTop.liminf (fun i =>
            ENNReal.ofReal (M₀ ^ (1-θ) * M₁ ^ θ) *
              eLpNorm (s (ns i) : ℂ → ℂ) (ENNReal.ofReal p) volume) :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall fun i => hbound (ns i))
      _ ≤ atTop.liminf (fun i =>
            ENNReal.ofReal (M₀ ^ (1-θ) * M₁ ^ θ) * eLpNorm φ (ENNReal.ofReal p) volume +
            ENNReal.ofReal (M₀ ^ (1-θ) * M₁ ^ θ) *
              eLpNorm ((s (ns i) : ℂ → ℂ) - φ) (ENNReal.ofReal p) volume) :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall fun i =>
            (mul_le_mul_right (hmink (ns i)) (ENNReal.ofReal (M₀ ^ (1-θ) * M₁ ^ θ))).trans_eq
              (mul_add (ENNReal.ofReal (M₀ ^ (1-θ) * M₁ ^ θ)) _ _))
      _ = ENNReal.ofReal (M₀ ^ (1-θ) * M₁ ^ θ) * eLpNorm φ (ENNReal.ofReal p) volume :=
          hrhs_tendsto.liminf_eq
  have hfinal : eLpNorm (hilbertH φ) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (M₀ ^ (1-θ) * M₁ ^ θ) * eLpNorm φ (ENNReal.ofReal p) volume :=
    hfatou.trans hliminf_le
  rwa [eLpNorm_congr_ae (hilbertH_eq_ae_smooth hφ hc)] at hfinal

end LiZhongQC
