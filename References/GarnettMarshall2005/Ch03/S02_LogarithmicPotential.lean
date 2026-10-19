import References.GarnettMarshall2005.Ch03.S01_CapacityGreenFunctions
import References.Common.Subharmonic

/-!
# Garnett–Marshall, Chapter III §2: The logarithmic potential

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. III §2 (pp. 77–79;
`full.md` P1:3486–3581).

Conventions as in §1. Measures are Borel measures on `ℂ`; the logarithmic potential is defined for positive measures
(finite, with compact support: the book's standing "finite, compactly supported" measure of P1:3488), with values in
`[−∞, +∞]` (leader ruling B2): the kernel `log (1/|ζ − z|)` is `+∞` on the diagonal, and the potential is the
integral of its positive part minus that of its negative part, so that no junk value `log 0` or non-integrable
integral arises. Sub- and superharmonic functions are the shared notions `References.IsSubharmonicOn`,
`References.IsSuperharmonicOn` (`EReal`-valued; the book uses them without a definition). The harmonic measure
`ω(∞, ·, Ω)` of this section is that of Chapter II (`harmonicMeasureFC`), carried to `ℂ`.

* Definition (the logarithmic potential `U_μ` of a finite, compactly supported measure, §2, P1:3488–3492) —
  `logPotential`
* Definition (subharmonic and superharmonic functions, which the book uses undefined from Lemma 2.1 on, §2) — exists:
  `References.IsSubharmonicOn`, `References.IsSuperharmonicOn` (the shared notions on open sets: EReal-valued, upper
  resp. lower semicontinuous, with the harmonic-majorant property on closed discs)
* Lemma 2.1 (§2) — `lemma3_2_1`
* Definition (the equilibrium distribution `μ_E = ω(∞, ·, ℂ* \ E)` of a set `E` whose complement is bounded by
  finitely many disjoint `C^{1+α}` Jordan curves, §2, P1:3506–3512 and P1:3530) — `equilibriumMeasureFC`
* Theorem 2.2 (§2; (2.1), (2.2), (2.3)) — `thm3_2_2_a`, `thm3_2_2_b`, `thm3_2_2_c`, `thm3_2_2_d`

Helpers (not book notions): `logKernel` (the kernel `log (1/|z − ζ|)` in `[−∞, +∞]`), `absLogKernel` (its absolute
value in `[0, ∞]`; absolute convergence in Theorem 2.2 and the finite-energy condition (3.1) of §3).

Not stated (inventory U−): the integral `U_μ` converges absolutely for area-almost every `z`, by Fubini's theorem
(P1:3494, not cited); the formula `dμ_E = −(1/2π) ∂g(ζ, ∞)/∂n_ζ ds = P_∞(ζ) ds` in the display of P1:3511 (not cited;
Corollary II.4.7 contains it); "later we shall see that `μ_E` is the unique probability measure on `E` with `U_μ`
constant on `E`" (P1:3530, a forward reference to §4); any weak-star cluster point of `{μ_{E_n}}` satisfies (2.1) and
(2.2) on `Ω` (P1:3580, superseded by Theorems 4.1 and 4.4, not cited). (2.4) and the other displays after Theorem 2.2
are steps of its proof.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt extInf)

/-- The kernel `log (1/|z − ζ|)` with values in `[−∞, +∞]` (helper, Ch. III §2, P1:3491): `−log |z − ζ|`, equal to
`+∞` on the diagonal `z = ζ` (no junk value `log 0`). -/
def logKernel (z ζ : ℂ) : EReal :=
  -ENNReal.log ‖z - ζ‖ₑ

/-- The kernel `|log (1/|z − ζ|)|` with values in `[0, ∞]` (helper, Ch. III §2–§3: the absolute convergence of
`U_{μ_E}` in Theorem 2.2 and the finite-energy condition (3.1)): the sum of the positive and the negative part of
`logKernel`, equal to `+∞` on the diagonal. -/
def absLogKernel (z ζ : ℂ) : ℝ≥0∞ :=
  (logKernel z ζ).toENNReal + (-logKernel z ζ).toENNReal

/-- **Definition** (the logarithmic potential, Ch. III §2, P1:3488–3492). For a finite, compactly supported Borel
measure `μ`, the logarithmic potential of `μ` is `U_μ(z) = ∫ log (1/|ζ − z|) dμ(ζ)`.
Modelling (leader ruling B2): for positive measures `μ` (every later use is positive: Lemma 2.1, `μ_E`, the measures
of `P(E)`; signed potentials `U_ν` appear only inside proofs, e.g. `I(ν) = ∫ U_ν dν`); values in `[−∞, +∞]`: the
lower integral of the positive part of the kernel minus that of its negative part. For a finite measure with compact
support the negative part is finite, so `U_μ(z) ∈ (−∞, +∞]` is the book's integral, `+∞` where the positive part
diverges. Junk: `⊥` (the difference `∞ − ∞`) only for measures that are not finite with compact support; every
statement assumes both. -/
def logPotential (μ : Measure ℂ) (z : ℂ) : EReal :=
  ((∫⁻ ζ, (logKernel ζ z).toENNReal ∂μ : ℝ≥0∞) : EReal) - ((∫⁻ ζ, (-logKernel ζ z).toENNReal ∂μ : ℝ≥0∞) : EReal)

/-- Helper (Ch. III §2). The clamp `min (max r e⁻ⁿ) R'` (`R' ≥ 1`) is positive, and `−log` of it is bounded by `n + R'`. -/
theorem gm32_clamp_bound (r : ℝ) {R' : ℝ} (hR' : 1 ≤ R') (n : ℕ) :
    0 < min (max r (Real.exp (-(n : ℝ)))) R' ∧ |-Real.log (min (max r (Real.exp (-(n : ℝ)))) R')| ≤ n + R' := by
  have hε1 : Real.exp (-(n : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    simp
  have hεpos : 0 < Real.exp (-(n : ℝ)) := Real.exp_pos _
  have hc : Real.exp (-(n : ℝ)) ≤ min (max r (Real.exp (-(n : ℝ)))) R' :=
    le_min (le_max_right _ _) (hε1.trans hR')
  have hpos : 0 < min (max r (Real.exp (-(n : ℝ)))) R' := lt_of_lt_of_le hεpos hc
  refine ⟨hpos, ?_⟩
  have h1 : -(n : ℝ) ≤ Real.log (min (max r (Real.exp (-(n : ℝ)))) R') := by
    have := Real.log_le_log hεpos hc
    rwa [Real.log_exp] at this
  have h2 : Real.log (min (max r (Real.exp (-(n : ℝ)))) R') ≤ R' := by
    refine (Real.log_le_log hpos (min_le_right _ _)).trans ?_
    have := Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos hR')
    linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [abs_le]
  constructor <;> linarith

/-- Helper (Ch. III §2, truncation of the logarithmic kernel). For a finite measure `m` and a measurable `w : X → ℂ`
with `‖w‖ ≤ R` almost everywhere, the bounded truncations `gₙ = −log (clamp ‖w‖ to [e⁻ⁿ, max R 1])` have integrals below
`∫ log⁺ (1/‖w‖) dm − ∫ log⁻ (1/‖w‖) dm` (lower integrals, in `EReal`), and that difference is their supremum. -/
theorem gm32_trunc_generic {X : Type*} [MeasurableSpace X] {m : Measure X} [IsFiniteMeasure m] {w : X → ℂ}
    (hw : Measurable w) {R : ℝ} (hR : ∀ᵐ x ∂m, ‖w x‖ ≤ R) :
    (∀ n : ℕ, ((∫ x, -Real.log (min (max ‖w x‖ (Real.exp (-(n : ℝ)))) (max R 1)) ∂m : ℝ) : EReal) ≤
        ((∫⁻ x, (-ENNReal.log ‖w x‖ₑ).toENNReal ∂m : ℝ≥0∞) : EReal) -
          ((∫⁻ x, (-(-ENNReal.log ‖w x‖ₑ)).toENNReal ∂m : ℝ≥0∞) : EReal)) ∧
      (((∫⁻ x, (-ENNReal.log ‖w x‖ₑ).toENNReal ∂m : ℝ≥0∞) : EReal) -
          ((∫⁻ x, (-(-ENNReal.log ‖w x‖ₑ)).toENNReal ∂m : ℝ≥0∞) : EReal) ≤
        ⨆ n : ℕ, ((∫ x, -Real.log (min (max ‖w x‖ (Real.exp (-(n : ℝ)))) (max R 1)) ∂m : ℝ) : EReal)) ∧
      ∫⁻ x, (-(-ENNReal.log ‖w x‖ₑ)).toENNReal ∂m ≠ ⊤ := by
  set R' : ℝ := max R 1 with hR'
  have hR'1 : 1 ≤ R' := le_max_right _ _
  have hRR' : R ≤ R' := le_max_left _ _
  set g : ℕ → X → ℝ := fun n x => -Real.log (min (max ‖w x‖ (Real.exp (-(n : ℝ)))) R') with hg
  have hεpos : ∀ n : ℕ, 0 < Real.exp (-(n : ℝ)) := fun n => Real.exp_pos _
  have hε1 : ∀ n : ℕ, Real.exp (-(n : ℝ)) ≤ 1 := fun n => by
    rw [Real.exp_le_one_iff]
    simp
  have hmeas : ∀ n, Measurable (g n) := fun n =>
    (Real.measurable_log.comp ((hw.norm.max measurable_const).min measurable_const)).neg
  have hclamp_pos : ∀ (n : ℕ) (x : X), Real.exp (-(n : ℝ)) ≤ min (max ‖w x‖ (Real.exp (-(n : ℝ)))) R' := fun n x =>
    le_min (le_max_right _ _) ((hε1 n).trans hR'1)
  have hbound : ∀ n x, |g n x| ≤ (n : ℝ) + R' := fun n x => by
    have h1 : -(n : ℝ) ≤ Real.log (min (max ‖w x‖ (Real.exp (-(n : ℝ)))) R') := by
      have := Real.log_le_log (hεpos n) (hclamp_pos n x)
      rwa [Real.log_exp] at this
    have h2 : Real.log (min (max ‖w x‖ (Real.exp (-(n : ℝ)))) R') ≤ R' := by
      refine (Real.log_le_log (lt_of_lt_of_le (hεpos n) (hclamp_pos n x)) (min_le_right _ _)).trans ?_
      have := Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos hR'1)
      linarith
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hR0 : 0 ≤ R' := by linarith
    simp only [hg]
    rw [abs_le]
    constructor <;> linarith
  have hint : ∀ n, Integrable (g n) m := fun n =>
    Integrable.of_bound (hmeas n).aestronglyMeasurable ((n : ℝ) + R')
      (Filter.Eventually.of_forall fun x => by simpa using hbound n x)
  -- pointwise facts on the set `‖w x‖ ≤ R`
  have key : ∀ᵐ x ∂m, (∀ n, ENNReal.ofReal (-(g n x)) = (-(-ENNReal.log ‖w x‖ₑ)).toENNReal) ∧
      (∀ n, ENNReal.ofReal (g n x) ≤ (-ENNReal.log ‖w x‖ₑ).toENNReal) ∧
      ⨆ n, ENNReal.ofReal (g n x) = (-ENNReal.log ‖w x‖ₑ).toENNReal := by
    filter_upwards [hR] with x hx
    have hxR' : ‖w x‖ ≤ R' := hx.trans hRR'
    have hr0 : 0 ≤ ‖w x‖ := norm_nonneg _
    have hePos : ∀ n : ℕ, ‖w x‖ < Real.exp (-(n : ℝ)) → g n x = n := fun n h => by
      simp only [hg]
      rw [max_eq_right h.le, min_eq_left ((hε1 n).trans hR'1), Real.log_exp]
      ring
    have hegt : ∀ n : ℕ, Real.exp (-(n : ℝ)) ≤ ‖w x‖ → g n x = -Real.log ‖w x‖ := fun n h => by
      simp only [hg]
      rw [max_eq_left h, min_eq_left hxR']
    rcases hr0.eq_or_lt with h0 | hpos
    · have hw0 : ‖w x‖ₑ = 0 := by
        rw [← ofReal_norm, ← h0]
        simp
      have hP : (-ENNReal.log ‖w x‖ₑ).toENNReal = ⊤ := by simp [hw0]
      have hN : (-(-ENNReal.log ‖w x‖ₑ)).toENNReal = 0 := by simp [hw0]
      have hgn : ∀ n : ℕ, g n x = n := fun n => hePos n (by rw [← h0]; exact hεpos n)
      refine ⟨fun n => ?_, fun n => ?_, ?_⟩
      · rw [hN, hgn]
        simp
      · rw [hP]
        exact le_top
      · rw [hP]
        simp only [hgn, ENNReal.ofReal_natCast]
        exact ENNReal.iSup_natCast
    · have hw : ‖w x‖ₑ = ENNReal.ofReal ‖w x‖ := (ofReal_norm _).symm
      have hlog : ENNReal.log ‖w x‖ₑ = ((Real.log ‖w x‖ : ℝ) : EReal) := by
        rw [hw]
        exact ENNReal.log_ofReal_of_pos hpos
      have hP : (-ENNReal.log ‖w x‖ₑ).toENNReal = ENNReal.ofReal (-Real.log ‖w x‖) := by
        rw [hlog, ← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
      have hN : (-(-ENNReal.log ‖w x‖ₑ)).toENNReal = ENNReal.ofReal (Real.log ‖w x‖) := by
        rw [hlog, neg_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
      have hlt : ∀ n : ℕ, ‖w x‖ < Real.exp (-(n : ℝ)) → Real.log ‖w x‖ < -(n : ℝ) := fun n h => by
        have := Real.log_lt_log hpos h
        rwa [Real.log_exp] at this
      refine ⟨fun n => ?_, fun n => ?_, ?_⟩
      · rw [hN]
        rcases le_or_gt (Real.exp (-(n : ℝ))) ‖w x‖ with h | h
        · rw [hegt n h, neg_neg]
        · rw [hePos n h]
          have h1 : -(n : ℝ) ≤ 0 := by simp
          rw [ENNReal.ofReal_of_nonpos (by simp), ENNReal.ofReal_of_nonpos]
          exact ((hlt n h).trans_le h1).le
      · rw [hP]
        rcases le_or_gt (Real.exp (-(n : ℝ))) ‖w x‖ with h | h
        · rw [hegt n h]
        · rw [hePos n h]
          exact ENNReal.ofReal_le_ofReal (by linarith [hlt n h])
      · refine le_antisymm (iSup_le fun n => ?_) ?_
        · rcases le_or_gt (Real.exp (-(n : ℝ))) ‖w x‖ with h | h
          · rw [hegt n h, hP]
          · rw [hP, hePos n h]
            exact ENNReal.ofReal_le_ofReal (by linarith [hlt n h])
        · obtain ⟨n, hn⟩ := exists_nat_ge (-Real.log ‖w x‖)
          have hle : Real.exp (-(n : ℝ)) ≤ ‖w x‖ := by
            calc Real.exp (-(n : ℝ)) ≤ Real.exp (Real.log ‖w x‖) :=
                  Real.exp_le_exp.2 (by linarith)
              _ = ‖w x‖ := Real.exp_log hpos
          rw [hP, ← hegt n hle]
          exact le_iSup (fun n => ENNReal.ofReal (g n x)) n
  set Pf : X → ℝ≥0∞ := fun x => (-ENNReal.log ‖w x‖ₑ).toENNReal with hPf
  set Nf : X → ℝ≥0∞ := fun x => (-(-ENNReal.log ‖w x‖ₑ)).toENNReal with hNf
  set A : ℕ → ℝ≥0∞ := fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂m with hA
  set B : ℝ≥0∞ := ∫⁻ x, Nf x ∂m with hB
  set p : ℝ≥0∞ := ∫⁻ x, Pf x ∂m with hp
  have hBn : ∀ n, ∫⁻ x, ENNReal.ofReal (-(g n x)) ∂m = B := fun n =>
    lintegral_congr_ae (by filter_upwards [key] with x hx using hx.1 n)
  have hAle : ∀ n, A n ≤ p := fun n =>
    lintegral_mono_ae (by filter_upwards [key] with x hx using hx.2.1 n)
  have hmono : Monotone fun n x => ENNReal.ofReal (g n x) := by
    refine monotone_nat_of_le_succ fun n x => ?_
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [hg]
    rw [neg_le_neg_iff]
    refine Real.log_le_log (lt_of_lt_of_le (hεpos (n + 1)) (hclamp_pos (n + 1) x)) ?_
    refine min_le_min (max_le_max le_rfl (Real.exp_le_exp.2 ?_)) le_rfl
    push_cast
    linarith
  have hpA : p = ⨆ n, A n := by
    have h := lintegral_iSup (μ := m) (f := fun n x => ENNReal.ofReal (g n x))
      (fun n => ENNReal.measurable_ofReal.comp (hmeas n)) hmono
    calc p = ∫⁻ x, ⨆ n, ENNReal.ofReal (g n x) ∂m :=
          lintegral_congr_ae (by filter_upwards [key] with x hx using hx.2.2.symm)
      _ = ⨆ n, A n := h
  have hAmono : Monotone A := fun a b hab => lintegral_mono fun x => hmono hab x
  have hAfin : ∀ n, A n ≠ ⊤ := fun n => by
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun x =>
      ENNReal.ofReal_le_ofReal (le_trans (le_abs_self _) (hbound n x)) :
        A n ≤ ∫⁻ _x, ENNReal.ofReal ((n : ℝ) + R') ∂m) ?_)
    rw [lintegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hBfin : B ≠ ⊤ := by
    rw [← hBn 0]
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun x =>
      ENNReal.ofReal_le_ofReal (le_trans (neg_le_abs _) (hbound 0 x)) :
        ∫⁻ x, ENNReal.ofReal (-(g 0 x)) ∂m ≤ ∫⁻ _x, ENNReal.ofReal (((0 : ℕ) : ℝ) + R') ∂m) ?_)
    rw [lintegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hI : ∀ n, ((∫ x, g n x ∂m : ℝ) : EReal) = (A n : EReal) - (B : EReal) := fun n => by
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint n), EReal.coe_sub,
      EReal.coe_ennreal_toReal (hAfin n), hBn n, EReal.coe_ennreal_toReal hBfin]
  refine ⟨fun n => ?_, ?_, hBfin⟩
  · rw [hI n]
    exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.2 (hAle n)) le_rfl
  · show _ ≤ ⨆ n : ℕ, ((∫ x, g n x ∂m : ℝ) : EReal)
    simp only [hI]
    have hT : Tendsto (fun n => (A n : EReal)) atTop (𝓝 (p : EReal)) := by
      have : Tendsto A atTop (𝓝 p) := by
        rw [hpA]
        exact tendsto_atTop_iSup hAmono
      exact (continuous_coe_ennreal_ereal.tendsto _).comp this
    have hBr : (B : EReal) = ((B.toReal : ℝ) : EReal) := (EReal.coe_ennreal_toReal hBfin).symm
    have hT2 : Tendsto (fun n => (A n : EReal) - B) atTop (𝓝 ((p : EReal) - B)) := by
      simp_rw [sub_eq_add_neg, hBr, ← EReal.coe_neg]
      exact (EReal.continuousAt_add (p := ((p : EReal), ((-B.toReal : ℝ) : EReal)))
        (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))).tendsto.comp
        (hT.prodMk_nhds tendsto_const_nhds)
    exact le_of_tendsto' hT2 fun n => le_iSup (fun n => (A n : EReal) - B) n

/-- Helper (Ch. III §2, Lemma 2.1). The truncated potential `z ↦ ∫ −log (clamp ‖ζ − z‖) dμ` is continuous. -/
theorem gm32_ut_continuous (μ : Measure ℂ) [IsFiniteMeasure μ] {R0 : ℝ} (hR0 : 1 ≤ R0) (n : ℕ) :
    Continuous fun z : ℂ => ∫ ζ, -Real.log (min (max ‖ζ - z‖ (Real.exp (-(n : ℝ)))) R0) ∂μ := by
  have hcont : Continuous fun p : ℂ × ℂ =>
      -Real.log (min (max ‖p.2 - p.1‖ (Real.exp (-(n : ℝ)))) R0) :=
    Continuous.neg (Continuous.log
      ((((continuous_snd.sub continuous_fst).norm).max continuous_const).min continuous_const)
      fun p => (gm32_clamp_bound ‖p.2 - p.1‖ hR0 n).1.ne')
  refine continuous_of_dominated (bound := fun _ => (n : ℝ) + R0) (fun z => ?_) (fun z => ?_)
    (integrable_const _) ?_
  · exact (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ζ => by
      rw [Real.norm_eq_abs]
      exact (gm32_clamp_bound ‖ζ - z‖ hR0 n).2
  · exact Filter.Eventually.of_forall fun ζ => hcont.comp (continuous_id.prodMk continuous_const)

/-- Helper (Ch. III §2, Lemma 2.1). At a point `z` with `‖ζ − z‖ ≤ R0` for `μ`-almost every `ζ`, the truncated potentials
lie below `U_μ(z)` and have it as their supremum. -/
theorem gm32_ut_eq (μ : Measure ℂ) [IsFiniteMeasure μ] {R0 : ℝ} (hR0 : 1 ≤ R0) {z : ℂ}
    (hz : ∀ᵐ ζ ∂μ, ‖ζ - z‖ ≤ R0) :
    (∀ n : ℕ, ((∫ ζ, -Real.log (min (max ‖ζ - z‖ (Real.exp (-(n : ℝ)))) R0) ∂μ : ℝ) : EReal) ≤
        logPotential μ z) ∧
      logPotential μ z ≤ ⨆ n : ℕ,
        ((∫ ζ, -Real.log (min (max ‖ζ - z‖ (Real.exp (-(n : ℝ)))) R0) ∂μ : ℝ) : EReal) := by
  have h := gm32_trunc_generic (m := μ) (w := fun ζ : ℂ => ζ - z) (measurable_id.sub measurable_const) hz
  rw [max_eq_left hR0] at h
  exact ⟨h.1, h.2.1⟩

/-- Helper (Ch. III §2). The parameters at which a circle of positive radius passes through a given point form a
Lebesgue-null set. -/
theorem gm32_circleMap_eq_null (c a : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    MeasureTheory.volume {θ : ℝ | circleMap c ρ θ = a} = 0 := by
  by_cases hne : {θ : ℝ | circleMap c ρ θ = a}.Nonempty
  · obtain ⟨θ0, hθ0⟩ := hne
    refine Set.Countable.measure_zero (Set.Countable.mono ?_
      (Set.countable_range fun k : ℤ => θ0 + 2 * π * k)) _
    intro θ hθ
    have h : circleMap c ρ θ = circleMap c ρ θ0 := (show circleMap c ρ θ = a from hθ).trans
      (show circleMap c ρ θ0 = a from hθ0).symm
    obtain ⟨n, hn⟩ := (circleMap_eq_circleMap_iff c hρ.ne').1 h
    rw [show (n : ℂ) * (2 * π * I) = ((n : ℂ) * 2 * π) * I by ring, ← add_mul, mul_eq_mul_right_iff] at hn
    rcases hn with hn | hn
    · norm_cast at hn
      exact ⟨n, by rw [hn]; push_cast; ring⟩
    · exact absurd hn I_ne_zero
  · rw [Set.not_nonempty_iff_eq_empty.1 hne]
    simp

/-- Helper (Ch. III §2, Lemma 2.1). The clamped logarithmic kernel `−log (clamp ‖x − a‖)` has the super-mean-value
property on a circle all of whose points (and whose centre) are within `R0` of `a`. -/
theorem gm32_kernel_supermean (a c : ℂ) {ρ ε R0 : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hεR : ε ≤ R0)
    (hR : ∀ x ∈ sphere c ρ, ‖x - a‖ ≤ R0) (hc : ‖c - a‖ ≤ R0) :
    Real.circleAverage (fun x => -Real.log (min (max ‖x - a‖ ε) R0)) c ρ ≤
      -Real.log (min (max ‖c - a‖ ε) R0) := by
  set k : ℂ → ℝ := fun x => -Real.log (max ‖x - a‖ ε) with hk
  have hkc : Continuous k := (Continuous.log
    (((continuous_id.sub continuous_const).norm).max continuous_const)
    fun x => (lt_of_lt_of_le hε (le_max_right _ _)).ne').neg
  have hkI : CircleIntegrable k c ρ := hkc.continuousOn.circleIntegrable'
  have hmin : ∀ x, ‖x - a‖ ≤ R0 → min (max ‖x - a‖ ε) R0 = max ‖x - a‖ ε := fun x hx =>
    min_eq_left (max_le hx hεR)
  have hA : Real.circleAverage (fun x => -Real.log (min (max ‖x - a‖ ε) R0)) c ρ =
      Real.circleAverage k c ρ := by
    simp only [Real.circleAverage_def]
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hk]
    rw [hmin _ (hR _ (circleMap_mem_sphere c hρ.le θ))]
  rw [hA, hmin c hc]
  have hi : Real.circleAverage k c ρ ≤ -Real.log ε :=
    Real.circleAverage_mono_on_of_le_circle hkI (fun x _ => by
      simp only [hk]
      exact neg_le_neg (Real.log_le_log hε (le_max_right _ _)))
  by_cases hd : ε ≤ ‖c - a‖
  · rw [max_eq_left hd]
    have hdpos : 0 < ‖c - a‖ := lt_of_lt_of_le hε hd
    have hf := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := a) (c := c) hρ.ne'
    have hfI : CircleIntegrable (fun x => -Real.log ‖x - a‖) c ρ :=
      (circleIntegrable_log_norm_sub_const (a := a) (c := c) ρ).neg
    have hle : Real.circleAverage k c ρ ≤ Real.circleAverage (fun x => -Real.log ‖x - a‖) c ρ := by
      rw [Real.circleAverage_def, Real.circleAverage_def]
      refine smul_le_smul_of_nonneg_left ?_ (by positivity)
      refine intervalIntegral.integral_mono_ae (by positivity) hkI hfI ?_
      filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1 (gm32_circleMap_eq_null c a hρ)]
        with θ hθ
      have hne : circleMap c ρ θ - a ≠ 0 := fun h => hθ (sub_eq_zero.1 h)
      have hpos : 0 < ‖circleMap c ρ θ - a‖ := norm_pos_iff.2 hne
      simp only [hk]
      exact neg_le_neg (Real.log_le_log hpos (le_max_left _ _))
    have hneg : Real.circleAverage (fun x => -Real.log ‖x - a‖) c ρ =
        -Real.circleAverage (fun x => Real.log ‖x - a‖) c ρ := by
      simp only [Real.circleAverage_def, intervalIntegral.integral_neg, smul_neg]
    rw [hneg, hf] at hle
    refine hle.trans (neg_le_neg ?_)
    have h1 : Real.log (ρ⁻¹ * ‖c - a‖) ≤ Real.posLog (ρ⁻¹ * ‖c - a‖) := le_max_right _ _
    rw [Real.log_mul (inv_pos.2 hρ).ne' hdpos.ne', Real.log_inv] at h1
    linarith
  · have hd' : ‖c - a‖ < ε := not_le.1 hd
    rw [max_eq_right hd'.le]
    exact hi

/-- Helper (Ch. III §2, Lemma 2.1). The truncated potential has the super-mean-value property on a circle whose closed
disc is within `R0` of `μ`-almost every point (Fubini plus `gm32_kernel_supermean`). -/
theorem gm32_ut_supermean (μ : Measure ℂ) [IsFiniteMeasure μ] {R0 : ℝ} (hR0 : 1 ≤ R0) (n : ℕ) (c : ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) (hsupp : ∀ᵐ ζ ∂μ, ∀ x ∈ closedBall c ρ, ‖ζ - x‖ ≤ R0) :
    Real.circleAverage (fun w : ℂ => ∫ ζ, -Real.log (min (max ‖ζ - w‖ (Real.exp (-(n : ℝ)))) R0) ∂μ) c ρ ≤
      ∫ ζ, -Real.log (min (max ‖ζ - c‖ (Real.exp (-(n : ℝ)))) R0) ∂μ := by
  set F : ℂ → ℂ → ℝ := fun w ζ => -Real.log (min (max ‖ζ - w‖ (Real.exp (-(n : ℝ)))) R0) with hF
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hFc : Continuous fun p : ℂ × ℂ => F p.1 p.2 :=
    Continuous.neg (Continuous.log
      ((((continuous_snd.sub continuous_fst).norm).max continuous_const).min continuous_const)
      fun p => (gm32_clamp_bound ‖p.2 - p.1‖ hR0 n).1.ne')
  have hFb : ∀ w ζ, |F w ζ| ≤ (n : ℝ) + R0 := fun w ζ => (gm32_clamp_bound ‖ζ - w‖ hR0 n).2
  have hint : Integrable (fun q : ℝ × ℂ => F (circleMap c ρ q.1) q.2)
      ((MeasureTheory.volume.restrict (Set.Ioc 0 (2 * π))).prod μ) := by
    refine Integrable.of_bound ?_ ((n : ℝ) + R0) (Filter.Eventually.of_forall fun q => ?_)
    · exact (hFc.comp ((continuous_circleMap c ρ).comp continuous_fst |>.prodMk continuous_snd)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact hFb _ _
  have hswap : ∫ θ : ℝ in Set.Ioc 0 (2 * π), (∫ ζ, F (circleMap c ρ θ) ζ ∂μ) =
      ∫ ζ, (∫ θ : ℝ in Set.Ioc 0 (2 * π), F (circleMap c ρ θ) ζ) ∂μ :=
    MeasureTheory.integral_integral_swap (f := fun θ ζ => F (circleMap c ρ θ) ζ) hint
  have hrw : Real.circleAverage (fun w : ℂ => ∫ ζ, F w ζ ∂μ) c ρ =
      ∫ ζ, Real.circleAverage (fun w => F w ζ) c ρ ∂μ := by
    simp_rw [Real.circleAverage_def, intervalIntegral.integral_of_le h2π]
    rw [hswap]
    exact (MeasureTheory.integral_smul _ _).symm
  have hI1 : Integrable (fun ζ => Real.circleAverage (fun w => F w ζ) c ρ) μ := by
    have := (hint.integral_prod_right).smul ((2 * π)⁻¹)
    refine this.congr (Filter.Eventually.of_forall fun ζ => ?_)
    simp_rw [Real.circleAverage_def, intervalIntegral.integral_of_le h2π]
    rfl
  have hI2 : Integrable (fun ζ => F c ζ) μ :=
    Integrable.of_bound (hFc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      ((n : ℝ) + R0) (Filter.Eventually.of_forall fun ζ => by
        rw [Real.norm_eq_abs]
        exact hFb _ _)
  show Real.circleAverage (fun w : ℂ => ∫ ζ, F w ζ ∂μ) c ρ ≤ ∫ ζ, F c ζ ∂μ
  rw [hrw]
  refine MeasureTheory.integral_mono_ae hI1 hI2 ?_
  filter_upwards [hsupp] with ζ hζ
  have hε : 0 < Real.exp (-(n : ℝ)) := Real.exp_pos _
  have hεR : Real.exp (-(n : ℝ)) ≤ R0 := by
    refine le_trans ?_ hR0
    rw [Real.exp_le_one_iff]
    simp
  have key := gm32_kernel_supermean ζ c hρ hε hεR
    (fun x hx => by rw [norm_sub_rev]; exact hζ x (sphere_subset_closedBall hx))
    (by rw [norm_sub_rev]; exact hζ c (mem_closedBall_self hρ.le))
  have e : (fun w => F w ζ) = fun x => -Real.log (min (max ‖x - ζ‖ (Real.exp (-(n : ℝ)))) R0) := by
    funext w
    simp only [hF]
    rw [norm_sub_rev]
  rw [e]
  simpa [hF, norm_sub_rev] using key

/-- Helper (Ch. III §2, Lemma 2.1). A nonnegative function, continuous on a circle, with circle average `≤ 0` vanishes
on the circle. -/
theorem gm32_circle_nonneg_zero {f : ℂ → ℝ} {x : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hf : ContinuousOn f (sphere x ρ))
    (h0 : ∀ y ∈ sphere x ρ, 0 ≤ f y) (havg : Real.circleAverage f x ρ ≤ 0) :
    ∀ y ∈ sphere x ρ, f y = 0 := by
  intro y hy
  by_contra hne
  have hpos : 0 < f y := lt_of_le_of_ne (h0 y hy) (Ne.symm hne)
  obtain ⟨θ0, -, hθ0⟩ : y ∈ circleMap x ρ '' Set.Ioc 0 (2 * π) := by
    rw [image_circleMap_Ioc, abs_of_pos hρ]
    exact hy
  subst hθ0
  set φ : ℝ → ℝ := fun θ => f (circleMap x ρ θ) with hφ
  have hφc : Continuous φ :=
    hf.comp_continuous (continuous_circleMap x ρ) (fun θ => by simp [abs_of_pos hρ])
  have hφ0 : ∀ θ, 0 ≤ φ θ := fun θ => h0 _ (by simp [abs_of_pos hρ])
  have hper : Function.Periodic φ (2 * π) := (periodic_circleMap x ρ).comp f
  have hint0 : ∫ θ in (0 : ℝ)..(0 + 2 * π), φ θ = ∫ θ in (θ0 - π)..(θ0 - π + 2 * π), φ θ :=
    hper.intervalIntegral_add_eq 0 (θ0 - π)
  have hposint : 0 < ∫ θ in (θ0 - π)..(θ0 - π + 2 * π), φ θ := by
    rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hφ0)
      (hφc.intervalIntegrable _ _)]
    refine ⟨by linarith [Real.pi_pos], ?_⟩
    have hopen : IsOpen (Function.support φ ∩ Set.Ioo (θ0 - π) (θ0 - π + 2 * π)) :=
      (hφc.isOpen_support).inter isOpen_Ioo
    have hne : (Function.support φ ∩ Set.Ioo (θ0 - π) (θ0 - π + 2 * π)).Nonempty :=
      ⟨θ0, hpos.ne', by constructor <;> linarith [Real.pi_pos]⟩
    exact lt_of_lt_of_le (hopen.measure_pos _ hne)
      (MeasureTheory.measure_mono (Set.inter_subset_inter_right _ Set.Ioo_subset_Ioc_self))
  rw [← hint0, zero_add] at hposint
  have : 0 < Real.circleAverage f x ρ := by
    rw [Real.circleAverage_def]
    exact smul_pos (inv_pos.2 (by positivity)) hposint
  linarith

/-- Helper (Ch. III §2, Lemma 2.1). Minimum principle: a function continuous on a closed disc with the super-mean-value
property on small circles is `≥ A` on the disc as soon as it is `≥ A` on the boundary circle. -/
theorem gm32_min_principle {g : ℂ → ℝ} {c : ℂ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (closedBall c r))
    (hsm : ∀ w ∈ ball c r, ∀ ρ : ℝ, 0 < ρ → closedBall w ρ ⊆ ball c r → Real.circleAverage g w ρ ≤ g w)
    {A : ℝ} (hb : ∀ ζ ∈ sphere c r, A ≤ g ζ) : ∀ z ∈ closedBall c r, A ≤ g z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨z1, hz1, hz1A⟩ := hcon
  obtain ⟨w, hw, hmin⟩ := (isCompact_closedBall c r).exists_isMinOn ⟨c, mem_closedBall_self hr.le⟩ hg
  have hwA : g w < A := lt_of_le_of_lt (hmin hz1) hz1A
  have hwball : w ∈ ball c r := by
    rcases (mem_closedBall.1 hw).lt_or_eq with h | h
    · exact mem_ball.2 h
    · exact absurd (hb w (mem_sphere.2 h)) (not_le.2 hwA)
  set m := g w with hm_def
  have hm : ∀ x ∈ closedBall c r, m ≤ g x := fun x hx => hmin hx
  set u : Set ℂ := {x | x ∈ ball c r ∧ g x = m} with hu
  have huopen : IsOpen u := by
    rw [Metric.isOpen_iff]
    rintro x ⟨hxb, hxm⟩
    have hxd : dist x c < r := mem_ball.1 hxb
    refine ⟨r - dist x c, by linarith, fun y hy => ?_⟩
    have hyd : dist y x < r - dist x c := mem_ball.1 hy
    have hyb : y ∈ ball c r := by
      rw [mem_ball]
      have := dist_triangle y x c
      linarith
    refine ⟨hyb, ?_⟩
    by_cases hyx : y = x
    · rw [hyx]; exact hxm
    have hρ : 0 < dist y x := dist_pos.2 hyx
    have hsub : closedBall x (dist y x) ⊆ ball c r := by
      intro z hz
      rw [mem_ball]
      have h1 := mem_closedBall.1 hz
      have := dist_triangle z x c
      linarith
    have hsph : sphere x (dist y x) ⊆ closedBall c r := fun z hz =>
      ball_subset_closedBall (hsub (sphere_subset_closedBall hz))
    have hgI : CircleIntegrable g x (dist y x) := ContinuousOn.circleIntegrable hρ.le (hg.mono hsph)
    have h1 : Real.circleAverage (fun z => g z - m) x (dist y x) =
        Real.circleAverage g x (dist y x) - m := by
      rw [Real.circleAverage_fun_sub hgI (circleIntegrable_const m x (dist y x)), Real.circleAverage_const]
    have hav : Real.circleAverage (fun z => g z - m) x (dist y x) ≤ 0 := by
      rw [h1]
      have := hsm x hxb (dist y x) hρ hsub
      linarith
    have h2 : g y - m = 0 := gm32_circle_nonneg_zero (f := fun z => g z - m) hρ
      ((hg.mono hsph).sub continuousOn_const)
      (fun z hz => sub_nonneg.2 (hm z (hsph hz))) hav y (mem_sphere.2 rfl)
    linarith
  have hclos : ball c r ∩ closure u ⊆ u := by
    rintro x ⟨hxb, hxcl⟩
    refine ⟨hxb, ?_⟩
    by_contra hne
    have hgt : m < g x := lt_of_le_of_ne (hm x (ball_subset_closedBall hxb)) (Ne.symm hne)
    have hcont : ContinuousAt g x := hg.continuousAt (mem_of_superset (isOpen_ball.mem_nhds hxb) ball_subset_closedBall)
    have hev : ∀ᶠ y in 𝓝 x, m < g y := (continuousAt_const (y := m)).eventually_lt hcont hgt
    obtain ⟨y, hyev, hyu⟩ := mem_closure_iff_nhds.1 hxcl _ hev
    exact absurd hyu.2 (ne_of_gt hyev)
  have hsub : ball c r ⊆ u :=
    (isConnected_ball hr).isPreconnected.subset_of_closure_inter_subset huopen ⟨w, hwball, hwball, rfl⟩
      (by simpa [Set.inter_comm] using hclos)
  -- the boundary
  have hζ : (c + (r : ℂ)) ∈ sphere c r := by
    simp [abs_of_pos hr]
  have hζcl : (c + (r : ℂ)) ∈ closure (ball c r) := by
    rw [closure_ball c hr.ne']
    exact sphere_subset_closedBall hζ
  have hcw : ContinuousWithinAt g (ball c r) (c + (r : ℂ)) :=
    (hg _ (sphere_subset_closedBall hζ)).mono ball_subset_closedBall
  have himg : g '' ball c r ⊆ {m} := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hsub hx).2
  have hmem := hcw.mem_closure_image hζcl
  have hcl : closure (g '' ball c r) ⊆ {m} :=
    closure_minimal himg isClosed_singleton
  have hgm : g (c + (r : ℂ)) = m := hcl hmem
  have := hb _ hζ
  linarith

/-- Helper (Ch. III §2, Lemma 2.1). The truncated potentials increase with the truncation index. -/
theorem gm32_ut_mono (μ : Measure ℂ) [IsFiniteMeasure μ] {R0 : ℝ} (hR0 : 1 ≤ R0) {n n' : ℕ} (h : n ≤ n') (z : ℂ) :
    ∫ ζ, -Real.log (min (max ‖ζ - z‖ (Real.exp (-(n : ℝ)))) R0) ∂μ ≤
      ∫ ζ, -Real.log (min (max ‖ζ - z‖ (Real.exp (-(n' : ℝ)))) R0) ∂μ := by
  have hint : ∀ k : ℕ, Integrable (fun ζ : ℂ => -Real.log (min (max ‖ζ - z‖ (Real.exp (-(k : ℝ)))) R0)) μ :=
    fun k => by
      refine Integrable.of_bound ?_ ((k : ℝ) + R0) (Filter.Eventually.of_forall fun ζ => ?_)
      · exact (Continuous.neg (Continuous.log
          ((((continuous_id.sub continuous_const).norm).max continuous_const).min continuous_const)
          fun ζ => (gm32_clamp_bound ‖ζ - z‖ hR0 k).1.ne')).aestronglyMeasurable
      · rw [Real.norm_eq_abs]
        exact (gm32_clamp_bound ‖ζ - z‖ hR0 k).2
  refine MeasureTheory.integral_mono (hint n) (hint n') fun ζ => ?_
  refine neg_le_neg (Real.log_le_log (gm32_clamp_bound ‖ζ - z‖ hR0 n').1 ?_)
  refine min_le_min (max_le_max le_rfl (Real.exp_le_exp.2 ?_)) le_rfl
  have : (n : ℝ) ≤ n' := Nat.cast_le.2 h
  linarith

/-- Helper (Ch. III §2, Lemma 2.1). The potential of a finite measure with compact support never takes the value `−∞`:
the negative part of the kernel is integrable against it. -/
theorem gm32_logPotential_ne_bot (μ : Measure ℂ) [IsFiniteMeasure μ] (hμ : ∃ K : Set ℂ, IsCompact K ∧ μ Kᶜ = 0)
    (z : ℂ) : logPotential μ z ≠ ⊥ := by
  obtain ⟨K, hK, hKμ⟩ := hμ
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall z
  have hae : ∀ᵐ ζ ∂μ, ‖(fun ζ : ℂ => ζ - z) ζ‖ ≤ R := by
    filter_upwards [(MeasureTheory.mem_ae_iff.2 hKμ : K ∈ MeasureTheory.ae μ)] with ζ hζ
    simpa [dist_eq_norm] using hR hζ
  obtain ⟨-, -, hB⟩ := gm32_trunc_generic (m := μ) (w := fun ζ : ℂ => ζ - z)
    (measurable_id.sub measurable_const) hae
  intro hbot
  have h0 : (0 : EReal) - ((∫⁻ ζ, (-(-ENNReal.log ‖ζ - z‖ₑ)).toENNReal ∂μ : ℝ≥0∞) : EReal) ≤
      logPotential μ z :=
    EReal.sub_le_sub (EReal.coe_ennreal_nonneg _) le_rfl
  rw [hbot, le_bot_iff, zero_sub, EReal.neg_eq_bot_iff, EReal.coe_ennreal_eq_top_iff] at h0
  exact hB h0

/-- Helper (Ch. III §2, Lemma 2.1). The potential of a finite measure with compact support is lower semicontinuous
(locally the supremum of the continuous truncations of the kernel). -/
theorem gm32_logPotential_lsc (μ : Measure ℂ) [IsFiniteMeasure μ] (hμ : ∃ K : Set ℂ, IsCompact K ∧ μ Kᶜ = 0) :
    LowerSemicontinuous (logPotential μ) := by
  obtain ⟨K, hK, hKμ⟩ := hμ
  obtain ⟨Rk, hRk⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  intro x0 y hy
  set R0 : ℝ := max (Rk + ‖x0‖ + 1) 1 with hR0
  have hR01 : 1 ≤ R0 := le_max_right _ _
  have hbd : ∀ x ∈ ball x0 1, ∀ᵐ ζ ∂μ, ‖ζ - x‖ ≤ R0 := fun x hx => by
    filter_upwards [(MeasureTheory.mem_ae_iff.2 hKμ : K ∈ MeasureTheory.ae μ)] with ζ hζ
    have h1 : ‖ζ‖ ≤ Rk := mem_closedBall_zero_iff.1 (hRk hζ)
    have h2 : ‖x - x0‖ < 1 := by simpa [dist_eq_norm] using hx
    have h3 := norm_sub_norm_le x x0
    have h4 : Rk + ‖x0‖ + 1 ≤ R0 := le_max_left _ _
    calc ‖ζ - x‖ ≤ ‖ζ‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ R0 := by linarith
  have hx0 := hbd x0 (mem_ball_self one_pos)
  obtain ⟨-, hsup⟩ := gm32_ut_eq μ hR01 hx0
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 (lt_of_lt_of_le hy hsup)
  have hcn := (continuous_coe_real_ereal.comp (gm32_ut_continuous μ hR01 n)).continuousAt (x := x0)
  have hev := (continuousAt_const (y := y)).eventually_lt hcn hn
  filter_upwards [hev, ball_mem_nhds x0 one_pos] with x' h1 h2
  exact lt_of_lt_of_le h1 ((gm32_ut_eq μ hR01 (hbd x' h2)).1 n)

/-- Helper (Ch. III §2, Lemma 2.1). Comparison on discs: if `H` is continuous on a closed disc, harmonic in the open
disc, and `H ≤ U_μ` on the circle, then `H ≤ U_μ` in the disc (the harmonic-minorant form of superharmonicity;
proof: super-mean-value of the truncated potentials plus a minimum principle). -/
theorem gm32_logPotential_comparison (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hμ : ∃ K : Set ℂ, IsCompact K ∧ μ Kᶜ = 0) (c : ℂ) (r : ℝ) (hr : 0 < r) (H : ℂ → ℝ)
    (hHc : ContinuousOn H (closedBall c r)) (hHh : InnerProductSpace.HarmonicOnNhd H (ball c r))
    (hb : ∀ ζ ∈ sphere c r, (H ζ : EReal) ≤ logPotential μ ζ) :
    ∀ z ∈ ball c r, (H z : EReal) ≤ logPotential μ z := by
  obtain ⟨K, hK, hKμ⟩ := hμ
  obtain ⟨Rk, hRk⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  set R0 : ℝ := max (Rk + ‖c‖ + r) 1 with hR0
  have hR01 : 1 ≤ R0 := le_max_right _ _
  have hR0' : Rk + ‖c‖ + r ≤ R0 := le_max_left _ _
  have hbd : ∀ᵐ ζ ∂μ, ∀ x ∈ closedBall c r, ‖ζ - x‖ ≤ R0 := by
    filter_upwards [(MeasureTheory.mem_ae_iff.2 hKμ : K ∈ MeasureTheory.ae μ)] with ζ hζ x hx
    have h1 : ‖ζ‖ ≤ Rk := mem_closedBall_zero_iff.1 (hRk hζ)
    have h2 : ‖x - c‖ ≤ r := by simpa [dist_eq_norm] using mem_closedBall.1 hx
    have h3 := norm_sub_norm_le x c
    calc ‖ζ - x‖ ≤ ‖ζ‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ R0 := by linarith
  have hbd1 : ∀ x ∈ closedBall c r, ∀ᵐ ζ ∂μ, ‖ζ - x‖ ≤ R0 := fun x hx => by
    filter_upwards [hbd] with ζ h using h x hx
  set ut : ℕ → ℂ → ℝ := fun n z => ∫ ζ, -Real.log (min (max ‖ζ - z‖ (Real.exp (-(n : ℝ)))) R0) ∂μ with hut_def
  have hut : ∀ n, Continuous (ut n) := fun n => gm32_ut_continuous μ hR01 n
  have key : ∀ ε : ℝ, 0 < ε → ∀ z ∈ ball c r, ((H z - ε : ℝ) : EReal) ≤ logPotential μ z := by
    intro ε hε z hz
    -- Dini on the circle
    have hdini : ∃ n : ℕ, ∀ ζ ∈ sphere c r, H ζ - ε < ut n ζ := by
      have hcS : CompactSpace (sphere c r) := isCompact_iff_compactSpace.1 (isCompact_sphere c r)
      have hHS : Continuous fun s : sphere c r => H s :=
        (hHc.mono sphere_subset_closedBall).domRestrict
      let U : ℕ → Set (sphere c r) := fun n => {s | H s - ε < ut n s}
      have hUo : ∀ n, IsOpen (U n) := fun n =>
        isOpen_lt (hHS.sub continuous_const) ((hut n).comp continuous_subtype_val)
      have hcover : (Set.univ : Set (sphere c r)) ⊆ ⋃ n, U n := by
        intro s _
        have hs := s.2
        obtain ⟨-, hsup⟩ := gm32_ut_eq μ hR01 (hbd1 s (sphere_subset_closedBall hs))
        have hle : ((H s - ε : ℝ) : EReal) < ⨆ n : ℕ, ((ut n s : ℝ) : EReal) :=
          lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (by linarith : H s - ε < H s)) ((hb s hs).trans hsup)
        obtain ⟨n, hn⟩ := lt_iSup_iff.1 hle
        exact Set.mem_iUnion.2 ⟨n, EReal.coe_lt_coe_iff.1 hn⟩
      have hdir : Directed (· ⊆ ·) U := fun a b =>
        ⟨max a b, fun s hs => lt_of_lt_of_le hs (gm32_ut_mono μ hR01 (le_max_left a b) s),
          fun s hs => lt_of_lt_of_le hs (gm32_ut_mono μ hR01 (le_max_right a b) s)⟩
      obtain ⟨n, hn⟩ := isCompact_univ.elim_directed_cover U hUo hcover hdir
      exact ⟨n, fun ζ hζ => hn (Set.mem_univ ⟨ζ, hζ⟩)⟩
    obtain ⟨n, hn⟩ := hdini
    -- minimum principle for `ut n - H`
    have hgc : ContinuousOn (fun w => ut n w - H w) (closedBall c r) :=
      (hut n).continuousOn.sub hHc
    have hsm : ∀ w ∈ ball c r, ∀ ρ : ℝ, 0 < ρ → closedBall w ρ ⊆ ball c r →
        Real.circleAverage (fun w => ut n w - H w) w ρ ≤ ut n w - H w := by
      intro w hw ρ hρ hsub
      have hsph : sphere w ρ ⊆ closedBall c r := fun x hx =>
        ball_subset_closedBall (hsub (sphere_subset_closedBall hx))
      have hI1 : CircleIntegrable (ut n) w ρ := (hut n).continuousOn.circleIntegrable hρ.le
      have hI2 : CircleIntegrable H w ρ := ContinuousOn.circleIntegrable hρ.le (hHc.mono hsph)
      rw [Real.circleAverage_fun_sub hI1 hI2]
      have hH : Real.circleAverage H w ρ = H w := by
        refine InnerProductSpace.HarmonicOnNhd.circleAverage_eq (hHh.mono ?_)
        rw [abs_of_pos hρ]
        exact hsub
      have hU := gm32_ut_supermean μ hR01 n w hρ (by
        filter_upwards [hbd] with ζ h x hx using h x (ball_subset_closedBall (hsub hx)))
      rw [hH]
      exact sub_le_sub_right hU _
    have hmp := gm32_min_principle (A := -ε) hr hgc hsm (fun ζ hζ => by
      have := hn ζ hζ
      show -ε ≤ ut n ζ - H ζ
      linarith) z (ball_subset_closedBall hz)
    have hle : H z - ε ≤ ut n z := by
      have : -ε ≤ ut n z - H z := hmp
      linarith
    exact (EReal.coe_le_coe_iff.2 hle).trans
      ((gm32_ut_eq μ hR01 (hbd1 z (ball_subset_closedBall hz))).1 n)
  intro z hz
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨y, hy1, hy2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  have hHy : y < H z := EReal.coe_lt_coe_iff.1 hy2
  have := key (H z - y) (by linarith) z hz
  rw [sub_sub_cancel] at this
  exact absurd (lt_of_lt_of_le hy1 this) (lt_irrefl _)

/-- **Lemma 2.1** (Ch. III §2; used in the proof of Theorem 2.2, P1:3566–3572, and of Theorem 6.3, P1:4361). If `μ > 0`,
the potential `U_μ` is lower semicontinuous and superharmonic.
Modelling: "H μ > 0" (P1:3496) is "If μ > 0" [OCR or misprint; inline, no crop]; `μ` is a positive measure, finite with
compact support (the measures of §2); superharmonic on `ℂ` is `References.IsSuperharmonicOn` (for `EReal`-valued
functions). -/
theorem lemma3_2_1 (μ : Measure ℂ) [IsFiniteMeasure μ] (hμ : ∃ K : Set ℂ, IsCompact K ∧ μ Kᶜ = 0) :
    LowerSemicontinuous (logPotential μ) ∧ References.IsSuperharmonicOn (logPotential μ) univ := by
  refine ⟨gm32_logPotential_lsc μ hμ, isOpen_univ, fun z _ => ?_, ?_, ?_⟩
  · exact lt_top_iff_ne_top.2 (fun h => gm32_logPotential_ne_bot μ hμ z (by
      have := congrArg (fun x : EReal => -x) h
      simpa using this))
  · intro x _
    have hl := gm32_logPotential_lsc μ hμ x
    intro y hy
    have hy' : -y < logPotential μ x := EReal.neg_lt_comm.1 hy
    rw [nhdsWithin_univ]
    filter_upwards [hl (-y) hy'] with x' hx'
    exact EReal.neg_lt_comm.1 hx'
  · intro c r hr _ h hhc hhh hb z hz
    have key := gm32_logPotential_comparison μ hμ c r hr (fun x => - h x)
      hhc.neg hhh.neg (fun ζ hζ => by
        have := hb ζ hζ
        rw [EReal.coe_neg]
        exact EReal.neg_le.1 this) z hz
    rw [EReal.coe_neg] at key
    exact EReal.neg_le.2 key

/-- **Definition** (the equilibrium distribution `μ_E` of a set with smooth complement, Ch. III §2, P1:3506–3512 and
P1:3530). Suppose `Ω = ℂ* \ E` is bounded by a finite family of disjoint `C^{1+α}` Jordan curves, `α > 0`; `μ_E` is
the harmonic measure of `∞` relative to `Ω`, `dμ_E = dω(∞, ·, Ω)`, and it is called the equilibrium distribution of
`E`.
Modelling: the harmonic measure `harmonicMeasureFC` of Ch. II §1 (the most general harmonic measure at this point of
the book) of `(toExt E)ᶜ` at the point `∞`, carried to `ℂ` by the inclusion `ℂ → ℂ*` (a measurable embedding; the
measure lives on `∂Ω ⊆ ℂ`). Junk: whatever `harmonicMeasureFC` gives when `ℂ* \ E` is not a finitely connected Jordan
domain; never used there. -/
def equilibriumMeasureFC (E : Set ℂ) : Measure ℂ :=
  (harmonicMeasureFC (toExt E)ᶜ extInf).comap ((↑) : ℂ → ExtPlane)

/-- **Theorem 2.2** (Ch. III §2; cited at P1:3580, in the proof of Theorem 4.1, P1:3798, and in Ch. V, P1:7071),
first part. If `Ω = ℂ* \ E` is connected and bounded by finitely many pairwise disjoint `C^{1+α}` Jordan curves, then
the integral `U_{μ_E}(z)` is absolutely convergent at every `z ∈ ℂ`, and the potential `U_{μ_E}` is continuous on
`ℂ`.
Modelling: the hypothesis is `IsSmoothFCDomain (toExt E)ᶜ` (then `E` is compact and `∞ ∈ Ω`); absolute convergence
is the finiteness of `∫ |log (1/|ζ − z|)| dμ_E(ζ)`; continuity is that of `U_{μ_E}` as an `EReal`-valued function,
whose values are finite by absolute convergence. -/
theorem thm3_2_2_a {E : Set ℂ} (hΩ : IsSmoothFCDomain (toExt E)ᶜ) :
    (∀ z : ℂ, ∫⁻ ζ, absLogKernel ζ z ∂(equilibriumMeasureFC E) < ⊤) ∧
      Continuous (logPotential (equilibriumMeasureFC E)) := by
  sorry

/-- **Theorem 2.2** (Ch. III §2), (2.1) (cited at P1:3556, 3578, 3580, 3908). Under the hypotheses of the first part,
(2.1) `g(z, ∞) = γ(E) − U_{μ_E}(z)`, `z ∈ Ω̄`.
Modelling: `g(·, ∞)` is Green's function `greenFunction` of Ch. II §2 of `Ω = (toExt E)ᶜ` and `γ(E)` is
`robinConstantFC E` (the theorem is set in the finitely connected case of §1); stated at the finite points of `Ω`,
where `z ∉ E` (`z = ∞` is the pole); on `∂Ω ⊆ E` the boundary value of `g` is `0`, and (2.1) there is
`U_{μ_E} = γ(E)`, part of (2.3) (`thm3_2_2_d`). -/
theorem thm3_2_2_b {E : Set ℂ} (hΩ : IsSmoothFCDomain (toExt E)ᶜ) :
    ∀ z : ℂ, z ∉ E →
      logPotential (equilibriumMeasureFC E) z =
        ((robinConstantFC E - greenFunction (toExt E)ᶜ z extInf : ℝ) : EReal) := by
  sorry

/-- **Theorem 2.2** (Ch. III §2), (2.2) (cited at P1:3580). Under the hypotheses of the first part,
(2.2) `U_{μ_E}(z) < γ(E)`, `z ∈ Ω`.
Modelling: at the finite points of `Ω = (toExt E)ᶜ`, i.e. `z ∉ E`; `γ(E)` is `robinConstantFC E`. -/
theorem thm3_2_2_c {E : Set ℂ} (hΩ : IsSmoothFCDomain (toExt E)ᶜ) :
    ∀ z : ℂ, z ∉ E → logPotential (equilibriumMeasureFC E) z < (robinConstantFC E : EReal) := by
  sorry

/-- **Theorem 2.2** (Ch. III §2), (2.3) (cited at P1:3798, proof of Theorem 4.1, and P1:4768). Under the hypotheses of
the first part, (2.3) `U_{μ_E}(z) = γ(E)`, `z ∈ E = ℂ* \ Ω`.
Modelling: `γ(E)` is `robinConstantFC E`. -/
theorem thm3_2_2_d {E : Set ℂ} (hΩ : IsSmoothFCDomain (toExt E)ᶜ) :
    ∀ z ∈ E, logPotential (equilibriumMeasureFC E) z = (robinConstantFC E : EReal) := by
  sorry

end GarnettMarshall2005
