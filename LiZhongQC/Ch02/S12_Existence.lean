import LiZhongQC.Ch02.S11_IntegralOperators
import LiZhongQC.Ch02.S11b_HilbertNorm
import LiZhongQC.Ch01.S08_Compactness
import LiZhongQC.Lemmas.InvarianceOfDomain

/-!
# §12 存在性定理 — The existence theorem

* §12.1 the singular integral equation `ω = μ H(ω) + h` (12.1) and its Neumann series (12.2)
                                                   — `eq12_1_exists_exponent`, `eq12_1_solution`,
                                                     `eq12_2_neumann`
* Lemma 12.1 (a proper local homeomorphism of `ℂ` is a homeomorphism) — `lemma12_1`
* Theorem 12.1 (global homeomorphic solutions of the Beltrami equation) — `thm12_1`
* Theorem 12.2 (existence of quasiconformal maps with given complex characteristic)
                                                   — `thm12_2`

## What is proved here

The choice of the exponent `p` (from Corollary 2 of Theorem 11.3) and the singular integral
equation (12.1) (`eq12_1_solution`) are proved, the latter as a Banach-space contraction on
`MeasureTheory.Lp ℂ p volume` (`phiMap_memLp`, `phiMap_congr_ae`, `phiMap_sub_bound`), resting only
on `hilbertH_memLp` and (11.16).  `thm12_1_smooth_case` (the `C₀^∞` case of the Beltrami equation,
W-D) is now proved in full: `f := exp(T ω̃)` for the (12.6) solution `ω̃`; the rectangle integrals
of `f (dz + μ dz̄)` vanish by the §9 Green formulas, giving a `C¹` primitive `w̃`
(`exists_contDiff_primitive_of_rect_integral_eq_zero`); `w̃ - z - T(μ f)` is entire (the Weyl
lemma `differentiable_of_genDzbar_eq_zero`), affine by Liouville on its `dslope`, and constant by
a decay argument (`hilbertH_tendsto_zero_of_bounded_support`); `μ f` is identified with the given
`ω` by uniqueness in (12.1); the homeomorphism comes from `homeomorph_of_contDiff_jacobian_pos`.
Its only remaining dependency is the W-A wall (`eq12_1_solution`/Theorem 11.1 resting on
`hilbertH_memLp`/(11.16)/Riesz–Thorin, still `sorry` in §11).  Theorem 12.1 (`thm12_1`) and
Theorem 12.2 (`thm12_2`) are now assembled from `eq12_1_solution`, Theorem 11.1 and
`thm12_1_isKQC` (the homeomorphism and quasiconformality half of Theorem 12.1), which is itself
now proved from the `C₀^∞` approximation argument, modulo `thm6_1_modulus_quasi_invariance` and
`thm8_2_limit`.  Kept as `sorry`: (12.2) is a Neumann-series restatement not otherwise needed.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-- `μ` is a Beltrami coefficient on the plane with bounded support: measurable, `|μ| ≤ k`
a.e. and vanishing outside a disc. -/
def IsCompactBeltramiCoeff (μ : ℂ → ℂ) (k : ℝ) : Prop :=
  IsBeltramiCoeff μ univ k ∧ ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → μ z = 0

/-- §12.1: given `k < 1` and `p₁ > 2`, there is `p ∈ (2, p₁]` with `k Λ_p < 1`
(by Corollary 2 of Theorem 11.3). -/
theorem eq12_1_exists_exponent {k : ℝ} (hk : k < 1) {p₁ : ℝ} (hp₁ : 2 < p₁) :
    ∃ p : ℝ, 2 < p ∧ p ≤ p₁ ∧ k * hilbertNorm p < 1 := by
  have hnn : ∀ q : ℝ, 0 ≤ hilbertNorm q := by
    intro q
    rw [hilbertNorm]
    refine Real.sSup_nonneg ?_
    rintro c ⟨ω, -, -, rfl⟩
    exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  rcases le_or_gt k 0 with hk0 | -
  · exact ⟨p₁, hp₁, le_rfl, by nlinarith [hnn p₁]⟩
  · -- `Λ_p → 1` as `p → 2` (Corollary 2 of Theorem 11.3), so `k Λ_p < 1` near `2`
    have hlim : Tendsto (fun q => k * hilbertNorm q) (𝓝 2) (𝓝 (k * 1)) :=
      tendsto_const_nhds.mul thm11_3_cor2
    rw [mul_one] at hlim
    have hev : ∀ᶠ q in 𝓝 (2 : ℝ), k * hilbertNorm q < 1 := hlim (Iio_mem_nhds hk)
    have hlt : ∀ᶠ q in 𝓝 (2 : ℝ), q < p₁ := Iio_mem_nhds hp₁
    have hev2 : ∀ᶠ q in 𝓝[>] (2 : ℝ), k * hilbertNorm q < 1 ∧ q < p₁ :=
      (hev.filter_mono nhdsWithin_le_nhds).and (hlt.filter_mono nhdsWithin_le_nhds)
    obtain ⟨q, hq1, hq2⟩ := (hev2.and self_mem_nhdsWithin).exists
    exact ⟨q, hq2, hq1.2.le, hq1.1⟩

/-- `Φ ω = μ H(ω) + h` preserves `MemLp p`: `μ ∈ MemLp ⊤` (from `IsBeltramiCoeff`'s a.e. bound)
times `H(ω) ∈ MemLp p` (from `hilbertH_memLp`) under the `HolderTriple ⊤ p p` instance. -/
theorem phiMap_memLp {μ h : ℂ → ℂ} {k p : ℝ} (hμ : IsBeltramiCoeff μ univ k) (hp : 1 < p)
    (hh : MemLp h (ENNReal.ofReal p)) {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p)) :
    MemLp (fun z => μ z * hilbertH ω z + h z) (ENNReal.ofReal p) := by
  have hμ' : AEStronglyMeasurable μ volume := by simpa using hμ.1
  have hμbd : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k := by simpa using hμ.2
  have hμTop : MemLp μ ⊤ volume := memLp_top_of_bound hμ' k hμbd
  have hHω : MemLp (hilbertH ω) (ENNReal.ofReal p) := (hilbertH_memLp hp hω)
  have hmul : MemLp (fun z => μ z * hilbertH ω z) (ENNReal.ofReal p) := hμTop.fun_mul hHω
  exact hmul.add hh

/-- `Φ` respects `=ᵐ` exactly (funext, via `hilbertH_congr_ae`). -/
theorem phiMap_congr_ae {μ h : ℂ → ℂ} {ω₁ ω₂ : ℂ → ℂ} (hω : ω₁ =ᵐ[volume] ω₂) :
    (fun z => μ z * hilbertH ω₁ z + h z) = fun z => μ z * hilbertH ω₂ z + h z := by
  rw [hilbertH_congr_ae hω]

/-- The contraction estimate for `Φ`. -/
theorem phiMap_sub_bound {μ h : ℂ → ℂ} {k p : ℝ} (hk₀ : 0 ≤ k) (hμ : IsBeltramiCoeff μ univ k)
    (hp : 1 < p) {ω₁ ω₂ : ℂ → ℂ} (hω₁ : MemLp ω₁ (ENNReal.ofReal p))
    (hω₂ : MemLp ω₂ (ENNReal.ofReal p)) :
    eLpNorm (fun z => (μ z * hilbertH ω₁ z + h z) - (μ z * hilbertH ω₂ z + h z))
      (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (k * hilbertNorm p) *
        eLpNorm (fun z => ω₁ z - ω₂ z) (ENNReal.ofReal p) volume := by
  have hμbd : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k := by simpa using hμ.2
  obtain ⟨A, hA0, hbound⟩ := zygmund_calderon hp
  have hHsub := hilbertH_sub_ae_of_smooth_bound hp hbound hω₁ hω₂
  have hcong : (fun z => (μ z * hilbertH ω₁ z + h z) - (μ z * hilbertH ω₂ z + h z)) =ᵐ[volume]
      fun z => μ z * hilbertH (fun z => ω₁ z - ω₂ z) z := by
    filter_upwards [hHsub] with z hz
    rw [hz]; ring
  rw [eLpNorm_congr_ae hcong]
  have hkenorm : ‖(k : ℝ)‖ₑ = ENNReal.ofReal k := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hk₀]
  calc eLpNorm (fun z => μ z * hilbertH (fun z => ω₁ z - ω₂ z) z) (ENNReal.ofReal p) volume
      ≤ eLpNorm (k • hilbertH (fun z => ω₁ z - ω₂ z)) (ENNReal.ofReal p) volume := by
        refine eLpNorm_mono_ae ?_ ?_
        · exact (by simpa using hμ.1 : AEStronglyMeasurable μ volume).mul
            (hilbertH_memLp hp (hω₁.sub hω₂)).aestronglyMeasurable
        filter_upwards [hμbd] with z hz
        simp only [Pi.smul_apply, Complex.real_smul, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hk₀]
        exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
    _ = ENNReal.ofReal k * eLpNorm (hilbertH (fun z => ω₁ z - ω₂ z)) (ENNReal.ofReal p) volume := by
        rw [eLpNorm_const_smul, hkenorm]
    _ ≤ ENNReal.ofReal k * (ENNReal.ofReal (hilbertNorm p) *
          eLpNorm (fun z => ω₁ z - ω₂ z) (ENNReal.ofReal p) volume) := by
        gcongr
        exact eq11_16_eLpNorm hp (hω₁.sub hω₂)
    _ = ENNReal.ofReal (k * hilbertNorm p) *
          eLpNorm (fun z => ω₁ z - ω₂ z) (ENNReal.ofReal p) volume := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hk₀]

/-- §12.1: if `|μ| ≤ k` a.e., `k Λ_p < 1` and `h ∈ L_p`, `p > 2`, then `ω ↦ μ H(ω)` is a
contraction of `L_p`, so the singular integral equation (12.1) `ω = μ H(ω) + h` has a unique
solution in `L_p`.

*Proof.*  `Φ ω = μ H(ω) + h` is a contraction of `MeasureTheory.Lp ℂ p volume` with constant
`k Λ_p < 1`, via (11.16) and the a.e. additivity of `H`; Banach's fixed point theorem
(`ContractingWith.exists_fixedPoint`) gives existence, and `eq_or_edist_eq_top_of_fixedPoints`
(every two elements of `Lp` are at finite distance) gives uniqueness. -/
theorem eq12_1_solution {μ h : ℂ → ℂ} {k p : ℝ} (hk₀ : 0 ≤ k) (hμ : IsBeltramiCoeff μ univ k)
    (hp : 2 < p) (hkp : k * hilbertNorm p < 1) (hh : MemLp h (ENNReal.ofReal p)) :
    ∃ ω : ℂ → ℂ, MemLp ω (ENNReal.ofReal p) ∧ (ω =ᵐ[volume] fun z => μ z * hilbertH ω z + h z) ∧
      ∀ ω' : ℂ → ℂ, MemLp ω' (ENNReal.ofReal p) →
        (ω' =ᵐ[volume] fun z => μ z * hilbertH ω' z + h z) → ω' =ᵐ[volume] ω := by
  have hp1 : (1 : ℝ) < p := by linarith
  haveI hfact : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1.le⟩
  set K : ℝ≥0 := ⟨k * hilbertNorm p, mul_nonneg hk₀ (hilbertNorm_nonneg p)⟩ with hKdef
  have hK1 : K < 1 := by
    rw [hKdef]
    exact_mod_cast hkp
  have hKof : ENNReal.ofReal (k * hilbertNorm p) = (K : ℝ≥0∞) := by
    rw [show (k * hilbertNorm p) = (K : ℝ) from rfl, ENNReal.ofReal_coe_nnreal]
  set Φraw : (ℂ → ℂ) → ℂ → ℂ := fun ω z => μ z * hilbertH ω z + h z with hΦrawdef
  set E := Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) with hEdef
  have hΦrawMemLp : ∀ ω : ℂ → ℂ, MemLp ω (ENNReal.ofReal p) → MemLp (Φraw ω) (ENNReal.ofReal p) :=
    fun ω hω => phiMap_memLp hμ hp1 hh hω
  let Φ : E → E := fun ω => (hΦrawMemLp (⇑ω) (Lp.memLp ω)).toLp (Φraw (⇑ω))
  have hΦcoe : ∀ ω : E, (⇑(Φ ω) : ℂ → ℂ) =ᵐ[volume] Φraw (⇑ω) := fun ω => MemLp.coeFn_toLp _
  have hLpedist_ne_top : ∀ x y : E, edist x y ≠ ⊤ := by
    intro x y
    rw [Lp.edist_def]
    have h1 : eLpNorm ((x : ℂ → ℂ) - (y : ℂ → ℂ)) (ENNReal.ofReal p) volume ≤
        eLpNorm (x : ℂ → ℂ) (ENNReal.ofReal p) volume +
          eLpNorm (y : ℂ → ℂ) (ENNReal.ofReal p) volume :=
      eLpNorm_sub_le hfact.out
    exact (h1.trans_lt (ENNReal.add_lt_top.2
      ⟨(Lp.memLp x).eLpNorm_lt_top, (Lp.memLp y).eLpNorm_lt_top⟩)).ne
  have hcontract : ContractingWith K Φ := by
    refine ⟨hK1, fun x y => ?_⟩
    rw [Lp.edist_def, Lp.edist_def]
    have hcong : ((⇑(Φ x) : ℂ → ℂ) - ⇑(Φ y)) =ᵐ[volume] (Φraw (⇑x) - Φraw (⇑y)) :=
      (hΦcoe x).sub (hΦcoe y)
    rw [eLpNorm_congr_ae hcong]
    calc eLpNorm (Φraw (⇑x) - Φraw (⇑y)) (ENNReal.ofReal p) volume
        ≤ ENNReal.ofReal (k * hilbertNorm p) *
            eLpNorm ((⇑x : ℂ → ℂ) - ⇑y) (ENNReal.ofReal p) volume :=
          phiMap_sub_bound hk₀ hμ hp1 (Lp.memLp x) (Lp.memLp y)
      _ = (K : ℝ≥0∞) * eLpNorm ((x : ℂ → ℂ) - (y : ℂ → ℂ)) (ENNReal.ofReal p) volume := by
            rw [hKof]
  obtain ⟨ωLp, hfix, -, -⟩ := hcontract.exists_fixedPoint (0 : E) (hLpedist_ne_top 0 (Φ 0))
  refine ⟨⇑ωLp, Lp.memLp ωLp, ?_, ?_⟩
  · have h1 : (⇑(Φ ωLp) : ℂ → ℂ) =ᵐ[volume] Φraw (⇑ωLp) := hΦcoe ωLp
    have h2 : (⇑(Φ ωLp) : ℂ → ℂ) = ⇑ωLp := by rw [hfix]
    rw [h2] at h1
    exact h1
  · intro ω' hω' heqω'
    set y : E := hω'.toLp ω' with hydef
    have hcoey : (⇑y : ℂ → ℂ) =ᵐ[volume] ω' := MemLp.coeFn_toLp hω'
    have hfixy : Φ y = y := by
      have hstep : (⇑(Φ y) : ℂ → ℂ) =ᵐ[volume] ω' := by
        refine (hΦcoe y).trans ?_
        have hraw : Φraw (⇑y) = Φraw ω' := by
          simp only [hΦrawdef]
          rw [hilbertH_congr_ae hcoey]
        rw [hraw]
        exact heqω'.symm
      have hfinal : (⇑(Φ y) : ℂ → ℂ) =ᵐ[volume] (⇑y : ℂ → ℂ) := hstep.trans hcoey.symm
      have hcong2 := MemLp.toLp_congr (Lp.memLp (Φ y)) (Lp.memLp y) hfinal
      rwa [Lp.toLp_coeFn, Lp.toLp_coeFn] at hcong2
    have huniq : y = ωLp ∨ edist y ωLp = ⊤ :=
      hcontract.eq_or_edist_eq_top_of_fixedPoints hfixy hfix
    rcases huniq with heq | htop
    · rw [heq] at hcoey
      exact hcoey.symm
    · exact absurd htop (hLpedist_ne_top y ωLp)

/-- T2.3 bullet 1: the bounded-support representative agrees a.e. with `ω`, using that `μ`
vanishes and (12.4) forces `ω` to vanish there too. -/
theorem t2_omega_ae_eq_indicator {μ ω : ℂ → ℂ} {R : ℝ}
    (hR : ∀ z : ℂ, R < ‖z‖ → μ z = 0)
    (hsol : ω =ᵐ[volume] fun z => μ z * hilbertH ω z + μ z) :
    ω =ᵐ[volume] (closedBall (0 : ℂ) R).indicator ω := by
  filter_upwards [hsol] with z hz
  by_cases hmem : z ∈ closedBall (0 : ℂ) R
  · rw [indicator_of_mem hmem]
  · rw [indicator_of_notMem hmem]
    rw [mem_closedBall_zero_iff, not_le] at hmem
    rw [hz, hR z hmem]
    ring

/-- A dominated-convergence helper for `eLpNorm`: `Fn n → 0` a.e., dominated by a *fixed*
real-valued `g` with `∫⁻ g^p < ⊤`, gives `eLpNorm (Fn n) p → 0`. Built from
`tendsto_lintegral_of_dominated_convergence'` the same way Mathlib's own
`tendsto_approxOn_Lp_eLpNorm` is. -/
theorem tendsto_eLpNorm_zero_of_dominated {p : ℝ} (hp0 : 0 < p) {Fn : ℕ → ℂ → ℂ}
    (hFnmeas : ∀ n, AEStronglyMeasurable (Fn n) volume) {g : ℂ → ℝ}
    (hbound : ∀ n, ∀ᵐ z ∂volume, ‖Fn n z‖ ≤ g z)
    (hgfin : (∫⁻ z, ENNReal.ofReal (g z) ^ p) ≠ ⊤)
    (hlim : ∀ᵐ z ∂volume, Tendsto (fun n => Fn n z) atTop (𝓝 (0 : ℂ))) :
    Tendsto (fun n => eLpNorm (Fn n) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hptoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  suffices h : Tendsto (fun n => ∫⁻ z, ‖Fn n z‖ₑ ^ p) atTop (𝓝 0) by
    have heq : ∀ n, eLpNorm (Fn n) (ENNReal.ofReal p) volume =
        (∫⁻ z, ‖Fn n z‖ₑ ^ (ENNReal.ofReal p).toReal) ^ (1 / (ENNReal.ofReal p).toReal) :=
      fun n => eLpNorm_eq_lintegral_rpow_enorm_toReal hpne hptop (hFnmeas n)
    simp only [heq, hptoReal]
    have hcomp := h.ennrpow_const (1 / p)
    simpa [one_div, ENNReal.zero_rpow_of_pos (by positivity : (0 : ℝ) < p⁻¹)] using hcomp
  have hFmeas : ∀ n, AEMeasurable (fun z => ‖Fn n z‖ₑ ^ p) volume := fun n =>
    (hFnmeas n).aemeasurable.enorm.pow_const p
  have hboundE : ∀ n, (fun z => ‖Fn n z‖ₑ ^ p) ≤ᵐ[volume] fun z => ENNReal.ofReal (g z) ^ p := by
    intro n
    filter_upwards [hbound n] with z hz
    exact ENNReal.rpow_le_rpow (by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hz) hp0.le
  have hlimE : ∀ᵐ z ∂volume, Tendsto (fun n => ‖Fn n z‖ₑ ^ p) atTop (𝓝 ((0 : ℝ≥0∞) ^ p)) := by
    filter_upwards [hlim] with z hz
    have henorm : Tendsto (fun n => ‖Fn n z‖ₑ) atTop (𝓝 (0 : ℝ≥0∞)) := by
      have h0 : ‖(0 : ℂ)‖ₑ = 0 := by simp
      rw [← h0]
      exact (continuous_enorm.tendsto (0 : ℂ)).comp hz
    exact henorm.ennrpow_const p
  have hmain := tendsto_lintegral_of_dominated_convergence' (fun z => ENNReal.ofReal (g z) ^ p)
    hFmeas hboundE hgfin hlimE
  simpa [ENNReal.zero_rpow_of_pos hp0] using hmain

/-- (12.10): `‖ωₙ − ω‖_p → 0` for a sequence of solutions `ωₙ` of (12.4) with coefficients
`μₙ → μ` a.e. and all supports in a common disc.

*Proof.*  `ωₙ − ω = μₙ H(ωₙ − ω) + (μₙ − μ)(1 + Hω)` a.e.; the contraction estimate
(as in `eq12_1_solution`, via (11.16) and the a.e. additivity of `H`) rearranges this into
`‖ωₙ − ω‖_p ≤ ‖(μₙ − μ)(1 + Hω)‖_p / (1 − kΛ_p)`, and the right side tends to `0` by dominated
convergence (`tendsto_eLpNorm_zero_of_dominated`), dominated by `2k(1 + Hω)` on the shared disc. -/
theorem eq12_1_solution_tendsto {μn : ℕ → ℂ → ℂ} {μ : ℂ → ℂ} {k p R : ℝ} (hk₀ : 0 ≤ k) (hp : 2 < p)
    (hkp : k * hilbertNorm p < 1) (hμn : ∀ n, IsBeltramiCoeff (μn n) univ k)
    (hμ : IsBeltramiCoeff μ univ k) (hsuppn : ∀ n z, R < ‖z‖ → μn n z = 0)
    (hsupp : ∀ z, R < ‖z‖ → μ z = 0) (hlim : ∀ᵐ z, Tendsto (fun n => μn n z) atTop (𝓝 (μ z)))
    {ωn : ℕ → ℂ → ℂ} {ω : ℂ → ℂ} (hωn : ∀ n, MemLp (ωn n) (ENNReal.ofReal p))
    (hsoln : ∀ n, ωn n =ᵐ[volume] fun z => μn n z * hilbertH (ωn n) z + μn n z)
    (hω : MemLp ω (ENNReal.ofReal p)) (hsol : ω =ᵐ[volume] fun z => μ z * hilbertH ω z + μ z) :
    Tendsto (fun n => eLpNorm (ωn n - ω) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hp1 : (1 : ℝ) < p := by linarith
  have hp1e : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1.le
  set R' := max R 1 with hR'def
  have hR' : (0 : ℝ) < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hle : R ≤ R' := le_max_left _ _
  have hsuppn' : ∀ n z, R' < ‖z‖ → μn n z = 0 := fun n z hz => hsuppn n z (lt_of_le_of_lt hle hz)
  have hsupp' : ∀ z, R' < ‖z‖ → μ z = 0 := fun z hz => hsupp z (lt_of_le_of_lt hle hz)
  have hμnbd : ∀ n, ∀ᵐ z ∂volume, ‖μn n z‖ ≤ k := fun n => by simpa using (hμn n).2
  have hμbd : ∀ᵐ z ∂volume, ‖μ z‖ ≤ k := by simpa using hμ.2
  have hμ'meas : AEStronglyMeasurable μ volume := by simpa using hμ.1
  have hμn'meas : ∀ n, AEStronglyMeasurable (μn n) volume := fun n => by simpa using (hμn n).1
  set Fn : ℕ → ℂ → ℂ := fun n z => (μn n z - μ z) * (1 + hilbertH ω z) with hFndef
  have hE1 : ∀ n, (fun z => ωn n z - ω z) =ᵐ[volume]
      fun z => μn n z * hilbertH (fun z => ωn n z - ω z) z + Fn n z := by
    intro n
    obtain ⟨A, hA0, hbound⟩ := zygmund_calderon hp1
    have hHsub := hilbertH_sub_ae_of_smooth_bound hp1 hbound (hωn n) hω
    filter_upwards [hsoln n, hsol, hHsub] with z hz1 hz2 hz3
    simp only [hFndef]
    rw [hz1, hz2, hz3]
    ring
  have hHωMemLp : MemLp (hilbertH ω) (ENNReal.ofReal p) := (hilbertH_memLp hp1 hω)
  haveI hfin' : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) R')) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have h1Hω : MemLp (fun z => (1 : ℂ) + hilbertH ω z) (ENNReal.ofReal p)
      (volume.restrict (closedBall (0 : ℂ) R')) :=
    (memLp_const (1 : ℂ)).add (hHωMemLp.restrict _)
  set gInd : ℂ → ℂ := (closedBall (0 : ℂ) R').indicator
      (fun z => (2 * k : ℝ) • ((1 : ℂ) + hilbertH ω z)) with hgInddef
  have hgMemLp : MemLp gInd (ENNReal.ofReal p) volume := by
    rw [hgInddef, memLp_indicator_iff_restrict measurableSet_closedBall.nullMeasurableSet]
    exact h1Hω.const_smul (2 * k : ℝ)
  have hp0 : (0 : ℝ) < p := by linarith
  have hgfin : (∫⁻ z, ENNReal.ofReal ‖gInd z‖ ^ p) ≠ ⊤ := by
    have hlt := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := ENNReal.ofReal p)
      (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top hgMemLp.eLpNorm_lt_top
    rw [ENNReal.toReal_ofReal hp0.le] at hlt
    simp only [ofReal_norm]
    exact hlt.ne
  have hE3 : Tendsto (fun n => eLpNorm (Fn n) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
    refine tendsto_eLpNorm_zero_of_dominated hp0 (g := fun z => ‖gInd z‖) ?_ ?_ hgfin ?_
    · intro n
      exact ((hμn'meas n).sub hμ'meas).mul (continuous_const.aestronglyMeasurable.add
        hHωMemLp.aestronglyMeasurable)
    · intro n
      filter_upwards [hμnbd n, hμbd] with z hzn hzμ
      rw [hFndef, hgInddef]
      simp only
      by_cases hzR : z ∈ closedBall (0 : ℂ) R'
      · rw [Set.indicator_of_mem hzR]
        rw [norm_mul]
        have h2 : ‖μn n z - μ z‖ ≤ 2 * k := by
          calc ‖μn n z - μ z‖ ≤ ‖μn n z‖ + ‖μ z‖ := norm_sub_le _ _
            _ ≤ k + k := add_le_add hzn hzμ
            _ = 2 * k := by ring
        calc ‖μn n z - μ z‖ * ‖1 + hilbertH ω z‖ ≤ (2 * k) * ‖1 + hilbertH ω z‖ :=
              mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
          _ = ‖(2 * k : ℝ) • ((1 : ℂ) + hilbertH ω z)‖ := by
              rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * k)]
      · rw [Set.indicator_of_notMem hzR]
        rw [mem_closedBall_zero_iff, not_le] at hzR
        rw [hsuppn' n z hzR, hsupp' z hzR, sub_self, zero_mul, norm_zero]
    · rw [hFndef]
      filter_upwards [hlim] with z hz
      have h1 : Tendsto (fun n => μn n z - μ z) atTop (𝓝 (0 : ℂ)) := by
        have := hz.sub (tendsto_const_nhds (x := μ z))
        simpa using this
      simpa using h1.mul_const (1 + hilbertH ω z)
  have hE2 : ∀ n, eLpNorm (fun z => ωn n z - ω z) (ENNReal.ofReal p) volume ≤
      eLpNorm (Fn n) (ENNReal.ofReal p) volume /
        ((1 : ℝ≥0∞) - ENNReal.ofReal (k * hilbertNorm p)) := by
    intro n
    have hAfin : eLpNorm (fun z => ωn n z - ω z) (ENNReal.ofReal p) volume ≠ ⊤ :=
      ((hωn n).sub hω).eLpNorm_ne_top
    have hHsubMemLp : MemLp (hilbertH (fun z => ωn n z - ω z)) (ENNReal.ofReal p) :=
      hilbertH_memLp hp1 ((hωn n).sub hω)
    have hmeas1 : AEStronglyMeasurable (fun z => μn n z * hilbertH (fun z => ωn n z - ω z) z)
        volume := (hμn'meas n).mul hHsubMemLp.aestronglyMeasurable
    have hmeas2 : AEStronglyMeasurable (Fn n) volume :=
      ((hμn'meas n).sub hμ'meas).mul (continuous_const.aestronglyMeasurable.add
        hHωMemLp.aestronglyMeasurable)
    have hbound2 : ∀ᵐ z ∂volume, ‖μn n z * hilbertH (fun z => ωn n z - ω z) z‖ ≤
        ‖(k : ℝ) • hilbertH (fun z => ωn n z - ω z) z‖ := by
      filter_upwards [hμnbd n] with z hzn
      simp only [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hk₀]
      exact mul_le_mul_of_nonneg_right hzn (norm_nonneg _)
    have hkenorm : ‖(k : ℝ)‖ₑ = ENNReal.ofReal k := by
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hk₀]
    have hstep : eLpNorm (fun z => ωn n z - ω z) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (k * hilbertNorm p) *
          eLpNorm (fun z => ωn n z - ω z) (ENNReal.ofReal p) volume +
        eLpNorm (Fn n) (ENNReal.ofReal p) volume := by
      calc eLpNorm (fun z => ωn n z - ω z) (ENNReal.ofReal p) volume
          = eLpNorm (fun z => μn n z * hilbertH (fun z => ωn n z - ω z) z + Fn n z)
              (ENNReal.ofReal p) volume := eLpNorm_congr_ae (hE1 n)
        _ ≤ eLpNorm (fun z => μn n z * hilbertH (fun z => ωn n z - ω z) z)
              (ENNReal.ofReal p) volume + eLpNorm (Fn n) (ENNReal.ofReal p) volume :=
            eLpNorm_add_le hp1e
        _ ≤ eLpNorm (fun z => (k : ℝ) • hilbertH (fun z => ωn n z - ω z) z)
              (ENNReal.ofReal p) volume + eLpNorm (Fn n) (ENNReal.ofReal p) volume :=
            add_le_add (eLpNorm_mono_ae hmeas1 hbound2) le_rfl
        _ = ENNReal.ofReal k * eLpNorm (hilbertH (fun z => ωn n z - ω z)) (ENNReal.ofReal p)
              volume + eLpNorm (Fn n) (ENNReal.ofReal p) volume := by
            congr 1
            rw [show (fun z => (k : ℝ) • hilbertH (fun z => ωn n z - ω z) z) =
              (k : ℝ) • hilbertH (fun z => ωn n z - ω z) from rfl, eLpNorm_const_smul, hkenorm]
        _ ≤ ENNReal.ofReal k * (ENNReal.ofReal (hilbertNorm p) *
              eLpNorm (fun z => ωn n z - ω z) (ENNReal.ofReal p) volume) +
              eLpNorm (Fn n) (ENNReal.ofReal p) volume := by
            gcongr
            exact eq11_16_eLpNorm hp1 ((hωn n).sub hω)
        _ = ENNReal.ofReal (k * hilbertNorm p) *
              eLpNorm (fun z => ωn n z - ω z) (ENNReal.ofReal p) volume +
              eLpNorm (Fn n) (ENNReal.ofReal p) volume := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hk₀]
    have hc0 : ENNReal.ofReal (k * hilbertNorm p) < 1 := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ) < 1)).2 hkp
    have hsub1 : (1 : ℝ≥0∞) - ENNReal.ofReal (k * hilbertNorm p) ≠ 0 :=
      tsub_pos_of_lt hc0 |>.ne'
    have hsub1top : (1 : ℝ≥0∞) - ENNReal.ofReal (k * hilbertNorm p) ≠ ⊤ :=
      (tsub_le_self.trans_lt ENNReal.one_lt_top).ne
    rw [ENNReal.le_div_iff_mul_le (Or.inl hsub1) (Or.inl hsub1top), mul_comm,
      ENNReal.sub_mul (fun _ _ => hAfin), one_mul, tsub_le_iff_right, add_comm]
    exact hstep
  have hc0 : ENNReal.ofReal (k * hilbertNorm p) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ) < 1)).2 hkp
  have hcinv_ne_top : ((1 : ℝ≥0∞) - ENNReal.ofReal (k * hilbertNorm p))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (tsub_pos_of_lt hc0).ne'
  have hdiv0 : Tendsto (fun n => eLpNorm (Fn n) (ENNReal.ofReal p) volume /
      ((1 : ℝ≥0∞) - ENNReal.ofReal (k * hilbertNorm p))) atTop (𝓝 0) := by
    have hmul := ENNReal.Tendsto.const_mul hE3 (Or.inr hcinv_ne_top)
    simp only [mul_zero] at hmul
    simpa [ENNReal.div_eq_inv_mul, mul_comm] using hmul
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiv0
    (Eventually.of_forall fun n => bot_le) (Eventually.of_forall hE2)

/-- The `cauchyT` form of (12.10): `T(ωₙ) → T(ω)` *uniformly* on `ℂ`.

*Proof.*  Transport to bounded-support representatives via `t2_omega_ae_eq_indicator` and
`cauchyT_congr_ae`; `cauchyT_sub` splits the difference, and Lemma 11.1 gives a *uniform* bound
by `M₁ · ‖ωₙ − ω‖_p`, which tends to `0` by `eq12_1_solution_tendsto`. -/
theorem eq12_1_solution_tendsto_cauchyT {μn : ℕ → ℂ → ℂ} {μ : ℂ → ℂ} {k p R : ℝ} (hk₀ : 0 ≤ k)
    (hp : 2 < p) (hkp : k * hilbertNorm p < 1) (hμn : ∀ n, IsBeltramiCoeff (μn n) univ k)
    (hμ : IsBeltramiCoeff μ univ k) (hsuppn : ∀ n z, R < ‖z‖ → μn n z = 0)
    (hsupp : ∀ z, R < ‖z‖ → μ z = 0) (hlim : ∀ᵐ z, Tendsto (fun n => μn n z) atTop (𝓝 (μ z)))
    {ωn : ℕ → ℂ → ℂ} {ω : ℂ → ℂ} (hωn : ∀ n, MemLp (ωn n) (ENNReal.ofReal p))
    (hsoln : ∀ n, ωn n =ᵐ[volume] fun z => μn n z * hilbertH (ωn n) z + μn n z)
    (hω : MemLp ω (ENNReal.ofReal p)) (hsol : ω =ᵐ[volume] fun z => μ z * hilbertH ω z + μ z) :
    TendstoUniformly (fun n => cauchyT (ωn n)) (cauchyT ω) atTop := by
  have hR' : (0 : ℝ) < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hle : R ≤ max R 1 := le_max_left _ _
  have hsuppn' : ∀ n z, max R 1 < ‖z‖ → μn n z = 0 := fun n z hz => hsuppn n z (lt_of_le_of_lt hle hz)
  have hsupp' : ∀ z, max R 1 < ‖z‖ → μ z = 0 := fun z hz => hsupp z (lt_of_le_of_lt hle hz)
  set ωnR : ℕ → ℂ → ℂ := fun n => (closedBall (0 : ℂ) (max R 1)).indicator (ωn n) with hωnRdef
  set ωR : ℂ → ℂ := (closedBall (0 : ℂ) (max R 1)).indicator ω with hωRdef
  have hωnRas : ∀ n, ωn n =ᵐ[volume] ωnR n := fun n =>
    t2_omega_ae_eq_indicator (hsuppn' n) (hsoln n)
  have hωRas : ω =ᵐ[volume] ωR := t2_omega_ae_eq_indicator hsupp' hsol
  have hωnRmem : ∀ n, MemLp (ωnR n) (ENNReal.ofReal p) := fun n =>
    (hωn n).indicator measurableSet_closedBall.nullMeasurableSet
  have hωRmem : MemLp ωR (ENNReal.ofReal p) := hω.indicator measurableSet_closedBall.nullMeasurableSet
  have hωnRsupp : ∀ n, ∀ z : ℂ, max R 1 < ‖z‖ → ωnR n z = 0 := fun n z hz =>
    Set.indicator_of_notMem (by simpa [mem_closedBall_zero_iff, not_le] using hz) _
  have hωRsupp : ∀ z : ℂ, max R 1 < ‖z‖ → ωR z = 0 := fun z hz =>
    Set.indicator_of_notMem (by simpa [mem_closedBall_zero_iff, not_le] using hz) _
  have hcTn : ∀ n, cauchyT (ωn n) = cauchyT (ωnR n) := fun n => cauchyT_congr_ae (hωnRas n)
  have hcT : cauchyT ω = cauchyT ωR := cauchyT_congr_ae hωRas
  have hsubeq : ∀ n, cauchyT (fun z => ωnR n z - ωR z) = fun z => cauchyT (ωnR n) z - cauchyT ωR z :=
    fun n => cauchyT_sub hp hR' (hωnRmem n) hωRmem (hωnRsupp n) hωRsupp
  have hdiffeLp : Tendsto (fun n => eLpNorm (fun z => ωnR n z - ωR z) (ENNReal.ofReal p) volume)
      atTop (𝓝 0) := by
    have hcong : ∀ n, (fun z => ωnR n z - ωR z) =ᵐ[volume] fun z => ωn n z - ω z := fun n => by
      filter_upwards [hωnRas n, hωRas] with z hz1 hz2
      rw [← hz1, ← hz2]
    have := eq12_1_solution_tendsto hk₀ hp hkp hμn hμ hsuppn hsupp hlim hωn hsoln hω hsol
    refine this.congr' (Eventually.of_forall fun n => ?_)
    exact (eLpNorm_congr_ae (hcong n)).symm
  obtain ⟨M₁, hM₁⟩ := lemma11_1 hp hR'
  have h0 : Tendsto (fun n => M₁ * (eLpNorm (fun z => ωnR n z - ωR z)
      (ENNReal.ofReal p) volume).toReal) atTop (𝓝 0) := by
    have hc := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hdiffeLp
    have h0' : Tendsto (fun n => (eLpNorm (fun z => ωnR n z - ωR z)
        (ENNReal.ofReal p) volume).toReal) atTop (𝓝 0) := by
      simpa [Function.comp_def] using hc
    simpa using h0'.const_mul M₁
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [h0.eventually (gt_mem_nhds hε)] with n hn
  intro z
  rw [dist_eq_norm, norm_sub_rev, hcTn n, hcT, ← congrFun (hsubeq n) z]
  exact lt_of_le_of_lt (hM₁ _ ((hωnRmem n).sub hωRmem)
    (fun z hz => by
      show ωnR n z - ωR z = 0
      rw [hωnRsupp n z hz, hωRsupp z hz, sub_zero]) z) hn

/-- `cauchyT ω` is bounded on `ℂ` for any `L_p` solution `ω` of (12.4). -/
theorem cauchyT_bounded_of_solution {μ ω : ℂ → ℂ} {k p : ℝ} (hμ : IsCompactBeltramiCoeff μ k)
    (hp : 2 < p) (hω : MemLp ω (ENNReal.ofReal p))
    (hsol : ω =ᵐ[volume] fun z => μ z * hilbertH ω z + μ z) :
    ∃ M : ℝ, ∀ z, ‖cauchyT ω z‖ ≤ M := by
  obtain ⟨R, hR0⟩ := hμ.2
  obtain ⟨R', hR', hRR'⟩ : ∃ R' : ℝ, 0 < R' ∧ ∀ z : ℂ, R' < ‖z‖ → μ z = 0 :=
    ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _),
      fun z hz => hR0 z (lt_of_le_of_lt (le_max_left R 1) hz)⟩
  set omR : ℂ → ℂ := (closedBall (0 : ℂ) R').indicator ω with homRdef
  have homs : ω =ᵐ[volume] omR := t2_omega_ae_eq_indicator hRR' hsol
  have hcT : cauchyT ω = cauchyT omR := cauchyT_congr_ae homs
  have homRmem : MemLp omR (ENNReal.ofReal p) := hω.indicator measurableSet_closedBall.nullMeasurableSet
  have homRsupp : ∀ z : ℂ, R' < ‖z‖ → omR z = 0 := by
    intro z hz
    rw [homRdef]
    exact indicator_of_notMem (by rwa [mem_closedBall_zero_iff, not_le]) _
  obtain ⟨M₁, hM₁⟩ := lemma11_1 hp hR'
  exact ⟨M₁ * (eLpNorm omR (ENNReal.ofReal p)).toReal, fun z => by
    rw [hcT]
    exact hM₁ omR homRmem homRsupp z⟩

/-- The successive approximations `ω₀ = h`, `ωₙ = μ H(ωₙ₋₁) + h` of §12.1. -/
def neumannIter (μ h : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => h
  | n + 1 => fun z => μ z * hilbertH (neumannIter μ h n) z + h z

/-- (12.2): the successive approximations converge in `L_p` to the solution of (12.1), which
is therefore `ω = h + μH(h) + μH(μH(h)) + ⋯`. -/
theorem eq12_2_neumann {μ h ω : ℂ → ℂ} {k p : ℝ} (hk₀ : 0 ≤ k) (hμ : IsBeltramiCoeff μ univ k)
    (hp : 2 < p) (hkp : k * hilbertNorm p < 1) (hh : MemLp h (ENNReal.ofReal p))
    (hω : MemLp ω (ENNReal.ofReal p)) (hsol : ω =ᵐ[volume] fun z => μ z * hilbertH ω z + h z) :
    Tendsto (fun n => eLpNorm (fun z => neumannIter μ h n z - ω z) (ENNReal.ofReal p)) atTop
      (𝓝 0) := by
  have hp1 : 1 < p := lt_trans one_lt_two hp
  have hstep : ∀ n : ℕ, neumannIter μ h (n + 1) = fun z => μ z * hilbertH (neumannIter μ h n) z + h z :=
    fun n => funext fun z => rfl
  have hzero : neumannIter μ h 0 = h := funext fun z => rfl
  -- MemLp for every iterate
  have hMemLp : ∀ n, MemLp (neumannIter μ h n) (ENNReal.ofReal p) := by
    intro n
    induction n with
    | zero => rw [hzero]; exact hh
    | succ n ih =>
      rw [hstep]
      exact phiMap_memLp hμ hp1 hh ih
  -- the contraction bound by induction
  have hbound : ∀ n, eLpNorm (fun z => neumannIter μ h n z - ω z) (ENNReal.ofReal p) ≤
      (ENNReal.ofReal (k * hilbertNorm p)) ^ n * eLpNorm (fun z => h z - ω z) (ENNReal.ofReal p) := by
    intro n
    induction n with
    | zero =>
      have heq : (fun z => neumannIter μ h 0 z - ω z) = fun z => h z - ω z := by
        rw [hzero]
      rw [heq, pow_zero, one_mul]
    | succ n ih =>
      have heq1 : (fun z => neumannIter μ h (n + 1) z - ω z) =
          fun z => (μ z * hilbertH (neumannIter μ h n) z + h z) - ω z := by
        rw [hstep]
      have hcong : (fun z => (μ z * hilbertH (neumannIter μ h n) z + h z) - ω z) =ᵐ[volume]
          fun z => (μ z * hilbertH (neumannIter μ h n) z + h z) -
            (μ z * hilbertH ω z + h z) := by
        filter_upwards [hsol] with z hz
        rw [hz]
      rw [heq1, eLpNorm_congr_ae hcong]
      have hstep1 : eLpNorm (fun z => (μ z * hilbertH (neumannIter μ h n) z + h z) -
            (μ z * hilbertH ω z + h z)) (ENNReal.ofReal p) ≤
          (ENNReal.ofReal (k * hilbertNorm p)) *
            eLpNorm (fun z => neumannIter μ h n z - ω z) (ENNReal.ofReal p) :=
        phiMap_sub_bound hk₀ hμ hp1 (hMemLp n) hω
      have hstep2 : (ENNReal.ofReal (k * hilbertNorm p)) *
            eLpNorm (fun z => neumannIter μ h n z - ω z) (ENNReal.ofReal p) ≤
          (ENNReal.ofReal (k * hilbertNorm p)) *
            ((ENNReal.ofReal (k * hilbertNorm p)) ^ n *
              eLpNorm (fun z => h z - ω z) (ENNReal.ofReal p)) :=
        mul_le_mul_right ih (ENNReal.ofReal (k * hilbertNorm p))
      have hstep3 : (ENNReal.ofReal (k * hilbertNorm p)) *
            ((ENNReal.ofReal (k * hilbertNorm p)) ^ n *
              eLpNorm (fun z => h z - ω z) (ENNReal.ofReal p)) =
          (ENNReal.ofReal (k * hilbertNorm p)) ^ (n + 1) *
            eLpNorm (fun z => h z - ω z) (ENNReal.ofReal p) := by
        rw [← mul_assoc, ← pow_succ']
      exact hstep3 ▸ (hstep1.trans hstep2)
  -- (ENNReal.ofReal (k * hilbertNorm p)) < 1
  have hcpos : 0 ≤ k * hilbertNorm p := mul_nonneg hk₀ (hilbertNorm_nonneg p)
  have hc1 : (ENNReal.ofReal (k * hilbertNorm p)) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hcpos |>.mpr hkp
  -- eLpNorm (h - ω) < ⊤
  have hhωlt : eLpNorm (fun z => h z - ω z) (ENNReal.ofReal p) < ⊤ := (hh.sub hω).eLpNorm_lt_top
  -- pow tendsto 0
  have hpow : Tendsto (fun n => (ENNReal.ofReal (k * hilbertNorm p)) ^ n) atTop (𝓝 0) := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc1
  have hmulTendsto : Tendsto (fun n => (ENNReal.ofReal (k * hilbertNorm p)) ^ n * eLpNorm (fun z => h z - ω z) (ENNReal.ofReal p))
      atTop (𝓝 (0 * eLpNorm (fun z => h z - ω z) (ENNReal.ofReal p))) :=
    ENNReal.Tendsto.mul_const hpow (Or.inr hhωlt.ne)
  rw [zero_mul] at hmulTendsto
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmulTendsto
    (Eventually.of_forall fun n => bot_le) (Eventually.of_forall hbound)

theorem l121_isLocalHomeomorph {w : ℂ → ℂ} (hw : Continuous w)
    (hloc : ∀ z₀ : ℂ, ∃ U ∈ 𝓝 z₀, InjOn w U) : IsLocalHomeomorph w := by
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ, isLocalHomeomorphOn_iff_isOpenEmbedding_restrict]
  intro z₀ _
  obtain ⟨U, hU, hi⟩ := hloc z₀
  obtain ⟨U', hU'U, hU'o, hz₀U'⟩ := _root_.mem_nhds_iff.mp hU
  have hi' : InjOn w U' := hi.mono hU'U
  refine ⟨U', hU'o.mem_nhds hz₀U', ?_⟩
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact hw.continuousOn.domRestrict
  · exact hi'.injective
  · intro s hs
    obtain ⟨V, hVo, hVU'⟩ := isOpen_induced_iff.mp hs
    have hVU'' : Subtype.val '' s = V ∩ U' := by
      rw [← hVU']
      ext x
      simp only [mem_image, mem_preimage, Subtype.exists, exists_and_left, exists_prop]
      constructor
      · rintro ⟨y, hy, hyU', rfl⟩
        exact ⟨hy, hyU'⟩
      · rintro ⟨hxV, hxU'⟩
        exact ⟨x, hxV, hxU', rfl⟩
    have heq : U'.domRestrict w '' s = w '' (Subtype.val '' s) := by
      rw [Set.image_image]
      rfl
    rw [heq, hVU'']
    exact isOpen_image_of_continuousOn_injOn_of_subset hU'o hw.continuousOn hi'
      Set.inter_subset_right (hVo.inter hU'o)

theorem l121_isProperMap {w : ℂ → ℂ} (hw : Continuous w)
    (hinf : Tendsto w (cocompact ℂ) (cocompact ℂ)) : IsProperMap w :=
  isProperMap_iff_tendsto_cocompact.mpr ⟨hw, hinf⟩

theorem l121_finite_fiber {w : ℂ → ℂ} (hloc : IsLocalHomeomorph w) (hprop : IsProperMap w)
    (y : ℂ) : (w ⁻¹' {y}).Finite := by
  have hdisc : IsDiscrete (w ⁻¹' {y}) :=
    IsDiscrete.of_openPartialHomeomorph w subset_rfl
      (fun e _ => let ⟨φ, hφ, hφe⟩ := hloc e; ⟨φ, hφ, hφe.symm⟩)
  exact (hprop.isCompact_preimage isCompact_singleton).finite hdisc

theorem l121_isCoveringMap {w : ℂ → ℂ} (hloc : IsLocalHomeomorph w) (hprop : IsProperMap w) :
    IsCoveringMap w := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  refine hprop.isClosedMap.isCoveringMapOn_of_openPartialHomeomorph (fun y _ => ?_) (fun e _ => ?_)
  · exact l121_finite_fiber hloc hprop y
  · obtain ⟨φ, hφ, hφe⟩ := hloc e
    exact ⟨φ, hφ, hφe⟩

theorem l121_bijective {w : ℂ → ℂ} (hloc : IsLocalHomeomorph w) (hcov : IsCoveringMap w) :
    Function.Bijective w := by
  obtain ⟨G, ⟨hG0, hGg⟩, -⟩ :=
    hcov.existsUnique_continuousMap_lifts (ContinuousMap.id ℂ) (w 0) 0 rfl
  have hwG : ∀ y, w (G y) = y := fun y => by
    have := congrFun hGg y
    simpa using this
  have hGw : ∀ x, G (w x) = x := by
    have h : (G ∘ w) = (id : ℂ → ℂ) :=
      hcov.eq_of_comp_eq (G.continuous.comp hloc.continuous) continuous_id
        (by funext x; show w (G (w x)) = w x; rw [hwG]) 0 (by show G (w 0) = 0; exact hG0)
    exact fun x => congrFun h x
  refine ⟨fun x y hxy => ?_, fun y => ⟨G y, hwG y⟩⟩
  rw [← hGw x, ← hGw y, hxy]

/-- **Lemma 12.1**: a continuous map `w : ℂ → ℂ` with `w(z) → ∞` as `z → ∞`, which is injective
in a neighbourhood of every point, is a homeomorphism of `ℂ` onto itself.

Proved via invariance of domain (continuity + local injectivity ⇒ local homeomorphism), properness
⇒ covering map, and simple connectedness of `ℂ` ⇒ bijectivity of the covering map, assembled by
`IsLocalHomeomorph.toHomeomorphOfBijective`. -/
theorem lemma12_1 {w : ℂ → ℂ} (hw : Continuous w) (hinf : Tendsto w (cocompact ℂ) (cocompact ℂ))
    (hloc : ∀ z₀ : ℂ, ∃ U ∈ 𝓝 z₀, InjOn w U) : ∃ e : ℂ ≃ₜ ℂ, ⇑e = w := by
  have hlh : IsLocalHomeomorph w := l121_isLocalHomeomorph hw hloc
  have hprop : IsProperMap w := l121_isProperMap hw hinf
  have hcov : IsCoveringMap w := l121_isCoveringMap hlh hprop
  have hbij : Function.Bijective w := l121_bijective hlh hcov
  exact ⟨hlh.toHomeomorphOfBijective hbij, rfl⟩

/-- `IsKQC` restricts from `D` to an open subset `U ⊆ D`. -/
theorem t3b_isKQC_restrict {f : ℂ → ℂ} {D U : Set ℂ} {K : ℝ} (hf : IsKQC f D K)
    (hUo : IsOpen U) (hUD : U ⊆ D) : IsKQC f U K := by
  obtain ⟨hDo, hK1, hhom, hquad⟩ := hf
  obtain ⟨hc, hi, -, hinv⟩ := hhom
  refine ⟨hUo, hK1, ⟨hc.mono hUD, hi.mono hUD, rfl, ?_⟩, fun Q hQ => hquad Q (hQ.trans (image_mono hUD))⟩
  have heq : Set.EqOn (Function.invFunOn f U) (Function.invFunOn f D) (f '' U) := by
    intro w hw
    obtain ⟨z, hzU, rfl⟩ := hw
    have h1 : Function.invFunOn f U (f z) = z := (hi.mono hUD).leftInvOn_invFunOn hzU
    have h2 : Function.invFunOn f D (f z) = z := hi.leftInvOn_invFunOn (hUD hzU)
    rw [h1, h2]
  exact (hinv.mono (image_mono hUD)).congr heq

/-- A `K`-q.c. map sends open subsets of its domain to open sets. -/
theorem t3b_isOpenMap {f : ℂ → ℂ} {D U : Set ℂ} {K : ℝ} (hf : IsKQC f D K) (hUD : U ⊆ D)
    (hUo : IsOpen U) : IsOpen (f '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨z, hzU, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hUo z hzU
  set ε : ℝ := r / 4 with hεdef
  have hε : 0 < ε := by positivity
  have hdistbound : ∀ p : ℂ, |p.re - z.re| ≤ ε → |p.im - z.im| ≤ ε → dist p z < r := by
    intro p h1 h2
    have h3 : dist p z = ‖p - z‖ := Complex.dist_eq p z
    have h4 : (p - z).re = p.re - z.re := by simp
    have h5 : (p - z).im = p.im - z.im := by simp
    calc dist p z = ‖p - z‖ := h3
      _ ≤ |(p - z).re| + |(p - z).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ ε + ε := by rw [h4, h5]; linarith
      _ < r := by rw [hεdef]; linarith
  obtain ⟨Q, hQdom, -, -, -⟩ := acl_exists_rectQuad (x' := z.re - ε) (x'' := z.re + ε)
    (t := z.im - ε) (h := 2 * ε) (by linarith) (by linarith)
  have hQdom' : Q.dom = openRect (z.re - ε) (z.re + ε) (z.im - ε) (z.im + ε) := by
    rw [hQdom]; ring_nf
  have hQU : Q.dom ⊆ U := by
    rw [hQdom']
    intro p hp
    simp only [openRect, mem_setOf_eq] at hp
    refine hball ?_
    rw [mem_ball]
    refine hdistbound p ?_ ?_
    · rw [abs_le]; constructor <;> linarith [hp.1, hp.2.1]
    · rw [abs_le]; constructor <;> linarith [hp.2.2.1, hp.2.2.2]
  have hQD : closure (toExt Q.dom) ⊆ toExt D := by
    rw [scExt_closure_toExt_of_isBounded (hQdom' ▸ acl_isBounded_openRect _ _ _ _)]
    refine image_mono (fun p hp => hUD (hball ?_))
    rw [hQdom'] at hp
    have hp' : p ∈ closedRect (z.re - ε) (z.re + ε) (z.im - ε) (z.im + ε) :=
      acl_closure_openRect_subset _ _ _ _ (hQdom' ▸ hp)
    simp only [closedRect, mem_setOf_eq] at hp'
    rw [mem_ball]
    refine hdistbound p ?_ ?_
    · rw [abs_le]; constructor <;> linarith [hp'.1, hp'.2.1]
    · rw [abs_le]; constructor <;> linarith [hp'.2.2.1, hp'.2.2.2]
  obtain ⟨Q', hQ', -⟩ := hf.2.2.2 Q hQD
  have hQ'dom : Q'.dom = f '' Q.dom := hQ'.1
  have hQ'o : IsOpen Q'.dom := Q'.isTopQuad.1.1
  have hzQ : z ∈ Q.dom := by
    rw [hQdom']
    simp only [openRect, mem_setOf_eq]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hmem : f z ∈ Q'.dom := hQ'dom ▸ mem_image_of_mem f hzQ
  have hsub : Q'.dom ⊆ f '' U := hQ'dom ▸ image_mono hQU
  exact mem_of_superset (hQ'o.mem_nhds hmem) hsub

/-- A set whose extended closure avoids `∞` is bounded. -/
theorem t3b_bounded_of_closure_toExt_subset_univ {S : Set ℂ}
    (h : closure (toExt S) ⊆ toExt univ) : Bornology.IsBounded S := by
  by_contra hub
  have hinf : extInf ∈ closure (toExt S) := by
    rw [mem_closure_iff_nhds_basis OnePoint.hasBasis_nhds_infty]
    intro s hs
    obtain ⟨-, hsK⟩ := hs
    have hns : ¬ (S ⊆ s) := fun hSs => hub (hsK.isBounded.subset hSs)
    obtain ⟨x, hxS, hxs⟩ := not_subset.1 hns
    exact ⟨(x : ExtPlane), mem_image_of_mem _ hxS, Or.inl ⟨x, hxs, rfl⟩⟩
  obtain ⟨y, -, hy⟩ := h hinf
  exact (OnePoint.infty_ne_coe y) hy.symm

/-- A `K`-q.c. map on every ball around `0`, that is also globally continuous, injective
and open, is `K`-q.c. on the whole plane. -/
theorem t3b_isKQC_univ_of_balls {w : ℂ → ℂ} {K : ℝ} (hK : 1 ≤ K)
    (hballs : ∀ R : ℝ, 0 < R → IsKQC w (ball 0 R) K) (hcont : Continuous w)
    (hinj : Function.Injective w) (hopen : IsOpenMap w) : IsKQC w univ K := by
  have hemb : IsOpenEmbedding w :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hopen
  haveI : Nonempty ℂ := ⟨0⟩
  set e := hemb.toOpenPartialHomeomorph w with hedef
  have hleft : ∀ x : ℂ, e.symm (w x) = x := fun x => hemb.toOpenPartialHomeomorph_left_inv w
  have htarget : e.target = range w := hedef ▸ hemb.toOpenPartialHomeomorph_target w
  refine ⟨isOpen_univ, hK, ⟨hcont.continuousOn, hinj.injOn, rfl, ?_⟩, fun Q hQ => ?_⟩
  · have heq : Set.EqOn (Function.invFunOn w univ) e.symm (w '' univ) := by
      rintro y ⟨x, -, rfl⟩
      rw [hinj.injOn.leftInvOn_invFunOn (mem_univ x), hleft x]
    refine (e.continuousOn_symm.mono ?_).congr heq
    rw [htarget, Set.image_univ]
  · have hbdd : Bornology.IsBounded Q.dom :=
      t3b_bounded_of_closure_toExt_subset_univ hQ
    obtain ⟨R, hR0, hRsub⟩ := hbdd.subset_ball_lt 0 (0 : ℂ)
    have hcl : closure (toExt Q.dom) ⊆ toExt (ball 0 (R + 1)) := by
      rw [scExt_closure_toExt_of_isBounded hbdd]
      refine image_mono ?_
      calc closure Q.dom ⊆ closure (ball (0 : ℂ) R) := closure_mono hRsub
        _ = closedBall 0 R := closure_ball 0 hR0.ne'
        _ ⊆ ball 0 (R + 1) := closedBall_subset_ball (by linarith)
    exact (hballs (R + 1) (by linarith)).2.2.2 Q hcl

/-- A continuous, injective, open, proper self-map of `ℂ` is a homeomorphism. -/
theorem t3b_homeomorph_of_open_proper {w : ℂ → ℂ} (hcont : Continuous w)
    (hinj : Function.Injective w) (hopen : IsOpenMap w)
    (hprop : Tendsto w (Filter.cocompact ℂ) (Filter.cocompact ℂ)) :
    ∃ e : ℂ ≃ₜ ℂ, ⇑e = w := by
  have hproper : IsProperMap w := isProperMap_iff_tendsto_cocompact.2 ⟨hcont, hprop⟩
  have hclosed : IsClosedMap w := (isProperMap_iff_isClosedMap_and_compact_fibers.1 hproper).2.1
  have hclopen : IsClopen (w '' univ) := ⟨hclosed univ isClosed_univ, hopen univ isOpen_univ⟩
  have hsurj : w '' univ = univ := hclopen.eq_univ ⟨w 0, mem_image_of_mem w (mem_univ 0)⟩
  have hemb : IsOpenEmbedding w :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hopen
  haveI : Nonempty ℂ := ⟨0⟩
  set e := hemb.toOpenPartialHomeomorph w with hedef
  have hsource : e.source = (univ : Set ℂ) := rfl
  have htarget0 : e.target = range w := hemb.toOpenPartialHomeomorph_target w
  have htarget : e.target = (univ : Set ℂ) := by
    rw [htarget0, ← Set.image_univ, hsurj]
  refine ⟨e.toHomeomorphOfSourceEqUnivTargetEqUniv hsource htarget, funext fun x => ?_⟩
  show e x = w x
  rw [hedef]
  exact congrFun (hemb.toOpenPartialHomeomorph_apply w) x

/-- A locally uniform, proper limit of `K`-q.c. self-maps of `ℂ` is `K`-q.c. and a
homeomorphism.

Not proved (kept as `sorry`): via `thm8_2_limit` only. -/
theorem t3b_limit {wn : ℕ → ℂ → ℂ} {w : ℂ → ℂ} {K : ℝ} (hK : 1 ≤ K)
    (hqc : ∀ n, IsKQC (wn n) univ K) (hlim : TendstoLocallyUniformly wn w atTop)
    (hprop : Tendsto w (Filter.cocompact ℂ) (Filter.cocompact ℂ)) :
    IsKQC w univ K ∧ ∃ e : ℂ ≃ₜ ℂ, ⇑e = w := by
  have hqcR : ∀ R : ℝ, 0 < R → ∀ n, IsKQC (wn n) (ball 0 R) K :=
    fun R _ n => t3b_isKQC_restrict (hqc n) isOpen_ball (subset_univ _)
  have hlimR : ∀ R : ℝ, TendstoLocallyUniformlyOn wn w atTop (ball 0 R) :=
    fun R => hlim.tendstoLocallyUniformlyOn
  have hkey : ∀ R : ℝ, 0 < R →
      (∃ c : ℂ, ∀ z ∈ ball (0 : ℂ) R, w z = c) ∨ IsKQC w (ball 0 R) K :=
    fun R hR => thm8_2_limit (isBounded_ball) (isConnected_ball hR) (hqcR R hR) (hlimR R)
  -- a globally constant `w` contradicts properness
  have hnotconst : ∀ c : ℂ, ¬ (∀ z, w z = c) := by
    intro c hc
    have h1 : {c}ᶜ ∈ Filter.cocompact ℂ := isCompact_singleton.compl_mem_cocompact
    have h2 : w ⁻¹' {c}ᶜ ∈ Filter.cocompact ℂ := hprop h1
    have h3 : w ⁻¹' {c}ᶜ = ∅ := by ext x; simp [hc x]
    rw [h3] at h2
    exact (Filter.cocompact_neBot_iff.2 inferInstance : (Filter.cocompact ℂ).NeBot).ne'
      (Filter.empty_mem_iff_bot.1 h2)
  -- so some ball has the `IsKQC` branch
  have hex : ∃ R : ℝ, 0 < R ∧ IsKQC w (ball 0 R) K := by
    by_contra hcon
    push Not at hcon
    have hallconst : ∀ R : ℝ, 0 < R → ∃ c : ℂ, ∀ z ∈ ball (0 : ℂ) R, w z = c := by
      intro R hR
      rcases hkey R hR with h | h
      · exact h
      · exact absurd h (hcon R hR)
    have hw0 : ∀ z : ℂ, w z = w 0 := by
      intro z
      obtain ⟨c, hc⟩ := hallconst (‖z‖ + 1) (by positivity)
      have hz : z ∈ ball (0 : ℂ) (‖z‖ + 1) := by simp [mem_ball]
      have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (‖z‖ + 1) := by simp [mem_ball]; positivity
      rw [hc z hz, hc 0 h0]
    exact hnotconst (w 0) hw0
  obtain ⟨R₀, hR₀, hQC₀⟩ := hex
  have hne2 : ∃ x y : ℂ, x ∈ ball (0 : ℂ) R₀ ∧ y ∈ ball (0 : ℂ) R₀ ∧ x ≠ y := by
    refine ⟨0, (R₀ / 2 : ℝ), mem_ball_self hR₀, ?_, ?_⟩
    · simp only [mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < R₀ / 2)]
      linarith
    · intro h
      have : (R₀ / 2 : ℝ) = 0 := Complex.ofReal_eq_zero.mp h.symm
      linarith
  have hnotconst0 : ¬ (∃ c : ℂ, ∀ z ∈ ball (0 : ℂ) R₀, w z = c) := by
    rintro ⟨c, hc⟩
    obtain ⟨x, y, hx, hy, hxy⟩ := hne2
    obtain ⟨-, -, hhom, -⟩ := hQC₀
    exact hxy (hhom.2.1 hx hy ((hc x hx).trans (hc y hy).symm))
  -- so `IsKQC w (ball 0 R) K` holds for every `R ≥ R₀`, hence for every `R > 0`
  have hallQC : ∀ R : ℝ, 0 < R → IsKQC w (ball 0 R) K := by
    intro R hR
    rcases le_or_gt R₀ R with hle | hlt
    · rcases hkey R hR with h | h
      · exact absurd (h.imp fun c hc => fun z hz => hc z (ball_subset_ball hle hz)) hnotconst0
      · exact h
    · exact t3b_isKQC_restrict hQC₀ isOpen_ball (ball_subset_ball hlt.le)
  have hcont : Continuous w := by
    rw [continuous_iff_continuousAt]
    intro z
    have hz : z ∈ ball (0 : ℂ) (‖z‖ + 1) := by simp [mem_ball]
    obtain ⟨-, -, hhom, -⟩ := hallQC (‖z‖ + 1) (by positivity)
    exact ((hhom.1.continuousAt (isOpen_ball.mem_nhds hz)))
  have hinj : Function.Injective w := by
    intro x y hxy
    set R : ℝ := max ‖x‖ ‖y‖ + 1 with hRdef
    have hR : 0 < R := by positivity
    have hxR : x ∈ ball (0 : ℂ) R := by
      simp only [mem_ball, dist_zero_right, hRdef]
      exact lt_of_le_of_lt (le_max_left _ _) (by linarith)
    have hyR : y ∈ ball (0 : ℂ) R := by
      simp only [mem_ball, dist_zero_right, hRdef]
      exact lt_of_le_of_lt (le_max_right _ _) (by linarith)
    obtain ⟨-, -, hhom, -⟩ := hallQC R hR
    exact hhom.2.1 hxR hyR hxy
  have hopen : IsOpenMap w := by
    intro U hU
    rw [isOpen_iff_mem_nhds]
    rintro w' ⟨z, hzU, rfl⟩
    obtain ⟨R, hR, hRz⟩ : ∃ R : ℝ, 0 < R ∧ z ∈ ball (0 : ℂ) R := ⟨‖z‖ + 1, by positivity, by simp [mem_ball]⟩
    have hUR : IsOpen (U ∩ ball 0 R) := hU.inter isOpen_ball
    have hzUR : z ∈ U ∩ ball 0 R := ⟨hzU, hRz⟩
    have hopenimg : IsOpen (w '' (U ∩ ball 0 R)) :=
      t3b_isOpenMap (hallQC R hR) inter_subset_right hUR
    exact mem_of_superset (hopenimg.mem_nhds (mem_image_of_mem w hzUR))
      (image_mono inter_subset_left)
  have hKQC : IsKQC w univ K := t3b_isKQC_univ_of_balls hK hallQC hcont hinj hopen
  obtain ⟨e, he⟩ := t3b_homeomorph_of_open_proper hcont hinj hopen hprop
  exact ⟨hKQC, e, he⟩

/-- The strengthened smooth case gives a `C¹` quasiconformal (hence `K`-q.c.) global solution.

Not proved (kept as `sorry`): via `thm6_1_modulus_quasi_invariance` only (through
`isKQC_of_isC1Quasiconformal`). -/
theorem t3b_isKQC_smooth {w μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : ∀ z, ‖μ z‖ ≤ k)
    (hCD : ContDiff ℝ 1 w) (hbeltrami : ∀ z, dzbar w z = μ z * dz w z)
    (hJ : ∀ z, 0 < jacobian w z) (he : ∃ e : ℂ ≃ₜ ℂ, ⇑e = w) :
    IsKQC w univ ((1 + k) / (1 - k)) := by
  apply isKQC_of_isC1Quasiconformal
  obtain ⟨e, he'⟩ := he
  have hbij : Function.Bijective w := he' ▸ e.bijective
  have hsurj : w '' univ = univ := by rw [← he', Set.image_univ, e.surjective.range_eq]
  have heq : ∀ y, Function.invFunOn w univ y = e.symm y := by
    intro y
    have h1 : w (e.symm y) = y := by rw [← he', e.apply_symm_apply]
    have hymem : y ∈ w '' univ := by rw [hsurj]; exact mem_univ y
    have h2 : w (Function.invFunOn w univ y) = y := Function.invFunOn_eq hymem
    exact hbij.injective (h2.trans h1.symm)
  refine ⟨isOpen_univ, ?_, hCD.contDiffOn, ⟨hCD.continuous.continuousOn, hbij.injective.injOn,
    rfl, ?_⟩, fun z _ => ?_⟩
  · rw [le_div_iff₀ (by linarith)]
    linarith
  · rw [hsurj]
    exact (e.symm.continuous.congr (fun y => (heq y).symm)).continuousOn
  · have hdz : dz w z ≠ 0 := by
      intro h
      have hj := hJ z
      rw [jacobian, h, norm_zero] at hj
      nlinarith [norm_nonneg (dzbar w z)]
    have hcd : complexDilatation w z = μ z := by
      rw [complexDilatation, hbeltrami z, mul_div_assoc, div_self hdz, mul_one]
    have hnorm : ‖complexDilatation w z‖ ≤ k := hcd ▸ hμ z
    have hdzpos : 0 < ‖dz w z‖ := norm_pos_iff.2 hdz
    have h1 : ‖dzbar w z‖ < ‖dz w z‖ := by
      rw [hbeltrami z, norm_mul]
      nlinarith [hμ z]
    refine ⟨h1, ?_⟩
    rw [dilatationQuotient, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [hnorm]

/-- (properness half) a plane translate by a bounded function is proper. -/
theorem t3b_proper_of_bounded {ω : ℂ → ℂ} {M : ℝ} (hM : ∀ z, ‖cauchyT ω z‖ ≤ M) :
    Tendsto (fun z => z + cauchyT ω z) (Filter.cocompact ℂ) (Filter.cocompact ℂ) := by
  rw [← Metric.cobounded_eq_cocompact,
    (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).tendsto_right_iff]
  intro r _
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) (Bornology.cobounded ℂ) atTop := by
    rw [Metric.cobounded_eq_cocompact]; exact tendsto_norm_cocompact_atTop
  filter_upwards [hnorm.eventually_gt_atTop (r + M)] with z hz
  simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
  have htri : ‖z‖ ≤ ‖z + cauchyT ω z‖ + ‖cauchyT ω z‖ := by
    calc ‖z‖ = ‖(z + cauchyT ω z) - cauchyT ω z‖ := by ring_nf
      _ ≤ ‖z + cauchyT ω z‖ + ‖cauchyT ω z‖ := norm_sub_le _ _
  linarith [hM z]

/-- A compactly-supported, a.e.-bounded Beltrami coefficient is `MemLp`. -/
theorem t3_memLp_of_compactBeltrami {μ : ℂ → ℂ} {k p : ℝ} (hμ : IsCompactBeltramiCoeff μ k) :
    MemLp μ (ENNReal.ofReal p) volume := by
  obtain ⟨⟨hmeas, hbdd⟩, R, hR⟩ := hμ
  obtain ⟨R', hR'0, hR'⟩ : ∃ R' : ℝ, 0 < R' ∧ ∀ z : ℂ, R' < ‖z‖ → μ z = 0 :=
    ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _),
      fun z hz => hR z (lt_of_le_of_lt (le_max_left R 1) hz)⟩
  have hind : μ = (closedBall (0 : ℂ) R').indicator μ := by
    funext z
    by_cases hz : z ∈ closedBall (0 : ℂ) R'
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz]
      exact hR' z (by rwa [mem_closedBall_zero_iff, not_le] at hz)
  rw [hind, memLp_indicator_iff_restrict measurableSet_closedBall.nullMeasurableSet]
  haveI : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) R')) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  refine MemLp.of_bound ?_ k ?_
  · exact (hmeas.mono_measure (by rw [Measure.restrict_univ])).mono_measure
      Measure.restrict_le_self
  · rw [Measure.restrict_univ] at hbdd
    exact ae_restrict_of_ae hbdd

/-- Convolving an a.e.-`k`-bounded function with a nonnegative, mass-`1` kernel stays `≤ k`
everywhere (not just a.e.): the a.e. exceptional set transfers under `t ↦ z - t`, which is
measure-preserving (`quasiMeasurePreserving_sub_left`). -/
theorem t5Mollify_norm_le_of_ae_bound {ω : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k)
    (hbdd : ∀ᵐ w, ‖ω w‖ ≤ k) (n : ℕ) (z : ℂ) : ‖t5Mollify ω n z‖ ≤ k := by
  have hbddz : ∀ᵐ t, ‖ω (z - t)‖ ≤ k := (quasiMeasurePreserving_sub_left volume z).ae hbdd
  have h1 : ‖t5Mollify ω n z‖ₑ ≤
      ∫⁻ t, ENNReal.ofReal ((lemma92Bump n).normed volume t) * ‖ω (z - t)‖ₑ := by
    rw [t5Mollify, convolution_def]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun t => ?_))
    rw [ContinuousLinearMap.lsmul_apply, enorm_smul,
      Real.enorm_eq_ofReal ((lemma92Bump n).nonneg_normed t)]
  have h2 : (∫⁻ t, ENNReal.ofReal ((lemma92Bump n).normed volume t) * ‖ω (z - t)‖ₑ) ≤
      ∫⁻ t, ENNReal.ofReal ((lemma92Bump n).normed volume t) * ENNReal.ofReal k := by
    refine lintegral_mono_ae ?_
    filter_upwards [hbddz] with t ht
    gcongr
    rw [← ofReal_norm (ω (z - t))]
    exact ENNReal.ofReal_le_ofReal ht
  have h3 : (∫⁻ t, ENNReal.ofReal ((lemma92Bump n).normed volume t)) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (lemma92Bump n).integrable_normed
      (Eventually.of_forall fun x => (lemma92Bump n).nonneg_normed x),
      (lemma92Bump n).integral_normed, ENNReal.ofReal_one]
  have h4 : (∫⁻ t, ENNReal.ofReal ((lemma92Bump n).normed volume t) * ENNReal.ofReal k) =
      ENNReal.ofReal k := by
    rw [lintegral_mul_const'' _ (lemma92Bump n).continuous_normed.measurable.ennreal_ofReal.aemeasurable,
      h3, one_mul]
  have hfin : ‖t5Mollify ω n z‖ₑ ≤ ENNReal.ofReal k := h1.trans (h2.trans h4.le)
  rw [← ofReal_norm (t5Mollify ω n z)] at hfin
  exact (ENNReal.ofReal_le_ofReal_iff hk₀).mp hfin

/-- Measurable + compactly supported + `k`-bounded Beltrami coefficients admit a `C^∞`,
`k`-bounded, uniformly compactly supported smooth approximation converging a.e. -/
theorem exists_smooth_beltrami_approx {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k)
    (hμ : IsCompactBeltramiCoeff μ k) :
    ∃ (R : ℝ) (μn : ℕ → ℂ → ℂ), 0 < R ∧ (∀ z, R < ‖z‖ → μ z = 0) ∧
      (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (μn n)) ∧ (∀ n, HasCompactSupport (μn n)) ∧
      (∀ n z, ‖μn n z‖ ≤ k) ∧ (∀ n z, R < ‖z‖ → μn n z = 0) ∧
      ∀ᵐ z, Tendsto (fun n => μn n z) atTop (𝓝 (μ z)) := by
  have hmemLp1 : MemLp μ (ENNReal.ofReal 1) volume := t3_memLp_of_compactBeltrami hμ
  obtain ⟨⟨hmeas, hbdd⟩, R₀, hR₀⟩ := hμ
  rw [Measure.restrict_univ] at hbdd
  obtain ⟨R₀', hR₀'0, hR₀'⟩ : ∃ R' : ℝ, 0 ≤ R' ∧ ∀ z : ℂ, R' < ‖z‖ → μ z = 0 :=
    ⟨max R₀ 0, le_max_right _ _, fun z hz => hR₀ z (lt_of_le_of_lt (le_max_left R₀ 0) hz)⟩
  have hsuppμ : Bornology.IsBounded (Function.support μ) :=
    isBounded_closedBall.subset (fun z hz => by
      rw [mem_closedBall_zero_iff]
      by_contra hzc
      exact hz (hR₀' z (not_le.mp hzc)))
  have hmemLp1' : MemLp μ 1 volume := ENNReal.ofReal_one ▸ hmemLp1
  have hloc : LocallyIntegrable μ volume := (memLp_one_iff_integrable.1 hmemLp1').locallyIntegrable
  refine ⟨R₀' + 1, t5Mollify μ, by linarith, fun z hz => hR₀' z (by linarith),
    fun n => t5Mollify_contDiff (le_refl (1 : ℝ)) hmemLp1 n,
    fun n => t5Mollify_hasCompactSupport hsuppμ n,
    fun n z => t5Mollify_norm_le_of_ae_bound hk₀ hbdd n z,
    fun n z hz => by
      by_contra hne
      have hmem := t5Mollify_support_subset hR₀' n hne
      rw [mem_closedBall_zero_iff] at hmem
      linarith,
    ?_⟩
  have hφ : Tendsto (fun n : ℕ => (lemma92Bump n).rOut) atTop (𝓝 0) := by
    have heq : ∀ n : ℕ, (lemma92Bump n).rOut = 1 / ((n : ℝ) + 1) := fun n => rfl
    simp only [heq]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have h'φ : ∀ n : ℕ, (lemma92Bump n).rOut ≤ 2 * (lemma92Bump n).rIn := by
    intro n
    have h1 : (lemma92Bump n).rOut = 1 / ((n : ℝ) + 1) := rfl
    have h2 : (lemma92Bump n).rIn = 1 / (2 * ((n : ℝ) + 1)) := rfl
    have hpos : (0:ℝ) < (n:ℝ) + 1 := by positivity
    rw [h1, h2]
    field_simp
    norm_num
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ
    (Eventually.of_forall h'φ) hloc

/-- `HasGenPartials` transfers through `exp`, by the chain rule `∂(e^f) = e^f·∂f`. -/
theorem hasGenPartials_cexp {f g h : ℂ → ℂ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : HasGenPartials f g h univ p) :
    HasGenPartials (fun z => Complex.exp (f z)) (fun z => Complex.exp (f z) * g z)
      (fun z => Complex.exp (f z) * h z) univ p := by
  obtain ⟨hmem, fn, hfnC1, hconv, hderiv⟩ := hf
  have hfc : ContinuousOn f univ :=
    hconv.continuousOn (Filter.Frequently.of_forall fun n => (hfnC1 n).continuousOn)
  have hExpC1 : ∀ n, ContDiffOn ℝ 1 (fun z => Complex.exp (fn n z)) univ := fun n =>
    (Complex.contDiff_exp (𝕜 := ℝ)).comp_contDiffOn (hfnC1 n)
  have hdiffAt : ∀ n, ∀ z : ℂ, DifferentiableAt ℝ (fn n) z := fun n z =>
    ((hfnC1 n).contDiffAt (isOpen_univ.mem_nhds (mem_univ z))).differentiableAt one_ne_zero
  have hdiffExpAt : ∀ n, ∀ z : ℂ, DifferentiableAt ℝ (fun z => Complex.exp (fn n z)) z :=
    fun n z => ((hExpC1 n).contDiffAt (isOpen_univ.mem_nhds (mem_univ z))).differentiableAt
      one_ne_zero
  have hchain : ∀ n, ∀ z v : ℂ, fderiv ℝ (fun z => Complex.exp (fn n z)) z v =
      Complex.exp (fn n z) * fderiv ℝ (fn n) z v := by
    intro n z v
    have h56 := eq6_5 (hdiffAt n z) Complex.differentiable_exp.differentiableAt
    rw [Complex.deriv_exp] at h56
    rw [fderiv_eq_dz_dzbar (hdiffExpAt n z), fderiv_eq_dz_dzbar (hdiffAt n z),
      show dz (fun z => Complex.exp (fn n z)) z = Complex.exp (fn n z) * dz (fn n) z from h56.1,
      show dzbar (fun z => Complex.exp (fn n z)) z = Complex.exp (fn n z) * dzbar (fn n) z
        from h56.2]
    ring
  -- `f` is bounded on every compact `C ⊆ univ`
  have hbdd : ∀ C : Set ℂ, IsCompact C → ∃ R : ℝ, 0 < R ∧ ∀ z ∈ C, ‖f z‖ ≤ R := by
    intro C hC
    obtain ⟨R, hR⟩ := (hC.image_of_continuousOn (hfc.mono (subset_univ C))).isBounded.subset_closedBall
      (0 : ℂ)
    refine ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun z hz => ?_⟩
    exact (mem_closedBall_zero_iff.1 (hR (mem_image_of_mem f hz))).trans (le_max_left R 1)
  have hgen : ∀ (v : ℂ) (gh : ℂ → ℂ),
      (∀ C, C ⊆ univ → IsCompact C → MemLp gh p (volume.restrict C)) →
      (∀ C, C ⊆ univ → IsCompact C →
        Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (fn n) z v - gh z) p (volume.restrict C))
          atTop (𝓝 0)) →
      ∀ C, C ⊆ univ → IsCompact C →
        Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (fun z => Complex.exp (fn n z)) z v -
          Complex.exp (f z) * gh z) p (volume.restrict C)) atTop (𝓝 0) := by
    intro v gh hghmem hghtend C hCD hC
    have hghmemC := hghmem C hCD hC
    have hghtendC := hghtend C hCD hC
    obtain ⟨R, hR0, hR⟩ := hbdd C hC
    have hUC : TendstoUniformlyOn fn f atTop C :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hC).1
        (hconv.mono (subset_univ C))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 <| by
      rw [Metric.tendstoUniformlyOn_iff] at hUC
      exact hUC 1 one_pos
    have hFmemN : ∀ n ≥ N, ∀ z ∈ C, ‖fn n z‖ ≤ R + 2 := by
      intro n hn z hz
      have hdist : dist (f z) (fn n z) < 1 := hN n hn z hz
      rw [dist_eq_norm] at hdist
      calc ‖fn n z‖ = ‖f z - (f z - fn n z)‖ := by ring_nf
        _ ≤ ‖f z‖ + ‖f z - fn n z‖ := norm_sub_le _ _
        _ ≤ R + 1 := by linarith [hR z hz]
        _ ≤ R + 2 := by linarith
    have hexpFnBddN : ∀ n ≥ N, ∀ z ∈ C, ‖Complex.exp (fn n z)‖ ≤ Real.exp (R + 2) := by
      intro n hn z hz
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.2 ((Complex.re_le_norm _).trans (hFmemN n hn z hz))
    have hUCsub : ∀ z ∈ C, f z ∈ closedBall (0 : ℂ) (R + 2) := fun z hz =>
      mem_closedBall_zero_iff.2 (by linarith [hR z hz])
    have hgcont : UniformContinuousOn Complex.exp (closedBall (0 : ℂ) (R + 2)) :=
      IsCompact.uniformContinuousOn_of_continuous (isCompact_closedBall _ _)
        Complex.continuous_exp.continuousOn
    have hUCexp : TendstoUniformlyOn (fun n z => Complex.exp (fn n z))
        (fun z => Complex.exp (f z)) atTop C :=
      UniformContinuousOn.comp_tendstoUniformlyOn_eventually
        (Filter.eventually_atTop.2 ⟨N, fun n hn z hz => mem_closedBall_zero_iff.2
          (hFmemN n hn z hz)⟩) hUCsub hgcont hUC
    have heq : ∀ n, (fun z => fderiv ℝ (fun z => Complex.exp (fn n z)) z v -
        Complex.exp (f z) * gh z) =
        fun z => Complex.exp (fn n z) • (fderiv ℝ (fn n) z v - gh z) +
          (Complex.exp (fn n z) - Complex.exp (f z)) • gh z := by
      intro n; funext z; rw [hchain n z v]; simp only [smul_eq_mul]; ring
    simp only [heq]
    have hA : Tendsto (fun n => eLpNorm (fun z => Complex.exp (fn n z) •
        (fderiv ℝ (fn n) z v - gh z)) p (volume.restrict C)) atTop (𝓝 0) := by
      have hboundA : ∀ᶠ n in atTop, eLpNorm (fun z => Complex.exp (fn n z) •
          (fderiv ℝ (fn n) z v - gh z)) p (volume.restrict C) ≤
          ENNReal.ofReal (Real.exp (R + 2)) *
            eLpNorm (fun z => fderiv ℝ (fn n) z v - gh z) p (volume.restrict C) := by
        filter_upwards [Filter.eventually_ge_atTop N] with n hn
        have hle1 : eLpNorm (fun z => Complex.exp (fn n z) • (fderiv ℝ (fn n) z v - gh z)) p
            (volume.restrict C) ≤
            eLpNorm ((Real.exp (R + 2) : ℂ) • (fun z => fderiv ℝ (fn n) z v - gh z)) p
              (volume.restrict C) := by
          refine eLpNorm_mono_ae ?_ ?_
          · exact (Complex.continuous_exp.comp
              (contDiffOn_univ.mp (hfnC1 n)).continuous).aestronglyMeasurable.smul
              ((((contDiffOn_univ.mp (hfnC1 n)).continuous_fderiv one_ne_zero).clm_apply
                continuous_const).aestronglyMeasurable.sub hghmemC.aestronglyMeasurable)
          rw [ae_restrict_iff' hC.measurableSet]
          filter_upwards with z hz
          simp only [Pi.smul_apply]
          rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
          exact mul_le_mul_of_nonneg_right (hexpFnBddN n hn z hz) (norm_nonneg _)
        have heq2 : eLpNorm ((Real.exp (R + 2) : ℂ) • (fun z => fderiv ℝ (fn n) z v - gh z)) p
            (volume.restrict C) = ENNReal.ofReal (Real.exp (R + 2)) *
            eLpNorm (fun z => fderiv ℝ (fn n) z v - gh z) p (volume.restrict C) := by
          rw [eLpNorm_const_smul]
          congr 1
          rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        rw [← heq2]; exact hle1
      have hlimA : Tendsto (fun n => ENNReal.ofReal (Real.exp (R + 2)) *
          eLpNorm (fun z => fderiv ℝ (fn n) z v - gh z) p (volume.restrict C)) atTop (𝓝 0) := by
        have hcm := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Real.exp (R + 2))) hghtendC
          (Or.inr ENNReal.ofReal_ne_top)
        simpa using hcm
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimA
        (Filter.Eventually.of_forall fun n => zero_le) hboundA
    have hDmeas : ∀ n, AEStronglyMeasurable (fun z => Complex.exp (fn n z) -
        Complex.exp (f z)) (volume.restrict C) := fun n =>
      (Complex.continuous_exp.comp (contDiffOn_univ.mp (hfnC1 n)).continuous).aestronglyMeasurable.sub
        ((Complex.continuous_exp.comp_continuousOn (hfc.mono (subset_univ C))).aestronglyMeasurable
          hC.isClosed.measurableSet)
    have hLinftyConv : Tendsto (fun n => eLpNorm (fun z => Complex.exp (fn n z) -
        Complex.exp (f z)) ⊤ (volume.restrict C)) atTop (𝓝 0) := by
      refine ENNReal.tendsto_nhds_zero.2 fun ε' hε' => ?_
      rcases eq_or_ne ε' ⊤ with hε'top | hε'top
      · simp [hε'top]
      · have hε0 : 0 < ε'.toReal := ENNReal.toReal_pos hε'.ne' hε'top
        rw [Metric.tendstoUniformlyOn_iff] at hUCexp
        filter_upwards [hUCexp ε'.toReal hε0] with n hn
        have hbound : ∀ᵐ z ∂(volume.restrict C), ‖Complex.exp (fn n z) - Complex.exp (f z)‖ ≤
            ε'.toReal := by
          rw [ae_restrict_iff' hC.measurableSet]
          filter_upwards with z hz
          have hd := hn z hz
          rw [dist_eq_norm] at hd
          calc ‖Complex.exp (fn n z) - Complex.exp (f z)‖ =
              ‖Complex.exp (f z) - Complex.exp (fn n z)‖ := (norm_sub_rev _ _)
            _ ≤ ε'.toReal := hd.le
        have hstep1 : eLpNorm (fun z => Complex.exp (fn n z) - Complex.exp (f z)) ⊤
            (volume.restrict C) = eLpNormEssSup (fun z => Complex.exp (fn n z) -
              Complex.exp (f z)) (volume.restrict C) := eLpNorm_exponent_top (hDmeas n)
        have hstep2 : eLpNormEssSup (fun z => Complex.exp (fn n z) - Complex.exp (f z))
            (volume.restrict C) ≤ ENNReal.ofReal ε'.toReal := eLpNormEssSup_le_of_ae_bound hbound
        rw [hstep1]
        exact hstep2.trans_eq (ENNReal.ofReal_toReal hε'top)
    have hfnDerivCont : ∀ n, Continuous (fun z => fderiv ℝ (fn n) z v) :=
      fun n => ((contDiffOn_univ.mp (hfnC1 n)).continuous_fderiv one_ne_zero).clm_apply
        continuous_const
    have hAmeas : ∀ n, AEStronglyMeasurable (fun z => Complex.exp (fn n z) •
        (fderiv ℝ (fn n) z v - gh z)) (volume.restrict C) := fun n =>
      (Complex.continuous_exp.comp (contDiffOn_univ.mp (hfnC1 n)).continuous).aestronglyMeasurable.smul
        ((hfnDerivCont n).aestronglyMeasurable.sub hghmemC.aestronglyMeasurable)
    have hBmeas : ∀ n, AEStronglyMeasurable (fun z => (Complex.exp (fn n z) -
        Complex.exp (f z)) • gh z) (volume.restrict C) := fun n =>
      ((Complex.continuous_exp.comp (contDiffOn_univ.mp (hfnC1 n)).continuous).aestronglyMeasurable.sub
        ((Complex.continuous_exp.comp_continuousOn (hfc.mono (subset_univ C))).aestronglyMeasurable
          hC.isClosed.measurableSet)).smul hghmemC.aestronglyMeasurable
    have hB' : Tendsto (fun n => eLpNorm (fun z => (Complex.exp (fn n z) -
        Complex.exp (f z)) • gh z) p (volume.restrict C)) atTop (𝓝 0) := by
      have hboundB : ∀ n, eLpNorm (fun z => (Complex.exp (fn n z) -
          Complex.exp (f z)) • gh z) p (volume.restrict C) ≤
          eLpNorm (fun z => Complex.exp (fn n z) - Complex.exp (f z)) ⊤
            (volume.restrict C) * eLpNorm gh p (volume.restrict C) := by
        intro n
        exact eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm p (hDmeas n)
      have hlimB : Tendsto (fun n => eLpNorm (fun z => Complex.exp (fn n z) -
          Complex.exp (f z)) ⊤ (volume.restrict C) * eLpNorm gh p (volume.restrict C)) atTop
          (𝓝 0) := by
        have hcm := ENNReal.Tendsto.mul_const (b := eLpNorm gh p (volume.restrict C)) hLinftyConv
          (Or.inr hghmemC.eLpNorm_lt_top.ne)
        simpa using hcm
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimB
        (Filter.Eventually.of_forall fun n => zero_le) (Filter.Eventually.of_forall hboundB)
    have hsum := hA.add hB'
    simp only [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Filter.Eventually.of_forall fun n => zero_le) (Filter.Eventually.of_forall fun n => ?_)
    simp only [smul_eq_mul] at hAmeas hBmeas
    exact eLpNorm_add_le hp
  refine ⟨?_, fun n z => Complex.exp (fn n z), hExpC1, ?_, ?_⟩
  · intro C _ hC
    obtain ⟨hg, hh⟩ := hmem C (subset_univ C) hC
    obtain ⟨R, hR0, hR⟩ := hbdd C hC
    have hCm : MeasurableSet C := hC.isClosed.measurableSet
    have hexpMeas : AEStronglyMeasurable (fun z => Complex.exp (f z)) (volume.restrict C) :=
      (Complex.continuous_exp.comp_continuousOn (hfc.mono (subset_univ C))).aestronglyMeasurable
        hCm
    have hexpTop : MemLp (fun z => Complex.exp (f z)) ⊤ (volume.restrict C) := by
      refine memLp_top_of_bound hexpMeas (Real.exp R) (ae_restrict_of_forall_mem hCm ?_)
      intro z hz
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.2 ((Complex.re_le_norm _).trans (hR z hz))
    exact ⟨hexpTop.fun_mul hg, hexpTop.fun_mul hh⟩
  · refine (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).2 fun C _ hC => ?_
    have hUC : TendstoUniformlyOn fn f atTop C :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hC).1
        (hconv.mono (subset_univ C))
    obtain ⟨R, hR0, hR⟩ := hbdd C hC
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 <| by
      rw [Metric.tendstoUniformlyOn_iff] at hUC
      exact hUC 1 one_pos
    have hFmemN : ∀ n ≥ N, ∀ z ∈ C, ‖fn n z‖ ≤ R + 2 := by
      intro n hn z hz
      have hdist : dist (f z) (fn n z) < 1 := hN n hn z hz
      rw [dist_eq_norm] at hdist
      calc ‖fn n z‖ = ‖f z - (f z - fn n z)‖ := by ring_nf
        _ ≤ ‖f z‖ + ‖f z - fn n z‖ := norm_sub_le _ _
        _ ≤ R + 1 := by linarith [hR z hz]
        _ ≤ R + 2 := by linarith
    have hUCsub : ∀ z ∈ C, f z ∈ closedBall (0 : ℂ) (R + 2) := fun z hz =>
      mem_closedBall_zero_iff.2 (by linarith [hR z hz])
    have hgcont : UniformContinuousOn Complex.exp (closedBall (0 : ℂ) (R + 2)) :=
      IsCompact.uniformContinuousOn_of_continuous (isCompact_closedBall _ _)
        Complex.continuous_exp.continuousOn
    exact UniformContinuousOn.comp_tendstoUniformlyOn_eventually
      (Filter.eventually_atTop.2 ⟨N, fun n hn z hz => mem_closedBall_zero_iff.2
        (hFmemN n hn z hz)⟩) hUCsub hgcont hUC
  · intro C hCD hC
    exact ⟨hgen 1 g (fun C hCD hC => (hmem C hCD hC).1) (fun C hCD hC => (hderiv C hCD hC).1)
        C hCD hC,
      hgen I h (fun C hCD hC => (hmem C hCD hC).2) (fun C hCD hC => (hderiv C hCD hC).2)
        C hCD hC⟩

/-- A `C¹` map with everywhere-positive Jacobian, staying within bounded distance of the
identity, is a homeomorphism of `ℂ`. -/
theorem homeomorph_of_contDiff_jacobian_pos {w : ℂ → ℂ} (hw : ContDiff ℝ 1 w)
    (hJ : ∀ z, 0 < jacobian w z) (hbd : ∃ M : ℝ, ∀ z, ‖w z - z‖ ≤ M) :
    ∃ e : ℂ ≃ₜ ℂ, ⇑e = w := by
  have hdiff : ∀ z, DifferentiableAt ℝ w z := fun z => hw.differentiable one_ne_zero z
  have hcont : Continuous w := hw.continuous
  have hker : ∀ z, LinearMap.ker (fderiv ℝ w z : ℂ →ₗ[ℝ] ℂ) = ⊥ := by
    intro z
    by_contra hne
    have hdet0 : LinearMap.det (fderiv ℝ w z : ℂ →ₗ[ℝ] ℂ) = 0 :=
      LinearMap.det_eq_zero_iff_ker_ne_bot.2 hne
    rw [det_fderiv_eq_jacobian (hdiff z)] at hdet0
    exact (hJ z).ne' hdet0
  have hrange : ∀ z, LinearMap.range (fderiv ℝ w z : ℂ →ₗ[ℝ] ℂ) = ⊤ := fun z =>
    LinearMap.ker_eq_bot_iff_range_eq_top.1 (hker z)
  set e' : ∀ z : ℂ, ℂ ≃L[ℝ] ℂ := fun z =>
    ContinuousLinearEquiv.ofBijective (fderiv ℝ w z) (hker z) (hrange z) with he'def
  have hstrict : ∀ z, HasStrictFDerivAt w (fderiv ℝ w z) z := fun z =>
    hw.contDiffAt.hasStrictFDerivAt one_ne_zero
  have hstrict' : ∀ z, HasStrictFDerivAt w (e' z : ℂ →L[ℝ] ℂ) z := by
    intro z
    have heq : (e' z : ℂ →L[ℝ] ℂ) = fderiv ℝ w z := by
      rw [he'def]; exact ContinuousLinearEquiv.coe_ofBijective _ _ _
    rw [heq]
    exact hstrict z
  have hopen : IsOpenMap w := isOpenMap_of_hasStrictFDerivAt_equiv hstrict'
  have hproper' : Tendsto w (Filter.cocompact ℂ) (Filter.cocompact ℂ) := by
    obtain ⟨M, hM⟩ := hbd
    rw [← Metric.cobounded_eq_cocompact,
      (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).tendsto_right_iff]
    intro r _
    have hnorm : Tendsto (fun z : ℂ => ‖z‖) (Bornology.cobounded ℂ) atTop := by
      rw [Metric.cobounded_eq_cocompact]; exact tendsto_norm_cocompact_atTop
    filter_upwards [hnorm.eventually_gt_atTop (r + M)] with z hz
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
    have htri : ‖z‖ ≤ ‖w z‖ + ‖w z - z‖ := by
      calc ‖z‖ = ‖w z - (w z - z)‖ := by ring_nf
        _ ≤ ‖w z‖ + ‖w z - z‖ := norm_sub_le _ _
    linarith [hM z]
  have hproper : IsProperMap w := isProperMap_iff_tendsto_cocompact.2 ⟨hcont, hproper'⟩
  have hclosed : IsClosedMap w := hproper.isClosedMap
  have hsurj : w '' univ = univ := by
    have hclopen : IsClopen (w '' univ) := ⟨hclosed univ isClosed_univ, hopen univ isOpen_univ⟩
    exact hclopen.eq_univ ⟨w 0, mem_image_of_mem w (mem_univ 0)⟩
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ℂ, w z₀ = 0 := by
    have h0 : (0 : ℂ) ∈ w '' univ := by rw [hsurj]; exact mem_univ 0
    obtain ⟨z₀, -, hz₀⟩ := h0
    exact ⟨z₀, hz₀⟩
  have hloc_witness : ∀ z : ℂ, ∃ φ : OpenPartialHomeomorph ℂ ℂ, z ∈ φ.source ∧ ⇑φ = w :=
    fun z => ⟨(hstrict' z).toOpenPartialHomeomorph w,
      (hstrict' z).mem_toOpenPartialHomeomorph_source, (hstrict' z).toOpenPartialHomeomorph_coe⟩
  have hfiber_finite : ∀ y : ℂ, (w ⁻¹' {y}).Finite := fun y => by
    have hdisc : IsDiscrete (w ⁻¹' {y}) :=
      IsDiscrete.of_openPartialHomeomorph w subset_rfl (fun e _ => hloc_witness e)
    exact (hproper.isCompact_preimage isCompact_singleton).finite hdisc
  have hcov : IsCoveringMap w := by
    rw [isCoveringMap_iff_isCoveringMapOn_univ]
    exact hproper.isClosedMap.isCoveringMapOn_of_openPartialHomeomorph
      (fun y _ => hfiber_finite y)
      (fun e _ => let ⟨φ, hφ, hφe⟩ := hloc_witness e; ⟨φ, hφ, hφe.symm⟩)
  obtain ⟨G, ⟨hG0, hGg⟩, -⟩ :=
    hcov.existsUnique_continuousMap_lifts (ContinuousMap.id ℂ) 0 z₀ hz₀
  have hwG : ∀ y, w (G y) = y := fun y => by
    have := congrFun hGg y; simpa using this
  have hGw : ∀ z, G (w z) = z := by
    have hcomp : (G ∘ w) = (id : ℂ → ℂ) :=
      hcov.eq_of_comp_eq (G.continuous.comp hcont) continuous_id
        (by funext z; show w (G (w z)) = w z; rw [hwG])
        z₀ (by show G (w z₀) = z₀; rw [hz₀]; exact hG0)
    exact fun z => congrFun hcomp z
  have hinj : Function.Injective w := fun a b hab => by
    have hg := congrArg G hab
    rwa [hGw, hGw] at hg
  exact t3b_homeomorph_of_open_proper hcont hinj hopen hproper'

open intervalIntegral in
/-- D4: a continuous closed 1-form `P dx + Q dy` (vanishing rectangle integrals) has a `C¹`
primitive. -/
theorem exists_contDiff_primitive_of_rect_integral_eq_zero {P Q : ℂ → ℂ} (hP : Continuous P)
    (hQ : Continuous Q)
    (hrect : ∀ a b c d : ℝ, a < b → c < d →
      (∫ x in a..b, P ((x : ℂ) + (c : ℂ) * I)) + (∫ y in c..d, Q ((b : ℂ) + (y : ℂ) * I)) -
        (∫ x in a..b, P ((x : ℂ) + (d : ℂ) * I)) - (∫ y in c..d, Q ((a : ℂ) + (y : ℂ) * I)) =
        0) :
    ∃ F : ℂ → ℂ, ContDiff ℝ 1 F ∧ ∀ z, fderiv ℝ F z 1 = P z ∧ fderiv ℝ F z I = Q z := by
  -- the closed-form functional, generalized off the `a < b, c < d` hypothesis
  have hzero : ∀ a b c d : ℝ,
      (∫ x in a..b, P ((x : ℂ) + (c : ℂ) * I)) + (∫ y in c..d, Q ((b : ℂ) + (y : ℂ) * I)) -
        (∫ x in a..b, P ((x : ℂ) + (d : ℂ) * I)) - (∫ y in c..d, Q ((a : ℂ) + (y : ℂ) * I)) =
        0 := by
    intro a b c d
    rcases lt_trichotomy a b with hab | hab | hab
    · rcases lt_trichotomy c d with hcd | hcd | hcd
      · exact hrect a b c d hab hcd
      · subst hcd; simp
      · have h0 := hrect a b d c hab hcd
        have es1 : (∫ y in d..c, Q ((b : ℂ) + (y : ℂ) * I)) =
            -∫ y in c..d, Q ((b : ℂ) + (y : ℂ) * I) := integral_symm c d
        have es2 : (∫ y in d..c, Q ((a : ℂ) + (y : ℂ) * I)) =
            -∫ y in c..d, Q ((a : ℂ) + (y : ℂ) * I) := integral_symm c d
        linear_combination -h0 + es1 - es2
    · subst hab; simp
    · rcases lt_trichotomy c d with hcd | hcd | hcd
      · have h0 := hrect b a c d hab hcd
        have es1 : (∫ x in b..a, P ((x : ℂ) + (c : ℂ) * I)) =
            -∫ x in a..b, P ((x : ℂ) + (c : ℂ) * I) := integral_symm a b
        have es2 : (∫ x in b..a, P ((x : ℂ) + (d : ℂ) * I)) =
            -∫ x in a..b, P ((x : ℂ) + (d : ℂ) * I) := integral_symm a b
        linear_combination -h0 + es1 - es2
      · subst hcd; simp
      · have h0 := hrect b a d c hab hcd
        have es1 : (∫ x in b..a, P ((x : ℂ) + (d : ℂ) * I)) =
            -∫ x in a..b, P ((x : ℂ) + (d : ℂ) * I) := integral_symm a b
        have es2 : (∫ x in b..a, P ((x : ℂ) + (c : ℂ) * I)) =
            -∫ x in a..b, P ((x : ℂ) + (c : ℂ) * I) := integral_symm a b
        have es3 : (∫ y in d..c, Q ((a : ℂ) + (y : ℂ) * I)) =
            -∫ y in c..d, Q ((a : ℂ) + (y : ℂ) * I) := integral_symm c d
        have es4 : (∫ y in d..c, Q ((b : ℂ) + (y : ℂ) * I)) =
            -∫ y in c..d, Q ((b : ℂ) + (y : ℂ) * I) := integral_symm c d
        linear_combination h0 - es1 + es2 - es3 + es4
  -- the primitive
  set F : ℂ → ℂ := fun z =>
    (∫ t in (0 : ℝ)..z.re, P (t : ℂ)) + ∫ s in (0 : ℝ)..z.im, Q ((z.re : ℂ) + (s : ℂ) * I) with
    hFdef
  have hFval : ∀ x y : ℝ, F ((x : ℂ) + (y : ℂ) * I) =
      (∫ t in (0 : ℝ)..x, P (t : ℂ)) + ∫ s in (0 : ℝ)..y, Q ((x : ℂ) + (s : ℂ) * I) := by
    intro x y
    simp [hFdef]
  -- the exact identity `F(u,y) - F(x,y) = ∫_x^u P(t+iy) dt`
  have hkey : ∀ x u y : ℝ, F ((u : ℂ) + (y : ℂ) * I) - F ((x : ℂ) + (y : ℂ) * I) =
      ∫ t in x..u, P ((t : ℂ) + (y : ℂ) * I) := by
    intro x u y
    have h0 := hzero x u 0 y
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h0
    have hadd : (∫ t in (0 : ℝ)..x, P (t : ℂ)) + ∫ t in x..u, P (t : ℂ) =
        ∫ t in (0 : ℝ)..u, P (t : ℂ) :=
      intervalIntegral.integral_add_adjacent_intervals
        ((hP.comp (by fun_prop)).intervalIntegrable 0 x)
        ((hP.comp (by fun_prop)).intervalIntegrable x u)
    rw [hFval, hFval]
    linear_combination h0 - hadd
  have hxderiv : ∀ x y : ℝ,
      HasStrictDerivAt (fun u : ℝ => F ((u : ℂ) + (y : ℂ) * I)) (P ((x : ℂ) + (y : ℂ) * I)) x := by
    intro x y
    have hcont : Continuous (fun t : ℝ => P ((t : ℂ) + (y : ℂ) * I)) :=
      hP.comp (by fun_prop)
    have hbase := (hcont.integral_hasStrictDerivAt x x).const_add (F ((x : ℂ) + (y : ℂ) * I))
    have hfe : (fun u : ℝ => F ((x : ℂ) + (y : ℂ) * I) + ∫ t in x..u, P ((t : ℂ) + (y : ℂ) * I)) =
        (fun u : ℝ => F ((u : ℂ) + (y : ℂ) * I)) := by
      funext u
      linear_combination -(hkey x u y)
    rwa [hfe] at hbase
  have hyderiv : ∀ x y : ℝ,
      HasStrictDerivAt (fun v : ℝ => F ((x : ℂ) + (v : ℂ) * I)) (Q ((x : ℂ) + (y : ℂ) * I)) y := by
    intro x y
    have hcont : Continuous (fun s : ℝ => Q ((x : ℂ) + (s : ℂ) * I)) :=
      hQ.comp (by fun_prop)
    have hbase := (hcont.integral_hasStrictDerivAt 0 y).const_add (∫ t in (0 : ℝ)..x, P (t : ℂ))
    have hfe : (fun v : ℝ => (∫ t in (0 : ℝ)..x, P (t : ℂ)) +
        ∫ s in (0 : ℝ)..v, Q ((x : ℂ) + (s : ℂ) * I)) =
        (fun v : ℝ => F ((x : ℂ) + (v : ℂ) * I)) := funext fun v => (hFval x v).symm
    rwa [hfe] at hbase
  -- assemble via `hasStrictFDerivAt_uncurry_coprod`
  set f₁ : ℝ → ℝ → (ℝ →L[ℝ] ℂ) := fun x y => ContinuousLinearMap.toSpanSingleton ℝ
    (P ((x : ℂ) + (y : ℂ) * I)) with hf₁def
  set f₂ : ℝ → ℝ → (ℝ →L[ℝ] ℂ) := fun x y => ContinuousLinearMap.toSpanSingleton ℝ
    (Q ((x : ℂ) + (y : ℂ) * I)) with hf₂def
  have hdf₁ : ∀ v : ℝ × ℝ, HasFDerivAt (fun x : ℝ => F ((x : ℂ) + (v.2 : ℂ) * I)) (↿f₁ v) v.1 :=
    fun v => (hxderiv v.1 v.2).hasDerivAt.hasFDerivAt
  have hdf₂ : ∀ v : ℝ × ℝ, HasFDerivAt (fun y : ℝ => F ((v.1 : ℂ) + (y : ℂ) * I)) (↿f₂ v) v.2 :=
    fun v => (hyderiv v.1 v.2).hasDerivAt.hasFDerivAt
  have hcf₁ : Continuous (↿f₁ : ℝ × ℝ → ℝ →L[ℝ] ℂ) := by
    have heq : (↿f₁ : ℝ × ℝ → ℝ →L[ℝ] ℂ) = fun v : ℝ × ℝ =>
        ContinuousLinearMap.toSpanSingletonLIE ℝ ℂ (P ((v.1 : ℂ) + (v.2 : ℂ) * I)) := rfl
    rw [heq]
    exact (ContinuousLinearMap.toSpanSingletonLIE ℝ ℂ).continuous.comp (by fun_prop)
  have hcf₂ : Continuous (↿f₂ : ℝ × ℝ → ℝ →L[ℝ] ℂ) := by
    have heq : (↿f₂ : ℝ × ℝ → ℝ →L[ℝ] ℂ) = fun v : ℝ × ℝ =>
        ContinuousLinearMap.toSpanSingletonLIE ℝ ℂ (Q ((v.1 : ℂ) + (v.2 : ℂ) * I)) := rfl
    rw [heq]
    exact (ContinuousLinearMap.toSpanSingletonLIE ℝ ℂ).continuous.comp (by fun_prop)
  have huncurry : ∀ u : ℝ × ℝ,
      HasStrictFDerivAt (Function.uncurry fun x y : ℝ => F ((x : ℂ) + (y : ℂ) * I))
        ((↿f₁ u).coprod (↿f₂ u)) u :=
    fun u => hasStrictFDerivAt_uncurry_coprod (f := fun x y : ℝ => F ((x : ℂ) + (y : ℂ) * I))
      (Filter.Eventually.of_forall hdf₁) (Filter.Eventually.of_forall hdf₂) hcf₁.continuousAt
      hcf₂.continuousAt
  -- transfer to `ℂ` via `Complex.equivRealProdCLM`
  have hFcomp : ∀ z : ℂ, F z = (Function.uncurry fun x y : ℝ => F ((x : ℂ) + (y : ℂ) * I))
      (Complex.equivRealProdCLM z) := by
    intro z
    show F z = F ((z.re : ℂ) + (z.im : ℂ) * I)
    rw [Complex.re_add_im]
  have hFstrict : ∀ z : ℂ, HasStrictFDerivAt F
      (((↿f₁ (Complex.equivRealProdCLM z)).coprod (↿f₂ (Complex.equivRealProdCLM z))).comp
        Complex.equivRealProdCLM.toContinuousLinearMap) z := by
    intro z
    have hcomp := (huncurry (Complex.equivRealProdCLM z)).comp z
      Complex.equivRealProdCLM.hasStrictFDerivAt
    have hfe : (fun x => (Function.uncurry fun x y : ℝ => F ((x : ℂ) + (y : ℂ) * I))
        (Complex.equivRealProdCLM x)) = F := funext fun z' => (hFcomp z').symm
    rwa [hfe] at hcomp
  refine ⟨F, ?_, fun z => ?_⟩
  · rw [contDiff_one_iff_fderiv]
    refine ⟨fun z => (hFstrict z).differentiableAt, ?_⟩
    have heqfd : fderiv ℝ F = fun z => (((↿f₁ (Complex.equivRealProdCLM z)).coprod
        (↿f₂ (Complex.equivRealProdCLM z))).comp Complex.equivRealProdCLM.toContinuousLinearMap) :=
      funext fun z => (hFstrict z).hasFDerivAt.fderiv
    rw [heqfd]
    have hcont1 : Continuous fun z : ℂ => ↿f₁ (Complex.equivRealProdCLM z) :=
      hcf₁.comp Complex.equivRealProdCLM.continuous
    have hcont2 : Continuous fun z : ℂ => ↿f₂ (Complex.equivRealProdCLM z) :=
      hcf₂.comp Complex.equivRealProdCLM.continuous
    fun_prop
  · have hz1 : Complex.equivRealProdCLM (1 : ℂ) = (1, 0) := by
      change ((1:ℂ).re, (1:ℂ).im) = (1, 0); norm_num
    have hzI : Complex.equivRealProdCLM (I : ℂ) = (0, 1) := by
      change ((I:ℂ).re, (I:ℂ).im) = (0, 1); norm_num
    have h1 : fderiv ℝ F z 1 =
        (((↿f₁ (Complex.equivRealProdCLM z)).coprod (↿f₂ (Complex.equivRealProdCLM z))).comp
          Complex.equivRealProdCLM.toContinuousLinearMap) 1 := by
      rw [(hFstrict z).hasFDerivAt.fderiv]
    have hI : fderiv ℝ F z I =
        (((↿f₁ (Complex.equivRealProdCLM z)).coprod (↿f₂ (Complex.equivRealProdCLM z))).comp
          Complex.equivRealProdCLM.toContinuousLinearMap) I := by
      rw [(hFstrict z).hasFDerivAt.fderiv]
    rw [h1, hI]
    simp [hz1, hzI, ContinuousLinearMap.coprod_apply]
    constructor
    · show (↿f₁ ((z.re : ℝ), (z.im : ℝ))) (1 : ℝ) = P z
      have hthis : (↿f₁ ((z.re : ℝ), (z.im : ℝ))) (1 : ℝ) = f₁ z.re z.im 1 := rfl
      rw [hthis, hf₁def, ContinuousLinearMap.toSpanSingleton_apply, one_smul, Complex.re_add_im]
    · show (↿f₂ ((z.re : ℝ), (z.im : ℝ))) (1 : ℝ) = Q z
      have hthis : (↿f₂ ((z.re : ℝ), (z.im : ℝ))) (1 : ℝ) = f₂ z.re z.im 1 := rfl
      rw [hthis, hf₂def, ContinuousLinearMap.toSpanSingleton_apply, one_smul, Complex.re_add_im]

/-- A Weyl-type lemma: a function with `HasGenPartials` witnesses whose generalized `∂_z̄` vanishes
a.e. is (classically) holomorphic — via the generalized Pompeiu formula collapsing to the plain
Cauchy integral formula. -/
theorem differentiable_of_genDzbar_eq_zero {f g h : ℂ → ℂ} {p : ℝ} (hp : 2 < p)
    (hf : HasGenPartials f g h univ (ENNReal.ofReal p)) (h0 : ∀ᵐ z, genDzbar g h z = 0) :
    Differentiable ℂ f := by
  have hcont : Continuous f := by
    obtain ⟨-, fn, hfn, hconv, -⟩ := hf
    have := hconv.continuousOn (Filter.Frequently.of_forall fun n => (hfn n).continuousOn)
    rwa [continuousOn_univ] at this
  intro z₀
  set c := z₀ with hc
  set R : ℝ≥0 := 1 with hR
  have hRpos : (0 : ℝ) < R := by rw [hR]; norm_num
  have hCI : CircleIntegrable f c R := hcont.continuousOn.circleIntegrable'
  have hFPS := hasFPowerSeriesOn_cauchy_integral hCI hRpos
  have heq : Set.EqOn f
      (fun w => (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) (ball c R) := by
    intro w hw
    have hgen := eq11_11_pompeiu_gen hRpos isOpen_univ (subset_univ _) hp hf hw
    have h0' : (fun z => genDzbar g h z / (z - w)) =ᵐ[volume] 0 :=
      h0.mono (fun z hz => by simp [hz])
    have hzero : (∫ z in ball c R, genDzbar g h z / (z - w)) = 0 := by
      rw [integral_congr_ae (h0'.filter_mono (ae_mono Measure.restrict_le_self))]
      simp
    rw [hzero, mul_zero, sub_zero] at hgen
    show f w = (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z
    rw [hgen, smul_eq_mul, one_div]
    congr 1
    apply circleIntegral.integral_congr hRpos.le
    intro z _
    simp only [smul_eq_mul]
    ring
  have hz0mem : z₀ ∈ ball c R := mem_ball_self hRpos
  have hAt : AnalyticAt ℂ f z₀ := by
    have := hFPS.analyticAt
    exact this.congr (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz0mem) heq.symm)
  exact hAt.differentiableAt

/-- D2: `omt` solves (12.6), `f := exp(T omt)` has generalized partials satisfying (12.5) a.e. -/
theorem wd_D2 {μ : ℂ → ℂ} {k : ℝ} (_hk : k < 1) (hμs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ)
    (hμc : HasCompactSupport μ) (hμ : ∀ z, ‖μ z‖ ≤ k) {p : ℝ} (hp : 2 < p)
    (hkp : k * hilbertNorm p < 1) :
    ∃ omt : ℂ → ℂ, MemLp omt (ENNReal.ofReal p) ∧
      Bornology.IsBounded (Function.support omt) ∧
      (omt =ᵐ[volume] fun z => μ z * hilbertH omt z + dz μ z) ∧
      HasGenPartials (fun z => Complex.exp (cauchyT omt z))
        (fun z => Complex.exp (cauchyT omt z) * (hilbertH omt z + omt z))
        (fun z => Complex.exp (cauchyT omt z) * (I * (hilbertH omt z - omt z))) univ
        (ENNReal.ofReal p) ∧
      ∀ᵐ z, genDzbar (fun z => Complex.exp (cauchyT omt z) * (hilbertH omt z + omt z))
          (fun z => Complex.exp (cauchyT omt z) * (I * (hilbertH omt z - omt z))) z =
        dz μ z * Complex.exp (cauchyT omt z) +
          μ z * genDz (fun z => Complex.exp (cauchyT omt z) * (hilbertH omt z + omt z))
            (fun z => Complex.exp (cauchyT omt z) * (I * (hilbertH omt z - omt z))) z := by
  -- `∂z μ` is smooth with compact support
  have hdzμCD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dz μ) := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ μ z 1) :=
      (hμs.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ μ z I) :=
      (hμs.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
    have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (I : ℂ) * fderiv ℝ μ z I) :=
      contDiff_const.mul h2
    exact (h1.sub h3).div_const 2
  have hsub : tsupport (dz μ) ⊆ tsupport μ := by
    apply closure_minimal _ (isClosed_tsupport μ)
    intro z hz
    by_contra hzn
    apply hz
    show dz μ z = 0
    unfold dz
    rw [fderiv_of_notMem_tsupport ℝ hzn]
    simp
  have hdzμc : HasCompactSupport (dz μ) :=
    hμc.isCompact.of_isClosed_subset (isClosed_tsupport (dz μ)) hsub
  obtain ⟨R₀, hR₀⟩ := hμc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨R₁, hR₁⟩ := hdzμc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  set R : ℝ := max R₀ R₁ with hRdef
  have hRμ : ∀ z, R < ‖z‖ → μ z = 0 := fun z hz => by
    by_contra h
    have hmem : z ∈ tsupport μ := subset_closure h
    have hb := hR₀ hmem
    rw [mem_closedBall_zero_iff] at hb
    have hle : R₀ ≤ R := le_max_left _ _
    linarith
  have hRdzμ : ∀ z, R < ‖z‖ → dz μ z = 0 := fun z hz => by
    by_contra h
    have hmem : z ∈ tsupport (dz μ) := subset_closure h
    have hb := hR₁ hmem
    rw [mem_closedBall_zero_iff] at hb
    have hle : R₁ ≤ R := le_max_right _ _
    linarith
  have hk₀ : 0 ≤ k := (norm_nonneg (μ 0)).trans (hμ 0)
  have hμB : IsBeltramiCoeff μ univ k :=
    ⟨hμs.continuous.aestronglyMeasurable, Filter.Eventually.of_forall hμ⟩
  have hbdd : ∃ C : ℝ, ∀ z, ‖dz μ z‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hdzμc.isCompact.image hdzμCD.continuous.norm).bddAbove
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z ∈ tsupport (dz μ)
    · exact (hC (mem_image_of_mem _ hz)).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
      exact le_max_right _ _
  obtain ⟨C, hC⟩ := hbdd
  have hdzμMemLp : MemLp (dz μ) (ENNReal.ofReal p) :=
    HasCompactSupport.memLp_of_bound hdzμc hdzμCD.continuous.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)
  obtain ⟨omt0, homt0MemLp, homt0Sol, -⟩ := eq12_1_solution hk₀ hμB hp hkp hdzμMemLp
  -- pass to the bounded-support representative
  set omt : ℂ → ℂ := (closedBall (0 : ℂ) R).indicator omt0 with homtdef
  have homtas : omt0 =ᵐ[volume] omt := by
    filter_upwards [homt0Sol] with z hz
    by_cases hmem : z ∈ closedBall (0 : ℂ) R
    · rw [homtdef, indicator_of_mem hmem]
    · rw [homtdef, indicator_of_notMem hmem]
      rw [mem_closedBall_zero_iff, not_le] at hmem
      rw [hz, hRμ z hmem, hRdzμ z hmem]
      ring
  have homtMemLp : MemLp omt (ENNReal.ofReal p) := homt0MemLp.indicator measurableSet_closedBall.nullMeasurableSet
  have homtSupp : Function.support omt ⊆ closedBall (0 : ℂ) R := fun z hz => by
    by_contra hz'
    exact hz (homtdef ▸ indicator_of_notMem hz' omt0)
  have homtBdd : Bornology.IsBounded (Function.support omt) :=
    isBounded_closedBall.subset homtSupp
  have hcTeq : cauchyT omt0 = cauchyT omt := cauchyT_congr_ae homtas
  have homtSol : omt =ᵐ[volume] fun z => μ z * hilbertH omt z + dz μ z := by
    have hHeq : hilbertH omt0 = hilbertH omt := hilbertH_congr_ae homtas
    filter_upwards [homt0Sol, homtas] with z hz1 hz2
    rw [← hz2, hz1, hHeq]
  -- `T omt` has generalized partials with the classical Pompeiu identity
  obtain ⟨hGP, hgd1, hgd2⟩ := thm11_1 hp homtMemLp homtBdd
  set g : ℂ → ℂ := fun z => hilbertH omt z + omt z with hgdef
  set h : ℂ → ℂ := fun z => I * (hilbertH omt z - omt z) with hhdef
  set f : ℂ → ℂ := fun z => Complex.exp (cauchyT omt z) with hfdef
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hGPf : HasGenPartials f (fun z => f z * g z) (fun z => f z * h z) univ
      (ENNReal.ofReal p) := hasGenPartials_cexp hp1 hGP
  have hgenDzbar : ∀ z, genDzbar (fun z => f z * g z) (fun z => f z * h z) z = f z * omt z := by
    intro z
    show (f z * g z + I * (f z * h z)) / 2 = f z * omt z
    have heq := hgd1 z
    change (g z + I * h z) / 2 = omt z at heq
    field_simp
    linear_combination f z * heq +
      (f z * hilbertH omt z / 2 - f z * omt z / 2) * I_sq
  have hgenDz : ∀ z, genDz (fun z => f z * g z) (fun z => f z * h z) z = f z * hilbertH omt z := by
    intro z
    show (f z * g z - I * (f z * h z)) / 2 = f z * hilbertH omt z
    have heq := hgd2 z
    change (g z - I * h z) / 2 = hilbertH omt z at heq
    field_simp
    linear_combination f z * heq +
      (f z * omt z / 2 - f z * hilbertH omt z / 2) * I_sq
  have h125 : ∀ᵐ z, genDzbar (fun z => f z * g z) (fun z => f z * h z) z =
      dz μ z * f z + μ z * genDz (fun z => f z * g z) (fun z => f z * h z) z := by
    filter_upwards [homtSol] with z hz
    rw [hgenDzbar, hgenDz, hz]
    ring
  refine ⟨omt, homtMemLp, homtBdd, homtSol, hGPf, h125⟩

/-- Product rule for `HasGenPartials` against a globally smooth, boundedly-differentiable
factor `ψ` (used for `ψ = 1 ± μ` in D3). -/
theorem hasGenPartials_mul_contDiff {f g h ψ : ℂ → ℂ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : HasGenPartials f g h univ p) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (Bψ Bx By : ℝ) (hψb : ∀ z, ‖ψ z‖ ≤ Bψ) (hψxb : ∀ z, ‖fderiv ℝ ψ z 1‖ ≤ Bx)
    (hψyb : ∀ z, ‖fderiv ℝ ψ z I‖ ≤ By) :
    HasGenPartials (fun z => f z * ψ z) (fun z => g z * ψ z + f z * fderiv ℝ ψ z 1)
      (fun z => h z * ψ z + f z * fderiv ℝ ψ z I) univ p := by
  obtain ⟨hMemLp, fn, hfnCD, hfnTLU, hfnConv⟩ := hf
  have hfc : Continuous f := by
    have := hfnTLU.continuousOn (Filter.Frequently.of_forall fun n => (hfnCD n).continuousOn)
    rwa [continuousOn_univ] at this
  have hψCD1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hψcont : Continuous ψ := hψCD1.continuous
  have hψDiff : Differentiable ℝ ψ := hψCD1.differentiable one_ne_zero
  have hψxCD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ ψ z 1) :=
    (hψ.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
  have hψyCD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ ψ z I) :=
    (hψ.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
  have hψxcont : Continuous (fun z => fderiv ℝ ψ z 1) := hψxCD.continuous
  have hψycont : Continuous (fun z => fderiv ℝ ψ z I) := hψyCD.continuous
  have hfnDiff : ∀ n, Differentiable ℝ (fn n) := fun n =>
    differentiableOn_univ.mp ((hfnCD n).differentiableOn one_ne_zero)
  refine ⟨?_, fun n z => fn n z * ψ z, fun n => (hfnCD n).mul hψCD1.contDiffOn, ?_, ?_⟩
  · -- MemLp on compacts
    intro C hC hCcpt
    haveI : IsFiniteMeasure (volume.restrict C) :=
      isFiniteMeasure_restrict.2 hCcpt.isBounded.measure_lt_top.ne
    obtain ⟨hMg, hMh⟩ := hMemLp C hC hCcpt
    have hAEg : AEStronglyMeasurable g (volume.restrict C) := hMg.aestronglyMeasurable
    have hAEh : AEStronglyMeasurable h (volume.restrict C) := hMh.aestronglyMeasurable
    have hAEf : AEStronglyMeasurable f (volume.restrict C) := hfc.aestronglyMeasurable
    have hMemGψ : MemLp (fun z => g z * ψ z) p (volume.restrict C) := by
      apply MemLp.of_le_mul hMg (hAEg.mul hψcont.aestronglyMeasurable) (c := Bψ)
      filter_upwards with z
      show ‖g z * ψ z‖ ≤ Bψ * ‖g z‖
      calc ‖g z * ψ z‖ = ‖g z‖ * ‖ψ z‖ := norm_mul _ _
        _ ≤ ‖g z‖ * Bψ := mul_le_mul_of_nonneg_left (hψb z) (norm_nonneg _)
        _ = Bψ * ‖g z‖ := mul_comm _ _
    have hMemHψ : MemLp (fun z => h z * ψ z) p (volume.restrict C) := by
      apply MemLp.of_le_mul hMh (hAEh.mul hψcont.aestronglyMeasurable) (c := Bψ)
      filter_upwards with z
      show ‖h z * ψ z‖ ≤ Bψ * ‖h z‖
      calc ‖h z * ψ z‖ = ‖h z‖ * ‖ψ z‖ := norm_mul _ _
        _ ≤ ‖h z‖ * Bψ := mul_le_mul_of_nonneg_left (hψb z) (norm_nonneg _)
        _ = Bψ * ‖h z‖ := mul_comm _ _
    have hCmeas : MeasurableSet C := hCcpt.isClosed.measurableSet
    obtain ⟨Mf, hMf⟩ := (hCcpt.image hfc.norm).bddAbove
    have hMfC : ∀ᵐ z ∂(volume.restrict C), ‖f z‖ ≤ Mf := by
      rw [ae_restrict_iff' hCmeas]
      filter_upwards with z hz
      exact hMf (mem_image_of_mem _ hz)
    have hMemFψx : MemLp (fun z => f z * fderiv ℝ ψ z 1) p (volume.restrict C) := by
      apply MemLp.of_bound (hAEf.mul hψxcont.aestronglyMeasurable) (Mf * Bx)
      filter_upwards [hMfC] with z hz
      show ‖f z * fderiv ℝ ψ z 1‖ ≤ Mf * Bx
      calc ‖f z * fderiv ℝ ψ z 1‖ = ‖f z‖ * ‖fderiv ℝ ψ z 1‖ := norm_mul _ _
        _ ≤ Mf * Bx := mul_le_mul hz (hψxb z) (norm_nonneg _) (le_trans (norm_nonneg _) hz)
    have hMemFψy : MemLp (fun z => f z * fderiv ℝ ψ z I) p (volume.restrict C) := by
      apply MemLp.of_bound (hAEf.mul hψycont.aestronglyMeasurable) (Mf * By)
      filter_upwards [hMfC] with z hz
      show ‖f z * fderiv ℝ ψ z I‖ ≤ Mf * By
      calc ‖f z * fderiv ℝ ψ z I‖ = ‖f z‖ * ‖fderiv ℝ ψ z I‖ := norm_mul _ _
        _ ≤ Mf * By := mul_le_mul hz (hψyb z) (norm_nonneg _) (le_trans (norm_nonneg _) hz)
    exact ⟨hMemGψ.add hMemFψx, hMemHψ.add hMemFψy⟩
  · -- TendstoLocallyUniformlyOn of the product approximants
    have hψconst : TendstoUniformlyOn (fun (_ : ℕ) => ψ) ψ atTop univ := by
      intro u hu
      filter_upwards with n z _
      exact refl_mem_uniformity hu
    have hmul := hfnTLU.mul₀ hψconst.tendstoLocallyUniformlyOn hfc.continuousOn hψcont.continuousOn
    exact hmul
  · -- fderiv convergence
    intro C hC hCcpt
    have hderiv1 : ∀ n z, fderiv ℝ (fun y => fn n y * ψ y) z 1 =
        fn n z * fderiv ℝ ψ z 1 + ψ z * fderiv ℝ (fn n) z 1 := by
      intro n z
      rw [fderiv_fun_mul (hfnDiff n z) (hψDiff z)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hderiv2 : ∀ n z, fderiv ℝ (fun y => fn n y * ψ y) z I =
        fn n z * fderiv ℝ ψ z I + ψ z * fderiv ℝ (fn n) z I := by
      intro n z
      rw [fderiv_fun_mul (hfnDiff n z) (hψDiff z)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    obtain ⟨hc1, hc2⟩ := hfnConv C hC hCcpt
    haveI : IsFiniteMeasure (volume.restrict C) :=
      isFiniteMeasure_restrict.2 hCcpt.isBounded.measure_lt_top.ne
    set K : ℝ≥0∞ := (volume C) ^ (p.toReal)⁻¹ with hKdef
    have hKfin : K ≠ ⊤ := by
      rw [hKdef]
      exact (ENNReal.rpow_lt_top_of_nonneg (by positivity) hCcpt.isBounded.measure_lt_top.ne).ne
    have hUnif : TendstoUniformlyOn fn f atTop C :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hfnTLU C (subset_univ C) hCcpt
    have hCmeas : MeasurableSet C := hCcpt.isClosed.measurableSet
    have hfnCDglobal : ∀ n, ContDiff ℝ 1 (fn n) := fun n => contDiffOn_univ.mp (hfnCD n)
    have hfnxCont : ∀ n, Continuous (fun z => fderiv ℝ (fn n) z 1) := fun n =>
      ((hfnCDglobal n).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hfnyCont : ∀ n, Continuous (fun z => fderiv ℝ (fn n) z I) := fun n =>
      ((hfnCDglobal n).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hAEg : AEStronglyMeasurable g (volume.restrict C) :=
      (hMemLp C (subset_univ C) hCcpt).1.aestronglyMeasurable
    have hAEh : AEStronglyMeasurable h (volume.restrict C) :=
      (hMemLp C (subset_univ C) hCcpt).2.aestronglyMeasurable
    -- extract a real bound sequence `δ` witnessing uniform convergence on `C`
    have hδ : ∃ δ : ℕ → ℝ, (∀ n, 0 ≤ δ n) ∧ (∀ n, ∀ z ∈ C, ‖fn n z - f z‖ ≤ δ n) ∧
        Tendsto δ atTop (𝓝 0) := by
      by_cases hCe : C.Nonempty
      · have hex : ∀ n : ℕ, ∃ z ∈ C, ∀ z' ∈ C, ‖fn n z' - f z'‖ ≤ ‖fn n z - f z‖ := by
          intro n
          obtain ⟨z, hz, hmax⟩ := hCcpt.exists_isMaxOn hCe
            ((((hfnCD n).continuousOn.mono (subset_univ C)).sub hfc.continuousOn).norm)
          exact ⟨z, hz, fun z' hz' => hmax hz'⟩
        choose zmax hzmaxC hzmaxge using hex
        refine ⟨fun n => ‖fn n (zmax n) - f (zmax n)‖, fun n => norm_nonneg _,
          fun n z hz => hzmaxge n z hz, ?_⟩
        rw [Metric.tendsto_nhds]
        intro ε hε
        filter_upwards [Metric.tendstoUniformlyOn_iff.mp hUnif ε hε] with n hn
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _), ← dist_eq_norm, dist_comm]
        exact hn (zmax n) (hzmaxC n)
      · refine ⟨fun _ => 0, fun _ => le_refl 0, fun n z hz => absurd ⟨z, hz⟩ hCe,
          tendsto_const_nhds⟩
    obtain ⟨δ, hδnn, hδbd, hδtendsto⟩ := hδ
    have hcross : ∀ κ : ℝ, 0 ≤ κ → ∀ F : ℂ → ℂ, Continuous F → (∀ z, ‖F z‖ ≤ κ) →
        Tendsto (fun n => eLpNorm (fun z => (fn n z - f z) * F z) p (volume.restrict C))
          atTop (𝓝 0) := by
      intro κ hκ F hFc hFb
      rw [ENNReal.tendsto_nhds_zero]
      intro ε hε
      have hbound : ∀ n, ∀ᵐ z ∂(volume.restrict C), ‖(fn n z - f z) * F z‖ ≤ κ * δ n := by
        intro n
        rw [ae_restrict_iff' hCmeas]
        filter_upwards with z hz
        rw [norm_mul, mul_comm κ (δ n)]
        exact mul_le_mul (hδbd n z hz) (hFb z) (norm_nonneg _) (hδnn n)
      have hεn : Tendsto (fun n => K * ENNReal.ofReal (κ * δ n)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n => κ * δ n) atTop (𝓝 0) := by
          have := hδtendsto.const_mul κ
          simpa using this
        have h2 : Tendsto (fun n => ENNReal.ofReal (κ * δ n)) atTop (𝓝 0) := by
          have h2' := (ENNReal.continuous_ofReal.tendsto 0).comp h1
          simp only [Function.comp_def, ENNReal.ofReal_zero] at h2'
          exact h2'
        have h3 : Tendsto (fun n => K * ENNReal.ofReal (κ * δ n)) atTop (𝓝 (K * 0)) :=
          ENNReal.Tendsto.const_mul h2 (Or.inr hKfin)
        simpa using h3
      filter_upwards [ENNReal.tendsto_nhds_zero.mp hεn ε hε] with n hn
      calc eLpNorm (fun z => (fn n z - f z) * F z) p (volume.restrict C)
          ≤ K * ENNReal.ofReal (κ * δ n) := by
            have hm : AEStronglyMeasurable (fun z => (fn n z - f z) * F z) (volume.restrict C) :=
              (((hfnCDglobal n).continuous.sub hfc).mul hFc).aestronglyMeasurable
            have := eLpNorm_le_of_ae_bound (μ := volume.restrict C) (p := p) hm (hbound n)
            simpa [Measure.restrict_apply_univ, hKdef] using this
        _ ≤ ε := hn
    have hBxnn : 0 ≤ Bx := le_trans (norm_nonneg _) (hψxb 0)
    have hBynn : 0 ≤ By := le_trans (norm_nonneg _) (hψyb 0)
    have hcrossX := hcross Bx hBxnn (fun z => fderiv ℝ ψ z 1) hψxcont hψxb
    have hcrossY := hcross By hBynn (fun z => fderiv ℝ ψ z I) hψycont hψyb
    have hgtermX : Tendsto (fun n => eLpNorm (fun z => ψ z * (fderiv ℝ (fn n) z 1 - g z)) p
        (volume.restrict C)) atTop (𝓝 0) := by
      have hb : ∀ n, eLpNorm (fun z => ψ z * (fderiv ℝ (fn n) z 1 - g z)) p (volume.restrict C) ≤
          ENNReal.ofReal Bψ * eLpNorm (fun z => fderiv ℝ (fn n) z 1 - g z) p (volume.restrict C) := by
        intro n
        refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (c := Bψ) ?_ ?_ p
        · exact hψcont.aestronglyMeasurable.mul ((hfnxCont n).aestronglyMeasurable.sub hAEg)
        filter_upwards with z
        calc ‖ψ z * (fderiv ℝ (fn n) z 1 - g z)‖ = ‖ψ z‖ * ‖fderiv ℝ (fn n) z 1 - g z‖ :=
              norm_mul _ _
          _ ≤ Bψ * ‖fderiv ℝ (fn n) z 1 - g z‖ :=
              mul_le_mul_of_nonneg_right (hψb z) (norm_nonneg _)
      have hlim : Tendsto (fun n => ENNReal.ofReal Bψ *
          eLpNorm (fun z => fderiv ℝ (fn n) z 1 - g z) p (volume.restrict C)) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal Bψ) hc1
          (Or.inr ENNReal.ofReal_ne_top)
        simpa using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
        (Filter.Eventually.of_forall fun n => zero_le) (Filter.Eventually.of_forall hb)
    have hgtermY : Tendsto (fun n => eLpNorm (fun z => ψ z * (fderiv ℝ (fn n) z I - h z)) p
        (volume.restrict C)) atTop (𝓝 0) := by
      have hb : ∀ n, eLpNorm (fun z => ψ z * (fderiv ℝ (fn n) z I - h z)) p (volume.restrict C) ≤
          ENNReal.ofReal Bψ * eLpNorm (fun z => fderiv ℝ (fn n) z I - h z) p (volume.restrict C) := by
        intro n
        refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (c := Bψ) ?_ ?_ p
        · exact hψcont.aestronglyMeasurable.mul ((hfnyCont n).aestronglyMeasurable.sub hAEh)
        filter_upwards with z
        calc ‖ψ z * (fderiv ℝ (fn n) z I - h z)‖ = ‖ψ z‖ * ‖fderiv ℝ (fn n) z I - h z‖ :=
              norm_mul _ _
          _ ≤ Bψ * ‖fderiv ℝ (fn n) z I - h z‖ :=
              mul_le_mul_of_nonneg_right (hψb z) (norm_nonneg _)
      have hlim : Tendsto (fun n => ENNReal.ofReal Bψ *
          eLpNorm (fun z => fderiv ℝ (fn n) z I - h z) p (volume.restrict C)) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal Bψ) hc2
          (Or.inr ENNReal.ofReal_ne_top)
        simpa using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
        (Filter.Eventually.of_forall fun n => zero_le) (Filter.Eventually.of_forall hb)
    have hsumX : Tendsto (fun n => eLpNorm (fun z => (fn n z - f z) * fderiv ℝ ψ z 1) p
          (volume.restrict C) + eLpNorm (fun z => ψ z * (fderiv ℝ (fn n) z 1 - g z)) p
          (volume.restrict C)) atTop (𝓝 0) := by
      have := hcrossX.add hgtermX
      simpa using this
    have hsumY : Tendsto (fun n => eLpNorm (fun z => (fn n z - f z) * fderiv ℝ ψ z I) p
          (volume.restrict C) + eLpNorm (fun z => ψ z * (fderiv ℝ (fn n) z I - h z)) p
          (volume.restrict C)) atTop (𝓝 0) := by
      have := hcrossY.add hgtermY
      simpa using this
    have heqX : ∀ n, (fun z => fderiv ℝ (fun y => fn n y * ψ y) z 1 -
        (g z * ψ z + f z * fderiv ℝ ψ z 1)) =
        (fun z => (fn n z - f z) * fderiv ℝ ψ z 1) + (fun z => ψ z * (fderiv ℝ (fn n) z 1 - g z)) := by
      intro n
      funext z
      rw [hderiv1 n z]
      simp only [Pi.add_apply]
      ring
    have heqY : ∀ n, (fun z => fderiv ℝ (fun y => fn n y * ψ y) z I -
        (h z * ψ z + f z * fderiv ℝ ψ z I)) =
        (fun z => (fn n z - f z) * fderiv ℝ ψ z I) + (fun z => ψ z * (fderiv ℝ (fn n) z I - h z)) := by
      intro n
      funext z
      rw [hderiv2 n z]
      simp only [Pi.add_apply]
      ring
    constructor
    · simp_rw [heqX]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsumX
        (Filter.Eventually.of_forall fun n => zero_le) (Filter.Eventually.of_forall fun n => ?_)
      exact eLpNorm_add_le hp
    · simp_rw [heqY]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsumY
        (Filter.Eventually.of_forall fun n => zero_le) (Filter.Eventually.of_forall fun n => ?_)
      exact eLpNorm_add_le hp

/-- D3: the rectangle-integral vanishing hypothesis `hrect` needed for -f4's
`exists_contDiff_primitive_of_rect_integral_eq_zero`, for `P := fun z => F z * (1 + μ z)`,
`Q := fun z => I * (F z * (1 - μ z))`. -/
theorem wd_D3 {μ : ℂ → ℂ} (hμs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ) (hμc : HasCompactSupport μ)
    {k : ℝ} (hμ : ∀ z, ‖μ z‖ ≤ k) {p : ℝ} (hp : 2 < p) {F g h : ℂ → ℂ}
    (hGPF : HasGenPartials F (fun z => F z * g z) (fun z => F z * h z) univ (ENNReal.ofReal p))
    (hPDE : ∀ᵐ z, genDzbar (fun z => F z * g z) (fun z => F z * h z) z =
        dz μ z * F z + μ z * genDz (fun z => F z * g z) (fun z => F z * h z) z) :
    ∀ a b c d : ℝ, a < b → c < d →
      (∫ x in a..b, F ((x : ℂ) + (c : ℂ) * I) * (1 + μ ((x : ℂ) + (c : ℂ) * I)))
        + (∫ y in c..d, F ((b : ℂ) + (y : ℂ) * I) * (I * (1 - μ ((b : ℂ) + (y : ℂ) * I))))
        - (∫ x in a..b, F ((x : ℂ) + (d : ℂ) * I) * (1 + μ ((x : ℂ) + (d : ℂ) * I)))
        - (∫ y in c..d, F ((a : ℂ) + (y : ℂ) * I) * (I * (1 - μ ((a : ℂ) + (y : ℂ) * I)))) = 0 := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hk₀ : 0 ≤ k := (norm_nonneg (μ 0)).trans (hμ 0)
  have hμDiff : ∀ z, DifferentiableAt ℝ μ z := hμs.differentiable (by simp)
  -- bounds for `μ`'s classical partials
  have hμxCD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ μ z 1) :=
    (hμs.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
  have hμyCD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ μ z I) :=
    (hμs.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
  have hμxsub : tsupport (fun z => fderiv ℝ μ z 1) ⊆ tsupport μ := by
    apply closure_minimal _ (isClosed_tsupport μ)
    intro z hz
    by_contra hzn
    apply hz
    show fderiv ℝ μ z 1 = 0
    rw [fderiv_of_notMem_tsupport ℝ hzn]; simp
  have hμysub : tsupport (fun z => fderiv ℝ μ z I) ⊆ tsupport μ := by
    apply closure_minimal _ (isClosed_tsupport μ)
    intro z hz
    by_contra hzn
    apply hz
    show fderiv ℝ μ z I = 0
    rw [fderiv_of_notMem_tsupport ℝ hzn]; simp
  have hμxc : HasCompactSupport (fun z => fderiv ℝ μ z 1) :=
    hμc.isCompact.of_isClosed_subset (isClosed_tsupport _) hμxsub
  have hμyc : HasCompactSupport (fun z => fderiv ℝ μ z I) :=
    hμc.isCompact.of_isClosed_subset (isClosed_tsupport _) hμysub
  obtain ⟨Bx, hBx⟩ : ∃ B : ℝ, ∀ z, ‖fderiv ℝ μ z 1‖ ≤ B := by
    obtain ⟨C, hC⟩ := (hμxc.isCompact.image hμxCD.continuous.norm).bddAbove
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z ∈ tsupport (fun z => fderiv ℝ μ z 1)
    · exact (hC (mem_image_of_mem _ hz)).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]; exact le_max_right _ _
  obtain ⟨By, hBy⟩ : ∃ B : ℝ, ∀ z, ‖fderiv ℝ μ z I‖ ≤ B := by
    obtain ⟨C, hC⟩ := (hμyc.isCompact.image hμyCD.continuous.norm).bddAbove
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z ∈ tsupport (fun z => fderiv ℝ μ z I)
    · exact (hC (mem_image_of_mem _ hz)).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]; exact le_max_right _ _
  -- `ψ_P := 1 + μ`, `ψ_Q := I * (1 - μ)`
  have hψPCD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (1 : ℂ) + μ z) :=
    contDiff_const.add hμs
  have hψQCD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => I * ((1 : ℂ) - μ z)) :=
    contDiff_const.mul (contDiff_const.sub hμs)
  have hψPb : ∀ z, ‖(1 : ℂ) + μ z‖ ≤ 1 + k := fun z =>
    (norm_add_le _ _).trans (by simpa using add_le_add_left (hμ z) 1)
  have hψQb : ∀ z, ‖(I : ℂ) * ((1 : ℂ) - μ z)‖ ≤ 1 + k := fun z => by
    rw [norm_mul, Complex.norm_I, one_mul]
    exact (norm_sub_le _ _).trans (by simpa using add_le_add_left (hμ z) 1)
  have hψPderiv : ∀ z, fderiv ℝ (fun z => (1 : ℂ) + μ z) z = fderiv ℝ μ z := fun z =>
    fderiv_const_add (1 : ℂ)
  have hψQderiv : ∀ z, fderiv ℝ (fun z => I * ((1 : ℂ) - μ z)) z = I • (-fderiv ℝ μ z) := fun z => by
    have h2 : HasFDerivAt (fun z => (1 : ℂ) - μ z) (-fderiv ℝ μ z) z :=
      (hμDiff z).hasFDerivAt.const_sub 1
    exact (h2.const_mul I).fderiv
  have hψPxb : ∀ z, ‖fderiv ℝ (fun z => (1 : ℂ) + μ z) z 1‖ ≤ Bx := fun z => by
    rw [hψPderiv]; exact hBx z
  have hψPyb : ∀ z, ‖fderiv ℝ (fun z => (1 : ℂ) + μ z) z I‖ ≤ By := fun z => by
    rw [hψPderiv]; exact hBy z
  have hψQxb : ∀ z, ‖fderiv ℝ (fun z => I * ((1 : ℂ) - μ z)) z 1‖ ≤ Bx := fun z => by
    rw [hψQderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul,
      norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact hBx z
  have hψQyb : ∀ z, ‖fderiv ℝ (fun z => I * ((1 : ℂ) - μ z)) z I‖ ≤ By := fun z => by
    rw [hψQderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul,
      norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact hBy z
  -- apply the product rule for `HasGenPartials`
  have hGPP := hasGenPartials_mul_contDiff hp1 hGPF hψPCD (1 + k) Bx By hψPb hψPxb hψPyb
  have hGPQ := hasGenPartials_mul_contDiff hp1 hGPF hψQCD (1 + k) Bx By hψQb hψQxb hψQyb
  -- ACL + a.e. partial identification
  obtain ⟨hACLP, hPXeq, hPYeq⟩ := lemma9_2_isACL_of_genPartials isOpen_univ hp1 hGPP
  obtain ⟨hACLQ, hQXeq, hQYeq⟩ := lemma9_2_isACL_of_genPartials isOpen_univ hp1 hGPQ
  simp only [Measure.restrict_univ] at hPXeq hPYeq hQXeq hQYeq
  set P : ℂ → ℂ := fun z => F z * (1 + μ z) with hPdef
  set Q : ℂ → ℂ := fun z => F z * (I * (1 - μ z)) with hQdef
  -- local integrability of the classical partials, via `MemLp` on compacts
  have hlocY : ∀ C ⊆ (univ : Set ℂ), IsCompact C → IntegrableOn (partialY P) C := by
    intro C hC hCcpt
    haveI : IsFiniteMeasure (volume.restrict C) :=
      isFiniteMeasure_restrict.2 hCcpt.isBounded.measure_lt_top.ne
    obtain ⟨-, hMh⟩ := hGPP.1 C hC hCcpt
    refine (hMh.integrable hp1).congr ?_
    filter_upwards [hPYeq.filter_mono (ae_mono (Measure.restrict_le_self (s := C)))] with z hz
    exact hz.symm
  have hlocX : ∀ C ⊆ (univ : Set ℂ), IsCompact C → IntegrableOn (partialX Q) C := by
    intro C hC hCcpt
    haveI : IsFiniteMeasure (volume.restrict C) :=
      isFiniteMeasure_restrict.2 hCcpt.isBounded.measure_lt_top.ne
    obtain ⟨hMg, -⟩ := hGPQ.1 C hC hCcpt
    refine (hMg.integrable hp1).congr ?_
    filter_upwards [hQXeq.filter_mono (ae_mono (Measure.restrict_le_self (s := C)))] with z hz
    exact hz.symm
  -- the a.e. cancellation identity `∂ₓQ = ∂_yP`, from D2's PDE
  have hae0 : (fun z => partialX Q z - partialY P z) =ᵐ[volume] (fun _ => (0 : ℂ)) := by
    filter_upwards [hQXeq, hPYeq, hPDE] with z hQX hPY hpde
    show partialX Q z - partialY P z = 0
    rw [hQX, hPY, hψQderiv, hψPderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul]
    have hpde' : F z * g z + I * (F z * h z) =
        2 * (dz μ z * F z) + μ z * (F z * g z - I * (F z * h z)) := by
      have h1 := hpde
      change (F z * g z + I * (F z * h z)) / 2 = dz μ z * F z +
          μ z * ((F z * g z - I * (F z * h z)) / 2) at h1
      linear_combination 2 * h1
    have hdzμ : dz μ z = (fderiv ℝ μ z 1 - I * fderiv ℝ μ z I) / 2 := rfl
    field_simp
    rw [hdzμ] at hpde'
    linear_combination I * hpde' -
      (F z * (fderiv ℝ μ z I + μ z * h z + h z)) * I_sq
  intro a b c d hab hcd
  have hR : closedRect a b c d ⊆ (univ : Set ℂ) := subset_univ _
  have hgreen1 := eq9_9_green hACLP hlocY hab hcd hR
  have hgreen2 := eq9_10_green hACLQ hlocX hab hcd hR
  have hint1 : IntegrableOn (partialY P) (openRect a b c d) :=
    (hlocY _ hR (isCompact_closedRect a b c d)).mono_set (openRect_subset_closedRect a b c d)
  have hint2 : IntegrableOn (partialX Q) (openRect a b c d) :=
    (hlocX _ hR (isCompact_closedRect a b c d)).mono_set (openRect_subset_closedRect a b c d)
  have hzero : (∫ z in openRect a b c d, partialX Q z) - ∫ z in openRect a b c d, partialY P z = 0 := by
    rw [← integral_sub hint2 hint1]
    rw [integral_congr_ae (hae0.filter_mono (ae_mono Measure.restrict_le_self))]
    simp
  calc (∫ x in a..b, P ((x : ℂ) + (c : ℂ) * I)) + (∫ y in c..d, Q ((b : ℂ) + (y : ℂ) * I))
      - (∫ x in a..b, P ((x : ℂ) + (d : ℂ) * I)) - (∫ y in c..d, Q ((a : ℂ) + (y : ℂ) * I))
      = ((∫ x in a..b, P ((x : ℂ) + (c : ℂ) * I)) - ∫ x in a..b, P ((x : ℂ) + (d : ℂ) * I)) +
        ((∫ y in c..d, Q ((b : ℂ) + (y : ℂ) * I)) - ∫ y in c..d, Q ((a : ℂ) + (y : ℂ) * I)) := by
        ring
    _ = -(∫ z in openRect a b c d, partialY P z) + ∫ z in openRect a b c d, partialX Q z := by
        rw [hgreen1, hgreen2]
    _ = (∫ z in openRect a b c d, partialX Q z) - ∫ z in openRect a b c d, partialY P z := by ring
    _ = 0 := hzero

/-- Additive combinator for `HasGenPartials` (needed for D7's Weyl-lemma application to
`w̃ - id - T(ω*)`). -/
theorem hasGenPartials_sub {f1 g1 h1 f2 g2 h2 : ℂ → ℂ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (H1 : HasGenPartials f1 g1 h1 univ p) (H2 : HasGenPartials f2 g2 h2 univ p) :
    HasGenPartials (fun z => f1 z - f2 z) (fun z => g1 z - g2 z) (fun z => h1 z - h2 z) univ p := by
  obtain ⟨hM1, fn1, hCD1, hTLU1, hConv1⟩ := H1
  obtain ⟨hM2, fn2, hCD2, hTLU2, hConv2⟩ := H2
  have hDiff1 : ∀ n z, DifferentiableAt ℝ (fn1 n) z := fun n z =>
    differentiableOn_univ.mp ((hCD1 n).differentiableOn one_ne_zero) z
  have hDiff2 : ∀ n z, DifferentiableAt ℝ (fn2 n) z := fun n z =>
    differentiableOn_univ.mp ((hCD2 n).differentiableOn one_ne_zero) z
  refine ⟨?_, fun n z => fn1 n z - fn2 n z, fun n => (hCD1 n).sub (hCD2 n), hTLU1.sub hTLU2, ?_⟩
  · intro C hC hCcpt
    obtain ⟨hg1, hh1⟩ := hM1 C hC hCcpt
    obtain ⟨hg2, hh2⟩ := hM2 C hC hCcpt
    exact ⟨hg1.sub hg2, hh1.sub hh2⟩
  · intro C hC hCcpt
    obtain ⟨hcx1, hcy1⟩ := hConv1 C hC hCcpt
    obtain ⟨hcx2, hcy2⟩ := hConv2 C hC hCcpt
    obtain ⟨hg1, hh1⟩ := hM1 C hC hCcpt
    obtain ⟨hg2, hh2⟩ := hM2 C hC hCcpt
    have hfn1CDglobal : ∀ n, ContDiff ℝ 1 (fn1 n) := fun n => contDiffOn_univ.mp (hCD1 n)
    have hfn2CDglobal : ∀ n, ContDiff ℝ 1 (fn2 n) := fun n => contDiffOn_univ.mp (hCD2 n)
    have hfn1xCont : ∀ n, Continuous (fun z => fderiv ℝ (fn1 n) z 1) := fun n =>
      ((hfn1CDglobal n).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hfn1yCont : ∀ n, Continuous (fun z => fderiv ℝ (fn1 n) z I) := fun n =>
      ((hfn1CDglobal n).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hfn2xCont : ∀ n, Continuous (fun z => fderiv ℝ (fn2 n) z 1) := fun n =>
      ((hfn2CDglobal n).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hfn2yCont : ∀ n, Continuous (fun z => fderiv ℝ (fn2 n) z I) := fun n =>
      ((hfn2CDglobal n).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have heqx : ∀ n, (fun z => fderiv ℝ (fun y => fn1 n y - fn2 n y) z 1 - (g1 z - g2 z)) =
        (fun z => fderiv ℝ (fn1 n) z 1 - g1 z) - fun z => fderiv ℝ (fn2 n) z 1 - g2 z := by
      intro n
      funext z
      rw [fderiv_fun_sub (hDiff1 n z) (hDiff2 n z)]
      simp only [ContinuousLinearMap.sub_apply, Pi.sub_apply]
      ring
    have heqy : ∀ n, (fun z => fderiv ℝ (fun y => fn1 n y - fn2 n y) z I - (h1 z - h2 z)) =
        (fun z => fderiv ℝ (fn1 n) z I - h1 z) - fun z => fderiv ℝ (fn2 n) z I - h2 z := by
      intro n
      funext z
      rw [fderiv_fun_sub (hDiff1 n z) (hDiff2 n z)]
      simp only [ContinuousLinearMap.sub_apply, Pi.sub_apply]
      ring
    constructor
    · simp_rw [heqx]
      have hbound : ∀ n, eLpNorm ((fun z => fderiv ℝ (fn1 n) z 1 - g1 z) -
          fun z => fderiv ℝ (fn2 n) z 1 - g2 z) p (volume.restrict C) ≤
          eLpNorm (fun z => fderiv ℝ (fn1 n) z 1 - g1 z) p (volume.restrict C) +
          eLpNorm (fun z => fderiv ℝ (fn2 n) z 1 - g2 z) p (volume.restrict C) :=
        fun n => eLpNorm_sub_le hp
      have hlim : Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (fn1 n) z 1 - g1 z) p
          (volume.restrict C) + eLpNorm (fun z => fderiv ℝ (fn2 n) z 1 - g2 z) p
          (volume.restrict C)) atTop (𝓝 0) := by
        have := hcx1.add hcx2
        simpa using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
        (Filter.Eventually.of_forall fun n => zero_le) (Filter.Eventually.of_forall hbound)
    · simp_rw [heqy]
      have hbound : ∀ n, eLpNorm ((fun z => fderiv ℝ (fn1 n) z I - h1 z) -
          fun z => fderiv ℝ (fn2 n) z I - h2 z) p (volume.restrict C) ≤
          eLpNorm (fun z => fderiv ℝ (fn1 n) z I - h1 z) p (volume.restrict C) +
          eLpNorm (fun z => fderiv ℝ (fn2 n) z I - h2 z) p (volume.restrict C) :=
        fun n => eLpNorm_sub_le hp
      have hlim : Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (fn1 n) z I - h1 z) p
          (volume.restrict C) + eLpNorm (fun z => fderiv ℝ (fn2 n) z I - h2 z) p
          (volume.restrict C)) atTop (𝓝 0) := by
        have := hcy1.add hcy2
        simpa using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
        (Filter.Eventually.of_forall fun n => zero_le) (Filter.Eventually.of_forall hbound)

/-- D4: the C¹ primitive `w̃` glued from D3's `hrect`, with its Beltrami-type equation and
positive Jacobian. -/
theorem wd_D4 {μ : ℂ → ℂ} {k : ℝ} (hk : k < 1) (hμs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ)
    (hμc : HasCompactSupport μ) (hμ : ∀ z, ‖μ z‖ ≤ k) {p : ℝ} (hp : 2 < p)
    (hkp : k * hilbertNorm p < 1) :
    ∃ omt wtilde : ℂ → ℂ,
      MemLp omt (ENNReal.ofReal p) ∧ Bornology.IsBounded (Function.support omt) ∧
      (omt =ᵐ[volume] fun z => μ z * hilbertH omt z + dz μ z) ∧
      ContDiff ℝ 1 wtilde ∧
      (∀ z, dz wtilde z = Complex.exp (cauchyT omt z)) ∧
      (∀ z, dzbar wtilde z = μ z * Complex.exp (cauchyT omt z)) ∧
      ∀ z, 0 < jacobian wtilde z := by
  obtain ⟨omt, homtMemLp, homtBdd, homtSol, hGPF, hPDE⟩ := wd_D2 hk hμs hμc hμ hp hkp
  set bigF : ℂ → ℂ := fun z => Complex.exp (cauchyT omt z) with hbigFdef
  have hGPomt := thm11_1 hp homtMemLp homtBdd
  have hcTcont : Continuous (cauchyT omt) := by
    obtain ⟨-, fn, hfn, hconv, -⟩ := hGPomt.1
    have := hconv.continuousOn (Filter.Frequently.of_forall fun n => (hfn n).continuousOn)
    rwa [continuousOn_univ] at this
  have hbigFcont : Continuous bigF := Complex.continuous_exp.comp hcTcont
  have hPcont : Continuous (fun z => bigF z * (1 + μ z)) :=
    hbigFcont.mul (continuous_const.add hμs.continuous)
  have hQcont : Continuous (fun z => bigF z * (I * (1 - μ z))) :=
    hbigFcont.mul (continuous_const.mul (continuous_const.sub hμs.continuous))
  have hrect := wd_D3 hμs hμc hμ hp hGPF hPDE
  obtain ⟨wtilde, hwtildeCD, hwtildeDeriv⟩ :=
    exists_contDiff_primitive_of_rect_integral_eq_zero hPcont hQcont hrect
  have hIQ : ∀ z, I * (bigF z * (I * (1 - μ z))) = -(bigF z * (1 - μ z)) := by
    intro z
    have h1 : I * (bigF z * (I * (1 - μ z))) = I ^ 2 * (bigF z * (1 - μ z)) := by ring
    rw [h1, I_sq]; ring
  have hdz : ∀ z, dz wtilde z = bigF z := by
    intro z
    obtain ⟨hP, hQ⟩ := hwtildeDeriv z
    show (fderiv ℝ wtilde z 1 - I * fderiv ℝ wtilde z I) / 2 = bigF z
    rw [hP, hQ, hIQ]; ring
  have hdzbar : ∀ z, dzbar wtilde z = μ z * bigF z := by
    intro z
    obtain ⟨hP, hQ⟩ := hwtildeDeriv z
    show (fderiv ℝ wtilde z 1 + I * fderiv ℝ wtilde z I) / 2 = μ z * bigF z
    rw [hP, hQ, hIQ]; ring
  refine ⟨omt, wtilde, homtMemLp, homtBdd, homtSol, hwtildeCD, hdz, hdzbar, fun z => ?_⟩
  show 0 < ‖dz wtilde z‖ ^ 2 - ‖dzbar wtilde z‖ ^ 2
  rw [hdz, hdzbar, norm_mul]
  have hbigFpos : 0 < ‖bigF z‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hμk : ‖μ z‖ < 1 := lt_of_le_of_lt (hμ z) hk
  have h2 : ‖μ z‖ ^ 2 < 1 := by nlinarith [norm_nonneg (μ z)]
  have h3 : ‖bigF z‖ ^ 2 * ‖μ z‖ ^ 2 < ‖bigF z‖ ^ 2 * 1 :=
    mul_lt_mul_of_pos_left h2 (by positivity)
  nlinarith [h3]


/-- D5+D7: identify `w̃` with `z + T(ω) + a` for the GIVEN `ω` solving the standard equation, and
get `w̃ − z` bounded along the way. -/
theorem wd_D5_D7 {μ : ℂ → ℂ} {k : ℝ} (hk : k < 1) (hμs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ)
    (hμc : HasCompactSupport μ) (hμ : ∀ z, ‖μ z‖ ≤ k) {p : ℝ} (hp : 2 < p)
    (hkp : k * hilbertNorm p < 1) {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p))
    (hsol : ω =ᵐ[volume] fun z => μ z * hilbertH ω z + μ z) :
    ∃ a : ℂ, ∃ wtilde : ℂ → ℂ, wtilde = (fun z => z + cauchyT ω z + a) ∧
      ContDiff ℝ 1 wtilde ∧ (∀ z, dzbar wtilde z = μ z * dz wtilde z) ∧
      (∀ z, 0 < jacobian wtilde z) ∧ ∃ M : ℝ, ∀ z, ‖wtilde z - z‖ ≤ M := by
  have hk₀ : 0 ≤ k := (norm_nonneg (μ 0)).trans (hμ 0)
  obtain ⟨omt, wtilde, homtMemLp, homtBdd, homtSol, hwtildeCD, hdz, hdzbar, hJ⟩ :=
    wd_D4 hk hμs hμc hμ hp hkp
  set bigF : ℂ → ℂ := fun z => Complex.exp (cauchyT omt z) with hbigFdef
  have hp1 : (1 : ℝ) < p := by linarith
  have hp1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1.le
  -- `bigF` is bounded
  obtain ⟨R₀, hR₀⟩ := homtBdd.subset_closedBall (0 : ℂ)
  have hR₀' : (0:ℝ) < max R₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set R : ℝ := max R₀ 1 with hRdef
  have homtsupp : ∀ z, R < ‖z‖ → omt z = 0 := fun z hz => by
    by_contra h
    have hmem : z ∈ closedBall (0:ℂ) R₀ := hR₀ h
    rw [mem_closedBall_zero_iff] at hmem
    have : R₀ ≤ R := le_max_left _ _
    linarith
  obtain ⟨M₁, hM₁⟩ := lemma11_1 hp hR₀'
  set MF' : ℝ := M₁ * (eLpNorm omt (ENNReal.ofReal p)).toReal with hMF'def
  have hcauchyTbdd : ∀ z, ‖cauchyT omt z‖ ≤ MF' := fun z => hM₁ omt homtMemLp homtsupp z
  have hMF'nn : 0 ≤ MF' := (norm_nonneg _).trans (hcauchyTbdd 0)
  set MF : ℝ := Real.exp MF' with hMFdef
  have hbigFbdd : ∀ z, ‖bigF z‖ ≤ MF := fun z => by
    show ‖Complex.exp (cauchyT omt z)‖ ≤ MF
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (hcauchyTbdd z))
  have hMFnn : (0:ℝ) ≤ MF := (norm_nonneg (bigF 0)).trans (hbigFbdd 0)
  -- `fderiv w̃` at each point, from `dz`/`dzbar`
  have hderiv1 : ∀ z, fderiv ℝ wtilde z 1 = bigF z + μ z * bigF z := fun z => by
    have h1 := hdz z
    have h2 := hdzbar z
    change (fderiv ℝ wtilde z 1 - I * fderiv ℝ wtilde z I) / 2 = bigF z at h1
    change (fderiv ℝ wtilde z 1 + I * fderiv ℝ wtilde z I) / 2 = μ z * bigF z at h2
    linear_combination h1 + h2
  have hderiv2 : ∀ z, fderiv ℝ wtilde z I = I * bigF z * (1 - μ z) := fun z => by
    have h1 := hdz z
    have h2 := hdzbar z
    change (fderiv ℝ wtilde z 1 - I * fderiv ℝ wtilde z I) / 2 = bigF z at h1
    change (fderiv ℝ wtilde z 1 + I * fderiv ℝ wtilde z I) / 2 = μ z * bigF z at h2
    linear_combination I * h1 - I * h2 + (fderiv ℝ wtilde z I) * I_sq
  -- operator-norm bound for `fderiv w̃`, hence `w̃` is Lipschitz
  have hopnorm : ∀ z, ‖fderiv ℝ wtilde z‖ ≤ 2 * MF * (1 + k) := by
    intro z
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    have hveq : v = v.re • (1 : ℂ) + v.im • (I : ℂ) := by
      simp [Complex.real_smul]
    conv_lhs => rw [hveq, map_add, map_smul, map_smul]
    have hb1 : ‖fderiv ℝ wtilde z 1‖ ≤ MF * (1 + k) := by
      rw [hderiv1]
      calc ‖bigF z + μ z * bigF z‖ ≤ ‖bigF z‖ + ‖μ z * bigF z‖ := norm_add_le _ _
        _ ≤ MF + k * MF := by
            gcongr
            · exact hbigFbdd z
            · rw [norm_mul]; exact mul_le_mul (hμ z) (hbigFbdd z) (norm_nonneg _) hk₀
        _ = MF * (1 + k) := by ring
    have hb2 : ‖fderiv ℝ wtilde z I‖ ≤ MF * (1 + k) := by
      rw [hderiv2]
      calc ‖I * bigF z * (1 - μ z)‖ = ‖bigF z‖ * ‖1 - μ z‖ := by
              rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
        _ ≤ MF * (1 + k) := by
            apply mul_le_mul (hbigFbdd z) _ (norm_nonneg _) hMFnn
            calc ‖(1:ℂ) - μ z‖ ≤ ‖(1:ℂ)‖ + ‖μ z‖ := norm_sub_le _ _
              _ ≤ 1 + k := by rw [norm_one]; linarith [hμ z]
    calc ‖v.re • fderiv ℝ wtilde z 1 + v.im • fderiv ℝ wtilde z I‖
        ≤ ‖v.re • fderiv ℝ wtilde z 1‖ + ‖v.im • fderiv ℝ wtilde z I‖ := norm_add_le _ _
      _ = |v.re| * ‖fderiv ℝ wtilde z 1‖ + |v.im| * ‖fderiv ℝ wtilde z I‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖v‖ * (MF * (1+k)) + ‖v‖ * (MF * (1+k)) := by
            gcongr
            · exact Complex.abs_re_le_norm v
            · exact Complex.abs_im_le_norm v
      _ = 2 * MF * (1 + k) * ‖v‖ := by ring
  have hwtildeDiff : Differentiable ℝ wtilde := hwtildeCD.differentiable one_ne_zero
  have hLip : LipschitzWith (Real.toNNReal (2 * MF * (1 + k))) wtilde := by
    apply lipschitzWith_of_nnnorm_fderiv_le hwtildeDiff
    intro z
    rw [← NNReal.coe_le_coe]
    simp only [coe_nnnorm, Real.coe_toNNReal', max_eq_left (by positivity : (0:ℝ) ≤ 2*MF*(1+k))]
    exact hopnorm z
  set CL : ℝ := 2 * MF * (1 + k) with hCLdef
  have hCLnn : 0 ≤ CL := by positivity
  have hLipbd : ∀ z, ‖wtilde z - wtilde 0‖ ≤ CL * ‖z‖ := by
    intro z
    have := hLip.dist_le_mul z 0
    rwa [dist_eq_norm, dist_eq_norm, sub_zero, Real.coe_toNNReal' , max_eq_left hCLnn] at this
  have hwtildeGrowth : ∀ z, ‖wtilde z - z‖ ≤ (CL + 1) * ‖z‖ + ‖wtilde 0‖ := fun z => by
    have heq : wtilde z - z = (wtilde z - wtilde 0) + (wtilde 0 - z) := by ring
    rw [heq]
    calc ‖(wtilde z - wtilde 0) + (wtilde 0 - z)‖
        ≤ ‖wtilde z - wtilde 0‖ + ‖wtilde 0 - z‖ := norm_add_le _ _
      _ ≤ CL * ‖z‖ + (‖wtilde 0‖ + ‖z‖) := by
            gcongr
            · exact hLipbd z
            · exact norm_sub_le _ _
      _ = (CL + 1) * ‖z‖ + ‖wtilde 0‖ := by ring
  -- a C¹ function trivially has `HasGenPartials` (approximant sequence = itself)
  have hGPtrivial : ∀ f : ℂ → ℂ, ContDiff ℝ 1 f →
      HasGenPartials f (fun z => fderiv ℝ f z 1) (fun z => fderiv ℝ f z I) univ
        (ENNReal.ofReal p) := by
    intro f hfCD
    have hcont1 : Continuous (fun z => fderiv ℝ f z 1) :=
      (hfCD.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hcont2 : Continuous (fun z => fderiv ℝ f z I) :=
      (hfCD.continuous_fderiv one_ne_zero).clm_apply continuous_const
    refine ⟨?_, fun _ => f, fun _ => hfCD.contDiffOn, ?_, ?_⟩
    · intro C hC hCcpt
      haveI : IsFiniteMeasure (volume.restrict C) :=
        isFiniteMeasure_restrict.2 hCcpt.isBounded.measure_lt_top.ne
      obtain ⟨B1, hB1⟩ := (hCcpt.image hcont1.norm).bddAbove
      obtain ⟨B2, hB2⟩ := (hCcpt.image hcont2.norm).bddAbove
      refine ⟨MemLp.of_bound hcont1.aestronglyMeasurable (max B1 0) ?_,
        MemLp.of_bound hcont2.aestronglyMeasurable (max B2 0) ?_⟩
      · rw [ae_restrict_iff' hCcpt.isClosed.measurableSet]
        filter_upwards with z hz
        exact (hB1 (mem_image_of_mem _ hz)).trans (le_max_left _ _)
      · rw [ae_restrict_iff' hCcpt.isClosed.measurableSet]
        filter_upwards with z hz
        exact (hB2 (mem_image_of_mem _ hz)).trans (le_max_left _ _)
    · have hUC : TendstoUniformlyOn (fun (_ : ℕ) => f) f atTop univ := by
        intro u hu
        filter_upwards with n z _
        exact refl_mem_uniformity hu
      exact hUC.tendstoLocallyUniformlyOn
    · intro C hC hCcpt
      constructor
      · simp
      · simp
  have hGPwtilde := hGPtrivial wtilde hwtildeCD
  have hGPid := hGPtrivial (fun z => z) (contDiff_id.of_le le_top)
  have hcTomtCont : Continuous (cauchyT omt) := by
    obtain ⟨-, fn, hfn, hconv, -⟩ := (thm11_1 hp homtMemLp homtBdd).1
    have := hconv.continuousOn (Filter.Frequently.of_forall fun n => (hfn n).continuousOn)
    rwa [continuousOn_univ] at this
  have hbigFcont : Continuous bigF := Complex.continuous_exp.comp hcTomtCont
  -- `ω* := μ·F`: bounded, compact support, hence `MemLp`
  set omstar : ℂ → ℂ := fun z => μ z * bigF z with homstardef
  have homstarBdd : ∀ z, ‖omstar z‖ ≤ k * MF := fun z => by
    show ‖μ z * bigF z‖ ≤ k * MF
    rw [norm_mul]; exact mul_le_mul (hμ z) (hbigFbdd z) (norm_nonneg _) hk₀
  obtain ⟨Rμ0, hRμ0⟩ := hμc.isBounded.subset_closedBall (0:ℂ)
  set Rμ : ℝ := max Rμ0 1 with hRμdef
  have hRμ' : (0:ℝ) < Rμ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hRμ : tsupport μ ⊆ closedBall (0:ℂ) Rμ :=
    hRμ0.trans (closedBall_subset_closedBall (le_max_left _ _))
  have homstarsupp : ∀ z, Rμ < ‖z‖ → omstar z = 0 := fun z hz => by
    show μ z * bigF z = 0
    have hμz0 : μ z = 0 := by
      by_contra h
      have : z ∈ tsupport μ := subset_closure h
      have hb := hRμ this
      rw [mem_closedBall_zero_iff] at hb
      linarith
    rw [hμz0, zero_mul]
  have homstarc : HasCompactSupport omstar := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:ℂ) Rμ)
    intro z hz
    rw [mem_closedBall_zero_iff]
    by_contra h
    push Not at h
    exact hz (homstarsupp z h)
  have homstarMemLp : MemLp omstar (ENNReal.ofReal p) :=
    HasCompactSupport.memLp_of_bound homstarc
      ((show Continuous omstar from hμs.continuous.mul hbigFcont).aestronglyMeasurable)
      (max (k*MF) 0)
      (Filter.Eventually.of_forall fun z => (homstarBdd z).trans (le_max_left _ _))
  have homstarBddSupp : Bornology.IsBounded (Function.support omstar) :=
    homstarc.isCompact.isBounded.subset (subset_tsupport _)
  obtain ⟨M₂, hM₂⟩ := lemma11_1 hp hRμ'
  set MT : ℝ := M₂ * (eLpNorm omstar (ENNReal.ofReal p)).toReal with hMTdef
  have hcauchyTomstarBdd : ∀ z, ‖cauchyT omstar z‖ ≤ MT := fun z => hM₂ omstar homstarMemLp homstarsupp z
  have hGPomstar := thm11_1 hp homstarMemLp homstarBddSupp
  obtain ⟨hGPcT, hgenDzbarcT, hgenDzcT⟩ := hGPomstar
  -- `h := w̃ - id - T(ω*)` has generalized partials via subtraction
  have hGPh := hasGenPartials_sub hp1' (hasGenPartials_sub hp1' hGPwtilde hGPid) hGPcT
  have hfderivid1 : ∀ z : ℂ, fderiv ℝ (fun z => z) z 1 = 1 := fun z => by simp
  have hfderividI : ∀ z : ℂ, fderiv ℝ (fun z => z) z I = I := fun z => by simp
  simp only [hfderivid1, hfderividI] at hGPh
  set g_combo : ℂ → ℂ := fun z => fderiv ℝ wtilde z 1 - 1 -
      (hilbertH omstar z + omstar z) with hgcombodef
  set h_combo : ℂ → ℂ := fun z => fderiv ℝ wtilde z I - I -
      I * (hilbertH omstar z - omstar z) with hhcombodef
  have hzero : ∀ z, genDzbar g_combo h_combo z = 0 := by
    intro z
    have hgc : genDzbar g_combo h_combo z =
        (fderiv ℝ wtilde z 1 - 1 - (hilbertH omstar z + omstar z) +
          I * (fderiv ℝ wtilde z I - I - I * (hilbertH omstar z - omstar z))) / 2 := rfl
    rw [hgc, hderiv1, hderiv2]
    have : omstar z = μ z * bigF z := rfl
    linear_combination ((bigF z - hilbertH omstar z - 1) / 2) * I_sq
  set hfun : ℂ → ℂ := fun z => wtilde z - z - cauchyT omstar z with hhfundef
  have hhDiff : Differentiable ℂ hfun :=
    differentiable_of_genDzbar_eq_zero hp hGPh (Filter.Eventually.of_forall hzero)
  have hcTomstarCont : Continuous (cauchyT omstar) := by
    obtain ⟨-, fn, hfn, hconv, -⟩ := hGPcT
    have := hconv.continuousOn (Filter.Frequently.of_forall fun n => (hfn n).continuousOn)
    rwa [continuousOn_univ] at this
  have hhGrowth : ∀ z, ‖hfun z‖ ≤ (CL + 1) * ‖z‖ + (‖wtilde 0‖ + MT) := fun z => by
    show ‖wtilde z - z - cauchyT omstar z‖ ≤ _
    calc ‖wtilde z - z - cauchyT omstar z‖ ≤ ‖wtilde z - z‖ + ‖cauchyT omstar z‖ := norm_sub_le _ _
      _ ≤ ((CL + 1) * ‖z‖ + ‖wtilde 0‖) + MT := add_le_add (hwtildeGrowth z) (hcauchyTomstarBdd z)
      _ = (CL + 1) * ‖z‖ + (‖wtilde 0‖ + MT) := by ring
  have hdslopeDiff : Differentiable ℂ (dslope hfun 0) :=
    differentiableOn_univ.mp ((differentiableOn_dslope (Filter.univ_mem)).mpr
      (differentiableOn_univ.mpr hhDiff))
  have hdslopeBdd : Bornology.IsBounded (Set.range (dslope hfun 0)) := by
    set A : ℝ := CL + 1 with hAdef
    set B : ℝ := ‖wtilde 0‖ + MT with hBdef
    have hAnn : 0 ≤ A := by positivity
    have hBnn : 0 ≤ B := add_nonneg (norm_nonneg _) ((norm_nonneg _).trans (hcauchyTomstarBdd 0))
    have hbig : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖dslope hfun 0 z‖ ≤ A + B + ‖hfun 0‖ := by
      intro z hz
      have hzne : z ≠ 0 := fun h => by rw [h, norm_zero] at hz; norm_num at hz
      rw [dslope_of_ne _ hzne, slope_def_module]
      have hz0 : (0:ℝ) < ‖z‖ := lt_of_lt_of_le one_pos hz
      calc ‖(z - 0)⁻¹ • (hfun z - hfun 0)‖ = ‖z‖⁻¹ * ‖hfun z - hfun 0‖ := by
            rw [sub_zero, norm_smul, norm_inv]
        _ ≤ ‖z‖⁻¹ * (‖hfun z‖ + ‖hfun 0‖) := by
            gcongr; exact norm_sub_le _ _
        _ ≤ ‖z‖⁻¹ * ((A * ‖z‖ + B) + ‖hfun 0‖) := by
            gcongr; exact hhGrowth z
        _ = A + (B + ‖hfun 0‖) * ‖z‖⁻¹ := by field_simp; ring
        _ ≤ A + (B + ‖hfun 0‖) * 1 := by
            gcongr
            rw [inv_le_one_iff₀]; right; exact hz
        _ = A + B + ‖hfun 0‖ := by ring
    obtain ⟨C, hC⟩ := ((isCompact_closedBall (0:ℂ) 1).image
      hdslopeDiff.continuous.norm).bddAbove
    rw [isBounded_iff_forall_norm_le]
    refine ⟨max (A + B + ‖hfun 0‖) C, ?_⟩
    rintro x ⟨z, rfl⟩
    by_cases hz : 1 ≤ ‖z‖
    · exact (hbig z hz).trans (le_max_left _ _)
    · exact (hC (mem_image_of_mem _ (mem_closedBall_zero_iff.mpr (not_le.mp hz).le))).trans
        (le_max_right _ _)
  obtain ⟨c, hc⟩ := hdslopeDiff.exists_const_forall_eq_of_bounded hdslopeBdd
  have haffine : ∀ z, hfun z = hfun 0 + c * z := by
    intro z
    rcases eq_or_ne z 0 with rfl | hzne
    · simp
    · have hcz := hc z
      rw [dslope_of_ne _ hzne, slope_def_module, sub_zero] at hcz
      have hzinv : z * z⁻¹ = 1 := mul_inv_cancel₀ hzne
      have : hfun z - hfun 0 = z • c := by rw [← hcz, smul_smul, hzinv, one_smul]
      linear_combination this
  -- `T(omt) → 0` at infinity (direct L¹ estimate, no truncation needed)
  have hcTomt_decay : Tendsto (cauchyT omt) (cocompact ℂ) (𝓝 0) := by
    haveI : IsFiniteMeasure (volume.restrict (closedBall (0:ℂ) R)) :=
      isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
    have hIntOn : IntegrableOn omt (closedBall (0:ℂ) R) :=
      (homtMemLp.mono_measure Measure.restrict_le_self).integrable hp1'
    set L : ℝ := ∫ ζ in closedBall (0:ℂ) R, ‖omt ζ‖ with hLdef
    have hLnn : 0 ≤ L := setIntegral_nonneg measurableSet_closedBall (fun _ _ => norm_nonneg _)
    have heq : ∀ z : ℂ, R < ‖z‖ →
        cauchyT omt z = -(1/π : ℂ) * ∫ ζ in closedBall (0:ℂ) R, omt ζ / (ζ - z) := by
      intro z hz
      show -(1/π : ℂ) * ∫ ζ, omt ζ / (ζ - z) = _
      congr 1
      rw [← setIntegral_univ]
      apply setIntegral_eq_of_subset_of_forall_diff_eq_zero MeasurableSet.univ
        (subset_univ _)
      intro ζ hζ
      have hζ2 : R < ‖ζ‖ := by
        have := hζ.2
        rwa [mem_closedBall_zero_iff, not_le] at this
      rw [homtsupp ζ hζ2, zero_div]
    have hbound : ∀ z : ℂ, R < ‖z‖ → ‖cauchyT omt z‖ ≤ (1/π) * (‖z‖ - R)⁻¹ * L := by
      intro z hz
      rw [heq z hz, norm_mul]
      have h1 : ‖(-(1/π : ℂ))‖ = 1/π := by
        rw [norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      rw [h1]
      have hkbound : ∀ ζ ∈ closedBall (0:ℂ) R, ‖omt ζ / (ζ - z)‖ ≤ (‖z‖ - R)⁻¹ * ‖omt ζ‖ := by
        intro ζ hζ
        rw [mem_closedBall_zero_iff] at hζ
        have h1 : ‖z‖ - R ≤ ‖ζ - z‖ := by
          have h2 : ‖z‖ - ‖ζ‖ ≤ ‖z - ζ‖ := by linarith [norm_sub_norm_le z ζ]
          have h3 : ‖z - ζ‖ = ‖ζ - z‖ := norm_sub_rev z ζ
          nlinarith [hζ]
        have hpos : (0:ℝ) < ‖z‖ - R := by linarith
        have hζzpos : (0:ℝ) < ‖ζ - z‖ := lt_of_lt_of_le hpos h1
        rw [norm_div, div_eq_mul_inv, mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [inv_le_inv₀ hζzpos hpos]
        exact h1
      have hLHSmeas : AEStronglyMeasurable (fun ζ : ℂ => ‖omt ζ / (ζ - z)‖)
          (volume.restrict (closedBall (0:ℂ) R)) := by
        have hωAEM : AEMeasurable omt (volume.restrict (closedBall (0:ℂ) R)) :=
          hIntOn.aestronglyMeasurable.aemeasurable
        have hdenAEM : AEMeasurable (fun ζ : ℂ => ζ - z) (volume.restrict (closedBall (0:ℂ) R)) :=
          (continuous_id.sub continuous_const).aemeasurable
        exact (hωAEM.div hdenAEM).aestronglyMeasurable.norm
      have hLHSint : IntegrableOn (fun ζ => ‖omt ζ / (ζ - z)‖) (closedBall (0:ℂ) R) := by
        apply Integrable.mono' (hIntOn.norm.const_mul ((‖z‖ - R)⁻¹)) hLHSmeas
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with ζ hζ
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hkbound ζ hζ
      have h2 : ‖∫ ζ in closedBall (0:ℂ) R, omt ζ / (ζ - z)‖ ≤ (‖z‖ - R)⁻¹ * L := by
        calc ‖∫ ζ in closedBall (0:ℂ) R, omt ζ / (ζ - z)‖
            ≤ ∫ ζ in closedBall (0:ℂ) R, ‖omt ζ / (ζ - z)‖ := norm_integral_le_integral_norm _
          _ ≤ ∫ ζ in closedBall (0:ℂ) R, (‖z‖ - R)⁻¹ * ‖omt ζ‖ := by
                apply setIntegral_mono_on hLHSint (hIntOn.norm.const_mul _)
                  measurableSet_closedBall hkbound
          _ = (‖z‖ - R)⁻¹ * L := by rw [integral_const_mul]
      calc 1/π * ‖∫ ζ in closedBall (0:ℂ) R, omt ζ / (ζ - z)‖
          ≤ 1/π * ((‖z‖ - R)⁻¹ * L) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 1/π * (‖z‖ - R)⁻¹ * L := by ring
    have hnorm : Tendsto (norm : ℂ → ℝ) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
    have hg : Tendsto (fun z : ℂ => 1/π * (‖z‖ - R)⁻¹ * L) (cocompact ℂ) (𝓝 0) := by
      have h1 : Tendsto (fun z : ℂ => ‖z‖ - R) (cocompact ℂ) atTop := by
        rw [Filter.tendsto_atTop] at hnorm ⊢
        intro b
        filter_upwards [hnorm (b + R)] with z hz
        linarith
      have h3 : Tendsto (fun z : ℂ => (‖z‖ - R)⁻¹) (cocompact ℂ) (𝓝 0) :=
        tendsto_inv_atTop_zero.comp h1
      have h4 : Tendsto (fun z : ℂ => 1/π * (‖z‖ - R)⁻¹ * L) (cocompact ℂ) (𝓝 (1/π * 0 * L)) :=
        (tendsto_const_nhds.mul h3).mul tendsto_const_nhds
      simpa using h4
    have hRev : ∀ᶠ z : ℂ in cocompact ℂ, R < ‖z‖ := by
      have hsub : (closedBall (0:ℂ) R)ᶜ ⊆ {z : ℂ | R < ‖z‖} := by
        intro z hz
        rw [mem_compl_iff, mem_closedBall_zero_iff, not_le] at hz
        exact hz
      exact Filter.mem_cocompact.2 ⟨closedBall (0:ℂ) R, isCompact_closedBall _ _, hsub⟩
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [hRev] with z hz using hbound z hz
  have hbigF_to_1 : Tendsto bigF (cocompact ℂ) (𝓝 1) := by
    have h := (Complex.continuous_exp.tendsto 0).comp hcTomt_decay
    rw [Complex.exp_zero] at h
    exact h
  -- `H(ω*) → 0` a.e. on the full-measure set `S`
  have homstarsupp' : Bornology.IsBounded (Function.support omstar) := by
    apply Bornology.IsBounded.subset (isBounded_closedBall (x := (0:ℂ)) (r := Rμ))
    intro z hz
    by_contra hzn
    exact hz (homstarsupp z (by simpa [mem_closedBall_zero_iff, not_le] using hzn))
  obtain ⟨S, hSfull, hHomstar_to_0⟩ :=
    hilbertH_tendsto_zero_ae_of_bounded_support hp1 homstarMemLp homstarsupp'
  -- bridge: `deriv hfun` equals `g_combo` a.e.
  obtain ⟨hACLh, hPXh, -⟩ := lemma9_2_isACL_of_genPartials isOpen_univ hp1' hGPh
  simp only [Measure.restrict_univ] at hPXh
  have hcfull : ∀ᵐ z, c = g_combo z := by
    filter_upwards [hPXh] with z hz
    have hdiffz : DifferentiableAt ℝ hfun z := (hhDiff z).restrictScalars ℝ
    have hpx : partialX hfun z = fderiv ℝ hfun z 1 := partialX_eq_of_differentiableAt hdiffz
    have hfd : fderiv ℝ hfun z 1 = c := by
      rw [funext haffine, fderiv_const_add, fderiv_const_mul differentiableAt_id, fderiv_fun_id]
      simp
    rw [← hz, hpx, hfd]
  -- `c = 0`: pick a sequence `z_n → ∞` in the full-measure set where BOTH `c = g_combo` AND
  -- `hilbertH omstar` genuinely decays (the intersection of two null-complement sets)
  have hScomp0 : volume {z : ℂ | ¬(c = g_combo z)} = 0 := ae_iff.mp hcfull
  have hexists : ∀ n : ℕ, ∃ z : ℂ, (n : ℝ) < ‖z‖ ∧ c = g_combo z ∧ z ∈ S := by
    intro n
    by_contra hcon
    push Not at hcon
    have hsub : ball ((n:ℂ)+1) 1 ⊆ {z : ℂ | ¬(c = g_combo z)} ∪ Sᶜ := by
      intro z hz
      rw [mem_ball, dist_eq_norm] at hz
      have hzn : (n:ℝ) < ‖z‖ := by
        have h3 : ‖((n:ℂ)+1)‖ = (n:ℝ)+1 := by
          have heqc : ((n:ℂ)+1) = ((((n:ℝ)+1:ℝ)):ℂ) := by push_cast; ring
          rw [heqc, Complex.norm_real]; exact abs_of_nonneg (by positivity)
        have h1 : ‖((n:ℂ)+1)‖ - ‖z‖ ≤ ‖((n:ℂ)+1) - z‖ := norm_sub_norm_le _ _
        rw [norm_sub_rev] at h1
        linarith [h1, h3, hz]
      by_cases hcz : c = g_combo z
      · right
        intro hzS
        exact absurd hzS (hcon z hzn hcz)
      · left; exact hcz
    have hne : (ball ((n:ℂ)+1) 1).Nonempty := ⟨_, mem_ball_self one_pos⟩
    have hunion0 : volume ({z : ℂ | ¬(c = g_combo z)} ∪ Sᶜ) = 0 :=
      measure_union_null hScomp0 hSfull
    exact (isOpen_ball.measure_ne_zero volume hne)
      (le_antisymm ((measure_mono hsub).trans_eq hunion0) zero_le)
  choose zseq hzseqnorm hzseqmem hzseqS using hexists
  have hzseq_tendsto : Tendsto (fun n : ℕ => ‖zseq n‖) atTop atTop :=
    tendsto_atTop_mono (fun n => (hzseqnorm n).le) tendsto_natCast_atTop_atTop
  have hzseq_cocompact : Tendsto zseq atTop (cocompact ℂ ⊓ Filter.principal S) := by
    refine Filter.tendsto_inf.2 ⟨?_, ?_⟩
    · intro s hs
      rw [Filter.mem_map]
      obtain ⟨K, hKcpt, hKsub⟩ := Filter.mem_cocompact.mp hs
      obtain ⟨R, hR⟩ := hKcpt.isBounded.subset_closedBall (0:ℂ)
      filter_upwards [hzseq_tendsto.eventually_gt_atTop R] with n hn
      apply hKsub
      intro hmem
      have := hR hmem
      rw [mem_closedBall_zero_iff] at this
      linarith
    · rw [Filter.tendsto_principal]
      exact Eventually.of_forall hzseqS
  have hgcombo_eq : ∀ z, g_combo z = bigF z - 1 - hilbertH omstar z := by
    intro z
    show fderiv ℝ wtilde z 1 - 1 - (hilbertH omstar z + omstar z) = bigF z - 1 - hilbertH omstar z
    rw [hderiv1]
    show bigF z + μ z * bigF z - 1 - (hilbertH omstar z + μ z * bigF z) =
      bigF z - 1 - hilbertH omstar z
    ring
  have hc0 : c = 0 := by
    have h1 : Tendsto (fun n => g_combo (zseq n)) atTop (𝓝 (1 - 1 - 0)) := by
      simp_rw [hgcombo_eq]
      have hF : Tendsto (fun n => bigF (zseq n)) atTop (𝓝 1) :=
        (hbigF_to_1.mono_left inf_le_left).comp hzseq_cocompact
      have hH : Tendsto (fun n => hilbertH omstar (zseq n)) atTop (𝓝 0) :=
        hHomstar_to_0.comp hzseq_cocompact
      exact (hF.sub tendsto_const_nhds).sub hH
    have h2 : Tendsto (fun n => g_combo (zseq n)) atTop (𝓝 c) := by
      have : ∀ n, g_combo (zseq n) = c := fun n => (hzseqmem n).symm
      simp [this]
    have := tendsto_nhds_unique h2 h1
    simpa using this
  -- `ω*` solves the standard equation a.e.
  have hzero_ae : ∀ᵐ z, g_combo z = 0 := by
    filter_upwards [hcfull] with z hz
    rw [← hz, hc0]
  have homstar_eq : ∀ᵐ z, omstar z = μ z * hilbertH omstar z + μ z := by
    filter_upwards [hzero_ae] with z hz
    rw [hgcombo_eq] at hz
    show μ z * bigF z = μ z * hilbertH omstar z + μ z
    have hbigF_eq : bigF z = 1 + hilbertH omstar z := by linear_combination hz
    rw [hbigF_eq]; ring
  -- match `ω*` to the given `ω` via uniqueness of solutions to the standard equation
  have hμB : IsBeltramiCoeff μ univ k :=
    ⟨hμs.continuous.aestronglyMeasurable, Filter.Eventually.of_forall hμ⟩
  have hμMemLp : MemLp μ (ENNReal.ofReal p) :=
    HasCompactSupport.memLp_of_bound hμc hμs.continuous.aestronglyMeasurable k
      (Filter.Eventually.of_forall hμ)
  obtain ⟨ω₀, hω₀MemLp, hω₀Sol, hω₀uniq⟩ := eq12_1_solution hk₀ hμB hp hkp hμMemLp
  have homstar_eq_ω : omstar =ᵐ[volume] ω := by
    have h1 : omstar =ᵐ[volume] ω₀ := hω₀uniq omstar homstarMemLp homstar_eq
    have h2 : ω =ᵐ[volume] ω₀ := hω₀uniq ω hω hsol
    exact h1.trans h2.symm
  have hcauchyT_eq : cauchyT omstar = cauchyT ω := cauchyT_congr_ae homstar_eq_ω
  set d : ℂ := wtilde 0 - cauchyT omstar 0 with hddef
  have hconst : ∀ z, hfun z = hfun 0 := fun z => by
    rw [haffine z, hc0, zero_mul, add_zero]
  have hwtilde_eq : ∀ z, wtilde z = z + cauchyT ω z + d := by
    intro z
    have hcz := hconst z
    change wtilde z - z - cauchyT omstar z = wtilde 0 - (0:ℂ) - cauchyT omstar 0 at hcz
    rw [hddef, ← hcauchyT_eq]
    linear_combination hcz
  refine ⟨d, wtilde, funext hwtilde_eq, hwtildeCD, fun z => ?_, hJ, ?_⟩
  · rw [hdzbar, hdz]
  · refine ⟨MT + ‖d‖, fun z => ?_⟩
    rw [hwtilde_eq z]
    have heq2 : z + cauchyT ω z + d - z = cauchyT omstar z + d := by
      rw [← hcauchyT_eq]; ring
    rw [heq2]
    calc ‖cauchyT omstar z + d‖ ≤ ‖cauchyT omstar z‖ + ‖d‖ := norm_add_le _ _
      _ ≤ MT + ‖d‖ := by gcongr; exact hcauchyTomstarBdd z

/-- The smooth case in the proof of Theorem 12.1: for `μ ∈ C₀^∞`, `‖μ‖_∞ < 1`, the solution
`w = z + T(ω)` is a `C¹` homeomorphism of `ℂ` with positive Jacobian.

*Correction.*  The smoothness hypothesis is `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ`, i.e. `C^∞`.  A bare
`ContDiff ℝ ⊤ μ` would mean `ContDiff ℝ ω μ` (real analytic) in current Mathlib, and a real-analytic
function with compact support vanishes identically, which would make the statement degenerate.

*Correction.*  The conclusion also records the Beltrami equation `∂_{z̄} w = μ ∂_z w` at every point,
which the book obtains from (12.6)′ (`∂_z w̃ = f`, `∂_{z̄} w̃ = μ f`, and `w = w̃ - a`).  Without it the
smooth case could not show that the approximating maps `wₙ` of the general case are `C¹`
quasiconformal.

*Proof.*  `f := exp(T ω̃)` for `ω̃` solving (12.6); the rectangle integrals of `f (dz + μ dz̄)` vanish
by the §9 Green formulas (`eq9_9_green`/`eq9_10_green`) applied to the ACL functions `f(1±μ)`; this
gives the `C¹` primitive `w̃` (`exists_contDiff_primitive_of_rect_integral_eq_zero`), with
`∂_z w̃ = f`, `∂_{z̄} w̃ = μ f` and positive Jacobian; `w̃ - z - T(μ f)` is entire by the Weyl lemma
(`differentiable_of_genDzbar_eq_zero`), affine by Liouville applied to its `dslope`, and constant
because the affine coefficient is pinned to `0` by a sequence argument using `f → 1` and
`H(μ f) → 0` at infinity; `μ f` is then identified with `ω` by uniqueness of solutions of (12.1);
the homeomorphism comes from `homeomorph_of_contDiff_jacobian_pos`. -/
theorem thm12_1_smooth_case {μ : ℂ → ℂ} {k : ℝ} (hk : k < 1)
    (hμs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ) (hμc : HasCompactSupport μ)
    (hμ : ∀ z, ‖μ z‖ ≤ k) {p : ℝ} (hp : 2 < p) (hkp : k * hilbertNorm p < 1)
    {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p))
    (hsol : ω =ᵐ[volume] fun z => μ z * hilbertH ω z + μ z) :
    ∃ a : ℂ, ContDiff ℝ 1 (fun z => z + cauchyT ω z + a) ∧
      (∀ z, dzbar (fun z => z + cauchyT ω z) z = μ z * dz (fun z => z + cauchyT ω z) z) ∧
      (∀ z, 0 < jacobian (fun z => z + cauchyT ω z) z) ∧
      ∃ e : ℂ ≃ₜ ℂ, ⇑e = fun z => z + cauchyT ω z := by
  obtain ⟨a, wtilde, hwtildeeq, hwtildeCD, hdzbardz, hJ, hbd⟩ :=
    wd_D5_D7 hk hμs hμc hμ hp hkp hω hsol
  obtain ⟨e, he⟩ := homeomorph_of_contDiff_jacobian_pos hwtildeCD hJ hbd
  have hw0eq : (fun z => z + cauchyT ω z) = fun z => wtilde z - a := by
    funext z; rw [hwtildeeq]; ring
  have hderiv0 : ∀ z, ∀ v : ℂ, fderiv ℝ (fun z => z + cauchyT ω z) z v = fderiv ℝ wtilde z v := by
    intro z v
    have : fderiv ℝ (fun z => z + cauchyT ω z) z = fderiv ℝ (fun z => wtilde z - a) z := by
      rw [hw0eq]
    rw [this, fderiv_sub_const]
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  · rw [← hwtildeeq]; exact hwtildeCD
  · intro z
    show (fderiv ℝ (fun z => z + cauchyT ω z) z 1 + I * fderiv ℝ (fun z => z + cauchyT ω z) z I) / 2 =
      μ z * ((fderiv ℝ (fun z => z + cauchyT ω z) z 1 - I * fderiv ℝ (fun z => z + cauchyT ω z) z I) / 2)
    rw [hderiv0 z 1, hderiv0 z I]
    exact hdzbardz z
  · intro z
    show 0 < ‖(fderiv ℝ (fun z => z + cauchyT ω z) z 1 - I * fderiv ℝ (fun z => z + cauchyT ω z) z I) / 2‖ ^ 2 -
      ‖(fderiv ℝ (fun z => z + cauchyT ω z) z 1 + I * fderiv ℝ (fun z => z + cauchyT ω z) z I) / 2‖ ^ 2
    rw [hderiv0 z 1, hderiv0 z I]
    exact hJ z
  · refine ⟨e.trans (Homeomorph.subRight a), ?_⟩
    funext z
    show (Homeomorph.subRight a) (e z) = z + cauchyT ω z
    rw [Homeomorph.subRight_apply, congrFun he z, hwtildeeq]
    ring

/-- The homeomorphism half of Theorem 12.1, for an arbitrary `L_p` solution `ω` of (12.4): the map
`w = z + T(ω)` is a `(1+k)/(1-k)`-quasiconformal homeomorphism of `ℂ` onto itself.

Stated separately so that Theorem 12.2 can take the quasiconformality of `w` from here instead of
from Theorem 10.2 (⇐).

*Proof.*  `μₙ ∈ C₀^∞` approximating `μ` and the corresponding `ωₙ` come from
`exists_smooth_beltrami_approx`; `thm12_1_smooth_case` plus `t3b_isKQC_smooth` give
`IsKQC (z + T ωₙ) univ K` for every `n`; `eq12_1_solution_tendsto_cauchyT` gives the uniform (hence
locally uniform) convergence `T ωₙ → T ω`; `cauchyT_bounded_of_solution` plus
`t3b_proper_of_bounded` give properness of the limit; `t3b_limit` assembles the conclusion. -/
theorem thm12_1_isKQC {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμ : IsCompactBeltramiCoeff μ k) {p : ℝ} (hp : 2 < p) (hkp : k * hilbertNorm p < 1)
    {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p))
    (hsol : ω =ᵐ[volume] fun z => μ z * hilbertH ω z + μ z) :
    IsKQC (fun z => z + cauchyT ω z) univ ((1 + k) / (1 - k)) ∧
      ∃ e : ℂ ≃ₜ ℂ, ⇑e = fun z => z + cauchyT ω z := by
  set K : ℝ := (1 + k) / (1 - k) with hKdef
  have hK1 : 1 ≤ K := by rw [hKdef, le_div_iff₀ (by linarith)]; linarith
  -- (a)
  obtain ⟨R, μn, hR0, hRμ, hCD, hμc, hμnb, hRμn, hlim⟩ :=
    exists_smooth_beltrami_approx hk₀ hμ
  -- (b)
  have hμnB : ∀ n, IsBeltramiCoeff (μn n) univ k := fun n =>
    ⟨(hCD n).continuous.aestronglyMeasurable, Filter.Eventually.of_forall (hμnb n)⟩
  have hμnMemLp : ∀ n, MemLp (μn n) (ENNReal.ofReal p) := fun n =>
    (hμc n).memLp_of_bound (hCD n).continuous.aestronglyMeasurable k
      (Filter.Eventually.of_forall (hμnb n))
  choose ωn hωnMemLp hωnSol _huniq using
    fun n => eq12_1_solution hk₀ (hμnB n) hp hkp (hμnMemLp n)
  -- (c)
  have hqc : ∀ n, IsKQC (fun z => z + cauchyT (ωn n) z) univ K := fun n => by
    have hsmooth := thm12_1_smooth_case hk (hCD n) (hμc n) (hμnb n) hp hkp (hωnMemLp n) (hωnSol n)
    obtain ⟨a, hCDa⟩ := hsmooth
    have hbelt := hCDa.2.1
    have hJ := hCDa.2.2.1
    have he := hCDa.2.2.2
    have hCDw : ContDiff ℝ 1 (fun z => z + cauchyT (ωn n) z) := by
      have h1 : ContDiff ℝ 1 (fun z => z + cauchyT (ωn n) z + a) :=
        (hCDa.1 : ContDiff ℝ 1 (fun z => z + cauchyT (ωn n) z + a))
      have h2 : ContDiff ℝ 1 (fun _ : ℂ => a) := contDiff_const
      have h3 : ContDiff ℝ 1 (fun z => (z + cauchyT (ωn n) z + a) - a) := ContDiff.sub h1 h2
      simpa using h3
    exact hKdef ▸ t3b_isKQC_smooth hk₀ hk (hμnb n) hCDw hbelt hJ he
  -- (d)
  have hTU : TendstoUniformly (fun n => cauchyT (ωn n)) (cauchyT ω) atTop :=
    eq12_1_solution_tendsto_cauchyT hk₀ hp hkp hμnB hμ.1 hRμn hRμ hlim hωnMemLp hωnSol hω hsol
  have hTUid : TendstoUniformly (fun (_ : ℕ) (z : ℂ) => z) (fun z => z) atTop := by
    intro u hu
    filter_upwards with n z
    exact refl_mem_uniformity hu
  have hTUsum : TendstoUniformly (fun n z => z + cauchyT (ωn n) z) (fun z => z + cauchyT ω z)
      atTop := hTUid.add hTU
  have hlimloc : TendstoLocallyUniformly (fun n z => z + cauchyT (ωn n) z)
      (fun z => z + cauchyT ω z) atTop := hTUsum.tendstoLocallyUniformly
  -- (e)
  obtain ⟨M, hM⟩ := cauchyT_bounded_of_solution hμ hp hω hsol
  have hprop : Tendsto (fun z => z + cauchyT ω z) (Filter.cocompact ℂ) (Filter.cocompact ℂ) :=
    t3b_proper_of_bounded hM
  -- (f)
  have hfinal := t3b_limit hK1 hqc hlimloc hprop
  exact hKdef ▸ hfinal

/-- A constant-in-`n` sequence of functions tends locally uniformly to itself. -/
theorem t3_tlu_const {α β ι : Type*} [TopologicalSpace α] [UniformSpace β] {g : α → β}
    {s : Set α} {p : Filter ι} : TendstoLocallyUniformlyOn (fun _ : ι => g) g p s := by
  intro u hu x _
  exact ⟨s, self_mem_nhdsWithin, Filter.Eventually.of_forall
    (fun _ y _ => refl_mem_uniformity hu)⟩

/-- Adding the identity map to a function with `L_p` generalized partial derivatives shifts those
derivatives by the (constant) generalized derivatives of `id`, `1` and `I`. -/
theorem t3_hasGenPartials_add_id {f g h : ℂ → ℂ} {p : ℝ≥0∞}
    (hf : HasGenPartials f g h univ p) :
    HasGenPartials (fun z => z + f z) (fun z => 1 + g z) (fun z => I + h z) univ p := by
  obtain ⟨hmem, fn, hfnC1, hconv, hderiv⟩ := hf
  have hdiffAt : ∀ n, ∀ z : ℂ, DifferentiableAt ℝ (fn n) z := fun n z =>
    ((hfnC1 n).contDiffAt (isOpen_univ.mem_nhds (mem_univ z))).differentiableAt one_ne_zero
  refine ⟨?_, fun n z => z + fn n z, fun n => contDiffOn_id.add (hfnC1 n),
    ?_, ?_⟩
  · intro C _ hC
    obtain ⟨hg, hh⟩ := hmem C (subset_univ C) hC
    haveI : IsFiniteMeasure (volume.restrict C) :=
      isFiniteMeasure_restrict.2 hC.measure_lt_top.ne
    exact ⟨(memLp_const (1 : ℂ)).add hg, (memLp_const (I : ℂ)).add hh⟩
  · have hid : TendstoLocallyUniformlyOn (fun _ : ℕ => (id : ℂ → ℂ)) id atTop univ := t3_tlu_const
    have hsum := hid.add hconv
    have hfe : (fun n : ℕ => fun z : ℂ => z + fn n z) = ((fun _ : ℕ => (id : ℂ → ℂ)) + fn) := by
      funext n z; rfl
    have hfe2 : (fun z : ℂ => z + f z) = ((id : ℂ → ℂ) + f) := by
      funext z; rfl
    rw [hfe, hfe2]
    exact hsum
  · intro C hCD hC
    obtain ⟨h1, h2⟩ := hderiv C hCD hC
    have hsplit : ∀ n, ∀ z : ℂ, fderiv ℝ (fun z => z + fn n z) z =
        ContinuousLinearMap.id ℝ ℂ + fderiv ℝ (fn n) z := fun n z =>
      ((hasFDerivAt_id z).add (hdiffAt n z).hasFDerivAt).fderiv
    have hsplit1 : ∀ n, ∀ z : ℂ,
        fderiv ℝ (fun z => z + fn n z) z 1 = 1 + fderiv ℝ (fn n) z 1 := by
      intro n z
      rw [hsplit n z]
      simp
    have hsplitI : ∀ n, ∀ z : ℂ,
        fderiv ℝ (fun z => z + fn n z) z I = I + fderiv ℝ (fn n) z I := by
      intro n z
      rw [hsplit n z]
      simp
    constructor
    · have heq : (fun n => eLpNorm (fun z => fderiv ℝ (fun z => z + fn n z) z 1 -
          (1 + g z)) p (volume.restrict C)) =
          fun n => eLpNorm (fun z => fderiv ℝ (fn n) z 1 - g z) p (volume.restrict C) := by
        funext n
        congr 1
        funext z
        rw [hsplit1]
        ring
      rw [heq]
      exact h1
    · have heq : (fun n => eLpNorm (fun z => fderiv ℝ (fun z => z + fn n z) z I -
          (I + h z)) p (volume.restrict C)) =
          fun n => eLpNorm (fun z => fderiv ℝ (fn n) z I - h z) p (volume.restrict C) := by
        funext n
        congr 1
        funext z
        rw [hsplitI]
        ring
      rw [heq]
      exact h2

/-- The support of an indicator over a closed ball is bounded. -/
theorem t3_isBounded_support_indicator {f : ℂ → ℂ} {R : ℝ} :
    Bornology.IsBounded (Function.support ((closedBall (0 : ℂ) R).indicator f)) :=
  isBounded_closedBall.subset (fun z hz => by
    by_contra hzc
    exact hz (indicator_of_notMem hzc f))

/-- **Theorem 12.1**: let `μ` be measurable with `‖μ‖_∞ ≤ k < 1` and bounded support.  Then the
Beltrami equation `∂_{z̄} w = μ ∂_z w` has a solution of the form `w(z) = z + T_ω(z)`,
`ω ∈ L_p`, `p > 2`, where `ω` solves `ω = μ H(ω) + μ` (12.4), and `w` is a homeomorphism of `ℂ`
onto itself (a global homeomorphic solution, 整体同胚解).

*Proof.*  `p` comes from Corollary 2 of Theorem 11.3 (`eq12_1_exists_exponent`); `ω` solves (12.1)
with `h = μ` (`eq12_1_solution`); its bounded-support representative feeds Theorem 11.1 for the
generalized derivatives, and `thm12_1_isKQC` supplies the homeomorphism and quasiconformality. -/
theorem thm12_1 {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : IsCompactBeltramiCoeff μ k) :
    ∃ p : ℝ, 2 < p ∧ k * hilbertNorm p < 1 ∧ ∃ ω : ℂ → ℂ, MemLp ω (ENNReal.ofReal p) ∧
      (ω =ᵐ[volume] fun z => μ z * hilbertH ω z + μ z) ∧
      IsGenHomeoSolution (fun z => z + cauchyT ω z) μ univ (ENNReal.ofReal p) ∧
      ∃ e : ℂ ≃ₜ ℂ, ⇑e = fun z => z + cauchyT ω z := by
  obtain ⟨p, hp, -, hkp⟩ := eq12_1_exists_exponent hk (show (2 : ℝ) < 3 by norm_num)
  have hμmem : MemLp μ (ENNReal.ofReal p) volume := t3_memLp_of_compactBeltrami hμ
  obtain ⟨ω, hω, hsol, -⟩ := eq12_1_solution hk₀ hμ.1 hp hkp hμmem
  obtain ⟨hkqc, e', he'⟩ := thm12_1_isKQC hk₀ hk hμ hp hkp hω hsol
  refine ⟨p, hp, hkp, ω, hω, hsol, ⟨hkqc.2.2.1, ?_⟩, e', he'⟩
  -- the witness ω̃ (ASCII `omR`), and (g, h) for `T(omR)` from Theorem 11.1
  obtain ⟨R, hR0⟩ := hμ.2
  obtain ⟨R', hR', hRR'⟩ : ∃ R' : ℝ, 0 < R' ∧ ∀ z : ℂ, R' < ‖z‖ → μ z = 0 :=
    ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _),
      fun z hz => hR0 z (lt_of_le_of_lt (le_max_left R 1) hz)⟩
  set omR : ℂ → ℂ := (closedBall (0 : ℂ) R').indicator ω with homRdef
  have homs : ω =ᵐ[volume] omR := t2_omega_ae_eq_indicator hRR' hsol
  have hcT : cauchyT ω = cauchyT omR := cauchyT_congr_ae homs
  have hHT : hilbertH ω = hilbertH omR := hilbertH_congr_ae homs
  have homRmem : MemLp omR (ENNReal.ofReal p) := hω.indicator measurableSet_closedBall.nullMeasurableSet
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

/-- T2.3 bullet 2–3 assembled: `cauchyT ω` is bounded, hence `w z / z → 1` along `cocompact ℂ`. -/
theorem t2_tendsto_div_one {μ ω : ℂ → ℂ} {p R : ℝ} (hp : 2 < p) (hR : 0 < R)
    (hRvanish : ∀ z : ℂ, R < ‖z‖ → μ z = 0) (hω : MemLp ω (ENNReal.ofReal p))
    (hsol : ω =ᵐ[volume] fun z => μ z * hilbertH ω z + μ z) :
    Tendsto (fun z => (z + cauchyT ω z) / z) (cocompact ℂ) (𝓝 1) := by
  set omR : ℂ → ℂ := (closedBall (0 : ℂ) R).indicator ω with homRdef
  have homs : ω =ᵐ[volume] omR := t2_omega_ae_eq_indicator hRvanish hsol
  have hcT : cauchyT ω = cauchyT omR := cauchyT_congr_ae homs
  have homRmem : MemLp omR (ENNReal.ofReal p) := hω.indicator measurableSet_closedBall.nullMeasurableSet
  have homRsupp : ∀ z : ℂ, R < ‖z‖ → omR z = 0 := by
    intro z hz
    rw [homRdef]
    exact indicator_of_notMem (by rwa [mem_closedBall_zero_iff, not_le]) _
  obtain ⟨M₁, hM₁⟩ := lemma11_1 hp hR
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = M₁ * (eLpNorm omR (ENNReal.ofReal p)).toReal := ⟨_, rfl⟩
  have hbound : ∀ z : ℂ, ‖cauchyT ω z‖ ≤ M := by
    intro z
    rw [hcT, hM]
    exact hM₁ omR homRmem homRsupp z
  have h0 : Tendsto (fun z : ℂ => cauchyT ω z / z) (cocompact ℂ) (𝓝 0) := by
    have hnorm : Tendsto (norm : ℂ → ℝ) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
    have hinv : Tendsto (fun z : ℂ => ‖z‖⁻¹) (cocompact ℂ) (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hnorm
    have hMinv : Tendsto (fun z : ℂ => M * ‖z‖⁻¹) (cocompact ℂ) (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hinv
    have hnz : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 := by
      have : {(0 : ℂ)}ᶜ ∈ cocompact ℂ :=
        Filter.mem_cocompact.2 ⟨{0}, isCompact_singleton, by simp⟩
      filter_upwards [this] with z hz
      simpa using hz
    refine squeeze_zero_norm' ?_ hMinv
    filter_upwards [hnz] with z hz
    rw [norm_div]
    rw [div_le_iff₀ (norm_pos_iff.2 hz)]
    calc ‖cauchyT ω z‖ ≤ M := hbound z
      _ = M * ‖z‖⁻¹ * ‖z‖ := by field_simp
  have hcongr : (fun z : ℂ => (z + cauchyT ω z) / z) =ᶠ[cocompact ℂ]
      (fun z : ℂ => 1 + cauchyT ω z / z) := by
    have hnz : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 := by
      have : {(0 : ℂ)}ᶜ ∈ cocompact ℂ :=
        Filter.mem_cocompact.2 ⟨{0}, isCompact_singleton, by simp⟩
      filter_upwards [this] with z hz
      simpa using hz
    filter_upwards [hnz] with z hz
    field_simp
  rw [tendsto_congr' hcongr]
  simpa using tendsto_const_nhds.add h0

/-- T2.2 assembled: for a genuine `L_p` generalized homeomorphic solution `w` of (12.4) that is
also `K`-q.c., the complex dilatation of `w` equals `μ` a.e. -/
theorem t2_complexDilatation_ae {w μ : ℂ → ℂ} {K p : ℝ} (hkqc : IsKQC w univ K)
    (hp : 2 < p) (hgen : IsGenHomeoSolution w μ univ (ENNReal.ofReal p)) :
    ∀ᵐ z, complexDilatation w z = μ z := by
  obtain ⟨-, g, h, hgp, heq⟩ := hgen
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  obtain ⟨-, hgX, hhY⟩ := lemma9_2_isACL_of_genPartials isOpen_univ hp1 hgp
  rw [Measure.restrict_univ] at heq hgX hhY
  have hdiff := thm9_3_differentiable_ae hkqc
  have hJpos := thm9_6_cor2_jacobian_pos hkqc
  rw [Measure.restrict_univ] at hdiff hJpos
  filter_upwards [heq, hgX, hhY, hdiff, hJpos] with z heqz hgXz hhYz hdiffz hJz
  have hdz : dz w z ≠ 0 := by
    intro hcontra
    rw [jacobian, hcontra, norm_zero] at hJz
    nlinarith [norm_nonneg (dzbar w z)]
  have hx : partialX w z = dz w z + dzbar w z := by
    rw [partialX_eq_of_differentiableAt hdiffz, fderiv_eq_dz_dzbar hdiffz]
    simp
  have hy : partialY w z = I * (dz w z - dzbar w z) := by
    rw [partialY_eq_of_differentiableAt hdiffz, fderiv_eq_dz_dzbar hdiffz, Complex.conj_I]
    ring
  have hgz : genDz g h z = dz w z := by
    rw [genDz, ← hgXz, ← hhYz, hx, hy]
    linear_combination (-(dz w z - dzbar w z) / 2) * I_sq
  have hgzb : genDzbar g h z = dzbar w z := by
    rw [genDzbar, ← hgXz, ← hhYz, hx, hy]
    linear_combination ((dz w z - dzbar w z) / 2) * I_sq
  have hdz' : genDz g h z ≠ 0 := by rw [hgz]; exact hdz
  rw [complexDilatation, ← hgz, ← hgzb, heqz, mul_div_cancel_right₀ _ hdz']

/-- **Theorem 12.2**: for measurable `μ` with `‖μ‖_∞ ≤ k < 1` and bounded support there is a
quasiconformal map `w` of the whole plane with complex characteristic `μ` and
`lim_{z → ∞} w(z)/z = 1` (12.12).

*Proof.*  `w = z + T_ω` for the `ω` of Theorem 12.1; `K`-quasiconformality is `thm12_1_isKQC`
applied to that `ω` directly (bypassing Theorem 10.2 (⇐)); the complex characteristic `μ_w = μ`
a.e. follows from Lemma 9.2 (⇐) identifying the classical and generalized partials, together with
Theorems 9.3 and 9.6 Corollary 2 (a.e. differentiability and `J > 0` a.e.); `w(z)/z → 1` comes from
Lemma 11.1 applied to the bounded-support representative of `ω`. -/
theorem thm12_2 {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : IsCompactBeltramiCoeff μ k) :
    ∃ w : ℂ → ℂ, IsKQC w univ ((1 + k) / (1 - k)) ∧ w '' univ = univ ∧
      (∀ᵐ z, complexDilatation w z = μ z) ∧ Tendsto (fun z => w z / z) (cocompact ℂ) (𝓝 1) := by
  obtain ⟨p, hp, hkp, ω, hω, hsol, hgen, -⟩ := thm12_1 hk₀ hk hμ
  obtain ⟨hkqc, e', he'⟩ := thm12_1_isKQC hk₀ hk hμ hp hkp hω hsol
  refine ⟨fun z => z + cauchyT ω z, hkqc, ?_, ?_, ?_⟩
  · have : (fun z => z + cauchyT ω z) '' univ = e' '' univ := by rw [he']
    rw [this, Set.image_univ, e'.surjective.range_eq]
  · exact t2_complexDilatation_ae hkqc hp hgen
  · obtain ⟨R, hR0⟩ := hμ.2
    obtain ⟨R', hR', hRR'⟩ : ∃ R' : ℝ, 0 < R' ∧ ∀ z : ℂ, R' < ‖z‖ → μ z = 0 :=
      ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _),
        fun z hz => hR0 z (lt_of_le_of_lt (le_max_left R 1) hz)⟩
    exact t2_tendsto_div_one hp hR' hRR' hω hsol

end LiZhongQC
