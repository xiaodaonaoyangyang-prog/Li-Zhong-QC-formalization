import References.GardinerLakic2000.Ch09.S03_TeichmullerDifferentials

/-!
# Gardiner–Lakic 2000, Ch. 9 §9.4 Delta inequalities

Source `teichmuller.txt`, lines 7583–7764 (Chapter 9, §9.4).

* Theorem 4 (the generalized infinitesimal delta inequality, l. 7586) — `thm9_4`
* Theorem 5 (the generalized delta inequality, l. 7628; contains (9.6)) — `coeffAtPoint`, `thm9_5`

Not items: (9.13), (9.14) and the construction of `η` (proof). Modelling: surface level. In Theorem 5, `f` and `g` are
quasiconformal maps of `R` onto the same surface `Y` with coefficients `μ`, `ν`, homotopic modulo the ideal boundary
(`LiZhongQC.HomotopicModBoundary` through uniformizations `p`, `q`); `μ̃`, `ν̃` are the Beltrami coefficients of `f⁻¹`,
`g⁻¹`, read at `f(z)` in the chart at `f(z)` (the integrand is chart-invariant); `C` depends only on `k` (`∀ k ∃ C`).
Theorem 5 prints `conj μ̃(f)` in the denominator and (9.6) does not (l. 7376, 7637); the absolute values agree only with
the conjugate, which is kept [misprint in (9.6)].
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (surfaceIntegral quadDiffNorm IsQCRS HomotopicModBoundary)

/-- Helper for **Theorem 4** (§9.4). The pointwise inequality behind the delta inequality: for `|m|, |n| ≤ k` and any
`f`, `|m − n|² |f| ≤ 8k²|f| − 4k Re(f m) − 4k Re(f n)` (parallelogram law for `m − kū` and `n − kū`, `u = \bar f/|f|`;
both sides vanish at `f = 0`). -/
theorem gl94_pointwise {m n f : ℂ} {k : ℝ} (hk : 0 ≤ k) (hm : ‖m‖ ≤ k) (hn : ‖n‖ ≤ k) :
    ‖m - n‖ ^ 2 * ‖f‖ ≤ 8 * k ^ 2 * ‖f‖ - 4 * k * (f * m).re - 4 * k * (f * n).re := by
  by_cases hf : f = 0
  · subst hf
    simp
  · have hfn : 0 < ‖f‖ := norm_pos_iff.2 hf
    have hfn' : (‖f‖ : ℂ) ≠ 0 := by exact_mod_cast hfn.ne'
    set c : ℂ := f / (‖f‖ : ℂ) with hcdef
    have hc : ‖c‖ = 1 := by
      rw [hcdef, norm_div, Complex.norm_real, norm_norm, div_self hfn.ne']
    have hfc : f = (‖f‖ : ℂ) * c := by
      rw [hcdef]
      field_simp
    have hma : ‖c * m‖ ≤ k := by rw [norm_mul, hc, one_mul]; exact hm
    have hnb : ‖c * n‖ ≤ k := by rw [norm_mul, hc, one_mul]; exact hn
    have hmn : ‖m - n‖ = ‖c * m - c * n‖ := by
      rw [← mul_sub, norm_mul, hc, one_mul]
    set a : ℂ := c * m with ha
    set b : ℂ := c * n with hb
    have ha2 : a.re ^ 2 + a.im ^ 2 ≤ k ^ 2 := by
      have h1 := Complex.sq_norm a
      rw [Complex.normSq_apply] at h1
      have h2 : ‖a‖ ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hma 2
      nlinarith [h1, h2]
    have hb2 : b.re ^ 2 + b.im ^ 2 ≤ k ^ 2 := by
      have h1 := Complex.sq_norm b
      rw [Complex.normSq_apply] at h1
      have h2 : ‖b‖ ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnb 2
      nlinarith [h1, h2]
    have hd : ‖m - n‖ ^ 2 = (a.re - b.re) ^ 2 + (a.im - b.im) ^ 2 := by
      rw [hmn]
      have h1 := Complex.sq_norm (a - b)
      rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at h1
      nlinarith [h1]
    have key : ‖m - n‖ ^ 2 ≤ 8 * k ^ 2 - 4 * k * a.re - 4 * k * b.re := by
      rw [hd]
      nlinarith [sq_nonneg (a.re + b.re - 2 * k), sq_nonneg (a.im + b.im), ha2, hb2]
    have e1 : (f * m).re = ‖f‖ * a.re := by
      have : f * m = (‖f‖ : ℂ) * (c * m) := by rw [← mul_assoc, ← hfc]
      rw [this, Complex.re_ofReal_mul]
    have e2 : (f * n).re = ‖f‖ * b.re := by
      have : f * n = (‖f‖ : ℂ) * (c * n) := by rw [← mul_assoc, ← hfc]
      rw [this, Complex.re_ofReal_mul]
    rw [e1, e2]
    nlinarith [mul_le_mul_of_nonneg_right key hfn.le]

/-- Helper for **Theorem 4** (§9.4). A Beltrami differential is bounded by its norm almost everywhere in every chart. -/
theorem gl94_ae_bound {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R] {μ : R → ℂ → ℂ}
    (hμ : μ ∈ beltramiSpace R) (x : R) :
    ∀ᵐ z ∂(volume.restrict (chartAt ℂ x).target), ‖μ x z‖ ≤ (beltramiNormRS μ).toReal := by
  obtain ⟨c, -, hbd⟩ := hμ
  have hfin : beltramiNormRS μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal c) ENNReal.ofReal_ne_top (iSup_le fun y => ?_)
    rw [eLpNorm_exponent_top (hbd y).1]
    exact eLpNormEssSup_le_of_ae_bound (hbd y).2
  filter_upwards [ae_le_eLpNormEssSup (μ := volume.restrict (chartAt ℂ x).target) (f := μ x)] with z hz
  rw [← eLpNorm_exponent_top (hbd x).1] at hz
  have h1 : ‖μ x z‖ₑ ≤ beltramiNormRS μ :=
    hz.trans (le_iSup (fun y => eLpNorm (μ y) ⊤ (volume.restrict (chartAt ℂ y).target)) x)
  calc ‖μ x z‖ = (‖μ x z‖ₑ).toReal := (toReal_enorm _).symm
    _ ≤ (beltramiNormRS μ).toReal := ENNReal.toReal_mono hfin h1

/-- Helper for **Theorem 4** (§9.4). The inequality on one chart piece `G ⊆ ℂ`: for `f` with `f`, `f m`, `f n`
integrable on `G` and `|m|, |n| ≤ k` a.e. on `G`,
`∬_G |m − n|² |f| ≤ 8k² ∬_G |f| − 4k Re ∬_G f m − 4k Re ∬_G f n` (integrate `gl94_pointwise`; the right side is the
integral of a function that is `≥` a non-negative one, so it is `≥ 0`). -/
theorem gl94_piece_le {G : Set ℂ} {f m n : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k) (hf : Integrable f (volume.restrict G))
    (hfm : Integrable (fun z => f z * m z) (volume.restrict G))
    (hfn : Integrable (fun z => f z * n z) (volume.restrict G))
    (hmm : AEStronglyMeasurable m (volume.restrict G)) (hnm : AEStronglyMeasurable n (volume.restrict G))
    (hmk : ∀ᵐ z ∂(volume.restrict G), ‖m z‖ ≤ k) (hnk : ∀ᵐ z ∂(volume.restrict G), ‖n z‖ ≤ k) :
    0 ≤ 8 * k ^ 2 * (∫ z in G, ‖f z‖) - 4 * k * (∫ z in G, f z * m z).re - 4 * k * (∫ z in G, f z * n z).re ∧
      ∫⁻ z in G, ENNReal.ofReal (‖m z - n z‖ ^ 2) * ENNReal.ofReal ‖f z‖ ≤
        ENNReal.ofReal (8 * k ^ 2 * (∫ z in G, ‖f z‖) - 4 * k * (∫ z in G, f z * m z).re -
          4 * k * (∫ z in G, f z * n z).re) := by
  set Gf : ℂ → ℝ := fun z => 8 * k ^ 2 * ‖f z‖ - 4 * k * (f z * m z).re - 4 * k * (f z * n z).re with hGf
  have hGint : Integrable Gf (volume.restrict G) := by
    have h1 : Integrable (fun z => 8 * k ^ 2 * ‖f z‖) (volume.restrict G) := hf.norm.const_mul _
    have h2 : Integrable (fun z => 4 * k * (f z * m z).re) (volume.restrict G) :=
      (Complex.reCLM.integrable_comp hfm).const_mul _
    have h3 : Integrable (fun z => 4 * k * (f z * n z).re) (volume.restrict G) :=
      (Complex.reCLM.integrable_comp hfn).const_mul _
    exact (h1.sub h2).sub h3
  have hval : ∫ z in G, Gf z = 8 * k ^ 2 * (∫ z in G, ‖f z‖) - 4 * k * (∫ z in G, f z * m z).re -
      4 * k * (∫ z in G, f z * n z).re := by
    have h1 : Integrable (fun z => 8 * k ^ 2 * ‖f z‖) (volume.restrict G) := hf.norm.const_mul _
    have h2 : Integrable (fun z => 4 * k * (f z * m z).re) (volume.restrict G) :=
      (Complex.reCLM.integrable_comp hfm).const_mul _
    have h3 : Integrable (fun z => 4 * k * (f z * n z).re) (volume.restrict G) :=
      (Complex.reCLM.integrable_comp hfn).const_mul _
    simp only [hGf]
    have e1 : ∫ z in G, (f z * m z).re = (∫ z in G, f z * m z).re := integral_re hfm
    have e2 : ∫ z in G, (f z * n z).re = (∫ z in G, f z * n z).re := integral_re hfn
    have h12 : Integrable (fun z => 8 * k ^ 2 * ‖f z‖ - 4 * k * (f z * m z).re) (volume.restrict G) := h1.sub h2
    rw [integral_sub h12 h3, integral_sub h1 h2, integral_const_mul, integral_const_mul,
      integral_const_mul, e1, e2]
  have hpt : ∀ᵐ z ∂(volume.restrict G), ‖m z - n z‖ ^ 2 * ‖f z‖ ≤ Gf z := by
    filter_upwards [hmk, hnk] with z h1 h2
    exact gl94_pointwise hk h1 h2
  have hnn : ∀ᵐ z ∂(volume.restrict G), 0 ≤ Gf z := by
    filter_upwards [hpt] with z hz
    exact (by positivity : (0 : ℝ) ≤ ‖m z - n z‖ ^ 2 * ‖f z‖).trans hz
  have hR : 0 ≤ ∫ z in G, Gf z := integral_nonneg_of_ae hnn
  rw [hval] at hR
  refine ⟨hR, ?_⟩
  rw [← hval, ofReal_integral_eq_lintegral_ofReal hGint hnn]
  refine lintegral_mono_ae ?_
  filter_upwards [hpt] with z hz
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hz

/-- Helper for **Theorem 4** (§9.4). The series step: if the pieces `Fᵢ` satisfy
`Fᵢ ≤ 8k² Nᵢ − 4k Re Aᵢ − 4k Re Bᵢ` (with non-negative right-hand sides) for summable `N, A, B`, then
`Σ Fᵢ` is finite and `(Σ Fᵢ).toReal ≤ 8k² ΣN − 4k Re ΣA − 4k Re ΣB`. -/
theorem gl94_series {F : ℕ → ℝ≥0∞} {N : ℕ → ℝ} {A B : ℕ → ℂ} {k : ℝ} (hN : Summable N) (hA : Summable A)
    (hB : Summable B) (h0 : ∀ i, 0 ≤ 8 * k ^ 2 * N i - 4 * k * (A i).re - 4 * k * (B i).re)
    (hF : ∀ i, F i ≤ ENNReal.ofReal (8 * k ^ 2 * N i - 4 * k * (A i).re - 4 * k * (B i).re)) :
    ∑' i, F i ≠ ⊤ ∧ (∑' i, F i).toReal ≤ 8 * k ^ 2 * ∑' i, N i - 4 * k * (∑' i, A i).re -
      4 * k * (∑' i, B i).re := by
  have hAr : Summable fun i => (A i).re := Complex.reCLM.summable hA
  have hBr : Summable fun i => (B i).re := Complex.reCLM.summable hB
  have hs : Summable fun i => 8 * k ^ 2 * N i - 4 * k * (A i).re - 4 * k * (B i).re :=
    ((hN.mul_left _).sub (hAr.mul_left _)).sub (hBr.mul_left _)
  have hval : ∑' i, (8 * k ^ 2 * N i - 4 * k * (A i).re - 4 * k * (B i).re) =
      8 * k ^ 2 * ∑' i, N i - 4 * k * (∑' i, A i).re - 4 * k * (∑' i, B i).re := by
    rw [Summable.tsum_sub ((hN.mul_left _).sub (hAr.mul_left _)) (hBr.mul_left _),
      Summable.tsum_sub (hN.mul_left _) (hAr.mul_left _),
      tsum_mul_left, tsum_mul_left, tsum_mul_left, Complex.re_tsum hA, Complex.re_tsum hB]
  have hle : ∑' i, F i ≤ ENNReal.ofReal (∑' i, (8 * k ^ 2 * N i - 4 * k * (A i).re - 4 * k * (B i).re)) := by
    rw [ENNReal.ofReal_tsum_of_nonneg h0 hs]
    exact ENNReal.tsum_le_tsum hF
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle, ?_⟩
  calc (∑' i, F i).toReal ≤ (ENNReal.ofReal (∑' i, (8 * k ^ 2 * N i - 4 * k * (A i).re - 4 * k * (B i).re))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = ∑' i, (8 * k ^ 2 * N i - 4 * k * (A i).re - 4 * k * (B i).re) :=
        ENNReal.toReal_ofReal (tsum_nonneg h0)
    _ = _ := hval

/-- **Theorem 4** (§9.4, l. 7586). For infinitesimally equivalent `μ`, `ν` with `‖ν‖∞ ≤ ‖μ‖∞ < ∞`,
`∫ |μ − ν|²|φ| ≤ 8‖μ‖∞ (‖μ‖∞ ‖φ‖ − Re ∫ μφ)` for all `φ ∈ A(R)`. -/
theorem thm9_4 {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] {μ ν : R → ℂ → ℂ} (hμ : μ ∈ beltramiSpace R) (hν : ν ∈ beltramiSpace R)
    (hle : beltramiNormRS ν ≤ beltramiNormRS μ) (heq : IsInfEquiv μ ν) {φ : R → ℂ → ℂ}
    (hφ : φ ∈ integrableHolQDSet R) :
    (surfaceIntegral φ (fun x z => ENNReal.ofReal (‖μ x z - ν x z‖ ^ 2))).toReal ≤
      8 * (beltramiNormRS μ).toReal * reichDelta (beltramiNormRS μ).toReal μ φ := by
  classical
  have hμfin : beltramiNormRS μ ≠ ⊤ := by
    obtain ⟨c, -, hbd⟩ := hμ
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal c) ENNReal.ofReal_ne_top (iSup_le fun y => ?_)
    rw [eLpNorm_exponent_top (hbd y).1]
    exact eLpNormEssSup_le_of_ae_bound (hbd y).2
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = (beltramiNormRS μ).toReal := ⟨_, rfl⟩
  have hk0 : 0 ≤ k := hkdef ▸ ENNReal.toReal_nonneg
  have hμk : ∀ y : R, ∀ᵐ z ∂(volume.restrict (chartAt ℂ y).target), ‖μ y z‖ ≤ k := fun y => by
    rw [hkdef]
    exact gl94_ae_bound hμ y
  have hνk : ∀ y : R, ∀ᵐ z ∂(volume.restrict (chartAt ℂ y).target), ‖ν y z‖ ≤ k := fun y => by
    filter_upwards [gl94_ae_bound hν y] with z hz
    rw [hkdef]
    exact hz.trans (ENNReal.toReal_mono hμfin hle)
  have h := gl31_exists_partition_of_ne_top hφ.2.ne
  obtain ⟨x, hx⟩ : ∃ x : ℕ → R, x = h.choose := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ → Set R, P = h.choose_spec.choose := ⟨_, rfl⟩
  have hP : LiZhongQC.IsChartPartition R x P := hx ▸ hPdef ▸ h.choose_spec.choose_spec
  have hGt : ∀ i, chartAt ℂ (x i) '' P i ⊆ (chartAt ℂ (x i)).target := fun i =>
    image_subset_iff.2 fun q hq => (chartAt ℂ (x i)).map_source ((hP.1 i).1 hq)
  obtain ⟨hμint, hμsum⟩ := gl84_pairing_summable hμ hP hφ
  obtain ⟨hνint, hνsum⟩ := gl84_pairing_summable hν hP hφ
  -- the norm of `φ` as a partition sum
  have e1 := LiZhongQC.s26v_surfaceIntegral_eq_tsum hφ.1 (fun _ => (1 : ℝ≥0∞)) hP
  simp only [one_mul, ofReal_norm] at e1
  have hqd : ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖φ (x i) z‖ₑ = quadDiffNorm φ := e1.symm
  have hqdi : ∀ i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖φ (x i) z‖ₑ ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (hqd ▸ hφ.2.ne) (ENNReal.le_tsum (f := fun i => ∫⁻ z in chartAt ℂ (x i) '' P i,
      ‖φ (x i) z‖ₑ) i)
  have hφm : ∀ i, AEStronglyMeasurable (φ (x i)) (volume.restrict (chartAt ℂ (x i) '' P i)) := fun i =>
    ((hφ.1.2 (x i)).continuousOn.mono (hGt i)).aestronglyMeasurable (hP.1 i).2
  have hφi : ∀ i, Integrable (φ (x i)) (volume.restrict (chartAt ℂ (x i) '' P i)) := fun i =>
    ⟨hφm i, (hqdi i).lt_top⟩
  have hnorm_i : ∀ i, ∫ z in chartAt ℂ (x i) '' P i, ‖φ (x i) z‖ =
      (∫⁻ z in chartAt ℂ (x i) '' P i, ‖φ (x i) z‖ₑ).toReal := fun i =>
    integral_norm_eq_lintegral_enorm (hφm i)
  have hsumN : Summable fun i => ∫ z in chartAt ℂ (x i) '' P i, ‖φ (x i) z‖ := by
    simp only [hnorm_i]
    exact ENNReal.summable_toReal (hqd ▸ hφ.2.ne)
  have htsumN : ∑' i, ∫ z in chartAt ℂ (x i) '' P i, ‖φ (x i) z‖ = (quadDiffNorm φ).toReal := by
    simp only [hnorm_i]
    rw [← ENNReal.tsum_toReal_eq hqdi, hqd]
  have hmeasμ : ∀ i, AEStronglyMeasurable (μ (x i)) (volume.restrict (chartAt ℂ (x i) '' P i)) := fun i => by
    obtain ⟨c, -, hbd⟩ := hμ
    exact ((hbd (x i)).1).mono_measure (Measure.restrict_mono (hGt i) le_rfl)
  have hmeasν : ∀ i, AEStronglyMeasurable (ν (x i)) (volume.restrict (chartAt ℂ (x i) '' P i)) := fun i => by
    obtain ⟨c, -, hbd⟩ := hν
    exact ((hbd (x i)).1).mono_measure (Measure.restrict_mono (hGt i) le_rfl)
  have hpiece := fun i => gl94_piece_le hk0 (hφi i) (hμint i) (hνint i) (hmeasμ i) (hmeasν i)
    (ae_restrict_of_ae_restrict_of_subset (hGt i) (hμk (x i)))
    (ae_restrict_of_ae_restrict_of_subset (hGt i) (hνk (x i)))
  obtain ⟨hfin, hser⟩ := gl94_series (F := fun i => ∫⁻ z in chartAt ℂ (x i) '' P i,
    ENNReal.ofReal (‖μ (x i) z - ν (x i) z‖ ^ 2) * ENNReal.ofReal ‖φ (x i) z‖)
    (N := fun i => ∫ z in chartAt ℂ (x i) '' P i, ‖φ (x i) z‖)
    (A := fun i => ∫ z in chartAt ℂ (x i) '' P i, φ (x i) z * μ (x i) z)
    (B := fun i => ∫ z in chartAt ℂ (x i) '' P i, φ (x i) z * ν (x i) z) hsumN hμsum hνsum
    (fun i => (hpiece i).1) (fun i => (hpiece i).2)
  have hS : surfaceIntegral φ (fun y z => ENNReal.ofReal (‖μ y z - ν y z‖ ^ 2)) ≤
      ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i,
        ENNReal.ofReal (‖μ (x i) z - ν (x i) z‖ ^ 2) * ENNReal.ofReal ‖φ (x i) z‖ :=
    iInf_le_of_le x (iInf_le_of_le P (iInf_le_of_le hP le_rfl))
  have hpairμ : ∑' i, (∫ z in chartAt ℂ (x i) '' P i, φ (x i) z * μ (x i) z) = pairingRS φ μ := by
    rw [gl31_pairingRS_eq φ μ h, hx, hPdef]
  have hpairν : ∑' i, (∫ z in chartAt ℂ (x i) '' P i, φ (x i) z * ν (x i) z) = pairingRS φ ν := by
    rw [gl31_pairingRS_eq φ ν h, hx, hPdef]
  rw [htsumN, hpairμ, hpairν, ← heq φ hφ] at hser
  calc (surfaceIntegral φ (fun y z => ENNReal.ofReal (‖μ y z - ν y z‖ ^ 2))).toReal
      ≤ (∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal (‖μ (x i) z - ν (x i) z‖ ^ 2) *
        ENNReal.ofReal ‖φ (x i) z‖).toReal := ENNReal.toReal_mono hfin hS
    _ ≤ _ := hser
    _ = 8 * (beltramiNormRS μ).toReal * reichDelta (beltramiNormRS μ).toReal μ φ := by
        unfold reichDelta
        rw [← hkdef]
        ring

/-- Helper (§9.4). The Beltrami coefficient of `h : Y → R` at the point `w`, read in the preferred chart at `w`. -/
def coeffAtPoint {Y R : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [TopologicalSpace R] [ChartedSpace ℂ R]
    (h : Y → R) (w : Y) : ℂ :=
  beltramiCoeffRS h w (chartAt ℂ w w)

/-- **Theorem 5** (§9.4, l. 7628). If `μ` and `ν` are equivalent in `T` with `‖ν‖∞ ≤ k = ‖μ‖∞ < 1`, realized by
homotopic quasiconformal maps `f`, `g` with the same image, then
`∫_R |(μ̃(f) − ν̃(f))/(1 − conj(μ̃(f)) ν̃(f))|² |φ| ≤ C (k‖φ‖ − Re ∫ μφ)` for all `φ ∈ A(R)`, `C` depending only on
`k`.
[CORRECTION/modelling] (leader -ea, from the skillor's F0 audit, 2026-10-06): `p` and `q` are now Fuchsian
uniformizations (`∃ Γ, IsFuchsian Γ ∧ IsUniformization Γ p`, likewise `q`), as in the sibling statements. Without
them the statement is false: for constant `p`, `q` the relation `HomotopicModBoundary` is a homotopy fixing one
point, and two maps of the disc onto an ellipse with `μ ≡ k` (so the right side is `0`) and different coefficients
give a counterexample. -/
theorem thm9_5 (k : ℝ) (hk0 : 0 ≤ k) (hk : k < 1) :
    ∃ C : ℝ, ∀ (R : Type u) [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
      [IsManifold 𝓘(ℂ) ω R] (p : UpperHalfPlane → R) (Y : RSBundle.{u}) (q : UpperHalfPlane → Y.carrier)
      (μ ν : beltramiBall R) (f g : R ≃ₜ Y.carrier),
      beltramiNormRS μ.1 = ENNReal.ofReal k → beltramiNormRS ν.1 ≤ ENNReal.ofReal k → IsQCRS f → IsQCRS g →
      HasBeltramiCoeff f μ.1 → HasBeltramiCoeff g ν.1 →
      (∃ Γ, LiZhongQC.IsFuchsian Γ ∧ LiZhongQC.IsUniformization Γ p) →
      (∃ Γ, LiZhongQC.IsFuchsian Γ ∧ LiZhongQC.IsUniformization Γ q) → HomotopicModBoundary p q f g →
        ∀ φ ∈ integrableHolQDSet R,
          (surfaceIntegral φ (fun x z =>
            ENNReal.ofReal (‖(coeffAtPoint f.symm (f ((chartAt ℂ x).symm z)) -
                coeffAtPoint g.symm (f ((chartAt ℂ x).symm z))) /
              (1 - conj (coeffAtPoint f.symm (f ((chartAt ℂ x).symm z))) *
                coeffAtPoint g.symm (f ((chartAt ℂ x).symm z)))‖ ^ 2))).toReal ≤
            C * reichDelta k μ.1 φ := by
  sorry

end GardinerLakic2000
